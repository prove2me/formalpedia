-- Prove2me | solution 1 for syracuse_descends_range_1831617_1833617
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:59:54.252315+00:00
-- url     : https://prove2.me/submissions/e5cb09d7-861e-4353-9078-d2fa9fb8abac

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


theorem B9273365 : Blo 1831617 9273365 := bbase (se 6 (by rfl) ⟨217344, by rfl⟩ : syracuseStep 9273365 = 434689) (by norm_num)
theorem B6184997 : Blo 1831617 6184997 := bbase (se 4 (by rfl) ⟨579843, by rfl⟩ : syracuseStep 6184997 = 1159687) (by norm_num)
theorem B2318377 : Blo 1831617 2318377 := bbase (se 2 (by rfl) ⟨869391, by rfl⟩ : syracuseStep 2318377 = 1738783) (by norm_num)
theorem B2318473 : Blo 1831617 2318473 := bbase (se 2 (by rfl) ⟨869427, by rfl⟩ : syracuseStep 2318473 = 1738855) (by norm_num)
theorem B5218501 : Blo 1831617 5218501 := bbase (se 4 (by rfl) ⟨489234, by rfl⟩ : syracuseStep 5218501 = 978469) (by norm_num)
theorem B4636885 : Blo 1831617 4636885 := bbase (se 7 (by rfl) ⟨54338, by rfl⟩ : syracuseStep 4636885 = 108677) (by norm_num)
theorem B5570789 : Blo 1831617 5570789 := bbase (se 4 (by rfl) ⟨522261, by rfl⟩ : syracuseStep 5570789 = 1044523) (by norm_num)
theorem B6955253 : Blo 1831617 6955253 := bbase (se 5 (by rfl) ⟨326027, by rfl⟩ : syracuseStep 6955253 = 652055) (by norm_num)
theorem B3916021 : Blo 1831617 3916021 := bbase (se 5 (by rfl) ⟨183563, by rfl⟩ : syracuseStep 3916021 = 367127) (by norm_num)
theorem B2318645 : Blo 1831617 2318645 := bbase (se 5 (by rfl) ⟨108686, by rfl⟩ : syracuseStep 2318645 = 217373) (by norm_num)
theorem B4636997 : Blo 1831617 4636997 := bbase (se 4 (by rfl) ⟨434718, by rfl⟩ : syracuseStep 4636997 = 869437) (by norm_num)
theorem B5218661 : Blo 1831617 5218661 := bbase (se 4 (by rfl) ⟨489249, by rfl⟩ : syracuseStep 5218661 = 978499) (by norm_num)
theorem B2318701 : Blo 1831617 2318701 := bbase (se 3 (by rfl) ⟨434756, by rfl⟩ : syracuseStep 2318701 = 869513) (by norm_num)
theorem B2146721 : Blo 1831617 2146721 := bbase (se 2 (by rfl) ⟨805020, by rfl⟩ : syracuseStep 2146721 = 1610041) (by norm_num)
theorem B2318797 : Blo 1831617 2318797 := bbase (se 3 (by rfl) ⟨434774, by rfl⟩ : syracuseStep 2318797 = 869549) (by norm_num)
theorem B6185429 : Blo 1831617 6185429 := bbase (se 7 (by rfl) ⟨72485, by rfl⟩ : syracuseStep 6185429 = 144971) (by norm_num)
theorem B4637189 : Blo 1831617 4637189 := bbase (se 4 (by rfl) ⟨434736, by rfl⟩ : syracuseStep 4637189 = 869473) (by norm_num)
theorem B3301901 : Blo 1831617 3301901 := bbase (se 3 (by rfl) ⟨619106, by rfl⟩ : syracuseStep 3301901 = 1238213) (by norm_num)
theorem B6955541 : Blo 1831617 6955541 := bbase (se 6 (by rfl) ⟨163020, by rfl⟩ : syracuseStep 6955541 = 326041) (by norm_num)
theorem B5218901 : Blo 1831617 5218901 := bbase (se 8 (by rfl) ⟨30579, by rfl⟩ : syracuseStep 5218901 = 61159) (by norm_num)
theorem B4121189 : Blo 1831617 4121189 := bbase (se 4 (by rfl) ⟨386361, by rfl⟩ : syracuseStep 4121189 = 772723) (by norm_num)
theorem B2318969 : Blo 1831617 2318969 := bbase (se 2 (by rfl) ⟨869613, by rfl⟩ : syracuseStep 2318969 = 1739227) (by norm_num)
theorem B1983101 : Blo 1831617 1983101 := bbase (se 3 (by rfl) ⟨371831, by rfl⟩ : syracuseStep 1983101 = 743663) (by norm_num)
theorem B4121261 : Blo 1831617 4121261 := bbase (se 3 (by rfl) ⟨772736, by rfl⟩ : syracuseStep 4121261 = 1545473) (by norm_num)
theorem B2319025 : Blo 1831617 2319025 := bbase (se 2 (by rfl) ⟨869634, by rfl⟩ : syracuseStep 2319025 = 1739269) (by norm_num)
theorem B10724021 : Blo 1831617 10724021 := bbase (se 5 (by rfl) ⟨502688, by rfl⟩ : syracuseStep 10724021 = 1005377) (by norm_num)
theorem B19808981 : Blo 1831617 19808981 := bbase (se 7 (by rfl) ⟨232136, by rfl⟩ : syracuseStep 19808981 = 464273) (by norm_num)
theorem B2351857 : Blo 1831617 2351857 := bbase (se 2 (by rfl) ⟨881946, by rfl⟩ : syracuseStep 2351857 = 1763893) (by norm_num)
theorem B4121333 : Blo 1831617 4121333 := bbase (se 5 (by rfl) ⟨193187, by rfl⟩ : syracuseStep 4121333 = 386375) (by norm_num)
theorem B4465405 : Blo 1831617 4465405 := bbase (se 3 (by rfl) ⟨837263, by rfl⟩ : syracuseStep 4465405 = 1674527) (by norm_num)
theorem B2319121 : Blo 1831617 2319121 := bbase (se 2 (by rfl) ⟨869670, by rfl⟩ : syracuseStep 2319121 = 1739341) (by norm_num)
theorem B5219093 : Blo 1831617 5219093 := bbase (se 6 (by rfl) ⟨122322, by rfl⟩ : syracuseStep 5219093 = 244645) (by norm_num)
theorem B8356661 : Blo 1831617 8356661 := bbase (se 5 (by rfl) ⟨391718, by rfl⟩ : syracuseStep 8356661 = 783437) (by norm_num)
theorem B4121405 : Blo 1831617 4121405 := bbase (se 3 (by rfl) ⟨772763, by rfl⟩ : syracuseStep 4121405 = 1545527) (by norm_num)
theorem B16089941 : Blo 1831617 16089941 := bbase (se 9 (by rfl) ⟨47138, by rfl⟩ : syracuseStep 16089941 = 94277) (by norm_num)
theorem B4637533 : Blo 1831617 4637533 := bbase (se 3 (by rfl) ⟨869537, by rfl⟩ : syracuseStep 4637533 = 1739075) (by norm_num)
theorem B4121477 : Blo 1831617 4121477 := bbase (se 4 (by rfl) ⟨386388, by rfl⟩ : syracuseStep 4121477 = 772777) (by norm_num)
theorem B6185861 : Blo 1831617 6185861 := bbase (se 4 (by rfl) ⟨579924, by rfl⟩ : syracuseStep 6185861 = 1159849) (by norm_num)
theorem B9282437 : Blo 1831617 9282437 := bbase (se 4 (by rfl) ⟨870228, by rfl⟩ : syracuseStep 9282437 = 1740457) (by norm_num)
theorem B7054229 : Blo 1831617 7054229 := bbase (se 6 (by rfl) ⟨165333, by rfl⟩ : syracuseStep 7054229 = 330667) (by norm_num)
theorem B6783925 : Blo 1831617 6783925 := bbase (se 5 (by rfl) ⟨317996, by rfl⟩ : syracuseStep 6783925 = 635993) (by norm_num)
theorem B1983413 : Blo 1831617 1983413 := bbase (se 5 (by rfl) ⟨92972, by rfl⟩ : syracuseStep 1983413 = 185945) (by norm_num)
theorem B2319293 : Blo 1831617 2319293 := bbase (se 3 (by rfl) ⟨434867, by rfl⟩ : syracuseStep 2319293 = 869735) (by norm_num)
theorem B4121549 : Blo 1831617 4121549 := bbase (se 3 (by rfl) ⟨772790, by rfl⟩ : syracuseStep 4121549 = 1545581) (by norm_num)
theorem B4637645 : Blo 1831617 4637645 := bbase (se 3 (by rfl) ⟨869558, by rfl⟩ : syracuseStep 4637645 = 1739117) (by norm_num)
theorem B2319349 : Blo 1831617 2319349 := bbase (se 5 (by rfl) ⟨108719, by rfl⟩ : syracuseStep 2319349 = 217439) (by norm_num)
theorem B4121621 : Blo 1831617 4121621 := bbase (se 6 (by rfl) ⟨96600, by rfl⟩ : syracuseStep 4121621 = 193201) (by norm_num)
theorem B2319445 : Blo 1831617 2319445 := bbase (se 8 (by rfl) ⟨13590, by rfl⟩ : syracuseStep 2319445 = 27181) (by norm_num)
theorem B4121693 : Blo 1831617 4121693 := bbase (se 3 (by rfl) ⟨772817, by rfl⟩ : syracuseStep 4121693 = 1545635) (by norm_num)
theorem B4637837 : Blo 1831617 4637837 := bbase (se 3 (by rfl) ⟨869594, by rfl⟩ : syracuseStep 4637837 = 1739189) (by norm_num)
theorem B4121765 : Blo 1831617 4121765 := bbase (se 4 (by rfl) ⟨386415, by rfl⟩ : syracuseStep 4121765 = 772831) (by norm_num)
theorem B4121837 : Blo 1831617 4121837 := bbase (se 3 (by rfl) ⟨772844, by rfl⟩ : syracuseStep 4121837 = 1545689) (by norm_num)
theorem B2319617 : Blo 1831617 2319617 := bbase (se 2 (by rfl) ⟨869856, by rfl⟩ : syracuseStep 2319617 = 1739713) (by norm_num)
theorem B9274661 : Blo 1831617 9274661 := bbase (se 4 (by rfl) ⟨869499, by rfl⟩ : syracuseStep 9274661 = 1738999) (by norm_num)
theorem B4121909 : Blo 1831617 4121909 := bbase (se 5 (by rfl) ⟨193214, by rfl⟩ : syracuseStep 4121909 = 386429) (by norm_num)
theorem B6186293 : Blo 1831617 6186293 := bbase (se 5 (by rfl) ⟨289982, by rfl⟩ : syracuseStep 6186293 = 579965) (by norm_num)
theorem B2319673 : Blo 1831617 2319673 := bbase (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) (by norm_num)
theorem B4121981 : Blo 1831617 4121981 := bbase (se 3 (by rfl) ⟨772871, by rfl⟩ : syracuseStep 4121981 = 1545743) (by norm_num)
theorem B2319769 : Blo 1831617 2319769 := bbase (se 2 (by rfl) ⟨869913, by rfl⟩ : syracuseStep 2319769 = 1739827) (by norm_num)
theorem B4122053 : Blo 1831617 4122053 := bbase (se 4 (by rfl) ⟨386442, by rfl⟩ : syracuseStep 4122053 = 772885) (by norm_num)
theorem B6268373 : Blo 1831617 6268373 := bbase (se 7 (by rfl) ⟨73457, by rfl⟩ : syracuseStep 6268373 = 146915) (by norm_num)
theorem B4638181 : Blo 1831617 4638181 := bbase (se 4 (by rfl) ⟨434829, by rfl⟩ : syracuseStep 4638181 = 869659) (by norm_num)
theorem B4122125 : Blo 1831617 4122125 := bbase (se 3 (by rfl) ⟨772898, by rfl⟩ : syracuseStep 4122125 = 1545797) (by norm_num)
theorem B2319941 : Blo 1831617 2319941 := bbase (se 4 (by rfl) ⟨217494, by rfl⟩ : syracuseStep 2319941 = 434989) (by norm_num)
theorem B4122197 : Blo 1831617 4122197 := bbase (se 8 (by rfl) ⟨24153, by rfl⟩ : syracuseStep 4122197 = 48307) (by norm_num)
theorem B4638293 : Blo 1831617 4638293 := bbase (se 8 (by rfl) ⟨27177, by rfl⟩ : syracuseStep 4638293 = 54355) (by norm_num)
theorem B2319997 : Blo 1831617 2319997 := bbase (se 3 (by rfl) ⟨434999, by rfl⟩ : syracuseStep 2319997 = 869999) (by norm_num)
theorem B10577557 : Blo 1831617 10577557 := bbase (se 6 (by rfl) ⟨247911, by rfl⟩ : syracuseStep 10577557 = 495823) (by norm_num)
theorem B15656597 : Blo 1831617 15656597 := bbase (se 6 (by rfl) ⟨366951, by rfl⟩ : syracuseStep 15656597 = 733903) (by norm_num)
theorem B4122269 : Blo 1831617 4122269 := bbase (se 3 (by rfl) ⟨772925, by rfl⟩ : syracuseStep 4122269 = 1545851) (by norm_num)
theorem B6956725 : Blo 1831617 6956725 := bbase (se 5 (by rfl) ⟨326096, by rfl⟩ : syracuseStep 6956725 = 652193) (by norm_num)
theorem B2934485 : Blo 1831617 2934485 := bbase (se 7 (by rfl) ⟨34388, by rfl⟩ : syracuseStep 2934485 = 68777) (by norm_num)
theorem B2320093 : Blo 1831617 2320093 := bbase (se 3 (by rfl) ⟨435017, by rfl⟩ : syracuseStep 2320093 = 870035) (by norm_num)
theorem B4122341 : Blo 1831617 4122341 := bbase (se 4 (by rfl) ⟨386469, by rfl⟩ : syracuseStep 4122341 = 772939) (by norm_num)
theorem B6186725 : Blo 1831617 6186725 := bbase (se 4 (by rfl) ⟨580005, by rfl⟩ : syracuseStep 6186725 = 1160011) (by norm_num)
theorem B5220085 : Blo 1831617 5220085 := bbase (se 5 (by rfl) ⟨244691, by rfl⟩ : syracuseStep 5220085 = 489383) (by norm_num)
theorem B4638485 : Blo 1831617 4638485 := bbase (se 6 (by rfl) ⟨108714, by rfl⟩ : syracuseStep 4638485 = 217429) (by norm_num)
theorem B4122413 : Blo 1831617 4122413 := bbase (se 3 (by rfl) ⟨772952, by rfl⟩ : syracuseStep 4122413 = 1545905) (by norm_num)
theorem B4122485 : Blo 1831617 4122485 := bbase (se 5 (by rfl) ⟨193241, by rfl⟩ : syracuseStep 4122485 = 386483) (by norm_num)
theorem B2320265 : Blo 1831617 2320265 := bbase (se 2 (by rfl) ⟨870099, by rfl⟩ : syracuseStep 2320265 = 1740199) (by norm_num)
theorem B2934677 : Blo 1831617 2934677 := bbase (se 6 (by rfl) ⟨68781, by rfl⟩ : syracuseStep 2934677 = 137563) (by norm_num)
theorem B2975653 : Blo 1831617 2975653 := bbase (se 4 (by rfl) ⟨278967, by rfl⟩ : syracuseStep 2975653 = 557935) (by norm_num)
theorem B4122557 : Blo 1831617 4122557 := bbase (se 3 (by rfl) ⟨772979, by rfl⟩ : syracuseStep 4122557 = 1545959) (by norm_num)
theorem B2320321 : Blo 1831617 2320321 := bbase (se 2 (by rfl) ⟨870120, by rfl⟩ : syracuseStep 2320321 = 1740241) (by norm_num)
theorem B2787269 : Blo 1831617 2787269 := bbase (se 4 (by rfl) ⟨261306, by rfl⟩ : syracuseStep 2787269 = 522613) (by norm_num)
theorem B6957029 : Blo 1831617 6957029 := bbase (se 4 (by rfl) ⟨652221, by rfl⟩ : syracuseStep 6957029 = 1304443) (by norm_num)
theorem B4122629 : Blo 1831617 4122629 := bbase (se 4 (by rfl) ⟨386496, by rfl⟩ : syracuseStep 4122629 = 772993) (by norm_num)
theorem B19810325 : Blo 1831617 19810325 := bbase (se 6 (by rfl) ⟨464304, by rfl⟩ : syracuseStep 19810325 = 928609) (by norm_num)
theorem B2320417 : Blo 1831617 2320417 := bbase (se 2 (by rfl) ⟨870156, by rfl⟩ : syracuseStep 2320417 = 1740313) (by norm_num)
theorem B17860661 : Blo 1831617 17860661 := bbase (se 5 (by rfl) ⟨837218, by rfl⟩ : syracuseStep 17860661 = 1674437) (by norm_num)
theorem B4122701 : Blo 1831617 4122701 := bbase (se 3 (by rfl) ⟨773006, by rfl⟩ : syracuseStep 4122701 = 1546013) (by norm_num)
theorem B3303509 : Blo 1831617 3303509 := bbase (se 8 (by rfl) ⟨19356, by rfl⟩ : syracuseStep 3303509 = 38713) (by norm_num)
theorem B4638829 : Blo 1831617 4638829 := bbase (se 3 (by rfl) ⟨869780, by rfl⟩ : syracuseStep 4638829 = 1739561) (by norm_num)
theorem B4122773 : Blo 1831617 4122773 := bbase (se 6 (by rfl) ⟨96627, by rfl⟩ : syracuseStep 4122773 = 193255) (by norm_num)
theorem B6187157 : Blo 1831617 6187157 := bbase (se 6 (by rfl) ⟨145011, by rfl⟩ : syracuseStep 6187157 = 290023) (by norm_num)
theorem B2320589 : Blo 1831617 2320589 := bbase (se 3 (by rfl) ⟨435110, by rfl⟩ : syracuseStep 2320589 = 870221) (by norm_num)
theorem B23472341 : Blo 1831617 23472341 := bbase (se 7 (by rfl) ⟨275066, by rfl⟩ : syracuseStep 23472341 = 550133) (by norm_num)
theorem B4122845 : Blo 1831617 4122845 := bbase (se 3 (by rfl) ⟨773033, by rfl⟩ : syracuseStep 4122845 = 1546067) (by norm_num)
theorem B4638941 : Blo 1831617 4638941 := bbase (se 3 (by rfl) ⟨869801, by rfl⟩ : syracuseStep 4638941 = 1739603) (by norm_num)
theorem B4180229 : Blo 1831617 4180229 := bbase (se 4 (by rfl) ⟨391896, by rfl⟩ : syracuseStep 4180229 = 783793) (by norm_num)
theorem B2320645 : Blo 1831617 2320645 := bbase (se 4 (by rfl) ⟨217560, by rfl⟩ : syracuseStep 2320645 = 435121) (by norm_num)
theorem B3713293 : Blo 1831617 3713293 := bbase (se 3 (by rfl) ⟨696242, by rfl⟩ : syracuseStep 3713293 = 1392485) (by norm_num)
theorem B4122917 : Blo 1831617 4122917 := bbase (se 4 (by rfl) ⟨386523, by rfl⟩ : syracuseStep 4122917 = 773047) (by norm_num)
theorem B11151701 : Blo 1831617 11151701 := bbase (se 10 (by rfl) ⟨16335, by rfl⟩ : syracuseStep 11151701 = 32671) (by norm_num)
theorem B4122989 : Blo 1831617 4122989 := bbase (se 3 (by rfl) ⟨773060, by rfl⟩ : syracuseStep 4122989 = 1546121) (by norm_num)
theorem B4639133 : Blo 1831617 4639133 := bbase (se 3 (by rfl) ⟨869837, by rfl⟩ : syracuseStep 4639133 = 1739675) (by norm_num)
theorem B4123061 : Blo 1831617 4123061 := bbase (se 5 (by rfl) ⟨193268, by rfl⟩ : syracuseStep 4123061 = 386537) (by norm_num)
theorem B4123133 : Blo 1831617 4123133 := bbase (se 3 (by rfl) ⟨773087, by rfl⟩ : syracuseStep 4123133 = 1546175) (by norm_num)
theorem B10439189 : Blo 1831617 10439189 := bbase (se 6 (by rfl) ⟨244668, by rfl⟩ : syracuseStep 10439189 = 489337) (by norm_num)
theorem B3090973 : Blo 1831617 3090973 := bbase (se 3 (by rfl) ⟨579557, by rfl⟩ : syracuseStep 3090973 = 1159115) (by norm_num)
theorem B9275957 : Blo 1831617 9275957 := bbase (se 5 (by rfl) ⟨434810, by rfl⟩ : syracuseStep 9275957 = 869621) (by norm_num)
theorem B2787901 : Blo 1831617 2787901 := bbase (se 3 (by rfl) ⟨522731, by rfl⟩ : syracuseStep 2787901 = 1045463) (by norm_num)
theorem B4123205 : Blo 1831617 4123205 := bbase (se 4 (by rfl) ⟨386550, by rfl⟩ : syracuseStep 4123205 = 773101) (by norm_num)
theorem B6187589 : Blo 1831617 6187589 := bbase (se 4 (by rfl) ⟨580086, by rfl⟩ : syracuseStep 6187589 = 1160173) (by norm_num)
theorem B3525205 : Blo 1831617 3525205 := bbase (se 8 (by rfl) ⟨20655, by rfl⟩ : syracuseStep 3525205 = 41311) (by norm_num)
theorem B3091061 : Blo 1831617 3091061 := bbase (se 5 (by rfl) ⟨144893, by rfl⟩ : syracuseStep 3091061 = 289787) (by norm_num)
theorem B4123277 : Blo 1831617 4123277 := bbase (se 3 (by rfl) ⟨773114, by rfl⟩ : syracuseStep 4123277 = 1546229) (by norm_num)
theorem B16714421 : Blo 1831617 16714421 := bbase (se 5 (by rfl) ⟨783488, by rfl⟩ : syracuseStep 16714421 = 1566977) (by norm_num)
theorem B4123349 : Blo 1831617 4123349 := bbase (se 7 (by rfl) ⟨48320, by rfl⟩ : syracuseStep 4123349 = 96641) (by norm_num)
theorem B3304165 : Blo 1831617 3304165 := bbase (se 4 (by rfl) ⟨309765, by rfl⟩ : syracuseStep 3304165 = 619531) (by norm_num)
theorem B3091189 : Blo 1831617 3091189 := bbase (se 5 (by rfl) ⟨144899, by rfl⟩ : syracuseStep 3091189 = 289799) (by norm_num)
theorem B7826165 : Blo 1831617 7826165 := bbase (se 5 (by rfl) ⟨366851, by rfl⟩ : syracuseStep 7826165 = 733703) (by norm_num)
theorem B4639477 : Blo 1831617 4639477 := bbase (se 5 (by rfl) ⟨217475, by rfl⟩ : syracuseStep 4639477 = 434951) (by norm_num)
theorem B4123421 : Blo 1831617 4123421 := bbase (se 3 (by rfl) ⟨773141, by rfl⟩ : syracuseStep 4123421 = 1546283) (by norm_num)
theorem B5221189 : Blo 1831617 5221189 := bbase (se 4 (by rfl) ⟨489486, by rfl⟩ : syracuseStep 5221189 = 978973) (by norm_num)
theorem B3091277 : Blo 1831617 3091277 := bbase (se 3 (by rfl) ⟨579614, by rfl⟩ : syracuseStep 3091277 = 1159229) (by norm_num)
theorem B4123493 : Blo 1831617 4123493 := bbase (se 4 (by rfl) ⟨386577, by rfl⟩ : syracuseStep 4123493 = 773155) (by norm_num)
theorem B4639589 : Blo 1831617 4639589 := bbase (se 4 (by rfl) ⟨434961, by rfl⟩ : syracuseStep 4639589 = 869923) (by norm_num)
theorem B4123565 : Blo 1831617 4123565 := bbase (se 3 (by rfl) ⟨773168, by rfl⟩ : syracuseStep 4123565 = 1546337) (by norm_num)
theorem B3091405 : Blo 1831617 3091405 := bbase (se 3 (by rfl) ⟨579638, by rfl⟩ : syracuseStep 3091405 = 1159277) (by norm_num)
theorem B4123637 : Blo 1831617 4123637 := bbase (se 5 (by rfl) ⟨193295, by rfl⟩ : syracuseStep 4123637 = 386591) (by norm_num)
theorem B6188021 : Blo 1831617 6188021 := bbase (se 5 (by rfl) ⟨290063, by rfl⟩ : syracuseStep 6188021 = 580127) (by norm_num)
theorem B7826453 : Blo 1831617 7826453 := bbase (se 6 (by rfl) ⟨183432, by rfl⟩ : syracuseStep 7826453 = 366865) (by norm_num)
theorem B2608157 : Blo 1831617 2608157 := bbase (se 3 (by rfl) ⟨489029, by rfl⟩ : syracuseStep 2608157 = 978059) (by norm_num)
theorem B2747429 : Blo 1831617 2747429 := bbase (se 4 (by rfl) ⟨257571, by rfl⟩ : syracuseStep 2747429 = 515143) (by norm_num)
theorem B3091493 : Blo 1831617 3091493 := bbase (se 4 (by rfl) ⟨289827, by rfl⟩ : syracuseStep 3091493 = 579655) (by norm_num)
theorem B4639781 : Blo 1831617 4639781 := bbase (se 4 (by rfl) ⟨434979, by rfl⟩ : syracuseStep 4639781 = 869959) (by norm_num)
theorem B18091061 : Blo 1831617 18091061 := bbase (se 5 (by rfl) ⟨848018, by rfl⟩ : syracuseStep 18091061 = 1696037) (by norm_num)
theorem B2747453 : Blo 1831617 2747453 := bbase (se 3 (by rfl) ⟨515147, by rfl⟩ : syracuseStep 2747453 = 1030295) (by norm_num)
theorem B4123709 : Blo 1831617 4123709 := bbase (se 3 (by rfl) ⟨773195, by rfl⟩ : syracuseStep 4123709 = 1546391) (by norm_num)
theorem B2747477 : Blo 1831617 2747477 := bbase (se 8 (by rfl) ⟨16098, by rfl⟩ : syracuseStep 2747477 = 32197) (by norm_num)
theorem B5360725 : Blo 1831617 5360725 := bbase (se 8 (by rfl) ⟨31410, by rfl⟩ : syracuseStep 5360725 = 62821) (by norm_num)
theorem B30125141 : Blo 1831617 30125141 := bbase (se 8 (by rfl) ⟨176514, by rfl⟩ : syracuseStep 30125141 = 353029) (by norm_num)
theorem B2747501 : Blo 1831617 2747501 := bbase (se 3 (by rfl) ⟨515156, by rfl⟩ : syracuseStep 2747501 = 1030313) (by norm_num)
theorem B2608237 : Blo 1831617 2608237 := bbase (se 3 (by rfl) ⟨489044, by rfl⟩ : syracuseStep 2608237 = 978089) (by norm_num)
theorem B7433333 : Blo 1831617 7433333 := bbase (se 5 (by rfl) ⟨348437, by rfl⟩ : syracuseStep 7433333 = 696875) (by norm_num)
theorem B2747525 : Blo 1831617 2747525 := bbase (se 4 (by rfl) ⟨257580, by rfl⟩ : syracuseStep 2747525 = 515161) (by norm_num)
theorem B4123781 : Blo 1831617 4123781 := bbase (se 4 (by rfl) ⟨386604, by rfl⟩ : syracuseStep 4123781 = 773209) (by norm_num)
theorem B2747549 : Blo 1831617 2747549 := bbase (se 3 (by rfl) ⟨515165, by rfl⟩ : syracuseStep 2747549 = 1030331) (by norm_num)
theorem B3091621 : Blo 1831617 3091621 := bbase (se 4 (by rfl) ⟨289839, by rfl⟩ : syracuseStep 3091621 = 579679) (by norm_num)
theorem B2747573 : Blo 1831617 2747573 := bbase (se 5 (by rfl) ⟨128792, by rfl⟩ : syracuseStep 2747573 = 257585) (by norm_num)
theorem B2935997 : Blo 1831617 2935997 := bbase (se 3 (by rfl) ⟨550499, by rfl⟩ : syracuseStep 2935997 = 1100999) (by norm_num)
theorem B2747597 : Blo 1831617 2747597 := bbase (se 3 (by rfl) ⟨515174, by rfl⟩ : syracuseStep 2747597 = 1030349) (by norm_num)
theorem B4123853 : Blo 1831617 4123853 := bbase (se 3 (by rfl) ⟨773222, by rfl⟩ : syracuseStep 4123853 = 1546445) (by norm_num)
theorem B11144405 : Blo 1831617 11144405 := bbase (se 7 (by rfl) ⟨130598, by rfl⟩ : syracuseStep 11144405 = 261197) (by norm_num)
theorem B2747621 : Blo 1831617 2747621 := bbase (se 4 (by rfl) ⟨257589, by rfl⟩ : syracuseStep 2747621 = 515179) (by norm_num)
theorem B2608357 : Blo 1831617 2608357 := bbase (se 4 (by rfl) ⟨244533, by rfl⟩ : syracuseStep 2608357 = 489067) (by norm_num)
theorem B2747645 : Blo 1831617 2747645 := bbase (se 3 (by rfl) ⟨515183, by rfl⟩ : syracuseStep 2747645 = 1030367) (by norm_num)
theorem B3091709 : Blo 1831617 3091709 := bbase (se 3 (by rfl) ⟨579695, by rfl⟩ : syracuseStep 3091709 = 1159391) (by norm_num)
theorem B2747669 : Blo 1831617 2747669 := bbase (se 6 (by rfl) ⟨64398, by rfl⟩ : syracuseStep 2747669 = 128797) (by norm_num)
theorem B4123925 : Blo 1831617 4123925 := bbase (se 6 (by rfl) ⟨96654, by rfl⟩ : syracuseStep 4123925 = 193309) (by norm_num)
theorem B2936093 : Blo 1831617 2936093 := bbase (se 3 (by rfl) ⟨550517, by rfl⟩ : syracuseStep 2936093 = 1101035) (by norm_num)
theorem B2747693 : Blo 1831617 2747693 := bbase (se 3 (by rfl) ⟨515192, by rfl⟩ : syracuseStep 2747693 = 1030385) (by norm_num)
theorem B2936125 : Blo 1831617 2936125 := bbase (se 3 (by rfl) ⟨550523, by rfl⟩ : syracuseStep 2936125 = 1101047) (by norm_num)
theorem B2747717 : Blo 1831617 2747717 := bbase (se 4 (by rfl) ⟨257598, by rfl⟩ : syracuseStep 2747717 = 515197) (by norm_num)
theorem B2608453 : Blo 1831617 2608453 := bbase (se 4 (by rfl) ⟨244542, by rfl⟩ : syracuseStep 2608453 = 489085) (by norm_num)
theorem B2747741 : Blo 1831617 2747741 := bbase (se 3 (by rfl) ⟨515201, by rfl⟩ : syracuseStep 2747741 = 1030403) (by norm_num)
theorem B4123997 : Blo 1831617 4123997 := bbase (se 3 (by rfl) ⟨773249, by rfl⟩ : syracuseStep 4123997 = 1546499) (by norm_num)
theorem B2747765 : Blo 1831617 2747765 := bbase (se 5 (by rfl) ⟨128801, by rfl⟩ : syracuseStep 2747765 = 257603) (by norm_num)
theorem B3091837 : Blo 1831617 3091837 := bbase (se 3 (by rfl) ⟨579719, by rfl⟩ : syracuseStep 3091837 = 1159439) (by norm_num)
theorem B4640125 : Blo 1831617 4640125 := bbase (se 3 (by rfl) ⟨870023, by rfl⟩ : syracuseStep 4640125 = 1740047) (by norm_num)
theorem B2747789 : Blo 1831617 2747789 := bbase (se 3 (by rfl) ⟨515210, by rfl⟩ : syracuseStep 2747789 = 1030421) (by norm_num)
theorem B2747813 : Blo 1831617 2747813 := bbase (se 4 (by rfl) ⟨257607, by rfl⟩ : syracuseStep 2747813 = 515215) (by norm_num)
theorem B4124069 : Blo 1831617 4124069 := bbase (se 4 (by rfl) ⟨386631, by rfl⟩ : syracuseStep 4124069 = 773263) (by norm_num)
theorem B6188453 : Blo 1831617 6188453 := bbase (se 4 (by rfl) ⟨580167, by rfl⟩ : syracuseStep 6188453 = 1160335) (by norm_num)
theorem B2747837 : Blo 1831617 2747837 := bbase (se 3 (by rfl) ⟨515219, by rfl⟩ : syracuseStep 2747837 = 1030439) (by norm_num)
theorem B2747861 : Blo 1831617 2747861 := bbase (se 7 (by rfl) ⟨32201, by rfl⟩ : syracuseStep 2747861 = 64403) (by norm_num)
theorem B3091925 : Blo 1831617 3091925 := bbase (se 7 (by rfl) ⟨36233, by rfl⟩ : syracuseStep 3091925 = 72467) (by norm_num)
theorem B2747885 : Blo 1831617 2747885 := bbase (se 3 (by rfl) ⟨515228, by rfl⟩ : syracuseStep 2747885 = 1030457) (by norm_num)
theorem B4124141 : Blo 1831617 4124141 := bbase (se 3 (by rfl) ⟨773276, by rfl⟩ : syracuseStep 4124141 = 1546553) (by norm_num)
theorem B4640237 : Blo 1831617 4640237 := bbase (se 3 (by rfl) ⟨870044, by rfl⟩ : syracuseStep 4640237 = 1740089) (by norm_num)
theorem B14855669 : Blo 1831617 14855669 := bbase (se 5 (by rfl) ⟨696359, by rfl⟩ : syracuseStep 14855669 = 1392719) (by norm_num)
theorem B2747909 : Blo 1831617 2747909 := bbase (se 4 (by rfl) ⟨257616, by rfl⟩ : syracuseStep 2747909 = 515233) (by norm_num)
theorem B2747933 : Blo 1831617 2747933 := bbase (se 3 (by rfl) ⟨515237, by rfl⟩ : syracuseStep 2747933 = 1030475) (by norm_num)
theorem B2747957 : Blo 1831617 2747957 := bbase (se 5 (by rfl) ⟨128810, by rfl⟩ : syracuseStep 2747957 = 257621) (by norm_num)
theorem B4124213 : Blo 1831617 4124213 := bbase (se 5 (by rfl) ⟨193322, by rfl⟩ : syracuseStep 4124213 = 386645) (by norm_num)
theorem B2747981 : Blo 1831617 2747981 := bbase (se 3 (by rfl) ⟨515246, by rfl⟩ : syracuseStep 2747981 = 1030493) (by norm_num)
theorem B4402765 : Blo 1831617 4402765 := bbase (se 3 (by rfl) ⟨825518, by rfl⟩ : syracuseStep 4402765 = 1651037) (by norm_num)
theorem B3092053 : Blo 1831617 3092053 := bbase (se 8 (by rfl) ⟨18117, by rfl⟩ : syracuseStep 3092053 = 36235) (by norm_num)
theorem B2748005 : Blo 1831617 2748005 := bbase (se 4 (by rfl) ⟨257625, by rfl⟩ : syracuseStep 2748005 = 515251) (by norm_num)
theorem B2748029 : Blo 1831617 2748029 := bbase (se 3 (by rfl) ⟨515255, by rfl⟩ : syracuseStep 2748029 = 1030511) (by norm_num)
theorem B4124285 : Blo 1831617 4124285 := bbase (se 3 (by rfl) ⟨773303, by rfl⟩ : syracuseStep 4124285 = 1546607) (by norm_num)
theorem B2748053 : Blo 1831617 2748053 := bbase (se 6 (by rfl) ⟨64407, by rfl⟩ : syracuseStep 2748053 = 128815) (by norm_num)
theorem B2748077 : Blo 1831617 2748077 := bbase (se 3 (by rfl) ⟨515264, by rfl⟩ : syracuseStep 2748077 = 1030529) (by norm_num)
theorem B3092141 : Blo 1831617 3092141 := bbase (se 3 (by rfl) ⟨579776, by rfl⟩ : syracuseStep 3092141 = 1159553) (by norm_num)
theorem B4640429 : Blo 1831617 4640429 := bbase (se 3 (by rfl) ⟨870080, by rfl⟩ : syracuseStep 4640429 = 1740161) (by norm_num)
theorem B10440373 : Blo 1831617 10440373 := bbase (se 5 (by rfl) ⟨489392, by rfl⟩ : syracuseStep 10440373 = 978785) (by norm_num)
theorem B2748101 : Blo 1831617 2748101 := bbase (se 4 (by rfl) ⟨257634, by rfl⟩ : syracuseStep 2748101 = 515269) (by norm_num)
theorem B4124357 : Blo 1831617 4124357 := bbase (se 4 (by rfl) ⟨386658, by rfl⟩ : syracuseStep 4124357 = 773317) (by norm_num)
theorem B2748125 : Blo 1831617 2748125 := bbase (se 3 (by rfl) ⟨515273, by rfl⟩ : syracuseStep 2748125 = 1030547) (by norm_num)
theorem B2748149 : Blo 1831617 2748149 := bbase (se 5 (by rfl) ⟨128819, by rfl⟩ : syracuseStep 2748149 = 257639) (by norm_num)
theorem B7827205 : Blo 1831617 7827205 := bbase (se 4 (by rfl) ⟨733800, by rfl⟩ : syracuseStep 7827205 = 1467601) (by norm_num)
theorem B2748173 : Blo 1831617 2748173 := bbase (se 3 (by rfl) ⟨515282, by rfl⟩ : syracuseStep 2748173 = 1030565) (by norm_num)
theorem B4124429 : Blo 1831617 4124429 := bbase (se 3 (by rfl) ⟨773330, by rfl⟩ : syracuseStep 4124429 = 1546661) (by norm_num)
theorem B3477269 : Blo 1831617 3477269 := bbase (se 6 (by rfl) ⟨81498, by rfl⟩ : syracuseStep 3477269 = 162997) (by norm_num)
theorem B2748197 : Blo 1831617 2748197 := bbase (se 4 (by rfl) ⟨257643, by rfl⟩ : syracuseStep 2748197 = 515287) (by norm_num)
theorem B3092269 : Blo 1831617 3092269 := bbase (se 3 (by rfl) ⟨579800, by rfl⟩ : syracuseStep 3092269 = 1159601) (by norm_num)
theorem B2608949 : Blo 1831617 2608949 := bbase (se 5 (by rfl) ⟨122294, by rfl⟩ : syracuseStep 2608949 = 244589) (by norm_num)
theorem B2748221 : Blo 1831617 2748221 := bbase (se 3 (by rfl) ⟨515291, by rfl⟩ : syracuseStep 2748221 = 1030583) (by norm_num)
theorem B9277253 : Blo 1831617 9277253 := bbase (se 4 (by rfl) ⟨869742, by rfl⟩ : syracuseStep 9277253 = 1739485) (by norm_num)
theorem B2748245 : Blo 1831617 2748245 := bbase (se 9 (by rfl) ⟨8051, by rfl⟩ : syracuseStep 2748245 = 16103) (by norm_num)
theorem B4124501 : Blo 1831617 4124501 := bbase (se 9 (by rfl) ⟨12083, by rfl⟩ : syracuseStep 4124501 = 24167) (by norm_num)
theorem B2748269 : Blo 1831617 2748269 := bbase (se 3 (by rfl) ⟨515300, by rfl⟩ : syracuseStep 2748269 = 1030601) (by norm_num)
theorem B2748293 : Blo 1831617 2748293 := bbase (se 4 (by rfl) ⟨257652, by rfl⟩ : syracuseStep 2748293 = 515305) (by norm_num)
theorem B3092357 : Blo 1831617 3092357 := bbase (se 4 (by rfl) ⟨289908, by rfl⟩ : syracuseStep 3092357 = 579817) (by norm_num)
theorem B2748317 : Blo 1831617 2748317 := bbase (se 3 (by rfl) ⟨515309, by rfl⟩ : syracuseStep 2748317 = 1030619) (by norm_num)
theorem B4124573 : Blo 1831617 4124573 := bbase (se 3 (by rfl) ⟨773357, by rfl⟩ : syracuseStep 4124573 = 1546715) (by norm_num)
theorem B3477421 : Blo 1831617 3477421 := bbase (se 3 (by rfl) ⟨652016, by rfl⟩ : syracuseStep 3477421 = 1304033) (by norm_num)
theorem B2748341 : Blo 1831617 2748341 := bbase (se 5 (by rfl) ⟨128828, by rfl⟩ : syracuseStep 2748341 = 257657) (by norm_num)
theorem B2748365 : Blo 1831617 2748365 := bbase (se 3 (by rfl) ⟨515318, by rfl⟩ : syracuseStep 2748365 = 1030637) (by norm_num)
theorem B35229653 : Blo 1831617 35229653 := bbase (se 7 (by rfl) ⟨412847, by rfl⟩ : syracuseStep 35229653 = 825695) (by norm_num)
theorem B3526621 : Blo 1831617 3526621 := bbase (se 3 (by rfl) ⟨661241, by rfl⟩ : syracuseStep 3526621 = 1322483) (by norm_num)
theorem B2748389 : Blo 1831617 2748389 := bbase (se 4 (by rfl) ⟨257661, by rfl⟩ : syracuseStep 2748389 = 515323) (by norm_num)
theorem B4124645 : Blo 1831617 4124645 := bbase (se 4 (by rfl) ⟨386685, by rfl⟩ : syracuseStep 4124645 = 773371) (by norm_num)
theorem B2748413 : Blo 1831617 2748413 := bbase (se 3 (by rfl) ⟨515327, by rfl⟩ : syracuseStep 2748413 = 1030655) (by norm_num)
theorem B3092485 : Blo 1831617 3092485 := bbase (se 4 (by rfl) ⟨289920, by rfl⟩ : syracuseStep 3092485 = 579841) (by norm_num)
theorem B4640773 : Blo 1831617 4640773 := bbase (se 4 (by rfl) ⟨435072, by rfl⟩ : syracuseStep 4640773 = 870145) (by norm_num)
theorem B2748437 : Blo 1831617 2748437 := bbase (se 6 (by rfl) ⟨64416, by rfl⟩ : syracuseStep 2748437 = 128833) (by norm_num)
theorem B8802341 : Blo 1831617 8802341 := bbase (se 4 (by rfl) ⟨825219, by rfl⟩ : syracuseStep 8802341 = 1650439) (by norm_num)
theorem B6959141 : Blo 1831617 6959141 := bbase (se 4 (by rfl) ⟨652419, by rfl⟩ : syracuseStep 6959141 = 1304839) (by norm_num)
theorem B2748461 : Blo 1831617 2748461 := bbase (se 3 (by rfl) ⟨515336, by rfl⟩ : syracuseStep 2748461 = 1030673) (by norm_num)
theorem B4124717 : Blo 1831617 4124717 := bbase (se 3 (by rfl) ⟨773384, by rfl⟩ : syracuseStep 4124717 = 1546769) (by norm_num)
theorem B4952117 : Blo 1831617 4952117 := bbase (se 5 (by rfl) ⟨232130, by rfl⟩ : syracuseStep 4952117 = 464261) (by norm_num)
theorem B2748485 : Blo 1831617 2748485 := bbase (se 4 (by rfl) ⟨257670, by rfl⟩ : syracuseStep 2748485 = 515341) (by norm_num)
theorem B6606917 : Blo 1831617 6606917 := bbase (se 4 (by rfl) ⟨619398, by rfl⟩ : syracuseStep 6606917 = 1238797) (by norm_num)
theorem B3715157 : Blo 1831617 3715157 := bbase (se 8 (by rfl) ⟨21768, by rfl⟩ : syracuseStep 3715157 = 43537) (by norm_num)
theorem B2748509 : Blo 1831617 2748509 := bbase (se 3 (by rfl) ⟨515345, by rfl⟩ : syracuseStep 2748509 = 1030691) (by norm_num)
theorem B3092573 : Blo 1831617 3092573 := bbase (se 3 (by rfl) ⟨579857, by rfl⟩ : syracuseStep 3092573 = 1159715) (by norm_num)
theorem B2748533 : Blo 1831617 2748533 := bbase (se 5 (by rfl) ⟨128837, by rfl⟩ : syracuseStep 2748533 = 257675) (by norm_num)
theorem B4124789 : Blo 1831617 4124789 := bbase (se 5 (by rfl) ⟨193349, by rfl⟩ : syracuseStep 4124789 = 386699) (by norm_num)
theorem B4640885 : Blo 1831617 4640885 := bbase (se 5 (by rfl) ⟨217541, by rfl⟩ : syracuseStep 4640885 = 435083) (by norm_num)
theorem B2748557 : Blo 1831617 2748557 := bbase (se 3 (by rfl) ⟨515354, by rfl⟩ : syracuseStep 2748557 = 1030709) (by norm_num)
theorem B3969181 : Blo 1831617 3969181 := bbase (se 3 (by rfl) ⟨744221, by rfl⟩ : syracuseStep 3969181 = 1488443) (by norm_num)
theorem B2748581 : Blo 1831617 2748581 := bbase (se 4 (by rfl) ⟨257679, by rfl⟩ : syracuseStep 2748581 = 515359) (by norm_num)
theorem B2748605 : Blo 1831617 2748605 := bbase (se 3 (by rfl) ⟨515363, by rfl⟩ : syracuseStep 2748605 = 1030727) (by norm_num)
theorem B4124861 : Blo 1831617 4124861 := bbase (se 3 (by rfl) ⟨773411, by rfl⟩ : syracuseStep 4124861 = 1546823) (by norm_num)
theorem B2748629 : Blo 1831617 2748629 := bbase (se 7 (by rfl) ⟨32210, by rfl⟩ : syracuseStep 2748629 = 64421) (by norm_num)
theorem B4526293 : Blo 1831617 4526293 := bbase (se 7 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 4526293 = 106085) (by norm_num)
theorem B3477725 : Blo 1831617 3477725 := bbase (se 3 (by rfl) ⟨652073, by rfl⟩ : syracuseStep 3477725 = 1304147) (by norm_num)
theorem B3092701 : Blo 1831617 3092701 := bbase (se 3 (by rfl) ⟨579881, by rfl⟩ : syracuseStep 3092701 = 1159763) (by norm_num)
theorem B2748653 : Blo 1831617 2748653 := bbase (se 3 (by rfl) ⟨515372, by rfl⟩ : syracuseStep 2748653 = 1030745) (by norm_num)
theorem B2748677 : Blo 1831617 2748677 := bbase (se 4 (by rfl) ⟨257688, by rfl⟩ : syracuseStep 2748677 = 515377) (by norm_num)
theorem B4124933 : Blo 1831617 4124933 := bbase (se 4 (by rfl) ⟨386712, by rfl⟩ : syracuseStep 4124933 = 773425) (by norm_num)
theorem B2748701 : Blo 1831617 2748701 := bbase (se 3 (by rfl) ⟨515381, by rfl⟩ : syracuseStep 2748701 = 1030763) (by norm_num)
theorem B2060581 : Blo 1831617 2060581 := bbase (se 4 (by rfl) ⟨193179, by rfl⟩ : syracuseStep 2060581 = 386359) (by norm_num)
theorem B3911989 : Blo 1831617 3911989 := bbase (se 5 (by rfl) ⟨183374, by rfl⟩ : syracuseStep 3911989 = 366749) (by norm_num)
theorem B2748725 : Blo 1831617 2748725 := bbase (se 5 (by rfl) ⟨128846, by rfl⟩ : syracuseStep 2748725 = 257693) (by norm_num)
theorem B3092789 : Blo 1831617 3092789 := bbase (se 5 (by rfl) ⟨144974, by rfl⟩ : syracuseStep 3092789 = 289949) (by norm_num)
theorem B4641077 : Blo 1831617 4641077 := bbase (se 5 (by rfl) ⟨217550, by rfl⟩ : syracuseStep 4641077 = 435101) (by norm_num)
theorem B6959429 : Blo 1831617 6959429 := bbase (se 4 (by rfl) ⟨652446, by rfl⟩ : syracuseStep 6959429 = 1304893) (by norm_num)
theorem B2060617 : Blo 1831617 2060617 := bbase (se 2 (by rfl) ⟨772731, by rfl⟩ : syracuseStep 2060617 = 1545463) (by norm_num)
theorem B2748749 : Blo 1831617 2748749 := bbase (se 3 (by rfl) ⟨515390, by rfl⟩ : syracuseStep 2748749 = 1030781) (by norm_num)
theorem B4125005 : Blo 1831617 4125005 := bbase (se 3 (by rfl) ⟨773438, by rfl⟩ : syracuseStep 4125005 = 1546877) (by norm_num)
theorem B2609501 : Blo 1831617 2609501 := bbase (se 3 (by rfl) ⟨489281, by rfl⟩ : syracuseStep 2609501 = 978563) (by norm_num)
theorem B2748773 : Blo 1831617 2748773 := bbase (se 4 (by rfl) ⟨257697, by rfl⟩ : syracuseStep 2748773 = 515395) (by norm_num)
theorem B2060653 : Blo 1831617 2060653 := bbase (se 3 (by rfl) ⟨386372, by rfl⟩ : syracuseStep 2060653 = 772745) (by norm_num)
theorem B2748797 : Blo 1831617 2748797 := bbase (se 3 (by rfl) ⟨515399, by rfl⟩ : syracuseStep 2748797 = 1030799) (by norm_num)
theorem B2060689 : Blo 1831617 2060689 := bbase (se 2 (by rfl) ⟨772758, by rfl⟩ : syracuseStep 2060689 = 1545517) (by norm_num)
theorem B2748821 : Blo 1831617 2748821 := bbase (se 6 (by rfl) ⟨64425, by rfl⟩ : syracuseStep 2748821 = 128851) (by norm_num)
theorem B4125077 : Blo 1831617 4125077 := bbase (se 6 (by rfl) ⟨96681, by rfl⟩ : syracuseStep 4125077 = 193363) (by norm_num)
theorem B2748845 : Blo 1831617 2748845 := bbase (se 3 (by rfl) ⟨515408, by rfl⟩ : syracuseStep 2748845 = 1030817) (by norm_num)
theorem B2060725 : Blo 1831617 2060725 := bbase (se 5 (by rfl) ⟨96596, by rfl⟩ : syracuseStep 2060725 = 193193) (by norm_num)
theorem B3092917 : Blo 1831617 3092917 := bbase (se 5 (by rfl) ⟨144980, by rfl⟩ : syracuseStep 3092917 = 289961) (by norm_num)
theorem B3912133 : Blo 1831617 3912133 := bbase (se 4 (by rfl) ⟨366762, by rfl⟩ : syracuseStep 3912133 = 733525) (by norm_num)
theorem B2748869 : Blo 1831617 2748869 := bbase (se 4 (by rfl) ⟨257706, by rfl⟩ : syracuseStep 2748869 = 515413) (by norm_num)
theorem B2060761 : Blo 1831617 2060761 := bbase (se 2 (by rfl) ⟨772785, by rfl⟩ : syracuseStep 2060761 = 1545571) (by norm_num)
theorem B2748893 : Blo 1831617 2748893 := bbase (se 3 (by rfl) ⟨515417, by rfl⟩ : syracuseStep 2748893 = 1030835) (by norm_num)
theorem B4125149 : Blo 1831617 4125149 := bbase (se 3 (by rfl) ⟨773465, by rfl⟩ : syracuseStep 4125149 = 1546931) (by norm_num)
theorem B7827941 : Blo 1831617 7827941 := bbase (se 4 (by rfl) ⟨733869, by rfl⟩ : syracuseStep 7827941 = 1467739) (by norm_num)
theorem B2748917 : Blo 1831617 2748917 := bbase (se 5 (by rfl) ⟨128855, by rfl⟩ : syracuseStep 2748917 = 257711) (by norm_num)
theorem B2060797 : Blo 1831617 2060797 := bbase (se 3 (by rfl) ⟨386399, by rfl⟩ : syracuseStep 2060797 = 772799) (by norm_num)
theorem B2748941 : Blo 1831617 2748941 := bbase (se 3 (by rfl) ⟨515426, by rfl⟩ : syracuseStep 2748941 = 1030853) (by norm_num)
theorem B3093005 : Blo 1831617 3093005 := bbase (se 3 (by rfl) ⟨579938, by rfl⟩ : syracuseStep 3093005 = 1159877) (by norm_num)
theorem B2060833 : Blo 1831617 2060833 := bbase (se 2 (by rfl) ⟨772812, by rfl⟩ : syracuseStep 2060833 = 1545625) (by norm_num)
theorem B2748965 : Blo 1831617 2748965 := bbase (se 4 (by rfl) ⟨257715, by rfl⟩ : syracuseStep 2748965 = 515431) (by norm_num)
theorem B4125221 : Blo 1831617 4125221 := bbase (se 4 (by rfl) ⟨386739, by rfl⟩ : syracuseStep 4125221 = 773479) (by norm_num)
theorem B2748989 : Blo 1831617 2748989 := bbase (se 3 (by rfl) ⟨515435, by rfl⟩ : syracuseStep 2748989 = 1030871) (by norm_num)
theorem B3715645 : Blo 1831617 3715645 := bbase (se 3 (by rfl) ⟨696683, by rfl⟩ : syracuseStep 3715645 = 1393367) (by norm_num)
theorem B2060869 : Blo 1831617 2060869 := bbase (se 4 (by rfl) ⟨193206, by rfl⟩ : syracuseStep 2060869 = 386413) (by norm_num)
theorem B2749013 : Blo 1831617 2749013 := bbase (se 8 (by rfl) ⟨16107, by rfl⟩ : syracuseStep 2749013 = 32215) (by norm_num)
theorem B2060905 : Blo 1831617 2060905 := bbase (se 2 (by rfl) ⟨772839, by rfl⟩ : syracuseStep 2060905 = 1545679) (by norm_num)
theorem B2749037 : Blo 1831617 2749037 := bbase (se 3 (by rfl) ⟨515444, by rfl⟩ : syracuseStep 2749037 = 1030889) (by norm_num)
theorem B4125293 : Blo 1831617 4125293 := bbase (se 3 (by rfl) ⟨773492, by rfl⟩ : syracuseStep 4125293 = 1546985) (by norm_num)
theorem B2749061 : Blo 1831617 2749061 := bbase (se 4 (by rfl) ⟨257724, by rfl⟩ : syracuseStep 2749061 = 515449) (by norm_num)
theorem B6607493 : Blo 1831617 6607493 := bbase (se 4 (by rfl) ⟨619452, by rfl⟩ : syracuseStep 6607493 = 1238905) (by norm_num)
theorem B2060941 : Blo 1831617 2060941 := bbase (se 3 (by rfl) ⟨386426, by rfl⟩ : syracuseStep 2060941 = 772853) (by norm_num)
theorem B3093133 : Blo 1831617 3093133 := bbase (se 3 (by rfl) ⟨579962, by rfl⟩ : syracuseStep 3093133 = 1159925) (by norm_num)
theorem B2749085 : Blo 1831617 2749085 := bbase (se 3 (by rfl) ⟨515453, by rfl⟩ : syracuseStep 2749085 = 1030907) (by norm_num)
theorem B2060977 : Blo 1831617 2060977 := bbase (se 2 (by rfl) ⟨772866, by rfl⟩ : syracuseStep 2060977 = 1545733) (by norm_num)
theorem B2749109 : Blo 1831617 2749109 := bbase (se 5 (by rfl) ⟨128864, by rfl⟩ : syracuseStep 2749109 = 257729) (by norm_num)
theorem B4125365 : Blo 1831617 4125365 := bbase (se 5 (by rfl) ⟨193376, by rfl⟩ : syracuseStep 4125365 = 386753) (by norm_num)
theorem B2749133 : Blo 1831617 2749133 := bbase (se 3 (by rfl) ⟨515462, by rfl⟩ : syracuseStep 2749133 = 1030925) (by norm_num)
theorem B2061013 : Blo 1831617 2061013 := bbase (se 7 (by rfl) ⟨24152, by rfl⟩ : syracuseStep 2061013 = 48305) (by norm_num)
theorem B7533269 : Blo 1831617 7533269 := bbase (se 7 (by rfl) ⟨88280, by rfl⟩ : syracuseStep 7533269 = 176561) (by norm_num)
theorem B2749157 : Blo 1831617 2749157 := bbase (se 4 (by rfl) ⟨257733, by rfl⟩ : syracuseStep 2749157 = 515467) (by norm_num)
theorem B3093221 : Blo 1831617 3093221 := bbase (se 4 (by rfl) ⟨289989, by rfl⟩ : syracuseStep 3093221 = 579979) (by norm_num)
theorem B2061049 : Blo 1831617 2061049 := bbase (se 2 (by rfl) ⟨772893, by rfl⟩ : syracuseStep 2061049 = 1545787) (by norm_num)
theorem B2749181 : Blo 1831617 2749181 := bbase (se 3 (by rfl) ⟨515471, by rfl⟩ : syracuseStep 2749181 = 1030943) (by norm_num)
theorem B4125437 : Blo 1831617 4125437 := bbase (se 3 (by rfl) ⟨773519, by rfl⟩ : syracuseStep 4125437 = 1547039) (by norm_num)
theorem B2749205 : Blo 1831617 2749205 := bbase (se 6 (by rfl) ⟨64434, by rfl⟩ : syracuseStep 2749205 = 128869) (by norm_num)
theorem B2061085 : Blo 1831617 2061085 := bbase (se 3 (by rfl) ⟨386453, by rfl⟩ : syracuseStep 2061085 = 772907) (by norm_num)
theorem B2749229 : Blo 1831617 2749229 := bbase (se 3 (by rfl) ⟨515480, by rfl⟩ : syracuseStep 2749229 = 1030961) (by norm_num)
theorem B3912509 : Blo 1831617 3912509 := bbase (se 3 (by rfl) ⟨733595, by rfl⟩ : syracuseStep 3912509 = 1467191) (by norm_num)
theorem B2061121 : Blo 1831617 2061121 := bbase (se 2 (by rfl) ⟨772920, by rfl⟩ : syracuseStep 2061121 = 1545841) (by norm_num)
theorem B2749253 : Blo 1831617 2749253 := bbase (se 4 (by rfl) ⟨257742, by rfl⟩ : syracuseStep 2749253 = 515485) (by norm_num)
theorem B4125509 : Blo 1831617 4125509 := bbase (se 4 (by rfl) ⟨386766, by rfl⟩ : syracuseStep 4125509 = 773533) (by norm_num)
theorem B2749277 : Blo 1831617 2749277 := bbase (se 3 (by rfl) ⟨515489, by rfl⟩ : syracuseStep 2749277 = 1030979) (by norm_num)
theorem B2061157 : Blo 1831617 2061157 := bbase (se 4 (by rfl) ⟨193233, by rfl⟩ : syracuseStep 2061157 = 386467) (by norm_num)
theorem B3093349 : Blo 1831617 3093349 := bbase (se 4 (by rfl) ⟨290001, by rfl⟩ : syracuseStep 3093349 = 580003) (by norm_num)
theorem B2749301 : Blo 1831617 2749301 := bbase (se 5 (by rfl) ⟨128873, by rfl⟩ : syracuseStep 2749301 = 257747) (by norm_num)
theorem B2200441 : Blo 1831617 2200441 := bbase (se 2 (by rfl) ⟨825165, by rfl⟩ : syracuseStep 2200441 = 1650331) (by norm_num)
theorem B2061193 : Blo 1831617 2061193 := bbase (se 2 (by rfl) ⟨772947, by rfl⟩ : syracuseStep 2061193 = 1545895) (by norm_num)
theorem B2749325 : Blo 1831617 2749325 := bbase (se 3 (by rfl) ⟨515498, by rfl⟩ : syracuseStep 2749325 = 1030997) (by norm_num)
theorem B4125581 : Blo 1831617 4125581 := bbase (se 3 (by rfl) ⟨773546, by rfl⟩ : syracuseStep 4125581 = 1547093) (by norm_num)
theorem B2749349 : Blo 1831617 2749349 := bbase (se 4 (by rfl) ⟨257751, by rfl⟩ : syracuseStep 2749349 = 515503) (by norm_num)
theorem B2061229 : Blo 1831617 2061229 := bbase (se 3 (by rfl) ⟨386480, by rfl⟩ : syracuseStep 2061229 = 772961) (by norm_num)
theorem B4404149 : Blo 1831617 4404149 := bbase (se 5 (by rfl) ⟨206444, by rfl⟩ : syracuseStep 4404149 = 412889) (by norm_num)
theorem B2749373 : Blo 1831617 2749373 := bbase (se 3 (by rfl) ⟨515507, by rfl⟩ : syracuseStep 2749373 = 1031015) (by norm_num)
theorem B3093437 : Blo 1831617 3093437 := bbase (se 3 (by rfl) ⟨580019, by rfl⟩ : syracuseStep 3093437 = 1160039) (by norm_num)
theorem B3478477 : Blo 1831617 3478477 := bbase (se 3 (by rfl) ⟨652214, by rfl⟩ : syracuseStep 3478477 = 1304429) (by norm_num)
theorem B2061265 : Blo 1831617 2061265 := bbase (se 2 (by rfl) ⟨772974, by rfl⟩ : syracuseStep 2061265 = 1545949) (by norm_num)
theorem B2749397 : Blo 1831617 2749397 := bbase (se 7 (by rfl) ⟨32219, by rfl⟩ : syracuseStep 2749397 = 64439) (by norm_num)
theorem B2200537 : Blo 1831617 2200537 := bbase (se 2 (by rfl) ⟨825201, by rfl⟩ : syracuseStep 2200537 = 1650403) (by norm_num)
theorem B2749421 : Blo 1831617 2749421 := bbase (se 3 (by rfl) ⟨515516, by rfl⟩ : syracuseStep 2749421 = 1031033) (by norm_num)
theorem B2061301 : Blo 1831617 2061301 := bbase (se 5 (by rfl) ⟨96623, by rfl⟩ : syracuseStep 2061301 = 193247) (by norm_num)
theorem B2749445 : Blo 1831617 2749445 := bbase (se 4 (by rfl) ⟨257760, by rfl⟩ : syracuseStep 2749445 = 515521) (by norm_num)
theorem B2061337 : Blo 1831617 2061337 := bbase (se 2 (by rfl) ⟨773001, by rfl⟩ : syracuseStep 2061337 = 1546003) (by norm_num)
theorem B2749469 : Blo 1831617 2749469 := bbase (se 3 (by rfl) ⟨515525, by rfl⟩ : syracuseStep 2749469 = 1031051) (by norm_num)
theorem B2749493 : Blo 1831617 2749493 := bbase (se 5 (by rfl) ⟨128882, by rfl⟩ : syracuseStep 2749493 = 257765) (by norm_num)
theorem B2061373 : Blo 1831617 2061373 := bbase (se 3 (by rfl) ⟨386507, by rfl⟩ : syracuseStep 2061373 = 773015) (by norm_num)
theorem B3093565 : Blo 1831617 3093565 := bbase (se 3 (by rfl) ⟨580043, by rfl⟩ : syracuseStep 3093565 = 1160087) (by norm_num)
theorem B2749517 : Blo 1831617 2749517 := bbase (se 3 (by rfl) ⟨515534, by rfl⟩ : syracuseStep 2749517 = 1031069) (by norm_num)
theorem B2610253 : Blo 1831617 2610253 := bbase (se 3 (by rfl) ⟨489422, by rfl⟩ : syracuseStep 2610253 = 978845) (by norm_num)
theorem B6181973 : Blo 1831617 6181973 := bbase (se 8 (by rfl) ⟨36222, by rfl⟩ : syracuseStep 6181973 = 72445) (by norm_num)
theorem B9278549 : Blo 1831617 9278549 := bbase (se 8 (by rfl) ⟨54366, by rfl⟩ : syracuseStep 9278549 = 108733) (by norm_num)
theorem B13923413 : Blo 1831617 13923413 := bbase (se 8 (by rfl) ⟨81582, by rfl⟩ : syracuseStep 13923413 = 163165) (by norm_num)
theorem B3478621 : Blo 1831617 3478621 := bbase (se 3 (by rfl) ⟨652241, by rfl⟩ : syracuseStep 3478621 = 1304483) (by norm_num)
theorem B2061409 : Blo 1831617 2061409 := bbase (se 2 (by rfl) ⟨773028, by rfl⟩ : syracuseStep 2061409 = 1546057) (by norm_num)
theorem B2749541 : Blo 1831617 2749541 := bbase (se 4 (by rfl) ⟨257769, by rfl⟩ : syracuseStep 2749541 = 515539) (by norm_num)
theorem B4404341 : Blo 1831617 4404341 := bbase (se 5 (by rfl) ⟨206453, by rfl⟩ : syracuseStep 4404341 = 412907) (by norm_num)
theorem B5952629 : Blo 1831617 5952629 := bbase (se 5 (by rfl) ⟨279029, by rfl⟩ : syracuseStep 5952629 = 558059) (by norm_num)
theorem B2749565 : Blo 1831617 2749565 := bbase (se 3 (by rfl) ⟨515543, by rfl⟩ : syracuseStep 2749565 = 1031087) (by norm_num)
theorem B2061445 : Blo 1831617 2061445 := bbase (se 4 (by rfl) ⟨193260, by rfl⟩ : syracuseStep 2061445 = 386521) (by norm_num)
theorem B2749589 : Blo 1831617 2749589 := bbase (se 6 (by rfl) ⟨64443, by rfl⟩ : syracuseStep 2749589 = 128887) (by norm_num)
theorem B3093653 : Blo 1831617 3093653 := bbase (se 6 (by rfl) ⟨72507, by rfl⟩ : syracuseStep 3093653 = 145015) (by norm_num)
theorem B2061481 : Blo 1831617 2061481 := bbase (se 2 (by rfl) ⟨773055, by rfl⟩ : syracuseStep 2061481 = 1546111) (by norm_num)
theorem B3912877 : Blo 1831617 3912877 := bbase (se 3 (by rfl) ⟨733664, by rfl⟩ : syracuseStep 3912877 = 1467329) (by norm_num)
theorem B2749613 : Blo 1831617 2749613 := bbase (se 3 (by rfl) ⟨515552, by rfl⟩ : syracuseStep 2749613 = 1031105) (by norm_num)
theorem B3527869 : Blo 1831617 3527869 := bbase (se 3 (by rfl) ⟨661475, by rfl⟩ : syracuseStep 3527869 = 1322951) (by norm_num)
theorem B5870789 : Blo 1831617 5870789 := bbase (se 4 (by rfl) ⟨550386, by rfl⟩ : syracuseStep 5870789 = 1100773) (by norm_num)
theorem B7935173 : Blo 1831617 7935173 := bbase (se 4 (by rfl) ⟨743922, by rfl⟩ : syracuseStep 7935173 = 1487845) (by norm_num)
theorem B2749637 : Blo 1831617 2749637 := bbase (se 4 (by rfl) ⟨257778, by rfl⟩ : syracuseStep 2749637 = 515557) (by norm_num)
theorem B2061517 : Blo 1831617 2061517 := bbase (se 3 (by rfl) ⟨386534, by rfl⟩ : syracuseStep 2061517 = 773069) (by norm_num)
theorem B2749661 : Blo 1831617 2749661 := bbase (se 3 (by rfl) ⟨515561, by rfl⟩ : syracuseStep 2749661 = 1031123) (by norm_num)
theorem B2061553 : Blo 1831617 2061553 := bbase (se 2 (by rfl) ⟨773082, by rfl⟩ : syracuseStep 2061553 = 1546165) (by norm_num)
theorem B2749685 : Blo 1831617 2749685 := bbase (se 5 (by rfl) ⟨128891, by rfl⟩ : syracuseStep 2749685 = 257783) (by norm_num)
theorem B3478781 : Blo 1831617 3478781 := bbase (se 3 (by rfl) ⟨652271, by rfl⟩ : syracuseStep 3478781 = 1304543) (by norm_num)
theorem B2749709 : Blo 1831617 2749709 := bbase (se 3 (by rfl) ⟨515570, by rfl⟩ : syracuseStep 2749709 = 1031141) (by norm_num)
theorem B6354197 : Blo 1831617 6354197 := bbase (se 6 (by rfl) ⟨148926, by rfl⟩ : syracuseStep 6354197 = 297853) (by norm_num)
theorem B2061589 : Blo 1831617 2061589 := bbase (se 6 (by rfl) ⟨48318, by rfl⟩ : syracuseStep 2061589 = 96637) (by norm_num)
theorem B3093781 : Blo 1831617 3093781 := bbase (se 6 (by rfl) ⟨72510, by rfl⟩ : syracuseStep 3093781 = 145021) (by norm_num)
theorem B2749733 : Blo 1831617 2749733 := bbase (se 4 (by rfl) ⟨257787, by rfl⟩ : syracuseStep 2749733 = 515575) (by norm_num)
theorem B2061625 : Blo 1831617 2061625 := bbase (se 2 (by rfl) ⟨773109, by rfl⟩ : syracuseStep 2061625 = 1546219) (by norm_num)
theorem B2749757 : Blo 1831617 2749757 := bbase (se 3 (by rfl) ⟨515579, by rfl⟩ : syracuseStep 2749757 = 1031159) (by norm_num)
theorem B2749781 : Blo 1831617 2749781 := bbase (se 13 (by rfl) ⟨503, by rfl⟩ : syracuseStep 2749781 = 1007) (by norm_num)
theorem B2061661 : Blo 1831617 2061661 := bbase (se 3 (by rfl) ⟨386561, by rfl⟩ : syracuseStep 2061661 = 773123) (by norm_num)
theorem B2749805 : Blo 1831617 2749805 := bbase (se 3 (by rfl) ⟨515588, by rfl⟩ : syracuseStep 2749805 = 1031177) (by norm_num)
theorem B3093869 : Blo 1831617 3093869 := bbase (se 3 (by rfl) ⟨580100, by rfl⟩ : syracuseStep 3093869 = 1160201) (by norm_num)
theorem B2061697 : Blo 1831617 2061697 := bbase (se 2 (by rfl) ⟨773136, by rfl⟩ : syracuseStep 2061697 = 1546273) (by norm_num)
theorem B2749829 : Blo 1831617 2749829 := bbase (se 4 (by rfl) ⟨257796, by rfl⟩ : syracuseStep 2749829 = 515593) (by norm_num)
theorem B3478925 : Blo 1831617 3478925 := bbase (se 3 (by rfl) ⟨652298, by rfl⟩ : syracuseStep 3478925 = 1304597) (by norm_num)
theorem B2749853 : Blo 1831617 2749853 := bbase (se 3 (by rfl) ⟨515597, by rfl⟩ : syracuseStep 2749853 = 1031195) (by norm_num)
theorem B2061733 : Blo 1831617 2061733 := bbase (se 4 (by rfl) ⟨193287, by rfl⟩ : syracuseStep 2061733 = 386575) (by norm_num)
theorem B2749877 : Blo 1831617 2749877 := bbase (se 5 (by rfl) ⟨128900, by rfl⟩ : syracuseStep 2749877 = 257801) (by norm_num)
theorem B2061769 : Blo 1831617 2061769 := bbase (se 2 (by rfl) ⟨773163, by rfl⟩ : syracuseStep 2061769 = 1546327) (by norm_num)
theorem B2749901 : Blo 1831617 2749901 := bbase (se 3 (by rfl) ⟨515606, by rfl⟩ : syracuseStep 2749901 = 1031213) (by norm_num)
theorem B6960613 : Blo 1831617 6960613 := bbase (se 4 (by rfl) ⟨652557, by rfl⟩ : syracuseStep 6960613 = 1305115) (by norm_num)
theorem B2749925 : Blo 1831617 2749925 := bbase (se 4 (by rfl) ⟨257805, by rfl⟩ : syracuseStep 2749925 = 515611) (by norm_num)
theorem B2061805 : Blo 1831617 2061805 := bbase (se 3 (by rfl) ⟨386588, by rfl⟩ : syracuseStep 2061805 = 773177) (by norm_num)
theorem B3093997 : Blo 1831617 3093997 := bbase (se 3 (by rfl) ⟨580124, by rfl⟩ : syracuseStep 3093997 = 1160249) (by norm_num)
theorem B4019701 : Blo 1831617 4019701 := bbase (se 5 (by rfl) ⟨188423, by rfl⟩ : syracuseStep 4019701 = 376847) (by norm_num)
theorem B13915637 : Blo 1831617 13915637 := bbase (se 5 (by rfl) ⟨652295, by rfl⟩ : syracuseStep 13915637 = 1304591) (by norm_num)
theorem B2749949 : Blo 1831617 2749949 := bbase (se 3 (by rfl) ⟨515615, by rfl⟩ : syracuseStep 2749949 = 1031231) (by norm_num)
theorem B6182405 : Blo 1831617 6182405 := bbase (se 4 (by rfl) ⟨579600, by rfl⟩ : syracuseStep 6182405 = 1159201) (by norm_num)
theorem B2061841 : Blo 1831617 2061841 := bbase (se 2 (by rfl) ⟨773190, by rfl⟩ : syracuseStep 2061841 = 1546381) (by norm_num)
theorem B2749973 : Blo 1831617 2749973 := bbase (se 6 (by rfl) ⟨64452, by rfl⟩ : syracuseStep 2749973 = 128905) (by norm_num)
theorem B2201113 : Blo 1831617 2201113 := bbase (se 2 (by rfl) ⟨825417, by rfl⟩ : syracuseStep 2201113 = 1650835) (by norm_num)
theorem B2749997 : Blo 1831617 2749997 := bbase (se 3 (by rfl) ⟨515624, by rfl⟩ : syracuseStep 2749997 = 1031249) (by norm_num)
theorem B2061877 : Blo 1831617 2061877 := bbase (se 5 (by rfl) ⟨96650, by rfl⟩ : syracuseStep 2061877 = 193301) (by norm_num)
theorem B2750021 : Blo 1831617 2750021 := bbase (se 4 (by rfl) ⟨257814, by rfl⟩ : syracuseStep 2750021 = 515629) (by norm_num)
theorem B3094085 : Blo 1831617 3094085 := bbase (se 4 (by rfl) ⟨290070, by rfl⟩ : syracuseStep 3094085 = 580141) (by norm_num)
theorem B2061913 : Blo 1831617 2061913 := bbase (se 2 (by rfl) ⟨773217, by rfl⟩ : syracuseStep 2061913 = 1546435) (by norm_num)
theorem B2750045 : Blo 1831617 2750045 := bbase (se 3 (by rfl) ⟨515633, by rfl⟩ : syracuseStep 2750045 = 1031267) (by norm_num)
theorem B1857125 : Blo 1831617 1857125 := bbase (se 4 (by rfl) ⟨174105, by rfl⟩ : syracuseStep 1857125 = 348211) (by norm_num)
theorem B2750069 : Blo 1831617 2750069 := bbase (se 5 (by rfl) ⟨128909, by rfl⟩ : syracuseStep 2750069 = 257819) (by norm_num)
theorem B10442357 : Blo 1831617 10442357 := bbase (se 5 (by rfl) ⟨489485, by rfl⟩ : syracuseStep 10442357 = 978971) (by norm_num)
theorem B2061949 : Blo 1831617 2061949 := bbase (se 3 (by rfl) ⟨386615, by rfl⟩ : syracuseStep 2061949 = 773231) (by norm_num)
theorem B2750093 : Blo 1831617 2750093 := bbase (se 3 (by rfl) ⟨515642, by rfl⟩ : syracuseStep 2750093 = 1031285) (by norm_num)
theorem B2061985 : Blo 1831617 2061985 := bbase (se 2 (by rfl) ⟨773244, by rfl⟩ : syracuseStep 2061985 = 1546489) (by norm_num)
theorem B3176101 : Blo 1831617 3176101 := bbase (se 4 (by rfl) ⟨297759, by rfl⟩ : syracuseStep 3176101 = 595519) (by norm_num)
theorem B2750117 : Blo 1831617 2750117 := bbase (se 4 (by rfl) ⟨257823, by rfl⟩ : syracuseStep 2750117 = 515647) (by norm_num)
theorem B3479213 : Blo 1831617 3479213 := bbase (se 3 (by rfl) ⟨652352, by rfl⟩ : syracuseStep 3479213 = 1304705) (by norm_num)
theorem B2750141 : Blo 1831617 2750141 := bbase (se 3 (by rfl) ⟨515651, by rfl⟩ : syracuseStep 2750141 = 1031303) (by norm_num)
theorem B2062021 : Blo 1831617 2062021 := bbase (se 4 (by rfl) ⟨193314, by rfl⟩ : syracuseStep 2062021 = 386629) (by norm_num)
theorem B3094213 : Blo 1831617 3094213 := bbase (se 4 (by rfl) ⟨290082, by rfl⟩ : syracuseStep 3094213 = 580165) (by norm_num)
theorem B2750165 : Blo 1831617 2750165 := bbase (se 7 (by rfl) ⟨32228, by rfl⟩ : syracuseStep 2750165 = 64457) (by norm_num)
theorem B2062057 : Blo 1831617 2062057 := bbase (se 2 (by rfl) ⟨773271, by rfl⟩ : syracuseStep 2062057 = 1546543) (by norm_num)
theorem B2750189 : Blo 1831617 2750189 := bbase (se 3 (by rfl) ⟨515660, by rfl⟩ : syracuseStep 2750189 = 1031321) (by norm_num)
theorem B2750213 : Blo 1831617 2750213 := bbase (se 4 (by rfl) ⟨257832, by rfl⟩ : syracuseStep 2750213 = 515665) (by norm_num)
theorem B2062093 : Blo 1831617 2062093 := bbase (se 3 (by rfl) ⟨386642, by rfl⟩ : syracuseStep 2062093 = 773285) (by norm_num)
theorem B6960917 : Blo 1831617 6960917 := bbase (se 6 (by rfl) ⟨163146, by rfl⟩ : syracuseStep 6960917 = 326293) (by norm_num)
theorem B2750237 : Blo 1831617 2750237 := bbase (se 3 (by rfl) ⟨515669, by rfl⟩ : syracuseStep 2750237 = 1031339) (by norm_num)
theorem B2062129 : Blo 1831617 2062129 := bbase (se 2 (by rfl) ⟨773298, by rfl⟩ : syracuseStep 2062129 = 1546597) (by norm_num)
theorem B2750261 : Blo 1831617 2750261 := bbase (se 5 (by rfl) ⟨128918, by rfl⟩ : syracuseStep 2750261 = 257837) (by norm_num)
theorem B3479365 : Blo 1831617 3479365 := bbase (se 4 (by rfl) ⟨326190, by rfl⟩ : syracuseStep 3479365 = 652381) (by norm_num)
theorem B2750285 : Blo 1831617 2750285 := bbase (se 3 (by rfl) ⟨515678, by rfl⟩ : syracuseStep 2750285 = 1031357) (by norm_num)
theorem B2062165 : Blo 1831617 2062165 := bbase (se 9 (by rfl) ⟨6041, by rfl⟩ : syracuseStep 2062165 = 12083) (by norm_num)
theorem B2750309 : Blo 1831617 2750309 := bbase (se 4 (by rfl) ⟨257841, by rfl⟩ : syracuseStep 2750309 = 515683) (by norm_num)
theorem B2062201 : Blo 1831617 2062201 := bbase (se 2 (by rfl) ⟨773325, by rfl⟩ : syracuseStep 2062201 = 1546651) (by norm_num)
theorem B2750333 : Blo 1831617 2750333 := bbase (se 3 (by rfl) ⟨515687, by rfl⟩ : syracuseStep 2750333 = 1031375) (by norm_num)
theorem B2750357 : Blo 1831617 2750357 := bbase (se 6 (by rfl) ⟨64461, by rfl⟩ : syracuseStep 2750357 = 128923) (by norm_num)
theorem B2062237 : Blo 1831617 2062237 := bbase (se 3 (by rfl) ⟨386669, by rfl⟩ : syracuseStep 2062237 = 773339) (by norm_num)
theorem B1857449 : Blo 1831617 1857449 := bbase (se 2 (by rfl) ⟨696543, by rfl⟩ : syracuseStep 1857449 = 1393087) (by norm_num)
theorem B2750381 : Blo 1831617 2750381 := bbase (se 3 (by rfl) ⟨515696, by rfl⟩ : syracuseStep 2750381 = 1031393) (by norm_num)
theorem B6182837 : Blo 1831617 6182837 := bbase (se 5 (by rfl) ⟨289820, by rfl⟩ : syracuseStep 6182837 = 579641) (by norm_num)
theorem B2062273 : Blo 1831617 2062273 := bbase (se 2 (by rfl) ⟨773352, by rfl⟩ : syracuseStep 2062273 = 1546705) (by norm_num)
theorem B2750405 : Blo 1831617 2750405 := bbase (se 4 (by rfl) ⟨257850, by rfl⟩ : syracuseStep 2750405 = 515701) (by norm_num)
theorem B2062309 : Blo 1831617 2062309 := bbase (se 4 (by rfl) ⟨193341, by rfl⟩ : syracuseStep 2062309 = 386683) (by norm_num)
theorem B11745269 : Blo 1831617 11745269 := bbase (se 5 (by rfl) ⟨550559, by rfl⟩ : syracuseStep 11745269 = 1101119) (by norm_num)
theorem B2062345 : Blo 1831617 2062345 := bbase (se 2 (by rfl) ⟨773379, by rfl⟩ : syracuseStep 2062345 = 1546759) (by norm_num)
theorem B2062381 : Blo 1831617 2062381 := bbase (se 3 (by rfl) ⟨386696, by rfl⟩ : syracuseStep 2062381 = 773393) (by norm_num)
theorem B5871685 : Blo 1831617 5871685 := bbase (se 4 (by rfl) ⟨550470, by rfl⟩ : syracuseStep 5871685 = 1100941) (by norm_num)
theorem B2062417 : Blo 1831617 2062417 := bbase (se 2 (by rfl) ⟨773406, by rfl⟩ : syracuseStep 2062417 = 1546813) (by norm_num)
theorem B3479669 : Blo 1831617 3479669 := bbase (se 5 (by rfl) ⟨163109, by rfl⟩ : syracuseStep 3479669 = 326219) (by norm_num)
theorem B2062453 : Blo 1831617 2062453 := bbase (se 5 (by rfl) ⟨96677, by rfl⟩ : syracuseStep 2062453 = 193355) (by norm_num)
theorem B2062489 : Blo 1831617 2062489 := bbase (se 2 (by rfl) ⟨773433, by rfl⟩ : syracuseStep 2062489 = 1546867) (by norm_num)
theorem B2062525 : Blo 1831617 2062525 := bbase (se 3 (by rfl) ⟨386723, by rfl⟩ : syracuseStep 2062525 = 773447) (by norm_num)
theorem B1857737 : Blo 1831617 1857737 := bbase (se 2 (by rfl) ⟨696651, by rfl⟩ : syracuseStep 1857737 = 1393303) (by norm_num)
theorem B2062561 : Blo 1831617 2062561 := bbase (se 2 (by rfl) ⟨773460, by rfl⟩ : syracuseStep 2062561 = 1546921) (by norm_num)
theorem B1956097 : Blo 1831617 1956097 := bbase (se 2 (by rfl) ⟨733536, by rfl⟩ : syracuseStep 1956097 = 1467073) (by norm_num)
theorem B2062597 : Blo 1831617 2062597 := bbase (se 4 (by rfl) ⟨193368, by rfl⟩ : syracuseStep 2062597 = 386737) (by norm_num)
theorem B2062633 : Blo 1831617 2062633 := bbase (se 2 (by rfl) ⟨773487, by rfl⟩ : syracuseStep 2062633 = 1546975) (by norm_num)
theorem B1956169 : Blo 1831617 1956169 := bbase (se 2 (by rfl) ⟨733563, by rfl⟩ : syracuseStep 1956169 = 1467127) (by norm_num)
theorem B2062669 : Blo 1831617 2062669 := bbase (se 3 (by rfl) ⟨386750, by rfl⟩ : syracuseStep 2062669 = 773501) (by norm_num)
theorem B6183269 : Blo 1831617 6183269 := bbase (se 4 (by rfl) ⟨579681, by rfl⟩ : syracuseStep 6183269 = 1159363) (by norm_num)
theorem B9279845 : Blo 1831617 9279845 := bbase (se 4 (by rfl) ⟨869985, by rfl⟩ : syracuseStep 9279845 = 1739971) (by norm_num)
theorem B2062705 : Blo 1831617 2062705 := bbase (se 2 (by rfl) ⟨773514, by rfl⟩ : syracuseStep 2062705 = 1547029) (by norm_num)
theorem B2062741 : Blo 1831617 2062741 := bbase (se 6 (by rfl) ⟨48345, by rfl⟩ : syracuseStep 2062741 = 96691) (by norm_num)
theorem B2062777 : Blo 1831617 2062777 := bbase (se 2 (by rfl) ⟨773541, by rfl⟩ : syracuseStep 2062777 = 1547083) (by norm_num)
theorem B5872085 : Blo 1831617 5872085 := bbase (se 7 (by rfl) ⟨68813, by rfl⟩ : syracuseStep 5872085 = 137627) (by norm_num)
theorem B2062813 : Blo 1831617 2062813 := bbase (se 3 (by rfl) ⟨386777, by rfl⟩ : syracuseStep 2062813 = 773555) (by norm_num)
theorem B1956349 : Blo 1831617 1956349 := bbase (se 3 (by rfl) ⟨366815, by rfl⟩ : syracuseStep 1956349 = 733631) (by norm_num)
theorem B2202113 : Blo 1831617 2202113 := bbase (se 2 (by rfl) ⟨825792, by rfl⟩ : syracuseStep 2202113 = 1651585) (by norm_num)
theorem B2202161 : Blo 1831617 2202161 := bbase (se 2 (by rfl) ⟨825810, by rfl⟩ : syracuseStep 2202161 = 1651621) (by norm_num)
theorem B3914381 : Blo 1831617 3914381 := bbase (se 3 (by rfl) ⟨733946, by rfl⟩ : syracuseStep 3914381 = 1467893) (by norm_num)
theorem B15866549 : Blo 1831617 15866549 := bbase (se 5 (by rfl) ⟨743744, by rfl⟩ : syracuseStep 15866549 = 1487489) (by norm_num)
theorem B6183701 : Blo 1831617 6183701 := bbase (se 6 (by rfl) ⟨144930, by rfl⟩ : syracuseStep 6183701 = 289861) (by norm_num)
theorem B3914525 : Blo 1831617 3914525 := bbase (se 3 (by rfl) ⟨733973, by rfl⟩ : syracuseStep 3914525 = 1467947) (by norm_num)
theorem B11139925 : Blo 1831617 11139925 := bbase (se 9 (by rfl) ⟨32636, by rfl⟩ : syracuseStep 11139925 = 65273) (by norm_num)
theorem B3480421 : Blo 1831617 3480421 := bbase (se 4 (by rfl) ⟨326289, by rfl⟩ : syracuseStep 3480421 = 652579) (by norm_num)
theorem B5651333 : Blo 1831617 5651333 := bbase (se 4 (by rfl) ⟨529812, by rfl⟩ : syracuseStep 5651333 = 1059625) (by norm_num)
theorem B11140021 : Blo 1831617 11140021 := bbase (se 5 (by rfl) ⟨522188, by rfl⟩ : syracuseStep 11140021 = 1044377) (by norm_num)
theorem B1956793 : Blo 1831617 1956793 := bbase (se 2 (by rfl) ⟨733797, by rfl⟩ : syracuseStep 1956793 = 1467595) (by norm_num)
theorem B4021229 : Blo 1831617 4021229 := bbase (se 3 (by rfl) ⟨753980, by rfl⟩ : syracuseStep 4021229 = 1507961) (by norm_num)
theorem B3480565 : Blo 1831617 3480565 := bbase (se 5 (by rfl) ⟨163151, by rfl⟩ : syracuseStep 3480565 = 326303) (by norm_num)
theorem B5217317 : Blo 1831617 5217317 := bbase (se 4 (by rfl) ⟨489123, by rfl⟩ : syracuseStep 5217317 = 978247) (by norm_num)
theorem B17611829 : Blo 1831617 17611829 := bbase (se 5 (by rfl) ⟨825554, by rfl⟩ : syracuseStep 17611829 = 1651109) (by norm_num)
theorem B1956917 : Blo 1831617 1956917 := bbase (se 5 (by rfl) ⟨91730, by rfl⟩ : syracuseStep 1956917 = 183461) (by norm_num)
theorem B2202709 : Blo 1831617 2202709 := bbase (se 8 (by rfl) ⟨12906, by rfl⟩ : syracuseStep 2202709 = 25813) (by norm_num)
theorem B3914885 : Blo 1831617 3914885 := bbase (se 4 (by rfl) ⟨367020, by rfl⟩ : syracuseStep 3914885 = 734041) (by norm_num)
theorem B3480725 : Blo 1831617 3480725 := bbase (se 6 (by rfl) ⟨81579, by rfl⟩ : syracuseStep 3480725 = 163159) (by norm_num)
theorem B2038937 : Blo 1831617 2038937 := bbase (se 2 (by rfl) ⟨764601, by rfl⟩ : syracuseStep 2038937 = 1529203) (by norm_num)
theorem B6184133 : Blo 1831617 6184133 := bbase (se 4 (by rfl) ⟨579762, by rfl⟩ : syracuseStep 6184133 = 1159525) (by norm_num)
theorem B3480869 : Blo 1831617 3480869 := bbase (se 4 (by rfl) ⟨326331, by rfl⟩ : syracuseStep 3480869 = 652663) (by norm_num)
theorem B1957169 : Blo 1831617 1957169 := bbase (se 2 (by rfl) ⟨733938, by rfl⟩ : syracuseStep 1957169 = 1467877) (by norm_num)
theorem B4702205 : Blo 1831617 4702205 := bbase (se 3 (by rfl) ⟨881663, by rfl⟩ : syracuseStep 4702205 = 1763327) (by norm_num)
theorem B3915773 : Blo 1831617 3915773 := bbase (se 3 (by rfl) ⟨734207, by rfl⟩ : syracuseStep 3915773 = 1468415) (by norm_num)
theorem B4832821 : Blo 1831617 4832821 := bbase (se 5 (by rfl) ⟨226538, by rfl⟩ : syracuseStep 4832821 = 453077) (by norm_num)
theorem B6184565 : Blo 1831617 6184565 := bbase (se 5 (by rfl) ⟨289901, by rfl⟩ : syracuseStep 6184565 = 579803) (by norm_num)
theorem B9281141 : Blo 1831617 9281141 := bbase (se 5 (by rfl) ⟨435053, by rfl⟩ : syracuseStep 9281141 = 870107) (by norm_num)
theorem B4636349 : Blo 1831617 4636349 := bbase (se 3 (by rfl) ⟨869315, by rfl⟩ : syracuseStep 4636349 = 1738631) (by norm_num)
theorem B7831237 : Blo 1831617 7831237 := bbase (se 4 (by rfl) ⟨734178, by rfl⟩ : syracuseStep 7831237 = 1468357) (by norm_num)
theorem B3301093 : Blo 1831617 3301093 := bbase (se 4 (by rfl) ⟨309477, by rfl⟩ : syracuseStep 3301093 = 618955) (by norm_num)
theorem B1957613 : Blo 1831617 1957613 := bbase (se 3 (by rfl) ⟨367052, by rfl⟩ : syracuseStep 1957613 = 734105) (by norm_num)
theorem B2416433 : Blo 1831617 2416433 := bbase (se 2 (by rfl) ⟨906162, by rfl⟩ : syracuseStep 2416433 = 1812325) (by norm_num)
theorem B2318149 : Blo 1831617 2318149 := bbase (se 4 (by rfl) ⟨217326, by rfl⟩ : syracuseStep 2318149 = 434653) (by norm_num)
theorem B4636541 : Blo 1831617 4636541 := bbase (se 3 (by rfl) ⟨869351, by rfl⟩ : syracuseStep 4636541 = 1738703) (by norm_num)
theorem B2383781 : Blo 1831617 2383781 := bbase (se 4 (by rfl) ⟨223479, by rfl⟩ : syracuseStep 2383781 = 446959) (by norm_num)
theorem B1957861 : Blo 1831617 1957861 := bbase (se 4 (by rfl) ⟨183549, by rfl⟩ : syracuseStep 1957861 = 367099) (by norm_num)
theorem B2318321 : Blo 1831617 2318321 := bbase (se 2 (by rfl) ⟨869370, by rfl⟩ : syracuseStep 2318321 = 1738741) (by norm_num)
theorem B3301411 : Blo 1831617 3301411 := bstep (se 1 (by rfl) ⟨2476058, by rfl⟩ : syracuseStep 3301411 = 4952117) B4952117
theorem B6955085 : Blo 1831617 6955085 := bstep (se 3 (by rfl) ⟨1304078, by rfl⟩ : syracuseStep 6955085 = 2608157) B2608157
theorem B11739269 : Blo 1831617 11739269 := bstep (se 4 (by rfl) ⟨1100556, by rfl⟩ : syracuseStep 11739269 = 2201113) B2201113
theorem B5218445 : Blo 1831617 5218445 := bstep (se 3 (by rfl) ⟨978458, by rfl⟩ : syracuseStep 5218445 = 1956917) B1956917
theorem B6185105 : Blo 1831617 6185105 := bstep (se 2 (by rfl) ⟨2319414, by rfl⟩ : syracuseStep 6185105 = 4638829) B4638829
theorem B2318483 : Blo 1831617 2318483 := bstep (se 1 (by rfl) ⟨1738862, by rfl⟩ : syracuseStep 2318483 = 3477725) B3477725
theorem B4636835 : Blo 1831617 4636835 := bstep (se 1 (by rfl) ⟨3477626, by rfl⟩ : syracuseStep 4636835 = 6955253) B6955253
theorem B5218627 : Blo 1831617 5218627 := bstep (se 1 (by rfl) ⟨3913970, by rfl⟩ : syracuseStep 5218627 = 7827941) B7827941
theorem B14868805 : Blo 1831617 14868805 := bstep (se 4 (by rfl) ⟨1393950, by rfl⟩ : syracuseStep 14868805 = 2787901) B2787901
theorem B4637027 : Blo 1831617 4637027 := bstep (se 1 (by rfl) ⟨3477770, by rfl⟩ : syracuseStep 4637027 = 6955541) B6955541
theorem B28590533 : Blo 1831617 28590533 := bstep (se 4 (by rfl) ⟨2680362, by rfl⟩ : syracuseStep 28590533 = 5360725) B5360725
theorem B13205987 : Blo 1831617 13205987 := bstep (se 1 (by rfl) ⟨9904490, by rfl⟩ : syracuseStep 13205987 = 19808981) B19808981
theorem B5022179 : Blo 1831617 5022179 := bstep (se 1 (by rfl) ⟨3766634, by rfl⟩ : syracuseStep 5022179 = 7533269) B7533269
theorem B5571107 : Blo 1831617 5571107 := bstep (se 1 (by rfl) ⟨4178330, by rfl⟩ : syracuseStep 5571107 = 8356661) B8356661
theorem B6185645 : Blo 1831617 6185645 := bstep (se 3 (by rfl) ⟨1159808, by rfl⟩ : syracuseStep 6185645 = 2319617) B2319617
theorem B4121297 : Blo 1831617 4121297 := bstep (se 2 (by rfl) ⟨1545486, by rfl⟩ : syracuseStep 4121297 = 3090973) B3090973
theorem B4121315 : Blo 1831617 4121315 := bstep (se 1 (by rfl) ⟨3090986, by rfl⟩ : syracuseStep 4121315 = 6181973) B6181973
theorem B6185699 : Blo 1831617 6185699 := bstep (se 1 (by rfl) ⟨4639274, by rfl⟩ : syracuseStep 6185699 = 9278549) B9278549
theorem B9282275 : Blo 1831617 9282275 := bstep (se 1 (by rfl) ⟨6961706, by rfl⟩ : syracuseStep 9282275 = 13923413) B13923413
theorem B5219117 : Blo 1831617 5219117 := bstep (se 3 (by rfl) ⟨978584, by rfl⟩ : syracuseStep 5219117 = 1957169) B1957169
theorem B21168965 : Blo 1831617 21168965 := bstep (se 4 (by rfl) ⟨1984590, by rfl⟩ : syracuseStep 21168965 = 3969181) B3969181
theorem B2319187 : Blo 1831617 2319187 := bstep (se 1 (by rfl) ⟨1739390, by rfl⟩ : syracuseStep 2319187 = 3478781) B3478781
theorem B4236131 : Blo 1831617 4236131 := bstep (se 1 (by rfl) ⟨3177098, by rfl⟩ : syracuseStep 4236131 = 6354197) B6354197
theorem B2319283 : Blo 1831617 2319283 := bstep (se 1 (by rfl) ⟨1739462, by rfl⟩ : syracuseStep 2319283 = 3478925) B3478925
theorem B4178915 : Blo 1831617 4178915 := bstep (se 1 (by rfl) ⟨3134186, by rfl⟩ : syracuseStep 4178915 = 6268373) B6268373
theorem B4121585 : Blo 1831617 4121585 := bstep (se 2 (by rfl) ⟨1545594, by rfl⟩ : syracuseStep 4121585 = 3091189) B3091189
theorem B6185969 : Blo 1831617 6185969 := bstep (se 2 (by rfl) ⟨2319738, by rfl⟩ : syracuseStep 6185969 = 4639477) B4639477
theorem B4121603 : Blo 1831617 4121603 := bstep (se 1 (by rfl) ⟨3091202, by rfl⟩ : syracuseStep 4121603 = 6182405) B6182405
theorem B10437731 : Blo 1831617 10437731 := bstep (se 1 (by rfl) ⟨7828298, by rfl⟩ : syracuseStep 10437731 = 15656597) B15656597
theorem B14853233 : Blo 1831617 14853233 := bstep (se 2 (by rfl) ⟨5569962, by rfl⟩ : syracuseStep 14853233 = 11139925) B11139925
theorem B2933921 : Blo 1831617 2933921 := bstep (se 2 (by rfl) ⟨1100220, by rfl⟩ : syracuseStep 2933921 = 2200441) B2200441
theorem B17605829 : Blo 1831617 17605829 := bstep (se 4 (by rfl) ⟨1650546, by rfl⟩ : syracuseStep 17605829 = 3301093) B3301093
theorem B9045233 : Blo 1831617 9045233 := bstep (se 2 (by rfl) ⟨3391962, by rfl⟩ : syracuseStep 9045233 = 6783925) B6783925
theorem B4121873 : Blo 1831617 4121873 := bstep (se 2 (by rfl) ⟨1545702, by rfl⟩ : syracuseStep 4121873 = 3091405) B3091405
theorem B4637969 : Blo 1831617 4637969 := bstep (se 2 (by rfl) ⟨1739238, by rfl⟩ : syracuseStep 4637969 = 3478477) B3478477
theorem B2934049 : Blo 1831617 2934049 := bstep (se 2 (by rfl) ⟨1100268, by rfl⟩ : syracuseStep 2934049 = 2200537) B2200537
theorem B4121891 : Blo 1831617 4121891 := bstep (se 1 (by rfl) ⟨3091418, by rfl⟩ : syracuseStep 4121891 = 6182837) B6182837
theorem B4638019 : Blo 1831617 4638019 := bstep (se 1 (by rfl) ⟨3478514, by rfl⟩ : syracuseStep 4638019 = 6957029) B6957029
theorem B13206883 : Blo 1831617 13206883 := bstep (se 1 (by rfl) ⟨9905162, by rfl⟩ : syracuseStep 13206883 = 19810325) B19810325
theorem B2319779 : Blo 1831617 2319779 := bstep (se 1 (by rfl) ⟨1739834, by rfl⟩ : syracuseStep 2319779 = 3479669) B3479669
theorem B4638161 : Blo 1831617 4638161 := bstep (se 2 (by rfl) ⟨1739310, by rfl⟩ : syracuseStep 4638161 = 3478621) B3478621
theorem B15648227 : Blo 1831617 15648227 := bstep (se 1 (by rfl) ⟨11736170, by rfl⟩ : syracuseStep 15648227 = 23472341) B23472341
theorem B2786819 : Blo 1831617 2786819 := bstep (se 1 (by rfl) ⟨2090114, by rfl⟩ : syracuseStep 2786819 = 4180229) B4180229
theorem B6186509 : Blo 1831617 6186509 := bstep (se 3 (by rfl) ⟨1159970, by rfl⟩ : syracuseStep 6186509 = 2319941) B2319941
theorem B4122161 : Blo 1831617 4122161 := bstep (se 2 (by rfl) ⟨1545810, by rfl⟩ : syracuseStep 4122161 = 3091621) B3091621
theorem B4122179 : Blo 1831617 4122179 := bstep (se 1 (by rfl) ⟨3091634, by rfl⟩ : syracuseStep 4122179 = 6183269) B6183269
theorem B6186563 : Blo 1831617 6186563 := bstep (se 1 (by rfl) ⟨4639922, by rfl⟩ : syracuseStep 6186563 = 9279845) B9279845
theorem B4703825 : Blo 1831617 4703825 := bstep (se 2 (by rfl) ⟨1763934, by rfl⟩ : syracuseStep 4703825 = 3527869) B3527869
theorem B13911749 : Blo 1831617 13911749 := bstep (se 4 (by rfl) ⟨1304226, by rfl⟩ : syracuseStep 13911749 = 2608453) B2608453
theorem B11142947 : Blo 1831617 11142947 := bstep (se 1 (by rfl) ⟨8357210, by rfl⟩ : syracuseStep 11142947 = 16714421) B16714421
theorem B10577699 : Blo 1831617 10577699 := bstep (se 1 (by rfl) ⟨7933274, by rfl⟩ : syracuseStep 10577699 = 15866549) B15866549
theorem B4122449 : Blo 1831617 4122449 := bstep (se 2 (by rfl) ⟨1545918, by rfl⟩ : syracuseStep 4122449 = 3091837) B3091837
theorem B6186833 : Blo 1831617 6186833 := bstep (se 2 (by rfl) ⟨2320062, by rfl⟩ : syracuseStep 6186833 = 4640125) B4640125
theorem B4122467 : Blo 1831617 4122467 := bstep (se 1 (by rfl) ⟨3091850, by rfl⟩ : syracuseStep 4122467 = 6183701) B6183701
theorem B5220301 : Blo 1831617 5220301 := bstep (se 3 (by rfl) ⟨978806, by rfl⟩ : syracuseStep 5220301 = 1957613) B1957613
theorem B5359601 : Blo 1831617 5359601 := bstep (se 2 (by rfl) ⟨2009850, by rfl⟩ : syracuseStep 5359601 = 4019701) B4019701
theorem B2680819 : Blo 1831617 2680819 := bstep (se 1 (by rfl) ⟨2010614, by rfl⟩ : syracuseStep 2680819 = 4021229) B4021229
theorem B12060707 : Blo 1831617 12060707 := bstep (se 1 (by rfl) ⟨9045530, by rfl⟩ : syracuseStep 12060707 = 18091061) B18091061
theorem B11741219 : Blo 1831617 11741219 := bstep (se 1 (by rfl) ⟨8805914, by rfl⟩ : syracuseStep 11741219 = 17611829) B17611829
theorem B10438733 : Blo 1831617 10438733 := bstep (se 3 (by rfl) ⟨1957262, by rfl⟩ : syracuseStep 10438733 = 3914525) B3914525
theorem B2320483 : Blo 1831617 2320483 := bstep (se 1 (by rfl) ⟨1740362, by rfl⟩ : syracuseStep 2320483 = 3480725) B3480725
theorem B4122737 : Blo 1831617 4122737 := bstep (se 2 (by rfl) ⟨1546026, by rfl⟩ : syracuseStep 4122737 = 3092053) B3092053
theorem B4122755 : Blo 1831617 4122755 := bstep (se 1 (by rfl) ⟨3092066, by rfl⟩ : syracuseStep 4122755 = 6184133) B6184133
theorem B6957197 : Blo 1831617 6957197 := bstep (se 3 (by rfl) ⟨1304474, by rfl⟩ : syracuseStep 6957197 = 2608949) B2608949
theorem B2320579 : Blo 1831617 2320579 := bstep (se 1 (by rfl) ⟨1740434, by rfl⟩ : syracuseStep 2320579 = 3480869) B3480869
theorem B9275633 : Blo 1831617 9275633 := bstep (se 2 (by rfl) ⟨3478362, by rfl⟩ : syracuseStep 9275633 = 6956725) B6956725
theorem B13920497 : Blo 1831617 13920497 := bstep (se 2 (by rfl) ⟨5220186, by rfl⟩ : syracuseStep 13920497 = 10440373) B10440373
theorem B6187373 : Blo 1831617 6187373 := bstep (se 3 (by rfl) ⟨1160132, by rfl⟩ : syracuseStep 6187373 = 2320265) B2320265
theorem B7825805 : Blo 1831617 7825805 := bstep (se 3 (by rfl) ⟨1467338, by rfl⟩ : syracuseStep 7825805 = 2934677) B2934677
theorem B18811277 : Blo 1831617 18811277 := bstep (se 3 (by rfl) ⟨3527114, by rfl⟩ : syracuseStep 18811277 = 7054229) B7054229
theorem B4123025 : Blo 1831617 4123025 := bstep (se 2 (by rfl) ⟨1546134, by rfl⟩ : syracuseStep 4123025 = 3092269) B3092269
theorem B4123043 : Blo 1831617 4123043 := bstep (se 1 (by rfl) ⟨3092282, by rfl⟩ : syracuseStep 4123043 = 6184565) B6184565
theorem B6187427 : Blo 1831617 6187427 := bstep (se 1 (by rfl) ⟨4640570, by rfl⟩ : syracuseStep 6187427 = 9281141) B9281141
theorem B3090865 : Blo 1831617 3090865 := bstep (se 2 (by rfl) ⟨1159074, by rfl⟩ : syracuseStep 3090865 = 2318149) B2318149
theorem B4639153 : Blo 1831617 4639153 := bstep (se 2 (by rfl) ⟨1739682, by rfl⟩ : syracuseStep 4639153 = 3479365) B3479365
theorem B3090899 : Blo 1831617 3090899 := bstep (se 1 (by rfl) ⟨2318174, by rfl⟩ : syracuseStep 3090899 = 4636349) B4636349
theorem B7432717 : Blo 1831617 7432717 := bstep (se 3 (by rfl) ⟨1393634, by rfl⟩ : syracuseStep 7432717 = 2787269) B2787269
theorem B3967537 : Blo 1831617 3967537 := bstep (se 2 (by rfl) ⟨1487826, by rfl⟩ : syracuseStep 3967537 = 2975653) B2975653
theorem B3091027 : Blo 1831617 3091027 := bstep (se 1 (by rfl) ⟨2318270, by rfl⟩ : syracuseStep 3091027 = 4636541) B4636541
theorem B4123313 : Blo 1831617 4123313 := bstep (se 2 (by rfl) ⟨1546242, by rfl⟩ : syracuseStep 4123313 = 3092485) B3092485
theorem B6187697 : Blo 1831617 6187697 := bstep (se 2 (by rfl) ⟨2320386, by rfl⟩ : syracuseStep 6187697 = 4640773) B4640773
theorem B5868227 : Blo 1831617 5868227 := bstep (se 1 (by rfl) ⟨4401170, by rfl⟩ : syracuseStep 5868227 = 8802341) B8802341
theorem B4123331 : Blo 1831617 4123331 := bstep (se 1 (by rfl) ⟨3092498, by rfl⟩ : syracuseStep 4123331 = 6184997) B6184997
theorem B4639427 : Blo 1831617 4639427 := bstep (se 1 (by rfl) ⟨3479570, by rfl⟩ : syracuseStep 4639427 = 6959141) B6959141
theorem B3091169 : Blo 1831617 3091169 := bstep (se 2 (by rfl) ⟨1159188, by rfl⟩ : syracuseStep 3091169 = 2318377) B2318377
theorem B3091297 : Blo 1831617 3091297 := bstep (se 2 (by rfl) ⟨1159236, by rfl⟩ : syracuseStep 3091297 = 2318473) B2318473
theorem B3091331 : Blo 1831617 3091331 := bstep (se 1 (by rfl) ⟨2318498, by rfl⟩ : syracuseStep 3091331 = 4636997) B4636997
theorem B4639619 : Blo 1831617 4639619 := bstep (se 1 (by rfl) ⟨3479714, by rfl⟩ : syracuseStep 4639619 = 6959429) B6959429
theorem B9907085 : Blo 1831617 9907085 := bstep (se 3 (by rfl) ⟨1857578, by rfl⟩ : syracuseStep 9907085 = 3715157) B3715157
theorem B8809357 : Blo 1831617 8809357 := bstep (se 3 (by rfl) ⟨1651754, by rfl⟩ : syracuseStep 8809357 = 3303509) B3303509
theorem B6958001 : Blo 1831617 6958001 := bstep (se 2 (by rfl) ⟨2609250, by rfl⟩ : syracuseStep 6958001 = 5218501) B5218501
theorem B4123601 : Blo 1831617 4123601 := bstep (se 2 (by rfl) ⟨1546350, by rfl⟩ : syracuseStep 4123601 = 3092701) B3092701
theorem B4123619 : Blo 1831617 4123619 := bstep (se 1 (by rfl) ⟨3092714, by rfl⟩ : syracuseStep 4123619 = 6185429) B6185429
theorem B5221361 : Blo 1831617 5221361 := bstep (se 2 (by rfl) ⟨1958010, by rfl⟩ : syracuseStep 5221361 = 3916021) B3916021
theorem B2608129 : Blo 1831617 2608129 := bstep (se 2 (by rfl) ⟨978048, by rfl⟩ : syracuseStep 2608129 = 1956097) B1956097
theorem B3091459 : Blo 1831617 3091459 := bstep (se 1 (by rfl) ⟨2318594, by rfl⟩ : syracuseStep 3091459 = 4637189) B4637189
theorem B4951057 : Blo 1831617 4951057 := bstep (se 2 (by rfl) ⟨1856646, by rfl⟩ : syracuseStep 4951057 = 3713293) B3713293
theorem B2747441 : Blo 1831617 2747441 := bstep (se 2 (by rfl) ⟨1030290, by rfl⟩ : syracuseStep 2747441 = 2060581) B2060581
theorem B2747459 : Blo 1831617 2747459 := bstep (se 1 (by rfl) ⟨2060594, by rfl⟩ : syracuseStep 2747459 = 4121189) B4121189
theorem B2747489 : Blo 1831617 2747489 := bstep (se 2 (by rfl) ⟨1030308, by rfl⟩ : syracuseStep 2747489 = 2060617) B2060617
theorem B2747507 : Blo 1831617 2747507 := bstep (se 1 (by rfl) ⟨2060630, by rfl⟩ : syracuseStep 2747507 = 4121261) B4121261
theorem B2747537 : Blo 1831617 2747537 := bstep (se 2 (by rfl) ⟨1030326, by rfl⟩ : syracuseStep 2747537 = 2060653) B2060653
theorem B3091601 : Blo 1831617 3091601 := bstep (se 2 (by rfl) ⟨1159350, by rfl⟩ : syracuseStep 3091601 = 2318701) B2318701
theorem B2747555 : Blo 1831617 2747555 := bstep (se 1 (by rfl) ⟨2060666, by rfl⟩ : syracuseStep 2747555 = 4121333) B4121333
theorem B2747585 : Blo 1831617 2747585 := bstep (se 2 (by rfl) ⟨1030344, by rfl⟩ : syracuseStep 2747585 = 2060689) B2060689
theorem B6188237 : Blo 1831617 6188237 := bstep (se 3 (by rfl) ⟨1160294, by rfl⟩ : syracuseStep 6188237 = 2320589) B2320589
theorem B2747603 : Blo 1831617 2747603 := bstep (se 1 (by rfl) ⟨2060702, by rfl⟩ : syracuseStep 2747603 = 4121405) B4121405
theorem B10726627 : Blo 1831617 10726627 := bstep (se 1 (by rfl) ⟨8044970, by rfl⟩ : syracuseStep 10726627 = 16089941) B16089941
theorem B2747633 : Blo 1831617 2747633 := bstep (se 2 (by rfl) ⟨1030362, by rfl⟩ : syracuseStep 2747633 = 2060725) B2060725
theorem B4123889 : Blo 1831617 4123889 := bstep (se 2 (by rfl) ⟨1546458, by rfl⟩ : syracuseStep 4123889 = 3092917) B3092917
theorem B2747651 : Blo 1831617 2747651 := bstep (se 1 (by rfl) ⟨2060738, by rfl⟩ : syracuseStep 2747651 = 4121477) B4121477
theorem B4123907 : Blo 1831617 4123907 := bstep (se 1 (by rfl) ⟨3092930, by rfl⟩ : syracuseStep 4123907 = 6185861) B6185861
theorem B6188291 : Blo 1831617 6188291 := bstep (se 1 (by rfl) ⟨4641218, by rfl⟩ : syracuseStep 6188291 = 9282437) B9282437
theorem B14855437 : Blo 1831617 14855437 := bstep (se 3 (by rfl) ⟨2785394, by rfl⟩ : syracuseStep 14855437 = 5570789) B5570789
theorem B3091729 : Blo 1831617 3091729 := bstep (se 2 (by rfl) ⟨1159398, by rfl⟩ : syracuseStep 3091729 = 2318797) B2318797
theorem B2747681 : Blo 1831617 2747681 := bstep (se 2 (by rfl) ⟨1030380, by rfl⟩ : syracuseStep 2747681 = 2060761) B2060761
theorem B2936099 : Blo 1831617 2936099 := bstep (se 1 (by rfl) ⟨2202074, by rfl⟩ : syracuseStep 2936099 = 4404149) B4404149
theorem B2747699 : Blo 1831617 2747699 := bstep (se 1 (by rfl) ⟨2060774, by rfl⟩ : syracuseStep 2747699 = 4121549) B4121549
theorem B3091763 : Blo 1831617 3091763 := bstep (se 1 (by rfl) ⟨2318822, by rfl⟩ : syracuseStep 3091763 = 4637645) B4637645
theorem B2747729 : Blo 1831617 2747729 := bstep (se 2 (by rfl) ⟨1030398, by rfl⟩ : syracuseStep 2747729 = 2060797) B2060797
theorem B2608465 : Blo 1831617 2608465 := bstep (se 2 (by rfl) ⟨978174, by rfl⟩ : syracuseStep 2608465 = 1956349) B1956349
theorem B2747747 : Blo 1831617 2747747 := bstep (se 1 (by rfl) ⟨2060810, by rfl⟩ : syracuseStep 2747747 = 4121621) B4121621
theorem B2747777 : Blo 1831617 2747777 := bstep (se 2 (by rfl) ⟨1030416, by rfl⟩ : syracuseStep 2747777 = 2060833) B2060833
theorem B2747795 : Blo 1831617 2747795 := bstep (se 1 (by rfl) ⟨2060846, by rfl⟩ : syracuseStep 2747795 = 4121693) B4121693
theorem B3968419 : Blo 1831617 3968419 := bstep (se 1 (by rfl) ⟨2976314, by rfl⟩ : syracuseStep 3968419 = 5952629) B5952629
theorem B2747825 : Blo 1831617 2747825 := bstep (se 2 (by rfl) ⟨1030434, by rfl⟩ : syracuseStep 2747825 = 2060869) B2060869
theorem B3091891 : Blo 1831617 3091891 := bstep (se 1 (by rfl) ⟨2318918, by rfl⟩ : syracuseStep 3091891 = 4637837) B4637837
theorem B2747843 : Blo 1831617 2747843 := bstep (se 1 (by rfl) ⟨2060882, by rfl⟩ : syracuseStep 2747843 = 4121765) B4121765
theorem B2747873 : Blo 1831617 2747873 := bstep (se 2 (by rfl) ⟨1030452, by rfl⟩ : syracuseStep 2747873 = 2060905) B2060905
theorem B2747891 : Blo 1831617 2747891 := bstep (se 1 (by rfl) ⟨2060918, by rfl⟩ : syracuseStep 2747891 = 4121837) B4121837
theorem B2747921 : Blo 1831617 2747921 := bstep (se 2 (by rfl) ⟨1030470, by rfl⟩ : syracuseStep 2747921 = 2060941) B2060941
theorem B4124177 : Blo 1831617 4124177 := bstep (se 2 (by rfl) ⟨1546566, by rfl⟩ : syracuseStep 4124177 = 3093133) B3093133
theorem B2747939 : Blo 1831617 2747939 := bstep (se 1 (by rfl) ⟨2060954, by rfl⟩ : syracuseStep 2747939 = 4121909) B4121909
theorem B4124195 : Blo 1831617 4124195 := bstep (se 1 (by rfl) ⟨3093146, by rfl⟩ : syracuseStep 4124195 = 6186293) B6186293
theorem B2747969 : Blo 1831617 2747969 := bstep (se 2 (by rfl) ⟨1030488, by rfl⟩ : syracuseStep 2747969 = 2060977) B2060977
theorem B3092033 : Blo 1831617 3092033 := bstep (se 2 (by rfl) ⟨1159512, by rfl⟩ : syracuseStep 3092033 = 2319025) B2319025
theorem B6958669 : Blo 1831617 6958669 := bstep (se 3 (by rfl) ⟨1304750, by rfl⟩ : syracuseStep 6958669 = 2609501) B2609501
theorem B2747987 : Blo 1831617 2747987 := bstep (se 1 (by rfl) ⟨2060990, by rfl⟩ : syracuseStep 2747987 = 4121981) B4121981
theorem B2748017 : Blo 1831617 2748017 := bstep (se 2 (by rfl) ⟨1030506, by rfl⟩ : syracuseStep 2748017 = 2061013) B2061013
theorem B2748035 : Blo 1831617 2748035 := bstep (se 1 (by rfl) ⟨2061026, by rfl⟩ : syracuseStep 2748035 = 4122053) B4122053
theorem B2748065 : Blo 1831617 2748065 := bstep (se 2 (by rfl) ⟨1030524, by rfl⟩ : syracuseStep 2748065 = 2061049) B2061049
theorem B9277091 : Blo 1831617 9277091 := bstep (se 1 (by rfl) ⟨6957818, by rfl⟩ : syracuseStep 9277091 = 13915637) B13915637
theorem B2748083 : Blo 1831617 2748083 := bstep (se 1 (by rfl) ⟨2061062, by rfl⟩ : syracuseStep 2748083 = 4122125) B4122125
theorem B3092161 : Blo 1831617 3092161 := bstep (se 2 (by rfl) ⟨1159560, by rfl⟩ : syracuseStep 3092161 = 2319121) B2319121
theorem B2748113 : Blo 1831617 2748113 := bstep (se 2 (by rfl) ⟨1030542, by rfl⟩ : syracuseStep 2748113 = 2061085) B2061085
theorem B2748131 : Blo 1831617 2748131 := bstep (se 1 (by rfl) ⟨2061098, by rfl⟩ : syracuseStep 2748131 = 4122197) B4122197
theorem B3092195 : Blo 1831617 3092195 := bstep (se 1 (by rfl) ⟨2319146, by rfl⟩ : syracuseStep 3092195 = 4638293) B4638293
theorem B2748161 : Blo 1831617 2748161 := bstep (se 2 (by rfl) ⟨1030560, by rfl⟩ : syracuseStep 2748161 = 2061121) B2061121
theorem B2748179 : Blo 1831617 2748179 := bstep (se 1 (by rfl) ⟨2061134, by rfl⟩ : syracuseStep 2748179 = 4122269) B4122269
theorem B2748209 : Blo 1831617 2748209 := bstep (se 2 (by rfl) ⟨1030578, by rfl⟩ : syracuseStep 2748209 = 2061157) B2061157
theorem B4124465 : Blo 1831617 4124465 := bstep (se 2 (by rfl) ⟨1546674, by rfl⟩ : syracuseStep 4124465 = 3093349) B3093349
theorem B4640561 : Blo 1831617 4640561 := bstep (se 2 (by rfl) ⟨1740210, by rfl⟩ : syracuseStep 4640561 = 3480421) B3480421
theorem B2748227 : Blo 1831617 2748227 := bstep (se 1 (by rfl) ⟨2061170, by rfl⟩ : syracuseStep 2748227 = 4122341) B4122341
theorem B4124483 : Blo 1831617 4124483 := bstep (se 1 (by rfl) ⟨3093362, by rfl⟩ : syracuseStep 4124483 = 6186725) B6186725
theorem B2748257 : Blo 1831617 2748257 := bstep (se 2 (by rfl) ⟨1030596, by rfl⟩ : syracuseStep 2748257 = 2061193) B2061193
theorem B3092323 : Blo 1831617 3092323 := bstep (se 1 (by rfl) ⟨2319242, by rfl⟩ : syracuseStep 3092323 = 4638485) B4638485
theorem B4640611 : Blo 1831617 4640611 := bstep (se 1 (by rfl) ⟨3480458, by rfl⟩ : syracuseStep 4640611 = 6960917) B6960917
theorem B2748275 : Blo 1831617 2748275 := bstep (se 1 (by rfl) ⟨2061206, by rfl⟩ : syracuseStep 2748275 = 4122413) B4122413
theorem B2748305 : Blo 1831617 2748305 := bstep (se 2 (by rfl) ⟨1030614, by rfl⟩ : syracuseStep 2748305 = 2061229) B2061229
theorem B2609057 : Blo 1831617 2609057 := bstep (se 2 (by rfl) ⟨978396, by rfl⟩ : syracuseStep 2609057 = 1956793) B1956793
theorem B2748323 : Blo 1831617 2748323 := bstep (se 1 (by rfl) ⟨2061242, by rfl⟩ : syracuseStep 2748323 = 4122485) B4122485
theorem B2748353 : Blo 1831617 2748353 := bstep (se 2 (by rfl) ⟨1030632, by rfl⟩ : syracuseStep 2748353 = 2061265) B2061265
theorem B2748371 : Blo 1831617 2748371 := bstep (se 1 (by rfl) ⟨2061278, by rfl⟩ : syracuseStep 2748371 = 4122557) B4122557
theorem B2748401 : Blo 1831617 2748401 := bstep (se 2 (by rfl) ⟨1030650, by rfl⟩ : syracuseStep 2748401 = 2061301) B2061301
theorem B3092465 : Blo 1831617 3092465 := bstep (se 2 (by rfl) ⟨1159674, by rfl⟩ : syracuseStep 3092465 = 2319349) B2319349
theorem B4640753 : Blo 1831617 4640753 := bstep (se 2 (by rfl) ⟨1740282, by rfl⟩ : syracuseStep 4640753 = 3480565) B3480565
theorem B2748419 : Blo 1831617 2748419 := bstep (se 1 (by rfl) ⟨2061314, by rfl⟩ : syracuseStep 2748419 = 4122629) B4122629
theorem B2748449 : Blo 1831617 2748449 := bstep (se 2 (by rfl) ⟨1030668, by rfl⟩ : syracuseStep 2748449 = 2061337) B2061337
theorem B11907107 : Blo 1831617 11907107 := bstep (se 1 (by rfl) ⟨8930330, by rfl⟩ : syracuseStep 11907107 = 17860661) B17860661
theorem B2748467 : Blo 1831617 2748467 := bstep (se 1 (by rfl) ⟨2061350, by rfl⟩ : syracuseStep 2748467 = 4122701) B4122701
theorem B2748497 : Blo 1831617 2748497 := bstep (se 2 (by rfl) ⟨1030686, by rfl⟩ : syracuseStep 2748497 = 2061373) B2061373
theorem B4124753 : Blo 1831617 4124753 := bstep (se 2 (by rfl) ⟨1546782, by rfl⟩ : syracuseStep 4124753 = 3093565) B3093565
theorem B2748515 : Blo 1831617 2748515 := bstep (se 1 (by rfl) ⟨2061386, by rfl⟩ : syracuseStep 2748515 = 4122773) B4122773
theorem B4124771 : Blo 1831617 4124771 := bstep (se 1 (by rfl) ⟨3093578, by rfl⟩ : syracuseStep 4124771 = 6187157) B6187157
theorem B3092593 : Blo 1831617 3092593 := bstep (se 2 (by rfl) ⟨1159722, by rfl⟩ : syracuseStep 3092593 = 2319445) B2319445
theorem B2936945 : Blo 1831617 2936945 := bstep (se 2 (by rfl) ⟨1101354, by rfl⟩ : syracuseStep 2936945 = 2202709) B2202709
theorem B2748545 : Blo 1831617 2748545 := bstep (se 2 (by rfl) ⟨1030704, by rfl⟩ : syracuseStep 2748545 = 2061409) B2061409
theorem B3477649 : Blo 1831617 3477649 := bstep (se 2 (by rfl) ⟨1304118, by rfl⟩ : syracuseStep 3477649 = 2608237) B2608237
theorem B2748563 : Blo 1831617 2748563 := bstep (se 1 (by rfl) ⟨2061422, by rfl⟩ : syracuseStep 2748563 = 4122845) B4122845
theorem B3092627 : Blo 1831617 3092627 := bstep (se 1 (by rfl) ⟨2319470, by rfl⟩ : syracuseStep 3092627 = 4638941) B4638941
theorem B2748593 : Blo 1831617 2748593 := bstep (se 2 (by rfl) ⟨1030722, by rfl⟩ : syracuseStep 2748593 = 2061445) B2061445
theorem B2748611 : Blo 1831617 2748611 := bstep (se 1 (by rfl) ⟨2061458, by rfl⟩ : syracuseStep 2748611 = 4122917) B4122917
theorem B2748641 : Blo 1831617 2748641 := bstep (se 2 (by rfl) ⟨1030740, by rfl⟩ : syracuseStep 2748641 = 2061481) B2061481
theorem B7434467 : Blo 1831617 7434467 := bstep (se 1 (by rfl) ⟨5575850, by rfl⟩ : syracuseStep 7434467 = 11151701) B11151701
theorem B2748659 : Blo 1831617 2748659 := bstep (se 1 (by rfl) ⟨2061494, by rfl⟩ : syracuseStep 2748659 = 4122989) B4122989
theorem B4952333 : Blo 1831617 4952333 := bstep (se 3 (by rfl) ⟨928562, by rfl⟩ : syracuseStep 4952333 = 1857125) B1857125
theorem B2748689 : Blo 1831617 2748689 := bstep (se 2 (by rfl) ⟨1030758, by rfl⟩ : syracuseStep 2748689 = 2061517) B2061517
theorem B3092755 : Blo 1831617 3092755 := bstep (se 1 (by rfl) ⟨2319566, by rfl⟩ : syracuseStep 3092755 = 4639133) B4639133
theorem B2748707 : Blo 1831617 2748707 := bstep (se 1 (by rfl) ⟨2061530, by rfl⟩ : syracuseStep 2748707 = 4123061) B4123061
theorem B3477809 : Blo 1831617 3477809 := bstep (se 2 (by rfl) ⟨1304178, by rfl⟩ : syracuseStep 3477809 = 2608357) B2608357
theorem B2748737 : Blo 1831617 2748737 := bstep (se 2 (by rfl) ⟨1030776, by rfl⟩ : syracuseStep 2748737 = 2061553) B2061553
theorem B5288269 : Blo 1831617 5288269 := bstep (se 3 (by rfl) ⟨991550, by rfl⟩ : syracuseStep 5288269 = 1983101) B1983101
theorem B2748755 : Blo 1831617 2748755 := bstep (se 1 (by rfl) ⟨2061566, by rfl⟩ : syracuseStep 2748755 = 4123133) B4123133
theorem B6959459 : Blo 1831617 6959459 := bstep (se 1 (by rfl) ⟨5219594, by rfl⟩ : syracuseStep 6959459 = 10439189) B10439189
theorem B2748785 : Blo 1831617 2748785 := bstep (se 2 (by rfl) ⟨1030794, by rfl⟩ : syracuseStep 2748785 = 2061589) B2061589
theorem B4125041 : Blo 1831617 4125041 := bstep (se 2 (by rfl) ⟨1546890, by rfl⟩ : syracuseStep 4125041 = 3093781) B3093781
theorem B2748803 : Blo 1831617 2748803 := bstep (se 1 (by rfl) ⟨2061602, by rfl⟩ : syracuseStep 2748803 = 4123205) B4123205
theorem B4125059 : Blo 1831617 4125059 := bstep (se 1 (by rfl) ⟨3093794, by rfl⟩ : syracuseStep 4125059 = 6187589) B6187589
theorem B10432901 : Blo 1831617 10432901 := bstep (se 4 (by rfl) ⟨978084, by rfl⟩ : syracuseStep 10432901 = 1956169) B1956169
theorem B2748833 : Blo 1831617 2748833 := bstep (se 2 (by rfl) ⟨1030812, by rfl⟩ : syracuseStep 2748833 = 2061625) B2061625
theorem B3092897 : Blo 1831617 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B2060707 : Blo 1831617 2060707 := bstep (se 1 (by rfl) ⟨1545530, by rfl⟩ : syracuseStep 2060707 = 3091061) B3091061
theorem B2748851 : Blo 1831617 2748851 := bstep (se 1 (by rfl) ⟨2061638, by rfl⟩ : syracuseStep 2748851 = 4123277) B4123277
theorem B2609587 : Blo 1831617 2609587 := bstep (se 1 (by rfl) ⟨1957190, by rfl⟩ : syracuseStep 2609587 = 3914381) B3914381
theorem B9277901 : Blo 1831617 9277901 := bstep (se 3 (by rfl) ⟨1739606, by rfl⟩ : syracuseStep 9277901 = 3479213) B3479213
theorem B2748881 : Blo 1831617 2748881 := bstep (se 2 (by rfl) ⟨1030830, by rfl⟩ : syracuseStep 2748881 = 2061661) B2061661
theorem B2748899 : Blo 1831617 2748899 := bstep (se 1 (by rfl) ⟨2061674, by rfl⟩ : syracuseStep 2748899 = 4123349) B4123349
theorem B2748929 : Blo 1831617 2748929 := bstep (se 2 (by rfl) ⟨1030848, by rfl⟩ : syracuseStep 2748929 = 2061697) B2061697
theorem B2748947 : Blo 1831617 2748947 := bstep (se 1 (by rfl) ⟨2061710, by rfl⟩ : syracuseStep 2748947 = 4123421) B4123421
theorem B3093025 : Blo 1831617 3093025 := bstep (se 2 (by rfl) ⟨1159884, by rfl⟩ : syracuseStep 3093025 = 2319769) B2319769
theorem B2748977 : Blo 1831617 2748977 := bstep (se 2 (by rfl) ⟨1030866, by rfl⟩ : syracuseStep 2748977 = 2061733) B2061733
theorem B2060851 : Blo 1831617 2060851 := bstep (se 1 (by rfl) ⟨1545638, by rfl⟩ : syracuseStep 2060851 = 3091277) B3091277
theorem B2748995 : Blo 1831617 2748995 := bstep (se 1 (by rfl) ⟨2061746, by rfl⟩ : syracuseStep 2748995 = 4123493) B4123493
theorem B3093059 : Blo 1831617 3093059 := bstep (se 1 (by rfl) ⟨2319794, by rfl⟩ : syracuseStep 3093059 = 4639589) B4639589
theorem B2749025 : Blo 1831617 2749025 := bstep (se 2 (by rfl) ⟨1030884, by rfl⟩ : syracuseStep 2749025 = 2061769) B2061769
theorem B2749043 : Blo 1831617 2749043 := bstep (se 1 (by rfl) ⟨2061782, by rfl⟩ : syracuseStep 2749043 = 4123565) B4123565
theorem B2749073 : Blo 1831617 2749073 := bstep (se 2 (by rfl) ⟨1030902, by rfl⟩ : syracuseStep 2749073 = 2061805) B2061805
theorem B4125329 : Blo 1831617 4125329 := bstep (se 2 (by rfl) ⟨1546998, by rfl⟩ : syracuseStep 4125329 = 3093997) B3093997
theorem B2749091 : Blo 1831617 2749091 := bstep (se 1 (by rfl) ⟨2061818, by rfl⟩ : syracuseStep 2749091 = 4123637) B4123637
theorem B4125347 : Blo 1831617 4125347 := bstep (se 1 (by rfl) ⟨3094010, by rfl⟩ : syracuseStep 4125347 = 6188021) B6188021
theorem B2749121 : Blo 1831617 2749121 := bstep (se 2 (by rfl) ⟨1030920, by rfl⟩ : syracuseStep 2749121 = 2061841) B2061841
theorem B1831619 : Blo 1831617 1831619 := bstep (se 1 (by rfl) ⟨1373714, by rfl⟩ : syracuseStep 1831619 = 2747429) B2747429
theorem B2060995 : Blo 1831617 2060995 := bstep (se 1 (by rfl) ⟨1545746, by rfl⟩ : syracuseStep 2060995 = 3091493) B3091493
theorem B3478211 : Blo 1831617 3478211 := bstep (se 1 (by rfl) ⟨2608658, by rfl⟩ : syracuseStep 3478211 = 5217317) B5217317
theorem B3093187 : Blo 1831617 3093187 := bstep (se 1 (by rfl) ⟨2319890, by rfl⟩ : syracuseStep 3093187 = 4639781) B4639781
theorem B1831635 : Blo 1831617 1831635 := bstep (se 1 (by rfl) ⟨1373726, by rfl⟩ : syracuseStep 1831635 = 2747453) B2747453
theorem B2749139 : Blo 1831617 2749139 := bstep (se 1 (by rfl) ⟨2061854, by rfl⟩ : syracuseStep 2749139 = 4123709) B4123709
theorem B1831651 : Blo 1831617 1831651 := bstep (se 1 (by rfl) ⟨1373738, by rfl⟩ : syracuseStep 1831651 = 2747477) B2747477
theorem B20083427 : Blo 1831617 20083427 := bstep (se 1 (by rfl) ⟨15062570, by rfl⟩ : syracuseStep 20083427 = 30125141) B30125141
theorem B2749169 : Blo 1831617 2749169 := bstep (se 2 (by rfl) ⟨1030938, by rfl⟩ : syracuseStep 2749169 = 2061877) B2061877
theorem B6443761 : Blo 1831617 6443761 := bstep (se 2 (by rfl) ⟨2416410, by rfl⟩ : syracuseStep 6443761 = 4832821) B4832821
theorem B1831667 : Blo 1831617 1831667 := bstep (se 1 (by rfl) ⟨1373750, by rfl⟩ : syracuseStep 1831667 = 2747501) B2747501
theorem B1831683 : Blo 1831617 1831683 := bstep (se 1 (by rfl) ⟨1373762, by rfl⟩ : syracuseStep 1831683 = 2747525) B2747525
theorem B2749187 : Blo 1831617 2749187 := bstep (se 1 (by rfl) ⟨2061890, by rfl⟩ : syracuseStep 2749187 = 4123781) B4123781
theorem B2609923 : Blo 1831617 2609923 := bstep (se 1 (by rfl) ⟨1957442, by rfl⟩ : syracuseStep 2609923 = 3914885) B3914885
theorem B5870353 : Blo 1831617 5870353 := bstep (se 2 (by rfl) ⟨2201382, by rfl⟩ : syracuseStep 5870353 = 4402765) B4402765
theorem B1831699 : Blo 1831617 1831699 := bstep (se 1 (by rfl) ⟨1373774, by rfl⟩ : syracuseStep 1831699 = 2747549) B2747549
theorem B2749217 : Blo 1831617 2749217 := bstep (se 2 (by rfl) ⟨1030956, by rfl⟩ : syracuseStep 2749217 = 2061913) B2061913
theorem B1831715 : Blo 1831617 1831715 := bstep (se 1 (by rfl) ⟨1373786, by rfl⟩ : syracuseStep 1831715 = 2747573) B2747573
theorem B6443821 : Blo 1831617 6443821 := bstep (se 3 (by rfl) ⟨1208216, by rfl⟩ : syracuseStep 6443821 = 2416433) B2416433
theorem B1831731 : Blo 1831617 1831731 := bstep (se 1 (by rfl) ⟨1373798, by rfl⟩ : syracuseStep 1831731 = 2747597) B2747597
theorem B2749235 : Blo 1831617 2749235 := bstep (se 1 (by rfl) ⟨2061926, by rfl⟩ : syracuseStep 2749235 = 4123853) B4123853
theorem B1831747 : Blo 1831617 1831747 := bstep (se 1 (by rfl) ⟨1373810, by rfl⟩ : syracuseStep 1831747 = 2747621) B2747621
theorem B10433357 : Blo 1831617 10433357 := bstep (se 3 (by rfl) ⟨1956254, by rfl⟩ : syracuseStep 10433357 = 3912509) B3912509
theorem B2749265 : Blo 1831617 2749265 := bstep (se 2 (by rfl) ⟨1030974, by rfl⟩ : syracuseStep 2749265 = 2061949) B2061949
theorem B3093329 : Blo 1831617 3093329 := bstep (se 2 (by rfl) ⟨1159998, by rfl⟩ : syracuseStep 3093329 = 2319997) B2319997
theorem B1831763 : Blo 1831617 1831763 := bstep (se 1 (by rfl) ⟨1373822, by rfl⟩ : syracuseStep 1831763 = 2747645) B2747645
theorem B2061139 : Blo 1831617 2061139 := bstep (se 1 (by rfl) ⟨1545854, by rfl⟩ : syracuseStep 2061139 = 3091709) B3091709
theorem B1831779 : Blo 1831617 1831779 := bstep (se 1 (by rfl) ⟨1373834, by rfl⟩ : syracuseStep 1831779 = 2747669) B2747669
theorem B2749283 : Blo 1831617 2749283 := bstep (se 1 (by rfl) ⟨2061962, by rfl⟩ : syracuseStep 2749283 = 4123925) B4123925
theorem B14103409 : Blo 1831617 14103409 := bstep (se 2 (by rfl) ⟨5288778, by rfl⟩ : syracuseStep 14103409 = 10577557) B10577557
theorem B1831795 : Blo 1831617 1831795 := bstep (se 1 (by rfl) ⟨1373846, by rfl⟩ : syracuseStep 1831795 = 2747693) B2747693
theorem B2749313 : Blo 1831617 2749313 := bstep (se 2 (by rfl) ⟨1030992, by rfl⟩ : syracuseStep 2749313 = 2061985) B2061985
theorem B1831811 : Blo 1831617 1831811 := bstep (se 1 (by rfl) ⟨1373858, by rfl⟩ : syracuseStep 1831811 = 2747717) B2747717
theorem B1831827 : Blo 1831617 1831827 := bstep (se 1 (by rfl) ⟨1373870, by rfl⟩ : syracuseStep 1831827 = 2747741) B2747741
theorem B2749331 : Blo 1831617 2749331 := bstep (se 1 (by rfl) ⟨2061998, by rfl⟩ : syracuseStep 2749331 = 4123997) B4123997
theorem B1831843 : Blo 1831617 1831843 := bstep (se 1 (by rfl) ⟨1373882, by rfl⟩ : syracuseStep 1831843 = 2747765) B2747765
theorem B2749361 : Blo 1831617 2749361 := bstep (se 2 (by rfl) ⟨1031010, by rfl⟩ : syracuseStep 2749361 = 2062021) B2062021
theorem B10441649 : Blo 1831617 10441649 := bstep (se 2 (by rfl) ⟨3915618, by rfl⟩ : syracuseStep 10441649 = 7831237) B7831237
theorem B1831859 : Blo 1831617 1831859 := bstep (se 1 (by rfl) ⟨1373894, by rfl⟩ : syracuseStep 1831859 = 2747789) B2747789
theorem B4125617 : Blo 1831617 4125617 := bstep (se 2 (by rfl) ⟨1547106, by rfl⟩ : syracuseStep 4125617 = 3094213) B3094213
theorem B1831875 : Blo 1831617 1831875 := bstep (se 1 (by rfl) ⟨1373906, by rfl⟩ : syracuseStep 1831875 = 2747813) B2747813
theorem B59413445 : Blo 1831617 59413445 := bstep (se 4 (by rfl) ⟨5570010, by rfl⟩ : syracuseStep 59413445 = 11140021) B11140021
theorem B2749379 : Blo 1831617 2749379 := bstep (se 1 (by rfl) ⟨2062034, by rfl⟩ : syracuseStep 2749379 = 4124069) B4124069
theorem B4125635 : Blo 1831617 4125635 := bstep (se 1 (by rfl) ⟨3094226, by rfl⟩ : syracuseStep 4125635 = 6188453) B6188453
theorem B3093457 : Blo 1831617 3093457 := bstep (se 2 (by rfl) ⟨1160046, by rfl⟩ : syracuseStep 3093457 = 2320093) B2320093
theorem B1831891 : Blo 1831617 1831891 := bstep (se 1 (by rfl) ⟨1373918, by rfl⟩ : syracuseStep 1831891 = 2747837) B2747837
theorem B2749409 : Blo 1831617 2749409 := bstep (se 2 (by rfl) ⟨1031028, by rfl⟩ : syracuseStep 2749409 = 2062057) B2062057
theorem B1831907 : Blo 1831617 1831907 := bstep (se 1 (by rfl) ⟨1373930, by rfl⟩ : syracuseStep 1831907 = 2747861) B2747861
theorem B2061283 : Blo 1831617 2061283 := bstep (se 1 (by rfl) ⟨1545962, by rfl⟩ : syracuseStep 2061283 = 3091925) B3091925
theorem B6960113 : Blo 1831617 6960113 := bstep (se 2 (by rfl) ⟨2610042, by rfl⟩ : syracuseStep 6960113 = 5220085) B5220085
theorem B1831923 : Blo 1831617 1831923 := bstep (se 1 (by rfl) ⟨1373942, by rfl⟩ : syracuseStep 1831923 = 2747885) B2747885
theorem B2749427 : Blo 1831617 2749427 := bstep (se 1 (by rfl) ⟨2062070, by rfl⟩ : syracuseStep 2749427 = 4124141) B4124141
theorem B3093491 : Blo 1831617 3093491 := bstep (se 1 (by rfl) ⟨2320118, by rfl⟩ : syracuseStep 3093491 = 4640237) B4640237
theorem B1831939 : Blo 1831617 1831939 := bstep (se 1 (by rfl) ⟨1373954, by rfl⟩ : syracuseStep 1831939 = 2747909) B2747909
theorem B2749457 : Blo 1831617 2749457 := bstep (se 2 (by rfl) ⟨1031046, by rfl⟩ : syracuseStep 2749457 = 2062093) B2062093
theorem B1831955 : Blo 1831617 1831955 := bstep (se 1 (by rfl) ⟨1373966, by rfl⟩ : syracuseStep 1831955 = 2747933) B2747933
theorem B1831971 : Blo 1831617 1831971 := bstep (se 1 (by rfl) ⟨1373978, by rfl⟩ : syracuseStep 1831971 = 2747957) B2747957
theorem B2749475 : Blo 1831617 2749475 := bstep (se 1 (by rfl) ⟨2062106, by rfl⟩ : syracuseStep 2749475 = 4124213) B4124213
theorem B1831987 : Blo 1831617 1831987 := bstep (se 1 (by rfl) ⟨1373990, by rfl⟩ : syracuseStep 1831987 = 2747981) B2747981
theorem B2749505 : Blo 1831617 2749505 := bstep (se 2 (by rfl) ⟨1031064, by rfl⟩ : syracuseStep 2749505 = 2062129) B2062129
theorem B1832003 : Blo 1831617 1832003 := bstep (se 1 (by rfl) ⟨1374002, by rfl⟩ : syracuseStep 1832003 = 2748005) B2748005
theorem B1832019 : Blo 1831617 1832019 := bstep (se 1 (by rfl) ⟨1374014, by rfl⟩ : syracuseStep 1832019 = 2748029) B2748029
theorem B2749523 : Blo 1831617 2749523 := bstep (se 1 (by rfl) ⟨2062142, by rfl⟩ : syracuseStep 2749523 = 4124285) B4124285
theorem B1832035 : Blo 1831617 1832035 := bstep (se 1 (by rfl) ⟨1374026, by rfl⟩ : syracuseStep 1832035 = 2748053) B2748053
theorem B4953197 : Blo 1831617 4953197 := bstep (se 3 (by rfl) ⟨928724, by rfl⟩ : syracuseStep 4953197 = 1857449) B1857449
theorem B2749553 : Blo 1831617 2749553 := bstep (se 2 (by rfl) ⟨1031082, by rfl⟩ : syracuseStep 2749553 = 2062165) B2062165
theorem B2061427 : Blo 1831617 2061427 := bstep (se 1 (by rfl) ⟨1546070, by rfl⟩ : syracuseStep 2061427 = 3092141) B3092141
theorem B1832051 : Blo 1831617 1832051 := bstep (se 1 (by rfl) ⟨1374038, by rfl⟩ : syracuseStep 1832051 = 2748077) B2748077
theorem B3093619 : Blo 1831617 3093619 := bstep (se 1 (by rfl) ⟨2320214, by rfl⟩ : syracuseStep 3093619 = 4640429) B4640429
theorem B1832067 : Blo 1831617 1832067 := bstep (se 1 (by rfl) ⟨1374050, by rfl⟩ : syracuseStep 1832067 = 2748101) B2748101
theorem B2749571 : Blo 1831617 2749571 := bstep (se 1 (by rfl) ⟨2062178, by rfl⟩ : syracuseStep 2749571 = 4124357) B4124357
theorem B5289101 : Blo 1831617 5289101 := bstep (se 3 (by rfl) ⟨991706, by rfl⟩ : syracuseStep 5289101 = 1983413) B1983413
theorem B1832083 : Blo 1831617 1832083 := bstep (se 1 (by rfl) ⟨1374062, by rfl⟩ : syracuseStep 1832083 = 2748125) B2748125
theorem B2749601 : Blo 1831617 2749601 := bstep (se 2 (by rfl) ⟨1031100, by rfl⟩ : syracuseStep 2749601 = 2062201) B2062201
theorem B1832099 : Blo 1831617 1832099 := bstep (se 1 (by rfl) ⟨1374074, by rfl⟩ : syracuseStep 1832099 = 2748149) B2748149
theorem B1832115 : Blo 1831617 1832115 := bstep (se 1 (by rfl) ⟨1374086, by rfl⟩ : syracuseStep 1832115 = 2748173) B2748173
theorem B2749619 : Blo 1831617 2749619 := bstep (se 1 (by rfl) ⟨2062214, by rfl⟩ : syracuseStep 2749619 = 4124429) B4124429
theorem B1832131 : Blo 1831617 1832131 := bstep (se 1 (by rfl) ⟨1374098, by rfl⟩ : syracuseStep 1832131 = 2748197) B2748197
theorem B2749649 : Blo 1831617 2749649 := bstep (se 2 (by rfl) ⟨1031118, by rfl⟩ : syracuseStep 2749649 = 2062237) B2062237
theorem B1832147 : Blo 1831617 1832147 := bstep (se 1 (by rfl) ⟨1374110, by rfl⟩ : syracuseStep 1832147 = 2748221) B2748221
theorem B1832163 : Blo 1831617 1832163 := bstep (se 1 (by rfl) ⟨1374122, by rfl⟩ : syracuseStep 1832163 = 2748245) B2748245
theorem B2749667 : Blo 1831617 2749667 := bstep (se 1 (by rfl) ⟨2062250, by rfl⟩ : syracuseStep 2749667 = 4124501) B4124501
theorem B1832179 : Blo 1831617 1832179 := bstep (se 1 (by rfl) ⟨1374134, by rfl⟩ : syracuseStep 1832179 = 2748269) B2748269
theorem B2749697 : Blo 1831617 2749697 := bstep (se 2 (by rfl) ⟨1031136, by rfl⟩ : syracuseStep 2749697 = 2062273) B2062273
theorem B3093761 : Blo 1831617 3093761 := bstep (se 2 (by rfl) ⟨1160160, by rfl⟩ : syracuseStep 3093761 = 2320321) B2320321
theorem B1832195 : Blo 1831617 1832195 := bstep (se 1 (by rfl) ⟨1374146, by rfl⟩ : syracuseStep 1832195 = 2748293) B2748293
theorem B2061571 : Blo 1831617 2061571 := bstep (se 1 (by rfl) ⟨1546178, by rfl⟩ : syracuseStep 2061571 = 3092357) B3092357
theorem B1832211 : Blo 1831617 1832211 := bstep (se 1 (by rfl) ⟨1374158, by rfl⟩ : syracuseStep 1832211 = 2748317) B2748317
theorem B2749715 : Blo 1831617 2749715 := bstep (se 1 (by rfl) ⟨2062286, by rfl⟩ : syracuseStep 2749715 = 4124573) B4124573
theorem B1832227 : Blo 1831617 1832227 := bstep (se 1 (by rfl) ⟨1374170, by rfl⟩ : syracuseStep 1832227 = 2748341) B2748341
theorem B6182189 : Blo 1831617 6182189 := bstep (se 3 (by rfl) ⟨1159160, by rfl⟩ : syracuseStep 6182189 = 2318321) B2318321
theorem B2749745 : Blo 1831617 2749745 := bstep (se 2 (by rfl) ⟨1031154, by rfl⟩ : syracuseStep 2749745 = 2062309) B2062309
theorem B1832243 : Blo 1831617 1832243 := bstep (se 1 (by rfl) ⟨1374182, by rfl⟩ : syracuseStep 1832243 = 2748365) B2748365
theorem B2610481 : Blo 1831617 2610481 := bstep (se 2 (by rfl) ⟨978930, by rfl⟩ : syracuseStep 2610481 = 1957861) B1957861
theorem B1832259 : Blo 1831617 1832259 := bstep (se 1 (by rfl) ⟨1374194, by rfl⟩ : syracuseStep 1832259 = 2748389) B2748389
theorem B2749763 : Blo 1831617 2749763 := bstep (se 1 (by rfl) ⟨2062322, by rfl⟩ : syracuseStep 2749763 = 4124645) B4124645
theorem B1832275 : Blo 1831617 1832275 := bstep (se 1 (by rfl) ⟨1374206, by rfl⟩ : syracuseStep 1832275 = 2748413) B2748413
theorem B3134803 : Blo 1831617 3134803 := bstep (se 1 (by rfl) ⟨2351102, by rfl⟩ : syracuseStep 3134803 = 4702205) B4702205
theorem B2610515 : Blo 1831617 2610515 := bstep (se 1 (by rfl) ⟨1957886, by rfl⟩ : syracuseStep 2610515 = 3915773) B3915773
theorem B2749793 : Blo 1831617 2749793 := bstep (se 2 (by rfl) ⟨1031172, by rfl⟩ : syracuseStep 2749793 = 2062345) B2062345
theorem B6182243 : Blo 1831617 6182243 := bstep (se 1 (by rfl) ⟨4636682, by rfl⟩ : syracuseStep 6182243 = 9273365) B9273365
theorem B1832291 : Blo 1831617 1832291 := bstep (se 1 (by rfl) ⟨1374218, by rfl⟩ : syracuseStep 1832291 = 2748437) B2748437
theorem B1832307 : Blo 1831617 1832307 := bstep (se 1 (by rfl) ⟨1374230, by rfl⟩ : syracuseStep 1832307 = 2748461) B2748461
theorem B2749811 : Blo 1831617 2749811 := bstep (se 1 (by rfl) ⟨2062358, by rfl⟩ : syracuseStep 2749811 = 4124717) B4124717
theorem B1832323 : Blo 1831617 1832323 := bstep (se 1 (by rfl) ⟨1374242, by rfl⟩ : syracuseStep 1832323 = 2748485) B2748485
theorem B4404611 : Blo 1831617 4404611 := bstep (se 1 (by rfl) ⟨3303458, by rfl⟩ : syracuseStep 4404611 = 6606917) B6606917
theorem B3093889 : Blo 1831617 3093889 := bstep (se 2 (by rfl) ⟨1160208, by rfl⟩ : syracuseStep 3093889 = 2320417) B2320417
theorem B2749841 : Blo 1831617 2749841 := bstep (se 2 (by rfl) ⟨1031190, by rfl⟩ : syracuseStep 2749841 = 2062381) B2062381
theorem B1832339 : Blo 1831617 1832339 := bstep (se 1 (by rfl) ⟨1374254, by rfl⟩ : syracuseStep 1832339 = 2748509) B2748509
theorem B2061715 : Blo 1831617 2061715 := bstep (se 1 (by rfl) ⟨1546286, by rfl⟩ : syracuseStep 2061715 = 3092573) B3092573
theorem B1832355 : Blo 1831617 1832355 := bstep (se 1 (by rfl) ⟨1374266, by rfl⟩ : syracuseStep 1832355 = 2748533) B2748533
theorem B2749859 : Blo 1831617 2749859 := bstep (se 1 (by rfl) ⟨2062394, by rfl⟩ : syracuseStep 2749859 = 4124789) B4124789
theorem B3093923 : Blo 1831617 3093923 := bstep (se 1 (by rfl) ⟨2320442, by rfl⟩ : syracuseStep 3093923 = 4640885) B4640885
theorem B7828913 : Blo 1831617 7828913 := bstep (se 2 (by rfl) ⟨2935842, by rfl⟩ : syracuseStep 7828913 = 5871685) B5871685
theorem B1832371 : Blo 1831617 1832371 := bstep (se 1 (by rfl) ⟨1374278, by rfl⟩ : syracuseStep 1832371 = 2748557) B2748557
theorem B2749889 : Blo 1831617 2749889 := bstep (se 2 (by rfl) ⟨1031208, by rfl⟩ : syracuseStep 2749889 = 2062417) B2062417
theorem B1832387 : Blo 1831617 1832387 := bstep (se 1 (by rfl) ⟨1374290, by rfl⟩ : syracuseStep 1832387 = 2748581) B2748581
theorem B1832403 : Blo 1831617 1832403 := bstep (se 1 (by rfl) ⟨1374302, by rfl⟩ : syracuseStep 1832403 = 2748605) B2748605
theorem B2749907 : Blo 1831617 2749907 := bstep (se 1 (by rfl) ⟨2062430, by rfl⟩ : syracuseStep 2749907 = 4124861) B4124861
theorem B1832419 : Blo 1831617 1832419 := bstep (se 1 (by rfl) ⟨1374314, by rfl⟩ : syracuseStep 1832419 = 2748629) B2748629
theorem B2749937 : Blo 1831617 2749937 := bstep (se 2 (by rfl) ⟨1031226, by rfl⟩ : syracuseStep 2749937 = 2062453) B2062453
theorem B1832435 : Blo 1831617 1832435 := bstep (se 1 (by rfl) ⟨1374326, by rfl⟩ : syracuseStep 1832435 = 2748653) B2748653
theorem B1832451 : Blo 1831617 1832451 := bstep (se 1 (by rfl) ⟨1374338, by rfl⟩ : syracuseStep 1832451 = 2748677) B2748677
theorem B2749955 : Blo 1831617 2749955 := bstep (se 1 (by rfl) ⟨2062466, by rfl⟩ : syracuseStep 2749955 = 4124933) B4124933
theorem B1832467 : Blo 1831617 1832467 := bstep (se 1 (by rfl) ⟨1374350, by rfl⟩ : syracuseStep 1832467 = 2748701) B2748701
theorem B2749985 : Blo 1831617 2749985 := bstep (se 2 (by rfl) ⟨1031244, by rfl⟩ : syracuseStep 2749985 = 2062489) B2062489
theorem B1832483 : Blo 1831617 1832483 := bstep (se 1 (by rfl) ⟨1374362, by rfl⟩ : syracuseStep 1832483 = 2748725) B2748725
theorem B2061859 : Blo 1831617 2061859 := bstep (se 1 (by rfl) ⟨1546394, by rfl⟩ : syracuseStep 2061859 = 3092789) B3092789
theorem B3094051 : Blo 1831617 3094051 := bstep (se 1 (by rfl) ⟨2320538, by rfl⟩ : syracuseStep 3094051 = 4641077) B4641077
theorem B1832499 : Blo 1831617 1832499 := bstep (se 1 (by rfl) ⟨1374374, by rfl⟩ : syracuseStep 1832499 = 2748749) B2748749
theorem B2750003 : Blo 1831617 2750003 := bstep (se 1 (by rfl) ⟨2062502, by rfl⟩ : syracuseStep 2750003 = 4125005) B4125005
theorem B1832515 : Blo 1831617 1832515 := bstep (se 1 (by rfl) ⟨1374386, by rfl⟩ : syracuseStep 1832515 = 2748773) B2748773
theorem B3479107 : Blo 1831617 3479107 := bstep (se 1 (by rfl) ⟨2609330, by rfl⟩ : syracuseStep 3479107 = 5218661) B5218661
theorem B2750033 : Blo 1831617 2750033 := bstep (se 2 (by rfl) ⟨1031262, by rfl⟩ : syracuseStep 2750033 = 2062525) B2062525
theorem B1832531 : Blo 1831617 1832531 := bstep (se 1 (by rfl) ⟨1374398, by rfl⟩ : syracuseStep 1832531 = 2748797) B2748797
theorem B1832547 : Blo 1831617 1832547 := bstep (se 1 (by rfl) ⟨1374410, by rfl⟩ : syracuseStep 1832547 = 2748821) B2748821
theorem B2750051 : Blo 1831617 2750051 := bstep (se 1 (by rfl) ⟨2062538, by rfl⟩ : syracuseStep 2750051 = 4125077) B4125077
theorem B6182513 : Blo 1831617 6182513 := bstep (se 2 (by rfl) ⟨2318442, by rfl⟩ : syracuseStep 6182513 = 4636885) B4636885
theorem B6035057 : Blo 1831617 6035057 := bstep (se 2 (by rfl) ⟨2263146, by rfl⟩ : syracuseStep 6035057 = 4526293) B4526293
theorem B1832563 : Blo 1831617 1832563 := bstep (se 1 (by rfl) ⟨1374422, by rfl⟩ : syracuseStep 1832563 = 2748845) B2748845
theorem B2750081 : Blo 1831617 2750081 := bstep (se 2 (by rfl) ⟨1031280, by rfl⟩ : syracuseStep 2750081 = 2062561) B2062561
theorem B1832579 : Blo 1831617 1832579 := bstep (se 1 (by rfl) ⟨1374434, by rfl⟩ : syracuseStep 1832579 = 2748869) B2748869
theorem B11744909 : Blo 1831617 11744909 := bstep (se 3 (by rfl) ⟨2202170, by rfl⟩ : syracuseStep 11744909 = 4404341) B4404341
theorem B1832595 : Blo 1831617 1832595 := bstep (se 1 (by rfl) ⟨1374446, by rfl⟩ : syracuseStep 1832595 = 2748893) B2748893
theorem B2750099 : Blo 1831617 2750099 := bstep (se 1 (by rfl) ⟨2062574, by rfl⟩ : syracuseStep 2750099 = 4125149) B4125149
theorem B1832611 : Blo 1831617 1832611 := bstep (se 1 (by rfl) ⟨1374458, by rfl⟩ : syracuseStep 1832611 = 2748917) B2748917
theorem B2750129 : Blo 1831617 2750129 := bstep (se 2 (by rfl) ⟨1031298, by rfl⟩ : syracuseStep 2750129 = 2062597) B2062597
theorem B3094193 : Blo 1831617 3094193 := bstep (se 2 (by rfl) ⟨1160322, by rfl⟩ : syracuseStep 3094193 = 2320645) B2320645
theorem B2201267 : Blo 1831617 2201267 := bstep (se 1 (by rfl) ⟨1650950, by rfl⟩ : syracuseStep 2201267 = 3301901) B3301901
theorem B1832627 : Blo 1831617 1832627 := bstep (se 1 (by rfl) ⟨1374470, by rfl⟩ : syracuseStep 1832627 = 2748941) B2748941
theorem B2062003 : Blo 1831617 2062003 := bstep (se 1 (by rfl) ⟨1546502, by rfl⟩ : syracuseStep 2062003 = 3093005) B3093005
theorem B1832643 : Blo 1831617 1832643 := bstep (se 1 (by rfl) ⟨1374482, by rfl⟩ : syracuseStep 1832643 = 2748965) B2748965
theorem B2750147 : Blo 1831617 2750147 := bstep (se 1 (by rfl) ⟨2062610, by rfl⟩ : syracuseStep 2750147 = 4125221) B4125221
theorem B1832659 : Blo 1831617 1832659 := bstep (se 1 (by rfl) ⟨1374494, by rfl⟩ : syracuseStep 1832659 = 2748989) B2748989
theorem B2750177 : Blo 1831617 2750177 := bstep (se 2 (by rfl) ⟨1031316, by rfl⟩ : syracuseStep 2750177 = 2062633) B2062633
theorem B1832675 : Blo 1831617 1832675 := bstep (se 1 (by rfl) ⟨1374506, by rfl⟩ : syracuseStep 1832675 = 2749013) B2749013
theorem B3479267 : Blo 1831617 3479267 := bstep (se 1 (by rfl) ⟨2609450, by rfl⟩ : syracuseStep 3479267 = 5218901) B5218901
theorem B5215985 : Blo 1831617 5215985 := bstep (se 2 (by rfl) ⟨1955994, by rfl⟩ : syracuseStep 5215985 = 3911989) B3911989
theorem B1832691 : Blo 1831617 1832691 := bstep (se 1 (by rfl) ⟨1374518, by rfl⟩ : syracuseStep 1832691 = 2749037) B2749037
theorem B2750195 : Blo 1831617 2750195 := bstep (se 1 (by rfl) ⟨2062646, by rfl⟩ : syracuseStep 2750195 = 4125293) B4125293
theorem B1832707 : Blo 1831617 1832707 := bstep (se 1 (by rfl) ⟨1374530, by rfl⟩ : syracuseStep 1832707 = 2749061) B2749061
theorem B4404995 : Blo 1831617 4404995 := bstep (se 1 (by rfl) ⟨3303746, by rfl⟩ : syracuseStep 4404995 = 6607493) B6607493
theorem B2750225 : Blo 1831617 2750225 := bstep (se 2 (by rfl) ⟨1031334, by rfl⟩ : syracuseStep 2750225 = 2062669) B2062669
theorem B1832723 : Blo 1831617 1832723 := bstep (se 1 (by rfl) ⟨1374542, by rfl⟩ : syracuseStep 1832723 = 2749085) B2749085
theorem B7149347 : Blo 1831617 7149347 := bstep (se 1 (by rfl) ⟨5362010, by rfl⟩ : syracuseStep 7149347 = 10724021) B10724021
theorem B1832739 : Blo 1831617 1832739 := bstep (se 1 (by rfl) ⟨1374554, by rfl⟩ : syracuseStep 1832739 = 2749109) B2749109
theorem B2750243 : Blo 1831617 2750243 := bstep (se 1 (by rfl) ⟨2062682, by rfl⟩ : syracuseStep 2750243 = 4125365) B4125365
theorem B1832755 : Blo 1831617 1832755 := bstep (se 1 (by rfl) ⟨1374566, by rfl⟩ : syracuseStep 1832755 = 2749133) B2749133
theorem B2750273 : Blo 1831617 2750273 := bstep (se 2 (by rfl) ⟨1031352, by rfl⟩ : syracuseStep 2750273 = 2062705) B2062705
theorem B1832771 : Blo 1831617 1832771 := bstep (se 1 (by rfl) ⟨1374578, by rfl⟩ : syracuseStep 1832771 = 2749157) B2749157
theorem B2062147 : Blo 1831617 2062147 := bstep (se 1 (by rfl) ⟨1546610, by rfl⟩ : syracuseStep 2062147 = 3093221) B3093221
theorem B1832787 : Blo 1831617 1832787 := bstep (se 1 (by rfl) ⟨1374590, by rfl⟩ : syracuseStep 1832787 = 2749181) B2749181
theorem B2750291 : Blo 1831617 2750291 := bstep (se 1 (by rfl) ⟨2062718, by rfl⟩ : syracuseStep 2750291 = 4125437) B4125437
theorem B1832803 : Blo 1831617 1832803 := bstep (se 1 (by rfl) ⟨1374602, by rfl⟩ : syracuseStep 1832803 = 2749205) B2749205
theorem B4953965 : Blo 1831617 4953965 := bstep (se 3 (by rfl) ⟨928868, by rfl⟩ : syracuseStep 4953965 = 1857737) B1857737
theorem B2750321 : Blo 1831617 2750321 := bstep (se 2 (by rfl) ⟨1031370, by rfl⟩ : syracuseStep 2750321 = 2062741) B2062741
theorem B1832819 : Blo 1831617 1832819 := bstep (se 1 (by rfl) ⟨1374614, by rfl⟩ : syracuseStep 1832819 = 2749229) B2749229
theorem B1832835 : Blo 1831617 1832835 := bstep (se 1 (by rfl) ⟨1374626, by rfl⟩ : syracuseStep 1832835 = 2749253) B2749253
theorem B2750339 : Blo 1831617 2750339 := bstep (se 1 (by rfl) ⟨2062754, by rfl⟩ : syracuseStep 2750339 = 4125509) B4125509
theorem B29718413 : Blo 1831617 29718413 := bstep (se 3 (by rfl) ⟨5572202, by rfl⟩ : syracuseStep 29718413 = 11144405) B11144405
theorem B1832851 : Blo 1831617 1832851 := bstep (se 1 (by rfl) ⟨1374638, by rfl⟩ : syracuseStep 1832851 = 2749277) B2749277
theorem B2750369 : Blo 1831617 2750369 := bstep (se 2 (by rfl) ⟨1031388, by rfl⟩ : syracuseStep 2750369 = 2062777) B2062777
theorem B1832867 : Blo 1831617 1832867 := bstep (se 1 (by rfl) ⟨1374650, by rfl⟩ : syracuseStep 1832867 = 2749301) B2749301
theorem B5216177 : Blo 1831617 5216177 := bstep (se 2 (by rfl) ⟨1956066, by rfl⟩ : syracuseStep 5216177 = 3912133) B3912133
theorem B1832883 : Blo 1831617 1832883 := bstep (se 1 (by rfl) ⟨1374662, by rfl⟩ : syracuseStep 1832883 = 2749325) B2749325
theorem B2750387 : Blo 1831617 2750387 := bstep (se 1 (by rfl) ⟨2062790, by rfl⟩ : syracuseStep 2750387 = 4125581) B4125581
theorem B1832899 : Blo 1831617 1832899 := bstep (se 1 (by rfl) ⟨1374674, by rfl⟩ : syracuseStep 1832899 = 2749349) B2749349
theorem B2750417 : Blo 1831617 2750417 := bstep (se 2 (by rfl) ⟨1031406, by rfl⟩ : syracuseStep 2750417 = 2062813) B2062813
theorem B1832915 : Blo 1831617 1832915 := bstep (se 1 (by rfl) ⟨1374686, by rfl⟩ : syracuseStep 1832915 = 2749373) B2749373
theorem B2062291 : Blo 1831617 2062291 := bstep (se 1 (by rfl) ⟨1546718, by rfl⟩ : syracuseStep 2062291 = 3093437) B3093437
theorem B1832931 : Blo 1831617 1832931 := bstep (se 1 (by rfl) ⟨1374698, by rfl⟩ : syracuseStep 1832931 = 2749397) B2749397
theorem B1832947 : Blo 1831617 1832947 := bstep (se 1 (by rfl) ⟨1374710, by rfl⟩ : syracuseStep 1832947 = 2749421) B2749421
theorem B1832963 : Blo 1831617 1832963 := bstep (se 1 (by rfl) ⟨1374722, by rfl⟩ : syracuseStep 1832963 = 2749445) B2749445
theorem B1832979 : Blo 1831617 1832979 := bstep (se 1 (by rfl) ⟨1374734, by rfl⟩ : syracuseStep 1832979 = 2749469) B2749469
theorem B1832995 : Blo 1831617 1832995 := bstep (se 1 (by rfl) ⟨1374746, by rfl⟩ : syracuseStep 1832995 = 2749493) B2749493
theorem B1833011 : Blo 1831617 1833011 := bstep (se 1 (by rfl) ⟨1374758, by rfl⟩ : syracuseStep 1833011 = 2749517) B2749517
theorem B1833027 : Blo 1831617 1833027 := bstep (se 1 (by rfl) ⟨1374770, by rfl⟩ : syracuseStep 1833027 = 2749541) B2749541
theorem B7829581 : Blo 1831617 7829581 := bstep (se 3 (by rfl) ⟨1468046, by rfl⟩ : syracuseStep 7829581 = 2936093) B2936093
theorem B4954193 : Blo 1831617 4954193 := bstep (se 2 (by rfl) ⟨1857822, by rfl⟩ : syracuseStep 4954193 = 3715645) B3715645
theorem B1833043 : Blo 1831617 1833043 := bstep (se 1 (by rfl) ⟨1374782, by rfl⟩ : syracuseStep 1833043 = 2749565) B2749565
theorem B1833059 : Blo 1831617 1833059 := bstep (se 1 (by rfl) ⟨1374794, by rfl⟩ : syracuseStep 1833059 = 2749589) B2749589
theorem B2062435 : Blo 1831617 2062435 := bstep (se 1 (by rfl) ⟨1546826, by rfl⟩ : syracuseStep 2062435 = 3093653) B3093653
theorem B4700273 : Blo 1831617 4700273 := bstep (se 2 (by rfl) ⟨1762602, by rfl⟩ : syracuseStep 4700273 = 3525205) B3525205
theorem B1833075 : Blo 1831617 1833075 := bstep (se 1 (by rfl) ⟨1374806, by rfl⟩ : syracuseStep 1833075 = 2749613) B2749613
theorem B3913859 : Blo 1831617 3913859 := bstep (se 1 (by rfl) ⟨2935394, by rfl⟩ : syracuseStep 3913859 = 5870789) B5870789
theorem B5290115 : Blo 1831617 5290115 := bstep (se 1 (by rfl) ⟨3967586, by rfl⟩ : syracuseStep 5290115 = 7935173) B7935173
theorem B1833091 : Blo 1831617 1833091 := bstep (se 1 (by rfl) ⟨1374818, by rfl⟩ : syracuseStep 1833091 = 2749637) B2749637
theorem B6183053 : Blo 1831617 6183053 := bstep (se 3 (by rfl) ⟨1159322, by rfl⟩ : syracuseStep 6183053 = 2318645) B2318645
theorem B1833107 : Blo 1831617 1833107 := bstep (se 1 (by rfl) ⟨1374830, by rfl⟩ : syracuseStep 1833107 = 2749661) B2749661
theorem B1833123 : Blo 1831617 1833123 := bstep (se 1 (by rfl) ⟨1374842, by rfl⟩ : syracuseStep 1833123 = 2749685) B2749685
theorem B1833139 : Blo 1831617 1833139 := bstep (se 1 (by rfl) ⟨1374854, by rfl⟩ : syracuseStep 1833139 = 2749709) B2749709
theorem B6183107 : Blo 1831617 6183107 := bstep (se 1 (by rfl) ⟨4637330, by rfl⟩ : syracuseStep 6183107 = 9274661) B9274661
theorem B16939205 : Blo 1831617 16939205 := bstep (se 4 (by rfl) ⟨1588050, by rfl⟩ : syracuseStep 16939205 = 3176101) B3176101
theorem B1833155 : Blo 1831617 1833155 := bstep (se 1 (by rfl) ⟨1374866, by rfl⟩ : syracuseStep 1833155 = 2749733) B2749733
theorem B1833171 : Blo 1831617 1833171 := bstep (se 1 (by rfl) ⟨1374878, by rfl⟩ : syracuseStep 1833171 = 2749757) B2749757
theorem B1833187 : Blo 1831617 1833187 := bstep (se 1 (by rfl) ⟨1374890, by rfl⟩ : syracuseStep 1833187 = 2749781) B2749781
theorem B1833203 : Blo 1831617 1833203 := bstep (se 1 (by rfl) ⟨1374902, by rfl⟩ : syracuseStep 1833203 = 2749805) B2749805
theorem B2062579 : Blo 1831617 2062579 := bstep (se 1 (by rfl) ⟨1546934, by rfl⟩ : syracuseStep 2062579 = 3093869) B3093869
theorem B1833219 : Blo 1831617 1833219 := bstep (se 1 (by rfl) ⟨1374914, by rfl⟩ : syracuseStep 1833219 = 2749829) B2749829
theorem B1833235 : Blo 1831617 1833235 := bstep (se 1 (by rfl) ⟨1374926, by rfl⟩ : syracuseStep 1833235 = 2749853) B2749853
theorem B1833251 : Blo 1831617 1833251 := bstep (se 1 (by rfl) ⟨1374938, by rfl⟩ : syracuseStep 1833251 = 2749877) B2749877
theorem B4405553 : Blo 1831617 4405553 := bstep (se 2 (by rfl) ⟨1652082, by rfl⟩ : syracuseStep 4405553 = 3304165) B3304165
theorem B1833267 : Blo 1831617 1833267 := bstep (se 1 (by rfl) ⟨1374950, by rfl⟩ : syracuseStep 1833267 = 2749901) B2749901
theorem B3135809 : Blo 1831617 3135809 := bstep (se 2 (by rfl) ⟨1175928, by rfl⟩ : syracuseStep 3135809 = 2351857) B2351857
theorem B1833283 : Blo 1831617 1833283 := bstep (se 1 (by rfl) ⟨1374962, by rfl⟩ : syracuseStep 1833283 = 2749925) B2749925
theorem B5953873 : Blo 1831617 5953873 := bstep (se 2 (by rfl) ⟨2232702, by rfl⟩ : syracuseStep 5953873 = 4465405) B4465405
theorem B1833299 : Blo 1831617 1833299 := bstep (se 1 (by rfl) ⟨1374974, by rfl⟩ : syracuseStep 1833299 = 2749949) B2749949
theorem B1833315 : Blo 1831617 1833315 := bstep (se 1 (by rfl) ⟨1374986, by rfl⟩ : syracuseStep 1833315 = 2749973) B2749973
theorem B1833331 : Blo 1831617 1833331 := bstep (se 1 (by rfl) ⟨1374998, by rfl⟩ : syracuseStep 1833331 = 2749997) B2749997
theorem B1833347 : Blo 1831617 1833347 := bstep (se 1 (by rfl) ⟨1375010, by rfl⟩ : syracuseStep 1833347 = 2750021) B2750021
theorem B2062723 : Blo 1831617 2062723 := bstep (se 1 (by rfl) ⟨1547042, by rfl⟩ : syracuseStep 2062723 = 3094085) B3094085
theorem B1833363 : Blo 1831617 1833363 := bstep (se 1 (by rfl) ⟨1375022, by rfl⟩ : syracuseStep 1833363 = 2750045) B2750045
theorem B1833379 : Blo 1831617 1833379 := bstep (se 1 (by rfl) ⟨1375034, by rfl⟩ : syracuseStep 1833379 = 2750069) B2750069
theorem B6961571 : Blo 1831617 6961571 := bstep (se 1 (by rfl) ⟨5221178, by rfl⟩ : syracuseStep 6961571 = 10442357) B10442357
theorem B5724589 : Blo 1831617 5724589 := bstep (se 3 (by rfl) ⟨1073360, by rfl⟩ : syracuseStep 5724589 = 2146721) B2146721
theorem B6961585 : Blo 1831617 6961585 := bstep (se 2 (by rfl) ⟨2610594, by rfl⟩ : syracuseStep 6961585 = 5221189) B5221189
theorem B1833395 : Blo 1831617 1833395 := bstep (se 1 (by rfl) ⟨1375046, by rfl⟩ : syracuseStep 1833395 = 2750093) B2750093
theorem B1833411 : Blo 1831617 1833411 := bstep (se 1 (by rfl) ⟨1375058, by rfl⟩ : syracuseStep 1833411 = 2750117) B2750117
theorem B6183377 : Blo 1831617 6183377 := bstep (se 2 (by rfl) ⟨2318766, by rfl⟩ : syracuseStep 6183377 = 4637533) B4637533
theorem B1833427 : Blo 1831617 1833427 := bstep (se 1 (by rfl) ⟨1375070, by rfl⟩ : syracuseStep 1833427 = 2750141) B2750141
theorem B1956323 : Blo 1831617 1956323 := bstep (se 1 (by rfl) ⟨1467242, by rfl⟩ : syracuseStep 1956323 = 2934485) B2934485
theorem B1833443 : Blo 1831617 1833443 := bstep (se 1 (by rfl) ⟨1375082, by rfl⟩ : syracuseStep 1833443 = 2750165) B2750165
theorem B1833459 : Blo 1831617 1833459 := bstep (se 1 (by rfl) ⟨1375094, by rfl⟩ : syracuseStep 1833459 = 2750189) B2750189
theorem B1833475 : Blo 1831617 1833475 := bstep (se 1 (by rfl) ⟨1375106, by rfl⟩ : syracuseStep 1833475 = 2750213) B2750213
theorem B1833491 : Blo 1831617 1833491 := bstep (se 1 (by rfl) ⟨1375118, by rfl⟩ : syracuseStep 1833491 = 2750237) B2750237
theorem B1833507 : Blo 1831617 1833507 := bstep (se 1 (by rfl) ⟨1375130, by rfl⟩ : syracuseStep 1833507 = 2750261) B2750261
theorem B1833523 : Blo 1831617 1833523 := bstep (se 1 (by rfl) ⟨1375142, by rfl⟩ : syracuseStep 1833523 = 2750285) B2750285
theorem B1833539 : Blo 1831617 1833539 := bstep (se 1 (by rfl) ⟨1375154, by rfl⟩ : syracuseStep 1833539 = 2750309) B2750309
theorem B1833555 : Blo 1831617 1833555 := bstep (se 1 (by rfl) ⟨1375166, by rfl⟩ : syracuseStep 1833555 = 2750333) B2750333
theorem B1833571 : Blo 1831617 1833571 := bstep (se 1 (by rfl) ⟨1375178, by rfl⟩ : syracuseStep 1833571 = 2750357) B2750357
theorem B1833587 : Blo 1831617 1833587 := bstep (se 1 (by rfl) ⟨1375190, by rfl⟩ : syracuseStep 1833587 = 2750381) B2750381
theorem B1833603 : Blo 1831617 1833603 := bstep (se 1 (by rfl) ⟨1375202, by rfl⟩ : syracuseStep 1833603 = 2750405) B2750405
theorem B7830179 : Blo 1831617 7830179 := bstep (se 1 (by rfl) ⟨5872634, by rfl⟩ : syracuseStep 7830179 = 11745269) B11745269
theorem B5872301 : Blo 1831617 5872301 := bstep (se 3 (by rfl) ⟨1101056, by rfl⟩ : syracuseStep 5872301 = 2202113) B2202113
theorem B3480337 : Blo 1831617 3480337 := bstep (se 2 (by rfl) ⟨1305126, by rfl⟩ : syracuseStep 3480337 = 2610253) B2610253
theorem B5872429 : Blo 1831617 5872429 := bstep (se 3 (by rfl) ⟨1101080, by rfl⟩ : syracuseStep 5872429 = 2202161) B2202161
theorem B5217169 : Blo 1831617 5217169 := bstep (se 2 (by rfl) ⟨1956438, by rfl⟩ : syracuseStep 5217169 = 3912877) B3912877
theorem B21748661 : Blo 1831617 21748661 := bstep (se 5 (by rfl) ⟨1019468, by rfl⟩ : syracuseStep 21748661 = 2038937) B2038937
theorem B3914723 : Blo 1831617 3914723 := bstep (se 1 (by rfl) ⟨2936042, by rfl⟩ : syracuseStep 3914723 = 5872085) B5872085
theorem B6183917 : Blo 1831617 6183917 := bstep (se 3 (by rfl) ⟨1159484, by rfl⟩ : syracuseStep 6183917 = 2318969) B2318969
theorem B6183971 : Blo 1831617 6183971 := bstep (se 1 (by rfl) ⟨4637978, by rfl⟩ : syracuseStep 6183971 = 9275957) B9275957
theorem B25426997 : Blo 1831617 25426997 := bstep (se 5 (by rfl) ⟨1191890, by rfl⟩ : syracuseStep 25426997 = 2383781) B2383781
theorem B3914833 : Blo 1831617 3914833 := bstep (se 2 (by rfl) ⟨1468062, by rfl⟩ : syracuseStep 3914833 = 2936125) B2936125
theorem B5217443 : Blo 1831617 5217443 := bstep (se 1 (by rfl) ⟨3913082, by rfl⟩ : syracuseStep 5217443 = 7826165) B7826165
theorem B3767555 : Blo 1831617 3767555 := bstep (se 1 (by rfl) ⟨2825666, by rfl⟩ : syracuseStep 3767555 = 5651333) B5651333
theorem B6184241 : Blo 1831617 6184241 := bstep (se 2 (by rfl) ⟨2319090, by rfl⟩ : syracuseStep 6184241 = 4638181) B4638181
theorem B9280817 : Blo 1831617 9280817 := bstep (se 2 (by rfl) ⟨3480306, by rfl⟩ : syracuseStep 9280817 = 6960613) B6960613
theorem B5217635 : Blo 1831617 5217635 := bstep (se 1 (by rfl) ⟨3913226, by rfl⟩ : syracuseStep 5217635 = 7826453) B7826453
theorem B9272717 : Blo 1831617 9272717 := bstep (se 3 (by rfl) ⟨1738634, by rfl⟩ : syracuseStep 9272717 = 3477269) B3477269
theorem B13917581 : Blo 1831617 13917581 := bstep (se 3 (by rfl) ⟨2609546, by rfl⟩ : syracuseStep 13917581 = 5219093) B5219093
theorem B4955555 : Blo 1831617 4955555 := bstep (se 1 (by rfl) ⟨3716666, by rfl⟩ : syracuseStep 4955555 = 7433333) B7433333
theorem B1957331 : Blo 1831617 1957331 := bstep (se 1 (by rfl) ⟨1467998, by rfl⟩ : syracuseStep 1957331 = 2935997) B2935997
theorem B9903779 : Blo 1831617 9903779 := bstep (se 1 (by rfl) ⟨7427834, by rfl⟩ : syracuseStep 9903779 = 14855669) B14855669
theorem B10436273 : Blo 1831617 10436273 := bstep (se 2 (by rfl) ⟨3913602, by rfl⟩ : syracuseStep 10436273 = 7827205) B7827205
theorem B18808645 : Blo 1831617 18808645 := bstep (se 4 (by rfl) ⟨1763310, by rfl⟩ : syracuseStep 18808645 = 3526621) B3526621
theorem B6184781 : Blo 1831617 6184781 := bstep (se 3 (by rfl) ⟨1159646, by rfl⟩ : syracuseStep 6184781 = 2319293) B2319293
theorem B6184835 : Blo 1831617 6184835 := bstep (se 1 (by rfl) ⟨4638626, by rfl⟩ : syracuseStep 6184835 = 9277253) B9277253
theorem B4636561 : Blo 1831617 4636561 := bstep (se 2 (by rfl) ⟨1738710, by rfl⟩ : syracuseStep 4636561 = 3477421) B3477421
theorem B23486435 : Blo 1831617 23486435 := bstep (se 1 (by rfl) ⟨17614826, by rfl⟩ : syracuseStep 23486435 = 35229653) B35229653
theorem B7938071 : Blo 1831617 7938071 := bstep (se 1 (by rfl) ⟨5953553, by rfl⟩ : syracuseStep 7938071 = 11907107) B11907107
theorem B4636723 : Blo 1831617 4636723 := bstep (se 1 (by rfl) ⟨3477542, by rfl⟩ : syracuseStep 4636723 = 6955085) B6955085
theorem B4956311 : Blo 1831617 4956311 := bstep (se 1 (by rfl) ⟨3717233, by rfl⟩ : syracuseStep 4956311 = 7434467) B7434467
theorem B3301555 : Blo 1831617 3301555 := bstep (se 1 (by rfl) ⟨2476166, by rfl⟩ : syracuseStep 3301555 = 4952333) B4952333
theorem B4636865 : Blo 1831617 4636865 := bstep (se 2 (by rfl) ⟨1738824, by rfl⟩ : syracuseStep 4636865 = 3477649) B3477649
theorem B2318539 : Blo 1831617 2318539 := bstep (se 1 (by rfl) ⟨1738904, by rfl⟩ : syracuseStep 2318539 = 3477809) B3477809
theorem B6955267 : Blo 1831617 6955267 := bstep (se 1 (by rfl) ⟨5216450, by rfl⟩ : syracuseStep 6955267 = 10432901) B10432901
theorem B39608621 : Blo 1831617 39608621 := bstep (se 3 (by rfl) ⟨7426616, by rfl⟩ : syracuseStep 39608621 = 14853233) B14853233
theorem B7831853 : Blo 1831617 7831853 := bstep (se 3 (by rfl) ⟨1468472, by rfl⟩ : syracuseStep 7831853 = 2936945) B2936945
theorem B6185267 : Blo 1831617 6185267 := bstep (se 1 (by rfl) ⟨4638950, by rfl⟩ : syracuseStep 6185267 = 9277901) B9277901
theorem B10436957 : Blo 1831617 10436957 := bstep (se 3 (by rfl) ⟨1956929, by rfl⟩ : syracuseStep 10436957 = 3913859) B3913859
theorem B14106973 : Blo 1831617 14106973 := bstep (se 3 (by rfl) ⟨2645057, by rfl⟩ : syracuseStep 14106973 = 5290115) B5290115
theorem B128647541 : Blo 1831617 128647541 := bstep (se 5 (by rfl) ⟨6030353, by rfl⟩ : syracuseStep 128647541 = 12060707) B12060707
theorem B7823789 : Blo 1831617 7823789 := bstep (se 3 (by rfl) ⟨1466960, by rfl⟩ : syracuseStep 7823789 = 2933921) B2933921
theorem B19825073 : Blo 1831617 19825073 := bstep (se 2 (by rfl) ⟨7434402, by rfl⟩ : syracuseStep 19825073 = 14868805) B14868805
theorem B7938497 : Blo 1831617 7938497 := bstep (se 2 (by rfl) ⟨2976936, by rfl⟩ : syracuseStep 7938497 = 5953873) B5953873
theorem B2318807 : Blo 1831617 2318807 := bstep (se 1 (by rfl) ⟨1739105, by rfl⟩ : syracuseStep 2318807 = 3478211) B3478211
theorem B6955571 : Blo 1831617 6955571 := bstep (se 1 (by rfl) ⟨5216678, by rfl⟩ : syracuseStep 6955571 = 10433357) B10433357
theorem B4121153 : Blo 1831617 4121153 := bstep (se 2 (by rfl) ⟨1545432, by rfl⟩ : syracuseStep 4121153 = 3090865) B3090865
theorem B6185537 : Blo 1831617 6185537 := bstep (se 2 (by rfl) ⟨2319576, by rfl⟩ : syracuseStep 6185537 = 4639153) B4639153
theorem B9282113 : Blo 1831617 9282113 := bstep (se 2 (by rfl) ⟨3480792, by rfl⟩ : syracuseStep 9282113 = 6961585) B6961585
theorem B39608963 : Blo 1831617 39608963 := bstep (se 1 (by rfl) ⟨29706722, by rfl⟩ : syracuseStep 39608963 = 59413445) B59413445
theorem B2785943 : Blo 1831617 2785943 := bstep (se 1 (by rfl) ⟨2089457, by rfl⟩ : syracuseStep 2785943 = 4178915) B4178915
theorem B3302131 : Blo 1831617 3302131 := bstep (se 1 (by rfl) ⟨2476598, by rfl⟩ : syracuseStep 3302131 = 4953197) B4953197
theorem B4121369 : Blo 1831617 4121369 := bstep (se 2 (by rfl) ⟨1545513, by rfl⟩ : syracuseStep 4121369 = 3091027) B3091027
theorem B6030155 : Blo 1831617 6030155 := bstep (se 1 (by rfl) ⟨4522616, by rfl⟩ : syracuseStep 6030155 = 9045233) B9045233
theorem B4121459 : Blo 1831617 4121459 := bstep (se 1 (by rfl) ⟨3091094, by rfl⟩ : syracuseStep 4121459 = 6182189) B6182189
theorem B4121495 : Blo 1831617 4121495 := bstep (se 1 (by rfl) ⟨3091121, by rfl⟩ : syracuseStep 4121495 = 6182243) B6182243
theorem B4121675 : Blo 1831617 4121675 := bstep (se 1 (by rfl) ⟨3091256, by rfl⟩ : syracuseStep 4121675 = 6182513) B6182513
theorem B4023371 : Blo 1831617 4023371 := bstep (se 1 (by rfl) ⟨3017528, by rfl⟩ : syracuseStep 4023371 = 6035057) B6035057
theorem B6186077 : Blo 1831617 6186077 := bstep (se 3 (by rfl) ⟨1159889, by rfl⟩ : syracuseStep 6186077 = 2319779) B2319779
theorem B4121729 : Blo 1831617 4121729 := bstep (se 2 (by rfl) ⟨1545648, by rfl⟩ : syracuseStep 4121729 = 3091297) B3091297
theorem B9274499 : Blo 1831617 9274499 := bstep (se 1 (by rfl) ⟨6955874, by rfl⟩ : syracuseStep 9274499 = 13911749) B13911749
theorem B2319511 : Blo 1831617 2319511 := bstep (se 1 (by rfl) ⟨1739633, by rfl⟩ : syracuseStep 2319511 = 3479267) B3479267
theorem B50136245 : Blo 1831617 50136245 := bstep (se 5 (by rfl) ⟨2350136, by rfl⟩ : syracuseStep 50136245 = 4700273) B4700273
theorem B6956225 : Blo 1831617 6956225 := bstep (se 2 (by rfl) ⟨2608584, by rfl⟩ : syracuseStep 6956225 = 5217169) B5217169
theorem B5219549 : Blo 1831617 5219549 := bstep (se 3 (by rfl) ⟨978665, by rfl⟩ : syracuseStep 5219549 = 1957331) B1957331
theorem B3573067 : Blo 1831617 3573067 := bstep (se 1 (by rfl) ⟨2679800, by rfl⟩ : syracuseStep 3573067 = 5359601) B5359601
theorem B4121945 : Blo 1831617 4121945 := bstep (se 2 (by rfl) ⟨1545729, by rfl⟩ : syracuseStep 4121945 = 3091459) B3091459
theorem B7431517 : Blo 1831617 7431517 := bstep (se 3 (by rfl) ⟨1393409, by rfl⟩ : syracuseStep 7431517 = 2786819) B2786819
theorem B3302795 : Blo 1831617 3302795 := bstep (se 1 (by rfl) ⟨2477096, by rfl⟩ : syracuseStep 3302795 = 4954193) B4954193
theorem B4122035 : Blo 1831617 4122035 := bstep (se 1 (by rfl) ⟨3091526, by rfl⟩ : syracuseStep 4122035 = 6183053) B6183053
theorem B4638131 : Blo 1831617 4638131 := bstep (se 1 (by rfl) ⟨3478598, by rfl⟩ : syracuseStep 4638131 = 6957197) B6957197
theorem B5219777 : Blo 1831617 5219777 := bstep (se 2 (by rfl) ⟨1957416, by rfl⟩ : syracuseStep 5219777 = 3914833) B3914833
theorem B4122071 : Blo 1831617 4122071 := bstep (se 1 (by rfl) ⟨3091553, by rfl⟩ : syracuseStep 4122071 = 6183107) B6183107
theorem B2090539 : Blo 1831617 2090539 := bstep (se 1 (by rfl) ⟨1567904, by rfl⟩ : syracuseStep 2090539 = 3135809) B3135809
theorem B4122251 : Blo 1831617 4122251 := bstep (se 1 (by rfl) ⟨3091688, by rfl⟩ : syracuseStep 4122251 = 6183377) B6183377
theorem B4122305 : Blo 1831617 4122305 := bstep (se 2 (by rfl) ⟨1545864, by rfl⟩ : syracuseStep 4122305 = 3091729) B3091729
theorem B5220119 : Blo 1831617 5220119 := bstep (se 1 (by rfl) ⟨3915089, by rfl⟩ : syracuseStep 5220119 = 7830179) B7830179
theorem B4179737 : Blo 1831617 4179737 := bstep (se 2 (by rfl) ⟨1567401, by rfl⟩ : syracuseStep 4179737 = 3134803) B3134803
theorem B4122521 : Blo 1831617 4122521 := bstep (se 2 (by rfl) ⟨1545945, by rfl⟩ : syracuseStep 4122521 = 3091891) B3091891
theorem B6604723 : Blo 1831617 6604723 := bstep (se 1 (by rfl) ⟨4953542, by rfl⟩ : syracuseStep 6604723 = 9907085) B9907085
theorem B4638667 : Blo 1831617 4638667 := bstep (se 1 (by rfl) ⟨3479000, by rfl⟩ : syracuseStep 4638667 = 6958001) B6958001
theorem B4122611 : Blo 1831617 4122611 := bstep (se 1 (by rfl) ⟨3091958, by rfl⟩ : syracuseStep 4122611 = 6183917) B6183917
theorem B4122647 : Blo 1831617 4122647 := bstep (se 1 (by rfl) ⟨3091985, by rfl⟩ : syracuseStep 4122647 = 6183971) B6183971
theorem B16951331 : Blo 1831617 16951331 := bstep (se 1 (by rfl) ⟨12713498, by rfl⟩ : syracuseStep 16951331 = 25426997) B25426997
theorem B4638809 : Blo 1831617 4638809 := bstep (se 2 (by rfl) ⟨1739553, by rfl⟩ : syracuseStep 4638809 = 3479107) B3479107
theorem B4122827 : Blo 1831617 4122827 := bstep (se 1 (by rfl) ⟨3092120, by rfl⟩ : syracuseStep 4122827 = 6184241) B6184241
theorem B6187211 : Blo 1831617 6187211 := bstep (se 1 (by rfl) ⟨4640408, by rfl⟩ : syracuseStep 6187211 = 9280817) B9280817
theorem B4122881 : Blo 1831617 4122881 := bstep (se 2 (by rfl) ⟨1546080, by rfl⟩ : syracuseStep 4122881 = 3092161) B3092161
theorem B3303703 : Blo 1831617 3303703 := bstep (se 1 (by rfl) ⟨2477777, by rfl⟩ : syracuseStep 3303703 = 4955555) B4955555
theorem B6957485 : Blo 1831617 6957485 := bstep (se 3 (by rfl) ⟨1304528, by rfl⟩ : syracuseStep 6957485 = 2609057) B2609057
theorem B25078193 : Blo 1831617 25078193 := bstep (se 2 (by rfl) ⟨9404322, by rfl⟩ : syracuseStep 25078193 = 18808645) B18808645
theorem B6957515 : Blo 1831617 6957515 := bstep (se 1 (by rfl) ⟨5218136, by rfl⟩ : syracuseStep 6957515 = 10436273) B10436273
theorem B4123097 : Blo 1831617 4123097 := bstep (se 2 (by rfl) ⟨1546161, by rfl⟩ : syracuseStep 4123097 = 3092323) B3092323
theorem B6187481 : Blo 1831617 6187481 := bstep (se 2 (by rfl) ⟨2320305, by rfl⟩ : syracuseStep 6187481 = 4640611) B4640611
theorem B4123187 : Blo 1831617 4123187 := bstep (se 1 (by rfl) ⟨3092390, by rfl⟩ : syracuseStep 4123187 = 6184781) B6184781
theorem B4123223 : Blo 1831617 4123223 := bstep (se 1 (by rfl) ⟨3092417, by rfl⟩ : syracuseStep 4123223 = 6184835) B6184835
theorem B14297701 : Blo 1831617 14297701 := bstep (se 4 (by rfl) ⟨1340409, by rfl⟩ : syracuseStep 14297701 = 2680819) B2680819
theorem B15657623 : Blo 1831617 15657623 := bstep (se 1 (by rfl) ⟨11743217, by rfl⟩ : syracuseStep 15657623 = 23486435) B23486435
theorem B4401881 : Blo 1831617 4401881 := bstep (se 2 (by rfl) ⟨1650705, by rfl⟩ : syracuseStep 4401881 = 3301411) B3301411
theorem B4123403 : Blo 1831617 4123403 := bstep (se 1 (by rfl) ⟨3092552, by rfl⟩ : syracuseStep 4123403 = 6185105) B6185105
theorem B10439441 : Blo 1831617 10439441 := bstep (se 2 (by rfl) ⟨3914790, by rfl⟩ : syracuseStep 10439441 = 7829581) B7829581
theorem B3091223 : Blo 1831617 3091223 := bstep (se 1 (by rfl) ⟨2318417, by rfl⟩ : syracuseStep 3091223 = 4636835) B4636835
theorem B4123457 : Blo 1831617 4123457 := bstep (se 2 (by rfl) ⟨1546296, by rfl⟩ : syracuseStep 4123457 = 3092593) B3092593
theorem B3091351 : Blo 1831617 3091351 := bstep (se 1 (by rfl) ⟨2318513, by rfl⟩ : syracuseStep 3091351 = 4637027) B4637027
theorem B4639639 : Blo 1831617 4639639 := bstep (se 1 (by rfl) ⟨3479729, by rfl⟩ : syracuseStep 4639639 = 6959459) B6959459
theorem B31304717 : Blo 1831617 31304717 := bstep (se 3 (by rfl) ⟨5869634, by rfl⟩ : syracuseStep 31304717 = 11739269) B11739269
theorem B3714071 : Blo 1831617 3714071 := bstep (se 1 (by rfl) ⟨2785553, by rfl⟩ : syracuseStep 3714071 = 5571107) B5571107
theorem B4123673 : Blo 1831617 4123673 := bstep (se 2 (by rfl) ⟨1546377, by rfl⟩ : syracuseStep 4123673 = 3092755) B3092755
theorem B6958169 : Blo 1831617 6958169 := bstep (se 2 (by rfl) ⟨2609313, by rfl⟩ : syracuseStep 6958169 = 5218627) B5218627
theorem B4123763 : Blo 1831617 4123763 := bstep (se 1 (by rfl) ⟨3092822, by rfl⟩ : syracuseStep 4123763 = 6185645) B6185645
theorem B2747531 : Blo 1831617 2747531 := bstep (se 1 (by rfl) ⟨2060648, by rfl⟩ : syracuseStep 2747531 = 4121297) B4121297
theorem B2747543 : Blo 1831617 2747543 := bstep (se 1 (by rfl) ⟨2060657, by rfl⟩ : syracuseStep 2747543 = 4121315) B4121315
theorem B13388951 : Blo 1831617 13388951 := bstep (se 1 (by rfl) ⟨10041713, by rfl⟩ : syracuseStep 13388951 = 20083427) B20083427
theorem B4123799 : Blo 1831617 4123799 := bstep (se 1 (by rfl) ⟨3092849, by rfl⟩ : syracuseStep 4123799 = 6185699) B6185699
theorem B6188183 : Blo 1831617 6188183 := bstep (se 1 (by rfl) ⟨4641137, by rfl⟩ : syracuseStep 6188183 = 9282275) B9282275
theorem B2747609 : Blo 1831617 2747609 := bstep (se 2 (by rfl) ⟨1030353, by rfl⟩ : syracuseStep 2747609 = 2060707) B2060707
theorem B2747723 : Blo 1831617 2747723 := bstep (se 1 (by rfl) ⟨2060792, by rfl⟩ : syracuseStep 2747723 = 4121585) B4121585
theorem B4123979 : Blo 1831617 4123979 := bstep (se 1 (by rfl) ⟨3092984, by rfl⟩ : syracuseStep 4123979 = 6185969) B6185969
theorem B4640075 : Blo 1831617 4640075 := bstep (se 1 (by rfl) ⟨3480056, by rfl⟩ : syracuseStep 4640075 = 6960113) B6960113
theorem B2747735 : Blo 1831617 2747735 := bstep (se 1 (by rfl) ⟨2060801, by rfl⟩ : syracuseStep 2747735 = 4121603) B4121603
theorem B4124033 : Blo 1831617 4124033 := bstep (se 2 (by rfl) ⟨1546512, by rfl⟩ : syracuseStep 4124033 = 3093025) B3093025
theorem B6958487 : Blo 1831617 6958487 := bstep (se 1 (by rfl) ⟨5218865, by rfl⟩ : syracuseStep 6958487 = 10437731) B10437731
theorem B2747801 : Blo 1831617 2747801 := bstep (se 2 (by rfl) ⟨1030425, by rfl⟩ : syracuseStep 2747801 = 2060851) B2060851
theorem B3526067 : Blo 1831617 3526067 := bstep (se 1 (by rfl) ⟨2644550, by rfl⟩ : syracuseStep 3526067 = 5289101) B5289101
theorem B2747915 : Blo 1831617 2747915 := bstep (se 1 (by rfl) ⟨2060936, by rfl⟩ : syracuseStep 2747915 = 4121873) B4121873
theorem B3091979 : Blo 1831617 3091979 := bstep (se 1 (by rfl) ⟨2318984, by rfl⟩ : syracuseStep 3091979 = 4637969) B4637969
theorem B2747927 : Blo 1831617 2747927 := bstep (se 1 (by rfl) ⟨2060945, by rfl⟩ : syracuseStep 2747927 = 4121891) B4121891
theorem B2936407 : Blo 1831617 2936407 := bstep (se 1 (by rfl) ⟨2202305, by rfl⟩ : syracuseStep 2936407 = 4404611) B4404611
theorem B2747993 : Blo 1831617 2747993 := bstep (se 2 (by rfl) ⟨1030497, by rfl⟩ : syracuseStep 2747993 = 2060995) B2060995
theorem B4124249 : Blo 1831617 4124249 := bstep (se 2 (by rfl) ⟨1546593, by rfl⟩ : syracuseStep 4124249 = 3093187) B3093187
theorem B13913693 : Blo 1831617 13913693 := bstep (se 3 (by rfl) ⟨2608817, by rfl⟩ : syracuseStep 13913693 = 5217635) B5217635
theorem B3092107 : Blo 1831617 3092107 := bstep (se 1 (by rfl) ⟨2319080, by rfl⟩ : syracuseStep 3092107 = 4638161) B4638161
theorem B10432151 : Blo 1831617 10432151 := bstep (se 1 (by rfl) ⟨7824113, by rfl⟩ : syracuseStep 10432151 = 15648227) B15648227
theorem B4124339 : Blo 1831617 4124339 := bstep (se 1 (by rfl) ⟨3093254, by rfl⟩ : syracuseStep 4124339 = 6186509) B6186509
theorem B7827137 : Blo 1831617 7827137 := bstep (se 2 (by rfl) ⟨2935176, by rfl⟩ : syracuseStep 7827137 = 5870353) B5870353
theorem B4640449 : Blo 1831617 4640449 := bstep (se 2 (by rfl) ⟨1740168, by rfl⟩ : syracuseStep 4640449 = 3480337) B3480337
theorem B2748107 : Blo 1831617 2748107 := bstep (se 1 (by rfl) ⟨2061080, by rfl⟩ : syracuseStep 2748107 = 4122161) B4122161
theorem B2748119 : Blo 1831617 2748119 := bstep (se 1 (by rfl) ⟨2061089, by rfl⟩ : syracuseStep 2748119 = 4122179) B4122179
theorem B4124375 : Blo 1831617 4124375 := bstep (se 1 (by rfl) ⟨3093281, by rfl⟩ : syracuseStep 4124375 = 6186563) B6186563
theorem B2748185 : Blo 1831617 2748185 := bstep (se 2 (by rfl) ⟨1030569, by rfl⟩ : syracuseStep 2748185 = 2061139) B2061139
theorem B3092249 : Blo 1831617 3092249 := bstep (se 2 (by rfl) ⟨1159593, by rfl⟩ : syracuseStep 3092249 = 2319187) B2319187
theorem B20877101 : Blo 1831617 20877101 := bstep (se 3 (by rfl) ⟨3914456, by rfl⟩ : syracuseStep 20877101 = 7828913) B7828913
theorem B52842293 : Blo 1831617 52842293 := bstep (se 5 (by rfl) ⟨2476982, by rfl⟩ : syracuseStep 52842293 = 4953965) B4953965
theorem B18804545 : Blo 1831617 18804545 := bstep (se 2 (by rfl) ⟨7051704, by rfl⟩ : syracuseStep 18804545 = 14103409) B14103409
theorem B3477323 : Blo 1831617 3477323 := bstep (se 1 (by rfl) ⟨2607992, by rfl⟩ : syracuseStep 3477323 = 5215985) B5215985
theorem B2936663 : Blo 1831617 2936663 := bstep (se 1 (by rfl) ⟨2202497, by rfl⟩ : syracuseStep 2936663 = 4404995) B4404995
theorem B2748299 : Blo 1831617 2748299 := bstep (se 1 (by rfl) ⟨2061224, by rfl⟩ : syracuseStep 2748299 = 4122449) B4122449
theorem B4124555 : Blo 1831617 4124555 := bstep (se 1 (by rfl) ⟨3093416, by rfl⟩ : syracuseStep 4124555 = 6186833) B6186833
theorem B2748311 : Blo 1831617 2748311 := bstep (se 1 (by rfl) ⟨2061233, by rfl⟩ : syracuseStep 2748311 = 4122467) B4122467
theorem B3092377 : Blo 1831617 3092377 := bstep (se 2 (by rfl) ⟨1159641, by rfl⟩ : syracuseStep 3092377 = 2319283) B2319283
theorem B19812275 : Blo 1831617 19812275 := bstep (se 1 (by rfl) ⟨14859206, by rfl⟩ : syracuseStep 19812275 = 29718413) B29718413
theorem B4124609 : Blo 1831617 4124609 := bstep (se 2 (by rfl) ⟨1546728, by rfl⟩ : syracuseStep 4124609 = 3093457) B3093457
theorem B2748377 : Blo 1831617 2748377 := bstep (se 2 (by rfl) ⟨1030641, by rfl⟩ : syracuseStep 2748377 = 2061283) B2061283
theorem B3477505 : Blo 1831617 3477505 := bstep (se 2 (by rfl) ⟨1304064, by rfl⟩ : syracuseStep 3477505 = 2608129) B2608129
theorem B7827479 : Blo 1831617 7827479 := bstep (se 1 (by rfl) ⟨5870609, by rfl⟩ : syracuseStep 7827479 = 11741219) B11741219
theorem B6959155 : Blo 1831617 6959155 := bstep (se 1 (by rfl) ⟨5219366, by rfl⟩ : syracuseStep 6959155 = 10438733) B10438733
theorem B2748491 : Blo 1831617 2748491 := bstep (se 1 (by rfl) ⟨2061368, by rfl⟩ : syracuseStep 2748491 = 4122737) B4122737
theorem B2748503 : Blo 1831617 2748503 := bstep (se 1 (by rfl) ⟨2061377, by rfl⟩ : syracuseStep 2748503 = 4122755) B4122755
theorem B11292803 : Blo 1831617 11292803 := bstep (se 1 (by rfl) ⟨8469602, by rfl⟩ : syracuseStep 11292803 = 16939205) B16939205
theorem B2748569 : Blo 1831617 2748569 := bstep (se 2 (by rfl) ⟨1030713, by rfl⟩ : syracuseStep 2748569 = 2061427) B2061427
theorem B4124825 : Blo 1831617 4124825 := bstep (se 2 (by rfl) ⟨1546809, by rfl⟩ : syracuseStep 4124825 = 3093619) B3093619
theorem B2937035 : Blo 1831617 2937035 := bstep (se 1 (by rfl) ⟨2202776, by rfl⟩ : syracuseStep 2937035 = 4405553) B4405553
theorem B4124915 : Blo 1831617 4124915 := bstep (se 1 (by rfl) ⟨3093686, by rfl⟩ : syracuseStep 4124915 = 6187373) B6187373
theorem B2748683 : Blo 1831617 2748683 := bstep (se 1 (by rfl) ⟨2061512, by rfl⟩ : syracuseStep 2748683 = 4123025) B4123025
theorem B2748695 : Blo 1831617 2748695 := bstep (se 1 (by rfl) ⟨2061521, by rfl⟩ : syracuseStep 2748695 = 4123043) B4123043
theorem B4124951 : Blo 1831617 4124951 := bstep (se 1 (by rfl) ⟨3093713, by rfl⟩ : syracuseStep 4124951 = 6187427) B6187427
theorem B4641047 : Blo 1831617 4641047 := bstep (se 1 (by rfl) ⟨3480785, by rfl⟩ : syracuseStep 4641047 = 6961571) B6961571
theorem B2060599 : Blo 1831617 2060599 := bstep (se 1 (by rfl) ⟨1545449, by rfl⟩ : syracuseStep 2060599 = 3090899) B3090899
theorem B2748761 : Blo 1831617 2748761 := bstep (se 2 (by rfl) ⟨1030785, by rfl⟩ : syracuseStep 2748761 = 2061571) B2061571
theorem B3912065 : Blo 1831617 3912065 := bstep (se 2 (by rfl) ⟨1467024, by rfl⟩ : syracuseStep 3912065 = 2934049) B2934049
theorem B3477953 : Blo 1831617 3477953 := bstep (se 2 (by rfl) ⟨1304232, by rfl⟩ : syracuseStep 3477953 = 2608465) B2608465
theorem B2748875 : Blo 1831617 2748875 := bstep (se 1 (by rfl) ⟨2061656, by rfl⟩ : syracuseStep 2748875 = 4123313) B4123313
theorem B4125131 : Blo 1831617 4125131 := bstep (se 1 (by rfl) ⟨3093848, by rfl⟩ : syracuseStep 4125131 = 6187697) B6187697
theorem B3912151 : Blo 1831617 3912151 := bstep (se 1 (by rfl) ⟨2934113, by rfl⟩ : syracuseStep 3912151 = 5868227) B5868227
theorem B2748887 : Blo 1831617 2748887 := bstep (se 1 (by rfl) ⟨2061665, by rfl⟩ : syracuseStep 2748887 = 4123331) B4123331
theorem B17609177 : Blo 1831617 17609177 := bstep (se 2 (by rfl) ⟨6603441, by rfl⟩ : syracuseStep 17609177 = 13206883) B13206883
theorem B3092951 : Blo 1831617 3092951 := bstep (se 1 (by rfl) ⟨2319713, by rfl⟩ : syracuseStep 3092951 = 4639427) B4639427
theorem B5870045 : Blo 1831617 5870045 := bstep (se 3 (by rfl) ⟨1100633, by rfl⟩ : syracuseStep 5870045 = 2201267) B2201267
theorem B2060779 : Blo 1831617 2060779 := bstep (se 1 (by rfl) ⟨1545584, by rfl⟩ : syracuseStep 2060779 = 3091169) B3091169
theorem B4125185 : Blo 1831617 4125185 := bstep (se 2 (by rfl) ⟨1546944, by rfl⟩ : syracuseStep 4125185 = 3093889) B3093889
theorem B2748953 : Blo 1831617 2748953 := bstep (se 2 (by rfl) ⟨1030857, by rfl⟩ : syracuseStep 2748953 = 2061715) B2061715
theorem B2060887 : Blo 1831617 2060887 := bstep (se 1 (by rfl) ⟨1545665, by rfl⟩ : syracuseStep 2060887 = 3091331) B3091331
theorem B3093079 : Blo 1831617 3093079 := bstep (se 1 (by rfl) ⟨2319809, by rfl⟩ : syracuseStep 3093079 = 4639619) B4639619
theorem B2749067 : Blo 1831617 2749067 := bstep (se 1 (by rfl) ⟨2061800, by rfl⟩ : syracuseStep 2749067 = 4123601) B4123601
theorem B2749079 : Blo 1831617 2749079 := bstep (se 1 (by rfl) ⟨2061809, by rfl⟩ : syracuseStep 2749079 = 4123619) B4123619
theorem B2609815 : Blo 1831617 2609815 := bstep (se 1 (by rfl) ⟨1957361, by rfl⟩ : syracuseStep 2609815 = 3914723) B3914723
theorem B1831627 : Blo 1831617 1831627 := bstep (se 1 (by rfl) ⟨1373720, by rfl⟩ : syracuseStep 1831627 = 2747441) B2747441
theorem B1831639 : Blo 1831617 1831639 := bstep (se 1 (by rfl) ⟨1373729, by rfl⟩ : syracuseStep 1831639 = 2747459) B2747459
theorem B2749145 : Blo 1831617 2749145 := bstep (se 2 (by rfl) ⟨1030929, by rfl⟩ : syracuseStep 2749145 = 2061859) B2061859
theorem B4125401 : Blo 1831617 4125401 := bstep (se 2 (by rfl) ⟨1547025, by rfl⟩ : syracuseStep 4125401 = 3094051) B3094051
theorem B1831659 : Blo 1831617 1831659 := bstep (se 1 (by rfl) ⟨1373744, by rfl⟩ : syracuseStep 1831659 = 2747489) B2747489
theorem B1831671 : Blo 1831617 1831671 := bstep (se 1 (by rfl) ⟨1373753, by rfl⟩ : syracuseStep 1831671 = 2747507) B2747507
theorem B1831691 : Blo 1831617 1831691 := bstep (se 1 (by rfl) ⟨1373768, by rfl⟩ : syracuseStep 1831691 = 2747537) B2747537
theorem B2061067 : Blo 1831617 2061067 := bstep (se 1 (by rfl) ⟨1545800, by rfl⟩ : syracuseStep 2061067 = 3091601) B3091601
theorem B9278225 : Blo 1831617 9278225 := bstep (se 2 (by rfl) ⟨3479334, by rfl⟩ : syracuseStep 9278225 = 6958669) B6958669
theorem B1831703 : Blo 1831617 1831703 := bstep (se 1 (by rfl) ⟨1373777, by rfl⟩ : syracuseStep 1831703 = 2747555) B2747555
theorem B3478295 : Blo 1831617 3478295 := bstep (se 1 (by rfl) ⟨2608721, by rfl⟩ : syracuseStep 3478295 = 5217443) B5217443
theorem B1831723 : Blo 1831617 1831723 := bstep (se 1 (by rfl) ⟨1373792, by rfl⟩ : syracuseStep 1831723 = 2747585) B2747585
theorem B4125491 : Blo 1831617 4125491 := bstep (se 1 (by rfl) ⟨3094118, by rfl⟩ : syracuseStep 4125491 = 6188237) B6188237
theorem B1831735 : Blo 1831617 1831735 := bstep (se 1 (by rfl) ⟨1373801, by rfl⟩ : syracuseStep 1831735 = 2747603) B2747603
theorem B1831755 : Blo 1831617 1831755 := bstep (se 1 (by rfl) ⟨1373816, by rfl⟩ : syracuseStep 1831755 = 2747633) B2747633
theorem B2749259 : Blo 1831617 2749259 := bstep (se 1 (by rfl) ⟨2061944, by rfl⟩ : syracuseStep 2749259 = 4123889) B4123889
theorem B1831767 : Blo 1831617 1831767 := bstep (se 1 (by rfl) ⟨1373825, by rfl⟩ : syracuseStep 1831767 = 2747651) B2747651
theorem B2749271 : Blo 1831617 2749271 := bstep (se 1 (by rfl) ⟨2061953, by rfl⟩ : syracuseStep 2749271 = 4123907) B4123907
theorem B2511703 : Blo 1831617 2511703 := bstep (se 1 (by rfl) ⟨1883777, by rfl⟩ : syracuseStep 2511703 = 3767555) B3767555
theorem B4125527 : Blo 1831617 4125527 := bstep (se 1 (by rfl) ⟨3094145, by rfl⟩ : syracuseStep 4125527 = 6188291) B6188291
theorem B1831787 : Blo 1831617 1831787 := bstep (se 1 (by rfl) ⟨1373840, by rfl⟩ : syracuseStep 1831787 = 2747681) B2747681
theorem B1831799 : Blo 1831617 1831799 := bstep (se 1 (by rfl) ⟨1373849, by rfl⟩ : syracuseStep 1831799 = 2747699) B2747699
theorem B2061175 : Blo 1831617 2061175 := bstep (se 1 (by rfl) ⟨1545881, by rfl⟩ : syracuseStep 2061175 = 3091763) B3091763
theorem B1831819 : Blo 1831617 1831819 := bstep (se 1 (by rfl) ⟨1373864, by rfl⟩ : syracuseStep 1831819 = 2747729) B2747729
theorem B1831831 : Blo 1831617 1831831 := bstep (se 1 (by rfl) ⟨1373873, by rfl⟩ : syracuseStep 1831831 = 2747747) B2747747
theorem B2749337 : Blo 1831617 2749337 := bstep (se 2 (by rfl) ⟨1031001, by rfl⟩ : syracuseStep 2749337 = 2062003) B2062003
theorem B1831851 : Blo 1831617 1831851 := bstep (se 1 (by rfl) ⟨1373888, by rfl⟩ : syracuseStep 1831851 = 2747777) B2747777
theorem B6181811 : Blo 1831617 6181811 := bstep (se 1 (by rfl) ⟨4636358, by rfl⟩ : syracuseStep 6181811 = 9272717) B9272717
theorem B9278387 : Blo 1831617 9278387 := bstep (se 1 (by rfl) ⟨6958790, by rfl⟩ : syracuseStep 9278387 = 13917581) B13917581
theorem B1831863 : Blo 1831617 1831863 := bstep (se 1 (by rfl) ⟨1373897, by rfl⟩ : syracuseStep 1831863 = 2747795) B2747795
theorem B1831883 : Blo 1831617 1831883 := bstep (se 1 (by rfl) ⟨1373912, by rfl⟩ : syracuseStep 1831883 = 2747825) B2747825
theorem B1831895 : Blo 1831617 1831895 := bstep (se 1 (by rfl) ⟨1373921, by rfl⟩ : syracuseStep 1831895 = 2747843) B2747843
theorem B1831915 : Blo 1831617 1831915 := bstep (se 1 (by rfl) ⟨1373936, by rfl⟩ : syracuseStep 1831915 = 2747873) B2747873
theorem B1831927 : Blo 1831617 1831927 := bstep (se 1 (by rfl) ⟨1373945, by rfl⟩ : syracuseStep 1831927 = 2747891) B2747891
theorem B1831947 : Blo 1831617 1831947 := bstep (se 1 (by rfl) ⟨1373960, by rfl⟩ : syracuseStep 1831947 = 2747921) B2747921
theorem B2749451 : Blo 1831617 2749451 := bstep (se 1 (by rfl) ⟨2062088, by rfl⟩ : syracuseStep 2749451 = 4124177) B4124177
theorem B1831959 : Blo 1831617 1831959 := bstep (se 1 (by rfl) ⟨1373969, by rfl⟩ : syracuseStep 1831959 = 2747939) B2747939
theorem B2749463 : Blo 1831617 2749463 := bstep (se 1 (by rfl) ⟨2062097, by rfl⟩ : syracuseStep 2749463 = 4124195) B4124195
theorem B1831979 : Blo 1831617 1831979 := bstep (se 1 (by rfl) ⟨1373984, by rfl⟩ : syracuseStep 1831979 = 2747969) B2747969
theorem B2061355 : Blo 1831617 2061355 := bstep (se 1 (by rfl) ⟨1546016, by rfl⟩ : syracuseStep 2061355 = 3092033) B3092033
theorem B1831991 : Blo 1831617 1831991 := bstep (se 1 (by rfl) ⟨1373993, by rfl⟩ : syracuseStep 1831991 = 2747987) B2747987
theorem B1832011 : Blo 1831617 1832011 := bstep (se 1 (by rfl) ⟨1374008, by rfl⟩ : syracuseStep 1832011 = 2748017) B2748017
theorem B1832023 : Blo 1831617 1832023 := bstep (se 1 (by rfl) ⟨1374017, by rfl⟩ : syracuseStep 1832023 = 2748035) B2748035
theorem B2749529 : Blo 1831617 2749529 := bstep (se 2 (by rfl) ⟨1031073, by rfl⟩ : syracuseStep 2749529 = 2062147) B2062147
theorem B1832043 : Blo 1831617 1832043 := bstep (se 1 (by rfl) ⟨1374032, by rfl⟩ : syracuseStep 1832043 = 2748065) B2748065
theorem B1832055 : Blo 1831617 1832055 := bstep (se 1 (by rfl) ⟨1374041, by rfl⟩ : syracuseStep 1832055 = 2748083) B2748083
theorem B1832075 : Blo 1831617 1832075 := bstep (se 1 (by rfl) ⟨1374056, by rfl⟩ : syracuseStep 1832075 = 2748113) B2748113
theorem B1832087 : Blo 1831617 1832087 := bstep (se 1 (by rfl) ⟨1374065, by rfl⟩ : syracuseStep 1832087 = 2748131) B2748131
theorem B2061463 : Blo 1831617 2061463 := bstep (se 1 (by rfl) ⟨1546097, by rfl⟩ : syracuseStep 2061463 = 3092195) B3092195
theorem B1832107 : Blo 1831617 1832107 := bstep (se 1 (by rfl) ⟨1374080, by rfl⟩ : syracuseStep 1832107 = 2748161) B2748161
theorem B1832119 : Blo 1831617 1832119 := bstep (se 1 (by rfl) ⟨1374089, by rfl⟩ : syracuseStep 1832119 = 2748179) B2748179
theorem B6182081 : Blo 1831617 6182081 := bstep (se 2 (by rfl) ⟨2318280, by rfl⟩ : syracuseStep 6182081 = 4636561) B4636561
theorem B1832139 : Blo 1831617 1832139 := bstep (se 1 (by rfl) ⟨1374104, by rfl⟩ : syracuseStep 1832139 = 2748209) B2748209
theorem B2749643 : Blo 1831617 2749643 := bstep (se 1 (by rfl) ⟨2062232, by rfl⟩ : syracuseStep 2749643 = 4124465) B4124465
theorem B3093707 : Blo 1831617 3093707 := bstep (se 1 (by rfl) ⟨2320280, by rfl⟩ : syracuseStep 3093707 = 4640561) B4640561
theorem B1832151 : Blo 1831617 1832151 := bstep (se 1 (by rfl) ⟨1374113, by rfl⟩ : syracuseStep 1832151 = 2748227) B2748227
theorem B2749655 : Blo 1831617 2749655 := bstep (se 1 (by rfl) ⟨2062241, by rfl⟩ : syracuseStep 2749655 = 4124483) B4124483
theorem B1832171 : Blo 1831617 1832171 := bstep (se 1 (by rfl) ⟨1374128, by rfl⟩ : syracuseStep 1832171 = 2748257) B2748257
theorem B1832183 : Blo 1831617 1832183 := bstep (se 1 (by rfl) ⟨1374137, by rfl⟩ : syracuseStep 1832183 = 2748275) B2748275
theorem B1832203 : Blo 1831617 1832203 := bstep (se 1 (by rfl) ⟨1374152, by rfl⟩ : syracuseStep 1832203 = 2748305) B2748305
theorem B6960401 : Blo 1831617 6960401 := bstep (se 2 (by rfl) ⟨2610150, by rfl⟩ : syracuseStep 6960401 = 5220301) B5220301
theorem B1832215 : Blo 1831617 1832215 := bstep (se 1 (by rfl) ⟨1374161, by rfl⟩ : syracuseStep 1832215 = 2748323) B2748323
theorem B2749721 : Blo 1831617 2749721 := bstep (se 2 (by rfl) ⟨1031145, by rfl⟩ : syracuseStep 2749721 = 2062291) B2062291
theorem B1832235 : Blo 1831617 1832235 := bstep (se 1 (by rfl) ⟨1374176, by rfl⟩ : syracuseStep 1832235 = 2748353) B2748353
theorem B1832247 : Blo 1831617 1832247 := bstep (se 1 (by rfl) ⟨1374185, by rfl⟩ : syracuseStep 1832247 = 2748371) B2748371
theorem B1832267 : Blo 1831617 1832267 := bstep (se 1 (by rfl) ⟨1374200, by rfl⟩ : syracuseStep 1832267 = 2748401) B2748401
theorem B2061643 : Blo 1831617 2061643 := bstep (se 1 (by rfl) ⟨1546232, by rfl⟩ : syracuseStep 2061643 = 3092465) B3092465
theorem B3093835 : Blo 1831617 3093835 := bstep (se 1 (by rfl) ⟨2320376, by rfl⟩ : syracuseStep 3093835 = 4640753) B4640753
theorem B1832279 : Blo 1831617 1832279 := bstep (se 1 (by rfl) ⟨1374209, by rfl⟩ : syracuseStep 1832279 = 2748419) B2748419
theorem B1832299 : Blo 1831617 1832299 := bstep (se 1 (by rfl) ⟨1374224, by rfl⟩ : syracuseStep 1832299 = 2748449) B2748449
theorem B1832311 : Blo 1831617 1832311 := bstep (se 1 (by rfl) ⟨1374233, by rfl⟩ : syracuseStep 1832311 = 2748467) B2748467
theorem B1832331 : Blo 1831617 1832331 := bstep (se 1 (by rfl) ⟨1374248, by rfl⟩ : syracuseStep 1832331 = 2748497) B2748497
theorem B2749835 : Blo 1831617 2749835 := bstep (se 1 (by rfl) ⟨2062376, by rfl⟩ : syracuseStep 2749835 = 4124753) B4124753
theorem B1832343 : Blo 1831617 1832343 := bstep (se 1 (by rfl) ⟨1374257, by rfl⟩ : syracuseStep 1832343 = 2748515) B2748515
theorem B2749847 : Blo 1831617 2749847 := bstep (se 1 (by rfl) ⟨2062385, by rfl⟩ : syracuseStep 2749847 = 4124771) B4124771
theorem B1832363 : Blo 1831617 1832363 := bstep (se 1 (by rfl) ⟨1374272, by rfl⟩ : syracuseStep 1832363 = 2748545) B2748545
theorem B3478963 : Blo 1831617 3478963 := bstep (se 1 (by rfl) ⟨2609222, by rfl⟩ : syracuseStep 3478963 = 5218445) B5218445
theorem B1832375 : Blo 1831617 1832375 := bstep (se 1 (by rfl) ⟨1374281, by rfl⟩ : syracuseStep 1832375 = 2748563) B2748563
theorem B2061751 : Blo 1831617 2061751 := bstep (se 1 (by rfl) ⟨1546313, by rfl⟩ : syracuseStep 2061751 = 3092627) B3092627
theorem B1832395 : Blo 1831617 1832395 := bstep (se 1 (by rfl) ⟨1374296, by rfl⟩ : syracuseStep 1832395 = 2748593) B2748593
theorem B1832407 : Blo 1831617 1832407 := bstep (se 1 (by rfl) ⟨1374305, by rfl⟩ : syracuseStep 1832407 = 2748611) B2748611
theorem B2749913 : Blo 1831617 2749913 := bstep (se 2 (by rfl) ⟨1031217, by rfl⟩ : syracuseStep 2749913 = 2062435) B2062435
theorem B3093977 : Blo 1831617 3093977 := bstep (se 2 (by rfl) ⟨1160241, by rfl⟩ : syracuseStep 3093977 = 2320483) B2320483
theorem B1832427 : Blo 1831617 1832427 := bstep (se 1 (by rfl) ⟨1374320, by rfl⟩ : syracuseStep 1832427 = 2748641) B2748641
theorem B1832439 : Blo 1831617 1832439 := bstep (se 1 (by rfl) ⟨1374329, by rfl⟩ : syracuseStep 1832439 = 2748659) B2748659
theorem B1832459 : Blo 1831617 1832459 := bstep (se 1 (by rfl) ⟨1374344, by rfl⟩ : syracuseStep 1832459 = 2748689) B2748689
theorem B1832471 : Blo 1831617 1832471 := bstep (se 1 (by rfl) ⟨1374353, by rfl⟩ : syracuseStep 1832471 = 2748707) B2748707
theorem B1832491 : Blo 1831617 1832491 := bstep (se 1 (by rfl) ⟨1374368, by rfl⟩ : syracuseStep 1832491 = 2748737) B2748737
theorem B1832503 : Blo 1831617 1832503 := bstep (se 1 (by rfl) ⟨1374377, by rfl⟩ : syracuseStep 1832503 = 2748755) B2748755
theorem B1832523 : Blo 1831617 1832523 := bstep (se 1 (by rfl) ⟨1374392, by rfl⟩ : syracuseStep 1832523 = 2748785) B2748785
theorem B2750027 : Blo 1831617 2750027 := bstep (se 1 (by rfl) ⟨2062520, by rfl⟩ : syracuseStep 2750027 = 4125041) B4125041
theorem B1832535 : Blo 1831617 1832535 := bstep (se 1 (by rfl) ⟨1374401, by rfl⟩ : syracuseStep 1832535 = 2748803) B2748803
theorem B2750039 : Blo 1831617 2750039 := bstep (se 1 (by rfl) ⟨2062529, by rfl⟩ : syracuseStep 2750039 = 4125059) B4125059
theorem B3094105 : Blo 1831617 3094105 := bstep (se 2 (by rfl) ⟨1160289, by rfl⟩ : syracuseStep 3094105 = 2320579) B2320579
theorem B1832555 : Blo 1831617 1832555 := bstep (se 1 (by rfl) ⟨1374416, by rfl⟩ : syracuseStep 1832555 = 2748833) B2748833
theorem B2061931 : Blo 1831617 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B1832567 : Blo 1831617 1832567 := bstep (se 1 (by rfl) ⟨1374425, by rfl⟩ : syracuseStep 1832567 = 2748851) B2748851
theorem B19060355 : Blo 1831617 19060355 := bstep (se 1 (by rfl) ⟨14295266, by rfl⟩ : syracuseStep 19060355 = 28590533) B28590533
theorem B1832587 : Blo 1831617 1832587 := bstep (se 1 (by rfl) ⟨1374440, by rfl⟩ : syracuseStep 1832587 = 2748881) B2748881
theorem B8803991 : Blo 1831617 8803991 := bstep (se 1 (by rfl) ⟨6602993, by rfl⟩ : syracuseStep 8803991 = 13205987) B13205987
theorem B1832599 : Blo 1831617 1832599 := bstep (se 1 (by rfl) ⟨1374449, by rfl⟩ : syracuseStep 1832599 = 2748899) B2748899
theorem B3348119 : Blo 1831617 3348119 := bstep (se 1 (by rfl) ⟨2511089, by rfl⟩ : syracuseStep 3348119 = 5022179) B5022179
theorem B2750105 : Blo 1831617 2750105 := bstep (se 2 (by rfl) ⟨1031289, by rfl⟩ : syracuseStep 2750105 = 2062579) B2062579
theorem B1832619 : Blo 1831617 1832619 := bstep (se 1 (by rfl) ⟨1374464, by rfl⟩ : syracuseStep 1832619 = 2748929) B2748929
theorem B1832631 : Blo 1831617 1832631 := bstep (se 1 (by rfl) ⟨1374473, by rfl⟩ : syracuseStep 1832631 = 2748947) B2748947
theorem B1832651 : Blo 1831617 1832651 := bstep (se 1 (by rfl) ⟨1374488, by rfl⟩ : syracuseStep 1832651 = 2748977) B2748977
theorem B1832663 : Blo 1831617 1832663 := bstep (se 1 (by rfl) ⟨1374497, by rfl⟩ : syracuseStep 1832663 = 2748995) B2748995
theorem B2062039 : Blo 1831617 2062039 := bstep (se 1 (by rfl) ⟨1546529, by rfl⟩ : syracuseStep 2062039 = 3093059) B3093059
theorem B6182621 : Blo 1831617 6182621 := bstep (se 3 (by rfl) ⟨1159241, by rfl⟩ : syracuseStep 6182621 = 2318483) B2318483
theorem B1832683 : Blo 1831617 1832683 := bstep (se 1 (by rfl) ⟨1374512, by rfl⟩ : syracuseStep 1832683 = 2749025) B2749025
theorem B1832695 : Blo 1831617 1832695 := bstep (se 1 (by rfl) ⟨1374521, by rfl⟩ : syracuseStep 1832695 = 2749043) B2749043
theorem B1832715 : Blo 1831617 1832715 := bstep (se 1 (by rfl) ⟨1374536, by rfl⟩ : syracuseStep 1832715 = 2749073) B2749073
theorem B2750219 : Blo 1831617 2750219 := bstep (se 1 (by rfl) ⟨2062664, by rfl⟩ : syracuseStep 2750219 = 4125329) B4125329
theorem B7051025 : Blo 1831617 7051025 := bstep (se 2 (by rfl) ⟨2644134, by rfl⟩ : syracuseStep 7051025 = 5288269) B5288269
theorem B1832727 : Blo 1831617 1832727 := bstep (se 1 (by rfl) ⟨1374545, by rfl⟩ : syracuseStep 1832727 = 2749091) B2749091
theorem B2750231 : Blo 1831617 2750231 := bstep (se 1 (by rfl) ⟨2062673, by rfl⟩ : syracuseStep 2750231 = 4125347) B4125347
theorem B1832747 : Blo 1831617 1832747 := bstep (se 1 (by rfl) ⟨1374560, by rfl⟩ : syracuseStep 1832747 = 2749121) B2749121
theorem B1832759 : Blo 1831617 1832759 := bstep (se 1 (by rfl) ⟨1374569, by rfl⟩ : syracuseStep 1832759 = 2749139) B2749139
theorem B1832779 : Blo 1831617 1832779 := bstep (se 1 (by rfl) ⟨1374584, by rfl⟩ : syracuseStep 1832779 = 2749169) B2749169
theorem B1832791 : Blo 1831617 1832791 := bstep (se 1 (by rfl) ⟨1374593, by rfl⟩ : syracuseStep 1832791 = 2749187) B2749187
theorem B2750297 : Blo 1831617 2750297 := bstep (se 2 (by rfl) ⟨1031361, by rfl⟩ : syracuseStep 2750297 = 2062723) B2062723
theorem B1832811 : Blo 1831617 1832811 := bstep (se 1 (by rfl) ⟨1374608, by rfl⟩ : syracuseStep 1832811 = 2749217) B2749217
theorem B3479411 : Blo 1831617 3479411 := bstep (se 1 (by rfl) ⟨2609558, by rfl⟩ : syracuseStep 3479411 = 5219117) B5219117
theorem B1832823 : Blo 1831617 1832823 := bstep (se 1 (by rfl) ⟨1374617, by rfl⟩ : syracuseStep 1832823 = 2749235) B2749235
theorem B14112643 : Blo 1831617 14112643 := bstep (se 1 (by rfl) ⟨10584482, by rfl⟩ : syracuseStep 14112643 = 21168965) B21168965
theorem B1832843 : Blo 1831617 1832843 := bstep (se 1 (by rfl) ⟨1374632, by rfl⟩ : syracuseStep 1832843 = 2749265) B2749265
theorem B2062219 : Blo 1831617 2062219 := bstep (se 1 (by rfl) ⟨1546664, by rfl⟩ : syracuseStep 2062219 = 3093329) B3093329
theorem B7632785 : Blo 1831617 7632785 := bstep (se 2 (by rfl) ⟨2862294, by rfl⟩ : syracuseStep 7632785 = 5724589) B5724589
theorem B1832855 : Blo 1831617 1832855 := bstep (se 1 (by rfl) ⟨1374641, by rfl⟩ : syracuseStep 1832855 = 2749283) B2749283
theorem B3479449 : Blo 1831617 3479449 := bstep (se 2 (by rfl) ⟨1304793, by rfl⟩ : syracuseStep 3479449 = 2609587) B2609587
theorem B1832875 : Blo 1831617 1832875 := bstep (se 1 (by rfl) ⟨1374656, by rfl⟩ : syracuseStep 1832875 = 2749313) B2749313
theorem B1832887 : Blo 1831617 1832887 := bstep (se 1 (by rfl) ⟨1374665, by rfl⟩ : syracuseStep 1832887 = 2749331) B2749331
theorem B1832907 : Blo 1831617 1832907 := bstep (se 1 (by rfl) ⟨1374680, by rfl⟩ : syracuseStep 1832907 = 2749361) B2749361
theorem B6961099 : Blo 1831617 6961099 := bstep (se 1 (by rfl) ⟨5220824, by rfl⟩ : syracuseStep 6961099 = 10441649) B10441649
theorem B2750411 : Blo 1831617 2750411 := bstep (se 1 (by rfl) ⟨2062808, by rfl⟩ : syracuseStep 2750411 = 4125617) B4125617
theorem B1832919 : Blo 1831617 1832919 := bstep (se 1 (by rfl) ⟨1374689, by rfl⟩ : syracuseStep 1832919 = 2749379) B2749379
theorem B2750423 : Blo 1831617 2750423 := bstep (se 1 (by rfl) ⟨2062817, by rfl⟩ : syracuseStep 2750423 = 4125635) B4125635
theorem B1832939 : Blo 1831617 1832939 := bstep (se 1 (by rfl) ⟨1374704, by rfl⟩ : syracuseStep 1832939 = 2749409) B2749409
theorem B1832951 : Blo 1831617 1832951 := bstep (se 1 (by rfl) ⟨1374713, by rfl⟩ : syracuseStep 1832951 = 2749427) B2749427
theorem B2062327 : Blo 1831617 2062327 := bstep (se 1 (by rfl) ⟨1546745, by rfl⟩ : syracuseStep 2062327 = 3093491) B3093491
theorem B1832971 : Blo 1831617 1832971 := bstep (se 1 (by rfl) ⟨1374728, by rfl⟩ : syracuseStep 1832971 = 2749457) B2749457
theorem B9910289 : Blo 1831617 9910289 := bstep (se 2 (by rfl) ⟨3716358, by rfl⟩ : syracuseStep 9910289 = 7432717) B7432717
theorem B1832983 : Blo 1831617 1832983 := bstep (se 1 (by rfl) ⟨1374737, by rfl⟩ : syracuseStep 1832983 = 2749475) B2749475
theorem B1833003 : Blo 1831617 1833003 := bstep (se 1 (by rfl) ⟨1374752, by rfl⟩ : syracuseStep 1833003 = 2749505) B2749505
theorem B1833015 : Blo 1831617 1833015 := bstep (se 1 (by rfl) ⟨1374761, by rfl⟩ : syracuseStep 1833015 = 2749523) B2749523
theorem B5290049 : Blo 1831617 5290049 := bstep (se 2 (by rfl) ⟨1983768, by rfl⟩ : syracuseStep 5290049 = 3967537) B3967537
theorem B1833035 : Blo 1831617 1833035 := bstep (se 1 (by rfl) ⟨1374776, by rfl⟩ : syracuseStep 1833035 = 2749553) B2749553
theorem B1833047 : Blo 1831617 1833047 := bstep (se 1 (by rfl) ⟨1374785, by rfl⟩ : syracuseStep 1833047 = 2749571) B2749571
theorem B7829597 : Blo 1831617 7829597 := bstep (se 3 (by rfl) ⟨1468049, by rfl⟩ : syracuseStep 7829597 = 2936099) B2936099
theorem B1833067 : Blo 1831617 1833067 := bstep (se 1 (by rfl) ⟨1374800, by rfl⟩ : syracuseStep 1833067 = 2749601) B2749601
theorem B1833079 : Blo 1831617 1833079 := bstep (se 1 (by rfl) ⟨1374809, by rfl⟩ : syracuseStep 1833079 = 2749619) B2749619
theorem B11737219 : Blo 1831617 11737219 := bstep (se 1 (by rfl) ⟨8802914, by rfl⟩ : syracuseStep 11737219 = 17605829) B17605829
theorem B1833099 : Blo 1831617 1833099 := bstep (se 1 (by rfl) ⟨1374824, by rfl⟩ : syracuseStep 1833099 = 2749649) B2749649
theorem B1833111 : Blo 1831617 1833111 := bstep (se 1 (by rfl) ⟨1374833, by rfl⟩ : syracuseStep 1833111 = 2749667) B2749667
theorem B1833131 : Blo 1831617 1833131 := bstep (se 1 (by rfl) ⟨1374848, by rfl⟩ : syracuseStep 1833131 = 2749697) B2749697
theorem B2062507 : Blo 1831617 2062507 := bstep (se 1 (by rfl) ⟨1546880, by rfl⟩ : syracuseStep 2062507 = 3093761) B3093761
theorem B1833143 : Blo 1831617 1833143 := bstep (se 1 (by rfl) ⟨1374857, by rfl⟩ : syracuseStep 1833143 = 2749715) B2749715
theorem B1833163 : Blo 1831617 1833163 := bstep (se 1 (by rfl) ⟨1374872, by rfl⟩ : syracuseStep 1833163 = 2749745) B2749745
theorem B1833175 : Blo 1831617 1833175 := bstep (se 1 (by rfl) ⟨1374881, by rfl⟩ : syracuseStep 1833175 = 2749763) B2749763
theorem B6961373 : Blo 1831617 6961373 := bstep (se 3 (by rfl) ⟨1305257, by rfl⟩ : syracuseStep 6961373 = 2610515) B2610515
theorem B1833195 : Blo 1831617 1833195 := bstep (se 1 (by rfl) ⟨1374896, by rfl⟩ : syracuseStep 1833195 = 2749793) B2749793
theorem B1833207 : Blo 1831617 1833207 := bstep (se 1 (by rfl) ⟨1374905, by rfl⟩ : syracuseStep 1833207 = 2749811) B2749811
theorem B1833227 : Blo 1831617 1833227 := bstep (se 1 (by rfl) ⟨1374920, by rfl⟩ : syracuseStep 1833227 = 2749841) B2749841
theorem B1833239 : Blo 1831617 1833239 := bstep (se 1 (by rfl) ⟨1374929, by rfl⟩ : syracuseStep 1833239 = 2749859) B2749859
theorem B2062615 : Blo 1831617 2062615 := bstep (se 1 (by rfl) ⟨1546961, by rfl⟩ : syracuseStep 2062615 = 3093923) B3093923
theorem B1833259 : Blo 1831617 1833259 := bstep (se 1 (by rfl) ⟨1374944, by rfl⟩ : syracuseStep 1833259 = 2749889) B2749889
theorem B1833271 : Blo 1831617 1833271 := bstep (se 1 (by rfl) ⟨1374953, by rfl⟩ : syracuseStep 1833271 = 2749907) B2749907
theorem B8591681 : Blo 1831617 8591681 := bstep (se 2 (by rfl) ⟨3221880, by rfl⟩ : syracuseStep 8591681 = 6443761) B6443761
theorem B1833291 : Blo 1831617 1833291 := bstep (se 1 (by rfl) ⟨1374968, by rfl⟩ : syracuseStep 1833291 = 2749937) B2749937
theorem B1833303 : Blo 1831617 1833303 := bstep (se 1 (by rfl) ⟨1374977, by rfl⟩ : syracuseStep 1833303 = 2749955) B2749955
theorem B3479897 : Blo 1831617 3479897 := bstep (se 2 (by rfl) ⟨1304961, by rfl⟩ : syracuseStep 3479897 = 2609923) B2609923
theorem B1833323 : Blo 1831617 1833323 := bstep (se 1 (by rfl) ⟨1374992, by rfl⟩ : syracuseStep 1833323 = 2749985) B2749985
theorem B1833335 : Blo 1831617 1833335 := bstep (se 1 (by rfl) ⟨1375001, by rfl⟩ : syracuseStep 1833335 = 2750003) B2750003
theorem B3135883 : Blo 1831617 3135883 := bstep (se 1 (by rfl) ⟨2351912, by rfl⟩ : syracuseStep 3135883 = 4703825) B4703825
theorem B1833355 : Blo 1831617 1833355 := bstep (se 1 (by rfl) ⟨1375016, by rfl⟩ : syracuseStep 1833355 = 2750033) B2750033
theorem B7829905 : Blo 1831617 7829905 := bstep (se 2 (by rfl) ⟨2936214, by rfl⟩ : syracuseStep 7829905 = 5872429) B5872429
theorem B8591761 : Blo 1831617 8591761 := bstep (se 2 (by rfl) ⟨3221910, by rfl⟩ : syracuseStep 8591761 = 6443821) B6443821
theorem B1833367 : Blo 1831617 1833367 := bstep (se 1 (by rfl) ⟨1375025, by rfl⟩ : syracuseStep 1833367 = 2750051) B2750051
theorem B1833387 : Blo 1831617 1833387 := bstep (se 1 (by rfl) ⟨1375040, by rfl⟩ : syracuseStep 1833387 = 2750081) B2750081
theorem B7829939 : Blo 1831617 7829939 := bstep (se 1 (by rfl) ⟨5872454, by rfl⟩ : syracuseStep 7829939 = 11744909) B11744909
theorem B1833399 : Blo 1831617 1833399 := bstep (se 1 (by rfl) ⟨1375049, by rfl⟩ : syracuseStep 1833399 = 2750099) B2750099
theorem B1833419 : Blo 1831617 1833419 := bstep (se 1 (by rfl) ⟨1375064, by rfl⟩ : syracuseStep 1833419 = 2750129) B2750129
theorem B2062795 : Blo 1831617 2062795 := bstep (se 1 (by rfl) ⟨1547096, by rfl⟩ : syracuseStep 2062795 = 3094193) B3094193
theorem B1833431 : Blo 1831617 1833431 := bstep (se 1 (by rfl) ⟨1375073, by rfl⟩ : syracuseStep 1833431 = 2750147) B2750147
theorem B1833451 : Blo 1831617 1833451 := bstep (se 1 (by rfl) ⟨1375088, by rfl⟩ : syracuseStep 1833451 = 2750177) B2750177
theorem B1833463 : Blo 1831617 1833463 := bstep (se 1 (by rfl) ⟨1375097, by rfl⟩ : syracuseStep 1833463 = 2750195) B2750195
theorem B1833483 : Blo 1831617 1833483 := bstep (se 1 (by rfl) ⟨1375112, by rfl⟩ : syracuseStep 1833483 = 2750225) B2750225
theorem B11745809 : Blo 1831617 11745809 := bstep (se 2 (by rfl) ⟨4404678, by rfl⟩ : syracuseStep 11745809 = 8809357) B8809357
theorem B7428631 : Blo 1831617 7428631 := bstep (se 1 (by rfl) ⟨5571473, by rfl⟩ : syracuseStep 7428631 = 11142947) B11142947
theorem B7051799 : Blo 1831617 7051799 := bstep (se 1 (by rfl) ⟨5288849, by rfl⟩ : syracuseStep 7051799 = 10577699) B10577699
theorem B4766231 : Blo 1831617 4766231 := bstep (se 1 (by rfl) ⟨3574673, by rfl⟩ : syracuseStep 4766231 = 7149347) B7149347
theorem B1833495 : Blo 1831617 1833495 := bstep (se 1 (by rfl) ⟨1375121, by rfl⟩ : syracuseStep 1833495 = 2750243) B2750243
theorem B1833515 : Blo 1831617 1833515 := bstep (se 1 (by rfl) ⟨1375136, by rfl⟩ : syracuseStep 1833515 = 2750273) B2750273
theorem B1833527 : Blo 1831617 1833527 := bstep (se 1 (by rfl) ⟨1375145, by rfl⟩ : syracuseStep 1833527 = 2750291) B2750291
theorem B1833547 : Blo 1831617 1833547 := bstep (se 1 (by rfl) ⟨1375160, by rfl⟩ : syracuseStep 1833547 = 2750321) B2750321
theorem B1833559 : Blo 1831617 1833559 := bstep (se 1 (by rfl) ⟨1375169, by rfl⟩ : syracuseStep 1833559 = 2750339) B2750339
theorem B5216861 : Blo 1831617 5216861 := bstep (se 3 (by rfl) ⟨978161, by rfl⟩ : syracuseStep 5216861 = 1956323) B1956323
theorem B1833579 : Blo 1831617 1833579 := bstep (se 1 (by rfl) ⟨1375184, by rfl⟩ : syracuseStep 1833579 = 2750369) B2750369
theorem B1833591 : Blo 1831617 1833591 := bstep (se 1 (by rfl) ⟨1375193, by rfl⟩ : syracuseStep 1833591 = 2750387) B2750387
theorem B1833611 : Blo 1831617 1833611 := bstep (se 1 (by rfl) ⟨1375208, by rfl⟩ : syracuseStep 1833611 = 2750417) B2750417
theorem B6601409 : Blo 1831617 6601409 := bstep (se 2 (by rfl) ⟨2475528, by rfl⟩ : syracuseStep 6601409 = 4951057) B4951057
theorem B6183755 : Blo 1831617 6183755 := bstep (se 1 (by rfl) ⟨4637816, by rfl⟩ : syracuseStep 6183755 = 9275633) B9275633
theorem B9280331 : Blo 1831617 9280331 := bstep (se 1 (by rfl) ⟨6960248, by rfl⟩ : syracuseStep 9280331 = 13920497) B13920497
theorem B5217203 : Blo 1831617 5217203 := bstep (se 1 (by rfl) ⟨3912902, by rfl⟩ : syracuseStep 5217203 = 7825805) B7825805
theorem B12540851 : Blo 1831617 12540851 := bstep (se 1 (by rfl) ⟨9405638, by rfl⟩ : syracuseStep 12540851 = 18811277) B18811277
theorem B14302169 : Blo 1831617 14302169 := bstep (se 2 (by rfl) ⟨5363313, by rfl⟩ : syracuseStep 14302169 = 10726627) B10726627
theorem B19807249 : Blo 1831617 19807249 := bstep (se 2 (by rfl) ⟨7427718, by rfl⟩ : syracuseStep 19807249 = 14855437) B14855437
theorem B3480641 : Blo 1831617 3480641 := bstep (se 2 (by rfl) ⟨1305240, by rfl⟩ : syracuseStep 3480641 = 2610481) B2610481
theorem B6184025 : Blo 1831617 6184025 := bstep (se 2 (by rfl) ⟨2319009, by rfl⟩ : syracuseStep 6184025 = 4638019) B4638019
theorem B3914867 : Blo 1831617 3914867 := bstep (se 1 (by rfl) ⟨2936150, by rfl⟩ : syracuseStep 3914867 = 5872301) B5872301
theorem B5291225 : Blo 1831617 5291225 := bstep (se 2 (by rfl) ⟨1984209, by rfl⟩ : syracuseStep 5291225 = 3968419) B3968419
theorem B14499107 : Blo 1831617 14499107 := bstep (se 1 (by rfl) ⟨10874330, by rfl⟩ : syracuseStep 14499107 = 21748661) B21748661
theorem B3480907 : Blo 1831617 3480907 := bstep (se 1 (by rfl) ⟨2610680, by rfl⟩ : syracuseStep 3480907 = 5221361) B5221361
theorem B11296349 : Blo 1831617 11296349 := bstep (se 3 (by rfl) ⟨2118065, by rfl⟩ : syracuseStep 11296349 = 4236131) B4236131
theorem B6602519 : Blo 1831617 6602519 := bstep (se 1 (by rfl) ⟨4951889, by rfl⟩ : syracuseStep 6602519 = 9903779) B9903779
theorem B6184727 : Blo 1831617 6184727 := bstep (se 1 (by rfl) ⟨4638545, by rfl⟩ : syracuseStep 6184727 = 9277091) B9277091
theorem B13909805 : Blo 1831617 13909805 := bstep (se 3 (by rfl) ⟨2608088, by rfl⟩ : syracuseStep 13909805 = 5216177) B5216177
theorem B4636673 : Blo 1831617 4636673 := bstep (se 2 (by rfl) ⟨1738752, by rfl⟩ : syracuseStep 4636673 = 3477505) B3477505
theorem B5218319 : Blo 1831617 5218319 := bstep (se 1 (by rfl) ⟨3913739, by rfl⟩ : syracuseStep 5218319 = 7827479) B7827479
theorem B5292047 : Blo 1831617 5292047 := bstep (se 1 (by rfl) ⟨3969035, by rfl⟩ : syracuseStep 5292047 = 7938071) B7938071
theorem B9904189 : Blo 1831617 9904189 := bstep (se 3 (by rfl) ⟨1857035, by rfl⟩ : syracuseStep 9904189 = 3714071) B3714071
theorem B7528535 : Blo 1831617 7528535 := bstep (se 1 (by rfl) ⟨5646401, by rfl⟩ : syracuseStep 7528535 = 11292803) B11292803
theorem B1958023 : Blo 1831617 1958023 := bstep (se 1 (by rfl) ⟨1468517, by rfl⟩ : syracuseStep 1958023 = 2937035) B2937035
theorem B2318635 : Blo 1831617 2318635 := bstep (se 1 (by rfl) ⟨1738976, by rfl⟩ : syracuseStep 2318635 = 3477953) B3477953
theorem B11739451 : Blo 1831617 11739451 := bstep (se 1 (by rfl) ⟨8804588, by rfl⟩ : syracuseStep 11739451 = 17609177) B17609177
theorem B9273689 : Blo 1831617 9273689 := bstep (se 2 (by rfl) ⟨3477633, by rfl⟩ : syracuseStep 9273689 = 6955267) B6955267
theorem B4637047 : Blo 1831617 4637047 := bstep (se 1 (by rfl) ⟨3477785, by rfl⟩ : syracuseStep 4637047 = 6955571) B6955571
theorem B18809297 : Blo 1831617 18809297 := bstep (se 2 (by rfl) ⟨7053486, by rfl⟩ : syracuseStep 18809297 = 14106973) B14106973
theorem B6185483 : Blo 1831617 6185483 := bstep (se 1 (by rfl) ⟨4639112, by rfl⟩ : syracuseStep 6185483 = 9278225) B9278225
theorem B2318863 : Blo 1831617 2318863 := bstep (se 1 (by rfl) ⟨1739147, by rfl⟩ : syracuseStep 2318863 = 3478295) B3478295
theorem B4121207 : Blo 1831617 4121207 := bstep (se 1 (by rfl) ⟨3090905, by rfl⟩ : syracuseStep 4121207 = 6181811) B6181811
theorem B6185591 : Blo 1831617 6185591 := bstep (se 1 (by rfl) ⟨4639193, by rfl⟩ : syracuseStep 6185591 = 9278387) B9278387
theorem B9904841 : Blo 1831617 9904841 := bstep (se 2 (by rfl) ⟨3714315, by rfl⟩ : syracuseStep 9904841 = 7428631) B7428631
theorem B33424163 : Blo 1831617 33424163 := bstep (se 1 (by rfl) ⟨25068122, by rfl⟩ : syracuseStep 33424163 = 50136245) B50136245
theorem B4121387 : Blo 1831617 4121387 := bstep (se 1 (by rfl) ⟨3091040, by rfl⟩ : syracuseStep 4121387 = 6182081) B6182081
theorem B4637483 : Blo 1831617 4637483 := bstep (se 1 (by rfl) ⟨3478112, by rfl⟩ : syracuseStep 4637483 = 6956225) B6956225
theorem B19063601 : Blo 1831617 19063601 := bstep (se 2 (by rfl) ⟨7148850, by rfl⟩ : syracuseStep 19063601 = 14297701) B14297701
theorem B8807453 : Blo 1831617 8807453 := bstep (se 3 (by rfl) ⟨1651397, by rfl⟩ : syracuseStep 8807453 = 3302795) B3302795
theorem B12706903 : Blo 1831617 12706903 := bstep (se 1 (by rfl) ⟨9530177, by rfl⟩ : syracuseStep 12706903 = 19060355) B19060355
theorem B4121747 : Blo 1831617 4121747 := bstep (se 1 (by rfl) ⟨3091310, by rfl⟩ : syracuseStep 4121747 = 6182621) B6182621
theorem B21169325 : Blo 1831617 21169325 := bstep (se 3 (by rfl) ⟨3969248, by rfl⟩ : syracuseStep 21169325 = 7938497) B7938497
theorem B2786491 : Blo 1831617 2786491 := bstep (se 1 (by rfl) ⟨2089868, by rfl⟩ : syracuseStep 2786491 = 4179737) B4179737
theorem B4121801 : Blo 1831617 4121801 := bstep (se 2 (by rfl) ⟨1545675, by rfl⟩ : syracuseStep 4121801 = 3091351) B3091351
theorem B6186185 : Blo 1831617 6186185 := bstep (se 2 (by rfl) ⟨2319819, by rfl⟩ : syracuseStep 6186185 = 4639639) B4639639
theorem B2319607 : Blo 1831617 2319607 := bstep (se 1 (by rfl) ⟨1739705, by rfl⟩ : syracuseStep 2319607 = 3479411) B3479411
theorem B5088523 : Blo 1831617 5088523 := bstep (se 1 (by rfl) ⟨3816392, by rfl⟩ : syracuseStep 5088523 = 7632785) B7632785
theorem B5219731 : Blo 1831617 5219731 := bstep (se 1 (by rfl) ⟨3914798, by rfl⟩ : syracuseStep 5219731 = 7829597) B7829597
theorem B2319931 : Blo 1831617 2319931 := bstep (se 1 (by rfl) ⟨1739948, by rfl⟩ : syracuseStep 2319931 = 3479897) B3479897
theorem B4638323 : Blo 1831617 4638323 := bstep (se 1 (by rfl) ⟨3478742, by rfl⟩ : syracuseStep 4638323 = 6957485) B6957485
theorem B5219959 : Blo 1831617 5219959 := bstep (se 1 (by rfl) ⟨3914969, by rfl⟩ : syracuseStep 5219959 = 7829939) B7829939
theorem B4638343 : Blo 1831617 4638343 := bstep (se 1 (by rfl) ⟨3478757, by rfl⟩ : syracuseStep 4638343 = 6957515) B6957515
theorem B10438415 : Blo 1831617 10438415 := bstep (se 1 (by rfl) ⟨7828811, by rfl⟩ : syracuseStep 10438415 = 15657623) B15657623
theorem B4400939 : Blo 1831617 4400939 := bstep (se 1 (by rfl) ⟨3300704, by rfl⟩ : syracuseStep 4400939 = 6601409) B6601409
theorem B2934587 : Blo 1831617 2934587 := bstep (se 1 (by rfl) ⟨2200940, by rfl⟩ : syracuseStep 2934587 = 4401881) B4401881
theorem B4122503 : Blo 1831617 4122503 := bstep (se 1 (by rfl) ⟨3091877, by rfl⟩ : syracuseStep 4122503 = 6183755) B6183755
theorem B6186887 : Blo 1831617 6186887 := bstep (se 1 (by rfl) ⟨4640165, by rfl⟩ : syracuseStep 6186887 = 9280331) B9280331
theorem B4638617 : Blo 1831617 4638617 := bstep (se 2 (by rfl) ⟨1739481, by rfl⟩ : syracuseStep 4638617 = 3478963) B3478963
theorem B2320427 : Blo 1831617 2320427 := bstep (se 1 (by rfl) ⟨1740320, by rfl⟩ : syracuseStep 2320427 = 3480641) B3480641
theorem B2787385 : Blo 1831617 2787385 := bstep (se 2 (by rfl) ⟨1045269, by rfl⟩ : syracuseStep 2787385 = 2090539) B2090539
theorem B4122683 : Blo 1831617 4122683 := bstep (se 1 (by rfl) ⟨3092012, by rfl⟩ : syracuseStep 4122683 = 6184025) B6184025
theorem B4638779 : Blo 1831617 4638779 := bstep (se 1 (by rfl) ⟨3479084, by rfl⟩ : syracuseStep 4638779 = 6958169) B6958169
theorem B17606717 : Blo 1831617 17606717 := bstep (se 3 (by rfl) ⟨3301259, by rfl⟩ : syracuseStep 17606717 = 6602519) B6602519
theorem B4122809 : Blo 1831617 4122809 := bstep (se 2 (by rfl) ⟨1546053, by rfl⟩ : syracuseStep 4122809 = 3092107) B3092107
theorem B6187265 : Blo 1831617 6187265 := bstep (se 2 (by rfl) ⟨2320224, by rfl⟩ : syracuseStep 6187265 = 4640449) B4640449
theorem B4638991 : Blo 1831617 4638991 := bstep (se 1 (by rfl) ⟨3479243, by rfl⟩ : syracuseStep 4638991 = 6958487) B6958487
theorem B9275795 : Blo 1831617 9275795 := bstep (se 1 (by rfl) ⟨6956846, by rfl⟩ : syracuseStep 9275795 = 13913693) B13913693
theorem B7530899 : Blo 1831617 7530899 := bstep (se 1 (by rfl) ⟨5648174, by rfl⟩ : syracuseStep 7530899 = 11296349) B11296349
theorem B4123151 : Blo 1831617 4123151 := bstep (se 1 (by rfl) ⟨3092363, by rfl⟩ : syracuseStep 4123151 = 6184727) B6184727
theorem B4123169 : Blo 1831617 4123169 := bstep (se 2 (by rfl) ⟨1546188, by rfl⟩ : syracuseStep 4123169 = 3092377) B3092377
theorem B4639265 : Blo 1831617 4639265 := bstep (se 2 (by rfl) ⟨1739724, by rfl⟩ : syracuseStep 4639265 = 3479449) B3479449
theorem B35228195 : Blo 1831617 35228195 := bstep (se 1 (by rfl) ⟨26421146, by rfl⟩ : syracuseStep 35228195 = 52842293) B52842293
theorem B12536363 : Blo 1831617 12536363 := bstep (se 1 (by rfl) ⟨9402272, by rfl⟩ : syracuseStep 12536363 = 18804545) B18804545
theorem B13208183 : Blo 1831617 13208183 := bstep (se 1 (by rfl) ⟨9906137, by rfl⟩ : syracuseStep 13208183 = 19812275) B19812275
theorem B3304207 : Blo 1831617 3304207 := bstep (se 1 (by rfl) ⟨2478155, by rfl⟩ : syracuseStep 3304207 = 4956311) B4956311
theorem B3091243 : Blo 1831617 3091243 := bstep (se 1 (by rfl) ⟨2318432, by rfl⟩ : syracuseStep 3091243 = 4636865) B4636865
theorem B15649625 : Blo 1831617 15649625 := bstep (se 2 (by rfl) ⟨5868609, by rfl⟩ : syracuseStep 15649625 = 11737219) B11737219
theorem B26405747 : Blo 1831617 26405747 := bstep (se 1 (by rfl) ⟨19804310, by rfl⟩ : syracuseStep 26405747 = 39608621) B39608621
theorem B5221235 : Blo 1831617 5221235 := bstep (se 1 (by rfl) ⟨3915926, by rfl⟩ : syracuseStep 5221235 = 7831853) B7831853
theorem B4123511 : Blo 1831617 4123511 := bstep (se 1 (by rfl) ⟨3092633, by rfl⟩ : syracuseStep 4123511 = 6185267) B6185267
theorem B6957971 : Blo 1831617 6957971 := bstep (se 1 (by rfl) ⟨5218478, by rfl⟩ : syracuseStep 6957971 = 10436957) B10436957
theorem B4402073 : Blo 1831617 4402073 := bstep (se 2 (by rfl) ⟨1650777, by rfl⟩ : syracuseStep 4402073 = 3301555) B3301555
theorem B85765027 : Blo 1831617 85765027 := bstep (se 1 (by rfl) ⟨64323770, by rfl⟩ : syracuseStep 85765027 = 128647541) B128647541
theorem B2608043 : Blo 1831617 2608043 := bstep (se 1 (by rfl) ⟨1956032, by rfl⟩ : syracuseStep 2608043 = 3912065) B3912065
theorem B3091385 : Blo 1831617 3091385 := bstep (se 2 (by rfl) ⟨1159269, by rfl⟩ : syracuseStep 3091385 = 2318539) B2318539
theorem B13216715 : Blo 1831617 13216715 := bstep (se 1 (by rfl) ⟨9912536, by rfl⟩ : syracuseStep 13216715 = 19825073) B19825073
theorem B2747435 : Blo 1831617 2747435 := bstep (se 1 (by rfl) ⟨2060576, by rfl⟩ : syracuseStep 2747435 = 4121153) B4121153
theorem B4123691 : Blo 1831617 4123691 := bstep (se 1 (by rfl) ⟨3092768, by rfl⟩ : syracuseStep 4123691 = 6185537) B6185537
theorem B6188075 : Blo 1831617 6188075 := bstep (se 1 (by rfl) ⟨4641056, by rfl⟩ : syracuseStep 6188075 = 9282113) B9282113
theorem B2747465 : Blo 1831617 2747465 := bstep (se 2 (by rfl) ⟨1030299, by rfl⟩ : syracuseStep 2747465 = 2060599) B2060599
theorem B26405975 : Blo 1831617 26405975 := bstep (se 1 (by rfl) ⟨19804481, by rfl⟩ : syracuseStep 26405975 = 39608963) B39608963
theorem B4181177 : Blo 1831617 4181177 := bstep (se 2 (by rfl) ⟨1567941, by rfl⟩ : syracuseStep 4181177 = 3135883) B3135883
theorem B2747579 : Blo 1831617 2747579 := bstep (se 1 (by rfl) ⟨2060684, by rfl⟩ : syracuseStep 2747579 = 4121369) B4121369
theorem B10439873 : Blo 1831617 10439873 := bstep (se 2 (by rfl) ⟨3914952, by rfl⟩ : syracuseStep 10439873 = 7829905) B7829905
theorem B11455681 : Blo 1831617 11455681 := bstep (se 2 (by rfl) ⟨4295880, by rfl⟩ : syracuseStep 11455681 = 8591761) B8591761
theorem B2747639 : Blo 1831617 2747639 := bstep (se 1 (by rfl) ⟨2060729, by rfl⟩ : syracuseStep 2747639 = 4121459) B4121459
theorem B2747663 : Blo 1831617 2747663 := bstep (se 1 (by rfl) ⟨2060747, by rfl⟩ : syracuseStep 2747663 = 4121495) B4121495
theorem B2747705 : Blo 1831617 2747705 := bstep (se 2 (by rfl) ⟨1030389, by rfl⟩ : syracuseStep 2747705 = 2060779) B2060779
theorem B2747783 : Blo 1831617 2747783 := bstep (se 1 (by rfl) ⟨2060837, by rfl⟩ : syracuseStep 2747783 = 4121675) B4121675
theorem B2682247 : Blo 1831617 2682247 := bstep (se 1 (by rfl) ⟨2011685, by rfl⟩ : syracuseStep 2682247 = 4023371) B4023371
theorem B4124051 : Blo 1831617 4124051 := bstep (se 1 (by rfl) ⟨3093038, by rfl⟩ : syracuseStep 4124051 = 6186077) B6186077
theorem B2747819 : Blo 1831617 2747819 := bstep (se 1 (by rfl) ⟨2060864, by rfl⟩ : syracuseStep 2747819 = 4121729) B4121729
theorem B2747849 : Blo 1831617 2747849 := bstep (se 2 (by rfl) ⟨1030443, by rfl⟩ : syracuseStep 2747849 = 2060887) B2060887
theorem B4124105 : Blo 1831617 4124105 := bstep (se 2 (by rfl) ⟨1546539, by rfl⟩ : syracuseStep 4124105 = 3093079) B3093079
theorem B4640267 : Blo 1831617 4640267 := bstep (se 1 (by rfl) ⟨3480200, by rfl⟩ : syracuseStep 4640267 = 6960401) B6960401
theorem B2747963 : Blo 1831617 2747963 := bstep (se 1 (by rfl) ⟨2060972, by rfl⟩ : syracuseStep 2747963 = 4121945) B4121945
theorem B2748023 : Blo 1831617 2748023 := bstep (se 1 (by rfl) ⟨2061017, by rfl⟩ : syracuseStep 2748023 = 4122035) B4122035
theorem B3092087 : Blo 1831617 3092087 := bstep (se 1 (by rfl) ⟨2319065, by rfl⟩ : syracuseStep 3092087 = 4638131) B4638131
theorem B2748047 : Blo 1831617 2748047 := bstep (se 1 (by rfl) ⟨2061035, by rfl⟩ : syracuseStep 2748047 = 4122071) B4122071
theorem B4402841 : Blo 1831617 4402841 := bstep (se 2 (by rfl) ⟨1651065, by rfl⟩ : syracuseStep 4402841 = 3302131) B3302131
theorem B2748089 : Blo 1831617 2748089 := bstep (se 2 (by rfl) ⟨1030533, by rfl⟩ : syracuseStep 2748089 = 2061067) B2061067
theorem B2748167 : Blo 1831617 2748167 := bstep (se 1 (by rfl) ⟨2061125, by rfl⟩ : syracuseStep 2748167 = 4122251) B4122251
theorem B2232079 : Blo 1831617 2232079 := bstep (se 1 (by rfl) ⟨1674059, by rfl⟩ : syracuseStep 2232079 = 3348119) B3348119
theorem B2748203 : Blo 1831617 2748203 := bstep (se 1 (by rfl) ⟨2061152, by rfl⟩ : syracuseStep 2748203 = 4122305) B4122305
theorem B2748233 : Blo 1831617 2748233 := bstep (se 2 (by rfl) ⟨1030587, by rfl⟩ : syracuseStep 2748233 = 2061175) B2061175
theorem B2748347 : Blo 1831617 2748347 := bstep (se 1 (by rfl) ⟨2061260, by rfl⟩ : syracuseStep 2748347 = 4122521) B4122521
theorem B2748407 : Blo 1831617 2748407 := bstep (se 1 (by rfl) ⟨2061305, by rfl⟩ : syracuseStep 2748407 = 4122611) B4122611
theorem B6606859 : Blo 1831617 6606859 := bstep (se 1 (by rfl) ⟨4955144, by rfl⟩ : syracuseStep 6606859 = 9910289) B9910289
theorem B2748431 : Blo 1831617 2748431 := bstep (se 1 (by rfl) ⟨2061323, by rfl⟩ : syracuseStep 2748431 = 4122647) B4122647
theorem B11300887 : Blo 1831617 11300887 := bstep (se 1 (by rfl) ⟨8475665, by rfl⟩ : syracuseStep 11300887 = 16951331) B16951331
theorem B3526699 : Blo 1831617 3526699 := bstep (se 1 (by rfl) ⟨2645024, by rfl⟩ : syracuseStep 3526699 = 5290049) B5290049
theorem B2748473 : Blo 1831617 2748473 := bstep (se 2 (by rfl) ⟨1030677, by rfl⟩ : syracuseStep 2748473 = 2061355) B2061355
theorem B3092539 : Blo 1831617 3092539 := bstep (se 1 (by rfl) ⟨2319404, by rfl⟩ : syracuseStep 3092539 = 4638809) B4638809
theorem B2748551 : Blo 1831617 2748551 := bstep (se 1 (by rfl) ⟨2061413, by rfl⟩ : syracuseStep 2748551 = 4122827) B4122827
theorem B4124807 : Blo 1831617 4124807 := bstep (se 1 (by rfl) ⟨3093605, by rfl⟩ : syracuseStep 4124807 = 6187211) B6187211
theorem B4640915 : Blo 1831617 4640915 := bstep (se 1 (by rfl) ⟨3480686, by rfl⟩ : syracuseStep 4640915 = 6961373) B6961373
theorem B2748587 : Blo 1831617 2748587 := bstep (se 1 (by rfl) ⟨2061440, by rfl⟩ : syracuseStep 2748587 = 4122881) B4122881
theorem B2748617 : Blo 1831617 2748617 := bstep (se 2 (by rfl) ⟨1030731, by rfl⟩ : syracuseStep 2748617 = 2061463) B2061463
theorem B3092681 : Blo 1831617 3092681 := bstep (se 2 (by rfl) ⟨1159755, by rfl⟩ : syracuseStep 3092681 = 2319511) B2319511
theorem B2748731 : Blo 1831617 2748731 := bstep (se 1 (by rfl) ⟨2061548, by rfl⟩ : syracuseStep 2748731 = 4123097) B4123097
theorem B4124987 : Blo 1831617 4124987 := bstep (se 1 (by rfl) ⟨3093740, by rfl⟩ : syracuseStep 4124987 = 6187481) B6187481
theorem B2748791 : Blo 1831617 2748791 := bstep (se 1 (by rfl) ⟨2061593, by rfl⟩ : syracuseStep 2748791 = 4123187) B4123187
theorem B2748815 : Blo 1831617 2748815 := bstep (se 1 (by rfl) ⟨2061611, by rfl⟩ : syracuseStep 2748815 = 4123223) B4123223
theorem B3477907 : Blo 1831617 3477907 := bstep (se 1 (by rfl) ⟨2608430, by rfl⟩ : syracuseStep 3477907 = 5216861) B5216861
theorem B4764089 : Blo 1831617 4764089 := bstep (se 2 (by rfl) ⟨1786533, by rfl⟩ : syracuseStep 4764089 = 3573067) B3573067
theorem B2748857 : Blo 1831617 2748857 := bstep (se 2 (by rfl) ⟨1030821, by rfl⟩ : syracuseStep 2748857 = 2061643) B2061643
theorem B4125113 : Blo 1831617 4125113 := bstep (se 2 (by rfl) ⟨1546917, by rfl⟩ : syracuseStep 4125113 = 3093835) B3093835
theorem B4641209 : Blo 1831617 4641209 := bstep (se 2 (by rfl) ⟨1740453, by rfl⟩ : syracuseStep 4641209 = 3480907) B3480907
theorem B9908689 : Blo 1831617 9908689 := bstep (se 2 (by rfl) ⟨3715758, by rfl⟩ : syracuseStep 9908689 = 7431517) B7431517
theorem B2748935 : Blo 1831617 2748935 := bstep (se 1 (by rfl) ⟨2061701, by rfl⟩ : syracuseStep 2748935 = 4123403) B4123403
theorem B6959627 : Blo 1831617 6959627 := bstep (se 1 (by rfl) ⟨5219720, by rfl⟩ : syracuseStep 6959627 = 10439441) B10439441
theorem B2060815 : Blo 1831617 2060815 := bstep (se 1 (by rfl) ⟨1545611, by rfl⟩ : syracuseStep 2060815 = 3091223) B3091223
theorem B2748971 : Blo 1831617 2748971 := bstep (se 1 (by rfl) ⟨2061728, by rfl⟩ : syracuseStep 2748971 = 4123457) B4123457
theorem B2749001 : Blo 1831617 2749001 := bstep (se 2 (by rfl) ⟨1030875, by rfl⟩ : syracuseStep 2749001 = 2061751) B2061751
theorem B3478135 : Blo 1831617 3478135 := bstep (se 1 (by rfl) ⟨2608601, by rfl⟩ : syracuseStep 3478135 = 5217203) B5217203
theorem B8360567 : Blo 1831617 8360567 := bstep (se 1 (by rfl) ⟨6270425, by rfl⟩ : syracuseStep 8360567 = 12540851) B12540851
theorem B20869811 : Blo 1831617 20869811 := bstep (se 1 (by rfl) ⟨15652358, by rfl⟩ : syracuseStep 20869811 = 31304717) B31304717
theorem B2749115 : Blo 1831617 2749115 := bstep (se 1 (by rfl) ⟨2061836, by rfl⟩ : syracuseStep 2749115 = 4123673) B4123673
theorem B2749175 : Blo 1831617 2749175 := bstep (se 1 (by rfl) ⟨2061881, by rfl⟩ : syracuseStep 2749175 = 4123763) B4123763
theorem B2609911 : Blo 1831617 2609911 := bstep (se 1 (by rfl) ⟨1957433, by rfl⟩ : syracuseStep 2609911 = 3914867) B3914867
theorem B1831687 : Blo 1831617 1831687 := bstep (se 1 (by rfl) ⟨1373765, by rfl⟩ : syracuseStep 1831687 = 2747531) B2747531
theorem B1831695 : Blo 1831617 1831695 := bstep (se 1 (by rfl) ⟨1373771, by rfl⟩ : syracuseStep 1831695 = 2747543) B2747543
theorem B8925967 : Blo 1831617 8925967 := bstep (se 1 (by rfl) ⟨6694475, by rfl⟩ : syracuseStep 8925967 = 13388951) B13388951
theorem B2749199 : Blo 1831617 2749199 := bstep (se 1 (by rfl) ⟨2061899, by rfl⟩ : syracuseStep 2749199 = 4123799) B4123799
theorem B4125455 : Blo 1831617 4125455 := bstep (se 1 (by rfl) ⟨3094091, by rfl⟩ : syracuseStep 4125455 = 6188183) B6188183
theorem B4125473 : Blo 1831617 4125473 := bstep (se 2 (by rfl) ⟨1547052, by rfl⟩ : syracuseStep 4125473 = 3094105) B3094105
theorem B2749241 : Blo 1831617 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B1831739 : Blo 1831617 1831739 := bstep (se 1 (by rfl) ⟨1373804, by rfl⟩ : syracuseStep 1831739 = 2747609) B2747609
theorem B3527483 : Blo 1831617 3527483 := bstep (se 1 (by rfl) ⟨2645612, by rfl⟩ : syracuseStep 3527483 = 5291225) B5291225
theorem B1831815 : Blo 1831617 1831815 := bstep (se 1 (by rfl) ⟨1373861, by rfl⟩ : syracuseStep 1831815 = 2747723) B2747723
theorem B2749319 : Blo 1831617 2749319 := bstep (se 1 (by rfl) ⟨2061989, by rfl⟩ : syracuseStep 2749319 = 4123979) B4123979
theorem B3093383 : Blo 1831617 3093383 := bstep (se 1 (by rfl) ⟨2320037, by rfl⟩ : syracuseStep 3093383 = 4640075) B4640075
theorem B1831823 : Blo 1831617 1831823 := bstep (se 1 (by rfl) ⟨1373867, by rfl⟩ : syracuseStep 1831823 = 2747735) B2747735
theorem B2749355 : Blo 1831617 2749355 := bstep (se 1 (by rfl) ⟨2062016, by rfl⟩ : syracuseStep 2749355 = 4124033) B4124033
theorem B1831867 : Blo 1831617 1831867 := bstep (se 1 (by rfl) ⟨1373900, by rfl⟩ : syracuseStep 1831867 = 2747801) B2747801
theorem B2749385 : Blo 1831617 2749385 := bstep (se 2 (by rfl) ⟨1031019, by rfl⟩ : syracuseStep 2749385 = 2062039) B2062039
theorem B1831943 : Blo 1831617 1831943 := bstep (se 1 (by rfl) ⟨1373957, by rfl⟩ : syracuseStep 1831943 = 2747915) B2747915
theorem B2061319 : Blo 1831617 2061319 := bstep (se 1 (by rfl) ⟨1545989, by rfl⟩ : syracuseStep 2061319 = 3091979) B3091979
theorem B1831951 : Blo 1831617 1831951 := bstep (se 1 (by rfl) ⟨1373963, by rfl⟩ : syracuseStep 1831951 = 2747927) B2747927
theorem B1831995 : Blo 1831617 1831995 := bstep (se 1 (by rfl) ⟨1373996, by rfl⟩ : syracuseStep 1831995 = 2747993) B2747993
theorem B2749499 : Blo 1831617 2749499 := bstep (se 1 (by rfl) ⟨2062124, by rfl⟩ : syracuseStep 2749499 = 4124249) B4124249
theorem B2749559 : Blo 1831617 2749559 := bstep (se 1 (by rfl) ⟨2062169, by rfl⟩ : syracuseStep 2749559 = 4124339) B4124339
theorem B1832071 : Blo 1831617 1832071 := bstep (se 1 (by rfl) ⟨1374053, by rfl⟩ : syracuseStep 1832071 = 2748107) B2748107
theorem B1832079 : Blo 1831617 1832079 := bstep (se 1 (by rfl) ⟨1374059, by rfl⟩ : syracuseStep 1832079 = 2748119) B2748119
theorem B2749583 : Blo 1831617 2749583 := bstep (se 1 (by rfl) ⟨2062187, by rfl⟩ : syracuseStep 2749583 = 4124375) B4124375
theorem B2749625 : Blo 1831617 2749625 := bstep (se 2 (by rfl) ⟨1031109, by rfl⟩ : syracuseStep 2749625 = 2062219) B2062219
theorem B1832123 : Blo 1831617 1832123 := bstep (se 1 (by rfl) ⟨1374092, by rfl⟩ : syracuseStep 1832123 = 2748185) B2748185
theorem B2061499 : Blo 1831617 2061499 := bstep (se 1 (by rfl) ⟨1546124, by rfl⟩ : syracuseStep 2061499 = 3092249) B3092249
theorem B1832199 : Blo 1831617 1832199 := bstep (se 1 (by rfl) ⟨1374149, by rfl⟩ : syracuseStep 1832199 = 2748299) B2748299
theorem B2749703 : Blo 1831617 2749703 := bstep (se 1 (by rfl) ⟨2062277, by rfl⟩ : syracuseStep 2749703 = 4124555) B4124555
theorem B1832207 : Blo 1831617 1832207 := bstep (se 1 (by rfl) ⟨1374155, by rfl⟩ : syracuseStep 1832207 = 2748311) B2748311
theorem B2749739 : Blo 1831617 2749739 := bstep (se 1 (by rfl) ⟨2062304, by rfl⟩ : syracuseStep 2749739 = 4124609) B4124609
theorem B1832251 : Blo 1831617 1832251 := bstep (se 1 (by rfl) ⟨1374188, by rfl⟩ : syracuseStep 1832251 = 2748377) B2748377
theorem B2749769 : Blo 1831617 2749769 := bstep (se 2 (by rfl) ⟨1031163, by rfl⟩ : syracuseStep 2749769 = 2062327) B2062327
theorem B1832327 : Blo 1831617 1832327 := bstep (se 1 (by rfl) ⟨1374245, by rfl⟩ : syracuseStep 1832327 = 2748491) B2748491
theorem B1832335 : Blo 1831617 1832335 := bstep (se 1 (by rfl) ⟨1374251, by rfl⟩ : syracuseStep 1832335 = 2748503) B2748503
theorem B6182297 : Blo 1831617 6182297 := bstep (se 2 (by rfl) ⟨2318361, by rfl⟩ : syracuseStep 6182297 = 4636723) B4636723
theorem B9278873 : Blo 1831617 9278873 := bstep (se 2 (by rfl) ⟨3479577, by rfl⟩ : syracuseStep 9278873 = 6959155) B6959155
theorem B1832379 : Blo 1831617 1832379 := bstep (se 1 (by rfl) ⟨1374284, by rfl⟩ : syracuseStep 1832379 = 2748569) B2748569
theorem B2749883 : Blo 1831617 2749883 := bstep (se 1 (by rfl) ⟨2062412, by rfl⟩ : syracuseStep 2749883 = 4124825) B4124825
theorem B2749943 : Blo 1831617 2749943 := bstep (se 1 (by rfl) ⟨2062457, by rfl⟩ : syracuseStep 2749943 = 4124915) B4124915
theorem B1832455 : Blo 1831617 1832455 := bstep (se 1 (by rfl) ⟨1374341, by rfl⟩ : syracuseStep 1832455 = 2748683) B2748683
theorem B1832463 : Blo 1831617 1832463 := bstep (se 1 (by rfl) ⟨1374347, by rfl⟩ : syracuseStep 1832463 = 2748695) B2748695
theorem B2749967 : Blo 1831617 2749967 := bstep (se 1 (by rfl) ⟨2062475, by rfl⟩ : syracuseStep 2749967 = 4124951) B4124951
theorem B3094031 : Blo 1831617 3094031 := bstep (se 1 (by rfl) ⟨2320523, by rfl⟩ : syracuseStep 3094031 = 4641047) B4641047
theorem B2750009 : Blo 1831617 2750009 := bstep (se 2 (by rfl) ⟨1031253, by rfl⟩ : syracuseStep 2750009 = 2062507) B2062507
theorem B1832507 : Blo 1831617 1832507 := bstep (se 1 (by rfl) ⟨1374380, by rfl⟩ : syracuseStep 1832507 = 2748761) B2748761
theorem B5215859 : Blo 1831617 5215859 := bstep (se 1 (by rfl) ⟨3911894, by rfl⟩ : syracuseStep 5215859 = 7823789) B7823789
theorem B1832583 : Blo 1831617 1832583 := bstep (se 1 (by rfl) ⟨1374437, by rfl⟩ : syracuseStep 1832583 = 2748875) B2748875
theorem B2750087 : Blo 1831617 2750087 := bstep (se 1 (by rfl) ⟨2062565, by rfl⟩ : syracuseStep 2750087 = 4125131) B4125131
theorem B1832591 : Blo 1831617 1832591 := bstep (se 1 (by rfl) ⟨1374443, by rfl⟩ : syracuseStep 1832591 = 2748887) B2748887
theorem B2061967 : Blo 1831617 2061967 := bstep (se 1 (by rfl) ⟨1546475, by rfl⟩ : syracuseStep 2061967 = 3092951) B3092951
theorem B3913363 : Blo 1831617 3913363 := bstep (se 1 (by rfl) ⟨2935022, by rfl⟩ : syracuseStep 3913363 = 5870045) B5870045
theorem B2750123 : Blo 1831617 2750123 := bstep (se 1 (by rfl) ⟨2062592, by rfl⟩ : syracuseStep 2750123 = 4125185) B4125185
theorem B1832635 : Blo 1831617 1832635 := bstep (se 1 (by rfl) ⟨1374476, by rfl⟩ : syracuseStep 1832635 = 2748953) B2748953
theorem B4404937 : Blo 1831617 4404937 := bstep (se 2 (by rfl) ⟨1651851, by rfl⟩ : syracuseStep 4404937 = 3303703) B3303703
theorem B2750153 : Blo 1831617 2750153 := bstep (se 2 (by rfl) ⟨1031307, by rfl⟩ : syracuseStep 2750153 = 2062615) B2062615
theorem B1832711 : Blo 1831617 1832711 := bstep (se 1 (by rfl) ⟨1374533, by rfl⟩ : syracuseStep 1832711 = 2749067) B2749067
theorem B1857295 : Blo 1831617 1857295 := bstep (se 1 (by rfl) ⟨1392971, by rfl⟩ : syracuseStep 1857295 = 2785943) B2785943
theorem B1832719 : Blo 1831617 1832719 := bstep (se 1 (by rfl) ⟨1374539, by rfl⟩ : syracuseStep 1832719 = 2749079) B2749079
theorem B1832763 : Blo 1831617 1832763 := bstep (se 1 (by rfl) ⟨1374572, by rfl⟩ : syracuseStep 1832763 = 2749145) B2749145
theorem B2750267 : Blo 1831617 2750267 := bstep (se 1 (by rfl) ⟨2062700, by rfl⟩ : syracuseStep 2750267 = 4125401) B4125401
theorem B2750327 : Blo 1831617 2750327 := bstep (se 1 (by rfl) ⟨2062745, by rfl⟩ : syracuseStep 2750327 = 4125491) B4125491
theorem B1832839 : Blo 1831617 1832839 := bstep (se 1 (by rfl) ⟨1374629, by rfl⟩ : syracuseStep 1832839 = 2749259) B2749259
theorem B1832847 : Blo 1831617 1832847 := bstep (se 1 (by rfl) ⟨1374635, by rfl⟩ : syracuseStep 1832847 = 2749271) B2749271
theorem B2750351 : Blo 1831617 2750351 := bstep (se 1 (by rfl) ⟨2062763, by rfl⟩ : syracuseStep 2750351 = 4125527) B4125527
theorem B2750393 : Blo 1831617 2750393 := bstep (se 2 (by rfl) ⟨1031397, by rfl⟩ : syracuseStep 2750393 = 2062795) B2062795
theorem B1832891 : Blo 1831617 1832891 := bstep (se 1 (by rfl) ⟨1374668, by rfl⟩ : syracuseStep 1832891 = 2749337) B2749337
theorem B5216201 : Blo 1831617 5216201 := bstep (se 2 (by rfl) ⟨1956075, by rfl⟩ : syracuseStep 5216201 = 3912151) B3912151
theorem B1832967 : Blo 1831617 1832967 := bstep (se 1 (by rfl) ⟨1374725, by rfl⟩ : syracuseStep 1832967 = 2749451) B2749451
theorem B1832975 : Blo 1831617 1832975 := bstep (se 1 (by rfl) ⟨1374731, by rfl⟩ : syracuseStep 1832975 = 2749463) B2749463
theorem B1833019 : Blo 1831617 1833019 := bstep (se 1 (by rfl) ⟨1374764, by rfl⟩ : syracuseStep 1833019 = 2749529) B2749529
theorem B6182999 : Blo 1831617 6182999 := bstep (se 1 (by rfl) ⟨4637249, by rfl⟩ : syracuseStep 6182999 = 9274499) B9274499
theorem B1833095 : Blo 1831617 1833095 := bstep (se 1 (by rfl) ⟨1374821, by rfl⟩ : syracuseStep 1833095 = 2749643) B2749643
theorem B2062471 : Blo 1831617 2062471 := bstep (se 1 (by rfl) ⟨1546853, by rfl⟩ : syracuseStep 2062471 = 3093707) B3093707
theorem B1833103 : Blo 1831617 1833103 := bstep (se 1 (by rfl) ⟨1374827, by rfl⟩ : syracuseStep 1833103 = 2749655) B2749655
theorem B3479699 : Blo 1831617 3479699 := bstep (se 1 (by rfl) ⟨2609774, by rfl⟩ : syracuseStep 3479699 = 5219549) B5219549
theorem B22911149 : Blo 1831617 22911149 := bstep (se 3 (by rfl) ⟨4295840, by rfl⟩ : syracuseStep 22911149 = 8591681) B8591681
theorem B1833147 : Blo 1831617 1833147 := bstep (se 1 (by rfl) ⟨1374860, by rfl⟩ : syracuseStep 1833147 = 2749721) B2749721
theorem B3479753 : Blo 1831617 3479753 := bstep (se 2 (by rfl) ⟨1304907, by rfl⟩ : syracuseStep 3479753 = 2609815) B2609815
theorem B1833223 : Blo 1831617 1833223 := bstep (se 1 (by rfl) ⟨1374917, by rfl⟩ : syracuseStep 1833223 = 2749835) B2749835
theorem B1833231 : Blo 1831617 1833231 := bstep (se 1 (by rfl) ⟨1374923, by rfl⟩ : syracuseStep 1833231 = 2749847) B2749847
theorem B3479851 : Blo 1831617 3479851 := bstep (se 1 (by rfl) ⟨2609888, by rfl⟩ : syracuseStep 3479851 = 5219777) B5219777
theorem B1833275 : Blo 1831617 1833275 := bstep (se 1 (by rfl) ⟨1374956, by rfl⟩ : syracuseStep 1833275 = 2749913) B2749913
theorem B2062651 : Blo 1831617 2062651 := bstep (se 1 (by rfl) ⟨1546988, by rfl⟩ : syracuseStep 2062651 = 3093977) B3093977
theorem B1833351 : Blo 1831617 1833351 := bstep (se 1 (by rfl) ⟨1375013, by rfl⟩ : syracuseStep 1833351 = 2750027) B2750027
theorem B1833359 : Blo 1831617 1833359 := bstep (se 1 (by rfl) ⟨1375019, by rfl⟩ : syracuseStep 1833359 = 2750039) B2750039
theorem B1833403 : Blo 1831617 1833403 := bstep (se 1 (by rfl) ⟨1375052, by rfl⟩ : syracuseStep 1833403 = 2750105) B2750105
theorem B3348937 : Blo 1831617 3348937 := bstep (se 2 (by rfl) ⟨1255851, by rfl⟩ : syracuseStep 3348937 = 2511703) B2511703
theorem B1833479 : Blo 1831617 1833479 := bstep (se 1 (by rfl) ⟨1375109, by rfl⟩ : syracuseStep 1833479 = 2750219) B2750219
theorem B4700683 : Blo 1831617 4700683 := bstep (se 1 (by rfl) ⟨3525512, by rfl⟩ : syracuseStep 4700683 = 7051025) B7051025
theorem B3480079 : Blo 1831617 3480079 := bstep (se 1 (by rfl) ⟨2610059, by rfl⟩ : syracuseStep 3480079 = 5220119) B5220119
theorem B1833487 : Blo 1831617 1833487 := bstep (se 1 (by rfl) ⟨1375115, by rfl⟩ : syracuseStep 1833487 = 2750231) B2750231
theorem B1833531 : Blo 1831617 1833531 := bstep (se 1 (by rfl) ⟨1375148, by rfl⟩ : syracuseStep 1833531 = 2750297) B2750297
theorem B6183485 : Blo 1831617 6183485 := bstep (se 3 (by rfl) ⟨1159403, by rfl⟩ : syracuseStep 6183485 = 2318807) B2318807
theorem B1833607 : Blo 1831617 1833607 := bstep (se 1 (by rfl) ⟨1375205, by rfl⟩ : syracuseStep 1833607 = 2750411) B2750411
theorem B1833615 : Blo 1831617 1833615 := bstep (se 1 (by rfl) ⟨1375211, by rfl⟩ : syracuseStep 1833615 = 2750423) B2750423
theorem B26409665 : Blo 1831617 26409665 := bstep (se 2 (by rfl) ⟨9903624, by rfl⟩ : syracuseStep 26409665 = 19807249) B19807249
theorem B16718795 : Blo 1831617 16718795 := bstep (se 1 (by rfl) ⟨12539096, by rfl⟩ : syracuseStep 16718795 = 25078193) B25078193
theorem B7830539 : Blo 1831617 7830539 := bstep (se 1 (by rfl) ⟨5872904, by rfl⟩ : syracuseStep 7830539 = 11745809) B11745809
theorem B4701199 : Blo 1831617 4701199 := bstep (se 1 (by rfl) ⟨3525899, by rfl⟩ : syracuseStep 4701199 = 7051799) B7051799
theorem B3177487 : Blo 1831617 3177487 := bstep (se 1 (by rfl) ⟨2383115, by rfl⟩ : syracuseStep 3177487 = 4766231) B4766231
theorem B23477309 : Blo 1831617 23477309 := bstep (se 3 (by rfl) ⟨4401995, by rfl⟩ : syracuseStep 23477309 = 8803991) B8803991
theorem B9534779 : Blo 1831617 9534779 := bstep (se 1 (by rfl) ⟨7151084, by rfl⟩ : syracuseStep 9534779 = 14302169) B14302169
theorem B3915209 : Blo 1831617 3915209 := bstep (se 2 (by rfl) ⟨1468203, by rfl⟩ : syracuseStep 3915209 = 2936407) B2936407
theorem B9666071 : Blo 1831617 9666071 := bstep (se 1 (by rfl) ⟨7249553, by rfl⟩ : syracuseStep 9666071 = 14499107) B14499107
theorem B16080413 : Blo 1831617 16080413 := bstep (se 3 (by rfl) ⟨3015077, by rfl⟩ : syracuseStep 16080413 = 6030155) B6030155
theorem B35225189 : Blo 1831617 35225189 := bstep (se 4 (by rfl) ⟨3302361, by rfl⟩ : syracuseStep 35225189 = 6604723) B6604723
theorem B2350711 : Blo 1831617 2350711 := bstep (se 1 (by rfl) ⟨1763033, by rfl⟩ : syracuseStep 2350711 = 3526067) B3526067
theorem B6954767 : Blo 1831617 6954767 := bstep (se 1 (by rfl) ⟨5216075, by rfl⟩ : syracuseStep 6954767 = 10432151) B10432151
theorem B5218091 : Blo 1831617 5218091 := bstep (se 1 (by rfl) ⟨3913568, by rfl⟩ : syracuseStep 5218091 = 7827137) B7827137
theorem B18816857 : Blo 1831617 18816857 := bstep (se 2 (by rfl) ⟨7056321, by rfl⟩ : syracuseStep 18816857 = 14112643) B14112643
theorem B9273203 : Blo 1831617 9273203 := bstep (se 1 (by rfl) ⟨6954902, by rfl⟩ : syracuseStep 9273203 = 13909805) B13909805
theorem B13918067 : Blo 1831617 13918067 := bstep (se 1 (by rfl) ⟨10438550, by rfl⟩ : syracuseStep 13918067 = 20877101) B20877101
theorem B2318215 : Blo 1831617 2318215 := bstep (se 1 (by rfl) ⟨1738661, by rfl⟩ : syracuseStep 2318215 = 3477323) B3477323
theorem B1957775 : Blo 1831617 1957775 := bstep (se 1 (by rfl) ⟨1468331, by rfl⟩ : syracuseStep 1957775 = 2936663) B2936663
theorem B6184889 : Blo 1831617 6184889 := bstep (se 2 (by rfl) ⟨2319333, by rfl⟩ : syracuseStep 6184889 = 4638667) B4638667
theorem B9281465 : Blo 1831617 9281465 := bstep (se 2 (by rfl) ⟨3480549, by rfl⟩ : syracuseStep 9281465 = 6961099) B6961099
theorem B4702265 : Blo 1831617 4702265 := bstep (se 2 (by rfl) ⟨1763349, by rfl⟩ : syracuseStep 4702265 = 3526699) B3526699
theorem B13205585 : Blo 1831617 13205585 := bstep (se 2 (by rfl) ⟨4952094, by rfl⟩ : syracuseStep 13205585 = 9904189) B9904189
theorem B171524405 : Blo 1831617 171524405 := bstep (se 5 (by rfl) ⟨8040206, by rfl⟩ : syracuseStep 171524405 = 16080413) B16080413
theorem B6185321 : Blo 1831617 6185321 := bstep (se 2 (by rfl) ⟨2319495, by rfl⟩ : syracuseStep 6185321 = 4638991) B4638991
theorem B6603227 : Blo 1831617 6603227 := bstep (se 1 (by rfl) ⟨4952420, by rfl⟩ : syracuseStep 6603227 = 9904841) B9904841
theorem B11149805 : Blo 1831617 11149805 := bstep (se 3 (by rfl) ⟨2090588, by rfl⟩ : syracuseStep 11149805 = 4181177) B4181177
theorem B22282775 : Blo 1831617 22282775 := bstep (se 1 (by rfl) ⟨16712081, by rfl⟩ : syracuseStep 22282775 = 33424163) B33424163
theorem B4637209 : Blo 1831617 4637209 := bstep (se 2 (by rfl) ⟨1738953, by rfl⟩ : syracuseStep 4637209 = 3477907) B3477907
theorem B4465249 : Blo 1831617 4465249 := bstep (se 2 (by rfl) ⟨1674468, by rfl⟩ : syracuseStep 4465249 = 3348937) B3348937
theorem B4637513 : Blo 1831617 4637513 := bstep (se 2 (by rfl) ⟨1739067, by rfl⟩ : syracuseStep 4637513 = 3478135) B3478135
theorem B4121531 : Blo 1831617 4121531 := bstep (se 1 (by rfl) ⟨3091148, by rfl⟩ : syracuseStep 4121531 = 6182297) B6182297
theorem B6185915 : Blo 1831617 6185915 := bstep (se 1 (by rfl) ⟨4639436, by rfl⟩ : syracuseStep 6185915 = 9278873) B9278873
theorem B4121657 : Blo 1831617 4121657 := bstep (se 2 (by rfl) ⟨1545621, by rfl⟩ : syracuseStep 4121657 = 3091243) B3091243
theorem B114353369 : Blo 1831617 114353369 := bstep (se 2 (by rfl) ⟨42882513, by rfl⟩ : syracuseStep 114353369 = 85765027) B85765027
theorem B13919525 : Blo 1831617 13919525 := bstep (se 4 (by rfl) ⟨1304955, by rfl⟩ : syracuseStep 13919525 = 2609911) B2609911
theorem B6268265 : Blo 1831617 6268265 := bstep (se 2 (by rfl) ⟨2350599, by rfl⟩ : syracuseStep 6268265 = 4701199) B4701199
theorem B4121999 : Blo 1831617 4121999 := bstep (se 1 (by rfl) ⟨3091499, by rfl⟩ : syracuseStep 4121999 = 6182999) B6182999
theorem B9905573 : Blo 1831617 9905573 := bstep (se 4 (by rfl) ⟨928647, by rfl⟩ : syracuseStep 9905573 = 1857295) B1857295
theorem B11904421 : Blo 1831617 11904421 := bstep (se 4 (by rfl) ⟨1116039, by rfl⟩ : syracuseStep 11904421 = 2232079) B2232079
theorem B16942537 : Blo 1831617 16942537 := bstep (se 2 (by rfl) ⟨6353451, by rfl⟩ : syracuseStep 16942537 = 12706903) B12706903
theorem B2319835 : Blo 1831617 2319835 := bstep (se 1 (by rfl) ⟨1739876, by rfl⟩ : syracuseStep 2319835 = 3479753) B3479753
theorem B20882933 : Blo 1831617 20882933 := bstep (se 5 (by rfl) ⟨978887, by rfl⟩ : syracuseStep 20882933 = 1957775) B1957775
theorem B6784697 : Blo 1831617 6784697 := bstep (se 2 (by rfl) ⟨2544261, by rfl⟩ : syracuseStep 6784697 = 5088523) B5088523
theorem B8357575 : Blo 1831617 8357575 := bstep (se 1 (by rfl) ⟨6268181, by rfl⟩ : syracuseStep 8357575 = 12536363) B12536363
theorem B4122323 : Blo 1831617 4122323 := bstep (se 1 (by rfl) ⟨3091742, by rfl⟩ : syracuseStep 4122323 = 6183485) B6183485
theorem B4638647 : Blo 1831617 4638647 := bstep (se 1 (by rfl) ⟨3478985, by rfl⟩ : syracuseStep 4638647 = 6957971) B6957971
theorem B2934715 : Blo 1831617 2934715 := bstep (se 1 (by rfl) ⟨2201036, by rfl⟩ : syracuseStep 2934715 = 4402073) B4402073
theorem B5220359 : Blo 1831617 5220359 := bstep (se 1 (by rfl) ⟨3915269, by rfl⟩ : syracuseStep 5220359 = 7830539) B7830539
theorem B7825565 : Blo 1831617 7825565 := bstep (se 3 (by rfl) ⟨1467293, by rfl⟩ : syracuseStep 7825565 = 2934587) B2934587
theorem B9406621 : Blo 1831617 9406621 := bstep (se 3 (by rfl) ⟨1763741, by rfl⟩ : syracuseStep 9406621 = 3527483) B3527483
theorem B3090953 : Blo 1831617 3090953 := bstep (se 2 (by rfl) ⟨1159107, by rfl⟩ : syracuseStep 3090953 = 2318215) B2318215
theorem B12544571 : Blo 1831617 12544571 := bstep (se 1 (by rfl) ⟨9408428, by rfl⟩ : syracuseStep 12544571 = 18816857) B18816857
theorem B4123259 : Blo 1831617 4123259 := bstep (se 1 (by rfl) ⟨3092444, by rfl⟩ : syracuseStep 4123259 = 6184889) B6184889
theorem B6187643 : Blo 1831617 6187643 := bstep (se 1 (by rfl) ⟨4640732, by rfl⟩ : syracuseStep 6187643 = 9281465) B9281465
theorem B3091115 : Blo 1831617 3091115 := bstep (se 1 (by rfl) ⟨2318336, by rfl⟩ : syracuseStep 3091115 = 4636673) B4636673
theorem B8809145 : Blo 1831617 8809145 := bstep (se 2 (by rfl) ⟨3303429, by rfl⟩ : syracuseStep 8809145 = 6606859) B6606859
theorem B25070309 : Blo 1831617 25070309 := bstep (se 4 (by rfl) ⟨2350341, by rfl⟩ : syracuseStep 25070309 = 4700683) B4700683
theorem B4123385 : Blo 1831617 4123385 := bstep (se 2 (by rfl) ⟨1546269, by rfl⟩ : syracuseStep 4123385 = 3092539) B3092539
theorem B6187805 : Blo 1831617 6187805 := bstep (se 3 (by rfl) ⟨1160213, by rfl⟩ : syracuseStep 6187805 = 2320427) B2320427
theorem B60271397 : Blo 1831617 60271397 := bstep (se 4 (by rfl) ⟨5650443, by rfl⟩ : syracuseStep 60271397 = 11300887) B11300887
theorem B4123655 : Blo 1831617 4123655 := bstep (se 1 (by rfl) ⟨3092741, by rfl⟩ : syracuseStep 4123655 = 6185483) B6185483
theorem B4639751 : Blo 1831617 4639751 := bstep (se 1 (by rfl) ⟨3479813, by rfl⟩ : syracuseStep 4639751 = 6959627) B6959627
theorem B3091513 : Blo 1831617 3091513 := bstep (se 2 (by rfl) ⟨1159317, by rfl⟩ : syracuseStep 3091513 = 2318635) B2318635
theorem B4639801 : Blo 1831617 4639801 := bstep (se 2 (by rfl) ⟨1739925, by rfl⟩ : syracuseStep 4639801 = 3479851) B3479851
theorem B2747471 : Blo 1831617 2747471 := bstep (se 1 (by rfl) ⟨2060603, by rfl⟩ : syracuseStep 2747471 = 4121207) B4121207
theorem B4123727 : Blo 1831617 4123727 := bstep (se 1 (by rfl) ⟨3092795, by rfl⟩ : syracuseStep 4123727 = 6185591) B6185591
theorem B5573711 : Blo 1831617 5573711 := bstep (se 1 (by rfl) ⟨4180283, by rfl⟩ : syracuseStep 5573711 = 8360567) B8360567
theorem B13913207 : Blo 1831617 13913207 := bstep (se 1 (by rfl) ⟨10434905, by rfl⟩ : syracuseStep 13913207 = 20869811) B20869811
theorem B2747591 : Blo 1831617 2747591 := bstep (se 1 (by rfl) ⟨2060693, by rfl⟩ : syracuseStep 2747591 = 4121387) B4121387
theorem B3091655 : Blo 1831617 3091655 := bstep (se 1 (by rfl) ⟨2318741, by rfl⟩ : syracuseStep 3091655 = 4637483) B4637483
theorem B12709067 : Blo 1831617 12709067 := bstep (se 1 (by rfl) ⟨9531800, by rfl⟩ : syracuseStep 12709067 = 19063601) B19063601
theorem B12537125 : Blo 1831617 12537125 := bstep (se 4 (by rfl) ⟨1175355, by rfl⟩ : syracuseStep 12537125 = 2350711) B2350711
theorem B2747753 : Blo 1831617 2747753 := bstep (se 2 (by rfl) ⟨1030407, by rfl⟩ : syracuseStep 2747753 = 2060815) B2060815
theorem B3091817 : Blo 1831617 3091817 := bstep (se 2 (by rfl) ⟨1159431, by rfl⟩ : syracuseStep 3091817 = 2318863) B2318863
theorem B4640105 : Blo 1831617 4640105 := bstep (se 2 (by rfl) ⟨1740039, by rfl⟩ : syracuseStep 4640105 = 3480079) B3480079
theorem B2747831 : Blo 1831617 2747831 := bstep (se 1 (by rfl) ⟨2060873, by rfl⟩ : syracuseStep 2747831 = 4121747) B4121747
theorem B2747867 : Blo 1831617 2747867 := bstep (se 1 (by rfl) ⟨2060900, by rfl⟩ : syracuseStep 2747867 = 4121801) B4121801
theorem B4124123 : Blo 1831617 4124123 := bstep (se 1 (by rfl) ⟨3093092, by rfl⟩ : syracuseStep 4124123 = 6186185) B6186185
theorem B3477239 : Blo 1831617 3477239 := bstep (se 1 (by rfl) ⟨2607929, by rfl⟩ : syracuseStep 3477239 = 5215859) B5215859
theorem B3092215 : Blo 1831617 3092215 := bstep (se 1 (by rfl) ⟨2319161, by rfl⟩ : syracuseStep 3092215 = 4638323) B4638323
theorem B6958943 : Blo 1831617 6958943 := bstep (se 1 (by rfl) ⟨5219207, by rfl⟩ : syracuseStep 6958943 = 10438415) B10438415
theorem B2748335 : Blo 1831617 2748335 := bstep (se 1 (by rfl) ⟨2061251, by rfl⟩ : syracuseStep 2748335 = 4122503) B4122503
theorem B4124591 : Blo 1831617 4124591 := bstep (se 1 (by rfl) ⟨3093443, by rfl⟩ : syracuseStep 4124591 = 6186887) B6186887
theorem B3092411 : Blo 1831617 3092411 := bstep (se 1 (by rfl) ⟨2319308, by rfl⟩ : syracuseStep 3092411 = 4638617) B4638617
theorem B3477467 : Blo 1831617 3477467 := bstep (se 1 (by rfl) ⟨2608100, by rfl⟩ : syracuseStep 3477467 = 5216201) B5216201
theorem B2748425 : Blo 1831617 2748425 := bstep (se 2 (by rfl) ⟨1030659, by rfl⟩ : syracuseStep 2748425 = 2061319) B2061319
theorem B2748455 : Blo 1831617 2748455 := bstep (se 1 (by rfl) ⟨2061341, by rfl⟩ : syracuseStep 2748455 = 4122683) B4122683
theorem B3092519 : Blo 1831617 3092519 := bstep (se 1 (by rfl) ⟨2319389, by rfl⟩ : syracuseStep 3092519 = 4638779) B4638779
theorem B15274099 : Blo 1831617 15274099 := bstep (se 1 (by rfl) ⟨11455574, by rfl⟩ : syracuseStep 15274099 = 22911149) B22911149
theorem B2748539 : Blo 1831617 2748539 := bstep (se 1 (by rfl) ⟨2061404, by rfl⟩ : syracuseStep 2748539 = 4122809) B4122809
theorem B4124843 : Blo 1831617 4124843 := bstep (se 1 (by rfl) ⟨3093632, by rfl⟩ : syracuseStep 4124843 = 6187265) B6187265
theorem B2748665 : Blo 1831617 2748665 := bstep (se 2 (by rfl) ⟨1030749, by rfl⟩ : syracuseStep 2748665 = 2061499) B2061499
theorem B3715321 : Blo 1831617 3715321 := bstep (se 2 (by rfl) ⟨1393245, by rfl⟩ : syracuseStep 3715321 = 2786491) B2786491
theorem B15274241 : Blo 1831617 15274241 := bstep (se 2 (by rfl) ⟨5727840, by rfl⟩ : syracuseStep 15274241 = 11455681) B11455681
theorem B3092809 : Blo 1831617 3092809 := bstep (se 2 (by rfl) ⟨1159803, by rfl⟩ : syracuseStep 3092809 = 2319607) B2319607
theorem B2748767 : Blo 1831617 2748767 := bstep (se 1 (by rfl) ⟨2061575, by rfl⟩ : syracuseStep 2748767 = 4123151) B4123151
theorem B2748779 : Blo 1831617 2748779 := bstep (se 1 (by rfl) ⟨2061584, by rfl⟩ : syracuseStep 2748779 = 4123169) B4123169
theorem B3092843 : Blo 1831617 3092843 := bstep (se 1 (by rfl) ⟨2319632, by rfl⟩ : syracuseStep 3092843 = 4639265) B4639265
theorem B3576329 : Blo 1831617 3576329 := bstep (se 2 (by rfl) ⟨1341123, by rfl⟩ : syracuseStep 3576329 = 2682247) B2682247
theorem B6959641 : Blo 1831617 6959641 := bstep (se 2 (by rfl) ⟨2609865, by rfl⟩ : syracuseStep 6959641 = 5219731) B5219731
theorem B10433083 : Blo 1831617 10433083 := bstep (se 1 (by rfl) ⟨7824812, by rfl⟩ : syracuseStep 10433083 = 15649625) B15649625
theorem B2749007 : Blo 1831617 2749007 := bstep (se 1 (by rfl) ⟨2061755, by rfl⟩ : syracuseStep 2749007 = 4123511) B4123511
theorem B2060923 : Blo 1831617 2060923 := bstep (se 1 (by rfl) ⟨1545692, by rfl⟩ : syracuseStep 2060923 = 3091385) B3091385
theorem B11145863 : Blo 1831617 11145863 := bstep (se 1 (by rfl) ⟨8359397, by rfl⟩ : syracuseStep 11145863 = 16718795) B16718795
theorem B8811143 : Blo 1831617 8811143 := bstep (se 1 (by rfl) ⟨6608357, by rfl⟩ : syracuseStep 8811143 = 13216715) B13216715
theorem B1831623 : Blo 1831617 1831623 := bstep (se 1 (by rfl) ⟨1373717, by rfl⟩ : syracuseStep 1831623 = 2747435) B2747435
theorem B2749127 : Blo 1831617 2749127 := bstep (se 1 (by rfl) ⟨2061845, by rfl⟩ : syracuseStep 2749127 = 4123691) B4123691
theorem B4125383 : Blo 1831617 4125383 := bstep (se 1 (by rfl) ⟨3094037, by rfl⟩ : syracuseStep 4125383 = 6188075) B6188075
theorem B15651539 : Blo 1831617 15651539 := bstep (se 1 (by rfl) ⟨11738654, by rfl⟩ : syracuseStep 15651539 = 23477309) B23477309
theorem B1831643 : Blo 1831617 1831643 := bstep (se 1 (by rfl) ⟨1373732, by rfl⟩ : syracuseStep 1831643 = 2747465) B2747465
theorem B3093241 : Blo 1831617 3093241 := bstep (se 2 (by rfl) ⟨1159965, by rfl⟩ : syracuseStep 3093241 = 2319931) B2319931
theorem B11735837 : Blo 1831617 11735837 := bstep (se 3 (by rfl) ⟨2200469, by rfl⟩ : syracuseStep 11735837 = 4400939) B4400939
theorem B1831719 : Blo 1831617 1831719 := bstep (se 1 (by rfl) ⟨1373789, by rfl⟩ : syracuseStep 1831719 = 2747579) B2747579
theorem B6959915 : Blo 1831617 6959915 := bstep (se 1 (by rfl) ⟨5219936, by rfl⟩ : syracuseStep 6959915 = 10439873) B10439873
theorem B6959945 : Blo 1831617 6959945 := bstep (se 2 (by rfl) ⟨2609979, by rfl⟩ : syracuseStep 6959945 = 5219959) B5219959
theorem B1831759 : Blo 1831617 1831759 := bstep (se 1 (by rfl) ⟨1373819, by rfl⟩ : syracuseStep 1831759 = 2747639) B2747639
theorem B1831775 : Blo 1831617 1831775 := bstep (se 1 (by rfl) ⟨1373831, by rfl⟩ : syracuseStep 1831775 = 2747663) B2747663
theorem B2749289 : Blo 1831617 2749289 := bstep (se 2 (by rfl) ⟨1030983, by rfl⟩ : syracuseStep 2749289 = 2061967) B2061967
theorem B1831803 : Blo 1831617 1831803 := bstep (se 1 (by rfl) ⟨1373852, by rfl⟩ : syracuseStep 1831803 = 2747705) B2747705
theorem B1831855 : Blo 1831617 1831855 := bstep (se 1 (by rfl) ⟨1373891, by rfl⟩ : syracuseStep 1831855 = 2747783) B2747783
theorem B2749367 : Blo 1831617 2749367 := bstep (se 1 (by rfl) ⟨2062025, by rfl⟩ : syracuseStep 2749367 = 4124051) B4124051
theorem B1831879 : Blo 1831617 1831879 := bstep (se 1 (by rfl) ⟨1373909, by rfl⟩ : syracuseStep 1831879 = 2747819) B2747819
theorem B1831899 : Blo 1831617 1831899 := bstep (se 1 (by rfl) ⟨1373924, by rfl⟩ : syracuseStep 1831899 = 2747849) B2747849
theorem B2749403 : Blo 1831617 2749403 := bstep (se 1 (by rfl) ⟨2062052, by rfl⟩ : syracuseStep 2749403 = 4124105) B4124105
theorem B2610139 : Blo 1831617 2610139 := bstep (se 1 (by rfl) ⟨1957604, by rfl⟩ : syracuseStep 2610139 = 3915209) B3915209
theorem B3093511 : Blo 1831617 3093511 := bstep (se 1 (by rfl) ⟨2320133, by rfl⟩ : syracuseStep 3093511 = 4640267) B4640267
theorem B6444047 : Blo 1831617 6444047 := bstep (se 1 (by rfl) ⟨4833035, by rfl⟩ : syracuseStep 6444047 = 9666071) B9666071
theorem B1831975 : Blo 1831617 1831975 := bstep (se 1 (by rfl) ⟨1373981, by rfl⟩ : syracuseStep 1831975 = 2747963) B2747963
theorem B23483459 : Blo 1831617 23483459 := bstep (se 1 (by rfl) ⟨17612594, by rfl⟩ : syracuseStep 23483459 = 35225189) B35225189
theorem B1832015 : Blo 1831617 1832015 := bstep (se 1 (by rfl) ⟨1374011, by rfl⟩ : syracuseStep 1832015 = 2748023) B2748023
theorem B2061391 : Blo 1831617 2061391 := bstep (se 1 (by rfl) ⟨1546043, by rfl⟩ : syracuseStep 2061391 = 3092087) B3092087
theorem B1832031 : Blo 1831617 1832031 := bstep (se 1 (by rfl) ⟨1374023, by rfl⟩ : syracuseStep 1832031 = 2748047) B2748047
theorem B1832059 : Blo 1831617 1832059 := bstep (se 1 (by rfl) ⟨1374044, by rfl⟩ : syracuseStep 1832059 = 2748089) B2748089
theorem B1832111 : Blo 1831617 1832111 := bstep (se 1 (by rfl) ⟨1374083, by rfl⟩ : syracuseStep 1832111 = 2748167) B2748167
theorem B1832135 : Blo 1831617 1832135 := bstep (se 1 (by rfl) ⟨1374101, by rfl⟩ : syracuseStep 1832135 = 2748203) B2748203
theorem B3478727 : Blo 1831617 3478727 := bstep (se 1 (by rfl) ⟨2609045, by rfl⟩ : syracuseStep 3478727 = 5218091) B5218091
theorem B1832155 : Blo 1831617 1832155 := bstep (se 1 (by rfl) ⟨1374116, by rfl⟩ : syracuseStep 1832155 = 2748233) B2748233
theorem B6182135 : Blo 1831617 6182135 := bstep (se 1 (by rfl) ⟨4636601, by rfl⟩ : syracuseStep 6182135 = 9273203) B9273203
theorem B9278711 : Blo 1831617 9278711 := bstep (se 1 (by rfl) ⟨6959033, by rfl⟩ : syracuseStep 9278711 = 13918067) B13918067
theorem B1832231 : Blo 1831617 1832231 := bstep (se 1 (by rfl) ⟨1374173, by rfl⟩ : syracuseStep 1832231 = 2748347) B2748347
theorem B1832271 : Blo 1831617 1832271 := bstep (se 1 (by rfl) ⟨1374203, by rfl⟩ : syracuseStep 1832271 = 2748407) B2748407
theorem B1832287 : Blo 1831617 1832287 := bstep (se 1 (by rfl) ⟨1374215, by rfl⟩ : syracuseStep 1832287 = 2748431) B2748431
theorem B3478879 : Blo 1831617 3478879 := bstep (se 1 (by rfl) ⟨2609159, by rfl⟩ : syracuseStep 3478879 = 5218319) B5218319
theorem B3528031 : Blo 1831617 3528031 := bstep (se 1 (by rfl) ⟨2646023, by rfl⟩ : syracuseStep 3528031 = 5292047) B5292047
theorem B1832315 : Blo 1831617 1832315 := bstep (se 1 (by rfl) ⟨1374236, by rfl⟩ : syracuseStep 1832315 = 2748473) B2748473
theorem B5019023 : Blo 1831617 5019023 := bstep (se 1 (by rfl) ⟨3764267, by rfl⟩ : syracuseStep 5019023 = 7528535) B7528535
theorem B3716513 : Blo 1831617 3716513 := bstep (se 2 (by rfl) ⟨1393692, by rfl⟩ : syracuseStep 3716513 = 2787385) B2787385
theorem B16946597 : Blo 1831617 16946597 := bstep (se 4 (by rfl) ⟨1588743, by rfl⟩ : syracuseStep 16946597 = 3177487) B3177487
theorem B1832367 : Blo 1831617 1832367 := bstep (se 1 (by rfl) ⟨1374275, by rfl⟩ : syracuseStep 1832367 = 2748551) B2748551
theorem B2749871 : Blo 1831617 2749871 := bstep (se 1 (by rfl) ⟨2062403, by rfl⟩ : syracuseStep 2749871 = 4124807) B4124807
theorem B3093943 : Blo 1831617 3093943 := bstep (se 1 (by rfl) ⟨2320457, by rfl⟩ : syracuseStep 3093943 = 4640915) B4640915
theorem B1832391 : Blo 1831617 1832391 := bstep (se 1 (by rfl) ⟨1374293, by rfl⟩ : syracuseStep 1832391 = 2748587) B2748587
theorem B1832411 : Blo 1831617 1832411 := bstep (se 1 (by rfl) ⟨1374308, by rfl⟩ : syracuseStep 1832411 = 2748617) B2748617
theorem B2061787 : Blo 1831617 2061787 := bstep (se 1 (by rfl) ⟨1546340, by rfl⟩ : syracuseStep 2061787 = 3092681) B3092681
theorem B2749961 : Blo 1831617 2749961 := bstep (se 2 (by rfl) ⟨1031235, by rfl⟩ : syracuseStep 2749961 = 2062471) B2062471
theorem B1832487 : Blo 1831617 1832487 := bstep (se 1 (by rfl) ⟨1374365, by rfl⟩ : syracuseStep 1832487 = 2748731) B2748731
theorem B2749991 : Blo 1831617 2749991 := bstep (se 1 (by rfl) ⟨2062493, by rfl⟩ : syracuseStep 2749991 = 4124987) B4124987
theorem B6182459 : Blo 1831617 6182459 := bstep (se 1 (by rfl) ⟨4636844, by rfl⟩ : syracuseStep 6182459 = 9273689) B9273689
theorem B1832527 : Blo 1831617 1832527 := bstep (se 1 (by rfl) ⟨1374395, by rfl⟩ : syracuseStep 1832527 = 2748791) B2748791
theorem B1832543 : Blo 1831617 1832543 := bstep (se 1 (by rfl) ⟨1374407, by rfl⟩ : syracuseStep 1832543 = 2748815) B2748815
theorem B3176059 : Blo 1831617 3176059 := bstep (se 1 (by rfl) ⟨2382044, by rfl⟩ : syracuseStep 3176059 = 4764089) B4764089
theorem B1832571 : Blo 1831617 1832571 := bstep (se 1 (by rfl) ⟨1374428, by rfl⟩ : syracuseStep 1832571 = 2748857) B2748857
theorem B2750075 : Blo 1831617 2750075 := bstep (se 1 (by rfl) ⟨2062556, by rfl⟩ : syracuseStep 2750075 = 4125113) B4125113
theorem B3094139 : Blo 1831617 3094139 := bstep (se 1 (by rfl) ⟨2320604, by rfl⟩ : syracuseStep 3094139 = 4641209) B4641209
theorem B12539531 : Blo 1831617 12539531 := bstep (se 1 (by rfl) ⟨9404648, by rfl⟩ : syracuseStep 12539531 = 18809297) B18809297
theorem B1832623 : Blo 1831617 1832623 := bstep (se 1 (by rfl) ⟨1374467, by rfl⟩ : syracuseStep 1832623 = 2748935) B2748935
theorem B1832647 : Blo 1831617 1832647 := bstep (se 1 (by rfl) ⟨1374485, by rfl⟩ : syracuseStep 1832647 = 2748971) B2748971
theorem B1832667 : Blo 1831617 1832667 := bstep (se 1 (by rfl) ⟨1374500, by rfl⟩ : syracuseStep 1832667 = 2749001) B2749001
theorem B9279197 : Blo 1831617 9279197 := bstep (se 3 (by rfl) ⟨1739849, by rfl⟩ : syracuseStep 9279197 = 3479699) B3479699
theorem B15652601 : Blo 1831617 15652601 := bstep (se 2 (by rfl) ⟨5869725, by rfl⟩ : syracuseStep 15652601 = 11739451) B11739451
theorem B2750201 : Blo 1831617 2750201 := bstep (se 2 (by rfl) ⟨1031325, by rfl⟩ : syracuseStep 2750201 = 2062651) B2062651
theorem B1832743 : Blo 1831617 1832743 := bstep (se 1 (by rfl) ⟨1374557, by rfl⟩ : syracuseStep 1832743 = 2749115) B2749115
theorem B6182729 : Blo 1831617 6182729 := bstep (se 2 (by rfl) ⟨2318523, by rfl⟩ : syracuseStep 6182729 = 4637047) B4637047
theorem B1832783 : Blo 1831617 1832783 := bstep (se 1 (by rfl) ⟨1374587, by rfl⟩ : syracuseStep 1832783 = 2749175) B2749175
theorem B1832799 : Blo 1831617 1832799 := bstep (se 1 (by rfl) ⟨1374599, by rfl⟩ : syracuseStep 1832799 = 2749199) B2749199
theorem B2750303 : Blo 1831617 2750303 := bstep (se 1 (by rfl) ⟨2062727, by rfl⟩ : syracuseStep 2750303 = 4125455) B4125455
theorem B2750315 : Blo 1831617 2750315 := bstep (se 1 (by rfl) ⟨2062736, by rfl⟩ : syracuseStep 2750315 = 4125473) B4125473
theorem B1832827 : Blo 1831617 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B1832879 : Blo 1831617 1832879 := bstep (se 1 (by rfl) ⟨1374659, by rfl⟩ : syracuseStep 1832879 = 2749319) B2749319
theorem B2062255 : Blo 1831617 2062255 := bstep (se 1 (by rfl) ⟨1546691, by rfl⟩ : syracuseStep 2062255 = 3093383) B3093383
theorem B13211585 : Blo 1831617 13211585 := bstep (se 2 (by rfl) ⟨4954344, by rfl⟩ : syracuseStep 13211585 = 9908689) B9908689
theorem B1832903 : Blo 1831617 1832903 := bstep (se 1 (by rfl) ⟨1374677, by rfl⟩ : syracuseStep 1832903 = 2749355) B2749355
theorem B1832923 : Blo 1831617 1832923 := bstep (se 1 (by rfl) ⟨1374692, by rfl⟩ : syracuseStep 1832923 = 2749385) B2749385
theorem B5871635 : Blo 1831617 5871635 := bstep (se 1 (by rfl) ⟨4403726, by rfl⟩ : syracuseStep 5871635 = 8807453) B8807453
theorem B10442789 : Blo 1831617 10442789 := bstep (se 4 (by rfl) ⟨979011, by rfl⟩ : syracuseStep 10442789 = 1958023) B1958023
theorem B1832999 : Blo 1831617 1832999 := bstep (se 1 (by rfl) ⟨1374749, by rfl⟩ : syracuseStep 1832999 = 2749499) B2749499
theorem B1833039 : Blo 1831617 1833039 := bstep (se 1 (by rfl) ⟨1374779, by rfl⟩ : syracuseStep 1833039 = 2749559) B2749559
theorem B1833055 : Blo 1831617 1833055 := bstep (se 1 (by rfl) ⟨1374791, by rfl⟩ : syracuseStep 1833055 = 2749583) B2749583
theorem B20871269 : Blo 1831617 20871269 := bstep (se 4 (by rfl) ⟨1956681, by rfl⟩ : syracuseStep 20871269 = 3913363) B3913363
theorem B14112883 : Blo 1831617 14112883 := bstep (se 1 (by rfl) ⟨10584662, by rfl⟩ : syracuseStep 14112883 = 21169325) B21169325
theorem B1833083 : Blo 1831617 1833083 := bstep (se 1 (by rfl) ⟨1374812, by rfl⟩ : syracuseStep 1833083 = 2749625) B2749625
theorem B1833135 : Blo 1831617 1833135 := bstep (se 1 (by rfl) ⟨1374851, by rfl⟩ : syracuseStep 1833135 = 2749703) B2749703
theorem B1833159 : Blo 1831617 1833159 := bstep (se 1 (by rfl) ⟨1374869, by rfl⟩ : syracuseStep 1833159 = 2749739) B2749739
theorem B1833179 : Blo 1831617 1833179 := bstep (se 1 (by rfl) ⟨1374884, by rfl⟩ : syracuseStep 1833179 = 2749769) B2749769
theorem B1833255 : Blo 1831617 1833255 := bstep (se 1 (by rfl) ⟨1374941, by rfl⟩ : syracuseStep 1833255 = 2749883) B2749883
theorem B1833295 : Blo 1831617 1833295 := bstep (se 1 (by rfl) ⟨1374971, by rfl⟩ : syracuseStep 1833295 = 2749943) B2749943
theorem B1833311 : Blo 1831617 1833311 := bstep (se 1 (by rfl) ⟨1374983, by rfl⟩ : syracuseStep 1833311 = 2749967) B2749967
theorem B2062687 : Blo 1831617 2062687 := bstep (se 1 (by rfl) ⟨1547015, by rfl⟩ : syracuseStep 2062687 = 3094031) B3094031
theorem B11901289 : Blo 1831617 11901289 := bstep (se 2 (by rfl) ⟨4462983, by rfl⟩ : syracuseStep 11901289 = 8925967) B8925967
theorem B4405609 : Blo 1831617 4405609 := bstep (se 2 (by rfl) ⟨1652103, by rfl⟩ : syracuseStep 4405609 = 3304207) B3304207
theorem B1833339 : Blo 1831617 1833339 := bstep (se 1 (by rfl) ⟨1375004, by rfl⟩ : syracuseStep 1833339 = 2750009) B2750009
theorem B1833391 : Blo 1831617 1833391 := bstep (se 1 (by rfl) ⟨1375043, by rfl⟩ : syracuseStep 1833391 = 2750087) B2750087
theorem B1833415 : Blo 1831617 1833415 := bstep (se 1 (by rfl) ⟨1375061, by rfl⟩ : syracuseStep 1833415 = 2750123) B2750123
theorem B1833435 : Blo 1831617 1833435 := bstep (se 1 (by rfl) ⟨1375076, by rfl⟩ : syracuseStep 1833435 = 2750153) B2750153
theorem B1833511 : Blo 1831617 1833511 := bstep (se 1 (by rfl) ⟨1375133, by rfl⟩ : syracuseStep 1833511 = 2750267) B2750267
theorem B1833551 : Blo 1831617 1833551 := bstep (se 1 (by rfl) ⟨1375163, by rfl⟩ : syracuseStep 1833551 = 2750327) B2750327
theorem B1833567 : Blo 1831617 1833567 := bstep (se 1 (by rfl) ⟨1375175, by rfl⟩ : syracuseStep 1833567 = 2750351) B2750351
theorem B1833595 : Blo 1831617 1833595 := bstep (se 1 (by rfl) ⟨1375196, by rfl⟩ : syracuseStep 1833595 = 2750393) B2750393
theorem B11737811 : Blo 1831617 11737811 := bstep (se 1 (by rfl) ⟨8803358, by rfl⟩ : syracuseStep 11737811 = 17606717) B17606717
theorem B80329589 : Blo 1831617 80329589 := bstep (se 5 (by rfl) ⟨3765449, by rfl⟩ : syracuseStep 80329589 = 7530899) B7530899
theorem B46963637 : Blo 1831617 46963637 := bstep (se 5 (by rfl) ⟨2201420, by rfl⟩ : syracuseStep 46963637 = 4402841) B4402841
theorem B6183863 : Blo 1831617 6183863 := bstep (se 1 (by rfl) ⟨4637897, by rfl⟩ : syracuseStep 6183863 = 9275795) B9275795
theorem B23485463 : Blo 1831617 23485463 := bstep (se 1 (by rfl) ⟨17614097, by rfl⟩ : syracuseStep 23485463 = 35228195) B35228195
theorem B8805455 : Blo 1831617 8805455 := bstep (se 1 (by rfl) ⟨6604091, by rfl⟩ : syracuseStep 8805455 = 13208183) B13208183
theorem B70425773 : Blo 1831617 70425773 := bstep (se 3 (by rfl) ⟨13204832, by rfl⟩ : syracuseStep 70425773 = 26409665) B26409665
theorem B17603831 : Blo 1831617 17603831 := bstep (se 1 (by rfl) ⟨13202873, by rfl⟩ : syracuseStep 17603831 = 26405747) B26405747
theorem B3480823 : Blo 1831617 3480823 := bstep (se 1 (by rfl) ⟨2610617, by rfl⟩ : syracuseStep 3480823 = 5221235) B5221235
theorem B17603983 : Blo 1831617 17603983 := bstep (se 1 (by rfl) ⟨13202987, by rfl⟩ : syracuseStep 17603983 = 26405975) B26405975
theorem B6184457 : Blo 1831617 6184457 := bstep (se 2 (by rfl) ⟨2319171, by rfl⟩ : syracuseStep 6184457 = 4638343) B4638343
theorem B6356519 : Blo 1831617 6356519 := bstep (se 1 (by rfl) ⟨4767389, by rfl⟩ : syracuseStep 6356519 = 9534779) B9534779
theorem B5873249 : Blo 1831617 5873249 := bstep (se 2 (by rfl) ⟨2202468, by rfl⟩ : syracuseStep 5873249 = 4404937) B4404937
theorem B6954781 : Blo 1831617 6954781 := bstep (se 3 (by rfl) ⟨1304021, by rfl⟩ : syracuseStep 6954781 = 2608043) B2608043
theorem B4636511 : Blo 1831617 4636511 := bstep (se 1 (by rfl) ⟨3477383, by rfl⟩ : syracuseStep 4636511 = 6954767) B6954767
theorem B20365465 : Blo 1831617 20365465 := bstep (se 2 (by rfl) ⟨7637049, by rfl⟩ : syracuseStep 20365465 = 15274099) B15274099
theorem B10182827 : Blo 1831617 10182827 := bstep (se 1 (by rfl) ⟨7637120, by rfl⟩ : syracuseStep 10182827 = 15274241) B15274241
theorem B12542161 : Blo 1831617 12542161 := bstep (se 2 (by rfl) ⟨4703310, by rfl⟩ : syracuseStep 12542161 = 9406621) B9406621
theorem B2384219 : Blo 1831617 2384219 := bstep (se 1 (by rfl) ⟨1788164, by rfl⟩ : syracuseStep 2384219 = 3576329) B3576329
theorem B7430575 : Blo 1831617 7430575 := bstep (se 1 (by rfl) ⟨5572931, by rfl⟩ : syracuseStep 7430575 = 11145863) B11145863
theorem B5874095 : Blo 1831617 5874095 := bstep (se 1 (by rfl) ⟨4405571, by rfl⟩ : syracuseStep 5874095 = 8811143) B8811143
theorem B15868385 : Blo 1831617 15868385 := bstep (se 2 (by rfl) ⟨5950644, by rfl⟩ : syracuseStep 15868385 = 11901289) B11901289
theorem B23814661 : Blo 1831617 23814661 := bstep (se 4 (by rfl) ⟨2232624, by rfl⟩ : syracuseStep 23814661 = 4465249) B4465249
theorem B7823891 : Blo 1831617 7823891 := bstep (se 1 (by rfl) ⟨5867918, by rfl⟩ : syracuseStep 7823891 = 11735837) B11735837
theorem B33890845 : Blo 1831617 33890845 := bstep (se 3 (by rfl) ⟨6354533, by rfl⟩ : syracuseStep 33890845 = 12709067) B12709067
theorem B75268709 : Blo 1831617 75268709 := bstep (se 4 (by rfl) ⟨7056441, by rfl⟩ : syracuseStep 75268709 = 14112883) B14112883
theorem B15655639 : Blo 1831617 15655639 := bstep (se 1 (by rfl) ⟨11741729, by rfl⟩ : syracuseStep 15655639 = 23483459) B23483459
theorem B13910777 : Blo 1831617 13910777 := bstep (se 2 (by rfl) ⟨5216541, by rfl⟩ : syracuseStep 13910777 = 10433083) B10433083
theorem B76235579 : Blo 1831617 76235579 := bstep (se 1 (by rfl) ⟨57176684, by rfl⟩ : syracuseStep 76235579 = 114353369) B114353369
theorem B4121423 : Blo 1831617 4121423 := bstep (se 1 (by rfl) ⟨3091067, by rfl⟩ : syracuseStep 4121423 = 6182135) B6182135
theorem B6185807 : Blo 1831617 6185807 := bstep (se 1 (by rfl) ⟨4639355, by rfl⟩ : syracuseStep 6185807 = 9278711) B9278711
theorem B4178843 : Blo 1831617 4178843 := bstep (se 1 (by rfl) ⟨3134132, by rfl⟩ : syracuseStep 4178843 = 6268265) B6268265
theorem B6603715 : Blo 1831617 6603715 := bstep (se 1 (by rfl) ⟨4952786, by rfl⟩ : syracuseStep 6603715 = 9905573) B9905573
theorem B11297731 : Blo 1831617 11297731 := bstep (se 1 (by rfl) ⟨8473298, by rfl⟩ : syracuseStep 11297731 = 16946597) B16946597
theorem B4121639 : Blo 1831617 4121639 := bstep (se 1 (by rfl) ⟨3091229, by rfl⟩ : syracuseStep 4121639 = 6182459) B6182459
theorem B4523131 : Blo 1831617 4523131 := bstep (se 1 (by rfl) ⟨3392348, by rfl⟩ : syracuseStep 4523131 = 6784697) B6784697
theorem B6186131 : Blo 1831617 6186131 := bstep (se 1 (by rfl) ⟨4639598, by rfl⟩ : syracuseStep 6186131 = 9279197) B9279197
theorem B4121819 : Blo 1831617 4121819 := bstep (se 1 (by rfl) ⟨3091364, by rfl⟩ : syracuseStep 4121819 = 6182729) B6182729
theorem B8807723 : Blo 1831617 8807723 := bstep (se 1 (by rfl) ⟨6605792, by rfl⟩ : syracuseStep 8807723 = 13211585) B13211585
theorem B4122017 : Blo 1831617 4122017 := bstep (se 2 (by rfl) ⟨1545756, by rfl⟩ : syracuseStep 4122017 = 3091513) B3091513
theorem B6186401 : Blo 1831617 6186401 := bstep (se 2 (by rfl) ⟨2319900, by rfl⟩ : syracuseStep 6186401 = 4639801) B4639801
theorem B4638505 : Blo 1831617 4638505 := bstep (se 2 (by rfl) ⟨1739439, by rfl⟩ : syracuseStep 4638505 = 3478879) B3478879
theorem B4704041 : Blo 1831617 4704041 := bstep (se 2 (by rfl) ⟨1764015, by rfl⟩ : syracuseStep 4704041 = 3528031) B3528031
theorem B7825207 : Blo 1831617 7825207 := bstep (se 1 (by rfl) ⟨5868905, by rfl⟩ : syracuseStep 7825207 = 11737811) B11737811
theorem B16713539 : Blo 1831617 16713539 := bstep (se 1 (by rfl) ⟨12535154, by rfl⟩ : syracuseStep 16713539 = 25070309) B25070309
theorem B23471977 : Blo 1831617 23471977 := bstep (se 2 (by rfl) ⟨8801991, by rfl⟩ : syracuseStep 23471977 = 17603983) B17603983
theorem B23496581 : Blo 1831617 23496581 := bstep (se 4 (by rfl) ⟨2202804, by rfl⟩ : syracuseStep 23496581 = 4405609) B4405609
theorem B53553059 : Blo 1831617 53553059 := bstep (se 1 (by rfl) ⟨40164794, by rfl⟩ : syracuseStep 53553059 = 80329589) B80329589
theorem B4122575 : Blo 1831617 4122575 := bstep (se 1 (by rfl) ⟨3091931, by rfl⟩ : syracuseStep 4122575 = 6183863) B6183863
theorem B15656975 : Blo 1831617 15656975 := bstep (se 1 (by rfl) ⟨11742731, by rfl⟩ : syracuseStep 15656975 = 23485463) B23485463
theorem B9275471 : Blo 1831617 9275471 := bstep (se 1 (by rfl) ⟨6956603, by rfl⟩ : syracuseStep 9275471 = 13913207) B13913207
theorem B46950515 : Blo 1831617 46950515 := bstep (se 1 (by rfl) ⟨35212886, by rfl⟩ : syracuseStep 46950515 = 70425773) B70425773
theorem B8358083 : Blo 1831617 8358083 := bstep (se 1 (by rfl) ⟨6268562, by rfl⟩ : syracuseStep 8358083 = 12537125) B12537125
theorem B11143433 : Blo 1831617 11143433 := bstep (se 2 (by rfl) ⟨4178787, by rfl⟩ : syracuseStep 11143433 = 8357575) B8357575
theorem B4122953 : Blo 1831617 4122953 := bstep (se 2 (by rfl) ⟨1546107, by rfl⟩ : syracuseStep 4122953 = 3092215) B3092215
theorem B4122971 : Blo 1831617 4122971 := bstep (se 1 (by rfl) ⟨3092228, by rfl⟩ : syracuseStep 4122971 = 6184457) B6184457
theorem B4237679 : Blo 1831617 4237679 := bstep (se 1 (by rfl) ⟨3178259, by rfl⟩ : syracuseStep 4237679 = 6356519) B6356519
theorem B90360197 : Blo 1831617 90360197 := bstep (se 4 (by rfl) ⟨8471268, by rfl⟩ : syracuseStep 90360197 = 16942537) B16942537
theorem B3091007 : Blo 1831617 3091007 := bstep (se 1 (by rfl) ⟨2318255, by rfl⟩ : syracuseStep 3091007 = 4636511) B4636511
theorem B4639295 : Blo 1831617 4639295 := bstep (se 1 (by rfl) ⟨3479471, by rfl⟩ : syracuseStep 4639295 = 6958943) B6958943
theorem B4123547 : Blo 1831617 4123547 := bstep (se 1 (by rfl) ⟨3092660, by rfl⟩ : syracuseStep 4123547 = 6185321) B6185321
theorem B4402151 : Blo 1831617 4402151 := bstep (se 1 (by rfl) ⟨3301613, by rfl⟩ : syracuseStep 4402151 = 6603227) B6603227
theorem B7433203 : Blo 1831617 7433203 := bstep (se 1 (by rfl) ⟨5574902, by rfl⟩ : syracuseStep 7433203 = 11149805) B11149805
theorem B14855183 : Blo 1831617 14855183 := bstep (se 1 (by rfl) ⟨11141387, by rfl⟩ : syracuseStep 14855183 = 22282775) B22282775
theorem B4123745 : Blo 1831617 4123745 := bstep (se 2 (by rfl) ⟨1546404, by rfl⟩ : syracuseStep 4123745 = 3092809) B3092809
theorem B9276605 : Blo 1831617 9276605 := bstep (se 3 (by rfl) ⟨1739363, by rfl⟩ : syracuseStep 9276605 = 3478727) B3478727
theorem B4639943 : Blo 1831617 4639943 := bstep (se 1 (by rfl) ⟨3479957, by rfl⟩ : syracuseStep 4639943 = 6959915) B6959915
theorem B3091675 : Blo 1831617 3091675 := bstep (se 1 (by rfl) ⟨2318756, by rfl⟩ : syracuseStep 3091675 = 4637513) B4637513
theorem B4639963 : Blo 1831617 4639963 := bstep (se 1 (by rfl) ⟨3479972, by rfl⟩ : syracuseStep 4639963 = 6959945) B6959945
theorem B2747687 : Blo 1831617 2747687 := bstep (se 1 (by rfl) ⟨2060765, by rfl⟩ : syracuseStep 2747687 = 4121531) B4121531
theorem B4123943 : Blo 1831617 4123943 := bstep (se 1 (by rfl) ⟨3092957, by rfl⟩ : syracuseStep 4123943 = 6185915) B6185915
theorem B2747771 : Blo 1831617 2747771 := bstep (se 1 (by rfl) ⟨2060828, by rfl⟩ : syracuseStep 2747771 = 4121657) B4121657
theorem B2747897 : Blo 1831617 2747897 := bstep (se 2 (by rfl) ⟨1030461, by rfl⟩ : syracuseStep 2747897 = 2060923) B2060923
theorem B2747999 : Blo 1831617 2747999 := bstep (se 1 (by rfl) ⟨2060999, by rfl⟩ : syracuseStep 2747999 = 4121999) B4121999
theorem B2477675 : Blo 1831617 2477675 := bstep (se 1 (by rfl) ⟨1858256, by rfl⟩ : syracuseStep 2477675 = 3716513) B3716513
theorem B4124321 : Blo 1831617 4124321 := bstep (se 2 (by rfl) ⟨1546620, by rfl⟩ : syracuseStep 4124321 = 3093241) B3093241
theorem B13921955 : Blo 1831617 13921955 := bstep (se 1 (by rfl) ⟨10441466, by rfl⟩ : syracuseStep 13921955 = 20882933) B20882933
theorem B8359687 : Blo 1831617 8359687 := bstep (se 1 (by rfl) ⟨6269765, by rfl⟩ : syracuseStep 8359687 = 12539531) B12539531
theorem B2748215 : Blo 1831617 2748215 := bstep (se 1 (by rfl) ⟨2061161, by rfl⟩ : syracuseStep 2748215 = 4122323) B4122323
theorem B3092431 : Blo 1831617 3092431 := bstep (se 1 (by rfl) ⟨2319323, by rfl⟩ : syracuseStep 3092431 = 4638647) B4638647
theorem B4124681 : Blo 1831617 4124681 := bstep (se 2 (by rfl) ⟨1546755, by rfl⟩ : syracuseStep 4124681 = 3093511) B3093511
theorem B13914179 : Blo 1831617 13914179 := bstep (se 1 (by rfl) ⟨10435634, by rfl⟩ : syracuseStep 13914179 = 20871269) B20871269
theorem B2748521 : Blo 1831617 2748521 := bstep (se 2 (by rfl) ⟨1030695, by rfl⟩ : syracuseStep 2748521 = 2061391) B2061391
theorem B4641097 : Blo 1831617 4641097 := bstep (se 2 (by rfl) ⟨1740411, by rfl⟩ : syracuseStep 4641097 = 3480823) B3480823
theorem B2060635 : Blo 1831617 2060635 := bstep (se 1 (by rfl) ⟨1545476, by rfl⟩ : syracuseStep 2060635 = 3090953) B3090953
theorem B2748839 : Blo 1831617 2748839 := bstep (se 1 (by rfl) ⟨2061629, by rfl⟩ : syracuseStep 2748839 = 4123259) B4123259
theorem B4125095 : Blo 1831617 4125095 := bstep (se 1 (by rfl) ⟨3093821, by rfl⟩ : syracuseStep 4125095 = 6187643) B6187643
theorem B2060743 : Blo 1831617 2060743 := bstep (se 1 (by rfl) ⟨1545557, by rfl⟩ : syracuseStep 2060743 = 3091115) B3091115
theorem B2748923 : Blo 1831617 2748923 := bstep (se 1 (by rfl) ⟨2061692, by rfl⟩ : syracuseStep 2748923 = 4123385) B4123385
theorem B4125203 : Blo 1831617 4125203 := bstep (se 1 (by rfl) ⟨3093902, by rfl⟩ : syracuseStep 4125203 = 6187805) B6187805
theorem B15872561 : Blo 1831617 15872561 := bstep (se 2 (by rfl) ⟨5952210, by rfl⟩ : syracuseStep 15872561 = 11904421) B11904421
theorem B4125257 : Blo 1831617 4125257 := bstep (se 2 (by rfl) ⟨1546971, by rfl⟩ : syracuseStep 4125257 = 3093943) B3093943
theorem B2749049 : Blo 1831617 2749049 := bstep (se 2 (by rfl) ⟨1030893, by rfl⟩ : syracuseStep 2749049 = 2061787) B2061787
theorem B3093113 : Blo 1831617 3093113 := bstep (se 2 (by rfl) ⟨1159917, by rfl⟩ : syracuseStep 3093113 = 2319835) B2319835
theorem B2749103 : Blo 1831617 2749103 := bstep (se 1 (by rfl) ⟨2061827, by rfl⟩ : syracuseStep 2749103 = 4123655) B4123655
theorem B3093167 : Blo 1831617 3093167 := bstep (se 1 (by rfl) ⟨2319875, by rfl⟩ : syracuseStep 3093167 = 4639751) B4639751
theorem B1831647 : Blo 1831617 1831647 := bstep (se 1 (by rfl) ⟨1373735, by rfl⟩ : syracuseStep 1831647 = 2747471) B2747471
theorem B5870303 : Blo 1831617 5870303 := bstep (se 1 (by rfl) ⟨4402727, by rfl⟩ : syracuseStep 5870303 = 8805455) B8805455
theorem B2749151 : Blo 1831617 2749151 := bstep (se 1 (by rfl) ⟨2061863, by rfl⟩ : syracuseStep 2749151 = 4123727) B4123727
theorem B3715807 : Blo 1831617 3715807 := bstep (se 1 (by rfl) ⟨2786855, by rfl⟩ : syracuseStep 3715807 = 5573711) B5573711
theorem B1831727 : Blo 1831617 1831727 := bstep (se 1 (by rfl) ⟨1373795, by rfl⟩ : syracuseStep 1831727 = 2747591) B2747591
theorem B2061103 : Blo 1831617 2061103 := bstep (se 1 (by rfl) ⟨1545827, by rfl⟩ : syracuseStep 2061103 = 3091655) B3091655
theorem B11735887 : Blo 1831617 11735887 := bstep (se 1 (by rfl) ⟨8801915, by rfl⟩ : syracuseStep 11735887 = 17603831) B17603831
theorem B1831835 : Blo 1831617 1831835 := bstep (se 1 (by rfl) ⟨1373876, by rfl⟩ : syracuseStep 1831835 = 2747753) B2747753
theorem B2061211 : Blo 1831617 2061211 := bstep (se 1 (by rfl) ⟨1545908, by rfl⟩ : syracuseStep 2061211 = 3091817) B3091817
theorem B3093403 : Blo 1831617 3093403 := bstep (se 1 (by rfl) ⟨2320052, by rfl⟩ : syracuseStep 3093403 = 4640105) B4640105
theorem B1831887 : Blo 1831617 1831887 := bstep (se 1 (by rfl) ⟨1373915, by rfl⟩ : syracuseStep 1831887 = 2747831) B2747831
theorem B1831911 : Blo 1831617 1831911 := bstep (se 1 (by rfl) ⟨1373933, by rfl⟩ : syracuseStep 1831911 = 2747867) B2747867
theorem B2749415 : Blo 1831617 2749415 := bstep (se 1 (by rfl) ⟨2062061, by rfl⟩ : syracuseStep 2749415 = 4124123) B4124123
theorem B2749673 : Blo 1831617 2749673 := bstep (se 2 (by rfl) ⟨1031127, by rfl⟩ : syracuseStep 2749673 = 2062255) B2062255
theorem B3912953 : Blo 1831617 3912953 := bstep (se 2 (by rfl) ⟨1467357, by rfl⟩ : syracuseStep 3912953 = 2934715) B2934715
theorem B1832223 : Blo 1831617 1832223 := bstep (se 1 (by rfl) ⟨1374167, by rfl⟩ : syracuseStep 1832223 = 2748335) B2748335
theorem B2749727 : Blo 1831617 2749727 := bstep (se 1 (by rfl) ⟨2062295, by rfl⟩ : syracuseStep 2749727 = 4124591) B4124591
theorem B2061607 : Blo 1831617 2061607 := bstep (se 1 (by rfl) ⟨1546205, by rfl⟩ : syracuseStep 2061607 = 3092411) B3092411
theorem B1832283 : Blo 1831617 1832283 := bstep (se 1 (by rfl) ⟨1374212, by rfl⟩ : syracuseStep 1832283 = 2748425) B2748425
theorem B1832303 : Blo 1831617 1832303 := bstep (se 1 (by rfl) ⟨1374227, by rfl⟩ : syracuseStep 1832303 = 2748455) B2748455
theorem B2061679 : Blo 1831617 2061679 := bstep (se 1 (by rfl) ⟨1546259, by rfl⟩ : syracuseStep 2061679 = 3092519) B3092519
theorem B3134843 : Blo 1831617 3134843 := bstep (se 1 (by rfl) ⟨2351132, by rfl⟩ : syracuseStep 3134843 = 4702265) B4702265
theorem B17184125 : Blo 1831617 17184125 := bstep (se 3 (by rfl) ⟨3222023, by rfl⟩ : syracuseStep 17184125 = 6444047) B6444047
theorem B8803723 : Blo 1831617 8803723 := bstep (se 1 (by rfl) ⟨6602792, by rfl⟩ : syracuseStep 8803723 = 13205585) B13205585
theorem B1832359 : Blo 1831617 1832359 := bstep (se 1 (by rfl) ⟨1374269, by rfl⟩ : syracuseStep 1832359 = 2748539) B2748539
theorem B2749895 : Blo 1831617 2749895 := bstep (se 1 (by rfl) ⟨2062421, by rfl⟩ : syracuseStep 2749895 = 4124843) B4124843
theorem B1832443 : Blo 1831617 1832443 := bstep (se 1 (by rfl) ⟨1374332, by rfl⟩ : syracuseStep 1832443 = 2748665) B2748665
theorem B114349603 : Blo 1831617 114349603 := bstep (se 1 (by rfl) ⟨85762202, by rfl⟩ : syracuseStep 114349603 = 171524405) B171524405
theorem B1832511 : Blo 1831617 1832511 := bstep (se 1 (by rfl) ⟨1374383, by rfl⟩ : syracuseStep 1832511 = 2748767) B2748767
theorem B1832519 : Blo 1831617 1832519 := bstep (se 1 (by rfl) ⟨1374389, by rfl⟩ : syracuseStep 1832519 = 2748779) B2748779
theorem B2061895 : Blo 1831617 2061895 := bstep (se 1 (by rfl) ⟨1546421, by rfl⟩ : syracuseStep 2061895 = 3092843) B3092843
theorem B4953761 : Blo 1831617 4953761 := bstep (se 2 (by rfl) ⟨1857660, by rfl⟩ : syracuseStep 4953761 = 3715321) B3715321
theorem B1832671 : Blo 1831617 1832671 := bstep (se 1 (by rfl) ⟨1374503, by rfl⟩ : syracuseStep 1832671 = 2749007) B2749007
theorem B2750249 : Blo 1831617 2750249 := bstep (se 2 (by rfl) ⟨1031343, by rfl⟩ : syracuseStep 2750249 = 2062687) B2062687
theorem B1832751 : Blo 1831617 1832751 := bstep (se 1 (by rfl) ⟨1374563, by rfl⟩ : syracuseStep 1832751 = 2749127) B2749127
theorem B2750255 : Blo 1831617 2750255 := bstep (se 1 (by rfl) ⟨2062691, by rfl⟩ : syracuseStep 2750255 = 4125383) B4125383
theorem B10434359 : Blo 1831617 10434359 := bstep (se 1 (by rfl) ⟨7825769, by rfl⟩ : syracuseStep 10434359 = 15651539) B15651539
theorem B1832859 : Blo 1831617 1832859 := bstep (se 1 (by rfl) ⟨1374644, by rfl⟩ : syracuseStep 1832859 = 2749289) B2749289
theorem B1832911 : Blo 1831617 1832911 := bstep (se 1 (by rfl) ⟨1374683, by rfl⟩ : syracuseStep 1832911 = 2749367) B2749367
theorem B1832935 : Blo 1831617 1832935 := bstep (se 1 (by rfl) ⟨1374701, by rfl⟩ : syracuseStep 1832935 = 2749403) B2749403
theorem B6182945 : Blo 1831617 6182945 := bstep (se 2 (by rfl) ⟨2318604, by rfl⟩ : syracuseStep 6182945 = 4637209) B4637209
theorem B9279521 : Blo 1831617 9279521 := bstep (se 2 (by rfl) ⟨3479820, by rfl⟩ : syracuseStep 9279521 = 6959641) B6959641
theorem B9279683 : Blo 1831617 9279683 := bstep (se 1 (by rfl) ⟨6959762, by rfl⟩ : syracuseStep 9279683 = 13919525) B13919525
theorem B1833247 : Blo 1831617 1833247 := bstep (se 1 (by rfl) ⟨1374935, by rfl⟩ : syracuseStep 1833247 = 2749871) B2749871
theorem B1833307 : Blo 1831617 1833307 := bstep (se 1 (by rfl) ⟨1374980, by rfl⟩ : syracuseStep 1833307 = 2749961) B2749961
theorem B1833327 : Blo 1831617 1833327 := bstep (se 1 (by rfl) ⟨1374995, by rfl⟩ : syracuseStep 1833327 = 2749991) B2749991
theorem B13384061 : Blo 1831617 13384061 := bstep (se 3 (by rfl) ⟨2509511, by rfl⟩ : syracuseStep 13384061 = 5019023) B5019023
theorem B1833383 : Blo 1831617 1833383 := bstep (se 1 (by rfl) ⟨1375037, by rfl⟩ : syracuseStep 1833383 = 2750075) B2750075
theorem B2062759 : Blo 1831617 2062759 := bstep (se 1 (by rfl) ⟨1547069, by rfl⟩ : syracuseStep 2062759 = 3094139) B3094139
theorem B10435067 : Blo 1831617 10435067 := bstep (se 1 (by rfl) ⟨7826300, by rfl⟩ : syracuseStep 10435067 = 15652601) B15652601
theorem B1833467 : Blo 1831617 1833467 := bstep (se 1 (by rfl) ⟨1375100, by rfl⟩ : syracuseStep 1833467 = 2750201) B2750201
theorem B1833535 : Blo 1831617 1833535 := bstep (se 1 (by rfl) ⟨1375151, by rfl⟩ : syracuseStep 1833535 = 2750303) B2750303
theorem B1833543 : Blo 1831617 1833543 := bstep (se 1 (by rfl) ⟨1375157, by rfl⟩ : syracuseStep 1833543 = 2750315) B2750315
theorem B3480185 : Blo 1831617 3480185 := bstep (se 2 (by rfl) ⟨1305069, by rfl⟩ : syracuseStep 3480185 = 2610139) B2610139
theorem B3480239 : Blo 1831617 3480239 := bstep (se 1 (by rfl) ⟨2610179, by rfl⟩ : syracuseStep 3480239 = 5220359) B5220359
theorem B3914423 : Blo 1831617 3914423 := bstep (se 1 (by rfl) ⟨2935817, by rfl⟩ : syracuseStep 3914423 = 5871635) B5871635
theorem B6961859 : Blo 1831617 6961859 := bstep (se 1 (by rfl) ⟨5221394, by rfl⟩ : syracuseStep 6961859 = 10442789) B10442789
theorem B5217043 : Blo 1831617 5217043 := bstep (se 1 (by rfl) ⟨3912782, by rfl⟩ : syracuseStep 5217043 = 7825565) B7825565
theorem B15661997 : Blo 1831617 15661997 := bstep (se 3 (by rfl) ⟨2936624, by rfl⟩ : syracuseStep 15661997 = 5873249) B5873249
theorem B8363047 : Blo 1831617 8363047 := bstep (se 1 (by rfl) ⟨6272285, by rfl⟩ : syracuseStep 8363047 = 12544571) B12544571
theorem B5872763 : Blo 1831617 5872763 := bstep (se 1 (by rfl) ⟨4404572, by rfl⟩ : syracuseStep 5872763 = 8809145) B8809145
theorem B40180931 : Blo 1831617 40180931 := bstep (se 1 (by rfl) ⟨30135698, by rfl⟩ : syracuseStep 40180931 = 60271397) B60271397
theorem B31309091 : Blo 1831617 31309091 := bstep (se 1 (by rfl) ⟨23481818, by rfl⟩ : syracuseStep 31309091 = 46963637) B46963637
theorem B4234745 : Blo 1831617 4234745 := bstep (se 2 (by rfl) ⟨1588029, by rfl⟩ : syracuseStep 4234745 = 3176059) B3176059
theorem B9273041 : Blo 1831617 9273041 := bstep (se 2 (by rfl) ⟨3477390, by rfl⟩ : syracuseStep 9273041 = 6954781) B6954781
theorem B2318159 : Blo 1831617 2318159 := bstep (se 1 (by rfl) ⟨1738619, by rfl⟩ : syracuseStep 2318159 = 3477239) B3477239
theorem B2318311 : Blo 1831617 2318311 := bstep (se 1 (by rfl) ⟨1738733, by rfl⟩ : syracuseStep 2318311 = 3477467) B3477467
theorem B3916063 : Blo 1831617 3916063 := bstep (se 1 (by rfl) ⟨2937047, by rfl⟩ : syracuseStep 3916063 = 5874095) B5874095
theorem B9273851 : Blo 1831617 9273851 := bstep (se 1 (by rfl) ⟨6955388, by rfl⟩ : syracuseStep 9273851 = 13910777) B13910777
theorem B50823719 : Blo 1831617 50823719 := bstep (se 1 (by rfl) ⟨38117789, by rfl⟩ : syracuseStep 50823719 = 76235579) B76235579
theorem B2785895 : Blo 1831617 2785895 := bstep (se 1 (by rfl) ⟨2089421, by rfl⟩ : syracuseStep 2785895 = 4178843) B4178843
theorem B31752881 : Blo 1831617 31752881 := bstep (se 2 (by rfl) ⟨11907330, by rfl⟩ : syracuseStep 31752881 = 23814661) B23814661
theorem B45187793 : Blo 1831617 45187793 := bstep (se 2 (by rfl) ⟨16945422, by rfl⟩ : syracuseStep 45187793 = 33890845) B33890845
theorem B6357917 : Blo 1831617 6357917 := bstep (se 3 (by rfl) ⟨1192109, by rfl⟩ : syracuseStep 6357917 = 2384219) B2384219
theorem B2089895 : Blo 1831617 2089895 := bstep (se 1 (by rfl) ⟨1567421, by rfl⟩ : syracuseStep 2089895 = 3134843) B3134843
theorem B20874185 : Blo 1831617 20874185 := bstep (se 2 (by rfl) ⟨7827819, by rfl⟩ : syracuseStep 20874185 = 15655639) B15655639
theorem B6956057 : Blo 1831617 6956057 := bstep (se 2 (by rfl) ⟨2608521, by rfl⟩ : syracuseStep 6956057 = 5217043) B5217043
theorem B15647849 : Blo 1831617 15647849 := bstep (se 2 (by rfl) ⟨5867943, by rfl⟩ : syracuseStep 15647849 = 11735887) B11735887
theorem B3302507 : Blo 1831617 3302507 := bstep (se 1 (by rfl) ⟨2476880, by rfl⟩ : syracuseStep 3302507 = 4953761) B4953761
theorem B6956239 : Blo 1831617 6956239 := bstep (se 1 (by rfl) ⟨5217179, by rfl⟩ : syracuseStep 6956239 = 10434359) B10434359
theorem B11142359 : Blo 1831617 11142359 := bstep (se 1 (by rfl) ⟨8356769, by rfl⟩ : syracuseStep 11142359 = 16713539) B16713539
theorem B15664387 : Blo 1831617 15664387 := bstep (se 1 (by rfl) ⟨11748290, by rfl⟩ : syracuseStep 15664387 = 23496581) B23496581
theorem B35702039 : Blo 1831617 35702039 := bstep (se 1 (by rfl) ⟨26776529, by rfl⟩ : syracuseStep 35702039 = 53553059) B53553059
theorem B10437983 : Blo 1831617 10437983 := bstep (se 1 (by rfl) ⟨7828487, by rfl⟩ : syracuseStep 10437983 = 15656975) B15656975
theorem B4121963 : Blo 1831617 4121963 := bstep (se 1 (by rfl) ⟨3091472, by rfl⟩ : syracuseStep 4121963 = 6182945) B6182945
theorem B6186347 : Blo 1831617 6186347 := bstep (se 1 (by rfl) ⟨4639760, by rfl⟩ : syracuseStep 6186347 = 9279521) B9279521
theorem B11150729 : Blo 1831617 11150729 := bstep (se 2 (by rfl) ⟨4181523, by rfl⟩ : syracuseStep 11150729 = 8363047) B8363047
theorem B5572055 : Blo 1831617 5572055 := bstep (se 1 (by rfl) ⟨4179041, by rfl⟩ : syracuseStep 5572055 = 8358083) B8358083
theorem B6186455 : Blo 1831617 6186455 := bstep (se 1 (by rfl) ⟨4639841, by rfl⟩ : syracuseStep 6186455 = 9279683) B9279683
theorem B6030841 : Blo 1831617 6030841 := bstep (se 2 (by rfl) ⟨2261565, by rfl⟩ : syracuseStep 6030841 = 4523131) B4523131
theorem B8922707 : Blo 1831617 8922707 := bstep (se 1 (by rfl) ⟨6692030, by rfl⟩ : syracuseStep 8922707 = 13384061) B13384061
theorem B4122233 : Blo 1831617 4122233 := bstep (se 2 (by rfl) ⟨1545837, by rfl⟩ : syracuseStep 4122233 = 3091675) B3091675
theorem B6186617 : Blo 1831617 6186617 := bstep (se 2 (by rfl) ⟨2319981, by rfl⟩ : syracuseStep 6186617 = 4639963) B4639963
theorem B6956711 : Blo 1831617 6956711 := bstep (se 1 (by rfl) ⟨5217533, by rfl⟩ : syracuseStep 6956711 = 10435067) B10435067
theorem B2320159 : Blo 1831617 2320159 := bstep (se 1 (by rfl) ⟨1740119, by rfl⟩ : syracuseStep 2320159 = 3480239) B3480239
theorem B2934767 : Blo 1831617 2934767 := bstep (se 1 (by rfl) ⟨2201075, by rfl⟩ : syracuseStep 2934767 = 4402151) B4402151
theorem B12544109 : Blo 1831617 12544109 := bstep (se 3 (by rfl) ⟨2352020, by rfl⟩ : syracuseStep 12544109 = 4704041) B4704041
theorem B31295969 : Blo 1831617 31295969 := bstep (se 2 (by rfl) ⟨11735988, by rfl⟩ : syracuseStep 31295969 = 23471977) B23471977
theorem B4123241 : Blo 1831617 4123241 := bstep (se 2 (by rfl) ⟨1546215, by rfl⟩ : syracuseStep 4123241 = 3092431) B3092431
theorem B3091081 : Blo 1831617 3091081 := bstep (se 2 (by rfl) ⟨1159155, by rfl⟩ : syracuseStep 3091081 = 2318311) B2318311
theorem B9276119 : Blo 1831617 9276119 := bstep (se 1 (by rfl) ⟨6957089, by rfl⟩ : syracuseStep 9276119 = 13914179) B13914179
theorem B16722881 : Blo 1831617 16722881 := bstep (se 2 (by rfl) ⟨6271080, by rfl⟩ : syracuseStep 16722881 = 12542161) B12542161
theorem B10578923 : Blo 1831617 10578923 := bstep (se 1 (by rfl) ⟨7934192, by rfl⟩ : syracuseStep 10578923 = 15868385) B15868385
theorem B50179139 : Blo 1831617 50179139 := bstep (se 1 (by rfl) ⟨37634354, by rfl⟩ : syracuseStep 50179139 = 75268709) B75268709
theorem B6188129 : Blo 1831617 6188129 := bstep (se 2 (by rfl) ⟨2320548, by rfl⟩ : syracuseStep 6188129 = 4641097) B4641097
theorem B2747513 : Blo 1831617 2747513 := bstep (se 2 (by rfl) ⟨1030317, by rfl⟩ : syracuseStep 2747513 = 2060635) B2060635
theorem B2747615 : Blo 1831617 2747615 := bstep (se 1 (by rfl) ⟨2060711, by rfl⟩ : syracuseStep 2747615 = 4121423) B4121423
theorem B4123871 : Blo 1831617 4123871 := bstep (se 1 (by rfl) ⟨3092903, by rfl⟩ : syracuseStep 4123871 = 6185807) B6185807
theorem B9907433 : Blo 1831617 9907433 := bstep (se 2 (by rfl) ⟨3715287, by rfl⟩ : syracuseStep 9907433 = 7430575) B7430575
theorem B2747657 : Blo 1831617 2747657 := bstep (se 2 (by rfl) ⟨1030371, by rfl⟩ : syracuseStep 2747657 = 2060743) B2060743
theorem B2747759 : Blo 1831617 2747759 := bstep (se 1 (by rfl) ⟨2060819, by rfl⟩ : syracuseStep 2747759 = 4121639) B4121639
theorem B4124087 : Blo 1831617 4124087 := bstep (se 1 (by rfl) ⟨3093065, by rfl⟩ : syracuseStep 4124087 = 6186131) B6186131
theorem B2747879 : Blo 1831617 2747879 := bstep (se 1 (by rfl) ⟨2060909, by rfl⟩ : syracuseStep 2747879 = 4121819) B4121819
theorem B11456083 : Blo 1831617 11456083 := bstep (se 1 (by rfl) ⟨8592062, by rfl⟩ : syracuseStep 11456083 = 17184125) B17184125
theorem B2748011 : Blo 1831617 2748011 := bstep (se 1 (by rfl) ⟨2061008, by rfl⟩ : syracuseStep 2748011 = 4122017) B4122017
theorem B4124267 : Blo 1831617 4124267 := bstep (se 1 (by rfl) ⟨3093200, by rfl⟩ : syracuseStep 4124267 = 6186401) B6186401
theorem B2748137 : Blo 1831617 2748137 := bstep (se 2 (by rfl) ⟨1030551, by rfl⟩ : syracuseStep 2748137 = 2061103) B2061103
theorem B2748281 : Blo 1831617 2748281 := bstep (se 2 (by rfl) ⟨1030605, by rfl⟩ : syracuseStep 2748281 = 2061211) B2061211
theorem B4124537 : Blo 1831617 4124537 := bstep (se 2 (by rfl) ⟨1546701, by rfl⟩ : syracuseStep 4124537 = 3093403) B3093403
theorem B2748383 : Blo 1831617 2748383 := bstep (se 1 (by rfl) ⟨2061287, by rfl⟩ : syracuseStep 2748383 = 4122575) B4122575
theorem B2748635 : Blo 1831617 2748635 := bstep (se 1 (by rfl) ⟨2061476, by rfl⟩ : syracuseStep 2748635 = 4122953) B4122953
theorem B2748647 : Blo 1831617 2748647 := bstep (se 1 (by rfl) ⟨2061485, by rfl⟩ : syracuseStep 2748647 = 4122971) B4122971
theorem B60240131 : Blo 1831617 60240131 := bstep (se 1 (by rfl) ⟨45180098, by rfl⟩ : syracuseStep 60240131 = 90360197) B90360197
theorem B6607133 : Blo 1831617 6607133 := bstep (se 3 (by rfl) ⟨1238837, by rfl⟩ : syracuseStep 6607133 = 2477675) B2477675
theorem B2060671 : Blo 1831617 2060671 := bstep (se 1 (by rfl) ⟨1545503, by rfl⟩ : syracuseStep 2060671 = 3091007) B3091007
theorem B3092863 : Blo 1831617 3092863 := bstep (se 1 (by rfl) ⟨2319647, by rfl⟩ : syracuseStep 3092863 = 4639295) B4639295
theorem B2748809 : Blo 1831617 2748809 := bstep (se 2 (by rfl) ⟨1030803, by rfl⟩ : syracuseStep 2748809 = 2061607) B2061607
theorem B2609615 : Blo 1831617 2609615 := bstep (se 1 (by rfl) ⟨1957211, by rfl⟩ : syracuseStep 2609615 = 3914423) B3914423
theorem B4641239 : Blo 1831617 4641239 := bstep (se 1 (by rfl) ⟨3480929, by rfl⟩ : syracuseStep 4641239 = 6961859) B6961859
theorem B2748905 : Blo 1831617 2748905 := bstep (se 2 (by rfl) ⟨1030839, by rfl⟩ : syracuseStep 2748905 = 2061679) B2061679
theorem B2749031 : Blo 1831617 2749031 := bstep (se 1 (by rfl) ⟨2061773, by rfl⟩ : syracuseStep 2749031 = 4123547) B4123547
theorem B10441331 : Blo 1831617 10441331 := bstep (se 1 (by rfl) ⟨7830998, by rfl⟩ : syracuseStep 10441331 = 15661997) B15661997
theorem B152466137 : Blo 1831617 152466137 := bstep (se 2 (by rfl) ⟨57174801, by rfl⟩ : syracuseStep 152466137 = 114349603) B114349603
theorem B2749163 : Blo 1831617 2749163 := bstep (se 1 (by rfl) ⟨2061872, by rfl⟩ : syracuseStep 2749163 = 4123745) B4123745
theorem B2749193 : Blo 1831617 2749193 := bstep (se 2 (by rfl) ⟨1030947, by rfl⟩ : syracuseStep 2749193 = 2061895) B2061895
theorem B3093295 : Blo 1831617 3093295 := bstep (se 1 (by rfl) ⟨2319971, by rfl⟩ : syracuseStep 3093295 = 4639943) B4639943
theorem B1831791 : Blo 1831617 1831791 := bstep (se 1 (by rfl) ⟨1373843, by rfl⟩ : syracuseStep 1831791 = 2747687) B2747687
theorem B2749295 : Blo 1831617 2749295 := bstep (se 1 (by rfl) ⟨2061971, by rfl⟩ : syracuseStep 2749295 = 4123943) B4123943
theorem B6181757 : Blo 1831617 6181757 := bstep (se 3 (by rfl) ⟨1159079, by rfl⟩ : syracuseStep 6181757 = 2318159) B2318159
theorem B1831847 : Blo 1831617 1831847 := bstep (se 1 (by rfl) ⟨1373885, by rfl⟩ : syracuseStep 1831847 = 2747771) B2747771
theorem B2823163 : Blo 1831617 2823163 := bstep (se 1 (by rfl) ⟨2117372, by rfl⟩ : syracuseStep 2823163 = 4234745) B4234745
theorem B1831931 : Blo 1831617 1831931 := bstep (se 1 (by rfl) ⟨1373948, by rfl⟩ : syracuseStep 1831931 = 2747897) B2747897
theorem B11146249 : Blo 1831617 11146249 := bstep (se 2 (by rfl) ⟨4179843, by rfl⟩ : syracuseStep 11146249 = 8359687) B8359687
theorem B1831999 : Blo 1831617 1831999 := bstep (se 1 (by rfl) ⟨1373999, by rfl⟩ : syracuseStep 1831999 = 2747999) B2747999
theorem B10433609 : Blo 1831617 10433609 := bstep (se 2 (by rfl) ⟨3912603, by rfl⟩ : syracuseStep 10433609 = 7825207) B7825207
theorem B2749547 : Blo 1831617 2749547 := bstep (se 1 (by rfl) ⟨2062160, by rfl⟩ : syracuseStep 2749547 = 4124321) B4124321
theorem B6182027 : Blo 1831617 6182027 := bstep (se 1 (by rfl) ⟨4636520, by rfl⟩ : syracuseStep 6182027 = 9273041) B9273041
theorem B1832143 : Blo 1831617 1832143 := bstep (se 1 (by rfl) ⟨1374107, by rfl⟩ : syracuseStep 1832143 = 2748215) B2748215
theorem B2749787 : Blo 1831617 2749787 := bstep (se 1 (by rfl) ⟨2062340, by rfl⟩ : syracuseStep 2749787 = 4124681) B4124681
theorem B1832347 : Blo 1831617 1832347 := bstep (se 1 (by rfl) ⟨1374260, by rfl⟩ : syracuseStep 1832347 = 2748521) B2748521
theorem B6788551 : Blo 1831617 6788551 := bstep (se 1 (by rfl) ⟨5091413, by rfl⟩ : syracuseStep 6788551 = 10182827) B10182827
theorem B27153953 : Blo 1831617 27153953 := bstep (se 2 (by rfl) ⟨10182732, by rfl⟩ : syracuseStep 27153953 = 20365465) B20365465
theorem B1832559 : Blo 1831617 1832559 := bstep (se 1 (by rfl) ⟨1374419, by rfl⟩ : syracuseStep 1832559 = 2748839) B2748839
theorem B2750063 : Blo 1831617 2750063 := bstep (se 1 (by rfl) ⟨2062547, by rfl⟩ : syracuseStep 2750063 = 4125095) B4125095
theorem B1832615 : Blo 1831617 1832615 := bstep (se 1 (by rfl) ⟨1374461, by rfl⟩ : syracuseStep 1832615 = 2748923) B2748923
theorem B5215927 : Blo 1831617 5215927 := bstep (se 1 (by rfl) ⟨3911945, by rfl⟩ : syracuseStep 5215927 = 7823891) B7823891
theorem B2750135 : Blo 1831617 2750135 := bstep (se 1 (by rfl) ⟨2062601, by rfl⟩ : syracuseStep 2750135 = 4125203) B4125203
theorem B10581707 : Blo 1831617 10581707 := bstep (se 1 (by rfl) ⟨7936280, by rfl⟩ : syracuseStep 10581707 = 15872561) B15872561
theorem B2750171 : Blo 1831617 2750171 := bstep (se 1 (by rfl) ⟨2062628, by rfl⟩ : syracuseStep 2750171 = 4125257) B4125257
theorem B1832699 : Blo 1831617 1832699 := bstep (se 1 (by rfl) ⟨1374524, by rfl⟩ : syracuseStep 1832699 = 2749049) B2749049
theorem B2062075 : Blo 1831617 2062075 := bstep (se 1 (by rfl) ⟨1546556, by rfl⟩ : syracuseStep 2062075 = 3093113) B3093113
theorem B1832735 : Blo 1831617 1832735 := bstep (se 1 (by rfl) ⟨1374551, by rfl⟩ : syracuseStep 1832735 = 2749103) B2749103
theorem B2062111 : Blo 1831617 2062111 := bstep (se 1 (by rfl) ⟨1546583, by rfl⟩ : syracuseStep 2062111 = 3093167) B3093167
theorem B3913535 : Blo 1831617 3913535 := bstep (se 1 (by rfl) ⟨2935151, by rfl⟩ : syracuseStep 3913535 = 5870303) B5870303
theorem B1832767 : Blo 1831617 1832767 := bstep (se 1 (by rfl) ⟨1374575, by rfl⟩ : syracuseStep 1832767 = 2749151) B2749151
theorem B2750345 : Blo 1831617 2750345 := bstep (se 2 (by rfl) ⟨1031379, by rfl⟩ : syracuseStep 2750345 = 2062759) B2062759
theorem B10434541 : Blo 1831617 10434541 := bstep (se 3 (by rfl) ⟨1956476, by rfl⟩ : syracuseStep 10434541 = 3912953) B3912953
theorem B1832943 : Blo 1831617 1832943 := bstep (se 1 (by rfl) ⟨1374707, by rfl⟩ : syracuseStep 1832943 = 2749415) B2749415
theorem B1833115 : Blo 1831617 1833115 := bstep (se 1 (by rfl) ⟨1374836, by rfl⟩ : syracuseStep 1833115 = 2749673) B2749673
theorem B1833151 : Blo 1831617 1833151 := bstep (se 1 (by rfl) ⟨1374863, by rfl⟩ : syracuseStep 1833151 = 2749727) B2749727
theorem B5871815 : Blo 1831617 5871815 := bstep (se 1 (by rfl) ⟨4403861, by rfl⟩ : syracuseStep 5871815 = 8807723) B8807723
theorem B4954409 : Blo 1831617 4954409 := bstep (se 2 (by rfl) ⟨1857903, by rfl⟩ : syracuseStep 4954409 = 3715807) B3715807
theorem B1833263 : Blo 1831617 1833263 := bstep (se 1 (by rfl) ⟨1374947, by rfl⟩ : syracuseStep 1833263 = 2749895) B2749895
theorem B1833499 : Blo 1831617 1833499 := bstep (se 1 (by rfl) ⟨1375124, by rfl⟩ : syracuseStep 1833499 = 2750249) B2750249
theorem B1833503 : Blo 1831617 1833503 := bstep (se 1 (by rfl) ⟨1375127, by rfl⟩ : syracuseStep 1833503 = 2750255) B2750255
theorem B8804953 : Blo 1831617 8804953 := bstep (se 2 (by rfl) ⟨3301857, by rfl⟩ : syracuseStep 8804953 = 6603715) B6603715
theorem B15063641 : Blo 1831617 15063641 := bstep (se 2 (by rfl) ⟨5648865, by rfl⟩ : syracuseStep 15063641 = 11297731) B11297731
theorem B9910937 : Blo 1831617 9910937 := bstep (se 2 (by rfl) ⟨3716601, by rfl⟩ : syracuseStep 9910937 = 7433203) B7433203
theorem B6183647 : Blo 1831617 6183647 := bstep (se 1 (by rfl) ⟨4637735, by rfl⟩ : syracuseStep 6183647 = 9275471) B9275471
theorem B31300343 : Blo 1831617 31300343 := bstep (se 1 (by rfl) ⟨23475257, by rfl⟩ : syracuseStep 31300343 = 46950515) B46950515
theorem B7428955 : Blo 1831617 7428955 := bstep (se 1 (by rfl) ⟨5571716, by rfl⟩ : syracuseStep 7428955 = 11143433) B11143433
theorem B2825119 : Blo 1831617 2825119 := bstep (se 1 (by rfl) ⟨2118839, by rfl⟩ : syracuseStep 2825119 = 4237679) B4237679
theorem B9280493 : Blo 1831617 9280493 := bstep (se 3 (by rfl) ⟨1740092, by rfl⟩ : syracuseStep 9280493 = 3480185) B3480185
theorem B11738297 : Blo 1831617 11738297 := bstep (se 2 (by rfl) ⟨4401861, by rfl⟩ : syracuseStep 11738297 = 8803723) B8803723
theorem B9903455 : Blo 1831617 9903455 := bstep (se 1 (by rfl) ⟨7427591, by rfl⟩ : syracuseStep 9903455 = 14855183) B14855183
theorem B3915175 : Blo 1831617 3915175 := bstep (se 1 (by rfl) ⟨2936381, by rfl⟩ : syracuseStep 3915175 = 5872763) B5872763
theorem B6184403 : Blo 1831617 6184403 := bstep (se 1 (by rfl) ⟨4638302, by rfl⟩ : syracuseStep 6184403 = 9276605) B9276605
theorem B26787287 : Blo 1831617 26787287 := bstep (se 1 (by rfl) ⟨20090465, by rfl⟩ : syracuseStep 26787287 = 40180931) B40180931
theorem B20872727 : Blo 1831617 20872727 := bstep (se 1 (by rfl) ⟨15654545, by rfl⟩ : syracuseStep 20872727 = 31309091) B31309091
theorem B6184673 : Blo 1831617 6184673 := bstep (se 2 (by rfl) ⟨2319252, by rfl⟩ : syracuseStep 6184673 = 4638505) B4638505
theorem B9281303 : Blo 1831617 9281303 := bstep (se 1 (by rfl) ⟨6960977, by rfl⟩ : syracuseStep 9281303 = 13921955) B13921955
theorem B33882479 : Blo 1831617 33882479 := bstep (se 1 (by rfl) ⟨25411859, by rfl⟩ : syracuseStep 33882479 = 50823719) B50823719
theorem B21168587 : Blo 1831617 21168587 := bstep (se 1 (by rfl) ⟨15876440, by rfl⟩ : syracuseStep 21168587 = 31752881) B31752881
theorem B4121171 : Blo 1831617 4121171 := bstep (se 1 (by rfl) ⟨3090878, by rfl⟩ : syracuseStep 4121171 = 6181757) B6181757
theorem B4637371 : Blo 1831617 4637371 := bstep (se 1 (by rfl) ⟨3478028, by rfl⟩ : syracuseStep 4637371 = 6956057) B6956057
theorem B6955739 : Blo 1831617 6955739 := bstep (se 1 (by rfl) ⟨5216804, by rfl⟩ : syracuseStep 6955739 = 10433609) B10433609
theorem B4121351 : Blo 1831617 4121351 := bstep (se 1 (by rfl) ⟨3091013, by rfl⟩ : syracuseStep 4121351 = 6182027) B6182027
theorem B11739937 : Blo 1831617 11739937 := bstep (se 2 (by rfl) ⟨4402476, by rfl⟩ : syracuseStep 11739937 = 8804953) B8804953
theorem B4121441 : Blo 1831617 4121441 := bstep (se 2 (by rfl) ⟨1545540, by rfl⟩ : syracuseStep 4121441 = 3091081) B3091081
theorem B5948471 : Blo 1831617 5948471 := bstep (se 1 (by rfl) ⟨4461353, by rfl⟩ : syracuseStep 5948471 = 8922707) B8922707
theorem B4637807 : Blo 1831617 4637807 := bstep (se 1 (by rfl) ⟨3478355, by rfl⟩ : syracuseStep 4637807 = 6956711) B6956711
theorem B9905273 : Blo 1831617 9905273 := bstep (se 2 (by rfl) ⟨3714477, by rfl⟩ : syracuseStep 9905273 = 7428955) B7428955
theorem B7054471 : Blo 1831617 7054471 := bstep (se 1 (by rfl) ⟨5290853, by rfl⟩ : syracuseStep 7054471 = 10581707) B10581707
theorem B14861665 : Blo 1831617 14861665 := bstep (se 2 (by rfl) ⟨5573124, by rfl⟩ : syracuseStep 14861665 = 11146249) B11146249
theorem B3302939 : Blo 1831617 3302939 := bstep (se 1 (by rfl) ⟨2477204, by rfl⟩ : syracuseStep 3302939 = 4954409) B4954409
theorem B9274985 : Blo 1831617 9274985 := bstep (se 2 (by rfl) ⟨3478119, by rfl⟩ : syracuseStep 9274985 = 6956239) B6956239
theorem B26429165 : Blo 1831617 26429165 := bstep (se 3 (by rfl) ⟨4955468, by rfl⟩ : syracuseStep 26429165 = 9910937) B9910937
theorem B4122431 : Blo 1831617 4122431 := bstep (se 1 (by rfl) ⟨3091823, by rfl⟩ : syracuseStep 4122431 = 6183647) B6183647
theorem B20866895 : Blo 1831617 20866895 := bstep (se 1 (by rfl) ⟨15650171, by rfl⟩ : syracuseStep 20866895 = 31300343) B31300343
theorem B5220233 : Blo 1831617 5220233 := bstep (se 2 (by rfl) ⟨1957587, by rfl⟩ : syracuseStep 5220233 = 3915175) B3915175
theorem B6186995 : Blo 1831617 6186995 := bstep (se 1 (by rfl) ⟨4640246, by rfl⟩ : syracuseStep 6186995 = 9280493) B9280493
theorem B7825531 : Blo 1831617 7825531 := bstep (se 1 (by rfl) ⟨5869148, by rfl⟩ : syracuseStep 7825531 = 11738297) B11738297
theorem B6604955 : Blo 1831617 6604955 := bstep (se 1 (by rfl) ⟨4953716, by rfl⟩ : syracuseStep 6604955 = 9907433) B9907433
theorem B4122935 : Blo 1831617 4122935 := bstep (se 1 (by rfl) ⟨3092201, by rfl⟩ : syracuseStep 4122935 = 6184403) B6184403
theorem B5573053 : Blo 1831617 5573053 := bstep (se 3 (by rfl) ⟨1044947, by rfl⟩ : syracuseStep 5573053 = 2089895) B2089895
theorem B4123115 : Blo 1831617 4123115 := bstep (se 1 (by rfl) ⟨3092336, by rfl⟩ : syracuseStep 4123115 = 6184673) B6184673
theorem B6187535 : Blo 1831617 6187535 := bstep (se 1 (by rfl) ⟨4640651, by rfl⟩ : syracuseStep 6187535 = 9281303) B9281303
theorem B13912721 : Blo 1831617 13912721 := bstep (se 2 (by rfl) ⟨5217270, by rfl⟩ : syracuseStep 13912721 = 10434541) B10434541
theorem B40160087 : Blo 1831617 40160087 := bstep (se 1 (by rfl) ⟨30120065, by rfl⟩ : syracuseStep 40160087 = 60240131) B60240131
theorem B5221417 : Blo 1831617 5221417 := bstep (se 2 (by rfl) ⟨1958031, by rfl⟩ : syracuseStep 5221417 = 3916063) B3916063
theorem B61099109 : Blo 1831617 61099109 := bstep (se 4 (by rfl) ⟨5728041, by rfl⟩ : syracuseStep 61099109 = 11456083) B11456083
theorem B30125195 : Blo 1831617 30125195 := bstep (se 1 (by rfl) ⟨22593896, by rfl⟩ : syracuseStep 30125195 = 45187793) B45187793
theorem B2747561 : Blo 1831617 2747561 := bstep (se 2 (by rfl) ⟨1030335, by rfl⟩ : syracuseStep 2747561 = 2060671) B2060671
theorem B4123817 : Blo 1831617 4123817 := bstep (se 2 (by rfl) ⟨1546431, by rfl⟩ : syracuseStep 4123817 = 3092863) B3092863
theorem B4238611 : Blo 1831617 4238611 := bstep (se 1 (by rfl) ⟨3178958, by rfl⟩ : syracuseStep 4238611 = 6357917) B6357917
theorem B10431899 : Blo 1831617 10431899 := bstep (se 1 (by rfl) ⟨7823924, by rfl⟩ : syracuseStep 10431899 = 15647849) B15647849
theorem B23801359 : Blo 1831617 23801359 := bstep (se 1 (by rfl) ⟨17851019, by rfl⟩ : syracuseStep 23801359 = 35702039) B35702039
theorem B6958655 : Blo 1831617 6958655 := bstep (se 1 (by rfl) ⟨5218991, by rfl⟩ : syracuseStep 6958655 = 10437983) B10437983
theorem B2747975 : Blo 1831617 2747975 := bstep (se 1 (by rfl) ⟨2060981, by rfl⟩ : syracuseStep 2747975 = 4121963) B4121963
theorem B4124231 : Blo 1831617 4124231 := bstep (se 1 (by rfl) ⟨3093173, by rfl⟩ : syracuseStep 4124231 = 6186347) B6186347
theorem B7433819 : Blo 1831617 7433819 := bstep (se 1 (by rfl) ⟨5575364, by rfl⟩ : syracuseStep 7433819 = 11150729) B11150729
theorem B3714703 : Blo 1831617 3714703 := bstep (se 1 (by rfl) ⟨2786027, by rfl⟩ : syracuseStep 3714703 = 5572055) B5572055
theorem B4124303 : Blo 1831617 4124303 := bstep (se 1 (by rfl) ⟨3093227, by rfl⟩ : syracuseStep 4124303 = 6186455) B6186455
theorem B4124393 : Blo 1831617 4124393 := bstep (se 2 (by rfl) ⟨1546647, by rfl⟩ : syracuseStep 4124393 = 3093295) B3093295
theorem B2748155 : Blo 1831617 2748155 := bstep (se 1 (by rfl) ⟨2061116, by rfl⟩ : syracuseStep 2748155 = 4122233) B4122233
theorem B4124411 : Blo 1831617 4124411 := bstep (se 1 (by rfl) ⟨3093308, by rfl⟩ : syracuseStep 4124411 = 6186617) B6186617
theorem B6958973 : Blo 1831617 6958973 := bstep (se 3 (by rfl) ⟨1304807, by rfl⟩ : syracuseStep 6958973 = 2609615) B2609615
theorem B2609023 : Blo 1831617 2609023 := bstep (se 1 (by rfl) ⟨1956767, by rfl⟩ : syracuseStep 2609023 = 3913535) B3913535
theorem B20885849 : Blo 1831617 20885849 := bstep (se 2 (by rfl) ⟨7832193, by rfl⟩ : syracuseStep 20885849 = 15664387) B15664387
theorem B2748827 : Blo 1831617 2748827 := bstep (se 1 (by rfl) ⟨2061620, by rfl⟩ : syracuseStep 2748827 = 4123241) B4123241
theorem B8041121 : Blo 1831617 8041121 := bstep (se 2 (by rfl) ⟨3015420, by rfl⟩ : syracuseStep 8041121 = 6030841) B6030841
theorem B33452759 : Blo 1831617 33452759 := bstep (se 1 (by rfl) ⟨25089569, by rfl⟩ : syracuseStep 33452759 = 50179139) B50179139
theorem B4125419 : Blo 1831617 4125419 := bstep (se 1 (by rfl) ⟨3094064, by rfl⟩ : syracuseStep 4125419 = 6188129) B6188129
theorem B1831675 : Blo 1831617 1831675 := bstep (se 1 (by rfl) ⟨1373756, by rfl⟩ : syracuseStep 1831675 = 2747513) B2747513
theorem B1831743 : Blo 1831617 1831743 := bstep (se 1 (by rfl) ⟨1373807, by rfl⟩ : syracuseStep 1831743 = 2747615) B2747615
theorem B2749247 : Blo 1831617 2749247 := bstep (se 1 (by rfl) ⟨2061935, by rfl⟩ : syracuseStep 2749247 = 4123871) B4123871
theorem B1831771 : Blo 1831617 1831771 := bstep (se 1 (by rfl) ⟨1373828, by rfl⟩ : syracuseStep 1831771 = 2747657) B2747657
theorem B1831839 : Blo 1831617 1831839 := bstep (se 1 (by rfl) ⟨1373879, by rfl⟩ : syracuseStep 1831839 = 2747759) B2747759
theorem B2749391 : Blo 1831617 2749391 := bstep (se 1 (by rfl) ⟨2062043, by rfl⟩ : syracuseStep 2749391 = 4124087) B4124087
theorem B1831919 : Blo 1831617 1831919 := bstep (se 1 (by rfl) ⟨1373939, by rfl⟩ : syracuseStep 1831919 = 2747879) B2747879
theorem B2749433 : Blo 1831617 2749433 := bstep (se 2 (by rfl) ⟨1031037, by rfl⟩ : syracuseStep 2749433 = 2062075) B2062075
theorem B13915151 : Blo 1831617 13915151 := bstep (se 1 (by rfl) ⟨10436363, by rfl⟩ : syracuseStep 13915151 = 20872727) B20872727
theorem B2749481 : Blo 1831617 2749481 := bstep (se 2 (by rfl) ⟨1031055, by rfl⟩ : syracuseStep 2749481 = 2062111) B2062111
theorem B3093545 : Blo 1831617 3093545 := bstep (se 2 (by rfl) ⟨1160079, by rfl⟩ : syracuseStep 3093545 = 2320159) B2320159
theorem B1832007 : Blo 1831617 1832007 := bstep (se 1 (by rfl) ⟨1374005, by rfl⟩ : syracuseStep 1832007 = 2748011) B2748011
theorem B2749511 : Blo 1831617 2749511 := bstep (se 1 (by rfl) ⟨2062133, by rfl⟩ : syracuseStep 2749511 = 4124267) B4124267
theorem B1832091 : Blo 1831617 1832091 := bstep (se 1 (by rfl) ⟨1374068, by rfl⟩ : syracuseStep 1832091 = 2748137) B2748137
theorem B1832187 : Blo 1831617 1832187 := bstep (se 1 (by rfl) ⟨1374140, by rfl⟩ : syracuseStep 1832187 = 2748281) B2748281
theorem B2749691 : Blo 1831617 2749691 := bstep (se 1 (by rfl) ⟨2062268, by rfl⟩ : syracuseStep 2749691 = 4124537) B4124537
theorem B1832255 : Blo 1831617 1832255 := bstep (se 1 (by rfl) ⟨1374191, by rfl⟩ : syracuseStep 1832255 = 2748383) B2748383
theorem B1832423 : Blo 1831617 1832423 := bstep (se 1 (by rfl) ⟨1374317, by rfl⟩ : syracuseStep 1832423 = 2748635) B2748635
theorem B1832431 : Blo 1831617 1832431 := bstep (se 1 (by rfl) ⟨1374323, by rfl⟩ : syracuseStep 1832431 = 2748647) B2748647
theorem B4404755 : Blo 1831617 4404755 := bstep (se 1 (by rfl) ⟨3303566, by rfl⟩ : syracuseStep 4404755 = 6607133) B6607133
theorem B1832539 : Blo 1831617 1832539 := bstep (se 1 (by rfl) ⟨1374404, by rfl⟩ : syracuseStep 1832539 = 2748809) B2748809
theorem B3094159 : Blo 1831617 3094159 := bstep (se 1 (by rfl) ⟨2320619, by rfl⟩ : syracuseStep 3094159 = 4641239) B4641239
theorem B1832603 : Blo 1831617 1832603 := bstep (se 1 (by rfl) ⟨1374452, by rfl⟩ : syracuseStep 1832603 = 2748905) B2748905
theorem B6182567 : Blo 1831617 6182567 := bstep (se 1 (by rfl) ⟨4636925, by rfl⟩ : syracuseStep 6182567 = 9273851) B9273851
theorem B1857263 : Blo 1831617 1857263 := bstep (se 1 (by rfl) ⟨1392947, by rfl⟩ : syracuseStep 1857263 = 2785895) B2785895
theorem B1832687 : Blo 1831617 1832687 := bstep (se 1 (by rfl) ⟨1374515, by rfl⟩ : syracuseStep 1832687 = 2749031) B2749031
theorem B6960887 : Blo 1831617 6960887 := bstep (se 1 (by rfl) ⟨5220665, by rfl⟩ : syracuseStep 6960887 = 10441331) B10441331
theorem B101644091 : Blo 1831617 101644091 := bstep (se 1 (by rfl) ⟨76233068, by rfl⟩ : syracuseStep 101644091 = 152466137) B152466137
theorem B1832775 : Blo 1831617 1832775 := bstep (se 1 (by rfl) ⟨1374581, by rfl⟩ : syracuseStep 1832775 = 2749163) B2749163
theorem B1832795 : Blo 1831617 1832795 := bstep (se 1 (by rfl) ⟨1374596, by rfl⟩ : syracuseStep 1832795 = 2749193) B2749193
theorem B1832863 : Blo 1831617 1832863 := bstep (se 1 (by rfl) ⟨1374647, by rfl⟩ : syracuseStep 1832863 = 2749295) B2749295
theorem B13916123 : Blo 1831617 13916123 := bstep (se 1 (by rfl) ⟨10437092, by rfl⟩ : syracuseStep 13916123 = 20874185) B20874185
theorem B2201671 : Blo 1831617 2201671 := bstep (se 1 (by rfl) ⟨1651253, by rfl⟩ : syracuseStep 2201671 = 3302507) B3302507
theorem B1833031 : Blo 1831617 1833031 := bstep (se 1 (by rfl) ⟨1374773, by rfl⟩ : syracuseStep 1833031 = 2749547) B2749547
theorem B7428239 : Blo 1831617 7428239 := bstep (se 1 (by rfl) ⟨5571179, by rfl⟩ : syracuseStep 7428239 = 11142359) B11142359
theorem B1833191 : Blo 1831617 1833191 := bstep (se 1 (by rfl) ⟨1374893, by rfl⟩ : syracuseStep 1833191 = 2749787) B2749787
theorem B18102635 : Blo 1831617 18102635 := bstep (se 1 (by rfl) ⟨13576976, by rfl⟩ : syracuseStep 18102635 = 27153953) B27153953
theorem B1833375 : Blo 1831617 1833375 := bstep (se 1 (by rfl) ⟨1375031, by rfl⟩ : syracuseStep 1833375 = 2750063) B2750063
theorem B1833423 : Blo 1831617 1833423 := bstep (se 1 (by rfl) ⟨1375067, by rfl⟩ : syracuseStep 1833423 = 2750135) B2750135
theorem B1833447 : Blo 1831617 1833447 := bstep (se 1 (by rfl) ⟨1375085, by rfl⟩ : syracuseStep 1833447 = 2750171) B2750171
theorem B3766825 : Blo 1831617 3766825 := bstep (se 2 (by rfl) ⟨1412559, by rfl⟩ : syracuseStep 3766825 = 2825119) B2825119
theorem B1833563 : Blo 1831617 1833563 := bstep (se 1 (by rfl) ⟨1375172, by rfl⟩ : syracuseStep 1833563 = 2750345) B2750345
theorem B1956511 : Blo 1831617 1956511 := bstep (se 1 (by rfl) ⟨1467383, by rfl⟩ : syracuseStep 1956511 = 2934767) B2934767
theorem B8362739 : Blo 1831617 8362739 := bstep (se 1 (by rfl) ⟨6272054, by rfl⟩ : syracuseStep 8362739 = 12544109) B12544109
theorem B3914543 : Blo 1831617 3914543 := bstep (se 1 (by rfl) ⟨2935907, by rfl⟩ : syracuseStep 3914543 = 5871815) B5871815
theorem B20863979 : Blo 1831617 20863979 := bstep (se 1 (by rfl) ⟨15647984, by rfl⟩ : syracuseStep 20863979 = 31295969) B31295969
theorem B10042427 : Blo 1831617 10042427 := bstep (se 1 (by rfl) ⟨7531820, by rfl⟩ : syracuseStep 10042427 = 15063641) B15063641
theorem B6184079 : Blo 1831617 6184079 := bstep (se 1 (by rfl) ⟨4638059, by rfl⟩ : syracuseStep 6184079 = 9276119) B9276119
theorem B9051401 : Blo 1831617 9051401 := bstep (se 2 (by rfl) ⟨3394275, by rfl⟩ : syracuseStep 9051401 = 6788551) B6788551
theorem B11148587 : Blo 1831617 11148587 := bstep (se 1 (by rfl) ⟨8361440, by rfl⟩ : syracuseStep 11148587 = 16722881) B16722881
theorem B7052615 : Blo 1831617 7052615 := bstep (se 1 (by rfl) ⟨5289461, by rfl⟩ : syracuseStep 7052615 = 10578923) B10578923
theorem B6602303 : Blo 1831617 6602303 := bstep (se 1 (by rfl) ⟨4951727, by rfl⟩ : syracuseStep 6602303 = 9903455) B9903455
theorem B6954569 : Blo 1831617 6954569 := bstep (se 2 (by rfl) ⟨2607963, by rfl⟩ : syracuseStep 6954569 = 5215927) B5215927
theorem B17858191 : Blo 1831617 17858191 := bstep (se 1 (by rfl) ⟨13393643, by rfl⟩ : syracuseStep 17858191 = 26787287) B26787287
theorem B15056869 : Blo 1831617 15056869 := bstep (se 4 (by rfl) ⟨1411581, by rfl⟩ : syracuseStep 15056869 = 2823163) B2823163
theorem B26779805 : Blo 1831617 26779805 := bstep (se 3 (by rfl) ⟨5021213, by rfl⟩ : syracuseStep 26779805 = 10042427) B10042427
theorem B4637159 : Blo 1831617 4637159 := bstep (se 1 (by rfl) ⟨3477869, by rfl⟩ : syracuseStep 4637159 = 6955739) B6955739
theorem B3965647 : Blo 1831617 3965647 := bstep (se 1 (by rfl) ⟨2974235, by rfl⟩ : syracuseStep 3965647 = 5948471) B5948471
theorem B5022433 : Blo 1831617 5022433 := bstep (se 2 (by rfl) ⟨1883412, by rfl⟩ : syracuseStep 5022433 = 3766825) B3766825
theorem B6603515 : Blo 1831617 6603515 := bstep (se 1 (by rfl) ⟨4952636, by rfl⟩ : syracuseStep 6603515 = 9905273) B9905273
theorem B4121711 : Blo 1831617 4121711 := bstep (se 1 (by rfl) ⟨3091283, by rfl⟩ : syracuseStep 4121711 = 6182567) B6182567
theorem B13911263 : Blo 1831617 13911263 := bstep (se 1 (by rfl) ⟨10433447, by rfl⟩ : syracuseStep 13911263 = 20866895) B20866895
theorem B12068423 : Blo 1831617 12068423 := bstep (se 1 (by rfl) ⟨9051317, by rfl⟩ : syracuseStep 12068423 = 18102635) B18102635
theorem B9275147 : Blo 1831617 9275147 := bstep (se 1 (by rfl) ⟨6956360, by rfl⟩ : syracuseStep 9275147 = 13912721) B13912721
theorem B26773391 : Blo 1831617 26773391 := bstep (se 1 (by rfl) ⟨20080043, by rfl⟩ : syracuseStep 26773391 = 40160087) B40160087
theorem B40732739 : Blo 1831617 40732739 := bstep (se 1 (by rfl) ⟨30549554, by rfl⟩ : syracuseStep 40732739 = 61099109) B61099109
theorem B4122719 : Blo 1831617 4122719 := bstep (se 1 (by rfl) ⟨3092039, by rfl⟩ : syracuseStep 4122719 = 6184079) B6184079
theorem B7432391 : Blo 1831617 7432391 := bstep (se 1 (by rfl) ⟨5574293, by rfl⟩ : syracuseStep 7432391 = 11148587) B11148587
theorem B29722949 : Blo 1831617 29722949 := bstep (se 4 (by rfl) ⟨2786526, by rfl⟩ : syracuseStep 29722949 = 5573053) B5573053
theorem B4401535 : Blo 1831617 4401535 := bstep (se 1 (by rfl) ⟨3301151, by rfl⟩ : syracuseStep 4401535 = 6602303) B6602303
theorem B4639103 : Blo 1831617 4639103 := bstep (se 1 (by rfl) ⟨3479327, by rfl⟩ : syracuseStep 4639103 = 6958655) B6958655
theorem B4639315 : Blo 1831617 4639315 := bstep (se 1 (by rfl) ⟨3479486, by rfl⟩ : syracuseStep 4639315 = 6958973) B6958973
theorem B22588319 : Blo 1831617 22588319 := bstep (se 1 (by rfl) ⟨16941239, by rfl⟩ : syracuseStep 22588319 = 33882479) B33882479
theorem B11742245 : Blo 1831617 11742245 := bstep (se 4 (by rfl) ⟨1100835, by rfl⟩ : syracuseStep 11742245 = 2201671) B2201671
theorem B2747447 : Blo 1831617 2747447 := bstep (se 1 (by rfl) ⟨2060585, by rfl⟩ : syracuseStep 2747447 = 4121171) B4121171
theorem B5360747 : Blo 1831617 5360747 := bstep (se 1 (by rfl) ⟨4020560, by rfl⟩ : syracuseStep 5360747 = 8041121) B8041121
theorem B22301839 : Blo 1831617 22301839 := bstep (se 1 (by rfl) ⟨16726379, by rfl⟩ : syracuseStep 22301839 = 33452759) B33452759
theorem B2747567 : Blo 1831617 2747567 := bstep (se 1 (by rfl) ⟨2060675, by rfl⟩ : syracuseStep 2747567 = 4121351) B4121351
theorem B2747627 : Blo 1831617 2747627 := bstep (se 1 (by rfl) ⟨2060720, by rfl⟩ : syracuseStep 2747627 = 4121441) B4121441
theorem B9276767 : Blo 1831617 9276767 := bstep (se 1 (by rfl) ⟨6957575, by rfl⟩ : syracuseStep 9276767 = 13915151) B13915151
theorem B3091871 : Blo 1831617 3091871 := bstep (se 1 (by rfl) ⟨2318903, by rfl⟩ : syracuseStep 3091871 = 4637807) B4637807
theorem B19811749 : Blo 1831617 19811749 := bstep (se 4 (by rfl) ⟨1857351, by rfl⟩ : syracuseStep 19811749 = 3714703) B3714703
theorem B2608681 : Blo 1831617 2608681 := bstep (se 2 (by rfl) ⟨978255, by rfl⟩ : syracuseStep 2608681 = 1956511) B1956511
theorem B2936503 : Blo 1831617 2936503 := bstep (se 1 (by rfl) ⟨2202377, by rfl⟩ : syracuseStep 2936503 = 4404755) B4404755
theorem B4640591 : Blo 1831617 4640591 := bstep (se 1 (by rfl) ⟨3480443, by rfl⟩ : syracuseStep 4640591 = 6960887) B6960887
theorem B2748287 : Blo 1831617 2748287 := bstep (se 1 (by rfl) ⟨2061215, by rfl⟩ : syracuseStep 2748287 = 4122431) B4122431
theorem B9277415 : Blo 1831617 9277415 := bstep (se 1 (by rfl) ⟨6958061, by rfl⟩ : syracuseStep 9277415 = 13916123) B13916123
theorem B4124663 : Blo 1831617 4124663 := bstep (se 1 (by rfl) ⟨3093497, by rfl⟩ : syracuseStep 4124663 = 6186995) B6186995
theorem B4952159 : Blo 1831617 4952159 := bstep (se 1 (by rfl) ⟨3714119, by rfl⟩ : syracuseStep 4952159 = 7428239) B7428239
theorem B22605925 : Blo 1831617 22605925 := bstep (se 4 (by rfl) ⟨2119305, by rfl⟩ : syracuseStep 22605925 = 4238611) B4238611
theorem B4403303 : Blo 1831617 4403303 := bstep (se 1 (by rfl) ⟨3302477, by rfl⟩ : syracuseStep 4403303 = 6604955) B6604955
theorem B2748623 : Blo 1831617 2748623 := bstep (se 1 (by rfl) ⟨2061467, by rfl⟩ : syracuseStep 2748623 = 4122935) B4122935
theorem B2748743 : Blo 1831617 2748743 := bstep (se 1 (by rfl) ⟨2061557, by rfl⟩ : syracuseStep 2748743 = 4123115) B4123115
theorem B4125023 : Blo 1831617 4125023 := bstep (se 1 (by rfl) ⟨3093767, by rfl⟩ : syracuseStep 4125023 = 6187535) B6187535
theorem B5575159 : Blo 1831617 5575159 := bstep (se 1 (by rfl) ⟨4181369, by rfl⟩ : syracuseStep 5575159 = 8362739) B8362739
theorem B2609695 : Blo 1831617 2609695 := bstep (se 1 (by rfl) ⟨1957271, by rfl⟩ : syracuseStep 2609695 = 3914543) B3914543
theorem B4952701 : Blo 1831617 4952701 := bstep (se 3 (by rfl) ⟨928631, by rfl⟩ : syracuseStep 4952701 = 1857263) B1857263
theorem B20083463 : Blo 1831617 20083463 := bstep (se 1 (by rfl) ⟨15062597, by rfl⟩ : syracuseStep 20083463 = 30125195) B30125195
theorem B1831707 : Blo 1831617 1831707 := bstep (se 1 (by rfl) ⟨1373780, by rfl⟩ : syracuseStep 1831707 = 2747561) B2747561
theorem B2749211 : Blo 1831617 2749211 := bstep (se 1 (by rfl) ⟨2061908, by rfl⟩ : syracuseStep 2749211 = 4123817) B4123817
theorem B6034267 : Blo 1831617 6034267 := bstep (se 1 (by rfl) ⟨4525700, by rfl⟩ : syracuseStep 6034267 = 9051401) B9051401
theorem B23810921 : Blo 1831617 23810921 := bstep (se 2 (by rfl) ⟨8929095, by rfl⟩ : syracuseStep 23810921 = 17858191) B17858191
theorem B4125545 : Blo 1831617 4125545 := bstep (se 2 (by rfl) ⟨1547079, by rfl⟩ : syracuseStep 4125545 = 3094159) B3094159
theorem B1831983 : Blo 1831617 1831983 := bstep (se 1 (by rfl) ⟨1373987, by rfl⟩ : syracuseStep 1831983 = 2747975) B2747975
theorem B2749487 : Blo 1831617 2749487 := bstep (se 1 (by rfl) ⟨2062115, by rfl⟩ : syracuseStep 2749487 = 4124231) B4124231
theorem B2749535 : Blo 1831617 2749535 := bstep (se 1 (by rfl) ⟨2062151, by rfl⟩ : syracuseStep 2749535 = 4124303) B4124303
theorem B2749595 : Blo 1831617 2749595 := bstep (se 1 (by rfl) ⟨2062196, by rfl⟩ : syracuseStep 2749595 = 4124393) B4124393
theorem B1832103 : Blo 1831617 1832103 := bstep (se 1 (by rfl) ⟨1374077, by rfl⟩ : syracuseStep 1832103 = 2748155) B2748155
theorem B2749607 : Blo 1831617 2749607 := bstep (se 1 (by rfl) ⟨2062205, by rfl⟩ : syracuseStep 2749607 = 4124411) B4124411
theorem B3478697 : Blo 1831617 3478697 := bstep (se 2 (by rfl) ⟨1304511, by rfl⟩ : syracuseStep 3478697 = 2609023) B2609023
theorem B20075825 : Blo 1831617 20075825 := bstep (se 2 (by rfl) ⟨7528434, by rfl⟩ : syracuseStep 20075825 = 15056869) B15056869
theorem B10434041 : Blo 1831617 10434041 := bstep (se 2 (by rfl) ⟨3912765, by rfl⟩ : syracuseStep 10434041 = 7825531) B7825531
theorem B13923899 : Blo 1831617 13923899 := bstep (se 1 (by rfl) ⟨10442924, by rfl⟩ : syracuseStep 13923899 = 20885849) B20885849
theorem B1832551 : Blo 1831617 1832551 := bstep (se 1 (by rfl) ⟨1374413, by rfl⟩ : syracuseStep 1832551 = 2748827) B2748827
theorem B14112391 : Blo 1831617 14112391 := bstep (se 1 (by rfl) ⟨10584293, by rfl⟩ : syracuseStep 14112391 = 21168587) B21168587
theorem B2750279 : Blo 1831617 2750279 := bstep (se 1 (by rfl) ⟨2062709, by rfl⟩ : syracuseStep 2750279 = 4125419) B4125419
theorem B1832831 : Blo 1831617 1832831 := bstep (se 1 (by rfl) ⟨1374623, by rfl⟩ : syracuseStep 1832831 = 2749247) B2749247
theorem B1832927 : Blo 1831617 1832927 := bstep (se 1 (by rfl) ⟨1374695, by rfl⟩ : syracuseStep 1832927 = 2749391) B2749391
theorem B1832955 : Blo 1831617 1832955 := bstep (se 1 (by rfl) ⟨1374716, by rfl⟩ : syracuseStep 1832955 = 2749433) B2749433
theorem B1832987 : Blo 1831617 1832987 := bstep (se 1 (by rfl) ⟨1374740, by rfl⟩ : syracuseStep 1832987 = 2749481) B2749481
theorem B2062363 : Blo 1831617 2062363 := bstep (se 1 (by rfl) ⟨1546772, by rfl⟩ : syracuseStep 2062363 = 3093545) B3093545
theorem B37623845 : Blo 1831617 37623845 := bstep (se 4 (by rfl) ⟨3527235, by rfl⟩ : syracuseStep 37623845 = 7054471) B7054471
theorem B1833007 : Blo 1831617 1833007 := bstep (se 1 (by rfl) ⟨1374755, by rfl⟩ : syracuseStep 1833007 = 2749511) B2749511
theorem B1833127 : Blo 1831617 1833127 := bstep (se 1 (by rfl) ⟨1374845, by rfl⟩ : syracuseStep 1833127 = 2749691) B2749691
theorem B6183161 : Blo 1831617 6183161 := bstep (se 2 (by rfl) ⟨2318685, by rfl⟩ : syracuseStep 6183161 = 4637371) B4637371
theorem B2201959 : Blo 1831617 2201959 := bstep (se 1 (by rfl) ⟨1651469, by rfl⟩ : syracuseStep 2201959 = 3302939) B3302939
theorem B15653249 : Blo 1831617 15653249 := bstep (se 2 (by rfl) ⟨5869968, by rfl⟩ : syracuseStep 15653249 = 11739937) B11739937
theorem B6183323 : Blo 1831617 6183323 := bstep (se 1 (by rfl) ⟨4637492, by rfl⟩ : syracuseStep 6183323 = 9274985) B9274985
theorem B17619443 : Blo 1831617 17619443 := bstep (se 1 (by rfl) ⟨13214582, by rfl⟩ : syracuseStep 17619443 = 26429165) B26429165
theorem B67762727 : Blo 1831617 67762727 := bstep (se 1 (by rfl) ⟨50822045, by rfl⟩ : syracuseStep 67762727 = 101644091) B101644091
theorem B3480155 : Blo 1831617 3480155 := bstep (se 1 (by rfl) ⟨2610116, by rfl⟩ : syracuseStep 3480155 = 5220233) B5220233
theorem B6961889 : Blo 1831617 6961889 := bstep (se 2 (by rfl) ⟨2610708, by rfl⟩ : syracuseStep 6961889 = 5221417) B5221417
theorem B19815553 : Blo 1831617 19815553 := bstep (se 2 (by rfl) ⟨7430832, by rfl⟩ : syracuseStep 19815553 = 14861665) B14861665
theorem B13909319 : Blo 1831617 13909319 := bstep (se 1 (by rfl) ⟨10431989, by rfl⟩ : syracuseStep 13909319 = 20863979) B20863979
theorem B31735145 : Blo 1831617 31735145 := bstep (se 2 (by rfl) ⟨11900679, by rfl⟩ : syracuseStep 31735145 = 23801359) B23801359
theorem B4701743 : Blo 1831617 4701743 := bstep (se 1 (by rfl) ⟨3526307, by rfl⟩ : syracuseStep 4701743 = 7052615) B7052615
theorem B6954599 : Blo 1831617 6954599 := bstep (se 1 (by rfl) ⟨5215949, by rfl⟩ : syracuseStep 6954599 = 10431899) B10431899
theorem B4636379 : Blo 1831617 4636379 := bstep (se 1 (by rfl) ⟨3477284, by rfl⟩ : syracuseStep 4636379 = 6954569) B6954569
theorem B4955879 : Blo 1831617 4955879 := bstep (se 1 (by rfl) ⟨3716909, by rfl⟩ : syracuseStep 4955879 = 7433819) B7433819
theorem B3301439 : Blo 1831617 3301439 := bstep (se 1 (by rfl) ⟨2476079, by rfl⟩ : syracuseStep 3301439 = 4952159) B4952159
theorem B6185753 : Blo 1831617 6185753 := bstep (se 2 (by rfl) ⟨2319657, by rfl⟩ : syracuseStep 6185753 = 4639315) B4639315
theorem B2319131 : Blo 1831617 2319131 := bstep (se 1 (by rfl) ⟨1739348, by rfl⟩ : syracuseStep 2319131 = 3478697) B3478697
theorem B9274175 : Blo 1831617 9274175 := bstep (se 1 (by rfl) ⟨6955631, by rfl⟩ : syracuseStep 9274175 = 13911263) B13911263
theorem B6603601 : Blo 1831617 6603601 := bstep (se 2 (by rfl) ⟨2476350, by rfl⟩ : syracuseStep 6603601 = 4952701) B4952701
theorem B6956027 : Blo 1831617 6956027 := bstep (se 1 (by rfl) ⟨5217020, by rfl⟩ : syracuseStep 6956027 = 10434041) B10434041
theorem B9282599 : Blo 1831617 9282599 := bstep (se 1 (by rfl) ⟨6961949, by rfl⟩ : syracuseStep 9282599 = 13923899) B13923899
theorem B8045615 : Blo 1831617 8045615 := bstep (se 1 (by rfl) ⟨6034211, by rfl⟩ : syracuseStep 8045615 = 12068423) B12068423
theorem B57181301 : Blo 1831617 57181301 := bstep (se 5 (by rfl) ⟨2680373, by rfl⟩ : syracuseStep 57181301 = 5360747) B5360747
theorem B8045689 : Blo 1831617 8045689 := bstep (se 2 (by rfl) ⟨3017133, by rfl⟩ : syracuseStep 8045689 = 6034267) B6034267
theorem B4122107 : Blo 1831617 4122107 := bstep (se 1 (by rfl) ⟨3091580, by rfl⟩ : syracuseStep 4122107 = 6183161) B6183161
theorem B26420737 : Blo 1831617 26420737 := bstep (se 2 (by rfl) ⟨9907776, by rfl⟩ : syracuseStep 26420737 = 19815553) B19815553
theorem B4122215 : Blo 1831617 4122215 := bstep (se 1 (by rfl) ⟨3091661, by rfl⟩ : syracuseStep 4122215 = 6183323) B6183323
theorem B2320103 : Blo 1831617 2320103 := bstep (se 1 (by rfl) ⟨1740077, by rfl⟩ : syracuseStep 2320103 = 3480155) B3480155
theorem B15058879 : Blo 1831617 15058879 := bstep (se 1 (by rfl) ⟨11294159, by rfl⟩ : syracuseStep 15058879 = 22588319) B22588319
theorem B3090919 : Blo 1831617 3090919 := bstep (se 1 (by rfl) ⟨2318189, by rfl⟩ : syracuseStep 3090919 = 4636379) B4636379
theorem B3303919 : Blo 1831617 3303919 := bstep (se 1 (by rfl) ⟨2477939, by rfl⟩ : syracuseStep 3303919 = 4955879) B4955879
theorem B2935535 : Blo 1831617 2935535 := bstep (se 1 (by rfl) ⟨2201651, by rfl⟩ : syracuseStep 2935535 = 4403303) B4403303
theorem B17853203 : Blo 1831617 17853203 := bstep (se 1 (by rfl) ⟨13389902, by rfl⟩ : syracuseStep 17853203 = 26779805) B26779805
theorem B30141233 : Blo 1831617 30141233 := bstep (se 2 (by rfl) ⟨11302962, by rfl⟩ : syracuseStep 30141233 = 22605925) B22605925
theorem B3091439 : Blo 1831617 3091439 := bstep (se 1 (by rfl) ⟨2318579, by rfl⟩ : syracuseStep 3091439 = 4637159) B4637159
theorem B2935945 : Blo 1831617 2935945 := bstep (se 2 (by rfl) ⟨1100979, by rfl⟩ : syracuseStep 2935945 = 2201959) B2201959
theorem B4402343 : Blo 1831617 4402343 := bstep (se 1 (by rfl) ⟨3301757, by rfl⟩ : syracuseStep 4402343 = 6603515) B6603515
theorem B5868713 : Blo 1831617 5868713 := bstep (se 2 (by rfl) ⟨2200767, by rfl⟩ : syracuseStep 5868713 = 4401535) B4401535
theorem B13388975 : Blo 1831617 13388975 := bstep (se 1 (by rfl) ⟨10041731, by rfl⟩ : syracuseStep 13388975 = 20083463) B20083463
theorem B7433545 : Blo 1831617 7433545 := bstep (se 2 (by rfl) ⟨2787579, by rfl⟩ : syracuseStep 7433545 = 5575159) B5575159
theorem B2747807 : Blo 1831617 2747807 := bstep (se 1 (by rfl) ⟨2060855, by rfl⟩ : syracuseStep 2747807 = 4121711) B4121711
theorem B5287529 : Blo 1831617 5287529 := bstep (se 2 (by rfl) ⟨1982823, by rfl⟩ : syracuseStep 5287529 = 3965647) B3965647
theorem B6696577 : Blo 1831617 6696577 := bstep (se 2 (by rfl) ⟨2511216, by rfl⟩ : syracuseStep 6696577 = 5022433) B5022433
theorem B2748479 : Blo 1831617 2748479 := bstep (se 1 (by rfl) ⟨2061359, by rfl⟩ : syracuseStep 2748479 = 4122719) B4122719
theorem B3092735 : Blo 1831617 3092735 := bstep (se 1 (by rfl) ⟨2319551, by rfl⟩ : syracuseStep 3092735 = 4639103) B4639103
theorem B45175151 : Blo 1831617 45175151 := bstep (se 1 (by rfl) ⟨33881363, by rfl⟩ : syracuseStep 45175151 = 67762727) B67762727
theorem B4641259 : Blo 1831617 4641259 := bstep (se 1 (by rfl) ⟨3480944, by rfl⟩ : syracuseStep 4641259 = 6961889) B6961889
theorem B26415665 : Blo 1831617 26415665 := bstep (se 2 (by rfl) ⟨9905874, by rfl⟩ : syracuseStep 26415665 = 19811749) B19811749
theorem B7828163 : Blo 1831617 7828163 := bstep (se 1 (by rfl) ⟨5871122, by rfl⟩ : syracuseStep 7828163 = 11742245) B11742245
theorem B1831631 : Blo 1831617 1831631 := bstep (se 1 (by rfl) ⟨1373723, by rfl⟩ : syracuseStep 1831631 = 2747447) B2747447
theorem B3478241 : Blo 1831617 3478241 := bstep (se 2 (by rfl) ⟨1304340, by rfl⟩ : syracuseStep 3478241 = 2608681) B2608681
theorem B1831711 : Blo 1831617 1831711 := bstep (se 1 (by rfl) ⟨1373783, by rfl⟩ : syracuseStep 1831711 = 2747567) B2747567
theorem B1831751 : Blo 1831617 1831751 := bstep (se 1 (by rfl) ⟨1373813, by rfl⟩ : syracuseStep 1831751 = 2747627) B2747627
theorem B21156763 : Blo 1831617 21156763 := bstep (se 1 (by rfl) ⟨15867572, by rfl⟩ : syracuseStep 21156763 = 31735145) B31735145
theorem B2061247 : Blo 1831617 2061247 := bstep (se 1 (by rfl) ⟨1545935, by rfl⟩ : syracuseStep 2061247 = 3091871) B3091871
theorem B3134495 : Blo 1831617 3134495 := bstep (se 1 (by rfl) ⟨2350871, by rfl⟩ : syracuseStep 3134495 = 4701743) B4701743
theorem B3093727 : Blo 1831617 3093727 := bstep (se 1 (by rfl) ⟨2320295, by rfl⟩ : syracuseStep 3093727 = 4640591) B4640591
theorem B1832191 : Blo 1831617 1832191 := bstep (se 1 (by rfl) ⟨1374143, by rfl⟩ : syracuseStep 1832191 = 2748287) B2748287
theorem B2749775 : Blo 1831617 2749775 := bstep (se 1 (by rfl) ⟨2062331, by rfl⟩ : syracuseStep 2749775 = 4124663) B4124663
theorem B2749817 : Blo 1831617 2749817 := bstep (se 2 (by rfl) ⟨1031181, by rfl⟩ : syracuseStep 2749817 = 2062363) B2062363
theorem B1832415 : Blo 1831617 1832415 := bstep (se 1 (by rfl) ⟨1374311, by rfl⟩ : syracuseStep 1832415 = 2748623) B2748623
theorem B1832495 : Blo 1831617 1832495 := bstep (se 1 (by rfl) ⟨1374371, by rfl⟩ : syracuseStep 1832495 = 2748743) B2748743
theorem B2750015 : Blo 1831617 2750015 := bstep (se 1 (by rfl) ⟨2062511, by rfl⟩ : syracuseStep 2750015 = 4125023) B4125023
theorem B1832807 : Blo 1831617 1832807 := bstep (se 1 (by rfl) ⟨1374605, by rfl⟩ : syracuseStep 1832807 = 2749211) B2749211
theorem B15873947 : Blo 1831617 15873947 := bstep (se 1 (by rfl) ⟨11905460, by rfl⟩ : syracuseStep 15873947 = 23810921) B23810921
theorem B2750363 : Blo 1831617 2750363 := bstep (se 1 (by rfl) ⟨2062772, by rfl⟩ : syracuseStep 2750363 = 4125545) B4125545
theorem B1832991 : Blo 1831617 1832991 := bstep (se 1 (by rfl) ⟨1374743, by rfl⟩ : syracuseStep 1832991 = 2749487) B2749487
theorem B3479593 : Blo 1831617 3479593 := bstep (se 2 (by rfl) ⟨1304847, by rfl⟩ : syracuseStep 3479593 = 2609695) B2609695
theorem B1833023 : Blo 1831617 1833023 := bstep (se 1 (by rfl) ⟨1374767, by rfl⟩ : syracuseStep 1833023 = 2749535) B2749535
theorem B1833063 : Blo 1831617 1833063 := bstep (se 1 (by rfl) ⟨1374797, by rfl⟩ : syracuseStep 1833063 = 2749595) B2749595
theorem B1833071 : Blo 1831617 1833071 := bstep (se 1 (by rfl) ⟨1374803, by rfl⟩ : syracuseStep 1833071 = 2749607) B2749607
theorem B13383883 : Blo 1831617 13383883 := bstep (se 1 (by rfl) ⟨10037912, by rfl⟩ : syracuseStep 13383883 = 20075825) B20075825
theorem B15661349 : Blo 1831617 15661349 := bstep (se 4 (by rfl) ⟨1468251, by rfl⟩ : syracuseStep 15661349 = 2936503) B2936503
theorem B6183431 : Blo 1831617 6183431 := bstep (se 1 (by rfl) ⟨4637573, by rfl⟩ : syracuseStep 6183431 = 9275147) B9275147
theorem B1833519 : Blo 1831617 1833519 := bstep (se 1 (by rfl) ⟨1375139, by rfl⟩ : syracuseStep 1833519 = 2750279) B2750279
theorem B17848927 : Blo 1831617 17848927 := bstep (se 1 (by rfl) ⟨13386695, by rfl⟩ : syracuseStep 17848927 = 26773391) B26773391
theorem B25082563 : Blo 1831617 25082563 := bstep (se 1 (by rfl) ⟨18811922, by rfl⟩ : syracuseStep 25082563 = 37623845) B37623845
theorem B27155159 : Blo 1831617 27155159 := bstep (se 1 (by rfl) ⟨20366369, by rfl⟩ : syracuseStep 27155159 = 40732739) B40732739
theorem B4954927 : Blo 1831617 4954927 := bstep (se 1 (by rfl) ⟨3716195, by rfl⟩ : syracuseStep 4954927 = 7432391) B7432391
theorem B29735785 : Blo 1831617 29735785 := bstep (se 2 (by rfl) ⟨11150919, by rfl⟩ : syracuseStep 29735785 = 22301839) B22301839
theorem B19815299 : Blo 1831617 19815299 := bstep (se 1 (by rfl) ⟨14861474, by rfl⟩ : syracuseStep 19815299 = 29722949) B29722949
theorem B10435499 : Blo 1831617 10435499 := bstep (se 1 (by rfl) ⟨7826624, by rfl⟩ : syracuseStep 10435499 = 15653249) B15653249
theorem B11746295 : Blo 1831617 11746295 := bstep (se 1 (by rfl) ⟨8809721, by rfl⟩ : syracuseStep 11746295 = 17619443) B17619443
theorem B18816521 : Blo 1831617 18816521 := bstep (se 2 (by rfl) ⟨7056195, by rfl⟩ : syracuseStep 18816521 = 14112391) B14112391
theorem B9272879 : Blo 1831617 9272879 := bstep (se 1 (by rfl) ⟨6954659, by rfl⟩ : syracuseStep 9272879 = 13909319) B13909319
theorem B6184511 : Blo 1831617 6184511 := bstep (se 1 (by rfl) ⟨4638383, by rfl⟩ : syracuseStep 6184511 = 9276767) B9276767
theorem B4636399 : Blo 1831617 4636399 := bstep (se 1 (by rfl) ⟨3477299, by rfl⟩ : syracuseStep 4636399 = 6954599) B6954599
theorem B6184943 : Blo 1831617 6184943 := bstep (se 1 (by rfl) ⟨4638707, by rfl⟩ : syracuseStep 6184943 = 9277415) B9277415
theorem B5218775 : Blo 1831617 5218775 := bstep (se 1 (by rfl) ⟨3914081, by rfl⟩ : syracuseStep 5218775 = 7828163) B7828163
theorem B4121225 : Blo 1831617 4121225 := bstep (se 2 (by rfl) ⟨1545459, by rfl⟩ : syracuseStep 4121225 = 3090919) B3090919
theorem B4637351 : Blo 1831617 4637351 := bstep (se 1 (by rfl) ⟨3478013, by rfl⟩ : syracuseStep 4637351 = 6956027) B6956027
theorem B23798569 : Blo 1831617 23798569 := bstep (se 2 (by rfl) ⟨8924463, by rfl⟩ : syracuseStep 23798569 = 17848927) B17848927
theorem B50177389 : Blo 1831617 50177389 := bstep (se 3 (by rfl) ⟨9408260, by rfl⟩ : syracuseStep 50177389 = 18816521) B18816521
theorem B14100077 : Blo 1831617 14100077 := bstep (se 3 (by rfl) ⟨2643764, by rfl⟩ : syracuseStep 14100077 = 5287529) B5287529
theorem B4122287 : Blo 1831617 4122287 := bstep (se 1 (by rfl) ⟨3091715, by rfl⟩ : syracuseStep 4122287 = 6183431) B6183431
theorem B9275309 : Blo 1831617 9275309 := bstep (se 3 (by rfl) ⟨1739120, by rfl⟩ : syracuseStep 9275309 = 3478241) B3478241
theorem B6186941 : Blo 1831617 6186941 := bstep (se 3 (by rfl) ⟨1160051, by rfl⟩ : syracuseStep 6186941 = 2320103) B2320103
theorem B6956999 : Blo 1831617 6956999 := bstep (se 1 (by rfl) ⟨5217749, by rfl⟩ : syracuseStep 6956999 = 10435499) B10435499
theorem B35227649 : Blo 1831617 35227649 := bstep (se 2 (by rfl) ⟨13210368, by rfl⟩ : syracuseStep 35227649 = 26420737) B26420737
theorem B2934895 : Blo 1831617 2934895 := bstep (se 1 (by rfl) ⟨2201171, by rfl⟩ : syracuseStep 2934895 = 4402343) B4402343
theorem B4123007 : Blo 1831617 4123007 := bstep (se 1 (by rfl) ⟨3092255, by rfl⟩ : syracuseStep 4123007 = 6184511) B6184511
theorem B4123295 : Blo 1831617 4123295 := bstep (se 1 (by rfl) ⟨3092471, by rfl⟩ : syracuseStep 4123295 = 6184943) B6184943
theorem B4639457 : Blo 1831617 4639457 := bstep (se 2 (by rfl) ⟨1739796, by rfl⟩ : syracuseStep 4639457 = 3479593) B3479593
theorem B8358653 : Blo 1831617 8358653 := bstep (se 3 (by rfl) ⟨1567247, by rfl⟩ : syracuseStep 8358653 = 3134495) B3134495
theorem B30116767 : Blo 1831617 30116767 := bstep (se 1 (by rfl) ⟨22587575, by rfl⟩ : syracuseStep 30116767 = 45175151) B45175151
theorem B4123835 : Blo 1831617 4123835 := bstep (se 1 (by rfl) ⟨3092876, by rfl⟩ : syracuseStep 4123835 = 6185753) B6185753
theorem B6188345 : Blo 1831617 6188345 := bstep (se 2 (by rfl) ⟨2320629, by rfl⟩ : syracuseStep 6188345 = 4641259) B4641259
theorem B6188399 : Blo 1831617 6188399 := bstep (se 1 (by rfl) ⟨4641299, by rfl⟩ : syracuseStep 6188399 = 9282599) B9282599
theorem B15658373 : Blo 1831617 15658373 := bstep (se 4 (by rfl) ⟨1467972, by rfl⟩ : syracuseStep 15658373 = 2935945) B2935945
theorem B38120867 : Blo 1831617 38120867 := bstep (se 1 (by rfl) ⟨28590650, by rfl⟩ : syracuseStep 38120867 = 57181301) B57181301
theorem B33443417 : Blo 1831617 33443417 := bstep (se 2 (by rfl) ⟨12541281, by rfl⟩ : syracuseStep 33443417 = 25082563) B25082563
theorem B2748071 : Blo 1831617 2748071 := bstep (se 1 (by rfl) ⟨2061053, by rfl⟩ : syracuseStep 2748071 = 4122107) B4122107
theorem B71380709 : Blo 1831617 71380709 := bstep (se 4 (by rfl) ⟨6691941, by rfl⟩ : syracuseStep 71380709 = 13383883) B13383883
theorem B6606569 : Blo 1831617 6606569 := bstep (se 2 (by rfl) ⟨2477463, by rfl⟩ : syracuseStep 6606569 = 4954927) B4954927
theorem B2748143 : Blo 1831617 2748143 := bstep (se 1 (by rfl) ⟨2061107, by rfl⟩ : syracuseStep 2748143 = 4122215) B4122215
theorem B28209017 : Blo 1831617 28209017 := bstep (se 2 (by rfl) ⟨10578381, by rfl⟩ : syracuseStep 28209017 = 21156763) B21156763
theorem B2748329 : Blo 1831617 2748329 := bstep (se 2 (by rfl) ⟨1030623, by rfl⟩ : syracuseStep 2748329 = 2061247) B2061247
theorem B10727585 : Blo 1831617 10727585 := bstep (se 2 (by rfl) ⟨4022844, by rfl⟩ : syracuseStep 10727585 = 8045689) B8045689
theorem B10440899 : Blo 1831617 10440899 := bstep (se 1 (by rfl) ⟨7830674, by rfl⟩ : syracuseStep 10440899 = 15661349) B15661349
theorem B4124969 : Blo 1831617 4124969 := bstep (se 2 (by rfl) ⟨1546863, by rfl⟩ : syracuseStep 4124969 = 3093727) B3093727
theorem B13210199 : Blo 1831617 13210199 := bstep (se 1 (by rfl) ⟨9907649, by rfl⟩ : syracuseStep 13210199 = 19815299) B19815299
theorem B7828093 : Blo 1831617 7828093 := bstep (se 3 (by rfl) ⟨1467767, by rfl⟩ : syracuseStep 7828093 = 2935535) B2935535
theorem B2060959 : Blo 1831617 2060959 := bstep (se 1 (by rfl) ⟨1545719, by rfl⟩ : syracuseStep 2060959 = 3091439) B3091439
theorem B3912475 : Blo 1831617 3912475 := bstep (se 1 (by rfl) ⟨2934356, by rfl⟩ : syracuseStep 3912475 = 5868713) B5868713
theorem B8925983 : Blo 1831617 8925983 := bstep (se 1 (by rfl) ⟨6694487, by rfl⟩ : syracuseStep 8925983 = 13388975) B13388975
theorem B1831871 : Blo 1831617 1831871 := bstep (se 1 (by rfl) ⟨1373903, by rfl⟩ : syracuseStep 1831871 = 2747807) B2747807
theorem B6181865 : Blo 1831617 6181865 := bstep (se 2 (by rfl) ⟨2318199, by rfl⟩ : syracuseStep 6181865 = 4636399) B4636399
theorem B6181919 : Blo 1831617 6181919 := bstep (se 1 (by rfl) ⟨4636439, by rfl⟩ : syracuseStep 6181919 = 9272879) B9272879
theorem B1832319 : Blo 1831617 1832319 := bstep (se 1 (by rfl) ⟨1374239, by rfl⟩ : syracuseStep 1832319 = 2748479) B2748479
theorem B8803837 : Blo 1831617 8803837 := bstep (se 3 (by rfl) ⟨1650719, by rfl⟩ : syracuseStep 8803837 = 3301439) B3301439
theorem B2061823 : Blo 1831617 2061823 := bstep (se 1 (by rfl) ⟨1546367, by rfl⟩ : syracuseStep 2061823 = 3092735) B3092735
theorem B17610443 : Blo 1831617 17610443 := bstep (se 1 (by rfl) ⟨13207832, by rfl⟩ : syracuseStep 17610443 = 26415665) B26415665
theorem B6182783 : Blo 1831617 6182783 := bstep (se 1 (by rfl) ⟨4637087, by rfl⟩ : syracuseStep 6182783 = 9274175) B9274175
theorem B35715077 : Blo 1831617 35715077 := bstep (se 4 (by rfl) ⟨3348288, by rfl⟩ : syracuseStep 35715077 = 6696577) B6696577
theorem B5363743 : Blo 1831617 5363743 := bstep (se 1 (by rfl) ⟨4022807, by rfl⟩ : syracuseStep 5363743 = 8045615) B8045615
theorem B1833183 : Blo 1831617 1833183 := bstep (se 1 (by rfl) ⟨1374887, by rfl⟩ : syracuseStep 1833183 = 2749775) B2749775
theorem B1833211 : Blo 1831617 1833211 := bstep (se 1 (by rfl) ⟨1374908, by rfl⟩ : syracuseStep 1833211 = 2749817) B2749817
theorem B1833343 : Blo 1831617 1833343 := bstep (se 1 (by rfl) ⟨1375007, by rfl⟩ : syracuseStep 1833343 = 2750015) B2750015
theorem B8804801 : Blo 1831617 8804801 := bstep (se 2 (by rfl) ⟨3301800, by rfl⟩ : syracuseStep 8804801 = 6603601) B6603601
theorem B39647713 : Blo 1831617 39647713 := bstep (se 2 (by rfl) ⟨14867892, by rfl⟩ : syracuseStep 39647713 = 29735785) B29735785
theorem B10582631 : Blo 1831617 10582631 := bstep (se 1 (by rfl) ⟨7936973, by rfl⟩ : syracuseStep 10582631 = 15873947) B15873947
theorem B1833575 : Blo 1831617 1833575 := bstep (se 1 (by rfl) ⟨1375181, by rfl⟩ : syracuseStep 1833575 = 2750363) B2750363
theorem B9911393 : Blo 1831617 9911393 := bstep (se 2 (by rfl) ⟨3716772, by rfl⟩ : syracuseStep 9911393 = 7433545) B7433545
theorem B18103439 : Blo 1831617 18103439 := bstep (se 1 (by rfl) ⟨13577579, by rfl⟩ : syracuseStep 18103439 = 27155159) B27155159
theorem B11902135 : Blo 1831617 11902135 := bstep (se 1 (by rfl) ⟨8926601, by rfl⟩ : syracuseStep 11902135 = 17853203) B17853203
theorem B20094155 : Blo 1831617 20094155 := bstep (se 1 (by rfl) ⟨15070616, by rfl⟩ : syracuseStep 20094155 = 30141233) B30141233
theorem B7830863 : Blo 1831617 7830863 := bstep (se 1 (by rfl) ⟨5873147, by rfl⟩ : syracuseStep 7830863 = 11746295) B11746295
theorem B6184349 : Blo 1831617 6184349 := bstep (se 3 (by rfl) ⟨1159565, by rfl⟩ : syracuseStep 6184349 = 2319131) B2319131
theorem B80314021 : Blo 1831617 80314021 := bstep (se 4 (by rfl) ⟨7529439, by rfl⟩ : syracuseStep 80314021 = 15058879) B15058879
theorem B17620901 : Blo 1831617 17620901 := bstep (se 4 (by rfl) ⟨1651959, by rfl⟩ : syracuseStep 17620901 = 3303919) B3303919
theorem B7151657 : Blo 1831617 7151657 := bstep (se 2 (by rfl) ⟨2681871, by rfl⟩ : syracuseStep 7151657 = 5363743) B5363743
theorem B7151723 : Blo 1831617 7151723 := bstep (se 1 (by rfl) ⟨5363792, by rfl⟩ : syracuseStep 7151723 = 10727585) B10727585
theorem B48275837 : Blo 1831617 48275837 := bstep (se 3 (by rfl) ⟨9051719, by rfl⟩ : syracuseStep 48275837 = 18103439) B18103439
theorem B8806799 : Blo 1831617 8806799 := bstep (se 1 (by rfl) ⟨6605099, by rfl⟩ : syracuseStep 8806799 = 13210199) B13210199
theorem B52863617 : Blo 1831617 52863617 := bstep (se 2 (by rfl) ⟨19823856, by rfl⟩ : syracuseStep 52863617 = 39647713) B39647713
theorem B4121243 : Blo 1831617 4121243 := bstep (se 1 (by rfl) ⟨3090932, by rfl⟩ : syracuseStep 4121243 = 6181865) B6181865
theorem B4121279 : Blo 1831617 4121279 := bstep (se 1 (by rfl) ⟨3090959, by rfl⟩ : syracuseStep 4121279 = 6181919) B6181919
theorem B10437457 : Blo 1831617 10437457 := bstep (se 2 (by rfl) ⟨3914046, by rfl⟩ : syracuseStep 10437457 = 7828093) B7828093
theorem B11740295 : Blo 1831617 11740295 := bstep (se 1 (by rfl) ⟨8805221, by rfl⟩ : syracuseStep 11740295 = 17610443) B17610443
theorem B4121855 : Blo 1831617 4121855 := bstep (se 1 (by rfl) ⟨3091391, by rfl⟩ : syracuseStep 4121855 = 6182783) B6182783
theorem B4637999 : Blo 1831617 4637999 := bstep (se 1 (by rfl) ⟨3478499, by rfl⟩ : syracuseStep 4637999 = 6956999) B6956999
theorem B15869513 : Blo 1831617 15869513 := bstep (se 2 (by rfl) ⟨5951067, by rfl⟩ : syracuseStep 15869513 = 11902135) B11902135
theorem B7055087 : Blo 1831617 7055087 := bstep (se 1 (by rfl) ⟨5291315, by rfl⟩ : syracuseStep 7055087 = 10582631) B10582631
theorem B5572435 : Blo 1831617 5572435 := bstep (se 1 (by rfl) ⟨4179326, by rfl⟩ : syracuseStep 5572435 = 8358653) B8358653
theorem B13396103 : Blo 1831617 13396103 := bstep (se 1 (by rfl) ⟨10047077, by rfl⟩ : syracuseStep 13396103 = 20094155) B20094155
theorem B5220575 : Blo 1831617 5220575 := bstep (se 1 (by rfl) ⟨3915431, by rfl⟩ : syracuseStep 5220575 = 7830863) B7830863
theorem B10438915 : Blo 1831617 10438915 := bstep (se 1 (by rfl) ⟨7829186, by rfl⟩ : syracuseStep 10438915 = 15658373) B15658373
theorem B4122899 : Blo 1831617 4122899 := bstep (se 1 (by rfl) ⟨3092174, by rfl⟩ : syracuseStep 4122899 = 6184349) B6184349
theorem B25413911 : Blo 1831617 25413911 := bstep (se 1 (by rfl) ⟨19060433, by rfl⟩ : syracuseStep 25413911 = 38120867) B38120867
theorem B2747483 : Blo 1831617 2747483 := bstep (se 1 (by rfl) ⟨2060612, by rfl⟩ : syracuseStep 2747483 = 4121225) B4121225
theorem B3091567 : Blo 1831617 3091567 := bstep (se 1 (by rfl) ⟨2318675, by rfl⟩ : syracuseStep 3091567 = 4637351) B4637351
theorem B5950655 : Blo 1831617 5950655 := bstep (se 1 (by rfl) ⟨4462991, by rfl⟩ : syracuseStep 5950655 = 8925983) B8925983
theorem B2747945 : Blo 1831617 2747945 := bstep (se 2 (by rfl) ⟨1030479, by rfl⟩ : syracuseStep 2747945 = 2060959) B2060959
theorem B31731425 : Blo 1831617 31731425 := bstep (se 2 (by rfl) ⟨11899284, by rfl⟩ : syracuseStep 31731425 = 23798569) B23798569
theorem B9400051 : Blo 1831617 9400051 := bstep (se 1 (by rfl) ⟨7050038, by rfl⟩ : syracuseStep 9400051 = 14100077) B14100077
theorem B2748191 : Blo 1831617 2748191 := bstep (se 1 (by rfl) ⟨2061143, by rfl⟩ : syracuseStep 2748191 = 4122287) B4122287
theorem B4124627 : Blo 1831617 4124627 := bstep (se 1 (by rfl) ⟨3093470, by rfl⟩ : syracuseStep 4124627 = 6186941) B6186941
theorem B23810051 : Blo 1831617 23810051 := bstep (se 1 (by rfl) ⟨17857538, by rfl⟩ : syracuseStep 23810051 = 35715077) B35715077
theorem B2748671 : Blo 1831617 2748671 := bstep (se 1 (by rfl) ⟨2061503, by rfl⟩ : syracuseStep 2748671 = 4123007) B4123007
theorem B5869867 : Blo 1831617 5869867 := bstep (se 1 (by rfl) ⟨4402400, by rfl⟩ : syracuseStep 5869867 = 8804801) B8804801
theorem B2748863 : Blo 1831617 2748863 := bstep (se 1 (by rfl) ⟨2061647, by rfl⟩ : syracuseStep 2748863 = 4123295) B4123295
theorem B3092971 : Blo 1831617 3092971 := bstep (se 1 (by rfl) ⟨2319728, by rfl⟩ : syracuseStep 3092971 = 4639457) B4639457
theorem B2749097 : Blo 1831617 2749097 := bstep (se 2 (by rfl) ⟨1030911, by rfl⟩ : syracuseStep 2749097 = 2061823) B2061823
theorem B6607595 : Blo 1831617 6607595 := bstep (se 1 (by rfl) ⟨4955696, by rfl⟩ : syracuseStep 6607595 = 9911393) B9911393
theorem B2749223 : Blo 1831617 2749223 := bstep (se 1 (by rfl) ⟨2061917, by rfl⟩ : syracuseStep 2749223 = 4123835) B4123835
theorem B4125563 : Blo 1831617 4125563 := bstep (se 1 (by rfl) ⟨3094172, by rfl⟩ : syracuseStep 4125563 = 6188345) B6188345
theorem B4125599 : Blo 1831617 4125599 := bstep (se 1 (by rfl) ⟨3094199, by rfl⟩ : syracuseStep 4125599 = 6188399) B6188399
theorem B75224045 : Blo 1831617 75224045 := bstep (se 3 (by rfl) ⟨14104508, by rfl⟩ : syracuseStep 75224045 = 28209017) B28209017
theorem B22295611 : Blo 1831617 22295611 := bstep (se 1 (by rfl) ⟨16721708, by rfl⟩ : syracuseStep 22295611 = 33443417) B33443417
theorem B1832047 : Blo 1831617 1832047 := bstep (se 1 (by rfl) ⟨1374035, by rfl⟩ : syracuseStep 1832047 = 2748071) B2748071
theorem B4404379 : Blo 1831617 4404379 := bstep (se 1 (by rfl) ⟨3303284, by rfl⟩ : syracuseStep 4404379 = 6606569) B6606569
theorem B1832095 : Blo 1831617 1832095 := bstep (se 1 (by rfl) ⟨1374071, by rfl⟩ : syracuseStep 1832095 = 2748143) B2748143
theorem B1832219 : Blo 1831617 1832219 := bstep (se 1 (by rfl) ⟨1374164, by rfl⟩ : syracuseStep 1832219 = 2748329) B2748329
theorem B6960599 : Blo 1831617 6960599 := bstep (se 1 (by rfl) ⟨5220449, by rfl⟩ : syracuseStep 6960599 = 10440899) B10440899
theorem B3913193 : Blo 1831617 3913193 := bstep (se 2 (by rfl) ⟨1467447, by rfl⟩ : syracuseStep 3913193 = 2934895) B2934895
theorem B2749979 : Blo 1831617 2749979 := bstep (se 1 (by rfl) ⟨2062484, by rfl⟩ : syracuseStep 2749979 = 4124969) B4124969
theorem B3479183 : Blo 1831617 3479183 := bstep (se 1 (by rfl) ⟨2609387, by rfl⟩ : syracuseStep 3479183 = 5218775) B5218775
theorem B428341445 : Blo 1831617 428341445 := bstep (se 4 (by rfl) ⟨40157010, by rfl⟩ : syracuseStep 428341445 = 80314021) B80314021
theorem B5216633 : Blo 1831617 5216633 := bstep (se 2 (by rfl) ⟨1956237, by rfl⟩ : syracuseStep 5216633 = 3912475) B3912475
theorem B40155689 : Blo 1831617 40155689 := bstep (se 2 (by rfl) ⟨15058383, by rfl⟩ : syracuseStep 40155689 = 30116767) B30116767
theorem B6183539 : Blo 1831617 6183539 := bstep (se 1 (by rfl) ⟨4637654, by rfl⟩ : syracuseStep 6183539 = 9275309) B9275309
theorem B23485099 : Blo 1831617 23485099 := bstep (se 1 (by rfl) ⟨17613824, by rfl⟩ : syracuseStep 23485099 = 35227649) B35227649
theorem B66903185 : Blo 1831617 66903185 := bstep (se 2 (by rfl) ⟨25088694, by rfl⟩ : syracuseStep 66903185 = 50177389) B50177389
theorem B11738449 : Blo 1831617 11738449 := bstep (se 2 (by rfl) ⟨4401918, by rfl⟩ : syracuseStep 11738449 = 8803837) B8803837
theorem B47587139 : Blo 1831617 47587139 := bstep (se 1 (by rfl) ⟨35690354, by rfl⟩ : syracuseStep 47587139 = 71380709) B71380709
theorem B11747267 : Blo 1831617 11747267 := bstep (se 1 (by rfl) ⟨8810450, by rfl⟩ : syracuseStep 11747267 = 17620901) B17620901
theorem B4767815 : Blo 1831617 4767815 := bstep (se 1 (by rfl) ⟨3575861, by rfl⟩ : syracuseStep 4767815 = 7151723) B7151723
theorem B19071085 : Blo 1831617 19071085 := bstep (se 3 (by rfl) ⟨3575828, by rfl⟩ : syracuseStep 19071085 = 7151657) B7151657
theorem B13918553 : Blo 1831617 13918553 := bstep (se 2 (by rfl) ⟨5219457, by rfl⟩ : syracuseStep 13918553 = 10438915) B10438915
theorem B35242411 : Blo 1831617 35242411 := bstep (se 1 (by rfl) ⟨26431808, by rfl⟩ : syracuseStep 35242411 = 52863617) B52863617
theorem B2319455 : Blo 1831617 2319455 := bstep (se 1 (by rfl) ⟨1739591, by rfl⟩ : syracuseStep 2319455 = 3479183) B3479183
theorem B8930735 : Blo 1831617 8930735 := bstep (se 1 (by rfl) ⟨6698051, by rfl⟩ : syracuseStep 8930735 = 13396103) B13396103
theorem B4122089 : Blo 1831617 4122089 := bstep (se 2 (by rfl) ⟨1545783, by rfl⟩ : syracuseStep 4122089 = 3091567) B3091567
theorem B16942607 : Blo 1831617 16942607 := bstep (se 1 (by rfl) ⟨12706955, by rfl⟩ : syracuseStep 16942607 = 25413911) B25413911
theorem B4122359 : Blo 1831617 4122359 := bstep (se 1 (by rfl) ⟨3091769, by rfl⟩ : syracuseStep 4122359 = 6183539) B6183539
theorem B3967103 : Blo 1831617 3967103 := bstep (se 1 (by rfl) ⟨2975327, by rfl⟩ : syracuseStep 3967103 = 5950655) B5950655
theorem B21154283 : Blo 1831617 21154283 := bstep (se 1 (by rfl) ⟨15865712, by rfl⟩ : syracuseStep 21154283 = 31731425) B31731425
theorem B7826489 : Blo 1831617 7826489 := bstep (se 2 (by rfl) ⟨2934933, by rfl⟩ : syracuseStep 7826489 = 5869867) B5869867
theorem B2747495 : Blo 1831617 2747495 := bstep (se 1 (by rfl) ⟨2060621, by rfl⟩ : syracuseStep 2747495 = 4121243) B4121243
theorem B2747519 : Blo 1831617 2747519 := bstep (se 1 (by rfl) ⟨2060639, by rfl⟩ : syracuseStep 2747519 = 4121279) B4121279
theorem B4123961 : Blo 1831617 4123961 := bstep (se 2 (by rfl) ⟨1546485, by rfl⟩ : syracuseStep 4123961 = 3092971) B3092971
theorem B7826863 : Blo 1831617 7826863 := bstep (se 1 (by rfl) ⟨5870147, by rfl⟩ : syracuseStep 7826863 = 11740295) B11740295
theorem B2747903 : Blo 1831617 2747903 := bstep (se 1 (by rfl) ⟨2060927, by rfl⟩ : syracuseStep 2747903 = 4121855) B4121855
theorem B3091999 : Blo 1831617 3091999 := bstep (se 1 (by rfl) ⟨2318999, by rfl⟩ : syracuseStep 3091999 = 4637999) B4637999
theorem B31313465 : Blo 1831617 31313465 := bstep (se 2 (by rfl) ⟨11742549, by rfl⟩ : syracuseStep 31313465 = 23485099) B23485099
theorem B4640399 : Blo 1831617 4640399 := bstep (se 1 (by rfl) ⟨3480299, by rfl⟩ : syracuseStep 4640399 = 6960599) B6960599
theorem B2608795 : Blo 1831617 2608795 := bstep (se 1 (by rfl) ⟨1956596, by rfl⟩ : syracuseStep 2608795 = 3913193) B3913193
theorem B285560963 : Blo 1831617 285560963 := bstep (se 1 (by rfl) ⟨214170722, by rfl⟩ : syracuseStep 285560963 = 428341445) B428341445
theorem B2748599 : Blo 1831617 2748599 := bstep (se 1 (by rfl) ⟨2061449, by rfl⟩ : syracuseStep 2748599 = 4122899) B4122899
theorem B3477755 : Blo 1831617 3477755 := bstep (se 1 (by rfl) ⟨2608316, by rfl⟩ : syracuseStep 3477755 = 5216633) B5216633
theorem B15651265 : Blo 1831617 15651265 := bstep (se 2 (by rfl) ⟨5869224, by rfl⟩ : syracuseStep 15651265 = 11738449) B11738449
theorem B18813565 : Blo 1831617 18813565 := bstep (se 3 (by rfl) ⟨3527543, by rfl⟩ : syracuseStep 18813565 = 7055087) B7055087
theorem B1831655 : Blo 1831617 1831655 := bstep (se 1 (by rfl) ⟨1373741, by rfl⟩ : syracuseStep 1831655 = 2747483) B2747483
theorem B44602123 : Blo 1831617 44602123 := bstep (se 1 (by rfl) ⟨33451592, by rfl⟩ : syracuseStep 44602123 = 66903185) B66903185
theorem B1831963 : Blo 1831617 1831963 := bstep (se 1 (by rfl) ⟨1373972, by rfl⟩ : syracuseStep 1831963 = 2747945) B2747945
theorem B1832127 : Blo 1831617 1832127 := bstep (se 1 (by rfl) ⟨1374095, by rfl⟩ : syracuseStep 1832127 = 2748191) B2748191
theorem B31724759 : Blo 1831617 31724759 := bstep (se 1 (by rfl) ⟨23793569, by rfl⟩ : syracuseStep 31724759 = 47587139) B47587139
theorem B2749751 : Blo 1831617 2749751 := bstep (se 1 (by rfl) ⟨2062313, by rfl⟩ : syracuseStep 2749751 = 4124627) B4124627
theorem B15873367 : Blo 1831617 15873367 := bstep (se 1 (by rfl) ⟨11905025, by rfl⟩ : syracuseStep 15873367 = 23810051) B23810051
theorem B1832447 : Blo 1831617 1832447 := bstep (se 1 (by rfl) ⟨1374335, by rfl⟩ : syracuseStep 1832447 = 2748671) B2748671
theorem B32183891 : Blo 1831617 32183891 := bstep (se 1 (by rfl) ⟨24137918, by rfl⟩ : syracuseStep 32183891 = 48275837) B48275837
theorem B5871199 : Blo 1831617 5871199 := bstep (se 1 (by rfl) ⟨4403399, by rfl⟩ : syracuseStep 5871199 = 8806799) B8806799
theorem B1832575 : Blo 1831617 1832575 := bstep (se 1 (by rfl) ⟨1374431, by rfl⟩ : syracuseStep 1832575 = 2748863) B2748863
theorem B1832731 : Blo 1831617 1832731 := bstep (se 1 (by rfl) ⟨1374548, by rfl⟩ : syracuseStep 1832731 = 2749097) B2749097
theorem B4405063 : Blo 1831617 4405063 := bstep (se 1 (by rfl) ⟨3303797, by rfl⟩ : syracuseStep 4405063 = 6607595) B6607595
theorem B1832815 : Blo 1831617 1832815 := bstep (se 1 (by rfl) ⟨1374611, by rfl⟩ : syracuseStep 1832815 = 2749223) B2749223
theorem B2750375 : Blo 1831617 2750375 := bstep (se 1 (by rfl) ⟨2062781, by rfl⟩ : syracuseStep 2750375 = 4125563) B4125563
theorem B2750399 : Blo 1831617 2750399 := bstep (se 1 (by rfl) ⟨2062799, by rfl⟩ : syracuseStep 2750399 = 4125599) B4125599
theorem B50149363 : Blo 1831617 50149363 := bstep (se 1 (by rfl) ⟨37612022, by rfl⟩ : syracuseStep 50149363 = 75224045) B75224045
theorem B1833319 : Blo 1831617 1833319 := bstep (se 1 (by rfl) ⟨1374989, by rfl⟩ : syracuseStep 1833319 = 2749979) B2749979
theorem B13916609 : Blo 1831617 13916609 := bstep (se 2 (by rfl) ⟨5218728, by rfl⟩ : syracuseStep 13916609 = 10437457) B10437457
theorem B29727481 : Blo 1831617 29727481 := bstep (se 2 (by rfl) ⟨11147805, by rfl⟩ : syracuseStep 29727481 = 22295611) B22295611
theorem B3480383 : Blo 1831617 3480383 := bstep (se 1 (by rfl) ⟨2610287, by rfl⟩ : syracuseStep 3480383 = 5220575) B5220575
theorem B42318701 : Blo 1831617 42318701 := bstep (se 3 (by rfl) ⟨7934756, by rfl⟩ : syracuseStep 42318701 = 15869513) B15869513
theorem B5872505 : Blo 1831617 5872505 := bstep (se 2 (by rfl) ⟨2202189, by rfl⟩ : syracuseStep 5872505 = 4404379) B4404379
theorem B26770459 : Blo 1831617 26770459 := bstep (se 1 (by rfl) ⟨20077844, by rfl⟩ : syracuseStep 26770459 = 40155689) B40155689
theorem B12533401 : Blo 1831617 12533401 := bstep (se 2 (by rfl) ⟨4700025, by rfl⟩ : syracuseStep 12533401 = 9400051) B9400051
theorem B7429913 : Blo 1831617 7429913 := bstep (se 2 (by rfl) ⟨2786217, by rfl⟩ : syracuseStep 7429913 = 5572435) B5572435
theorem B7831511 : Blo 1831617 7831511 := bstep (se 1 (by rfl) ⟨5873633, by rfl⟩ : syracuseStep 7831511 = 11747267) B11747267
theorem B3178543 : Blo 1831617 3178543 := bstep (se 1 (by rfl) ⟨2383907, by rfl⟩ : syracuseStep 3178543 = 4767815) B4767815
theorem B190373975 : Blo 1831617 190373975 := bstep (se 1 (by rfl) ⟨142780481, by rfl⟩ : syracuseStep 190373975 = 285560963) B285560963
theorem B25428113 : Blo 1831617 25428113 := bstep (se 2 (by rfl) ⟨9535542, by rfl⟩ : syracuseStep 25428113 = 19071085) B19071085
theorem B6185213 : Blo 1831617 6185213 := bstep (se 3 (by rfl) ⟨1159727, by rfl⟩ : syracuseStep 6185213 = 2319455) B2319455
theorem B46989881 : Blo 1831617 46989881 := bstep (se 2 (by rfl) ⟨17621205, by rfl⟩ : syracuseStep 46989881 = 35242411) B35242411
theorem B9274013 : Blo 1831617 9274013 := bstep (se 3 (by rfl) ⟨1738877, by rfl⟩ : syracuseStep 9274013 = 3477755) B3477755
theorem B21455927 : Blo 1831617 21455927 := bstep (se 1 (by rfl) ⟨16091945, by rfl⟩ : syracuseStep 21455927 = 32183891) B32183891
theorem B35693945 : Blo 1831617 35693945 := bstep (se 2 (by rfl) ⟨13385229, by rfl⟩ : syracuseStep 35693945 = 26770459) B26770459
theorem B2320255 : Blo 1831617 2320255 := bstep (se 1 (by rfl) ⟨1740191, by rfl⟩ : syracuseStep 2320255 = 3480383) B3480383
theorem B4122665 : Blo 1831617 4122665 := bstep (se 2 (by rfl) ⟨1545999, by rfl⟩ : syracuseStep 4122665 = 3091999) B3091999
theorem B20875643 : Blo 1831617 20875643 := bstep (se 1 (by rfl) ⟨15656732, by rfl⟩ : syracuseStep 20875643 = 31313465) B31313465
theorem B5221007 : Blo 1831617 5221007 := bstep (se 1 (by rfl) ⟨3915755, by rfl⟩ : syracuseStep 5221007 = 7831511) B7831511
theorem B66865817 : Blo 1831617 66865817 := bstep (se 2 (by rfl) ⟨25074681, by rfl⟩ : syracuseStep 66865817 = 50149363) B50149363
theorem B10578941 : Blo 1831617 10578941 := bstep (se 3 (by rfl) ⟨1983551, by rfl⟩ : syracuseStep 10578941 = 3967103) B3967103
theorem B20868353 : Blo 1831617 20868353 := bstep (se 2 (by rfl) ⟨7825632, by rfl⟩ : syracuseStep 20868353 = 15651265) B15651265
theorem B100339013 : Blo 1831617 100339013 := bstep (se 4 (by rfl) ⟨9406782, by rfl⟩ : syracuseStep 100339013 = 18813565) B18813565
theorem B2748059 : Blo 1831617 2748059 := bstep (se 1 (by rfl) ⟨2061044, by rfl⟩ : syracuseStep 2748059 = 4122089) B4122089
theorem B39636641 : Blo 1831617 39636641 := bstep (se 2 (by rfl) ⟨14863740, by rfl⟩ : syracuseStep 39636641 = 29727481) B29727481
theorem B59469497 : Blo 1831617 59469497 := bstep (se 2 (by rfl) ⟨22301061, by rfl⟩ : syracuseStep 59469497 = 44602123) B44602123
theorem B2748239 : Blo 1831617 2748239 := bstep (se 1 (by rfl) ⟨2061179, by rfl⟩ : syracuseStep 2748239 = 4122359) B4122359
theorem B9277739 : Blo 1831617 9277739 := bstep (se 1 (by rfl) ⟨6958304, by rfl⟩ : syracuseStep 9277739 = 13916609) B13916609
theorem B14102855 : Blo 1831617 14102855 := bstep (se 1 (by rfl) ⟨10577141, by rfl⟩ : syracuseStep 14102855 = 21154283) B21154283
theorem B21164489 : Blo 1831617 21164489 := bstep (se 2 (by rfl) ⟨7936683, by rfl⟩ : syracuseStep 21164489 = 15873367) B15873367
theorem B1831663 : Blo 1831617 1831663 := bstep (se 1 (by rfl) ⟨1373747, by rfl⟩ : syracuseStep 1831663 = 2747495) B2747495
theorem B1831679 : Blo 1831617 1831679 := bstep (se 1 (by rfl) ⟨1373759, by rfl⟩ : syracuseStep 1831679 = 2747519) B2747519
theorem B7828265 : Blo 1831617 7828265 := bstep (se 2 (by rfl) ⟨2935599, by rfl⟩ : syracuseStep 7828265 = 5871199) B5871199
theorem B3478393 : Blo 1831617 3478393 := bstep (se 2 (by rfl) ⟨1304397, by rfl⟩ : syracuseStep 3478393 = 2608795) B2608795
theorem B2749307 : Blo 1831617 2749307 := bstep (se 1 (by rfl) ⟨2061980, by rfl⟩ : syracuseStep 2749307 = 4123961) B4123961
theorem B15660013 : Blo 1831617 15660013 := bstep (se 3 (by rfl) ⟨2936252, by rfl⟩ : syracuseStep 15660013 = 5872505) B5872505
theorem B1831935 : Blo 1831617 1831935 := bstep (se 1 (by rfl) ⟨1373951, by rfl⟩ : syracuseStep 1831935 = 2747903) B2747903
theorem B3093599 : Blo 1831617 3093599 := bstep (se 1 (by rfl) ⟨2320199, by rfl⟩ : syracuseStep 3093599 = 4640399) B4640399
theorem B4953275 : Blo 1831617 4953275 := bstep (se 1 (by rfl) ⟨3714956, by rfl⟩ : syracuseStep 4953275 = 7429913) B7429913
theorem B1832399 : Blo 1831617 1832399 := bstep (se 1 (by rfl) ⟨1374299, by rfl⟩ : syracuseStep 1832399 = 2748599) B2748599
theorem B9279035 : Blo 1831617 9279035 := bstep (se 1 (by rfl) ⟨6959276, by rfl⟩ : syracuseStep 9279035 = 13918553) B13918553
theorem B21149839 : Blo 1831617 21149839 := bstep (se 1 (by rfl) ⟨15862379, by rfl⟩ : syracuseStep 21149839 = 31724759) B31724759
theorem B1833167 : Blo 1831617 1833167 := bstep (se 1 (by rfl) ⟨1374875, by rfl⟩ : syracuseStep 1833167 = 2749751) B2749751
theorem B5953823 : Blo 1831617 5953823 := bstep (se 1 (by rfl) ⟨4465367, by rfl⟩ : syracuseStep 5953823 = 8930735) B8930735
theorem B11295071 : Blo 1831617 11295071 := bstep (se 1 (by rfl) ⟨8471303, by rfl⟩ : syracuseStep 11295071 = 16942607) B16942607
theorem B1833583 : Blo 1831617 1833583 := bstep (se 1 (by rfl) ⟨1375187, by rfl⟩ : syracuseStep 1833583 = 2750375) B2750375
theorem B1833599 : Blo 1831617 1833599 := bstep (se 1 (by rfl) ⟨1375199, by rfl⟩ : syracuseStep 1833599 = 2750399) B2750399
theorem B10435817 : Blo 1831617 10435817 := bstep (se 2 (by rfl) ⟨3913431, by rfl⟩ : syracuseStep 10435817 = 7826863) B7826863
theorem B28212467 : Blo 1831617 28212467 := bstep (se 1 (by rfl) ⟨21159350, by rfl⟩ : syracuseStep 28212467 = 42318701) B42318701
theorem B5217659 : Blo 1831617 5217659 := bstep (se 1 (by rfl) ⟨3913244, by rfl⟩ : syracuseStep 5217659 = 7826489) B7826489
theorem B16711201 : Blo 1831617 16711201 := bstep (se 2 (by rfl) ⟨6266700, by rfl⟩ : syracuseStep 16711201 = 12533401) B12533401
theorem B5873417 : Blo 1831617 5873417 := bstep (se 2 (by rfl) ⟨2202531, by rfl⟩ : syracuseStep 5873417 = 4405063) B4405063
theorem B6185159 : Blo 1831617 6185159 := bstep (se 1 (by rfl) ⟨4638869, by rfl⟩ : syracuseStep 6185159 = 9277739) B9277739
theorem B31326587 : Blo 1831617 31326587 := bstep (se 1 (by rfl) ⟨23494940, by rfl⟩ : syracuseStep 31326587 = 46989881) B46989881
theorem B5218843 : Blo 1831617 5218843 := bstep (se 1 (by rfl) ⟨3914132, by rfl⟩ : syracuseStep 5218843 = 7828265) B7828265
theorem B14303951 : Blo 1831617 14303951 := bstep (se 1 (by rfl) ⟨10727963, by rfl⟩ : syracuseStep 14303951 = 21455927) B21455927
theorem B3302183 : Blo 1831617 3302183 := bstep (se 1 (by rfl) ⟨2476637, by rfl⟩ : syracuseStep 3302183 = 4953275) B4953275
theorem B6186023 : Blo 1831617 6186023 := bstep (se 1 (by rfl) ⟨4639517, by rfl⟩ : syracuseStep 6186023 = 9279035) B9279035
theorem B4637857 : Blo 1831617 4637857 := bstep (se 2 (by rfl) ⟨1739196, by rfl⟩ : syracuseStep 4637857 = 3478393) B3478393
theorem B7530047 : Blo 1831617 7530047 := bstep (se 1 (by rfl) ⟨5647535, by rfl⟩ : syracuseStep 7530047 = 11295071) B11295071
theorem B6957211 : Blo 1831617 6957211 := bstep (se 1 (by rfl) ⟨5217908, by rfl⟩ : syracuseStep 6957211 = 10435817) B10435817
theorem B13912235 : Blo 1831617 13912235 := bstep (se 1 (by rfl) ⟨10434176, by rfl⟩ : syracuseStep 13912235 = 20868353) B20868353
theorem B4238057 : Blo 1831617 4238057 := bstep (se 2 (by rfl) ⟨1589271, by rfl⟩ : syracuseStep 4238057 = 3178543) B3178543
theorem B16952075 : Blo 1831617 16952075 := bstep (se 1 (by rfl) ⟨12714056, by rfl⟩ : syracuseStep 16952075 = 25428113) B25428113
theorem B4123475 : Blo 1831617 4123475 := bstep (se 1 (by rfl) ⟨3092606, by rfl⟩ : syracuseStep 4123475 = 6185213) B6185213
theorem B14109659 : Blo 1831617 14109659 := bstep (se 1 (by rfl) ⟨10582244, by rfl⟩ : syracuseStep 14109659 = 21164489) B21164489
theorem B112799141 : Blo 1831617 112799141 := bstep (se 4 (by rfl) ⟨10574919, by rfl⟩ : syracuseStep 112799141 = 21149839) B21149839
theorem B267570701 : Blo 1831617 267570701 := bstep (se 3 (by rfl) ⟨50169506, by rfl⟩ : syracuseStep 267570701 = 100339013) B100339013
theorem B2748443 : Blo 1831617 2748443 := bstep (se 1 (by rfl) ⟨2061332, by rfl⟩ : syracuseStep 2748443 = 4122665) B4122665
theorem B3969215 : Blo 1831617 3969215 := bstep (se 1 (by rfl) ⟨2976911, by rfl⟩ : syracuseStep 3969215 = 5953823) B5953823
theorem B105697709 : Blo 1831617 105697709 := bstep (se 3 (by rfl) ⟨19818320, by rfl⟩ : syracuseStep 105697709 = 39636641) B39636641
theorem B44577211 : Blo 1831617 44577211 := bstep (se 1 (by rfl) ⟨33432908, by rfl⟩ : syracuseStep 44577211 = 66865817) B66865817
theorem B3478439 : Blo 1831617 3478439 := bstep (se 1 (by rfl) ⟨2608829, by rfl⟩ : syracuseStep 3478439 = 5217659) B5217659
theorem B1832039 : Blo 1831617 1832039 := bstep (se 1 (by rfl) ⟨1374029, by rfl⟩ : syracuseStep 1832039 = 2748059) B2748059
theorem B39646331 : Blo 1831617 39646331 := bstep (se 1 (by rfl) ⟨29734748, by rfl⟩ : syracuseStep 39646331 = 59469497) B59469497
theorem B3093673 : Blo 1831617 3093673 := bstep (se 2 (by rfl) ⟨1160127, by rfl⟩ : syracuseStep 3093673 = 2320255) B2320255
theorem B1832159 : Blo 1831617 1832159 := bstep (se 1 (by rfl) ⟨1374119, by rfl⟩ : syracuseStep 1832159 = 2748239) B2748239
theorem B126915983 : Blo 1831617 126915983 := bstep (se 1 (by rfl) ⟨95186987, by rfl⟩ : syracuseStep 126915983 = 190373975) B190373975
theorem B9401903 : Blo 1831617 9401903 := bstep (se 1 (by rfl) ⟨7051427, by rfl⟩ : syracuseStep 9401903 = 14102855) B14102855
theorem B6182675 : Blo 1831617 6182675 := bstep (se 1 (by rfl) ⟨4637006, by rfl⟩ : syracuseStep 6182675 = 9274013) B9274013
theorem B1832871 : Blo 1831617 1832871 := bstep (se 1 (by rfl) ⟨1374653, by rfl⟩ : syracuseStep 1832871 = 2749307) B2749307
theorem B75233245 : Blo 1831617 75233245 := bstep (se 3 (by rfl) ⟨14106233, by rfl⟩ : syracuseStep 75233245 = 28212467) B28212467
theorem B2062399 : Blo 1831617 2062399 := bstep (se 1 (by rfl) ⟨1546799, by rfl⟩ : syracuseStep 2062399 = 3093599) B3093599
theorem B23795963 : Blo 1831617 23795963 := bstep (se 1 (by rfl) ⟨17846972, by rfl⟩ : syracuseStep 23795963 = 35693945) B35693945
theorem B20880017 : Blo 1831617 20880017 := bstep (se 2 (by rfl) ⟨7830006, by rfl⟩ : syracuseStep 20880017 = 15660013) B15660013
theorem B13917095 : Blo 1831617 13917095 := bstep (se 1 (by rfl) ⟨10437821, by rfl⟩ : syracuseStep 13917095 = 20875643) B20875643
theorem B3480671 : Blo 1831617 3480671 := bstep (se 1 (by rfl) ⟨2610503, by rfl⟩ : syracuseStep 3480671 = 5221007) B5221007
theorem B7052627 : Blo 1831617 7052627 := bstep (se 1 (by rfl) ⟨5289470, by rfl⟩ : syracuseStep 7052627 = 10578941) B10578941
theorem B22281601 : Blo 1831617 22281601 := bstep (se 2 (by rfl) ⟨8355600, by rfl⟩ : syracuseStep 22281601 = 16711201) B16711201
theorem B3915611 : Blo 1831617 3915611 := bstep (se 1 (by rfl) ⟨2936708, by rfl⟩ : syracuseStep 3915611 = 5873417) B5873417
theorem B2646143 : Blo 1831617 2646143 := bstep (se 1 (by rfl) ⟨1984607, by rfl⟩ : syracuseStep 2646143 = 3969215) B3969215
theorem B9281789 : Blo 1831617 9281789 := bstep (se 3 (by rfl) ⟨1740335, by rfl⟩ : syracuseStep 9281789 = 3480671) B3480671
theorem B9535967 : Blo 1831617 9535967 := bstep (se 1 (by rfl) ⟨7151975, by rfl⟩ : syracuseStep 9535967 = 14303951) B14303951
theorem B2318959 : Blo 1831617 2318959 := bstep (se 1 (by rfl) ⟨1739219, by rfl⟩ : syracuseStep 2318959 = 3478439) B3478439
theorem B6267935 : Blo 1831617 6267935 := bstep (se 1 (by rfl) ⟨4700951, by rfl⟩ : syracuseStep 6267935 = 9401903) B9401903
theorem B4121783 : Blo 1831617 4121783 := bstep (se 1 (by rfl) ⟨3091337, by rfl⟩ : syracuseStep 4121783 = 6182675) B6182675
theorem B9274823 : Blo 1831617 9274823 := bstep (se 1 (by rfl) ⟨6956117, by rfl⟩ : syracuseStep 9274823 = 13912235) B13912235
theorem B13920011 : Blo 1831617 13920011 := bstep (se 1 (by rfl) ⟨10440008, by rfl⟩ : syracuseStep 13920011 = 20880017) B20880017
theorem B9406439 : Blo 1831617 9406439 := bstep (se 1 (by rfl) ⟨7054829, by rfl⟩ : syracuseStep 9406439 = 14109659) B14109659
theorem B4123439 : Blo 1831617 4123439 := bstep (se 1 (by rfl) ⟨3092579, by rfl⟩ : syracuseStep 4123439 = 6185159) B6185159
theorem B9276281 : Blo 1831617 9276281 := bstep (se 2 (by rfl) ⟨3478605, by rfl⟩ : syracuseStep 9276281 = 6957211) B6957211
theorem B20884391 : Blo 1831617 20884391 := bstep (se 1 (by rfl) ⟨15663293, by rfl⟩ : syracuseStep 20884391 = 31326587) B31326587
theorem B59436281 : Blo 1831617 59436281 := bstep (se 2 (by rfl) ⟨22288605, by rfl⟩ : syracuseStep 59436281 = 44577211) B44577211
theorem B4124015 : Blo 1831617 4124015 := bstep (se 1 (by rfl) ⟨3093011, by rfl⟩ : syracuseStep 4124015 = 6186023) B6186023
theorem B6958457 : Blo 1831617 6958457 := bstep (se 2 (by rfl) ⟨2609421, by rfl⟩ : syracuseStep 6958457 = 5218843) B5218843
theorem B26430887 : Blo 1831617 26430887 := bstep (se 1 (by rfl) ⟨19823165, by rfl⟩ : syracuseStep 26430887 = 39646331) B39646331
theorem B84610655 : Blo 1831617 84610655 := bstep (se 1 (by rfl) ⟨63457991, by rfl⟩ : syracuseStep 84610655 = 126915983) B126915983
theorem B15863975 : Blo 1831617 15863975 := bstep (se 1 (by rfl) ⟨11897981, by rfl⟩ : syracuseStep 15863975 = 23795963) B23795963
theorem B4124897 : Blo 1831617 4124897 := bstep (se 2 (by rfl) ⟨1546836, by rfl⟩ : syracuseStep 4124897 = 3093673) B3093673
theorem B29708801 : Blo 1831617 29708801 := bstep (se 2 (by rfl) ⟨11140800, by rfl⟩ : syracuseStep 29708801 = 22281601) B22281601
theorem B11301383 : Blo 1831617 11301383 := bstep (se 1 (by rfl) ⟨8476037, by rfl⟩ : syracuseStep 11301383 = 16952075) B16952075
theorem B2748983 : Blo 1831617 2748983 := bstep (se 1 (by rfl) ⟨2061737, by rfl⟩ : syracuseStep 2748983 = 4123475) B4123475
theorem B9278063 : Blo 1831617 9278063 := bstep (se 1 (by rfl) ⟨6958547, by rfl⟩ : syracuseStep 9278063 = 13917095) B13917095
theorem B75199427 : Blo 1831617 75199427 := bstep (se 1 (by rfl) ⟨56399570, by rfl⟩ : syracuseStep 75199427 = 112799141) B112799141
theorem B2610407 : Blo 1831617 2610407 := bstep (se 1 (by rfl) ⟨1957805, by rfl⟩ : syracuseStep 2610407 = 3915611) B3915611
theorem B1832295 : Blo 1831617 1832295 := bstep (se 1 (by rfl) ⟨1374221, by rfl⟩ : syracuseStep 1832295 = 2748443) B2748443
theorem B2749865 : Blo 1831617 2749865 := bstep (se 2 (by rfl) ⟨1031199, by rfl⟩ : syracuseStep 2749865 = 2062399) B2062399
theorem B70465139 : Blo 1831617 70465139 := bstep (se 1 (by rfl) ⟨52848854, by rfl⟩ : syracuseStep 70465139 = 105697709) B105697709
theorem B2201455 : Blo 1831617 2201455 := bstep (se 1 (by rfl) ⟨1651091, by rfl⟩ : syracuseStep 2201455 = 3302183) B3302183
theorem B18807005 : Blo 1831617 18807005 := bstep (se 3 (by rfl) ⟨3526313, by rfl⟩ : syracuseStep 18807005 = 7052627) B7052627
theorem B5020031 : Blo 1831617 5020031 := bstep (se 1 (by rfl) ⟨3765023, by rfl⟩ : syracuseStep 5020031 = 7530047) B7530047
theorem B6183809 : Blo 1831617 6183809 := bstep (se 2 (by rfl) ⟨2318928, by rfl⟩ : syracuseStep 6183809 = 4637857) B4637857
theorem B2825371 : Blo 1831617 2825371 := bstep (se 1 (by rfl) ⟨2119028, by rfl⟩ : syracuseStep 2825371 = 4238057) B4238057
theorem B178380467 : Blo 1831617 178380467 := bstep (se 1 (by rfl) ⟨133785350, by rfl⟩ : syracuseStep 178380467 = 267570701) B267570701
theorem B100310993 : Blo 1831617 100310993 := bstep (se 2 (by rfl) ⟨37616622, by rfl⟩ : syracuseStep 100310993 = 75233245) B75233245
theorem B10575983 : Blo 1831617 10575983 := bstep (se 1 (by rfl) ⟨7931987, by rfl⟩ : syracuseStep 10575983 = 15863975) B15863975
theorem B6357311 : Blo 1831617 6357311 := bstep (se 1 (by rfl) ⟨4767983, by rfl⟩ : syracuseStep 6357311 = 9535967) B9535967
theorem B6185375 : Blo 1831617 6185375 := bstep (se 1 (by rfl) ⟨4639031, by rfl⟩ : syracuseStep 6185375 = 9278063) B9278063
theorem B4178623 : Blo 1831617 4178623 := bstep (se 1 (by rfl) ⟨3133967, by rfl⟩ : syracuseStep 4178623 = 6267935) B6267935
theorem B4122539 : Blo 1831617 4122539 := bstep (se 1 (by rfl) ⟨3091904, by rfl⟩ : syracuseStep 4122539 = 6183809) B6183809
theorem B4638971 : Blo 1831617 4638971 := bstep (se 1 (by rfl) ⟨3479228, by rfl⟩ : syracuseStep 4638971 = 6958457) B6958457
theorem B2935273 : Blo 1831617 2935273 := bstep (se 2 (by rfl) ⟨1100727, by rfl⟩ : syracuseStep 2935273 = 2201455) B2201455
theorem B66873995 : Blo 1831617 66873995 := bstep (se 1 (by rfl) ⟨50155496, by rfl⟩ : syracuseStep 66873995 = 100310993) B100310993
theorem B6187859 : Blo 1831617 6187859 := bstep (se 1 (by rfl) ⟨4640894, by rfl⟩ : syracuseStep 6187859 = 9281789) B9281789
theorem B2747855 : Blo 1831617 2747855 := bstep (se 1 (by rfl) ⟨2060891, by rfl⟩ : syracuseStep 2747855 = 4121783) B4121783
theorem B15068645 : Blo 1831617 15068645 := bstep (se 4 (by rfl) ⟨1412685, by rfl⟩ : syracuseStep 15068645 = 2825371) B2825371
theorem B3091945 : Blo 1831617 3091945 := bstep (se 2 (by rfl) ⟨1159479, by rfl⟩ : syracuseStep 3091945 = 2318959) B2318959
theorem B46976759 : Blo 1831617 46976759 := bstep (se 1 (by rfl) ⟨35232569, by rfl⟩ : syracuseStep 46976759 = 70465139) B70465139
theorem B6270959 : Blo 1831617 6270959 := bstep (se 1 (by rfl) ⟨4703219, by rfl⟩ : syracuseStep 6270959 = 9406439) B9406439
theorem B28225525 : Blo 1831617 28225525 := bstep (se 5 (by rfl) ⟨1323071, by rfl⟩ : syracuseStep 28225525 = 2646143) B2646143
theorem B12538003 : Blo 1831617 12538003 := bstep (se 1 (by rfl) ⟨9403502, by rfl⟩ : syracuseStep 12538003 = 18807005) B18807005
theorem B3346687 : Blo 1831617 3346687 := bstep (se 1 (by rfl) ⟨2510015, by rfl⟩ : syracuseStep 3346687 = 5020031) B5020031
theorem B2748959 : Blo 1831617 2748959 := bstep (se 1 (by rfl) ⟨2061719, by rfl⟩ : syracuseStep 2748959 = 4123439) B4123439
theorem B13922927 : Blo 1831617 13922927 := bstep (se 1 (by rfl) ⟨10442195, by rfl⟩ : syracuseStep 13922927 = 20884391) B20884391
theorem B2749343 : Blo 1831617 2749343 := bstep (se 1 (by rfl) ⟨2062007, by rfl⟩ : syracuseStep 2749343 = 4124015) B4124015
theorem B56407103 : Blo 1831617 56407103 := bstep (se 1 (by rfl) ⟨42305327, by rfl⟩ : syracuseStep 56407103 = 84610655) B84610655
theorem B118920311 : Blo 1831617 118920311 := bstep (se 1 (by rfl) ⟨89190233, by rfl⟩ : syracuseStep 118920311 = 178380467) B178380467
theorem B2749931 : Blo 1831617 2749931 := bstep (se 1 (by rfl) ⟨2062448, by rfl⟩ : syracuseStep 2749931 = 4124897) B4124897
theorem B19805867 : Blo 1831617 19805867 := bstep (se 1 (by rfl) ⟨14854400, by rfl⟩ : syracuseStep 19805867 = 29708801) B29708801
theorem B1832655 : Blo 1831617 1832655 := bstep (se 1 (by rfl) ⟨1374491, by rfl⟩ : syracuseStep 1832655 = 2748983) B2748983
theorem B6961085 : Blo 1831617 6961085 := bstep (se 3 (by rfl) ⟨1305203, by rfl⟩ : syracuseStep 6961085 = 2610407) B2610407
theorem B50132951 : Blo 1831617 50132951 := bstep (se 1 (by rfl) ⟨37599713, by rfl⟩ : syracuseStep 50132951 = 75199427) B75199427
theorem B1833243 : Blo 1831617 1833243 := bstep (se 1 (by rfl) ⟨1374932, by rfl⟩ : syracuseStep 1833243 = 2749865) B2749865
theorem B6183215 : Blo 1831617 6183215 := bstep (se 1 (by rfl) ⟨4637411, by rfl⟩ : syracuseStep 6183215 = 9274823) B9274823
theorem B9280007 : Blo 1831617 9280007 := bstep (se 1 (by rfl) ⟨6960005, by rfl⟩ : syracuseStep 9280007 = 13920011) B13920011
theorem B30137021 : Blo 1831617 30137021 := bstep (se 3 (by rfl) ⟨5650691, by rfl⟩ : syracuseStep 30137021 = 11301383) B11301383
theorem B6184187 : Blo 1831617 6184187 := bstep (se 1 (by rfl) ⟨4638140, by rfl⟩ : syracuseStep 6184187 = 9276281) B9276281
theorem B39624187 : Blo 1831617 39624187 := bstep (se 1 (by rfl) ⟨29718140, by rfl⟩ : syracuseStep 39624187 = 59436281) B59436281
theorem B17620591 : Blo 1831617 17620591 := bstep (se 1 (by rfl) ⟨13215443, by rfl⟩ : syracuseStep 17620591 = 26430887) B26430887
theorem B9281951 : Blo 1831617 9281951 := bstep (se 1 (by rfl) ⟨6961463, by rfl⟩ : syracuseStep 9281951 = 13922927) B13922927
theorem B5571497 : Blo 1831617 5571497 := bstep (se 2 (by rfl) ⟨2089311, by rfl⟩ : syracuseStep 5571497 = 4178623) B4178623
theorem B4122143 : Blo 1831617 4122143 := bstep (se 1 (by rfl) ⟨3091607, by rfl⟩ : syracuseStep 4122143 = 6183215) B6183215
theorem B6186671 : Blo 1831617 6186671 := bstep (se 1 (by rfl) ⟨4640003, by rfl⟩ : syracuseStep 6186671 = 9280007) B9280007
theorem B44582663 : Blo 1831617 44582663 := bstep (se 1 (by rfl) ⟨33436997, by rfl⟩ : syracuseStep 44582663 = 66873995) B66873995
theorem B4122593 : Blo 1831617 4122593 := bstep (se 2 (by rfl) ⟨1545972, by rfl⟩ : syracuseStep 4122593 = 3091945) B3091945
theorem B52832249 : Blo 1831617 52832249 := bstep (se 2 (by rfl) ⟨19812093, by rfl⟩ : syracuseStep 52832249 = 39624187) B39624187
theorem B4122791 : Blo 1831617 4122791 := bstep (se 1 (by rfl) ⟨3092093, by rfl⟩ : syracuseStep 4122791 = 6184187) B6184187
theorem B10045763 : Blo 1831617 10045763 := bstep (se 1 (by rfl) ⟨7534322, by rfl⟩ : syracuseStep 10045763 = 15068645) B15068645
theorem B4180639 : Blo 1831617 4180639 := bstep (se 1 (by rfl) ⟨3135479, by rfl⟩ : syracuseStep 4180639 = 6270959) B6270959
theorem B4238207 : Blo 1831617 4238207 := bstep (se 1 (by rfl) ⟨3178655, by rfl⟩ : syracuseStep 4238207 = 6357311) B6357311
theorem B4123583 : Blo 1831617 4123583 := bstep (se 1 (by rfl) ⟨3092687, by rfl⟩ : syracuseStep 4123583 = 6185375) B6185375
theorem B37604735 : Blo 1831617 37604735 := bstep (se 1 (by rfl) ⟨28203551, by rfl⟩ : syracuseStep 37604735 = 56407103) B56407103
theorem B2748359 : Blo 1831617 2748359 := bstep (se 1 (by rfl) ⟨2061269, by rfl⟩ : syracuseStep 2748359 = 4122539) B4122539
theorem B4640723 : Blo 1831617 4640723 := bstep (se 1 (by rfl) ⟨3480542, by rfl⟩ : syracuseStep 4640723 = 6961085) B6961085
theorem B3092647 : Blo 1831617 3092647 := bstep (se 1 (by rfl) ⟨2319485, by rfl⟩ : syracuseStep 3092647 = 4638971) B4638971
theorem B20091347 : Blo 1831617 20091347 := bstep (se 1 (by rfl) ⟨15068510, by rfl⟩ : syracuseStep 20091347 = 30137021) B30137021
theorem B4125239 : Blo 1831617 4125239 := bstep (se 1 (by rfl) ⟨3093929, by rfl⟩ : syracuseStep 4125239 = 6187859) B6187859
theorem B1831903 : Blo 1831617 1831903 := bstep (se 1 (by rfl) ⟨1373927, by rfl⟩ : syracuseStep 1831903 = 2747855) B2747855
theorem B7050655 : Blo 1831617 7050655 := bstep (se 1 (by rfl) ⟨5287991, by rfl⟩ : syracuseStep 7050655 = 10575983) B10575983
theorem B16717337 : Blo 1831617 16717337 := bstep (se 2 (by rfl) ⟨6269001, by rfl⟩ : syracuseStep 16717337 = 12538003) B12538003
theorem B4462249 : Blo 1831617 4462249 := bstep (se 2 (by rfl) ⟨1673343, by rfl⟩ : syracuseStep 4462249 = 3346687) B3346687
theorem B1832639 : Blo 1831617 1832639 := bstep (se 1 (by rfl) ⟨1374479, by rfl⟩ : syracuseStep 1832639 = 2748959) B2748959
theorem B1832895 : Blo 1831617 1832895 := bstep (se 1 (by rfl) ⟨1374671, by rfl⟩ : syracuseStep 1832895 = 2749343) B2749343
theorem B3913697 : Blo 1831617 3913697 := bstep (se 2 (by rfl) ⟨1467636, by rfl⟩ : syracuseStep 3913697 = 2935273) B2935273
theorem B79280207 : Blo 1831617 79280207 := bstep (se 1 (by rfl) ⟨59460155, by rfl⟩ : syracuseStep 79280207 = 118920311) B118920311
theorem B1833287 : Blo 1831617 1833287 := bstep (se 1 (by rfl) ⟨1374965, by rfl⟩ : syracuseStep 1833287 = 2749931) B2749931
theorem B13203911 : Blo 1831617 13203911 := bstep (se 1 (by rfl) ⟨9902933, by rfl⟩ : syracuseStep 13203911 = 19805867) B19805867
theorem B33421967 : Blo 1831617 33421967 := bstep (se 1 (by rfl) ⟨25066475, by rfl⟩ : syracuseStep 33421967 = 50132951) B50132951
theorem B23494121 : Blo 1831617 23494121 := bstep (se 2 (by rfl) ⟨8810295, by rfl⟩ : syracuseStep 23494121 = 17620591) B17620591
theorem B31317839 : Blo 1831617 31317839 := bstep (se 1 (by rfl) ⟨23488379, by rfl⟩ : syracuseStep 31317839 = 46976759) B46976759
theorem B37634033 : Blo 1831617 37634033 := bstep (se 2 (by rfl) ⟨14112762, by rfl⟩ : syracuseStep 37634033 = 28225525) B28225525
theorem B13394231 : Blo 1831617 13394231 := bstep (se 1 (by rfl) ⟨10045673, by rfl⟩ : syracuseStep 13394231 = 20091347) B20091347
theorem B29721775 : Blo 1831617 29721775 := bstep (se 1 (by rfl) ⟨22291331, by rfl⟩ : syracuseStep 29721775 = 44582663) B44582663
theorem B5949665 : Blo 1831617 5949665 := bstep (se 2 (by rfl) ⟨2231124, by rfl⟩ : syracuseStep 5949665 = 4462249) B4462249
theorem B25069823 : Blo 1831617 25069823 := bstep (se 1 (by rfl) ⟨18802367, by rfl⟩ : syracuseStep 25069823 = 37604735) B37604735
theorem B4123529 : Blo 1831617 4123529 := bstep (se 2 (by rfl) ⟨1546323, by rfl⟩ : syracuseStep 4123529 = 3092647) B3092647
theorem B6187967 : Blo 1831617 6187967 := bstep (se 1 (by rfl) ⟨4640975, by rfl⟩ : syracuseStep 6187967 = 9281951) B9281951
theorem B3714331 : Blo 1831617 3714331 := bstep (se 1 (by rfl) ⟨2785748, by rfl⟩ : syracuseStep 3714331 = 5571497) B5571497
theorem B5574185 : Blo 1831617 5574185 := bstep (se 2 (by rfl) ⟨2090319, by rfl⟩ : syracuseStep 5574185 = 4180639) B4180639
theorem B11144891 : Blo 1831617 11144891 := bstep (se 1 (by rfl) ⟨8358668, by rfl⟩ : syracuseStep 11144891 = 16717337) B16717337
theorem B2748095 : Blo 1831617 2748095 := bstep (se 1 (by rfl) ⟨2061071, by rfl⟩ : syracuseStep 2748095 = 4122143) B4122143
theorem B4124447 : Blo 1831617 4124447 := bstep (se 1 (by rfl) ⟨3093335, by rfl⟩ : syracuseStep 4124447 = 6186671) B6186671
theorem B2748395 : Blo 1831617 2748395 := bstep (se 1 (by rfl) ⟨2061296, by rfl⟩ : syracuseStep 2748395 = 4122593) B4122593
theorem B35221499 : Blo 1831617 35221499 := bstep (se 1 (by rfl) ⟨26416124, by rfl⟩ : syracuseStep 35221499 = 52832249) B52832249
theorem B2748527 : Blo 1831617 2748527 := bstep (se 1 (by rfl) ⟨2061395, by rfl⟩ : syracuseStep 2748527 = 4122791) B4122791
theorem B6697175 : Blo 1831617 6697175 := bstep (se 1 (by rfl) ⟨5022881, by rfl⟩ : syracuseStep 6697175 = 10045763) B10045763
theorem B8802607 : Blo 1831617 8802607 := bstep (se 1 (by rfl) ⟨6601955, by rfl⟩ : syracuseStep 8802607 = 13203911) B13203911
theorem B9400873 : Blo 1831617 9400873 := bstep (se 2 (by rfl) ⟨3525327, by rfl⟩ : syracuseStep 9400873 = 7050655) B7050655
theorem B2749055 : Blo 1831617 2749055 := bstep (se 1 (by rfl) ⟨2061791, by rfl⟩ : syracuseStep 2749055 = 4123583) B4123583
theorem B20878559 : Blo 1831617 20878559 := bstep (se 1 (by rfl) ⟨15658919, by rfl⟩ : syracuseStep 20878559 = 31317839) B31317839
theorem B1832239 : Blo 1831617 1832239 := bstep (se 1 (by rfl) ⟨1374179, by rfl⟩ : syracuseStep 1832239 = 2748359) B2748359
theorem B3093815 : Blo 1831617 3093815 := bstep (se 1 (by rfl) ⟨2320361, by rfl⟩ : syracuseStep 3093815 = 4640723) B4640723
theorem B25089355 : Blo 1831617 25089355 := bstep (se 1 (by rfl) ⟨18817016, by rfl⟩ : syracuseStep 25089355 = 37634033) B37634033
theorem B2750159 : Blo 1831617 2750159 := bstep (se 1 (by rfl) ⟨2062619, by rfl⟩ : syracuseStep 2750159 = 4125239) B4125239
theorem B52853471 : Blo 1831617 52853471 := bstep (se 1 (by rfl) ⟨39640103, by rfl⟩ : syracuseStep 52853471 = 79280207) B79280207
theorem B22281311 : Blo 1831617 22281311 := bstep (se 1 (by rfl) ⟨16710983, by rfl⟩ : syracuseStep 22281311 = 33421967) B33421967
theorem B2825471 : Blo 1831617 2825471 := bstep (se 1 (by rfl) ⟨2119103, by rfl⟩ : syracuseStep 2825471 = 4238207) B4238207
theorem B15662747 : Blo 1831617 15662747 := bstep (se 1 (by rfl) ⟨11747060, by rfl⟩ : syracuseStep 15662747 = 23494121) B23494121
theorem B10436525 : Blo 1831617 10436525 := bstep (se 3 (by rfl) ⟨1956848, by rfl⟩ : syracuseStep 10436525 = 3913697) B3913697
theorem B8929487 : Blo 1831617 8929487 := bstep (se 1 (by rfl) ⟨6697115, by rfl⟩ : syracuseStep 8929487 = 13394231) B13394231
theorem B17859133 : Blo 1831617 17859133 := bstep (se 3 (by rfl) ⟨3348587, by rfl⟩ : syracuseStep 17859133 = 6697175) B6697175
theorem B12534497 : Blo 1831617 12534497 := bstep (se 2 (by rfl) ⟨4700436, by rfl⟩ : syracuseStep 12534497 = 9400873) B9400873
theorem B13919039 : Blo 1831617 13919039 := bstep (se 1 (by rfl) ⟨10439279, by rfl⟩ : syracuseStep 13919039 = 20878559) B20878559
theorem B3966443 : Blo 1831617 3966443 := bstep (se 1 (by rfl) ⟨2974832, by rfl⟩ : syracuseStep 3966443 = 5949665) B5949665
theorem B16713215 : Blo 1831617 16713215 := bstep (se 1 (by rfl) ⟨12534911, by rfl⟩ : syracuseStep 16713215 = 25069823) B25069823
theorem B35235647 : Blo 1831617 35235647 := bstep (se 1 (by rfl) ⟨26426735, by rfl⟩ : syracuseStep 35235647 = 52853471) B52853471
theorem B14854207 : Blo 1831617 14854207 := bstep (se 1 (by rfl) ⟨11140655, by rfl⟩ : syracuseStep 14854207 = 22281311) B22281311
theorem B6957683 : Blo 1831617 6957683 := bstep (se 1 (by rfl) ⟨5218262, by rfl⟩ : syracuseStep 6957683 = 10436525) B10436525
theorem B23480999 : Blo 1831617 23480999 := bstep (se 1 (by rfl) ⟨17610749, by rfl⟩ : syracuseStep 23480999 = 35221499) B35221499
theorem B39629033 : Blo 1831617 39629033 := bstep (se 2 (by rfl) ⟨14860887, by rfl⟩ : syracuseStep 39629033 = 29721775) B29721775
theorem B4952441 : Blo 1831617 4952441 := bstep (se 2 (by rfl) ⟨1857165, by rfl⟩ : syracuseStep 4952441 = 3714331) B3714331
theorem B33452473 : Blo 1831617 33452473 := bstep (se 2 (by rfl) ⟨12544677, by rfl⟩ : syracuseStep 33452473 = 25089355) B25089355
theorem B2749019 : Blo 1831617 2749019 := bstep (se 1 (by rfl) ⟨2061764, by rfl⟩ : syracuseStep 2749019 = 4123529) B4123529
theorem B4125311 : Blo 1831617 4125311 := bstep (se 1 (by rfl) ⟨3093983, by rfl⟩ : syracuseStep 4125311 = 6187967) B6187967
theorem B3716123 : Blo 1831617 3716123 := bstep (se 1 (by rfl) ⟨2787092, by rfl⟩ : syracuseStep 3716123 = 5574185) B5574185
theorem B10441831 : Blo 1831617 10441831 := bstep (se 1 (by rfl) ⟨7831373, by rfl⟩ : syracuseStep 10441831 = 15662747) B15662747
theorem B1832063 : Blo 1831617 1832063 := bstep (se 1 (by rfl) ⟨1374047, by rfl⟩ : syracuseStep 1832063 = 2748095) B2748095
theorem B2749631 : Blo 1831617 2749631 := bstep (se 1 (by rfl) ⟨2062223, by rfl⟩ : syracuseStep 2749631 = 4124447) B4124447
theorem B1832263 : Blo 1831617 1832263 := bstep (se 1 (by rfl) ⟨1374197, by rfl⟩ : syracuseStep 1832263 = 2748395) B2748395
theorem B1832351 : Blo 1831617 1832351 := bstep (se 1 (by rfl) ⟨1374263, by rfl⟩ : syracuseStep 1832351 = 2748527) B2748527
theorem B11736809 : Blo 1831617 11736809 := bstep (se 2 (by rfl) ⟨4401303, by rfl⟩ : syracuseStep 11736809 = 8802607) B8802607
theorem B1832703 : Blo 1831617 1832703 := bstep (se 1 (by rfl) ⟨1374527, by rfl⟩ : syracuseStep 1832703 = 2749055) B2749055
theorem B2062543 : Blo 1831617 2062543 := bstep (se 1 (by rfl) ⟨1546907, by rfl⟩ : syracuseStep 2062543 = 3093815) B3093815
theorem B1833439 : Blo 1831617 1833439 := bstep (se 1 (by rfl) ⟨1375079, by rfl⟩ : syracuseStep 1833439 = 2750159) B2750159
theorem B1883647 : Blo 1831617 1883647 := bstep (se 1 (by rfl) ⟨1412735, by rfl⟩ : syracuseStep 1883647 = 2825471) B2825471
theorem B7429927 : Blo 1831617 7429927 := bstep (se 1 (by rfl) ⟨5572445, by rfl⟩ : syracuseStep 7429927 = 11144891) B11144891
theorem B26419355 : Blo 1831617 26419355 := bstep (se 1 (by rfl) ⟨19814516, by rfl⟩ : syracuseStep 26419355 = 39629033) B39629033
theorem B8356331 : Blo 1831617 8356331 := bstep (se 1 (by rfl) ⟨6267248, by rfl⟩ : syracuseStep 8356331 = 12534497) B12534497
theorem B13206509 : Blo 1831617 13206509 := bstep (se 3 (by rfl) ⟨2476220, by rfl⟩ : syracuseStep 13206509 = 4952441) B4952441
theorem B11142143 : Blo 1831617 11142143 := bstep (se 1 (by rfl) ⟨8356607, by rfl⟩ : syracuseStep 11142143 = 16713215) B16713215
theorem B7824539 : Blo 1831617 7824539 := bstep (se 1 (by rfl) ⟨5868404, by rfl⟩ : syracuseStep 7824539 = 11736809) B11736809
theorem B4638455 : Blo 1831617 4638455 := bstep (se 1 (by rfl) ⟨3478841, by rfl⟩ : syracuseStep 4638455 = 6957683) B6957683
theorem B9906569 : Blo 1831617 9906569 := bstep (se 2 (by rfl) ⟨3714963, by rfl⟩ : syracuseStep 9906569 = 7429927) B7429927
theorem B23490431 : Blo 1831617 23490431 := bstep (se 1 (by rfl) ⟨17617823, by rfl⟩ : syracuseStep 23490431 = 35235647) B35235647
theorem B13922441 : Blo 1831617 13922441 := bstep (se 2 (by rfl) ⟨5220915, by rfl⟩ : syracuseStep 13922441 = 10441831) B10441831
theorem B2511529 : Blo 1831617 2511529 := bstep (se 2 (by rfl) ⟨941823, by rfl⟩ : syracuseStep 2511529 = 1883647) B1883647
theorem B42308725 : Blo 1831617 42308725 := bstep (se 5 (by rfl) ⟨1983221, by rfl⟩ : syracuseStep 42308725 = 3966443) B3966443
theorem B19805609 : Blo 1831617 19805609 := bstep (se 2 (by rfl) ⟨7427103, by rfl⟩ : syracuseStep 19805609 = 14854207) B14854207
theorem B2750057 : Blo 1831617 2750057 := bstep (se 2 (by rfl) ⟨1031271, by rfl⟩ : syracuseStep 2750057 = 2062543) B2062543
theorem B39638645 : Blo 1831617 39638645 := bstep (se 5 (by rfl) ⟨1858061, by rfl⟩ : syracuseStep 39638645 = 3716123) B3716123
theorem B1832679 : Blo 1831617 1832679 := bstep (se 1 (by rfl) ⟨1374509, by rfl⟩ : syracuseStep 1832679 = 2749019) B2749019
theorem B2750207 : Blo 1831617 2750207 := bstep (se 1 (by rfl) ⟨2062655, by rfl⟩ : syracuseStep 2750207 = 4125311) B4125311
theorem B23811965 : Blo 1831617 23811965 := bstep (se 3 (by rfl) ⟨4464743, by rfl⟩ : syracuseStep 23811965 = 8929487) B8929487
theorem B9279359 : Blo 1831617 9279359 := bstep (se 1 (by rfl) ⟨6959519, by rfl⟩ : syracuseStep 9279359 = 13919039) B13919039
theorem B44603297 : Blo 1831617 44603297 := bstep (se 2 (by rfl) ⟨16726236, by rfl⟩ : syracuseStep 44603297 = 33452473) B33452473
theorem B23812177 : Blo 1831617 23812177 := bstep (se 2 (by rfl) ⟨8929566, by rfl⟩ : syracuseStep 23812177 = 17859133) B17859133
theorem B1833087 : Blo 1831617 1833087 := bstep (se 1 (by rfl) ⟨1374815, by rfl⟩ : syracuseStep 1833087 = 2749631) B2749631
theorem B15653999 : Blo 1831617 15653999 := bstep (se 1 (by rfl) ⟨11740499, by rfl⟩ : syracuseStep 15653999 = 23480999) B23480999
theorem B9281627 : Blo 1831617 9281627 := bstep (se 1 (by rfl) ⟨6961220, by rfl⟩ : syracuseStep 9281627 = 13922441) B13922441
theorem B17612903 : Blo 1831617 17612903 := bstep (se 1 (by rfl) ⟨13209677, by rfl⟩ : syracuseStep 17612903 = 26419355) B26419355
theorem B20865437 : Blo 1831617 20865437 := bstep (se 3 (by rfl) ⟨3912269, by rfl⟩ : syracuseStep 20865437 = 7824539) B7824539
theorem B13394821 : Blo 1831617 13394821 := bstep (se 4 (by rfl) ⟨1255764, by rfl⟩ : syracuseStep 13394821 = 2511529) B2511529
theorem B6186239 : Blo 1831617 6186239 := bstep (se 1 (by rfl) ⟨4639679, by rfl⟩ : syracuseStep 6186239 = 9279359) B9279359
theorem B22283549 : Blo 1831617 22283549 := bstep (se 3 (by rfl) ⟨4178165, by rfl⟩ : syracuseStep 22283549 = 8356331) B8356331
theorem B56411633 : Blo 1831617 56411633 := bstep (se 2 (by rfl) ⟨21154362, by rfl⟩ : syracuseStep 56411633 = 42308725) B42308725
theorem B6604379 : Blo 1831617 6604379 := bstep (se 1 (by rfl) ⟨4953284, by rfl⟩ : syracuseStep 6604379 = 9906569) B9906569
theorem B3092303 : Blo 1831617 3092303 := bstep (se 1 (by rfl) ⟨2319227, by rfl⟩ : syracuseStep 3092303 = 4638455) B4638455
theorem B15660287 : Blo 1831617 15660287 := bstep (se 1 (by rfl) ⟨11745215, by rfl⟩ : syracuseStep 15660287 = 23490431) B23490431
theorem B31749569 : Blo 1831617 31749569 := bstep (se 2 (by rfl) ⟨11906088, by rfl⟩ : syracuseStep 31749569 = 23812177) B23812177
theorem B8804339 : Blo 1831617 8804339 := bstep (se 1 (by rfl) ⟨6603254, by rfl⟩ : syracuseStep 8804339 = 13206509) B13206509
theorem B7428095 : Blo 1831617 7428095 := bstep (se 1 (by rfl) ⟨5571071, by rfl⟩ : syracuseStep 7428095 = 11142143) B11142143
theorem B13203739 : Blo 1831617 13203739 := bstep (se 1 (by rfl) ⟨9902804, by rfl⟩ : syracuseStep 13203739 = 19805609) B19805609
theorem B1833371 : Blo 1831617 1833371 := bstep (se 1 (by rfl) ⟨1375028, by rfl⟩ : syracuseStep 1833371 = 2750057) B2750057
theorem B26425763 : Blo 1831617 26425763 := bstep (se 1 (by rfl) ⟨19819322, by rfl⟩ : syracuseStep 26425763 = 39638645) B39638645
theorem B1833471 : Blo 1831617 1833471 := bstep (se 1 (by rfl) ⟨1375103, by rfl⟩ : syracuseStep 1833471 = 2750207) B2750207
theorem B15874643 : Blo 1831617 15874643 := bstep (se 1 (by rfl) ⟨11905982, by rfl⟩ : syracuseStep 15874643 = 23811965) B23811965
theorem B29735531 : Blo 1831617 29735531 := bstep (se 1 (by rfl) ⟨22301648, by rfl⟩ : syracuseStep 29735531 = 44603297) B44603297
theorem B10435999 : Blo 1831617 10435999 := bstep (se 1 (by rfl) ⟨7826999, by rfl⟩ : syracuseStep 10435999 = 15653999) B15653999
theorem B13910291 : Blo 1831617 13910291 := bstep (se 1 (by rfl) ⟨10432718, by rfl⟩ : syracuseStep 13910291 = 20865437) B20865437
theorem B17604985 : Blo 1831617 17604985 := bstep (se 2 (by rfl) ⟨6601869, by rfl⟩ : syracuseStep 17604985 = 13203739) B13203739
theorem B17859761 : Blo 1831617 17859761 := bstep (se 2 (by rfl) ⟨6697410, by rfl⟩ : syracuseStep 17859761 = 13394821) B13394821
theorem B6187751 : Blo 1831617 6187751 := bstep (se 1 (by rfl) ⟨4640813, by rfl⟩ : syracuseStep 6187751 = 9281627) B9281627
theorem B11741935 : Blo 1831617 11741935 := bstep (se 1 (by rfl) ⟨8806451, by rfl⟩ : syracuseStep 11741935 = 17612903) B17612903
theorem B4124159 : Blo 1831617 4124159 := bstep (se 1 (by rfl) ⟨3093119, by rfl⟩ : syracuseStep 4124159 = 6186239) B6186239
theorem B10440191 : Blo 1831617 10440191 := bstep (se 1 (by rfl) ⟨7830143, by rfl⟩ : syracuseStep 10440191 = 15660287) B15660287
theorem B14855699 : Blo 1831617 14855699 := bstep (se 1 (by rfl) ⟨11141774, by rfl⟩ : syracuseStep 14855699 = 22283549) B22283549
theorem B4402919 : Blo 1831617 4402919 := bstep (se 1 (by rfl) ⟨3302189, by rfl⟩ : syracuseStep 4402919 = 6604379) B6604379
theorem B5869559 : Blo 1831617 5869559 := bstep (se 1 (by rfl) ⟨4402169, by rfl⟩ : syracuseStep 5869559 = 8804339) B8804339
theorem B4952063 : Blo 1831617 4952063 := bstep (se 1 (by rfl) ⟨3714047, by rfl⟩ : syracuseStep 4952063 = 7428095) B7428095
theorem B17617175 : Blo 1831617 17617175 := bstep (se 1 (by rfl) ⟨13212881, by rfl⟩ : syracuseStep 17617175 = 26425763) B26425763
theorem B13914665 : Blo 1831617 13914665 := bstep (se 2 (by rfl) ⟨5217999, by rfl⟩ : syracuseStep 13914665 = 10435999) B10435999
theorem B2061535 : Blo 1831617 2061535 := bstep (se 1 (by rfl) ⟨1546151, by rfl⟩ : syracuseStep 2061535 = 3092303) B3092303
theorem B21166379 : Blo 1831617 21166379 := bstep (se 1 (by rfl) ⟨15874784, by rfl⟩ : syracuseStep 21166379 = 31749569) B31749569
theorem B37607755 : Blo 1831617 37607755 := bstep (se 1 (by rfl) ⟨28205816, by rfl⟩ : syracuseStep 37607755 = 56411633) B56411633
theorem B10583095 : Blo 1831617 10583095 := bstep (se 1 (by rfl) ⟨7937321, by rfl⟩ : syracuseStep 10583095 = 15874643) B15874643
theorem B19823687 : Blo 1831617 19823687 := bstep (se 1 (by rfl) ⟨14867765, by rfl⟩ : syracuseStep 19823687 = 29735531) B29735531
theorem B9273527 : Blo 1831617 9273527 := bstep (se 1 (by rfl) ⟨6955145, by rfl⟩ : syracuseStep 9273527 = 13910291) B13910291
theorem B50143673 : Blo 1831617 50143673 := bstep (se 2 (by rfl) ⟨18803877, by rfl⟩ : syracuseStep 50143673 = 37607755) B37607755
theorem B15655913 : Blo 1831617 15655913 := bstep (se 2 (by rfl) ⟨5870967, by rfl⟩ : syracuseStep 15655913 = 11741935) B11741935
theorem B13215791 : Blo 1831617 13215791 := bstep (se 1 (by rfl) ⟨9911843, by rfl⟩ : syracuseStep 13215791 = 19823687) B19823687
theorem B2935279 : Blo 1831617 2935279 := bstep (se 1 (by rfl) ⟨2201459, by rfl⟩ : syracuseStep 2935279 = 4402919) B4402919
theorem B9276443 : Blo 1831617 9276443 := bstep (se 1 (by rfl) ⟨6957332, by rfl⟩ : syracuseStep 9276443 = 13914665) B13914665
theorem B23473313 : Blo 1831617 23473313 := bstep (se 2 (by rfl) ⟨8802492, by rfl⟩ : syracuseStep 23473313 = 17604985) B17604985
theorem B11906507 : Blo 1831617 11906507 := bstep (se 1 (by rfl) ⟨8929880, by rfl⟩ : syracuseStep 11906507 = 17859761) B17859761
theorem B14110793 : Blo 1831617 14110793 := bstep (se 2 (by rfl) ⟨5291547, by rfl⟩ : syracuseStep 14110793 = 10583095) B10583095
theorem B14110919 : Blo 1831617 14110919 := bstep (se 1 (by rfl) ⟨10583189, by rfl⟩ : syracuseStep 14110919 = 21166379) B21166379
theorem B2748713 : Blo 1831617 2748713 := bstep (se 2 (by rfl) ⟨1030767, by rfl⟩ : syracuseStep 2748713 = 2061535) B2061535
theorem B4125167 : Blo 1831617 4125167 := bstep (se 1 (by rfl) ⟨3093875, by rfl⟩ : syracuseStep 4125167 = 6187751) B6187751
theorem B2749439 : Blo 1831617 2749439 := bstep (se 1 (by rfl) ⟨2062079, by rfl⟩ : syracuseStep 2749439 = 4124159) B4124159
theorem B6960127 : Blo 1831617 6960127 := bstep (se 1 (by rfl) ⟨5220095, by rfl⟩ : syracuseStep 6960127 = 10440191) B10440191
theorem B3913039 : Blo 1831617 3913039 := bstep (se 1 (by rfl) ⟨2934779, by rfl⟩ : syracuseStep 3913039 = 5869559) B5869559
theorem B11744783 : Blo 1831617 11744783 := bstep (se 1 (by rfl) ⟨8808587, by rfl⟩ : syracuseStep 11744783 = 17617175) B17617175
theorem B9903799 : Blo 1831617 9903799 := bstep (se 1 (by rfl) ⟨7427849, by rfl⟩ : syracuseStep 9903799 = 14855699) B14855699
theorem B13205501 : Blo 1831617 13205501 := bstep (se 3 (by rfl) ⟨2476031, by rfl⟩ : syracuseStep 13205501 = 4952063) B4952063
theorem B10437275 : Blo 1831617 10437275 := bstep (se 1 (by rfl) ⟨7827956, by rfl⟩ : syracuseStep 10437275 = 15655913) B15655913
theorem B15648875 : Blo 1831617 15648875 := bstep (se 1 (by rfl) ⟨11736656, by rfl⟩ : syracuseStep 15648875 = 23473313) B23473313
theorem B9407195 : Blo 1831617 9407195 := bstep (se 1 (by rfl) ⟨7055396, by rfl⟩ : syracuseStep 9407195 = 14110793) B14110793
theorem B9407279 : Blo 1831617 9407279 := bstep (se 1 (by rfl) ⟨7055459, by rfl⟩ : syracuseStep 9407279 = 14110919) B14110919
theorem B8810527 : Blo 1831617 8810527 := bstep (se 1 (by rfl) ⟨6607895, by rfl⟩ : syracuseStep 8810527 = 13215791) B13215791
theorem B8803667 : Blo 1831617 8803667 := bstep (se 1 (by rfl) ⟨6602750, by rfl⟩ : syracuseStep 8803667 = 13205501) B13205501
theorem B6182351 : Blo 1831617 6182351 := bstep (se 1 (by rfl) ⟨4636763, by rfl⟩ : syracuseStep 6182351 = 9273527) B9273527
theorem B1832475 : Blo 1831617 1832475 := bstep (se 1 (by rfl) ⟨1374356, by rfl⟩ : syracuseStep 1832475 = 2748713) B2748713
theorem B33429115 : Blo 1831617 33429115 := bstep (se 1 (by rfl) ⟨25071836, by rfl⟩ : syracuseStep 33429115 = 50143673) B50143673
theorem B2750111 : Blo 1831617 2750111 := bstep (se 1 (by rfl) ⟨2062583, by rfl⟩ : syracuseStep 2750111 = 4125167) B4125167
theorem B3913705 : Blo 1831617 3913705 := bstep (se 2 (by rfl) ⟨1467639, by rfl⟩ : syracuseStep 3913705 = 2935279) B2935279
theorem B1832959 : Blo 1831617 1832959 := bstep (se 1 (by rfl) ⟨1374719, by rfl⟩ : syracuseStep 1832959 = 2749439) B2749439
theorem B7829855 : Blo 1831617 7829855 := bstep (se 1 (by rfl) ⟨5872391, by rfl⟩ : syracuseStep 7829855 = 11744783) B11744783
theorem B9280169 : Blo 1831617 9280169 := bstep (se 2 (by rfl) ⟨3480063, by rfl⟩ : syracuseStep 9280169 = 6960127) B6960127
theorem B5217385 : Blo 1831617 5217385 := bstep (se 2 (by rfl) ⟨1956519, by rfl⟩ : syracuseStep 5217385 = 3913039) B3913039
theorem B6184295 : Blo 1831617 6184295 := bstep (se 1 (by rfl) ⟨4638221, by rfl⟩ : syracuseStep 6184295 = 9276443) B9276443
theorem B13205065 : Blo 1831617 13205065 := bstep (se 2 (by rfl) ⟨4951899, by rfl⟩ : syracuseStep 13205065 = 9903799) B9903799
theorem B7937671 : Blo 1831617 7937671 := bstep (se 1 (by rfl) ⟨5953253, by rfl⟩ : syracuseStep 7937671 = 11906507) B11906507
theorem B11747369 : Blo 1831617 11747369 := bstep (se 2 (by rfl) ⟨4405263, by rfl⟩ : syracuseStep 11747369 = 8810527) B8810527
theorem B4121567 : Blo 1831617 4121567 := bstep (se 1 (by rfl) ⟨3091175, by rfl⟩ : syracuseStep 4121567 = 6182351) B6182351
theorem B6956513 : Blo 1831617 6956513 := bstep (se 2 (by rfl) ⟨2608692, by rfl⟩ : syracuseStep 6956513 = 5217385) B5217385
theorem B5219903 : Blo 1831617 5219903 := bstep (se 1 (by rfl) ⟨3914927, by rfl⟩ : syracuseStep 5219903 = 7829855) B7829855
theorem B6186779 : Blo 1831617 6186779 := bstep (se 1 (by rfl) ⟨4640084, by rfl⟩ : syracuseStep 6186779 = 9280169) B9280169
theorem B17606753 : Blo 1831617 17606753 := bstep (se 2 (by rfl) ⟨6602532, by rfl⟩ : syracuseStep 17606753 = 13205065) B13205065
theorem B4122863 : Blo 1831617 4122863 := bstep (se 1 (by rfl) ⟨3092147, by rfl⟩ : syracuseStep 4122863 = 6184295) B6184295
theorem B6958183 : Blo 1831617 6958183 := bstep (se 1 (by rfl) ⟨5218637, by rfl⟩ : syracuseStep 6958183 = 10437275) B10437275
theorem B5869111 : Blo 1831617 5869111 := bstep (se 1 (by rfl) ⟨4401833, by rfl⟩ : syracuseStep 5869111 = 8803667) B8803667
theorem B10432583 : Blo 1831617 10432583 := bstep (se 1 (by rfl) ⟨7824437, by rfl⟩ : syracuseStep 10432583 = 15648875) B15648875
theorem B6271463 : Blo 1831617 6271463 := bstep (se 1 (by rfl) ⟨4703597, by rfl⟩ : syracuseStep 6271463 = 9407195) B9407195
theorem B6271519 : Blo 1831617 6271519 := bstep (se 1 (by rfl) ⟨4703639, by rfl⟩ : syracuseStep 6271519 = 9407279) B9407279
theorem B178288613 : Blo 1831617 178288613 := bstep (se 4 (by rfl) ⟨16714557, by rfl⟩ : syracuseStep 178288613 = 33429115) B33429115
theorem B1833407 : Blo 1831617 1833407 := bstep (se 1 (by rfl) ⟨1375055, by rfl⟩ : syracuseStep 1833407 = 2750111) B2750111
theorem B10583561 : Blo 1831617 10583561 := bstep (se 2 (by rfl) ⟨3968835, by rfl⟩ : syracuseStep 10583561 = 7937671) B7937671
theorem B5218273 : Blo 1831617 5218273 := bstep (se 2 (by rfl) ⟨1956852, by rfl⟩ : syracuseStep 5218273 = 3913705) B3913705
theorem B7831579 : Blo 1831617 7831579 := bstep (se 1 (by rfl) ⟨5873684, by rfl⟩ : syracuseStep 7831579 = 11747369) B11747369
theorem B6955055 : Blo 1831617 6955055 := bstep (se 1 (by rfl) ⟨5216291, by rfl⟩ : syracuseStep 6955055 = 10432583) B10432583
theorem B4637675 : Blo 1831617 4637675 := bstep (se 1 (by rfl) ⟨3478256, by rfl⟩ : syracuseStep 4637675 = 6956513) B6956513
theorem B118859075 : Blo 1831617 118859075 := bstep (se 1 (by rfl) ⟨89144306, by rfl⟩ : syracuseStep 118859075 = 178288613) B178288613
theorem B7825481 : Blo 1831617 7825481 := bstep (se 2 (by rfl) ⟨2934555, by rfl⟩ : syracuseStep 7825481 = 5869111) B5869111
theorem B7055707 : Blo 1831617 7055707 := bstep (se 1 (by rfl) ⟨5291780, by rfl⟩ : syracuseStep 7055707 = 10583561) B10583561
theorem B6957697 : Blo 1831617 6957697 := bstep (se 2 (by rfl) ⟨2609136, by rfl⟩ : syracuseStep 6957697 = 5218273) B5218273
theorem B2747711 : Blo 1831617 2747711 := bstep (se 1 (by rfl) ⟨2060783, by rfl⟩ : syracuseStep 2747711 = 4121567) B4121567
theorem B4124519 : Blo 1831617 4124519 := bstep (se 1 (by rfl) ⟨3093389, by rfl⟩ : syracuseStep 4124519 = 6186779) B6186779
theorem B16723901 : Blo 1831617 16723901 := bstep (se 3 (by rfl) ⟨3135731, by rfl⟩ : syracuseStep 16723901 = 6271463) B6271463
theorem B9277577 : Blo 1831617 9277577 := bstep (se 2 (by rfl) ⟨3479091, by rfl⟩ : syracuseStep 9277577 = 6958183) B6958183
theorem B2748575 : Blo 1831617 2748575 := bstep (se 1 (by rfl) ⟨2061431, by rfl⟩ : syracuseStep 2748575 = 4122863) B4122863
theorem B8362025 : Blo 1831617 8362025 := bstep (se 2 (by rfl) ⟨3135759, by rfl⟩ : syracuseStep 8362025 = 6271519) B6271519
theorem B3479935 : Blo 1831617 3479935 := bstep (se 1 (by rfl) ⟨2609951, by rfl⟩ : syracuseStep 3479935 = 5219903) B5219903
theorem B11737835 : Blo 1831617 11737835 := bstep (se 1 (by rfl) ⟨8803376, by rfl⟩ : syracuseStep 11737835 = 17606753) B17606753
theorem B4636703 : Blo 1831617 4636703 := bstep (se 1 (by rfl) ⟨3477527, by rfl⟩ : syracuseStep 4636703 = 6955055) B6955055
theorem B6185051 : Blo 1831617 6185051 := bstep (se 1 (by rfl) ⟨4638788, by rfl⟩ : syracuseStep 6185051 = 9277577) B9277577
theorem B7825223 : Blo 1831617 7825223 := bstep (se 1 (by rfl) ⟨5868917, by rfl⟩ : syracuseStep 7825223 = 11737835) B11737835
theorem B9407609 : Blo 1831617 9407609 := bstep (se 2 (by rfl) ⟨3527853, by rfl⟩ : syracuseStep 9407609 = 7055707) B7055707
theorem B4639913 : Blo 1831617 4639913 := bstep (se 2 (by rfl) ⟨1739967, by rfl⟩ : syracuseStep 4639913 = 3479935) B3479935
theorem B3091783 : Blo 1831617 3091783 := bstep (se 1 (by rfl) ⟨2318837, by rfl⟩ : syracuseStep 3091783 = 4637675) B4637675
theorem B9276929 : Blo 1831617 9276929 := bstep (se 2 (by rfl) ⟨3478848, by rfl⟩ : syracuseStep 9276929 = 6957697) B6957697
theorem B5574683 : Blo 1831617 5574683 := bstep (se 1 (by rfl) ⟨4181012, by rfl⟩ : syracuseStep 5574683 = 8362025) B8362025
theorem B1831807 : Blo 1831617 1831807 := bstep (se 1 (by rfl) ⟨1373855, by rfl⟩ : syracuseStep 1831807 = 2747711) B2747711
theorem B2749679 : Blo 1831617 2749679 := bstep (se 1 (by rfl) ⟨2062259, by rfl⟩ : syracuseStep 2749679 = 4124519) B4124519
theorem B10442105 : Blo 1831617 10442105 := bstep (se 2 (by rfl) ⟨3915789, by rfl⟩ : syracuseStep 10442105 = 7831579) B7831579
theorem B1832383 : Blo 1831617 1832383 := bstep (se 1 (by rfl) ⟨1374287, by rfl⟩ : syracuseStep 1832383 = 2748575) B2748575
theorem B79239383 : Blo 1831617 79239383 := bstep (se 1 (by rfl) ⟨59429537, by rfl⟩ : syracuseStep 79239383 = 118859075) B118859075
theorem B5216987 : Blo 1831617 5216987 := bstep (se 1 (by rfl) ⟨3912740, by rfl⟩ : syracuseStep 5216987 = 7825481) B7825481
theorem B11149267 : Blo 1831617 11149267 := bstep (se 1 (by rfl) ⟨8361950, by rfl⟩ : syracuseStep 11149267 = 16723901) B16723901
theorem B4122377 : Blo 1831617 4122377 := bstep (se 2 (by rfl) ⟨1545891, by rfl⟩ : syracuseStep 4122377 = 3091783) B3091783
theorem B3091135 : Blo 1831617 3091135 := bstep (se 1 (by rfl) ⟨2318351, by rfl⟩ : syracuseStep 3091135 = 4636703) B4636703
theorem B4123367 : Blo 1831617 4123367 := bstep (se 1 (by rfl) ⟨3092525, by rfl⟩ : syracuseStep 4123367 = 6185051) B6185051
theorem B52826255 : Blo 1831617 52826255 := bstep (se 1 (by rfl) ⟨39619691, by rfl⟩ : syracuseStep 52826255 = 79239383) B79239383
theorem B3477991 : Blo 1831617 3477991 := bstep (se 1 (by rfl) ⟨2608493, by rfl⟩ : syracuseStep 3477991 = 5216987) B5216987
theorem B6271739 : Blo 1831617 6271739 := bstep (se 1 (by rfl) ⟨4703804, by rfl⟩ : syracuseStep 6271739 = 9407609) B9407609
theorem B3093275 : Blo 1831617 3093275 := bstep (se 1 (by rfl) ⟨2319956, by rfl⟩ : syracuseStep 3093275 = 4639913) B4639913
theorem B14865689 : Blo 1831617 14865689 := bstep (se 2 (by rfl) ⟨5574633, by rfl⟩ : syracuseStep 14865689 = 11149267) B11149267
theorem B3716455 : Blo 1831617 3716455 := bstep (se 1 (by rfl) ⟨2787341, by rfl⟩ : syracuseStep 3716455 = 5574683) B5574683
theorem B1833119 : Blo 1831617 1833119 := bstep (se 1 (by rfl) ⟨1374839, by rfl⟩ : syracuseStep 1833119 = 2749679) B2749679
theorem B6961403 : Blo 1831617 6961403 := bstep (se 1 (by rfl) ⟨5221052, by rfl⟩ : syracuseStep 6961403 = 10442105) B10442105
theorem B5216815 : Blo 1831617 5216815 := bstep (se 1 (by rfl) ⟨3912611, by rfl⟩ : syracuseStep 5216815 = 7825223) B7825223
theorem B6184619 : Blo 1831617 6184619 := bstep (se 1 (by rfl) ⟨4638464, by rfl⟩ : syracuseStep 6184619 = 9276929) B9276929
theorem B35217503 : Blo 1831617 35217503 := bstep (se 1 (by rfl) ⟨26413127, by rfl⟩ : syracuseStep 35217503 = 52826255) B52826255
theorem B4637321 : Blo 1831617 4637321 := bstep (se 2 (by rfl) ⟨1738995, by rfl⟩ : syracuseStep 4637321 = 3477991) B3477991
theorem B6955753 : Blo 1831617 6955753 := bstep (se 2 (by rfl) ⟨2608407, by rfl⟩ : syracuseStep 6955753 = 5216815) B5216815
theorem B4121513 : Blo 1831617 4121513 := bstep (se 2 (by rfl) ⟨1545567, by rfl⟩ : syracuseStep 4121513 = 3091135) B3091135
theorem B4123079 : Blo 1831617 4123079 := bstep (se 1 (by rfl) ⟨3092309, by rfl⟩ : syracuseStep 4123079 = 6184619) B6184619
theorem B4181159 : Blo 1831617 4181159 := bstep (se 1 (by rfl) ⟨3135869, by rfl⟩ : syracuseStep 4181159 = 6271739) B6271739
theorem B2748251 : Blo 1831617 2748251 := bstep (se 1 (by rfl) ⟨2061188, by rfl⟩ : syracuseStep 2748251 = 4122377) B4122377
theorem B4640935 : Blo 1831617 4640935 := bstep (se 1 (by rfl) ⟨3480701, by rfl⟩ : syracuseStep 4640935 = 6961403) B6961403
theorem B2748911 : Blo 1831617 2748911 := bstep (se 1 (by rfl) ⟨2061683, by rfl⟩ : syracuseStep 2748911 = 4123367) B4123367
theorem B2062183 : Blo 1831617 2062183 := bstep (se 1 (by rfl) ⟨1546637, by rfl⟩ : syracuseStep 2062183 = 3093275) B3093275
theorem B9910459 : Blo 1831617 9910459 := bstep (se 1 (by rfl) ⟨7432844, by rfl⟩ : syracuseStep 9910459 = 14865689) B14865689
theorem B4955273 : Blo 1831617 4955273 := bstep (se 2 (by rfl) ⟨1858227, by rfl⟩ : syracuseStep 4955273 = 3716455) B3716455
theorem B23478335 : Blo 1831617 23478335 := bstep (se 1 (by rfl) ⟨17608751, by rfl⟩ : syracuseStep 23478335 = 35217503) B35217503
theorem B13213945 : Blo 1831617 13213945 := bstep (se 2 (by rfl) ⟨4955229, by rfl⟩ : syracuseStep 13213945 = 9910459) B9910459
theorem B9274337 : Blo 1831617 9274337 := bstep (se 2 (by rfl) ⟨3477876, by rfl⟩ : syracuseStep 9274337 = 6955753) B6955753
theorem B3303515 : Blo 1831617 3303515 := bstep (se 1 (by rfl) ⟨2477636, by rfl⟩ : syracuseStep 3303515 = 4955273) B4955273
theorem B2787439 : Blo 1831617 2787439 := bstep (se 1 (by rfl) ⟨2090579, by rfl⟩ : syracuseStep 2787439 = 4181159) B4181159
theorem B6187913 : Blo 1831617 6187913 := bstep (se 2 (by rfl) ⟨2320467, by rfl⟩ : syracuseStep 6187913 = 4640935) B4640935
theorem B3091547 : Blo 1831617 3091547 := bstep (se 1 (by rfl) ⟨2318660, by rfl⟩ : syracuseStep 3091547 = 4637321) B4637321
theorem B2747675 : Blo 1831617 2747675 := bstep (se 1 (by rfl) ⟨2060756, by rfl⟩ : syracuseStep 2747675 = 4121513) B4121513
theorem B2748719 : Blo 1831617 2748719 := bstep (se 1 (by rfl) ⟨2061539, by rfl⟩ : syracuseStep 2748719 = 4123079) B4123079
theorem B2749577 : Blo 1831617 2749577 := bstep (se 2 (by rfl) ⟨1031091, by rfl⟩ : syracuseStep 2749577 = 2062183) B2062183
theorem B1832167 : Blo 1831617 1832167 := bstep (se 1 (by rfl) ⟨1374125, by rfl⟩ : syracuseStep 1832167 = 2748251) B2748251
theorem B1832607 : Blo 1831617 1832607 := bstep (se 1 (by rfl) ⟨1374455, by rfl⟩ : syracuseStep 1832607 = 2748911) B2748911
theorem B8809373 : Blo 1831617 8809373 := bstep (se 3 (by rfl) ⟨1651757, by rfl⟩ : syracuseStep 8809373 = 3303515) B3303515
theorem B4125275 : Blo 1831617 4125275 := bstep (se 1 (by rfl) ⟨3093956, by rfl⟩ : syracuseStep 4125275 = 6187913) B6187913
theorem B2061031 : Blo 1831617 2061031 := bstep (se 1 (by rfl) ⟨1545773, by rfl⟩ : syracuseStep 2061031 = 3091547) B3091547
theorem B1831783 : Blo 1831617 1831783 := bstep (se 1 (by rfl) ⟨1373837, by rfl⟩ : syracuseStep 1831783 = 2747675) B2747675
theorem B15652223 : Blo 1831617 15652223 := bstep (se 1 (by rfl) ⟨11739167, by rfl⟩ : syracuseStep 15652223 = 23478335) B23478335
theorem B3716585 : Blo 1831617 3716585 := bstep (se 2 (by rfl) ⟨1393719, by rfl⟩ : syracuseStep 3716585 = 2787439) B2787439
theorem B1832479 : Blo 1831617 1832479 := bstep (se 1 (by rfl) ⟨1374359, by rfl⟩ : syracuseStep 1832479 = 2748719) B2748719
theorem B17618593 : Blo 1831617 17618593 := bstep (se 2 (by rfl) ⟨6606972, by rfl⟩ : syracuseStep 17618593 = 13213945) B13213945
theorem B6182891 : Blo 1831617 6182891 := bstep (se 1 (by rfl) ⟨4637168, by rfl⟩ : syracuseStep 6182891 = 9274337) B9274337
theorem B1833051 : Blo 1831617 1833051 := bstep (se 1 (by rfl) ⟨1374788, by rfl⟩ : syracuseStep 1833051 = 2749577) B2749577
theorem B4121927 : Blo 1831617 4121927 := bstep (se 1 (by rfl) ⟨3091445, by rfl⟩ : syracuseStep 4121927 = 6182891) B6182891
theorem B2748041 : Blo 1831617 2748041 := bstep (se 2 (by rfl) ⟨1030515, by rfl⟩ : syracuseStep 2748041 = 2061031) B2061031
theorem B2477723 : Blo 1831617 2477723 := bstep (se 1 (by rfl) ⟨1858292, by rfl⟩ : syracuseStep 2477723 = 3716585) B3716585
theorem B23491457 : Blo 1831617 23491457 := bstep (se 2 (by rfl) ⟨8809296, by rfl⟩ : syracuseStep 23491457 = 17618593) B17618593
theorem B2750183 : Blo 1831617 2750183 := bstep (se 1 (by rfl) ⟨2062637, by rfl⟩ : syracuseStep 2750183 = 4125275) B4125275
theorem B10434815 : Blo 1831617 10434815 := bstep (se 1 (by rfl) ⟨7826111, by rfl⟩ : syracuseStep 10434815 = 15652223) B15652223
theorem B5872915 : Blo 1831617 5872915 := bstep (se 1 (by rfl) ⟨4404686, by rfl⟩ : syracuseStep 5872915 = 8809373) B8809373
theorem B6956543 : Blo 1831617 6956543 := bstep (se 1 (by rfl) ⟨5217407, by rfl⟩ : syracuseStep 6956543 = 10434815) B10434815
theorem B2747951 : Blo 1831617 2747951 := bstep (se 1 (by rfl) ⟨2060963, by rfl⟩ : syracuseStep 2747951 = 4121927) B4121927
theorem B31322213 : Blo 1831617 31322213 := bstep (se 4 (by rfl) ⟨2936457, by rfl⟩ : syracuseStep 31322213 = 5872915) B5872915
theorem B6607261 : Blo 1831617 6607261 := bstep (se 3 (by rfl) ⟨1238861, by rfl⟩ : syracuseStep 6607261 = 2477723) B2477723
theorem B1832027 : Blo 1831617 1832027 := bstep (se 1 (by rfl) ⟨1374020, by rfl⟩ : syracuseStep 1832027 = 2748041) B2748041
theorem B15660971 : Blo 1831617 15660971 := bstep (se 1 (by rfl) ⟨11745728, by rfl⟩ : syracuseStep 15660971 = 23491457) B23491457
theorem B1833455 : Blo 1831617 1833455 := bstep (se 1 (by rfl) ⟨1375091, by rfl⟩ : syracuseStep 1833455 = 2750183) B2750183
theorem B20881475 : Blo 1831617 20881475 := bstep (se 1 (by rfl) ⟨15661106, by rfl⟩ : syracuseStep 20881475 = 31322213) B31322213
theorem B4637695 : Blo 1831617 4637695 := bstep (se 1 (by rfl) ⟨3478271, by rfl⟩ : syracuseStep 4637695 = 6956543) B6956543
theorem B8809681 : Blo 1831617 8809681 := bstep (se 2 (by rfl) ⟨3303630, by rfl⟩ : syracuseStep 8809681 = 6607261) B6607261
theorem B10440647 : Blo 1831617 10440647 := bstep (se 1 (by rfl) ⟨7830485, by rfl⟩ : syracuseStep 10440647 = 15660971) B15660971
theorem B1831967 : Blo 1831617 1831967 := bstep (se 1 (by rfl) ⟨1373975, by rfl⟩ : syracuseStep 1831967 = 2747951) B2747951
theorem B13920983 : Blo 1831617 13920983 := bstep (se 1 (by rfl) ⟨10440737, by rfl⟩ : syracuseStep 13920983 = 20881475) B20881475
theorem B6960431 : Blo 1831617 6960431 := bstep (se 1 (by rfl) ⟨5220323, by rfl⟩ : syracuseStep 6960431 = 10440647) B10440647
theorem B6183593 : Blo 1831617 6183593 := bstep (se 2 (by rfl) ⟨2318847, by rfl⟩ : syracuseStep 6183593 = 4637695) B4637695
theorem B11746241 : Blo 1831617 11746241 := bstep (se 2 (by rfl) ⟨4404840, by rfl⟩ : syracuseStep 11746241 = 8809681) B8809681
theorem B4122395 : Blo 1831617 4122395 := bstep (se 1 (by rfl) ⟨3091796, by rfl⟩ : syracuseStep 4122395 = 6183593) B6183593
theorem B4640287 : Blo 1831617 4640287 := bstep (se 1 (by rfl) ⟨3480215, by rfl⟩ : syracuseStep 4640287 = 6960431) B6960431
theorem B9280655 : Blo 1831617 9280655 := bstep (se 1 (by rfl) ⟨6960491, by rfl⟩ : syracuseStep 9280655 = 13920983) B13920983
theorem B7830827 : Blo 1831617 7830827 := bstep (se 1 (by rfl) ⟨5873120, by rfl⟩ : syracuseStep 7830827 = 11746241) B11746241
theorem B6187049 : Blo 1831617 6187049 := bstep (se 2 (by rfl) ⟨2320143, by rfl⟩ : syracuseStep 6187049 = 4640287) B4640287
theorem B6187103 : Blo 1831617 6187103 := bstep (se 1 (by rfl) ⟨4640327, by rfl⟩ : syracuseStep 6187103 = 9280655) B9280655
theorem B5220551 : Blo 1831617 5220551 := bstep (se 1 (by rfl) ⟨3915413, by rfl⟩ : syracuseStep 5220551 = 7830827) B7830827
theorem B2748263 : Blo 1831617 2748263 := bstep (se 1 (by rfl) ⟨2061197, by rfl⟩ : syracuseStep 2748263 = 4122395) B4122395
theorem B13921469 : Blo 1831617 13921469 := bstep (se 3 (by rfl) ⟨2610275, by rfl⟩ : syracuseStep 13921469 = 5220551) B5220551
theorem B4124699 : Blo 1831617 4124699 := bstep (se 1 (by rfl) ⟨3093524, by rfl⟩ : syracuseStep 4124699 = 6187049) B6187049
theorem B4124735 : Blo 1831617 4124735 := bstep (se 1 (by rfl) ⟨3093551, by rfl⟩ : syracuseStep 4124735 = 6187103) B6187103
theorem B1832175 : Blo 1831617 1832175 := bstep (se 1 (by rfl) ⟨1374131, by rfl⟩ : syracuseStep 1832175 = 2748263) B2748263
theorem B2749799 : Blo 1831617 2749799 := bstep (se 1 (by rfl) ⟨2062349, by rfl⟩ : syracuseStep 2749799 = 4124699) B4124699
theorem B2749823 : Blo 1831617 2749823 := bstep (se 1 (by rfl) ⟨2062367, by rfl⟩ : syracuseStep 2749823 = 4124735) B4124735
theorem B9280979 : Blo 1831617 9280979 := bstep (se 1 (by rfl) ⟨6960734, by rfl⟩ : syracuseStep 9280979 = 13921469) B13921469
theorem B6187319 : Blo 1831617 6187319 := bstep (se 1 (by rfl) ⟨4640489, by rfl⟩ : syracuseStep 6187319 = 9280979) B9280979
theorem B1833199 : Blo 1831617 1833199 := bstep (se 1 (by rfl) ⟨1374899, by rfl⟩ : syracuseStep 1833199 = 2749799) B2749799
theorem B1833215 : Blo 1831617 1833215 := bstep (se 1 (by rfl) ⟨1374911, by rfl⟩ : syracuseStep 1833215 = 2749823) B2749823
theorem B4124879 : Blo 1831617 4124879 := bstep (se 1 (by rfl) ⟨3093659, by rfl⟩ : syracuseStep 4124879 = 6187319) B6187319
theorem B2749919 : Blo 1831617 2749919 := bstep (se 1 (by rfl) ⟨2062439, by rfl⟩ : syracuseStep 2749919 = 4124879) B4124879
theorem B1833279 : Blo 1831617 1833279 := bstep (se 1 (by rfl) ⟨1374959, by rfl⟩ : syracuseStep 1833279 = 2749919) B2749919

theorem C0 (j : ℕ) (h1 : 457904 ≤ j) (h2 : j ≤ 458403) : Blo 1831617 (4 * j + 3) := by
  interval_cases j
  · exact B1831619
  · exact B1831623
  · exact B1831627
  · exact B1831631
  · exact B1831635
  · exact B1831639
  · exact B1831643
  · exact B1831647
  · exact B1831651
  · exact B1831655
  · exact B1831659
  · exact B1831663
  · exact B1831667
  · exact B1831671
  · exact B1831675
  · exact B1831679
  · exact B1831683
  · exact B1831687
  · exact B1831691
  · exact B1831695
  · exact B1831699
  · exact B1831703
  · exact B1831707
  · exact B1831711
  · exact B1831715
  · exact B1831719
  · exact B1831723
  · exact B1831727
  · exact B1831731
  · exact B1831735
  · exact B1831739
  · exact B1831743
  · exact B1831747
  · exact B1831751
  · exact B1831755
  · exact B1831759
  · exact B1831763
  · exact B1831767
  · exact B1831771
  · exact B1831775
  · exact B1831779
  · exact B1831783
  · exact B1831787
  · exact B1831791
  · exact B1831795
  · exact B1831799
  · exact B1831803
  · exact B1831807
  · exact B1831811
  · exact B1831815
  · exact B1831819
  · exact B1831823
  · exact B1831827
  · exact B1831831
  · exact B1831835
  · exact B1831839
  · exact B1831843
  · exact B1831847
  · exact B1831851
  · exact B1831855
  · exact B1831859
  · exact B1831863
  · exact B1831867
  · exact B1831871
  · exact B1831875
  · exact B1831879
  · exact B1831883
  · exact B1831887
  · exact B1831891
  · exact B1831895
  · exact B1831899
  · exact B1831903
  · exact B1831907
  · exact B1831911
  · exact B1831915
  · exact B1831919
  · exact B1831923
  · exact B1831927
  · exact B1831931
  · exact B1831935
  · exact B1831939
  · exact B1831943
  · exact B1831947
  · exact B1831951
  · exact B1831955
  · exact B1831959
  · exact B1831963
  · exact B1831967
  · exact B1831971
  · exact B1831975
  · exact B1831979
  · exact B1831983
  · exact B1831987
  · exact B1831991
  · exact B1831995
  · exact B1831999
  · exact B1832003
  · exact B1832007
  · exact B1832011
  · exact B1832015
  · exact B1832019
  · exact B1832023
  · exact B1832027
  · exact B1832031
  · exact B1832035
  · exact B1832039
  · exact B1832043
  · exact B1832047
  · exact B1832051
  · exact B1832055
  · exact B1832059
  · exact B1832063
  · exact B1832067
  · exact B1832071
  · exact B1832075
  · exact B1832079
  · exact B1832083
  · exact B1832087
  · exact B1832091
  · exact B1832095
  · exact B1832099
  · exact B1832103
  · exact B1832107
  · exact B1832111
  · exact B1832115
  · exact B1832119
  · exact B1832123
  · exact B1832127
  · exact B1832131
  · exact B1832135
  · exact B1832139
  · exact B1832143
  · exact B1832147
  · exact B1832151
  · exact B1832155
  · exact B1832159
  · exact B1832163
  · exact B1832167
  · exact B1832171
  · exact B1832175
  · exact B1832179
  · exact B1832183
  · exact B1832187
  · exact B1832191
  · exact B1832195
  · exact B1832199
  · exact B1832203
  · exact B1832207
  · exact B1832211
  · exact B1832215
  · exact B1832219
  · exact B1832223
  · exact B1832227
  · exact B1832231
  · exact B1832235
  · exact B1832239
  · exact B1832243
  · exact B1832247
  · exact B1832251
  · exact B1832255
  · exact B1832259
  · exact B1832263
  · exact B1832267
  · exact B1832271
  · exact B1832275
  · exact B1832279
  · exact B1832283
  · exact B1832287
  · exact B1832291
  · exact B1832295
  · exact B1832299
  · exact B1832303
  · exact B1832307
  · exact B1832311
  · exact B1832315
  · exact B1832319
  · exact B1832323
  · exact B1832327
  · exact B1832331
  · exact B1832335
  · exact B1832339
  · exact B1832343
  · exact B1832347
  · exact B1832351
  · exact B1832355
  · exact B1832359
  · exact B1832363
  · exact B1832367
  · exact B1832371
  · exact B1832375
  · exact B1832379
  · exact B1832383
  · exact B1832387
  · exact B1832391
  · exact B1832395
  · exact B1832399
  · exact B1832403
  · exact B1832407
  · exact B1832411
  · exact B1832415
  · exact B1832419
  · exact B1832423
  · exact B1832427
  · exact B1832431
  · exact B1832435
  · exact B1832439
  · exact B1832443
  · exact B1832447
  · exact B1832451
  · exact B1832455
  · exact B1832459
  · exact B1832463
  · exact B1832467
  · exact B1832471
  · exact B1832475
  · exact B1832479
  · exact B1832483
  · exact B1832487
  · exact B1832491
  · exact B1832495
  · exact B1832499
  · exact B1832503
  · exact B1832507
  · exact B1832511
  · exact B1832515
  · exact B1832519
  · exact B1832523
  · exact B1832527
  · exact B1832531
  · exact B1832535
  · exact B1832539
  · exact B1832543
  · exact B1832547
  · exact B1832551
  · exact B1832555
  · exact B1832559
  · exact B1832563
  · exact B1832567
  · exact B1832571
  · exact B1832575
  · exact B1832579
  · exact B1832583
  · exact B1832587
  · exact B1832591
  · exact B1832595
  · exact B1832599
  · exact B1832603
  · exact B1832607
  · exact B1832611
  · exact B1832615
  · exact B1832619
  · exact B1832623
  · exact B1832627
  · exact B1832631
  · exact B1832635
  · exact B1832639
  · exact B1832643
  · exact B1832647
  · exact B1832651
  · exact B1832655
  · exact B1832659
  · exact B1832663
  · exact B1832667
  · exact B1832671
  · exact B1832675
  · exact B1832679
  · exact B1832683
  · exact B1832687
  · exact B1832691
  · exact B1832695
  · exact B1832699
  · exact B1832703
  · exact B1832707
  · exact B1832711
  · exact B1832715
  · exact B1832719
  · exact B1832723
  · exact B1832727
  · exact B1832731
  · exact B1832735
  · exact B1832739
  · exact B1832743
  · exact B1832747
  · exact B1832751
  · exact B1832755
  · exact B1832759
  · exact B1832763
  · exact B1832767
  · exact B1832771
  · exact B1832775
  · exact B1832779
  · exact B1832783
  · exact B1832787
  · exact B1832791
  · exact B1832795
  · exact B1832799
  · exact B1832803
  · exact B1832807
  · exact B1832811
  · exact B1832815
  · exact B1832819
  · exact B1832823
  · exact B1832827
  · exact B1832831
  · exact B1832835
  · exact B1832839
  · exact B1832843
  · exact B1832847
  · exact B1832851
  · exact B1832855
  · exact B1832859
  · exact B1832863
  · exact B1832867
  · exact B1832871
  · exact B1832875
  · exact B1832879
  · exact B1832883
  · exact B1832887
  · exact B1832891
  · exact B1832895
  · exact B1832899
  · exact B1832903
  · exact B1832907
  · exact B1832911
  · exact B1832915
  · exact B1832919
  · exact B1832923
  · exact B1832927
  · exact B1832931
  · exact B1832935
  · exact B1832939
  · exact B1832943
  · exact B1832947
  · exact B1832951
  · exact B1832955
  · exact B1832959
  · exact B1832963
  · exact B1832967
  · exact B1832971
  · exact B1832975
  · exact B1832979
  · exact B1832983
  · exact B1832987
  · exact B1832991
  · exact B1832995
  · exact B1832999
  · exact B1833003
  · exact B1833007
  · exact B1833011
  · exact B1833015
  · exact B1833019
  · exact B1833023
  · exact B1833027
  · exact B1833031
  · exact B1833035
  · exact B1833039
  · exact B1833043
  · exact B1833047
  · exact B1833051
  · exact B1833055
  · exact B1833059
  · exact B1833063
  · exact B1833067
  · exact B1833071
  · exact B1833075
  · exact B1833079
  · exact B1833083
  · exact B1833087
  · exact B1833091
  · exact B1833095
  · exact B1833099
  · exact B1833103
  · exact B1833107
  · exact B1833111
  · exact B1833115
  · exact B1833119
  · exact B1833123
  · exact B1833127
  · exact B1833131
  · exact B1833135
  · exact B1833139
  · exact B1833143
  · exact B1833147
  · exact B1833151
  · exact B1833155
  · exact B1833159
  · exact B1833163
  · exact B1833167
  · exact B1833171
  · exact B1833175
  · exact B1833179
  · exact B1833183
  · exact B1833187
  · exact B1833191
  · exact B1833195
  · exact B1833199
  · exact B1833203
  · exact B1833207
  · exact B1833211
  · exact B1833215
  · exact B1833219
  · exact B1833223
  · exact B1833227
  · exact B1833231
  · exact B1833235
  · exact B1833239
  · exact B1833243
  · exact B1833247
  · exact B1833251
  · exact B1833255
  · exact B1833259
  · exact B1833263
  · exact B1833267
  · exact B1833271
  · exact B1833275
  · exact B1833279
  · exact B1833283
  · exact B1833287
  · exact B1833291
  · exact B1833295
  · exact B1833299
  · exact B1833303
  · exact B1833307
  · exact B1833311
  · exact B1833315
  · exact B1833319
  · exact B1833323
  · exact B1833327
  · exact B1833331
  · exact B1833335
  · exact B1833339
  · exact B1833343
  · exact B1833347
  · exact B1833351
  · exact B1833355
  · exact B1833359
  · exact B1833363
  · exact B1833367
  · exact B1833371
  · exact B1833375
  · exact B1833379
  · exact B1833383
  · exact B1833387
  · exact B1833391
  · exact B1833395
  · exact B1833399
  · exact B1833403
  · exact B1833407
  · exact B1833411
  · exact B1833415
  · exact B1833419
  · exact B1833423
  · exact B1833427
  · exact B1833431
  · exact B1833435
  · exact B1833439
  · exact B1833443
  · exact B1833447
  · exact B1833451
  · exact B1833455
  · exact B1833459
  · exact B1833463
  · exact B1833467
  · exact B1833471
  · exact B1833475
  · exact B1833479
  · exact B1833483
  · exact B1833487
  · exact B1833491
  · exact B1833495
  · exact B1833499
  · exact B1833503
  · exact B1833507
  · exact B1833511
  · exact B1833515
  · exact B1833519
  · exact B1833523
  · exact B1833527
  · exact B1833531
  · exact B1833535
  · exact B1833539
  · exact B1833543
  · exact B1833547
  · exact B1833551
  · exact B1833555
  · exact B1833559
  · exact B1833563
  · exact B1833567
  · exact B1833571
  · exact B1833575
  · exact B1833579
  · exact B1833583
  · exact B1833587
  · exact B1833591
  · exact B1833595
  · exact B1833599
  · exact B1833603
  · exact B1833607
  · exact B1833611
  · exact B1833615

theorem solution (m : ℕ) (hlo : 1831617 ≤ m) (hhi : m ≤ 1833617) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 457904 ≤ j := by omega
    have hj2 : j ≤ 458403 := by omega
    have hb : Blo 1831617 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
