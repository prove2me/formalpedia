-- Prove2me | solution 1 for syracuse_descends_range_1480560_1482060
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:45:40.365278+00:00
-- url     : https://prove2.me/submissions/11f2c24f-0f39-479e-9362-28de4c816e90

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


theorem B2498573 : Blo 1480560 2498573 := bbase (se 3 (by rfl) ⟨468482, by rfl⟩ : syracuseStep 2498573 = 936965) (by norm_num)
theorem B3334157 : Blo 1480560 3334157 := bbase (se 3 (by rfl) ⟨625154, by rfl⟩ : syracuseStep 3334157 = 1250309) (by norm_num)
theorem B3162197 : Blo 1480560 3162197 := bbase (se 8 (by rfl) ⟨18528, by rfl⟩ : syracuseStep 3162197 = 37057) (by norm_num)
theorem B3334229 : Blo 1480560 3334229 := bbase (se 8 (by rfl) ⟨19536, by rfl⟩ : syracuseStep 3334229 = 39073) (by norm_num)
theorem B2498701 : Blo 1480560 2498701 := bbase (se 3 (by rfl) ⟨468506, by rfl⟩ : syracuseStep 2498701 = 937013) (by norm_num)
theorem B3334301 : Blo 1480560 3334301 := bbase (se 3 (by rfl) ⟨625181, by rfl⟩ : syracuseStep 3334301 = 1250363) (by norm_num)
theorem B2498789 : Blo 1480560 2498789 := bbase (se 4 (by rfl) ⟨234261, by rfl⟩ : syracuseStep 2498789 = 468523) (by norm_num)
theorem B3334373 : Blo 1480560 3334373 := bbase (se 4 (by rfl) ⟨312597, by rfl⟩ : syracuseStep 3334373 = 625195) (by norm_num)
theorem B3334445 : Blo 1480560 3334445 := bbase (se 3 (by rfl) ⟨625208, by rfl⟩ : syracuseStep 3334445 = 1250417) (by norm_num)
theorem B4997429 : Blo 1480560 4997429 := bbase (se 5 (by rfl) ⟨234254, by rfl⟩ : syracuseStep 4997429 = 468509) (by norm_num)
theorem B12345653 : Blo 1480560 12345653 := bbase (se 5 (by rfl) ⟨578702, by rfl⟩ : syracuseStep 12345653 = 1157405) (by norm_num)
theorem B2498917 : Blo 1480560 2498917 := bbase (se 4 (by rfl) ⟨234273, by rfl⟩ : syracuseStep 2498917 = 468547) (by norm_num)
theorem B3334517 : Blo 1480560 3334517 := bbase (se 5 (by rfl) ⟨156305, by rfl⟩ : syracuseStep 3334517 = 312611) (by norm_num)
theorem B1581449 : Blo 1480560 1581449 := bbase (se 2 (by rfl) ⟨593043, by rfl⟩ : syracuseStep 1581449 = 1186087) (by norm_num)
theorem B3162557 : Blo 1480560 3162557 := bbase (se 3 (by rfl) ⟨592979, by rfl⟩ : syracuseStep 3162557 = 1185959) (by norm_num)
theorem B2499005 : Blo 1480560 2499005 := bbase (se 3 (by rfl) ⟨468563, by rfl⟩ : syracuseStep 2499005 = 937127) (by norm_num)
theorem B3334589 : Blo 1480560 3334589 := bbase (se 3 (by rfl) ⟨625235, by rfl⟩ : syracuseStep 3334589 = 1250471) (by norm_num)
theorem B2253349 : Blo 1480560 2253349 := bbase (se 4 (by rfl) ⟨211251, by rfl⟩ : syracuseStep 2253349 = 422503) (by norm_num)
theorem B2499133 : Blo 1480560 2499133 := bbase (se 3 (by rfl) ⟨468587, by rfl⟩ : syracuseStep 2499133 = 937175) (by norm_num)
theorem B8438357 : Blo 1480560 8438357 := bbase (se 8 (by rfl) ⟨49443, by rfl⟩ : syracuseStep 8438357 = 98887) (by norm_num)
theorem B1581697 : Blo 1480560 1581697 := bbase (se 2 (by rfl) ⟨593136, by rfl⟩ : syracuseStep 1581697 = 1186273) (by norm_num)
theorem B2499221 : Blo 1480560 2499221 := bbase (se 6 (by rfl) ⟨58575, by rfl⟩ : syracuseStep 2499221 = 117151) (by norm_num)
theorem B4809365 : Blo 1480560 4809365 := bbase (se 6 (by rfl) ⟨112719, by rfl⟩ : syracuseStep 4809365 = 225439) (by norm_num)
theorem B4219589 : Blo 1480560 4219589 := bbase (se 4 (by rfl) ⟨395586, by rfl⟩ : syracuseStep 4219589 = 791173) (by norm_num)
theorem B26002133 : Blo 1480560 26002133 := bbase (se 7 (by rfl) ⟨304712, by rfl⟩ : syracuseStep 26002133 = 609425) (by norm_num)
theorem B4997861 : Blo 1480560 4997861 := bbase (se 4 (by rfl) ⟨468549, by rfl⟩ : syracuseStep 4997861 = 937099) (by norm_num)
theorem B2499349 : Blo 1480560 2499349 := bbase (se 6 (by rfl) ⟨58578, by rfl⟩ : syracuseStep 2499349 = 117157) (by norm_num)
theorem B2220845 : Blo 1480560 2220845 := bbase (se 3 (by rfl) ⟨416408, by rfl⟩ : syracuseStep 2220845 = 832817) (by norm_num)
theorem B2220869 : Blo 1480560 2220869 := bbase (se 4 (by rfl) ⟨208206, by rfl⟩ : syracuseStep 2220869 = 416413) (by norm_num)
theorem B11248469 : Blo 1480560 11248469 := bbase (se 9 (by rfl) ⟨32954, by rfl⟩ : syracuseStep 11248469 = 65909) (by norm_num)
theorem B2220893 : Blo 1480560 2220893 := bbase (se 3 (by rfl) ⟨416417, by rfl⟩ : syracuseStep 2220893 = 832835) (by norm_num)
theorem B7496549 : Blo 1480560 7496549 := bbase (se 4 (by rfl) ⟨702801, by rfl⟩ : syracuseStep 7496549 = 1405603) (by norm_num)
theorem B2499437 : Blo 1480560 2499437 := bbase (se 3 (by rfl) ⟨468644, by rfl⟩ : syracuseStep 2499437 = 937289) (by norm_num)
theorem B2220917 : Blo 1480560 2220917 := bbase (se 5 (by rfl) ⟨104105, by rfl⟩ : syracuseStep 2220917 = 208211) (by norm_num)
theorem B2220941 : Blo 1480560 2220941 := bbase (se 3 (by rfl) ⟨416426, by rfl⟩ : syracuseStep 2220941 = 832853) (by norm_num)
theorem B2220965 : Blo 1480560 2220965 := bbase (se 4 (by rfl) ⟨208215, by rfl⟩ : syracuseStep 2220965 = 416431) (by norm_num)
theorem B2220989 : Blo 1480560 2220989 := bbase (se 3 (by rfl) ⟨416435, by rfl⟩ : syracuseStep 2220989 = 832871) (by norm_num)
theorem B2221013 : Blo 1480560 2221013 := bbase (se 7 (by rfl) ⟨26027, by rfl⟩ : syracuseStep 2221013 = 52055) (by norm_num)
theorem B2221037 : Blo 1480560 2221037 := bbase (se 3 (by rfl) ⟨416444, by rfl⟩ : syracuseStep 2221037 = 832889) (by norm_num)
theorem B2499565 : Blo 1480560 2499565 := bbase (se 3 (by rfl) ⟨468668, by rfl⟩ : syracuseStep 2499565 = 937337) (by norm_num)
theorem B2221061 : Blo 1480560 2221061 := bbase (se 4 (by rfl) ⟨208224, by rfl⟩ : syracuseStep 2221061 = 416449) (by norm_num)
theorem B2221085 : Blo 1480560 2221085 := bbase (se 3 (by rfl) ⟨416453, by rfl⟩ : syracuseStep 2221085 = 832907) (by norm_num)
theorem B2810933 : Blo 1480560 2810933 := bbase (se 5 (by rfl) ⟨131762, by rfl⟩ : syracuseStep 2810933 = 263525) (by norm_num)
theorem B2221109 : Blo 1480560 2221109 := bbase (se 5 (by rfl) ⟨104114, by rfl⟩ : syracuseStep 2221109 = 208229) (by norm_num)
theorem B1582141 : Blo 1480560 1582141 := bbase (se 3 (by rfl) ⟨296651, by rfl⟩ : syracuseStep 1582141 = 593303) (by norm_num)
theorem B2499653 : Blo 1480560 2499653 := bbase (se 4 (by rfl) ⟨234342, by rfl⟩ : syracuseStep 2499653 = 468685) (by norm_num)
theorem B2221133 : Blo 1480560 2221133 := bbase (se 3 (by rfl) ⟨416462, by rfl⟩ : syracuseStep 2221133 = 832925) (by norm_num)
theorem B2221157 : Blo 1480560 2221157 := bbase (se 4 (by rfl) ⟨208233, by rfl⟩ : syracuseStep 2221157 = 416467) (by norm_num)
theorem B1582201 : Blo 1480560 1582201 := bbase (se 2 (by rfl) ⟨593325, by rfl⟩ : syracuseStep 1582201 = 1186651) (by norm_num)
theorem B2221181 : Blo 1480560 2221181 := bbase (se 3 (by rfl) ⟨416471, by rfl⟩ : syracuseStep 2221181 = 832943) (by norm_num)
theorem B2221205 : Blo 1480560 2221205 := bbase (se 6 (by rfl) ⟨52059, by rfl⟩ : syracuseStep 2221205 = 104119) (by norm_num)
theorem B4998293 : Blo 1480560 4998293 := bbase (se 6 (by rfl) ⟨117147, by rfl⟩ : syracuseStep 4998293 = 234295) (by norm_num)
theorem B2221229 : Blo 1480560 2221229 := bbase (se 3 (by rfl) ⟨416480, by rfl⟩ : syracuseStep 2221229 = 832961) (by norm_num)
theorem B2221253 : Blo 1480560 2221253 := bbase (se 4 (by rfl) ⟨208242, by rfl⟩ : syracuseStep 2221253 = 416485) (by norm_num)
theorem B2499781 : Blo 1480560 2499781 := bbase (se 4 (by rfl) ⟨234354, by rfl⟩ : syracuseStep 2499781 = 468709) (by norm_num)
theorem B2221277 : Blo 1480560 2221277 := bbase (se 3 (by rfl) ⟨416489, by rfl⟩ : syracuseStep 2221277 = 832979) (by norm_num)
theorem B2221301 : Blo 1480560 2221301 := bbase (se 5 (by rfl) ⟨104123, by rfl⟩ : syracuseStep 2221301 = 208247) (by norm_num)
theorem B2221325 : Blo 1480560 2221325 := bbase (se 3 (by rfl) ⟨416498, by rfl⟩ : syracuseStep 2221325 = 832997) (by norm_num)
theorem B2499869 : Blo 1480560 2499869 := bbase (se 3 (by rfl) ⟨468725, by rfl⟩ : syracuseStep 2499869 = 937451) (by norm_num)
theorem B2221349 : Blo 1480560 2221349 := bbase (se 4 (by rfl) ⟨208251, by rfl⟩ : syracuseStep 2221349 = 416503) (by norm_num)
theorem B3163445 : Blo 1480560 3163445 := bbase (se 5 (by rfl) ⟨148286, by rfl⟩ : syracuseStep 3163445 = 296573) (by norm_num)
theorem B1779005 : Blo 1480560 1779005 := bbase (se 3 (by rfl) ⟨333563, by rfl⟩ : syracuseStep 1779005 = 667127) (by norm_num)
theorem B2221373 : Blo 1480560 2221373 := bbase (se 3 (by rfl) ⟨416507, by rfl⟩ : syracuseStep 2221373 = 833015) (by norm_num)
theorem B2221397 : Blo 1480560 2221397 := bbase (se 12 (by rfl) ⟨813, by rfl⟩ : syracuseStep 2221397 = 1627) (by norm_num)
theorem B10020181 : Blo 1480560 10020181 := bbase (se 12 (by rfl) ⟨3669, by rfl⟩ : syracuseStep 10020181 = 7339) (by norm_num)
theorem B2221421 : Blo 1480560 2221421 := bbase (se 3 (by rfl) ⟨416516, by rfl⟩ : syracuseStep 2221421 = 833033) (by norm_num)
theorem B2221445 : Blo 1480560 2221445 := bbase (se 4 (by rfl) ⟨208260, by rfl⟩ : syracuseStep 2221445 = 416521) (by norm_num)
theorem B2221469 : Blo 1480560 2221469 := bbase (se 3 (by rfl) ⟨416525, by rfl⟩ : syracuseStep 2221469 = 833051) (by norm_num)
theorem B2499997 : Blo 1480560 2499997 := bbase (se 3 (by rfl) ⟨468749, by rfl⟩ : syracuseStep 2499997 = 937499) (by norm_num)
theorem B1779121 : Blo 1480560 1779121 := bbase (se 2 (by rfl) ⟨667170, by rfl⟩ : syracuseStep 1779121 = 1334341) (by norm_num)
theorem B2221493 : Blo 1480560 2221493 := bbase (se 5 (by rfl) ⟨104132, by rfl⟩ : syracuseStep 2221493 = 208265) (by norm_num)
theorem B1582517 : Blo 1480560 1582517 := bbase (se 5 (by rfl) ⟨74180, by rfl⟩ : syracuseStep 1582517 = 148361) (by norm_num)
theorem B2221517 : Blo 1480560 2221517 := bbase (se 3 (by rfl) ⟨416534, by rfl⟩ : syracuseStep 2221517 = 833069) (by norm_num)
theorem B2704853 : Blo 1480560 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B2532829 : Blo 1480560 2532829 := bbase (se 3 (by rfl) ⟨474905, by rfl⟩ : syracuseStep 2532829 = 949811) (by norm_num)
theorem B2221541 : Blo 1480560 2221541 := bbase (se 4 (by rfl) ⟨208269, by rfl⟩ : syracuseStep 2221541 = 416539) (by norm_num)
theorem B2500085 : Blo 1480560 2500085 := bbase (se 5 (by rfl) ⟨117191, by rfl⟩ : syracuseStep 2500085 = 234383) (by norm_num)
theorem B1779193 : Blo 1480560 1779193 := bbase (se 2 (by rfl) ⟨667197, by rfl⟩ : syracuseStep 1779193 = 1334395) (by norm_num)
theorem B2221565 : Blo 1480560 2221565 := bbase (se 3 (by rfl) ⟨416543, by rfl⟩ : syracuseStep 2221565 = 833087) (by norm_num)
theorem B2221589 : Blo 1480560 2221589 := bbase (se 6 (by rfl) ⟨52068, by rfl⟩ : syracuseStep 2221589 = 104137) (by norm_num)
theorem B2221613 : Blo 1480560 2221613 := bbase (se 3 (by rfl) ⟨416552, by rfl⟩ : syracuseStep 2221613 = 833105) (by norm_num)
theorem B3163693 : Blo 1480560 3163693 := bbase (se 3 (by rfl) ⟨593192, by rfl⟩ : syracuseStep 3163693 = 1186385) (by norm_num)
theorem B9487925 : Blo 1480560 9487925 := bbase (se 5 (by rfl) ⟨444746, by rfl⟩ : syracuseStep 9487925 = 889493) (by norm_num)
theorem B4744757 : Blo 1480560 4744757 := bbase (se 5 (by rfl) ⟨222410, by rfl⟩ : syracuseStep 4744757 = 444821) (by norm_num)
theorem B2221637 : Blo 1480560 2221637 := bbase (se 4 (by rfl) ⟨208278, by rfl⟩ : syracuseStep 2221637 = 416557) (by norm_num)
theorem B4998725 : Blo 1480560 4998725 := bbase (se 4 (by rfl) ⟨468630, by rfl⟩ : syracuseStep 4998725 = 937261) (by norm_num)
theorem B2221661 : Blo 1480560 2221661 := bbase (se 3 (by rfl) ⟨416561, by rfl⟩ : syracuseStep 2221661 = 833123) (by norm_num)
theorem B1779313 : Blo 1480560 1779313 := bbase (se 2 (by rfl) ⟨667242, by rfl⟩ : syracuseStep 1779313 = 1334485) (by norm_num)
theorem B2221685 : Blo 1480560 2221685 := bbase (se 5 (by rfl) ⟨104141, by rfl⟩ : syracuseStep 2221685 = 208283) (by norm_num)
theorem B2500213 : Blo 1480560 2500213 := bbase (se 5 (by rfl) ⟨117197, by rfl⟩ : syracuseStep 2500213 = 234395) (by norm_num)
theorem B2221709 : Blo 1480560 2221709 := bbase (se 3 (by rfl) ⟨416570, by rfl⟩ : syracuseStep 2221709 = 833141) (by norm_num)
theorem B2221733 : Blo 1480560 2221733 := bbase (se 4 (by rfl) ⟨208287, by rfl⟩ : syracuseStep 2221733 = 416575) (by norm_num)
theorem B2221757 : Blo 1480560 2221757 := bbase (se 3 (by rfl) ⟨416579, by rfl⟩ : syracuseStep 2221757 = 833159) (by norm_num)
theorem B2500301 : Blo 1480560 2500301 := bbase (se 3 (by rfl) ⟨468806, by rfl⟩ : syracuseStep 2500301 = 937613) (by norm_num)
theorem B2221781 : Blo 1480560 2221781 := bbase (se 7 (by rfl) ⟨26036, by rfl⟩ : syracuseStep 2221781 = 52073) (by norm_num)
theorem B18982613 : Blo 1480560 18982613 := bbase (se 7 (by rfl) ⟨222452, by rfl⟩ : syracuseStep 18982613 = 444905) (by norm_num)
theorem B2221805 : Blo 1480560 2221805 := bbase (se 3 (by rfl) ⟨416588, by rfl⟩ : syracuseStep 2221805 = 833177) (by norm_num)
theorem B1689341 : Blo 1480560 1689341 := bbase (se 3 (by rfl) ⟨316751, by rfl⟩ : syracuseStep 1689341 = 633503) (by norm_num)
theorem B2221829 : Blo 1480560 2221829 := bbase (se 4 (by rfl) ⟨208296, by rfl⟩ : syracuseStep 2221829 = 416593) (by norm_num)
theorem B2221853 : Blo 1480560 2221853 := bbase (se 3 (by rfl) ⟨416597, by rfl⟩ : syracuseStep 2221853 = 833195) (by norm_num)
theorem B1689377 : Blo 1480560 1689377 := bbase (se 2 (by rfl) ⟨633516, by rfl⟩ : syracuseStep 1689377 = 1267033) (by norm_num)
theorem B2811685 : Blo 1480560 2811685 := bbase (se 4 (by rfl) ⟨263595, by rfl⟩ : syracuseStep 2811685 = 527191) (by norm_num)
theorem B2221877 : Blo 1480560 2221877 := bbase (se 5 (by rfl) ⟨104150, by rfl⟩ : syracuseStep 2221877 = 208301) (by norm_num)
theorem B2221901 : Blo 1480560 2221901 := bbase (se 3 (by rfl) ⟨416606, by rfl⟩ : syracuseStep 2221901 = 833213) (by norm_num)
theorem B2500429 : Blo 1480560 2500429 := bbase (se 3 (by rfl) ⟨468830, by rfl⟩ : syracuseStep 2500429 = 937661) (by norm_num)
theorem B1828705 : Blo 1480560 1828705 := bbase (se 2 (by rfl) ⟨685764, by rfl⟩ : syracuseStep 1828705 = 1371529) (by norm_num)
theorem B2221925 : Blo 1480560 2221925 := bbase (se 4 (by rfl) ⟨208305, by rfl⟩ : syracuseStep 2221925 = 416611) (by norm_num)
theorem B2221949 : Blo 1480560 2221949 := bbase (se 3 (by rfl) ⟨416615, by rfl⟩ : syracuseStep 2221949 = 833231) (by norm_num)
theorem B2221973 : Blo 1480560 2221973 := bbase (se 6 (by rfl) ⟨52077, by rfl⟩ : syracuseStep 2221973 = 104155) (by norm_num)
theorem B5621669 : Blo 1480560 5621669 := bbase (se 4 (by rfl) ⟨527031, by rfl⟩ : syracuseStep 5621669 = 1054063) (by norm_num)
theorem B2500517 : Blo 1480560 2500517 := bbase (se 4 (by rfl) ⟨234423, by rfl⟩ : syracuseStep 2500517 = 468847) (by norm_num)
theorem B2221997 : Blo 1480560 2221997 := bbase (se 3 (by rfl) ⟨416624, by rfl⟩ : syracuseStep 2221997 = 833249) (by norm_num)
theorem B2811829 : Blo 1480560 2811829 := bbase (se 5 (by rfl) ⟨131804, by rfl⟩ : syracuseStep 2811829 = 263609) (by norm_num)
theorem B2222021 : Blo 1480560 2222021 := bbase (se 4 (by rfl) ⟨208314, by rfl⟩ : syracuseStep 2222021 = 416629) (by norm_num)
theorem B1689541 : Blo 1480560 1689541 := bbase (se 4 (by rfl) ⟨158394, by rfl⟩ : syracuseStep 1689541 = 316789) (by norm_num)
theorem B2222045 : Blo 1480560 2222045 := bbase (se 3 (by rfl) ⟨416633, by rfl⟩ : syracuseStep 2222045 = 833267) (by norm_num)
theorem B1779697 : Blo 1480560 1779697 := bbase (se 2 (by rfl) ⟨667386, by rfl⟩ : syracuseStep 1779697 = 1334773) (by norm_num)
theorem B4999157 : Blo 1480560 4999157 := bbase (se 5 (by rfl) ⟨234335, by rfl⟩ : syracuseStep 4999157 = 468671) (by norm_num)
theorem B2222069 : Blo 1480560 2222069 := bbase (se 5 (by rfl) ⟨104159, by rfl⟩ : syracuseStep 2222069 = 208319) (by norm_num)
theorem B2222093 : Blo 1480560 2222093 := bbase (se 3 (by rfl) ⟨416642, by rfl⟩ : syracuseStep 2222093 = 833285) (by norm_num)
theorem B2222117 : Blo 1480560 2222117 := bbase (se 4 (by rfl) ⟨208323, by rfl⟩ : syracuseStep 2222117 = 416647) (by norm_num)
theorem B3164197 : Blo 1480560 3164197 := bbase (se 4 (by rfl) ⟨296643, by rfl⟩ : syracuseStep 3164197 = 593287) (by norm_num)
theorem B2500645 : Blo 1480560 2500645 := bbase (se 4 (by rfl) ⟨234435, by rfl⟩ : syracuseStep 2500645 = 468871) (by norm_num)
theorem B2222141 : Blo 1480560 2222141 := bbase (se 3 (by rfl) ⟨416651, by rfl⟩ : syracuseStep 2222141 = 833303) (by norm_num)
theorem B2811989 : Blo 1480560 2811989 := bbase (se 8 (by rfl) ⟨16476, by rfl⟩ : syracuseStep 2811989 = 32953) (by norm_num)
theorem B2222165 : Blo 1480560 2222165 := bbase (se 8 (by rfl) ⟨13020, by rfl⟩ : syracuseStep 2222165 = 26041) (by norm_num)
theorem B6006869 : Blo 1480560 6006869 := bbase (se 8 (by rfl) ⟨35196, by rfl⟩ : syracuseStep 6006869 = 70393) (by norm_num)
theorem B2222189 : Blo 1480560 2222189 := bbase (se 3 (by rfl) ⟨416660, by rfl⟩ : syracuseStep 2222189 = 833321) (by norm_num)
theorem B7497845 : Blo 1480560 7497845 := bbase (se 5 (by rfl) ⟨351461, by rfl⟩ : syracuseStep 7497845 = 702923) (by norm_num)
theorem B2500733 : Blo 1480560 2500733 := bbase (se 3 (by rfl) ⟨468887, by rfl⟩ : syracuseStep 2500733 = 937775) (by norm_num)
theorem B2222213 : Blo 1480560 2222213 := bbase (se 4 (by rfl) ⟨208332, by rfl⟩ : syracuseStep 2222213 = 416665) (by norm_num)
theorem B2222237 : Blo 1480560 2222237 := bbase (se 3 (by rfl) ⟨416669, by rfl⟩ : syracuseStep 2222237 = 833339) (by norm_num)
theorem B3557549 : Blo 1480560 3557549 := bbase (se 3 (by rfl) ⟨667040, by rfl⟩ : syracuseStep 3557549 = 1334081) (by norm_num)
theorem B2222261 : Blo 1480560 2222261 := bbase (se 5 (by rfl) ⟨104168, by rfl⟩ : syracuseStep 2222261 = 208337) (by norm_num)
theorem B5621957 : Blo 1480560 5621957 := bbase (se 4 (by rfl) ⟨527058, by rfl⟩ : syracuseStep 5621957 = 1054117) (by norm_num)
theorem B2222285 : Blo 1480560 2222285 := bbase (se 3 (by rfl) ⟨416678, by rfl⟩ : syracuseStep 2222285 = 833357) (by norm_num)
theorem B1501409 : Blo 1480560 1501409 := bbase (se 2 (by rfl) ⟨563028, by rfl⟩ : syracuseStep 1501409 = 1126057) (by norm_num)
theorem B2812133 : Blo 1480560 2812133 := bbase (se 4 (by rfl) ⟨263637, by rfl⟩ : syracuseStep 2812133 = 527275) (by norm_num)
theorem B2222309 : Blo 1480560 2222309 := bbase (se 4 (by rfl) ⟨208341, by rfl⟩ : syracuseStep 2222309 = 416683) (by norm_num)
theorem B1689833 : Blo 1480560 1689833 := bbase (se 2 (by rfl) ⟨633687, by rfl⟩ : syracuseStep 1689833 = 1267375) (by norm_num)
theorem B2222333 : Blo 1480560 2222333 := bbase (se 3 (by rfl) ⟨416687, by rfl⟩ : syracuseStep 2222333 = 833375) (by norm_num)
theorem B2500861 : Blo 1480560 2500861 := bbase (se 3 (by rfl) ⟨468911, by rfl⟩ : syracuseStep 2500861 = 937823) (by norm_num)
theorem B2222357 : Blo 1480560 2222357 := bbase (se 6 (by rfl) ⟨52086, by rfl⟩ : syracuseStep 2222357 = 104173) (by norm_num)
theorem B1804573 : Blo 1480560 1804573 := bbase (se 3 (by rfl) ⟨338357, by rfl⟩ : syracuseStep 1804573 = 676715) (by norm_num)
theorem B2222381 : Blo 1480560 2222381 := bbase (se 3 (by rfl) ⟨416696, by rfl⟩ : syracuseStep 2222381 = 833393) (by norm_num)
theorem B6326581 : Blo 1480560 6326581 := bbase (se 5 (by rfl) ⟨296558, by rfl⟩ : syracuseStep 6326581 = 593117) (by norm_num)
theorem B2222405 : Blo 1480560 2222405 := bbase (se 4 (by rfl) ⟨208350, by rfl⟩ : syracuseStep 2222405 = 416701) (by norm_num)
theorem B2500949 : Blo 1480560 2500949 := bbase (se 10 (by rfl) ⟨3663, by rfl⟩ : syracuseStep 2500949 = 7327) (by norm_num)
theorem B2222429 : Blo 1480560 2222429 := bbase (se 3 (by rfl) ⟨416705, by rfl⟩ : syracuseStep 2222429 = 833411) (by norm_num)
theorem B2222453 : Blo 1480560 2222453 := bbase (se 5 (by rfl) ⟨104177, by rfl⟩ : syracuseStep 2222453 = 208355) (by norm_num)
theorem B2222477 : Blo 1480560 2222477 := bbase (se 3 (by rfl) ⟨416714, by rfl⟩ : syracuseStep 2222477 = 833429) (by norm_num)
theorem B4999589 : Blo 1480560 4999589 := bbase (se 4 (by rfl) ⟨468711, by rfl⟩ : syracuseStep 4999589 = 937423) (by norm_num)
theorem B2222501 : Blo 1480560 2222501 := bbase (se 4 (by rfl) ⟨208359, by rfl⟩ : syracuseStep 2222501 = 416719) (by norm_num)
theorem B2222525 : Blo 1480560 2222525 := bbase (se 3 (by rfl) ⟨416723, by rfl⟩ : syracuseStep 2222525 = 833447) (by norm_num)
theorem B2001349 : Blo 1480560 2001349 := bbase (se 4 (by rfl) ⟨187626, by rfl⟩ : syracuseStep 2001349 = 375253) (by norm_num)
theorem B2222549 : Blo 1480560 2222549 := bbase (se 7 (by rfl) ⟨26045, by rfl⟩ : syracuseStep 2222549 = 52091) (by norm_num)
theorem B2222573 : Blo 1480560 2222573 := bbase (se 3 (by rfl) ⟨416732, by rfl⟩ : syracuseStep 2222573 = 833465) (by norm_num)
theorem B2812421 : Blo 1480560 2812421 := bbase (se 4 (by rfl) ⟨263664, by rfl⟩ : syracuseStep 2812421 = 527329) (by norm_num)
theorem B2222597 : Blo 1480560 2222597 := bbase (se 4 (by rfl) ⟨208368, by rfl⟩ : syracuseStep 2222597 = 416737) (by norm_num)
theorem B2222621 : Blo 1480560 2222621 := bbase (se 3 (by rfl) ⟨416741, by rfl⟩ : syracuseStep 2222621 = 833483) (by norm_num)
theorem B8006197 : Blo 1480560 8006197 := bbase (se 5 (by rfl) ⟨375290, by rfl⟩ : syracuseStep 8006197 = 750581) (by norm_num)
theorem B2222645 : Blo 1480560 2222645 := bbase (se 5 (by rfl) ⟨104186, by rfl⟩ : syracuseStep 2222645 = 208373) (by norm_num)
theorem B2222669 : Blo 1480560 2222669 := bbase (se 3 (by rfl) ⟨416750, by rfl⟩ : syracuseStep 2222669 = 833501) (by norm_num)
theorem B2222693 : Blo 1480560 2222693 := bbase (se 4 (by rfl) ⟨208377, by rfl⟩ : syracuseStep 2222693 = 416755) (by norm_num)
theorem B1665661 : Blo 1480560 1665661 := bbase (se 3 (by rfl) ⟨312311, by rfl⟩ : syracuseStep 1665661 = 624623) (by norm_num)
theorem B2222717 : Blo 1480560 2222717 := bbase (se 3 (by rfl) ⟨416759, by rfl⟩ : syracuseStep 2222717 = 833519) (by norm_num)
theorem B2222741 : Blo 1480560 2222741 := bbase (se 6 (by rfl) ⟨52095, by rfl⟩ : syracuseStep 2222741 = 104191) (by norm_num)
theorem B2812573 : Blo 1480560 2812573 := bbase (se 3 (by rfl) ⟨527357, by rfl⟩ : syracuseStep 2812573 = 1054715) (by norm_num)
theorem B1665697 : Blo 1480560 1665697 := bbase (se 2 (by rfl) ⟨624636, by rfl⟩ : syracuseStep 1665697 = 1249273) (by norm_num)
theorem B1780385 : Blo 1480560 1780385 := bbase (se 2 (by rfl) ⟨667644, by rfl⟩ : syracuseStep 1780385 = 1335289) (by norm_num)
theorem B2222765 : Blo 1480560 2222765 := bbase (se 3 (by rfl) ⟨416768, by rfl⟩ : syracuseStep 2222765 = 833537) (by norm_num)
theorem B1665733 : Blo 1480560 1665733 := bbase (se 4 (by rfl) ⟨156162, by rfl⟩ : syracuseStep 1665733 = 312325) (by norm_num)
theorem B2222789 : Blo 1480560 2222789 := bbase (se 4 (by rfl) ⟨208386, by rfl⟩ : syracuseStep 2222789 = 416773) (by norm_num)
theorem B2534093 : Blo 1480560 2534093 := bbase (se 3 (by rfl) ⟨475142, by rfl⟩ : syracuseStep 2534093 = 950285) (by norm_num)
theorem B2222813 : Blo 1480560 2222813 := bbase (se 3 (by rfl) ⟨416777, by rfl⟩ : syracuseStep 2222813 = 833555) (by norm_num)
theorem B1665769 : Blo 1480560 1665769 := bbase (se 2 (by rfl) ⟨624663, by rfl⟩ : syracuseStep 1665769 = 1249327) (by norm_num)
theorem B2222837 : Blo 1480560 2222837 := bbase (se 5 (by rfl) ⟨104195, by rfl⟩ : syracuseStep 2222837 = 208391) (by norm_num)
theorem B1665805 : Blo 1480560 1665805 := bbase (se 3 (by rfl) ⟨312338, by rfl⟩ : syracuseStep 1665805 = 624677) (by norm_num)
theorem B2222861 : Blo 1480560 2222861 := bbase (se 3 (by rfl) ⟨416786, by rfl⟩ : syracuseStep 2222861 = 833573) (by norm_num)
theorem B2222885 : Blo 1480560 2222885 := bbase (se 4 (by rfl) ⟨208395, by rfl⟩ : syracuseStep 2222885 = 416791) (by norm_num)
theorem B1665841 : Blo 1480560 1665841 := bbase (se 2 (by rfl) ⟨624690, by rfl⟩ : syracuseStep 1665841 = 1249381) (by norm_num)
theorem B2222909 : Blo 1480560 2222909 := bbase (se 3 (by rfl) ⟨416795, by rfl⟩ : syracuseStep 2222909 = 833591) (by norm_num)
theorem B4746053 : Blo 1480560 4746053 := bbase (se 4 (by rfl) ⟨444942, by rfl⟩ : syracuseStep 4746053 = 889885) (by norm_num)
theorem B1665877 : Blo 1480560 1665877 := bbase (se 9 (by rfl) ⟨4880, by rfl⟩ : syracuseStep 1665877 = 9761) (by norm_num)
theorem B5000021 : Blo 1480560 5000021 := bbase (se 9 (by rfl) ⟨14648, by rfl⟩ : syracuseStep 5000021 = 29297) (by norm_num)
theorem B2222933 : Blo 1480560 2222933 := bbase (se 9 (by rfl) ⟨6512, by rfl⟩ : syracuseStep 2222933 = 13025) (by norm_num)
theorem B2222957 : Blo 1480560 2222957 := bbase (se 3 (by rfl) ⟨416804, by rfl⟩ : syracuseStep 2222957 = 833609) (by norm_num)
theorem B1665913 : Blo 1480560 1665913 := bbase (se 2 (by rfl) ⟨624717, by rfl⟩ : syracuseStep 1665913 = 1249435) (by norm_num)
theorem B2222981 : Blo 1480560 2222981 := bbase (se 4 (by rfl) ⟨208404, by rfl⟩ : syracuseStep 2222981 = 416809) (by norm_num)
theorem B1665949 : Blo 1480560 1665949 := bbase (se 3 (by rfl) ⟨312365, by rfl⟩ : syracuseStep 1665949 = 624731) (by norm_num)
theorem B3165085 : Blo 1480560 3165085 := bbase (se 3 (by rfl) ⟨593453, by rfl⟩ : syracuseStep 3165085 = 1186907) (by norm_num)
theorem B2223005 : Blo 1480560 2223005 := bbase (se 3 (by rfl) ⟨416813, by rfl⟩ : syracuseStep 2223005 = 833627) (by norm_num)
theorem B2223029 : Blo 1480560 2223029 := bbase (se 5 (by rfl) ⟨104204, by rfl⟩ : syracuseStep 2223029 = 208409) (by norm_num)
theorem B1665985 : Blo 1480560 1665985 := bbase (se 2 (by rfl) ⟨624744, by rfl⟩ : syracuseStep 1665985 = 1249489) (by norm_num)
theorem B2812877 : Blo 1480560 2812877 := bbase (se 3 (by rfl) ⟨527414, by rfl⟩ : syracuseStep 2812877 = 1054829) (by norm_num)
theorem B2223053 : Blo 1480560 2223053 := bbase (se 3 (by rfl) ⟨416822, by rfl⟩ : syracuseStep 2223053 = 833645) (by norm_num)
theorem B13519829 : Blo 1480560 13519829 := bbase (se 7 (by rfl) ⟨158435, by rfl⟩ : syracuseStep 13519829 = 316871) (by norm_num)
theorem B1666021 : Blo 1480560 1666021 := bbase (se 4 (by rfl) ⟨156189, by rfl⟩ : syracuseStep 1666021 = 312379) (by norm_num)
theorem B2223077 : Blo 1480560 2223077 := bbase (se 4 (by rfl) ⟨208413, by rfl⟩ : syracuseStep 2223077 = 416827) (by norm_num)
theorem B1666057 : Blo 1480560 1666057 := bbase (se 2 (by rfl) ⟨624771, by rfl⟩ : syracuseStep 1666057 = 1249543) (by norm_num)
theorem B1666093 : Blo 1480560 1666093 := bbase (se 3 (by rfl) ⟨312392, by rfl⟩ : syracuseStep 1666093 = 624785) (by norm_num)
theorem B1666129 : Blo 1480560 1666129 := bbase (se 2 (by rfl) ⟨624798, by rfl⟩ : syracuseStep 1666129 = 1249597) (by norm_num)
theorem B1666165 : Blo 1480560 1666165 := bbase (se 5 (by rfl) ⟨78101, by rfl⟩ : syracuseStep 1666165 = 156203) (by norm_num)
theorem B6089861 : Blo 1480560 6089861 := bbase (se 4 (by rfl) ⟨570924, by rfl⟩ : syracuseStep 6089861 = 1141849) (by norm_num)
theorem B1666201 : Blo 1480560 1666201 := bbase (se 2 (by rfl) ⟨624825, by rfl⟩ : syracuseStep 1666201 = 1249651) (by norm_num)
theorem B1666237 : Blo 1480560 1666237 := bbase (se 3 (by rfl) ⟨312419, by rfl⟩ : syracuseStep 1666237 = 624839) (by norm_num)
theorem B1666273 : Blo 1480560 1666273 := bbase (se 2 (by rfl) ⟨624852, by rfl⟩ : syracuseStep 1666273 = 1249705) (by norm_num)
theorem B1666309 : Blo 1480560 1666309 := bbase (se 4 (by rfl) ⟨156216, by rfl⟩ : syracuseStep 1666309 = 312433) (by norm_num)
theorem B5000453 : Blo 1480560 5000453 := bbase (se 4 (by rfl) ⟨468792, by rfl⟩ : syracuseStep 5000453 = 937585) (by norm_num)
theorem B2108701 : Blo 1480560 2108701 := bbase (se 3 (by rfl) ⟨395381, by rfl⟩ : syracuseStep 2108701 = 790763) (by norm_num)
theorem B1666345 : Blo 1480560 1666345 := bbase (se 2 (by rfl) ⟨624879, by rfl⟩ : syracuseStep 1666345 = 1249759) (by norm_num)
theorem B1666381 : Blo 1480560 1666381 := bbase (se 3 (by rfl) ⟨312446, by rfl⟩ : syracuseStep 1666381 = 624893) (by norm_num)
theorem B8432981 : Blo 1480560 8432981 := bbase (se 11 (by rfl) ⟨6176, by rfl⟩ : syracuseStep 8432981 = 12353) (by norm_num)
theorem B3607901 : Blo 1480560 3607901 := bbase (se 3 (by rfl) ⟨676481, by rfl⟩ : syracuseStep 3607901 = 1352963) (by norm_num)
theorem B5623141 : Blo 1480560 5623141 := bbase (se 4 (by rfl) ⟨527169, by rfl⟩ : syracuseStep 5623141 = 1054339) (by norm_num)
theorem B1666417 : Blo 1480560 1666417 := bbase (se 2 (by rfl) ⟨624906, by rfl⟩ : syracuseStep 1666417 = 1249813) (by norm_num)
theorem B7499141 : Blo 1480560 7499141 := bbase (se 4 (by rfl) ⟨703044, by rfl⟩ : syracuseStep 7499141 = 1406089) (by norm_num)
theorem B1666453 : Blo 1480560 1666453 := bbase (se 6 (by rfl) ⟨39057, by rfl⟩ : syracuseStep 1666453 = 78115) (by norm_num)
theorem B2002333 : Blo 1480560 2002333 := bbase (se 3 (by rfl) ⟨375437, by rfl⟩ : syracuseStep 2002333 = 750875) (by norm_num)
theorem B1666489 : Blo 1480560 1666489 := bbase (se 2 (by rfl) ⟨624933, by rfl⟩ : syracuseStep 1666489 = 1249867) (by norm_num)
theorem B7212485 : Blo 1480560 7212485 := bbase (se 4 (by rfl) ⟨676170, by rfl⟩ : syracuseStep 7212485 = 1352341) (by norm_num)
theorem B1666525 : Blo 1480560 1666525 := bbase (se 3 (by rfl) ⟨312473, by rfl⟩ : syracuseStep 1666525 = 624947) (by norm_num)
theorem B1666561 : Blo 1480560 1666561 := bbase (se 2 (by rfl) ⟨624960, by rfl⟩ : syracuseStep 1666561 = 1249921) (by norm_num)
theorem B11406869 : Blo 1480560 11406869 := bbase (se 6 (by rfl) ⟨267348, by rfl⟩ : syracuseStep 11406869 = 534697) (by norm_num)
theorem B2534941 : Blo 1480560 2534941 := bbase (se 3 (by rfl) ⟨475301, by rfl⟩ : syracuseStep 2534941 = 950603) (by norm_num)
theorem B1666597 : Blo 1480560 1666597 := bbase (se 4 (by rfl) ⟨156243, by rfl⟩ : syracuseStep 1666597 = 312487) (by norm_num)
theorem B1666633 : Blo 1480560 1666633 := bbase (se 2 (by rfl) ⟨624987, by rfl⟩ : syracuseStep 1666633 = 1249975) (by norm_num)
theorem B1666669 : Blo 1480560 1666669 := bbase (se 3 (by rfl) ⟨312500, by rfl⟩ : syracuseStep 1666669 = 625001) (by norm_num)
theorem B1666705 : Blo 1480560 1666705 := bbase (se 2 (by rfl) ⟨625014, by rfl⟩ : syracuseStep 1666705 = 1250029) (by norm_num)
theorem B11398805 : Blo 1480560 11398805 := bbase (se 6 (by rfl) ⟨267159, by rfl⟩ : syracuseStep 11398805 = 534319) (by norm_num)
theorem B5623445 : Blo 1480560 5623445 := bbase (se 6 (by rfl) ⟨131799, by rfl⟩ : syracuseStep 5623445 = 263599) (by norm_num)
theorem B1666741 : Blo 1480560 1666741 := bbase (se 5 (by rfl) ⟨78128, by rfl⟩ : syracuseStep 1666741 = 156257) (by norm_num)
theorem B5000885 : Blo 1480560 5000885 := bbase (se 5 (by rfl) ⟨234416, by rfl⟩ : syracuseStep 5000885 = 468833) (by norm_num)
theorem B8113877 : Blo 1480560 8113877 := bbase (se 7 (by rfl) ⟨95084, by rfl⟩ : syracuseStep 8113877 = 190169) (by norm_num)
theorem B1666777 : Blo 1480560 1666777 := bbase (se 2 (by rfl) ⟨625041, by rfl⟩ : syracuseStep 1666777 = 1250083) (by norm_num)
theorem B1666813 : Blo 1480560 1666813 := bbase (se 3 (by rfl) ⟨312527, by rfl⟩ : syracuseStep 1666813 = 625055) (by norm_num)
theorem B1666849 : Blo 1480560 1666849 := bbase (se 2 (by rfl) ⟨625068, by rfl⟩ : syracuseStep 1666849 = 1250137) (by norm_num)
theorem B1666885 : Blo 1480560 1666885 := bbase (se 4 (by rfl) ⟨156270, by rfl⟩ : syracuseStep 1666885 = 312541) (by norm_num)
theorem B1666921 : Blo 1480560 1666921 := bbase (se 2 (by rfl) ⟨625095, by rfl⟩ : syracuseStep 1666921 = 1250191) (by norm_num)
theorem B14241653 : Blo 1480560 14241653 := bbase (se 5 (by rfl) ⟨667577, by rfl⟩ : syracuseStep 14241653 = 1335155) (by norm_num)
theorem B1666957 : Blo 1480560 1666957 := bbase (se 3 (by rfl) ⟨312554, by rfl⟩ : syracuseStep 1666957 = 625109) (by norm_num)
theorem B1666993 : Blo 1480560 1666993 := bbase (se 2 (by rfl) ⟨625122, by rfl⟩ : syracuseStep 1666993 = 1250245) (by norm_num)
theorem B1667029 : Blo 1480560 1667029 := bbase (se 7 (by rfl) ⟨19535, by rfl⟩ : syracuseStep 1667029 = 39071) (by norm_num)
theorem B3747829 : Blo 1480560 3747829 := bbase (se 5 (by rfl) ⟨175679, by rfl⟩ : syracuseStep 3747829 = 351359) (by norm_num)
theorem B1667065 : Blo 1480560 1667065 := bbase (se 2 (by rfl) ⟨625149, by rfl⟩ : syracuseStep 1667065 = 1250299) (by norm_num)
theorem B3379229 : Blo 1480560 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B1667101 : Blo 1480560 1667101 := bbase (se 3 (by rfl) ⟨312581, by rfl⟩ : syracuseStep 1667101 = 625163) (by norm_num)
theorem B2109493 : Blo 1480560 2109493 := bbase (se 5 (by rfl) ⟨98882, by rfl⟩ : syracuseStep 2109493 = 197765) (by norm_num)
theorem B1667137 : Blo 1480560 1667137 := bbase (se 2 (by rfl) ⟨625176, by rfl⟩ : syracuseStep 1667137 = 1250353) (by norm_num)
theorem B6754373 : Blo 1480560 6754373 := bbase (se 4 (by rfl) ⟨633222, by rfl⟩ : syracuseStep 6754373 = 1266445) (by norm_num)
theorem B3747941 : Blo 1480560 3747941 := bbase (se 4 (by rfl) ⟨351369, by rfl⟩ : syracuseStep 3747941 = 702739) (by norm_num)
theorem B5001317 : Blo 1480560 5001317 := bbase (se 4 (by rfl) ⟨468873, by rfl⟩ : syracuseStep 5001317 = 937747) (by norm_num)
theorem B1667173 : Blo 1480560 1667173 := bbase (se 4 (by rfl) ⟨156297, by rfl⟩ : syracuseStep 1667173 = 312595) (by norm_num)
theorem B1667209 : Blo 1480560 1667209 := bbase (se 2 (by rfl) ⟨625203, by rfl⟩ : syracuseStep 1667209 = 1250407) (by norm_num)
theorem B1667245 : Blo 1480560 1667245 := bbase (se 3 (by rfl) ⟨312608, by rfl⟩ : syracuseStep 1667245 = 625217) (by norm_num)
theorem B3903677 : Blo 1480560 3903677 := bbase (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) (by norm_num)
theorem B1667281 : Blo 1480560 1667281 := bbase (se 2 (by rfl) ⟨625230, by rfl⟩ : syracuseStep 1667281 = 1250461) (by norm_num)
theorem B1667317 : Blo 1480560 1667317 := bbase (se 5 (by rfl) ⟨78155, by rfl⟩ : syracuseStep 1667317 = 156311) (by norm_num)
theorem B2371853 : Blo 1480560 2371853 := bbase (se 3 (by rfl) ⟨444722, by rfl⟩ : syracuseStep 2371853 = 889445) (by norm_num)
theorem B3748133 : Blo 1480560 3748133 := bbase (se 4 (by rfl) ⟨351387, by rfl⟩ : syracuseStep 3748133 = 702775) (by norm_num)
theorem B2109829 : Blo 1480560 2109829 := bbase (se 4 (by rfl) ⟨197796, by rfl⟩ : syracuseStep 2109829 = 395593) (by norm_num)
theorem B3658133 : Blo 1480560 3658133 := bbase (se 6 (by rfl) ⟨85737, by rfl⟩ : syracuseStep 3658133 = 171475) (by norm_num)
theorem B8434165 : Blo 1480560 8434165 := bbase (se 5 (by rfl) ⟨395351, by rfl⟩ : syracuseStep 8434165 = 790703) (by norm_num)
theorem B5001749 : Blo 1480560 5001749 := bbase (se 6 (by rfl) ⟨117228, by rfl⟩ : syracuseStep 5001749 = 234457) (by norm_num)
theorem B2110045 : Blo 1480560 2110045 := bbase (se 3 (by rfl) ⟨395633, by rfl⟩ : syracuseStep 2110045 = 791267) (by norm_num)
theorem B3748477 : Blo 1480560 3748477 := bbase (se 3 (by rfl) ⟨702839, by rfl⟩ : syracuseStep 3748477 = 1405679) (by norm_num)
theorem B4747909 : Blo 1480560 4747909 := bbase (se 4 (by rfl) ⟨445116, by rfl⟩ : syracuseStep 4747909 = 890233) (by norm_num)
theorem B7500437 : Blo 1480560 7500437 := bbase (se 6 (by rfl) ⟨175791, by rfl⟩ : syracuseStep 7500437 = 351583) (by norm_num)
theorem B3560125 : Blo 1480560 3560125 := bbase (se 3 (by rfl) ⟨667523, by rfl⟩ : syracuseStep 3560125 = 1335047) (by norm_num)
theorem B22794965 : Blo 1480560 22794965 := bbase (se 7 (by rfl) ⟨267128, by rfl⟩ : syracuseStep 22794965 = 534257) (by norm_num)
theorem B3748589 : Blo 1480560 3748589 := bbase (se 3 (by rfl) ⟨702860, by rfl⟩ : syracuseStep 3748589 = 1405721) (by norm_num)
theorem B3380069 : Blo 1480560 3380069 := bbase (se 4 (by rfl) ⟨316881, by rfl⟩ : syracuseStep 3380069 = 633763) (by norm_num)
theorem B3748781 : Blo 1480560 3748781 := bbase (se 3 (by rfl) ⟨702896, by rfl⟩ : syracuseStep 3748781 = 1405793) (by norm_num)
theorem B2372789 : Blo 1480560 2372789 := bbase (se 5 (by rfl) ⟨111224, by rfl⟩ : syracuseStep 2372789 = 222449) (by norm_num)
theorem B3003581 : Blo 1480560 3003581 := bbase (se 3 (by rfl) ⟨563171, by rfl⟩ : syracuseStep 3003581 = 1126343) (by norm_num)
theorem B3331277 : Blo 1480560 3331277 := bbase (se 3 (by rfl) ⟨624614, by rfl⟩ : syracuseStep 3331277 = 1249229) (by norm_num)
theorem B6329573 : Blo 1480560 6329573 := bbase (se 4 (by rfl) ⟨593397, by rfl⟩ : syracuseStep 6329573 = 1186795) (by norm_num)
theorem B3749125 : Blo 1480560 3749125 := bbase (se 4 (by rfl) ⟨351480, by rfl⟩ : syracuseStep 3749125 = 702961) (by norm_num)
theorem B3331349 : Blo 1480560 3331349 := bbase (se 6 (by rfl) ⟨78078, by rfl⟩ : syracuseStep 3331349 = 156157) (by norm_num)
theorem B3331421 : Blo 1480560 3331421 := bbase (se 3 (by rfl) ⟨624641, by rfl⟩ : syracuseStep 3331421 = 1249283) (by norm_num)
theorem B3749237 : Blo 1480560 3749237 := bbase (se 5 (by rfl) ⟨175745, by rfl⟩ : syracuseStep 3749237 = 351491) (by norm_num)
theorem B3331493 : Blo 1480560 3331493 := bbase (se 4 (by rfl) ⟨312327, by rfl⟩ : syracuseStep 3331493 = 624655) (by norm_num)
theorem B3126701 : Blo 1480560 3126701 := bbase (se 3 (by rfl) ⟨586256, by rfl⟩ : syracuseStep 3126701 = 1172513) (by norm_num)
theorem B3331565 : Blo 1480560 3331565 := bbase (se 3 (by rfl) ⟨624668, by rfl⟩ : syracuseStep 3331565 = 1249337) (by norm_num)
theorem B3331637 : Blo 1480560 3331637 := bbase (se 5 (by rfl) ⟨156170, by rfl⟩ : syracuseStep 3331637 = 312341) (by norm_num)
theorem B3749429 : Blo 1480560 3749429 := bbase (se 5 (by rfl) ⟨175754, by rfl⟩ : syracuseStep 3749429 = 351509) (by norm_num)
theorem B3331709 : Blo 1480560 3331709 := bbase (se 3 (by rfl) ⟨624695, by rfl⟩ : syracuseStep 3331709 = 1249391) (by norm_num)
theorem B4273813 : Blo 1480560 4273813 := bbase (se 6 (by rfl) ⟨100167, by rfl⟩ : syracuseStep 4273813 = 200335) (by norm_num)
theorem B3331781 : Blo 1480560 3331781 := bbase (se 4 (by rfl) ⟨312354, by rfl⟩ : syracuseStep 3331781 = 624709) (by norm_num)
theorem B5625557 : Blo 1480560 5625557 := bbase (se 7 (by rfl) ⟨65924, by rfl⟩ : syracuseStep 5625557 = 131849) (by norm_num)
theorem B3331853 : Blo 1480560 3331853 := bbase (se 3 (by rfl) ⟨624722, by rfl⟩ : syracuseStep 3331853 = 1249445) (by norm_num)
theorem B2373437 : Blo 1480560 2373437 := bbase (se 3 (by rfl) ⟨445019, by rfl⟩ : syracuseStep 2373437 = 890039) (by norm_num)
theorem B3331925 : Blo 1480560 3331925 := bbase (se 9 (by rfl) ⟨9761, by rfl⟩ : syracuseStep 3331925 = 19523) (by norm_num)
theorem B3749773 : Blo 1480560 3749773 := bbase (se 3 (by rfl) ⟨703082, by rfl⟩ : syracuseStep 3749773 = 1406165) (by norm_num)
theorem B3331997 : Blo 1480560 3331997 := bbase (se 3 (by rfl) ⟨624749, by rfl⟩ : syracuseStep 3331997 = 1249499) (by norm_num)
theorem B7501733 : Blo 1480560 7501733 := bbase (se 4 (by rfl) ⟨703287, by rfl⟩ : syracuseStep 7501733 = 1406575) (by norm_num)
theorem B1873849 : Blo 1480560 1873849 := bbase (se 2 (by rfl) ⟨702693, by rfl⟩ : syracuseStep 1873849 = 1405387) (by norm_num)
theorem B3332069 : Blo 1480560 3332069 := bbase (se 4 (by rfl) ⟨312381, by rfl⟩ : syracuseStep 3332069 = 624763) (by norm_num)
theorem B5625845 : Blo 1480560 5625845 := bbase (se 5 (by rfl) ⟨263711, by rfl⟩ : syracuseStep 5625845 = 527423) (by norm_num)
theorem B3749885 : Blo 1480560 3749885 := bbase (se 3 (by rfl) ⟨703103, by rfl⟩ : syracuseStep 3749885 = 1406207) (by norm_num)
theorem B1873945 : Blo 1480560 1873945 := bbase (se 2 (by rfl) ⟨702729, by rfl⟩ : syracuseStep 1873945 = 1405459) (by norm_num)
theorem B3332141 : Blo 1480560 3332141 := bbase (se 3 (by rfl) ⟨624776, by rfl⟩ : syracuseStep 3332141 = 1249553) (by norm_num)
theorem B3332213 : Blo 1480560 3332213 := bbase (se 5 (by rfl) ⟨156197, by rfl⟩ : syracuseStep 3332213 = 312395) (by norm_num)
theorem B4216981 : Blo 1480560 4216981 := bbase (se 6 (by rfl) ⟨98835, by rfl⟩ : syracuseStep 4216981 = 197671) (by norm_num)
theorem B3332285 : Blo 1480560 3332285 := bbase (se 3 (by rfl) ⟨624803, by rfl⟩ : syracuseStep 3332285 = 1249607) (by norm_num)
theorem B3750077 : Blo 1480560 3750077 := bbase (se 3 (by rfl) ⟨703139, by rfl⟩ : syracuseStep 3750077 = 1406279) (by norm_num)
theorem B1874117 : Blo 1480560 1874117 := bbase (se 4 (by rfl) ⟨175698, by rfl⟩ : syracuseStep 1874117 = 351397) (by norm_num)
theorem B6330581 : Blo 1480560 6330581 := bbase (se 7 (by rfl) ⟨74186, by rfl⟩ : syracuseStep 6330581 = 148373) (by norm_num)
theorem B1874173 : Blo 1480560 1874173 := bbase (se 3 (by rfl) ⟨351407, by rfl⟩ : syracuseStep 1874173 = 702815) (by norm_num)
theorem B3332357 : Blo 1480560 3332357 := bbase (se 4 (by rfl) ⟨312408, by rfl⟩ : syracuseStep 3332357 = 624817) (by norm_num)
theorem B3332429 : Blo 1480560 3332429 := bbase (se 3 (by rfl) ⟨624830, by rfl⟩ : syracuseStep 3332429 = 1249661) (by norm_num)
theorem B1874269 : Blo 1480560 1874269 := bbase (se 3 (by rfl) ⟨351425, by rfl⟩ : syracuseStep 1874269 = 702851) (by norm_num)
theorem B3332501 : Blo 1480560 3332501 := bbase (se 6 (by rfl) ⟨78105, by rfl⟩ : syracuseStep 3332501 = 156211) (by norm_num)
theorem B6945173 : Blo 1480560 6945173 := bbase (se 6 (by rfl) ⟨162777, by rfl⟩ : syracuseStep 6945173 = 325555) (by norm_num)
theorem B2251165 : Blo 1480560 2251165 := bbase (se 3 (by rfl) ⟨422093, by rfl⟩ : syracuseStep 2251165 = 844187) (by norm_num)
theorem B8436149 : Blo 1480560 8436149 := bbase (se 5 (by rfl) ⟨395444, by rfl⟩ : syracuseStep 8436149 = 790889) (by norm_num)
theorem B8010197 : Blo 1480560 8010197 := bbase (se 7 (by rfl) ⟨93869, by rfl⟩ : syracuseStep 8010197 = 187739) (by norm_num)
theorem B2669021 : Blo 1480560 2669021 := bbase (se 3 (by rfl) ⟨500441, by rfl⟩ : syracuseStep 2669021 = 1000883) (by norm_num)
theorem B3332573 : Blo 1480560 3332573 := bbase (se 3 (by rfl) ⟨624857, by rfl⟩ : syracuseStep 3332573 = 1249715) (by norm_num)
theorem B2030069 : Blo 1480560 2030069 := bbase (se 5 (by rfl) ⟨95159, by rfl⟩ : syracuseStep 2030069 = 190319) (by norm_num)
theorem B1874441 : Blo 1480560 1874441 := bbase (se 2 (by rfl) ⟨702915, by rfl⟩ : syracuseStep 1874441 = 1405831) (by norm_num)
theorem B3750421 : Blo 1480560 3750421 := bbase (se 6 (by rfl) ⟨87900, by rfl⟩ : syracuseStep 3750421 = 175801) (by norm_num)
theorem B3332645 : Blo 1480560 3332645 := bbase (se 4 (by rfl) ⟨312435, by rfl⟩ : syracuseStep 3332645 = 624871) (by norm_num)
theorem B1874497 : Blo 1480560 1874497 := bbase (se 2 (by rfl) ⟨702936, by rfl⟩ : syracuseStep 1874497 = 1405873) (by norm_num)
theorem B3332717 : Blo 1480560 3332717 := bbase (se 3 (by rfl) ⟨624884, by rfl⟩ : syracuseStep 3332717 = 1249769) (by norm_num)
theorem B3750533 : Blo 1480560 3750533 := bbase (se 4 (by rfl) ⟨351612, by rfl⟩ : syracuseStep 3750533 = 703225) (by norm_num)
theorem B1874593 : Blo 1480560 1874593 := bbase (se 2 (by rfl) ⟨702972, by rfl⟩ : syracuseStep 1874593 = 1405945) (by norm_num)
theorem B3332789 : Blo 1480560 3332789 := bbase (se 5 (by rfl) ⟨156224, by rfl⟩ : syracuseStep 3332789 = 312449) (by norm_num)
theorem B12655349 : Blo 1480560 12655349 := bbase (se 5 (by rfl) ⟨593219, by rfl⟩ : syracuseStep 12655349 = 1186439) (by norm_num)
theorem B3332861 : Blo 1480560 3332861 := bbase (se 3 (by rfl) ⟨624911, by rfl⟩ : syracuseStep 3332861 = 1249823) (by norm_num)
theorem B4275013 : Blo 1480560 4275013 := bbase (se 4 (by rfl) ⟨400782, by rfl⟩ : syracuseStep 4275013 = 801565) (by norm_num)
theorem B3332933 : Blo 1480560 3332933 := bbase (se 4 (by rfl) ⟨312462, by rfl⟩ : syracuseStep 3332933 = 624925) (by norm_num)
theorem B3750725 : Blo 1480560 3750725 := bbase (se 4 (by rfl) ⟨351630, by rfl⟩ : syracuseStep 3750725 = 703261) (by norm_num)
theorem B1874765 : Blo 1480560 1874765 := bbase (se 3 (by rfl) ⟨351518, by rfl⟩ : syracuseStep 1874765 = 703037) (by norm_num)
theorem B1874821 : Blo 1480560 1874821 := bbase (se 4 (by rfl) ⟨175764, by rfl⟩ : syracuseStep 1874821 = 351529) (by norm_num)
theorem B3333005 : Blo 1480560 3333005 := bbase (se 3 (by rfl) ⟨624938, by rfl⟩ : syracuseStep 3333005 = 1249877) (by norm_num)
theorem B3333077 : Blo 1480560 3333077 := bbase (se 7 (by rfl) ⟨39059, by rfl⟩ : syracuseStep 3333077 = 78119) (by norm_num)
theorem B1874917 : Blo 1480560 1874917 := bbase (se 4 (by rfl) ⟨175773, by rfl⟩ : syracuseStep 1874917 = 351547) (by norm_num)
theorem B3333149 : Blo 1480560 3333149 := bbase (se 3 (by rfl) ⟨624965, by rfl⟩ : syracuseStep 3333149 = 1249931) (by norm_num)
theorem B2849869 : Blo 1480560 2849869 := bbase (se 3 (by rfl) ⟨534350, by rfl⟩ : syracuseStep 2849869 = 1068701) (by norm_num)
theorem B3333221 : Blo 1480560 3333221 := bbase (se 4 (by rfl) ⟨312489, by rfl⟩ : syracuseStep 3333221 = 624979) (by norm_num)
theorem B5700725 : Blo 1480560 5700725 := bbase (se 5 (by rfl) ⟨267221, by rfl⟩ : syracuseStep 5700725 = 534443) (by norm_num)
theorem B1875089 : Blo 1480560 1875089 := bbase (se 2 (by rfl) ⟨703158, by rfl⟩ : syracuseStep 1875089 = 1406317) (by norm_num)
theorem B5627029 : Blo 1480560 5627029 := bbase (se 6 (by rfl) ⟨131883, by rfl⟩ : syracuseStep 5627029 = 263767) (by norm_num)
theorem B3751069 : Blo 1480560 3751069 := bbase (se 3 (by rfl) ⟨703325, by rfl⟩ : syracuseStep 3751069 = 1406651) (by norm_num)
theorem B3333293 : Blo 1480560 3333293 := bbase (se 3 (by rfl) ⟨624992, by rfl⟩ : syracuseStep 3333293 = 1249985) (by norm_num)
theorem B1875145 : Blo 1480560 1875145 := bbase (se 2 (by rfl) ⟨703179, by rfl⟩ : syracuseStep 1875145 = 1406359) (by norm_num)
theorem B4218085 : Blo 1480560 4218085 := bbase (se 4 (by rfl) ⟨395445, by rfl⟩ : syracuseStep 4218085 = 790891) (by norm_num)
theorem B3333365 : Blo 1480560 3333365 := bbase (se 5 (by rfl) ⟨156251, by rfl⟩ : syracuseStep 3333365 = 312503) (by norm_num)
theorem B3751181 : Blo 1480560 3751181 := bbase (se 3 (by rfl) ⟨703346, by rfl⟩ : syracuseStep 3751181 = 1406693) (by norm_num)
theorem B1875241 : Blo 1480560 1875241 := bbase (se 2 (by rfl) ⟨703215, by rfl⟩ : syracuseStep 1875241 = 1406431) (by norm_num)
theorem B3333437 : Blo 1480560 3333437 := bbase (se 3 (by rfl) ⟨625019, by rfl⟩ : syracuseStep 3333437 = 1250039) (by norm_num)
theorem B3333509 : Blo 1480560 3333509 := bbase (se 4 (by rfl) ⟨312516, by rfl⟩ : syracuseStep 3333509 = 625033) (by norm_num)
theorem B4504981 : Blo 1480560 4504981 := bbase (se 6 (by rfl) ⟨105585, by rfl⟩ : syracuseStep 4504981 = 211171) (by norm_num)
theorem B3333581 : Blo 1480560 3333581 := bbase (se 3 (by rfl) ⟨625046, by rfl⟩ : syracuseStep 3333581 = 1250093) (by norm_num)
theorem B3751373 : Blo 1480560 3751373 := bbase (se 3 (by rfl) ⟨703382, by rfl⟩ : syracuseStep 3751373 = 1406765) (by norm_num)
theorem B9493973 : Blo 1480560 9493973 := bbase (se 7 (by rfl) ⟨111257, by rfl⟩ : syracuseStep 9493973 = 222515) (by norm_num)
theorem B1875413 : Blo 1480560 1875413 := bbase (se 7 (by rfl) ⟨21977, by rfl⟩ : syracuseStep 1875413 = 43955) (by norm_num)
theorem B1875469 : Blo 1480560 1875469 := bbase (se 3 (by rfl) ⟨351650, by rfl⟩ : syracuseStep 1875469 = 703301) (by norm_num)
theorem B3333653 : Blo 1480560 3333653 := bbase (se 6 (by rfl) ⟨78132, by rfl⟩ : syracuseStep 3333653 = 156265) (by norm_num)
theorem B7118405 : Blo 1480560 7118405 := bbase (se 4 (by rfl) ⟨667350, by rfl⟩ : syracuseStep 7118405 = 1334701) (by norm_num)
theorem B3333725 : Blo 1480560 3333725 := bbase (se 3 (by rfl) ⟨625073, by rfl⟩ : syracuseStep 3333725 = 1250147) (by norm_num)
theorem B1875565 : Blo 1480560 1875565 := bbase (se 3 (by rfl) ⟨351668, by rfl⟩ : syracuseStep 1875565 = 703337) (by norm_num)
theorem B5340821 : Blo 1480560 5340821 := bbase (se 6 (by rfl) ⟨125175, by rfl⟩ : syracuseStep 5340821 = 250351) (by norm_num)
theorem B3333797 : Blo 1480560 3333797 := bbase (se 4 (by rfl) ⟨312543, by rfl⟩ : syracuseStep 3333797 = 625087) (by norm_num)
theorem B1900201 : Blo 1480560 1900201 := bbase (se 2 (by rfl) ⟨712575, by rfl⟩ : syracuseStep 1900201 = 1425151) (by norm_num)
theorem B3333869 : Blo 1480560 3333869 := bbase (se 3 (by rfl) ⟨625100, by rfl⟩ : syracuseStep 3333869 = 1250201) (by norm_num)
theorem B6004469 : Blo 1480560 6004469 := bbase (se 5 (by rfl) ⟨281459, by rfl⟩ : syracuseStep 6004469 = 562919) (by norm_num)
theorem B3333941 : Blo 1480560 3333941 := bbase (se 5 (by rfl) ⟨156278, by rfl⟩ : syracuseStep 3333941 = 312557) (by norm_num)
theorem B100081493 : Blo 1480560 100081493 := bbase (se 9 (by rfl) ⟨293207, by rfl⟩ : syracuseStep 100081493 = 586415) (by norm_num)
theorem B6004597 : Blo 1480560 6004597 := bbase (se 5 (by rfl) ⟨281465, by rfl⟩ : syracuseStep 6004597 = 562931) (by norm_num)
theorem B3334013 : Blo 1480560 3334013 := bbase (se 3 (by rfl) ⟨625127, by rfl⟩ : syracuseStep 3334013 = 1250255) (by norm_num)
theorem B4996997 : Blo 1480560 4996997 := bbase (se 4 (by rfl) ⟨468468, by rfl⟩ : syracuseStep 4996997 = 936937) (by norm_num)
theorem B2498485 : Blo 1480560 2498485 := bbase (se 5 (by rfl) ⟨117116, by rfl⟩ : syracuseStep 2498485 = 234233) (by norm_num)
theorem B3334085 : Blo 1480560 3334085 := bbase (se 4 (by rfl) ⟨312570, by rfl⟩ : syracuseStep 3334085 = 625141) (by norm_num)
theorem B2252819 : Blo 1480560 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B2498593 : Blo 1480560 2498593 := bstep (se 2 (by rfl) ⟨936972, by rfl⟩ : syracuseStep 2498593 = 1873945) B1873945
theorem B4218929 : Blo 1480560 4218929 := bstep (se 2 (by rfl) ⟨1582098, by rfl⟩ : syracuseStep 4218929 = 3164197) B3164197
theorem B3334193 : Blo 1480560 3334193 := bstep (se 2 (by rfl) ⟨1250322, by rfl⟩ : syracuseStep 3334193 = 2500645) B2500645
theorem B2498627 : Blo 1480560 2498627 := bstep (se 1 (by rfl) ⟨1873970, by rfl⟩ : syracuseStep 2498627 = 3747941) B3747941
theorem B3334211 : Blo 1480560 3334211 := bstep (se 1 (by rfl) ⟨2500658, by rfl⟩ : syracuseStep 3334211 = 5001317) B5001317
theorem B2498755 : Blo 1480560 2498755 := bstep (se 1 (by rfl) ⟨1874066, by rfl⟩ : syracuseStep 2498755 = 3748133) B3748133
theorem B2498897 : Blo 1480560 2498897 := bstep (se 2 (by rfl) ⟨937086, by rfl⟩ : syracuseStep 2498897 = 1874173) B1874173
theorem B3334481 : Blo 1480560 3334481 := bstep (se 2 (by rfl) ⟨1250430, by rfl⟩ : syracuseStep 3334481 = 2500861) B2500861
theorem B3334499 : Blo 1480560 3334499 := bstep (se 1 (by rfl) ⟨2500874, by rfl⟩ : syracuseStep 3334499 = 5001749) B5001749
theorem B2499025 : Blo 1480560 2499025 := bstep (se 2 (by rfl) ⟨937134, by rfl⟩ : syracuseStep 2499025 = 1874269) B1874269
theorem B15196643 : Blo 1480560 15196643 := bstep (se 1 (by rfl) ⟨11397482, by rfl⟩ : syracuseStep 15196643 = 22794965) B22794965
theorem B17334755 : Blo 1480560 17334755 := bstep (se 1 (by rfl) ⟨13001066, by rfl⟩ : syracuseStep 17334755 = 26002133) B26002133
theorem B2499059 : Blo 1480560 2499059 := bstep (se 1 (by rfl) ⟨1874294, by rfl⟩ : syracuseStep 2499059 = 3748589) B3748589
theorem B4997645 : Blo 1480560 4997645 := bstep (se 3 (by rfl) ⟨937058, by rfl⟩ : syracuseStep 4997645 = 1874117) B1874117
theorem B4997699 : Blo 1480560 4997699 := bstep (se 1 (by rfl) ⟨3748274, by rfl⟩ : syracuseStep 4997699 = 7496549) B7496549
theorem B4506221 : Blo 1480560 4506221 := bstep (se 3 (by rfl) ⟨844916, by rfl⟩ : syracuseStep 4506221 = 1689833) B1689833
theorem B2499187 : Blo 1480560 2499187 := bstep (se 1 (by rfl) ⟨1874390, by rfl⟩ : syracuseStep 2499187 = 3748781) B3748781
theorem B6324941 : Blo 1480560 6324941 := bstep (se 3 (by rfl) ⟨1185926, by rfl⟩ : syracuseStep 6324941 = 2371853) B2371853
theorem B10674929 : Blo 1480560 10674929 := bstep (se 2 (by rfl) ⟨4003098, by rfl⟩ : syracuseStep 10674929 = 8006197) B8006197
theorem B2499329 : Blo 1480560 2499329 := bstep (se 2 (by rfl) ⟨937248, by rfl⟩ : syracuseStep 2499329 = 1874497) B1874497
theorem B1581859 : Blo 1480560 1581859 := bstep (se 1 (by rfl) ⟨1186394, by rfl⟩ : syracuseStep 1581859 = 2372789) B2372789
theorem B2220851 : Blo 1480560 2220851 := bstep (se 1 (by rfl) ⟨1665638, by rfl⟩ : syracuseStep 2220851 = 3331277) B3331277
theorem B4219715 : Blo 1480560 4219715 := bstep (se 1 (by rfl) ⟨3164786, by rfl⟩ : syracuseStep 4219715 = 6329573) B6329573
theorem B4744013 : Blo 1480560 4744013 := bstep (se 3 (by rfl) ⟨889502, by rfl⟩ : syracuseStep 4744013 = 1779005) B1779005
theorem B2220881 : Blo 1480560 2220881 := bstep (se 2 (by rfl) ⟨832830, by rfl⟩ : syracuseStep 2220881 = 1665661) B1665661
theorem B4997969 : Blo 1480560 4997969 := bstep (se 2 (by rfl) ⟨1874238, by rfl⟩ : syracuseStep 4997969 = 3748477) B3748477
theorem B2220899 : Blo 1480560 2220899 := bstep (se 1 (by rfl) ⟨1665674, by rfl⟩ : syracuseStep 2220899 = 3331349) B3331349
theorem B2220929 : Blo 1480560 2220929 := bstep (se 2 (by rfl) ⟨832848, by rfl⟩ : syracuseStep 2220929 = 1665697) B1665697
theorem B2499457 : Blo 1480560 2499457 := bstep (se 2 (by rfl) ⟨937296, by rfl⟩ : syracuseStep 2499457 = 1874593) B1874593
theorem B2220947 : Blo 1480560 2220947 := bstep (se 1 (by rfl) ⟨1665710, by rfl⟩ : syracuseStep 2220947 = 3331421) B3331421
theorem B2499491 : Blo 1480560 2499491 := bstep (se 1 (by rfl) ⟨1874618, by rfl⟩ : syracuseStep 2499491 = 3749237) B3749237
theorem B2220977 : Blo 1480560 2220977 := bstep (se 2 (by rfl) ⟨832866, by rfl⟩ : syracuseStep 2220977 = 1665733) B1665733
theorem B2220995 : Blo 1480560 2220995 := bstep (se 1 (by rfl) ⟨1665746, by rfl⟩ : syracuseStep 2220995 = 3331493) B3331493
theorem B2221025 : Blo 1480560 2221025 := bstep (se 2 (by rfl) ⟨832884, by rfl⟩ : syracuseStep 2221025 = 1665769) B1665769
theorem B1803235 : Blo 1480560 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B2221043 : Blo 1480560 2221043 := bstep (se 1 (by rfl) ⟨1665782, by rfl⟩ : syracuseStep 2221043 = 3331565) B3331565
theorem B2221073 : Blo 1480560 2221073 := bstep (se 2 (by rfl) ⟨832902, by rfl⟩ : syracuseStep 2221073 = 1665805) B1665805
theorem B2221091 : Blo 1480560 2221091 := bstep (se 1 (by rfl) ⟨1665818, by rfl⟩ : syracuseStep 2221091 = 3331637) B3331637
theorem B6325283 : Blo 1480560 6325283 := bstep (se 1 (by rfl) ⟨4743962, by rfl⟩ : syracuseStep 6325283 = 9487925) B9487925
theorem B2499619 : Blo 1480560 2499619 := bstep (se 1 (by rfl) ⟨1874714, by rfl⟩ : syracuseStep 2499619 = 3749429) B3749429
theorem B2221121 : Blo 1480560 2221121 := bstep (se 2 (by rfl) ⟨832920, by rfl⟩ : syracuseStep 2221121 = 1665841) B1665841
theorem B2221139 : Blo 1480560 2221139 := bstep (se 1 (by rfl) ⟨1665854, by rfl⟩ : syracuseStep 2221139 = 3331709) B3331709
theorem B2221169 : Blo 1480560 2221169 := bstep (se 2 (by rfl) ⟨832938, by rfl⟩ : syracuseStep 2221169 = 1665877) B1665877
theorem B2221187 : Blo 1480560 2221187 := bstep (se 1 (by rfl) ⟨1665890, by rfl⟩ : syracuseStep 2221187 = 3331781) B3331781
theorem B4220045 : Blo 1480560 4220045 := bstep (se 3 (by rfl) ⟨791258, by rfl⟩ : syracuseStep 4220045 = 1582517) B1582517
theorem B2221217 : Blo 1480560 2221217 := bstep (se 2 (by rfl) ⟨832956, by rfl⟩ : syracuseStep 2221217 = 1665913) B1665913
theorem B2499761 : Blo 1480560 2499761 := bstep (se 2 (by rfl) ⟨937410, by rfl⟩ : syracuseStep 2499761 = 1874821) B1874821
theorem B2221235 : Blo 1480560 2221235 := bstep (se 1 (by rfl) ⟨1665926, by rfl⟩ : syracuseStep 2221235 = 3331853) B3331853
theorem B2221265 : Blo 1480560 2221265 := bstep (se 2 (by rfl) ⟨832974, by rfl⟩ : syracuseStep 2221265 = 1665949) B1665949
theorem B4220113 : Blo 1480560 4220113 := bstep (se 2 (by rfl) ⟨1582542, by rfl⟩ : syracuseStep 4220113 = 3165085) B3165085
theorem B1582291 : Blo 1480560 1582291 := bstep (se 1 (by rfl) ⟨1186718, by rfl⟩ : syracuseStep 1582291 = 2373437) B2373437
theorem B2221283 : Blo 1480560 2221283 := bstep (se 1 (by rfl) ⟨1665962, by rfl⟩ : syracuseStep 2221283 = 3331925) B3331925
theorem B2221313 : Blo 1480560 2221313 := bstep (se 2 (by rfl) ⟨832992, by rfl⟩ : syracuseStep 2221313 = 1665985) B1665985
theorem B2221331 : Blo 1480560 2221331 := bstep (se 1 (by rfl) ⟨1665998, by rfl⟩ : syracuseStep 2221331 = 3331997) B3331997
theorem B2221361 : Blo 1480560 2221361 := bstep (se 2 (by rfl) ⟨833010, by rfl⟩ : syracuseStep 2221361 = 1666021) B1666021
theorem B2499889 : Blo 1480560 2499889 := bstep (se 2 (by rfl) ⟨937458, by rfl⟩ : syracuseStep 2499889 = 1874917) B1874917
theorem B2221379 : Blo 1480560 2221379 := bstep (se 1 (by rfl) ⟨1666034, by rfl⟩ : syracuseStep 2221379 = 3332069) B3332069
theorem B2499923 : Blo 1480560 2499923 := bstep (se 1 (by rfl) ⟨1874942, by rfl⟩ : syracuseStep 2499923 = 3749885) B3749885
theorem B2221409 : Blo 1480560 2221409 := bstep (se 2 (by rfl) ⟨833028, by rfl⟩ : syracuseStep 2221409 = 1666057) B1666057
theorem B4998509 : Blo 1480560 4998509 := bstep (se 3 (by rfl) ⟨937220, by rfl⟩ : syracuseStep 4998509 = 1874441) B1874441
theorem B2221427 : Blo 1480560 2221427 := bstep (se 1 (by rfl) ⟨1666070, by rfl⟩ : syracuseStep 2221427 = 3332141) B3332141
theorem B2221457 : Blo 1480560 2221457 := bstep (se 2 (by rfl) ⟨833046, by rfl⟩ : syracuseStep 2221457 = 1666093) B1666093
theorem B2221475 : Blo 1480560 2221475 := bstep (se 1 (by rfl) ⟨1666106, by rfl⟩ : syracuseStep 2221475 = 3332213) B3332213
theorem B4998563 : Blo 1480560 4998563 := bstep (se 1 (by rfl) ⟨3748922, by rfl⟩ : syracuseStep 4998563 = 7497845) B7497845
theorem B2221505 : Blo 1480560 2221505 := bstep (se 2 (by rfl) ⟨833064, by rfl⟩ : syracuseStep 2221505 = 1666129) B1666129
theorem B2221523 : Blo 1480560 2221523 := bstep (se 1 (by rfl) ⟨1666142, by rfl⟩ : syracuseStep 2221523 = 3332285) B3332285
theorem B2500051 : Blo 1480560 2500051 := bstep (se 1 (by rfl) ⟨1875038, by rfl⟩ : syracuseStep 2500051 = 3750077) B3750077
theorem B4220387 : Blo 1480560 4220387 := bstep (se 1 (by rfl) ⟨3165290, by rfl⟩ : syracuseStep 4220387 = 6330581) B6330581
theorem B2221553 : Blo 1480560 2221553 := bstep (se 2 (by rfl) ⟨833082, by rfl⟩ : syracuseStep 2221553 = 1666165) B1666165
theorem B2221571 : Blo 1480560 2221571 := bstep (se 1 (by rfl) ⟨1666178, by rfl⟩ : syracuseStep 2221571 = 3332357) B3332357
theorem B2221601 : Blo 1480560 2221601 := bstep (se 2 (by rfl) ⟨833100, by rfl⟩ : syracuseStep 2221601 = 1666201) B1666201
theorem B2221619 : Blo 1480560 2221619 := bstep (se 1 (by rfl) ⟨1666214, by rfl⟩ : syracuseStep 2221619 = 3332429) B3332429
theorem B2221649 : Blo 1480560 2221649 := bstep (se 2 (by rfl) ⟨833118, by rfl⟩ : syracuseStep 2221649 = 1666237) B1666237
theorem B2500193 : Blo 1480560 2500193 := bstep (se 2 (by rfl) ⟨937572, by rfl⟩ : syracuseStep 2500193 = 1875145) B1875145
theorem B2221667 : Blo 1480560 2221667 := bstep (se 1 (by rfl) ⟨1666250, by rfl⟩ : syracuseStep 2221667 = 3332501) B3332501
theorem B4630115 : Blo 1480560 4630115 := bstep (se 1 (by rfl) ⟨3472586, by rfl⟩ : syracuseStep 4630115 = 6945173) B6945173
theorem B2221697 : Blo 1480560 2221697 := bstep (se 2 (by rfl) ⟨833136, by rfl⟩ : syracuseStep 2221697 = 1666273) B1666273
theorem B1779347 : Blo 1480560 1779347 := bstep (se 1 (by rfl) ⟨1334510, by rfl⟩ : syracuseStep 1779347 = 2669021) B2669021
theorem B2221715 : Blo 1480560 2221715 := bstep (se 1 (by rfl) ⟨1666286, by rfl⟩ : syracuseStep 2221715 = 3332573) B3332573
theorem B4998833 : Blo 1480560 4998833 := bstep (se 2 (by rfl) ⟨1874562, by rfl⟩ : syracuseStep 4998833 = 3749125) B3749125
theorem B2221745 : Blo 1480560 2221745 := bstep (se 2 (by rfl) ⟨833154, by rfl⟩ : syracuseStep 2221745 = 1666309) B1666309
theorem B2221763 : Blo 1480560 2221763 := bstep (se 1 (by rfl) ⟨1666322, by rfl⟩ : syracuseStep 2221763 = 3332645) B3332645
theorem B2811601 : Blo 1480560 2811601 := bstep (se 2 (by rfl) ⟨1054350, by rfl⟩ : syracuseStep 2811601 = 2108701) B2108701
theorem B2221793 : Blo 1480560 2221793 := bstep (se 2 (by rfl) ⟨833172, by rfl⟩ : syracuseStep 2221793 = 1666345) B1666345
theorem B2500321 : Blo 1480560 2500321 := bstep (se 2 (by rfl) ⟨937620, by rfl⟩ : syracuseStep 2500321 = 1875241) B1875241
theorem B2221811 : Blo 1480560 2221811 := bstep (se 1 (by rfl) ⟨1666358, by rfl⟩ : syracuseStep 2221811 = 3332717) B3332717
theorem B2500355 : Blo 1480560 2500355 := bstep (se 1 (by rfl) ⟨1875266, by rfl⟩ : syracuseStep 2500355 = 3750533) B3750533
theorem B2221841 : Blo 1480560 2221841 := bstep (se 2 (by rfl) ⟨833190, by rfl⟩ : syracuseStep 2221841 = 1666381) B1666381
theorem B2221859 : Blo 1480560 2221859 := bstep (se 1 (by rfl) ⟨1666394, by rfl⟩ : syracuseStep 2221859 = 3332789) B3332789
theorem B7497521 : Blo 1480560 7497521 := bstep (se 2 (by rfl) ⟨2811570, by rfl⟩ : syracuseStep 7497521 = 5623141) B5623141
theorem B1689395 : Blo 1480560 1689395 := bstep (se 1 (by rfl) ⟨1267046, by rfl⟩ : syracuseStep 1689395 = 2534093) B2534093
theorem B2221889 : Blo 1480560 2221889 := bstep (se 2 (by rfl) ⟨833208, by rfl⟩ : syracuseStep 2221889 = 1666417) B1666417
theorem B2221907 : Blo 1480560 2221907 := bstep (se 1 (by rfl) ⟨1666430, by rfl⟩ : syracuseStep 2221907 = 3332861) B3332861
theorem B2221937 : Blo 1480560 2221937 := bstep (se 2 (by rfl) ⟨833226, by rfl⟩ : syracuseStep 2221937 = 1666453) B1666453
theorem B6006641 : Blo 1480560 6006641 := bstep (se 2 (by rfl) ⟨2252490, by rfl⟩ : syracuseStep 6006641 = 4504981) B4504981
theorem B2221955 : Blo 1480560 2221955 := bstep (se 1 (by rfl) ⟨1666466, by rfl⟩ : syracuseStep 2221955 = 3332933) B3332933
theorem B3164035 : Blo 1480560 3164035 := bstep (se 1 (by rfl) ⟨2373026, by rfl⟩ : syracuseStep 3164035 = 4746053) B4746053
theorem B2500483 : Blo 1480560 2500483 := bstep (se 1 (by rfl) ⟨1875362, by rfl⟩ : syracuseStep 2500483 = 3750725) B3750725
theorem B2221985 : Blo 1480560 2221985 := bstep (se 2 (by rfl) ⟨833244, by rfl⟩ : syracuseStep 2221985 = 1666489) B1666489
theorem B2222003 : Blo 1480560 2222003 := bstep (se 1 (by rfl) ⟨1666502, by rfl⟩ : syracuseStep 2222003 = 3333005) B3333005
theorem B3377105 : Blo 1480560 3377105 := bstep (se 2 (by rfl) ⟨1266414, by rfl⟩ : syracuseStep 3377105 = 2532829) B2532829
theorem B2222033 : Blo 1480560 2222033 := bstep (se 2 (by rfl) ⟨833262, by rfl⟩ : syracuseStep 2222033 = 1666525) B1666525
theorem B2222051 : Blo 1480560 2222051 := bstep (se 1 (by rfl) ⟨1666538, by rfl⟩ : syracuseStep 2222051 = 3333077) B3333077
theorem B2222081 : Blo 1480560 2222081 := bstep (se 2 (by rfl) ⟨833280, by rfl⟩ : syracuseStep 2222081 = 1666561) B1666561
theorem B2500625 : Blo 1480560 2500625 := bstep (se 2 (by rfl) ⟨937734, by rfl⟩ : syracuseStep 2500625 = 1875469) B1875469
theorem B2222099 : Blo 1480560 2222099 := bstep (se 1 (by rfl) ⟨1666574, by rfl⟩ : syracuseStep 2222099 = 3333149) B3333149
theorem B2222129 : Blo 1480560 2222129 := bstep (se 2 (by rfl) ⟨833298, by rfl⟩ : syracuseStep 2222129 = 1666597) B1666597
theorem B2222147 : Blo 1480560 2222147 := bstep (se 1 (by rfl) ⟨1666610, by rfl⟩ : syracuseStep 2222147 = 3333221) B3333221
theorem B2222177 : Blo 1480560 2222177 := bstep (se 2 (by rfl) ⟨833316, by rfl⟩ : syracuseStep 2222177 = 1666633) B1666633
theorem B2222195 : Blo 1480560 2222195 := bstep (se 1 (by rfl) ⟨1666646, by rfl⟩ : syracuseStep 2222195 = 3333293) B3333293
theorem B2222225 : Blo 1480560 2222225 := bstep (se 2 (by rfl) ⟨833334, by rfl⟩ : syracuseStep 2222225 = 1666669) B1666669
theorem B2500753 : Blo 1480560 2500753 := bstep (se 2 (by rfl) ⟨937782, by rfl⟩ : syracuseStep 2500753 = 1875565) B1875565
theorem B2222243 : Blo 1480560 2222243 := bstep (se 1 (by rfl) ⟨1666682, by rfl⟩ : syracuseStep 2222243 = 3333365) B3333365
theorem B2500787 : Blo 1480560 2500787 := bstep (se 1 (by rfl) ⟨1875590, by rfl⟩ : syracuseStep 2500787 = 3751181) B3751181
theorem B2222273 : Blo 1480560 2222273 := bstep (se 2 (by rfl) ⟨833352, by rfl⟩ : syracuseStep 2222273 = 1666705) B1666705
theorem B4999373 : Blo 1480560 4999373 := bstep (se 3 (by rfl) ⟨937382, by rfl⟩ : syracuseStep 4999373 = 1874765) B1874765
theorem B2222291 : Blo 1480560 2222291 := bstep (se 1 (by rfl) ⟨1666718, by rfl⟩ : syracuseStep 2222291 = 3333437) B3333437
theorem B2533601 : Blo 1480560 2533601 := bstep (se 2 (by rfl) ⟨950100, by rfl⟩ : syracuseStep 2533601 = 1900201) B1900201
theorem B5621987 : Blo 1480560 5621987 := bstep (se 1 (by rfl) ⟨4216490, by rfl⟩ : syracuseStep 5621987 = 8432981) B8432981
theorem B2222321 : Blo 1480560 2222321 := bstep (se 2 (by rfl) ⟨833370, by rfl⟩ : syracuseStep 2222321 = 1666741) B1666741
theorem B4999427 : Blo 1480560 4999427 := bstep (se 1 (by rfl) ⟨3749570, by rfl⟩ : syracuseStep 4999427 = 7499141) B7499141
theorem B2222339 : Blo 1480560 2222339 := bstep (se 1 (by rfl) ⟨1666754, by rfl⟩ : syracuseStep 2222339 = 3333509) B3333509
theorem B9013517 : Blo 1480560 9013517 := bstep (se 3 (by rfl) ⟨1690034, by rfl⟩ : syracuseStep 9013517 = 3380069) B3380069
theorem B2222369 : Blo 1480560 2222369 := bstep (se 2 (by rfl) ⟨833388, by rfl⟩ : syracuseStep 2222369 = 1666777) B1666777
theorem B2222387 : Blo 1480560 2222387 := bstep (se 1 (by rfl) ⟨1666790, by rfl⟩ : syracuseStep 2222387 = 3333581) B3333581
theorem B2500915 : Blo 1480560 2500915 := bstep (se 1 (by rfl) ⟨1875686, by rfl⟩ : syracuseStep 2500915 = 3751373) B3751373
theorem B2222417 : Blo 1480560 2222417 := bstep (se 2 (by rfl) ⟨833406, by rfl⟩ : syracuseStep 2222417 = 1666813) B1666813
theorem B2222435 : Blo 1480560 2222435 := bstep (se 1 (by rfl) ⟨1666826, by rfl⟩ : syracuseStep 2222435 = 3333653) B3333653
theorem B7604579 : Blo 1480560 7604579 := bstep (se 1 (by rfl) ⟨5703434, by rfl⟩ : syracuseStep 7604579 = 11406869) B11406869
theorem B2222465 : Blo 1480560 2222465 := bstep (se 2 (by rfl) ⟨833424, by rfl⟩ : syracuseStep 2222465 = 1666849) B1666849
theorem B4745603 : Blo 1480560 4745603 := bstep (se 1 (by rfl) ⟨3559202, by rfl⟩ : syracuseStep 4745603 = 7118405) B7118405
theorem B2222483 : Blo 1480560 2222483 := bstep (se 1 (by rfl) ⟨1666862, by rfl⟩ : syracuseStep 2222483 = 3333725) B3333725
theorem B2222513 : Blo 1480560 2222513 := bstep (se 2 (by rfl) ⟨833442, by rfl⟩ : syracuseStep 2222513 = 1666885) B1666885
theorem B2222531 : Blo 1480560 2222531 := bstep (se 1 (by rfl) ⟨1666898, by rfl⟩ : syracuseStep 2222531 = 3333797) B3333797
theorem B5409251 : Blo 1480560 5409251 := bstep (se 1 (by rfl) ⟨4056938, by rfl⟩ : syracuseStep 5409251 = 8113877) B8113877
theorem B2222561 : Blo 1480560 2222561 := bstep (se 2 (by rfl) ⟨833460, by rfl⟩ : syracuseStep 2222561 = 1666921) B1666921
theorem B8006129 : Blo 1480560 8006129 := bstep (se 2 (by rfl) ⟨3002298, by rfl⟩ : syracuseStep 8006129 = 6004597) B6004597
theorem B2222579 : Blo 1480560 2222579 := bstep (se 1 (by rfl) ⟨1666934, by rfl⟩ : syracuseStep 2222579 = 3333869) B3333869
theorem B4999697 : Blo 1480560 4999697 := bstep (se 2 (by rfl) ⟨1874886, by rfl⟩ : syracuseStep 4999697 = 3749773) B3749773
theorem B2222609 : Blo 1480560 2222609 := bstep (se 2 (by rfl) ⟨833478, by rfl⟩ : syracuseStep 2222609 = 1666957) B1666957
theorem B2222627 : Blo 1480560 2222627 := bstep (se 1 (by rfl) ⟨1666970, by rfl⟩ : syracuseStep 2222627 = 3333941) B3333941
theorem B2222657 : Blo 1480560 2222657 := bstep (se 2 (by rfl) ⟨833496, by rfl⟩ : syracuseStep 2222657 = 1666993) B1666993
theorem B2222675 : Blo 1480560 2222675 := bstep (se 1 (by rfl) ⟨1667006, by rfl⟩ : syracuseStep 2222675 = 3334013) B3334013
theorem B2222705 : Blo 1480560 2222705 := bstep (se 2 (by rfl) ⟨833514, by rfl⟩ : syracuseStep 2222705 = 1667029) B1667029
theorem B2222723 : Blo 1480560 2222723 := bstep (se 1 (by rfl) ⟨1667042, by rfl⟩ : syracuseStep 2222723 = 3334085) B3334085
theorem B2222753 : Blo 1480560 2222753 := bstep (se 2 (by rfl) ⟨833532, by rfl⟩ : syracuseStep 2222753 = 1667065) B1667065
theorem B1665715 : Blo 1480560 1665715 := bstep (se 1 (by rfl) ⟨1249286, by rfl⟩ : syracuseStep 1665715 = 2498573) B2498573
theorem B2222771 : Blo 1480560 2222771 := bstep (se 1 (by rfl) ⟨1667078, by rfl⟩ : syracuseStep 2222771 = 3334157) B3334157
theorem B2222801 : Blo 1480560 2222801 := bstep (se 2 (by rfl) ⟨833550, by rfl⟩ : syracuseStep 2222801 = 1667101) B1667101
theorem B2222819 : Blo 1480560 2222819 := bstep (se 1 (by rfl) ⟨1667114, by rfl⟩ : syracuseStep 2222819 = 3334229) B3334229
theorem B2812657 : Blo 1480560 2812657 := bstep (se 2 (by rfl) ⟨1054746, by rfl⟩ : syracuseStep 2812657 = 2109493) B2109493
theorem B2222849 : Blo 1480560 2222849 := bstep (se 2 (by rfl) ⟨833568, by rfl⟩ : syracuseStep 2222849 = 1667137) B1667137
theorem B2222867 : Blo 1480560 2222867 := bstep (se 1 (by rfl) ⟨1667150, by rfl⟩ : syracuseStep 2222867 = 3334301) B3334301
theorem B2222897 : Blo 1480560 2222897 := bstep (se 2 (by rfl) ⟨833586, by rfl⟩ : syracuseStep 2222897 = 1667173) B1667173
theorem B1665859 : Blo 1480560 1665859 := bstep (se 1 (by rfl) ⟨1249394, by rfl⟩ : syracuseStep 1665859 = 2498789) B2498789
theorem B2222915 : Blo 1480560 2222915 := bstep (se 1 (by rfl) ⟨1667186, by rfl⟩ : syracuseStep 2222915 = 3334373) B3334373
theorem B13519685 : Blo 1480560 13519685 := bstep (se 4 (by rfl) ⟨1267470, by rfl⟩ : syracuseStep 13519685 = 2534941) B2534941
theorem B2222945 : Blo 1480560 2222945 := bstep (se 2 (by rfl) ⟨833604, by rfl⟩ : syracuseStep 2222945 = 1667209) B1667209
theorem B5622641 : Blo 1480560 5622641 := bstep (se 2 (by rfl) ⟨2108490, by rfl⟩ : syracuseStep 5622641 = 4216981) B4216981
theorem B2222963 : Blo 1480560 2222963 := bstep (se 1 (by rfl) ⟨1667222, by rfl⟩ : syracuseStep 2222963 = 3334445) B3334445
theorem B8432525 : Blo 1480560 8432525 := bstep (se 3 (by rfl) ⟨1581098, by rfl⟩ : syracuseStep 8432525 = 3162197) B3162197
theorem B2222993 : Blo 1480560 2222993 := bstep (se 2 (by rfl) ⟨833622, by rfl⟩ : syracuseStep 2222993 = 1667245) B1667245
theorem B2223011 : Blo 1480560 2223011 := bstep (se 1 (by rfl) ⟨1667258, by rfl⟩ : syracuseStep 2223011 = 3334517) B3334517
theorem B2223041 : Blo 1480560 2223041 := bstep (se 2 (by rfl) ⟨833640, by rfl⟩ : syracuseStep 2223041 = 1667281) B1667281
theorem B2108371 : Blo 1480560 2108371 := bstep (se 1 (by rfl) ⟨1581278, by rfl⟩ : syracuseStep 2108371 = 3162557) B3162557
theorem B1666003 : Blo 1480560 1666003 := bstep (se 1 (by rfl) ⟨1249502, by rfl⟩ : syracuseStep 1666003 = 2499005) B2499005
theorem B2223059 : Blo 1480560 2223059 := bstep (se 1 (by rfl) ⟨1667294, by rfl⟩ : syracuseStep 2223059 = 3334589) B3334589
theorem B2223089 : Blo 1480560 2223089 := bstep (se 2 (by rfl) ⟨833658, by rfl⟩ : syracuseStep 2223089 = 1667317) B1667317
theorem B16239629 : Blo 1480560 16239629 := bstep (se 3 (by rfl) ⟨3044930, by rfl⟩ : syracuseStep 16239629 = 6089861) B6089861
theorem B5000237 : Blo 1480560 5000237 := bstep (se 3 (by rfl) ⟨937544, by rfl⟩ : syracuseStep 5000237 = 1875089) B1875089
theorem B15199301 : Blo 1480560 15199301 := bstep (se 4 (by rfl) ⟨1424934, by rfl⟩ : syracuseStep 15199301 = 2849869) B2849869
theorem B1666147 : Blo 1480560 1666147 := bstep (se 1 (by rfl) ⟨1249610, by rfl⟩ : syracuseStep 1666147 = 2499221) B2499221
theorem B3206243 : Blo 1480560 3206243 := bstep (se 1 (by rfl) ⟨2404682, by rfl⟩ : syracuseStep 3206243 = 4809365) B4809365
theorem B5000291 : Blo 1480560 5000291 := bstep (se 1 (by rfl) ⟨3750218, by rfl⟩ : syracuseStep 5000291 = 7500437) B7500437
theorem B2813059 : Blo 1480560 2813059 := bstep (se 1 (by rfl) ⟨2109794, by rfl⟩ : syracuseStep 2813059 = 4219589) B4219589
theorem B2813105 : Blo 1480560 2813105 := bstep (se 2 (by rfl) ⟨1054914, by rfl⟩ : syracuseStep 2813105 = 2109829) B2109829
theorem B3001553 : Blo 1480560 3001553 := bstep (se 2 (by rfl) ⟨1125582, by rfl⟩ : syracuseStep 3001553 = 2251165) B2251165
theorem B7498979 : Blo 1480560 7498979 := bstep (se 1 (by rfl) ⟨5624234, by rfl⟩ : syracuseStep 7498979 = 11248469) B11248469
theorem B1666291 : Blo 1480560 1666291 := bstep (se 1 (by rfl) ⟨1249718, by rfl⟩ : syracuseStep 1666291 = 2499437) B2499437
theorem B5000561 : Blo 1480560 5000561 := bstep (se 2 (by rfl) ⟨1875210, by rfl⟩ : syracuseStep 5000561 = 3750421) B3750421
theorem B1666435 : Blo 1480560 1666435 := bstep (se 1 (by rfl) ⟨1249826, by rfl⟩ : syracuseStep 1666435 = 2499653) B2499653
theorem B2813393 : Blo 1480560 2813393 := bstep (se 2 (by rfl) ⟨1055022, by rfl⟩ : syracuseStep 2813393 = 2110045) B2110045
theorem B2002387 : Blo 1480560 2002387 := bstep (se 1 (by rfl) ⟨1501790, by rfl⟩ : syracuseStep 2002387 = 3003581) B3003581
theorem B2108929 : Blo 1480560 2108929 := bstep (se 2 (by rfl) ⟨790848, by rfl⟩ : syracuseStep 2108929 = 1581697) B1581697
theorem B1666579 : Blo 1480560 1666579 := bstep (se 1 (by rfl) ⟨1249934, by rfl⟩ : syracuseStep 1666579 = 2499869) B2499869
theorem B2108963 : Blo 1480560 2108963 := bstep (se 1 (by rfl) ⟨1581722, by rfl⟩ : syracuseStep 2108963 = 3163445) B3163445
theorem B4746833 : Blo 1480560 4746833 := bstep (se 2 (by rfl) ⟨1780062, by rfl⟩ : syracuseStep 4746833 = 3560125) B3560125
theorem B2084467 : Blo 1480560 2084467 := bstep (se 1 (by rfl) ⟨1563350, by rfl⟩ : syracuseStep 2084467 = 3126701) B3126701
theorem B1666723 : Blo 1480560 1666723 := bstep (se 1 (by rfl) ⟨1250042, by rfl⟩ : syracuseStep 1666723 = 2500085) B2500085
theorem B1666867 : Blo 1480560 1666867 := bstep (se 1 (by rfl) ⟨1250150, by rfl⟩ : syracuseStep 1666867 = 2500301) B2500301
theorem B5001101 : Blo 1480560 5001101 := bstep (se 3 (by rfl) ⟨937706, by rfl⟩ : syracuseStep 5001101 = 1875413) B1875413
theorem B3747779 : Blo 1480560 3747779 := bstep (se 1 (by rfl) ⟨2810834, by rfl⟩ : syracuseStep 3747779 = 5621669) B5621669
theorem B1667011 : Blo 1480560 1667011 := bstep (se 1 (by rfl) ⟨1250258, by rfl⟩ : syracuseStep 1667011 = 2500517) B2500517
theorem B5001155 : Blo 1480560 5001155 := bstep (se 1 (by rfl) ⟨3750866, by rfl⟩ : syracuseStep 5001155 = 7501733) B7501733
theorem B7499789 : Blo 1480560 7499789 := bstep (se 3 (by rfl) ⟨1406210, by rfl⟩ : syracuseStep 7499789 = 2812421) B2812421
theorem B2109521 : Blo 1480560 2109521 := bstep (se 2 (by rfl) ⟨791070, by rfl⟩ : syracuseStep 2109521 = 1582141) B1582141
theorem B1667155 : Blo 1480560 1667155 := bstep (se 1 (by rfl) ⟨1250366, by rfl⟩ : syracuseStep 1667155 = 2500733) B2500733
theorem B2371699 : Blo 1480560 2371699 := bstep (se 1 (by rfl) ⟨1778774, by rfl⟩ : syracuseStep 2371699 = 3557549) B3557549
theorem B3747971 : Blo 1480560 3747971 := bstep (se 1 (by rfl) ⟨2810978, by rfl⟩ : syracuseStep 3747971 = 5621957) B5621957
theorem B12652685 : Blo 1480560 12652685 := bstep (se 3 (by rfl) ⟨2372378, by rfl⟩ : syracuseStep 12652685 = 4744757) B4744757
theorem B2109601 : Blo 1480560 2109601 := bstep (se 2 (by rfl) ⟨791100, by rfl⟩ : syracuseStep 2109601 = 1582201) B1582201
theorem B5001425 : Blo 1480560 5001425 := bstep (se 2 (by rfl) ⟨1875534, by rfl⟩ : syracuseStep 5001425 = 3751069) B3751069
theorem B1667299 : Blo 1480560 1667299 := bstep (se 1 (by rfl) ⟨1250474, by rfl⟩ : syracuseStep 1667299 = 2500949) B2500949
theorem B5624099 : Blo 1480560 5624099 := bstep (se 1 (by rfl) ⟨4218074, by rfl⟩ : syracuseStep 5624099 = 8436149) B8436149
theorem B5624113 : Blo 1480560 5624113 := bstep (se 2 (by rfl) ⟨2109042, by rfl⟩ : syracuseStep 5624113 = 4218085) B4218085
theorem B14242189 : Blo 1480560 14242189 := bstep (se 3 (by rfl) ⟨2670410, by rfl⟩ : syracuseStep 14242189 = 5340821) B5340821
theorem B4747693 : Blo 1480560 4747693 := bstep (se 3 (by rfl) ⟨890192, by rfl⟩ : syracuseStep 4747693 = 1780385) B1780385
theorem B2372161 : Blo 1480560 2372161 := bstep (se 2 (by rfl) ⟨889560, by rfl⟩ : syracuseStep 2372161 = 1779121) B1779121
theorem B16011917 : Blo 1480560 16011917 := bstep (se 3 (by rfl) ⟨3002234, by rfl⟩ : syracuseStep 16011917 = 6004469) B6004469
theorem B2372257 : Blo 1480560 2372257 := bstep (se 2 (by rfl) ⟨889596, by rfl⟩ : syracuseStep 2372257 = 1779193) B1779193
theorem B2372417 : Blo 1480560 2372417 := bstep (se 2 (by rfl) ⟨889656, by rfl⟩ : syracuseStep 2372417 = 1779313) B1779313
theorem B5698417 : Blo 1480560 5698417 := bstep (se 2 (by rfl) ⟨2136906, by rfl⟩ : syracuseStep 5698417 = 4273813) B4273813
theorem B2405267 : Blo 1480560 2405267 := bstep (se 1 (by rfl) ⟨1803950, by rfl⟩ : syracuseStep 2405267 = 3607901) B3607901
theorem B6329315 : Blo 1480560 6329315 := bstep (se 1 (by rfl) ⟨4746986, by rfl⟩ : syracuseStep 6329315 = 9493973) B9493973
theorem B3748913 : Blo 1480560 3748913 := bstep (se 2 (by rfl) ⟨1405842, by rfl⟩ : syracuseStep 3748913 = 2811685) B2811685
theorem B7599203 : Blo 1480560 7599203 := bstep (se 1 (by rfl) ⟨5699402, by rfl⟩ : syracuseStep 7599203 = 11398805) B11398805
theorem B3748963 : Blo 1480560 3748963 := bstep (se 1 (by rfl) ⟨2811722, by rfl⟩ : syracuseStep 3748963 = 5623445) B5623445
theorem B2438273 : Blo 1480560 2438273 := bstep (se 2 (by rfl) ⟨914352, by rfl⟩ : syracuseStep 2438273 = 1828705) B1828705
theorem B66720995 : Blo 1480560 66720995 := bstep (se 1 (by rfl) ⟨50040746, by rfl⟩ : syracuseStep 66720995 = 100081493) B100081493
theorem B3331313 : Blo 1480560 3331313 := bstep (se 2 (by rfl) ⟨1249242, by rfl⟩ : syracuseStep 3331313 = 2498485) B2498485
theorem B3749105 : Blo 1480560 3749105 := bstep (se 2 (by rfl) ⟨1405914, by rfl⟩ : syracuseStep 3749105 = 2811829) B2811829
theorem B3331331 : Blo 1480560 3331331 := bstep (se 1 (by rfl) ⟨2498498, by rfl⟩ : syracuseStep 3331331 = 4996997) B4996997
theorem B9491717 : Blo 1480560 9491717 := bstep (se 4 (by rfl) ⟨889848, by rfl⟩ : syracuseStep 9491717 = 1779697) B1779697
theorem B4502915 : Blo 1480560 4502915 := bstep (se 1 (by rfl) ⟨3377186, by rfl⟩ : syracuseStep 4502915 = 6754373) B6754373
theorem B2602451 : Blo 1480560 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B3331601 : Blo 1480560 3331601 := bstep (se 2 (by rfl) ⟨1249350, by rfl⟩ : syracuseStep 3331601 = 2498701) B2498701
theorem B3331619 : Blo 1480560 3331619 := bstep (se 1 (by rfl) ⟨2498714, by rfl⟩ : syracuseStep 3331619 = 4997429) B4997429
theorem B2438755 : Blo 1480560 2438755 := bstep (se 1 (by rfl) ⟨1829066, by rfl⟩ : syracuseStep 2438755 = 3658133) B3658133
theorem B5625571 : Blo 1480560 5625571 := bstep (se 1 (by rfl) ⟨4219178, by rfl⟩ : syracuseStep 5625571 = 8438357) B8438357
theorem B8435441 : Blo 1480560 8435441 := bstep (se 2 (by rfl) ⟨3163290, by rfl⟩ : syracuseStep 8435441 = 6326581) B6326581
theorem B3331889 : Blo 1480560 3331889 := bstep (se 2 (by rfl) ⟨1249458, by rfl⟩ : syracuseStep 3331889 = 2498917) B2498917
theorem B3331907 : Blo 1480560 3331907 := bstep (se 1 (by rfl) ⟨2498930, by rfl⟩ : syracuseStep 3331907 = 4997861) B4997861
theorem B1480563 : Blo 1480560 1480563 := bstep (se 1 (by rfl) ⟨1110422, by rfl⟩ : syracuseStep 1480563 = 2220845) B2220845
theorem B1480579 : Blo 1480560 1480579 := bstep (se 1 (by rfl) ⟨1110434, by rfl⟩ : syracuseStep 1480579 = 2220869) B2220869
theorem B1480595 : Blo 1480560 1480595 := bstep (se 1 (by rfl) ⟨1110446, by rfl⟩ : syracuseStep 1480595 = 2220893) B2220893
theorem B1480611 : Blo 1480560 1480611 := bstep (se 1 (by rfl) ⟨1110458, by rfl⟩ : syracuseStep 1480611 = 2220917) B2220917
theorem B4003757 : Blo 1480560 4003757 := bstep (se 3 (by rfl) ⟨750704, by rfl⟩ : syracuseStep 4003757 = 1501409) B1501409
theorem B2668465 : Blo 1480560 2668465 := bstep (se 2 (by rfl) ⟨1000674, by rfl⟩ : syracuseStep 2668465 = 2001349) B2001349
theorem B1480627 : Blo 1480560 1480627 := bstep (se 1 (by rfl) ⟨1110470, by rfl⟩ : syracuseStep 1480627 = 2220941) B2220941
theorem B1480643 : Blo 1480560 1480643 := bstep (se 1 (by rfl) ⟨1110482, by rfl⟩ : syracuseStep 1480643 = 2220965) B2220965
theorem B1480659 : Blo 1480560 1480659 := bstep (se 1 (by rfl) ⟨1110494, by rfl⟩ : syracuseStep 1480659 = 2220989) B2220989
theorem B1480675 : Blo 1480560 1480675 := bstep (se 1 (by rfl) ⟨1110506, by rfl⟩ : syracuseStep 1480675 = 2221013) B2221013
theorem B11245553 : Blo 1480560 11245553 := bstep (se 2 (by rfl) ⟨4217082, by rfl⟩ : syracuseStep 11245553 = 8434165) B8434165
theorem B1480691 : Blo 1480560 1480691 := bstep (se 1 (by rfl) ⟨1110518, by rfl⟩ : syracuseStep 1480691 = 2221037) B2221037
theorem B1480707 : Blo 1480560 1480707 := bstep (se 1 (by rfl) ⟨1110530, by rfl⟩ : syracuseStep 1480707 = 2221061) B2221061
theorem B1480723 : Blo 1480560 1480723 := bstep (se 1 (by rfl) ⟨1110542, by rfl⟩ : syracuseStep 1480723 = 2221085) B2221085
theorem B1873955 : Blo 1480560 1873955 := bstep (se 1 (by rfl) ⟨1405466, by rfl⟩ : syracuseStep 1873955 = 2810933) B2810933
theorem B1480739 : Blo 1480560 1480739 := bstep (se 1 (by rfl) ⟨1110554, by rfl⟩ : syracuseStep 1480739 = 2221109) B2221109
theorem B3004465 : Blo 1480560 3004465 := bstep (se 2 (by rfl) ⟨1126674, by rfl⟩ : syracuseStep 3004465 = 2253349) B2253349
theorem B1480755 : Blo 1480560 1480755 := bstep (se 1 (by rfl) ⟨1110566, by rfl⟩ : syracuseStep 1480755 = 2221133) B2221133
theorem B1480771 : Blo 1480560 1480771 := bstep (se 1 (by rfl) ⟨1110578, by rfl⟩ : syracuseStep 1480771 = 2221157) B2221157
theorem B3332177 : Blo 1480560 3332177 := bstep (se 2 (by rfl) ⟨1249566, by rfl⟩ : syracuseStep 3332177 = 2499133) B2499133
theorem B1480787 : Blo 1480560 1480787 := bstep (se 1 (by rfl) ⟨1110590, by rfl⟩ : syracuseStep 1480787 = 2221181) B2221181
theorem B1480803 : Blo 1480560 1480803 := bstep (se 1 (by rfl) ⟨1110602, by rfl⟩ : syracuseStep 1480803 = 2221205) B2221205
theorem B3332195 : Blo 1480560 3332195 := bstep (se 1 (by rfl) ⟨2499146, by rfl⟩ : syracuseStep 3332195 = 4998293) B4998293
theorem B1480819 : Blo 1480560 1480819 := bstep (se 1 (by rfl) ⟨1110614, by rfl⟩ : syracuseStep 1480819 = 2221229) B2221229
theorem B1480835 : Blo 1480560 1480835 := bstep (se 1 (by rfl) ⟨1110626, by rfl⟩ : syracuseStep 1480835 = 2221253) B2221253
theorem B32921741 : Blo 1480560 32921741 := bstep (se 3 (by rfl) ⟨6172826, by rfl⟩ : syracuseStep 32921741 = 12345653) B12345653
theorem B1480851 : Blo 1480560 1480851 := bstep (se 1 (by rfl) ⟨1110638, by rfl⟩ : syracuseStep 1480851 = 2221277) B2221277
theorem B1480867 : Blo 1480560 1480867 := bstep (se 1 (by rfl) ⟨1110650, by rfl⟩ : syracuseStep 1480867 = 2221301) B2221301
theorem B6330545 : Blo 1480560 6330545 := bstep (se 2 (by rfl) ⟨2373954, by rfl⟩ : syracuseStep 6330545 = 4747909) B4747909
theorem B1480883 : Blo 1480560 1480883 := bstep (se 1 (by rfl) ⟨1110662, by rfl⟩ : syracuseStep 1480883 = 2221325) B2221325
theorem B1480899 : Blo 1480560 1480899 := bstep (se 1 (by rfl) ⟨1110674, by rfl⟩ : syracuseStep 1480899 = 2221349) B2221349
theorem B3750097 : Blo 1480560 3750097 := bstep (se 2 (by rfl) ⟨1406286, by rfl⟩ : syracuseStep 3750097 = 2812573) B2812573
theorem B1480915 : Blo 1480560 1480915 := bstep (se 1 (by rfl) ⟨1110686, by rfl⟩ : syracuseStep 1480915 = 2221373) B2221373
theorem B1480931 : Blo 1480560 1480931 := bstep (se 1 (by rfl) ⟨1110698, by rfl⟩ : syracuseStep 1480931 = 2221397) B2221397
theorem B1480947 : Blo 1480560 1480947 := bstep (se 1 (by rfl) ⟨1110710, by rfl⟩ : syracuseStep 1480947 = 2221421) B2221421
theorem B1480963 : Blo 1480560 1480963 := bstep (se 1 (by rfl) ⟨1110722, by rfl⟩ : syracuseStep 1480963 = 2221445) B2221445
theorem B1480979 : Blo 1480560 1480979 := bstep (se 1 (by rfl) ⟨1110734, by rfl⟩ : syracuseStep 1480979 = 2221469) B2221469
theorem B1480995 : Blo 1480560 1480995 := bstep (se 1 (by rfl) ⟨1110746, by rfl⟩ : syracuseStep 1480995 = 2221493) B2221493
theorem B1481011 : Blo 1480560 1481011 := bstep (se 1 (by rfl) ⟨1110758, by rfl⟩ : syracuseStep 1481011 = 2221517) B2221517
theorem B1481027 : Blo 1480560 1481027 := bstep (se 1 (by rfl) ⟨1110770, by rfl⟩ : syracuseStep 1481027 = 2221541) B2221541
theorem B1481043 : Blo 1480560 1481043 := bstep (se 1 (by rfl) ⟨1110782, by rfl⟩ : syracuseStep 1481043 = 2221565) B2221565
theorem B1481059 : Blo 1480560 1481059 := bstep (se 1 (by rfl) ⟨1110794, by rfl⟩ : syracuseStep 1481059 = 2221589) B2221589
theorem B4217197 : Blo 1480560 4217197 := bstep (se 3 (by rfl) ⟨790724, by rfl⟩ : syracuseStep 4217197 = 1581449) B1581449
theorem B3332465 : Blo 1480560 3332465 := bstep (se 2 (by rfl) ⟨1249674, by rfl⟩ : syracuseStep 3332465 = 2499349) B2499349
theorem B1481075 : Blo 1480560 1481075 := bstep (se 1 (by rfl) ⟨1110806, by rfl⟩ : syracuseStep 1481075 = 2221613) B2221613
theorem B1481091 : Blo 1480560 1481091 := bstep (se 1 (by rfl) ⟨1110818, by rfl⟩ : syracuseStep 1481091 = 2221637) B2221637
theorem B3332483 : Blo 1480560 3332483 := bstep (se 1 (by rfl) ⟨2499362, by rfl⟩ : syracuseStep 3332483 = 4998725) B4998725
theorem B1481107 : Blo 1480560 1481107 := bstep (se 1 (by rfl) ⟨1110830, by rfl⟩ : syracuseStep 1481107 = 2221661) B2221661
theorem B1481123 : Blo 1480560 1481123 := bstep (se 1 (by rfl) ⟨1110842, by rfl⟩ : syracuseStep 1481123 = 2221685) B2221685
theorem B5700017 : Blo 1480560 5700017 := bstep (se 2 (by rfl) ⟨2137506, by rfl⟩ : syracuseStep 5700017 = 4275013) B4275013
theorem B1481139 : Blo 1480560 1481139 := bstep (se 1 (by rfl) ⟨1110854, by rfl⟩ : syracuseStep 1481139 = 2221709) B2221709
theorem B1481155 : Blo 1480560 1481155 := bstep (se 1 (by rfl) ⟨1110866, by rfl⟩ : syracuseStep 1481155 = 2221733) B2221733
theorem B1481171 : Blo 1480560 1481171 := bstep (se 1 (by rfl) ⟨1110878, by rfl⟩ : syracuseStep 1481171 = 2221757) B2221757
theorem B1481187 : Blo 1480560 1481187 := bstep (se 1 (by rfl) ⟨1110890, by rfl⟩ : syracuseStep 1481187 = 2221781) B2221781
theorem B12655075 : Blo 1480560 12655075 := bstep (se 1 (by rfl) ⟨9491306, by rfl⟩ : syracuseStep 12655075 = 18982613) B18982613
theorem B3750371 : Blo 1480560 3750371 := bstep (se 1 (by rfl) ⟨2812778, by rfl⟩ : syracuseStep 3750371 = 5625557) B5625557
theorem B1481203 : Blo 1480560 1481203 := bstep (se 1 (by rfl) ⟨1110902, by rfl⟩ : syracuseStep 1481203 = 2221805) B2221805
theorem B1481219 : Blo 1480560 1481219 := bstep (se 1 (by rfl) ⟨1110914, by rfl⟩ : syracuseStep 1481219 = 2221829) B2221829
theorem B1481235 : Blo 1480560 1481235 := bstep (se 1 (by rfl) ⟨1110926, by rfl⟩ : syracuseStep 1481235 = 2221853) B2221853
theorem B1481251 : Blo 1480560 1481251 := bstep (se 1 (by rfl) ⟨1110938, by rfl⟩ : syracuseStep 1481251 = 2221877) B2221877
theorem B1481267 : Blo 1480560 1481267 := bstep (se 1 (by rfl) ⟨1110950, by rfl⟩ : syracuseStep 1481267 = 2221901) B2221901
theorem B1481283 : Blo 1480560 1481283 := bstep (se 1 (by rfl) ⟨1110962, by rfl⟩ : syracuseStep 1481283 = 2221925) B2221925
theorem B1481299 : Blo 1480560 1481299 := bstep (se 1 (by rfl) ⟨1110974, by rfl⟩ : syracuseStep 1481299 = 2221949) B2221949
theorem B1481315 : Blo 1480560 1481315 := bstep (se 1 (by rfl) ⟨1110986, by rfl⟩ : syracuseStep 1481315 = 2221973) B2221973
theorem B1481331 : Blo 1480560 1481331 := bstep (se 1 (by rfl) ⟨1110998, by rfl⟩ : syracuseStep 1481331 = 2221997) B2221997
theorem B1481347 : Blo 1480560 1481347 := bstep (se 1 (by rfl) ⟨1111010, by rfl⟩ : syracuseStep 1481347 = 2222021) B2222021
theorem B5413517 : Blo 1480560 5413517 := bstep (se 3 (by rfl) ⟨1015034, by rfl⟩ : syracuseStep 5413517 = 2030069) B2030069
theorem B3332753 : Blo 1480560 3332753 := bstep (se 2 (by rfl) ⟨1249782, by rfl⟩ : syracuseStep 3332753 = 2499565) B2499565
theorem B1481363 : Blo 1480560 1481363 := bstep (se 1 (by rfl) ⟨1111022, by rfl⟩ : syracuseStep 1481363 = 2222045) B2222045
theorem B3332771 : Blo 1480560 3332771 := bstep (se 1 (by rfl) ⟨2499578, by rfl⟩ : syracuseStep 3332771 = 4999157) B4999157
theorem B1481379 : Blo 1480560 1481379 := bstep (se 1 (by rfl) ⟨1111034, by rfl⟩ : syracuseStep 1481379 = 2222069) B2222069
theorem B3750563 : Blo 1480560 3750563 := bstep (se 1 (by rfl) ⟨2812922, by rfl⟩ : syracuseStep 3750563 = 5625845) B5625845
theorem B1481395 : Blo 1480560 1481395 := bstep (se 1 (by rfl) ⟨1111046, by rfl⟩ : syracuseStep 1481395 = 2222093) B2222093
theorem B1481411 : Blo 1480560 1481411 := bstep (se 1 (by rfl) ⟨1111058, by rfl⟩ : syracuseStep 1481411 = 2222117) B2222117
theorem B1481427 : Blo 1480560 1481427 := bstep (se 1 (by rfl) ⟨1111070, by rfl⟩ : syracuseStep 1481427 = 2222141) B2222141
theorem B1874659 : Blo 1480560 1874659 := bstep (se 1 (by rfl) ⟨1405994, by rfl⟩ : syracuseStep 1874659 = 2811989) B2811989
theorem B1481443 : Blo 1480560 1481443 := bstep (se 1 (by rfl) ⟨1111082, by rfl⟩ : syracuseStep 1481443 = 2222165) B2222165
theorem B4004579 : Blo 1480560 4004579 := bstep (se 1 (by rfl) ⟨3003434, by rfl⟩ : syracuseStep 4004579 = 6006869) B6006869
theorem B1481459 : Blo 1480560 1481459 := bstep (se 1 (by rfl) ⟨1111094, by rfl⟩ : syracuseStep 1481459 = 2222189) B2222189
theorem B1481475 : Blo 1480560 1481475 := bstep (se 1 (by rfl) ⟨1111106, by rfl⟩ : syracuseStep 1481475 = 2222213) B2222213
theorem B1481491 : Blo 1480560 1481491 := bstep (se 1 (by rfl) ⟨1111118, by rfl⟩ : syracuseStep 1481491 = 2222237) B2222237
theorem B1481507 : Blo 1480560 1481507 := bstep (se 1 (by rfl) ⟨1111130, by rfl⟩ : syracuseStep 1481507 = 2222261) B2222261
theorem B1481523 : Blo 1480560 1481523 := bstep (se 1 (by rfl) ⟨1111142, by rfl⟩ : syracuseStep 1481523 = 2222285) B2222285
theorem B1874755 : Blo 1480560 1874755 := bstep (se 1 (by rfl) ⟨1406066, by rfl⟩ : syracuseStep 1874755 = 2812133) B2812133
theorem B1481539 : Blo 1480560 1481539 := bstep (se 1 (by rfl) ⟨1111154, by rfl⟩ : syracuseStep 1481539 = 2222309) B2222309
theorem B9624389 : Blo 1480560 9624389 := bstep (se 4 (by rfl) ⟨902286, by rfl⟩ : syracuseStep 9624389 = 1804573) B1804573
theorem B1481555 : Blo 1480560 1481555 := bstep (se 1 (by rfl) ⟨1111166, by rfl⟩ : syracuseStep 1481555 = 2222333) B2222333
theorem B1481571 : Blo 1480560 1481571 := bstep (se 1 (by rfl) ⟨1111178, by rfl⟩ : syracuseStep 1481571 = 2222357) B2222357
theorem B7502705 : Blo 1480560 7502705 := bstep (se 2 (by rfl) ⟨2813514, by rfl⟩ : syracuseStep 7502705 = 5627029) B5627029
theorem B1481587 : Blo 1480560 1481587 := bstep (se 1 (by rfl) ⟨1111190, by rfl⟩ : syracuseStep 1481587 = 2222381) B2222381
theorem B1481603 : Blo 1480560 1481603 := bstep (se 1 (by rfl) ⟨1111202, by rfl⟩ : syracuseStep 1481603 = 2222405) B2222405
theorem B1481619 : Blo 1480560 1481619 := bstep (se 1 (by rfl) ⟨1111214, by rfl⟩ : syracuseStep 1481619 = 2222429) B2222429
theorem B1481635 : Blo 1480560 1481635 := bstep (se 1 (by rfl) ⟨1111226, by rfl⟩ : syracuseStep 1481635 = 2222453) B2222453
theorem B3333041 : Blo 1480560 3333041 := bstep (se 2 (by rfl) ⟨1249890, by rfl⟩ : syracuseStep 3333041 = 2499781) B2499781
theorem B1481651 : Blo 1480560 1481651 := bstep (se 1 (by rfl) ⟨1111238, by rfl⟩ : syracuseStep 1481651 = 2222477) B2222477
theorem B3333059 : Blo 1480560 3333059 := bstep (se 1 (by rfl) ⟨2499794, by rfl⟩ : syracuseStep 3333059 = 4999589) B4999589
theorem B1481667 : Blo 1480560 1481667 := bstep (se 1 (by rfl) ⟨1111250, by rfl⟩ : syracuseStep 1481667 = 2222501) B2222501
theorem B1481683 : Blo 1480560 1481683 := bstep (se 1 (by rfl) ⟨1111262, by rfl⟩ : syracuseStep 1481683 = 2222525) B2222525
theorem B5340131 : Blo 1480560 5340131 := bstep (se 1 (by rfl) ⟨4005098, by rfl⟩ : syracuseStep 5340131 = 8010197) B8010197
theorem B1481699 : Blo 1480560 1481699 := bstep (se 1 (by rfl) ⟨1111274, by rfl⟩ : syracuseStep 1481699 = 2222549) B2222549
theorem B1481715 : Blo 1480560 1481715 := bstep (se 1 (by rfl) ⟨1111286, by rfl⟩ : syracuseStep 1481715 = 2222573) B2222573
theorem B1481731 : Blo 1480560 1481731 := bstep (se 1 (by rfl) ⟨1111298, by rfl⟩ : syracuseStep 1481731 = 2222597) B2222597
theorem B1481747 : Blo 1480560 1481747 := bstep (se 1 (by rfl) ⟨1111310, by rfl⟩ : syracuseStep 1481747 = 2222621) B2222621
theorem B1481763 : Blo 1480560 1481763 := bstep (se 1 (by rfl) ⟨1111322, by rfl⟩ : syracuseStep 1481763 = 2222645) B2222645
theorem B1481779 : Blo 1480560 1481779 := bstep (se 1 (by rfl) ⟨1111334, by rfl⟩ : syracuseStep 1481779 = 2222669) B2222669
theorem B1481795 : Blo 1480560 1481795 := bstep (se 1 (by rfl) ⟨1111346, by rfl⟩ : syracuseStep 1481795 = 2222693) B2222693
theorem B1481811 : Blo 1480560 1481811 := bstep (se 1 (by rfl) ⟨1111358, by rfl⟩ : syracuseStep 1481811 = 2222717) B2222717
theorem B1481827 : Blo 1480560 1481827 := bstep (se 1 (by rfl) ⟨1111370, by rfl⟩ : syracuseStep 1481827 = 2222741) B2222741
theorem B13360241 : Blo 1480560 13360241 := bstep (se 2 (by rfl) ⟨5010090, by rfl⟩ : syracuseStep 13360241 = 10020181) B10020181
theorem B1481843 : Blo 1480560 1481843 := bstep (se 1 (by rfl) ⟨1111382, by rfl⟩ : syracuseStep 1481843 = 2222765) B2222765
theorem B1481859 : Blo 1480560 1481859 := bstep (se 1 (by rfl) ⟨1111394, by rfl⟩ : syracuseStep 1481859 = 2222789) B2222789
theorem B1481875 : Blo 1480560 1481875 := bstep (se 1 (by rfl) ⟨1111406, by rfl⟩ : syracuseStep 1481875 = 2222813) B2222813
theorem B8436899 : Blo 1480560 8436899 := bstep (se 1 (by rfl) ⟨6327674, by rfl⟩ : syracuseStep 8436899 = 12655349) B12655349
theorem B1481891 : Blo 1480560 1481891 := bstep (se 1 (by rfl) ⟨1111418, by rfl⟩ : syracuseStep 1481891 = 2222837) B2222837
theorem B1481907 : Blo 1480560 1481907 := bstep (se 1 (by rfl) ⟨1111430, by rfl⟩ : syracuseStep 1481907 = 2222861) B2222861
theorem B1481923 : Blo 1480560 1481923 := bstep (se 1 (by rfl) ⟨1111442, by rfl⟩ : syracuseStep 1481923 = 2222885) B2222885
theorem B3333329 : Blo 1480560 3333329 := bstep (se 2 (by rfl) ⟨1249998, by rfl⟩ : syracuseStep 3333329 = 2499997) B2499997
theorem B2669777 : Blo 1480560 2669777 := bstep (se 2 (by rfl) ⟨1001166, by rfl⟩ : syracuseStep 2669777 = 2002333) B2002333
theorem B1481939 : Blo 1480560 1481939 := bstep (se 1 (by rfl) ⟨1111454, by rfl⟩ : syracuseStep 1481939 = 2222909) B2222909
theorem B3333347 : Blo 1480560 3333347 := bstep (se 1 (by rfl) ⟨2500010, by rfl⟩ : syracuseStep 3333347 = 5000021) B5000021
theorem B1481955 : Blo 1480560 1481955 := bstep (se 1 (by rfl) ⟨1111466, by rfl⟩ : syracuseStep 1481955 = 2222933) B2222933
theorem B1481971 : Blo 1480560 1481971 := bstep (se 1 (by rfl) ⟨1111478, by rfl⟩ : syracuseStep 1481971 = 2222957) B2222957
theorem B1481987 : Blo 1480560 1481987 := bstep (se 1 (by rfl) ⟨1111490, by rfl⟩ : syracuseStep 1481987 = 2222981) B2222981
theorem B1482003 : Blo 1480560 1482003 := bstep (se 1 (by rfl) ⟨1111502, by rfl⟩ : syracuseStep 1482003 = 2223005) B2223005
theorem B1482019 : Blo 1480560 1482019 := bstep (se 1 (by rfl) ⟨1111514, by rfl⟩ : syracuseStep 1482019 = 2223029) B2223029
theorem B1875251 : Blo 1480560 1875251 := bstep (se 1 (by rfl) ⟨1406438, by rfl⟩ : syracuseStep 1875251 = 2812877) B2812877
theorem B1482035 : Blo 1480560 1482035 := bstep (se 1 (by rfl) ⟨1111526, by rfl⟩ : syracuseStep 1482035 = 2223053) B2223053
theorem B1482051 : Blo 1480560 1482051 := bstep (se 1 (by rfl) ⟨1111538, by rfl⟩ : syracuseStep 1482051 = 2223077) B2223077
theorem B4504909 : Blo 1480560 4504909 := bstep (se 3 (by rfl) ⟨844670, by rfl⟩ : syracuseStep 4504909 = 1689341) B1689341
theorem B4218257 : Blo 1480560 4218257 := bstep (se 2 (by rfl) ⟨1581846, by rfl⟩ : syracuseStep 4218257 = 3163693) B3163693
theorem B3800483 : Blo 1480560 3800483 := bstep (se 1 (by rfl) ⟨2850362, by rfl⟩ : syracuseStep 3800483 = 5700725) B5700725
theorem B4505005 : Blo 1480560 4505005 := bstep (se 3 (by rfl) ⟨844688, by rfl⟩ : syracuseStep 4505005 = 1689377) B1689377
theorem B3333617 : Blo 1480560 3333617 := bstep (se 2 (by rfl) ⟨1250106, by rfl⟩ : syracuseStep 3333617 = 2500213) B2500213
theorem B3333635 : Blo 1480560 3333635 := bstep (se 1 (by rfl) ⟨2500226, by rfl⟩ : syracuseStep 3333635 = 5000453) B5000453
theorem B4808323 : Blo 1480560 4808323 := bstep (se 1 (by rfl) ⟨3606242, by rfl⟩ : syracuseStep 4808323 = 7212485) B7212485
theorem B9010885 : Blo 1480560 9010885 := bstep (se 4 (by rfl) ⟨844770, by rfl⟩ : syracuseStep 9010885 = 1689541) B1689541
theorem B3333905 : Blo 1480560 3333905 := bstep (se 2 (by rfl) ⟨1250214, by rfl⟩ : syracuseStep 3333905 = 2500429) B2500429
theorem B3333923 : Blo 1480560 3333923 := bstep (se 1 (by rfl) ⟨2500442, by rfl⟩ : syracuseStep 3333923 = 5000885) B5000885
theorem B36052877 : Blo 1480560 36052877 := bstep (se 3 (by rfl) ⟨6759914, by rfl⟩ : syracuseStep 36052877 = 13519829) B13519829
theorem B2498465 : Blo 1480560 2498465 := bstep (se 2 (by rfl) ⟨936924, by rfl⟩ : syracuseStep 2498465 = 1873849) B1873849
theorem B9494435 : Blo 1480560 9494435 := bstep (se 1 (by rfl) ⟨7120826, by rfl⟩ : syracuseStep 9494435 = 14241653) B14241653
theorem B4997105 : Blo 1480560 4997105 := bstep (se 2 (by rfl) ⟨1873914, by rfl⟩ : syracuseStep 4997105 = 3747829) B3747829
theorem B4005953 : Blo 1480560 4005953 := bstep (se 2 (by rfl) ⟨1502232, by rfl⟩ : syracuseStep 4005953 = 3004465) B3004465
theorem B2498647 : Blo 1480560 2498647 := bstep (se 1 (by rfl) ⟨1873985, by rfl⟩ : syracuseStep 2498647 = 3747971) B3747971
theorem B4997213 : Blo 1480560 4997213 := bstep (se 3 (by rfl) ⟨936977, by rfl⟩ : syracuseStep 4997213 = 1873955) B1873955
theorem B3334283 : Blo 1480560 3334283 := bstep (se 1 (by rfl) ⟨2500712, by rfl⟩ : syracuseStep 3334283 = 5001425) B5001425
theorem B3334337 : Blo 1480560 3334337 := bstep (se 2 (by rfl) ⟨1250376, by rfl⟩ : syracuseStep 3334337 = 2500753) B2500753
theorem B35627309 : Blo 1480560 35627309 := bstep (se 3 (by rfl) ⟨6680120, by rfl⟩ : syracuseStep 35627309 = 13360241) B13360241
theorem B3334553 : Blo 1480560 3334553 := bstep (se 2 (by rfl) ⟨1250457, by rfl⟩ : syracuseStep 3334553 = 2500915) B2500915
theorem B10674611 : Blo 1480560 10674611 := bstep (se 1 (by rfl) ⟨8005958, by rfl⟩ : syracuseStep 10674611 = 16011917) B16011917
theorem B18989585 : Blo 1480560 18989585 := bstep (se 2 (by rfl) ⟨7121094, by rfl⟩ : syracuseStep 18989585 = 14242189) B14242189
theorem B1581611 : Blo 1480560 1581611 := bstep (se 1 (by rfl) ⟨1186208, by rfl⟩ : syracuseStep 1581611 = 2372417) B2372417
theorem B12649061 : Blo 1480560 12649061 := bstep (se 4 (by rfl) ⟨1185849, by rfl⟩ : syracuseStep 12649061 = 2371699) B2371699
theorem B4219543 : Blo 1480560 4219543 := bstep (se 1 (by rfl) ⟨3164657, by rfl⟩ : syracuseStep 4219543 = 6329315) B6329315
theorem B2499275 : Blo 1480560 2499275 := bstep (se 1 (by rfl) ⟨1874456, by rfl⟩ : syracuseStep 2499275 = 3748913) B3748913
theorem B3162881 : Blo 1480560 3162881 := bstep (se 2 (by rfl) ⟨1186080, by rfl⟩ : syracuseStep 3162881 = 2372161) B2372161
theorem B2220875 : Blo 1480560 2220875 := bstep (se 1 (by rfl) ⟨1665656, by rfl⟩ : syracuseStep 2220875 = 3331313) B3331313
theorem B2499403 : Blo 1480560 2499403 := bstep (se 1 (by rfl) ⟨1874552, by rfl⟩ : syracuseStep 2499403 = 3749105) B3749105
theorem B2220887 : Blo 1480560 2220887 := bstep (se 1 (by rfl) ⟨1665665, by rfl⟩ : syracuseStep 2220887 = 3331331) B3331331
theorem B2220953 : Blo 1480560 2220953 := bstep (se 2 (by rfl) ⟨832857, by rfl⟩ : syracuseStep 2220953 = 1665715) B1665715
theorem B2499545 : Blo 1480560 2499545 := bstep (se 2 (by rfl) ⟨937329, by rfl⟩ : syracuseStep 2499545 = 1874659) B1874659
theorem B2221067 : Blo 1480560 2221067 := bstep (se 1 (by rfl) ⟨1665800, by rfl⟩ : syracuseStep 2221067 = 3331601) B3331601
theorem B2221079 : Blo 1480560 2221079 := bstep (se 1 (by rfl) ⟨1665809, by rfl⟩ : syracuseStep 2221079 = 3331619) B3331619
theorem B2221145 : Blo 1480560 2221145 := bstep (se 2 (by rfl) ⟨832929, by rfl⟩ : syracuseStep 2221145 = 1665859) B1665859
theorem B2499673 : Blo 1480560 2499673 := bstep (se 2 (by rfl) ⟨937377, by rfl⟩ : syracuseStep 2499673 = 1874755) B1874755
theorem B2221259 : Blo 1480560 2221259 := bstep (se 1 (by rfl) ⟨1665944, by rfl⟩ : syracuseStep 2221259 = 3331889) B3331889
theorem B4998347 : Blo 1480560 4998347 := bstep (se 1 (by rfl) ⟨3748760, by rfl⟩ : syracuseStep 4998347 = 7497521) B7497521
theorem B2221271 : Blo 1480560 2221271 := bstep (se 1 (by rfl) ⟨1665953, by rfl⟩ : syracuseStep 2221271 = 3331907) B3331907
theorem B2811161 : Blo 1480560 2811161 := bstep (se 2 (by rfl) ⟨1054185, by rfl⟩ : syracuseStep 2811161 = 2108371) B2108371
theorem B2221337 : Blo 1480560 2221337 := bstep (se 2 (by rfl) ⟨833001, by rfl⟩ : syracuseStep 2221337 = 1666003) B1666003
theorem B7497035 : Blo 1480560 7497035 := bstep (se 1 (by rfl) ⟨5622776, by rfl⟩ : syracuseStep 7497035 = 11245553) B11245553
theorem B2221451 : Blo 1480560 2221451 := bstep (se 1 (by rfl) ⟨1666088, by rfl⟩ : syracuseStep 2221451 = 3332177) B3332177
theorem B2221463 : Blo 1480560 2221463 := bstep (se 1 (by rfl) ⟨1666097, by rfl⟩ : syracuseStep 2221463 = 3332195) B3332195
theorem B21947827 : Blo 1480560 21947827 := bstep (se 1 (by rfl) ⟨16460870, by rfl⟩ : syracuseStep 21947827 = 32921741) B32921741
theorem B4220363 : Blo 1480560 4220363 := bstep (se 1 (by rfl) ⟨3165272, by rfl⟩ : syracuseStep 4220363 = 6330545) B6330545
theorem B2221529 : Blo 1480560 2221529 := bstep (se 2 (by rfl) ⟨833073, by rfl⟩ : syracuseStep 2221529 = 1666147) B1666147
theorem B4998617 : Blo 1480560 4998617 := bstep (se 2 (by rfl) ⟨1874481, by rfl⟩ : syracuseStep 4998617 = 3748963) B3748963
theorem B1689067 : Blo 1480560 1689067 := bstep (se 1 (by rfl) ⟨1266800, by rfl⟩ : syracuseStep 1689067 = 2533601) B2533601
theorem B2221643 : Blo 1480560 2221643 := bstep (se 1 (by rfl) ⟨1666232, by rfl⟩ : syracuseStep 2221643 = 3332465) B3332465
theorem B2221655 : Blo 1480560 2221655 := bstep (se 1 (by rfl) ⟨1666241, by rfl⟩ : syracuseStep 2221655 = 3332483) B3332483
theorem B3163735 : Blo 1480560 3163735 := bstep (se 1 (by rfl) ⟨2372801, by rfl⟩ : syracuseStep 3163735 = 4745603) B4745603
theorem B3606167 : Blo 1480560 3606167 := bstep (se 1 (by rfl) ⟨2704625, by rfl⟩ : syracuseStep 3606167 = 5409251) B5409251
theorem B2500247 : Blo 1480560 2500247 := bstep (se 1 (by rfl) ⟨1875185, by rfl⟩ : syracuseStep 2500247 = 3750371) B3750371
theorem B2221721 : Blo 1480560 2221721 := bstep (se 2 (by rfl) ⟨833145, by rfl⟩ : syracuseStep 2221721 = 1666291) B1666291
theorem B4744925 : Blo 1480560 4744925 := bstep (se 3 (by rfl) ⟨889673, by rfl⟩ : syracuseStep 4744925 = 1779347) B1779347
theorem B2221835 : Blo 1480560 2221835 := bstep (se 1 (by rfl) ⟨1666376, by rfl⟩ : syracuseStep 2221835 = 3332753) B3332753
theorem B6006545 : Blo 1480560 6006545 := bstep (se 2 (by rfl) ⟨2252454, by rfl⟩ : syracuseStep 6006545 = 4504909) B4504909
theorem B2221847 : Blo 1480560 2221847 := bstep (se 1 (by rfl) ⟨1666385, by rfl⟩ : syracuseStep 2221847 = 3332771) B3332771
theorem B2500375 : Blo 1480560 2500375 := bstep (se 1 (by rfl) ⟨1875281, by rfl⟩ : syracuseStep 2500375 = 3750563) B3750563
theorem B2221913 : Blo 1480560 2221913 := bstep (se 2 (by rfl) ⟨833217, by rfl⟩ : syracuseStep 2221913 = 1666435) B1666435
theorem B9013123 : Blo 1480560 9013123 := bstep (se 1 (by rfl) ⟨6759842, by rfl⟩ : syracuseStep 9013123 = 13519685) B13519685
theorem B6006673 : Blo 1480560 6006673 := bstep (se 2 (by rfl) ⟨2252502, by rfl⟩ : syracuseStep 6006673 = 4505005) B4505005
theorem B5621683 : Blo 1480560 5621683 := bstep (se 1 (by rfl) ⟨4216262, by rfl⟩ : syracuseStep 5621683 = 8432525) B8432525
theorem B2222027 : Blo 1480560 2222027 := bstep (se 1 (by rfl) ⟨1666520, by rfl⟩ : syracuseStep 2222027 = 3333041) B3333041
theorem B2222039 : Blo 1480560 2222039 := bstep (se 1 (by rfl) ⟨1666529, by rfl⟩ : syracuseStep 2222039 = 3333059) B3333059
theorem B2811905 : Blo 1480560 2811905 := bstep (se 2 (by rfl) ⟨1054464, by rfl⟩ : syracuseStep 2811905 = 2108929) B2108929
theorem B2222105 : Blo 1480560 2222105 := bstep (se 2 (by rfl) ⟨833289, by rfl⟩ : syracuseStep 2222105 = 1666579) B1666579
theorem B2001035 : Blo 1480560 2001035 := bstep (se 1 (by rfl) ⟨1500776, by rfl⟩ : syracuseStep 2001035 = 3001553) B3001553
theorem B2222219 : Blo 1480560 2222219 := bstep (se 1 (by rfl) ⟨1666664, by rfl⟩ : syracuseStep 2222219 = 3333329) B3333329
theorem B1779851 : Blo 1480560 1779851 := bstep (se 1 (by rfl) ⟨1334888, by rfl⟩ : syracuseStep 1779851 = 2669777) B2669777
theorem B4999319 : Blo 1480560 4999319 := bstep (se 1 (by rfl) ⟨3749489, by rfl⟩ : syracuseStep 4999319 = 7498979) B7498979
theorem B2222231 : Blo 1480560 2222231 := bstep (se 1 (by rfl) ⟨1666673, by rfl⟩ : syracuseStep 2222231 = 3333347) B3333347
theorem B2779289 : Blo 1480560 2779289 := bstep (se 2 (by rfl) ⟨1042233, by rfl⟩ : syracuseStep 2779289 = 2084467) B2084467
theorem B12650701 : Blo 1480560 12650701 := bstep (se 3 (by rfl) ⟨2372006, by rfl⟩ : syracuseStep 12650701 = 4744013) B4744013
theorem B2222297 : Blo 1480560 2222297 := bstep (se 2 (by rfl) ⟨833361, by rfl⟩ : syracuseStep 2222297 = 1666723) B1666723
theorem B2812171 : Blo 1480560 2812171 := bstep (se 1 (by rfl) ⟨2109128, by rfl⟩ : syracuseStep 2812171 = 4218257) B4218257
theorem B2533655 : Blo 1480560 2533655 := bstep (se 1 (by rfl) ⟨1900241, by rfl⟩ : syracuseStep 2533655 = 3800483) B3800483
theorem B16017709 : Blo 1480560 16017709 := bstep (se 3 (by rfl) ⟨3003320, by rfl⟩ : syracuseStep 16017709 = 6006641) B6006641
theorem B2222411 : Blo 1480560 2222411 := bstep (se 1 (by rfl) ⟨1666808, by rfl⟩ : syracuseStep 2222411 = 3333617) B3333617
theorem B2222423 : Blo 1480560 2222423 := bstep (se 1 (by rfl) ⟨1666817, by rfl⟩ : syracuseStep 2222423 = 3333635) B3333635
theorem B3164555 : Blo 1480560 3164555 := bstep (se 1 (by rfl) ⟨2373416, by rfl⟩ : syracuseStep 3164555 = 4746833) B4746833
theorem B2222489 : Blo 1480560 2222489 := bstep (se 2 (by rfl) ⟨833433, by rfl⟩ : syracuseStep 2222489 = 1666867) B1666867
theorem B2222603 : Blo 1480560 2222603 := bstep (se 1 (by rfl) ⟨1666952, by rfl⟩ : syracuseStep 2222603 = 3333905) B3333905
theorem B2222615 : Blo 1480560 2222615 := bstep (se 1 (by rfl) ⟨1666961, by rfl⟩ : syracuseStep 2222615 = 3333923) B3333923
theorem B3557953 : Blo 1480560 3557953 := bstep (se 2 (by rfl) ⟨1334232, by rfl⟩ : syracuseStep 3557953 = 2668465) B2668465
theorem B2222681 : Blo 1480560 2222681 := bstep (se 2 (by rfl) ⟨833505, by rfl⟩ : syracuseStep 2222681 = 1667011) B1667011
theorem B1665643 : Blo 1480560 1665643 := bstep (se 1 (by rfl) ⟨1249232, by rfl⟩ : syracuseStep 1665643 = 2498465) B2498465
theorem B4999859 : Blo 1480560 4999859 := bstep (se 1 (by rfl) ⟨3749894, by rfl⟩ : syracuseStep 4999859 = 7499789) B7499789
theorem B2812619 : Blo 1480560 2812619 := bstep (se 1 (by rfl) ⟨2109464, by rfl⟩ : syracuseStep 2812619 = 4218929) B4218929
theorem B2222795 : Blo 1480560 2222795 := bstep (se 1 (by rfl) ⟨1667096, by rfl⟩ : syracuseStep 2222795 = 3334193) B3334193
theorem B43305677 : Blo 1480560 43305677 := bstep (se 3 (by rfl) ⟨8119814, by rfl⟩ : syracuseStep 43305677 = 16239629) B16239629
theorem B1665751 : Blo 1480560 1665751 := bstep (se 1 (by rfl) ⟨1249313, by rfl⟩ : syracuseStep 1665751 = 2498627) B2498627
theorem B2222807 : Blo 1480560 2222807 := bstep (se 1 (by rfl) ⟨1667105, by rfl⟩ : syracuseStep 2222807 = 3334211) B3334211
theorem B6007517 : Blo 1480560 6007517 := bstep (se 3 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 6007517 = 2252819) B2252819
theorem B2222873 : Blo 1480560 2222873 := bstep (se 2 (by rfl) ⟨833577, by rfl⟩ : syracuseStep 2222873 = 1667155) B1667155
theorem B2812801 : Blo 1480560 2812801 := bstep (se 2 (by rfl) ⟨1054800, by rfl⟩ : syracuseStep 2812801 = 2109601) B2109601
theorem B1665931 : Blo 1480560 1665931 := bstep (se 1 (by rfl) ⟨1249448, by rfl⟩ : syracuseStep 1665931 = 2498897) B2498897
theorem B2222987 : Blo 1480560 2222987 := bstep (se 1 (by rfl) ⟨1667240, by rfl⟩ : syracuseStep 2222987 = 3334481) B3334481
theorem B2222999 : Blo 1480560 2222999 := bstep (se 1 (by rfl) ⟨1667249, by rfl⟩ : syracuseStep 2222999 = 3334499) B3334499
theorem B5000129 : Blo 1480560 5000129 := bstep (se 2 (by rfl) ⟨1875048, by rfl⟩ : syracuseStep 5000129 = 3750097) B3750097
theorem B2223065 : Blo 1480560 2223065 := bstep (se 2 (by rfl) ⟨833649, by rfl⟩ : syracuseStep 2223065 = 1667299) B1667299
theorem B1666039 : Blo 1480560 1666039 := bstep (se 1 (by rfl) ⟨1249529, by rfl⟩ : syracuseStep 1666039 = 2499059) B2499059
theorem B7498817 : Blo 1480560 7498817 := bstep (se 2 (by rfl) ⟨2812056, by rfl⟩ : syracuseStep 7498817 = 5624113) B5624113
theorem B5622929 : Blo 1480560 5622929 := bstep (se 2 (by rfl) ⟨2108598, by rfl⟩ : syracuseStep 5622929 = 4217197) B4217197
theorem B1666219 : Blo 1480560 1666219 := bstep (se 1 (by rfl) ⟨1249664, by rfl⟩ : syracuseStep 1666219 = 2499329) B2499329
theorem B2813143 : Blo 1480560 2813143 := bstep (se 1 (by rfl) ⟨2109857, by rfl⟩ : syracuseStep 2813143 = 4219715) B4219715
theorem B1666327 : Blo 1480560 1666327 := bstep (se 1 (by rfl) ⟨1249745, by rfl⟩ : syracuseStep 1666327 = 2499491) B2499491
theorem B5066135 : Blo 1480560 5066135 := bstep (se 1 (by rfl) ⟨3799601, by rfl⟩ : syracuseStep 5066135 = 7599203) B7599203
theorem B1625515 : Blo 1480560 1625515 := bstep (se 1 (by rfl) ⟨1219136, by rfl⟩ : syracuseStep 1625515 = 2438273) B2438273
theorem B2813363 : Blo 1480560 2813363 := bstep (se 1 (by rfl) ⟨2110022, by rfl⟩ : syracuseStep 2813363 = 4220045) B4220045
theorem B1666507 : Blo 1480560 1666507 := bstep (se 1 (by rfl) ⟨1249880, by rfl⟩ : syracuseStep 1666507 = 2499761) B2499761
theorem B5000669 : Blo 1480560 5000669 := bstep (se 3 (by rfl) ⟨937625, by rfl⟩ : syracuseStep 5000669 = 1875251) B1875251
theorem B6327811 : Blo 1480560 6327811 := bstep (se 1 (by rfl) ⟨4745858, by rfl⟩ : syracuseStep 6327811 = 9491717) B9491717
theorem B12652037 : Blo 1480560 12652037 := bstep (se 4 (by rfl) ⟨1186128, by rfl⟩ : syracuseStep 12652037 = 2372257) B2372257
theorem B1666615 : Blo 1480560 1666615 := bstep (se 1 (by rfl) ⟨1249961, by rfl⟩ : syracuseStep 1666615 = 2499923) B2499923
theorem B3001943 : Blo 1480560 3001943 := bstep (se 1 (by rfl) ⟨2251457, by rfl⟩ : syracuseStep 3001943 = 4502915) B4502915
theorem B2813591 : Blo 1480560 2813591 := bstep (se 1 (by rfl) ⟨2110193, by rfl⟩ : syracuseStep 2813591 = 4220387) B4220387
theorem B1666795 : Blo 1480560 1666795 := bstep (se 1 (by rfl) ⟨1250096, by rfl⟩ : syracuseStep 1666795 = 2500193) B2500193
theorem B7597889 : Blo 1480560 7597889 := bstep (se 2 (by rfl) ⟨2849208, by rfl⟩ : syracuseStep 7597889 = 5698417) B5698417
theorem B5623627 : Blo 1480560 5623627 := bstep (se 1 (by rfl) ⟨4217720, by rfl⟩ : syracuseStep 5623627 = 8435441) B8435441
theorem B1666903 : Blo 1480560 1666903 := bstep (se 1 (by rfl) ⟨1250177, by rfl⟩ : syracuseStep 1666903 = 2500355) B2500355
theorem B2404313 : Blo 1480560 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B1667083 : Blo 1480560 1667083 := bstep (se 1 (by rfl) ⟨1250312, by rfl⟩ : syracuseStep 1667083 = 2500625) B2500625
theorem B5623901 : Blo 1480560 5623901 := bstep (se 3 (by rfl) ⟨1054481, by rfl⟩ : syracuseStep 5623901 = 2108963) B2108963
theorem B1667191 : Blo 1480560 1667191 := bstep (se 1 (by rfl) ⟨1250393, by rfl⟩ : syracuseStep 1667191 = 2500787) B2500787
theorem B3747991 : Blo 1480560 3747991 := bstep (se 1 (by rfl) ⟨2810993, by rfl⟩ : syracuseStep 3747991 = 5621987) B5621987
theorem B6009011 : Blo 1480560 6009011 := bstep (se 1 (by rfl) ⟨4506758, by rfl⟩ : syracuseStep 6009011 = 9013517) B9013517
theorem B2109721 : Blo 1480560 2109721 := bstep (se 2 (by rfl) ⟨791145, by rfl⟩ : syracuseStep 2109721 = 1582291) B1582291
theorem B5337419 : Blo 1480560 5337419 := bstep (se 1 (by rfl) ⟨4003064, by rfl⟩ : syracuseStep 5337419 = 8006129) B8006129
theorem B3609011 : Blo 1480560 3609011 := bstep (se 1 (by rfl) ⟨2706758, by rfl⟩ : syracuseStep 3609011 = 5413517) B5413517
theorem B3748427 : Blo 1480560 3748427 := bstep (se 1 (by rfl) ⟨2811320, by rfl⟩ : syracuseStep 3748427 = 5622641) B5622641
theorem B5001803 : Blo 1480560 5001803 := bstep (se 1 (by rfl) ⟨3751352, by rfl⟩ : syracuseStep 5001803 = 7502705) B7502705
theorem B10678877 : Blo 1480560 10678877 := bstep (se 3 (by rfl) ⟨2002289, by rfl⟩ : syracuseStep 10678877 = 4004579) B4004579
theorem B3560087 : Blo 1480560 3560087 := bstep (se 1 (by rfl) ⟨2670065, by rfl⟩ : syracuseStep 3560087 = 5340131) B5340131
theorem B5624599 : Blo 1480560 5624599 := bstep (se 1 (by rfl) ⟨4218449, by rfl⟩ : syracuseStep 5624599 = 8436899) B8436899
theorem B6411097 : Blo 1480560 6411097 := bstep (se 2 (by rfl) ⟨2404161, by rfl⟩ : syracuseStep 6411097 = 4808323) B4808323
theorem B12014513 : Blo 1480560 12014513 := bstep (se 2 (by rfl) ⟨4505442, by rfl⟩ : syracuseStep 12014513 = 9010885) B9010885
theorem B3748801 : Blo 1480560 3748801 := bstep (se 2 (by rfl) ⟨1405800, by rfl⟩ : syracuseStep 3748801 = 2811601) B2811601
theorem B7500761 : Blo 1480560 7500761 := bstep (se 2 (by rfl) ⟨2812785, by rfl⟩ : syracuseStep 7500761 = 5625571) B5625571
theorem B6329623 : Blo 1480560 6329623 := bstep (se 1 (by rfl) ⟨4747217, by rfl⟩ : syracuseStep 6329623 = 9494435) B9494435
theorem B3331403 : Blo 1480560 3331403 := bstep (se 1 (by rfl) ⟨2498552, by rfl⟩ : syracuseStep 3331403 = 4997105) B4997105
theorem B3331457 : Blo 1480560 3331457 := bstep (se 2 (by rfl) ⟨1249296, by rfl⟩ : syracuseStep 3331457 = 2498593) B2498593
theorem B8435123 : Blo 1480560 8435123 := bstep (se 1 (by rfl) ⟨6326342, by rfl⟩ : syracuseStep 8435123 = 12652685) B12652685
theorem B3749399 : Blo 1480560 3749399 := bstep (se 1 (by rfl) ⟨2812049, by rfl⟩ : syracuseStep 3749399 = 5624099) B5624099
theorem B5625389 : Blo 1480560 5625389 := bstep (se 3 (by rfl) ⟨1054760, by rfl⟩ : syracuseStep 5625389 = 2109521) B2109521
theorem B3331673 : Blo 1480560 3331673 := bstep (se 2 (by rfl) ⟨1249377, by rfl⟩ : syracuseStep 3331673 = 2498755) B2498755
theorem B10131095 : Blo 1480560 10131095 := bstep (se 1 (by rfl) ⟨7598321, by rfl⟩ : syracuseStep 10131095 = 15196643) B15196643
theorem B11556503 : Blo 1480560 11556503 := bstep (se 1 (by rfl) ⟨8667377, by rfl⟩ : syracuseStep 11556503 = 17334755) B17334755
theorem B3331763 : Blo 1480560 3331763 := bstep (se 1 (by rfl) ⟨2498822, by rfl⟩ : syracuseStep 3331763 = 4997645) B4997645
theorem B3331799 : Blo 1480560 3331799 := bstep (se 1 (by rfl) ⟨2498849, by rfl⟩ : syracuseStep 3331799 = 4997699) B4997699
theorem B3004147 : Blo 1480560 3004147 := bstep (se 1 (by rfl) ⟨2253110, by rfl⟩ : syracuseStep 3004147 = 4506221) B4506221
theorem B4216627 : Blo 1480560 4216627 := bstep (se 1 (by rfl) ⟨3162470, by rfl⟩ : syracuseStep 4216627 = 6324941) B6324941
theorem B7116619 : Blo 1480560 7116619 := bstep (se 1 (by rfl) ⟨5337464, by rfl⟩ : syracuseStep 7116619 = 10674929) B10674929
theorem B13006693 : Blo 1480560 13006693 := bstep (se 4 (by rfl) ⟨1219377, by rfl⟩ : syracuseStep 13006693 = 2438755) B2438755
theorem B1480567 : Blo 1480560 1480567 := bstep (se 1 (by rfl) ⟨1110425, by rfl⟩ : syracuseStep 1480567 = 2220851) B2220851
theorem B1480587 : Blo 1480560 1480587 := bstep (se 1 (by rfl) ⟨1110440, by rfl⟩ : syracuseStep 1480587 = 2220881) B2220881
theorem B3331979 : Blo 1480560 3331979 := bstep (se 1 (by rfl) ⟨2498984, by rfl⟩ : syracuseStep 3331979 = 4997969) B4997969
theorem B6330257 : Blo 1480560 6330257 := bstep (se 2 (by rfl) ⟨2373846, by rfl⟩ : syracuseStep 6330257 = 4747693) B4747693
theorem B1480599 : Blo 1480560 1480599 := bstep (se 1 (by rfl) ⟨1110449, by rfl⟩ : syracuseStep 1480599 = 2220899) B2220899
theorem B1480619 : Blo 1480560 1480619 := bstep (se 1 (by rfl) ⟨1110464, by rfl⟩ : syracuseStep 1480619 = 2220929) B2220929
theorem B1480631 : Blo 1480560 1480631 := bstep (se 1 (by rfl) ⟨1110473, by rfl⟩ : syracuseStep 1480631 = 2220947) B2220947
theorem B1603511 : Blo 1480560 1603511 := bstep (se 1 (by rfl) ⟨1202633, by rfl⟩ : syracuseStep 1603511 = 2405267) B2405267
theorem B3332033 : Blo 1480560 3332033 := bstep (se 2 (by rfl) ⟨1249512, by rfl⟩ : syracuseStep 3332033 = 2499025) B2499025
theorem B1480651 : Blo 1480560 1480651 := bstep (se 1 (by rfl) ⟨1110488, by rfl⟩ : syracuseStep 1480651 = 2220977) B2220977
theorem B1480663 : Blo 1480560 1480663 := bstep (se 1 (by rfl) ⟨1110497, by rfl⟩ : syracuseStep 1480663 = 2220995) B2220995
theorem B16873433 : Blo 1480560 16873433 := bstep (se 2 (by rfl) ⟨6327537, by rfl⟩ : syracuseStep 16873433 = 12655075) B12655075
theorem B1480683 : Blo 1480560 1480683 := bstep (se 1 (by rfl) ⟨1110512, by rfl⟩ : syracuseStep 1480683 = 2221025) B2221025
theorem B1480695 : Blo 1480560 1480695 := bstep (se 1 (by rfl) ⟨1110521, by rfl⟩ : syracuseStep 1480695 = 2221043) B2221043
theorem B1480715 : Blo 1480560 1480715 := bstep (se 1 (by rfl) ⟨1110536, by rfl⟩ : syracuseStep 1480715 = 2221073) B2221073
theorem B1480727 : Blo 1480560 1480727 := bstep (se 1 (by rfl) ⟨1110545, by rfl⟩ : syracuseStep 1480727 = 2221091) B2221091
theorem B4216855 : Blo 1480560 4216855 := bstep (se 1 (by rfl) ⟨3162641, by rfl⟩ : syracuseStep 4216855 = 6325283) B6325283
theorem B1480747 : Blo 1480560 1480747 := bstep (se 1 (by rfl) ⟨1110560, by rfl⟩ : syracuseStep 1480747 = 2221121) B2221121
theorem B102660149 : Blo 1480560 102660149 := bstep (se 5 (by rfl) ⟨4812194, by rfl⟩ : syracuseStep 102660149 = 9624389) B9624389
theorem B1480759 : Blo 1480560 1480759 := bstep (se 1 (by rfl) ⟨1110569, by rfl⟩ : syracuseStep 1480759 = 2221139) B2221139
theorem B1480779 : Blo 1480560 1480779 := bstep (se 1 (by rfl) ⟨1110584, by rfl⟩ : syracuseStep 1480779 = 2221169) B2221169
theorem B1480791 : Blo 1480560 1480791 := bstep (se 1 (by rfl) ⟨1110593, by rfl⟩ : syracuseStep 1480791 = 2221187) B2221187
theorem B1480811 : Blo 1480560 1480811 := bstep (se 1 (by rfl) ⟨1110608, by rfl⟩ : syracuseStep 1480811 = 2221217) B2221217
theorem B1480823 : Blo 1480560 1480823 := bstep (se 1 (by rfl) ⟨1110617, by rfl⟩ : syracuseStep 1480823 = 2221235) B2221235
theorem B1480843 : Blo 1480560 1480843 := bstep (se 1 (by rfl) ⟨1110632, by rfl⟩ : syracuseStep 1480843 = 2221265) B2221265
theorem B1480855 : Blo 1480560 1480855 := bstep (se 1 (by rfl) ⟨1110641, by rfl⟩ : syracuseStep 1480855 = 2221283) B2221283
theorem B44480663 : Blo 1480560 44480663 := bstep (se 1 (by rfl) ⟨33360497, by rfl⟩ : syracuseStep 44480663 = 66720995) B66720995
theorem B3332249 : Blo 1480560 3332249 := bstep (se 2 (by rfl) ⟨1249593, by rfl⟩ : syracuseStep 3332249 = 2499187) B2499187
theorem B1480875 : Blo 1480560 1480875 := bstep (se 1 (by rfl) ⟨1110656, by rfl⟩ : syracuseStep 1480875 = 2221313) B2221313
theorem B1480887 : Blo 1480560 1480887 := bstep (se 1 (by rfl) ⟨1110665, by rfl⟩ : syracuseStep 1480887 = 2221331) B2221331
theorem B1480907 : Blo 1480560 1480907 := bstep (se 1 (by rfl) ⟨1110680, by rfl⟩ : syracuseStep 1480907 = 2221361) B2221361
theorem B1480919 : Blo 1480560 1480919 := bstep (se 1 (by rfl) ⟨1110689, by rfl⟩ : syracuseStep 1480919 = 2221379) B2221379
theorem B1480939 : Blo 1480560 1480939 := bstep (se 1 (by rfl) ⟨1110704, by rfl⟩ : syracuseStep 1480939 = 2221409) B2221409
theorem B3332339 : Blo 1480560 3332339 := bstep (se 1 (by rfl) ⟨2499254, by rfl⟩ : syracuseStep 3332339 = 4998509) B4998509
theorem B1480951 : Blo 1480560 1480951 := bstep (se 1 (by rfl) ⟨1110713, by rfl⟩ : syracuseStep 1480951 = 2221427) B2221427
theorem B1480971 : Blo 1480560 1480971 := bstep (se 1 (by rfl) ⟨1110728, by rfl⟩ : syracuseStep 1480971 = 2221457) B2221457
theorem B1480983 : Blo 1480560 1480983 := bstep (se 1 (by rfl) ⟨1110737, by rfl⟩ : syracuseStep 1480983 = 2221475) B2221475
theorem B3332375 : Blo 1480560 3332375 := bstep (se 1 (by rfl) ⟨2499281, by rfl⟩ : syracuseStep 3332375 = 4998563) B4998563
theorem B1481003 : Blo 1480560 1481003 := bstep (se 1 (by rfl) ⟨1110752, by rfl⟩ : syracuseStep 1481003 = 2221505) B2221505
theorem B1734967 : Blo 1480560 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B1481015 : Blo 1480560 1481015 := bstep (se 1 (by rfl) ⟨1110761, by rfl⟩ : syracuseStep 1481015 = 2221523) B2221523
theorem B3750209 : Blo 1480560 3750209 := bstep (se 2 (by rfl) ⟨1406328, by rfl⟩ : syracuseStep 3750209 = 2812657) B2812657
theorem B1481035 : Blo 1480560 1481035 := bstep (se 1 (by rfl) ⟨1110776, by rfl⟩ : syracuseStep 1481035 = 2221553) B2221553
theorem B1481047 : Blo 1480560 1481047 := bstep (se 1 (by rfl) ⟨1110785, by rfl⟩ : syracuseStep 1481047 = 2221571) B2221571
theorem B1481067 : Blo 1480560 1481067 := bstep (se 1 (by rfl) ⟨1110800, by rfl⟩ : syracuseStep 1481067 = 2221601) B2221601
theorem B1481079 : Blo 1480560 1481079 := bstep (se 1 (by rfl) ⟨1110809, by rfl⟩ : syracuseStep 1481079 = 2221619) B2221619
theorem B1481099 : Blo 1480560 1481099 := bstep (se 1 (by rfl) ⟨1110824, by rfl⟩ : syracuseStep 1481099 = 2221649) B2221649
theorem B1481111 : Blo 1480560 1481111 := bstep (se 1 (by rfl) ⟨1110833, by rfl⟩ : syracuseStep 1481111 = 2221667) B2221667
theorem B3086743 : Blo 1480560 3086743 := bstep (se 1 (by rfl) ⟨2315057, by rfl⟩ : syracuseStep 3086743 = 4630115) B4630115
theorem B1481131 : Blo 1480560 1481131 := bstep (se 1 (by rfl) ⟨1110848, by rfl⟩ : syracuseStep 1481131 = 2221697) B2221697
theorem B1481143 : Blo 1480560 1481143 := bstep (se 1 (by rfl) ⟨1110857, by rfl⟩ : syracuseStep 1481143 = 2221715) B2221715
theorem B3332555 : Blo 1480560 3332555 := bstep (se 1 (by rfl) ⟨2499416, by rfl⟩ : syracuseStep 3332555 = 4998833) B4998833
theorem B1481163 : Blo 1480560 1481163 := bstep (se 1 (by rfl) ⟨1110872, by rfl⟩ : syracuseStep 1481163 = 2221745) B2221745
theorem B1481175 : Blo 1480560 1481175 := bstep (se 1 (by rfl) ⟨1110881, by rfl⟩ : syracuseStep 1481175 = 2221763) B2221763
theorem B1481195 : Blo 1480560 1481195 := bstep (se 1 (by rfl) ⟨1110896, by rfl⟩ : syracuseStep 1481195 = 2221793) B2221793
theorem B1481207 : Blo 1480560 1481207 := bstep (se 1 (by rfl) ⟨1110905, by rfl⟩ : syracuseStep 1481207 = 2221811) B2221811
theorem B3332609 : Blo 1480560 3332609 := bstep (se 2 (by rfl) ⟨1249728, by rfl⟩ : syracuseStep 3332609 = 2499457) B2499457
theorem B1481227 : Blo 1480560 1481227 := bstep (se 1 (by rfl) ⟨1110920, by rfl⟩ : syracuseStep 1481227 = 2221841) B2221841
theorem B1481239 : Blo 1480560 1481239 := bstep (se 1 (by rfl) ⟨1110929, by rfl⟩ : syracuseStep 1481239 = 2221859) B2221859
theorem B1481259 : Blo 1480560 1481259 := bstep (se 1 (by rfl) ⟨1110944, by rfl⟩ : syracuseStep 1481259 = 2221889) B2221889
theorem B7502381 : Blo 1480560 7502381 := bstep (se 3 (by rfl) ⟨1406696, by rfl⟩ : syracuseStep 7502381 = 2813393) B2813393
theorem B1481271 : Blo 1480560 1481271 := bstep (se 1 (by rfl) ⟨1110953, by rfl⟩ : syracuseStep 1481271 = 2221907) B2221907
theorem B1481291 : Blo 1480560 1481291 := bstep (se 1 (by rfl) ⟨1110968, by rfl⟩ : syracuseStep 1481291 = 2221937) B2221937
theorem B1481303 : Blo 1480560 1481303 := bstep (se 1 (by rfl) ⟨1110977, by rfl⟩ : syracuseStep 1481303 = 2221955) B2221955
theorem B1481323 : Blo 1480560 1481323 := bstep (se 1 (by rfl) ⟨1110992, by rfl⟩ : syracuseStep 1481323 = 2221985) B2221985
theorem B2669171 : Blo 1480560 2669171 := bstep (se 1 (by rfl) ⟨2001878, by rfl⟩ : syracuseStep 2669171 = 4003757) B4003757
theorem B1481335 : Blo 1480560 1481335 := bstep (se 1 (by rfl) ⟨1111001, by rfl⟩ : syracuseStep 1481335 = 2222003) B2222003
theorem B2251403 : Blo 1480560 2251403 := bstep (se 1 (by rfl) ⟨1688552, by rfl⟩ : syracuseStep 2251403 = 3377105) B3377105
theorem B1481355 : Blo 1480560 1481355 := bstep (se 1 (by rfl) ⟨1111016, by rfl⟩ : syracuseStep 1481355 = 2222033) B2222033
theorem B1481367 : Blo 1480560 1481367 := bstep (se 1 (by rfl) ⟨1111025, by rfl⟩ : syracuseStep 1481367 = 2222051) B2222051
theorem B1481387 : Blo 1480560 1481387 := bstep (se 1 (by rfl) ⟨1111040, by rfl⟩ : syracuseStep 1481387 = 2222081) B2222081
theorem B1481399 : Blo 1480560 1481399 := bstep (se 1 (by rfl) ⟨1111049, by rfl⟩ : syracuseStep 1481399 = 2222099) B2222099
theorem B1481419 : Blo 1480560 1481419 := bstep (se 1 (by rfl) ⟨1111064, by rfl⟩ : syracuseStep 1481419 = 2222129) B2222129
theorem B1481431 : Blo 1480560 1481431 := bstep (se 1 (by rfl) ⟨1111073, by rfl⟩ : syracuseStep 1481431 = 2222147) B2222147
theorem B3332825 : Blo 1480560 3332825 := bstep (se 2 (by rfl) ⟨1249809, by rfl⟩ : syracuseStep 3332825 = 2499619) B2499619
theorem B1481451 : Blo 1480560 1481451 := bstep (se 1 (by rfl) ⟨1111088, by rfl⟩ : syracuseStep 1481451 = 2222177) B2222177
theorem B1481463 : Blo 1480560 1481463 := bstep (se 1 (by rfl) ⟨1111097, by rfl⟩ : syracuseStep 1481463 = 2222195) B2222195
theorem B1481483 : Blo 1480560 1481483 := bstep (se 1 (by rfl) ⟨1111112, by rfl⟩ : syracuseStep 1481483 = 2222225) B2222225
theorem B1481495 : Blo 1480560 1481495 := bstep (se 1 (by rfl) ⟨1111121, by rfl⟩ : syracuseStep 1481495 = 2222243) B2222243
theorem B1481515 : Blo 1480560 1481515 := bstep (se 1 (by rfl) ⟨1111136, by rfl⟩ : syracuseStep 1481515 = 2222273) B2222273
theorem B3332915 : Blo 1480560 3332915 := bstep (se 1 (by rfl) ⟨2499686, by rfl⟩ : syracuseStep 3332915 = 4999373) B4999373
theorem B1481527 : Blo 1480560 1481527 := bstep (se 1 (by rfl) ⟨1111145, by rfl⟩ : syracuseStep 1481527 = 2222291) B2222291
theorem B1481547 : Blo 1480560 1481547 := bstep (se 1 (by rfl) ⟨1111160, by rfl⟩ : syracuseStep 1481547 = 2222321) B2222321
theorem B3332951 : Blo 1480560 3332951 := bstep (se 1 (by rfl) ⟨2499713, by rfl⟩ : syracuseStep 3332951 = 4999427) B4999427
theorem B1481559 : Blo 1480560 1481559 := bstep (se 1 (by rfl) ⟨1111169, by rfl⟩ : syracuseStep 1481559 = 2222339) B2222339
theorem B3750745 : Blo 1480560 3750745 := bstep (se 2 (by rfl) ⟨1406529, by rfl⟩ : syracuseStep 3750745 = 2813059) B2813059
theorem B8436581 : Blo 1480560 8436581 := bstep (se 4 (by rfl) ⟨790929, by rfl⟩ : syracuseStep 8436581 = 1581859) B1581859
theorem B1481579 : Blo 1480560 1481579 := bstep (se 1 (by rfl) ⟨1111184, by rfl⟩ : syracuseStep 1481579 = 2222369) B2222369
theorem B1481591 : Blo 1480560 1481591 := bstep (se 1 (by rfl) ⟨1111193, by rfl⟩ : syracuseStep 1481591 = 2222387) B2222387
theorem B1481611 : Blo 1480560 1481611 := bstep (se 1 (by rfl) ⟨1111208, by rfl⟩ : syracuseStep 1481611 = 2222417) B2222417
theorem B1481623 : Blo 1480560 1481623 := bstep (se 1 (by rfl) ⟨1111217, by rfl⟩ : syracuseStep 1481623 = 2222435) B2222435
theorem B5069719 : Blo 1480560 5069719 := bstep (se 1 (by rfl) ⟨3802289, by rfl⟩ : syracuseStep 5069719 = 7604579) B7604579
theorem B1481643 : Blo 1480560 1481643 := bstep (se 1 (by rfl) ⟨1111232, by rfl⟩ : syracuseStep 1481643 = 2222465) B2222465
theorem B1481655 : Blo 1480560 1481655 := bstep (se 1 (by rfl) ⟨1111241, by rfl⟩ : syracuseStep 1481655 = 2222483) B2222483
theorem B5626817 : Blo 1480560 5626817 := bstep (se 2 (by rfl) ⟨2110056, by rfl⟩ : syracuseStep 5626817 = 4220113) B4220113
theorem B3800011 : Blo 1480560 3800011 := bstep (se 1 (by rfl) ⟨2850008, by rfl⟩ : syracuseStep 3800011 = 5700017) B5700017
theorem B1481675 : Blo 1480560 1481675 := bstep (se 1 (by rfl) ⟨1111256, by rfl⟩ : syracuseStep 1481675 = 2222513) B2222513
theorem B1481687 : Blo 1480560 1481687 := bstep (se 1 (by rfl) ⟨1111265, by rfl⟩ : syracuseStep 1481687 = 2222531) B2222531
theorem B1481707 : Blo 1480560 1481707 := bstep (se 1 (by rfl) ⟨1111280, by rfl⟩ : syracuseStep 1481707 = 2222561) B2222561
theorem B1481719 : Blo 1480560 1481719 := bstep (se 1 (by rfl) ⟨1111289, by rfl⟩ : syracuseStep 1481719 = 2222579) B2222579
theorem B3333131 : Blo 1480560 3333131 := bstep (se 1 (by rfl) ⟨2499848, by rfl⟩ : syracuseStep 3333131 = 4999697) B4999697
theorem B1481739 : Blo 1480560 1481739 := bstep (se 1 (by rfl) ⟨1111304, by rfl⟩ : syracuseStep 1481739 = 2222609) B2222609
theorem B1481751 : Blo 1480560 1481751 := bstep (se 1 (by rfl) ⟨1111313, by rfl⟩ : syracuseStep 1481751 = 2222627) B2222627
theorem B1481771 : Blo 1480560 1481771 := bstep (se 1 (by rfl) ⟨1111328, by rfl⟩ : syracuseStep 1481771 = 2222657) B2222657
theorem B1481783 : Blo 1480560 1481783 := bstep (se 1 (by rfl) ⟨1111337, by rfl⟩ : syracuseStep 1481783 = 2222675) B2222675
theorem B3333185 : Blo 1480560 3333185 := bstep (se 2 (by rfl) ⟨1249944, by rfl⟩ : syracuseStep 3333185 = 2499889) B2499889
theorem B1481803 : Blo 1480560 1481803 := bstep (se 1 (by rfl) ⟨1111352, by rfl⟩ : syracuseStep 1481803 = 2222705) B2222705
theorem B1481815 : Blo 1480560 1481815 := bstep (se 1 (by rfl) ⟨1111361, by rfl⟩ : syracuseStep 1481815 = 2222723) B2222723
theorem B1481835 : Blo 1480560 1481835 := bstep (se 1 (by rfl) ⟨1111376, by rfl⟩ : syracuseStep 1481835 = 2222753) B2222753
theorem B1481847 : Blo 1480560 1481847 := bstep (se 1 (by rfl) ⟨1111385, by rfl⟩ : syracuseStep 1481847 = 2222771) B2222771
theorem B1481867 : Blo 1480560 1481867 := bstep (se 1 (by rfl) ⟨1111400, by rfl⟩ : syracuseStep 1481867 = 2222801) B2222801
theorem B1481879 : Blo 1480560 1481879 := bstep (se 1 (by rfl) ⟨1111409, by rfl⟩ : syracuseStep 1481879 = 2222819) B2222819
theorem B1481899 : Blo 1480560 1481899 := bstep (se 1 (by rfl) ⟨1111424, by rfl⟩ : syracuseStep 1481899 = 2222849) B2222849
theorem B1481911 : Blo 1480560 1481911 := bstep (se 1 (by rfl) ⟨1111433, by rfl⟩ : syracuseStep 1481911 = 2222867) B2222867
theorem B1481931 : Blo 1480560 1481931 := bstep (se 1 (by rfl) ⟨1111448, by rfl⟩ : syracuseStep 1481931 = 2222897) B2222897
theorem B1481943 : Blo 1480560 1481943 := bstep (se 1 (by rfl) ⟨1111457, by rfl⟩ : syracuseStep 1481943 = 2222915) B2222915
theorem B1481963 : Blo 1480560 1481963 := bstep (se 1 (by rfl) ⟨1111472, by rfl⟩ : syracuseStep 1481963 = 2222945) B2222945
theorem B1481975 : Blo 1480560 1481975 := bstep (se 1 (by rfl) ⟨1111481, by rfl⟩ : syracuseStep 1481975 = 2222963) B2222963
theorem B1481995 : Blo 1480560 1481995 := bstep (se 1 (by rfl) ⟨1111496, by rfl⟩ : syracuseStep 1481995 = 2222993) B2222993
theorem B1482007 : Blo 1480560 1482007 := bstep (se 1 (by rfl) ⟨1111505, by rfl⟩ : syracuseStep 1482007 = 2223011) B2223011
theorem B3333401 : Blo 1480560 3333401 := bstep (se 2 (by rfl) ⟨1250025, by rfl⟩ : syracuseStep 3333401 = 2500051) B2500051
theorem B2669849 : Blo 1480560 2669849 := bstep (se 2 (by rfl) ⟨1001193, by rfl⟩ : syracuseStep 2669849 = 2002387) B2002387
theorem B1482027 : Blo 1480560 1482027 := bstep (se 1 (by rfl) ⟨1111520, by rfl⟩ : syracuseStep 1482027 = 2223041) B2223041
theorem B1482039 : Blo 1480560 1482039 := bstep (se 1 (by rfl) ⟨1111529, by rfl⟩ : syracuseStep 1482039 = 2223059) B2223059
theorem B1482059 : Blo 1480560 1482059 := bstep (se 1 (by rfl) ⟨1111544, by rfl⟩ : syracuseStep 1482059 = 2223089) B2223089
theorem B3333491 : Blo 1480560 3333491 := bstep (se 1 (by rfl) ⟨2500118, by rfl⟩ : syracuseStep 3333491 = 5000237) B5000237
theorem B10132867 : Blo 1480560 10132867 := bstep (se 1 (by rfl) ⟨7599650, by rfl⟩ : syracuseStep 10132867 = 15199301) B15199301
theorem B2137495 : Blo 1480560 2137495 := bstep (se 1 (by rfl) ⟨1603121, by rfl⟩ : syracuseStep 2137495 = 3206243) B3206243
theorem B3333527 : Blo 1480560 3333527 := bstep (se 1 (by rfl) ⟨2500145, by rfl⟩ : syracuseStep 3333527 = 5000291) B5000291
theorem B1875403 : Blo 1480560 1875403 := bstep (se 1 (by rfl) ⟨1406552, by rfl⟩ : syracuseStep 1875403 = 2813105) B2813105
theorem B4505053 : Blo 1480560 4505053 := bstep (se 3 (by rfl) ⟨844697, by rfl⟩ : syracuseStep 4505053 = 1689395) B1689395
theorem B3333707 : Blo 1480560 3333707 := bstep (se 1 (by rfl) ⟨2500280, by rfl⟩ : syracuseStep 3333707 = 5000561) B5000561
theorem B3333761 : Blo 1480560 3333761 := bstep (se 2 (by rfl) ⟨1250160, by rfl⟩ : syracuseStep 3333761 = 2500321) B2500321
theorem B4218713 : Blo 1480560 4218713 := bstep (se 2 (by rfl) ⟨1582017, by rfl⟩ : syracuseStep 4218713 = 3164035) B3164035
theorem B3333977 : Blo 1480560 3333977 := bstep (se 2 (by rfl) ⟨1250241, by rfl⟩ : syracuseStep 3333977 = 2500483) B2500483
theorem B3334067 : Blo 1480560 3334067 := bstep (se 1 (by rfl) ⟨2500550, by rfl⟩ : syracuseStep 3334067 = 5001101) B5001101
theorem B24035251 : Blo 1480560 24035251 := bstep (se 1 (by rfl) ⟨18026438, by rfl⟩ : syracuseStep 24035251 = 36052877) B36052877
theorem B2498519 : Blo 1480560 2498519 := bstep (se 1 (by rfl) ⟨1873889, by rfl⟩ : syracuseStep 2498519 = 3747779) B3747779
theorem B3334103 : Blo 1480560 3334103 := bstep (se 1 (by rfl) ⟨2500577, by rfl⟩ : syracuseStep 3334103 = 5001155) B5001155
theorem B2670635 : Blo 1480560 2670635 := bstep (se 1 (by rfl) ⟨2002976, by rfl⟩ : syracuseStep 2670635 = 4005953) B4005953
theorem B4006007 : Blo 1480560 4006007 := bstep (se 1 (by rfl) ⟨3004505, by rfl⟩ : syracuseStep 4006007 = 6009011) B6009011
theorem B4997321 : Blo 1480560 4997321 := bstep (se 2 (by rfl) ⟨1873995, by rfl⟩ : syracuseStep 4997321 = 3747991) B3747991
theorem B16867601 : Blo 1480560 16867601 := bstep (se 2 (by rfl) ⟨6325350, by rfl⟩ : syracuseStep 16867601 = 12650701) B12650701
theorem B2498951 : Blo 1480560 2498951 := bstep (se 1 (by rfl) ⟨1874213, by rfl⟩ : syracuseStep 2498951 = 3748427) B3748427
theorem B3334535 : Blo 1480560 3334535 := bstep (se 1 (by rfl) ⟨2500901, by rfl⟩ : syracuseStep 3334535 = 5001803) B5001803
theorem B21356945 : Blo 1480560 21356945 := bstep (se 2 (by rfl) ⟨8008854, by rfl⟩ : syracuseStep 21356945 = 16017709) B16017709
theorem B7119251 : Blo 1480560 7119251 := bstep (se 1 (by rfl) ⟨5339438, by rfl⟩ : syracuseStep 7119251 = 10678877) B10678877
theorem B4743937 : Blo 1480560 4743937 := bstep (se 2 (by rfl) ⟨1778976, by rfl⟩ : syracuseStep 4743937 = 3557953) B3557953
theorem B2220857 : Blo 1480560 2220857 := bstep (se 2 (by rfl) ⟨832821, by rfl⟩ : syracuseStep 2220857 = 1665643) B1665643
theorem B2220935 : Blo 1480560 2220935 := bstep (se 1 (by rfl) ⟨1665701, by rfl⟩ : syracuseStep 2220935 = 3331403) B3331403
theorem B4998023 : Blo 1480560 4998023 := bstep (se 1 (by rfl) ⟨3748517, by rfl⟩ : syracuseStep 4998023 = 7497035) B7497035
theorem B2220971 : Blo 1480560 2220971 := bstep (se 1 (by rfl) ⟨1665728, by rfl⟩ : syracuseStep 2220971 = 3331457) B3331457
theorem B2221001 : Blo 1480560 2221001 := bstep (se 2 (by rfl) ⟨832875, by rfl⟩ : syracuseStep 2221001 = 1665751) B1665751
theorem B2499599 : Blo 1480560 2499599 := bstep (se 1 (by rfl) ⟨1874699, by rfl⟩ : syracuseStep 2499599 = 3749399) B3749399
theorem B8438813 : Blo 1480560 8438813 := bstep (se 3 (by rfl) ⟨1582277, by rfl⟩ : syracuseStep 8438813 = 3164555) B3164555
theorem B2221115 : Blo 1480560 2221115 := bstep (se 1 (by rfl) ⟨1665836, by rfl⟩ : syracuseStep 2221115 = 3331673) B3331673
theorem B2221175 : Blo 1480560 2221175 := bstep (se 1 (by rfl) ⟨1665881, by rfl⟩ : syracuseStep 2221175 = 3331763) B3331763
theorem B2221199 : Blo 1480560 2221199 := bstep (se 1 (by rfl) ⟨1665899, by rfl⟩ : syracuseStep 2221199 = 3331799) B3331799
theorem B3163283 : Blo 1480560 3163283 := bstep (se 1 (by rfl) ⟨2372462, by rfl⟩ : syracuseStep 3163283 = 4744925) B4744925
theorem B2221241 : Blo 1480560 2221241 := bstep (se 2 (by rfl) ⟨832965, by rfl⟩ : syracuseStep 2221241 = 1665931) B1665931
theorem B6759625 : Blo 1480560 6759625 := bstep (se 2 (by rfl) ⟨2534859, by rfl⟩ : syracuseStep 6759625 = 5069719) B5069719
theorem B4998401 : Blo 1480560 4998401 := bstep (se 2 (by rfl) ⟨1874400, by rfl⟩ : syracuseStep 4998401 = 3748801) B3748801
theorem B2221319 : Blo 1480560 2221319 := bstep (se 1 (by rfl) ⟨1665989, by rfl⟩ : syracuseStep 2221319 = 3331979) B3331979
theorem B4220171 : Blo 1480560 4220171 := bstep (se 1 (by rfl) ⟨3165128, by rfl⟩ : syracuseStep 4220171 = 6330257) B6330257
theorem B2221355 : Blo 1480560 2221355 := bstep (se 1 (by rfl) ⟨1666016, by rfl⟩ : syracuseStep 2221355 = 3332033) B3332033
theorem B11248955 : Blo 1480560 11248955 := bstep (se 1 (by rfl) ⟨8436716, by rfl⟩ : syracuseStep 11248955 = 16873433) B16873433
theorem B2221385 : Blo 1480560 2221385 := bstep (se 2 (by rfl) ⟨833019, by rfl⟩ : syracuseStep 2221385 = 1666039) B1666039
theorem B1852859 : Blo 1480560 1852859 := bstep (se 1 (by rfl) ⟨1389644, by rfl⟩ : syracuseStep 1852859 = 2779289) B2779289
theorem B2221499 : Blo 1480560 2221499 := bstep (se 1 (by rfl) ⟨1666124, by rfl⟩ : syracuseStep 2221499 = 3332249) B3332249
theorem B2221559 : Blo 1480560 2221559 := bstep (se 1 (by rfl) ⟨1666169, by rfl⟩ : syracuseStep 2221559 = 3332339) B3332339
theorem B2221583 : Blo 1480560 2221583 := bstep (se 1 (by rfl) ⟨1666187, by rfl⟩ : syracuseStep 2221583 = 3332375) B3332375
theorem B1689103 : Blo 1480560 1689103 := bstep (se 1 (by rfl) ⟨1266827, by rfl⟩ : syracuseStep 1689103 = 2533655) B2533655
theorem B2500139 : Blo 1480560 2500139 := bstep (se 1 (by rfl) ⟨1875104, by rfl⟩ : syracuseStep 2500139 = 3750209) B3750209
theorem B2221625 : Blo 1480560 2221625 := bstep (se 2 (by rfl) ⟨833109, by rfl⟩ : syracuseStep 2221625 = 1666219) B1666219
theorem B2221703 : Blo 1480560 2221703 := bstep (se 1 (by rfl) ⟨1666277, by rfl⟩ : syracuseStep 2221703 = 3332555) B3332555
theorem B2221739 : Blo 1480560 2221739 := bstep (se 1 (by rfl) ⟨1666304, by rfl⟩ : syracuseStep 2221739 = 3332609) B3332609
theorem B2221769 : Blo 1480560 2221769 := bstep (se 2 (by rfl) ⟨833163, by rfl⟩ : syracuseStep 2221769 = 1666327) B1666327
theorem B8439497 : Blo 1480560 8439497 := bstep (se 2 (by rfl) ⟨3164811, by rfl⟩ : syracuseStep 8439497 = 6329623) B6329623
theorem B1500935 : Blo 1480560 1500935 := bstep (se 1 (by rfl) ⟨1125701, by rfl⟩ : syracuseStep 1500935 = 2251403) B2251403
theorem B28870451 : Blo 1480560 28870451 := bstep (se 1 (by rfl) ⟨21652838, by rfl⟩ : syracuseStep 28870451 = 43305677) B43305677
theorem B2221883 : Blo 1480560 2221883 := bstep (se 1 (by rfl) ⟨1666412, by rfl⟩ : syracuseStep 2221883 = 3332825) B3332825
theorem B13510489 : Blo 1480560 13510489 := bstep (se 2 (by rfl) ⟨5066433, by rfl⟩ : syracuseStep 13510489 = 10132867) B10132867
theorem B2221943 : Blo 1480560 2221943 := bstep (se 1 (by rfl) ⟨1666457, by rfl⟩ : syracuseStep 2221943 = 3332915) B3332915
theorem B2221967 : Blo 1480560 2221967 := bstep (se 1 (by rfl) ⟨1666475, by rfl⟩ : syracuseStep 2221967 = 3332951) B3332951
theorem B29263769 : Blo 1480560 29263769 := bstep (se 2 (by rfl) ⟨10973913, by rfl⟩ : syracuseStep 29263769 = 21947827) B21947827
theorem B2222009 : Blo 1480560 2222009 := bstep (se 2 (by rfl) ⟨833253, by rfl⟩ : syracuseStep 2222009 = 1666507) B1666507
theorem B2500537 : Blo 1480560 2500537 := bstep (se 2 (by rfl) ⟨937701, by rfl⟩ : syracuseStep 2500537 = 1875403) B1875403
theorem B6006737 : Blo 1480560 6006737 := bstep (se 2 (by rfl) ⟨2252526, by rfl⟩ : syracuseStep 6006737 = 4505053) B4505053
theorem B2222087 : Blo 1480560 2222087 := bstep (se 1 (by rfl) ⟨1666565, by rfl⟩ : syracuseStep 2222087 = 3333131) B3333131
theorem B4999211 : Blo 1480560 4999211 := bstep (se 1 (by rfl) ⟨3749408, by rfl⟩ : syracuseStep 4999211 = 7498817) B7498817
theorem B2222123 : Blo 1480560 2222123 := bstep (se 1 (by rfl) ⟨1666592, by rfl⟩ : syracuseStep 2222123 = 3333185) B3333185
theorem B2222153 : Blo 1480560 2222153 := bstep (se 2 (by rfl) ⟨833307, by rfl⟩ : syracuseStep 2222153 = 1666615) B1666615
theorem B2222267 : Blo 1480560 2222267 := bstep (se 1 (by rfl) ⟨1666700, by rfl⟩ : syracuseStep 2222267 = 3333401) B3333401
theorem B1779899 : Blo 1480560 1779899 := bstep (se 1 (by rfl) ⟨1334924, by rfl⟩ : syracuseStep 1779899 = 2669849) B2669849
theorem B8669413 : Blo 1480560 8669413 := bstep (se 4 (by rfl) ⟨812757, by rfl⟩ : syracuseStep 8669413 = 1625515) B1625515
theorem B2222327 : Blo 1480560 2222327 := bstep (se 1 (by rfl) ⟨1666745, by rfl⟩ : syracuseStep 2222327 = 3333491) B3333491
theorem B3377423 : Blo 1480560 3377423 := bstep (se 1 (by rfl) ⟨2533067, by rfl⟩ : syracuseStep 3377423 = 5066135) B5066135
theorem B2222351 : Blo 1480560 2222351 := bstep (se 1 (by rfl) ⟨1666763, by rfl⟩ : syracuseStep 2222351 = 3333527) B3333527
theorem B2222393 : Blo 1480560 2222393 := bstep (se 2 (by rfl) ⟨833397, by rfl⟩ : syracuseStep 2222393 = 1666795) B1666795
theorem B2222471 : Blo 1480560 2222471 := bstep (se 1 (by rfl) ⟨1666853, by rfl⟩ : syracuseStep 2222471 = 3333707) B3333707
theorem B2001295 : Blo 1480560 2001295 := bstep (se 1 (by rfl) ⟨1500971, by rfl⟩ : syracuseStep 2001295 = 3001943) B3001943
theorem B5622169 : Blo 1480560 5622169 := bstep (se 2 (by rfl) ⟨2108313, by rfl⟩ : syracuseStep 5622169 = 4216627) B4216627
theorem B2222507 : Blo 1480560 2222507 := bstep (se 1 (by rfl) ⟨1666880, by rfl⟩ : syracuseStep 2222507 = 3333761) B3333761
theorem B9488825 : Blo 1480560 9488825 := bstep (se 2 (by rfl) ⟨3558309, by rfl⟩ : syracuseStep 9488825 = 7116619) B7116619
theorem B7498169 : Blo 1480560 7498169 := bstep (se 2 (by rfl) ⟨2811813, by rfl⟩ : syracuseStep 7498169 = 5623627) B5623627
theorem B2222537 : Blo 1480560 2222537 := bstep (se 2 (by rfl) ⟨833451, by rfl⟩ : syracuseStep 2222537 = 1666903) B1666903
theorem B5065259 : Blo 1480560 5065259 := bstep (se 1 (by rfl) ⟨3798944, by rfl⟩ : syracuseStep 5065259 = 7597889) B7597889
theorem B2812475 : Blo 1480560 2812475 := bstep (se 1 (by rfl) ⟨2109356, by rfl⟩ : syracuseStep 2812475 = 4218713) B4218713
theorem B2222651 : Blo 1480560 2222651 := bstep (se 1 (by rfl) ⟨1666988, by rfl⟩ : syracuseStep 2222651 = 3333977) B3333977
theorem B2222711 : Blo 1480560 2222711 := bstep (se 1 (by rfl) ⟨1667033, by rfl⟩ : syracuseStep 2222711 = 3334067) B3334067
theorem B1665679 : Blo 1480560 1665679 := bstep (se 1 (by rfl) ⟨1249259, by rfl⟩ : syracuseStep 1665679 = 2498519) B2498519
theorem B2222735 : Blo 1480560 2222735 := bstep (se 1 (by rfl) ⟨1667051, by rfl⟩ : syracuseStep 2222735 = 3334103) B3334103
theorem B2222777 : Blo 1480560 2222777 := bstep (se 2 (by rfl) ⟨833541, by rfl⟩ : syracuseStep 2222777 = 1667083) B1667083
theorem B5622473 : Blo 1480560 5622473 := bstep (se 2 (by rfl) ⟨2108427, by rfl⟩ : syracuseStep 5622473 = 4216855) B4216855
theorem B2222855 : Blo 1480560 2222855 := bstep (se 1 (by rfl) ⟨1667141, by rfl⟩ : syracuseStep 2222855 = 3334283) B3334283
theorem B2222891 : Blo 1480560 2222891 := bstep (se 1 (by rfl) ⟨1667168, by rfl⟩ : syracuseStep 2222891 = 3334337) B3334337
theorem B2222921 : Blo 1480560 2222921 := bstep (se 2 (by rfl) ⟨833595, by rfl⟩ : syracuseStep 2222921 = 1667191) B1667191
theorem B23751539 : Blo 1480560 23751539 := bstep (se 1 (by rfl) ⟨17813654, by rfl⟩ : syracuseStep 23751539 = 35627309) B35627309
theorem B2223035 : Blo 1480560 2223035 := bstep (se 1 (by rfl) ⟨1667276, by rfl⟩ : syracuseStep 2223035 = 3334553) B3334553
theorem B12659723 : Blo 1480560 12659723 := bstep (se 1 (by rfl) ⟨9494792, by rfl⟩ : syracuseStep 12659723 = 18989585) B18989585
theorem B5336093 : Blo 1480560 5336093 := bstep (se 3 (by rfl) ⟨1000517, by rfl⟩ : syracuseStep 5336093 = 2001035) B2001035
theorem B4746269 : Blo 1480560 4746269 := bstep (se 3 (by rfl) ⟨889925, by rfl⟩ : syracuseStep 4746269 = 1779851) B1779851
theorem B2812961 : Blo 1480560 2812961 := bstep (se 2 (by rfl) ⟨1054860, by rfl⟩ : syracuseStep 2812961 = 2109721) B2109721
theorem B8432707 : Blo 1480560 8432707 := bstep (se 1 (by rfl) ⟨6324530, by rfl⟩ : syracuseStep 8432707 = 12649061) B12649061
theorem B2313289 : Blo 1480560 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B16870517 : Blo 1480560 16870517 := bstep (se 5 (by rfl) ⟨790805, by rfl⟩ : syracuseStep 16870517 = 1581611) B1581611
theorem B1666183 : Blo 1480560 1666183 := bstep (se 1 (by rfl) ⟨1249637, by rfl⟩ : syracuseStep 1666183 = 2499275) B2499275
theorem B2108587 : Blo 1480560 2108587 := bstep (se 1 (by rfl) ⟨1581440, by rfl⟩ : syracuseStep 2108587 = 3162881) B3162881
theorem B4115657 : Blo 1480560 4115657 := bstep (se 2 (by rfl) ⟨1543371, by rfl⟩ : syracuseStep 4115657 = 3086743) B3086743
theorem B1666363 : Blo 1480560 1666363 := bstep (se 1 (by rfl) ⟨1249772, by rfl⟩ : syracuseStep 1666363 = 2499545) B2499545
theorem B5000507 : Blo 1480560 5000507 := bstep (se 1 (by rfl) ⟨3750380, by rfl⟩ : syracuseStep 5000507 = 7500761) B7500761
theorem B14233117 : Blo 1480560 14233117 := bstep (se 3 (by rfl) ⟨2668709, by rfl⟩ : syracuseStep 14233117 = 5337419) B5337419
theorem B5623415 : Blo 1480560 5623415 := bstep (se 1 (by rfl) ⟨4217561, by rfl⟩ : syracuseStep 5623415 = 8435123) B8435123
theorem B7499465 : Blo 1480560 7499465 := bstep (se 2 (by rfl) ⟨2812299, by rfl⟩ : syracuseStep 7499465 = 5624599) B5624599
theorem B7704335 : Blo 1480560 7704335 := bstep (se 1 (by rfl) ⟨5778251, by rfl⟩ : syracuseStep 7704335 = 11556503) B11556503
theorem B1666831 : Blo 1480560 1666831 := bstep (se 1 (by rfl) ⟨1250123, by rfl⟩ : syracuseStep 1666831 = 2500247) B2500247
theorem B8548129 : Blo 1480560 8548129 := bstep (se 2 (by rfl) ⟨3205548, by rfl⟩ : syracuseStep 8548129 = 6411097) B6411097
theorem B5000993 : Blo 1480560 5000993 := bstep (se 2 (by rfl) ⟨1875372, by rfl⟩ : syracuseStep 5000993 = 3750745) B3750745
theorem B5066681 : Blo 1480560 5066681 := bstep (se 2 (by rfl) ⟨1900005, by rfl⟩ : syracuseStep 5066681 = 3800011) B3800011
theorem B68440099 : Blo 1480560 68440099 := bstep (se 1 (by rfl) ⟨51330074, by rfl⟩ : syracuseStep 68440099 = 102660149) B102660149
theorem B5001587 : Blo 1480560 5001587 := bstep (se 1 (by rfl) ⟨3751190, by rfl⟩ : syracuseStep 5001587 = 7502381) B7502381
theorem B5624387 : Blo 1480560 5624387 := bstep (se 1 (by rfl) ⟨4218290, by rfl⟩ : syracuseStep 5624387 = 8436581) B8436581
theorem B3748619 : Blo 1480560 3748619 := bstep (se 1 (by rfl) ⟨2811464, by rfl⟩ : syracuseStep 3748619 = 5622929) B5622929
theorem B8434691 : Blo 1480560 8434691 := bstep (se 1 (by rfl) ⟨6326018, by rfl⟩ : syracuseStep 8434691 = 12652037) B12652037
theorem B8008897 : Blo 1480560 8008897 := bstep (se 2 (by rfl) ⟨3003336, by rfl⟩ : syracuseStep 8008897 = 6006673) B6006673
theorem B1602875 : Blo 1480560 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B3331475 : Blo 1480560 3331475 := bstep (se 1 (by rfl) ⟨2498606, by rfl⟩ : syracuseStep 3331475 = 4997213) B4997213
theorem B3749267 : Blo 1480560 3749267 := bstep (se 1 (by rfl) ⟨2811950, by rfl⟩ : syracuseStep 3749267 = 5623901) B5623901
theorem B3331529 : Blo 1480560 3331529 := bstep (se 2 (by rfl) ⟨1249323, by rfl⟩ : syracuseStep 3331529 = 2498647) B2498647
theorem B7116407 : Blo 1480560 7116407 := bstep (se 1 (by rfl) ⟨5337305, by rfl⟩ : syracuseStep 7116407 = 10674611) B10674611
theorem B2406007 : Blo 1480560 2406007 := bstep (se 1 (by rfl) ⟨1804505, by rfl⟩ : syracuseStep 2406007 = 3609011) B3609011
theorem B3749561 : Blo 1480560 3749561 := bstep (se 2 (by rfl) ⟨1406085, by rfl⟩ : syracuseStep 3749561 = 2812171) B2812171
theorem B2373391 : Blo 1480560 2373391 := bstep (se 1 (by rfl) ⟨1780043, by rfl⟩ : syracuseStep 2373391 = 3560087) B3560087
theorem B1480583 : Blo 1480560 1480583 := bstep (se 1 (by rfl) ⟨1110437, by rfl⟩ : syracuseStep 1480583 = 2220875) B2220875
theorem B1480591 : Blo 1480560 1480591 := bstep (se 1 (by rfl) ⟨1110443, by rfl⟩ : syracuseStep 1480591 = 2220887) B2220887
theorem B1480635 : Blo 1480560 1480635 := bstep (se 1 (by rfl) ⟨1110476, by rfl⟩ : syracuseStep 1480635 = 2220953) B2220953
theorem B8009675 : Blo 1480560 8009675 := bstep (se 1 (by rfl) ⟨6007256, by rfl⟩ : syracuseStep 8009675 = 12014513) B12014513
theorem B1480711 : Blo 1480560 1480711 := bstep (se 1 (by rfl) ⟨1110533, by rfl⟩ : syracuseStep 1480711 = 2221067) B2221067
theorem B1480719 : Blo 1480560 1480719 := bstep (se 1 (by rfl) ⟨1110539, by rfl⟩ : syracuseStep 1480719 = 2221079) B2221079
theorem B1480763 : Blo 1480560 1480763 := bstep (se 1 (by rfl) ⟨1110572, by rfl⟩ : syracuseStep 1480763 = 2221145) B2221145
theorem B1480839 : Blo 1480560 1480839 := bstep (se 1 (by rfl) ⟨1110629, by rfl⟩ : syracuseStep 1480839 = 2221259) B2221259
theorem B3332231 : Blo 1480560 3332231 := bstep (se 1 (by rfl) ⟨2499173, by rfl⟩ : syracuseStep 3332231 = 4998347) B4998347
theorem B1480847 : Blo 1480560 1480847 := bstep (se 1 (by rfl) ⟨1110635, by rfl⟩ : syracuseStep 1480847 = 2221271) B2221271
theorem B1874107 : Blo 1480560 1874107 := bstep (se 1 (by rfl) ⟨1405580, by rfl⟩ : syracuseStep 1874107 = 2811161) B2811161
theorem B1480891 : Blo 1480560 1480891 := bstep (se 1 (by rfl) ⟨1110668, by rfl⟩ : syracuseStep 1480891 = 2221337) B2221337
theorem B5626057 : Blo 1480560 5626057 := bstep (se 2 (by rfl) ⟨2109771, by rfl⟩ : syracuseStep 5626057 = 4219543) B4219543
theorem B1480967 : Blo 1480560 1480967 := bstep (se 1 (by rfl) ⟨1110725, by rfl⟩ : syracuseStep 1480967 = 2221451) B2221451
theorem B1480975 : Blo 1480560 1480975 := bstep (se 1 (by rfl) ⟨1110731, by rfl⟩ : syracuseStep 1480975 = 2221463) B2221463
theorem B1481019 : Blo 1480560 1481019 := bstep (se 1 (by rfl) ⟨1110764, by rfl⟩ : syracuseStep 1481019 = 2221529) B2221529
theorem B3332411 : Blo 1480560 3332411 := bstep (se 1 (by rfl) ⟨2499308, by rfl⟩ : syracuseStep 3332411 = 4998617) B4998617
theorem B3750259 : Blo 1480560 3750259 := bstep (se 1 (by rfl) ⟨2812694, by rfl⟩ : syracuseStep 3750259 = 5625389) B5625389
theorem B1481095 : Blo 1480560 1481095 := bstep (se 1 (by rfl) ⟨1110821, by rfl⟩ : syracuseStep 1481095 = 2221643) B2221643
theorem B1481103 : Blo 1480560 1481103 := bstep (se 1 (by rfl) ⟨1110827, by rfl⟩ : syracuseStep 1481103 = 2221655) B2221655
theorem B3332537 : Blo 1480560 3332537 := bstep (se 2 (by rfl) ⟨1249701, by rfl⟩ : syracuseStep 3332537 = 2499403) B2499403
theorem B1481147 : Blo 1480560 1481147 := bstep (se 1 (by rfl) ⟨1110860, by rfl⟩ : syracuseStep 1481147 = 2221721) B2221721
theorem B3750401 : Blo 1480560 3750401 := bstep (se 2 (by rfl) ⟨1406400, by rfl⟩ : syracuseStep 3750401 = 2812801) B2812801
theorem B1481223 : Blo 1480560 1481223 := bstep (se 1 (by rfl) ⟨1110917, by rfl⟩ : syracuseStep 1481223 = 2221835) B2221835
theorem B4004363 : Blo 1480560 4004363 := bstep (se 1 (by rfl) ⟨3003272, by rfl⟩ : syracuseStep 4004363 = 6006545) B6006545
theorem B1481231 : Blo 1480560 1481231 := bstep (se 1 (by rfl) ⟨1110923, by rfl⟩ : syracuseStep 1481231 = 2221847) B2221847
theorem B11254301 : Blo 1480560 11254301 := bstep (se 3 (by rfl) ⟨2110181, by rfl⟩ : syracuseStep 11254301 = 4220363) B4220363
theorem B1481275 : Blo 1480560 1481275 := bstep (se 1 (by rfl) ⟨1110956, by rfl⟩ : syracuseStep 1481275 = 2221913) B2221913
theorem B16022117 : Blo 1480560 16022117 := bstep (se 4 (by rfl) ⟨1502073, by rfl⟩ : syracuseStep 16022117 = 3004147) B3004147
theorem B1481351 : Blo 1480560 1481351 := bstep (se 1 (by rfl) ⟨1111013, by rfl⟩ : syracuseStep 1481351 = 2222027) B2222027
theorem B1481359 : Blo 1480560 1481359 := bstep (se 1 (by rfl) ⟨1111019, by rfl⟩ : syracuseStep 1481359 = 2222039) B2222039
theorem B1874603 : Blo 1480560 1874603 := bstep (se 1 (by rfl) ⟨1405952, by rfl⟩ : syracuseStep 1874603 = 2811905) B2811905
theorem B1481403 : Blo 1480560 1481403 := bstep (se 1 (by rfl) ⟨1111052, by rfl⟩ : syracuseStep 1481403 = 2222105) B2222105
theorem B1481479 : Blo 1480560 1481479 := bstep (se 1 (by rfl) ⟨1111109, by rfl⟩ : syracuseStep 1481479 = 2222219) B2222219
theorem B29653775 : Blo 1480560 29653775 := bstep (se 1 (by rfl) ⟨22240331, by rfl⟩ : syracuseStep 29653775 = 44480663) B44480663
theorem B3332879 : Blo 1480560 3332879 := bstep (se 1 (by rfl) ⟨2499659, by rfl⟩ : syracuseStep 3332879 = 4999319) B4999319
theorem B1481487 : Blo 1480560 1481487 := bstep (se 1 (by rfl) ⟨1111115, by rfl⟩ : syracuseStep 1481487 = 2222231) B2222231
theorem B3332897 : Blo 1480560 3332897 := bstep (se 2 (by rfl) ⟨1249836, by rfl⟩ : syracuseStep 3332897 = 2499673) B2499673
theorem B1481531 : Blo 1480560 1481531 := bstep (se 1 (by rfl) ⟨1111148, by rfl⟩ : syracuseStep 1481531 = 2222297) B2222297
theorem B1481607 : Blo 1480560 1481607 := bstep (se 1 (by rfl) ⟨1111205, by rfl⟩ : syracuseStep 1481607 = 2222411) B2222411
theorem B1481615 : Blo 1480560 1481615 := bstep (se 1 (by rfl) ⟨1111211, by rfl⟩ : syracuseStep 1481615 = 2222423) B2222423
theorem B1481659 : Blo 1480560 1481659 := bstep (se 1 (by rfl) ⟨1111244, by rfl⟩ : syracuseStep 1481659 = 2222489) B2222489
theorem B3750857 : Blo 1480560 3750857 := bstep (se 2 (by rfl) ⟨1406571, by rfl⟩ : syracuseStep 3750857 = 2813143) B2813143
theorem B7117789 : Blo 1480560 7117789 := bstep (se 3 (by rfl) ⟨1334585, by rfl⟩ : syracuseStep 7117789 = 2669171) B2669171
theorem B1481735 : Blo 1480560 1481735 := bstep (se 1 (by rfl) ⟨1111301, by rfl⟩ : syracuseStep 1481735 = 2222603) B2222603
theorem B1481743 : Blo 1480560 1481743 := bstep (se 1 (by rfl) ⟨1111307, by rfl⟩ : syracuseStep 1481743 = 2222615) B2222615
theorem B1481787 : Blo 1480560 1481787 := bstep (se 1 (by rfl) ⟨1111340, by rfl⟩ : syracuseStep 1481787 = 2222681) B2222681
theorem B9616445 : Blo 1480560 9616445 := bstep (se 3 (by rfl) ⟨1803083, by rfl⟩ : syracuseStep 9616445 = 3606167) B3606167
theorem B27016253 : Blo 1480560 27016253 := bstep (se 3 (by rfl) ⟨5065547, by rfl⟩ : syracuseStep 27016253 = 10131095) B10131095
theorem B3333239 : Blo 1480560 3333239 := bstep (se 1 (by rfl) ⟨2499929, by rfl⟩ : syracuseStep 3333239 = 4999859) B4999859
theorem B1875079 : Blo 1480560 1875079 := bstep (se 1 (by rfl) ⟨1406309, by rfl⟩ : syracuseStep 1875079 = 2812619) B2812619
theorem B1481863 : Blo 1480560 1481863 := bstep (se 1 (by rfl) ⟨1111397, by rfl⟩ : syracuseStep 1481863 = 2222795) B2222795
theorem B1481871 : Blo 1480560 1481871 := bstep (se 1 (by rfl) ⟨1111403, by rfl⟩ : syracuseStep 1481871 = 2222807) B2222807
theorem B4005011 : Blo 1480560 4005011 := bstep (se 1 (by rfl) ⟨3003758, by rfl⟩ : syracuseStep 4005011 = 6007517) B6007517
theorem B1481915 : Blo 1480560 1481915 := bstep (se 1 (by rfl) ⟨1111436, by rfl⟩ : syracuseStep 1481915 = 2222873) B2222873
theorem B2849993 : Blo 1480560 2849993 := bstep (se 2 (by rfl) ⟨1068747, by rfl⟩ : syracuseStep 2849993 = 2137495) B2137495
theorem B17104117 : Blo 1480560 17104117 := bstep (se 5 (by rfl) ⟨801755, by rfl⟩ : syracuseStep 17104117 = 1603511) B1603511
theorem B1481991 : Blo 1480560 1481991 := bstep (se 1 (by rfl) ⟨1111493, by rfl⟩ : syracuseStep 1481991 = 2222987) B2222987
theorem B1481999 : Blo 1480560 1481999 := bstep (se 1 (by rfl) ⟨1111499, by rfl⟩ : syracuseStep 1481999 = 2222999) B2222999
theorem B3333419 : Blo 1480560 3333419 := bstep (se 1 (by rfl) ⟨2500064, by rfl⟩ : syracuseStep 3333419 = 5000129) B5000129
theorem B3751211 : Blo 1480560 3751211 := bstep (se 1 (by rfl) ⟨2813408, by rfl⟩ : syracuseStep 3751211 = 5626817) B5626817
theorem B2252089 : Blo 1480560 2252089 := bstep (se 2 (by rfl) ⟨844533, by rfl⟩ : syracuseStep 2252089 = 1689067) B1689067
theorem B1482043 : Blo 1480560 1482043 := bstep (se 1 (by rfl) ⟨1111532, by rfl⟩ : syracuseStep 1482043 = 2223065) B2223065
theorem B8437081 : Blo 1480560 8437081 := bstep (se 2 (by rfl) ⟨3163905, by rfl⟩ : syracuseStep 8437081 = 6327811) B6327811
theorem B4218313 : Blo 1480560 4218313 := bstep (se 2 (by rfl) ⟨1581867, by rfl⟩ : syracuseStep 4218313 = 3163735) B3163735
theorem B1875575 : Blo 1480560 1875575 := bstep (se 1 (by rfl) ⟨1406681, by rfl⟩ : syracuseStep 1875575 = 2813363) B2813363
theorem B3333779 : Blo 1480560 3333779 := bstep (se 1 (by rfl) ⟨2500334, by rfl⟩ : syracuseStep 3333779 = 5000669) B5000669
theorem B3333833 : Blo 1480560 3333833 := bstep (se 2 (by rfl) ⟨1250187, by rfl⟩ : syracuseStep 3333833 = 2500375) B2500375
theorem B1875727 : Blo 1480560 1875727 := bstep (se 1 (by rfl) ⟨1406795, by rfl⟩ : syracuseStep 1875727 = 2813591) B2813591
theorem B17342257 : Blo 1480560 17342257 := bstep (se 2 (by rfl) ⟨6503346, by rfl⟩ : syracuseStep 17342257 = 13006693) B13006693
theorem B12017497 : Blo 1480560 12017497 := bstep (se 2 (by rfl) ⟨4506561, by rfl⟩ : syracuseStep 12017497 = 9013123) B9013123
theorem B7495577 : Blo 1480560 7495577 := bstep (se 2 (by rfl) ⟨2810841, by rfl⟩ : syracuseStep 7495577 = 5621683) B5621683
theorem B32047001 : Blo 1480560 32047001 := bstep (se 2 (by rfl) ⟨12017625, by rfl⟩ : syracuseStep 32047001 = 24035251) B24035251
theorem B2670671 : Blo 1480560 2670671 := bstep (se 1 (by rfl) ⟨2003003, by rfl⟩ : syracuseStep 2670671 = 4006007) B4006007
theorem B3334391 : Blo 1480560 3334391 := bstep (se 1 (by rfl) ⟨2500793, by rfl⟩ : syracuseStep 3334391 = 5001587) B5001587
theorem B2498809 : Blo 1480560 2498809 := bstep (se 2 (by rfl) ⟨937053, by rfl⟩ : syracuseStep 2498809 = 1874107) B1874107
theorem B14237963 : Blo 1480560 14237963 := bstep (se 1 (by rfl) ⟨10678472, by rfl⟩ : syracuseStep 14237963 = 21356945) B21356945
theorem B11559217 : Blo 1480560 11559217 := bstep (se 2 (by rfl) ⟨4334706, by rfl⟩ : syracuseStep 11559217 = 8669413) B8669413
theorem B12337541 : Blo 1480560 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B2499079 : Blo 1480560 2499079 := bstep (se 1 (by rfl) ⟨1874309, by rfl⟩ : syracuseStep 2499079 = 3748619) B3748619
theorem B7496225 : Blo 1480560 7496225 := bstep (se 2 (by rfl) ⟨2811084, by rfl⟩ : syracuseStep 7496225 = 5622169) B5622169
theorem B2220905 : Blo 1480560 2220905 := bstep (se 2 (by rfl) ⟨832839, by rfl⟩ : syracuseStep 2220905 = 1665679) B1665679
theorem B2220983 : Blo 1480560 2220983 := bstep (se 1 (by rfl) ⟨1665737, by rfl⟩ : syracuseStep 2220983 = 3331475) B3331475
theorem B2499511 : Blo 1480560 2499511 := bstep (se 1 (by rfl) ⟨1874633, by rfl⟩ : syracuseStep 2499511 = 3749267) B3749267
theorem B2221019 : Blo 1480560 2221019 := bstep (se 1 (by rfl) ⟨1665764, by rfl⟩ : syracuseStep 2221019 = 3331529) B3331529
theorem B6325249 : Blo 1480560 6325249 := bstep (se 2 (by rfl) ⟨2371968, by rfl⟩ : syracuseStep 6325249 = 4743937) B4743937
theorem B4744271 : Blo 1480560 4744271 := bstep (se 1 (by rfl) ⟨3558203, by rfl⟩ : syracuseStep 4744271 = 7116407) B7116407
theorem B2499707 : Blo 1480560 2499707 := bstep (se 1 (by rfl) ⟨1874780, by rfl⟩ : syracuseStep 2499707 = 3749561) B3749561
theorem B4940957 : Blo 1480560 4940957 := bstep (se 3 (by rfl) ⟨926429, by rfl⟩ : syracuseStep 4940957 = 1852859) B1852859
theorem B2221487 : Blo 1480560 2221487 := bstep (se 1 (by rfl) ⟨1666115, by rfl⟩ : syracuseStep 2221487 = 3332231) B3332231
theorem B2221577 : Blo 1480560 2221577 := bstep (se 2 (by rfl) ⟨833091, by rfl⟩ : syracuseStep 2221577 = 1666183) B1666183
theorem B2500105 : Blo 1480560 2500105 := bstep (se 2 (by rfl) ⟨937539, by rfl⟩ : syracuseStep 2500105 = 1875079) B1875079
theorem B2221607 : Blo 1480560 2221607 := bstep (se 1 (by rfl) ⟨1666205, by rfl⟩ : syracuseStep 2221607 = 3332411) B3332411
theorem B2811449 : Blo 1480560 2811449 := bstep (se 2 (by rfl) ⟨1054293, by rfl⟩ : syracuseStep 2811449 = 2108587) B2108587
theorem B9012833 : Blo 1480560 9012833 := bstep (se 2 (by rfl) ⟨3379812, by rfl⟩ : syracuseStep 9012833 = 6759625) B6759625
theorem B6325883 : Blo 1480560 6325883 := bstep (se 1 (by rfl) ⟨4744412, by rfl⟩ : syracuseStep 6325883 = 9488825) B9488825
theorem B4998779 : Blo 1480560 4998779 := bstep (se 1 (by rfl) ⟨3749084, by rfl⟩ : syracuseStep 4998779 = 7498169) B7498169
theorem B2221691 : Blo 1480560 2221691 := bstep (se 1 (by rfl) ⟨1666268, by rfl⟩ : syracuseStep 2221691 = 3332537) B3332537
theorem B12011141 : Blo 1480560 12011141 := bstep (se 4 (by rfl) ⟨1126044, by rfl⟩ : syracuseStep 12011141 = 2252089) B2252089
theorem B2500267 : Blo 1480560 2500267 := bstep (se 1 (by rfl) ⟨1875200, by rfl⟩ : syracuseStep 2500267 = 3750401) B3750401
theorem B2221817 : Blo 1480560 2221817 := bstep (se 2 (by rfl) ⟨833181, by rfl⟩ : syracuseStep 2221817 = 1666363) B1666363
theorem B4998941 : Blo 1480560 4998941 := bstep (se 3 (by rfl) ⟨937301, by rfl⟩ : syracuseStep 4998941 = 1874603) B1874603
theorem B11249441 : Blo 1480560 11249441 := bstep (se 2 (by rfl) ⟨4218540, by rfl⟩ : syracuseStep 11249441 = 8437081) B8437081
theorem B19769183 : Blo 1480560 19769183 := bstep (se 1 (by rfl) ⟨14826887, by rfl⟩ : syracuseStep 19769183 = 29653775) B29653775
theorem B2221919 : Blo 1480560 2221919 := bstep (se 1 (by rfl) ⟨1666439, by rfl⟩ : syracuseStep 2221919 = 3332879) B3332879
theorem B2221931 : Blo 1480560 2221931 := bstep (se 1 (by rfl) ⟨1666448, by rfl⟩ : syracuseStep 2221931 = 3332897) B3332897
theorem B54044597 : Blo 1480560 54044597 := bstep (se 5 (by rfl) ⟨2533340, by rfl⟩ : syracuseStep 54044597 = 5066681) B5066681
theorem B2500571 : Blo 1480560 2500571 := bstep (se 1 (by rfl) ⟨1875428, by rfl⟩ : syracuseStep 2500571 = 3750857) B3750857
theorem B8439815 : Blo 1480560 8439815 := bstep (se 1 (by rfl) ⟨6329861, by rfl⟩ : syracuseStep 8439815 = 12659723) B12659723
theorem B3557395 : Blo 1480560 3557395 := bstep (se 1 (by rfl) ⟨2668046, by rfl⟩ : syracuseStep 3557395 = 5336093) B5336093
theorem B3164179 : Blo 1480560 3164179 := bstep (se 1 (by rfl) ⟨2373134, by rfl⟩ : syracuseStep 3164179 = 4746269) B4746269
theorem B2222159 : Blo 1480560 2222159 := bstep (se 1 (by rfl) ⟨1666619, by rfl⟩ : syracuseStep 2222159 = 3333239) B3333239
theorem B2222279 : Blo 1480560 2222279 := bstep (se 1 (by rfl) ⟨1666709, by rfl⟩ : syracuseStep 2222279 = 3333419) B3333419
theorem B2500807 : Blo 1480560 2500807 := bstep (se 1 (by rfl) ⟨1875605, by rfl⟩ : syracuseStep 2500807 = 3751211) B3751211
theorem B2222441 : Blo 1480560 2222441 := bstep (se 2 (by rfl) ⟨833415, by rfl⟩ : syracuseStep 2222441 = 1666831) B1666831
theorem B3164521 : Blo 1480560 3164521 := bstep (se 2 (by rfl) ⟨1186695, by rfl⟩ : syracuseStep 3164521 = 2373391) B2373391
theorem B2500969 : Blo 1480560 2500969 := bstep (se 2 (by rfl) ⟨937863, by rfl⟩ : syracuseStep 2500969 = 1875727) B1875727
theorem B11397505 : Blo 1480560 11397505 := bstep (se 2 (by rfl) ⟨4274064, by rfl⟩ : syracuseStep 11397505 = 8548129) B8548129
theorem B2222519 : Blo 1480560 2222519 := bstep (se 1 (by rfl) ⟨1666889, by rfl⟩ : syracuseStep 2222519 = 3333779) B3333779
theorem B4999643 : Blo 1480560 4999643 := bstep (se 1 (by rfl) ⟨3749732, by rfl⟩ : syracuseStep 4999643 = 7499465) B7499465
theorem B2222555 : Blo 1480560 2222555 := bstep (se 1 (by rfl) ⟨1666916, by rfl⟩ : syracuseStep 2222555 = 3333833) B3333833
theorem B16017965 : Blo 1480560 16017965 := bstep (se 3 (by rfl) ⟨3003368, by rfl⟩ : syracuseStep 16017965 = 6006737) B6006737
theorem B1780423 : Blo 1480560 1780423 := bstep (se 1 (by rfl) ⟨1335317, by rfl⟩ : syracuseStep 1780423 = 2670635) B2670635
theorem B91253465 : Blo 1480560 91253465 := bstep (se 2 (by rfl) ⟨34220049, by rfl⟩ : syracuseStep 91253465 = 68440099) B68440099
theorem B1665967 : Blo 1480560 1665967 := bstep (se 1 (by rfl) ⟨1249475, by rfl⟩ : syracuseStep 1665967 = 2498951) B2498951
theorem B2223023 : Blo 1480560 2223023 := bstep (se 1 (by rfl) ⟨1667267, by rfl⟩ : syracuseStep 2223023 = 3334535) B3334535
theorem B4746167 : Blo 1480560 4746167 := bstep (se 1 (by rfl) ⟨3559625, by rfl⟩ : syracuseStep 4746167 = 7119251) B7119251
theorem B5000345 : Blo 1480560 5000345 := bstep (se 2 (by rfl) ⟨1875129, by rfl⟩ : syracuseStep 5000345 = 3750259) B3750259
theorem B5623127 : Blo 1480560 5623127 := bstep (se 1 (by rfl) ⟨4217345, by rfl⟩ : syracuseStep 5623127 = 8434691) B8434691
theorem B1666399 : Blo 1480560 1666399 := bstep (se 1 (by rfl) ⟨1249799, by rfl⟩ : syracuseStep 1666399 = 2499599) B2499599
theorem B9006461 : Blo 1480560 9006461 := bstep (se 3 (by rfl) ⟨1688711, by rfl⟩ : syracuseStep 9006461 = 3377423) B3377423
theorem B2108855 : Blo 1480560 2108855 := bstep (se 1 (by rfl) ⟨1581641, by rfl⟩ : syracuseStep 2108855 = 3163283) B3163283
theorem B2813447 : Blo 1480560 2813447 := bstep (se 1 (by rfl) ⟨2110085, by rfl⟩ : syracuseStep 2813447 = 4220171) B4220171
theorem B7499303 : Blo 1480560 7499303 := bstep (se 1 (by rfl) ⟨5624477, by rfl⟩ : syracuseStep 7499303 = 11248955) B11248955
theorem B1666759 : Blo 1480560 1666759 := bstep (se 1 (by rfl) ⟨1250069, by rfl⟩ : syracuseStep 1666759 = 2500139) B2500139
theorem B19246967 : Blo 1480560 19246967 := bstep (se 1 (by rfl) ⟨14435225, by rfl⟩ : syracuseStep 19246967 = 28870451) B28870451
theorem B19509179 : Blo 1480560 19509179 := bstep (se 1 (by rfl) ⟨14631884, by rfl⟩ : syracuseStep 19509179 = 29263769) B29263769
theorem B9490385 : Blo 1480560 9490385 := bstep (se 2 (by rfl) ⟨3558894, by rfl⟩ : syracuseStep 9490385 = 7117789) B7117789
theorem B10678301 : Blo 1480560 10678301 := bstep (se 3 (by rfl) ⟨2002181, by rfl⟩ : syracuseStep 10678301 = 4004363) B4004363
theorem B11243609 : Blo 1480560 11243609 := bstep (se 2 (by rfl) ⟨4216353, by rfl⟩ : syracuseStep 11243609 = 8432707) B8432707
theorem B10678529 : Blo 1480560 10678529 := bstep (se 2 (by rfl) ⟨4004448, by rfl⟩ : syracuseStep 10678529 = 8008897) B8008897
theorem B5001533 : Blo 1480560 5001533 := bstep (se 3 (by rfl) ⟨937787, by rfl⟩ : syracuseStep 5001533 = 1875575) B1875575
theorem B3748315 : Blo 1480560 3748315 := bstep (se 1 (by rfl) ⟨2811236, by rfl⟩ : syracuseStep 3748315 = 5622473) B5622473
theorem B5624417 : Blo 1480560 5624417 := bstep (se 2 (by rfl) ⟨2109156, by rfl⟩ : syracuseStep 5624417 = 4218313) B4218313
theorem B18985589 : Blo 1480560 18985589 := bstep (se 5 (by rfl) ⟨889949, by rfl⟩ : syracuseStep 18985589 = 1779899) B1779899
theorem B4002493 : Blo 1480560 4002493 := bstep (se 3 (by rfl) ⟨750467, by rfl⟩ : syracuseStep 4002493 = 1500935) B1500935
theorem B18977489 : Blo 1480560 18977489 := bstep (se 2 (by rfl) ⟨7116558, by rfl⟩ : syracuseStep 18977489 = 14233117) B14233117
theorem B6410963 : Blo 1480560 6410963 := bstep (se 1 (by rfl) ⟨4808222, by rfl⟩ : syracuseStep 6410963 = 9616445) B9616445
theorem B18010835 : Blo 1480560 18010835 := bstep (se 1 (by rfl) ⟨13508126, by rfl⟩ : syracuseStep 18010835 = 27016253) B27016253
theorem B3208009 : Blo 1480560 3208009 := bstep (se 2 (by rfl) ⟨1203003, by rfl⟩ : syracuseStep 3208009 = 2406007) B2406007
theorem B23123009 : Blo 1480560 23123009 := bstep (se 2 (by rfl) ⟨8671128, by rfl⟩ : syracuseStep 23123009 = 17342257) B17342257
theorem B3748943 : Blo 1480560 3748943 := bstep (se 1 (by rfl) ⟨2811707, by rfl⟩ : syracuseStep 3748943 = 5623415) B5623415
theorem B9008549 : Blo 1480560 9008549 := bstep (se 4 (by rfl) ⟨844551, by rfl⟩ : syracuseStep 9008549 = 1689103) B1689103
theorem B3331547 : Blo 1480560 3331547 := bstep (se 1 (by rfl) ⟨2498660, by rfl⟩ : syracuseStep 3331547 = 4997321) B4997321
theorem B11245067 : Blo 1480560 11245067 := bstep (se 1 (by rfl) ⟨8433800, by rfl⟩ : syracuseStep 11245067 = 16867601) B16867601
theorem B7501409 : Blo 1480560 7501409 := bstep (se 2 (by rfl) ⟨2813028, by rfl⟩ : syracuseStep 7501409 = 5626057) B5626057
theorem B3749591 : Blo 1480560 3749591 := bstep (se 1 (by rfl) ⟨2812193, by rfl⟩ : syracuseStep 3749591 = 5624387) B5624387
theorem B2668393 : Blo 1480560 2668393 := bstep (se 2 (by rfl) ⟨1000647, by rfl⟩ : syracuseStep 2668393 = 2001295) B2001295
theorem B10975085 : Blo 1480560 10975085 := bstep (se 3 (by rfl) ⟨2057828, by rfl⟩ : syracuseStep 10975085 = 4115657) B4115657
theorem B1480571 : Blo 1480560 1480571 := bstep (se 1 (by rfl) ⟨1110428, by rfl⟩ : syracuseStep 1480571 = 2220857) B2220857
theorem B1480623 : Blo 1480560 1480623 := bstep (se 1 (by rfl) ⟨1110467, by rfl⟩ : syracuseStep 1480623 = 2220935) B2220935
theorem B3332015 : Blo 1480560 3332015 := bstep (se 1 (by rfl) ⟨2499011, by rfl⟩ : syracuseStep 3332015 = 4998023) B4998023
theorem B1480647 : Blo 1480560 1480647 := bstep (se 1 (by rfl) ⟨1110485, by rfl⟩ : syracuseStep 1480647 = 2220971) B2220971
theorem B1480667 : Blo 1480560 1480667 := bstep (se 1 (by rfl) ⟨1110500, by rfl⟩ : syracuseStep 1480667 = 2221001) B2221001
theorem B5625875 : Blo 1480560 5625875 := bstep (se 1 (by rfl) ⟨4219406, by rfl⟩ : syracuseStep 5625875 = 8438813) B8438813
theorem B1480743 : Blo 1480560 1480743 := bstep (se 1 (by rfl) ⟨1110557, by rfl⟩ : syracuseStep 1480743 = 2221115) B2221115
theorem B1480783 : Blo 1480560 1480783 := bstep (se 1 (by rfl) ⟨1110587, by rfl⟩ : syracuseStep 1480783 = 2221175) B2221175
theorem B1480799 : Blo 1480560 1480799 := bstep (se 1 (by rfl) ⟨1110599, by rfl⟩ : syracuseStep 1480799 = 2221199) B2221199
theorem B1480827 : Blo 1480560 1480827 := bstep (se 1 (by rfl) ⟨1110620, by rfl⟩ : syracuseStep 1480827 = 2221241) B2221241
theorem B4274333 : Blo 1480560 4274333 := bstep (se 3 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 4274333 = 1602875) B1602875
theorem B3332267 : Blo 1480560 3332267 := bstep (se 1 (by rfl) ⟨2499200, by rfl⟩ : syracuseStep 3332267 = 4998401) B4998401
theorem B1480879 : Blo 1480560 1480879 := bstep (se 1 (by rfl) ⟨1110659, by rfl⟩ : syracuseStep 1480879 = 2221319) B2221319
theorem B1480903 : Blo 1480560 1480903 := bstep (se 1 (by rfl) ⟨1110677, by rfl⟩ : syracuseStep 1480903 = 2221355) B2221355
theorem B1480923 : Blo 1480560 1480923 := bstep (se 1 (by rfl) ⟨1110692, by rfl⟩ : syracuseStep 1480923 = 2221385) B2221385
theorem B1480999 : Blo 1480560 1480999 := bstep (se 1 (by rfl) ⟨1110749, by rfl⟩ : syracuseStep 1480999 = 2221499) B2221499
theorem B1481039 : Blo 1480560 1481039 := bstep (se 1 (by rfl) ⟨1110779, by rfl⟩ : syracuseStep 1481039 = 2221559) B2221559
theorem B1481055 : Blo 1480560 1481055 := bstep (se 1 (by rfl) ⟨1110791, by rfl⟩ : syracuseStep 1481055 = 2221583) B2221583
theorem B1481083 : Blo 1480560 1481083 := bstep (se 1 (by rfl) ⟨1110812, by rfl⟩ : syracuseStep 1481083 = 2221625) B2221625
theorem B1481135 : Blo 1480560 1481135 := bstep (se 1 (by rfl) ⟨1110851, by rfl⟩ : syracuseStep 1481135 = 2221703) B2221703
theorem B1481159 : Blo 1480560 1481159 := bstep (se 1 (by rfl) ⟨1110869, by rfl⟩ : syracuseStep 1481159 = 2221739) B2221739
theorem B1481179 : Blo 1480560 1481179 := bstep (se 1 (by rfl) ⟨1110884, by rfl⟩ : syracuseStep 1481179 = 2221769) B2221769
theorem B5626331 : Blo 1480560 5626331 := bstep (se 1 (by rfl) ⟨4219748, by rfl⟩ : syracuseStep 5626331 = 8439497) B8439497
theorem B1481255 : Blo 1480560 1481255 := bstep (se 1 (by rfl) ⟨1110941, by rfl⟩ : syracuseStep 1481255 = 2221883) B2221883
theorem B1481295 : Blo 1480560 1481295 := bstep (se 1 (by rfl) ⟨1110971, by rfl⟩ : syracuseStep 1481295 = 2221943) B2221943
theorem B1481311 : Blo 1480560 1481311 := bstep (se 1 (by rfl) ⟨1110983, by rfl⟩ : syracuseStep 1481311 = 2221967) B2221967
theorem B1481339 : Blo 1480560 1481339 := bstep (se 1 (by rfl) ⟨1111004, by rfl⟩ : syracuseStep 1481339 = 2222009) B2222009
theorem B5339783 : Blo 1480560 5339783 := bstep (se 1 (by rfl) ⟨4004837, by rfl⟩ : syracuseStep 5339783 = 8009675) B8009675
theorem B1481391 : Blo 1480560 1481391 := bstep (se 1 (by rfl) ⟨1111043, by rfl⟩ : syracuseStep 1481391 = 2222087) B2222087
theorem B3332807 : Blo 1480560 3332807 := bstep (se 1 (by rfl) ⟨2499605, by rfl⟩ : syracuseStep 3332807 = 4999211) B4999211
theorem B1481415 : Blo 1480560 1481415 := bstep (se 1 (by rfl) ⟨1111061, by rfl⟩ : syracuseStep 1481415 = 2222123) B2222123
theorem B1481435 : Blo 1480560 1481435 := bstep (se 1 (by rfl) ⟨1111076, by rfl⟩ : syracuseStep 1481435 = 2222153) B2222153
theorem B13507357 : Blo 1480560 13507357 := bstep (se 3 (by rfl) ⟨2532629, by rfl⟩ : syracuseStep 13507357 = 5065259) B5065259
theorem B1481511 : Blo 1480560 1481511 := bstep (se 1 (by rfl) ⟨1111133, by rfl⟩ : syracuseStep 1481511 = 2222267) B2222267
theorem B1481551 : Blo 1480560 1481551 := bstep (se 1 (by rfl) ⟨1111163, by rfl⟩ : syracuseStep 1481551 = 2222327) B2222327
theorem B1481567 : Blo 1480560 1481567 := bstep (se 1 (by rfl) ⟨1111175, by rfl⟩ : syracuseStep 1481567 = 2222351) B2222351
theorem B1481595 : Blo 1480560 1481595 := bstep (se 1 (by rfl) ⟨1111196, by rfl⟩ : syracuseStep 1481595 = 2222393) B2222393
theorem B1481647 : Blo 1480560 1481647 := bstep (se 1 (by rfl) ⟨1111235, by rfl⟩ : syracuseStep 1481647 = 2222471) B2222471
theorem B1481671 : Blo 1480560 1481671 := bstep (se 1 (by rfl) ⟨1111253, by rfl⟩ : syracuseStep 1481671 = 2222507) B2222507
theorem B1481691 : Blo 1480560 1481691 := bstep (se 1 (by rfl) ⟨1111268, by rfl⟩ : syracuseStep 1481691 = 2222537) B2222537
theorem B22805489 : Blo 1480560 22805489 := bstep (se 2 (by rfl) ⟨8552058, by rfl⟩ : syracuseStep 22805489 = 17104117) B17104117
theorem B7502867 : Blo 1480560 7502867 := bstep (se 1 (by rfl) ⟨5627150, by rfl⟩ : syracuseStep 7502867 = 11254301) B11254301
theorem B1874983 : Blo 1480560 1874983 := bstep (se 1 (by rfl) ⟨1406237, by rfl⟩ : syracuseStep 1874983 = 2812475) B2812475
theorem B1481767 : Blo 1480560 1481767 := bstep (se 1 (by rfl) ⟨1111325, by rfl⟩ : syracuseStep 1481767 = 2222651) B2222651
theorem B10681411 : Blo 1480560 10681411 := bstep (se 1 (by rfl) ⟨8011058, by rfl⟩ : syracuseStep 10681411 = 16022117) B16022117
theorem B1481807 : Blo 1480560 1481807 := bstep (se 1 (by rfl) ⟨1111355, by rfl⟩ : syracuseStep 1481807 = 2222711) B2222711
theorem B1481823 : Blo 1480560 1481823 := bstep (se 1 (by rfl) ⟨1111367, by rfl⟩ : syracuseStep 1481823 = 2222735) B2222735
theorem B1481851 : Blo 1480560 1481851 := bstep (se 1 (by rfl) ⟨1111388, by rfl⟩ : syracuseStep 1481851 = 2222777) B2222777
theorem B1481903 : Blo 1480560 1481903 := bstep (se 1 (by rfl) ⟨1111427, by rfl⟩ : syracuseStep 1481903 = 2222855) B2222855
theorem B1481927 : Blo 1480560 1481927 := bstep (se 1 (by rfl) ⟨1111445, by rfl⟩ : syracuseStep 1481927 = 2222891) B2222891
theorem B1481947 : Blo 1480560 1481947 := bstep (se 1 (by rfl) ⟨1111460, by rfl⟩ : syracuseStep 1481947 = 2222921) B2222921
theorem B15834359 : Blo 1480560 15834359 := bstep (se 1 (by rfl) ⟨11875769, by rfl⟩ : syracuseStep 15834359 = 23751539) B23751539
theorem B1482023 : Blo 1480560 1482023 := bstep (se 1 (by rfl) ⟨1111517, by rfl⟩ : syracuseStep 1482023 = 2223035) B2223035
theorem B1875307 : Blo 1480560 1875307 := bstep (se 1 (by rfl) ⟨1406480, by rfl⟩ : syracuseStep 1875307 = 2812961) B2812961
theorem B11247011 : Blo 1480560 11247011 := bstep (se 1 (by rfl) ⟨8435258, by rfl⟩ : syracuseStep 11247011 = 16870517) B16870517
theorem B2670007 : Blo 1480560 2670007 := bstep (se 1 (by rfl) ⟨2002505, by rfl⟩ : syracuseStep 2670007 = 4005011) B4005011
theorem B1899995 : Blo 1480560 1899995 := bstep (se 1 (by rfl) ⟨1424996, by rfl⟩ : syracuseStep 1899995 = 2849993) B2849993
theorem B3333671 : Blo 1480560 3333671 := bstep (se 1 (by rfl) ⟨2500253, by rfl⟩ : syracuseStep 3333671 = 5000507) B5000507
theorem B18013985 : Blo 1480560 18013985 := bstep (se 2 (by rfl) ⟨6755244, by rfl⟩ : syracuseStep 18013985 = 13510489) B13510489
theorem B16023329 : Blo 1480560 16023329 := bstep (se 2 (by rfl) ⟨6008748, by rfl⟩ : syracuseStep 16023329 = 12017497) B12017497
theorem B5136223 : Blo 1480560 5136223 := bstep (se 1 (by rfl) ⟨3852167, by rfl⟩ : syracuseStep 5136223 = 7704335) B7704335
theorem B3333995 : Blo 1480560 3333995 := bstep (se 1 (by rfl) ⟨2500496, by rfl⟩ : syracuseStep 3333995 = 5000993) B5000993
theorem B3334049 : Blo 1480560 3334049 := bstep (se 2 (by rfl) ⟨1250268, by rfl⟩ : syracuseStep 3334049 = 2500537) B2500537
theorem B4997051 : Blo 1480560 4997051 := bstep (se 1 (by rfl) ⟨3747788, by rfl⟩ : syracuseStep 4997051 = 7495577) B7495577
theorem B21364667 : Blo 1480560 21364667 := bstep (se 1 (by rfl) ⟨16023500, by rfl⟩ : syracuseStep 21364667 = 32047001) B32047001
theorem B7118867 : Blo 1480560 7118867 := bstep (se 1 (by rfl) ⟨5339150, by rfl⟩ : syracuseStep 7118867 = 10678301) B10678301
theorem B4743193 : Blo 1480560 4743193 := bstep (se 2 (by rfl) ⟨1778697, by rfl⟩ : syracuseStep 4743193 = 3557395) B3557395
theorem B4218905 : Blo 1480560 4218905 := bstep (se 2 (by rfl) ⟨1582089, by rfl⟩ : syracuseStep 4218905 = 3164179) B3164179
theorem B7495739 : Blo 1480560 7495739 := bstep (se 1 (by rfl) ⟨5621804, by rfl⟩ : syracuseStep 7495739 = 11243609) B11243609
theorem B7119019 : Blo 1480560 7119019 := bstep (se 1 (by rfl) ⟨5339264, by rfl⟩ : syracuseStep 7119019 = 10678529) B10678529
theorem B61661357 : Blo 1480560 61661357 := bstep (se 3 (by rfl) ⟨11561504, by rfl⟩ : syracuseStep 61661357 = 23123009) B23123009
theorem B3334355 : Blo 1480560 3334355 := bstep (se 1 (by rfl) ⟨2500766, by rfl⟩ : syracuseStep 3334355 = 5001533) B5001533
theorem B8225027 : Blo 1480560 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B3334409 : Blo 1480560 3334409 := bstep (se 2 (by rfl) ⟨1250403, by rfl⟩ : syracuseStep 3334409 = 2500807) B2500807
theorem B4997483 : Blo 1480560 4997483 := bstep (se 1 (by rfl) ⟨3748112, by rfl⟩ : syracuseStep 4997483 = 7496225) B7496225
theorem B12657059 : Blo 1480560 12657059 := bstep (se 1 (by rfl) ⟨9492794, by rfl⟩ : syracuseStep 12657059 = 18985589) B18985589
theorem B4219361 : Blo 1480560 4219361 := bstep (se 2 (by rfl) ⟨1582260, by rfl⟩ : syracuseStep 4219361 = 3164521) B3164521
theorem B3334625 : Blo 1480560 3334625 := bstep (se 2 (by rfl) ⟨1250484, by rfl⟩ : syracuseStep 3334625 = 2500969) B2500969
theorem B15196673 : Blo 1480560 15196673 := bstep (se 2 (by rfl) ⟨5698752, by rfl⟩ : syracuseStep 15196673 = 11397505) B11397505
theorem B4997753 : Blo 1480560 4997753 := bstep (se 2 (by rfl) ⟨1874157, by rfl⟩ : syracuseStep 4997753 = 3748315) B3748315
theorem B3162847 : Blo 1480560 3162847 := bstep (se 1 (by rfl) ⟨2372135, by rfl⟩ : syracuseStep 3162847 = 4744271) B4744271
theorem B2499295 : Blo 1480560 2499295 := bstep (se 1 (by rfl) ⟨1874471, by rfl⟩ : syracuseStep 2499295 = 3748943) B3748943
theorem B6005699 : Blo 1480560 6005699 := bstep (se 1 (by rfl) ⟨4504274, by rfl⟩ : syracuseStep 6005699 = 9008549) B9008549
theorem B2221031 : Blo 1480560 2221031 := bstep (se 1 (by rfl) ⟨1665773, by rfl⟩ : syracuseStep 2221031 = 3331547) B3331547
theorem B7496711 : Blo 1480560 7496711 := bstep (se 1 (by rfl) ⟨5622533, by rfl⟩ : syracuseStep 7496711 = 11245067) B11245067
theorem B9495589 : Blo 1480560 9495589 := bstep (se 4 (by rfl) ⟨890211, by rfl⟩ : syracuseStep 9495589 = 1780423) B1780423
theorem B4277345 : Blo 1480560 4277345 := bstep (se 2 (by rfl) ⟨1604004, by rfl⟩ : syracuseStep 4277345 = 3208009) B3208009
theorem B2499727 : Blo 1480560 2499727 := bstep (se 1 (by rfl) ⟨1874795, by rfl⟩ : syracuseStep 2499727 = 3749591) B3749591
theorem B2221289 : Blo 1480560 2221289 := bstep (se 2 (by rfl) ⟨832983, by rfl⟩ : syracuseStep 2221289 = 1665967) B1665967
theorem B7316723 : Blo 1480560 7316723 := bstep (se 1 (by rfl) ⟨5487542, by rfl⟩ : syracuseStep 7316723 = 10975085) B10975085
theorem B2221343 : Blo 1480560 2221343 := bstep (se 1 (by rfl) ⟨1666007, by rfl⟩ : syracuseStep 2221343 = 3332015) B3332015
theorem B36029731 : Blo 1480560 36029731 := bstep (se 1 (by rfl) ⟨27022298, by rfl⟩ : syracuseStep 36029731 = 54044597) B54044597
theorem B2499977 : Blo 1480560 2499977 := bstep (se 2 (by rfl) ⟨937491, by rfl⟩ : syracuseStep 2499977 = 1874983) B1874983
theorem B2221511 : Blo 1480560 2221511 := bstep (se 1 (by rfl) ⟨1666133, by rfl⟩ : syracuseStep 2221511 = 3332267) B3332267
theorem B7497197 : Blo 1480560 7497197 := bstep (se 3 (by rfl) ⟨1405724, by rfl⟩ : syracuseStep 7497197 = 2811449) B2811449
theorem B14239421 : Blo 1480560 14239421 := bstep (se 3 (by rfl) ⟨2669891, by rfl⟩ : syracuseStep 14239421 = 5339783) B5339783
theorem B2221865 : Blo 1480560 2221865 := bstep (se 2 (by rfl) ⟨833199, by rfl⟩ : syracuseStep 2221865 = 1666399) B1666399
theorem B2221871 : Blo 1480560 2221871 := bstep (se 1 (by rfl) ⟨1666403, by rfl⟩ : syracuseStep 2221871 = 3332807) B3332807
theorem B2500409 : Blo 1480560 2500409 := bstep (se 2 (by rfl) ⟨937653, by rfl⟩ : syracuseStep 2500409 = 1875307) B1875307
theorem B60835643 : Blo 1480560 60835643 := bstep (se 1 (by rfl) ⟨45626732, by rfl⟩ : syracuseStep 60835643 = 91253465) B91253465
theorem B3164111 : Blo 1480560 3164111 := bstep (se 1 (by rfl) ⟨2373083, by rfl⟩ : syracuseStep 3164111 = 4746167) B4746167
theorem B2222345 : Blo 1480560 2222345 := bstep (se 2 (by rfl) ⟨833379, by rfl⟩ : syracuseStep 2222345 = 1666759) B1666759
theorem B7498007 : Blo 1480560 7498007 := bstep (se 1 (by rfl) ⟨5623505, by rfl⟩ : syracuseStep 7498007 = 11247011) B11247011
theorem B4999535 : Blo 1480560 4999535 := bstep (se 1 (by rfl) ⟨3749651, by rfl⟩ : syracuseStep 4999535 = 7499303) B7499303
theorem B2222447 : Blo 1480560 2222447 := bstep (se 1 (by rfl) ⟨1666835, by rfl⟩ : syracuseStep 2222447 = 3333671) B3333671
theorem B3557857 : Blo 1480560 3557857 := bstep (se 2 (by rfl) ⟨1334196, by rfl⟩ : syracuseStep 3557857 = 2668393) B2668393
theorem B2222663 : Blo 1480560 2222663 := bstep (se 1 (by rfl) ⟨1666997, by rfl⟩ : syracuseStep 2222663 = 3333995) B3333995
theorem B12831311 : Blo 1480560 12831311 := bstep (se 1 (by rfl) ⟨9623483, by rfl⟩ : syracuseStep 12831311 = 19246967) B19246967
theorem B2222699 : Blo 1480560 2222699 := bstep (se 1 (by rfl) ⟨1667024, by rfl⟩ : syracuseStep 2222699 = 3334049) B3334049
theorem B6326923 : Blo 1480560 6326923 := bstep (se 1 (by rfl) ⟨4745192, by rfl⟩ : syracuseStep 6326923 = 9490385) B9490385
theorem B2222927 : Blo 1480560 2222927 := bstep (se 1 (by rfl) ⟨1667195, by rfl⟩ : syracuseStep 2222927 = 3334391) B3334391
theorem B7121789 : Blo 1480560 7121789 := bstep (se 3 (by rfl) ⟨1335335, by rfl⟩ : syracuseStep 7121789 = 2670671) B2670671
theorem B15412289 : Blo 1480560 15412289 := bstep (se 2 (by rfl) ⟨5779608, by rfl⟩ : syracuseStep 15412289 = 11559217) B11559217
theorem B13175885 : Blo 1480560 13175885 := bstep (se 3 (by rfl) ⟨2470478, by rfl⟩ : syracuseStep 13175885 = 4940957) B4940957
theorem B12651659 : Blo 1480560 12651659 := bstep (se 1 (by rfl) ⟨9488744, by rfl⟩ : syracuseStep 12651659 = 18977489) B18977489
theorem B1666471 : Blo 1480560 1666471 := bstep (se 1 (by rfl) ⟨1249853, by rfl⟩ : syracuseStep 1666471 = 2499707) B2499707
theorem B5336657 : Blo 1480560 5336657 := bstep (se 2 (by rfl) ⟨2001246, by rfl⟩ : syracuseStep 5336657 = 4002493) B4002493
theorem B18009809 : Blo 1480560 18009809 := bstep (se 2 (by rfl) ⟨6753678, by rfl⟩ : syracuseStep 18009809 = 13507357) B13507357
theorem B5000939 : Blo 1480560 5000939 := bstep (se 1 (by rfl) ⟨3750704, by rfl⟩ : syracuseStep 5000939 = 7501409) B7501409
theorem B6008555 : Blo 1480560 6008555 := bstep (se 1 (by rfl) ⟨4506416, by rfl⟩ : syracuseStep 6008555 = 9012833) B9012833
theorem B8007427 : Blo 1480560 8007427 := bstep (se 1 (by rfl) ⟨6005570, by rfl⟩ : syracuseStep 8007427 = 12011141) B12011141
theorem B5623613 : Blo 1480560 5623613 := bstep (se 3 (by rfl) ⟨1054427, by rfl⟩ : syracuseStep 5623613 = 2108855) B2108855
theorem B7499627 : Blo 1480560 7499627 := bstep (se 1 (by rfl) ⟨5624720, by rfl⟩ : syracuseStep 7499627 = 11249441) B11249441
theorem B5066653 : Blo 1480560 5066653 := bstep (se 3 (by rfl) ⟨949997, by rfl⟩ : syracuseStep 5066653 = 1899995) B1899995
theorem B1667047 : Blo 1480560 1667047 := bstep (se 1 (by rfl) ⟨1250285, by rfl⟩ : syracuseStep 1667047 = 2500571) B2500571
theorem B8433665 : Blo 1480560 8433665 := bstep (se 2 (by rfl) ⟨3162624, by rfl⟩ : syracuseStep 8433665 = 6325249) B6325249
theorem B14241881 : Blo 1480560 14241881 := bstep (se 2 (by rfl) ⟨5340705, by rfl⟩ : syracuseStep 14241881 = 10681411) B10681411
theorem B10678643 : Blo 1480560 10678643 := bstep (se 1 (by rfl) ⟨8008982, by rfl⟩ : syracuseStep 10678643 = 16017965) B16017965
theorem B3560009 : Blo 1480560 3560009 := bstep (se 2 (by rfl) ⟨1335003, by rfl⟩ : syracuseStep 3560009 = 2670007) B2670007
theorem B5001911 : Blo 1480560 5001911 := bstep (se 1 (by rfl) ⟨3751433, by rfl⟩ : syracuseStep 5001911 = 7502867) B7502867
theorem B10556239 : Blo 1480560 10556239 := bstep (se 1 (by rfl) ⟨7917179, by rfl⟩ : syracuseStep 10556239 = 15834359) B15834359
theorem B3748751 : Blo 1480560 3748751 := bstep (se 1 (by rfl) ⟨2811563, by rfl⟩ : syracuseStep 3748751 = 5623127) B5623127
theorem B52024477 : Blo 1480560 52024477 := bstep (se 3 (by rfl) ⟨9754589, by rfl⟩ : syracuseStep 52024477 = 19509179) B19509179
theorem B3331367 : Blo 1480560 3331367 := bstep (se 1 (by rfl) ⟨2498525, by rfl⟩ : syracuseStep 3331367 = 4997051) B4997051
theorem B14243111 : Blo 1480560 14243111 := bstep (se 1 (by rfl) ⟨10682333, by rfl⟩ : syracuseStep 14243111 = 21364667) B21364667
theorem B9491975 : Blo 1480560 9491975 := bstep (se 1 (by rfl) ⟨7118981, by rfl⟩ : syracuseStep 9491975 = 14237963) B14237963
theorem B3331745 : Blo 1480560 3331745 := bstep (se 2 (by rfl) ⟨1249404, by rfl⟩ : syracuseStep 3331745 = 2498809) B2498809
theorem B3749611 : Blo 1480560 3749611 := bstep (se 1 (by rfl) ⟨2812208, by rfl⟩ : syracuseStep 3749611 = 5624417) B5624417
theorem B4273975 : Blo 1480560 4273975 := bstep (se 1 (by rfl) ⟨3205481, by rfl⟩ : syracuseStep 4273975 = 6410963) B6410963
theorem B12007223 : Blo 1480560 12007223 := bstep (se 1 (by rfl) ⟨9005417, by rfl⟩ : syracuseStep 12007223 = 18010835) B18010835
theorem B1480603 : Blo 1480560 1480603 := bstep (se 1 (by rfl) ⟨1110452, by rfl⟩ : syracuseStep 1480603 = 2220905) B2220905
theorem B1480655 : Blo 1480560 1480655 := bstep (se 1 (by rfl) ⟨1110491, by rfl⟩ : syracuseStep 1480655 = 2220983) B2220983
theorem B1480679 : Blo 1480560 1480679 := bstep (se 1 (by rfl) ⟨1110509, by rfl⟩ : syracuseStep 1480679 = 2221019) B2221019
theorem B3332105 : Blo 1480560 3332105 := bstep (se 2 (by rfl) ⟨1249539, by rfl⟩ : syracuseStep 3332105 = 2499079) B2499079
theorem B1480991 : Blo 1480560 1480991 := bstep (se 1 (by rfl) ⟨1110743, by rfl⟩ : syracuseStep 1480991 = 2221487) B2221487
theorem B1481051 : Blo 1480560 1481051 := bstep (se 1 (by rfl) ⟨1110788, by rfl⟩ : syracuseStep 1481051 = 2221577) B2221577
theorem B1481071 : Blo 1480560 1481071 := bstep (se 1 (by rfl) ⟨1110803, by rfl⟩ : syracuseStep 1481071 = 2221607) B2221607
theorem B4217255 : Blo 1480560 4217255 := bstep (se 1 (by rfl) ⟨3162941, by rfl⟩ : syracuseStep 4217255 = 6325883) B6325883
theorem B3332519 : Blo 1480560 3332519 := bstep (se 1 (by rfl) ⟨2499389, by rfl⟩ : syracuseStep 3332519 = 4998779) B4998779
theorem B1481127 : Blo 1480560 1481127 := bstep (se 1 (by rfl) ⟨1110845, by rfl⟩ : syracuseStep 1481127 = 2221691) B2221691
theorem B1481211 : Blo 1480560 1481211 := bstep (se 1 (by rfl) ⟨1110908, by rfl⟩ : syracuseStep 1481211 = 2221817) B2221817
theorem B3332627 : Blo 1480560 3332627 := bstep (se 1 (by rfl) ⟨2499470, by rfl⟩ : syracuseStep 3332627 = 4998941) B4998941
theorem B13179455 : Blo 1480560 13179455 := bstep (se 1 (by rfl) ⟨9884591, by rfl⟩ : syracuseStep 13179455 = 19769183) B19769183
theorem B1481279 : Blo 1480560 1481279 := bstep (se 1 (by rfl) ⟨1110959, by rfl⟩ : syracuseStep 1481279 = 2221919) B2221919
theorem B1481287 : Blo 1480560 1481287 := bstep (se 1 (by rfl) ⟨1110965, by rfl⟩ : syracuseStep 1481287 = 2221931) B2221931
theorem B3332681 : Blo 1480560 3332681 := bstep (se 2 (by rfl) ⟨1249755, by rfl⟩ : syracuseStep 3332681 = 2499511) B2499511
theorem B5626543 : Blo 1480560 5626543 := bstep (se 1 (by rfl) ⟨4219907, by rfl⟩ : syracuseStep 5626543 = 8439815) B8439815
theorem B3750583 : Blo 1480560 3750583 := bstep (se 1 (by rfl) ⟨2812937, by rfl⟩ : syracuseStep 3750583 = 5625875) B5625875
theorem B1481439 : Blo 1480560 1481439 := bstep (se 1 (by rfl) ⟨1111079, by rfl⟩ : syracuseStep 1481439 = 2222159) B2222159
theorem B2849555 : Blo 1480560 2849555 := bstep (se 1 (by rfl) ⟨2137166, by rfl⟩ : syracuseStep 2849555 = 4274333) B4274333
theorem B1481519 : Blo 1480560 1481519 := bstep (se 1 (by rfl) ⟨1111139, by rfl⟩ : syracuseStep 1481519 = 2222279) B2222279
theorem B1481627 : Blo 1480560 1481627 := bstep (se 1 (by rfl) ⟨1111220, by rfl⟩ : syracuseStep 1481627 = 2222441) B2222441
theorem B1481679 : Blo 1480560 1481679 := bstep (se 1 (by rfl) ⟨1111259, by rfl⟩ : syracuseStep 1481679 = 2222519) B2222519
theorem B3333095 : Blo 1480560 3333095 := bstep (se 1 (by rfl) ⟨2499821, by rfl⟩ : syracuseStep 3333095 = 4999643) B4999643
theorem B1481703 : Blo 1480560 1481703 := bstep (se 1 (by rfl) ⟨1111277, by rfl⟩ : syracuseStep 1481703 = 2222555) B2222555
theorem B3750887 : Blo 1480560 3750887 := bstep (se 1 (by rfl) ⟨2813165, by rfl⟩ : syracuseStep 3750887 = 5626331) B5626331
theorem B1482015 : Blo 1480560 1482015 := bstep (se 1 (by rfl) ⟨1111511, by rfl⟩ : syracuseStep 1482015 = 2223023) B2223023
theorem B15203659 : Blo 1480560 15203659 := bstep (se 1 (by rfl) ⟨11402744, by rfl⟩ : syracuseStep 15203659 = 22805489) B22805489
theorem B3333473 : Blo 1480560 3333473 := bstep (se 2 (by rfl) ⟨1250052, by rfl⟩ : syracuseStep 3333473 = 2500105) B2500105
theorem B3333563 : Blo 1480560 3333563 := bstep (se 1 (by rfl) ⟨2500172, by rfl⟩ : syracuseStep 3333563 = 5000345) B5000345
theorem B3333689 : Blo 1480560 3333689 := bstep (se 2 (by rfl) ⟨1250133, by rfl⟩ : syracuseStep 3333689 = 2500267) B2500267
theorem B6004307 : Blo 1480560 6004307 := bstep (se 1 (by rfl) ⟨4503230, by rfl⟩ : syracuseStep 6004307 = 9006461) B9006461
theorem B1875631 : Blo 1480560 1875631 := bstep (se 1 (by rfl) ⟨1406723, by rfl⟩ : syracuseStep 1875631 = 2813447) B2813447
theorem B6848297 : Blo 1480560 6848297 := bstep (se 2 (by rfl) ⟨2568111, by rfl⟩ : syracuseStep 6848297 = 5136223) B5136223
theorem B12009323 : Blo 1480560 12009323 := bstep (se 1 (by rfl) ⟨9006992, by rfl⟩ : syracuseStep 12009323 = 18013985) B18013985
theorem B10682219 : Blo 1480560 10682219 := bstep (se 1 (by rfl) ⟨8011664, by rfl⟩ : syracuseStep 10682219 = 16023329) B16023329
theorem B6324257 : Blo 1480560 6324257 := bstep (se 2 (by rfl) ⟨2371596, by rfl⟩ : syracuseStep 6324257 = 4743193) B4743193
theorem B4997159 : Blo 1480560 4997159 := bstep (se 1 (by rfl) ⟨3747869, by rfl⟩ : syracuseStep 4997159 = 7495739) B7495739
theorem B9494587 : Blo 1480560 9494587 := bstep (se 1 (by rfl) ⟨7120940, by rfl⟩ : syracuseStep 9494587 = 14241881) B14241881
theorem B41107571 : Blo 1480560 41107571 := bstep (se 1 (by rfl) ⟨30830678, by rfl⟩ : syracuseStep 41107571 = 61661357) B61661357
theorem B41099437 : Blo 1480560 41099437 := bstep (se 3 (by rfl) ⟨7706144, by rfl⟩ : syracuseStep 41099437 = 15412289) B15412289
theorem B7119095 : Blo 1480560 7119095 := bstep (se 1 (by rfl) ⟨5339321, by rfl⟩ : syracuseStep 7119095 = 10678643) B10678643
theorem B8438039 : Blo 1480560 8438039 := bstep (se 1 (by rfl) ⟨6328529, by rfl⟩ : syracuseStep 8438039 = 12657059) B12657059
theorem B3334607 : Blo 1480560 3334607 := bstep (se 1 (by rfl) ⟨2500955, by rfl⟩ : syracuseStep 3334607 = 5001911) B5001911
theorem B2499167 : Blo 1480560 2499167 := bstep (se 1 (by rfl) ⟨1874375, by rfl⟩ : syracuseStep 2499167 = 3748751) B3748751
theorem B4743809 : Blo 1480560 4743809 := bstep (se 2 (by rfl) ⟨1778928, by rfl⟩ : syracuseStep 4743809 = 3557857) B3557857
theorem B4997807 : Blo 1480560 4997807 := bstep (se 1 (by rfl) ⟨3748355, by rfl⟩ : syracuseStep 4997807 = 7496711) B7496711
theorem B2220911 : Blo 1480560 2220911 := bstep (se 1 (by rfl) ⟨1665683, by rfl⟩ : syracuseStep 2220911 = 3331367) B3331367
theorem B9495407 : Blo 1480560 9495407 := bstep (se 1 (by rfl) ⟨7121555, by rfl⟩ : syracuseStep 9495407 = 14243111) B14243111
theorem B4998131 : Blo 1480560 4998131 := bstep (se 1 (by rfl) ⟨3748598, by rfl⟩ : syracuseStep 4998131 = 7497197) B7497197
theorem B14074985 : Blo 1480560 14074985 := bstep (se 2 (by rfl) ⟨5278119, by rfl⟩ : syracuseStep 14074985 = 10556239) B10556239
theorem B2221163 : Blo 1480560 2221163 := bstep (se 1 (by rfl) ⟨1665872, by rfl⟩ : syracuseStep 2221163 = 3331745) B3331745
theorem B8004815 : Blo 1480560 8004815 := bstep (se 1 (by rfl) ⟨6003611, by rfl⟩ : syracuseStep 8004815 = 12007223) B12007223
theorem B2221403 : Blo 1480560 2221403 := bstep (se 1 (by rfl) ⟨1666052, by rfl⟩ : syracuseStep 2221403 = 3332105) B3332105
theorem B4998671 : Blo 1480560 4998671 := bstep (se 1 (by rfl) ⟨3749003, by rfl⟩ : syracuseStep 4998671 = 7498007) B7498007
theorem B2811503 : Blo 1480560 2811503 := bstep (se 1 (by rfl) ⟨2108627, by rfl⟩ : syracuseStep 2811503 = 4217255) B4217255
theorem B2221679 : Blo 1480560 2221679 := bstep (se 1 (by rfl) ⟨1666259, by rfl⟩ : syracuseStep 2221679 = 3332519) B3332519
theorem B2221751 : Blo 1480560 2221751 := bstep (se 1 (by rfl) ⟨1666313, by rfl⟩ : syracuseStep 2221751 = 3332627) B3332627
theorem B48039641 : Blo 1480560 48039641 := bstep (se 2 (by rfl) ⟨18014865, by rfl⟩ : syracuseStep 48039641 = 36029731) B36029731
theorem B2221787 : Blo 1480560 2221787 := bstep (se 1 (by rfl) ⟨1666340, by rfl⟩ : syracuseStep 2221787 = 3332681) B3332681
theorem B8554207 : Blo 1480560 8554207 := bstep (se 1 (by rfl) ⟨6415655, by rfl⟩ : syracuseStep 8554207 = 12831311) B12831311
theorem B2221961 : Blo 1480560 2221961 := bstep (se 2 (by rfl) ⟨833235, by rfl⟩ : syracuseStep 2221961 = 1666471) B1666471
theorem B2222063 : Blo 1480560 2222063 := bstep (se 1 (by rfl) ⟨1666547, by rfl⟩ : syracuseStep 2222063 = 3333095) B3333095
theorem B2500591 : Blo 1480560 2500591 := bstep (se 1 (by rfl) ⟨1875443, by rfl⟩ : syracuseStep 2500591 = 3750887) B3750887
theorem B8783923 : Blo 1480560 8783923 := bstep (se 1 (by rfl) ⟨6587942, by rfl⟩ : syracuseStep 8783923 = 13175885) B13175885
theorem B2500841 : Blo 1480560 2500841 := bstep (se 2 (by rfl) ⟨937815, by rfl⟩ : syracuseStep 2500841 = 1875631) B1875631
theorem B2222315 : Blo 1480560 2222315 := bstep (se 1 (by rfl) ⟨1666736, by rfl⟩ : syracuseStep 2222315 = 3333473) B3333473
theorem B28485917 : Blo 1480560 28485917 := bstep (se 3 (by rfl) ⟨5341109, by rfl⟩ : syracuseStep 28485917 = 10682219) B10682219
theorem B2222375 : Blo 1480560 2222375 := bstep (se 1 (by rfl) ⟨1666781, by rfl⟩ : syracuseStep 2222375 = 3333563) B3333563
theorem B4999481 : Blo 1480560 4999481 := bstep (se 2 (by rfl) ⟨1874805, by rfl⟩ : syracuseStep 4999481 = 3749611) B3749611
theorem B10676569 : Blo 1480560 10676569 := bstep (se 2 (by rfl) ⟨4003713, by rfl⟩ : syracuseStep 10676569 = 8007427) B8007427
theorem B2222459 : Blo 1480560 2222459 := bstep (se 1 (by rfl) ⟨1666844, by rfl⟩ : syracuseStep 2222459 = 3333689) B3333689
theorem B3557771 : Blo 1480560 3557771 := bstep (se 1 (by rfl) ⟨2668328, by rfl⟩ : syracuseStep 3557771 = 5336657) B5336657
theorem B4565531 : Blo 1480560 4565531 := bstep (se 1 (by rfl) ⟨3424148, by rfl⟩ : syracuseStep 4565531 = 6848297) B6848297
theorem B8006215 : Blo 1480560 8006215 := bstep (se 1 (by rfl) ⟨6004661, by rfl⟩ : syracuseStep 8006215 = 12009323) B12009323
theorem B4999751 : Blo 1480560 4999751 := bstep (se 1 (by rfl) ⟨3749813, by rfl⟩ : syracuseStep 4999751 = 7499627) B7499627
theorem B2222729 : Blo 1480560 2222729 := bstep (se 2 (by rfl) ⟨833523, by rfl⟩ : syracuseStep 2222729 = 1667047) B1667047
theorem B5622443 : Blo 1480560 5622443 := bstep (se 1 (by rfl) ⟨4216832, by rfl⟩ : syracuseStep 5622443 = 8433665) B8433665
theorem B4745911 : Blo 1480560 4745911 := bstep (se 1 (by rfl) ⟨3559433, by rfl⟩ : syracuseStep 4745911 = 7118867) B7118867
theorem B11250413 : Blo 1480560 11250413 := bstep (se 3 (by rfl) ⟨2109452, by rfl⟩ : syracuseStep 11250413 = 4218905) B4218905
theorem B2222903 : Blo 1480560 2222903 := bstep (se 1 (by rfl) ⟨1667177, by rfl⟩ : syracuseStep 2222903 = 3334355) B3334355
theorem B5483351 : Blo 1480560 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B2222939 : Blo 1480560 2222939 := bstep (se 1 (by rfl) ⟨1667204, by rfl⟩ : syracuseStep 2222939 = 3334409) B3334409
theorem B11406253 : Blo 1480560 11406253 := bstep (se 3 (by rfl) ⟨2138672, by rfl⟩ : syracuseStep 11406253 = 4277345) B4277345
theorem B2812907 : Blo 1480560 2812907 := bstep (se 1 (by rfl) ⟨2109680, by rfl⟩ : syracuseStep 2812907 = 4219361) B4219361
theorem B2223083 : Blo 1480560 2223083 := bstep (se 1 (by rfl) ⟨1667312, by rfl⟩ : syracuseStep 2223083 = 3334625) B3334625
theorem B4877815 : Blo 1480560 4877815 := bstep (se 1 (by rfl) ⟨3658361, by rfl⟩ : syracuseStep 4877815 = 7316723) B7316723
theorem B5000777 : Blo 1480560 5000777 := bstep (se 2 (by rfl) ⟨1875291, by rfl⟩ : syracuseStep 5000777 = 3750583) B3750583
theorem B1666651 : Blo 1480560 1666651 := bstep (se 1 (by rfl) ⟨1249988, by rfl⟩ : syracuseStep 1666651 = 2499977) B2499977
theorem B6327983 : Blo 1480560 6327983 := bstep (se 1 (by rfl) ⟨4745987, by rfl⟩ : syracuseStep 6327983 = 9491975) B9491975
theorem B1666939 : Blo 1480560 1666939 := bstep (se 1 (by rfl) ⟨1250204, by rfl⟩ : syracuseStep 1666939 = 2500409) B2500409
theorem B2109407 : Blo 1480560 2109407 := bstep (se 1 (by rfl) ⟨1582055, by rfl⟩ : syracuseStep 2109407 = 3164111) B3164111
theorem B12660785 : Blo 1480560 12660785 := bstep (se 2 (by rfl) ⟨4747794, by rfl⟩ : syracuseStep 12660785 = 9495589) B9495589
theorem B69365969 : Blo 1480560 69365969 := bstep (se 2 (by rfl) ⟨26012238, by rfl⟩ : syracuseStep 69365969 = 52024477) B52024477
theorem B22794533 : Blo 1480560 22794533 := bstep (se 4 (by rfl) ⟨2136987, by rfl⟩ : syracuseStep 22794533 = 4273975) B4273975
theorem B8786303 : Blo 1480560 8786303 := bstep (se 1 (by rfl) ⟨6589727, by rfl⟩ : syracuseStep 8786303 = 13179455) B13179455
theorem B20271545 : Blo 1480560 20271545 := bstep (se 2 (by rfl) ⟨7601829, by rfl⟩ : syracuseStep 20271545 = 15203659) B15203659
theorem B4747859 : Blo 1480560 4747859 := bstep (se 1 (by rfl) ⟨3560894, by rfl⟩ : syracuseStep 4747859 = 7121789) B7121789
theorem B8434439 : Blo 1480560 8434439 := bstep (se 1 (by rfl) ⟨6325829, by rfl⟩ : syracuseStep 8434439 = 12651659) B12651659
theorem B4002871 : Blo 1480560 4002871 := bstep (se 1 (by rfl) ⟨3002153, by rfl⟩ : syracuseStep 4002871 = 6004307) B6004307
theorem B12006539 : Blo 1480560 12006539 := bstep (se 1 (by rfl) ⟨9004904, by rfl⟩ : syracuseStep 12006539 = 18009809) B18009809
theorem B6755537 : Blo 1480560 6755537 := bstep (se 2 (by rfl) ⟨2533326, by rfl⟩ : syracuseStep 6755537 = 5066653) B5066653
theorem B3749075 : Blo 1480560 3749075 := bstep (se 1 (by rfl) ⟨2811806, by rfl⟩ : syracuseStep 3749075 = 5623613) B5623613
theorem B9492025 : Blo 1480560 9492025 := bstep (se 2 (by rfl) ⟨3559509, by rfl⟩ : syracuseStep 9492025 = 7119019) B7119019
theorem B3331655 : Blo 1480560 3331655 := bstep (se 1 (by rfl) ⟨2498741, by rfl⟩ : syracuseStep 3331655 = 4997483) B4997483
theorem B10131115 : Blo 1480560 10131115 := bstep (se 1 (by rfl) ⟨7598336, by rfl⟩ : syracuseStep 10131115 = 15196673) B15196673
theorem B3331835 : Blo 1480560 3331835 := bstep (se 1 (by rfl) ⟨2498876, by rfl⟩ : syracuseStep 3331835 = 4997753) B4997753
theorem B4003799 : Blo 1480560 4003799 := bstep (se 1 (by rfl) ⟨3002849, by rfl⟩ : syracuseStep 4003799 = 6005699) B6005699
theorem B1480687 : Blo 1480560 1480687 := bstep (se 1 (by rfl) ⟨1110515, by rfl⟩ : syracuseStep 1480687 = 2221031) B2221031
theorem B1480859 : Blo 1480560 1480859 := bstep (se 1 (by rfl) ⟨1110644, by rfl⟩ : syracuseStep 1480859 = 2221289) B2221289
theorem B8435897 : Blo 1480560 8435897 := bstep (se 2 (by rfl) ⟨3163461, by rfl⟩ : syracuseStep 8435897 = 6326923) B6326923
theorem B1480895 : Blo 1480560 1480895 := bstep (se 1 (by rfl) ⟨1110671, by rfl⟩ : syracuseStep 1480895 = 2221343) B2221343
theorem B7502057 : Blo 1480560 7502057 := bstep (se 2 (by rfl) ⟨2813271, by rfl⟩ : syracuseStep 7502057 = 5626543) B5626543
theorem B4217129 : Blo 1480560 4217129 := bstep (se 2 (by rfl) ⟨1581423, by rfl⟩ : syracuseStep 4217129 = 3162847) B3162847
theorem B3332393 : Blo 1480560 3332393 := bstep (se 2 (by rfl) ⟨1249647, by rfl⟩ : syracuseStep 3332393 = 2499295) B2499295
theorem B1481007 : Blo 1480560 1481007 := bstep (se 1 (by rfl) ⟨1110755, by rfl⟩ : syracuseStep 1481007 = 2221511) B2221511
theorem B9492947 : Blo 1480560 9492947 := bstep (se 1 (by rfl) ⟨7119710, by rfl⟩ : syracuseStep 9492947 = 14239421) B14239421
theorem B1481243 : Blo 1480560 1481243 := bstep (se 1 (by rfl) ⟨1110932, by rfl⟩ : syracuseStep 1481243 = 2221865) B2221865
theorem B1481247 : Blo 1480560 1481247 := bstep (se 1 (by rfl) ⟨1110935, by rfl⟩ : syracuseStep 1481247 = 2221871) B2221871
theorem B40557095 : Blo 1480560 40557095 := bstep (se 1 (by rfl) ⟨30417821, by rfl⟩ : syracuseStep 40557095 = 60835643) B60835643
theorem B1481563 : Blo 1480560 1481563 := bstep (se 1 (by rfl) ⟨1111172, by rfl⟩ : syracuseStep 1481563 = 2222345) B2222345
theorem B3332969 : Blo 1480560 3332969 := bstep (se 2 (by rfl) ⟨1249863, by rfl⟩ : syracuseStep 3332969 = 2499727) B2499727
theorem B9493357 : Blo 1480560 9493357 := bstep (se 3 (by rfl) ⟨1780004, by rfl⟩ : syracuseStep 9493357 = 3560009) B3560009
theorem B3333023 : Blo 1480560 3333023 := bstep (se 1 (by rfl) ⟨2499767, by rfl⟩ : syracuseStep 3333023 = 4999535) B4999535
theorem B1481631 : Blo 1480560 1481631 := bstep (se 1 (by rfl) ⟨1111223, by rfl⟩ : syracuseStep 1481631 = 2222447) B2222447
theorem B1481775 : Blo 1480560 1481775 := bstep (se 1 (by rfl) ⟨1111331, by rfl⟩ : syracuseStep 1481775 = 2222663) B2222663
theorem B1481799 : Blo 1480560 1481799 := bstep (se 1 (by rfl) ⟨1111349, by rfl⟩ : syracuseStep 1481799 = 2222699) B2222699
theorem B1899703 : Blo 1480560 1899703 := bstep (se 1 (by rfl) ⟨1424777, by rfl⟩ : syracuseStep 1899703 = 2849555) B2849555
theorem B1481951 : Blo 1480560 1481951 := bstep (se 1 (by rfl) ⟨1111463, by rfl⟩ : syracuseStep 1481951 = 2222927) B2222927
theorem B3333959 : Blo 1480560 3333959 := bstep (se 1 (by rfl) ⟨2500469, by rfl⟩ : syracuseStep 3333959 = 5000939) B5000939
theorem B4005703 : Blo 1480560 4005703 := bstep (se 1 (by rfl) ⟨3004277, by rfl⟩ : syracuseStep 4005703 = 6008555) B6008555
theorem B46243979 : Blo 1480560 46243979 := bstep (se 1 (by rfl) ⟨34682984, by rfl⟩ : syracuseStep 46243979 = 69365969) B69365969
theorem B15196355 : Blo 1480560 15196355 := bstep (se 1 (by rfl) ⟨11397266, by rfl⟩ : syracuseStep 15196355 = 22794533) B22794533
theorem B5857535 : Blo 1480560 5857535 := bstep (se 1 (by rfl) ⟨4393151, by rfl⟩ : syracuseStep 5857535 = 8786303) B8786303
theorem B3162539 : Blo 1480560 3162539 := bstep (se 1 (by rfl) ⟨2371904, by rfl⟩ : syracuseStep 3162539 = 4743809) B4743809
theorem B8004359 : Blo 1480560 8004359 := bstep (se 1 (by rfl) ⟨6003269, by rfl⟩ : syracuseStep 8004359 = 12006539) B12006539
theorem B10674953 : Blo 1480560 10674953 := bstep (se 2 (by rfl) ⟨4003107, by rfl⟩ : syracuseStep 10674953 = 8006215) B8006215
theorem B2499383 : Blo 1480560 2499383 := bstep (se 1 (by rfl) ⟨1874537, by rfl⟩ : syracuseStep 2499383 = 3749075) B3749075
theorem B2221103 : Blo 1480560 2221103 := bstep (se 1 (by rfl) ⟨1665827, by rfl⟩ : syracuseStep 2221103 = 3331655) B3331655
theorem B12657809 : Blo 1480560 12657809 := bstep (se 2 (by rfl) ⟨4746678, by rfl⟩ : syracuseStep 12657809 = 9493357) B9493357
theorem B2221223 : Blo 1480560 2221223 := bstep (se 1 (by rfl) ⟨1665917, by rfl⟩ : syracuseStep 2221223 = 3331835) B3331835
theorem B18990611 : Blo 1480560 18990611 := bstep (se 1 (by rfl) ⟨14242958, by rfl⟩ : syracuseStep 18990611 = 28485917) B28485917
theorem B2811419 : Blo 1480560 2811419 := bstep (se 1 (by rfl) ⟨2108564, by rfl⟩ : syracuseStep 2811419 = 4217129) B4217129
theorem B2221595 : Blo 1480560 2221595 := bstep (se 1 (by rfl) ⟨1666196, by rfl⟩ : syracuseStep 2221595 = 3332393) B3332393
theorem B3655567 : Blo 1480560 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B2221979 : Blo 1480560 2221979 := bstep (se 1 (by rfl) ⟨1666484, by rfl⟩ : syracuseStep 2221979 = 3332969) B3332969
theorem B2222015 : Blo 1480560 2222015 := bstep (se 1 (by rfl) ⟨1666511, by rfl⟩ : syracuseStep 2222015 = 3333023) B3333023
theorem B2222201 : Blo 1480560 2222201 := bstep (se 2 (by rfl) ⟨833325, by rfl⟩ : syracuseStep 2222201 = 1666651) B1666651
theorem B42707189 : Blo 1480560 42707189 := bstep (se 5 (by rfl) ⟨2001899, by rfl⟩ : syracuseStep 42707189 = 4003799) B4003799
theorem B11405609 : Blo 1480560 11405609 := bstep (se 2 (by rfl) ⟨4277103, by rfl⟩ : syracuseStep 11405609 = 8554207) B8554207
theorem B2222585 : Blo 1480560 2222585 := bstep (se 2 (by rfl) ⟨833469, by rfl⟩ : syracuseStep 2222585 = 1666939) B1666939
theorem B2222639 : Blo 1480560 2222639 := bstep (se 1 (by rfl) ⟨1666979, by rfl⟩ : syracuseStep 2222639 = 3333959) B3333959
theorem B8440523 : Blo 1480560 8440523 := bstep (se 1 (by rfl) ⟨6330392, by rfl⟩ : syracuseStep 8440523 = 12660785) B12660785
theorem B27405047 : Blo 1480560 27405047 := bstep (se 1 (by rfl) ⟨20553785, by rfl⟩ : syracuseStep 27405047 = 41107571) B41107571
theorem B12659449 : Blo 1480560 12659449 := bstep (se 2 (by rfl) ⟨4747293, by rfl⟩ : syracuseStep 12659449 = 9494587) B9494587
theorem B54799249 : Blo 1480560 54799249 := bstep (se 2 (by rfl) ⟨20549718, by rfl⟩ : syracuseStep 54799249 = 41099437) B41099437
theorem B2223071 : Blo 1480560 2223071 := bstep (se 1 (by rfl) ⟨1667303, by rfl⟩ : syracuseStep 2223071 = 3334607) B3334607
theorem B3165239 : Blo 1480560 3165239 := bstep (se 1 (by rfl) ⟨2373929, by rfl⟩ : syracuseStep 3165239 = 4747859) B4747859
theorem B1666111 : Blo 1480560 1666111 := bstep (se 1 (by rfl) ⟨1249583, by rfl⟩ : syracuseStep 1666111 = 2499167) B2499167
theorem B5622959 : Blo 1480560 5622959 := bstep (se 1 (by rfl) ⟨4217219, by rfl⟩ : syracuseStep 5622959 = 8434439) B8434439
theorem B18984253 : Blo 1480560 18984253 := bstep (se 3 (by rfl) ⟨3559547, by rfl⟩ : syracuseStep 18984253 = 7119095) B7119095
theorem B5336543 : Blo 1480560 5336543 := bstep (se 1 (by rfl) ⟨4002407, by rfl⟩ : syracuseStep 5336543 = 8004815) B8004815
theorem B6327881 : Blo 1480560 6327881 := bstep (se 2 (by rfl) ⟨2372955, by rfl⟩ : syracuseStep 6327881 = 4745911) B4745911
theorem B32026427 : Blo 1480560 32026427 := bstep (se 1 (by rfl) ⟨24019820, by rfl⟩ : syracuseStep 32026427 = 48039641) B48039641
theorem B15208337 : Blo 1480560 15208337 := bstep (se 2 (by rfl) ⟨5703126, by rfl⟩ : syracuseStep 15208337 = 11406253) B11406253
theorem B5337161 : Blo 1480560 5337161 := bstep (se 2 (by rfl) ⟨2001435, by rfl⟩ : syracuseStep 5337161 = 4002871) B4002871
theorem B5623931 : Blo 1480560 5623931 := bstep (se 1 (by rfl) ⟨4217948, by rfl⟩ : syracuseStep 5623931 = 8435897) B8435897
theorem B5001371 : Blo 1480560 5001371 := bstep (se 1 (by rfl) ⟨3751028, by rfl⟩ : syracuseStep 5001371 = 7502057) B7502057
theorem B1667227 : Blo 1480560 1667227 := bstep (se 1 (by rfl) ⟨1250420, by rfl⟩ : syracuseStep 1667227 = 2500841) B2500841
theorem B2371847 : Blo 1480560 2371847 := bstep (se 1 (by rfl) ⟨1778885, by rfl⟩ : syracuseStep 2371847 = 3557771) B3557771
theorem B6328631 : Blo 1480560 6328631 := bstep (se 1 (by rfl) ⟨4746473, by rfl⟩ : syracuseStep 6328631 = 9492947) B9492947
theorem B3043687 : Blo 1480560 3043687 := bstep (se 1 (by rfl) ⟨2282765, by rfl⟩ : syracuseStep 3043687 = 4565531) B4565531
theorem B27038063 : Blo 1480560 27038063 := bstep (se 1 (by rfl) ⟨20278547, by rfl⟩ : syracuseStep 27038063 = 40557095) B40557095
theorem B3748295 : Blo 1480560 3748295 := bstep (se 1 (by rfl) ⟨2811221, by rfl⟩ : syracuseStep 3748295 = 5622443) B5622443
theorem B7500275 : Blo 1480560 7500275 := bstep (se 1 (by rfl) ⟨5625206, by rfl⟩ : syracuseStep 7500275 = 11250413) B11250413
theorem B5625085 : Blo 1480560 5625085 := bstep (se 3 (by rfl) ⟨1054703, by rfl⟩ : syracuseStep 5625085 = 2109407) B2109407
theorem B7501085 : Blo 1480560 7501085 := bstep (se 3 (by rfl) ⟨1406453, by rfl⟩ : syracuseStep 7501085 = 2812907) B2812907
theorem B3331439 : Blo 1480560 3331439 := bstep (se 1 (by rfl) ⟨2498579, by rfl⟩ : syracuseStep 3331439 = 4997159) B4997159
theorem B11711897 : Blo 1480560 11711897 := bstep (se 2 (by rfl) ⟨4391961, by rfl⟩ : syracuseStep 11711897 = 8783923) B8783923
theorem B16864685 : Blo 1480560 16864685 := bstep (se 3 (by rfl) ⟨3162128, by rfl⟩ : syracuseStep 16864685 = 6324257) B6324257
theorem B5625359 : Blo 1480560 5625359 := bstep (se 1 (by rfl) ⟨4219019, by rfl⟩ : syracuseStep 5625359 = 8438039) B8438039
theorem B37533293 : Blo 1480560 37533293 := bstep (se 3 (by rfl) ⟨7037492, by rfl⟩ : syracuseStep 37533293 = 14074985) B14074985
theorem B13514363 : Blo 1480560 13514363 := bstep (se 1 (by rfl) ⟨10135772, by rfl⟩ : syracuseStep 13514363 = 20271545) B20271545
theorem B3331871 : Blo 1480560 3331871 := bstep (se 1 (by rfl) ⟨2498903, by rfl⟩ : syracuseStep 3331871 = 4997807) B4997807
theorem B14235425 : Blo 1480560 14235425 := bstep (se 2 (by rfl) ⟨5338284, by rfl⟩ : syracuseStep 14235425 = 10676569) B10676569
theorem B1480607 : Blo 1480560 1480607 := bstep (se 1 (by rfl) ⟨1110455, by rfl⟩ : syracuseStep 1480607 = 2220911) B2220911
theorem B3332087 : Blo 1480560 3332087 := bstep (se 1 (by rfl) ⟨2499065, by rfl⟩ : syracuseStep 3332087 = 4998131) B4998131
theorem B1480775 : Blo 1480560 1480775 := bstep (se 1 (by rfl) ⟨1110581, by rfl⟩ : syracuseStep 1480775 = 2221163) B2221163
theorem B4503691 : Blo 1480560 4503691 := bstep (se 1 (by rfl) ⟨3377768, by rfl⟩ : syracuseStep 4503691 = 6755537) B6755537
theorem B1480935 : Blo 1480560 1480935 := bstep (se 1 (by rfl) ⟨1110701, by rfl⟩ : syracuseStep 1480935 = 2221403) B2221403
theorem B10131749 : Blo 1480560 10131749 := bstep (se 4 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 10131749 = 1899703) B1899703
theorem B3332447 : Blo 1480560 3332447 := bstep (se 1 (by rfl) ⟨2499335, by rfl⟩ : syracuseStep 3332447 = 4998671) B4998671
theorem B1874335 : Blo 1480560 1874335 := bstep (se 1 (by rfl) ⟨1405751, by rfl⟩ : syracuseStep 1874335 = 2811503) B2811503
theorem B1481119 : Blo 1480560 1481119 := bstep (se 1 (by rfl) ⟨1110839, by rfl⟩ : syracuseStep 1481119 = 2221679) B2221679
theorem B1481167 : Blo 1480560 1481167 := bstep (se 1 (by rfl) ⟨1110875, by rfl⟩ : syracuseStep 1481167 = 2221751) B2221751
theorem B1481191 : Blo 1480560 1481191 := bstep (se 1 (by rfl) ⟨1110893, by rfl⟩ : syracuseStep 1481191 = 2221787) B2221787
theorem B1481307 : Blo 1480560 1481307 := bstep (se 1 (by rfl) ⟨1110980, by rfl⟩ : syracuseStep 1481307 = 2221961) B2221961
theorem B1481375 : Blo 1480560 1481375 := bstep (se 1 (by rfl) ⟨1111031, by rfl⟩ : syracuseStep 1481375 = 2222063) B2222063
theorem B1481543 : Blo 1480560 1481543 := bstep (se 1 (by rfl) ⟨1111157, by rfl⟩ : syracuseStep 1481543 = 2222315) B2222315
theorem B1481583 : Blo 1480560 1481583 := bstep (se 1 (by rfl) ⟨1111187, by rfl⟩ : syracuseStep 1481583 = 2222375) B2222375
theorem B3332987 : Blo 1480560 3332987 := bstep (se 1 (by rfl) ⟨2499740, by rfl⟩ : syracuseStep 3332987 = 4999481) B4999481
theorem B1481639 : Blo 1480560 1481639 := bstep (se 1 (by rfl) ⟨1111229, by rfl⟩ : syracuseStep 1481639 = 2222459) B2222459
theorem B3333167 : Blo 1480560 3333167 := bstep (se 1 (by rfl) ⟨2499875, by rfl⟩ : syracuseStep 3333167 = 4999751) B4999751
theorem B1481819 : Blo 1480560 1481819 := bstep (se 1 (by rfl) ⟨1111364, by rfl⟩ : syracuseStep 1481819 = 2222729) B2222729
theorem B1481935 : Blo 1480560 1481935 := bstep (se 1 (by rfl) ⟨1111451, by rfl⟩ : syracuseStep 1481935 = 2222903) B2222903
theorem B1481959 : Blo 1480560 1481959 := bstep (se 1 (by rfl) ⟨1111469, by rfl⟩ : syracuseStep 1481959 = 2222939) B2222939
theorem B1482055 : Blo 1480560 1482055 := bstep (se 1 (by rfl) ⟨1111541, by rfl⟩ : syracuseStep 1482055 = 2223083) B2223083
theorem B6503753 : Blo 1480560 6503753 := bstep (se 2 (by rfl) ⟨2438907, by rfl⟩ : syracuseStep 6503753 = 4877815) B4877815
theorem B12656033 : Blo 1480560 12656033 := bstep (se 2 (by rfl) ⟨4746012, by rfl⟩ : syracuseStep 12656033 = 9492025) B9492025
theorem B13508153 : Blo 1480560 13508153 := bstep (se 2 (by rfl) ⟨5065557, by rfl⟩ : syracuseStep 13508153 = 10131115) B10131115
theorem B25321085 : Blo 1480560 25321085 := bstep (se 3 (by rfl) ⟨4747703, by rfl⟩ : syracuseStep 25321085 = 9495407) B9495407
theorem B3333851 : Blo 1480560 3333851 := bstep (se 1 (by rfl) ⟨2500388, by rfl⟩ : syracuseStep 3333851 = 5000777) B5000777
theorem B5340937 : Blo 1480560 5340937 := bstep (se 2 (by rfl) ⟨2002851, by rfl⟩ : syracuseStep 5340937 = 4005703) B4005703
theorem B4218655 : Blo 1480560 4218655 := bstep (se 1 (by rfl) ⟨3163991, by rfl⟩ : syracuseStep 4218655 = 6327983) B6327983
theorem B3334121 : Blo 1480560 3334121 := bstep (se 2 (by rfl) ⟨1250295, by rfl⟩ : syracuseStep 3334121 = 2500591) B2500591
theorem B3334247 : Blo 1480560 3334247 := bstep (se 1 (by rfl) ⟨2500685, by rfl⟩ : syracuseStep 3334247 = 5001371) B5001371
theorem B2498863 : Blo 1480560 2498863 := bstep (se 1 (by rfl) ⟨1874147, by rfl⟩ : syracuseStep 2498863 = 3748295) B3748295
theorem B2499113 : Blo 1480560 2499113 := bstep (se 2 (by rfl) ⟨937167, by rfl⟩ : syracuseStep 2499113 = 1874335) B1874335
theorem B6324925 : Blo 1480560 6324925 := bstep (se 3 (by rfl) ⟨1185923, by rfl⟩ : syracuseStep 6324925 = 2371847) B2371847
theorem B24019685 : Blo 1480560 24019685 := bstep (se 4 (by rfl) ⟨2251845, by rfl⟩ : syracuseStep 24019685 = 4503691) B4503691
theorem B8438539 : Blo 1480560 8438539 := bstep (se 1 (by rfl) ⟨6328904, by rfl⟩ : syracuseStep 8438539 = 12657809) B12657809
theorem B16876349 : Blo 1480560 16876349 := bstep (se 3 (by rfl) ⟨3164315, by rfl⟩ : syracuseStep 16876349 = 6328631) B6328631
theorem B2220959 : Blo 1480560 2220959 := bstep (se 1 (by rfl) ⟨1665719, by rfl⟩ : syracuseStep 2220959 = 3331439) B3331439
theorem B7807931 : Blo 1480560 7807931 := bstep (se 1 (by rfl) ⟨5855948, by rfl⟩ : syracuseStep 7807931 = 11711897) B11711897
theorem B2221247 : Blo 1480560 2221247 := bstep (se 1 (by rfl) ⟨1665935, by rfl⟩ : syracuseStep 2221247 = 3331871) B3331871
theorem B73065665 : Blo 1480560 73065665 := bstep (se 2 (by rfl) ⟨27399624, by rfl⟩ : syracuseStep 73065665 = 54799249) B54799249
theorem B2221391 : Blo 1480560 2221391 := bstep (se 1 (by rfl) ⟨1666043, by rfl⟩ : syracuseStep 2221391 = 3332087) B3332087
theorem B2221481 : Blo 1480560 2221481 := bstep (se 2 (by rfl) ⟨833055, by rfl⟩ : syracuseStep 2221481 = 1666111) B1666111
theorem B7603739 : Blo 1480560 7603739 := bstep (se 1 (by rfl) ⟨5702804, by rfl⟩ : syracuseStep 7603739 = 11405609) B11405609
theorem B2221631 : Blo 1480560 2221631 := bstep (se 1 (by rfl) ⟨1666223, by rfl⟩ : syracuseStep 2221631 = 3332447) B3332447
theorem B18270031 : Blo 1480560 18270031 := bstep (se 1 (by rfl) ⟨13702523, by rfl⟩ : syracuseStep 18270031 = 27405047) B27405047
theorem B2221991 : Blo 1480560 2221991 := bstep (se 1 (by rfl) ⟨1666493, by rfl⟩ : syracuseStep 2221991 = 3332987) B3332987
theorem B2222111 : Blo 1480560 2222111 := bstep (se 1 (by rfl) ⟨1666583, by rfl⟩ : syracuseStep 2222111 = 3333167) B3333167
theorem B64931989 : Blo 1480560 64931989 := bstep (se 6 (by rfl) ⟨1521843, by rfl⟩ : syracuseStep 64931989 = 3043687) B3043687
theorem B4335835 : Blo 1480560 4335835 := bstep (se 1 (by rfl) ⟨3251876, by rfl⟩ : syracuseStep 4335835 = 6503753) B6503753
theorem B3557695 : Blo 1480560 3557695 := bstep (se 1 (by rfl) ⟨2668271, by rfl⟩ : syracuseStep 3557695 = 5336543) B5336543
theorem B7121249 : Blo 1480560 7121249 := bstep (se 2 (by rfl) ⟨2670468, by rfl⟩ : syracuseStep 7121249 = 5340937) B5340937
theorem B9005435 : Blo 1480560 9005435 := bstep (se 1 (by rfl) ⟨6754076, by rfl⟩ : syracuseStep 9005435 = 13508153) B13508153
theorem B2222567 : Blo 1480560 2222567 := bstep (se 1 (by rfl) ⟨1666925, by rfl⟩ : syracuseStep 2222567 = 3333851) B3333851
theorem B21350951 : Blo 1480560 21350951 := bstep (se 1 (by rfl) ⟨16013213, by rfl⟩ : syracuseStep 21350951 = 32026427) B32026427
theorem B2222747 : Blo 1480560 2222747 := bstep (se 1 (by rfl) ⟨1667060, by rfl⟩ : syracuseStep 2222747 = 3334121) B3334121
theorem B3558107 : Blo 1480560 3558107 := bstep (se 1 (by rfl) ⟨2668580, by rfl⟩ : syracuseStep 3558107 = 5337161) B5337161
theorem B30829319 : Blo 1480560 30829319 := bstep (se 1 (by rfl) ⟨23121989, by rfl⟩ : syracuseStep 30829319 = 46243979) B46243979
theorem B2222969 : Blo 1480560 2222969 := bstep (se 2 (by rfl) ⟨833613, by rfl⟩ : syracuseStep 2222969 = 1667227) B1667227
theorem B18025375 : Blo 1480560 18025375 := bstep (se 1 (by rfl) ⟨13519031, by rfl⟩ : syracuseStep 18025375 = 27038063) B27038063
theorem B2108359 : Blo 1480560 2108359 := bstep (se 1 (by rfl) ⟨1581269, by rfl⟩ : syracuseStep 2108359 = 3162539) B3162539
theorem B5000183 : Blo 1480560 5000183 := bstep (se 1 (by rfl) ⟨3750137, by rfl⟩ : syracuseStep 5000183 = 7500275) B7500275
theorem B5336239 : Blo 1480560 5336239 := bstep (se 1 (by rfl) ⟨4002179, by rfl⟩ : syracuseStep 5336239 = 8004359) B8004359
theorem B1666255 : Blo 1480560 1666255 := bstep (se 1 (by rfl) ⟨1249691, by rfl⟩ : syracuseStep 1666255 = 2499383) B2499383
theorem B5000723 : Blo 1480560 5000723 := bstep (se 1 (by rfl) ⟨3750542, by rfl⟩ : syracuseStep 5000723 = 7501085) B7501085
theorem B11243123 : Blo 1480560 11243123 := bstep (se 1 (by rfl) ⟨8432342, by rfl⟩ : syracuseStep 11243123 = 16864685) B16864685
theorem B16879265 : Blo 1480560 16879265 := bstep (se 2 (by rfl) ⟨6329724, by rfl⟩ : syracuseStep 16879265 = 12659449) B12659449
theorem B12660407 : Blo 1480560 12660407 := bstep (se 1 (by rfl) ⟨9495305, by rfl⟩ : syracuseStep 12660407 = 18990611) B18990611
theorem B25022195 : Blo 1480560 25022195 := bstep (se 1 (by rfl) ⟨18766646, by rfl⟩ : syracuseStep 25022195 = 37533293) B37533293
theorem B9490283 : Blo 1480560 9490283 := bstep (se 1 (by rfl) ⟨7117712, by rfl⟩ : syracuseStep 9490283 = 14235425) B14235425
theorem B28471459 : Blo 1480560 28471459 := bstep (se 1 (by rfl) ⟨21353594, by rfl⟩ : syracuseStep 28471459 = 42707189) B42707189
theorem B6754499 : Blo 1480560 6754499 := bstep (se 1 (by rfl) ⟨5065874, by rfl⟩ : syracuseStep 6754499 = 10131749) B10131749
theorem B7500113 : Blo 1480560 7500113 := bstep (se 2 (by rfl) ⟨2812542, by rfl⟩ : syracuseStep 7500113 = 5625085) B5625085
theorem B2110159 : Blo 1480560 2110159 := bstep (se 1 (by rfl) ⟨1582619, by rfl⟩ : syracuseStep 2110159 = 3165239) B3165239
theorem B3748639 : Blo 1480560 3748639 := bstep (se 1 (by rfl) ⟨2811479, by rfl⟩ : syracuseStep 3748639 = 5622959) B5622959
theorem B5624873 : Blo 1480560 5624873 := bstep (se 2 (by rfl) ⟨2109327, by rfl⟩ : syracuseStep 5624873 = 4218655) B4218655
theorem B16880723 : Blo 1480560 16880723 := bstep (se 1 (by rfl) ⟨12660542, by rfl⟩ : syracuseStep 16880723 = 25321085) B25321085
theorem B10138891 : Blo 1480560 10138891 := bstep (se 1 (by rfl) ⟨7604168, by rfl⟩ : syracuseStep 10138891 = 15208337) B15208337
theorem B3749287 : Blo 1480560 3749287 := bstep (se 1 (by rfl) ⟨2811965, by rfl⟩ : syracuseStep 3749287 = 5623931) B5623931
theorem B10130903 : Blo 1480560 10130903 := bstep (se 1 (by rfl) ⟨7598177, by rfl⟩ : syracuseStep 10130903 = 15196355) B15196355
theorem B3905023 : Blo 1480560 3905023 := bstep (se 1 (by rfl) ⟨2928767, by rfl⟩ : syracuseStep 3905023 = 5857535) B5857535
theorem B7116635 : Blo 1480560 7116635 := bstep (se 1 (by rfl) ⟨5337476, by rfl⟩ : syracuseStep 7116635 = 10674953) B10674953
theorem B1480735 : Blo 1480560 1480735 := bstep (se 1 (by rfl) ⟨1110551, by rfl⟩ : syracuseStep 1480735 = 2221103) B2221103
theorem B1480815 : Blo 1480560 1480815 := bstep (se 1 (by rfl) ⟨1110611, by rfl⟩ : syracuseStep 1480815 = 2221223) B2221223
theorem B3750239 : Blo 1480560 3750239 := bstep (se 1 (by rfl) ⟨2812679, by rfl⟩ : syracuseStep 3750239 = 5625359) B5625359
theorem B1874279 : Blo 1480560 1874279 := bstep (se 1 (by rfl) ⟨1405709, by rfl⟩ : syracuseStep 1874279 = 2811419) B2811419
theorem B1481063 : Blo 1480560 1481063 := bstep (se 1 (by rfl) ⟨1110797, by rfl⟩ : syracuseStep 1481063 = 2221595) B2221595
theorem B9009575 : Blo 1480560 9009575 := bstep (se 1 (by rfl) ⟨6757181, by rfl⟩ : syracuseStep 9009575 = 13514363) B13514363
theorem B1481319 : Blo 1480560 1481319 := bstep (se 1 (by rfl) ⟨1110989, by rfl⟩ : syracuseStep 1481319 = 2221979) B2221979
theorem B1481343 : Blo 1480560 1481343 := bstep (se 1 (by rfl) ⟨1111007, by rfl⟩ : syracuseStep 1481343 = 2222015) B2222015
theorem B1481467 : Blo 1480560 1481467 := bstep (se 1 (by rfl) ⟨1111100, by rfl⟩ : syracuseStep 1481467 = 2222201) B2222201
theorem B1481723 : Blo 1480560 1481723 := bstep (se 1 (by rfl) ⟨1111292, by rfl⟩ : syracuseStep 1481723 = 2222585) B2222585
theorem B1481759 : Blo 1480560 1481759 := bstep (se 1 (by rfl) ⟨1111319, by rfl⟩ : syracuseStep 1481759 = 2222639) B2222639
theorem B25312337 : Blo 1480560 25312337 := bstep (se 2 (by rfl) ⟨9492126, by rfl⟩ : syracuseStep 25312337 = 18984253) B18984253
theorem B5627015 : Blo 1480560 5627015 := bstep (se 1 (by rfl) ⟨4220261, by rfl⟩ : syracuseStep 5627015 = 8440523) B8440523
theorem B1482047 : Blo 1480560 1482047 := bstep (se 1 (by rfl) ⟨1111535, by rfl⟩ : syracuseStep 1482047 = 2223071) B2223071
theorem B8437355 : Blo 1480560 8437355 := bstep (se 1 (by rfl) ⟨6328016, by rfl⟩ : syracuseStep 8437355 = 12656033) B12656033
theorem B4218587 : Blo 1480560 4218587 := bstep (se 1 (by rfl) ⟨3163940, by rfl⟩ : syracuseStep 4218587 = 6327881) B6327881
theorem B4874089 : Blo 1480560 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B37961945 : Blo 1480560 37961945 := bstep (se 2 (by rfl) ⟨14235729, by rfl⟩ : syracuseStep 37961945 = 28471459) B28471459
theorem B4743593 : Blo 1480560 4743593 := bstep (se 2 (by rfl) ⟨1778847, by rfl⟩ : syracuseStep 4743593 = 3557695) B3557695
theorem B48710443 : Blo 1480560 48710443 := bstep (se 1 (by rfl) ⟨36532832, by rfl⟩ : syracuseStep 48710443 = 73065665) B73065665
theorem B4998077 : Blo 1480560 4998077 := bstep (se 3 (by rfl) ⟨937139, by rfl⟩ : syracuseStep 4998077 = 1874279) B1874279
theorem B4998185 : Blo 1480560 4998185 := bstep (se 2 (by rfl) ⟨1874319, by rfl⟩ : syracuseStep 4998185 = 3748639) B3748639
theorem B4744423 : Blo 1480560 4744423 := bstep (se 1 (by rfl) ⟨3558317, by rfl⟩ : syracuseStep 4744423 = 7116635) B7116635
theorem B2500159 : Blo 1480560 2500159 := bstep (se 1 (by rfl) ⟨1875119, by rfl⟩ : syracuseStep 2500159 = 3750239) B3750239
theorem B2221673 : Blo 1480560 2221673 := bstep (se 2 (by rfl) ⟨833127, by rfl⟩ : syracuseStep 2221673 = 1666255) B1666255
theorem B6006383 : Blo 1480560 6006383 := bstep (se 1 (by rfl) ⟨4504787, by rfl⟩ : syracuseStep 6006383 = 9009575) B9009575
theorem B13518521 : Blo 1480560 13518521 := bstep (se 2 (by rfl) ⟨5069445, by rfl⟩ : syracuseStep 13518521 = 10138891) B10138891
theorem B4999049 : Blo 1480560 4999049 := bstep (se 2 (by rfl) ⟨1874643, by rfl⟩ : syracuseStep 4999049 = 3749287) B3749287
theorem B9488285 : Blo 1480560 9488285 := bstep (se 3 (by rfl) ⟨1779053, by rfl⟩ : syracuseStep 9488285 = 3558107) B3558107
theorem B8440271 : Blo 1480560 8440271 := bstep (se 1 (by rfl) ⟨6330203, by rfl⟩ : syracuseStep 8440271 = 12660407) B12660407
theorem B6498785 : Blo 1480560 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B2812391 : Blo 1480560 2812391 := bstep (se 1 (by rfl) ⟨2109293, by rfl⟩ : syracuseStep 2812391 = 4218587) B4218587
theorem B16681463 : Blo 1480560 16681463 := bstep (se 1 (by rfl) ⟨12511097, by rfl⟩ : syracuseStep 16681463 = 25022195) B25022195
theorem B6326855 : Blo 1480560 6326855 := bstep (se 1 (by rfl) ⟨4745141, by rfl⟩ : syracuseStep 6326855 = 9490283) B9490283
theorem B2222831 : Blo 1480560 2222831 := bstep (se 1 (by rfl) ⟨1667123, by rfl⟩ : syracuseStep 2222831 = 3334247) B3334247
theorem B86575985 : Blo 1480560 86575985 := bstep (se 2 (by rfl) ⟨32465994, by rfl⟩ : syracuseStep 86575985 = 64931989) B64931989
theorem B5000075 : Blo 1480560 5000075 := bstep (se 1 (by rfl) ⟨3750056, by rfl⟩ : syracuseStep 5000075 = 7500113) B7500113
theorem B1666075 : Blo 1480560 1666075 := bstep (se 1 (by rfl) ⟨1249556, by rfl⟩ : syracuseStep 1666075 = 2499113) B2499113
theorem B11250899 : Blo 1480560 11250899 := bstep (se 1 (by rfl) ⟨8438174, by rfl⟩ : syracuseStep 11250899 = 16876349) B16876349
theorem B5205287 : Blo 1480560 5205287 := bstep (se 1 (by rfl) ⟨3903965, by rfl⟩ : syracuseStep 5205287 = 7807931) B7807931
theorem B8433233 : Blo 1480560 8433233 := bstep (se 2 (by rfl) ⟨3162462, by rfl⟩ : syracuseStep 8433233 = 6324925) B6324925
theorem B2813545 : Blo 1480560 2813545 := bstep (se 2 (by rfl) ⟨1055079, by rfl⟩ : syracuseStep 2813545 = 2110159) B2110159
theorem B6753935 : Blo 1480560 6753935 := bstep (se 1 (by rfl) ⟨5065451, by rfl⟩ : syracuseStep 6753935 = 10130903) B10130903
theorem B11251385 : Blo 1480560 11251385 := bstep (se 2 (by rfl) ⟨4219269, by rfl⟩ : syracuseStep 11251385 = 8438539) B8438539
theorem B7114985 : Blo 1480560 7114985 := bstep (se 2 (by rfl) ⟨2668119, by rfl⟩ : syracuseStep 7114985 = 5336239) B5336239
theorem B4747499 : Blo 1480560 4747499 := bstep (se 1 (by rfl) ⟨3560624, by rfl⟩ : syracuseStep 4747499 = 7121249) B7121249
theorem B14233967 : Blo 1480560 14233967 := bstep (se 1 (by rfl) ⟨10675475, by rfl⟩ : syracuseStep 14233967 = 21350951) B21350951
theorem B5206697 : Blo 1480560 5206697 := bstep (se 2 (by rfl) ⟨1952511, by rfl⟩ : syracuseStep 5206697 = 3905023) B3905023
theorem B11244581 : Blo 1480560 11244581 := bstep (se 4 (by rfl) ⟨1054179, by rfl⟩ : syracuseStep 11244581 = 2108359) B2108359
theorem B5624903 : Blo 1480560 5624903 := bstep (se 1 (by rfl) ⟨4218677, by rfl⟩ : syracuseStep 5624903 = 8437355) B8437355
theorem B24360041 : Blo 1480560 24360041 := bstep (se 2 (by rfl) ⟨9135015, by rfl⟩ : syracuseStep 24360041 = 18270031) B18270031
theorem B11252843 : Blo 1480560 11252843 := bstep (se 1 (by rfl) ⟨8439632, by rfl⟩ : syracuseStep 11252843 = 16879265) B16879265
theorem B4502999 : Blo 1480560 4502999 := bstep (se 1 (by rfl) ⟨3377249, by rfl⟩ : syracuseStep 4502999 = 6754499) B6754499
theorem B5781113 : Blo 1480560 5781113 := bstep (se 2 (by rfl) ⟨2167917, by rfl⟩ : syracuseStep 5781113 = 4335835) B4335835
theorem B3331817 : Blo 1480560 3331817 := bstep (se 2 (by rfl) ⟨1249431, by rfl⟩ : syracuseStep 3331817 = 2498863) B2498863
theorem B16013123 : Blo 1480560 16013123 := bstep (se 1 (by rfl) ⟨12009842, by rfl⟩ : syracuseStep 16013123 = 24019685) B24019685
theorem B1480639 : Blo 1480560 1480639 := bstep (se 1 (by rfl) ⟨1110479, by rfl⟩ : syracuseStep 1480639 = 2220959) B2220959
theorem B3749915 : Blo 1480560 3749915 := bstep (se 1 (by rfl) ⟨2812436, by rfl⟩ : syracuseStep 3749915 = 5624873) B5624873
theorem B11253815 : Blo 1480560 11253815 := bstep (se 1 (by rfl) ⟨8440361, by rfl⟩ : syracuseStep 11253815 = 16880723) B16880723
theorem B1480831 : Blo 1480560 1480831 := bstep (se 1 (by rfl) ⟨1110623, by rfl⟩ : syracuseStep 1480831 = 2221247) B2221247
theorem B1480927 : Blo 1480560 1480927 := bstep (se 1 (by rfl) ⟨1110695, by rfl⟩ : syracuseStep 1480927 = 2221391) B2221391
theorem B1480987 : Blo 1480560 1480987 := bstep (se 1 (by rfl) ⟨1110740, by rfl⟩ : syracuseStep 1480987 = 2221481) B2221481
theorem B5069159 : Blo 1480560 5069159 := bstep (se 1 (by rfl) ⟨3801869, by rfl⟩ : syracuseStep 5069159 = 7603739) B7603739
theorem B1481087 : Blo 1480560 1481087 := bstep (se 1 (by rfl) ⟨1110815, by rfl⟩ : syracuseStep 1481087 = 2221631) B2221631
theorem B24033833 : Blo 1480560 24033833 := bstep (se 2 (by rfl) ⟨9012687, by rfl⟩ : syracuseStep 24033833 = 18025375) B18025375
theorem B1481327 : Blo 1480560 1481327 := bstep (se 1 (by rfl) ⟨1110995, by rfl⟩ : syracuseStep 1481327 = 2221991) B2221991
theorem B1481407 : Blo 1480560 1481407 := bstep (se 1 (by rfl) ⟨1111055, by rfl⟩ : syracuseStep 1481407 = 2222111) B2222111
theorem B6003623 : Blo 1480560 6003623 := bstep (se 1 (by rfl) ⟨4502717, by rfl⟩ : syracuseStep 6003623 = 9005435) B9005435
theorem B1481711 : Blo 1480560 1481711 := bstep (se 1 (by rfl) ⟨1111283, by rfl⟩ : syracuseStep 1481711 = 2222567) B2222567
theorem B1481831 : Blo 1480560 1481831 := bstep (se 1 (by rfl) ⟨1111373, by rfl⟩ : syracuseStep 1481831 = 2222747) B2222747
theorem B20552879 : Blo 1480560 20552879 := bstep (se 1 (by rfl) ⟨15414659, by rfl⟩ : syracuseStep 20552879 = 30829319) B30829319
theorem B1481979 : Blo 1480560 1481979 := bstep (se 1 (by rfl) ⟨1111484, by rfl⟩ : syracuseStep 1481979 = 2222969) B2222969
theorem B3333455 : Blo 1480560 3333455 := bstep (se 1 (by rfl) ⟨2500091, by rfl⟩ : syracuseStep 3333455 = 5000183) B5000183
theorem B16874891 : Blo 1480560 16874891 := bstep (se 1 (by rfl) ⟨12656168, by rfl⟩ : syracuseStep 16874891 = 25312337) B25312337
theorem B3751343 : Blo 1480560 3751343 := bstep (se 1 (by rfl) ⟨2813507, by rfl⟩ : syracuseStep 3751343 = 5627015) B5627015
theorem B3333815 : Blo 1480560 3333815 := bstep (se 1 (by rfl) ⟨2500361, by rfl⟩ : syracuseStep 3333815 = 5000723) B5000723
theorem B7495415 : Blo 1480560 7495415 := bstep (se 1 (by rfl) ⟨5621561, by rfl⟩ : syracuseStep 7495415 = 11243123) B11243123
theorem B4743323 : Blo 1480560 4743323 := bstep (se 1 (by rfl) ⟨3557492, by rfl⟩ : syracuseStep 4743323 = 7114985) B7114985
theorem B3162395 : Blo 1480560 3162395 := bstep (se 1 (by rfl) ⟨2371796, by rfl⟩ : syracuseStep 3162395 = 4743593) B4743593
theorem B7496387 : Blo 1480560 7496387 := bstep (se 1 (by rfl) ⟨5622290, by rfl⟩ : syracuseStep 7496387 = 11244581) B11244581
theorem B64947257 : Blo 1480560 64947257 := bstep (se 2 (by rfl) ⟨24355221, by rfl⟩ : syracuseStep 64947257 = 48710443) B48710443
theorem B9012347 : Blo 1480560 9012347 := bstep (se 1 (by rfl) ⟨6759260, by rfl⟩ : syracuseStep 9012347 = 13518521) B13518521
theorem B2221211 : Blo 1480560 2221211 := bstep (se 1 (by rfl) ⟨1665908, by rfl⟩ : syracuseStep 2221211 = 3331817) B3331817
theorem B10675415 : Blo 1480560 10675415 := bstep (se 1 (by rfl) ⟨8006561, by rfl⟩ : syracuseStep 10675415 = 16013123) B16013123
theorem B6325523 : Blo 1480560 6325523 := bstep (se 1 (by rfl) ⟨4744142, by rfl⟩ : syracuseStep 6325523 = 9488285) B9488285
theorem B2499943 : Blo 1480560 2499943 := bstep (se 1 (by rfl) ⟨1874957, by rfl⟩ : syracuseStep 2499943 = 3749915) B3749915
theorem B2221433 : Blo 1480560 2221433 := bstep (se 2 (by rfl) ⟨833037, by rfl⟩ : syracuseStep 2221433 = 1666075) B1666075
theorem B2222303 : Blo 1480560 2222303 := bstep (se 1 (by rfl) ⟨1666727, by rfl⟩ : syracuseStep 2222303 = 3333455) B3333455
theorem B11249927 : Blo 1480560 11249927 := bstep (se 1 (by rfl) ⟨8437445, by rfl⟩ : syracuseStep 11249927 = 16874891) B16874891
theorem B2500895 : Blo 1480560 2500895 := bstep (se 1 (by rfl) ⟨1875671, by rfl⟩ : syracuseStep 2500895 = 3751343) B3751343
theorem B5622155 : Blo 1480560 5622155 := bstep (se 1 (by rfl) ⟨4216616, by rfl⟩ : syracuseStep 5622155 = 8433233) B8433233
theorem B2222543 : Blo 1480560 2222543 := bstep (se 1 (by rfl) ⟨1666907, by rfl⟩ : syracuseStep 2222543 = 3333815) B3333815
theorem B25307963 : Blo 1480560 25307963 := bstep (se 1 (by rfl) ⟨18980972, by rfl⟩ : syracuseStep 25307963 = 37961945) B37961945
theorem B3164999 : Blo 1480560 3164999 := bstep (se 1 (by rfl) ⟨2373749, by rfl⟩ : syracuseStep 3164999 = 4747499) B4747499
theorem B9489311 : Blo 1480560 9489311 := bstep (se 1 (by rfl) ⟨7116983, by rfl⟩ : syracuseStep 9489311 = 14233967) B14233967
theorem B16240027 : Blo 1480560 16240027 := bstep (se 1 (by rfl) ⟨12180020, by rfl⟩ : syracuseStep 16240027 = 24360041) B24360041
theorem B3854075 : Blo 1480560 3854075 := bstep (se 1 (by rfl) ⟨2890556, by rfl⟩ : syracuseStep 3854075 = 5781113) B5781113
theorem B3379439 : Blo 1480560 3379439 := bstep (se 1 (by rfl) ⟨2534579, by rfl⟩ : syracuseStep 3379439 = 5069159) B5069159
theorem B11120975 : Blo 1480560 11120975 := bstep (se 1 (by rfl) ⟨8340731, by rfl⟩ : syracuseStep 11120975 = 16681463) B16681463
theorem B57717323 : Blo 1480560 57717323 := bstep (se 1 (by rfl) ⟨43287992, by rfl⟩ : syracuseStep 57717323 = 86575985) B86575985
theorem B4002415 : Blo 1480560 4002415 := bstep (se 1 (by rfl) ⟨3001811, by rfl⟩ : syracuseStep 4002415 = 6003623) B6003623
theorem B13701919 : Blo 1480560 13701919 := bstep (se 1 (by rfl) ⟨10276439, by rfl⟩ : syracuseStep 13701919 = 20552879) B20552879
theorem B7500599 : Blo 1480560 7500599 := bstep (se 1 (by rfl) ⟨5625449, by rfl⟩ : syracuseStep 7500599 = 11250899) B11250899
theorem B3470191 : Blo 1480560 3470191 := bstep (se 1 (by rfl) ⟨2602643, by rfl⟩ : syracuseStep 3470191 = 5205287) B5205287
theorem B4502623 : Blo 1480560 4502623 := bstep (se 1 (by rfl) ⟨3376967, by rfl⟩ : syracuseStep 4502623 = 6753935) B6753935
theorem B7500923 : Blo 1480560 7500923 := bstep (se 1 (by rfl) ⟨5625692, by rfl⟩ : syracuseStep 7500923 = 11251385) B11251385
theorem B3471131 : Blo 1480560 3471131 := bstep (se 1 (by rfl) ⟨2603348, by rfl⟩ : syracuseStep 3471131 = 5206697) B5206697
theorem B3332051 : Blo 1480560 3332051 := bstep (se 1 (by rfl) ⟨2499038, by rfl⟩ : syracuseStep 3332051 = 4998077) B4998077
theorem B3332123 : Blo 1480560 3332123 := bstep (se 1 (by rfl) ⟨2499092, by rfl⟩ : syracuseStep 3332123 = 4998185) B4998185
theorem B3749935 : Blo 1480560 3749935 := bstep (se 1 (by rfl) ⟨2812451, by rfl⟩ : syracuseStep 3749935 = 5624903) B5624903
theorem B7501895 : Blo 1480560 7501895 := bstep (se 1 (by rfl) ⟨5626421, by rfl⟩ : syracuseStep 7501895 = 11252843) B11252843
theorem B1481115 : Blo 1480560 1481115 := bstep (se 1 (by rfl) ⟨1110836, by rfl⟩ : syracuseStep 1481115 = 2221673) B2221673
theorem B4004255 : Blo 1480560 4004255 := bstep (se 1 (by rfl) ⟨3003191, by rfl⟩ : syracuseStep 4004255 = 6006383) B6006383
theorem B25303589 : Blo 1480560 25303589 := bstep (se 4 (by rfl) ⟨2372211, by rfl⟩ : syracuseStep 25303589 = 4744423) B4744423
theorem B12007997 : Blo 1480560 12007997 := bstep (se 3 (by rfl) ⟨2251499, by rfl⟩ : syracuseStep 12007997 = 4502999) B4502999
theorem B3332699 : Blo 1480560 3332699 := bstep (se 1 (by rfl) ⟨2499524, by rfl⟩ : syracuseStep 3332699 = 4999049) B4999049
theorem B7502543 : Blo 1480560 7502543 := bstep (se 1 (by rfl) ⟨5626907, by rfl⟩ : syracuseStep 7502543 = 11253815) B11253815
theorem B5626847 : Blo 1480560 5626847 := bstep (se 1 (by rfl) ⟨4220135, by rfl⟩ : syracuseStep 5626847 = 8440271) B8440271
theorem B4332523 : Blo 1480560 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B1874927 : Blo 1480560 1874927 := bstep (se 1 (by rfl) ⟨1406195, by rfl⟩ : syracuseStep 1874927 = 2812391) B2812391
theorem B16022555 : Blo 1480560 16022555 := bstep (se 1 (by rfl) ⟨12016916, by rfl⟩ : syracuseStep 16022555 = 24033833) B24033833
theorem B4217903 : Blo 1480560 4217903 := bstep (se 1 (by rfl) ⟨3163427, by rfl⟩ : syracuseStep 4217903 = 6326855) B6326855
theorem B1481887 : Blo 1480560 1481887 := bstep (se 1 (by rfl) ⟨1111415, by rfl⟩ : syracuseStep 1481887 = 2222831) B2222831
theorem B3333383 : Blo 1480560 3333383 := bstep (se 1 (by rfl) ⟨2500037, by rfl⟩ : syracuseStep 3333383 = 5000075) B5000075
theorem B3333545 : Blo 1480560 3333545 := bstep (se 2 (by rfl) ⟨1250079, by rfl⟩ : syracuseStep 3333545 = 2500159) B2500159
theorem B3751393 : Blo 1480560 3751393 := bstep (se 2 (by rfl) ⟨1406772, by rfl⟩ : syracuseStep 3751393 = 2813545) B2813545
theorem B4996943 : Blo 1480560 4996943 := bstep (se 1 (by rfl) ⟨3747707, by rfl⟩ : syracuseStep 4996943 = 7495415) B7495415
theorem B3162215 : Blo 1480560 3162215 := bstep (se 1 (by rfl) ⟨2371661, by rfl⟩ : syracuseStep 3162215 = 4743323) B4743323
theorem B7413983 : Blo 1480560 7413983 := bstep (se 1 (by rfl) ⟨5560487, by rfl⟩ : syracuseStep 7413983 = 11120975) B11120975
theorem B38478215 : Blo 1480560 38478215 := bstep (se 1 (by rfl) ⟨28858661, by rfl⟩ : syracuseStep 38478215 = 57717323) B57717323
theorem B4997591 : Blo 1480560 4997591 := bstep (se 1 (by rfl) ⟨3748193, by rfl⟩ : syracuseStep 4997591 = 7496387) B7496387
theorem B9011837 : Blo 1480560 9011837 := bstep (se 3 (by rfl) ⟨1689719, by rfl⟩ : syracuseStep 9011837 = 3379439) B3379439
theorem B18269225 : Blo 1480560 18269225 := bstep (se 2 (by rfl) ⟨6850959, by rfl⟩ : syracuseStep 18269225 = 13701919) B13701919
theorem B2221367 : Blo 1480560 2221367 := bstep (se 1 (by rfl) ⟨1666025, by rfl⟩ : syracuseStep 2221367 = 3332051) B3332051
theorem B5776697 : Blo 1480560 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B2221415 : Blo 1480560 2221415 := bstep (se 1 (by rfl) ⟨1666061, by rfl⟩ : syracuseStep 2221415 = 3332123) B3332123
theorem B16869059 : Blo 1480560 16869059 := bstep (se 1 (by rfl) ⟨12651794, by rfl⟩ : syracuseStep 16869059 = 25303589) B25303589
theorem B8005331 : Blo 1480560 8005331 := bstep (se 1 (by rfl) ⟨6003998, by rfl⟩ : syracuseStep 8005331 = 12007997) B12007997
theorem B2221799 : Blo 1480560 2221799 := bstep (se 1 (by rfl) ⟨1666349, by rfl⟩ : syracuseStep 2221799 = 3332699) B3332699
theorem B21653369 : Blo 1480560 21653369 := bstep (se 2 (by rfl) ⟨8120013, by rfl⟩ : syracuseStep 21653369 = 16240027) B16240027
theorem B18507685 : Blo 1480560 18507685 := bstep (se 4 (by rfl) ⟨1735095, by rfl⟩ : syracuseStep 18507685 = 3470191) B3470191
theorem B6326207 : Blo 1480560 6326207 := bstep (se 1 (by rfl) ⟨4744655, by rfl⟩ : syracuseStep 6326207 = 9489311) B9489311
theorem B2811935 : Blo 1480560 2811935 := bstep (se 1 (by rfl) ⟨2108951, by rfl⟩ : syracuseStep 2811935 = 4217903) B4217903
theorem B2222255 : Blo 1480560 2222255 := bstep (se 1 (by rfl) ⟨1666691, by rfl⟩ : syracuseStep 2222255 = 3333383) B3333383
theorem B8439997 : Blo 1480560 8439997 := bstep (se 3 (by rfl) ⟨1582499, by rfl⟩ : syracuseStep 8439997 = 3164999) B3164999
theorem B2222363 : Blo 1480560 2222363 := bstep (se 1 (by rfl) ⟨1666772, by rfl⟩ : syracuseStep 2222363 = 3333545) B3333545
theorem B4999805 : Blo 1480560 4999805 := bstep (se 3 (by rfl) ⟨937463, by rfl⟩ : syracuseStep 4999805 = 1874927) B1874927
theorem B4999913 : Blo 1480560 4999913 := bstep (se 2 (by rfl) ⟨1874967, by rfl⟩ : syracuseStep 4999913 = 3749935) B3749935
theorem B2108263 : Blo 1480560 2108263 := bstep (se 1 (by rfl) ⟨1581197, by rfl⟩ : syracuseStep 2108263 = 3162395) B3162395
theorem B5000399 : Blo 1480560 5000399 := bstep (se 1 (by rfl) ⟨3750299, by rfl⟩ : syracuseStep 5000399 = 7500599) B7500599
theorem B43298171 : Blo 1480560 43298171 := bstep (se 1 (by rfl) ⟨32473628, by rfl⟩ : syracuseStep 43298171 = 64947257) B64947257
theorem B5000615 : Blo 1480560 5000615 := bstep (se 1 (by rfl) ⟨3750461, by rfl⟩ : syracuseStep 5000615 = 7500923) B7500923
theorem B6008231 : Blo 1480560 6008231 := bstep (se 1 (by rfl) ⟨4506173, by rfl⟩ : syracuseStep 6008231 = 9012347) B9012347
theorem B10678013 : Blo 1480560 10678013 := bstep (se 3 (by rfl) ⟨2002127, by rfl⟩ : syracuseStep 10678013 = 4004255) B4004255
theorem B5001263 : Blo 1480560 5001263 := bstep (se 1 (by rfl) ⟨3750947, by rfl⟩ : syracuseStep 5001263 = 7501895) B7501895
theorem B7499951 : Blo 1480560 7499951 := bstep (se 1 (by rfl) ⟨5624963, by rfl⟩ : syracuseStep 7499951 = 11249927) B11249927
theorem B1667263 : Blo 1480560 1667263 := bstep (se 1 (by rfl) ⟨1250447, by rfl⟩ : syracuseStep 1667263 = 2500895) B2500895
theorem B3748103 : Blo 1480560 3748103 := bstep (se 1 (by rfl) ⟨2811077, by rfl⟩ : syracuseStep 3748103 = 5622155) B5622155
theorem B5001695 : Blo 1480560 5001695 := bstep (se 1 (by rfl) ⟨3751271, by rfl⟩ : syracuseStep 5001695 = 7502543) B7502543
theorem B16871975 : Blo 1480560 16871975 := bstep (se 1 (by rfl) ⟨12653981, by rfl⟩ : syracuseStep 16871975 = 25307963) B25307963
theorem B5001857 : Blo 1480560 5001857 := bstep (se 2 (by rfl) ⟨1875696, by rfl⟩ : syracuseStep 5001857 = 3751393) B3751393
theorem B10277533 : Blo 1480560 10277533 := bstep (se 3 (by rfl) ⟨1927037, by rfl⟩ : syracuseStep 10277533 = 3854075) B3854075
theorem B3331295 : Blo 1480560 3331295 := bstep (se 1 (by rfl) ⟨2498471, by rfl⟩ : syracuseStep 3331295 = 4996943) B4996943
theorem B1480807 : Blo 1480560 1480807 := bstep (se 1 (by rfl) ⟨1110605, by rfl⟩ : syracuseStep 1480807 = 2221211) B2221211
theorem B7116943 : Blo 1480560 7116943 := bstep (se 1 (by rfl) ⟨5337707, by rfl⟩ : syracuseStep 7116943 = 10675415) B10675415
theorem B4217015 : Blo 1480560 4217015 := bstep (se 1 (by rfl) ⟨3162761, by rfl⟩ : syracuseStep 4217015 = 6325523) B6325523
theorem B1480955 : Blo 1480560 1480955 := bstep (se 1 (by rfl) ⟨1110716, by rfl⟩ : syracuseStep 1480955 = 2221433) B2221433
theorem B6003497 : Blo 1480560 6003497 := bstep (se 2 (by rfl) ⟨2251311, by rfl⟩ : syracuseStep 6003497 = 4502623) B4502623
theorem B1481535 : Blo 1480560 1481535 := bstep (se 1 (by rfl) ⟨1111151, by rfl⟩ : syracuseStep 1481535 = 2222303) B2222303
theorem B1481695 : Blo 1480560 1481695 := bstep (se 1 (by rfl) ⟨1111271, by rfl⟩ : syracuseStep 1481695 = 2222543) B2222543
theorem B3333257 : Blo 1480560 3333257 := bstep (se 2 (by rfl) ⟨1249971, by rfl⟩ : syracuseStep 3333257 = 2499943) B2499943
theorem B3751231 : Blo 1480560 3751231 := bstep (se 1 (by rfl) ⟨2813423, by rfl⟩ : syracuseStep 3751231 = 5626847) B5626847
theorem B10681703 : Blo 1480560 10681703 := bstep (se 1 (by rfl) ⟨8011277, by rfl⟩ : syracuseStep 10681703 = 16022555) B16022555
theorem B9256349 : Blo 1480560 9256349 := bstep (se 3 (by rfl) ⟨1735565, by rfl⟩ : syracuseStep 9256349 = 3471131) B3471131
theorem B85384853 : Blo 1480560 85384853 := bstep (se 6 (by rfl) ⟨2001207, by rfl⟩ : syracuseStep 85384853 = 4002415) B4002415
theorem B3334175 : Blo 1480560 3334175 := bstep (se 1 (by rfl) ⟨2500631, by rfl⟩ : syracuseStep 3334175 = 5001263) B5001263
theorem B2498735 : Blo 1480560 2498735 := bstep (se 1 (by rfl) ⟨1874051, by rfl⟩ : syracuseStep 2498735 = 3748103) B3748103
theorem B3334463 : Blo 1480560 3334463 := bstep (se 1 (by rfl) ⟨2500847, by rfl⟩ : syracuseStep 3334463 = 5001695) B5001695
theorem B11247983 : Blo 1480560 11247983 := bstep (se 1 (by rfl) ⟨8435987, by rfl⟩ : syracuseStep 11247983 = 16871975) B16871975
theorem B3334571 : Blo 1480560 3334571 := bstep (se 1 (by rfl) ⟨2500928, by rfl⟩ : syracuseStep 3334571 = 5001857) B5001857
theorem B2220863 : Blo 1480560 2220863 := bstep (se 1 (by rfl) ⟨1665647, by rfl⟩ : syracuseStep 2220863 = 3331295) B3331295
theorem B2811017 : Blo 1480560 2811017 := bstep (se 2 (by rfl) ⟨1054131, by rfl⟩ : syracuseStep 2811017 = 2108263) B2108263
theorem B14435579 : Blo 1480560 14435579 := bstep (se 1 (by rfl) ⟨10826684, by rfl⟩ : syracuseStep 14435579 = 21653369) B21653369
theorem B2811343 : Blo 1480560 2811343 := bstep (se 1 (by rfl) ⟨2108507, by rfl⟩ : syracuseStep 2811343 = 4217015) B4217015
theorem B2222171 : Blo 1480560 2222171 := bstep (se 1 (by rfl) ⟨1666628, by rfl⟩ : syracuseStep 2222171 = 3333257) B3333257
theorem B7121135 : Blo 1480560 7121135 := bstep (se 1 (by rfl) ⟨5340851, by rfl⟩ : syracuseStep 7121135 = 10681703) B10681703
theorem B6170899 : Blo 1480560 6170899 := bstep (se 1 (by rfl) ⟨4628174, by rfl⟩ : syracuseStep 6170899 = 9256349) B9256349
theorem B24676913 : Blo 1480560 24676913 := bstep (se 2 (by rfl) ⟨9253842, by rfl⟩ : syracuseStep 24676913 = 18507685) B18507685
theorem B2108143 : Blo 1480560 2108143 := bstep (se 1 (by rfl) ⟨1581107, by rfl⟩ : syracuseStep 2108143 = 3162215) B3162215
theorem B7498493 : Blo 1480560 7498493 := bstep (se 3 (by rfl) ⟨1405967, by rfl⟩ : syracuseStep 7498493 = 2811935) B2811935
theorem B4999967 : Blo 1480560 4999967 := bstep (se 1 (by rfl) ⟨3749975, by rfl⟩ : syracuseStep 4999967 = 7499951) B7499951
theorem B4942655 : Blo 1480560 4942655 := bstep (se 1 (by rfl) ⟨3706991, by rfl⟩ : syracuseStep 4942655 = 7413983) B7413983
theorem B9489257 : Blo 1480560 9489257 := bstep (se 2 (by rfl) ⟨3558471, by rfl⟩ : syracuseStep 9489257 = 7116943) B7116943
theorem B2223017 : Blo 1480560 2223017 := bstep (se 2 (by rfl) ⟨833631, by rfl⟩ : syracuseStep 2223017 = 1667263) B1667263
theorem B25652143 : Blo 1480560 25652143 := bstep (se 1 (by rfl) ⟨19239107, by rfl⟩ : syracuseStep 25652143 = 38478215) B38478215
theorem B6007891 : Blo 1480560 6007891 := bstep (se 1 (by rfl) ⟨4505918, by rfl⟩ : syracuseStep 6007891 = 9011837) B9011837
theorem B15404525 : Blo 1480560 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B5001641 : Blo 1480560 5001641 := bstep (se 2 (by rfl) ⟨1875615, by rfl⟩ : syracuseStep 5001641 = 3751231) B3751231
theorem B4002331 : Blo 1480560 4002331 := bstep (se 1 (by rfl) ⟨3001748, by rfl⟩ : syracuseStep 4002331 = 6003497) B6003497
theorem B28865447 : Blo 1480560 28865447 := bstep (se 1 (by rfl) ⟨21649085, by rfl⟩ : syracuseStep 28865447 = 43298171) B43298171
theorem B56923235 : Blo 1480560 56923235 := bstep (se 1 (by rfl) ⟨42692426, by rfl⟩ : syracuseStep 56923235 = 85384853) B85384853
theorem B11253329 : Blo 1480560 11253329 := bstep (se 2 (by rfl) ⟨4219998, by rfl⟩ : syracuseStep 11253329 = 8439997) B8439997
theorem B3331727 : Blo 1480560 3331727 := bstep (se 1 (by rfl) ⟨2498795, by rfl⟩ : syracuseStep 3331727 = 4997591) B4997591
theorem B12179483 : Blo 1480560 12179483 := bstep (se 1 (by rfl) ⟨9134612, by rfl⟩ : syracuseStep 12179483 = 18269225) B18269225
theorem B1480911 : Blo 1480560 1480911 := bstep (se 1 (by rfl) ⟨1110683, by rfl⟩ : syracuseStep 1480911 = 2221367) B2221367
theorem B13703377 : Blo 1480560 13703377 := bstep (se 2 (by rfl) ⟨5138766, by rfl⟩ : syracuseStep 13703377 = 10277533) B10277533
theorem B1480943 : Blo 1480560 1480943 := bstep (se 1 (by rfl) ⟨1110707, by rfl⟩ : syracuseStep 1480943 = 2221415) B2221415
theorem B11246039 : Blo 1480560 11246039 := bstep (se 1 (by rfl) ⟨8434529, by rfl⟩ : syracuseStep 11246039 = 16869059) B16869059
theorem B1481199 : Blo 1480560 1481199 := bstep (se 1 (by rfl) ⟨1110899, by rfl⟩ : syracuseStep 1481199 = 2221799) B2221799
theorem B4217471 : Blo 1480560 4217471 := bstep (se 1 (by rfl) ⟨3163103, by rfl⟩ : syracuseStep 4217471 = 6326207) B6326207
theorem B1481503 : Blo 1480560 1481503 := bstep (se 1 (by rfl) ⟨1111127, by rfl⟩ : syracuseStep 1481503 = 2222255) B2222255
theorem B1481575 : Blo 1480560 1481575 := bstep (se 1 (by rfl) ⟨1111181, by rfl⟩ : syracuseStep 1481575 = 2222363) B2222363
theorem B3333203 : Blo 1480560 3333203 := bstep (se 1 (by rfl) ⟨2499902, by rfl⟩ : syracuseStep 3333203 = 4999805) B4999805
theorem B3333275 : Blo 1480560 3333275 := bstep (se 1 (by rfl) ⟨2499956, by rfl⟩ : syracuseStep 3333275 = 4999913) B4999913
theorem B21347549 : Blo 1480560 21347549 := bstep (se 3 (by rfl) ⟨4002665, by rfl⟩ : syracuseStep 21347549 = 8005331) B8005331
theorem B3333599 : Blo 1480560 3333599 := bstep (se 1 (by rfl) ⟨2500199, by rfl⟩ : syracuseStep 3333599 = 5000399) B5000399
theorem B3333743 : Blo 1480560 3333743 := bstep (se 1 (by rfl) ⟨2500307, by rfl⟩ : syracuseStep 3333743 = 5000615) B5000615
theorem B4005487 : Blo 1480560 4005487 := bstep (se 1 (by rfl) ⟨3004115, by rfl⟩ : syracuseStep 4005487 = 6008231) B6008231
theorem B7118675 : Blo 1480560 7118675 := bstep (se 1 (by rfl) ⟨5339006, by rfl⟩ : syracuseStep 7118675 = 10678013) B10678013
theorem B3334427 : Blo 1480560 3334427 := bstep (se 1 (by rfl) ⟨2500820, by rfl⟩ : syracuseStep 3334427 = 5001641) B5001641
theorem B19243631 : Blo 1480560 19243631 := bstep (se 1 (by rfl) ⟨14432723, by rfl⟩ : syracuseStep 19243631 = 28865447) B28865447
theorem B2810857 : Blo 1480560 2810857 := bstep (se 2 (by rfl) ⟨1054071, by rfl⟩ : syracuseStep 2810857 = 2108143) B2108143
theorem B2221151 : Blo 1480560 2221151 := bstep (se 1 (by rfl) ⟨1665863, by rfl⟩ : syracuseStep 2221151 = 3331727) B3331727
theorem B8119655 : Blo 1480560 8119655 := bstep (se 1 (by rfl) ⟨6089741, by rfl⟩ : syracuseStep 8119655 = 12179483) B12179483
theorem B7497359 : Blo 1480560 7497359 := bstep (se 1 (by rfl) ⟨5623019, by rfl⟩ : syracuseStep 7497359 = 11246039) B11246039
theorem B16451275 : Blo 1480560 16451275 := bstep (se 1 (by rfl) ⟨12338456, by rfl⟩ : syracuseStep 16451275 = 24676913) B24676913
theorem B2811647 : Blo 1480560 2811647 := bstep (se 1 (by rfl) ⟨2108735, by rfl⟩ : syracuseStep 2811647 = 4217471) B4217471
theorem B4998995 : Blo 1480560 4998995 := bstep (se 1 (by rfl) ⟨3749246, by rfl⟩ : syracuseStep 4998995 = 7498493) B7498493
theorem B3295103 : Blo 1480560 3295103 := bstep (se 1 (by rfl) ⟨2471327, by rfl⟩ : syracuseStep 3295103 = 4942655) B4942655
theorem B6326171 : Blo 1480560 6326171 := bstep (se 1 (by rfl) ⟨4744628, by rfl⟩ : syracuseStep 6326171 = 9489257) B9489257
theorem B2222135 : Blo 1480560 2222135 := bstep (se 1 (by rfl) ⟨1666601, by rfl⟩ : syracuseStep 2222135 = 3333203) B3333203
theorem B2222183 : Blo 1480560 2222183 := bstep (se 1 (by rfl) ⟨1666637, by rfl⟩ : syracuseStep 2222183 = 3333275) B3333275
theorem B14231699 : Blo 1480560 14231699 := bstep (se 1 (by rfl) ⟨10673774, by rfl⟩ : syracuseStep 14231699 = 21347549) B21347549
theorem B2222399 : Blo 1480560 2222399 := bstep (se 1 (by rfl) ⟨1666799, by rfl⟩ : syracuseStep 2222399 = 3333599) B3333599
theorem B2222495 : Blo 1480560 2222495 := bstep (se 1 (by rfl) ⟨1666871, by rfl⟩ : syracuseStep 2222495 = 3333743) B3333743
theorem B4745783 : Blo 1480560 4745783 := bstep (se 1 (by rfl) ⟨3559337, by rfl⟩ : syracuseStep 4745783 = 7118675) B7118675
theorem B2222783 : Blo 1480560 2222783 := bstep (se 1 (by rfl) ⟨1667087, by rfl⟩ : syracuseStep 2222783 = 3334175) B3334175
theorem B1665823 : Blo 1480560 1665823 := bstep (se 1 (by rfl) ⟨1249367, by rfl⟩ : syracuseStep 1665823 = 2498735) B2498735
theorem B2222975 : Blo 1480560 2222975 := bstep (se 1 (by rfl) ⟨1667231, by rfl⟩ : syracuseStep 2222975 = 3334463) B3334463
theorem B7498655 : Blo 1480560 7498655 := bstep (se 1 (by rfl) ⟨5623991, by rfl⟩ : syracuseStep 7498655 = 11247983) B11247983
theorem B18271169 : Blo 1480560 18271169 := bstep (se 2 (by rfl) ⟨6851688, by rfl⟩ : syracuseStep 18271169 = 13703377) B13703377
theorem B2223047 : Blo 1480560 2223047 := bstep (se 1 (by rfl) ⟨1667285, by rfl⟩ : syracuseStep 2223047 = 3334571) B3334571
theorem B8227865 : Blo 1480560 8227865 := bstep (se 2 (by rfl) ⟨3085449, by rfl⟩ : syracuseStep 8227865 = 6170899) B6170899
theorem B5336441 : Blo 1480560 5336441 := bstep (se 2 (by rfl) ⟨2001165, by rfl⟩ : syracuseStep 5336441 = 4002331) B4002331
theorem B37948823 : Blo 1480560 37948823 := bstep (se 1 (by rfl) ⟨28461617, by rfl⟩ : syracuseStep 37948823 = 56923235) B56923235
theorem B4747423 : Blo 1480560 4747423 := bstep (se 1 (by rfl) ⟨3560567, by rfl⟩ : syracuseStep 4747423 = 7121135) B7121135
theorem B3748457 : Blo 1480560 3748457 := bstep (se 2 (by rfl) ⟨1405671, by rfl⟩ : syracuseStep 3748457 = 2811343) B2811343
theorem B136811429 : Blo 1480560 136811429 := bstep (se 4 (by rfl) ⟨12826071, by rfl⟩ : syracuseStep 136811429 = 25652143) B25652143
theorem B10269683 : Blo 1480560 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B1480575 : Blo 1480560 1480575 := bstep (se 1 (by rfl) ⟨1110431, by rfl⟩ : syracuseStep 1480575 = 2220863) B2220863
theorem B1874011 : Blo 1480560 1874011 := bstep (se 1 (by rfl) ⟨1405508, by rfl⟩ : syracuseStep 1874011 = 2811017) B2811017
theorem B9623719 : Blo 1480560 9623719 := bstep (se 1 (by rfl) ⟨7217789, by rfl⟩ : syracuseStep 9623719 = 14435579) B14435579
theorem B7502219 : Blo 1480560 7502219 := bstep (se 1 (by rfl) ⟨5626664, by rfl⟩ : syracuseStep 7502219 = 11253329) B11253329
theorem B1481447 : Blo 1480560 1481447 := bstep (se 1 (by rfl) ⟨1111085, by rfl⟩ : syracuseStep 1481447 = 2222171) B2222171
theorem B8010521 : Blo 1480560 8010521 := bstep (se 2 (by rfl) ⟨3003945, by rfl⟩ : syracuseStep 8010521 = 6007891) B6007891
theorem B3333311 : Blo 1480560 3333311 := bstep (se 1 (by rfl) ⟨2499983, by rfl⟩ : syracuseStep 3333311 = 4999967) B4999967
theorem B1482011 : Blo 1480560 1482011 := bstep (se 1 (by rfl) ⟨1111508, by rfl⟩ : syracuseStep 1482011 = 2223017) B2223017
theorem B5340649 : Blo 1480560 5340649 := bstep (se 2 (by rfl) ⟨2002743, by rfl⟩ : syracuseStep 5340649 = 4005487) B4005487
theorem B2498681 : Blo 1480560 2498681 := bstep (se 2 (by rfl) ⟨937005, by rfl⟩ : syracuseStep 2498681 = 1874011) B1874011
theorem B2498971 : Blo 1480560 2498971 := bstep (se 1 (by rfl) ⟨1874228, by rfl⟩ : syracuseStep 2498971 = 3748457) B3748457
theorem B2221097 : Blo 1480560 2221097 := bstep (se 2 (by rfl) ⟨832911, by rfl⟩ : syracuseStep 2221097 = 1665823) B1665823
theorem B4998239 : Blo 1480560 4998239 := bstep (se 1 (by rfl) ⟨3748679, by rfl⟩ : syracuseStep 4998239 = 7497359) B7497359
theorem B9487799 : Blo 1480560 9487799 := bstep (se 1 (by rfl) ⟨7115849, by rfl⟩ : syracuseStep 9487799 = 14231699) B14231699
theorem B51316349 : Blo 1480560 51316349 := bstep (se 3 (by rfl) ⟨9621815, by rfl⟩ : syracuseStep 51316349 = 19243631) B19243631
theorem B3163855 : Blo 1480560 3163855 := bstep (se 1 (by rfl) ⟨2372891, by rfl⟩ : syracuseStep 3163855 = 4745783) B4745783
theorem B4999103 : Blo 1480560 4999103 := bstep (se 1 (by rfl) ⟨3749327, by rfl⟩ : syracuseStep 4999103 = 7498655) B7498655
theorem B7120865 : Blo 1480560 7120865 := bstep (se 2 (by rfl) ⟨2670324, by rfl⟩ : syracuseStep 7120865 = 5340649) B5340649
theorem B2222207 : Blo 1480560 2222207 := bstep (se 1 (by rfl) ⟨1666655, by rfl⟩ : syracuseStep 2222207 = 3333311) B3333311
theorem B3557627 : Blo 1480560 3557627 := bstep (se 1 (by rfl) ⟨2668220, by rfl⟩ : syracuseStep 3557627 = 5336441) B5336441
theorem B25299215 : Blo 1480560 25299215 := bstep (se 1 (by rfl) ⟨18974411, by rfl⟩ : syracuseStep 25299215 = 37948823) B37948823
theorem B2222951 : Blo 1480560 2222951 := bstep (se 1 (by rfl) ⟨1667213, by rfl⟩ : syracuseStep 2222951 = 3334427) B3334427
theorem B12831625 : Blo 1480560 12831625 := bstep (se 2 (by rfl) ⟨4811859, by rfl⟩ : syracuseStep 12831625 = 9623719) B9623719
theorem B3747809 : Blo 1480560 3747809 := bstep (se 2 (by rfl) ⟨1405428, by rfl⟩ : syracuseStep 3747809 = 2810857) B2810857
theorem B35147765 : Blo 1480560 35147765 := bstep (se 5 (by rfl) ⟨1647551, by rfl⟩ : syracuseStep 35147765 = 3295103) B3295103
theorem B5001479 : Blo 1480560 5001479 := bstep (se 1 (by rfl) ⟨3751109, by rfl⟩ : syracuseStep 5001479 = 7502219) B7502219
theorem B5485243 : Blo 1480560 5485243 := bstep (se 1 (by rfl) ⟨4113932, by rfl⟩ : syracuseStep 5485243 = 8227865) B8227865
theorem B21935033 : Blo 1480560 21935033 := bstep (se 2 (by rfl) ⟨8225637, by rfl⟩ : syracuseStep 21935033 = 16451275) B16451275
theorem B6329897 : Blo 1480560 6329897 := bstep (se 2 (by rfl) ⟨2373711, by rfl⟩ : syracuseStep 6329897 = 4747423) B4747423
theorem B91207619 : Blo 1480560 91207619 := bstep (se 1 (by rfl) ⟨68405714, by rfl⟩ : syracuseStep 91207619 = 136811429) B136811429
theorem B6846455 : Blo 1480560 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B1480767 : Blo 1480560 1480767 := bstep (se 1 (by rfl) ⟨1110575, by rfl⟩ : syracuseStep 1480767 = 2221151) B2221151
theorem B5413103 : Blo 1480560 5413103 := bstep (se 1 (by rfl) ⟨4059827, by rfl⟩ : syracuseStep 5413103 = 8119655) B8119655
theorem B1874431 : Blo 1480560 1874431 := bstep (se 1 (by rfl) ⟨1405823, by rfl⟩ : syracuseStep 1874431 = 2811647) B2811647
theorem B3332663 : Blo 1480560 3332663 := bstep (se 1 (by rfl) ⟨2499497, by rfl⟩ : syracuseStep 3332663 = 4998995) B4998995
theorem B4217447 : Blo 1480560 4217447 := bstep (se 1 (by rfl) ⟨3163085, by rfl⟩ : syracuseStep 4217447 = 6326171) B6326171
theorem B1481423 : Blo 1480560 1481423 := bstep (se 1 (by rfl) ⟨1111067, by rfl⟩ : syracuseStep 1481423 = 2222135) B2222135
theorem B1481455 : Blo 1480560 1481455 := bstep (se 1 (by rfl) ⟨1111091, by rfl⟩ : syracuseStep 1481455 = 2222183) B2222183
theorem B1481599 : Blo 1480560 1481599 := bstep (se 1 (by rfl) ⟨1111199, by rfl⟩ : syracuseStep 1481599 = 2222399) B2222399
theorem B1481663 : Blo 1480560 1481663 := bstep (se 1 (by rfl) ⟨1111247, by rfl⟩ : syracuseStep 1481663 = 2222495) B2222495
theorem B1481855 : Blo 1480560 1481855 := bstep (se 1 (by rfl) ⟨1111391, by rfl⟩ : syracuseStep 1481855 = 2222783) B2222783
theorem B5340347 : Blo 1480560 5340347 := bstep (se 1 (by rfl) ⟨4005260, by rfl⟩ : syracuseStep 5340347 = 8010521) B8010521
theorem B1481983 : Blo 1480560 1481983 := bstep (se 1 (by rfl) ⟨1111487, by rfl⟩ : syracuseStep 1481983 = 2222975) B2222975
theorem B12180779 : Blo 1480560 12180779 := bstep (se 1 (by rfl) ⟨9135584, by rfl⟩ : syracuseStep 12180779 = 18271169) B18271169
theorem B1482031 : Blo 1480560 1482031 := bstep (se 1 (by rfl) ⟨1111523, by rfl⟩ : syracuseStep 1482031 = 2223047) B2223047
theorem B3334319 : Blo 1480560 3334319 := bstep (se 1 (by rfl) ⟨2500739, by rfl⟩ : syracuseStep 3334319 = 5001479) B5001479
theorem B14623355 : Blo 1480560 14623355 := bstep (se 1 (by rfl) ⟨10967516, by rfl⟩ : syracuseStep 14623355 = 21935033) B21935033
theorem B2499241 : Blo 1480560 2499241 := bstep (se 2 (by rfl) ⟨937215, by rfl⟩ : syracuseStep 2499241 = 1874431) B1874431
theorem B6325199 : Blo 1480560 6325199 := bstep (se 1 (by rfl) ⟨4743899, by rfl⟩ : syracuseStep 6325199 = 9487799) B9487799
theorem B4219931 : Blo 1480560 4219931 := bstep (se 1 (by rfl) ⟨3164948, by rfl⟩ : syracuseStep 4219931 = 6329897) B6329897
theorem B2221775 : Blo 1480560 2221775 := bstep (se 1 (by rfl) ⟨1666331, by rfl⟩ : syracuseStep 2221775 = 3332663) B3332663
theorem B8120519 : Blo 1480560 8120519 := bstep (se 1 (by rfl) ⟨6090389, by rfl⟩ : syracuseStep 8120519 = 12180779) B12180779
theorem B23431843 : Blo 1480560 23431843 := bstep (se 1 (by rfl) ⟨17573882, by rfl⟩ : syracuseStep 23431843 = 35147765) B35147765
theorem B1665787 : Blo 1480560 1665787 := bstep (se 1 (by rfl) ⟨1249340, by rfl⟩ : syracuseStep 1665787 = 2498681) B2498681
theorem B17108833 : Blo 1480560 17108833 := bstep (se 2 (by rfl) ⟨6415812, by rfl⟩ : syracuseStep 17108833 = 12831625) B12831625
theorem B60805079 : Blo 1480560 60805079 := bstep (se 1 (by rfl) ⟨45603809, by rfl⟩ : syracuseStep 60805079 = 91207619) B91207619
theorem B4747243 : Blo 1480560 4747243 := bstep (se 1 (by rfl) ⟨3560432, by rfl⟩ : syracuseStep 4747243 = 7120865) B7120865
theorem B3608735 : Blo 1480560 3608735 := bstep (se 1 (by rfl) ⟨2706551, by rfl⟩ : syracuseStep 3608735 = 5413103) B5413103
theorem B2371751 : Blo 1480560 2371751 := bstep (se 1 (by rfl) ⟨1778813, by rfl⟩ : syracuseStep 2371751 = 3557627) B3557627
theorem B136843597 : Blo 1480560 136843597 := bstep (se 3 (by rfl) ⟨25658174, by rfl⟩ : syracuseStep 136843597 = 51316349) B51316349
theorem B3560231 : Blo 1480560 3560231 := bstep (se 1 (by rfl) ⟨2670173, by rfl⟩ : syracuseStep 3560231 = 5340347) B5340347
theorem B18257213 : Blo 1480560 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B3331961 : Blo 1480560 3331961 := bstep (se 2 (by rfl) ⟨1249485, by rfl⟩ : syracuseStep 3331961 = 2498971) B2498971
theorem B1480731 : Blo 1480560 1480731 := bstep (se 1 (by rfl) ⟨1110548, by rfl⟩ : syracuseStep 1480731 = 2221097) B2221097
theorem B3332159 : Blo 1480560 3332159 := bstep (se 1 (by rfl) ⟨2499119, by rfl⟩ : syracuseStep 3332159 = 4998239) B4998239
theorem B7313657 : Blo 1480560 7313657 := bstep (se 2 (by rfl) ⟨2742621, by rfl⟩ : syracuseStep 7313657 = 5485243) B5485243
theorem B3332735 : Blo 1480560 3332735 := bstep (se 1 (by rfl) ⟨2499551, by rfl⟩ : syracuseStep 3332735 = 4999103) B4999103
theorem B1481471 : Blo 1480560 1481471 := bstep (se 1 (by rfl) ⟨1111103, by rfl⟩ : syracuseStep 1481471 = 2222207) B2222207
theorem B16866143 : Blo 1480560 16866143 := bstep (se 1 (by rfl) ⟨12649607, by rfl⟩ : syracuseStep 16866143 = 25299215) B25299215
theorem B11246525 : Blo 1480560 11246525 := bstep (se 3 (by rfl) ⟨2108723, by rfl⟩ : syracuseStep 11246525 = 4217447) B4217447
theorem B1481967 : Blo 1480560 1481967 := bstep (se 1 (by rfl) ⟨1111475, by rfl⟩ : syracuseStep 1481967 = 2222951) B2222951
theorem B4218473 : Blo 1480560 4218473 := bstep (se 2 (by rfl) ⟨1581927, by rfl⟩ : syracuseStep 4218473 = 3163855) B3163855
theorem B2498539 : Blo 1480560 2498539 := bstep (se 1 (by rfl) ⟨1873904, by rfl⟩ : syracuseStep 2498539 = 3747809) B3747809
theorem B1581167 : Blo 1480560 1581167 := bstep (se 1 (by rfl) ⟨1185875, by rfl⟩ : syracuseStep 1581167 = 2371751) B2371751
theorem B2221049 : Blo 1480560 2221049 := bstep (se 2 (by rfl) ⟨832893, by rfl⟩ : syracuseStep 2221049 = 1665787) B1665787
theorem B2221307 : Blo 1480560 2221307 := bstep (se 1 (by rfl) ⟨1665980, by rfl⟩ : syracuseStep 2221307 = 3331961) B3331961
theorem B2221439 : Blo 1480560 2221439 := bstep (se 1 (by rfl) ⟨1666079, by rfl⟩ : syracuseStep 2221439 = 3332159) B3332159
theorem B38995613 : Blo 1480560 38995613 := bstep (se 3 (by rfl) ⟨7311677, by rfl⟩ : syracuseStep 38995613 = 14623355) B14623355
theorem B2221823 : Blo 1480560 2221823 := bstep (se 1 (by rfl) ⟨1666367, by rfl⟩ : syracuseStep 2221823 = 3332735) B3332735
theorem B7497683 : Blo 1480560 7497683 := bstep (se 1 (by rfl) ⟨5623262, by rfl⟩ : syracuseStep 7497683 = 11246525) B11246525
theorem B2812315 : Blo 1480560 2812315 := bstep (se 1 (by rfl) ⟨2109236, by rfl⟩ : syracuseStep 2812315 = 4218473) B4218473
theorem B40536719 : Blo 1480560 40536719 := bstep (se 1 (by rfl) ⟨30402539, by rfl⟩ : syracuseStep 40536719 = 60805079) B60805079
theorem B2222879 : Blo 1480560 2222879 := bstep (se 1 (by rfl) ⟨1667159, by rfl⟩ : syracuseStep 2222879 = 3334319) B3334319
theorem B2813287 : Blo 1480560 2813287 := bstep (se 1 (by rfl) ⟨2109965, by rfl⟩ : syracuseStep 2813287 = 4219931) B4219931
theorem B11244095 : Blo 1480560 11244095 := bstep (se 1 (by rfl) ⟨8433071, by rfl⟩ : syracuseStep 11244095 = 16866143) B16866143
theorem B22811777 : Blo 1480560 22811777 := bstep (se 2 (by rfl) ⟨8554416, by rfl⟩ : syracuseStep 22811777 = 17108833) B17108833
theorem B3331385 : Blo 1480560 3331385 := bstep (se 2 (by rfl) ⟨1249269, by rfl⟩ : syracuseStep 3331385 = 2498539) B2498539
theorem B6329657 : Blo 1480560 6329657 := bstep (se 2 (by rfl) ⟨2373621, by rfl⟩ : syracuseStep 6329657 = 4747243) B4747243
theorem B182458129 : Blo 1480560 182458129 := bstep (se 2 (by rfl) ⟨68421798, by rfl⟩ : syracuseStep 182458129 = 136843597) B136843597
theorem B4216799 : Blo 1480560 4216799 := bstep (se 1 (by rfl) ⟨3162599, by rfl⟩ : syracuseStep 4216799 = 6325199) B6325199
theorem B12171475 : Blo 1480560 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B31242457 : Blo 1480560 31242457 := bstep (se 2 (by rfl) ⟨11715921, by rfl⟩ : syracuseStep 31242457 = 23431843) B23431843
theorem B3332321 : Blo 1480560 3332321 := bstep (se 2 (by rfl) ⟨1249620, by rfl⟩ : syracuseStep 3332321 = 2499241) B2499241
theorem B1481183 : Blo 1480560 1481183 := bstep (se 1 (by rfl) ⟨1110887, by rfl⟩ : syracuseStep 1481183 = 2221775) B2221775
theorem B5413679 : Blo 1480560 5413679 := bstep (se 1 (by rfl) ⟨4060259, by rfl⟩ : syracuseStep 5413679 = 8120519) B8120519
theorem B38493173 : Blo 1480560 38493173 := bstep (se 5 (by rfl) ⟨1804367, by rfl⟩ : syracuseStep 38493173 = 3608735) B3608735
theorem B9493949 : Blo 1480560 9493949 := bstep (se 3 (by rfl) ⟨1780115, by rfl⟩ : syracuseStep 9493949 = 3560231) B3560231
theorem B78012341 : Blo 1480560 78012341 := bstep (se 5 (by rfl) ⟨3656828, by rfl⟩ : syracuseStep 78012341 = 7313657) B7313657
theorem B41656609 : Blo 1480560 41656609 := bstep (se 2 (by rfl) ⟨15621228, by rfl⟩ : syracuseStep 41656609 = 31242457) B31242457
theorem B7496063 : Blo 1480560 7496063 := bstep (se 1 (by rfl) ⟨5622047, by rfl⟩ : syracuseStep 7496063 = 11244095) B11244095
theorem B2220923 : Blo 1480560 2220923 := bstep (se 1 (by rfl) ⟨1665692, by rfl⟩ : syracuseStep 2220923 = 3331385) B3331385
theorem B4219771 : Blo 1480560 4219771 := bstep (se 1 (by rfl) ⟨3164828, by rfl⟩ : syracuseStep 4219771 = 6329657) B6329657
theorem B64914533 : Blo 1480560 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B4998455 : Blo 1480560 4998455 := bstep (se 1 (by rfl) ⟨3748841, by rfl⟩ : syracuseStep 4998455 = 7497683) B7497683
theorem B2811199 : Blo 1480560 2811199 := bstep (se 1 (by rfl) ⟨2108399, by rfl⟩ : syracuseStep 2811199 = 4216799) B4216799
theorem B2221547 : Blo 1480560 2221547 := bstep (se 1 (by rfl) ⟨1666160, by rfl⟩ : syracuseStep 2221547 = 3332321) B3332321
theorem B15207851 : Blo 1480560 15207851 := bstep (se 1 (by rfl) ⟨11405888, by rfl⟩ : syracuseStep 15207851 = 22811777) B22811777
theorem B25997075 : Blo 1480560 25997075 := bstep (se 1 (by rfl) ⟨19497806, by rfl⟩ : syracuseStep 25997075 = 38995613) B38995613
theorem B3609119 : Blo 1480560 3609119 := bstep (se 1 (by rfl) ⟨2706839, by rfl⟩ : syracuseStep 3609119 = 5413679) B5413679
theorem B25662115 : Blo 1480560 25662115 := bstep (se 1 (by rfl) ⟨19246586, by rfl⟩ : syracuseStep 25662115 = 38493173) B38493173
theorem B6329299 : Blo 1480560 6329299 := bstep (se 1 (by rfl) ⟨4746974, by rfl⟩ : syracuseStep 6329299 = 9493949) B9493949
theorem B52008227 : Blo 1480560 52008227 := bstep (se 1 (by rfl) ⟨39006170, by rfl⟩ : syracuseStep 52008227 = 78012341) B78012341
theorem B4216445 : Blo 1480560 4216445 := bstep (se 3 (by rfl) ⟨790583, by rfl⟩ : syracuseStep 4216445 = 1581167) B1581167
theorem B3749753 : Blo 1480560 3749753 := bstep (se 2 (by rfl) ⟨1406157, by rfl⟩ : syracuseStep 3749753 = 2812315) B2812315
theorem B1480699 : Blo 1480560 1480699 := bstep (se 1 (by rfl) ⟨1110524, by rfl⟩ : syracuseStep 1480699 = 2221049) B2221049
theorem B1480871 : Blo 1480560 1480871 := bstep (se 1 (by rfl) ⟨1110653, by rfl⟩ : syracuseStep 1480871 = 2221307) B2221307
theorem B1480959 : Blo 1480560 1480959 := bstep (se 1 (by rfl) ⟨1110719, by rfl⟩ : syracuseStep 1480959 = 2221439) B2221439
theorem B1481215 : Blo 1480560 1481215 := bstep (se 1 (by rfl) ⟨1110911, by rfl⟩ : syracuseStep 1481215 = 2221823) B2221823
theorem B27024479 : Blo 1480560 27024479 := bstep (se 1 (by rfl) ⟨20268359, by rfl⟩ : syracuseStep 27024479 = 40536719) B40536719
theorem B3751049 : Blo 1480560 3751049 := bstep (se 2 (by rfl) ⟨1406643, by rfl⟩ : syracuseStep 3751049 = 2813287) B2813287
theorem B1481919 : Blo 1480560 1481919 := bstep (se 1 (by rfl) ⟨1111439, by rfl⟩ : syracuseStep 1481919 = 2222879) B2222879
theorem B243277505 : Blo 1480560 243277505 := bstep (se 2 (by rfl) ⟨91229064, by rfl⟩ : syracuseStep 243277505 = 182458129) B182458129
theorem B4997375 : Blo 1480560 4997375 := bstep (se 1 (by rfl) ⟨3748031, by rfl⟩ : syracuseStep 4997375 = 7496063) B7496063
theorem B55542145 : Blo 1480560 55542145 := bstep (se 2 (by rfl) ⟨20828304, by rfl⟩ : syracuseStep 55542145 = 41656609) B41656609
theorem B136864613 : Blo 1480560 136864613 := bstep (se 4 (by rfl) ⟨12831057, by rfl⟩ : syracuseStep 136864613 = 25662115) B25662115
theorem B2810963 : Blo 1480560 2810963 := bstep (se 1 (by rfl) ⟨2108222, by rfl⟩ : syracuseStep 2810963 = 4216445) B4216445
theorem B2499835 : Blo 1480560 2499835 := bstep (se 1 (by rfl) ⟨1874876, by rfl⟩ : syracuseStep 2499835 = 3749753) B3749753
theorem B8439065 : Blo 1480560 8439065 := bstep (se 2 (by rfl) ⟨3164649, by rfl⟩ : syracuseStep 8439065 = 6329299) B6329299
theorem B18016319 : Blo 1480560 18016319 := bstep (se 1 (by rfl) ⟨13512239, by rfl⟩ : syracuseStep 18016319 = 27024479) B27024479
theorem B2500699 : Blo 1480560 2500699 := bstep (se 1 (by rfl) ⟨1875524, by rfl⟩ : syracuseStep 2500699 = 3751049) B3751049
theorem B34672151 : Blo 1480560 34672151 := bstep (se 1 (by rfl) ⟨26004113, by rfl⟩ : syracuseStep 34672151 = 52008227) B52008227
theorem B3748265 : Blo 1480560 3748265 := bstep (se 2 (by rfl) ⟨1405599, by rfl⟩ : syracuseStep 3748265 = 2811199) B2811199
theorem B10138567 : Blo 1480560 10138567 := bstep (se 1 (by rfl) ⟨7603925, by rfl⟩ : syracuseStep 10138567 = 15207851) B15207851
theorem B17331383 : Blo 1480560 17331383 := bstep (se 1 (by rfl) ⟨12998537, by rfl⟩ : syracuseStep 17331383 = 25997075) B25997075
theorem B2406079 : Blo 1480560 2406079 := bstep (se 1 (by rfl) ⟨1804559, by rfl⟩ : syracuseStep 2406079 = 3609119) B3609119
theorem B1480615 : Blo 1480560 1480615 := bstep (se 1 (by rfl) ⟨1110461, by rfl⟩ : syracuseStep 1480615 = 2220923) B2220923
theorem B43276355 : Blo 1480560 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B3332303 : Blo 1480560 3332303 := bstep (se 1 (by rfl) ⟨2499227, by rfl⟩ : syracuseStep 3332303 = 4998455) B4998455
theorem B1481031 : Blo 1480560 1481031 := bstep (se 1 (by rfl) ⟨1110773, by rfl⟩ : syracuseStep 1481031 = 2221547) B2221547
theorem B5626361 : Blo 1480560 5626361 := bstep (se 2 (by rfl) ⟨2109885, by rfl⟩ : syracuseStep 5626361 = 4219771) B4219771
theorem B162185003 : Blo 1480560 162185003 := bstep (se 1 (by rfl) ⟨121638752, by rfl⟩ : syracuseStep 162185003 = 243277505) B243277505
theorem B3334265 : Blo 1480560 3334265 := bstep (se 2 (by rfl) ⟨1250349, by rfl⟩ : syracuseStep 3334265 = 2500699) B2500699
theorem B7495901 : Blo 1480560 7495901 := bstep (se 3 (by rfl) ⟨1405481, by rfl⟩ : syracuseStep 7495901 = 2810963) B2810963
theorem B2498843 : Blo 1480560 2498843 := bstep (se 1 (by rfl) ⟨1874132, by rfl⟩ : syracuseStep 2498843 = 3748265) B3748265
theorem B74056193 : Blo 1480560 74056193 := bstep (se 2 (by rfl) ⟨27771072, by rfl⟩ : syracuseStep 74056193 = 55542145) B55542145
theorem B13518089 : Blo 1480560 13518089 := bstep (se 2 (by rfl) ⟨5069283, by rfl⟩ : syracuseStep 13518089 = 10138567) B10138567
theorem B12010879 : Blo 1480560 12010879 := bstep (se 1 (by rfl) ⟨9008159, by rfl⟩ : syracuseStep 12010879 = 18016319) B18016319
theorem B2221535 : Blo 1480560 2221535 := bstep (se 1 (by rfl) ⟨1666151, by rfl⟩ : syracuseStep 2221535 = 3332303) B3332303
theorem B364972301 : Blo 1480560 364972301 := bstep (se 3 (by rfl) ⟨68432306, by rfl⟩ : syracuseStep 364972301 = 136864613) B136864613
theorem B11554255 : Blo 1480560 11554255 := bstep (se 1 (by rfl) ⟨8665691, by rfl⟩ : syracuseStep 11554255 = 17331383) B17331383
theorem B92459069 : Blo 1480560 92459069 := bstep (se 3 (by rfl) ⟨17336075, by rfl⟩ : syracuseStep 92459069 = 34672151) B34672151
theorem B3208105 : Blo 1480560 3208105 := bstep (se 2 (by rfl) ⟨1203039, by rfl⟩ : syracuseStep 3208105 = 2406079) B2406079
theorem B108123335 : Blo 1480560 108123335 := bstep (se 1 (by rfl) ⟨81092501, by rfl⟩ : syracuseStep 108123335 = 162185003) B162185003
theorem B3331583 : Blo 1480560 3331583 := bstep (se 1 (by rfl) ⟨2498687, by rfl⟩ : syracuseStep 3331583 = 4997375) B4997375
theorem B5626043 : Blo 1480560 5626043 := bstep (se 1 (by rfl) ⟨4219532, by rfl⟩ : syracuseStep 5626043 = 8439065) B8439065
theorem B28850903 : Blo 1480560 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B3333113 : Blo 1480560 3333113 := bstep (se 2 (by rfl) ⟨1249917, by rfl⟩ : syracuseStep 3333113 = 2499835) B2499835
theorem B3750907 : Blo 1480560 3750907 := bstep (se 1 (by rfl) ⟨2813180, by rfl⟩ : syracuseStep 3750907 = 5626361) B5626361
theorem B4997267 : Blo 1480560 4997267 := bstep (se 1 (by rfl) ⟨3747950, by rfl⟩ : syracuseStep 4997267 = 7495901) B7495901
theorem B72082223 : Blo 1480560 72082223 := bstep (se 1 (by rfl) ⟨54061667, by rfl⟩ : syracuseStep 72082223 = 108123335) B108123335
theorem B9012059 : Blo 1480560 9012059 := bstep (se 1 (by rfl) ⟨6759044, by rfl⟩ : syracuseStep 9012059 = 13518089) B13518089
theorem B2221055 : Blo 1480560 2221055 := bstep (se 1 (by rfl) ⟨1665791, by rfl⟩ : syracuseStep 2221055 = 3331583) B3331583
theorem B2222075 : Blo 1480560 2222075 := bstep (se 1 (by rfl) ⟨1666556, by rfl⟩ : syracuseStep 2222075 = 3333113) B3333113
theorem B61639379 : Blo 1480560 61639379 := bstep (se 1 (by rfl) ⟨46229534, by rfl⟩ : syracuseStep 61639379 = 92459069) B92459069
theorem B2222843 : Blo 1480560 2222843 := bstep (se 1 (by rfl) ⟨1667132, by rfl⟩ : syracuseStep 2222843 = 3334265) B3334265
theorem B1665895 : Blo 1480560 1665895 := bstep (se 1 (by rfl) ⟨1249421, by rfl⟩ : syracuseStep 1665895 = 2498843) B2498843
theorem B5001209 : Blo 1480560 5001209 := bstep (se 2 (by rfl) ⟨1875453, by rfl⟩ : syracuseStep 5001209 = 3750907) B3750907
theorem B243314867 : Blo 1480560 243314867 := bstep (se 1 (by rfl) ⟨182486150, by rfl⟩ : syracuseStep 243314867 = 364972301) B364972301
theorem B15405673 : Blo 1480560 15405673 := bstep (se 2 (by rfl) ⟨5777127, by rfl⟩ : syracuseStep 15405673 = 11554255) B11554255
theorem B17109893 : Blo 1480560 17109893 := bstep (se 4 (by rfl) ⟨1604052, by rfl⟩ : syracuseStep 17109893 = 3208105) B3208105
theorem B49370795 : Blo 1480560 49370795 := bstep (se 1 (by rfl) ⟨37028096, by rfl⟩ : syracuseStep 49370795 = 74056193) B74056193
theorem B1481023 : Blo 1480560 1481023 := bstep (se 1 (by rfl) ⟨1110767, by rfl⟩ : syracuseStep 1481023 = 2221535) B2221535
theorem B3750695 : Blo 1480560 3750695 := bstep (se 1 (by rfl) ⟨2813021, by rfl⟩ : syracuseStep 3750695 = 5626043) B5626043
theorem B19233935 : Blo 1480560 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B16014505 : Blo 1480560 16014505 := bstep (se 2 (by rfl) ⟨6005439, by rfl⟩ : syracuseStep 16014505 = 12010879) B12010879
theorem B162209911 : Blo 1480560 162209911 := bstep (se 1 (by rfl) ⟨121657433, by rfl⟩ : syracuseStep 162209911 = 243314867) B243314867
theorem B48054815 : Blo 1480560 48054815 := bstep (se 1 (by rfl) ⟨36041111, by rfl⟩ : syracuseStep 48054815 = 72082223) B72082223
theorem B2221193 : Blo 1480560 2221193 := bstep (se 2 (by rfl) ⟨832947, by rfl⟩ : syracuseStep 2221193 = 1665895) B1665895
theorem B41092919 : Blo 1480560 41092919 := bstep (se 1 (by rfl) ⟨30819689, by rfl⟩ : syracuseStep 41092919 = 61639379) B61639379
theorem B2500463 : Blo 1480560 2500463 := bstep (se 1 (by rfl) ⟨1875347, by rfl⟩ : syracuseStep 2500463 = 3750695) B3750695
theorem B12822623 : Blo 1480560 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B6008039 : Blo 1480560 6008039 := bstep (se 1 (by rfl) ⟨4506029, by rfl⟩ : syracuseStep 6008039 = 9012059) B9012059
theorem B11406595 : Blo 1480560 11406595 := bstep (se 1 (by rfl) ⟨8554946, by rfl⟩ : syracuseStep 11406595 = 17109893) B17109893
theorem B20540897 : Blo 1480560 20540897 := bstep (se 2 (by rfl) ⟨7702836, by rfl⟩ : syracuseStep 20540897 = 15405673) B15405673
theorem B21352673 : Blo 1480560 21352673 := bstep (se 2 (by rfl) ⟨8007252, by rfl⟩ : syracuseStep 21352673 = 16014505) B16014505
theorem B3331511 : Blo 1480560 3331511 := bstep (se 1 (by rfl) ⟨2498633, by rfl⟩ : syracuseStep 3331511 = 4997267) B4997267
theorem B1480703 : Blo 1480560 1480703 := bstep (se 1 (by rfl) ⟨1110527, by rfl⟩ : syracuseStep 1480703 = 2221055) B2221055
theorem B32913863 : Blo 1480560 32913863 := bstep (se 1 (by rfl) ⟨24685397, by rfl⟩ : syracuseStep 32913863 = 49370795) B49370795
theorem B1481383 : Blo 1480560 1481383 := bstep (se 1 (by rfl) ⟨1111037, by rfl⟩ : syracuseStep 1481383 = 2222075) B2222075
theorem B1481895 : Blo 1480560 1481895 := bstep (se 1 (by rfl) ⟨1111421, by rfl⟩ : syracuseStep 1481895 = 2222843) B2222843
theorem B3334139 : Blo 1480560 3334139 := bstep (se 1 (by rfl) ⟨2500604, by rfl⟩ : syracuseStep 3334139 = 5001209) B5001209
theorem B2221007 : Blo 1480560 2221007 := bstep (se 1 (by rfl) ⟨1665755, by rfl⟩ : syracuseStep 2221007 = 3331511) B3331511
theorem B27395279 : Blo 1480560 27395279 := bstep (se 1 (by rfl) ⟨20546459, by rfl⟩ : syracuseStep 27395279 = 41092919) B41092919
theorem B2222759 : Blo 1480560 2222759 := bstep (se 1 (by rfl) ⟨1667069, by rfl⟩ : syracuseStep 2222759 = 3334139) B3334139
theorem B216279881 : Blo 1480560 216279881 := bstep (se 2 (by rfl) ⟨81104955, by rfl⟩ : syracuseStep 216279881 = 162209911) B162209911
theorem B1666975 : Blo 1480560 1666975 := bstep (se 1 (by rfl) ⟨1250231, by rfl⟩ : syracuseStep 1666975 = 2500463) B2500463
theorem B8548415 : Blo 1480560 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B21942575 : Blo 1480560 21942575 := bstep (se 1 (by rfl) ⟨16456931, by rfl⟩ : syracuseStep 21942575 = 32913863) B32913863
theorem B15208793 : Blo 1480560 15208793 := bstep (se 2 (by rfl) ⟨5703297, by rfl⟩ : syracuseStep 15208793 = 11406595) B11406595
theorem B13693931 : Blo 1480560 13693931 := bstep (se 1 (by rfl) ⟨10270448, by rfl⟩ : syracuseStep 13693931 = 20540897) B20540897
theorem B14235115 : Blo 1480560 14235115 := bstep (se 1 (by rfl) ⟨10676336, by rfl⟩ : syracuseStep 14235115 = 21352673) B21352673
theorem B32036543 : Blo 1480560 32036543 := bstep (se 1 (by rfl) ⟨24027407, by rfl⟩ : syracuseStep 32036543 = 48054815) B48054815
theorem B1480795 : Blo 1480560 1480795 := bstep (se 1 (by rfl) ⟨1110596, by rfl⟩ : syracuseStep 1480795 = 2221193) B2221193
theorem B4005359 : Blo 1480560 4005359 := bstep (se 1 (by rfl) ⟨3004019, by rfl⟩ : syracuseStep 4005359 = 6008039) B6008039
theorem B21357695 : Blo 1480560 21357695 := bstep (se 1 (by rfl) ⟨16018271, by rfl⟩ : syracuseStep 21357695 = 32036543) B32036543
theorem B2222633 : Blo 1480560 2222633 := bstep (se 2 (by rfl) ⟨833487, by rfl⟩ : syracuseStep 2222633 = 1666975) B1666975
theorem B9129287 : Blo 1480560 9129287 := bstep (se 1 (by rfl) ⟨6846965, by rfl⟩ : syracuseStep 9129287 = 13693931) B13693931
theorem B18263519 : Blo 1480560 18263519 := bstep (se 1 (by rfl) ⟨13697639, by rfl⟩ : syracuseStep 18263519 = 27395279) B27395279
theorem B5698943 : Blo 1480560 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B14628383 : Blo 1480560 14628383 := bstep (se 1 (by rfl) ⟨10971287, by rfl⟩ : syracuseStep 14628383 = 21942575) B21942575
theorem B10139195 : Blo 1480560 10139195 := bstep (se 1 (by rfl) ⟨7604396, by rfl⟩ : syracuseStep 10139195 = 15208793) B15208793
theorem B1480671 : Blo 1480560 1480671 := bstep (se 1 (by rfl) ⟨1110503, by rfl⟩ : syracuseStep 1480671 = 2221007) B2221007
theorem B1481839 : Blo 1480560 1481839 := bstep (se 1 (by rfl) ⟨1111379, by rfl⟩ : syracuseStep 1481839 = 2222759) B2222759
theorem B144186587 : Blo 1480560 144186587 := bstep (se 1 (by rfl) ⟨108139940, by rfl⟩ : syracuseStep 144186587 = 216279881) B216279881
theorem B18980153 : Blo 1480560 18980153 := bstep (se 2 (by rfl) ⟨7117557, by rfl⟩ : syracuseStep 18980153 = 14235115) B14235115
theorem B2670239 : Blo 1480560 2670239 := bstep (se 1 (by rfl) ⟨2002679, by rfl⟩ : syracuseStep 2670239 = 4005359) B4005359
theorem B14238463 : Blo 1480560 14238463 := bstep (se 1 (by rfl) ⟨10678847, by rfl⟩ : syracuseStep 14238463 = 21357695) B21357695
theorem B6759463 : Blo 1480560 6759463 := bstep (se 1 (by rfl) ⟨5069597, by rfl⟩ : syracuseStep 6759463 = 10139195) B10139195
theorem B12175679 : Blo 1480560 12175679 := bstep (se 1 (by rfl) ⟨9131759, by rfl⟩ : syracuseStep 12175679 = 18263519) B18263519
theorem B1780159 : Blo 1480560 1780159 := bstep (se 1 (by rfl) ⟨1335119, by rfl⟩ : syracuseStep 1780159 = 2670239) B2670239
theorem B9752255 : Blo 1480560 9752255 := bstep (se 1 (by rfl) ⟨7314191, by rfl⟩ : syracuseStep 9752255 = 14628383) B14628383
theorem B12653435 : Blo 1480560 12653435 := bstep (se 1 (by rfl) ⟨9490076, by rfl⟩ : syracuseStep 12653435 = 18980153) B18980153
theorem B3799295 : Blo 1480560 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B1481755 : Blo 1480560 1481755 := bstep (se 1 (by rfl) ⟨1111316, by rfl⟩ : syracuseStep 1481755 = 2222633) B2222633
theorem B96124391 : Blo 1480560 96124391 := bstep (se 1 (by rfl) ⟨72093293, by rfl⟩ : syracuseStep 96124391 = 144186587) B144186587
theorem B6086191 : Blo 1480560 6086191 := bstep (se 1 (by rfl) ⟨4564643, by rfl⟩ : syracuseStep 6086191 = 9129287) B9129287
theorem B9012617 : Blo 1480560 9012617 := bstep (se 2 (by rfl) ⟨3379731, by rfl⟩ : syracuseStep 9012617 = 6759463) B6759463
theorem B2532863 : Blo 1480560 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B18984617 : Blo 1480560 18984617 := bstep (se 2 (by rfl) ⟨7119231, by rfl⟩ : syracuseStep 18984617 = 14238463) B14238463
theorem B8114921 : Blo 1480560 8114921 := bstep (se 2 (by rfl) ⟨3043095, by rfl⟩ : syracuseStep 8114921 = 6086191) B6086191
theorem B64082927 : Blo 1480560 64082927 := bstep (se 1 (by rfl) ⟨48062195, by rfl⟩ : syracuseStep 64082927 = 96124391) B96124391
theorem B6501503 : Blo 1480560 6501503 := bstep (se 1 (by rfl) ⟨4876127, by rfl⟩ : syracuseStep 6501503 = 9752255) B9752255
theorem B8435623 : Blo 1480560 8435623 := bstep (se 1 (by rfl) ⟨6326717, by rfl⟩ : syracuseStep 8435623 = 12653435) B12653435
theorem B2373545 : Blo 1480560 2373545 := bstep (se 2 (by rfl) ⟨890079, by rfl⟩ : syracuseStep 2373545 = 1780159) B1780159
theorem B8117119 : Blo 1480560 8117119 := bstep (se 1 (by rfl) ⟨6087839, by rfl⟩ : syracuseStep 8117119 = 12175679) B12175679
theorem B42721951 : Blo 1480560 42721951 := bstep (se 1 (by rfl) ⟨32041463, by rfl⟩ : syracuseStep 42721951 = 64082927) B64082927
theorem B4334335 : Blo 1480560 4334335 := bstep (se 1 (by rfl) ⟨3250751, by rfl⟩ : syracuseStep 4334335 = 6501503) B6501503
theorem B1688575 : Blo 1480560 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B10822825 : Blo 1480560 10822825 := bstep (se 2 (by rfl) ⟨4058559, by rfl⟩ : syracuseStep 10822825 = 8117119) B8117119
theorem B1582363 : Blo 1480560 1582363 := bstep (se 1 (by rfl) ⟨1186772, by rfl⟩ : syracuseStep 1582363 = 2373545) B2373545
theorem B5409947 : Blo 1480560 5409947 := bstep (se 1 (by rfl) ⟨4057460, by rfl⟩ : syracuseStep 5409947 = 8114921) B8114921
theorem B6008411 : Blo 1480560 6008411 := bstep (se 1 (by rfl) ⟨4506308, by rfl⟩ : syracuseStep 6008411 = 9012617) B9012617
theorem B12656411 : Blo 1480560 12656411 := bstep (se 1 (by rfl) ⟨9492308, by rfl⟩ : syracuseStep 12656411 = 18984617) B18984617
theorem B11247497 : Blo 1480560 11247497 := bstep (se 2 (by rfl) ⟨4217811, by rfl⟩ : syracuseStep 11247497 = 8435623) B8435623
theorem B14426525 : Blo 1480560 14426525 := bstep (se 3 (by rfl) ⟨2704973, by rfl⟩ : syracuseStep 14426525 = 5409947) B5409947
theorem B57721733 : Blo 1480560 57721733 := bstep (se 4 (by rfl) ⟨5411412, by rfl⟩ : syracuseStep 57721733 = 10822825) B10822825
theorem B7498331 : Blo 1480560 7498331 := bstep (se 1 (by rfl) ⟨5623748, by rfl⟩ : syracuseStep 7498331 = 11247497) B11247497
theorem B92465813 : Blo 1480560 92465813 := bstep (se 6 (by rfl) ⟨2167167, by rfl⟩ : syracuseStep 92465813 = 4334335) B4334335
theorem B56962601 : Blo 1480560 56962601 := bstep (se 2 (by rfl) ⟨21360975, by rfl⟩ : syracuseStep 56962601 = 42721951) B42721951
theorem B2109817 : Blo 1480560 2109817 := bstep (se 2 (by rfl) ⟨791181, by rfl⟩ : syracuseStep 2109817 = 1582363) B1582363
theorem B2251433 : Blo 1480560 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B4005607 : Blo 1480560 4005607 := bstep (se 1 (by rfl) ⟨3004205, by rfl⟩ : syracuseStep 4005607 = 6008411) B6008411
theorem B8437607 : Blo 1480560 8437607 := bstep (se 1 (by rfl) ⟨6328205, by rfl⟩ : syracuseStep 8437607 = 12656411) B12656411
theorem B9617683 : Blo 1480560 9617683 := bstep (se 1 (by rfl) ⟨7213262, by rfl⟩ : syracuseStep 9617683 = 14426525) B14426525
theorem B4998887 : Blo 1480560 4998887 := bstep (se 1 (by rfl) ⟨3749165, by rfl⟩ : syracuseStep 4998887 = 7498331) B7498331
theorem B38481155 : Blo 1480560 38481155 := bstep (se 1 (by rfl) ⟨28860866, by rfl⟩ : syracuseStep 38481155 = 57721733) B57721733
theorem B11252357 : Blo 1480560 11252357 := bstep (se 4 (by rfl) ⟨1054908, by rfl⟩ : syracuseStep 11252357 = 2109817) B2109817
theorem B37975067 : Blo 1480560 37975067 := bstep (se 1 (by rfl) ⟨28481300, by rfl⟩ : syracuseStep 37975067 = 56962601) B56962601
theorem B5625071 : Blo 1480560 5625071 := bstep (se 1 (by rfl) ⟨4218803, by rfl⟩ : syracuseStep 5625071 = 8437607) B8437607
theorem B61643875 : Blo 1480560 61643875 := bstep (se 1 (by rfl) ⟨46232906, by rfl⟩ : syracuseStep 61643875 = 92465813) B92465813
theorem B6003821 : Blo 1480560 6003821 := bstep (se 3 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 6003821 = 2251433) B2251433
theorem B5340809 : Blo 1480560 5340809 := bstep (se 2 (by rfl) ⟨2002803, by rfl⟩ : syracuseStep 5340809 = 4005607) B4005607
theorem B82191833 : Blo 1480560 82191833 := bstep (se 2 (by rfl) ⟨30821937, by rfl⟩ : syracuseStep 82191833 = 61643875) B61643875
theorem B12823577 : Blo 1480560 12823577 := bstep (se 2 (by rfl) ⟨4808841, by rfl⟩ : syracuseStep 12823577 = 9617683) B9617683
theorem B25316711 : Blo 1480560 25316711 := bstep (se 1 (by rfl) ⟨18987533, by rfl⟩ : syracuseStep 25316711 = 37975067) B37975067
theorem B4002547 : Blo 1480560 4002547 := bstep (se 1 (by rfl) ⟨3001910, by rfl⟩ : syracuseStep 4002547 = 6003821) B6003821
theorem B25654103 : Blo 1480560 25654103 := bstep (se 1 (by rfl) ⟨19240577, by rfl⟩ : syracuseStep 25654103 = 38481155) B38481155
theorem B3560539 : Blo 1480560 3560539 := bstep (se 1 (by rfl) ⟨2670404, by rfl⟩ : syracuseStep 3560539 = 5340809) B5340809
theorem B7501571 : Blo 1480560 7501571 := bstep (se 1 (by rfl) ⟨5626178, by rfl⟩ : syracuseStep 7501571 = 11252357) B11252357
theorem B3750047 : Blo 1480560 3750047 := bstep (se 1 (by rfl) ⟨2812535, by rfl⟩ : syracuseStep 3750047 = 5625071) B5625071
theorem B3332591 : Blo 1480560 3332591 := bstep (se 1 (by rfl) ⟨2499443, by rfl⟩ : syracuseStep 3332591 = 4998887) B4998887
theorem B2500031 : Blo 1480560 2500031 := bstep (se 1 (by rfl) ⟨1875023, by rfl⟩ : syracuseStep 2500031 = 3750047) B3750047
theorem B2221727 : Blo 1480560 2221727 := bstep (se 1 (by rfl) ⟨1666295, by rfl⟩ : syracuseStep 2221727 = 3332591) B3332591
theorem B16877807 : Blo 1480560 16877807 := bstep (se 1 (by rfl) ⟨12658355, by rfl⟩ : syracuseStep 16877807 = 25316711) B25316711
theorem B136784821 : Blo 1480560 136784821 := bstep (se 5 (by rfl) ⟨6411788, by rfl⟩ : syracuseStep 136784821 = 12823577) B12823577
theorem B5336729 : Blo 1480560 5336729 := bstep (se 2 (by rfl) ⟨2001273, by rfl⟩ : syracuseStep 5336729 = 4002547) B4002547
theorem B5001047 : Blo 1480560 5001047 := bstep (se 1 (by rfl) ⟨3750785, by rfl⟩ : syracuseStep 5001047 = 7501571) B7501571
theorem B4747385 : Blo 1480560 4747385 := bstep (se 2 (by rfl) ⟨1780269, by rfl⟩ : syracuseStep 4747385 = 3560539) B3560539
theorem B17102735 : Blo 1480560 17102735 := bstep (se 1 (by rfl) ⟨12827051, by rfl⟩ : syracuseStep 17102735 = 25654103) B25654103
theorem B54794555 : Blo 1480560 54794555 := bstep (se 1 (by rfl) ⟨41095916, by rfl⟩ : syracuseStep 54794555 = 82191833) B82191833
theorem B182379761 : Blo 1480560 182379761 := bstep (se 2 (by rfl) ⟨68392410, by rfl⟩ : syracuseStep 182379761 = 136784821) B136784821
theorem B36529703 : Blo 1480560 36529703 := bstep (se 1 (by rfl) ⟨27397277, by rfl⟩ : syracuseStep 36529703 = 54794555) B54794555
theorem B3557819 : Blo 1480560 3557819 := bstep (se 1 (by rfl) ⟨2668364, by rfl⟩ : syracuseStep 3557819 = 5336729) B5336729
theorem B3164923 : Blo 1480560 3164923 := bstep (se 1 (by rfl) ⟨2373692, by rfl⟩ : syracuseStep 3164923 = 4747385) B4747385
theorem B1666687 : Blo 1480560 1666687 := bstep (se 1 (by rfl) ⟨1250015, by rfl⟩ : syracuseStep 1666687 = 2500031) B2500031
theorem B11251871 : Blo 1480560 11251871 := bstep (se 1 (by rfl) ⟨8438903, by rfl⟩ : syracuseStep 11251871 = 16877807) B16877807
theorem B1481151 : Blo 1480560 1481151 := bstep (se 1 (by rfl) ⟨1110863, by rfl⟩ : syracuseStep 1481151 = 2221727) B2221727
theorem B11401823 : Blo 1480560 11401823 := bstep (se 1 (by rfl) ⟨8551367, by rfl⟩ : syracuseStep 11401823 = 17102735) B17102735
theorem B3334031 : Blo 1480560 3334031 := bstep (se 1 (by rfl) ⟨2500523, by rfl⟩ : syracuseStep 3334031 = 5001047) B5001047
theorem B121586507 : Blo 1480560 121586507 := bstep (se 1 (by rfl) ⟨91189880, by rfl⟩ : syracuseStep 121586507 = 182379761) B182379761
theorem B4219897 : Blo 1480560 4219897 := bstep (se 2 (by rfl) ⟨1582461, by rfl⟩ : syracuseStep 4219897 = 3164923) B3164923
theorem B2222249 : Blo 1480560 2222249 := bstep (se 2 (by rfl) ⟨833343, by rfl⟩ : syracuseStep 2222249 = 1666687) B1666687
theorem B2222687 : Blo 1480560 2222687 := bstep (se 1 (by rfl) ⟨1667015, by rfl⟩ : syracuseStep 2222687 = 3334031) B3334031
theorem B2371879 : Blo 1480560 2371879 := bstep (se 1 (by rfl) ⟨1778909, by rfl⟩ : syracuseStep 2371879 = 3557819) B3557819
theorem B7501247 : Blo 1480560 7501247 := bstep (se 1 (by rfl) ⟨5625935, by rfl⟩ : syracuseStep 7501247 = 11251871) B11251871
theorem B24353135 : Blo 1480560 24353135 := bstep (se 1 (by rfl) ⟨18264851, by rfl⟩ : syracuseStep 24353135 = 36529703) B36529703
theorem B7601215 : Blo 1480560 7601215 := bstep (se 1 (by rfl) ⟨5700911, by rfl⟩ : syracuseStep 7601215 = 11401823) B11401823
theorem B3162505 : Blo 1480560 3162505 := bstep (se 2 (by rfl) ⟨1185939, by rfl⟩ : syracuseStep 3162505 = 2371879) B2371879
theorem B10134953 : Blo 1480560 10134953 := bstep (se 2 (by rfl) ⟨3800607, by rfl⟩ : syracuseStep 10134953 = 7601215) B7601215
theorem B5000831 : Blo 1480560 5000831 := bstep (se 1 (by rfl) ⟨3750623, by rfl⟩ : syracuseStep 5000831 = 7501247) B7501247
theorem B81057671 : Blo 1480560 81057671 := bstep (se 1 (by rfl) ⟨60793253, by rfl⟩ : syracuseStep 81057671 = 121586507) B121586507
theorem B5626529 : Blo 1480560 5626529 := bstep (se 2 (by rfl) ⟨2109948, by rfl⟩ : syracuseStep 5626529 = 4219897) B4219897
theorem B1481499 : Blo 1480560 1481499 := bstep (se 1 (by rfl) ⟨1111124, by rfl⟩ : syracuseStep 1481499 = 2222249) B2222249
theorem B16235423 : Blo 1480560 16235423 := bstep (se 1 (by rfl) ⟨12176567, by rfl⟩ : syracuseStep 16235423 = 24353135) B24353135
theorem B1481791 : Blo 1480560 1481791 := bstep (se 1 (by rfl) ⟨1111343, by rfl⟩ : syracuseStep 1481791 = 2222687) B2222687
theorem B10823615 : Blo 1480560 10823615 := bstep (se 1 (by rfl) ⟨8117711, by rfl⟩ : syracuseStep 10823615 = 16235423) B16235423
theorem B54038447 : Blo 1480560 54038447 := bstep (se 1 (by rfl) ⟨40528835, by rfl⟩ : syracuseStep 54038447 = 81057671) B81057671
theorem B4216673 : Blo 1480560 4216673 := bstep (se 2 (by rfl) ⟨1581252, by rfl⟩ : syracuseStep 4216673 = 3162505) B3162505
theorem B6756635 : Blo 1480560 6756635 := bstep (se 1 (by rfl) ⟨5067476, by rfl⟩ : syracuseStep 6756635 = 10134953) B10134953
theorem B3751019 : Blo 1480560 3751019 := bstep (se 1 (by rfl) ⟨2813264, by rfl⟩ : syracuseStep 3751019 = 5626529) B5626529
theorem B3333887 : Blo 1480560 3333887 := bstep (se 1 (by rfl) ⟨2500415, by rfl⟩ : syracuseStep 3333887 = 5000831) B5000831
theorem B2811115 : Blo 1480560 2811115 := bstep (se 1 (by rfl) ⟨2108336, by rfl⟩ : syracuseStep 2811115 = 4216673) B4216673
theorem B2500679 : Blo 1480560 2500679 := bstep (se 1 (by rfl) ⟨1875509, by rfl⟩ : syracuseStep 2500679 = 3751019) B3751019
theorem B2222591 : Blo 1480560 2222591 := bstep (se 1 (by rfl) ⟨1666943, by rfl⟩ : syracuseStep 2222591 = 3333887) B3333887
theorem B36025631 : Blo 1480560 36025631 := bstep (se 1 (by rfl) ⟨27019223, by rfl⟩ : syracuseStep 36025631 = 54038447) B54038447
theorem B7215743 : Blo 1480560 7215743 := bstep (se 1 (by rfl) ⟨5411807, by rfl⟩ : syracuseStep 7215743 = 10823615) B10823615
theorem B4504423 : Blo 1480560 4504423 := bstep (se 1 (by rfl) ⟨3378317, by rfl⟩ : syracuseStep 4504423 = 6756635) B6756635
theorem B6005897 : Blo 1480560 6005897 := bstep (se 2 (by rfl) ⟨2252211, by rfl⟩ : syracuseStep 6005897 = 4504423) B4504423
theorem B4810495 : Blo 1480560 4810495 := bstep (se 1 (by rfl) ⟨3607871, by rfl⟩ : syracuseStep 4810495 = 7215743) B7215743
theorem B1667119 : Blo 1480560 1667119 := bstep (se 1 (by rfl) ⟨1250339, by rfl⟩ : syracuseStep 1667119 = 2500679) B2500679
theorem B3748153 : Blo 1480560 3748153 := bstep (se 2 (by rfl) ⟨1405557, by rfl⟩ : syracuseStep 3748153 = 2811115) B2811115
theorem B24017087 : Blo 1480560 24017087 := bstep (se 1 (by rfl) ⟨18012815, by rfl⟩ : syracuseStep 24017087 = 36025631) B36025631
theorem B1481727 : Blo 1480560 1481727 := bstep (se 1 (by rfl) ⟨1111295, by rfl⟩ : syracuseStep 1481727 = 2222591) B2222591
theorem B4997537 : Blo 1480560 4997537 := bstep (se 2 (by rfl) ⟨1874076, by rfl⟩ : syracuseStep 4997537 = 3748153) B3748153
theorem B64045565 : Blo 1480560 64045565 := bstep (se 3 (by rfl) ⟨12008543, by rfl⟩ : syracuseStep 64045565 = 24017087) B24017087
theorem B2222825 : Blo 1480560 2222825 := bstep (se 2 (by rfl) ⟨833559, by rfl⟩ : syracuseStep 2222825 = 1667119) B1667119
theorem B4003931 : Blo 1480560 4003931 := bstep (se 1 (by rfl) ⟨3002948, by rfl⟩ : syracuseStep 4003931 = 6005897) B6005897
theorem B6413993 : Blo 1480560 6413993 := bstep (se 2 (by rfl) ⟨2405247, by rfl⟩ : syracuseStep 6413993 = 4810495) B4810495
theorem B42697043 : Blo 1480560 42697043 := bstep (se 1 (by rfl) ⟨32022782, by rfl⟩ : syracuseStep 42697043 = 64045565) B64045565
theorem B3331691 : Blo 1480560 3331691 := bstep (se 1 (by rfl) ⟨2498768, by rfl⟩ : syracuseStep 3331691 = 4997537) B4997537
theorem B2669287 : Blo 1480560 2669287 := bstep (se 1 (by rfl) ⟨2001965, by rfl⟩ : syracuseStep 2669287 = 4003931) B4003931
theorem B1481883 : Blo 1480560 1481883 := bstep (se 1 (by rfl) ⟨1111412, by rfl⟩ : syracuseStep 1481883 = 2222825) B2222825
theorem B4275995 : Blo 1480560 4275995 := bstep (se 1 (by rfl) ⟨3206996, by rfl⟩ : syracuseStep 4275995 = 6413993) B6413993
theorem B2221127 : Blo 1480560 2221127 := bstep (se 1 (by rfl) ⟨1665845, by rfl⟩ : syracuseStep 2221127 = 3331691) B3331691
theorem B3559049 : Blo 1480560 3559049 := bstep (se 2 (by rfl) ⟨1334643, by rfl⟩ : syracuseStep 3559049 = 2669287) B2669287
theorem B28464695 : Blo 1480560 28464695 := bstep (se 1 (by rfl) ⟨21348521, by rfl⟩ : syracuseStep 28464695 = 42697043) B42697043
theorem B11402653 : Blo 1480560 11402653 := bstep (se 3 (by rfl) ⟨2137997, by rfl⟩ : syracuseStep 11402653 = 4275995) B4275995
theorem B18976463 : Blo 1480560 18976463 := bstep (se 1 (by rfl) ⟨14232347, by rfl⟩ : syracuseStep 18976463 = 28464695) B28464695
theorem B2372699 : Blo 1480560 2372699 := bstep (se 1 (by rfl) ⟨1779524, by rfl⟩ : syracuseStep 2372699 = 3559049) B3559049
theorem B1480751 : Blo 1480560 1480751 := bstep (se 1 (by rfl) ⟨1110563, by rfl⟩ : syracuseStep 1480751 = 2221127) B2221127
theorem B15203537 : Blo 1480560 15203537 := bstep (se 2 (by rfl) ⟨5701326, by rfl⟩ : syracuseStep 15203537 = 11402653) B11402653
theorem B10135691 : Blo 1480560 10135691 := bstep (se 1 (by rfl) ⟨7601768, by rfl⟩ : syracuseStep 10135691 = 15203537) B15203537
theorem B12650975 : Blo 1480560 12650975 := bstep (se 1 (by rfl) ⟨9488231, by rfl⟩ : syracuseStep 12650975 = 18976463) B18976463
theorem B6327197 : Blo 1480560 6327197 := bstep (se 3 (by rfl) ⟨1186349, by rfl⟩ : syracuseStep 6327197 = 2372699) B2372699
theorem B8433983 : Blo 1480560 8433983 := bstep (se 1 (by rfl) ⟨6325487, by rfl⟩ : syracuseStep 8433983 = 12650975) B12650975
theorem B6757127 : Blo 1480560 6757127 := bstep (se 1 (by rfl) ⟨5067845, by rfl⟩ : syracuseStep 6757127 = 10135691) B10135691
theorem B4218131 : Blo 1480560 4218131 := bstep (se 1 (by rfl) ⟨3163598, by rfl⟩ : syracuseStep 4218131 = 6327197) B6327197
theorem B2812087 : Blo 1480560 2812087 := bstep (se 1 (by rfl) ⟨2109065, by rfl⟩ : syracuseStep 2812087 = 4218131) B4218131
theorem B5622655 : Blo 1480560 5622655 := bstep (se 1 (by rfl) ⟨4216991, by rfl⟩ : syracuseStep 5622655 = 8433983) B8433983
theorem B4504751 : Blo 1480560 4504751 := bstep (se 1 (by rfl) ⟨3378563, by rfl⟩ : syracuseStep 4504751 = 6757127) B6757127
theorem B7496873 : Blo 1480560 7496873 := bstep (se 2 (by rfl) ⟨2811327, by rfl⟩ : syracuseStep 7496873 = 5622655) B5622655
theorem B3003167 : Blo 1480560 3003167 := bstep (se 1 (by rfl) ⟨2252375, by rfl⟩ : syracuseStep 3003167 = 4504751) B4504751
theorem B3749449 : Blo 1480560 3749449 := bstep (se 2 (by rfl) ⟨1406043, by rfl⟩ : syracuseStep 3749449 = 2812087) B2812087
theorem B4997915 : Blo 1480560 4997915 := bstep (se 1 (by rfl) ⟨3748436, by rfl⟩ : syracuseStep 4997915 = 7496873) B7496873
theorem B4999265 : Blo 1480560 4999265 := bstep (se 2 (by rfl) ⟨1874724, by rfl⟩ : syracuseStep 4999265 = 3749449) B3749449
theorem B8008445 : Blo 1480560 8008445 := bstep (se 3 (by rfl) ⟨1501583, by rfl⟩ : syracuseStep 8008445 = 3003167) B3003167
theorem B5338963 : Blo 1480560 5338963 := bstep (se 1 (by rfl) ⟨4004222, by rfl⟩ : syracuseStep 5338963 = 8008445) B8008445
theorem B3331943 : Blo 1480560 3331943 := bstep (se 1 (by rfl) ⟨2498957, by rfl⟩ : syracuseStep 3331943 = 4997915) B4997915
theorem B3332843 : Blo 1480560 3332843 := bstep (se 1 (by rfl) ⟨2499632, by rfl⟩ : syracuseStep 3332843 = 4999265) B4999265
theorem B2221295 : Blo 1480560 2221295 := bstep (se 1 (by rfl) ⟨1665971, by rfl⟩ : syracuseStep 2221295 = 3331943) B3331943
theorem B2221895 : Blo 1480560 2221895 := bstep (se 1 (by rfl) ⟨1666421, by rfl⟩ : syracuseStep 2221895 = 3332843) B3332843
theorem B7118617 : Blo 1480560 7118617 := bstep (se 2 (by rfl) ⟨2669481, by rfl⟩ : syracuseStep 7118617 = 5338963) B5338963
theorem B9491489 : Blo 1480560 9491489 := bstep (se 2 (by rfl) ⟨3559308, by rfl⟩ : syracuseStep 9491489 = 7118617) B7118617
theorem B1480863 : Blo 1480560 1480863 := bstep (se 1 (by rfl) ⟨1110647, by rfl⟩ : syracuseStep 1480863 = 2221295) B2221295
theorem B1481263 : Blo 1480560 1481263 := bstep (se 1 (by rfl) ⟨1110947, by rfl⟩ : syracuseStep 1481263 = 2221895) B2221895
theorem B6327659 : Blo 1480560 6327659 := bstep (se 1 (by rfl) ⟨4745744, by rfl⟩ : syracuseStep 6327659 = 9491489) B9491489
theorem B4218439 : Blo 1480560 4218439 := bstep (se 1 (by rfl) ⟨3163829, by rfl⟩ : syracuseStep 4218439 = 6327659) B6327659
theorem B5624585 : Blo 1480560 5624585 := bstep (se 2 (by rfl) ⟨2109219, by rfl⟩ : syracuseStep 5624585 = 4218439) B4218439
theorem B3749723 : Blo 1480560 3749723 := bstep (se 1 (by rfl) ⟨2812292, by rfl⟩ : syracuseStep 3749723 = 5624585) B5624585
theorem B2499815 : Blo 1480560 2499815 := bstep (se 1 (by rfl) ⟨1874861, by rfl⟩ : syracuseStep 2499815 = 3749723) B3749723
theorem B1666543 : Blo 1480560 1666543 := bstep (se 1 (by rfl) ⟨1249907, by rfl⟩ : syracuseStep 1666543 = 2499815) B2499815
theorem B2222057 : Blo 1480560 2222057 := bstep (se 2 (by rfl) ⟨833271, by rfl⟩ : syracuseStep 2222057 = 1666543) B1666543
theorem B1481371 : Blo 1480560 1481371 := bstep (se 1 (by rfl) ⟨1111028, by rfl⟩ : syracuseStep 1481371 = 2222057) B2222057

theorem C0 (j : ℕ) (h1 : 370140 ≤ j) (h2 : j ≤ 370514) : Blo 1480560 (4 * j + 3) := by
  interval_cases j
  · exact B1480563
  · exact B1480567
  · exact B1480571
  · exact B1480575
  · exact B1480579
  · exact B1480583
  · exact B1480587
  · exact B1480591
  · exact B1480595
  · exact B1480599
  · exact B1480603
  · exact B1480607
  · exact B1480611
  · exact B1480615
  · exact B1480619
  · exact B1480623
  · exact B1480627
  · exact B1480631
  · exact B1480635
  · exact B1480639
  · exact B1480643
  · exact B1480647
  · exact B1480651
  · exact B1480655
  · exact B1480659
  · exact B1480663
  · exact B1480667
  · exact B1480671
  · exact B1480675
  · exact B1480679
  · exact B1480683
  · exact B1480687
  · exact B1480691
  · exact B1480695
  · exact B1480699
  · exact B1480703
  · exact B1480707
  · exact B1480711
  · exact B1480715
  · exact B1480719
  · exact B1480723
  · exact B1480727
  · exact B1480731
  · exact B1480735
  · exact B1480739
  · exact B1480743
  · exact B1480747
  · exact B1480751
  · exact B1480755
  · exact B1480759
  · exact B1480763
  · exact B1480767
  · exact B1480771
  · exact B1480775
  · exact B1480779
  · exact B1480783
  · exact B1480787
  · exact B1480791
  · exact B1480795
  · exact B1480799
  · exact B1480803
  · exact B1480807
  · exact B1480811
  · exact B1480815
  · exact B1480819
  · exact B1480823
  · exact B1480827
  · exact B1480831
  · exact B1480835
  · exact B1480839
  · exact B1480843
  · exact B1480847
  · exact B1480851
  · exact B1480855
  · exact B1480859
  · exact B1480863
  · exact B1480867
  · exact B1480871
  · exact B1480875
  · exact B1480879
  · exact B1480883
  · exact B1480887
  · exact B1480891
  · exact B1480895
  · exact B1480899
  · exact B1480903
  · exact B1480907
  · exact B1480911
  · exact B1480915
  · exact B1480919
  · exact B1480923
  · exact B1480927
  · exact B1480931
  · exact B1480935
  · exact B1480939
  · exact B1480943
  · exact B1480947
  · exact B1480951
  · exact B1480955
  · exact B1480959
  · exact B1480963
  · exact B1480967
  · exact B1480971
  · exact B1480975
  · exact B1480979
  · exact B1480983
  · exact B1480987
  · exact B1480991
  · exact B1480995
  · exact B1480999
  · exact B1481003
  · exact B1481007
  · exact B1481011
  · exact B1481015
  · exact B1481019
  · exact B1481023
  · exact B1481027
  · exact B1481031
  · exact B1481035
  · exact B1481039
  · exact B1481043
  · exact B1481047
  · exact B1481051
  · exact B1481055
  · exact B1481059
  · exact B1481063
  · exact B1481067
  · exact B1481071
  · exact B1481075
  · exact B1481079
  · exact B1481083
  · exact B1481087
  · exact B1481091
  · exact B1481095
  · exact B1481099
  · exact B1481103
  · exact B1481107
  · exact B1481111
  · exact B1481115
  · exact B1481119
  · exact B1481123
  · exact B1481127
  · exact B1481131
  · exact B1481135
  · exact B1481139
  · exact B1481143
  · exact B1481147
  · exact B1481151
  · exact B1481155
  · exact B1481159
  · exact B1481163
  · exact B1481167
  · exact B1481171
  · exact B1481175
  · exact B1481179
  · exact B1481183
  · exact B1481187
  · exact B1481191
  · exact B1481195
  · exact B1481199
  · exact B1481203
  · exact B1481207
  · exact B1481211
  · exact B1481215
  · exact B1481219
  · exact B1481223
  · exact B1481227
  · exact B1481231
  · exact B1481235
  · exact B1481239
  · exact B1481243
  · exact B1481247
  · exact B1481251
  · exact B1481255
  · exact B1481259
  · exact B1481263
  · exact B1481267
  · exact B1481271
  · exact B1481275
  · exact B1481279
  · exact B1481283
  · exact B1481287
  · exact B1481291
  · exact B1481295
  · exact B1481299
  · exact B1481303
  · exact B1481307
  · exact B1481311
  · exact B1481315
  · exact B1481319
  · exact B1481323
  · exact B1481327
  · exact B1481331
  · exact B1481335
  · exact B1481339
  · exact B1481343
  · exact B1481347
  · exact B1481351
  · exact B1481355
  · exact B1481359
  · exact B1481363
  · exact B1481367
  · exact B1481371
  · exact B1481375
  · exact B1481379
  · exact B1481383
  · exact B1481387
  · exact B1481391
  · exact B1481395
  · exact B1481399
  · exact B1481403
  · exact B1481407
  · exact B1481411
  · exact B1481415
  · exact B1481419
  · exact B1481423
  · exact B1481427
  · exact B1481431
  · exact B1481435
  · exact B1481439
  · exact B1481443
  · exact B1481447
  · exact B1481451
  · exact B1481455
  · exact B1481459
  · exact B1481463
  · exact B1481467
  · exact B1481471
  · exact B1481475
  · exact B1481479
  · exact B1481483
  · exact B1481487
  · exact B1481491
  · exact B1481495
  · exact B1481499
  · exact B1481503
  · exact B1481507
  · exact B1481511
  · exact B1481515
  · exact B1481519
  · exact B1481523
  · exact B1481527
  · exact B1481531
  · exact B1481535
  · exact B1481539
  · exact B1481543
  · exact B1481547
  · exact B1481551
  · exact B1481555
  · exact B1481559
  · exact B1481563
  · exact B1481567
  · exact B1481571
  · exact B1481575
  · exact B1481579
  · exact B1481583
  · exact B1481587
  · exact B1481591
  · exact B1481595
  · exact B1481599
  · exact B1481603
  · exact B1481607
  · exact B1481611
  · exact B1481615
  · exact B1481619
  · exact B1481623
  · exact B1481627
  · exact B1481631
  · exact B1481635
  · exact B1481639
  · exact B1481643
  · exact B1481647
  · exact B1481651
  · exact B1481655
  · exact B1481659
  · exact B1481663
  · exact B1481667
  · exact B1481671
  · exact B1481675
  · exact B1481679
  · exact B1481683
  · exact B1481687
  · exact B1481691
  · exact B1481695
  · exact B1481699
  · exact B1481703
  · exact B1481707
  · exact B1481711
  · exact B1481715
  · exact B1481719
  · exact B1481723
  · exact B1481727
  · exact B1481731
  · exact B1481735
  · exact B1481739
  · exact B1481743
  · exact B1481747
  · exact B1481751
  · exact B1481755
  · exact B1481759
  · exact B1481763
  · exact B1481767
  · exact B1481771
  · exact B1481775
  · exact B1481779
  · exact B1481783
  · exact B1481787
  · exact B1481791
  · exact B1481795
  · exact B1481799
  · exact B1481803
  · exact B1481807
  · exact B1481811
  · exact B1481815
  · exact B1481819
  · exact B1481823
  · exact B1481827
  · exact B1481831
  · exact B1481835
  · exact B1481839
  · exact B1481843
  · exact B1481847
  · exact B1481851
  · exact B1481855
  · exact B1481859
  · exact B1481863
  · exact B1481867
  · exact B1481871
  · exact B1481875
  · exact B1481879
  · exact B1481883
  · exact B1481887
  · exact B1481891
  · exact B1481895
  · exact B1481899
  · exact B1481903
  · exact B1481907
  · exact B1481911
  · exact B1481915
  · exact B1481919
  · exact B1481923
  · exact B1481927
  · exact B1481931
  · exact B1481935
  · exact B1481939
  · exact B1481943
  · exact B1481947
  · exact B1481951
  · exact B1481955
  · exact B1481959
  · exact B1481963
  · exact B1481967
  · exact B1481971
  · exact B1481975
  · exact B1481979
  · exact B1481983
  · exact B1481987
  · exact B1481991
  · exact B1481995
  · exact B1481999
  · exact B1482003
  · exact B1482007
  · exact B1482011
  · exact B1482015
  · exact B1482019
  · exact B1482023
  · exact B1482027
  · exact B1482031
  · exact B1482035
  · exact B1482039
  · exact B1482043
  · exact B1482047
  · exact B1482051
  · exact B1482055
  · exact B1482059

theorem solution (m : ℕ) (hlo : 1480560 ≤ m) (hhi : m ≤ 1482060) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 370140 ≤ j := by omega
    have hj2 : j ≤ 370514 := by omega
    have hb : Blo 1480560 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
