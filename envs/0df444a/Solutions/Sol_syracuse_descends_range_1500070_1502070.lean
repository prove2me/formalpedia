-- Prove2me | solution 1 for syracuse_descends_range_1500070_1502070
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:47:48.545328+00:00
-- url     : https://prove2.me/submissions/560de925-00e5-455c-a087-e930f521fd9d

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


theorem B2252813 : Blo 1500070 2252813 := bbase (se 3 (by rfl) ⟨422402, by rfl⟩ : syracuseStep 2252813 = 844805) (by norm_num)
theorem B1925141 : Blo 1500070 1925141 := bbase (se 6 (by rfl) ⟨45120, by rfl⟩ : syracuseStep 1925141 = 90241) (by norm_num)
theorem B10821653 : Blo 1500070 10821653 := bbase (se 6 (by rfl) ⟨253632, by rfl⟩ : syracuseStep 10821653 = 507265) (by norm_num)
theorem B1687585 : Blo 1500070 1687585 := bbase (se 2 (by rfl) ⟨632844, by rfl⟩ : syracuseStep 1687585 = 1265689) (by norm_num)
theorem B2252837 : Blo 1500070 2252837 := bbase (se 4 (by rfl) ⟨211203, by rfl⟩ : syracuseStep 2252837 = 422407) (by norm_num)
theorem B2850869 : Blo 1500070 2850869 := bbase (se 5 (by rfl) ⟨133634, by rfl⟩ : syracuseStep 2850869 = 267269) (by norm_num)
theorem B2252861 : Blo 1500070 2252861 := bbase (se 3 (by rfl) ⟨422411, by rfl⟩ : syracuseStep 2252861 = 844823) (by norm_num)
theorem B1687621 : Blo 1500070 1687621 := bbase (se 4 (by rfl) ⟨158214, by rfl⟩ : syracuseStep 1687621 = 316429) (by norm_num)
theorem B2531405 : Blo 1500070 2531405 := bbase (se 3 (by rfl) ⟨474638, by rfl⟩ : syracuseStep 2531405 = 949277) (by norm_num)
theorem B1925201 : Blo 1500070 1925201 := bbase (se 2 (by rfl) ⟨721950, by rfl⟩ : syracuseStep 1925201 = 1443901) (by norm_num)
theorem B2252885 : Blo 1500070 2252885 := bbase (se 8 (by rfl) ⟨13200, by rfl⟩ : syracuseStep 2252885 = 26401) (by norm_num)
theorem B3375197 : Blo 1500070 3375197 := bbase (se 3 (by rfl) ⟨632849, by rfl⟩ : syracuseStep 3375197 = 1265699) (by norm_num)
theorem B1687657 : Blo 1500070 1687657 := bbase (se 2 (by rfl) ⟨632871, by rfl⟩ : syracuseStep 1687657 = 1265743) (by norm_num)
theorem B2703469 : Blo 1500070 2703469 := bbase (se 3 (by rfl) ⟨506900, by rfl⟩ : syracuseStep 2703469 = 1013801) (by norm_num)
theorem B2252909 : Blo 1500070 2252909 := bbase (se 3 (by rfl) ⟨422420, by rfl⟩ : syracuseStep 2252909 = 844841) (by norm_num)
theorem B2252933 : Blo 1500070 2252933 := bbase (se 4 (by rfl) ⟨211212, by rfl⟩ : syracuseStep 2252933 = 422425) (by norm_num)
theorem B1687693 : Blo 1500070 1687693 := bbase (se 3 (by rfl) ⟨316442, by rfl⟩ : syracuseStep 1687693 = 632885) (by norm_num)
theorem B1900685 : Blo 1500070 1900685 := bbase (se 3 (by rfl) ⟨356378, by rfl⟩ : syracuseStep 1900685 = 712757) (by norm_num)
theorem B2252957 : Blo 1500070 2252957 := bbase (se 3 (by rfl) ⟨422429, by rfl⟩ : syracuseStep 2252957 = 844859) (by norm_num)
theorem B3375269 : Blo 1500070 3375269 := bbase (se 4 (by rfl) ⟨316431, by rfl⟩ : syracuseStep 3375269 = 632863) (by norm_num)
theorem B1802413 : Blo 1500070 1802413 := bbase (se 3 (by rfl) ⟨337952, by rfl⟩ : syracuseStep 1802413 = 675905) (by norm_num)
theorem B1687729 : Blo 1500070 1687729 := bbase (se 2 (by rfl) ⟨632898, by rfl⟩ : syracuseStep 1687729 = 1265797) (by norm_num)
theorem B1802417 : Blo 1500070 1802417 := bbase (se 2 (by rfl) ⟨675906, by rfl⟩ : syracuseStep 1802417 = 1351813) (by norm_num)
theorem B4276405 : Blo 1500070 4276405 := bbase (se 5 (by rfl) ⟨200456, by rfl⟩ : syracuseStep 4276405 = 400913) (by norm_num)
theorem B3801269 : Blo 1500070 3801269 := bbase (se 5 (by rfl) ⟨178184, by rfl⟩ : syracuseStep 3801269 = 356369) (by norm_num)
theorem B2252981 : Blo 1500070 2252981 := bbase (se 5 (by rfl) ⟨105608, by rfl⟩ : syracuseStep 2252981 = 211217) (by norm_num)
theorem B2851013 : Blo 1500070 2851013 := bbase (se 4 (by rfl) ⟨267282, by rfl⟩ : syracuseStep 2851013 = 534565) (by norm_num)
theorem B1900741 : Blo 1500070 1900741 := bbase (se 4 (by rfl) ⟨178194, by rfl⟩ : syracuseStep 1900741 = 356389) (by norm_num)
theorem B2531533 : Blo 1500070 2531533 := bbase (se 3 (by rfl) ⟨474662, by rfl⟩ : syracuseStep 2531533 = 949325) (by norm_num)
theorem B2253005 : Blo 1500070 2253005 := bbase (se 3 (by rfl) ⟨422438, by rfl⟩ : syracuseStep 2253005 = 844877) (by norm_num)
theorem B1687765 : Blo 1500070 1687765 := bbase (se 7 (by rfl) ⟨19778, by rfl⟩ : syracuseStep 1687765 = 39557) (by norm_num)
theorem B9126101 : Blo 1500070 9126101 := bbase (se 7 (by rfl) ⟨106946, by rfl⟩ : syracuseStep 9126101 = 213893) (by norm_num)
theorem B4808933 : Blo 1500070 4808933 := bbase (se 4 (by rfl) ⟨450837, by rfl⟩ : syracuseStep 4808933 = 901675) (by norm_num)
theorem B2253029 : Blo 1500070 2253029 := bbase (se 4 (by rfl) ⟨211221, by rfl⟩ : syracuseStep 2253029 = 422443) (by norm_num)
theorem B3375341 : Blo 1500070 3375341 := bbase (se 3 (by rfl) ⟨632876, by rfl⟩ : syracuseStep 3375341 = 1265753) (by norm_num)
theorem B1687801 : Blo 1500070 1687801 := bbase (se 2 (by rfl) ⟨632925, by rfl⟩ : syracuseStep 1687801 = 1265851) (by norm_num)
theorem B2253053 : Blo 1500070 2253053 := bbase (se 3 (by rfl) ⟨422447, by rfl⟩ : syracuseStep 2253053 = 844895) (by norm_num)
theorem B3604757 : Blo 1500070 3604757 := bbase (se 6 (by rfl) ⟨84486, by rfl⟩ : syracuseStep 3604757 = 168973) (by norm_num)
theorem B2253077 : Blo 1500070 2253077 := bbase (se 6 (by rfl) ⟨52806, by rfl⟩ : syracuseStep 2253077 = 105613) (by norm_num)
theorem B1687837 : Blo 1500070 1687837 := bbase (se 3 (by rfl) ⟨316469, by rfl⟩ : syracuseStep 1687837 = 632939) (by norm_num)
theorem B2531621 : Blo 1500070 2531621 := bbase (se 4 (by rfl) ⟨237339, by rfl⟩ : syracuseStep 2531621 = 474679) (by norm_num)
theorem B1900837 : Blo 1500070 1900837 := bbase (se 4 (by rfl) ⟨178203, by rfl⟩ : syracuseStep 1900837 = 356407) (by norm_num)
theorem B2253101 : Blo 1500070 2253101 := bbase (se 3 (by rfl) ⟨422456, by rfl⟩ : syracuseStep 2253101 = 844913) (by norm_num)
theorem B3375413 : Blo 1500070 3375413 := bbase (se 5 (by rfl) ⟨158222, by rfl⟩ : syracuseStep 3375413 = 316445) (by norm_num)
theorem B1687873 : Blo 1500070 1687873 := bbase (se 2 (by rfl) ⟨632952, by rfl⟩ : syracuseStep 1687873 = 1265905) (by norm_num)
theorem B32440661 : Blo 1500070 32440661 := bbase (se 10 (by rfl) ⟨47520, by rfl⟩ : syracuseStep 32440661 = 95041) (by norm_num)
theorem B8552789 : Blo 1500070 8552789 := bbase (se 10 (by rfl) ⟨12528, by rfl⟩ : syracuseStep 8552789 = 25057) (by norm_num)
theorem B6414677 : Blo 1500070 6414677 := bbase (se 10 (by rfl) ⟨9396, by rfl⟩ : syracuseStep 6414677 = 18793) (by norm_num)
theorem B1687909 : Blo 1500070 1687909 := bbase (se 4 (by rfl) ⟨158241, by rfl⟩ : syracuseStep 1687909 = 316483) (by norm_num)
theorem B3375485 : Blo 1500070 3375485 := bbase (se 3 (by rfl) ⟨632903, by rfl⟩ : syracuseStep 3375485 = 1265807) (by norm_num)
theorem B1687945 : Blo 1500070 1687945 := bbase (se 2 (by rfl) ⟨632979, by rfl⟩ : syracuseStep 1687945 = 1265959) (by norm_num)
theorem B2531749 : Blo 1500070 2531749 := bbase (se 4 (by rfl) ⟨237351, by rfl⟩ : syracuseStep 2531749 = 474703) (by norm_num)
theorem B1687981 : Blo 1500070 1687981 := bbase (se 3 (by rfl) ⟨316496, by rfl⟩ : syracuseStep 1687981 = 632993) (by norm_num)
theorem B5063093 : Blo 1500070 5063093 := bbase (se 5 (by rfl) ⟨237332, by rfl⟩ : syracuseStep 5063093 = 474665) (by norm_num)
theorem B3375557 : Blo 1500070 3375557 := bbase (se 4 (by rfl) ⟨316458, by rfl⟩ : syracuseStep 3375557 = 632917) (by norm_num)
theorem B1688017 : Blo 1500070 1688017 := bbase (se 2 (by rfl) ⟨633006, by rfl⟩ : syracuseStep 1688017 = 1266013) (by norm_num)
theorem B1901009 : Blo 1500070 1901009 := bbase (se 2 (by rfl) ⟨712878, by rfl⟩ : syracuseStep 1901009 = 1425757) (by norm_num)
theorem B2851301 : Blo 1500070 2851301 := bbase (se 4 (by rfl) ⟨267309, by rfl⟩ : syracuseStep 2851301 = 534619) (by norm_num)
theorem B1688053 : Blo 1500070 1688053 := bbase (se 5 (by rfl) ⟨79127, by rfl⟩ : syracuseStep 1688053 = 158255) (by norm_num)
theorem B2531837 : Blo 1500070 2531837 := bbase (se 3 (by rfl) ⟨474719, by rfl⟩ : syracuseStep 2531837 = 949439) (by norm_num)
theorem B3375629 : Blo 1500070 3375629 := bbase (se 3 (by rfl) ⟨632930, by rfl⟩ : syracuseStep 3375629 = 1265861) (by norm_num)
theorem B3801613 : Blo 1500070 3801613 := bbase (se 3 (by rfl) ⟨712802, by rfl⟩ : syracuseStep 3801613 = 1425605) (by norm_num)
theorem B1688089 : Blo 1500070 1688089 := bbase (se 2 (by rfl) ⟨633033, by rfl⟩ : syracuseStep 1688089 = 1266067) (by norm_num)
theorem B2138653 : Blo 1500070 2138653 := bbase (se 3 (by rfl) ⟨400997, by rfl⟩ : syracuseStep 2138653 = 801995) (by norm_num)
theorem B1712677 : Blo 1500070 1712677 := bbase (se 4 (by rfl) ⟨160563, by rfl⟩ : syracuseStep 1712677 = 321127) (by norm_num)
theorem B1688125 : Blo 1500070 1688125 := bbase (se 3 (by rfl) ⟨316523, by rfl⟩ : syracuseStep 1688125 = 633047) (by norm_num)
theorem B1802821 : Blo 1500070 1802821 := bbase (se 4 (by rfl) ⟨169014, by rfl⟩ : syracuseStep 1802821 = 338029) (by norm_num)
theorem B3375701 : Blo 1500070 3375701 := bbase (se 8 (by rfl) ⟨19779, by rfl⟩ : syracuseStep 3375701 = 39559) (by norm_num)
theorem B1688161 : Blo 1500070 1688161 := bbase (se 2 (by rfl) ⟨633060, by rfl⟩ : syracuseStep 1688161 = 1266121) (by norm_num)
theorem B2531965 : Blo 1500070 2531965 := bbase (se 3 (by rfl) ⟨474743, by rfl⟩ : syracuseStep 2531965 = 949487) (by norm_num)
theorem B3801725 : Blo 1500070 3801725 := bbase (se 3 (by rfl) ⟨712823, by rfl⟩ : syracuseStep 3801725 = 1425647) (by norm_num)
theorem B2851453 : Blo 1500070 2851453 := bbase (se 3 (by rfl) ⟨534647, by rfl⟩ : syracuseStep 2851453 = 1069295) (by norm_num)
theorem B1688197 : Blo 1500070 1688197 := bbase (se 4 (by rfl) ⟨158268, by rfl⟩ : syracuseStep 1688197 = 316537) (by norm_num)
theorem B7602821 : Blo 1500070 7602821 := bbase (se 4 (by rfl) ⟨712764, by rfl⟩ : syracuseStep 7602821 = 1425529) (by norm_num)
theorem B3375773 : Blo 1500070 3375773 := bbase (se 3 (by rfl) ⟨632957, by rfl⟩ : syracuseStep 3375773 = 1265915) (by norm_num)
theorem B1688233 : Blo 1500070 1688233 := bbase (se 2 (by rfl) ⟨633087, by rfl⟩ : syracuseStep 1688233 = 1266175) (by norm_num)
theorem B1688269 : Blo 1500070 1688269 := bbase (se 3 (by rfl) ⟨316550, by rfl⟩ : syracuseStep 1688269 = 633101) (by norm_num)
theorem B2532053 : Blo 1500070 2532053 := bbase (se 7 (by rfl) ⟨29672, by rfl⟩ : syracuseStep 2532053 = 59345) (by norm_num)
theorem B11403989 : Blo 1500070 11403989 := bbase (se 7 (by rfl) ⟨133640, by rfl⟩ : syracuseStep 11403989 = 267281) (by norm_num)
theorem B3375845 : Blo 1500070 3375845 := bbase (se 4 (by rfl) ⟨316485, by rfl⟩ : syracuseStep 3375845 = 632971) (by norm_num)
theorem B1688305 : Blo 1500070 1688305 := bbase (se 2 (by rfl) ⟨633114, by rfl⟩ : syracuseStep 1688305 = 1266229) (by norm_num)
theorem B1688341 : Blo 1500070 1688341 := bbase (se 6 (by rfl) ⟨39570, by rfl⟩ : syracuseStep 1688341 = 79141) (by norm_num)
theorem B3375917 : Blo 1500070 3375917 := bbase (se 3 (by rfl) ⟨632984, by rfl⟩ : syracuseStep 3375917 = 1265969) (by norm_num)
theorem B1688377 : Blo 1500070 1688377 := bbase (se 2 (by rfl) ⟨633141, by rfl⟩ : syracuseStep 1688377 = 1266283) (by norm_num)
theorem B3801917 : Blo 1500070 3801917 := bbase (se 3 (by rfl) ⟨712859, by rfl⟩ : syracuseStep 3801917 = 1425719) (by norm_num)
theorem B2532181 : Blo 1500070 2532181 := bbase (se 9 (by rfl) ⟨7418, by rfl⟩ : syracuseStep 2532181 = 14837) (by norm_num)
theorem B1688413 : Blo 1500070 1688413 := bbase (se 3 (by rfl) ⟨316577, by rfl⟩ : syracuseStep 1688413 = 633155) (by norm_num)
theorem B5063525 : Blo 1500070 5063525 := bbase (se 4 (by rfl) ⟨474705, by rfl⟩ : syracuseStep 5063525 = 949411) (by norm_num)
theorem B3375989 : Blo 1500070 3375989 := bbase (se 5 (by rfl) ⟨158249, by rfl⟩ : syracuseStep 3375989 = 316499) (by norm_num)
theorem B1688449 : Blo 1500070 1688449 := bbase (se 2 (by rfl) ⟨633168, by rfl⟩ : syracuseStep 1688449 = 1266337) (by norm_num)
theorem B1688485 : Blo 1500070 1688485 := bbase (se 4 (by rfl) ⟨158295, by rfl⟩ : syracuseStep 1688485 = 316591) (by norm_num)
theorem B2532269 : Blo 1500070 2532269 := bbase (se 3 (by rfl) ⟨474800, by rfl⟩ : syracuseStep 2532269 = 949601) (by norm_num)
theorem B3376061 : Blo 1500070 3376061 := bbase (se 3 (by rfl) ⟨633011, by rfl⟩ : syracuseStep 3376061 = 1266023) (by norm_num)
theorem B1688521 : Blo 1500070 1688521 := bbase (se 2 (by rfl) ⟨633195, by rfl⟩ : syracuseStep 1688521 = 1266391) (by norm_num)
theorem B1688557 : Blo 1500070 1688557 := bbase (se 3 (by rfl) ⟨316604, by rfl⟩ : syracuseStep 1688557 = 633209) (by norm_num)
theorem B3376133 : Blo 1500070 3376133 := bbase (se 4 (by rfl) ⟨316512, by rfl⟩ : syracuseStep 3376133 = 633025) (by norm_num)
theorem B1688593 : Blo 1500070 1688593 := bbase (se 2 (by rfl) ⟨633222, by rfl⟩ : syracuseStep 1688593 = 1266445) (by norm_num)
theorem B7595045 : Blo 1500070 7595045 := bbase (se 4 (by rfl) ⟨712035, by rfl⟩ : syracuseStep 7595045 = 1424071) (by norm_num)
theorem B2532397 : Blo 1500070 2532397 := bbase (se 3 (by rfl) ⟨474824, by rfl⟩ : syracuseStep 2532397 = 949649) (by norm_num)
theorem B1688629 : Blo 1500070 1688629 := bbase (se 5 (by rfl) ⟨79154, by rfl⟩ : syracuseStep 1688629 = 158309) (by norm_num)
theorem B3376205 : Blo 1500070 3376205 := bbase (se 3 (by rfl) ⟨633038, by rfl⟩ : syracuseStep 3376205 = 1266077) (by norm_num)
theorem B5407829 : Blo 1500070 5407829 := bbase (se 8 (by rfl) ⟨31686, by rfl⟩ : syracuseStep 5407829 = 63373) (by norm_num)
theorem B17572949 : Blo 1500070 17572949 := bbase (se 8 (by rfl) ⟨102966, by rfl⟩ : syracuseStep 17572949 = 205933) (by norm_num)
theorem B1688665 : Blo 1500070 1688665 := bbase (se 2 (by rfl) ⟨633249, by rfl⟩ : syracuseStep 1688665 = 1266499) (by norm_num)
theorem B11396213 : Blo 1500070 11396213 := bbase (se 5 (by rfl) ⟨534197, by rfl⟩ : syracuseStep 11396213 = 1068395) (by norm_num)
theorem B1688701 : Blo 1500070 1688701 := bbase (se 3 (by rfl) ⟨316631, by rfl⟩ : syracuseStep 1688701 = 633263) (by norm_num)
theorem B2532485 : Blo 1500070 2532485 := bbase (se 4 (by rfl) ⟨237420, by rfl⟩ : syracuseStep 2532485 = 474841) (by norm_num)
theorem B3376277 : Blo 1500070 3376277 := bbase (se 6 (by rfl) ⟨79131, by rfl⟩ : syracuseStep 3376277 = 158263) (by norm_num)
theorem B1688737 : Blo 1500070 1688737 := bbase (se 2 (by rfl) ⟨633276, by rfl⟩ : syracuseStep 1688737 = 1266553) (by norm_num)
theorem B1688773 : Blo 1500070 1688773 := bbase (se 4 (by rfl) ⟨158322, by rfl⟩ : syracuseStep 1688773 = 316645) (by norm_num)
theorem B3376349 : Blo 1500070 3376349 := bbase (se 3 (by rfl) ⟨633065, by rfl⟩ : syracuseStep 3376349 = 1266131) (by norm_num)
theorem B5407973 : Blo 1500070 5407973 := bbase (se 4 (by rfl) ⟨506997, by rfl⟩ : syracuseStep 5407973 = 1013995) (by norm_num)
theorem B1688809 : Blo 1500070 1688809 := bbase (se 2 (by rfl) ⟨633303, by rfl⟩ : syracuseStep 1688809 = 1266607) (by norm_num)
theorem B2532613 : Blo 1500070 2532613 := bbase (se 4 (by rfl) ⟨237432, by rfl⟩ : syracuseStep 2532613 = 474865) (by norm_num)
theorem B3204365 : Blo 1500070 3204365 := bbase (se 3 (by rfl) ⟨600818, by rfl⟩ : syracuseStep 3204365 = 1201637) (by norm_num)
theorem B1688845 : Blo 1500070 1688845 := bbase (se 3 (by rfl) ⟨316658, by rfl⟩ : syracuseStep 1688845 = 633317) (by norm_num)
theorem B5063957 : Blo 1500070 5063957 := bbase (se 6 (by rfl) ⟨118686, by rfl⟩ : syracuseStep 5063957 = 237373) (by norm_num)
theorem B1926433 : Blo 1500070 1926433 := bbase (se 2 (by rfl) ⟨722412, by rfl⟩ : syracuseStep 1926433 = 1444825) (by norm_num)
theorem B3376421 : Blo 1500070 3376421 := bbase (se 4 (by rfl) ⟨316539, by rfl⟩ : syracuseStep 3376421 = 633079) (by norm_num)
theorem B1688881 : Blo 1500070 1688881 := bbase (se 2 (by rfl) ⟨633330, by rfl⟩ : syracuseStep 1688881 = 1266661) (by norm_num)
theorem B2704693 : Blo 1500070 2704693 := bbase (se 5 (by rfl) ⟨126782, by rfl⟩ : syracuseStep 2704693 = 253565) (by norm_num)
theorem B2778437 : Blo 1500070 2778437 := bbase (se 4 (by rfl) ⟨260478, by rfl⟩ : syracuseStep 2778437 = 520957) (by norm_num)
theorem B1688917 : Blo 1500070 1688917 := bbase (se 12 (by rfl) ⟨618, by rfl⟩ : syracuseStep 1688917 = 1237) (by norm_num)
theorem B2532701 : Blo 1500070 2532701 := bbase (se 3 (by rfl) ⟨474881, by rfl⟩ : syracuseStep 2532701 = 949763) (by norm_num)
theorem B3376493 : Blo 1500070 3376493 := bbase (se 3 (by rfl) ⟨633092, by rfl⟩ : syracuseStep 3376493 = 1266185) (by norm_num)
theorem B1688953 : Blo 1500070 1688953 := bbase (se 2 (by rfl) ⟨633357, by rfl⟩ : syracuseStep 1688953 = 1266715) (by norm_num)
theorem B1688989 : Blo 1500070 1688989 := bbase (se 3 (by rfl) ⟨316685, by rfl⟩ : syracuseStep 1688989 = 633371) (by norm_num)
theorem B3376565 : Blo 1500070 3376565 := bbase (se 5 (by rfl) ⟨158276, by rfl⟩ : syracuseStep 3376565 = 316553) (by norm_num)
theorem B1689025 : Blo 1500070 1689025 := bbase (se 2 (by rfl) ⟨633384, by rfl⟩ : syracuseStep 1689025 = 1266769) (by norm_num)
theorem B2704853 : Blo 1500070 2704853 := bbase (se 7 (by rfl) ⟨31697, by rfl⟩ : syracuseStep 2704853 = 63395) (by norm_num)
theorem B2532829 : Blo 1500070 2532829 := bbase (se 3 (by rfl) ⟨474905, by rfl⟩ : syracuseStep 2532829 = 949811) (by norm_num)
theorem B6497765 : Blo 1500070 6497765 := bbase (se 4 (by rfl) ⟨609165, by rfl⟩ : syracuseStep 6497765 = 1218331) (by norm_num)
theorem B1689061 : Blo 1500070 1689061 := bbase (se 4 (by rfl) ⟨158349, by rfl⟩ : syracuseStep 1689061 = 316699) (by norm_num)
theorem B3204605 : Blo 1500070 3204605 := bbase (se 3 (by rfl) ⟨600863, by rfl⟩ : syracuseStep 3204605 = 1201727) (by norm_num)
theorem B3376637 : Blo 1500070 3376637 := bbase (se 3 (by rfl) ⟨633119, by rfl⟩ : syracuseStep 3376637 = 1266239) (by norm_num)
theorem B1689097 : Blo 1500070 1689097 := bbase (se 2 (by rfl) ⟨633411, by rfl⟩ : syracuseStep 1689097 = 1266823) (by norm_num)
theorem B1689133 : Blo 1500070 1689133 := bbase (se 3 (by rfl) ⟨316712, by rfl⟩ : syracuseStep 1689133 = 633425) (by norm_num)
theorem B2532917 : Blo 1500070 2532917 := bbase (se 5 (by rfl) ⟨118730, by rfl⟩ : syracuseStep 2532917 = 237461) (by norm_num)
theorem B3376709 : Blo 1500070 3376709 := bbase (se 4 (by rfl) ⟨316566, by rfl⟩ : syracuseStep 3376709 = 633133) (by norm_num)
theorem B1689169 : Blo 1500070 1689169 := bbase (se 2 (by rfl) ⟨633438, by rfl⟩ : syracuseStep 1689169 = 1266877) (by norm_num)
theorem B1689205 : Blo 1500070 1689205 := bbase (se 5 (by rfl) ⟨79181, by rfl⟩ : syracuseStep 1689205 = 158363) (by norm_num)
theorem B3376781 : Blo 1500070 3376781 := bbase (se 3 (by rfl) ⟨633146, by rfl⟩ : syracuseStep 3376781 = 1266293) (by norm_num)
theorem B1689241 : Blo 1500070 1689241 := bbase (se 2 (by rfl) ⟨633465, by rfl⟩ : syracuseStep 1689241 = 1266931) (by norm_num)
theorem B2533045 : Blo 1500070 2533045 := bbase (se 5 (by rfl) ⟨118736, by rfl⟩ : syracuseStep 2533045 = 237473) (by norm_num)
theorem B1689277 : Blo 1500070 1689277 := bbase (se 3 (by rfl) ⟨316739, by rfl⟩ : syracuseStep 1689277 = 633479) (by norm_num)
theorem B5064389 : Blo 1500070 5064389 := bbase (se 4 (by rfl) ⟨474786, by rfl⟩ : syracuseStep 5064389 = 949573) (by norm_num)
theorem B3376853 : Blo 1500070 3376853 := bbase (se 7 (by rfl) ⟨39572, by rfl⟩ : syracuseStep 3376853 = 79145) (by norm_num)
theorem B1689313 : Blo 1500070 1689313 := bbase (se 2 (by rfl) ⟨633492, by rfl⟩ : syracuseStep 1689313 = 1266985) (by norm_num)
theorem B1689349 : Blo 1500070 1689349 := bbase (se 4 (by rfl) ⟨158376, by rfl⟩ : syracuseStep 1689349 = 316753) (by norm_num)
theorem B2533133 : Blo 1500070 2533133 := bbase (se 3 (by rfl) ⟨474962, by rfl⟩ : syracuseStep 2533133 = 949925) (by norm_num)
theorem B3376925 : Blo 1500070 3376925 := bbase (se 3 (by rfl) ⟨633173, by rfl⟩ : syracuseStep 3376925 = 1266347) (by norm_num)
theorem B1689385 : Blo 1500070 1689385 := bbase (se 2 (by rfl) ⟨633519, by rfl⟩ : syracuseStep 1689385 = 1267039) (by norm_num)
theorem B2565949 : Blo 1500070 2565949 := bbase (se 3 (by rfl) ⟨481115, by rfl⟩ : syracuseStep 2565949 = 962231) (by norm_num)
theorem B1689421 : Blo 1500070 1689421 := bbase (se 3 (by rfl) ⟨316766, by rfl⟩ : syracuseStep 1689421 = 633533) (by norm_num)
theorem B8898389 : Blo 1500070 8898389 := bbase (se 9 (by rfl) ⟨26069, by rfl⟩ : syracuseStep 8898389 = 52139) (by norm_num)
theorem B3376997 : Blo 1500070 3376997 := bbase (se 4 (by rfl) ⟨316593, by rfl⟩ : syracuseStep 3376997 = 633187) (by norm_num)
theorem B1689457 : Blo 1500070 1689457 := bbase (se 2 (by rfl) ⟨633546, by rfl⟩ : syracuseStep 1689457 = 1267093) (by norm_num)
theorem B2533261 : Blo 1500070 2533261 := bbase (se 3 (by rfl) ⟨474986, by rfl⟩ : syracuseStep 2533261 = 949973) (by norm_num)
theorem B1689493 : Blo 1500070 1689493 := bbase (se 6 (by rfl) ⟨39597, by rfl⟩ : syracuseStep 1689493 = 79195) (by norm_num)
theorem B7604117 : Blo 1500070 7604117 := bbase (se 6 (by rfl) ⟨178221, by rfl⟩ : syracuseStep 7604117 = 356443) (by norm_num)
theorem B3377069 : Blo 1500070 3377069 := bbase (se 3 (by rfl) ⟨633200, by rfl⟩ : syracuseStep 3377069 = 1266401) (by norm_num)
theorem B1804205 : Blo 1500070 1804205 := bbase (se 3 (by rfl) ⟨338288, by rfl⟩ : syracuseStep 1804205 = 676577) (by norm_num)
theorem B1689529 : Blo 1500070 1689529 := bbase (se 2 (by rfl) ⟨633573, by rfl⟩ : syracuseStep 1689529 = 1267147) (by norm_num)
theorem B1689565 : Blo 1500070 1689565 := bbase (se 3 (by rfl) ⟨316793, by rfl⟩ : syracuseStep 1689565 = 633587) (by norm_num)
theorem B2533349 : Blo 1500070 2533349 := bbase (se 4 (by rfl) ⟨237501, by rfl⟩ : syracuseStep 2533349 = 475003) (by norm_num)
theorem B3205109 : Blo 1500070 3205109 := bbase (se 5 (by rfl) ⟨150239, by rfl⟩ : syracuseStep 3205109 = 300479) (by norm_num)
theorem B3377141 : Blo 1500070 3377141 := bbase (se 5 (by rfl) ⟨158303, by rfl⟩ : syracuseStep 3377141 = 316607) (by norm_num)
theorem B3205117 : Blo 1500070 3205117 := bbase (se 3 (by rfl) ⟨600959, by rfl⟩ : syracuseStep 3205117 = 1201919) (by norm_num)
theorem B1689601 : Blo 1500070 1689601 := bbase (se 2 (by rfl) ⟨633600, by rfl⟩ : syracuseStep 1689601 = 1267201) (by norm_num)
theorem B3606565 : Blo 1500070 3606565 := bbase (se 4 (by rfl) ⟨338115, by rfl⟩ : syracuseStep 3606565 = 676231) (by norm_num)
theorem B1689637 : Blo 1500070 1689637 := bbase (se 4 (by rfl) ⟨158403, by rfl⟩ : syracuseStep 1689637 = 316807) (by norm_num)
theorem B3377213 : Blo 1500070 3377213 := bbase (se 3 (by rfl) ⟨633227, by rfl⟩ : syracuseStep 3377213 = 1266455) (by norm_num)
theorem B1689673 : Blo 1500070 1689673 := bbase (se 2 (by rfl) ⟨633627, by rfl⟩ : syracuseStep 1689673 = 1267255) (by norm_num)
theorem B2533477 : Blo 1500070 2533477 := bbase (se 4 (by rfl) ⟨237513, by rfl⟩ : syracuseStep 2533477 = 475027) (by norm_num)
theorem B1689709 : Blo 1500070 1689709 := bbase (se 3 (by rfl) ⟨316820, by rfl⟩ : syracuseStep 1689709 = 633641) (by norm_num)
theorem B5064821 : Blo 1500070 5064821 := bbase (se 5 (by rfl) ⟨237413, by rfl⟩ : syracuseStep 5064821 = 474827) (by norm_num)
theorem B3377285 : Blo 1500070 3377285 := bbase (se 4 (by rfl) ⟨316620, by rfl⟩ : syracuseStep 3377285 = 633241) (by norm_num)
theorem B1689745 : Blo 1500070 1689745 := bbase (se 2 (by rfl) ⟨633654, by rfl⟩ : syracuseStep 1689745 = 1267309) (by norm_num)
theorem B1804465 : Blo 1500070 1804465 := bbase (se 2 (by rfl) ⟨676674, by rfl⟩ : syracuseStep 1804465 = 1353349) (by norm_num)
theorem B1689781 : Blo 1500070 1689781 := bbase (se 5 (by rfl) ⟨79208, by rfl⟩ : syracuseStep 1689781 = 158417) (by norm_num)
theorem B2533565 : Blo 1500070 2533565 := bbase (se 3 (by rfl) ⟨475043, by rfl⟩ : syracuseStep 2533565 = 950087) (by norm_num)
theorem B6408389 : Blo 1500070 6408389 := bbase (se 4 (by rfl) ⟨600786, by rfl⟩ : syracuseStep 6408389 = 1201573) (by norm_num)
theorem B3377357 : Blo 1500070 3377357 := bbase (se 3 (by rfl) ⟨633254, by rfl⟩ : syracuseStep 3377357 = 1266509) (by norm_num)
theorem B1689817 : Blo 1500070 1689817 := bbase (se 2 (by rfl) ⟨633681, by rfl⟩ : syracuseStep 1689817 = 1267363) (by norm_num)
theorem B1804513 : Blo 1500070 1804513 := bbase (se 2 (by rfl) ⟨676692, by rfl⟩ : syracuseStep 1804513 = 1353385) (by norm_num)
theorem B3377429 : Blo 1500070 3377429 := bbase (se 6 (by rfl) ⟨79158, by rfl⟩ : syracuseStep 3377429 = 158317) (by norm_num)
theorem B7596341 : Blo 1500070 7596341 := bbase (se 5 (by rfl) ⟨356078, by rfl⟩ : syracuseStep 7596341 = 712157) (by norm_num)
theorem B2533693 : Blo 1500070 2533693 := bbase (se 3 (by rfl) ⟨475067, by rfl⟩ : syracuseStep 2533693 = 950135) (by norm_num)
theorem B5695829 : Blo 1500070 5695829 := bbase (se 10 (by rfl) ⟨8343, by rfl⟩ : syracuseStep 5695829 = 16687) (by norm_num)
theorem B3377501 : Blo 1500070 3377501 := bbase (se 3 (by rfl) ⟨633281, by rfl⟩ : syracuseStep 3377501 = 1266563) (by norm_num)
theorem B2533781 : Blo 1500070 2533781 := bbase (se 6 (by rfl) ⟨59385, by rfl⟩ : syracuseStep 2533781 = 118771) (by norm_num)
theorem B3377573 : Blo 1500070 3377573 := bbase (se 4 (by rfl) ⟨316647, by rfl⟩ : syracuseStep 3377573 = 633295) (by norm_num)
theorem B6408629 : Blo 1500070 6408629 := bbase (se 5 (by rfl) ⟨300404, by rfl⟩ : syracuseStep 6408629 = 600809) (by norm_num)
theorem B3377645 : Blo 1500070 3377645 := bbase (se 3 (by rfl) ⟨633308, by rfl⟩ : syracuseStep 3377645 = 1266617) (by norm_num)
theorem B2705933 : Blo 1500070 2705933 := bbase (se 3 (by rfl) ⟨507362, by rfl⟩ : syracuseStep 2705933 = 1014725) (by norm_num)
theorem B2533909 : Blo 1500070 2533909 := bbase (se 6 (by rfl) ⟨59388, by rfl⟩ : syracuseStep 2533909 = 118777) (by norm_num)
theorem B5065253 : Blo 1500070 5065253 := bbase (se 4 (by rfl) ⟨474867, by rfl⟩ : syracuseStep 5065253 = 949735) (by norm_num)
theorem B3607085 : Blo 1500070 3607085 := bbase (se 3 (by rfl) ⟨676328, by rfl⟩ : syracuseStep 3607085 = 1352657) (by norm_num)
theorem B3377717 : Blo 1500070 3377717 := bbase (se 5 (by rfl) ⟨158330, by rfl⟩ : syracuseStep 3377717 = 316661) (by norm_num)
theorem B2533997 : Blo 1500070 2533997 := bbase (se 3 (by rfl) ⟨475124, by rfl⟩ : syracuseStep 2533997 = 950249) (by norm_num)
theorem B2402941 : Blo 1500070 2402941 := bbase (se 3 (by rfl) ⟨450551, by rfl⟩ : syracuseStep 2402941 = 901103) (by norm_num)
theorem B3377789 : Blo 1500070 3377789 := bbase (se 3 (by rfl) ⟨633335, by rfl⟩ : syracuseStep 3377789 = 1266671) (by norm_num)
theorem B2706077 : Blo 1500070 2706077 := bbase (se 3 (by rfl) ⟨507389, by rfl⟩ : syracuseStep 2706077 = 1014779) (by norm_num)
theorem B3377861 : Blo 1500070 3377861 := bbase (se 4 (by rfl) ⟨316674, by rfl⟩ : syracuseStep 3377861 = 633349) (by norm_num)
theorem B2534125 : Blo 1500070 2534125 := bbase (se 3 (by rfl) ⟨475148, by rfl⟩ : syracuseStep 2534125 = 950297) (by norm_num)
theorem B3377933 : Blo 1500070 3377933 := bbase (se 3 (by rfl) ⟨633362, by rfl⟩ : syracuseStep 3377933 = 1266725) (by norm_num)
theorem B2534213 : Blo 1500070 2534213 := bbase (se 4 (by rfl) ⟨237582, by rfl⟩ : syracuseStep 2534213 = 475165) (by norm_num)
theorem B7211861 : Blo 1500070 7211861 := bbase (se 9 (by rfl) ⟨21128, by rfl⟩ : syracuseStep 7211861 = 42257) (by norm_num)
theorem B3378005 : Blo 1500070 3378005 := bbase (se 9 (by rfl) ⟨9896, by rfl⟩ : syracuseStep 3378005 = 19793) (by norm_num)
theorem B3378077 : Blo 1500070 3378077 := bbase (se 3 (by rfl) ⟨633389, by rfl⟩ : syracuseStep 3378077 = 1266779) (by norm_num)
theorem B3607469 : Blo 1500070 3607469 := bbase (se 3 (by rfl) ⟨676400, by rfl⟩ : syracuseStep 3607469 = 1352801) (by norm_num)
theorem B2534341 : Blo 1500070 2534341 := bbase (se 4 (by rfl) ⟨237594, by rfl⟩ : syracuseStep 2534341 = 475189) (by norm_num)
theorem B5065685 : Blo 1500070 5065685 := bbase (se 7 (by rfl) ⟨59363, by rfl⟩ : syracuseStep 5065685 = 118727) (by norm_num)
theorem B3607517 : Blo 1500070 3607517 := bbase (se 3 (by rfl) ⟨676409, by rfl⟩ : syracuseStep 3607517 = 1352819) (by norm_num)
theorem B3378149 : Blo 1500070 3378149 := bbase (se 4 (by rfl) ⟨316701, by rfl⟩ : syracuseStep 3378149 = 633403) (by norm_num)
theorem B3607525 : Blo 1500070 3607525 := bbase (se 4 (by rfl) ⟨338205, by rfl⟩ : syracuseStep 3607525 = 676411) (by norm_num)
theorem B2534429 : Blo 1500070 2534429 := bbase (se 3 (by rfl) ⟨475205, by rfl⟩ : syracuseStep 2534429 = 950411) (by norm_num)
theorem B3378221 : Blo 1500070 3378221 := bbase (se 3 (by rfl) ⟨633416, by rfl⟩ : syracuseStep 3378221 = 1266833) (by norm_num)
theorem B3206245 : Blo 1500070 3206245 := bbase (se 4 (by rfl) ⟨300585, by rfl⟩ : syracuseStep 3206245 = 601171) (by norm_num)
theorem B3378293 : Blo 1500070 3378293 := bbase (se 5 (by rfl) ⟨158357, by rfl⟩ : syracuseStep 3378293 = 316715) (by norm_num)
theorem B2534557 : Blo 1500070 2534557 := bbase (se 3 (by rfl) ⟨475229, by rfl⟩ : syracuseStep 2534557 = 950459) (by norm_num)
theorem B2567333 : Blo 1500070 2567333 := bbase (se 4 (by rfl) ⟨240687, by rfl⟩ : syracuseStep 2567333 = 481375) (by norm_num)
theorem B3378365 : Blo 1500070 3378365 := bbase (se 3 (by rfl) ⟨633443, by rfl⟩ : syracuseStep 3378365 = 1266887) (by norm_num)
theorem B7310533 : Blo 1500070 7310533 := bbase (se 4 (by rfl) ⟨685362, by rfl⟩ : syracuseStep 7310533 = 1370725) (by norm_num)
theorem B9612533 : Blo 1500070 9612533 := bbase (se 5 (by rfl) ⟨450587, by rfl⟩ : syracuseStep 9612533 = 901175) (by norm_num)
theorem B2534645 : Blo 1500070 2534645 := bbase (se 5 (by rfl) ⟨118811, by rfl⟩ : syracuseStep 2534645 = 237623) (by norm_num)
theorem B2084093 : Blo 1500070 2084093 := bbase (se 3 (by rfl) ⟨390767, by rfl⟩ : syracuseStep 2084093 = 781535) (by norm_num)
theorem B3378437 : Blo 1500070 3378437 := bbase (se 4 (by rfl) ⟨316728, by rfl⟩ : syracuseStep 3378437 = 633457) (by norm_num)
theorem B3378509 : Blo 1500070 3378509 := bbase (se 3 (by rfl) ⟨633470, by rfl⟩ : syracuseStep 3378509 = 1266941) (by norm_num)
theorem B7810405 : Blo 1500070 7810405 := bbase (se 4 (by rfl) ⟨732225, by rfl⟩ : syracuseStep 7810405 = 1464451) (by norm_num)
theorem B2567533 : Blo 1500070 2567533 := bbase (se 3 (by rfl) ⟨481412, by rfl⟩ : syracuseStep 2567533 = 962825) (by norm_num)
theorem B5066117 : Blo 1500070 5066117 := bbase (se 4 (by rfl) ⟨474948, by rfl⟩ : syracuseStep 5066117 = 949897) (by norm_num)
theorem B3378581 : Blo 1500070 3378581 := bbase (se 6 (by rfl) ⟨79185, by rfl⟩ : syracuseStep 3378581 = 158371) (by norm_num)
theorem B2403749 : Blo 1500070 2403749 := bbase (se 4 (by rfl) ⟨225351, by rfl⟩ : syracuseStep 2403749 = 450703) (by norm_num)
theorem B2280893 : Blo 1500070 2280893 := bbase (se 3 (by rfl) ⟨427667, by rfl⟩ : syracuseStep 2280893 = 855335) (by norm_num)
theorem B12824021 : Blo 1500070 12824021 := bbase (se 7 (by rfl) ⟨150281, by rfl⟩ : syracuseStep 12824021 = 300563) (by norm_num)
theorem B3206621 : Blo 1500070 3206621 := bbase (se 3 (by rfl) ⟨601241, by rfl⟩ : syracuseStep 3206621 = 1202483) (by norm_num)
theorem B3378653 : Blo 1500070 3378653 := bbase (se 3 (by rfl) ⟨633497, by rfl⟩ : syracuseStep 3378653 = 1266995) (by norm_num)
theorem B5697013 : Blo 1500070 5697013 := bbase (se 5 (by rfl) ⟨267047, by rfl⟩ : syracuseStep 5697013 = 534095) (by norm_num)
theorem B3378725 : Blo 1500070 3378725 := bbase (se 4 (by rfl) ⟨316755, by rfl⟩ : syracuseStep 3378725 = 633511) (by norm_num)
theorem B7597637 : Blo 1500070 7597637 := bbase (se 4 (by rfl) ⟨712278, by rfl⟩ : syracuseStep 7597637 = 1424557) (by norm_num)
theorem B3378797 : Blo 1500070 3378797 := bbase (se 3 (by rfl) ⟨633524, by rfl⟩ : syracuseStep 3378797 = 1267049) (by norm_num)
theorem B5484181 : Blo 1500070 5484181 := bbase (se 6 (by rfl) ⟨128535, by rfl⟩ : syracuseStep 5484181 = 257071) (by norm_num)
theorem B3378869 : Blo 1500070 3378869 := bbase (se 5 (by rfl) ⟨158384, by rfl⟩ : syracuseStep 3378869 = 316769) (by norm_num)
theorem B2404037 : Blo 1500070 2404037 := bbase (se 4 (by rfl) ⟨225378, by rfl⟩ : syracuseStep 2404037 = 450757) (by norm_num)
theorem B3378941 : Blo 1500070 3378941 := bbase (se 3 (by rfl) ⟨633551, by rfl⟩ : syracuseStep 3378941 = 1267103) (by norm_num)
theorem B5697317 : Blo 1500070 5697317 := bbase (se 4 (by rfl) ⟨534123, by rfl⟩ : syracuseStep 5697317 = 1068247) (by norm_num)
theorem B5410597 : Blo 1500070 5410597 := bbase (se 4 (by rfl) ⟨507243, by rfl⟩ : syracuseStep 5410597 = 1014487) (by norm_num)
theorem B5066549 : Blo 1500070 5066549 := bbase (se 5 (by rfl) ⟨237494, by rfl⟩ : syracuseStep 5066549 = 474989) (by norm_num)
theorem B3379013 : Blo 1500070 3379013 := bbase (se 4 (by rfl) ⟨316782, by rfl⟩ : syracuseStep 3379013 = 633565) (by norm_num)
theorem B3379085 : Blo 1500070 3379085 := bbase (se 3 (by rfl) ⟨633578, by rfl⟩ : syracuseStep 3379085 = 1267157) (by norm_num)
theorem B5410741 : Blo 1500070 5410741 := bbase (se 5 (by rfl) ⟨253628, by rfl⟩ : syracuseStep 5410741 = 507257) (by norm_num)
theorem B3608525 : Blo 1500070 3608525 := bbase (se 3 (by rfl) ⟨676598, by rfl⟩ : syracuseStep 3608525 = 1353197) (by norm_num)
theorem B3379157 : Blo 1500070 3379157 := bbase (se 7 (by rfl) ⟨39599, by rfl⟩ : syracuseStep 3379157 = 79199) (by norm_num)
theorem B3043325 : Blo 1500070 3043325 := bbase (se 3 (by rfl) ⟨570623, by rfl⟩ : syracuseStep 3043325 = 1141247) (by norm_num)
theorem B3379229 : Blo 1500070 3379229 := bbase (se 3 (by rfl) ⟨633605, by rfl⟩ : syracuseStep 3379229 = 1267211) (by norm_num)
theorem B2887741 : Blo 1500070 2887741 := bbase (se 3 (by rfl) ⟨541451, by rfl⟩ : syracuseStep 2887741 = 1082903) (by norm_num)
theorem B3797077 : Blo 1500070 3797077 := bbase (se 8 (by rfl) ⟨22248, by rfl⟩ : syracuseStep 3797077 = 44497) (by norm_num)
theorem B2404453 : Blo 1500070 2404453 := bbase (se 4 (by rfl) ⟨225417, by rfl⟩ : syracuseStep 2404453 = 450835) (by norm_num)
theorem B3379301 : Blo 1500070 3379301 := bbase (se 4 (by rfl) ⟨316809, by rfl⟩ : syracuseStep 3379301 = 633619) (by norm_num)
theorem B3608717 : Blo 1500070 3608717 := bbase (se 3 (by rfl) ⟨676634, by rfl⟩ : syracuseStep 3608717 = 1353269) (by norm_num)
theorem B7213205 : Blo 1500070 7213205 := bbase (se 6 (by rfl) ⟨169059, by rfl⟩ : syracuseStep 7213205 = 338119) (by norm_num)
theorem B3379373 : Blo 1500070 3379373 := bbase (se 3 (by rfl) ⟨633632, by rfl⟩ : syracuseStep 3379373 = 1267265) (by norm_num)
theorem B3903677 : Blo 1500070 3903677 := bbase (se 3 (by rfl) ⟨731939, by rfl⟩ : syracuseStep 3903677 = 1463879) (by norm_num)
theorem B3797189 : Blo 1500070 3797189 := bbase (se 4 (by rfl) ⟨355986, by rfl⟩ : syracuseStep 3797189 = 711973) (by norm_num)
theorem B5066981 : Blo 1500070 5066981 := bbase (se 4 (by rfl) ⟨475029, by rfl⟩ : syracuseStep 5066981 = 950059) (by norm_num)
theorem B3379445 : Blo 1500070 3379445 := bbase (se 5 (by rfl) ⟨158411, by rfl⟩ : syracuseStep 3379445 = 316823) (by norm_num)
theorem B3379517 : Blo 1500070 3379517 := bbase (se 3 (by rfl) ⟨633659, by rfl⟩ : syracuseStep 3379517 = 1267319) (by norm_num)
theorem B2027845 : Blo 1500070 2027845 := bbase (se 4 (by rfl) ⟨190110, by rfl⟩ : syracuseStep 2027845 = 380221) (by norm_num)
theorem B3797381 : Blo 1500070 3797381 := bbase (se 4 (by rfl) ⟨356004, by rfl⟩ : syracuseStep 3797381 = 712009) (by norm_num)
theorem B2281861 : Blo 1500070 2281861 := bbase (se 4 (by rfl) ⟨213924, by rfl⟩ : syracuseStep 2281861 = 427849) (by norm_num)
theorem B3379589 : Blo 1500070 3379589 := bbase (se 4 (by rfl) ⟨316836, by rfl⟩ : syracuseStep 3379589 = 633673) (by norm_num)
theorem B4272533 : Blo 1500070 4272533 := bbase (se 6 (by rfl) ⟨100137, by rfl⟩ : syracuseStep 4272533 = 200275) (by norm_num)
theorem B11121077 : Blo 1500070 11121077 := bbase (se 5 (by rfl) ⟨521300, by rfl⟩ : syracuseStep 11121077 = 1042601) (by norm_num)
theorem B1602029 : Blo 1500070 1602029 := bbase (se 3 (by rfl) ⟨300380, by rfl⟩ : syracuseStep 1602029 = 600761) (by norm_num)
theorem B2601485 : Blo 1500070 2601485 := bbase (se 3 (by rfl) ⟨487778, by rfl⟩ : syracuseStep 2601485 = 975557) (by norm_num)
theorem B5067413 : Blo 1500070 5067413 := bbase (se 6 (by rfl) ⟨118767, by rfl⟩ : syracuseStep 5067413 = 237535) (by norm_num)
theorem B3043997 : Blo 1500070 3043997 := bbase (se 3 (by rfl) ⟨570749, by rfl⟩ : syracuseStep 3043997 = 1141499) (by norm_num)
theorem B6410917 : Blo 1500070 6410917 := bbase (se 4 (by rfl) ⟨601023, by rfl⟩ : syracuseStep 6410917 = 1202047) (by norm_num)
theorem B1602217 : Blo 1500070 1602217 := bbase (se 2 (by rfl) ⟨600831, by rfl⟩ : syracuseStep 1602217 = 1201663) (by norm_num)
theorem B12513973 : Blo 1500070 12513973 := bbase (se 5 (by rfl) ⟨586592, by rfl⟩ : syracuseStep 12513973 = 1173185) (by norm_num)
theorem B3797725 : Blo 1500070 3797725 := bbase (se 3 (by rfl) ⟨712073, by rfl⟩ : syracuseStep 3797725 = 1424147) (by norm_num)
theorem B17330965 : Blo 1500070 17330965 := bbase (se 6 (by rfl) ⟨406194, by rfl⟩ : syracuseStep 17330965 = 812389) (by norm_num)
theorem B3797837 : Blo 1500070 3797837 := bbase (se 3 (by rfl) ⟨712094, by rfl⟩ : syracuseStep 3797837 = 1424189) (by norm_num)
theorem B7598933 : Blo 1500070 7598933 := bbase (se 9 (by rfl) ⟨22262, by rfl⟩ : syracuseStep 7598933 = 44525) (by norm_num)
theorem B9384821 : Blo 1500070 9384821 := bbase (se 5 (by rfl) ⟨439913, by rfl⟩ : syracuseStep 9384821 = 879827) (by norm_num)
theorem B2028541 : Blo 1500070 2028541 := bbase (se 3 (by rfl) ⟨380351, by rfl⟩ : syracuseStep 2028541 = 760703) (by norm_num)
theorem B3798029 : Blo 1500070 3798029 := bbase (se 3 (by rfl) ⟨712130, by rfl⟩ : syracuseStep 3798029 = 1424261) (by norm_num)
theorem B2405389 : Blo 1500070 2405389 := bbase (se 3 (by rfl) ⟨451010, by rfl⟩ : syracuseStep 2405389 = 902021) (by norm_num)
theorem B5067845 : Blo 1500070 5067845 := bbase (se 4 (by rfl) ⟨475110, by rfl⟩ : syracuseStep 5067845 = 950221) (by norm_num)
theorem B3249229 : Blo 1500070 3249229 := bbase (se 3 (by rfl) ⟨609230, by rfl⟩ : syracuseStep 3249229 = 1218461) (by norm_num)
theorem B2438245 : Blo 1500070 2438245 := bbase (se 4 (by rfl) ⟨228585, by rfl⟩ : syracuseStep 2438245 = 457171) (by norm_num)
theorem B2847869 : Blo 1500070 2847869 := bbase (se 3 (by rfl) ⟨533975, by rfl⟩ : syracuseStep 2847869 = 1067951) (by norm_num)
theorem B2282669 : Blo 1500070 2282669 := bbase (se 3 (by rfl) ⟨428000, by rfl⟩ : syracuseStep 2282669 = 856001) (by norm_num)
theorem B9622709 : Blo 1500070 9622709 := bbase (se 5 (by rfl) ⟨451064, by rfl⟩ : syracuseStep 9622709 = 902129) (by norm_num)
theorem B3044557 : Blo 1500070 3044557 := bbase (se 3 (by rfl) ⟨570854, by rfl⟩ : syracuseStep 3044557 = 1141709) (by norm_num)
theorem B8549621 : Blo 1500070 8549621 := bbase (se 5 (by rfl) ⟨400763, by rfl⟩ : syracuseStep 8549621 = 801527) (by norm_num)
theorem B6944069 : Blo 1500070 6944069 := bbase (se 4 (by rfl) ⟨651006, by rfl⟩ : syracuseStep 6944069 = 1302013) (by norm_num)
theorem B3798373 : Blo 1500070 3798373 := bbase (se 4 (by rfl) ⟨356097, by rfl⟩ : syracuseStep 3798373 = 712195) (by norm_num)
theorem B2250125 : Blo 1500070 2250125 := bbase (se 3 (by rfl) ⟨421898, by rfl⟩ : syracuseStep 2250125 = 843797) (by norm_num)
theorem B2250149 : Blo 1500070 2250149 := bbase (se 4 (by rfl) ⟨210951, by rfl⟩ : syracuseStep 2250149 = 421903) (by norm_num)
theorem B2250173 : Blo 1500070 2250173 := bbase (se 3 (by rfl) ⟨421907, by rfl⟩ : syracuseStep 2250173 = 843815) (by norm_num)
theorem B2250197 : Blo 1500070 2250197 := bbase (se 7 (by rfl) ⟨26369, by rfl⟩ : syracuseStep 2250197 = 52739) (by norm_num)
theorem B3798485 : Blo 1500070 3798485 := bbase (se 7 (by rfl) ⟨44513, by rfl⟩ : syracuseStep 3798485 = 89027) (by norm_num)
theorem B1603037 : Blo 1500070 1603037 := bbase (se 3 (by rfl) ⟨300569, by rfl⟩ : syracuseStep 1603037 = 601139) (by norm_num)
theorem B2250221 : Blo 1500070 2250221 := bbase (se 3 (by rfl) ⟨421916, by rfl⟩ : syracuseStep 2250221 = 843833) (by norm_num)
theorem B5068277 : Blo 1500070 5068277 := bbase (se 5 (by rfl) ⟨237575, by rfl⟩ : syracuseStep 5068277 = 475151) (by norm_num)
theorem B2250245 : Blo 1500070 2250245 := bbase (se 4 (by rfl) ⟨210960, by rfl⟩ : syracuseStep 2250245 = 421921) (by norm_num)
theorem B2250269 : Blo 1500070 2250269 := bbase (se 3 (by rfl) ⟨421925, by rfl⟩ : syracuseStep 2250269 = 843851) (by norm_num)
theorem B7214629 : Blo 1500070 7214629 := bbase (se 4 (by rfl) ⟨676371, by rfl⟩ : syracuseStep 7214629 = 1352743) (by norm_num)
theorem B2250293 : Blo 1500070 2250293 := bbase (se 5 (by rfl) ⟨105482, by rfl⟩ : syracuseStep 2250293 = 210965) (by norm_num)
theorem B4273717 : Blo 1500070 4273717 := bbase (se 5 (by rfl) ⟨200330, by rfl⟩ : syracuseStep 4273717 = 400661) (by norm_num)
theorem B2250317 : Blo 1500070 2250317 := bbase (se 3 (by rfl) ⟨421934, by rfl⟩ : syracuseStep 2250317 = 843869) (by norm_num)
theorem B4806229 : Blo 1500070 4806229 := bbase (se 8 (by rfl) ⟨28161, by rfl⟩ : syracuseStep 4806229 = 56323) (by norm_num)
theorem B2250341 : Blo 1500070 2250341 := bbase (se 4 (by rfl) ⟨210969, by rfl⟩ : syracuseStep 2250341 = 421939) (by norm_num)
theorem B6084197 : Blo 1500070 6084197 := bbase (se 4 (by rfl) ⟨570393, by rfl⟩ : syracuseStep 6084197 = 1140787) (by norm_num)
theorem B2250365 : Blo 1500070 2250365 := bbase (se 3 (by rfl) ⟨421943, by rfl⟩ : syracuseStep 2250365 = 843887) (by norm_num)
theorem B2250389 : Blo 1500070 2250389 := bbase (se 6 (by rfl) ⟨52743, by rfl⟩ : syracuseStep 2250389 = 105487) (by norm_num)
theorem B3798677 : Blo 1500070 3798677 := bbase (se 6 (by rfl) ⟨89031, by rfl⟩ : syracuseStep 3798677 = 178063) (by norm_num)
theorem B2250413 : Blo 1500070 2250413 := bbase (se 3 (by rfl) ⟨421952, by rfl⟩ : syracuseStep 2250413 = 843905) (by norm_num)
theorem B2250437 : Blo 1500070 2250437 := bbase (se 4 (by rfl) ⟨210978, by rfl⟩ : syracuseStep 2250437 = 421957) (by norm_num)
theorem B4273877 : Blo 1500070 4273877 := bbase (se 7 (by rfl) ⟨50084, by rfl⟩ : syracuseStep 4273877 = 100169) (by norm_num)
theorem B2250461 : Blo 1500070 2250461 := bbase (se 3 (by rfl) ⟨421961, by rfl⟩ : syracuseStep 2250461 = 843923) (by norm_num)
theorem B2250485 : Blo 1500070 2250485 := bbase (se 5 (by rfl) ⟨105491, by rfl⟩ : syracuseStep 2250485 = 210983) (by norm_num)
theorem B2250509 : Blo 1500070 2250509 := bbase (se 3 (by rfl) ⟨421970, by rfl⟩ : syracuseStep 2250509 = 843941) (by norm_num)
theorem B2135845 : Blo 1500070 2135845 := bbase (se 4 (by rfl) ⟨200235, by rfl⟩ : syracuseStep 2135845 = 400471) (by norm_num)
theorem B2250533 : Blo 1500070 2250533 := bbase (se 4 (by rfl) ⟨210987, by rfl⟩ : syracuseStep 2250533 = 421975) (by norm_num)
theorem B3421997 : Blo 1500070 3421997 := bbase (se 3 (by rfl) ⟨641624, by rfl⟩ : syracuseStep 3421997 = 1283249) (by norm_num)
theorem B2250557 : Blo 1500070 2250557 := bbase (se 3 (by rfl) ⟨421979, by rfl⟩ : syracuseStep 2250557 = 843959) (by norm_num)
theorem B2250581 : Blo 1500070 2250581 := bbase (se 9 (by rfl) ⟨6593, by rfl⟩ : syracuseStep 2250581 = 13187) (by norm_num)
theorem B5699429 : Blo 1500070 5699429 := bbase (se 4 (by rfl) ⟨534321, by rfl⟩ : syracuseStep 5699429 = 1068643) (by norm_num)
theorem B2250605 : Blo 1500070 2250605 := bbase (se 3 (by rfl) ⟨421988, by rfl⟩ : syracuseStep 2250605 = 843977) (by norm_num)
theorem B2848621 : Blo 1500070 2848621 := bbase (se 3 (by rfl) ⟨534116, by rfl⟩ : syracuseStep 2848621 = 1068233) (by norm_num)
theorem B2250629 : Blo 1500070 2250629 := bbase (se 4 (by rfl) ⟨210996, by rfl⟩ : syracuseStep 2250629 = 421993) (by norm_num)
theorem B1603481 : Blo 1500070 1603481 := bbase (se 2 (by rfl) ⟨601305, by rfl⟩ : syracuseStep 1603481 = 1202611) (by norm_num)
theorem B2135965 : Blo 1500070 2135965 := bbase (se 3 (by rfl) ⟨400493, by rfl⟩ : syracuseStep 2135965 = 800987) (by norm_num)
theorem B2250653 : Blo 1500070 2250653 := bbase (se 3 (by rfl) ⟨421997, by rfl⟩ : syracuseStep 2250653 = 843995) (by norm_num)
theorem B7698341 : Blo 1500070 7698341 := bbase (se 4 (by rfl) ⟨721719, by rfl⟩ : syracuseStep 7698341 = 1443439) (by norm_num)
theorem B5068709 : Blo 1500070 5068709 := bbase (se 4 (by rfl) ⟨475191, by rfl⟩ : syracuseStep 5068709 = 950383) (by norm_num)
theorem B2250677 : Blo 1500070 2250677 := bbase (se 5 (by rfl) ⟨105500, by rfl⟩ : syracuseStep 2250677 = 211001) (by norm_num)
theorem B4274117 : Blo 1500070 4274117 := bbase (se 4 (by rfl) ⟨400698, by rfl⟩ : syracuseStep 4274117 = 801397) (by norm_num)
theorem B2250701 : Blo 1500070 2250701 := bbase (se 3 (by rfl) ⟨422006, by rfl⟩ : syracuseStep 2250701 = 844013) (by norm_num)
theorem B2250725 : Blo 1500070 2250725 := bbase (se 4 (by rfl) ⟨211005, by rfl⟩ : syracuseStep 2250725 = 422011) (by norm_num)
theorem B3799021 : Blo 1500070 3799021 := bbase (se 3 (by rfl) ⟨712316, by rfl⟩ : syracuseStep 3799021 = 1424633) (by norm_num)
theorem B2250749 : Blo 1500070 2250749 := bbase (se 3 (by rfl) ⟨422015, by rfl⟩ : syracuseStep 2250749 = 844031) (by norm_num)
theorem B2848765 : Blo 1500070 2848765 := bbase (se 3 (by rfl) ⟨534143, by rfl⟩ : syracuseStep 2848765 = 1068287) (by norm_num)
theorem B2136061 : Blo 1500070 2136061 := bbase (se 3 (by rfl) ⟨400511, by rfl⟩ : syracuseStep 2136061 = 801023) (by norm_num)
theorem B4806677 : Blo 1500070 4806677 := bbase (se 6 (by rfl) ⟨112656, by rfl⟩ : syracuseStep 4806677 = 225313) (by norm_num)
theorem B2250773 : Blo 1500070 2250773 := bbase (se 6 (by rfl) ⟨52752, by rfl⟩ : syracuseStep 2250773 = 105505) (by norm_num)
theorem B2250797 : Blo 1500070 2250797 := bbase (se 3 (by rfl) ⟨422024, by rfl⟩ : syracuseStep 2250797 = 844049) (by norm_num)
theorem B2250821 : Blo 1500070 2250821 := bbase (se 4 (by rfl) ⟨211014, by rfl⟩ : syracuseStep 2250821 = 422029) (by norm_num)
theorem B1898569 : Blo 1500070 1898569 := bbase (se 2 (by rfl) ⟨711963, by rfl⟩ : syracuseStep 1898569 = 1423927) (by norm_num)
theorem B2250845 : Blo 1500070 2250845 := bbase (se 3 (by rfl) ⟨422033, by rfl⟩ : syracuseStep 2250845 = 844067) (by norm_num)
theorem B3799133 : Blo 1500070 3799133 := bbase (se 3 (by rfl) ⟨712337, by rfl⟩ : syracuseStep 3799133 = 1424675) (by norm_num)
theorem B7600229 : Blo 1500070 7600229 := bbase (se 4 (by rfl) ⟨712521, by rfl⟩ : syracuseStep 7600229 = 1425043) (by norm_num)
theorem B2250869 : Blo 1500070 2250869 := bbase (se 5 (by rfl) ⟨105509, by rfl⟩ : syracuseStep 2250869 = 211019) (by norm_num)
theorem B6412405 : Blo 1500070 6412405 := bbase (se 5 (by rfl) ⟨300581, by rfl⟩ : syracuseStep 6412405 = 601163) (by norm_num)
theorem B4274309 : Blo 1500070 4274309 := bbase (se 4 (by rfl) ⟨400716, by rfl⟩ : syracuseStep 4274309 = 801433) (by norm_num)
theorem B5699717 : Blo 1500070 5699717 := bbase (se 4 (by rfl) ⟨534348, by rfl⟩ : syracuseStep 5699717 = 1068697) (by norm_num)
theorem B6412421 : Blo 1500070 6412421 := bbase (se 4 (by rfl) ⟨601164, by rfl⟩ : syracuseStep 6412421 = 1202329) (by norm_num)
theorem B2250893 : Blo 1500070 2250893 := bbase (se 3 (by rfl) ⟨422042, by rfl⟩ : syracuseStep 2250893 = 844085) (by norm_num)
theorem B2283661 : Blo 1500070 2283661 := bbase (se 3 (by rfl) ⟨428186, by rfl⟩ : syracuseStep 2283661 = 856373) (by norm_num)
theorem B1603729 : Blo 1500070 1603729 := bbase (se 2 (by rfl) ⟨601398, by rfl⟩ : syracuseStep 1603729 = 1202797) (by norm_num)
theorem B2848925 : Blo 1500070 2848925 := bbase (se 3 (by rfl) ⟨534173, by rfl⟩ : syracuseStep 2848925 = 1068347) (by norm_num)
theorem B2250917 : Blo 1500070 2250917 := bbase (se 4 (by rfl) ⟨211023, by rfl⟩ : syracuseStep 2250917 = 422047) (by norm_num)
theorem B2250941 : Blo 1500070 2250941 := bbase (se 3 (by rfl) ⟨422051, by rfl⟩ : syracuseStep 2250941 = 844103) (by norm_num)
theorem B2283709 : Blo 1500070 2283709 := bbase (se 3 (by rfl) ⟨428195, by rfl⟩ : syracuseStep 2283709 = 856391) (by norm_num)
theorem B2250965 : Blo 1500070 2250965 := bbase (se 7 (by rfl) ⟨26378, by rfl⟩ : syracuseStep 2250965 = 52757) (by norm_num)
theorem B1521877 : Blo 1500070 1521877 := bbase (se 7 (by rfl) ⟨17834, by rfl⟩ : syracuseStep 1521877 = 35669) (by norm_num)
theorem B3250405 : Blo 1500070 3250405 := bbase (se 4 (by rfl) ⟨304725, by rfl⟩ : syracuseStep 3250405 = 609451) (by norm_num)
theorem B2250989 : Blo 1500070 2250989 := bbase (se 3 (by rfl) ⟨422060, by rfl⟩ : syracuseStep 2250989 = 844121) (by norm_num)
theorem B1898741 : Blo 1500070 1898741 := bbase (se 5 (by rfl) ⟨89003, by rfl⟩ : syracuseStep 1898741 = 178007) (by norm_num)
theorem B2251013 : Blo 1500070 2251013 := bbase (se 4 (by rfl) ⟨211032, by rfl⟩ : syracuseStep 2251013 = 422065) (by norm_num)
theorem B2251037 : Blo 1500070 2251037 := bbase (se 3 (by rfl) ⟨422069, by rfl⟩ : syracuseStep 2251037 = 844139) (by norm_num)
theorem B3799325 : Blo 1500070 3799325 := bbase (se 3 (by rfl) ⟨712373, by rfl⟩ : syracuseStep 3799325 = 1424747) (by norm_num)
theorem B2029861 : Blo 1500070 2029861 := bbase (se 4 (by rfl) ⟨190299, by rfl⟩ : syracuseStep 2029861 = 380599) (by norm_num)
theorem B1898797 : Blo 1500070 1898797 := bbase (se 3 (by rfl) ⟨356024, by rfl⟩ : syracuseStep 1898797 = 712049) (by norm_num)
theorem B2849069 : Blo 1500070 2849069 := bbase (se 3 (by rfl) ⟨534200, by rfl⟩ : syracuseStep 2849069 = 1068401) (by norm_num)
theorem B2251061 : Blo 1500070 2251061 := bbase (se 5 (by rfl) ⟨105518, by rfl⟩ : syracuseStep 2251061 = 211037) (by norm_num)
theorem B2251085 : Blo 1500070 2251085 := bbase (se 3 (by rfl) ⟨422078, by rfl⟩ : syracuseStep 2251085 = 844157) (by norm_num)
theorem B5069141 : Blo 1500070 5069141 := bbase (se 10 (by rfl) ⟨7425, by rfl⟩ : syracuseStep 5069141 = 14851) (by norm_num)
theorem B2251109 : Blo 1500070 2251109 := bbase (se 4 (by rfl) ⟨211041, by rfl⟩ : syracuseStep 2251109 = 422083) (by norm_num)
theorem B2029925 : Blo 1500070 2029925 := bbase (se 4 (by rfl) ⟨190305, by rfl⟩ : syracuseStep 2029925 = 380611) (by norm_num)
theorem B12826997 : Blo 1500070 12826997 := bbase (se 5 (by rfl) ⟨601265, by rfl⟩ : syracuseStep 12826997 = 1202531) (by norm_num)
theorem B2251133 : Blo 1500070 2251133 := bbase (se 3 (by rfl) ⟨422087, by rfl⟩ : syracuseStep 2251133 = 844175) (by norm_num)
theorem B1898893 : Blo 1500070 1898893 := bbase (se 3 (by rfl) ⟨356042, by rfl⟩ : syracuseStep 1898893 = 712085) (by norm_num)
theorem B2251157 : Blo 1500070 2251157 := bbase (se 6 (by rfl) ⟨52761, by rfl⟩ : syracuseStep 2251157 = 105523) (by norm_num)
theorem B8550805 : Blo 1500070 8550805 := bbase (se 6 (by rfl) ⟨200409, by rfl⟩ : syracuseStep 8550805 = 400819) (by norm_num)
theorem B2251181 : Blo 1500070 2251181 := bbase (se 3 (by rfl) ⟨422096, by rfl⟩ : syracuseStep 2251181 = 844193) (by norm_num)
theorem B2251205 : Blo 1500070 2251205 := bbase (se 4 (by rfl) ⟨211050, by rfl⟩ : syracuseStep 2251205 = 422101) (by norm_num)
theorem B2251229 : Blo 1500070 2251229 := bbase (se 3 (by rfl) ⟨422105, by rfl⟩ : syracuseStep 2251229 = 844211) (by norm_num)
theorem B2136557 : Blo 1500070 2136557 := bbase (se 3 (by rfl) ⟨400604, by rfl⟩ : syracuseStep 2136557 = 801209) (by norm_num)
theorem B2251253 : Blo 1500070 2251253 := bbase (se 5 (by rfl) ⟨105527, by rfl⟩ : syracuseStep 2251253 = 211055) (by norm_num)
theorem B2251277 : Blo 1500070 2251277 := bbase (se 3 (by rfl) ⟨422114, by rfl⟩ : syracuseStep 2251277 = 844229) (by norm_num)
theorem B2251301 : Blo 1500070 2251301 := bbase (se 4 (by rfl) ⟨211059, by rfl⟩ : syracuseStep 2251301 = 422119) (by norm_num)
theorem B1899065 : Blo 1500070 1899065 := bbase (se 2 (by rfl) ⟨712149, by rfl⟩ : syracuseStep 1899065 = 1424299) (by norm_num)
theorem B2251325 : Blo 1500070 2251325 := bbase (se 3 (by rfl) ⟨422123, by rfl⟩ : syracuseStep 2251325 = 844247) (by norm_num)
theorem B2849357 : Blo 1500070 2849357 := bbase (se 3 (by rfl) ⟨534254, by rfl⟩ : syracuseStep 2849357 = 1068509) (by norm_num)
theorem B2251349 : Blo 1500070 2251349 := bbase (se 8 (by rfl) ⟨13191, by rfl⟩ : syracuseStep 2251349 = 26383) (by norm_num)
theorem B2251373 : Blo 1500070 2251373 := bbase (se 3 (by rfl) ⟨422132, by rfl⟩ : syracuseStep 2251373 = 844265) (by norm_num)
theorem B1899121 : Blo 1500070 1899121 := bbase (se 2 (by rfl) ⟨712170, by rfl⟩ : syracuseStep 1899121 = 1424341) (by norm_num)
theorem B3799669 : Blo 1500070 3799669 := bbase (se 5 (by rfl) ⟨178109, by rfl⟩ : syracuseStep 3799669 = 356219) (by norm_num)
theorem B2251397 : Blo 1500070 2251397 := bbase (se 4 (by rfl) ⟨211068, by rfl⟩ : syracuseStep 2251397 = 422137) (by norm_num)
theorem B5077637 : Blo 1500070 5077637 := bbase (se 4 (by rfl) ⟨476028, by rfl⟩ : syracuseStep 5077637 = 952057) (by norm_num)
theorem B2251421 : Blo 1500070 2251421 := bbase (se 3 (by rfl) ⟨422141, by rfl⟩ : syracuseStep 2251421 = 844283) (by norm_num)
theorem B2603677 : Blo 1500070 2603677 := bbase (se 3 (by rfl) ⟨488189, by rfl⟩ : syracuseStep 2603677 = 976379) (by norm_num)
theorem B2251445 : Blo 1500070 2251445 := bbase (se 5 (by rfl) ⟨105536, by rfl⟩ : syracuseStep 2251445 = 211073) (by norm_num)
theorem B2251469 : Blo 1500070 2251469 := bbase (se 3 (by rfl) ⟨422150, by rfl⟩ : syracuseStep 2251469 = 844301) (by norm_num)
theorem B1899217 : Blo 1500070 1899217 := bbase (se 2 (by rfl) ⟨712206, by rfl⟩ : syracuseStep 1899217 = 1424413) (by norm_num)
theorem B2849509 : Blo 1500070 2849509 := bbase (se 4 (by rfl) ⟨267141, by rfl⟩ : syracuseStep 2849509 = 534283) (by norm_num)
theorem B2251493 : Blo 1500070 2251493 := bbase (se 4 (by rfl) ⟨211077, by rfl⟩ : syracuseStep 2251493 = 422155) (by norm_num)
theorem B3799781 : Blo 1500070 3799781 := bbase (se 4 (by rfl) ⟨356229, by rfl⟩ : syracuseStep 3799781 = 712459) (by norm_num)
theorem B2251517 : Blo 1500070 2251517 := bbase (se 3 (by rfl) ⟨422159, by rfl⟩ : syracuseStep 2251517 = 844319) (by norm_num)
theorem B2251541 : Blo 1500070 2251541 := bbase (se 6 (by rfl) ⟨52770, by rfl⟩ : syracuseStep 2251541 = 105541) (by norm_num)
theorem B9132821 : Blo 1500070 9132821 := bbase (se 6 (by rfl) ⟨214050, by rfl⟩ : syracuseStep 9132821 = 428101) (by norm_num)
theorem B2251565 : Blo 1500070 2251565 := bbase (se 3 (by rfl) ⟨422168, by rfl⟩ : syracuseStep 2251565 = 844337) (by norm_num)
theorem B1522477 : Blo 1500070 1522477 := bbase (se 3 (by rfl) ⟨285464, by rfl⟩ : syracuseStep 1522477 = 570929) (by norm_num)
theorem B2251589 : Blo 1500070 2251589 := bbase (se 4 (by rfl) ⟨211086, by rfl⟩ : syracuseStep 2251589 = 422173) (by norm_num)
theorem B2251613 : Blo 1500070 2251613 := bbase (se 3 (by rfl) ⟨422177, by rfl⟩ : syracuseStep 2251613 = 844355) (by norm_num)
theorem B2251637 : Blo 1500070 2251637 := bbase (se 5 (by rfl) ⟨105545, by rfl⟩ : syracuseStep 2251637 = 211091) (by norm_num)
theorem B1899389 : Blo 1500070 1899389 := bbase (se 3 (by rfl) ⟨356135, by rfl⟩ : syracuseStep 1899389 = 712271) (by norm_num)
theorem B2251661 : Blo 1500070 2251661 := bbase (se 3 (by rfl) ⟨422186, by rfl⟩ : syracuseStep 2251661 = 844373) (by norm_num)
theorem B2251685 : Blo 1500070 2251685 := bbase (se 4 (by rfl) ⟨211095, by rfl⟩ : syracuseStep 2251685 = 422191) (by norm_num)
theorem B3799973 : Blo 1500070 3799973 := bbase (se 4 (by rfl) ⟨356247, by rfl⟩ : syracuseStep 3799973 = 712495) (by norm_num)
theorem B1899445 : Blo 1500070 1899445 := bbase (se 5 (by rfl) ⟨89036, by rfl⟩ : syracuseStep 1899445 = 178073) (by norm_num)
theorem B2251709 : Blo 1500070 2251709 := bbase (se 3 (by rfl) ⟨422195, by rfl⟩ : syracuseStep 2251709 = 844391) (by norm_num)
theorem B2251733 : Blo 1500070 2251733 := bbase (se 7 (by rfl) ⟨26387, by rfl⟩ : syracuseStep 2251733 = 52775) (by norm_num)
theorem B1711081 : Blo 1500070 1711081 := bbase (se 2 (by rfl) ⟨641655, by rfl⟩ : syracuseStep 1711081 = 1283311) (by norm_num)
theorem B2251757 : Blo 1500070 2251757 := bbase (se 3 (by rfl) ⟨422204, by rfl⟩ : syracuseStep 2251757 = 844409) (by norm_num)
theorem B2251781 : Blo 1500070 2251781 := bbase (se 4 (by rfl) ⟨211104, by rfl⟩ : syracuseStep 2251781 = 422209) (by norm_num)
theorem B1899541 : Blo 1500070 1899541 := bbase (se 6 (by rfl) ⟨44520, by rfl⟩ : syracuseStep 1899541 = 89041) (by norm_num)
theorem B2137109 : Blo 1500070 2137109 := bbase (se 6 (by rfl) ⟨50088, by rfl⟩ : syracuseStep 2137109 = 100177) (by norm_num)
theorem B2849813 : Blo 1500070 2849813 := bbase (se 6 (by rfl) ⟨66792, by rfl⟩ : syracuseStep 2849813 = 133585) (by norm_num)
theorem B2251805 : Blo 1500070 2251805 := bbase (se 3 (by rfl) ⟨422213, by rfl⟩ : syracuseStep 2251805 = 844427) (by norm_num)
theorem B2251829 : Blo 1500070 2251829 := bbase (se 5 (by rfl) ⟨105554, by rfl⟩ : syracuseStep 2251829 = 211109) (by norm_num)
theorem B2251853 : Blo 1500070 2251853 := bbase (se 3 (by rfl) ⟨422222, by rfl⟩ : syracuseStep 2251853 = 844445) (by norm_num)
theorem B2251877 : Blo 1500070 2251877 := bbase (se 4 (by rfl) ⟨211113, by rfl⟩ : syracuseStep 2251877 = 422227) (by norm_num)
theorem B4275301 : Blo 1500070 4275301 := bbase (se 4 (by rfl) ⟨400809, by rfl⟩ : syracuseStep 4275301 = 801619) (by norm_num)
theorem B2251901 : Blo 1500070 2251901 := bbase (se 3 (by rfl) ⟨422231, by rfl⟩ : syracuseStep 2251901 = 844463) (by norm_num)
theorem B2251925 : Blo 1500070 2251925 := bbase (se 6 (by rfl) ⟨52779, by rfl⟩ : syracuseStep 2251925 = 105559) (by norm_num)
theorem B2251949 : Blo 1500070 2251949 := bbase (se 3 (by rfl) ⟨422240, by rfl⟩ : syracuseStep 2251949 = 844481) (by norm_num)
theorem B7699637 : Blo 1500070 7699637 := bbase (se 5 (by rfl) ⟨360920, by rfl⟩ : syracuseStep 7699637 = 721841) (by norm_num)
theorem B1899713 : Blo 1500070 1899713 := bbase (se 2 (by rfl) ⟨712392, by rfl⟩ : syracuseStep 1899713 = 1424785) (by norm_num)
theorem B2251973 : Blo 1500070 2251973 := bbase (se 4 (by rfl) ⟨211122, by rfl⟩ : syracuseStep 2251973 = 422245) (by norm_num)
theorem B2251997 : Blo 1500070 2251997 := bbase (se 3 (by rfl) ⟨422249, by rfl⟩ : syracuseStep 2251997 = 844499) (by norm_num)
theorem B2252021 : Blo 1500070 2252021 := bbase (se 5 (by rfl) ⟨105563, by rfl⟩ : syracuseStep 2252021 = 211127) (by norm_num)
theorem B1899769 : Blo 1500070 1899769 := bbase (se 2 (by rfl) ⟨712413, by rfl⟩ : syracuseStep 1899769 = 1424827) (by norm_num)
theorem B3800317 : Blo 1500070 3800317 := bbase (se 3 (by rfl) ⟨712559, by rfl⟩ : syracuseStep 3800317 = 1425119) (by norm_num)
theorem B2252045 : Blo 1500070 2252045 := bbase (se 3 (by rfl) ⟨422258, by rfl⟩ : syracuseStep 2252045 = 844517) (by norm_num)
theorem B2252069 : Blo 1500070 2252069 := bbase (se 4 (by rfl) ⟨211131, by rfl⟩ : syracuseStep 2252069 = 422263) (by norm_num)
theorem B5700901 : Blo 1500070 5700901 := bbase (se 4 (by rfl) ⟨534459, by rfl⟩ : syracuseStep 5700901 = 1068919) (by norm_num)
theorem B2252093 : Blo 1500070 2252093 := bbase (se 3 (by rfl) ⟨422267, by rfl⟩ : syracuseStep 2252093 = 844535) (by norm_num)
theorem B2252117 : Blo 1500070 2252117 := bbase (se 11 (by rfl) ⟨1649, by rfl⟩ : syracuseStep 2252117 = 3299) (by norm_num)
theorem B1899865 : Blo 1500070 1899865 := bbase (se 2 (by rfl) ⟨712449, by rfl⟩ : syracuseStep 1899865 = 1424899) (by norm_num)
theorem B3800429 : Blo 1500070 3800429 := bbase (se 3 (by rfl) ⟨712580, by rfl⟩ : syracuseStep 3800429 = 1425161) (by norm_num)
theorem B2252141 : Blo 1500070 2252141 := bbase (se 3 (by rfl) ⟨422276, by rfl⟩ : syracuseStep 2252141 = 844553) (by norm_num)
theorem B7601525 : Blo 1500070 7601525 := bbase (se 5 (by rfl) ⟨356321, by rfl⟩ : syracuseStep 7601525 = 712643) (by norm_num)
theorem B2252165 : Blo 1500070 2252165 := bbase (se 4 (by rfl) ⟨211140, by rfl⟩ : syracuseStep 2252165 = 422281) (by norm_num)
theorem B2252189 : Blo 1500070 2252189 := bbase (se 3 (by rfl) ⟨422285, by rfl⟩ : syracuseStep 2252189 = 844571) (by norm_num)
theorem B2252213 : Blo 1500070 2252213 := bbase (se 5 (by rfl) ⟨105572, by rfl⟩ : syracuseStep 2252213 = 211145) (by norm_num)
theorem B2252237 : Blo 1500070 2252237 := bbase (se 3 (by rfl) ⟨422294, by rfl⟩ : syracuseStep 2252237 = 844589) (by norm_num)
theorem B2252261 : Blo 1500070 2252261 := bbase (se 4 (by rfl) ⟨211149, by rfl⟩ : syracuseStep 2252261 = 422299) (by norm_num)
theorem B2252285 : Blo 1500070 2252285 := bbase (se 3 (by rfl) ⟨422303, by rfl⟩ : syracuseStep 2252285 = 844607) (by norm_num)
theorem B1900037 : Blo 1500070 1900037 := bbase (se 4 (by rfl) ⟨178128, by rfl⟩ : syracuseStep 1900037 = 356257) (by norm_num)
theorem B2252309 : Blo 1500070 2252309 := bbase (se 6 (by rfl) ⟨52788, by rfl⟩ : syracuseStep 2252309 = 105577) (by norm_num)
theorem B3800621 : Blo 1500070 3800621 := bbase (se 3 (by rfl) ⟨712616, by rfl⟩ : syracuseStep 3800621 = 1425233) (by norm_num)
theorem B2252333 : Blo 1500070 2252333 := bbase (se 3 (by rfl) ⟨422312, by rfl⟩ : syracuseStep 2252333 = 844625) (by norm_num)
theorem B1900093 : Blo 1500070 1900093 := bbase (se 3 (by rfl) ⟨356267, by rfl⟩ : syracuseStep 1900093 = 712535) (by norm_num)
theorem B2252357 : Blo 1500070 2252357 := bbase (se 4 (by rfl) ⟨211158, by rfl⟩ : syracuseStep 2252357 = 422317) (by norm_num)
theorem B5701205 : Blo 1500070 5701205 := bbase (se 8 (by rfl) ⟨33405, by rfl⟩ : syracuseStep 5701205 = 66811) (by norm_num)
theorem B2252381 : Blo 1500070 2252381 := bbase (se 3 (by rfl) ⟨422321, by rfl⟩ : syracuseStep 2252381 = 844643) (by norm_num)
theorem B2252405 : Blo 1500070 2252405 := bbase (se 5 (by rfl) ⟨105581, by rfl⟩ : syracuseStep 2252405 = 211163) (by norm_num)
theorem B2252429 : Blo 1500070 2252429 := bbase (se 3 (by rfl) ⟨422330, by rfl⟩ : syracuseStep 2252429 = 844661) (by norm_num)
theorem B1900189 : Blo 1500070 1900189 := bbase (se 3 (by rfl) ⟨356285, by rfl⟩ : syracuseStep 1900189 = 712571) (by norm_num)
theorem B2252453 : Blo 1500070 2252453 := bbase (se 4 (by rfl) ⟨211167, by rfl⟩ : syracuseStep 2252453 = 422335) (by norm_num)
theorem B1564337 : Blo 1500070 1564337 := bbase (se 2 (by rfl) ⟨586626, by rfl⟩ : syracuseStep 1564337 = 1173253) (by norm_num)
theorem B2252477 : Blo 1500070 2252477 := bbase (se 3 (by rfl) ⟨422339, by rfl⟩ : syracuseStep 2252477 = 844679) (by norm_num)
theorem B2252501 : Blo 1500070 2252501 := bbase (se 7 (by rfl) ⟨26396, by rfl⟩ : syracuseStep 2252501 = 52793) (by norm_num)
theorem B1564381 : Blo 1500070 1564381 := bbase (se 3 (by rfl) ⟨293321, by rfl⟩ : syracuseStep 1564381 = 586643) (by norm_num)
theorem B2252525 : Blo 1500070 2252525 := bbase (se 3 (by rfl) ⟨422348, by rfl⟩ : syracuseStep 2252525 = 844697) (by norm_num)
theorem B2137861 : Blo 1500070 2137861 := bbase (se 4 (by rfl) ⟨200424, by rfl⟩ : syracuseStep 2137861 = 400849) (by norm_num)
theorem B2850565 : Blo 1500070 2850565 := bbase (se 4 (by rfl) ⟨267240, by rfl⟩ : syracuseStep 2850565 = 534481) (by norm_num)
theorem B2252549 : Blo 1500070 2252549 := bbase (se 4 (by rfl) ⟨211176, by rfl⟩ : syracuseStep 2252549 = 422353) (by norm_num)
theorem B10821397 : Blo 1500070 10821397 := bbase (se 6 (by rfl) ⟨253626, by rfl⟩ : syracuseStep 10821397 = 507253) (by norm_num)
theorem B2252573 : Blo 1500070 2252573 := bbase (se 3 (by rfl) ⟨422357, by rfl⟩ : syracuseStep 2252573 = 844715) (by norm_num)
theorem B2252597 : Blo 1500070 2252597 := bbase (se 5 (by rfl) ⟨105590, by rfl⟩ : syracuseStep 2252597 = 211181) (by norm_num)
theorem B1900361 : Blo 1500070 1900361 := bbase (se 2 (by rfl) ⟨712635, by rfl⟩ : syracuseStep 1900361 = 1425271) (by norm_num)
theorem B2252621 : Blo 1500070 2252621 := bbase (se 3 (by rfl) ⟨422366, by rfl⟩ : syracuseStep 2252621 = 844733) (by norm_num)
theorem B2252645 : Blo 1500070 2252645 := bbase (se 4 (by rfl) ⟨211185, by rfl⟩ : syracuseStep 2252645 = 422371) (by norm_num)
theorem B2252669 : Blo 1500070 2252669 := bbase (se 3 (by rfl) ⟨422375, by rfl⟩ : syracuseStep 2252669 = 844751) (by norm_num)
theorem B1900417 : Blo 1500070 1900417 := bbase (se 2 (by rfl) ⟨712656, by rfl⟩ : syracuseStep 1900417 = 1425313) (by norm_num)
theorem B3800965 : Blo 1500070 3800965 := bbase (se 4 (by rfl) ⟨356340, by rfl⟩ : syracuseStep 3800965 = 712681) (by norm_num)
theorem B2850709 : Blo 1500070 2850709 := bbase (se 6 (by rfl) ⟨66813, by rfl⟩ : syracuseStep 2850709 = 133627) (by norm_num)
theorem B2252693 : Blo 1500070 2252693 := bbase (se 6 (by rfl) ⟨52797, by rfl⟩ : syracuseStep 2252693 = 105595) (by norm_num)
theorem B2252717 : Blo 1500070 2252717 := bbase (se 3 (by rfl) ⟨422384, by rfl⟩ : syracuseStep 2252717 = 844769) (by norm_num)
theorem B2252741 : Blo 1500070 2252741 := bbase (se 4 (by rfl) ⟨211194, by rfl⟩ : syracuseStep 2252741 = 422389) (by norm_num)
theorem B2252765 : Blo 1500070 2252765 := bbase (se 3 (by rfl) ⟨422393, by rfl⟩ : syracuseStep 2252765 = 844787) (by norm_num)
theorem B1900513 : Blo 1500070 1900513 := bbase (se 2 (by rfl) ⟨712692, by rfl⟩ : syracuseStep 1900513 = 1425385) (by norm_num)
theorem B3801077 : Blo 1500070 3801077 := bbase (se 5 (by rfl) ⟨178175, by rfl⟩ : syracuseStep 3801077 = 356351) (by norm_num)
theorem B2252789 : Blo 1500070 2252789 := bbase (se 5 (by rfl) ⟨105599, by rfl⟩ : syracuseStep 2252789 = 211199) (by norm_num)
theorem B2252801 : Blo 1500070 2252801 := bstep (se 2 (by rfl) ⟨844800, by rfl⟩ : syracuseStep 2252801 = 1689601) B1689601
theorem B2252819 : Blo 1500070 2252819 := bstep (se 1 (by rfl) ⟨1689614, by rfl⟩ : syracuseStep 2252819 = 3379229) B3379229
theorem B1900579 : Blo 1500070 1900579 := bstep (se 1 (by rfl) ⟨1425434, by rfl⟩ : syracuseStep 1900579 = 2850869) B2850869
theorem B4808753 : Blo 1500070 4808753 := bstep (se 2 (by rfl) ⟨1803282, by rfl⟩ : syracuseStep 4808753 = 3606565) B3606565
theorem B2252849 : Blo 1500070 2252849 := bstep (se 2 (by rfl) ⟨844818, by rfl⟩ : syracuseStep 2252849 = 1689637) B1689637
theorem B1687603 : Blo 1500070 1687603 := bstep (se 1 (by rfl) ⟨1265702, by rfl⟩ : syracuseStep 1687603 = 2531405) B2531405
theorem B2252867 : Blo 1500070 2252867 := bstep (se 1 (by rfl) ⟨1689650, by rfl⟩ : syracuseStep 2252867 = 3379301) B3379301
theorem B3850321 : Blo 1500070 3850321 := bstep (se 2 (by rfl) ⟨1443870, by rfl⟩ : syracuseStep 3850321 = 2887741) B2887741
theorem B2531425 : Blo 1500070 2531425 := bstep (se 2 (by rfl) ⟨949284, by rfl⟩ : syracuseStep 2531425 = 1898569) B1898569
theorem B2252897 : Blo 1500070 2252897 := bstep (se 2 (by rfl) ⟨844836, by rfl⟩ : syracuseStep 2252897 = 1689673) B1689673
theorem B4808803 : Blo 1500070 4808803 := bstep (se 1 (by rfl) ⟨3606602, by rfl⟩ : syracuseStep 4808803 = 7213205) B7213205
theorem B5062769 : Blo 1500070 5062769 := bstep (se 2 (by rfl) ⟨1898538, by rfl⟩ : syracuseStep 5062769 = 3797077) B3797077
theorem B2252915 : Blo 1500070 2252915 := bstep (se 1 (by rfl) ⟨1689686, by rfl⟩ : syracuseStep 2252915 = 3379373) B3379373
theorem B2531459 : Blo 1500070 2531459 := bstep (se 1 (by rfl) ⟨1898594, by rfl⟩ : syracuseStep 2531459 = 3797189) B3797189
theorem B1900675 : Blo 1500070 1900675 := bstep (se 1 (by rfl) ⟨1425506, by rfl⟩ : syracuseStep 1900675 = 2851013) B2851013
theorem B3604625 : Blo 1500070 3604625 := bstep (se 2 (by rfl) ⟨1351734, by rfl⟩ : syracuseStep 3604625 = 2703469) B2703469
theorem B2252945 : Blo 1500070 2252945 := bstep (se 2 (by rfl) ⟨844854, by rfl⟩ : syracuseStep 2252945 = 1689709) B1689709
theorem B2252963 : Blo 1500070 2252963 := bstep (se 1 (by rfl) ⟨1689722, by rfl⟩ : syracuseStep 2252963 = 3379445) B3379445
theorem B2252993 : Blo 1500070 2252993 := bstep (se 2 (by rfl) ⟨844872, by rfl⟩ : syracuseStep 2252993 = 1689745) B1689745
theorem B1687747 : Blo 1500070 1687747 := bstep (se 1 (by rfl) ⟨1265810, by rfl⟩ : syracuseStep 1687747 = 2531621) B2531621
theorem B2253011 : Blo 1500070 2253011 := bstep (se 1 (by rfl) ⟨1689758, by rfl⟩ : syracuseStep 2253011 = 3379517) B3379517
theorem B21627107 : Blo 1500070 21627107 := bstep (se 1 (by rfl) ⟨16220330, by rfl⟩ : syracuseStep 21627107 = 32440661) B32440661
theorem B5701859 : Blo 1500070 5701859 := bstep (se 1 (by rfl) ⟨4276394, by rfl⟩ : syracuseStep 5701859 = 8552789) B8552789
theorem B4276451 : Blo 1500070 4276451 := bstep (se 1 (by rfl) ⟨3207338, by rfl⟩ : syracuseStep 4276451 = 6414677) B6414677
theorem B5701873 : Blo 1500070 5701873 := bstep (se 2 (by rfl) ⟨2138202, by rfl⟩ : syracuseStep 5701873 = 4276405) B4276405
theorem B2253041 : Blo 1500070 2253041 := bstep (se 2 (by rfl) ⟨844890, by rfl⟩ : syracuseStep 2253041 = 1689781) B1689781
theorem B2531587 : Blo 1500070 2531587 := bstep (se 1 (by rfl) ⟨1898690, by rfl⟩ : syracuseStep 2531587 = 3797381) B3797381
theorem B2253059 : Blo 1500070 2253059 := bstep (se 1 (by rfl) ⟨1689794, by rfl⟩ : syracuseStep 2253059 = 3379589) B3379589
theorem B3375377 : Blo 1500070 3375377 := bstep (se 2 (by rfl) ⟨1265766, by rfl⟩ : syracuseStep 3375377 = 2531533) B2531533
theorem B2253089 : Blo 1500070 2253089 := bstep (se 2 (by rfl) ⟨844908, by rfl⟩ : syracuseStep 2253089 = 1689817) B1689817
theorem B3375395 : Blo 1500070 3375395 := bstep (se 1 (by rfl) ⟨2531546, by rfl⟩ : syracuseStep 3375395 = 5063093) B5063093
theorem B7414051 : Blo 1500070 7414051 := bstep (se 1 (by rfl) ⟨5560538, by rfl⟩ : syracuseStep 7414051 = 11121077) B11121077
theorem B4333873 : Blo 1500070 4333873 := bstep (se 2 (by rfl) ⟨1625202, by rfl⟩ : syracuseStep 4333873 = 3250405) B3250405
theorem B1687891 : Blo 1500070 1687891 := bstep (se 1 (by rfl) ⟨1265918, by rfl⟩ : syracuseStep 1687891 = 2531837) B2531837
theorem B2531729 : Blo 1500070 2531729 := bstep (se 2 (by rfl) ⟨949398, by rfl⟩ : syracuseStep 2531729 = 1898797) B1898797
theorem B2703793 : Blo 1500070 2703793 := bstep (se 2 (by rfl) ⟨1013922, by rfl⟩ : syracuseStep 2703793 = 2027845) B2027845
theorem B1688035 : Blo 1500070 1688035 := bstep (se 1 (by rfl) ⟨1266026, by rfl⟩ : syracuseStep 1688035 = 2532053) B2532053
theorem B7602659 : Blo 1500070 7602659 := bstep (se 1 (by rfl) ⟨5701994, by rfl⟩ : syracuseStep 7602659 = 11403989) B11403989
theorem B2531857 : Blo 1500070 2531857 := bstep (se 2 (by rfl) ⟨949446, by rfl⟩ : syracuseStep 2531857 = 1898893) B1898893
theorem B3375665 : Blo 1500070 3375665 := bstep (se 2 (by rfl) ⟨1265874, by rfl⟩ : syracuseStep 3375665 = 2531749) B2531749
theorem B2531891 : Blo 1500070 2531891 := bstep (se 1 (by rfl) ⟨1898918, by rfl⟩ : syracuseStep 2531891 = 3797837) B3797837
theorem B3375683 : Blo 1500070 3375683 := bstep (se 1 (by rfl) ⟨2531762, by rfl⟩ : syracuseStep 3375683 = 5063525) B5063525
theorem B1688179 : Blo 1500070 1688179 := bstep (se 1 (by rfl) ⟨1266134, by rfl⟩ : syracuseStep 1688179 = 2532269) B2532269
theorem B5063309 : Blo 1500070 5063309 := bstep (se 3 (by rfl) ⟨949370, by rfl⟩ : syracuseStep 5063309 = 1898741) B1898741
theorem B2532019 : Blo 1500070 2532019 := bstep (se 1 (by rfl) ⟨1899014, by rfl⟩ : syracuseStep 2532019 = 3798029) B3798029
theorem B5063363 : Blo 1500070 5063363 := bstep (se 1 (by rfl) ⟨3797522, by rfl⟩ : syracuseStep 5063363 = 7595045) B7595045
theorem B8544973 : Blo 1500070 8544973 := bstep (se 3 (by rfl) ⟨1602182, by rfl⟩ : syracuseStep 8544973 = 3204365) B3204365
theorem B2851537 : Blo 1500070 2851537 := bstep (se 2 (by rfl) ⟨1069326, by rfl⟩ : syracuseStep 2851537 = 2138653) B2138653
theorem B3605219 : Blo 1500070 3605219 := bstep (se 1 (by rfl) ⟨2703914, by rfl⟩ : syracuseStep 3605219 = 5407829) B5407829
theorem B11715299 : Blo 1500070 11715299 := bstep (se 1 (by rfl) ⟨8786474, by rfl⟩ : syracuseStep 11715299 = 17572949) B17572949
theorem B1688323 : Blo 1500070 1688323 := bstep (se 1 (by rfl) ⟨1266242, by rfl⟩ : syracuseStep 1688323 = 2532485) B2532485
theorem B8553221 : Blo 1500070 8553221 := bstep (se 4 (by rfl) ⟨801864, by rfl⟩ : syracuseStep 8553221 = 1603729) B1603729
theorem B6415139 : Blo 1500070 6415139 := bstep (se 1 (by rfl) ⟨4811354, by rfl⟩ : syracuseStep 6415139 = 9622709) B9622709
theorem B2532161 : Blo 1500070 2532161 := bstep (se 2 (by rfl) ⟨949560, by rfl⟩ : syracuseStep 2532161 = 1899121) B1899121
theorem B3605315 : Blo 1500070 3605315 := bstep (se 1 (by rfl) ⟨2703986, by rfl⟩ : syracuseStep 3605315 = 5407973) B5407973
theorem B3203921 : Blo 1500070 3203921 := bstep (se 2 (by rfl) ⟨1201470, by rfl⟩ : syracuseStep 3203921 = 2402941) B2402941
theorem B3375953 : Blo 1500070 3375953 := bstep (se 2 (by rfl) ⟨1265982, by rfl⟩ : syracuseStep 3375953 = 2531965) B2531965
theorem B3801937 : Blo 1500070 3801937 := bstep (se 2 (by rfl) ⟨1425726, by rfl⟩ : syracuseStep 3801937 = 2851453) B2851453
theorem B3375971 : Blo 1500070 3375971 := bstep (se 1 (by rfl) ⟨2531978, by rfl⟩ : syracuseStep 3375971 = 5063957) B5063957
theorem B1852291 : Blo 1500070 1852291 := bstep (se 1 (by rfl) ⟨1389218, by rfl⟩ : syracuseStep 1852291 = 2778437) B2778437
theorem B4629379 : Blo 1500070 4629379 := bstep (se 1 (by rfl) ⟨3472034, by rfl⟩ : syracuseStep 4629379 = 6944069) B6944069
theorem B1688467 : Blo 1500070 1688467 := bstep (se 1 (by rfl) ⟨1266350, by rfl⟩ : syracuseStep 1688467 = 2532701) B2532701
theorem B1500083 : Blo 1500070 1500083 := bstep (se 1 (by rfl) ⟨1125062, by rfl⟩ : syracuseStep 1500083 = 2250125) B2250125
theorem B2532289 : Blo 1500070 2532289 := bstep (se 2 (by rfl) ⟨949608, by rfl⟩ : syracuseStep 2532289 = 1899217) B1899217
theorem B1500099 : Blo 1500070 1500099 := bstep (se 1 (by rfl) ⟨1125074, by rfl⟩ : syracuseStep 1500099 = 2250149) B2250149
theorem B5063633 : Blo 1500070 5063633 := bstep (se 2 (by rfl) ⟨1898862, by rfl⟩ : syracuseStep 5063633 = 3797725) B3797725
theorem B1500115 : Blo 1500070 1500115 := bstep (se 1 (by rfl) ⟨1125086, by rfl⟩ : syracuseStep 1500115 = 2250173) B2250173
theorem B1500131 : Blo 1500070 1500131 := bstep (se 1 (by rfl) ⟨1125098, by rfl⟩ : syracuseStep 1500131 = 2250197) B2250197
theorem B2532323 : Blo 1500070 2532323 := bstep (se 1 (by rfl) ⟨1899242, by rfl⟩ : syracuseStep 2532323 = 3798485) B3798485
theorem B1803235 : Blo 1500070 1803235 := bstep (se 1 (by rfl) ⟨1352426, by rfl⟩ : syracuseStep 1803235 = 2704853) B2704853
theorem B1500147 : Blo 1500070 1500147 := bstep (se 1 (by rfl) ⟨1125110, by rfl⟩ : syracuseStep 1500147 = 2250221) B2250221
theorem B1500163 : Blo 1500070 1500163 := bstep (se 1 (by rfl) ⟨1125122, by rfl⟩ : syracuseStep 1500163 = 2250245) B2250245
theorem B1500179 : Blo 1500070 1500179 := bstep (se 1 (by rfl) ⟨1125134, by rfl⟩ : syracuseStep 1500179 = 2250269) B2250269
theorem B1500195 : Blo 1500070 1500195 := bstep (se 1 (by rfl) ⟨1125146, by rfl⟩ : syracuseStep 1500195 = 2250293) B2250293
theorem B1688611 : Blo 1500070 1688611 := bstep (se 1 (by rfl) ⟨1266458, by rfl⟩ : syracuseStep 1688611 = 2532917) B2532917
theorem B1500211 : Blo 1500070 1500211 := bstep (se 1 (by rfl) ⟨1125158, by rfl⟩ : syracuseStep 1500211 = 2250317) B2250317
theorem B1500227 : Blo 1500070 1500227 := bstep (se 1 (by rfl) ⟨1125170, by rfl⟩ : syracuseStep 1500227 = 2250341) B2250341
theorem B4056131 : Blo 1500070 4056131 := bstep (se 1 (by rfl) ⟨3042098, by rfl⟩ : syracuseStep 4056131 = 6084197) B6084197
theorem B1500243 : Blo 1500070 1500243 := bstep (se 1 (by rfl) ⟨1125182, by rfl⟩ : syracuseStep 1500243 = 2250365) B2250365
theorem B1500259 : Blo 1500070 1500259 := bstep (se 1 (by rfl) ⟨1125194, by rfl⟩ : syracuseStep 1500259 = 2250389) B2250389
theorem B2532451 : Blo 1500070 2532451 := bstep (se 1 (by rfl) ⟨1899338, by rfl⟩ : syracuseStep 2532451 = 3798677) B3798677
theorem B3376241 : Blo 1500070 3376241 := bstep (se 2 (by rfl) ⟨1266090, by rfl⟩ : syracuseStep 3376241 = 2532181) B2532181
theorem B1500275 : Blo 1500070 1500275 := bstep (se 1 (by rfl) ⟨1125206, by rfl⟩ : syracuseStep 1500275 = 2250413) B2250413
theorem B1500291 : Blo 1500070 1500291 := bstep (se 1 (by rfl) ⟨1125218, by rfl⟩ : syracuseStep 1500291 = 2250437) B2250437
theorem B3376259 : Blo 1500070 3376259 := bstep (se 1 (by rfl) ⟨2532194, by rfl⟩ : syracuseStep 3376259 = 5064389) B5064389
theorem B1500307 : Blo 1500070 1500307 := bstep (se 1 (by rfl) ⟨1125230, by rfl⟩ : syracuseStep 1500307 = 2250461) B2250461
theorem B1500323 : Blo 1500070 1500323 := bstep (se 1 (by rfl) ⟨1125242, by rfl⟩ : syracuseStep 1500323 = 2250485) B2250485
theorem B1500339 : Blo 1500070 1500339 := bstep (se 1 (by rfl) ⟨1125254, by rfl⟩ : syracuseStep 1500339 = 2250509) B2250509
theorem B1688755 : Blo 1500070 1688755 := bstep (se 1 (by rfl) ⟨1266566, by rfl⟩ : syracuseStep 1688755 = 2533133) B2533133
theorem B1500355 : Blo 1500070 1500355 := bstep (se 1 (by rfl) ⟨1125266, by rfl⟩ : syracuseStep 1500355 = 2250533) B2250533
theorem B1500371 : Blo 1500070 1500371 := bstep (se 1 (by rfl) ⟨1125278, by rfl⟩ : syracuseStep 1500371 = 2250557) B2250557
theorem B5932259 : Blo 1500070 5932259 := bstep (se 1 (by rfl) ⟨4449194, by rfl⟩ : syracuseStep 5932259 = 8898389) B8898389
theorem B1500387 : Blo 1500070 1500387 := bstep (se 1 (by rfl) ⟨1125290, by rfl⟩ : syracuseStep 1500387 = 2250581) B2250581
theorem B2532593 : Blo 1500070 2532593 := bstep (se 2 (by rfl) ⟨949722, by rfl⟩ : syracuseStep 2532593 = 1899445) B1899445
theorem B1500403 : Blo 1500070 1500403 := bstep (se 1 (by rfl) ⟨1125302, by rfl⟩ : syracuseStep 1500403 = 2250605) B2250605
theorem B1500419 : Blo 1500070 1500419 := bstep (se 1 (by rfl) ⟨1125314, by rfl⟩ : syracuseStep 1500419 = 2250629) B2250629
theorem B7603469 : Blo 1500070 7603469 := bstep (se 3 (by rfl) ⟨1425650, by rfl⟩ : syracuseStep 7603469 = 2851301) B2851301
theorem B1500435 : Blo 1500070 1500435 := bstep (se 1 (by rfl) ⟨1125326, by rfl⟩ : syracuseStep 1500435 = 2250653) B2250653
theorem B54740245 : Blo 1500070 54740245 := bstep (se 6 (by rfl) ⟨1282974, by rfl⟩ : syracuseStep 54740245 = 2565949) B2565949
theorem B1500451 : Blo 1500070 1500451 := bstep (se 1 (by rfl) ⟨1125338, by rfl⟩ : syracuseStep 1500451 = 2250677) B2250677
theorem B4810033 : Blo 1500070 4810033 := bstep (se 2 (by rfl) ⟨1803762, by rfl⟩ : syracuseStep 4810033 = 3607525) B3607525
theorem B1500467 : Blo 1500070 1500467 := bstep (se 1 (by rfl) ⟨1125350, by rfl⟩ : syracuseStep 1500467 = 2250701) B2250701
theorem B1500483 : Blo 1500070 1500483 := bstep (se 1 (by rfl) ⟨1125362, by rfl⟩ : syracuseStep 1500483 = 2250725) B2250725
theorem B1688899 : Blo 1500070 1688899 := bstep (se 1 (by rfl) ⟨1266674, by rfl⟩ : syracuseStep 1688899 = 2533349) B2533349
theorem B2704721 : Blo 1500070 2704721 := bstep (se 2 (by rfl) ⟨1014270, by rfl⟩ : syracuseStep 2704721 = 2028541) B2028541
theorem B1500499 : Blo 1500070 1500499 := bstep (se 1 (by rfl) ⟨1125374, by rfl⟩ : syracuseStep 1500499 = 2250749) B2250749
theorem B3204451 : Blo 1500070 3204451 := bstep (se 1 (by rfl) ⟨2403338, by rfl⟩ : syracuseStep 3204451 = 4806677) B4806677
theorem B1500515 : Blo 1500070 1500515 := bstep (se 1 (by rfl) ⟨1125386, by rfl⟩ : syracuseStep 1500515 = 2250773) B2250773
theorem B2532721 : Blo 1500070 2532721 := bstep (se 2 (by rfl) ⟨949770, by rfl⟩ : syracuseStep 2532721 = 1899541) B1899541
theorem B1500531 : Blo 1500070 1500531 := bstep (se 1 (by rfl) ⟨1125398, by rfl⟩ : syracuseStep 1500531 = 2250797) B2250797
theorem B1500547 : Blo 1500070 1500547 := bstep (se 1 (by rfl) ⟨1125410, by rfl⟩ : syracuseStep 1500547 = 2250821) B2250821
theorem B3376529 : Blo 1500070 3376529 := bstep (se 2 (by rfl) ⟨1266198, by rfl⟩ : syracuseStep 3376529 = 2532397) B2532397
theorem B1500563 : Blo 1500070 1500563 := bstep (se 1 (by rfl) ⟨1125422, by rfl⟩ : syracuseStep 1500563 = 2250845) B2250845
theorem B2532755 : Blo 1500070 2532755 := bstep (se 1 (by rfl) ⟨1899566, by rfl⟩ : syracuseStep 2532755 = 3799133) B3799133
theorem B1500579 : Blo 1500070 1500579 := bstep (se 1 (by rfl) ⟨1125434, by rfl⟩ : syracuseStep 1500579 = 2250869) B2250869
theorem B3376547 : Blo 1500070 3376547 := bstep (se 1 (by rfl) ⟨2532410, by rfl⟩ : syracuseStep 3376547 = 5064821) B5064821
theorem B1500595 : Blo 1500070 1500595 := bstep (se 1 (by rfl) ⟨1125446, by rfl⟩ : syracuseStep 1500595 = 2250893) B2250893
theorem B1500611 : Blo 1500070 1500611 := bstep (se 1 (by rfl) ⟨1125458, by rfl⟩ : syracuseStep 1500611 = 2250917) B2250917
theorem B92431813 : Blo 1500070 92431813 := bstep (se 4 (by rfl) ⟨8665482, by rfl⟩ : syracuseStep 92431813 = 17330965) B17330965
theorem B1500627 : Blo 1500070 1500627 := bstep (se 1 (by rfl) ⟨1125470, by rfl⟩ : syracuseStep 1500627 = 2250941) B2250941
theorem B1689043 : Blo 1500070 1689043 := bstep (se 1 (by rfl) ⟨1266782, by rfl⟩ : syracuseStep 1689043 = 2533565) B2533565
theorem B1500643 : Blo 1500070 1500643 := bstep (se 1 (by rfl) ⟨1125482, by rfl⟩ : syracuseStep 1500643 = 2250965) B2250965
theorem B5064173 : Blo 1500070 5064173 := bstep (se 3 (by rfl) ⟨949532, by rfl⟩ : syracuseStep 5064173 = 1899065) B1899065
theorem B1500659 : Blo 1500070 1500659 := bstep (se 1 (by rfl) ⟨1125494, by rfl⟩ : syracuseStep 1500659 = 2250989) B2250989
theorem B1500675 : Blo 1500070 1500675 := bstep (se 1 (by rfl) ⟨1125506, by rfl⟩ : syracuseStep 1500675 = 2251013) B2251013
theorem B1500691 : Blo 1500070 1500691 := bstep (se 1 (by rfl) ⟨1125518, by rfl⟩ : syracuseStep 1500691 = 2251037) B2251037
theorem B2532883 : Blo 1500070 2532883 := bstep (se 1 (by rfl) ⟨1899662, by rfl⟩ : syracuseStep 2532883 = 3799325) B3799325
theorem B5064227 : Blo 1500070 5064227 := bstep (se 1 (by rfl) ⟨3798170, by rfl⟩ : syracuseStep 5064227 = 7596341) B7596341
theorem B1500707 : Blo 1500070 1500707 := bstep (se 1 (by rfl) ⟨1125530, by rfl⟩ : syracuseStep 1500707 = 2251061) B2251061
theorem B1500723 : Blo 1500070 1500723 := bstep (se 1 (by rfl) ⟨1125542, by rfl⟩ : syracuseStep 1500723 = 2251085) B2251085
theorem B1500739 : Blo 1500070 1500739 := bstep (se 1 (by rfl) ⟨1125554, by rfl⟩ : syracuseStep 1500739 = 2251109) B2251109
theorem B1500755 : Blo 1500070 1500755 := bstep (se 1 (by rfl) ⟨1125566, by rfl⟩ : syracuseStep 1500755 = 2251133) B2251133
theorem B1500771 : Blo 1500070 1500771 := bstep (se 1 (by rfl) ⟨1125578, by rfl⟩ : syracuseStep 1500771 = 2251157) B2251157
theorem B1689187 : Blo 1500070 1689187 := bstep (se 1 (by rfl) ⟨1266890, by rfl⟩ : syracuseStep 1689187 = 2533781) B2533781
theorem B1500787 : Blo 1500070 1500787 := bstep (se 1 (by rfl) ⟨1125590, by rfl⟩ : syracuseStep 1500787 = 2251181) B2251181
theorem B1500803 : Blo 1500070 1500803 := bstep (se 1 (by rfl) ⟨1125602, by rfl⟩ : syracuseStep 1500803 = 2251205) B2251205
theorem B1500819 : Blo 1500070 1500819 := bstep (se 1 (by rfl) ⟨1125614, by rfl⟩ : syracuseStep 1500819 = 2251229) B2251229
theorem B2533025 : Blo 1500070 2533025 := bstep (se 2 (by rfl) ⟨949884, by rfl⟩ : syracuseStep 2533025 = 1899769) B1899769
theorem B1500835 : Blo 1500070 1500835 := bstep (se 1 (by rfl) ⟨1125626, by rfl⟩ : syracuseStep 1500835 = 2251253) B2251253
theorem B3376817 : Blo 1500070 3376817 := bstep (se 2 (by rfl) ⟨1266306, by rfl⟩ : syracuseStep 3376817 = 2532613) B2532613
theorem B1500851 : Blo 1500070 1500851 := bstep (se 1 (by rfl) ⟨1125638, by rfl⟩ : syracuseStep 1500851 = 2251277) B2251277
theorem B1803955 : Blo 1500070 1803955 := bstep (se 1 (by rfl) ⟨1352966, by rfl⟩ : syracuseStep 1803955 = 2705933) B2705933
theorem B3376835 : Blo 1500070 3376835 := bstep (se 1 (by rfl) ⟨2532626, by rfl⟩ : syracuseStep 3376835 = 5065253) B5065253
theorem B1500867 : Blo 1500070 1500867 := bstep (se 1 (by rfl) ⟨1125650, by rfl⟩ : syracuseStep 1500867 = 2251301) B2251301
theorem B1500883 : Blo 1500070 1500883 := bstep (se 1 (by rfl) ⟨1125662, by rfl⟩ : syracuseStep 1500883 = 2251325) B2251325
theorem B1500899 : Blo 1500070 1500899 := bstep (se 1 (by rfl) ⟨1125674, by rfl⟩ : syracuseStep 1500899 = 2251349) B2251349
theorem B3606257 : Blo 1500070 3606257 := bstep (se 2 (by rfl) ⟨1352346, by rfl⟩ : syracuseStep 3606257 = 2704693) B2704693
theorem B1500915 : Blo 1500070 1500915 := bstep (se 1 (by rfl) ⟨1125686, by rfl⟩ : syracuseStep 1500915 = 2251373) B2251373
theorem B1689331 : Blo 1500070 1689331 := bstep (se 1 (by rfl) ⟨1266998, by rfl⟩ : syracuseStep 1689331 = 2533997) B2533997
theorem B1500931 : Blo 1500070 1500931 := bstep (se 1 (by rfl) ⟨1125698, by rfl⟩ : syracuseStep 1500931 = 2251397) B2251397
theorem B3385091 : Blo 1500070 3385091 := bstep (se 1 (by rfl) ⟨2538818, by rfl⟩ : syracuseStep 3385091 = 5077637) B5077637
theorem B1500947 : Blo 1500070 1500947 := bstep (se 1 (by rfl) ⟨1125710, by rfl⟩ : syracuseStep 1500947 = 2251421) B2251421
theorem B1804051 : Blo 1500070 1804051 := bstep (se 1 (by rfl) ⟨1353038, by rfl⟩ : syracuseStep 1804051 = 2706077) B2706077
theorem B2533153 : Blo 1500070 2533153 := bstep (se 2 (by rfl) ⟨949932, by rfl⟩ : syracuseStep 2533153 = 1899865) B1899865
theorem B1500963 : Blo 1500070 1500963 := bstep (se 1 (by rfl) ⟨1125722, by rfl⟩ : syracuseStep 1500963 = 2251445) B2251445
theorem B4171565 : Blo 1500070 4171565 := bstep (se 3 (by rfl) ⟨782168, by rfl⟩ : syracuseStep 4171565 = 1564337) B1564337
theorem B5064497 : Blo 1500070 5064497 := bstep (se 2 (by rfl) ⟨1899186, by rfl⟩ : syracuseStep 5064497 = 3798373) B3798373
theorem B1500979 : Blo 1500070 1500979 := bstep (se 1 (by rfl) ⟨1125734, by rfl⟩ : syracuseStep 1500979 = 2251469) B2251469
theorem B1500995 : Blo 1500070 1500995 := bstep (se 1 (by rfl) ⟨1125746, by rfl⟩ : syracuseStep 1500995 = 2251493) B2251493
theorem B2533187 : Blo 1500070 2533187 := bstep (se 1 (by rfl) ⟨1899890, by rfl⟩ : syracuseStep 2533187 = 3799781) B3799781
theorem B1501011 : Blo 1500070 1501011 := bstep (se 1 (by rfl) ⟨1125758, by rfl⟩ : syracuseStep 1501011 = 2251517) B2251517
theorem B1501027 : Blo 1500070 1501027 := bstep (se 1 (by rfl) ⟨1125770, by rfl⟩ : syracuseStep 1501027 = 2251541) B2251541
theorem B6088547 : Blo 1500070 6088547 := bstep (se 1 (by rfl) ⟨4566410, by rfl⟩ : syracuseStep 6088547 = 9132821) B9132821
theorem B1501043 : Blo 1500070 1501043 := bstep (se 1 (by rfl) ⟨1125782, by rfl⟩ : syracuseStep 1501043 = 2251565) B2251565
theorem B1501059 : Blo 1500070 1501059 := bstep (se 1 (by rfl) ⟨1125794, by rfl⟩ : syracuseStep 1501059 = 2251589) B2251589
theorem B1689475 : Blo 1500070 1689475 := bstep (se 1 (by rfl) ⟨1267106, by rfl⟩ : syracuseStep 1689475 = 2534213) B2534213
theorem B1501075 : Blo 1500070 1501075 := bstep (se 1 (by rfl) ⟨1125806, by rfl⟩ : syracuseStep 1501075 = 2251613) B2251613
theorem B1501091 : Blo 1500070 1501091 := bstep (se 1 (by rfl) ⟨1125818, by rfl⟩ : syracuseStep 1501091 = 2251637) B2251637
theorem B1501107 : Blo 1500070 1501107 := bstep (se 1 (by rfl) ⟨1125830, by rfl⟩ : syracuseStep 1501107 = 2251661) B2251661
theorem B1501123 : Blo 1500070 1501123 := bstep (se 1 (by rfl) ⟨1125842, by rfl⟩ : syracuseStep 1501123 = 2251685) B2251685
theorem B2533315 : Blo 1500070 2533315 := bstep (se 1 (by rfl) ⟨1899986, by rfl⟩ : syracuseStep 2533315 = 3799973) B3799973
theorem B3377105 : Blo 1500070 3377105 := bstep (se 2 (by rfl) ⟨1266414, by rfl⟩ : syracuseStep 3377105 = 2532829) B2532829
theorem B1501139 : Blo 1500070 1501139 := bstep (se 1 (by rfl) ⟨1125854, by rfl⟩ : syracuseStep 1501139 = 2251709) B2251709
theorem B3377123 : Blo 1500070 3377123 := bstep (se 1 (by rfl) ⟨2532842, by rfl⟩ : syracuseStep 3377123 = 5065685) B5065685
theorem B1501155 : Blo 1500070 1501155 := bstep (se 1 (by rfl) ⟨1125866, by rfl⟩ : syracuseStep 1501155 = 2251733) B2251733
theorem B7596017 : Blo 1500070 7596017 := bstep (se 2 (by rfl) ⟨2848506, by rfl⟩ : syracuseStep 7596017 = 5697013) B5697013
theorem B1501171 : Blo 1500070 1501171 := bstep (se 1 (by rfl) ⟨1125878, by rfl⟩ : syracuseStep 1501171 = 2251757) B2251757
theorem B1501187 : Blo 1500070 1501187 := bstep (se 1 (by rfl) ⟨1125890, by rfl⟩ : syracuseStep 1501187 = 2251781) B2251781
theorem B1501203 : Blo 1500070 1501203 := bstep (se 1 (by rfl) ⟨1125902, by rfl⟩ : syracuseStep 1501203 = 2251805) B2251805
theorem B1689619 : Blo 1500070 1689619 := bstep (se 1 (by rfl) ⟨1267214, by rfl⟩ : syracuseStep 1689619 = 2534429) B2534429
theorem B1501219 : Blo 1500070 1501219 := bstep (se 1 (by rfl) ⟨1125914, by rfl⟩ : syracuseStep 1501219 = 2251829) B2251829
theorem B9619505 : Blo 1500070 9619505 := bstep (se 2 (by rfl) ⟨3607314, by rfl⟩ : syracuseStep 9619505 = 7214629) B7214629
theorem B1501235 : Blo 1500070 1501235 := bstep (se 1 (by rfl) ⟨1125926, by rfl⟩ : syracuseStep 1501235 = 2251853) B2251853
theorem B1501251 : Blo 1500070 1501251 := bstep (se 1 (by rfl) ⟨1125938, by rfl⟩ : syracuseStep 1501251 = 2251877) B2251877
theorem B2533457 : Blo 1500070 2533457 := bstep (se 2 (by rfl) ⟨950046, by rfl⟩ : syracuseStep 2533457 = 1900093) B1900093
theorem B1501267 : Blo 1500070 1501267 := bstep (se 1 (by rfl) ⟨1125950, by rfl⟩ : syracuseStep 1501267 = 2251901) B2251901
theorem B1501283 : Blo 1500070 1501283 := bstep (se 1 (by rfl) ⟨1125962, by rfl⟩ : syracuseStep 1501283 = 2251925) B2251925
theorem B6408305 : Blo 1500070 6408305 := bstep (se 2 (by rfl) ⟨2403114, by rfl⟩ : syracuseStep 6408305 = 4806229) B4806229
theorem B1501299 : Blo 1500070 1501299 := bstep (se 1 (by rfl) ⟨1125974, by rfl⟩ : syracuseStep 1501299 = 2251949) B2251949
theorem B1501315 : Blo 1500070 1501315 := bstep (se 1 (by rfl) ⟨1125986, by rfl⟩ : syracuseStep 1501315 = 2251973) B2251973
theorem B1501331 : Blo 1500070 1501331 := bstep (se 1 (by rfl) ⟨1125998, by rfl⟩ : syracuseStep 1501331 = 2251997) B2251997
theorem B6408355 : Blo 1500070 6408355 := bstep (se 1 (by rfl) ⟨4806266, by rfl⟩ : syracuseStep 6408355 = 9612533) B9612533
theorem B1501347 : Blo 1500070 1501347 := bstep (se 1 (by rfl) ⟨1126010, by rfl⟩ : syracuseStep 1501347 = 2252021) B2252021
theorem B1689763 : Blo 1500070 1689763 := bstep (se 1 (by rfl) ⟨1267322, by rfl⟩ : syracuseStep 1689763 = 2534645) B2534645
theorem B1501363 : Blo 1500070 1501363 := bstep (se 1 (by rfl) ⟨1126022, by rfl⟩ : syracuseStep 1501363 = 2252045) B2252045
theorem B1501379 : Blo 1500070 1501379 := bstep (se 1 (by rfl) ⟨1126034, by rfl⟩ : syracuseStep 1501379 = 2252069) B2252069
theorem B2533585 : Blo 1500070 2533585 := bstep (se 2 (by rfl) ⟨950094, by rfl⟩ : syracuseStep 2533585 = 1900189) B1900189
theorem B1501395 : Blo 1500070 1501395 := bstep (se 1 (by rfl) ⟨1126046, by rfl⟩ : syracuseStep 1501395 = 2252093) B2252093
theorem B1501411 : Blo 1500070 1501411 := bstep (se 1 (by rfl) ⟨1126058, by rfl⟩ : syracuseStep 1501411 = 2252117) B2252117
theorem B3377393 : Blo 1500070 3377393 := bstep (se 2 (by rfl) ⟨1266522, by rfl⟩ : syracuseStep 3377393 = 2533045) B2533045
theorem B2533619 : Blo 1500070 2533619 := bstep (se 1 (by rfl) ⟨1900214, by rfl⟩ : syracuseStep 2533619 = 3800429) B3800429
theorem B1501427 : Blo 1500070 1501427 := bstep (se 1 (by rfl) ⟨1126070, by rfl⟩ : syracuseStep 1501427 = 2252141) B2252141
theorem B3377411 : Blo 1500070 3377411 := bstep (se 1 (by rfl) ⟨2533058, by rfl⟩ : syracuseStep 3377411 = 5066117) B5066117
theorem B1501443 : Blo 1500070 1501443 := bstep (se 1 (by rfl) ⟨1126082, by rfl⟩ : syracuseStep 1501443 = 2252165) B2252165
theorem B1501459 : Blo 1500070 1501459 := bstep (se 1 (by rfl) ⟨1126094, by rfl⟩ : syracuseStep 1501459 = 2252189) B2252189
theorem B1501475 : Blo 1500070 1501475 := bstep (se 1 (by rfl) ⟨1126106, by rfl⟩ : syracuseStep 1501475 = 2252213) B2252213
theorem B1501491 : Blo 1500070 1501491 := bstep (se 1 (by rfl) ⟨1126118, by rfl⟩ : syracuseStep 1501491 = 2252237) B2252237
theorem B1501507 : Blo 1500070 1501507 := bstep (se 1 (by rfl) ⟨1126130, by rfl⟩ : syracuseStep 1501507 = 2252261) B2252261
theorem B5065037 : Blo 1500070 5065037 := bstep (se 3 (by rfl) ⟨949694, by rfl⟩ : syracuseStep 5065037 = 1899389) B1899389
theorem B1501523 : Blo 1500070 1501523 := bstep (se 1 (by rfl) ⟨1126142, by rfl⟩ : syracuseStep 1501523 = 2252285) B2252285
theorem B1501539 : Blo 1500070 1501539 := bstep (se 1 (by rfl) ⟨1126154, by rfl⟩ : syracuseStep 1501539 = 2252309) B2252309
theorem B14428529 : Blo 1500070 14428529 := bstep (se 2 (by rfl) ⟨5410698, by rfl⟩ : syracuseStep 14428529 = 10821397) B10821397
theorem B2533747 : Blo 1500070 2533747 := bstep (se 1 (by rfl) ⟨1900310, by rfl⟩ : syracuseStep 2533747 = 3800621) B3800621
theorem B1501555 : Blo 1500070 1501555 := bstep (se 1 (by rfl) ⟨1126166, by rfl⟩ : syracuseStep 1501555 = 2252333) B2252333
theorem B5065091 : Blo 1500070 5065091 := bstep (se 1 (by rfl) ⟨3798818, by rfl⟩ : syracuseStep 5065091 = 7597637) B7597637
theorem B1501571 : Blo 1500070 1501571 := bstep (se 1 (by rfl) ⟨1126178, by rfl⟩ : syracuseStep 1501571 = 2252357) B2252357
theorem B1501587 : Blo 1500070 1501587 := bstep (se 1 (by rfl) ⟨1126190, by rfl⟩ : syracuseStep 1501587 = 2252381) B2252381
theorem B1501603 : Blo 1500070 1501603 := bstep (se 1 (by rfl) ⟨1126202, by rfl⟩ : syracuseStep 1501603 = 2252405) B2252405
theorem B1501619 : Blo 1500070 1501619 := bstep (se 1 (by rfl) ⟨1126214, by rfl⟩ : syracuseStep 1501619 = 2252429) B2252429
theorem B1501635 : Blo 1500070 1501635 := bstep (se 1 (by rfl) ⟨1126226, by rfl⟩ : syracuseStep 1501635 = 2252453) B2252453
theorem B4811213 : Blo 1500070 4811213 := bstep (se 3 (by rfl) ⟨902102, by rfl⟩ : syracuseStep 4811213 = 1804205) B1804205
theorem B1501651 : Blo 1500070 1501651 := bstep (se 1 (by rfl) ⟨1126238, by rfl⟩ : syracuseStep 1501651 = 2252477) B2252477
theorem B1501667 : Blo 1500070 1501667 := bstep (se 1 (by rfl) ⟨1126250, by rfl⟩ : syracuseStep 1501667 = 2252501) B2252501
theorem B1501683 : Blo 1500070 1501683 := bstep (se 1 (by rfl) ⟨1126262, by rfl⟩ : syracuseStep 1501683 = 2252525) B2252525
theorem B2533889 : Blo 1500070 2533889 := bstep (se 2 (by rfl) ⟨950208, by rfl⟩ : syracuseStep 2533889 = 1900417) B1900417
theorem B1501699 : Blo 1500070 1501699 := bstep (se 1 (by rfl) ⟨1126274, by rfl⟩ : syracuseStep 1501699 = 2252549) B2252549
theorem B3377681 : Blo 1500070 3377681 := bstep (se 2 (by rfl) ⟨1266630, by rfl⟩ : syracuseStep 3377681 = 2533261) B2533261
theorem B1501715 : Blo 1500070 1501715 := bstep (se 1 (by rfl) ⟨1126286, by rfl⟩ : syracuseStep 1501715 = 2252573) B2252573
theorem B3377699 : Blo 1500070 3377699 := bstep (se 1 (by rfl) ⟨2533274, by rfl⟩ : syracuseStep 3377699 = 5066549) B5066549
theorem B1501731 : Blo 1500070 1501731 := bstep (se 1 (by rfl) ⟨1126298, by rfl⟩ : syracuseStep 1501731 = 2252597) B2252597
theorem B1501747 : Blo 1500070 1501747 := bstep (se 1 (by rfl) ⟨1126310, by rfl⟩ : syracuseStep 1501747 = 2252621) B2252621
theorem B1501763 : Blo 1500070 1501763 := bstep (se 1 (by rfl) ⟨1126322, by rfl⟩ : syracuseStep 1501763 = 2252645) B2252645
theorem B9620045 : Blo 1500070 9620045 := bstep (se 3 (by rfl) ⟨1803758, by rfl⟩ : syracuseStep 9620045 = 3607517) B3607517
theorem B1501779 : Blo 1500070 1501779 := bstep (se 1 (by rfl) ⟨1126334, by rfl⟩ : syracuseStep 1501779 = 2252669) B2252669
theorem B1501795 : Blo 1500070 1501795 := bstep (se 1 (by rfl) ⟨1126346, by rfl⟩ : syracuseStep 1501795 = 2252693) B2252693
theorem B1501811 : Blo 1500070 1501811 := bstep (se 1 (by rfl) ⟨1126358, by rfl⟩ : syracuseStep 1501811 = 2252717) B2252717
theorem B2534017 : Blo 1500070 2534017 := bstep (se 2 (by rfl) ⟨950256, by rfl⟩ : syracuseStep 2534017 = 1900513) B1900513
theorem B1501827 : Blo 1500070 1501827 := bstep (se 1 (by rfl) ⟨1126370, by rfl⟩ : syracuseStep 1501827 = 2252741) B2252741
theorem B8546957 : Blo 1500070 8546957 := bstep (se 3 (by rfl) ⟨1602554, by rfl⟩ : syracuseStep 8546957 = 3205109) B3205109
theorem B5065361 : Blo 1500070 5065361 := bstep (se 2 (by rfl) ⟨1899510, by rfl⟩ : syracuseStep 5065361 = 3799021) B3799021
theorem B1501843 : Blo 1500070 1501843 := bstep (se 1 (by rfl) ⟨1126382, by rfl⟩ : syracuseStep 1501843 = 2252765) B2252765
theorem B2534051 : Blo 1500070 2534051 := bstep (se 1 (by rfl) ⟨1900538, by rfl⟩ : syracuseStep 2534051 = 3801077) B3801077
theorem B1501859 : Blo 1500070 1501859 := bstep (se 1 (by rfl) ⟨1126394, by rfl⟩ : syracuseStep 1501859 = 2252789) B2252789
theorem B1501875 : Blo 1500070 1501875 := bstep (se 1 (by rfl) ⟨1126406, by rfl⟩ : syracuseStep 1501875 = 2252813) B2252813
theorem B1501891 : Blo 1500070 1501891 := bstep (se 1 (by rfl) ⟨1126418, by rfl⟩ : syracuseStep 1501891 = 2252837) B2252837
theorem B1501907 : Blo 1500070 1501907 := bstep (se 1 (by rfl) ⟨1126430, by rfl⟩ : syracuseStep 1501907 = 2252861) B2252861
theorem B1501923 : Blo 1500070 1501923 := bstep (se 1 (by rfl) ⟨1126442, by rfl⟩ : syracuseStep 1501923 = 2252885) B2252885
theorem B1501939 : Blo 1500070 1501939 := bstep (se 1 (by rfl) ⟨1126454, by rfl⟩ : syracuseStep 1501939 = 2252909) B2252909
theorem B1501955 : Blo 1500070 1501955 := bstep (se 1 (by rfl) ⟨1126466, by rfl⟩ : syracuseStep 1501955 = 2252933) B2252933
theorem B1501971 : Blo 1500070 1501971 := bstep (se 1 (by rfl) ⟨1126478, by rfl⟩ : syracuseStep 1501971 = 2252957) B2252957
theorem B2534179 : Blo 1500070 2534179 := bstep (se 1 (by rfl) ⟨1900634, by rfl⟩ : syracuseStep 2534179 = 3801269) B3801269
theorem B1501987 : Blo 1500070 1501987 := bstep (se 1 (by rfl) ⟨1126490, by rfl⟩ : syracuseStep 1501987 = 2252981) B2252981
theorem B3205937 : Blo 1500070 3205937 := bstep (se 2 (by rfl) ⟨1202226, by rfl⟩ : syracuseStep 3205937 = 2404453) B2404453
theorem B3377969 : Blo 1500070 3377969 := bstep (se 2 (by rfl) ⟨1266738, by rfl⟩ : syracuseStep 3377969 = 2533477) B2533477
theorem B1502003 : Blo 1500070 1502003 := bstep (se 1 (by rfl) ⟨1126502, by rfl⟩ : syracuseStep 1502003 = 2253005) B2253005
theorem B3205955 : Blo 1500070 3205955 := bstep (se 1 (by rfl) ⟨2404466, by rfl⟩ : syracuseStep 3205955 = 4808933) B4808933
theorem B3377987 : Blo 1500070 3377987 := bstep (se 1 (by rfl) ⟨2533490, by rfl⟩ : syracuseStep 3377987 = 5066981) B5066981
theorem B1502019 : Blo 1500070 1502019 := bstep (se 1 (by rfl) ⟨1126514, by rfl⟩ : syracuseStep 1502019 = 2253029) B2253029
theorem B1502035 : Blo 1500070 1502035 := bstep (se 1 (by rfl) ⟨1126526, by rfl⟩ : syracuseStep 1502035 = 2253053) B2253053
theorem B1502051 : Blo 1500070 1502051 := bstep (se 1 (by rfl) ⟨1126538, by rfl⟩ : syracuseStep 1502051 = 2253077) B2253077
theorem B1502067 : Blo 1500070 1502067 := bstep (se 1 (by rfl) ⟨1126550, by rfl⟩ : syracuseStep 1502067 = 2253101) B2253101
theorem B2403217 : Blo 1500070 2403217 := bstep (se 2 (by rfl) ⟨901206, by rfl⟩ : syracuseStep 2403217 = 1802413) B1802413
theorem B2534321 : Blo 1500070 2534321 := bstep (se 2 (by rfl) ⟨950370, by rfl⟩ : syracuseStep 2534321 = 1900741) B1900741
theorem B11398157 : Blo 1500070 11398157 := bstep (se 3 (by rfl) ⟨2137154, by rfl⟩ : syracuseStep 11398157 = 4274309) B4274309
theorem B2534449 : Blo 1500070 2534449 := bstep (se 2 (by rfl) ⟨950418, by rfl⟩ : syracuseStep 2534449 = 1900837) B1900837
theorem B2706481 : Blo 1500070 2706481 := bstep (se 2 (by rfl) ⟨1014930, by rfl⟩ : syracuseStep 2706481 = 2029861) B2029861
theorem B3378257 : Blo 1500070 3378257 := bstep (se 2 (by rfl) ⟨1266846, by rfl⟩ : syracuseStep 3378257 = 2533693) B2533693
theorem B2534483 : Blo 1500070 2534483 := bstep (se 1 (by rfl) ⟨1900862, by rfl⟩ : syracuseStep 2534483 = 3801725) B3801725
theorem B3378275 : Blo 1500070 3378275 := bstep (se 1 (by rfl) ⟨2533706, by rfl⟩ : syracuseStep 3378275 = 5067413) B5067413
theorem B5065901 : Blo 1500070 5065901 := bstep (se 3 (by rfl) ⟨949856, by rfl⟩ : syracuseStep 5065901 = 1899713) B1899713
theorem B13003973 : Blo 1500070 13003973 := bstep (se 4 (by rfl) ⟨1219122, by rfl⟩ : syracuseStep 13003973 = 2438245) B2438245
theorem B2534611 : Blo 1500070 2534611 := bstep (se 1 (by rfl) ⟨1900958, by rfl⟩ : syracuseStep 2534611 = 3801917) B3801917
theorem B5065955 : Blo 1500070 5065955 := bstep (se 1 (by rfl) ⟨3799466, by rfl⟩ : syracuseStep 5065955 = 7598933) B7598933
theorem B3378545 : Blo 1500070 3378545 := bstep (se 2 (by rfl) ⟨1266954, by rfl⟩ : syracuseStep 3378545 = 2533909) B2533909
theorem B3378563 : Blo 1500070 3378563 := bstep (se 1 (by rfl) ⟨2533922, by rfl⟩ : syracuseStep 3378563 = 5067845) B5067845
theorem B9612685 : Blo 1500070 9612685 := bstep (se 3 (by rfl) ⟨1802378, by rfl⟩ : syracuseStep 9612685 = 3604757) B3604757
theorem B7597475 : Blo 1500070 7597475 := bstep (se 1 (by rfl) ⟨5698106, by rfl⟩ : syracuseStep 7597475 = 11396213) B11396213
theorem B2403761 : Blo 1500070 2403761 := bstep (se 2 (by rfl) ⟨901410, by rfl⟩ : syracuseStep 2403761 = 1802821) B1802821
theorem B5066225 : Blo 1500070 5066225 := bstep (se 2 (by rfl) ⟨1899834, by rfl⟩ : syracuseStep 5066225 = 3799669) B3799669
theorem B8547889 : Blo 1500070 8547889 := bstep (se 2 (by rfl) ⟨3205458, by rfl⟩ : syracuseStep 8547889 = 6410917) B6410917
theorem B3378833 : Blo 1500070 3378833 := bstep (se 2 (by rfl) ⟨1267062, by rfl⟩ : syracuseStep 3378833 = 2534125) B2534125
theorem B3378851 : Blo 1500070 3378851 := bstep (se 1 (by rfl) ⟨2534138, by rfl⟩ : syracuseStep 3378851 = 5068277) B5068277
theorem B6082381 : Blo 1500070 6082381 := bstep (se 3 (by rfl) ⟨1140446, by rfl⟩ : syracuseStep 6082381 = 2280893) B2280893
theorem B2281331 : Blo 1500070 2281331 := bstep (se 1 (by rfl) ⟨1710998, by rfl⟩ : syracuseStep 2281331 = 3421997) B3421997
theorem B3379121 : Blo 1500070 3379121 := bstep (se 2 (by rfl) ⟨1267170, by rfl⟩ : syracuseStep 3379121 = 2534341) B2534341
theorem B3379139 : Blo 1500070 3379139 := bstep (se 1 (by rfl) ⟨2534354, by rfl⟩ : syracuseStep 3379139 = 5068709) B5068709
theorem B4272077 : Blo 1500070 4272077 := bstep (se 3 (by rfl) ⟨801014, by rfl⟩ : syracuseStep 4272077 = 1602029) B1602029
theorem B5697485 : Blo 1500070 5697485 := bstep (se 3 (by rfl) ⟨1068278, by rfl⟩ : syracuseStep 5697485 = 2136557) B2136557
theorem B2281441 : Blo 1500070 2281441 := bstep (se 2 (by rfl) ⟨855540, by rfl⟩ : syracuseStep 2281441 = 1711081) B1711081
theorem B5066765 : Blo 1500070 5066765 := bstep (se 3 (by rfl) ⟨950018, by rfl⟩ : syracuseStep 5066765 = 1900037) B1900037
theorem B3207185 : Blo 1500070 3207185 := bstep (se 2 (by rfl) ⟨1202694, by rfl⟩ : syracuseStep 3207185 = 2405389) B2405389
theorem B5066819 : Blo 1500070 5066819 := bstep (se 1 (by rfl) ⟨3800114, by rfl⟩ : syracuseStep 5066819 = 7600229) B7600229
theorem B4272259 : Blo 1500070 4272259 := bstep (se 1 (by rfl) ⟨3204194, by rfl⟩ : syracuseStep 4272259 = 6408389) B6408389
theorem B7598285 : Blo 1500070 7598285 := bstep (se 3 (by rfl) ⟨1424678, by rfl⟩ : syracuseStep 7598285 = 2849357) B2849357
theorem B3379409 : Blo 1500070 3379409 := bstep (se 2 (by rfl) ⟨1267278, by rfl⟩ : syracuseStep 3379409 = 2534557) B2534557
theorem B3797219 : Blo 1500070 3797219 := bstep (se 1 (by rfl) ⟨2847914, by rfl⟩ : syracuseStep 3797219 = 5695829) B5695829
theorem B3379427 : Blo 1500070 3379427 := bstep (se 1 (by rfl) ⟨2534570, by rfl⟩ : syracuseStep 3379427 = 5069141) B5069141
theorem B4059409 : Blo 1500070 4059409 := bstep (se 2 (by rfl) ⟨1522278, by rfl⟩ : syracuseStep 4059409 = 3044557) B3044557
theorem B4272419 : Blo 1500070 4272419 := bstep (se 1 (by rfl) ⟨3204314, by rfl⟩ : syracuseStep 4272419 = 6408629) B6408629
theorem B5067089 : Blo 1500070 5067089 := bstep (se 2 (by rfl) ⟨1900158, by rfl⟩ : syracuseStep 5067089 = 3800317) B3800317
theorem B2404723 : Blo 1500070 2404723 := bstep (se 1 (by rfl) ⟨1803542, by rfl⟩ : syracuseStep 2404723 = 3607085) B3607085
theorem B2568577 : Blo 1500070 2568577 := bstep (se 2 (by rfl) ⟨963216, by rfl⟩ : syracuseStep 2568577 = 1926433) B1926433
theorem B6410765 : Blo 1500070 6410765 := bstep (se 3 (by rfl) ⟨1202018, by rfl⟩ : syracuseStep 6410765 = 2404037) B2404037
theorem B2404979 : Blo 1500070 2404979 := bstep (se 1 (by rfl) ⟨1803734, by rfl⟩ : syracuseStep 2404979 = 3607469) B3607469
theorem B12169925 : Blo 1500070 12169925 := bstep (se 4 (by rfl) ⟨1140930, by rfl⟩ : syracuseStep 12169925 = 2281861) B2281861
theorem B5698289 : Blo 1500070 5698289 := bstep (se 2 (by rfl) ⟨2136858, by rfl⟩ : syracuseStep 5698289 = 4273717) B4273717
theorem B5133091 : Blo 1500070 5133091 := bstep (se 1 (by rfl) ⟨3849818, by rfl⟩ : syracuseStep 5133091 = 7699637) B7699637
theorem B5067629 : Blo 1500070 5067629 := bstep (se 3 (by rfl) ⟨950180, by rfl⟩ : syracuseStep 5067629 = 1900361) B1900361
theorem B7312241 : Blo 1500070 7312241 := bstep (se 2 (by rfl) ⟨2742090, by rfl⟩ : syracuseStep 7312241 = 5484181) B5484181
theorem B5067683 : Blo 1500070 5067683 := bstep (se 1 (by rfl) ⟨3800762, by rfl⟩ : syracuseStep 5067683 = 7601525) B7601525
theorem B1602499 : Blo 1500070 1602499 := bstep (se 1 (by rfl) ⟨1201874, by rfl⟩ : syracuseStep 1602499 = 2403749) B2403749
theorem B2085841 : Blo 1500070 2085841 := bstep (se 2 (by rfl) ⟨782190, by rfl⟩ : syracuseStep 2085841 = 1564381) B1564381
theorem B8549347 : Blo 1500070 8549347 := bstep (se 1 (by rfl) ⟨6412010, by rfl⟩ : syracuseStep 8549347 = 12824021) B12824021
theorem B2847793 : Blo 1500070 2847793 := bstep (se 2 (by rfl) ⟨1067922, by rfl⟩ : syracuseStep 2847793 = 2135845) B2135845
theorem B7214129 : Blo 1500070 7214129 := bstep (se 2 (by rfl) ⟨2705298, by rfl⟩ : syracuseStep 7214129 = 5410597) B5410597
theorem B3798161 : Blo 1500070 3798161 := bstep (se 2 (by rfl) ⟨1424310, by rfl⟩ : syracuseStep 3798161 = 2848621) B2848621
theorem B5067953 : Blo 1500070 5067953 := bstep (se 2 (by rfl) ⟨1900482, by rfl⟩ : syracuseStep 5067953 = 3800965) B3800965
theorem B3798211 : Blo 1500070 3798211 := bstep (se 1 (by rfl) ⟨2848658, by rfl⟩ : syracuseStep 3798211 = 5697317) B5697317
theorem B2847953 : Blo 1500070 2847953 := bstep (se 2 (by rfl) ⟨1067982, by rfl⟩ : syracuseStep 2847953 = 2135965) B2135965
theorem B7214321 : Blo 1500070 7214321 := bstep (se 2 (by rfl) ⟨2705370, by rfl⟩ : syracuseStep 7214321 = 5410741) B5410741
theorem B22230325 : Blo 1500070 22230325 := bstep (se 5 (by rfl) ⟨1042046, by rfl⟩ : syracuseStep 22230325 = 2084093) B2084093
theorem B2405683 : Blo 1500070 2405683 := bstep (se 1 (by rfl) ⟨1804262, by rfl⟩ : syracuseStep 2405683 = 3608525) B3608525
theorem B11392325 : Blo 1500070 11392325 := bstep (se 4 (by rfl) ⟨1068030, by rfl⟩ : syracuseStep 11392325 = 2136061) B2136061
theorem B3798353 : Blo 1500070 3798353 := bstep (se 2 (by rfl) ⟨1424382, by rfl⟩ : syracuseStep 3798353 = 2848765) B2848765
theorem B4273489 : Blo 1500070 4273489 := bstep (se 2 (by rfl) ⟨1602558, by rfl⟩ : syracuseStep 4273489 = 3205117) B3205117
theorem B2028883 : Blo 1500070 2028883 := bstep (se 1 (by rfl) ⟨1521662, by rfl⟩ : syracuseStep 2028883 = 3043325) B3043325
theorem B7214435 : Blo 1500070 7214435 := bstep (se 1 (by rfl) ⟨5410826, by rfl⟩ : syracuseStep 7214435 = 10821653) B10821653
theorem B2250113 : Blo 1500070 2250113 := bstep (se 2 (by rfl) ⟨843792, by rfl⟩ : syracuseStep 2250113 = 1687585) B1687585
theorem B5133709 : Blo 1500070 5133709 := bstep (se 3 (by rfl) ⟨962570, by rfl⟩ : syracuseStep 5133709 = 1925141) B1925141
theorem B5698957 : Blo 1500070 5698957 := bstep (se 3 (by rfl) ⟨1068554, by rfl⟩ : syracuseStep 5698957 = 2137109) B2137109
theorem B2250131 : Blo 1500070 2250131 := bstep (se 1 (by rfl) ⟨1687598, by rfl⟩ : syracuseStep 2250131 = 3375197) B3375197
theorem B2250161 : Blo 1500070 2250161 := bstep (se 2 (by rfl) ⟨843810, by rfl⟩ : syracuseStep 2250161 = 1687621) B1687621
theorem B2250179 : Blo 1500070 2250179 := bstep (se 1 (by rfl) ⟨1687634, by rfl⟩ : syracuseStep 2250179 = 3375269) B3375269
theorem B2602451 : Blo 1500070 2602451 := bstep (se 1 (by rfl) ⟨1951838, by rfl⟩ : syracuseStep 2602451 = 3903677) B3903677
theorem B2250209 : Blo 1500070 2250209 := bstep (se 2 (by rfl) ⟨843828, by rfl⟩ : syracuseStep 2250209 = 1687657) B1687657
theorem B6084067 : Blo 1500070 6084067 := bstep (se 1 (by rfl) ⟨4563050, by rfl⟩ : syracuseStep 6084067 = 9126101) B9126101
theorem B8549873 : Blo 1500070 8549873 := bstep (se 2 (by rfl) ⟨3206202, by rfl⟩ : syracuseStep 8549873 = 6412405) B6412405
theorem B2250227 : Blo 1500070 2250227 := bstep (se 1 (by rfl) ⟨1687670, by rfl⟩ : syracuseStep 2250227 = 3375341) B3375341
theorem B2250257 : Blo 1500070 2250257 := bstep (se 2 (by rfl) ⟨843846, by rfl⟩ : syracuseStep 2250257 = 1687693) B1687693
theorem B3044881 : Blo 1500070 3044881 := bstep (se 2 (by rfl) ⟨1141830, by rfl⟩ : syracuseStep 3044881 = 2283661) B2283661
theorem B2250275 : Blo 1500070 2250275 := bstep (se 1 (by rfl) ⟨1687706, by rfl⟩ : syracuseStep 2250275 = 3375413) B3375413
theorem B5133869 : Blo 1500070 5133869 := bstep (se 3 (by rfl) ⟨962600, by rfl⟩ : syracuseStep 5133869 = 1925201) B1925201
theorem B2250305 : Blo 1500070 2250305 := bstep (se 2 (by rfl) ⟨843864, by rfl⟩ : syracuseStep 2250305 = 1687729) B1687729
theorem B2405953 : Blo 1500070 2405953 := bstep (se 2 (by rfl) ⟨902232, by rfl⟩ : syracuseStep 2405953 = 1804465) B1804465
theorem B3044945 : Blo 1500070 3044945 := bstep (se 2 (by rfl) ⟨1141854, by rfl⟩ : syracuseStep 3044945 = 2283709) B2283709
theorem B2250323 : Blo 1500070 2250323 := bstep (se 1 (by rfl) ⟨1687742, by rfl⟩ : syracuseStep 2250323 = 3375485) B3375485
theorem B2848355 : Blo 1500070 2848355 := bstep (se 1 (by rfl) ⟨2136266, by rfl⟩ : syracuseStep 2848355 = 4272533) B4272533
theorem B2250353 : Blo 1500070 2250353 := bstep (se 2 (by rfl) ⟨843882, by rfl⟩ : syracuseStep 2250353 = 1687765) B1687765
theorem B2029169 : Blo 1500070 2029169 := bstep (se 2 (by rfl) ⟨760938, by rfl⟩ : syracuseStep 2029169 = 1521877) B1521877
theorem B2406017 : Blo 1500070 2406017 := bstep (se 2 (by rfl) ⟨902256, by rfl⟩ : syracuseStep 2406017 = 1804513) B1804513
theorem B2250371 : Blo 1500070 2250371 := bstep (se 1 (by rfl) ⟨1687778, by rfl⟩ : syracuseStep 2250371 = 3375557) B3375557
theorem B2250401 : Blo 1500070 2250401 := bstep (se 2 (by rfl) ⟨843900, by rfl⟩ : syracuseStep 2250401 = 1687801) B1687801
theorem B2250419 : Blo 1500070 2250419 := bstep (se 1 (by rfl) ⟨1687814, by rfl⟩ : syracuseStep 2250419 = 3375629) B3375629
theorem B1734323 : Blo 1500070 1734323 := bstep (se 1 (by rfl) ⟨1300742, by rfl⟩ : syracuseStep 1734323 = 2601485) B2601485
theorem B5068493 : Blo 1500070 5068493 := bstep (se 3 (by rfl) ⟨950342, by rfl⟩ : syracuseStep 5068493 = 1900685) B1900685
theorem B9623245 : Blo 1500070 9623245 := bstep (se 3 (by rfl) ⟨1804358, by rfl⟩ : syracuseStep 9623245 = 3608717) B3608717
theorem B2250449 : Blo 1500070 2250449 := bstep (se 2 (by rfl) ⟨843918, by rfl⟩ : syracuseStep 2250449 = 1687837) B1687837
theorem B2250467 : Blo 1500070 2250467 := bstep (se 1 (by rfl) ⟨1687850, by rfl⟩ : syracuseStep 2250467 = 3375701) B3375701
theorem B2250497 : Blo 1500070 2250497 := bstep (se 2 (by rfl) ⟨843936, by rfl⟩ : syracuseStep 2250497 = 1687873) B1687873
theorem B5068547 : Blo 1500070 5068547 := bstep (se 1 (by rfl) ⟨3801410, by rfl⟩ : syracuseStep 5068547 = 7602821) B7602821
theorem B6846221 : Blo 1500070 6846221 := bstep (se 3 (by rfl) ⟨1283666, by rfl⟩ : syracuseStep 6846221 = 2567333) B2567333
theorem B2250515 : Blo 1500070 2250515 := bstep (se 1 (by rfl) ⟨1687886, by rfl⟩ : syracuseStep 2250515 = 3375773) B3375773
theorem B2029331 : Blo 1500070 2029331 := bstep (se 1 (by rfl) ⟨1521998, by rfl⟩ : syracuseStep 2029331 = 3043997) B3043997
theorem B2250545 : Blo 1500070 2250545 := bstep (se 2 (by rfl) ⟨843954, by rfl⟩ : syracuseStep 2250545 = 1687909) B1687909
theorem B2250563 : Blo 1500070 2250563 := bstep (se 1 (by rfl) ⟨1687922, by rfl⟩ : syracuseStep 2250563 = 3375845) B3375845
theorem B2250593 : Blo 1500070 2250593 := bstep (se 2 (by rfl) ⟨843972, by rfl⟩ : syracuseStep 2250593 = 1687945) B1687945
theorem B11401073 : Blo 1500070 11401073 := bstep (se 2 (by rfl) ⟨4275402, by rfl⟩ : syracuseStep 11401073 = 8550805) B8550805
theorem B2250611 : Blo 1500070 2250611 := bstep (se 1 (by rfl) ⟨1687958, by rfl⟩ : syracuseStep 2250611 = 3375917) B3375917
theorem B2250641 : Blo 1500070 2250641 := bstep (se 2 (by rfl) ⟨843990, by rfl⟩ : syracuseStep 2250641 = 1687981) B1687981
theorem B2250659 : Blo 1500070 2250659 := bstep (se 1 (by rfl) ⟨1687994, by rfl⟩ : syracuseStep 2250659 = 3375989) B3375989
theorem B6256547 : Blo 1500070 6256547 := bstep (se 1 (by rfl) ⟨4692410, by rfl⟩ : syracuseStep 6256547 = 9384821) B9384821
theorem B2250689 : Blo 1500070 2250689 := bstep (se 2 (by rfl) ⟨844008, by rfl⟩ : syracuseStep 2250689 = 1688017) B1688017
theorem B2250707 : Blo 1500070 2250707 := bstep (se 1 (by rfl) ⟨1688030, by rfl⟩ : syracuseStep 2250707 = 3376061) B3376061
theorem B2250737 : Blo 1500070 2250737 := bstep (se 2 (by rfl) ⟨844026, by rfl⟩ : syracuseStep 2250737 = 1688053) B1688053
theorem B2250755 : Blo 1500070 2250755 := bstep (se 1 (by rfl) ⟨1688066, by rfl⟩ : syracuseStep 2250755 = 3376133) B3376133
theorem B5068817 : Blo 1500070 5068817 := bstep (se 2 (by rfl) ⟨1900806, by rfl⟩ : syracuseStep 5068817 = 3801613) B3801613
theorem B2250785 : Blo 1500070 2250785 := bstep (se 2 (by rfl) ⟨844044, by rfl⟩ : syracuseStep 2250785 = 1688089) B1688089
theorem B2283569 : Blo 1500070 2283569 := bstep (se 2 (by rfl) ⟨856338, by rfl⟩ : syracuseStep 2283569 = 1712677) B1712677
theorem B2250803 : Blo 1500070 2250803 := bstep (se 1 (by rfl) ⟨1688102, by rfl⟩ : syracuseStep 2250803 = 3376205) B3376205
theorem B2250833 : Blo 1500070 2250833 := bstep (se 2 (by rfl) ⟨844062, by rfl⟩ : syracuseStep 2250833 = 1688125) B1688125
theorem B1898579 : Blo 1500070 1898579 := bstep (se 1 (by rfl) ⟨1423934, by rfl⟩ : syracuseStep 1898579 = 2847869) B2847869
theorem B2250851 : Blo 1500070 2250851 := bstep (se 1 (by rfl) ⟨1688138, by rfl⟩ : syracuseStep 2250851 = 3376277) B3376277
theorem B1521779 : Blo 1500070 1521779 := bstep (se 1 (by rfl) ⟨1141334, by rfl⟩ : syracuseStep 1521779 = 2282669) B2282669
theorem B2250881 : Blo 1500070 2250881 := bstep (se 2 (by rfl) ⟨844080, by rfl⟩ : syracuseStep 2250881 = 1688161) B1688161
theorem B2250899 : Blo 1500070 2250899 := bstep (se 1 (by rfl) ⟨1688174, by rfl⟩ : syracuseStep 2250899 = 3376349) B3376349
theorem B5699747 : Blo 1500070 5699747 := bstep (se 1 (by rfl) ⟨4274810, by rfl⟩ : syracuseStep 5699747 = 8549621) B8549621
theorem B2250929 : Blo 1500070 2250929 := bstep (se 2 (by rfl) ⟨844098, by rfl⟩ : syracuseStep 2250929 = 1688197) B1688197
theorem B2250947 : Blo 1500070 2250947 := bstep (se 1 (by rfl) ⟨1688210, by rfl⟩ : syracuseStep 2250947 = 3376421) B3376421
theorem B3471569 : Blo 1500070 3471569 := bstep (se 2 (by rfl) ⟨1301838, by rfl⟩ : syracuseStep 3471569 = 2603677) B2603677
theorem B2136289 : Blo 1500070 2136289 := bstep (se 2 (by rfl) ⟨801108, by rfl⟩ : syracuseStep 2136289 = 1602217) B1602217
theorem B2250977 : Blo 1500070 2250977 := bstep (se 2 (by rfl) ⟨844116, by rfl⟩ : syracuseStep 2250977 = 1688233) B1688233
theorem B16685297 : Blo 1500070 16685297 := bstep (se 2 (by rfl) ⟨6256986, by rfl⟩ : syracuseStep 16685297 = 12513973) B12513973
theorem B2250995 : Blo 1500070 2250995 := bstep (se 1 (by rfl) ⟨1688246, by rfl⟩ : syracuseStep 2250995 = 3376493) B3376493
theorem B5413133 : Blo 1500070 5413133 := bstep (se 3 (by rfl) ⟨1014962, by rfl⟩ : syracuseStep 5413133 = 2029925) B2029925
theorem B2251025 : Blo 1500070 2251025 := bstep (se 2 (by rfl) ⟨844134, by rfl⟩ : syracuseStep 2251025 = 1688269) B1688269
theorem B2251043 : Blo 1500070 2251043 := bstep (se 1 (by rfl) ⟨1688282, by rfl⟩ : syracuseStep 2251043 = 3376565) B3376565
theorem B3799345 : Blo 1500070 3799345 := bstep (se 2 (by rfl) ⟨1424754, by rfl⟩ : syracuseStep 3799345 = 2849509) B2849509
theorem B2251073 : Blo 1500070 2251073 := bstep (se 2 (by rfl) ⟨844152, by rfl⟩ : syracuseStep 2251073 = 1688305) B1688305
theorem B4331843 : Blo 1500070 4331843 := bstep (se 1 (by rfl) ⟨3248882, by rfl⟩ : syracuseStep 4331843 = 6497765) B6497765
theorem B2136403 : Blo 1500070 2136403 := bstep (se 1 (by rfl) ⟨1602302, by rfl⟩ : syracuseStep 2136403 = 3204605) B3204605
theorem B2251091 : Blo 1500070 2251091 := bstep (se 1 (by rfl) ⟨1688318, by rfl⟩ : syracuseStep 2251091 = 3376637) B3376637
theorem B2251121 : Blo 1500070 2251121 := bstep (se 2 (by rfl) ⟨844170, by rfl⟩ : syracuseStep 2251121 = 1688341) B1688341
theorem B2251139 : Blo 1500070 2251139 := bstep (se 1 (by rfl) ⟨1688354, by rfl⟩ : syracuseStep 2251139 = 3376709) B3376709
theorem B2029969 : Blo 1500070 2029969 := bstep (se 2 (by rfl) ⟨761238, by rfl⟩ : syracuseStep 2029969 = 1522477) B1522477
theorem B2251169 : Blo 1500070 2251169 := bstep (se 2 (by rfl) ⟨844188, by rfl⟩ : syracuseStep 2251169 = 1688377) B1688377
theorem B2251187 : Blo 1500070 2251187 := bstep (se 1 (by rfl) ⟨1688390, by rfl⟩ : syracuseStep 2251187 = 3376781) B3376781
theorem B2251217 : Blo 1500070 2251217 := bstep (se 2 (by rfl) ⟨844206, by rfl⟩ : syracuseStep 2251217 = 1688413) B1688413
theorem B2251235 : Blo 1500070 2251235 := bstep (se 1 (by rfl) ⟨1688426, by rfl⟩ : syracuseStep 2251235 = 3376853) B3376853
theorem B2849251 : Blo 1500070 2849251 := bstep (se 1 (by rfl) ⟨2136938, by rfl⟩ : syracuseStep 2849251 = 4273877) B4273877
theorem B2251265 : Blo 1500070 2251265 := bstep (se 2 (by rfl) ⟨844224, by rfl⟩ : syracuseStep 2251265 = 1688449) B1688449
theorem B2251283 : Blo 1500070 2251283 := bstep (se 1 (by rfl) ⟨1688462, by rfl⟩ : syracuseStep 2251283 = 3376925) B3376925
theorem B5069357 : Blo 1500070 5069357 := bstep (se 3 (by rfl) ⟨950504, by rfl⟩ : syracuseStep 5069357 = 1901009) B1901009
theorem B2251313 : Blo 1500070 2251313 := bstep (se 2 (by rfl) ⟨844242, by rfl⟩ : syracuseStep 2251313 = 1688485) B1688485
theorem B2251331 : Blo 1500070 2251331 := bstep (se 1 (by rfl) ⟨1688498, by rfl⟩ : syracuseStep 2251331 = 3376997) B3376997
theorem B3799619 : Blo 1500070 3799619 := bstep (se 1 (by rfl) ⟨2849714, by rfl⟩ : syracuseStep 3799619 = 5699429) B5699429
theorem B4274765 : Blo 1500070 4274765 := bstep (se 3 (by rfl) ⟨801518, by rfl⟩ : syracuseStep 4274765 = 1603037) B1603037
theorem B2251361 : Blo 1500070 2251361 := bstep (se 2 (by rfl) ⟨844260, by rfl⟩ : syracuseStep 2251361 = 1688521) B1688521
theorem B5069411 : Blo 1500070 5069411 := bstep (se 1 (by rfl) ⟨3802058, by rfl⟩ : syracuseStep 5069411 = 7604117) B7604117
theorem B2251379 : Blo 1500070 2251379 := bstep (se 1 (by rfl) ⟨1688534, by rfl⟩ : syracuseStep 2251379 = 3377069) B3377069
theorem B2849411 : Blo 1500070 2849411 := bstep (se 1 (by rfl) ⟨2137058, by rfl⟩ : syracuseStep 2849411 = 4274117) B4274117
theorem B2251409 : Blo 1500070 2251409 := bstep (se 2 (by rfl) ⟨844278, by rfl⟩ : syracuseStep 2251409 = 1688557) B1688557
theorem B2251427 : Blo 1500070 2251427 := bstep (se 1 (by rfl) ⟨1688570, by rfl⟩ : syracuseStep 2251427 = 3377141) B3377141
theorem B2251457 : Blo 1500070 2251457 := bstep (se 2 (by rfl) ⟨844296, by rfl⟩ : syracuseStep 2251457 = 1688593) B1688593
theorem B2251475 : Blo 1500070 2251475 := bstep (se 1 (by rfl) ⟨1688606, by rfl⟩ : syracuseStep 2251475 = 3377213) B3377213
theorem B2251505 : Blo 1500070 2251505 := bstep (se 2 (by rfl) ⟨844314, by rfl⟩ : syracuseStep 2251505 = 1688629) B1688629
theorem B2251523 : Blo 1500070 2251523 := bstep (se 1 (by rfl) ⟨1688642, by rfl⟩ : syracuseStep 2251523 = 3377285) B3377285
theorem B3799811 : Blo 1500070 3799811 := bstep (se 1 (by rfl) ⟨2849858, by rfl⟩ : syracuseStep 3799811 = 5699717) B5699717
theorem B4274947 : Blo 1500070 4274947 := bstep (se 1 (by rfl) ⟨3206210, by rfl⟩ : syracuseStep 4274947 = 6412421) B6412421
theorem B4332305 : Blo 1500070 4332305 := bstep (se 2 (by rfl) ⟨1624614, by rfl⟩ : syracuseStep 4332305 = 3249229) B3249229
theorem B1899283 : Blo 1500070 1899283 := bstep (se 1 (by rfl) ⟨1424462, by rfl⟩ : syracuseStep 1899283 = 2848925) B2848925
theorem B2251553 : Blo 1500070 2251553 := bstep (se 2 (by rfl) ⟨844332, by rfl⟩ : syracuseStep 2251553 = 1688665) B1688665
theorem B4274993 : Blo 1500070 4274993 := bstep (se 2 (by rfl) ⟨1603122, by rfl⟩ : syracuseStep 4274993 = 3206245) B3206245
theorem B5700401 : Blo 1500070 5700401 := bstep (se 2 (by rfl) ⟨2137650, by rfl⟩ : syracuseStep 5700401 = 4275301) B4275301
theorem B2251571 : Blo 1500070 2251571 := bstep (se 1 (by rfl) ⟨1688678, by rfl⟩ : syracuseStep 2251571 = 3377357) B3377357
theorem B2251601 : Blo 1500070 2251601 := bstep (se 2 (by rfl) ⟨844350, by rfl⟩ : syracuseStep 2251601 = 1688701) B1688701
theorem B2251619 : Blo 1500070 2251619 := bstep (se 1 (by rfl) ⟨1688714, by rfl⟩ : syracuseStep 2251619 = 3377429) B3377429
theorem B1899379 : Blo 1500070 1899379 := bstep (se 1 (by rfl) ⟨1424534, by rfl⟩ : syracuseStep 1899379 = 2849069) B2849069
theorem B2251649 : Blo 1500070 2251649 := bstep (se 2 (by rfl) ⟨844368, by rfl⟩ : syracuseStep 2251649 = 1688737) B1688737
theorem B2251667 : Blo 1500070 2251667 := bstep (se 1 (by rfl) ⟨1688750, by rfl⟩ : syracuseStep 2251667 = 3377501) B3377501
theorem B8551331 : Blo 1500070 8551331 := bstep (se 1 (by rfl) ⟨6413498, by rfl⟩ : syracuseStep 8551331 = 12826997) B12826997
theorem B9747377 : Blo 1500070 9747377 := bstep (se 2 (by rfl) ⟨3655266, by rfl⟩ : syracuseStep 9747377 = 7310533) B7310533
theorem B2251697 : Blo 1500070 2251697 := bstep (se 2 (by rfl) ⟨844386, by rfl⟩ : syracuseStep 2251697 = 1688773) B1688773
theorem B17103797 : Blo 1500070 17103797 := bstep (se 5 (by rfl) ⟨801740, by rfl⟩ : syracuseStep 17103797 = 1603481) B1603481
theorem B2251715 : Blo 1500070 2251715 := bstep (se 1 (by rfl) ⟨1688786, by rfl⟩ : syracuseStep 2251715 = 3377573) B3377573
theorem B2251745 : Blo 1500070 2251745 := bstep (se 2 (by rfl) ⟨844404, by rfl⟩ : syracuseStep 2251745 = 1688809) B1688809
theorem B2251763 : Blo 1500070 2251763 := bstep (se 1 (by rfl) ⟨1688822, by rfl⟩ : syracuseStep 2251763 = 3377645) B3377645
theorem B2251793 : Blo 1500070 2251793 := bstep (se 2 (by rfl) ⟨844422, by rfl⟩ : syracuseStep 2251793 = 1688845) B1688845
theorem B2251811 : Blo 1500070 2251811 := bstep (se 1 (by rfl) ⟨1688858, by rfl⟩ : syracuseStep 2251811 = 3377717) B3377717
theorem B7601201 : Blo 1500070 7601201 := bstep (se 2 (by rfl) ⟨2850450, by rfl⟩ : syracuseStep 7601201 = 5700901) B5700901
theorem B2251841 : Blo 1500070 2251841 := bstep (se 2 (by rfl) ⟨844440, by rfl⟩ : syracuseStep 2251841 = 1688881) B1688881
theorem B2251859 : Blo 1500070 2251859 := bstep (se 1 (by rfl) ⟨1688894, by rfl⟩ : syracuseStep 2251859 = 3377789) B3377789
theorem B2251889 : Blo 1500070 2251889 := bstep (se 2 (by rfl) ⟨844458, by rfl⟩ : syracuseStep 2251889 = 1688917) B1688917
theorem B2251907 : Blo 1500070 2251907 := bstep (se 1 (by rfl) ⟨1688930, by rfl⟩ : syracuseStep 2251907 = 3377861) B3377861
theorem B3423377 : Blo 1500070 3423377 := bstep (se 2 (by rfl) ⟨1283766, by rfl⟩ : syracuseStep 3423377 = 2567533) B2567533
theorem B2251937 : Blo 1500070 2251937 := bstep (se 2 (by rfl) ⟨844476, by rfl⟩ : syracuseStep 2251937 = 1688953) B1688953
theorem B2251955 : Blo 1500070 2251955 := bstep (se 1 (by rfl) ⟨1688966, by rfl⟩ : syracuseStep 2251955 = 3377933) B3377933
theorem B19225781 : Blo 1500070 19225781 := bstep (se 5 (by rfl) ⟨901208, by rfl⟩ : syracuseStep 19225781 = 1802417) B1802417
theorem B41655493 : Blo 1500070 41655493 := bstep (se 4 (by rfl) ⟨3905202, by rfl⟩ : syracuseStep 41655493 = 7810405) B7810405
theorem B2251985 : Blo 1500070 2251985 := bstep (se 2 (by rfl) ⟨844494, by rfl⟩ : syracuseStep 2251985 = 1688989) B1688989
theorem B4807907 : Blo 1500070 4807907 := bstep (se 1 (by rfl) ⟨3605930, by rfl⟩ : syracuseStep 4807907 = 7211861) B7211861
theorem B2252003 : Blo 1500070 2252003 := bstep (se 1 (by rfl) ⟨1689002, by rfl⟩ : syracuseStep 2252003 = 3378005) B3378005
theorem B2252033 : Blo 1500070 2252033 := bstep (se 2 (by rfl) ⟨844512, by rfl⟩ : syracuseStep 2252033 = 1689025) B1689025
theorem B2252051 : Blo 1500070 2252051 := bstep (se 1 (by rfl) ⟨1689038, by rfl⟩ : syracuseStep 2252051 = 3378077) B3378077
theorem B2252081 : Blo 1500070 2252081 := bstep (se 2 (by rfl) ⟨844530, by rfl⟩ : syracuseStep 2252081 = 1689061) B1689061
theorem B2252099 : Blo 1500070 2252099 := bstep (se 1 (by rfl) ⟨1689074, by rfl⟩ : syracuseStep 2252099 = 3378149) B3378149
theorem B2252129 : Blo 1500070 2252129 := bstep (se 2 (by rfl) ⟨844548, by rfl⟩ : syracuseStep 2252129 = 1689097) B1689097
theorem B1899875 : Blo 1500070 1899875 := bstep (se 1 (by rfl) ⟨1424906, by rfl⟩ : syracuseStep 1899875 = 2849813) B2849813
theorem B2252147 : Blo 1500070 2252147 := bstep (se 1 (by rfl) ⟨1689110, by rfl⟩ : syracuseStep 2252147 = 3378221) B3378221
theorem B2252177 : Blo 1500070 2252177 := bstep (se 2 (by rfl) ⟨844566, by rfl⟩ : syracuseStep 2252177 = 1689133) B1689133
theorem B2252195 : Blo 1500070 2252195 := bstep (se 1 (by rfl) ⟨1689146, by rfl⟩ : syracuseStep 2252195 = 3378293) B3378293
theorem B2252225 : Blo 1500070 2252225 := bstep (se 2 (by rfl) ⟨844584, by rfl⟩ : syracuseStep 2252225 = 1689169) B1689169
theorem B2252243 : Blo 1500070 2252243 := bstep (se 1 (by rfl) ⟨1689182, by rfl⟩ : syracuseStep 2252243 = 3378365) B3378365
theorem B2252273 : Blo 1500070 2252273 := bstep (se 2 (by rfl) ⟨844602, by rfl⟩ : syracuseStep 2252273 = 1689205) B1689205
theorem B2252291 : Blo 1500070 2252291 := bstep (se 1 (by rfl) ⟨1689218, by rfl⟩ : syracuseStep 2252291 = 3378437) B3378437
theorem B2252321 : Blo 1500070 2252321 := bstep (se 2 (by rfl) ⟨844620, by rfl⟩ : syracuseStep 2252321 = 1689241) B1689241
theorem B2252339 : Blo 1500070 2252339 := bstep (se 1 (by rfl) ⟨1689254, by rfl⟩ : syracuseStep 2252339 = 3378509) B3378509
theorem B2252369 : Blo 1500070 2252369 := bstep (se 2 (by rfl) ⟨844638, by rfl⟩ : syracuseStep 2252369 = 1689277) B1689277
theorem B2252387 : Blo 1500070 2252387 := bstep (se 1 (by rfl) ⟨1689290, by rfl⟩ : syracuseStep 2252387 = 3378581) B3378581
theorem B2252417 : Blo 1500070 2252417 := bstep (se 2 (by rfl) ⟨844656, by rfl⟩ : syracuseStep 2252417 = 1689313) B1689313
theorem B2137747 : Blo 1500070 2137747 := bstep (se 1 (by rfl) ⟨1603310, by rfl⟩ : syracuseStep 2137747 = 3206621) B3206621
theorem B2252435 : Blo 1500070 2252435 := bstep (se 1 (by rfl) ⟨1689326, by rfl⟩ : syracuseStep 2252435 = 3378653) B3378653
theorem B2850481 : Blo 1500070 2850481 := bstep (se 2 (by rfl) ⟨1068930, by rfl⟩ : syracuseStep 2850481 = 2137861) B2137861
theorem B3800753 : Blo 1500070 3800753 := bstep (se 2 (by rfl) ⟨1425282, by rfl⟩ : syracuseStep 3800753 = 2850565) B2850565
theorem B2252465 : Blo 1500070 2252465 := bstep (se 2 (by rfl) ⟨844674, by rfl⟩ : syracuseStep 2252465 = 1689349) B1689349
theorem B2252483 : Blo 1500070 2252483 := bstep (se 1 (by rfl) ⟨1689362, by rfl⟩ : syracuseStep 2252483 = 3378725) B3378725
theorem B2252513 : Blo 1500070 2252513 := bstep (se 2 (by rfl) ⟨844692, by rfl⟩ : syracuseStep 2252513 = 1689385) B1689385
theorem B3800803 : Blo 1500070 3800803 := bstep (se 1 (by rfl) ⟨2850602, by rfl⟩ : syracuseStep 3800803 = 5701205) B5701205
theorem B2252531 : Blo 1500070 2252531 := bstep (se 1 (by rfl) ⟨1689398, by rfl⟩ : syracuseStep 2252531 = 3378797) B3378797
theorem B20528909 : Blo 1500070 20528909 := bstep (se 3 (by rfl) ⟨3849170, by rfl⟩ : syracuseStep 20528909 = 7698341) B7698341
theorem B2252561 : Blo 1500070 2252561 := bstep (se 2 (by rfl) ⟨844710, by rfl⟩ : syracuseStep 2252561 = 1689421) B1689421
theorem B2252579 : Blo 1500070 2252579 := bstep (se 1 (by rfl) ⟨1689434, by rfl⟩ : syracuseStep 2252579 = 3378869) B3378869
theorem B2252609 : Blo 1500070 2252609 := bstep (se 2 (by rfl) ⟨844728, by rfl⟩ : syracuseStep 2252609 = 1689457) B1689457
theorem B2252627 : Blo 1500070 2252627 := bstep (se 1 (by rfl) ⟨1689470, by rfl⟩ : syracuseStep 2252627 = 3378941) B3378941
theorem B3800945 : Blo 1500070 3800945 := bstep (se 2 (by rfl) ⟨1425354, by rfl⟩ : syracuseStep 3800945 = 2850709) B2850709
theorem B2252657 : Blo 1500070 2252657 := bstep (se 2 (by rfl) ⟨844746, by rfl⟩ : syracuseStep 2252657 = 1689493) B1689493
theorem B2252675 : Blo 1500070 2252675 := bstep (se 1 (by rfl) ⟨1689506, by rfl⟩ : syracuseStep 2252675 = 3379013) B3379013
theorem B2252705 : Blo 1500070 2252705 := bstep (se 2 (by rfl) ⟨844764, by rfl⟩ : syracuseStep 2252705 = 1689529) B1689529
theorem B2252723 : Blo 1500070 2252723 := bstep (se 1 (by rfl) ⟨1689542, by rfl⟩ : syracuseStep 2252723 = 3379085) B3379085
theorem B2252753 : Blo 1500070 2252753 := bstep (se 2 (by rfl) ⟨844782, by rfl⟩ : syracuseStep 2252753 = 1689565) B1689565
theorem B2252771 : Blo 1500070 2252771 := bstep (se 1 (by rfl) ⟨1689578, by rfl⟩ : syracuseStep 2252771 = 3379157) B3379157
theorem B2138123 : Blo 1500070 2138123 := bstep (se 1 (by rfl) ⟨1603592, by rfl⟩ : syracuseStep 2138123 = 3207185) B3207185
theorem B2252825 : Blo 1500070 2252825 := bstep (se 2 (by rfl) ⟨844809, by rfl⟩ : syracuseStep 2252825 = 1689619) B1689619
theorem B3375179 : Blo 1500070 3375179 := bstep (se 1 (by rfl) ⟨2531384, by rfl⟩ : syracuseStep 3375179 = 5062769) B5062769
theorem B1687639 : Blo 1500070 1687639 := bstep (se 1 (by rfl) ⟨1265729, by rfl⟩ : syracuseStep 1687639 = 2531459) B2531459
theorem B3375233 : Blo 1500070 3375233 := bstep (se 2 (by rfl) ⟨1265712, by rfl⟩ : syracuseStep 3375233 = 2531425) B2531425
theorem B2252939 : Blo 1500070 2252939 := bstep (se 1 (by rfl) ⟨1689704, by rfl⟩ : syracuseStep 2252939 = 3379409) B3379409
theorem B2531479 : Blo 1500070 2531479 := bstep (se 1 (by rfl) ⟨1898609, by rfl⟩ : syracuseStep 2531479 = 3797219) B3797219
theorem B14418071 : Blo 1500070 14418071 := bstep (se 1 (by rfl) ⟨10813553, by rfl⟩ : syracuseStep 14418071 = 21627107) B21627107
theorem B3801239 : Blo 1500070 3801239 := bstep (se 1 (by rfl) ⟨2850929, by rfl⟩ : syracuseStep 3801239 = 5701859) B5701859
theorem B2850967 : Blo 1500070 2850967 := bstep (se 1 (by rfl) ⟨2138225, by rfl⟩ : syracuseStep 2850967 = 4276451) B4276451
theorem B2252951 : Blo 1500070 2252951 := bstep (se 1 (by rfl) ⟨1689713, by rfl⟩ : syracuseStep 2252951 = 3379427) B3379427
theorem B8544473 : Blo 1500070 8544473 := bstep (se 2 (by rfl) ⟨3204177, by rfl⟩ : syracuseStep 8544473 = 6408355) B6408355
theorem B2253017 : Blo 1500070 2253017 := bstep (se 2 (by rfl) ⟨844881, by rfl⟩ : syracuseStep 2253017 = 1689763) B1689763
theorem B5062877 : Blo 1500070 5062877 := bstep (se 3 (by rfl) ⟨949289, by rfl⟩ : syracuseStep 5062877 = 1898579) B1898579
theorem B1687819 : Blo 1500070 1687819 := bstep (se 1 (by rfl) ⟨1265864, by rfl⟩ : syracuseStep 1687819 = 2531729) B2531729
theorem B7602497 : Blo 1500070 7602497 := bstep (se 2 (by rfl) ⟨2850936, by rfl⟩ : syracuseStep 7602497 = 5701873) B5701873
theorem B3375449 : Blo 1500070 3375449 := bstep (se 2 (by rfl) ⟨1265793, by rfl⟩ : syracuseStep 3375449 = 2531587) B2531587
theorem B1687927 : Blo 1500070 1687927 := bstep (se 1 (by rfl) ⟨1265945, by rfl⟩ : syracuseStep 1687927 = 2531891) B2531891
theorem B3375539 : Blo 1500070 3375539 := bstep (se 1 (by rfl) ⟨2531654, by rfl⟩ : syracuseStep 3375539 = 5063309) B5063309
theorem B3375575 : Blo 1500070 3375575 := bstep (se 1 (by rfl) ⟨2531681, by rfl⟩ : syracuseStep 3375575 = 5063363) B5063363
theorem B3424769 : Blo 1500070 3424769 := bstep (se 2 (by rfl) ⟨1284288, by rfl⟩ : syracuseStep 3424769 = 2568577) B2568577
theorem B5702147 : Blo 1500070 5702147 := bstep (se 1 (by rfl) ⟨4276610, by rfl⟩ : syracuseStep 5702147 = 8553221) B8553221
theorem B4276759 : Blo 1500070 4276759 := bstep (se 1 (by rfl) ⟨3207569, by rfl⟩ : syracuseStep 4276759 = 6415139) B6415139
theorem B1688107 : Blo 1500070 1688107 := bstep (se 1 (by rfl) ⟨1266080, by rfl⟩ : syracuseStep 1688107 = 2532161) B2532161
theorem B3605057 : Blo 1500070 3605057 := bstep (se 2 (by rfl) ⟨1351896, by rfl⟩ : syracuseStep 3605057 = 2703793) B2703793
theorem B4874827 : Blo 1500070 4874827 := bstep (se 1 (by rfl) ⟨3656120, by rfl⟩ : syracuseStep 4874827 = 7312241) B7312241
theorem B3375755 : Blo 1500070 3375755 := bstep (se 1 (by rfl) ⟨2531816, by rfl⟩ : syracuseStep 3375755 = 5063633) B5063633
theorem B1688215 : Blo 1500070 1688215 := bstep (se 1 (by rfl) ⟨1266161, by rfl⟩ : syracuseStep 1688215 = 2532323) B2532323
theorem B3375809 : Blo 1500070 3375809 := bstep (se 2 (by rfl) ⟨1265928, by rfl⟩ : syracuseStep 3375809 = 2531857) B2531857
theorem B4809419 : Blo 1500070 4809419 := bstep (se 1 (by rfl) ⟨3607064, by rfl⟩ : syracuseStep 4809419 = 7214129) B7214129
theorem B2704087 : Blo 1500070 2704087 := bstep (se 1 (by rfl) ⟨2028065, by rfl⟩ : syracuseStep 2704087 = 4056131) B4056131
theorem B2532107 : Blo 1500070 2532107 := bstep (se 1 (by rfl) ⟨1899080, by rfl⟩ : syracuseStep 2532107 = 3798161) B3798161
theorem B1688395 : Blo 1500070 1688395 := bstep (se 1 (by rfl) ⟨1266296, by rfl⟩ : syracuseStep 1688395 = 2532593) B2532593
theorem B4809547 : Blo 1500070 4809547 := bstep (se 1 (by rfl) ⟨3607160, by rfl⟩ : syracuseStep 4809547 = 7214321) B7214321
theorem B7594883 : Blo 1500070 7594883 := bstep (se 1 (by rfl) ⟨5696162, by rfl⟩ : syracuseStep 7594883 = 11392325) B11392325
theorem B2532235 : Blo 1500070 2532235 := bstep (se 1 (by rfl) ⟨1899176, by rfl⟩ : syracuseStep 2532235 = 3798353) B3798353
theorem B4809623 : Blo 1500070 4809623 := bstep (se 1 (by rfl) ⟨3607217, by rfl⟩ : syracuseStep 4809623 = 7214435) B7214435
theorem B3376025 : Blo 1500070 3376025 := bstep (se 2 (by rfl) ⟨1266009, by rfl⟩ : syracuseStep 3376025 = 2532019) B2532019
theorem B1500075 : Blo 1500070 1500075 := bstep (se 1 (by rfl) ⟨1125056, by rfl⟩ : syracuseStep 1500075 = 2250113) B2250113
theorem B1500087 : Blo 1500070 1500087 := bstep (se 1 (by rfl) ⟨1125065, by rfl⟩ : syracuseStep 1500087 = 2250131) B2250131
theorem B1688503 : Blo 1500070 1688503 := bstep (se 1 (by rfl) ⟨1266377, by rfl⟩ : syracuseStep 1688503 = 2532755) B2532755
theorem B3802049 : Blo 1500070 3802049 := bstep (se 2 (by rfl) ⟨1425768, by rfl⟩ : syracuseStep 3802049 = 2851537) B2851537
theorem B1500107 : Blo 1500070 1500107 := bstep (se 1 (by rfl) ⟨1125080, by rfl⟩ : syracuseStep 1500107 = 2250161) B2250161
theorem B1500119 : Blo 1500070 1500119 := bstep (se 1 (by rfl) ⟨1125089, by rfl⟩ : syracuseStep 1500119 = 2250179) B2250179
theorem B1500139 : Blo 1500070 1500139 := bstep (se 1 (by rfl) ⟨1125104, by rfl⟩ : syracuseStep 1500139 = 2250209) B2250209
theorem B3376115 : Blo 1500070 3376115 := bstep (se 1 (by rfl) ⟨2532086, by rfl⟩ : syracuseStep 3376115 = 5064173) B5064173
theorem B1500151 : Blo 1500070 1500151 := bstep (se 1 (by rfl) ⟨1125113, by rfl⟩ : syracuseStep 1500151 = 2250227) B2250227
theorem B1500171 : Blo 1500070 1500171 := bstep (se 1 (by rfl) ⟨1125128, by rfl⟩ : syracuseStep 1500171 = 2250257) B2250257
theorem B1500183 : Blo 1500070 1500183 := bstep (se 1 (by rfl) ⟨1125137, by rfl⟩ : syracuseStep 1500183 = 2250275) B2250275
theorem B3376151 : Blo 1500070 3376151 := bstep (se 1 (by rfl) ⟨2532113, by rfl⟩ : syracuseStep 3376151 = 5064227) B5064227
theorem B2532377 : Blo 1500070 2532377 := bstep (se 2 (by rfl) ⟨949641, by rfl⟩ : syracuseStep 2532377 = 1899283) B1899283
theorem B1500203 : Blo 1500070 1500203 := bstep (se 1 (by rfl) ⟨1125152, by rfl⟩ : syracuseStep 1500203 = 2250305) B2250305
theorem B1500215 : Blo 1500070 1500215 := bstep (se 1 (by rfl) ⟨1125161, by rfl⟩ : syracuseStep 1500215 = 2250323) B2250323
theorem B1500235 : Blo 1500070 1500235 := bstep (se 1 (by rfl) ⟨1125176, by rfl⟩ : syracuseStep 1500235 = 2250353) B2250353
theorem B1500247 : Blo 1500070 1500247 := bstep (se 1 (by rfl) ⟨1125185, by rfl⟩ : syracuseStep 1500247 = 2250371) B2250371
theorem B1500267 : Blo 1500070 1500267 := bstep (se 1 (by rfl) ⟨1125200, by rfl⟩ : syracuseStep 1500267 = 2250401) B2250401
theorem B1688683 : Blo 1500070 1688683 := bstep (se 1 (by rfl) ⟨1266512, by rfl⟩ : syracuseStep 1688683 = 2533025) B2533025
theorem B1500279 : Blo 1500070 1500279 := bstep (se 1 (by rfl) ⟨1125209, by rfl⟩ : syracuseStep 1500279 = 2250419) B2250419
theorem B1500299 : Blo 1500070 1500299 := bstep (se 1 (by rfl) ⟨1125224, by rfl⟩ : syracuseStep 1500299 = 2250449) B2250449
theorem B1500311 : Blo 1500070 1500311 := bstep (se 1 (by rfl) ⟨1125233, by rfl⟩ : syracuseStep 1500311 = 2250467) B2250467
theorem B2532505 : Blo 1500070 2532505 := bstep (se 2 (by rfl) ⟨949689, by rfl⟩ : syracuseStep 2532505 = 1899379) B1899379
theorem B1500331 : Blo 1500070 1500331 := bstep (se 1 (by rfl) ⟨1125248, by rfl⟩ : syracuseStep 1500331 = 2250497) B2250497
theorem B4564147 : Blo 1500070 4564147 := bstep (se 1 (by rfl) ⟨3423110, by rfl⟩ : syracuseStep 4564147 = 6846221) B6846221
theorem B1500343 : Blo 1500070 1500343 := bstep (se 1 (by rfl) ⟨1125257, by rfl⟩ : syracuseStep 1500343 = 2250515) B2250515
theorem B3204289 : Blo 1500070 3204289 := bstep (se 2 (by rfl) ⟨1201608, by rfl⟩ : syracuseStep 3204289 = 2403217) B2403217
theorem B1500363 : Blo 1500070 1500363 := bstep (se 1 (by rfl) ⟨1125272, by rfl⟩ : syracuseStep 1500363 = 2250545) B2250545
theorem B3376331 : Blo 1500070 3376331 := bstep (se 1 (by rfl) ⟨2532248, by rfl⟩ : syracuseStep 3376331 = 5064497) B5064497
theorem B1500375 : Blo 1500070 1500375 := bstep (se 1 (by rfl) ⟨1125281, by rfl⟩ : syracuseStep 1500375 = 2250563) B2250563
theorem B1688791 : Blo 1500070 1688791 := bstep (se 1 (by rfl) ⟨1266593, by rfl⟩ : syracuseStep 1688791 = 2533187) B2533187
theorem B1500395 : Blo 1500070 1500395 := bstep (se 1 (by rfl) ⟨1125296, by rfl⟩ : syracuseStep 1500395 = 2250593) B2250593
theorem B1500407 : Blo 1500070 1500407 := bstep (se 1 (by rfl) ⟨1125305, by rfl⟩ : syracuseStep 1500407 = 2250611) B2250611
theorem B3376385 : Blo 1500070 3376385 := bstep (se 2 (by rfl) ⟨1266144, by rfl⟩ : syracuseStep 3376385 = 2532289) B2532289
theorem B1500427 : Blo 1500070 1500427 := bstep (se 1 (by rfl) ⟨1125320, by rfl⟩ : syracuseStep 1500427 = 2250641) B2250641
theorem B1500439 : Blo 1500070 1500439 := bstep (se 1 (by rfl) ⟨1125329, by rfl⟩ : syracuseStep 1500439 = 2250659) B2250659
theorem B4171031 : Blo 1500070 4171031 := bstep (se 1 (by rfl) ⟨3128273, by rfl⟩ : syracuseStep 4171031 = 6256547) B6256547
theorem B1500459 : Blo 1500070 1500459 := bstep (se 1 (by rfl) ⟨1125344, by rfl⟩ : syracuseStep 1500459 = 2250689) B2250689
theorem B1500471 : Blo 1500070 1500471 := bstep (se 1 (by rfl) ⟨1125353, by rfl⟩ : syracuseStep 1500471 = 2250707) B2250707
theorem B5064011 : Blo 1500070 5064011 := bstep (se 1 (by rfl) ⟨3798008, by rfl⟩ : syracuseStep 5064011 = 7596017) B7596017
theorem B1500491 : Blo 1500070 1500491 := bstep (se 1 (by rfl) ⟨1125368, by rfl⟩ : syracuseStep 1500491 = 2250737) B2250737
theorem B1500503 : Blo 1500070 1500503 := bstep (se 1 (by rfl) ⟨1125377, by rfl⟩ : syracuseStep 1500503 = 2250755) B2250755
theorem B1500523 : Blo 1500070 1500523 := bstep (se 1 (by rfl) ⟨1125392, by rfl⟩ : syracuseStep 1500523 = 2250785) B2250785
theorem B1500535 : Blo 1500070 1500535 := bstep (se 1 (by rfl) ⟨1125401, by rfl⟩ : syracuseStep 1500535 = 2250803) B2250803
theorem B1500555 : Blo 1500070 1500555 := bstep (se 1 (by rfl) ⟨1125416, by rfl⟩ : syracuseStep 1500555 = 2250833) B2250833
theorem B1688971 : Blo 1500070 1688971 := bstep (se 1 (by rfl) ⟨1266728, by rfl⟩ : syracuseStep 1688971 = 2533457) B2533457
theorem B1500567 : Blo 1500070 1500567 := bstep (se 1 (by rfl) ⟨1125425, by rfl⟩ : syracuseStep 1500567 = 2250851) B2250851
theorem B1500587 : Blo 1500070 1500587 := bstep (se 1 (by rfl) ⟨1125440, by rfl⟩ : syracuseStep 1500587 = 2250881) B2250881
theorem B1500599 : Blo 1500070 1500599 := bstep (se 1 (by rfl) ⟨1125449, by rfl⟩ : syracuseStep 1500599 = 2250899) B2250899
theorem B1500619 : Blo 1500070 1500619 := bstep (se 1 (by rfl) ⟨1125464, by rfl⟩ : syracuseStep 1500619 = 2250929) B2250929
theorem B1500631 : Blo 1500070 1500631 := bstep (se 1 (by rfl) ⟨1125473, by rfl⟩ : syracuseStep 1500631 = 2250947) B2250947
theorem B3376601 : Blo 1500070 3376601 := bstep (se 2 (by rfl) ⟨1266225, by rfl⟩ : syracuseStep 3376601 = 2532451) B2532451
theorem B1500651 : Blo 1500070 1500651 := bstep (se 1 (by rfl) ⟨1125488, by rfl⟩ : syracuseStep 1500651 = 2250977) B2250977
theorem B1500663 : Blo 1500070 1500663 := bstep (se 1 (by rfl) ⟨1125497, by rfl⟩ : syracuseStep 1500663 = 2250995) B2250995
theorem B1689079 : Blo 1500070 1689079 := bstep (se 1 (by rfl) ⟨1266809, by rfl⟩ : syracuseStep 1689079 = 2533619) B2533619
theorem B1500683 : Blo 1500070 1500683 := bstep (se 1 (by rfl) ⟨1125512, by rfl⟩ : syracuseStep 1500683 = 2251025) B2251025
theorem B1500695 : Blo 1500070 1500695 := bstep (se 1 (by rfl) ⟨1125521, by rfl⟩ : syracuseStep 1500695 = 2251043) B2251043
theorem B1500715 : Blo 1500070 1500715 := bstep (se 1 (by rfl) ⟨1125536, by rfl⟩ : syracuseStep 1500715 = 2251073) B2251073
theorem B8119853 : Blo 1500070 8119853 := bstep (se 3 (by rfl) ⟨1522472, by rfl⟩ : syracuseStep 8119853 = 3044945) B3044945
theorem B3376691 : Blo 1500070 3376691 := bstep (se 1 (by rfl) ⟨2532518, by rfl⟩ : syracuseStep 3376691 = 5065037) B5065037
theorem B1500727 : Blo 1500070 1500727 := bstep (se 1 (by rfl) ⟨1125545, by rfl⟩ : syracuseStep 1500727 = 2251091) B2251091
theorem B1500747 : Blo 1500070 1500747 := bstep (se 1 (by rfl) ⟨1125560, by rfl⟩ : syracuseStep 1500747 = 2251121) B2251121
theorem B9619019 : Blo 1500070 9619019 := bstep (se 1 (by rfl) ⟨7214264, by rfl⟩ : syracuseStep 9619019 = 14428529) B14428529
theorem B1500759 : Blo 1500070 1500759 := bstep (se 1 (by rfl) ⟨1125569, by rfl⟩ : syracuseStep 1500759 = 2251139) B2251139
theorem B3376727 : Blo 1500070 3376727 := bstep (se 1 (by rfl) ⟨2532545, by rfl⟩ : syracuseStep 3376727 = 5065091) B5065091
theorem B5064281 : Blo 1500070 5064281 := bstep (se 2 (by rfl) ⟨1899105, by rfl⟩ : syracuseStep 5064281 = 3798211) B3798211
theorem B12830309 : Blo 1500070 12830309 := bstep (se 4 (by rfl) ⟨1202841, by rfl⟩ : syracuseStep 12830309 = 2405683) B2405683
theorem B1500779 : Blo 1500070 1500779 := bstep (se 1 (by rfl) ⟨1125584, by rfl⟩ : syracuseStep 1500779 = 2251169) B2251169
theorem B1500791 : Blo 1500070 1500791 := bstep (se 1 (by rfl) ⟨1125593, by rfl⟩ : syracuseStep 1500791 = 2251187) B2251187
theorem B1500811 : Blo 1500070 1500811 := bstep (se 1 (by rfl) ⟨1125608, by rfl⟩ : syracuseStep 1500811 = 2251217) B2251217
theorem B1500823 : Blo 1500070 1500823 := bstep (se 1 (by rfl) ⟨1125617, by rfl⟩ : syracuseStep 1500823 = 2251235) B2251235
theorem B1500843 : Blo 1500070 1500843 := bstep (se 1 (by rfl) ⟨1125632, by rfl⟩ : syracuseStep 1500843 = 2251265) B2251265
theorem B1689259 : Blo 1500070 1689259 := bstep (se 1 (by rfl) ⟨1266944, by rfl⟩ : syracuseStep 1689259 = 2533889) B2533889
theorem B1500855 : Blo 1500070 1500855 := bstep (se 1 (by rfl) ⟨1125641, by rfl⟩ : syracuseStep 1500855 = 2251283) B2251283
theorem B1500875 : Blo 1500070 1500875 := bstep (se 1 (by rfl) ⟨1125656, by rfl⟩ : syracuseStep 1500875 = 2251313) B2251313
theorem B1500887 : Blo 1500070 1500887 := bstep (se 1 (by rfl) ⟨1125665, by rfl⟩ : syracuseStep 1500887 = 2251331) B2251331
theorem B2533079 : Blo 1500070 2533079 := bstep (se 1 (by rfl) ⟨1899809, by rfl⟩ : syracuseStep 2533079 = 3799619) B3799619
theorem B1500907 : Blo 1500070 1500907 := bstep (se 1 (by rfl) ⟨1125680, by rfl⟩ : syracuseStep 1500907 = 2251361) B2251361
theorem B29640433 : Blo 1500070 29640433 := bstep (se 2 (by rfl) ⟨11115162, by rfl⟩ : syracuseStep 29640433 = 22230325) B22230325
theorem B1500919 : Blo 1500070 1500919 := bstep (se 1 (by rfl) ⟨1125689, by rfl⟩ : syracuseStep 1500919 = 2251379) B2251379
theorem B3376907 : Blo 1500070 3376907 := bstep (se 1 (by rfl) ⟨2532680, by rfl⟩ : syracuseStep 3376907 = 5065361) B5065361
theorem B1500939 : Blo 1500070 1500939 := bstep (se 1 (by rfl) ⟨1125704, by rfl⟩ : syracuseStep 1500939 = 2251409) B2251409
theorem B1500951 : Blo 1500070 1500951 := bstep (se 1 (by rfl) ⟨1125713, by rfl⟩ : syracuseStep 1500951 = 2251427) B2251427
theorem B1689367 : Blo 1500070 1689367 := bstep (se 1 (by rfl) ⟨1267025, by rfl⟩ : syracuseStep 1689367 = 2534051) B2534051
theorem B2705177 : Blo 1500070 2705177 := bstep (se 2 (by rfl) ⟨1014441, by rfl⟩ : syracuseStep 2705177 = 2028883) B2028883
theorem B1500971 : Blo 1500070 1500971 := bstep (se 1 (by rfl) ⟨1125728, by rfl⟩ : syracuseStep 1500971 = 2251457) B2251457
theorem B1500983 : Blo 1500070 1500983 := bstep (se 1 (by rfl) ⟨1125737, by rfl⟩ : syracuseStep 1500983 = 2251475) B2251475
theorem B3376961 : Blo 1500070 3376961 := bstep (se 2 (by rfl) ⟨1266360, by rfl⟩ : syracuseStep 3376961 = 2532721) B2532721
theorem B1501003 : Blo 1500070 1501003 := bstep (se 1 (by rfl) ⟨1125752, by rfl⟩ : syracuseStep 1501003 = 2251505) B2251505
theorem B1501015 : Blo 1500070 1501015 := bstep (se 1 (by rfl) ⟨1125761, by rfl⟩ : syracuseStep 1501015 = 2251523) B2251523
theorem B2533207 : Blo 1500070 2533207 := bstep (se 1 (by rfl) ⟨1899905, by rfl⟩ : syracuseStep 2533207 = 3799811) B3799811
theorem B1501035 : Blo 1500070 1501035 := bstep (se 1 (by rfl) ⟨1125776, by rfl⟩ : syracuseStep 1501035 = 2251553) B2251553
theorem B18499445 : Blo 1500070 18499445 := bstep (se 5 (by rfl) ⟨867161, by rfl⟩ : syracuseStep 18499445 = 1734323) B1734323
theorem B1501047 : Blo 1500070 1501047 := bstep (se 1 (by rfl) ⟨1125785, by rfl⟩ : syracuseStep 1501047 = 2251571) B2251571
theorem B1501067 : Blo 1500070 1501067 := bstep (se 1 (by rfl) ⟨1125800, by rfl⟩ : syracuseStep 1501067 = 2251601) B2251601
theorem B1501079 : Blo 1500070 1501079 := bstep (se 1 (by rfl) ⟨1125809, by rfl⟩ : syracuseStep 1501079 = 2251619) B2251619
theorem B1501099 : Blo 1500070 1501099 := bstep (se 1 (by rfl) ⟨1125824, by rfl⟩ : syracuseStep 1501099 = 2251649) B2251649
theorem B123242417 : Blo 1500070 123242417 := bstep (se 2 (by rfl) ⟨46215906, by rfl⟩ : syracuseStep 123242417 = 92431813) B92431813
theorem B1501111 : Blo 1500070 1501111 := bstep (se 1 (by rfl) ⟨1125833, by rfl⟩ : syracuseStep 1501111 = 2251667) B2251667
theorem B6498251 : Blo 1500070 6498251 := bstep (se 1 (by rfl) ⟨4873688, by rfl⟩ : syracuseStep 6498251 = 9747377) B9747377
theorem B1501131 : Blo 1500070 1501131 := bstep (se 1 (by rfl) ⟨1125848, by rfl⟩ : syracuseStep 1501131 = 2251697) B2251697
theorem B1689547 : Blo 1500070 1689547 := bstep (se 1 (by rfl) ⟨1267160, by rfl⟩ : syracuseStep 1689547 = 2534321) B2534321
theorem B1501143 : Blo 1500070 1501143 := bstep (se 1 (by rfl) ⟨1125857, by rfl⟩ : syracuseStep 1501143 = 2251715) B2251715
theorem B8112089 : Blo 1500070 8112089 := bstep (se 2 (by rfl) ⟨3042033, by rfl⟩ : syracuseStep 8112089 = 6084067) B6084067
theorem B1501163 : Blo 1500070 1501163 := bstep (se 1 (by rfl) ⟨1125872, by rfl⟩ : syracuseStep 1501163 = 2251745) B2251745
theorem B1501175 : Blo 1500070 1501175 := bstep (se 1 (by rfl) ⟨1125881, by rfl⟩ : syracuseStep 1501175 = 2251763) B2251763
theorem B1501195 : Blo 1500070 1501195 := bstep (se 1 (by rfl) ⟨1125896, by rfl⟩ : syracuseStep 1501195 = 2251793) B2251793
theorem B1501207 : Blo 1500070 1501207 := bstep (se 1 (by rfl) ⟨1125905, by rfl⟩ : syracuseStep 1501207 = 2251811) B2251811
theorem B3377177 : Blo 1500070 3377177 := bstep (se 2 (by rfl) ⟨1266441, by rfl⟩ : syracuseStep 3377177 = 2532883) B2532883
theorem B1501227 : Blo 1500070 1501227 := bstep (se 1 (by rfl) ⟨1125920, by rfl⟩ : syracuseStep 1501227 = 2251841) B2251841
theorem B11552813 : Blo 1500070 11552813 := bstep (se 3 (by rfl) ⟨2166152, by rfl⟩ : syracuseStep 11552813 = 4332305) B4332305
theorem B1501239 : Blo 1500070 1501239 := bstep (se 1 (by rfl) ⟨1125929, by rfl⟩ : syracuseStep 1501239 = 2251859) B2251859
theorem B1689655 : Blo 1500070 1689655 := bstep (se 1 (by rfl) ⟨1267241, by rfl⟩ : syracuseStep 1689655 = 2534483) B2534483
theorem B11397185 : Blo 1500070 11397185 := bstep (se 2 (by rfl) ⟨4273944, by rfl⟩ : syracuseStep 11397185 = 8547889) B8547889
theorem B1501259 : Blo 1500070 1501259 := bstep (se 1 (by rfl) ⟨1125944, by rfl⟩ : syracuseStep 1501259 = 2251889) B2251889
theorem B1501271 : Blo 1500070 1501271 := bstep (se 1 (by rfl) ⟨1125953, by rfl⟩ : syracuseStep 1501271 = 2251907) B2251907
theorem B1501291 : Blo 1500070 1501291 := bstep (se 1 (by rfl) ⟨1125968, by rfl⟩ : syracuseStep 1501291 = 2251937) B2251937
theorem B3377267 : Blo 1500070 3377267 := bstep (se 1 (by rfl) ⟨2532950, by rfl⟩ : syracuseStep 3377267 = 5065901) B5065901
theorem B1501303 : Blo 1500070 1501303 := bstep (se 1 (by rfl) ⟨1125977, by rfl⟩ : syracuseStep 1501303 = 2251955) B2251955
theorem B8669315 : Blo 1500070 8669315 := bstep (se 1 (by rfl) ⟨6501986, by rfl⟩ : syracuseStep 8669315 = 13003973) B13003973
theorem B1501323 : Blo 1500070 1501323 := bstep (se 1 (by rfl) ⟨1125992, by rfl⟩ : syracuseStep 1501323 = 2251985) B2251985
theorem B3205271 : Blo 1500070 3205271 := bstep (se 1 (by rfl) ⟨2403953, by rfl⟩ : syracuseStep 3205271 = 4807907) B4807907
theorem B3377303 : Blo 1500070 3377303 := bstep (se 1 (by rfl) ⟨2532977, by rfl⟩ : syracuseStep 3377303 = 5065955) B5065955
theorem B1501335 : Blo 1500070 1501335 := bstep (se 1 (by rfl) ⟨1126001, by rfl⟩ : syracuseStep 1501335 = 2252003) B2252003
theorem B1501355 : Blo 1500070 1501355 := bstep (se 1 (by rfl) ⟨1126016, by rfl⟩ : syracuseStep 1501355 = 2252033) B2252033
theorem B1501367 : Blo 1500070 1501367 := bstep (se 1 (by rfl) ⟨1126025, by rfl⟩ : syracuseStep 1501367 = 2252051) B2252051
theorem B1501387 : Blo 1500070 1501387 := bstep (se 1 (by rfl) ⟨1126040, by rfl⟩ : syracuseStep 1501387 = 2252081) B2252081
theorem B1501399 : Blo 1500070 1501399 := bstep (se 1 (by rfl) ⟨1126049, by rfl⟩ : syracuseStep 1501399 = 2252099) B2252099
theorem B1501419 : Blo 1500070 1501419 := bstep (se 1 (by rfl) ⟨1126064, by rfl⟩ : syracuseStep 1501419 = 2252129) B2252129
theorem B1501431 : Blo 1500070 1501431 := bstep (se 1 (by rfl) ⟨1126073, by rfl⟩ : syracuseStep 1501431 = 2252147) B2252147
theorem B1501451 : Blo 1500070 1501451 := bstep (se 1 (by rfl) ⟨1126088, by rfl⟩ : syracuseStep 1501451 = 2252177) B2252177
theorem B12830993 : Blo 1500070 12830993 := bstep (se 2 (by rfl) ⟨4811622, by rfl⟩ : syracuseStep 12830993 = 9623245) B9623245
theorem B5064983 : Blo 1500070 5064983 := bstep (se 1 (by rfl) ⟨3798737, by rfl⟩ : syracuseStep 5064983 = 7597475) B7597475
theorem B1501463 : Blo 1500070 1501463 := bstep (se 1 (by rfl) ⟨1126097, by rfl⟩ : syracuseStep 1501463 = 2252195) B2252195
theorem B1501483 : Blo 1500070 1501483 := bstep (se 1 (by rfl) ⟨1126112, by rfl⟩ : syracuseStep 1501483 = 2252225) B2252225
theorem B1501495 : Blo 1500070 1501495 := bstep (se 1 (by rfl) ⟨1126121, by rfl⟩ : syracuseStep 1501495 = 2252243) B2252243
theorem B3377483 : Blo 1500070 3377483 := bstep (se 1 (by rfl) ⟨2533112, by rfl⟩ : syracuseStep 3377483 = 5066225) B5066225
theorem B1501515 : Blo 1500070 1501515 := bstep (se 1 (by rfl) ⟨1126136, by rfl⟩ : syracuseStep 1501515 = 2252273) B2252273
theorem B1501527 : Blo 1500070 1501527 := bstep (se 1 (by rfl) ⟨1126145, by rfl⟩ : syracuseStep 1501527 = 2252291) B2252291
theorem B1501547 : Blo 1500070 1501547 := bstep (se 1 (by rfl) ⟨1126160, by rfl⟩ : syracuseStep 1501547 = 2252321) B2252321
theorem B1501559 : Blo 1500070 1501559 := bstep (se 1 (by rfl) ⟨1126169, by rfl⟩ : syracuseStep 1501559 = 2252339) B2252339
theorem B3377537 : Blo 1500070 3377537 := bstep (se 2 (by rfl) ⟨1266576, by rfl⟩ : syracuseStep 3377537 = 2533153) B2533153
theorem B1501579 : Blo 1500070 1501579 := bstep (se 1 (by rfl) ⟨1126184, by rfl⟩ : syracuseStep 1501579 = 2252369) B2252369
theorem B1501591 : Blo 1500070 1501591 := bstep (se 1 (by rfl) ⟨1126193, by rfl⟩ : syracuseStep 1501591 = 2252387) B2252387
theorem B1501611 : Blo 1500070 1501611 := bstep (se 1 (by rfl) ⟨1126208, by rfl⟩ : syracuseStep 1501611 = 2252417) B2252417
theorem B1501623 : Blo 1500070 1501623 := bstep (se 1 (by rfl) ⟨1126217, by rfl⟩ : syracuseStep 1501623 = 2252435) B2252435
theorem B2533835 : Blo 1500070 2533835 := bstep (se 1 (by rfl) ⟨1900376, by rfl⟩ : syracuseStep 2533835 = 3800753) B3800753
theorem B1501643 : Blo 1500070 1501643 := bstep (se 1 (by rfl) ⟨1126232, by rfl⟩ : syracuseStep 1501643 = 2252465) B2252465
theorem B1501655 : Blo 1500070 1501655 := bstep (se 1 (by rfl) ⟨1126241, by rfl⟩ : syracuseStep 1501655 = 2252483) B2252483
theorem B1501675 : Blo 1500070 1501675 := bstep (se 1 (by rfl) ⟨1126256, by rfl⟩ : syracuseStep 1501675 = 2252513) B2252513
theorem B1501687 : Blo 1500070 1501687 := bstep (se 1 (by rfl) ⟨1126265, by rfl⟩ : syracuseStep 1501687 = 2252531) B2252531
theorem B1501707 : Blo 1500070 1501707 := bstep (se 1 (by rfl) ⟨1126280, by rfl⟩ : syracuseStep 1501707 = 2252561) B2252561
theorem B1501719 : Blo 1500070 1501719 := bstep (se 1 (by rfl) ⟨1126289, by rfl⟩ : syracuseStep 1501719 = 2252579) B2252579
theorem B1501739 : Blo 1500070 1501739 := bstep (se 1 (by rfl) ⟨1126304, by rfl⟩ : syracuseStep 1501739 = 2252609) B2252609
theorem B1501751 : Blo 1500070 1501751 := bstep (se 1 (by rfl) ⟨1126313, by rfl⟩ : syracuseStep 1501751 = 2252627) B2252627
theorem B2533963 : Blo 1500070 2533963 := bstep (se 1 (by rfl) ⟨1900472, by rfl⟩ : syracuseStep 2533963 = 3800945) B3800945
theorem B1501771 : Blo 1500070 1501771 := bstep (se 1 (by rfl) ⟨1126328, by rfl⟩ : syracuseStep 1501771 = 2252657) B2252657
theorem B1501783 : Blo 1500070 1501783 := bstep (se 1 (by rfl) ⟨1126337, by rfl⟩ : syracuseStep 1501783 = 2252675) B2252675
theorem B3377753 : Blo 1500070 3377753 := bstep (se 2 (by rfl) ⟨1266657, by rfl⟩ : syracuseStep 3377753 = 2533315) B2533315
theorem B1501803 : Blo 1500070 1501803 := bstep (se 1 (by rfl) ⟨1126352, by rfl⟩ : syracuseStep 1501803 = 2252705) B2252705
theorem B1501815 : Blo 1500070 1501815 := bstep (se 1 (by rfl) ⟨1126361, by rfl⟩ : syracuseStep 1501815 = 2252723) B2252723
theorem B3041921 : Blo 1500070 3041921 := bstep (se 2 (by rfl) ⟨1140720, by rfl⟩ : syracuseStep 3041921 = 2281441) B2281441
theorem B1501835 : Blo 1500070 1501835 := bstep (se 1 (by rfl) ⟨1126376, by rfl⟩ : syracuseStep 1501835 = 2252753) B2252753
theorem B1501847 : Blo 1500070 1501847 := bstep (se 1 (by rfl) ⟨1126385, by rfl⟩ : syracuseStep 1501847 = 2252771) B2252771
theorem B1501867 : Blo 1500070 1501867 := bstep (se 1 (by rfl) ⟨1126400, by rfl⟩ : syracuseStep 1501867 = 2252801) B2252801
theorem B3377843 : Blo 1500070 3377843 := bstep (se 1 (by rfl) ⟨2533382, by rfl⟩ : syracuseStep 3377843 = 5066765) B5066765
theorem B1501879 : Blo 1500070 1501879 := bstep (se 1 (by rfl) ⟨1126409, by rfl⟩ : syracuseStep 1501879 = 2252819) B2252819
theorem B3205835 : Blo 1500070 3205835 := bstep (se 1 (by rfl) ⟨2404376, by rfl⟩ : syracuseStep 3205835 = 4808753) B4808753
theorem B1501899 : Blo 1500070 1501899 := bstep (se 1 (by rfl) ⟨1126424, by rfl⟩ : syracuseStep 1501899 = 2252849) B2252849
theorem B3377879 : Blo 1500070 3377879 := bstep (se 1 (by rfl) ⟨2533409, by rfl⟩ : syracuseStep 3377879 = 5066819) B5066819
theorem B2534105 : Blo 1500070 2534105 := bstep (se 2 (by rfl) ⟨950289, by rfl⟩ : syracuseStep 2534105 = 1900579) B1900579
theorem B1501911 : Blo 1500070 1501911 := bstep (se 1 (by rfl) ⟨1126433, by rfl⟩ : syracuseStep 1501911 = 2252867) B2252867
theorem B1501931 : Blo 1500070 1501931 := bstep (se 1 (by rfl) ⟨1126448, by rfl⟩ : syracuseStep 1501931 = 2252897) B2252897
theorem B1501943 : Blo 1500070 1501943 := bstep (se 1 (by rfl) ⟨1126457, by rfl⟩ : syracuseStep 1501943 = 2252915) B2252915
theorem B16239365 : Blo 1500070 16239365 := bstep (se 4 (by rfl) ⟨1522440, by rfl⟩ : syracuseStep 16239365 = 3044881) B3044881
theorem B2403083 : Blo 1500070 2403083 := bstep (se 1 (by rfl) ⟨1802312, by rfl⟩ : syracuseStep 2403083 = 3604625) B3604625
theorem B1501963 : Blo 1500070 1501963 := bstep (se 1 (by rfl) ⟨1126472, by rfl⟩ : syracuseStep 1501963 = 2252945) B2252945
theorem B1501975 : Blo 1500070 1501975 := bstep (se 1 (by rfl) ⟨1126481, by rfl⟩ : syracuseStep 1501975 = 2252963) B2252963
theorem B1501995 : Blo 1500070 1501995 := bstep (se 1 (by rfl) ⟨1126496, by rfl⟩ : syracuseStep 1501995 = 2252993) B2252993
theorem B5065523 : Blo 1500070 5065523 := bstep (se 1 (by rfl) ⟨3799142, by rfl⟩ : syracuseStep 5065523 = 7598285) B7598285
theorem B1502007 : Blo 1500070 1502007 := bstep (se 1 (by rfl) ⟨1126505, by rfl⟩ : syracuseStep 1502007 = 2253011) B2253011
theorem B1502027 : Blo 1500070 1502027 := bstep (se 1 (by rfl) ⟨1126520, by rfl⟩ : syracuseStep 1502027 = 2253041) B2253041
theorem B1502039 : Blo 1500070 1502039 := bstep (se 1 (by rfl) ⟨1126529, by rfl⟩ : syracuseStep 1502039 = 2253059) B2253059
theorem B5696345 : Blo 1500070 5696345 := bstep (se 2 (by rfl) ⟨2136129, by rfl⟩ : syracuseStep 5696345 = 4272259) B4272259
theorem B2534233 : Blo 1500070 2534233 := bstep (se 2 (by rfl) ⟨950337, by rfl⟩ : syracuseStep 2534233 = 1900675) B1900675
theorem B1502059 : Blo 1500070 1502059 := bstep (se 1 (by rfl) ⟨1126544, by rfl⟩ : syracuseStep 1502059 = 2253089) B2253089
theorem B3378059 : Blo 1500070 3378059 := bstep (se 1 (by rfl) ⟨2533544, by rfl⟩ : syracuseStep 3378059 = 5067089) B5067089
theorem B3378113 : Blo 1500070 3378113 := bstep (se 2 (by rfl) ⟨1266792, by rfl⟩ : syracuseStep 3378113 = 2533585) B2533585
theorem B5065793 : Blo 1500070 5065793 := bstep (se 2 (by rfl) ⟨1899672, by rfl⟩ : syracuseStep 5065793 = 3799345) B3799345
theorem B5778497 : Blo 1500070 5778497 := bstep (se 2 (by rfl) ⟨2166936, by rfl⟩ : syracuseStep 5778497 = 4333873) B4333873
theorem B8113283 : Blo 1500070 8113283 := bstep (se 1 (by rfl) ⟨6084962, by rfl⟩ : syracuseStep 8113283 = 12169925) B12169925
theorem B2403479 : Blo 1500070 2403479 := bstep (se 1 (by rfl) ⟨1802609, by rfl⟩ : syracuseStep 2403479 = 3605219) B3605219
theorem B7810199 : Blo 1500070 7810199 := bstep (se 1 (by rfl) ⟨5857649, by rfl⟩ : syracuseStep 7810199 = 11715299) B11715299
theorem B3206297 : Blo 1500070 3206297 := bstep (se 2 (by rfl) ⟨1202361, by rfl⟩ : syracuseStep 3206297 = 2404723) B2404723
theorem B3378329 : Blo 1500070 3378329 := bstep (se 2 (by rfl) ⟨1266873, by rfl⟩ : syracuseStep 3378329 = 2533747) B2533747
theorem B2706625 : Blo 1500070 2706625 := bstep (se 2 (by rfl) ⟨1014984, by rfl⟩ : syracuseStep 2706625 = 2029969) B2029969
theorem B3378419 : Blo 1500070 3378419 := bstep (se 1 (by rfl) ⟨2533814, by rfl⟩ : syracuseStep 3378419 = 5067629) B5067629
theorem B3378455 : Blo 1500070 3378455 := bstep (se 1 (by rfl) ⟨2533841, by rfl⟩ : syracuseStep 3378455 = 5067683) B5067683
theorem B3378635 : Blo 1500070 3378635 := bstep (se 1 (by rfl) ⟨2533976, by rfl⟩ : syracuseStep 3378635 = 5067953) B5067953
theorem B3378689 : Blo 1500070 3378689 := bstep (se 2 (by rfl) ⟨1267008, by rfl⟩ : syracuseStep 3378689 = 2534017) B2534017
theorem B5066333 : Blo 1500070 5066333 := bstep (se 3 (by rfl) ⟨949937, by rfl⟩ : syracuseStep 5066333 = 1899875) B1899875
theorem B6844121 : Blo 1500070 6844121 := bstep (se 2 (by rfl) ⟨2566545, by rfl⟩ : syracuseStep 6844121 = 5133091) B5133091
theorem B3378905 : Blo 1500070 3378905 := bstep (se 2 (by rfl) ⟨1267089, by rfl⟩ : syracuseStep 3378905 = 2534179) B2534179
theorem B6410029 : Blo 1500070 6410029 := bstep (se 3 (by rfl) ⟨1201880, by rfl⟩ : syracuseStep 6410029 = 2403761) B2403761
theorem B3378995 : Blo 1500070 3378995 := bstep (se 1 (by rfl) ⟨2534246, by rfl⟩ : syracuseStep 3378995 = 5068493) B5068493
theorem B2404171 : Blo 1500070 2404171 := bstep (se 1 (by rfl) ⟨1803128, by rfl⟩ : syracuseStep 2404171 = 3606257) B3606257
theorem B2256727 : Blo 1500070 2256727 := bstep (se 1 (by rfl) ⟨1692545, by rfl⟩ : syracuseStep 2256727 = 3385091) B3385091
theorem B3379031 : Blo 1500070 3379031 := bstep (se 1 (by rfl) ⟨2534273, by rfl⟩ : syracuseStep 3379031 = 5068547) B5068547
theorem B6172505 : Blo 1500070 6172505 := bstep (se 2 (by rfl) ⟨2314689, by rfl⟩ : syracuseStep 6172505 = 4629379) B4629379
theorem B16232309 : Blo 1500070 16232309 := bstep (se 5 (by rfl) ⟨760889, by rfl⟩ : syracuseStep 16232309 = 1521779) B1521779
theorem B4059031 : Blo 1500070 4059031 := bstep (se 1 (by rfl) ⟨3044273, by rfl⟩ : syracuseStep 4059031 = 6088547) B6088547
theorem B2404313 : Blo 1500070 2404313 := bstep (se 2 (by rfl) ⟨901617, by rfl⟩ : syracuseStep 2404313 = 1803235) B1803235
theorem B11399129 : Blo 1500070 11399129 := bstep (se 2 (by rfl) ⟨4274673, by rfl⟩ : syracuseStep 11399129 = 8549347) B8549347
theorem B3379211 : Blo 1500070 3379211 := bstep (se 1 (by rfl) ⟨2534408, by rfl⟩ : syracuseStep 3379211 = 5068817) B5068817
theorem B3797057 : Blo 1500070 3797057 := bstep (se 2 (by rfl) ⟨1423896, by rfl⟩ : syracuseStep 3797057 = 2847793) B2847793
theorem B3379265 : Blo 1500070 3379265 := bstep (se 2 (by rfl) ⟨1267224, by rfl⟩ : syracuseStep 3379265 = 2534449) B2534449
theorem B3608641 : Blo 1500070 3608641 := bstep (se 2 (by rfl) ⟨1353240, by rfl⟩ : syracuseStep 3608641 = 2706481) B2706481
theorem B4272203 : Blo 1500070 4272203 := bstep (se 1 (by rfl) ⟨3204152, by rfl⟩ : syracuseStep 4272203 = 6408305) B6408305
theorem B9621605 : Blo 1500070 9621605 := bstep (se 4 (by rfl) ⟨902025, by rfl⟩ : syracuseStep 9621605 = 1804051) B1804051
theorem B2314379 : Blo 1500070 2314379 := bstep (se 1 (by rfl) ⟨1735784, by rfl⟩ : syracuseStep 2314379 = 3471569) B3471569
theorem B3608755 : Blo 1500070 3608755 := bstep (se 1 (by rfl) ⟨2706566, by rfl⟩ : syracuseStep 3608755 = 5413133) B5413133
theorem B2887895 : Blo 1500070 2887895 := bstep (se 1 (by rfl) ⟨2165921, by rfl⟩ : syracuseStep 2887895 = 4331843) B4331843
theorem B25653509 : Blo 1500070 25653509 := bstep (se 4 (by rfl) ⟨2405016, by rfl⟩ : syracuseStep 25653509 = 4810033) B4810033
theorem B3379481 : Blo 1500070 3379481 := bstep (se 2 (by rfl) ⟨1267305, by rfl⟩ : syracuseStep 3379481 = 2534611) B2534611
theorem B5411117 : Blo 1500070 5411117 := bstep (se 3 (by rfl) ⟨1014584, by rfl⟩ : syracuseStep 5411117 = 2029169) B2029169
theorem B3207475 : Blo 1500070 3207475 := bstep (se 1 (by rfl) ⟨2405606, by rfl⟩ : syracuseStep 3207475 = 4811213) B4811213
theorem B72986993 : Blo 1500070 72986993 := bstep (se 2 (by rfl) ⟨27370122, by rfl⟩ : syracuseStep 72986993 = 54740245) B54740245
theorem B3379571 : Blo 1500070 3379571 := bstep (se 1 (by rfl) ⟨2534678, by rfl⟩ : syracuseStep 3379571 = 5069357) B5069357
theorem B3379607 : Blo 1500070 3379607 := bstep (se 1 (by rfl) ⟨2534705, by rfl⟩ : syracuseStep 3379607 = 5069411) B5069411
theorem B5697971 : Blo 1500070 5697971 := bstep (se 1 (by rfl) ⟨4273478, by rfl⟩ : syracuseStep 5697971 = 8546957) B8546957
theorem B5697985 : Blo 1500070 5697985 := bstep (se 2 (by rfl) ⟨2136744, by rfl⟩ : syracuseStep 5697985 = 4273489) B4273489
theorem B4272601 : Blo 1500070 4272601 := bstep (se 2 (by rfl) ⟨1602225, by rfl⟩ : syracuseStep 4272601 = 3204451) B3204451
theorem B12816913 : Blo 1500070 12816913 := bstep (se 2 (by rfl) ⟨4806342, by rfl⟩ : syracuseStep 12816913 = 9612685) B9612685
theorem B6844945 : Blo 1500070 6844945 := bstep (se 2 (by rfl) ⟨2566854, by rfl⟩ : syracuseStep 6844945 = 5133709) B5133709
theorem B7598609 : Blo 1500070 7598609 := bstep (se 2 (by rfl) ⟨2849478, by rfl⟩ : syracuseStep 7598609 = 5698957) B5698957
theorem B7598771 : Blo 1500070 7598771 := bstep (se 1 (by rfl) ⟨5699078, by rfl⟩ : syracuseStep 7598771 = 11398157) B11398157
theorem B5067467 : Blo 1500070 5067467 := bstep (se 1 (by rfl) ⟨3800600, by rfl⟩ : syracuseStep 5067467 = 7601201) B7601201
theorem B5411549 : Blo 1500070 5411549 := bstep (se 3 (by rfl) ⟨1014665, by rfl⟩ : syracuseStep 5411549 = 2029331) B2029331
theorem B3207937 : Blo 1500070 3207937 := bstep (se 2 (by rfl) ⟨1202976, by rfl⟩ : syracuseStep 3207937 = 2405953) B2405953
theorem B2282251 : Blo 1500070 2282251 := bstep (se 1 (by rfl) ⟨1711688, by rfl⟩ : syracuseStep 2282251 = 3423377) B3423377
theorem B12817187 : Blo 1500070 12817187 := bstep (se 1 (by rfl) ⟨9612890, by rfl⟩ : syracuseStep 12817187 = 19225781) B19225781
theorem B8549165 : Blo 1500070 8549165 := bstep (se 3 (by rfl) ⟨1602968, by rfl⟩ : syracuseStep 8549165 = 3205937) B3205937
theorem B9614173 : Blo 1500070 9614173 := bstep (se 3 (by rfl) ⟨1802657, by rfl⟩ : syracuseStep 9614173 = 3605315) B3605315
theorem B2405273 : Blo 1500070 2405273 := bstep (se 2 (by rfl) ⟨901977, by rfl⟩ : syracuseStep 2405273 = 1803955) B1803955
theorem B5067737 : Blo 1500070 5067737 := bstep (se 2 (by rfl) ⟨1900401, by rfl⟩ : syracuseStep 5067737 = 3800803) B3800803
theorem B13685939 : Blo 1500070 13685939 := bstep (se 1 (by rfl) ⟨10264454, by rfl⟩ : syracuseStep 13685939 = 20528909) B20528909
theorem B1520887 : Blo 1500070 1520887 := bstep (se 1 (by rfl) ⟨1140665, by rfl⟩ : syracuseStep 1520887 = 2281331) B2281331
theorem B2848051 : Blo 1500070 2848051 := bstep (se 1 (by rfl) ⟨2136038, by rfl⟩ : syracuseStep 2848051 = 4272077) B4272077
theorem B3798323 : Blo 1500070 3798323 := bstep (se 1 (by rfl) ⟨2848742, by rfl⟩ : syracuseStep 3798323 = 5697485) B5697485
theorem B2250137 : Blo 1500070 2250137 := bstep (se 2 (by rfl) ⟨843801, by rfl⟩ : syracuseStep 2250137 = 1687603) B1687603
theorem B5133761 : Blo 1500070 5133761 := bstep (se 2 (by rfl) ⟨1925160, by rfl⟩ : syracuseStep 5133761 = 3850321) B3850321
theorem B6411737 : Blo 1500070 6411737 := bstep (se 2 (by rfl) ⟨2404401, by rfl⟩ : syracuseStep 6411737 = 4808803) B4808803
theorem B2250251 : Blo 1500070 2250251 := bstep (se 1 (by rfl) ⟨1687688, by rfl⟩ : syracuseStep 2250251 = 3375377) B3375377
theorem B2250263 : Blo 1500070 2250263 := bstep (se 1 (by rfl) ⟨1687697, by rfl⟩ : syracuseStep 2250263 = 3375395) B3375395
theorem B2848279 : Blo 1500070 2848279 := bstep (se 1 (by rfl) ⟨2136209, by rfl⟩ : syracuseStep 2848279 = 4272419) B4272419
theorem B2250329 : Blo 1500070 2250329 := bstep (se 2 (by rfl) ⟨843873, by rfl⟩ : syracuseStep 2250329 = 1687747) B1687747
theorem B2848385 : Blo 1500070 2848385 := bstep (se 2 (by rfl) ⟨1068144, by rfl⟩ : syracuseStep 2848385 = 2136289) B2136289
theorem B5068439 : Blo 1500070 5068439 := bstep (se 1 (by rfl) ⟨3801329, by rfl⟩ : syracuseStep 5068439 = 7602659) B7602659
theorem B4273843 : Blo 1500070 4273843 := bstep (se 1 (by rfl) ⟨3205382, by rfl⟩ : syracuseStep 4273843 = 6410765) B6410765
theorem B5412545 : Blo 1500070 5412545 := bstep (se 2 (by rfl) ⟨2029704, by rfl⟩ : syracuseStep 5412545 = 4059409) B4059409
theorem B2250443 : Blo 1500070 2250443 := bstep (se 1 (by rfl) ⟨1687832, by rfl⟩ : syracuseStep 2250443 = 3375665) B3375665
theorem B2250455 : Blo 1500070 2250455 := bstep (se 1 (by rfl) ⟨1687841, by rfl⟩ : syracuseStep 2250455 = 3375683) B3375683
theorem B9885401 : Blo 1500070 9885401 := bstep (se 2 (by rfl) ⟨3707025, by rfl⟩ : syracuseStep 9885401 = 7414051) B7414051
theorem B1603319 : Blo 1500070 1603319 := bstep (se 1 (by rfl) ⟨1202489, by rfl⟩ : syracuseStep 1603319 = 2404979) B2404979
theorem B2250521 : Blo 1500070 2250521 := bstep (se 2 (by rfl) ⟨843945, by rfl⟩ : syracuseStep 2250521 = 1687891) B1687891
theorem B2848537 : Blo 1500070 2848537 := bstep (se 2 (by rfl) ⟨1068201, by rfl⟩ : syracuseStep 2848537 = 2136403) B2136403
theorem B3798859 : Blo 1500070 3798859 := bstep (se 1 (by rfl) ⟨2849144, by rfl⟩ : syracuseStep 3798859 = 5698289) B5698289
theorem B2250635 : Blo 1500070 2250635 := bstep (se 1 (by rfl) ⟨1687976, by rfl⟩ : syracuseStep 2250635 = 3375953) B3375953
theorem B2250647 : Blo 1500070 2250647 := bstep (se 1 (by rfl) ⟨1687985, by rfl⟩ : syracuseStep 2250647 = 3375971) B3375971
theorem B2250713 : Blo 1500070 2250713 := bstep (se 2 (by rfl) ⟨844017, by rfl⟩ : syracuseStep 2250713 = 1688035) B1688035
theorem B3799001 : Blo 1500070 3799001 := bstep (se 2 (by rfl) ⟨1424625, by rfl⟩ : syracuseStep 3799001 = 2849251) B2849251
theorem B2250827 : Blo 1500070 2250827 := bstep (se 1 (by rfl) ⟨1688120, by rfl⟩ : syracuseStep 2250827 = 3376241) B3376241
theorem B2250839 : Blo 1500070 2250839 := bstep (se 1 (by rfl) ⟨1688129, by rfl⟩ : syracuseStep 2250839 = 3376259) B3376259
theorem B1898635 : Blo 1500070 1898635 := bstep (se 1 (by rfl) ⟨1423976, by rfl⟩ : syracuseStep 1898635 = 2847953) B2847953
theorem B3954839 : Blo 1500070 3954839 := bstep (se 1 (by rfl) ⟨2966129, by rfl⟩ : syracuseStep 3954839 = 5932259) B5932259
theorem B2250905 : Blo 1500070 2250905 := bstep (se 2 (by rfl) ⟨844089, by rfl⟩ : syracuseStep 2250905 = 1688179) B1688179
theorem B5068979 : Blo 1500070 5068979 := bstep (se 1 (by rfl) ⟨3801734, by rfl⟩ : syracuseStep 5068979 = 7603469) B7603469
theorem B28850357 : Blo 1500070 28850357 := bstep (se 5 (by rfl) ⟨1352360, by rfl⟩ : syracuseStep 28850357 = 2704721) B2704721
theorem B2251019 : Blo 1500070 2251019 := bstep (se 1 (by rfl) ⟨1688264, by rfl⟩ : syracuseStep 2251019 = 3376529) B3376529
theorem B11393297 : Blo 1500070 11393297 := bstep (se 2 (by rfl) ⟨4272486, by rfl⟩ : syracuseStep 11393297 = 8544973) B8544973
theorem B2251031 : Blo 1500070 2251031 := bstep (se 1 (by rfl) ⟨1688273, by rfl⟩ : syracuseStep 2251031 = 3376547) B3376547
theorem B1734967 : Blo 1500070 1734967 := bstep (se 1 (by rfl) ⟨1301225, by rfl⟩ : syracuseStep 1734967 = 2602451) B2602451
theorem B5699915 : Blo 1500070 5699915 := bstep (se 1 (by rfl) ⟨4274936, by rfl⟩ : syracuseStep 5699915 = 8549873) B8549873
theorem B2251097 : Blo 1500070 2251097 := bstep (se 2 (by rfl) ⟨844161, by rfl⟩ : syracuseStep 2251097 = 1688323) B1688323
theorem B5699929 : Blo 1500070 5699929 := bstep (se 2 (by rfl) ⟨2137473, by rfl⟩ : syracuseStep 5699929 = 4274947) B4274947
theorem B3422579 : Blo 1500070 3422579 := bstep (se 1 (by rfl) ⟨2566934, by rfl⟩ : syracuseStep 3422579 = 5133869) B5133869
theorem B1898903 : Blo 1500070 1898903 := bstep (se 1 (by rfl) ⟨1424177, by rfl⟩ : syracuseStep 1898903 = 2848355) B2848355
theorem B1604011 : Blo 1500070 1604011 := bstep (se 1 (by rfl) ⟨1203008, by rfl⟩ : syracuseStep 1604011 = 2406017) B2406017
theorem B5069249 : Blo 1500070 5069249 := bstep (se 2 (by rfl) ⟨1900968, by rfl⟩ : syracuseStep 5069249 = 3801937) B3801937
theorem B2251211 : Blo 1500070 2251211 := bstep (se 1 (by rfl) ⟨1688408, by rfl⟩ : syracuseStep 2251211 = 3376817) B3376817
theorem B2251223 : Blo 1500070 2251223 := bstep (se 1 (by rfl) ⟨1688417, by rfl⟩ : syracuseStep 2251223 = 3376835) B3376835
theorem B2251289 : Blo 1500070 2251289 := bstep (se 2 (by rfl) ⟨844233, by rfl⟩ : syracuseStep 2251289 = 1688467) B1688467
theorem B7600715 : Blo 1500070 7600715 := bstep (se 1 (by rfl) ⟨5700536, by rfl⟩ : syracuseStep 7600715 = 11401073) B11401073
theorem B2136665 : Blo 1500070 2136665 := bstep (se 2 (by rfl) ⟨801249, by rfl⟩ : syracuseStep 2136665 = 1602499) B1602499
theorem B2251403 : Blo 1500070 2251403 := bstep (se 1 (by rfl) ⟨1688552, by rfl⟩ : syracuseStep 2251403 = 3377105) B3377105
theorem B2251415 : Blo 1500070 2251415 := bstep (se 1 (by rfl) ⟨1688561, by rfl⟩ : syracuseStep 2251415 = 3377123) B3377123
theorem B6413003 : Blo 1500070 6413003 := bstep (se 1 (by rfl) ⟨4809752, by rfl⟩ : syracuseStep 6413003 = 9619505) B9619505
theorem B1522379 : Blo 1500070 1522379 := bstep (se 1 (by rfl) ⟨1141784, by rfl⟩ : syracuseStep 1522379 = 2283569) B2283569
theorem B2251481 : Blo 1500070 2251481 := bstep (se 2 (by rfl) ⟨844305, by rfl⟩ : syracuseStep 2251481 = 1688611) B1688611
theorem B3799831 : Blo 1500070 3799831 := bstep (se 1 (by rfl) ⟨2849873, by rfl⟩ : syracuseStep 3799831 = 5699747) B5699747
theorem B2251595 : Blo 1500070 2251595 := bstep (se 1 (by rfl) ⟨1688696, by rfl⟩ : syracuseStep 2251595 = 3377393) B3377393
theorem B11123531 : Blo 1500070 11123531 := bstep (se 1 (by rfl) ⟨8342648, by rfl⟩ : syracuseStep 11123531 = 16685297) B16685297
theorem B2251607 : Blo 1500070 2251607 := bstep (se 1 (by rfl) ⟨1688705, by rfl⟩ : syracuseStep 2251607 = 3377411) B3377411
theorem B2251673 : Blo 1500070 2251673 := bstep (se 2 (by rfl) ⟨844377, by rfl⟩ : syracuseStep 2251673 = 1688755) B1688755
theorem B55540657 : Blo 1500070 55540657 := bstep (se 2 (by rfl) ⟨20827746, by rfl⟩ : syracuseStep 55540657 = 41655493) B41655493
theorem B2251787 : Blo 1500070 2251787 := bstep (se 1 (by rfl) ⟨1688840, by rfl⟩ : syracuseStep 2251787 = 3377681) B3377681
theorem B2251799 : Blo 1500070 2251799 := bstep (se 1 (by rfl) ⟨1688849, by rfl⟩ : syracuseStep 2251799 = 3377699) B3377699
theorem B2849843 : Blo 1500070 2849843 := bstep (se 1 (by rfl) ⟨2137382, by rfl⟩ : syracuseStep 2849843 = 4274765) B4274765
theorem B6413363 : Blo 1500070 6413363 := bstep (se 1 (by rfl) ⟨4810022, by rfl⟩ : syracuseStep 6413363 = 9620045) B9620045
theorem B1899607 : Blo 1500070 1899607 := bstep (se 1 (by rfl) ⟨1424705, by rfl⟩ : syracuseStep 1899607 = 2849411) B2849411
theorem B2251865 : Blo 1500070 2251865 := bstep (se 2 (by rfl) ⟨844449, by rfl⟩ : syracuseStep 2251865 = 1688899) B1688899
theorem B2849995 : Blo 1500070 2849995 := bstep (se 1 (by rfl) ⟨2137496, by rfl⟩ : syracuseStep 2849995 = 4274993) B4274993
theorem B2251979 : Blo 1500070 2251979 := bstep (se 1 (by rfl) ⟨1688984, by rfl⟩ : syracuseStep 2251979 = 3377969) B3377969
theorem B3800267 : Blo 1500070 3800267 := bstep (se 1 (by rfl) ⟨2850200, by rfl⟩ : syracuseStep 3800267 = 5700401) B5700401
theorem B2137303 : Blo 1500070 2137303 := bstep (se 1 (by rfl) ⟨1602977, by rfl⟩ : syracuseStep 2137303 = 3205955) B3205955
theorem B2251991 : Blo 1500070 2251991 := bstep (se 1 (by rfl) ⟨1688993, by rfl⟩ : syracuseStep 2251991 = 3377987) B3377987
theorem B5700887 : Blo 1500070 5700887 := bstep (se 1 (by rfl) ⟨4275665, by rfl⟩ : syracuseStep 5700887 = 8551331) B8551331
theorem B2252057 : Blo 1500070 2252057 := bstep (se 2 (by rfl) ⟨844521, by rfl⟩ : syracuseStep 2252057 = 1689043) B1689043
theorem B11402531 : Blo 1500070 11402531 := bstep (se 1 (by rfl) ⟨8551898, by rfl⟩ : syracuseStep 11402531 = 17103797) B17103797
theorem B9878885 : Blo 1500070 9878885 := bstep (se 4 (by rfl) ⟨926145, by rfl⟩ : syracuseStep 9878885 = 1852291) B1852291
theorem B2252171 : Blo 1500070 2252171 := bstep (se 1 (by rfl) ⟨1689128, by rfl⟩ : syracuseStep 2252171 = 3378257) B3378257
theorem B2252183 : Blo 1500070 2252183 := bstep (se 1 (by rfl) ⟨1689137, by rfl⟩ : syracuseStep 2252183 = 3378275) B3378275
theorem B11124173 : Blo 1500070 11124173 := bstep (se 3 (by rfl) ⟨2085782, by rfl⟩ : syracuseStep 11124173 = 4171565) B4171565
theorem B2252249 : Blo 1500070 2252249 := bstep (se 2 (by rfl) ⟨844593, by rfl⟩ : syracuseStep 2252249 = 1689187) B1689187
theorem B2850329 : Blo 1500070 2850329 := bstep (se 2 (by rfl) ⟨1068873, by rfl⟩ : syracuseStep 2850329 = 2137747) B2137747
theorem B8543789 : Blo 1500070 8543789 := bstep (se 3 (by rfl) ⟨1601960, by rfl⟩ : syracuseStep 8543789 = 3203921) B3203921
theorem B3800641 : Blo 1500070 3800641 := bstep (se 2 (by rfl) ⟨1425240, by rfl⟩ : syracuseStep 3800641 = 2850481) B2850481
theorem B2252363 : Blo 1500070 2252363 := bstep (se 1 (by rfl) ⟨1689272, by rfl⟩ : syracuseStep 2252363 = 3378545) B3378545
theorem B2252375 : Blo 1500070 2252375 := bstep (se 1 (by rfl) ⟨1689281, by rfl⟩ : syracuseStep 2252375 = 3378563) B3378563
theorem B2252441 : Blo 1500070 2252441 := bstep (se 2 (by rfl) ⟨844665, by rfl⟩ : syracuseStep 2252441 = 1689331) B1689331
theorem B11124485 : Blo 1500070 11124485 := bstep (se 4 (by rfl) ⟨1042920, by rfl⟩ : syracuseStep 11124485 = 2085841) B2085841
theorem B2252555 : Blo 1500070 2252555 := bstep (se 1 (by rfl) ⟨1689416, by rfl⟩ : syracuseStep 2252555 = 3378833) B3378833
theorem B8109841 : Blo 1500070 8109841 := bstep (se 2 (by rfl) ⟨3041190, by rfl⟩ : syracuseStep 8109841 = 6082381) B6082381
theorem B2252567 : Blo 1500070 2252567 := bstep (se 1 (by rfl) ⟨1689425, by rfl⟩ : syracuseStep 2252567 = 3378851) B3378851
theorem B2252633 : Blo 1500070 2252633 := bstep (se 2 (by rfl) ⟨844737, by rfl⟩ : syracuseStep 2252633 = 1689475) B1689475
theorem B2252747 : Blo 1500070 2252747 := bstep (se 1 (by rfl) ⟨1689560, by rfl⟩ : syracuseStep 2252747 = 3379121) B3379121
theorem B2252759 : Blo 1500070 2252759 := bstep (se 1 (by rfl) ⟨1689569, by rfl⟩ : syracuseStep 2252759 = 3379139) B3379139
theorem B2252807 : Blo 1500070 2252807 := bstep (se 1 (by rfl) ⟨1689605, by rfl⟩ : syracuseStep 2252807 = 3379211) B3379211
theorem B5701661 : Blo 1500070 5701661 := bstep (se 3 (by rfl) ⟨1069061, by rfl⟩ : syracuseStep 5701661 = 2138123) B2138123
theorem B2531371 : Blo 1500070 2531371 := bstep (se 1 (by rfl) ⟨1898528, by rfl⟩ : syracuseStep 2531371 = 3797057) B3797057
theorem B2252843 : Blo 1500070 2252843 := bstep (se 1 (by rfl) ⟨1689632, by rfl⟩ : syracuseStep 2252843 = 3379265) B3379265
theorem B6414403 : Blo 1500070 6414403 := bstep (se 1 (by rfl) ⟨4810802, by rfl⟩ : syracuseStep 6414403 = 9621605) B9621605
theorem B2252873 : Blo 1500070 2252873 := bstep (se 2 (by rfl) ⟨844827, by rfl⟩ : syracuseStep 2252873 = 1689655) B1689655
theorem B1925263 : Blo 1500070 1925263 := bstep (se 1 (by rfl) ⟨1443947, by rfl⟩ : syracuseStep 1925263 = 2887895) B2887895
theorem B3375251 : Blo 1500070 3375251 := bstep (se 1 (by rfl) ⟨2531438, by rfl⟩ : syracuseStep 3375251 = 5062877) B5062877
theorem B15409325 : Blo 1500070 15409325 := bstep (se 3 (by rfl) ⟨2889248, by rfl⟩ : syracuseStep 15409325 = 5778497) B5778497
theorem B2531513 : Blo 1500070 2531513 := bstep (se 2 (by rfl) ⟨949317, by rfl⟩ : syracuseStep 2531513 = 1898635) B1898635
theorem B2252987 : Blo 1500070 2252987 := bstep (se 1 (by rfl) ⟨1689740, by rfl⟩ : syracuseStep 2252987 = 3379481) B3379481
theorem B3375305 : Blo 1500070 3375305 := bstep (se 2 (by rfl) ⟨1265739, by rfl⟩ : syracuseStep 3375305 = 2531479) B2531479
theorem B3801289 : Blo 1500070 3801289 := bstep (se 2 (by rfl) ⟨1425483, by rfl⟩ : syracuseStep 3801289 = 2850967) B2850967
theorem B2253047 : Blo 1500070 2253047 := bstep (se 1 (by rfl) ⟨1689785, by rfl⟩ : syracuseStep 2253047 = 3379571) B3379571
theorem B2253071 : Blo 1500070 2253071 := bstep (se 1 (by rfl) ⟨1689803, by rfl⟩ : syracuseStep 2253071 = 3379607) B3379607
theorem B3801431 : Blo 1500070 3801431 := bstep (se 1 (by rfl) ⟨2851073, by rfl⟩ : syracuseStep 3801431 = 5702147) B5702147
theorem B4276633 : Blo 1500070 4276633 := bstep (se 2 (by rfl) ⟨1603737, by rfl⟩ : syracuseStep 4276633 = 3207475) B3207475
theorem B1688071 : Blo 1500070 1688071 := bstep (se 1 (by rfl) ⟨1266053, by rfl⟩ : syracuseStep 1688071 = 2532107) B2532107
theorem B8544791 : Blo 1500070 8544791 := bstep (se 1 (by rfl) ⟨6408593, by rfl⟩ : syracuseStep 8544791 = 12817187) B12817187
theorem B2138681 : Blo 1500070 2138681 := bstep (se 2 (by rfl) ⟨802005, by rfl⟩ : syracuseStep 2138681 = 1604011) B1604011
theorem B5063255 : Blo 1500070 5063255 := bstep (se 1 (by rfl) ⟨3797441, by rfl⟩ : syracuseStep 5063255 = 7594883) B7594883
theorem B1688251 : Blo 1500070 1688251 := bstep (se 1 (by rfl) ⟨1266188, by rfl⟩ : syracuseStep 1688251 = 2532377) B2532377
theorem B17089217 : Blo 1500070 17089217 := bstep (se 2 (by rfl) ⟨6408456, by rfl⟩ : syracuseStep 17089217 = 12816913) B12816913
theorem B9126593 : Blo 1500070 9126593 := bstep (se 2 (by rfl) ⟨3422472, by rfl⟩ : syracuseStep 9126593 = 6844945) B6844945
theorem B5702345 : Blo 1500070 5702345 := bstep (se 2 (by rfl) ⟨2138379, by rfl⟩ : syracuseStep 5702345 = 4276759) B4276759
theorem B2532215 : Blo 1500070 2532215 := bstep (se 1 (by rfl) ⟨1899161, by rfl⟩ : syracuseStep 2532215 = 3798323) B3798323
theorem B3376007 : Blo 1500070 3376007 := bstep (se 1 (by rfl) ⟨2532005, by rfl⟩ : syracuseStep 3376007 = 5064011) B5064011
theorem B1500091 : Blo 1500070 1500091 := bstep (se 1 (by rfl) ⟨1125068, by rfl⟩ : syracuseStep 1500091 = 2250137) B2250137
theorem B4277249 : Blo 1500070 4277249 := bstep (se 2 (by rfl) ⟨1603968, by rfl⟩ : syracuseStep 4277249 = 3207937) B3207937
theorem B1500167 : Blo 1500070 1500167 := bstep (se 1 (by rfl) ⟨1125125, by rfl⟩ : syracuseStep 1500167 = 2250251) B2250251
theorem B1500175 : Blo 1500070 1500175 := bstep (se 1 (by rfl) ⟨1125131, by rfl⟩ : syracuseStep 1500175 = 2250263) B2250263
theorem B1500219 : Blo 1500070 1500219 := bstep (se 1 (by rfl) ⟨1125164, by rfl⟩ : syracuseStep 1500219 = 2250329) B2250329
theorem B3376187 : Blo 1500070 3376187 := bstep (se 1 (by rfl) ⟨2532140, by rfl⟩ : syracuseStep 3376187 = 5064281) B5064281
theorem B5063741 : Blo 1500070 5063741 := bstep (se 3 (by rfl) ⟨949451, by rfl⟩ : syracuseStep 5063741 = 1898903) B1898903
theorem B8553539 : Blo 1500070 8553539 := bstep (se 1 (by rfl) ⟨6415154, by rfl⟩ : syracuseStep 8553539 = 12830309) B12830309
theorem B1500295 : Blo 1500070 1500295 := bstep (se 1 (by rfl) ⟨1125221, by rfl⟩ : syracuseStep 1500295 = 2250443) B2250443
theorem B1500303 : Blo 1500070 1500303 := bstep (se 1 (by rfl) ⟨1125227, by rfl⟩ : syracuseStep 1500303 = 2250455) B2250455
theorem B1688719 : Blo 1500070 1688719 := bstep (se 1 (by rfl) ⟨1266539, by rfl⟩ : syracuseStep 1688719 = 2533079) B2533079
theorem B3376313 : Blo 1500070 3376313 := bstep (se 2 (by rfl) ⟨1266117, by rfl⟩ : syracuseStep 3376313 = 2532235) B2532235
theorem B1500347 : Blo 1500070 1500347 := bstep (se 1 (by rfl) ⟨1125260, by rfl⟩ : syracuseStep 1500347 = 2250521) B2250521
theorem B29664461 : Blo 1500070 29664461 := bstep (se 3 (by rfl) ⟨5562086, by rfl⟩ : syracuseStep 29664461 = 11124173) B11124173
theorem B17097965 : Blo 1500070 17097965 := bstep (se 3 (by rfl) ⟨3205868, by rfl⟩ : syracuseStep 17097965 = 6411737) B6411737
theorem B1500423 : Blo 1500070 1500423 := bstep (se 1 (by rfl) ⟨1125317, by rfl⟩ : syracuseStep 1500423 = 2250635) B2250635
theorem B1500431 : Blo 1500070 1500431 := bstep (se 1 (by rfl) ⟨1125323, by rfl⟩ : syracuseStep 1500431 = 2250647) B2250647
theorem B1500475 : Blo 1500070 1500475 := bstep (se 1 (by rfl) ⟨1125356, by rfl⟩ : syracuseStep 1500475 = 2250713) B2250713
theorem B5408059 : Blo 1500070 5408059 := bstep (se 1 (by rfl) ⟨4056044, by rfl⟩ : syracuseStep 5408059 = 8112089) B8112089
theorem B2532667 : Blo 1500070 2532667 := bstep (se 1 (by rfl) ⟨1899500, by rfl⟩ : syracuseStep 2532667 = 3799001) B3799001
theorem B7701875 : Blo 1500070 7701875 := bstep (se 1 (by rfl) ⟨5776406, by rfl⟩ : syracuseStep 7701875 = 11552813) B11552813
theorem B1500551 : Blo 1500070 1500551 := bstep (se 1 (by rfl) ⟨1125413, by rfl⟩ : syracuseStep 1500551 = 2250827) B2250827
theorem B1500559 : Blo 1500070 1500559 := bstep (se 1 (by rfl) ⟨1125419, by rfl⟩ : syracuseStep 1500559 = 2250839) B2250839
theorem B1500603 : Blo 1500070 1500603 := bstep (se 1 (by rfl) ⟨1125452, by rfl⟩ : syracuseStep 1500603 = 2250905) B2250905
theorem B2532809 : Blo 1500070 2532809 := bstep (se 2 (by rfl) ⟨949803, by rfl⟩ : syracuseStep 2532809 = 1899607) B1899607
theorem B1500679 : Blo 1500070 1500679 := bstep (se 1 (by rfl) ⟨1125509, by rfl⟩ : syracuseStep 1500679 = 2251019) B2251019
theorem B7595531 : Blo 1500070 7595531 := bstep (se 1 (by rfl) ⟨5696648, by rfl⟩ : syracuseStep 7595531 = 11393297) B11393297
theorem B8553995 : Blo 1500070 8553995 := bstep (se 1 (by rfl) ⟨6415496, by rfl⟩ : syracuseStep 8553995 = 12830993) B12830993
theorem B1500687 : Blo 1500070 1500687 := bstep (se 1 (by rfl) ⟨1125515, by rfl⟩ : syracuseStep 1500687 = 2251031) B2251031
theorem B3376655 : Blo 1500070 3376655 := bstep (se 1 (by rfl) ⟨2532491, by rfl⟩ : syracuseStep 3376655 = 5064983) B5064983
theorem B3376673 : Blo 1500070 3376673 := bstep (se 2 (by rfl) ⟨1266252, by rfl⟩ : syracuseStep 3376673 = 2532505) B2532505
theorem B1500731 : Blo 1500070 1500731 := bstep (se 1 (by rfl) ⟨1125548, by rfl⟩ : syracuseStep 1500731 = 2251097) B2251097
theorem B1500807 : Blo 1500070 1500807 := bstep (se 1 (by rfl) ⟨1125605, by rfl⟩ : syracuseStep 1500807 = 2251211) B2251211
theorem B1689223 : Blo 1500070 1689223 := bstep (se 1 (by rfl) ⟨1266917, by rfl⟩ : syracuseStep 1689223 = 2533835) B2533835
theorem B1500815 : Blo 1500070 1500815 := bstep (se 1 (by rfl) ⟨1125611, by rfl⟩ : syracuseStep 1500815 = 2251223) B2251223
theorem B7595693 : Blo 1500070 7595693 := bstep (se 3 (by rfl) ⟨1424192, by rfl⟩ : syracuseStep 7595693 = 2848385) B2848385
theorem B8111789 : Blo 1500070 8111789 := bstep (se 3 (by rfl) ⟨1520960, by rfl⟩ : syracuseStep 8111789 = 3041921) B3041921
theorem B1500859 : Blo 1500070 1500859 := bstep (se 1 (by rfl) ⟨1125644, by rfl⟩ : syracuseStep 1500859 = 2251289) B2251289
theorem B12822245 : Blo 1500070 12822245 := bstep (se 4 (by rfl) ⟨1202085, by rfl⟩ : syracuseStep 12822245 = 2404171) B2404171
theorem B1500935 : Blo 1500070 1500935 := bstep (se 1 (by rfl) ⟨1125701, by rfl⟩ : syracuseStep 1500935 = 2251403) B2251403
theorem B1500943 : Blo 1500070 1500943 := bstep (se 1 (by rfl) ⟨1125707, by rfl⟩ : syracuseStep 1500943 = 2251415) B2251415
theorem B1500987 : Blo 1500070 1500987 := bstep (se 1 (by rfl) ⟨1125740, by rfl⟩ : syracuseStep 1500987 = 2251481) B2251481
theorem B1689403 : Blo 1500070 1689403 := bstep (se 1 (by rfl) ⟨1267052, by rfl⟩ : syracuseStep 1689403 = 2534105) B2534105
theorem B3377015 : Blo 1500070 3377015 := bstep (se 1 (by rfl) ⟨2532761, by rfl⟩ : syracuseStep 3377015 = 5065523) B5065523
theorem B1501063 : Blo 1500070 1501063 := bstep (se 1 (by rfl) ⟨1125797, by rfl⟩ : syracuseStep 1501063 = 2251595) B2251595
theorem B7415687 : Blo 1500070 7415687 := bstep (se 1 (by rfl) ⟨5561765, by rfl⟩ : syracuseStep 7415687 = 11123531) B11123531
theorem B1501071 : Blo 1500070 1501071 := bstep (se 1 (by rfl) ⟨1125803, by rfl⟩ : syracuseStep 1501071 = 2251607) B2251607
theorem B1501115 : Blo 1500070 1501115 := bstep (se 1 (by rfl) ⟨1125836, by rfl⟩ : syracuseStep 1501115 = 2251673) B2251673
theorem B1501191 : Blo 1500070 1501191 := bstep (se 1 (by rfl) ⟨1125893, by rfl⟩ : syracuseStep 1501191 = 2251787) B2251787
theorem B1501199 : Blo 1500070 1501199 := bstep (se 1 (by rfl) ⟨1125899, by rfl⟩ : syracuseStep 1501199 = 2251799) B2251799
theorem B3377195 : Blo 1500070 3377195 := bstep (se 1 (by rfl) ⟨2532896, by rfl⟩ : syracuseStep 3377195 = 5065793) B5065793
theorem B1501243 : Blo 1500070 1501243 := bstep (se 1 (by rfl) ⟨1125932, by rfl⟩ : syracuseStep 1501243 = 2251865) B2251865
theorem B5408855 : Blo 1500070 5408855 := bstep (se 1 (by rfl) ⟨4056641, by rfl⟩ : syracuseStep 5408855 = 8113283) B8113283
theorem B1501319 : Blo 1500070 1501319 := bstep (se 1 (by rfl) ⟨1125989, by rfl⟩ : syracuseStep 1501319 = 2251979) B2251979
theorem B2533511 : Blo 1500070 2533511 := bstep (se 1 (by rfl) ⟨1900133, by rfl⟩ : syracuseStep 2533511 = 3800267) B3800267
theorem B1501327 : Blo 1500070 1501327 := bstep (se 1 (by rfl) ⟨1125995, by rfl⟩ : syracuseStep 1501327 = 2251991) B2251991
theorem B1501371 : Blo 1500070 1501371 := bstep (se 1 (by rfl) ⟨1126028, by rfl⟩ : syracuseStep 1501371 = 2252057) B2252057
theorem B1501447 : Blo 1500070 1501447 := bstep (se 1 (by rfl) ⟨1126085, by rfl⟩ : syracuseStep 1501447 = 2252171) B2252171
theorem B1501455 : Blo 1500070 1501455 := bstep (se 1 (by rfl) ⟨1126091, by rfl⟩ : syracuseStep 1501455 = 2252183) B2252183
theorem B1501499 : Blo 1500070 1501499 := bstep (se 1 (by rfl) ⟨1126124, by rfl⟩ : syracuseStep 1501499 = 2252249) B2252249
theorem B39520577 : Blo 1500070 39520577 := bstep (se 2 (by rfl) ⟨14820216, by rfl⟩ : syracuseStep 39520577 = 29640433) B29640433
theorem B5695859 : Blo 1500070 5695859 := bstep (se 1 (by rfl) ⟨4271894, by rfl⟩ : syracuseStep 5695859 = 8543789) B8543789
theorem B1501575 : Blo 1500070 1501575 := bstep (se 1 (by rfl) ⟨1126181, by rfl⟩ : syracuseStep 1501575 = 2252363) B2252363
theorem B1501583 : Blo 1500070 1501583 := bstep (se 1 (by rfl) ⟨1126187, by rfl⟩ : syracuseStep 1501583 = 2252375) B2252375
theorem B8546705 : Blo 1500070 8546705 := bstep (se 2 (by rfl) ⟨3205014, by rfl⟩ : syracuseStep 8546705 = 6410029) B6410029
theorem B3377555 : Blo 1500070 3377555 := bstep (se 1 (by rfl) ⟨2533166, by rfl⟩ : syracuseStep 3377555 = 5066333) B5066333
theorem B5065145 : Blo 1500070 5065145 := bstep (se 2 (by rfl) ⟨1899429, by rfl⟩ : syracuseStep 5065145 = 3798859) B3798859
theorem B1501627 : Blo 1500070 1501627 := bstep (se 1 (by rfl) ⟨1126220, by rfl⟩ : syracuseStep 1501627 = 2252441) B2252441
theorem B3377609 : Blo 1500070 3377609 := bstep (se 2 (by rfl) ⟨1266603, by rfl⟩ : syracuseStep 3377609 = 2533207) B2533207
theorem B3008969 : Blo 1500070 3008969 := bstep (se 2 (by rfl) ⟨1128363, by rfl⟩ : syracuseStep 3008969 = 2256727) B2256727
theorem B7416323 : Blo 1500070 7416323 := bstep (se 1 (by rfl) ⟨5562242, by rfl⟩ : syracuseStep 7416323 = 11124485) B11124485
theorem B1501703 : Blo 1500070 1501703 := bstep (se 1 (by rfl) ⟨1126277, by rfl⟩ : syracuseStep 1501703 = 2252555) B2252555
theorem B1501711 : Blo 1500070 1501711 := bstep (se 1 (by rfl) ⟨1126283, by rfl⟩ : syracuseStep 1501711 = 2252567) B2252567
theorem B1501755 : Blo 1500070 1501755 := bstep (se 1 (by rfl) ⟨1126316, by rfl⟩ : syracuseStep 1501755 = 2252633) B2252633
theorem B4115003 : Blo 1500070 4115003 := bstep (se 1 (by rfl) ⟨3086252, by rfl⟩ : syracuseStep 4115003 = 6172505) B6172505
theorem B1501831 : Blo 1500070 1501831 := bstep (se 1 (by rfl) ⟨1126373, by rfl⟩ : syracuseStep 1501831 = 2252747) B2252747
theorem B1501839 : Blo 1500070 1501839 := bstep (se 1 (by rfl) ⟨1126379, by rfl⟩ : syracuseStep 1501839 = 2252759) B2252759
theorem B1501883 : Blo 1500070 1501883 := bstep (se 1 (by rfl) ⟨1126412, by rfl⟩ : syracuseStep 1501883 = 2252825) B2252825
theorem B4811521 : Blo 1500070 4811521 := bstep (se 2 (by rfl) ⟨1804320, by rfl⟩ : syracuseStep 4811521 = 3608641) B3608641
theorem B1501959 : Blo 1500070 1501959 := bstep (se 1 (by rfl) ⟨1126469, by rfl⟩ : syracuseStep 1501959 = 2252939) B2252939
theorem B9612047 : Blo 1500070 9612047 := bstep (se 1 (by rfl) ⟨7209035, by rfl⟩ : syracuseStep 9612047 = 14418071) B14418071
theorem B2534159 : Blo 1500070 2534159 := bstep (se 1 (by rfl) ⟨1900619, by rfl⟩ : syracuseStep 2534159 = 3801239) B3801239
theorem B1501967 : Blo 1500070 1501967 := bstep (se 1 (by rfl) ⟨1126475, by rfl⟩ : syracuseStep 1501967 = 2252951) B2252951
theorem B5696315 : Blo 1500070 5696315 := bstep (se 1 (by rfl) ⟨4272236, by rfl⟩ : syracuseStep 5696315 = 8544473) B8544473
theorem B1502011 : Blo 1500070 1502011 := bstep (se 1 (by rfl) ⟨1126508, by rfl⟩ : syracuseStep 1502011 = 2253017) B2253017
theorem B3607411 : Blo 1500070 3607411 := bstep (se 1 (by rfl) ⟨2705558, by rfl⟩ : syracuseStep 3607411 = 5411117) B5411117
theorem B5065739 : Blo 1500070 5065739 := bstep (se 1 (by rfl) ⟨3799304, by rfl⟩ : syracuseStep 5065739 = 7598609) B7598609
theorem B6171677 : Blo 1500070 6171677 := bstep (se 3 (by rfl) ⟨1157189, by rfl⟩ : syracuseStep 6171677 = 2314379) B2314379
theorem B2403371 : Blo 1500070 2403371 := bstep (se 1 (by rfl) ⟨1802528, by rfl⟩ : syracuseStep 2403371 = 3605057) B3605057
theorem B10546237 : Blo 1500070 10546237 := bstep (se 3 (by rfl) ⟨1977419, by rfl⟩ : syracuseStep 10546237 = 3954839) B3954839
theorem B6409277 : Blo 1500070 6409277 := bstep (se 3 (by rfl) ⟨1201739, by rfl⟩ : syracuseStep 6409277 = 2403479) B2403479
theorem B8547389 : Blo 1500070 8547389 := bstep (se 3 (by rfl) ⟨1602635, by rfl⟩ : syracuseStep 8547389 = 3205271) B3205271
theorem B2313289 : Blo 1500070 2313289 := bstep (se 2 (by rfl) ⟨867483, by rfl⟩ : syracuseStep 2313289 = 1734967) B1734967
theorem B5065847 : Blo 1500070 5065847 := bstep (se 1 (by rfl) ⟨3799385, by rfl⟩ : syracuseStep 5065847 = 7598771) B7598771
theorem B3206279 : Blo 1500070 3206279 := bstep (se 1 (by rfl) ⟨2404709, by rfl⟩ : syracuseStep 3206279 = 4809419) B4809419
theorem B3378311 : Blo 1500070 3378311 := bstep (se 1 (by rfl) ⟨2533733, by rfl⟩ : syracuseStep 3378311 = 5067467) B5067467
theorem B7597313 : Blo 1500070 7597313 := bstep (se 2 (by rfl) ⟨2848992, by rfl⟩ : syracuseStep 7597313 = 5697985) B5697985
theorem B5696801 : Blo 1500070 5696801 := bstep (se 2 (by rfl) ⟨2136300, by rfl⟩ : syracuseStep 5696801 = 4272601) B4272601
theorem B2534699 : Blo 1500070 2534699 := bstep (se 1 (by rfl) ⟨1901024, by rfl⟩ : syracuseStep 2534699 = 3802049) B3802049
theorem B3378491 : Blo 1500070 3378491 := bstep (se 1 (by rfl) ⟨2533868, by rfl⟩ : syracuseStep 3378491 = 5067737) B5067737
theorem B6499769 : Blo 1500070 6499769 := bstep (se 2 (by rfl) ⟨2437413, by rfl⟩ : syracuseStep 6499769 = 4874827) B4874827
theorem B3378617 : Blo 1500070 3378617 := bstep (se 2 (by rfl) ⟨1266981, by rfl⟩ : syracuseStep 3378617 = 2533963) B2533963
theorem B2780687 : Blo 1500070 2780687 := bstep (se 1 (by rfl) ⟨2085515, by rfl⟩ : syracuseStep 2780687 = 4171031) B4171031
theorem B19246693 : Blo 1500070 19246693 := bstep (se 4 (by rfl) ⟨1804377, by rfl⟩ : syracuseStep 19246693 = 3608755) B3608755
theorem B3043001 : Blo 1500070 3043001 := bstep (se 2 (by rfl) ⟨1141125, by rfl⟩ : syracuseStep 3043001 = 2282251) B2282251
theorem B5066441 : Blo 1500070 5066441 := bstep (se 2 (by rfl) ⟨1899915, by rfl⟩ : syracuseStep 5066441 = 3799831) B3799831
theorem B3378959 : Blo 1500070 3378959 := bstep (se 1 (by rfl) ⟨2534219, by rfl⟩ : syracuseStep 3378959 = 5068439) B5068439
theorem B3378977 : Blo 1500070 3378977 := bstep (se 2 (by rfl) ⟨1267116, by rfl⟩ : syracuseStep 3378977 = 2534233) B2534233
theorem B14421797 : Blo 1500070 14421797 := bstep (se 4 (by rfl) ⟨1352043, by rfl⟩ : syracuseStep 14421797 = 2704087) B2704087
theorem B3608363 : Blo 1500070 3608363 := bstep (se 1 (by rfl) ⟨2706272, by rfl⟩ : syracuseStep 3608363 = 5412545) B5412545
theorem B6590267 : Blo 1500070 6590267 := bstep (se 1 (by rfl) ⟨4942700, by rfl⟩ : syracuseStep 6590267 = 9885401) B9885401
theorem B36507509 : Blo 1500070 36507509 := bstep (se 5 (by rfl) ⟨1711289, by rfl⟩ : syracuseStep 36507509 = 3422579) B3422579
theorem B12332963 : Blo 1500070 12332963 := bstep (se 1 (by rfl) ⟨9249722, by rfl⟩ : syracuseStep 12332963 = 18499445) B18499445
theorem B82161611 : Blo 1500070 82161611 := bstep (se 1 (by rfl) ⟨61621208, by rfl⟩ : syracuseStep 82161611 = 123242417) B123242417
theorem B7598123 : Blo 1500070 7598123 := bstep (se 1 (by rfl) ⟨5698592, by rfl⟩ : syracuseStep 7598123 = 11397185) B11397185
theorem B5779543 : Blo 1500070 5779543 := bstep (se 1 (by rfl) ⟨4334657, by rfl⟩ : syracuseStep 5779543 = 8669315) B8669315
theorem B3379319 : Blo 1500070 3379319 := bstep (se 1 (by rfl) ⟨2534489, by rfl⟩ : syracuseStep 3379319 = 5068979) B5068979
theorem B5697773 : Blo 1500070 5697773 := bstep (se 3 (by rfl) ⟨1068332, by rfl⟩ : syracuseStep 5697773 = 2136665) B2136665
theorem B4272385 : Blo 1500070 4272385 := bstep (se 2 (by rfl) ⟨1602144, by rfl⟩ : syracuseStep 4272385 = 3204289) B3204289
theorem B3608833 : Blo 1500070 3608833 := bstep (se 2 (by rfl) ⟨1353312, by rfl⟩ : syracuseStep 3608833 = 2706625) B2706625
theorem B3379499 : Blo 1500070 3379499 := bstep (se 1 (by rfl) ⟨2534624, by rfl⟩ : syracuseStep 3379499 = 5069249) B5069249
theorem B2027849 : Blo 1500070 2027849 := bstep (se 2 (by rfl) ⟨760443, by rfl⟩ : syracuseStep 2027849 = 1520887) B1520887
theorem B5067143 : Blo 1500070 5067143 := bstep (se 1 (by rfl) ⟨3800357, by rfl⟩ : syracuseStep 5067143 = 7600715) B7600715
theorem B3797401 : Blo 1500070 3797401 := bstep (se 2 (by rfl) ⟨1424025, by rfl⟩ : syracuseStep 3797401 = 2848051) B2848051
theorem B10826243 : Blo 1500070 10826243 := bstep (se 1 (by rfl) ⟨8119682, by rfl⟩ : syracuseStep 10826243 = 16239365) B16239365
theorem B1602055 : Blo 1500070 1602055 := bstep (se 1 (by rfl) ⟨1201541, by rfl⟩ : syracuseStep 1602055 = 2403083) B2403083
theorem B4059677 : Blo 1500070 4059677 := bstep (se 3 (by rfl) ⟨761189, by rfl⟩ : syracuseStep 4059677 = 1522379) B1522379
theorem B3797563 : Blo 1500070 3797563 := bstep (se 1 (by rfl) ⟨2848172, by rfl⟩ : syracuseStep 3797563 = 5696345) B5696345
theorem B14430797 : Blo 1500070 14430797 := bstep (se 3 (by rfl) ⟨2705774, by rfl⟩ : syracuseStep 14430797 = 5411549) B5411549
theorem B3797705 : Blo 1500070 3797705 := bstep (se 2 (by rfl) ⟨1424139, by rfl⟩ : syracuseStep 3797705 = 2848279) B2848279
theorem B7213805 : Blo 1500070 7213805 := bstep (se 3 (by rfl) ⟨1352588, by rfl⟩ : syracuseStep 7213805 = 2705177) B2705177
theorem B5067521 : Blo 1500070 5067521 := bstep (se 2 (by rfl) ⟨1900320, by rfl⟩ : syracuseStep 5067521 = 3800641) B3800641
theorem B5206799 : Blo 1500070 5206799 := bstep (se 1 (by rfl) ⟨3905099, by rfl⟩ : syracuseStep 5206799 = 7810199) B7810199
theorem B5698457 : Blo 1500070 5698457 := bstep (se 2 (by rfl) ⟨2136921, by rfl⟩ : syracuseStep 5698457 = 4273843) B4273843
theorem B3798049 : Blo 1500070 3798049 := bstep (se 2 (by rfl) ⟨1424268, by rfl⟩ : syracuseStep 3798049 = 2848537) B2848537
theorem B12825661 : Blo 1500070 12825661 := bstep (se 3 (by rfl) ⟨2404811, by rfl⟩ : syracuseStep 12825661 = 4809623) B4809623
theorem B5412041 : Blo 1500070 5412041 := bstep (se 2 (by rfl) ⟨2029515, by rfl⟩ : syracuseStep 5412041 = 4059031) B4059031
theorem B1602875 : Blo 1500070 1602875 := bstep (se 1 (by rfl) ⟨1202156, by rfl⟩ : syracuseStep 1602875 = 2404313) B2404313
theorem B7599419 : Blo 1500070 7599419 := bstep (se 1 (by rfl) ⟨5699564, by rfl⟩ : syracuseStep 7599419 = 11399129) B11399129
theorem B2250119 : Blo 1500070 2250119 := bstep (se 1 (by rfl) ⟨1687589, by rfl⟩ : syracuseStep 2250119 = 3375179) B3375179
theorem B2848135 : Blo 1500070 2848135 := bstep (se 1 (by rfl) ⟨2136101, by rfl⟩ : syracuseStep 2848135 = 4272203) B4272203
theorem B2250155 : Blo 1500070 2250155 := bstep (se 1 (by rfl) ⟨1687616, by rfl⟩ : syracuseStep 2250155 = 3375233) B3375233
theorem B2250185 : Blo 1500070 2250185 := bstep (se 2 (by rfl) ⟨843819, by rfl⟩ : syracuseStep 2250185 = 1687639) B1687639
theorem B7599581 : Blo 1500070 7599581 := bstep (se 3 (by rfl) ⟨1424921, by rfl⟩ : syracuseStep 7599581 = 2849843) B2849843
theorem B17102339 : Blo 1500070 17102339 := bstep (se 1 (by rfl) ⟨12826754, by rfl⟩ : syracuseStep 17102339 = 25653509) B25653509
theorem B5068331 : Blo 1500070 5068331 := bstep (se 1 (by rfl) ⟨3801248, by rfl⟩ : syracuseStep 5068331 = 7602497) B7602497
theorem B2250299 : Blo 1500070 2250299 := bstep (se 1 (by rfl) ⟨1687724, by rfl⟩ : syracuseStep 2250299 = 3375449) B3375449
theorem B48657995 : Blo 1500070 48657995 := bstep (se 1 (by rfl) ⟨36493496, by rfl⟩ : syracuseStep 48657995 = 72986993) B72986993
theorem B2250359 : Blo 1500070 2250359 := bstep (se 1 (by rfl) ⟨1687769, by rfl⟩ : syracuseStep 2250359 = 3375539) B3375539
theorem B3798647 : Blo 1500070 3798647 := bstep (se 1 (by rfl) ⟨2848985, by rfl⟩ : syracuseStep 3798647 = 5697971) B5697971
theorem B2250383 : Blo 1500070 2250383 := bstep (se 1 (by rfl) ⟨1687787, by rfl⟩ : syracuseStep 2250383 = 3375575) B3375575
theorem B2283179 : Blo 1500070 2283179 := bstep (se 1 (by rfl) ⟨1712384, by rfl⟩ : syracuseStep 2283179 = 3424769) B3424769
theorem B2250425 : Blo 1500070 2250425 := bstep (se 2 (by rfl) ⟨843909, by rfl⟩ : syracuseStep 2250425 = 1687819) B1687819
theorem B2250503 : Blo 1500070 2250503 := bstep (se 1 (by rfl) ⟨1687877, by rfl⟩ : syracuseStep 2250503 = 3375755) B3375755
theorem B7599905 : Blo 1500070 7599905 := bstep (se 2 (by rfl) ⟨2849964, by rfl⟩ : syracuseStep 7599905 = 5699929) B5699929
theorem B2250539 : Blo 1500070 2250539 := bstep (se 1 (by rfl) ⟨1687904, by rfl⟩ : syracuseStep 2250539 = 3375809) B3375809
theorem B2250569 : Blo 1500070 2250569 := bstep (se 2 (by rfl) ⟨843963, by rfl⟩ : syracuseStep 2250569 = 1687927) B1687927
theorem B5699443 : Blo 1500070 5699443 := bstep (se 1 (by rfl) ⟨4274582, by rfl⟩ : syracuseStep 5699443 = 8549165) B8549165
theorem B2250683 : Blo 1500070 2250683 := bstep (se 1 (by rfl) ⟨1688012, by rfl⟩ : syracuseStep 2250683 = 3376025) B3376025
theorem B2250743 : Blo 1500070 2250743 := bstep (se 1 (by rfl) ⟨1688057, by rfl⟩ : syracuseStep 2250743 = 3376115) B3376115
theorem B2250767 : Blo 1500070 2250767 := bstep (se 1 (by rfl) ⟨1688075, by rfl⟩ : syracuseStep 2250767 = 3376151) B3376151
theorem B2250809 : Blo 1500070 2250809 := bstep (se 2 (by rfl) ⟨844053, by rfl⟩ : syracuseStep 2250809 = 1688107) B1688107
theorem B9123959 : Blo 1500070 9123959 := bstep (se 1 (by rfl) ⟨6842969, by rfl⟩ : syracuseStep 9123959 = 13685939) B13685939
theorem B2250887 : Blo 1500070 2250887 := bstep (se 1 (by rfl) ⟨1688165, by rfl⟩ : syracuseStep 2250887 = 3376331) B3376331
theorem B2250923 : Blo 1500070 2250923 := bstep (se 1 (by rfl) ⟨1688192, by rfl⟩ : syracuseStep 2250923 = 3376385) B3376385
theorem B2250953 : Blo 1500070 2250953 := bstep (se 2 (by rfl) ⟨844107, by rfl⟩ : syracuseStep 2250953 = 1688215) B1688215
theorem B3422507 : Blo 1500070 3422507 := bstep (se 1 (by rfl) ⟨2566880, by rfl⟩ : syracuseStep 3422507 = 5133761) B5133761
theorem B2251067 : Blo 1500070 2251067 := bstep (se 1 (by rfl) ⟨1688300, by rfl⟩ : syracuseStep 2251067 = 3376601) B3376601
theorem B5413235 : Blo 1500070 5413235 := bstep (se 1 (by rfl) ⟨4059926, by rfl⟩ : syracuseStep 5413235 = 8119853) B8119853
theorem B2251127 : Blo 1500070 2251127 := bstep (se 1 (by rfl) ⟨1688345, by rfl⟩ : syracuseStep 2251127 = 3376691) B3376691
theorem B6412679 : Blo 1500070 6412679 := bstep (se 1 (by rfl) ⟨4809509, by rfl⟩ : syracuseStep 6412679 = 9619019) B9619019
theorem B2251151 : Blo 1500070 2251151 := bstep (se 1 (by rfl) ⟨1688363, by rfl⟩ : syracuseStep 2251151 = 3376727) B3376727
theorem B2251193 : Blo 1500070 2251193 := bstep (se 2 (by rfl) ⟨844197, by rfl⟩ : syracuseStep 2251193 = 1688395) B1688395
theorem B6412729 : Blo 1500070 6412729 := bstep (se 2 (by rfl) ⟨2404773, by rfl⟩ : syracuseStep 6412729 = 4809547) B4809547
theorem B12818897 : Blo 1500070 12818897 := bstep (se 2 (by rfl) ⟨4807086, by rfl⟩ : syracuseStep 12818897 = 9614173) B9614173
theorem B2251271 : Blo 1500070 2251271 := bstep (se 1 (by rfl) ⟨1688453, by rfl⟩ : syracuseStep 2251271 = 3376907) B3376907
theorem B2251307 : Blo 1500070 2251307 := bstep (se 1 (by rfl) ⟨1688480, by rfl⟩ : syracuseStep 2251307 = 3376961) B3376961
theorem B74054209 : Blo 1500070 74054209 := bstep (se 2 (by rfl) ⟨27770328, by rfl⟩ : syracuseStep 74054209 = 55540657) B55540657
theorem B2251337 : Blo 1500070 2251337 := bstep (se 2 (by rfl) ⟨844251, by rfl⟩ : syracuseStep 2251337 = 1688503) B1688503
theorem B4332167 : Blo 1500070 4332167 := bstep (se 1 (by rfl) ⟨3249125, by rfl⟩ : syracuseStep 4332167 = 6498251) B6498251
theorem B2251451 : Blo 1500070 2251451 := bstep (se 1 (by rfl) ⟨1688588, by rfl⟩ : syracuseStep 2251451 = 3377177) B3377177
theorem B7600877 : Blo 1500070 7600877 := bstep (se 3 (by rfl) ⟨1425164, by rfl⟩ : syracuseStep 7600877 = 2850329) B2850329
theorem B2251511 : Blo 1500070 2251511 := bstep (se 1 (by rfl) ⟨1688633, by rfl⟩ : syracuseStep 2251511 = 3377267) B3377267
theorem B2251535 : Blo 1500070 2251535 := bstep (se 1 (by rfl) ⟨1688651, by rfl⟩ : syracuseStep 2251535 = 3377303) B3377303
theorem B19233571 : Blo 1500070 19233571 := bstep (se 1 (by rfl) ⟨14425178, by rfl⟩ : syracuseStep 19233571 = 28850357) B28850357
theorem B2251577 : Blo 1500070 2251577 := bstep (se 2 (by rfl) ⟨844341, by rfl⟩ : syracuseStep 2251577 = 1688683) B1688683
theorem B2251655 : Blo 1500070 2251655 := bstep (se 1 (by rfl) ⟨1688741, by rfl⟩ : syracuseStep 2251655 = 3377483) B3377483
theorem B3799943 : Blo 1500070 3799943 := bstep (se 1 (by rfl) ⟨2849957, by rfl⟩ : syracuseStep 3799943 = 5699915) B5699915
theorem B6085529 : Blo 1500070 6085529 := bstep (se 2 (by rfl) ⟨2282073, by rfl⟩ : syracuseStep 6085529 = 4564147) B4564147
theorem B2251691 : Blo 1500070 2251691 := bstep (se 1 (by rfl) ⟨1688768, by rfl⟩ : syracuseStep 2251691 = 3377537) B3377537
theorem B3799993 : Blo 1500070 3799993 := bstep (se 2 (by rfl) ⟨1424997, by rfl⟩ : syracuseStep 3799993 = 2849995) B2849995
theorem B2849737 : Blo 1500070 2849737 := bstep (se 2 (by rfl) ⟨1068651, by rfl⟩ : syracuseStep 2849737 = 2137303) B2137303
theorem B2251721 : Blo 1500070 2251721 := bstep (se 2 (by rfl) ⟨844395, by rfl⟩ : syracuseStep 2251721 = 1688791) B1688791
theorem B2251835 : Blo 1500070 2251835 := bstep (se 1 (by rfl) ⟨1688876, by rfl⟩ : syracuseStep 2251835 = 3377753) B3377753
theorem B2251895 : Blo 1500070 2251895 := bstep (se 1 (by rfl) ⟨1688921, by rfl⟩ : syracuseStep 2251895 = 3377843) B3377843
theorem B2137223 : Blo 1500070 2137223 := bstep (se 1 (by rfl) ⟨1602917, by rfl⟩ : syracuseStep 2137223 = 3205835) B3205835
theorem B4275335 : Blo 1500070 4275335 := bstep (se 1 (by rfl) ⟨3206501, by rfl⟩ : syracuseStep 4275335 = 6413003) B6413003
theorem B2251919 : Blo 1500070 2251919 := bstep (se 1 (by rfl) ⟨1688939, by rfl⟩ : syracuseStep 2251919 = 3377879) B3377879
theorem B2251961 : Blo 1500070 2251961 := bstep (se 2 (by rfl) ⟨844485, by rfl⟩ : syracuseStep 2251961 = 1688971) B1688971
theorem B2252039 : Blo 1500070 2252039 := bstep (se 1 (by rfl) ⟨1689029, by rfl⟩ : syracuseStep 2252039 = 3378059) B3378059
theorem B2252075 : Blo 1500070 2252075 := bstep (se 1 (by rfl) ⟨1689056, by rfl⟩ : syracuseStep 2252075 = 3378113) B3378113
theorem B4275517 : Blo 1500070 4275517 := bstep (se 3 (by rfl) ⟨801659, by rfl⟩ : syracuseStep 4275517 = 1603319) B1603319
theorem B2252105 : Blo 1500070 2252105 := bstep (se 2 (by rfl) ⟨844539, by rfl⟩ : syracuseStep 2252105 = 1689079) B1689079
theorem B4275575 : Blo 1500070 4275575 := bstep (se 1 (by rfl) ⟨3206681, by rfl⟩ : syracuseStep 4275575 = 6413363) B6413363
theorem B2137531 : Blo 1500070 2137531 := bstep (se 1 (by rfl) ⟨1603148, by rfl⟩ : syracuseStep 2137531 = 3206297) B3206297
theorem B2252219 : Blo 1500070 2252219 := bstep (se 1 (by rfl) ⟨1689164, by rfl⟩ : syracuseStep 2252219 = 3378329) B3378329
theorem B2252279 : Blo 1500070 2252279 := bstep (se 1 (by rfl) ⟨1689209, by rfl⟩ : syracuseStep 2252279 = 3378419) B3378419
theorem B3800591 : Blo 1500070 3800591 := bstep (se 1 (by rfl) ⟨2850443, by rfl⟩ : syracuseStep 3800591 = 5700887) B5700887
theorem B2252303 : Blo 1500070 2252303 := bstep (se 1 (by rfl) ⟨1689227, by rfl⟩ : syracuseStep 2252303 = 3378455) B3378455
theorem B7601687 : Blo 1500070 7601687 := bstep (se 1 (by rfl) ⟨5701265, by rfl⟩ : syracuseStep 7601687 = 11402531) B11402531
theorem B2252345 : Blo 1500070 2252345 := bstep (se 2 (by rfl) ⟨844629, by rfl⟩ : syracuseStep 2252345 = 1689259) B1689259
theorem B6585923 : Blo 1500070 6585923 := bstep (se 1 (by rfl) ⟨4939442, by rfl⟩ : syracuseStep 6585923 = 9878885) B9878885
theorem B2252423 : Blo 1500070 2252423 := bstep (se 1 (by rfl) ⟨1689317, by rfl⟩ : syracuseStep 2252423 = 3378635) B3378635
theorem B2252459 : Blo 1500070 2252459 := bstep (se 1 (by rfl) ⟨1689344, by rfl⟩ : syracuseStep 2252459 = 3378689) B3378689
theorem B10813121 : Blo 1500070 10813121 := bstep (se 2 (by rfl) ⟨4054920, by rfl⟩ : syracuseStep 10813121 = 8109841) B8109841
theorem B2252489 : Blo 1500070 2252489 := bstep (se 2 (by rfl) ⟨844683, by rfl⟩ : syracuseStep 2252489 = 1689367) B1689367
theorem B6414061 : Blo 1500070 6414061 := bstep (se 3 (by rfl) ⟨1202636, by rfl⟩ : syracuseStep 6414061 = 2405273) B2405273
theorem B4562747 : Blo 1500070 4562747 := bstep (se 1 (by rfl) ⟨3422060, by rfl⟩ : syracuseStep 4562747 = 6844121) B6844121
theorem B2252603 : Blo 1500070 2252603 := bstep (se 1 (by rfl) ⟨1689452, by rfl⟩ : syracuseStep 2252603 = 3378905) B3378905
theorem B2252663 : Blo 1500070 2252663 := bstep (se 1 (by rfl) ⟨1689497, by rfl⟩ : syracuseStep 2252663 = 3378995) B3378995
theorem B2252687 : Blo 1500070 2252687 := bstep (se 1 (by rfl) ⟨1689515, by rfl⟩ : syracuseStep 2252687 = 3379031) B3379031
theorem B10821539 : Blo 1500070 10821539 := bstep (se 1 (by rfl) ⟨8116154, by rfl⟩ : syracuseStep 10821539 = 16232309) B16232309
theorem B2252729 : Blo 1500070 2252729 := bstep (se 2 (by rfl) ⟨844773, by rfl⟩ : syracuseStep 2252729 = 1689547) B1689547
theorem B3801107 : Blo 1500070 3801107 := bstep (se 1 (by rfl) ⟨2850830, by rfl⟩ : syracuseStep 3801107 = 5701661) B5701661
theorem B3375161 : Blo 1500070 3375161 := bstep (se 2 (by rfl) ⟨1265685, by rfl⟩ : syracuseStep 3375161 = 2531371) B2531371
theorem B2252879 : Blo 1500070 2252879 := bstep (se 1 (by rfl) ⟨1689659, by rfl⟩ : syracuseStep 2252879 = 3379319) B3379319
theorem B8552537 : Blo 1500070 8552537 := bstep (se 2 (by rfl) ⟨3207201, by rfl⟩ : syracuseStep 8552537 = 6414403) B6414403
theorem B1687675 : Blo 1500070 1687675 := bstep (se 1 (by rfl) ⟨1265756, by rfl⟩ : syracuseStep 1687675 = 2531513) B2531513
theorem B2252999 : Blo 1500070 2252999 := bstep (se 1 (by rfl) ⟨1689749, by rfl⟩ : syracuseStep 2252999 = 3379499) B3379499
theorem B24330557 : Blo 1500070 24330557 := bstep (se 3 (by rfl) ⟨4561979, by rfl⟩ : syracuseStep 24330557 = 9123959) B9123959
theorem B7217495 : Blo 1500070 7217495 := bstep (se 1 (by rfl) ⟨5413121, by rfl⟩ : syracuseStep 7217495 = 10826243) B10826243
theorem B12337541 : Blo 1500070 12337541 := bstep (se 4 (by rfl) ⟨1156644, by rfl⟩ : syracuseStep 12337541 = 2313289) B2313289
theorem B3375503 : Blo 1500070 3375503 := bstep (se 1 (by rfl) ⟨2531627, by rfl⟩ : syracuseStep 3375503 = 5063255) B5063255
theorem B41091533 : Blo 1500070 41091533 := bstep (se 3 (by rfl) ⟨7704662, by rfl⟩ : syracuseStep 41091533 = 15409325) B15409325
theorem B2531803 : Blo 1500070 2531803 := bstep (se 1 (by rfl) ⟨1898852, by rfl⟩ : syracuseStep 2531803 = 3797705) B3797705
theorem B3801563 : Blo 1500070 3801563 := bstep (se 1 (by rfl) ⟨2851172, by rfl⟩ : syracuseStep 3801563 = 5702345) B5702345
theorem B4809203 : Blo 1500070 4809203 := bstep (se 1 (by rfl) ⟨3606902, by rfl⟩ : syracuseStep 4809203 = 7213805) B7213805
theorem B5063201 : Blo 1500070 5063201 := bstep (se 2 (by rfl) ⟨1898700, by rfl⟩ : syracuseStep 5063201 = 3797401) B3797401
theorem B5702177 : Blo 1500070 5702177 := bstep (se 2 (by rfl) ⟨2138316, by rfl⟩ : syracuseStep 5702177 = 4276633) B4276633
theorem B1688143 : Blo 1500070 1688143 := bstep (se 1 (by rfl) ⟨1266107, by rfl⟩ : syracuseStep 1688143 = 2532215) B2532215
theorem B2851499 : Blo 1500070 2851499 := bstep (se 1 (by rfl) ⟨2138624, by rfl⟩ : syracuseStep 2851499 = 4277249) B4277249
theorem B3375827 : Blo 1500070 3375827 := bstep (se 1 (by rfl) ⟨2531870, by rfl⟩ : syracuseStep 3375827 = 5063741) B5063741
theorem B5702359 : Blo 1500070 5702359 := bstep (se 1 (by rfl) ⟨4276769, by rfl⟩ : syracuseStep 5702359 = 8553539) B8553539
theorem B5063417 : Blo 1500070 5063417 := bstep (se 2 (by rfl) ⟨1898781, by rfl⟩ : syracuseStep 5063417 = 3797563) B3797563
theorem B98738945 : Blo 1500070 98738945 := bstep (se 2 (by rfl) ⟨37027104, by rfl⟩ : syracuseStep 98738945 = 74054209) B74054209
theorem B9126685 : Blo 1500070 9126685 := bstep (se 3 (by rfl) ⟨1711253, by rfl⟩ : syracuseStep 9126685 = 3422507) B3422507
theorem B19776307 : Blo 1500070 19776307 := bstep (se 1 (by rfl) ⟨14832230, by rfl⟩ : syracuseStep 19776307 = 29664461) B29664461
theorem B5407597 : Blo 1500070 5407597 := bstep (se 3 (by rfl) ⟨1013924, by rfl⟩ : syracuseStep 5407597 = 2027849) B2027849
theorem B1500079 : Blo 1500070 1500079 := bstep (se 1 (by rfl) ⟨1125059, by rfl⟩ : syracuseStep 1500079 = 2250119) B2250119
theorem B1500103 : Blo 1500070 1500103 := bstep (se 1 (by rfl) ⟨1125077, by rfl⟩ : syracuseStep 1500103 = 2250155) B2250155
theorem B1500123 : Blo 1500070 1500123 := bstep (se 1 (by rfl) ⟨1125092, by rfl⟩ : syracuseStep 1500123 = 2250185) B2250185
theorem B1688539 : Blo 1500070 1688539 := bstep (se 1 (by rfl) ⟨1266404, by rfl⟩ : syracuseStep 1688539 = 2532809) B2532809
theorem B14435293 : Blo 1500070 14435293 := bstep (se 3 (by rfl) ⟨2706617, by rfl⟩ : syracuseStep 14435293 = 5413235) B5413235
theorem B6415361 : Blo 1500070 6415361 := bstep (se 2 (by rfl) ⟨2405760, by rfl⟩ : syracuseStep 6415361 = 4811521) B4811521
theorem B5063687 : Blo 1500070 5063687 := bstep (se 1 (by rfl) ⟨3797765, by rfl⟩ : syracuseStep 5063687 = 7595531) B7595531
theorem B5702663 : Blo 1500070 5702663 := bstep (se 1 (by rfl) ⟨4276997, by rfl⟩ : syracuseStep 5702663 = 8553995) B8553995
theorem B1500199 : Blo 1500070 1500199 := bstep (se 1 (by rfl) ⟨1125149, by rfl⟩ : syracuseStep 1500199 = 2250299) B2250299
theorem B1500239 : Blo 1500070 1500239 := bstep (se 1 (by rfl) ⟨1125179, by rfl⟩ : syracuseStep 1500239 = 2250359) B2250359
theorem B2532431 : Blo 1500070 2532431 := bstep (se 1 (by rfl) ⟨1899323, by rfl⟩ : syracuseStep 2532431 = 3798647) B3798647
theorem B1500255 : Blo 1500070 1500255 := bstep (se 1 (by rfl) ⟨1125191, by rfl⟩ : syracuseStep 1500255 = 2250383) B2250383
theorem B5063795 : Blo 1500070 5063795 := bstep (se 1 (by rfl) ⟨3797846, by rfl⟩ : syracuseStep 5063795 = 7595693) B7595693
theorem B5407859 : Blo 1500070 5407859 := bstep (se 1 (by rfl) ⟨4055894, by rfl⟩ : syracuseStep 5407859 = 8111789) B8111789
theorem B1500283 : Blo 1500070 1500283 := bstep (se 1 (by rfl) ⟨1125212, by rfl⟩ : syracuseStep 1500283 = 2250425) B2250425
theorem B4809881 : Blo 1500070 4809881 := bstep (se 2 (by rfl) ⟨1803705, by rfl⟩ : syracuseStep 4809881 = 3607411) B3607411
theorem B1500335 : Blo 1500070 1500335 := bstep (se 1 (by rfl) ⟨1125251, by rfl⟩ : syracuseStep 1500335 = 2250503) B2250503
theorem B1500359 : Blo 1500070 1500359 := bstep (se 1 (by rfl) ⟨1125269, by rfl⟩ : syracuseStep 1500359 = 2250539) B2250539
theorem B1500379 : Blo 1500070 1500379 := bstep (se 1 (by rfl) ⟨1125284, by rfl⟩ : syracuseStep 1500379 = 2250569) B2250569
theorem B1500455 : Blo 1500070 1500455 := bstep (se 1 (by rfl) ⟨1125341, by rfl⟩ : syracuseStep 1500455 = 2250683) B2250683
theorem B1500495 : Blo 1500070 1500495 := bstep (se 1 (by rfl) ⟨1125371, by rfl⟩ : syracuseStep 1500495 = 2250743) B2250743
theorem B1500511 : Blo 1500070 1500511 := bstep (se 1 (by rfl) ⟨1125383, by rfl⟩ : syracuseStep 1500511 = 2250767) B2250767
theorem B1500539 : Blo 1500070 1500539 := bstep (se 1 (by rfl) ⟨1125404, by rfl⟩ : syracuseStep 1500539 = 2250809) B2250809
theorem B5064065 : Blo 1500070 5064065 := bstep (se 2 (by rfl) ⟨1899024, by rfl⟩ : syracuseStep 5064065 = 3798049) B3798049
theorem B3605903 : Blo 1500070 3605903 := bstep (se 1 (by rfl) ⟨2704427, by rfl⟩ : syracuseStep 3605903 = 5408855) B5408855
theorem B1500591 : Blo 1500070 1500591 := bstep (se 1 (by rfl) ⟨1125443, by rfl⟩ : syracuseStep 1500591 = 2250887) B2250887
theorem B1689007 : Blo 1500070 1689007 := bstep (se 1 (by rfl) ⟨1266755, by rfl⟩ : syracuseStep 1689007 = 2533511) B2533511
theorem B1500615 : Blo 1500070 1500615 := bstep (se 1 (by rfl) ⟨1125461, by rfl⟩ : syracuseStep 1500615 = 2250923) B2250923
theorem B1500635 : Blo 1500070 1500635 := bstep (se 1 (by rfl) ⟨1125476, by rfl⟩ : syracuseStep 1500635 = 2250953) B2250953
theorem B5703149 : Blo 1500070 5703149 := bstep (se 3 (by rfl) ⟨1069340, by rfl⟩ : syracuseStep 5703149 = 2138681) B2138681
theorem B1500711 : Blo 1500070 1500711 := bstep (se 1 (by rfl) ⟨1125533, by rfl⟩ : syracuseStep 1500711 = 2251067) B2251067
theorem B26347051 : Blo 1500070 26347051 := bstep (se 1 (by rfl) ⟨19760288, by rfl⟩ : syracuseStep 26347051 = 39520577) B39520577
theorem B1500751 : Blo 1500070 1500751 := bstep (se 1 (by rfl) ⟨1125563, by rfl⟩ : syracuseStep 1500751 = 2251127) B2251127
theorem B1500767 : Blo 1500070 1500767 := bstep (se 1 (by rfl) ⟨1125575, by rfl⟩ : syracuseStep 1500767 = 2251151) B2251151
theorem B3376763 : Blo 1500070 3376763 := bstep (se 1 (by rfl) ⟨2532572, by rfl⟩ : syracuseStep 3376763 = 5065145) B5065145
theorem B1500795 : Blo 1500070 1500795 := bstep (se 1 (by rfl) ⟨1125596, by rfl⟩ : syracuseStep 1500795 = 2251193) B2251193
theorem B8545931 : Blo 1500070 8545931 := bstep (se 1 (by rfl) ⟨6409448, by rfl⟩ : syracuseStep 8545931 = 12818897) B12818897
theorem B1500847 : Blo 1500070 1500847 := bstep (se 1 (by rfl) ⟨1125635, by rfl⟩ : syracuseStep 1500847 = 2251271) B2251271
theorem B1500871 : Blo 1500070 1500871 := bstep (se 1 (by rfl) ⟨1125653, by rfl⟩ : syracuseStep 1500871 = 2251307) B2251307
theorem B1500891 : Blo 1500070 1500891 := bstep (se 1 (by rfl) ⟨1125668, by rfl⟩ : syracuseStep 1500891 = 2251337) B2251337
theorem B7210745 : Blo 1500070 7210745 := bstep (se 2 (by rfl) ⟨2704029, by rfl⟩ : syracuseStep 7210745 = 5408059) B5408059
theorem B3376889 : Blo 1500070 3376889 := bstep (se 2 (by rfl) ⟨1266333, by rfl⟩ : syracuseStep 3376889 = 2532667) B2532667
theorem B1500967 : Blo 1500070 1500967 := bstep (se 1 (by rfl) ⟨1125725, by rfl⟩ : syracuseStep 1500967 = 2251451) B2251451
theorem B1501007 : Blo 1500070 1501007 := bstep (se 1 (by rfl) ⟨1125755, by rfl⟩ : syracuseStep 1501007 = 2251511) B2251511
theorem B6408031 : Blo 1500070 6408031 := bstep (se 1 (by rfl) ⟨4806023, by rfl⟩ : syracuseStep 6408031 = 9612047) B9612047
theorem B1501023 : Blo 1500070 1501023 := bstep (se 1 (by rfl) ⟨1125767, by rfl⟩ : syracuseStep 1501023 = 2251535) B2251535
theorem B1689439 : Blo 1500070 1689439 := bstep (se 1 (by rfl) ⟨1267079, by rfl⟩ : syracuseStep 1689439 = 2534159) B2534159
theorem B1501051 : Blo 1500070 1501051 := bstep (se 1 (by rfl) ⟨1125788, by rfl⟩ : syracuseStep 1501051 = 2251577) B2251577
theorem B1501103 : Blo 1500070 1501103 := bstep (se 1 (by rfl) ⟨1125827, by rfl⟩ : syracuseStep 1501103 = 2251655) B2251655
theorem B2533295 : Blo 1500070 2533295 := bstep (se 1 (by rfl) ⟨1899971, by rfl⟩ : syracuseStep 2533295 = 3799943) B3799943
theorem B4057019 : Blo 1500070 4057019 := bstep (se 1 (by rfl) ⟨3042764, by rfl⟩ : syracuseStep 4057019 = 6085529) B6085529
theorem B1501127 : Blo 1500070 1501127 := bstep (se 1 (by rfl) ⟨1125845, by rfl⟩ : syracuseStep 1501127 = 2251691) B2251691
theorem B1501147 : Blo 1500070 1501147 := bstep (se 1 (by rfl) ⟨1125860, by rfl⟩ : syracuseStep 1501147 = 2251721) B2251721
theorem B3377159 : Blo 1500070 3377159 := bstep (se 1 (by rfl) ⟨2532869, by rfl⟩ : syracuseStep 3377159 = 5065739) B5065739
theorem B4114451 : Blo 1500070 4114451 := bstep (se 1 (by rfl) ⟨3085838, by rfl⟩ : syracuseStep 4114451 = 6171677) B6171677
theorem B1501223 : Blo 1500070 1501223 := bstep (se 1 (by rfl) ⟨1125917, by rfl⟩ : syracuseStep 1501223 = 2251835) B2251835
theorem B3377231 : Blo 1500070 3377231 := bstep (se 1 (by rfl) ⟨2532923, by rfl⟩ : syracuseStep 3377231 = 5065847) B5065847
theorem B1501263 : Blo 1500070 1501263 := bstep (se 1 (by rfl) ⟨1125947, by rfl⟩ : syracuseStep 1501263 = 2251895) B2251895
theorem B1501279 : Blo 1500070 1501279 := bstep (se 1 (by rfl) ⟨1125959, by rfl⟩ : syracuseStep 1501279 = 2251919) B2251919
theorem B1501307 : Blo 1500070 1501307 := bstep (se 1 (by rfl) ⟨1125980, by rfl⟩ : syracuseStep 1501307 = 2251961) B2251961
theorem B5064875 : Blo 1500070 5064875 := bstep (se 1 (by rfl) ⟨3798656, by rfl⟩ : syracuseStep 5064875 = 7597313) B7597313
theorem B1501359 : Blo 1500070 1501359 := bstep (se 1 (by rfl) ⟨1126019, by rfl⟩ : syracuseStep 1501359 = 2252039) B2252039
theorem B1501383 : Blo 1500070 1501383 := bstep (se 1 (by rfl) ⟨1126037, by rfl⟩ : syracuseStep 1501383 = 2252075) B2252075
theorem B1689799 : Blo 1500070 1689799 := bstep (se 1 (by rfl) ⟨1267349, by rfl⟩ : syracuseStep 1689799 = 2534699) B2534699
theorem B1501403 : Blo 1500070 1501403 := bstep (se 1 (by rfl) ⟨1126052, by rfl⟩ : syracuseStep 1501403 = 2252105) B2252105
theorem B1501479 : Blo 1500070 1501479 := bstep (se 1 (by rfl) ⟨1126109, by rfl⟩ : syracuseStep 1501479 = 2252219) B2252219
theorem B1501519 : Blo 1500070 1501519 := bstep (se 1 (by rfl) ⟨1126139, by rfl⟩ : syracuseStep 1501519 = 2252279) B2252279
theorem B2533727 : Blo 1500070 2533727 := bstep (se 1 (by rfl) ⟨1900295, by rfl⟩ : syracuseStep 2533727 = 3800591) B3800591
theorem B1501535 : Blo 1500070 1501535 := bstep (se 1 (by rfl) ⟨1126151, by rfl⟩ : syracuseStep 1501535 = 2252303) B2252303
theorem B1853791 : Blo 1500070 1853791 := bstep (se 1 (by rfl) ⟨1390343, by rfl⟩ : syracuseStep 1853791 = 2780687) B2780687
theorem B1501563 : Blo 1500070 1501563 := bstep (se 1 (by rfl) ⟨1126172, by rfl⟩ : syracuseStep 1501563 = 2252345) B2252345
theorem B1501615 : Blo 1500070 1501615 := bstep (se 1 (by rfl) ⟨1126211, by rfl⟩ : syracuseStep 1501615 = 2252423) B2252423
theorem B1501639 : Blo 1500070 1501639 := bstep (se 1 (by rfl) ⟨1126229, by rfl⟩ : syracuseStep 1501639 = 2252459) B2252459
theorem B3377627 : Blo 1500070 3377627 := bstep (se 1 (by rfl) ⟨2533220, by rfl⟩ : syracuseStep 3377627 = 5066441) B5066441
theorem B1501659 : Blo 1500070 1501659 := bstep (se 1 (by rfl) ⟨1126244, by rfl⟩ : syracuseStep 1501659 = 2252489) B2252489
theorem B3041831 : Blo 1500070 3041831 := bstep (se 1 (by rfl) ⟨2281373, by rfl⟩ : syracuseStep 3041831 = 4562747) B4562747
theorem B4393511 : Blo 1500070 4393511 := bstep (se 1 (by rfl) ⟨3295133, by rfl⟩ : syracuseStep 4393511 = 6590267) B6590267
theorem B1501735 : Blo 1500070 1501735 := bstep (se 1 (by rfl) ⟨1126301, by rfl⟩ : syracuseStep 1501735 = 2252603) B2252603
theorem B1501775 : Blo 1500070 1501775 := bstep (se 1 (by rfl) ⟨1126331, by rfl⟩ : syracuseStep 1501775 = 2252663) B2252663
theorem B1501791 : Blo 1500070 1501791 := bstep (se 1 (by rfl) ⟨1126343, by rfl⟩ : syracuseStep 1501791 = 2252687) B2252687
theorem B1501819 : Blo 1500070 1501819 := bstep (se 1 (by rfl) ⟨1126364, by rfl⟩ : syracuseStep 1501819 = 2252729) B2252729
theorem B54774407 : Blo 1500070 54774407 := bstep (se 1 (by rfl) ⟨41080805, by rfl⟩ : syracuseStep 54774407 = 82161611) B82161611
theorem B1501871 : Blo 1500070 1501871 := bstep (se 1 (by rfl) ⟨1126403, by rfl⟩ : syracuseStep 1501871 = 2252807) B2252807
theorem B5065415 : Blo 1500070 5065415 := bstep (se 1 (by rfl) ⟨3799061, by rfl⟩ : syracuseStep 5065415 = 7598123) B7598123
theorem B1501895 : Blo 1500070 1501895 := bstep (se 1 (by rfl) ⟨1126421, by rfl⟩ : syracuseStep 1501895 = 2252843) B2252843
theorem B1501915 : Blo 1500070 1501915 := bstep (se 1 (by rfl) ⟨1126436, by rfl⟩ : syracuseStep 1501915 = 2252873) B2252873
theorem B6408989 : Blo 1500070 6408989 := bstep (se 3 (by rfl) ⟨1201685, by rfl⟩ : syracuseStep 6408989 = 2403371) B2403371
theorem B1501991 : Blo 1500070 1501991 := bstep (se 1 (by rfl) ⟨1126493, by rfl⟩ : syracuseStep 1501991 = 2252987) B2252987
theorem B1502031 : Blo 1500070 1502031 := bstep (se 1 (by rfl) ⟨1126523, by rfl⟩ : syracuseStep 1502031 = 2253047) B2253047
theorem B1502047 : Blo 1500070 1502047 := bstep (se 1 (by rfl) ⟨1126535, by rfl⟩ : syracuseStep 1502047 = 2253071) B2253071
theorem B2567017 : Blo 1500070 2567017 := bstep (se 2 (by rfl) ⟨962631, by rfl⟩ : syracuseStep 2567017 = 1925263) B1925263
theorem B2534287 : Blo 1500070 2534287 := bstep (se 1 (by rfl) ⟨1900715, by rfl⟩ : syracuseStep 2534287 = 3801431) B3801431
theorem B3378095 : Blo 1500070 3378095 := bstep (se 1 (by rfl) ⟨2533571, by rfl⟩ : syracuseStep 3378095 = 5067143) B5067143
theorem B5696513 : Blo 1500070 5696513 := bstep (se 2 (by rfl) ⟨2136192, by rfl⟩ : syracuseStep 5696513 = 4272385) B4272385
theorem B4811777 : Blo 1500070 4811777 := bstep (se 2 (by rfl) ⟨1804416, by rfl⟩ : syracuseStep 4811777 = 3608833) B3608833
theorem B5696527 : Blo 1500070 5696527 := bstep (se 1 (by rfl) ⟨4272395, by rfl⟩ : syracuseStep 5696527 = 8544791) B8544791
theorem B9620531 : Blo 1500070 9620531 := bstep (se 1 (by rfl) ⟨7215398, by rfl⟩ : syracuseStep 9620531 = 14430797) B14430797
theorem B3378347 : Blo 1500070 3378347 := bstep (se 1 (by rfl) ⟨2533760, by rfl⟩ : syracuseStep 3378347 = 5067521) B5067521
theorem B3608027 : Blo 1500070 3608027 := bstep (se 1 (by rfl) ⟨2706020, by rfl⟩ : syracuseStep 3608027 = 5412041) B5412041
theorem B11398643 : Blo 1500070 11398643 := bstep (se 1 (by rfl) ⟨8548982, by rfl⟩ : syracuseStep 11398643 = 17097965) B17097965
theorem B5066279 : Blo 1500070 5066279 := bstep (se 1 (by rfl) ⟨3799709, by rfl⟩ : syracuseStep 5066279 = 7599419) B7599419
theorem B5066387 : Blo 1500070 5066387 := bstep (se 1 (by rfl) ⟨3799790, by rfl⟩ : syracuseStep 5066387 = 7599581) B7599581
theorem B3378887 : Blo 1500070 3378887 := bstep (se 1 (by rfl) ⟨2534165, by rfl⟩ : syracuseStep 3378887 = 5068331) B5068331
theorem B25644761 : Blo 1500070 25644761 := bstep (se 2 (by rfl) ⟨9616785, by rfl⟩ : syracuseStep 25644761 = 19233571) B19233571
theorem B8548163 : Blo 1500070 8548163 := bstep (se 1 (by rfl) ⟨6411122, by rfl⟩ : syracuseStep 8548163 = 12822245) B12822245
theorem B5066603 : Blo 1500070 5066603 := bstep (se 1 (by rfl) ⟨3799952, by rfl⟩ : syracuseStep 5066603 = 7599905) B7599905
theorem B5066657 : Blo 1500070 5066657 := bstep (se 2 (by rfl) ⟨1899996, by rfl⟩ : syracuseStep 5066657 = 3799993) B3799993
theorem B4943791 : Blo 1500070 4943791 := bstep (se 1 (by rfl) ⟨3707843, by rfl⟩ : syracuseStep 4943791 = 7415687) B7415687
theorem B10825805 : Blo 1500070 10825805 := bstep (se 3 (by rfl) ⟨2029838, by rfl⟩ : syracuseStep 10825805 = 4059677) B4059677
theorem B14061649 : Blo 1500070 14061649 := bstep (se 2 (by rfl) ⟨5273118, by rfl⟩ : syracuseStep 14061649 = 10546237) B10546237
theorem B17100881 : Blo 1500070 17100881 := bstep (se 2 (by rfl) ⟨6412830, by rfl⟩ : syracuseStep 17100881 = 12825661) B12825661
theorem B10973341 : Blo 1500070 10973341 := bstep (se 3 (by rfl) ⟨2057501, by rfl⟩ : syracuseStep 10973341 = 4115003) B4115003
theorem B3797239 : Blo 1500070 3797239 := bstep (se 1 (by rfl) ⟨2847929, by rfl⟩ : syracuseStep 3797239 = 5695859) B5695859
theorem B5697803 : Blo 1500070 5697803 := bstep (se 1 (by rfl) ⟨4273352, by rfl⟩ : syracuseStep 5697803 = 8546705) B8546705
theorem B4944215 : Blo 1500070 4944215 := bstep (se 1 (by rfl) ⟨3708161, by rfl⟩ : syracuseStep 4944215 = 7416323) B7416323
theorem B2888111 : Blo 1500070 2888111 := bstep (se 1 (by rfl) ⟨2166083, by rfl⟩ : syracuseStep 2888111 = 4332167) B4332167
theorem B5067251 : Blo 1500070 5067251 := bstep (se 1 (by rfl) ⟨3800438, by rfl⟩ : syracuseStep 5067251 = 7600877) B7600877
theorem B3797513 : Blo 1500070 3797513 := bstep (se 2 (by rfl) ⟨1424067, by rfl⟩ : syracuseStep 3797513 = 2848135) B2848135
theorem B3797543 : Blo 1500070 3797543 := bstep (se 1 (by rfl) ⟨2848157, by rfl⟩ : syracuseStep 3797543 = 5696315) B5696315
theorem B4272851 : Blo 1500070 4272851 := bstep (se 1 (by rfl) ⟨3204638, by rfl⟩ : syracuseStep 4272851 = 6409277) B6409277
theorem B5698259 : Blo 1500070 5698259 := bstep (se 1 (by rfl) ⟨4273694, by rfl⟩ : syracuseStep 5698259 = 8547389) B8547389
theorem B25662257 : Blo 1500070 25662257 := bstep (se 2 (by rfl) ⟨9623346, by rfl⟩ : syracuseStep 25662257 = 19246693) B19246693
theorem B3797867 : Blo 1500070 3797867 := bstep (se 1 (by rfl) ⟨2848400, by rfl⟩ : syracuseStep 3797867 = 5696801) B5696801
theorem B5067791 : Blo 1500070 5067791 := bstep (se 1 (by rfl) ⟨3800843, by rfl⟩ : syracuseStep 5067791 = 7601687) B7601687
theorem B32887901 : Blo 1500070 32887901 := bstep (se 3 (by rfl) ⟨6166481, by rfl⟩ : syracuseStep 32887901 = 12332963) B12332963
theorem B2028667 : Blo 1500070 2028667 := bstep (se 1 (by rfl) ⟨1521500, by rfl⟩ : syracuseStep 2028667 = 3043001) B3043001
theorem B7599257 : Blo 1500070 7599257 := bstep (se 2 (by rfl) ⟨2849721, by rfl⟩ : syracuseStep 7599257 = 5699443) B5699443
theorem B9614531 : Blo 1500070 9614531 := bstep (se 1 (by rfl) ⟨7210898, by rfl⟩ : syracuseStep 9614531 = 14421797) B14421797
theorem B2405575 : Blo 1500070 2405575 := bstep (se 1 (by rfl) ⟨1804181, by rfl⟩ : syracuseStep 2405575 = 3608363) B3608363
theorem B7214359 : Blo 1500070 7214359 := bstep (se 1 (by rfl) ⟨5410769, by rfl⟩ : syracuseStep 7214359 = 10821539) B10821539
theorem B2250167 : Blo 1500070 2250167 := bstep (se 1 (by rfl) ⟨1687625, by rfl⟩ : syracuseStep 2250167 = 3375251) B3375251
theorem B7706057 : Blo 1500070 7706057 := bstep (se 2 (by rfl) ⟨2889771, by rfl⟩ : syracuseStep 7706057 = 5779543) B5779543
theorem B2250203 : Blo 1500070 2250203 := bstep (se 1 (by rfl) ⟨1687652, by rfl⟩ : syracuseStep 2250203 = 3375305) B3375305
theorem B3798515 : Blo 1500070 3798515 := bstep (se 1 (by rfl) ⟨2848886, by rfl⟩ : syracuseStep 3798515 = 5697773) B5697773
theorem B5068385 : Blo 1500070 5068385 := bstep (se 2 (by rfl) ⟨1900644, by rfl⟩ : syracuseStep 5068385 = 3801289) B3801289
theorem B5699261 : Blo 1500070 5699261 := bstep (se 3 (by rfl) ⟨1068611, by rfl⟩ : syracuseStep 5699261 = 2137223) B2137223
theorem B11392811 : Blo 1500070 11392811 := bstep (se 1 (by rfl) ⟨8544608, by rfl⟩ : syracuseStep 11392811 = 17089217) B17089217
theorem B6084395 : Blo 1500070 6084395 := bstep (se 1 (by rfl) ⟨4563296, by rfl⟩ : syracuseStep 6084395 = 9126593) B9126593
theorem B8550305 : Blo 1500070 8550305 := bstep (se 2 (by rfl) ⟨3206364, by rfl⟩ : syracuseStep 8550305 = 6412729) B6412729
theorem B2250671 : Blo 1500070 2250671 := bstep (se 1 (by rfl) ⟨1688003, by rfl⟩ : syracuseStep 2250671 = 3376007) B3376007
theorem B3798971 : Blo 1500070 3798971 := bstep (se 1 (by rfl) ⟨2849228, by rfl⟩ : syracuseStep 3798971 = 5698457) B5698457
theorem B2136073 : Blo 1500070 2136073 := bstep (se 2 (by rfl) ⟨801027, by rfl⟩ : syracuseStep 2136073 = 1602055) B1602055
theorem B2250761 : Blo 1500070 2250761 := bstep (se 2 (by rfl) ⟨844035, by rfl⟩ : syracuseStep 2250761 = 1688071) B1688071
theorem B2250791 : Blo 1500070 2250791 := bstep (se 1 (by rfl) ⟨1688093, by rfl⟩ : syracuseStep 2250791 = 3376187) B3376187
theorem B2250875 : Blo 1500070 2250875 := bstep (se 1 (by rfl) ⟨1688156, by rfl⟩ : syracuseStep 2250875 = 3376313) B3376313
theorem B4274333 : Blo 1500070 4274333 := bstep (se 3 (by rfl) ⟨801437, by rfl⟩ : syracuseStep 4274333 = 1602875) B1602875
theorem B5134583 : Blo 1500070 5134583 := bstep (se 1 (by rfl) ⟨3850937, by rfl⟩ : syracuseStep 5134583 = 7701875) B7701875
theorem B2251001 : Blo 1500070 2251001 := bstep (se 2 (by rfl) ⟨844125, by rfl⟩ : syracuseStep 2251001 = 1688251) B1688251
theorem B11401559 : Blo 1500070 11401559 := bstep (se 1 (by rfl) ⟨8551169, by rfl⟩ : syracuseStep 11401559 = 17102339) B17102339
theorem B2251103 : Blo 1500070 2251103 := bstep (se 1 (by rfl) ⟨1688327, by rfl⟩ : syracuseStep 2251103 = 3376655) B3376655
theorem B2251115 : Blo 1500070 2251115 := bstep (se 1 (by rfl) ⟨1688336, by rfl⟩ : syracuseStep 2251115 = 3376673) B3376673
theorem B32438663 : Blo 1500070 32438663 := bstep (se 1 (by rfl) ⟨24328997, by rfl⟩ : syracuseStep 32438663 = 48657995) B48657995
theorem B17332717 : Blo 1500070 17332717 := bstep (se 3 (by rfl) ⟨3249884, by rfl⟩ : syracuseStep 17332717 = 6499769) B6499769
theorem B2251343 : Blo 1500070 2251343 := bstep (se 1 (by rfl) ⟨1688507, by rfl⟩ : syracuseStep 2251343 = 3377015) B3377015
theorem B3799649 : Blo 1500070 3799649 := bstep (se 2 (by rfl) ⟨1424868, by rfl⟩ : syracuseStep 3799649 = 2849737) B2849737
theorem B2251463 : Blo 1500070 2251463 := bstep (se 1 (by rfl) ⟨1688597, by rfl⟩ : syracuseStep 2251463 = 3377195) B3377195
theorem B2251625 : Blo 1500070 2251625 := bstep (se 2 (by rfl) ⟨844359, by rfl⟩ : syracuseStep 2251625 = 1688719) B1688719
theorem B4275119 : Blo 1500070 4275119 := bstep (se 1 (by rfl) ⟨3206339, by rfl⟩ : syracuseStep 4275119 = 6412679) B6412679
theorem B2251703 : Blo 1500070 2251703 := bstep (se 1 (by rfl) ⟨1688777, by rfl⟩ : syracuseStep 2251703 = 3377555) B3377555
theorem B2251739 : Blo 1500070 2251739 := bstep (se 1 (by rfl) ⟨1688804, by rfl⟩ : syracuseStep 2251739 = 3377609) B3377609
theorem B2005979 : Blo 1500070 2005979 := bstep (se 1 (by rfl) ⟨1504484, by rfl⟩ : syracuseStep 2005979 = 3008969) B3008969
theorem B5700689 : Blo 1500070 5700689 := bstep (se 2 (by rfl) ⟨2137758, by rfl⟩ : syracuseStep 5700689 = 4275517) B4275517
theorem B24353909 : Blo 1500070 24353909 := bstep (se 5 (by rfl) ⟨1141589, by rfl⟩ : syracuseStep 24353909 = 2283179) B2283179
theorem B2850041 : Blo 1500070 2850041 := bstep (se 2 (by rfl) ⟨1068765, by rfl⟩ : syracuseStep 2850041 = 2137531) B2137531
theorem B13884797 : Blo 1500070 13884797 := bstep (se 3 (by rfl) ⟨2603399, by rfl⟩ : syracuseStep 13884797 = 5206799) B5206799
theorem B2137519 : Blo 1500070 2137519 := bstep (se 1 (by rfl) ⟨1603139, by rfl⟩ : syracuseStep 2137519 = 3206279) B3206279
theorem B2850223 : Blo 1500070 2850223 := bstep (se 1 (by rfl) ⟨2137667, by rfl⟩ : syracuseStep 2850223 = 4275335) B4275335
theorem B2252207 : Blo 1500070 2252207 := bstep (se 1 (by rfl) ⟨1689155, by rfl⟩ : syracuseStep 2252207 = 3378311) B3378311
theorem B2252297 : Blo 1500070 2252297 := bstep (se 2 (by rfl) ⟨844611, by rfl⟩ : syracuseStep 2252297 = 1689223) B1689223
theorem B2252327 : Blo 1500070 2252327 := bstep (se 1 (by rfl) ⟨1689245, by rfl⟩ : syracuseStep 2252327 = 3378491) B3378491
theorem B2850383 : Blo 1500070 2850383 := bstep (se 1 (by rfl) ⟨2137787, by rfl⟩ : syracuseStep 2850383 = 4275575) B4275575
theorem B2252411 : Blo 1500070 2252411 := bstep (se 1 (by rfl) ⟨1689308, by rfl⟩ : syracuseStep 2252411 = 3378617) B3378617
theorem B8552081 : Blo 1500070 8552081 := bstep (se 2 (by rfl) ⟨3207030, by rfl⟩ : syracuseStep 8552081 = 6414061) B6414061
theorem B4390615 : Blo 1500070 4390615 := bstep (se 1 (by rfl) ⟨3292961, by rfl⟩ : syracuseStep 4390615 = 6585923) B6585923
theorem B2252537 : Blo 1500070 2252537 := bstep (se 2 (by rfl) ⟨844701, by rfl⟩ : syracuseStep 2252537 = 1689403) B1689403
theorem B7208747 : Blo 1500070 7208747 := bstep (se 1 (by rfl) ⟨5406560, by rfl⟩ : syracuseStep 7208747 = 10813121) B10813121
theorem B2252639 : Blo 1500070 2252639 := bstep (se 1 (by rfl) ⟨1689479, by rfl⟩ : syracuseStep 2252639 = 3378959) B3378959
theorem B2252651 : Blo 1500070 2252651 := bstep (se 1 (by rfl) ⟨1689488, by rfl⟩ : syracuseStep 2252651 = 3378977) B3378977
theorem B24338339 : Blo 1500070 24338339 := bstep (se 1 (by rfl) ⟨18253754, by rfl⟩ : syracuseStep 24338339 = 36507509) B36507509
theorem B7217203 : Blo 1500070 7217203 := bstep (se 1 (by rfl) ⟨5412902, by rfl⟩ : syracuseStep 7217203 = 10825805) B10825805
theorem B5701691 : Blo 1500070 5701691 := bstep (se 1 (by rfl) ⟨4276268, by rfl⟩ : syracuseStep 5701691 = 8552537) B8552537
theorem B14631121 : Blo 1500070 14631121 := bstep (se 2 (by rfl) ⟨5486670, by rfl⟩ : syracuseStep 14631121 = 10973341) B10973341
theorem B16220371 : Blo 1500070 16220371 := bstep (se 1 (by rfl) ⟨12165278, by rfl⟩ : syracuseStep 16220371 = 24330557) B24330557
theorem B140517605 : Blo 1500070 140517605 := bstep (se 4 (by rfl) ⟨13173525, by rfl⟩ : syracuseStep 140517605 = 26347051) B26347051
theorem B8225027 : Blo 1500070 8225027 := bstep (se 1 (by rfl) ⟨6168770, by rfl⟩ : syracuseStep 8225027 = 12337541) B12337541
theorem B2253065 : Blo 1500070 2253065 := bstep (se 2 (by rfl) ⟨844899, by rfl⟩ : syracuseStep 2253065 = 1689799) B1689799
theorem B1925407 : Blo 1500070 1925407 := bstep (se 1 (by rfl) ⟨1444055, by rfl⟩ : syracuseStep 1925407 = 2888111) B2888111
theorem B27394355 : Blo 1500070 27394355 := bstep (se 1 (by rfl) ⟨20545766, by rfl⟩ : syracuseStep 27394355 = 41091533) B41091533
theorem B5062985 : Blo 1500070 5062985 := bstep (se 2 (by rfl) ⟨1898619, by rfl⟩ : syracuseStep 5062985 = 3797239) B3797239
theorem B2531675 : Blo 1500070 2531675 := bstep (se 1 (by rfl) ⟨1898756, by rfl⟩ : syracuseStep 2531675 = 3797513) B3797513
theorem B3375467 : Blo 1500070 3375467 := bstep (se 1 (by rfl) ⟨2531600, by rfl⟩ : syracuseStep 3375467 = 5063201) B5063201
theorem B3801451 : Blo 1500070 3801451 := bstep (se 1 (by rfl) ⟨2851088, by rfl⟩ : syracuseStep 3801451 = 5702177) B5702177
theorem B2531695 : Blo 1500070 2531695 := bstep (se 1 (by rfl) ⟨1898771, by rfl⟩ : syracuseStep 2531695 = 3797543) B3797543
theorem B1900999 : Blo 1500070 1900999 := bstep (se 1 (by rfl) ⟨1425749, by rfl⟩ : syracuseStep 1900999 = 2851499) B2851499
theorem B3375611 : Blo 1500070 3375611 := bstep (se 1 (by rfl) ⟨2531708, by rfl⟩ : syracuseStep 3375611 = 5063417) B5063417
theorem B2531911 : Blo 1500070 2531911 := bstep (se 1 (by rfl) ⟨1898933, by rfl⟩ : syracuseStep 2531911 = 3797867) B3797867
theorem B3375737 : Blo 1500070 3375737 := bstep (se 2 (by rfl) ⟨1265901, by rfl⟩ : syracuseStep 3375737 = 2531803) B2531803
theorem B23110289 : Blo 1500070 23110289 := bstep (se 2 (by rfl) ⟨8666358, by rfl⟩ : syracuseStep 23110289 = 17332717) B17332717
theorem B4276907 : Blo 1500070 4276907 := bstep (se 1 (by rfl) ⟨3207680, by rfl⟩ : syracuseStep 4276907 = 6415361) B6415361
theorem B3375791 : Blo 1500070 3375791 := bstep (se 1 (by rfl) ⟨2531843, by rfl⟩ : syracuseStep 3375791 = 5063687) B5063687
theorem B3801775 : Blo 1500070 3801775 := bstep (se 1 (by rfl) ⟨2851331, by rfl⟩ : syracuseStep 3801775 = 5702663) B5702663
theorem B1688287 : Blo 1500070 1688287 := bstep (se 1 (by rfl) ⟨1266215, by rfl⟩ : syracuseStep 1688287 = 2532431) B2532431
theorem B3375863 : Blo 1500070 3375863 := bstep (se 1 (by rfl) ⟨2531897, by rfl⟩ : syracuseStep 3375863 = 5063795) B5063795
theorem B3605239 : Blo 1500070 3605239 := bstep (se 1 (by rfl) ⟨2703929, by rfl⟩ : syracuseStep 3605239 = 5407859) B5407859
theorem B3376043 : Blo 1500070 3376043 := bstep (se 1 (by rfl) ⟨2532032, by rfl⟩ : syracuseStep 3376043 = 5064065) B5064065
theorem B7603145 : Blo 1500070 7603145 := bstep (se 2 (by rfl) ⟨2851179, by rfl⟩ : syracuseStep 7603145 = 5702359) B5702359
theorem B1500111 : Blo 1500070 1500111 := bstep (se 1 (by rfl) ⟨1125083, by rfl⟩ : syracuseStep 1500111 = 2250167) B2250167
theorem B1500135 : Blo 1500070 1500135 := bstep (se 1 (by rfl) ⟨1125101, by rfl⟩ : syracuseStep 1500135 = 2250203) B2250203
theorem B3802099 : Blo 1500070 3802099 := bstep (se 1 (by rfl) ⟨2851574, by rfl⟩ : syracuseStep 3802099 = 5703149) B5703149
theorem B2532343 : Blo 1500070 2532343 := bstep (se 1 (by rfl) ⟨1899257, by rfl⟩ : syracuseStep 2532343 = 3798515) B3798515
theorem B7210129 : Blo 1500070 7210129 := bstep (se 2 (by rfl) ⟨2703798, by rfl⟩ : syracuseStep 7210129 = 5407597) B5407597
theorem B7595207 : Blo 1500070 7595207 := bstep (se 1 (by rfl) ⟨5696405, by rfl⟩ : syracuseStep 7595207 = 11392811) B11392811
theorem B4056263 : Blo 1500070 4056263 := bstep (se 1 (by rfl) ⟨3042197, by rfl⟩ : syracuseStep 4056263 = 6084395) B6084395
theorem B1500447 : Blo 1500070 1500447 := bstep (se 1 (by rfl) ⟨1125335, by rfl⟩ : syracuseStep 1500447 = 2250671) B2250671
theorem B1688863 : Blo 1500070 1688863 := bstep (se 1 (by rfl) ⟨1266647, by rfl⟩ : syracuseStep 1688863 = 2533295) B2533295
theorem B2532647 : Blo 1500070 2532647 := bstep (se 1 (by rfl) ⟨1899485, by rfl⟩ : syracuseStep 2532647 = 3798971) B3798971
theorem B2704679 : Blo 1500070 2704679 := bstep (se 1 (by rfl) ⟨2028509, by rfl⟩ : syracuseStep 2704679 = 4057019) B4057019
theorem B1500507 : Blo 1500070 1500507 := bstep (se 1 (by rfl) ⟨1125380, by rfl⟩ : syracuseStep 1500507 = 2250761) B2250761
theorem B7595369 : Blo 1500070 7595369 := bstep (se 2 (by rfl) ⟨2848263, by rfl⟩ : syracuseStep 7595369 = 5696527) B5696527
theorem B1500527 : Blo 1500070 1500527 := bstep (se 1 (by rfl) ⟨1125395, by rfl⟩ : syracuseStep 1500527 = 2250791) B2250791
theorem B1500583 : Blo 1500070 1500583 := bstep (se 1 (by rfl) ⟨1125437, by rfl⟩ : syracuseStep 1500583 = 2250875) B2250875
theorem B8111549 : Blo 1500070 8111549 := bstep (se 3 (by rfl) ⟨1520915, by rfl⟩ : syracuseStep 8111549 = 3041831) B3041831
theorem B3376583 : Blo 1500070 3376583 := bstep (se 1 (by rfl) ⟨2532437, by rfl⟩ : syracuseStep 3376583 = 5064875) B5064875
theorem B2704889 : Blo 1500070 2704889 := bstep (se 2 (by rfl) ⟨1014333, by rfl⟩ : syracuseStep 2704889 = 2028667) B2028667
theorem B1500667 : Blo 1500070 1500667 := bstep (se 1 (by rfl) ⟨1125500, by rfl⟩ : syracuseStep 1500667 = 2251001) B2251001
theorem B1500735 : Blo 1500070 1500735 := bstep (se 1 (by rfl) ⟨1125551, by rfl⟩ : syracuseStep 1500735 = 2251103) B2251103
theorem B1689151 : Blo 1500070 1689151 := bstep (se 1 (by rfl) ⟨1266863, by rfl⟩ : syracuseStep 1689151 = 2533727) B2533727
theorem B1500743 : Blo 1500070 1500743 := bstep (se 1 (by rfl) ⟨1125557, by rfl⟩ : syracuseStep 1500743 = 2251115) B2251115
theorem B9619145 : Blo 1500070 9619145 := bstep (se 2 (by rfl) ⟨3607179, by rfl⟩ : syracuseStep 9619145 = 7214359) B7214359
theorem B1500895 : Blo 1500070 1500895 := bstep (se 1 (by rfl) ⟨1125671, by rfl⟩ : syracuseStep 1500895 = 2251343) B2251343
theorem B2533099 : Blo 1500070 2533099 := bstep (se 1 (by rfl) ⟨1899824, by rfl⟩ : syracuseStep 2533099 = 3799649) B3799649
theorem B3376943 : Blo 1500070 3376943 := bstep (se 1 (by rfl) ⟨2532707, by rfl⟩ : syracuseStep 3376943 = 5065415) B5065415
theorem B1500975 : Blo 1500070 1500975 := bstep (se 1 (by rfl) ⟨1125731, by rfl⟩ : syracuseStep 1500975 = 2251463) B2251463
theorem B13690757 : Blo 1500070 13690757 := bstep (se 4 (by rfl) ⟨1283508, by rfl⟩ : syracuseStep 13690757 = 2567017) B2567017
theorem B1501083 : Blo 1500070 1501083 := bstep (se 1 (by rfl) ⟨1125812, by rfl⟩ : syracuseStep 1501083 = 2251625) B2251625
theorem B1501135 : Blo 1500070 1501135 := bstep (se 1 (by rfl) ⟨1125851, by rfl⟩ : syracuseStep 1501135 = 2251703) B2251703
theorem B1501159 : Blo 1500070 1501159 := bstep (se 1 (by rfl) ⟨1125869, by rfl⟩ : syracuseStep 1501159 = 2251739) B2251739
theorem B1501471 : Blo 1500070 1501471 := bstep (se 1 (by rfl) ⟨1126103, by rfl⟩ : syracuseStep 1501471 = 2252207) B2252207
theorem B1501531 : Blo 1500070 1501531 := bstep (se 1 (by rfl) ⟨1126148, by rfl⟩ : syracuseStep 1501531 = 2252297) B2252297
theorem B3377519 : Blo 1500070 3377519 := bstep (se 1 (by rfl) ⟨2533139, by rfl⟩ : syracuseStep 3377519 = 5066279) B5066279
theorem B1501551 : Blo 1500070 1501551 := bstep (se 1 (by rfl) ⟨1126163, by rfl⟩ : syracuseStep 1501551 = 2252327) B2252327
theorem B1501607 : Blo 1500070 1501607 := bstep (se 1 (by rfl) ⟨1126205, by rfl⟩ : syracuseStep 1501607 = 2252411) B2252411
theorem B3377591 : Blo 1500070 3377591 := bstep (se 1 (by rfl) ⟨2533193, by rfl⟩ : syracuseStep 3377591 = 5066387) B5066387
theorem B1501691 : Blo 1500070 1501691 := bstep (se 1 (by rfl) ⟨1126268, by rfl⟩ : syracuseStep 1501691 = 2252537) B2252537
theorem B1501759 : Blo 1500070 1501759 := bstep (se 1 (by rfl) ⟨1126319, by rfl⟩ : syracuseStep 1501759 = 2252639) B2252639
theorem B3377735 : Blo 1500070 3377735 := bstep (se 1 (by rfl) ⟨2533301, by rfl⟩ : syracuseStep 3377735 = 5066603) B5066603
theorem B1501767 : Blo 1500070 1501767 := bstep (se 1 (by rfl) ⟨1126325, by rfl⟩ : syracuseStep 1501767 = 2252651) B2252651
theorem B3377771 : Blo 1500070 3377771 := bstep (se 1 (by rfl) ⟨2533328, by rfl⟩ : syracuseStep 3377771 = 5066657) B5066657
theorem B2534071 : Blo 1500070 2534071 := bstep (se 1 (by rfl) ⟨1900553, by rfl⟩ : syracuseStep 2534071 = 3801107) B3801107
theorem B1501919 : Blo 1500070 1501919 := bstep (se 1 (by rfl) ⟨1126439, by rfl⟩ : syracuseStep 1501919 = 2252879) B2252879
theorem B1501999 : Blo 1500070 1501999 := bstep (se 1 (by rfl) ⟨1126499, by rfl⟩ : syracuseStep 1501999 = 2252999) B2252999
theorem B4811663 : Blo 1500070 4811663 := bstep (se 1 (by rfl) ⟨3608747, by rfl⟩ : syracuseStep 4811663 = 7217495) B7217495
theorem B3296143 : Blo 1500070 3296143 := bstep (se 1 (by rfl) ⟨2472107, by rfl⟩ : syracuseStep 3296143 = 4944215) B4944215
theorem B2534375 : Blo 1500070 2534375 := bstep (se 1 (by rfl) ⟨1900781, by rfl⟩ : syracuseStep 2534375 = 3801563) B3801563
theorem B3206135 : Blo 1500070 3206135 := bstep (se 1 (by rfl) ⟨2404601, by rfl⟩ : syracuseStep 3206135 = 4809203) B4809203
theorem B3378167 : Blo 1500070 3378167 := bstep (se 1 (by rfl) ⟨2533625, by rfl⟩ : syracuseStep 3378167 = 5067251) B5067251
theorem B65825963 : Blo 1500070 65825963 := bstep (se 1 (by rfl) ⟨49369472, by rfl⟩ : syracuseStep 65825963 = 98738945) B98738945
theorem B17108171 : Blo 1500070 17108171 := bstep (se 1 (by rfl) ⟨12831128, by rfl⟩ : syracuseStep 17108171 = 25662257) B25662257
theorem B3378527 : Blo 1500070 3378527 := bstep (se 1 (by rfl) ⟨2533895, by rfl⟩ : syracuseStep 3378527 = 5067791) B5067791
theorem B5066171 : Blo 1500070 5066171 := bstep (se 1 (by rfl) ⟨3799628, by rfl⟩ : syracuseStep 5066171 = 7599257) B7599257
theorem B3206587 : Blo 1500070 3206587 := bstep (se 1 (by rfl) ⟨2404940, by rfl⟩ : syracuseStep 3206587 = 4809881) B4809881
theorem B6409687 : Blo 1500070 6409687 := bstep (se 1 (by rfl) ⟨4807265, by rfl⟩ : syracuseStep 6409687 = 9614531) B9614531
theorem B2403935 : Blo 1500070 2403935 := bstep (se 1 (by rfl) ⟨1802951, by rfl⟩ : syracuseStep 2403935 = 3605903) B3605903
theorem B12168913 : Blo 1500070 12168913 := bstep (se 2 (by rfl) ⟨4563342, by rfl⟩ : syracuseStep 12168913 = 9126685) B9126685
theorem B3378923 : Blo 1500070 3378923 := bstep (se 1 (by rfl) ⟨2534192, by rfl⟩ : syracuseStep 3378923 = 5068385) B5068385
theorem B5697287 : Blo 1500070 5697287 := bstep (se 1 (by rfl) ⟨4272965, by rfl⟩ : syracuseStep 5697287 = 8545931) B8545931
theorem B3379049 : Blo 1500070 3379049 := bstep (se 2 (by rfl) ⟨1267143, by rfl⟩ : syracuseStep 3379049 = 2534287) B2534287
theorem B20549485 : Blo 1500070 20549485 := bstep (se 3 (by rfl) ⟨3853028, by rfl⟩ : syracuseStep 20549485 = 7706057) B7706057
theorem B19247057 : Blo 1500070 19247057 := bstep (se 2 (by rfl) ⟨7217646, by rfl⟩ : syracuseStep 19247057 = 14435293) B14435293
theorem B3207433 : Blo 1500070 3207433 := bstep (se 2 (by rfl) ⟨1202787, by rfl⟩ : syracuseStep 3207433 = 2405575) B2405575
theorem B2929007 : Blo 1500070 2929007 := bstep (se 1 (by rfl) ⟨2196755, by rfl⟩ : syracuseStep 2929007 = 4393511) B4393511
theorem B36516271 : Blo 1500070 36516271 := bstep (se 1 (by rfl) ⟨27387203, by rfl⟩ : syracuseStep 36516271 = 54774407) B54774407
theorem B4272659 : Blo 1500070 4272659 := bstep (se 1 (by rfl) ⟨3204494, by rfl⟩ : syracuseStep 4272659 = 6408989) B6408989
theorem B39547541 : Blo 1500070 39547541 := bstep (se 6 (by rfl) ⟨926895, by rfl⟩ : syracuseStep 39547541 = 1853791) B1853791
theorem B3797675 : Blo 1500070 3797675 := bstep (se 1 (by rfl) ⟨2848256, by rfl⟩ : syracuseStep 3797675 = 5696513) B5696513
theorem B3207851 : Blo 1500070 3207851 := bstep (se 1 (by rfl) ⟨2405888, by rfl⟩ : syracuseStep 3207851 = 4811777) B4811777
theorem B11400101 : Blo 1500070 11400101 := bstep (se 4 (by rfl) ⟨1068759, by rfl⟩ : syracuseStep 11400101 = 2137519) B2137519
theorem B5854153 : Blo 1500070 5854153 := bstep (se 2 (by rfl) ⟨2195307, by rfl⟩ : syracuseStep 5854153 = 4390615) B4390615
theorem B2405351 : Blo 1500070 2405351 := bstep (se 1 (by rfl) ⟨1804013, by rfl⟩ : syracuseStep 2405351 = 3608027) B3608027
theorem B7599095 : Blo 1500070 7599095 := bstep (se 1 (by rfl) ⟨5699321, by rfl⟩ : syracuseStep 7599095 = 11398643) B11398643
theorem B4805831 : Blo 1500070 4805831 := bstep (se 1 (by rfl) ⟨3604373, by rfl⟩ : syracuseStep 4805831 = 7208747) B7208747
theorem B5698775 : Blo 1500070 5698775 := bstep (se 1 (by rfl) ⟨4274081, by rfl⟩ : syracuseStep 5698775 = 8548163) B8548163
theorem B6591721 : Blo 1500070 6591721 := bstep (se 2 (by rfl) ⟨2471895, by rfl⟩ : syracuseStep 6591721 = 4943791) B4943791
theorem B16225559 : Blo 1500070 16225559 := bstep (se 1 (by rfl) ⟨12169169, by rfl⟩ : syracuseStep 16225559 = 24338339) B24338339
theorem B2848097 : Blo 1500070 2848097 := bstep (se 2 (by rfl) ⟨1068036, by rfl⟩ : syracuseStep 2848097 = 2136073) B2136073
theorem B2250107 : Blo 1500070 2250107 := bstep (se 1 (by rfl) ⟨1687580, by rfl⟩ : syracuseStep 2250107 = 3375161) B3375161
theorem B11400587 : Blo 1500070 11400587 := bstep (se 1 (by rfl) ⟨8550440, by rfl⟩ : syracuseStep 11400587 = 17100881) B17100881
theorem B18748865 : Blo 1500070 18748865 := bstep (se 2 (by rfl) ⟨7030824, by rfl⟩ : syracuseStep 18748865 = 14061649) B14061649
theorem B2250233 : Blo 1500070 2250233 := bstep (se 2 (by rfl) ⟨843837, by rfl⟩ : syracuseStep 2250233 = 1687675) B1687675
theorem B3798535 : Blo 1500070 3798535 := bstep (se 1 (by rfl) ⟨2848901, by rfl⟩ : syracuseStep 3798535 = 5697803) B5697803
theorem B87701069 : Blo 1500070 87701069 := bstep (se 3 (by rfl) ⟨16443950, by rfl⟩ : syracuseStep 87701069 = 32887901) B32887901
theorem B2250335 : Blo 1500070 2250335 := bstep (se 1 (by rfl) ⟨1687751, by rfl⟩ : syracuseStep 2250335 = 3375503) B3375503
theorem B2250551 : Blo 1500070 2250551 := bstep (se 1 (by rfl) ⟨1687913, by rfl⟩ : syracuseStep 2250551 = 3375827) B3375827
theorem B3798839 : Blo 1500070 3798839 := bstep (se 1 (by rfl) ⟨2849129, by rfl⟩ : syracuseStep 3798839 = 5698259) B5698259
theorem B702199637 : Blo 1500070 702199637 := bstep (se 9 (by rfl) ⟨2057225, by rfl⟩ : syracuseStep 702199637 = 4114451) B4114451
theorem B2250857 : Blo 1500070 2250857 := bstep (se 2 (by rfl) ⟨844071, by rfl⟩ : syracuseStep 2250857 = 1688143) B1688143
theorem B26368409 : Blo 1500070 26368409 := bstep (se 2 (by rfl) ⟨9888153, by rfl⟩ : syracuseStep 26368409 = 19776307) B19776307
theorem B2251175 : Blo 1500070 2251175 := bstep (se 1 (by rfl) ⟨1688381, by rfl⟩ : syracuseStep 2251175 = 3376763) B3376763
theorem B3799507 : Blo 1500070 3799507 := bstep (se 1 (by rfl) ⟨2849630, by rfl⟩ : syracuseStep 3799507 = 5699261) B5699261
theorem B4807163 : Blo 1500070 4807163 := bstep (se 1 (by rfl) ⟨3605372, by rfl⟩ : syracuseStep 4807163 = 7210745) B7210745
theorem B2251259 : Blo 1500070 2251259 := bstep (se 1 (by rfl) ⟨1688444, by rfl⟩ : syracuseStep 2251259 = 3376889) B3376889
theorem B5700203 : Blo 1500070 5700203 := bstep (se 1 (by rfl) ⟨4275152, by rfl⟩ : syracuseStep 5700203 = 8550305) B8550305
theorem B2251385 : Blo 1500070 2251385 := bstep (se 2 (by rfl) ⟨844269, by rfl⟩ : syracuseStep 2251385 = 1688539) B1688539
theorem B2251439 : Blo 1500070 2251439 := bstep (se 1 (by rfl) ⟨1688579, by rfl⟩ : syracuseStep 2251439 = 3377159) B3377159
theorem B2251487 : Blo 1500070 2251487 := bstep (se 1 (by rfl) ⟨1688615, by rfl⟩ : syracuseStep 2251487 = 3377231) B3377231
theorem B2849555 : Blo 1500070 2849555 := bstep (se 1 (by rfl) ⟨2137166, by rfl⟩ : syracuseStep 2849555 = 4274333) B4274333
theorem B3423055 : Blo 1500070 3423055 := bstep (se 1 (by rfl) ⟨2567291, by rfl⟩ : syracuseStep 3423055 = 5134583) B5134583
theorem B7601039 : Blo 1500070 7601039 := bstep (se 1 (by rfl) ⟨5700779, by rfl⟩ : syracuseStep 7601039 = 11401559) B11401559
theorem B21625775 : Blo 1500070 21625775 := bstep (se 1 (by rfl) ⟨16219331, by rfl⟩ : syracuseStep 21625775 = 32438663) B32438663
theorem B2251751 : Blo 1500070 2251751 := bstep (se 1 (by rfl) ⟨1688813, by rfl⟩ : syracuseStep 2251751 = 3377627) B3377627
theorem B11394269 : Blo 1500070 11394269 := bstep (se 3 (by rfl) ⟨2136425, by rfl⟩ : syracuseStep 11394269 = 4272851) B4272851
theorem B2252009 : Blo 1500070 2252009 := bstep (se 2 (by rfl) ⟨844503, by rfl⟩ : syracuseStep 2252009 = 1689007) B1689007
theorem B3800297 : Blo 1500070 3800297 := bstep (se 2 (by rfl) ⟨1425111, by rfl⟩ : syracuseStep 3800297 = 2850223) B2850223
theorem B2850079 : Blo 1500070 2850079 := bstep (se 1 (by rfl) ⟨2137559, by rfl⟩ : syracuseStep 2850079 = 4275119) B4275119
theorem B2252063 : Blo 1500070 2252063 := bstep (se 1 (by rfl) ⟨1689047, by rfl⟩ : syracuseStep 2252063 = 3378095) B3378095
theorem B6413687 : Blo 1500070 6413687 := bstep (se 1 (by rfl) ⟨4810265, by rfl⟩ : syracuseStep 6413687 = 9620531) B9620531
theorem B3800459 : Blo 1500070 3800459 := bstep (se 1 (by rfl) ⟨2850344, by rfl⟩ : syracuseStep 3800459 = 5700689) B5700689
theorem B16235939 : Blo 1500070 16235939 := bstep (se 1 (by rfl) ⟨12176954, by rfl⟩ : syracuseStep 16235939 = 24353909) B24353909
theorem B2252231 : Blo 1500070 2252231 := bstep (se 1 (by rfl) ⟨1689173, by rfl⟩ : syracuseStep 2252231 = 3378347) B3378347
theorem B1900027 : Blo 1500070 1900027 := bstep (se 1 (by rfl) ⟨1425020, by rfl⟩ : syracuseStep 1900027 = 2850041) B2850041
theorem B9256531 : Blo 1500070 9256531 := bstep (se 1 (by rfl) ⟨6942398, by rfl⟩ : syracuseStep 9256531 = 13884797) B13884797
theorem B1900255 : Blo 1500070 1900255 := bstep (se 1 (by rfl) ⟨1425191, by rfl⟩ : syracuseStep 1900255 = 2850383) B2850383
theorem B5701387 : Blo 1500070 5701387 := bstep (se 1 (by rfl) ⟨4276040, by rfl⟩ : syracuseStep 5701387 = 8552081) B8552081
theorem B8544041 : Blo 1500070 8544041 := bstep (se 2 (by rfl) ⟨3204015, by rfl⟩ : syracuseStep 8544041 = 6408031) B6408031
theorem B2252585 : Blo 1500070 2252585 := bstep (se 2 (by rfl) ⟨844719, by rfl⟩ : syracuseStep 2252585 = 1689439) B1689439
theorem B2252591 : Blo 1500070 2252591 := bstep (se 1 (by rfl) ⟨1689443, by rfl⟩ : syracuseStep 2252591 = 3378887) B3378887
theorem B17096507 : Blo 1500070 17096507 := bstep (se 1 (by rfl) ⟨12822380, by rfl⟩ : syracuseStep 17096507 = 25644761) B25644761
theorem B5349277 : Blo 1500070 5349277 := bstep (se 3 (by rfl) ⟨1002989, by rfl⟩ : syracuseStep 5349277 = 2005979) B2005979
theorem B3801127 : Blo 1500070 3801127 := bstep (se 1 (by rfl) ⟨2850845, by rfl⟩ : syracuseStep 3801127 = 5701691) B5701691
theorem B3375323 : Blo 1500070 3375323 := bstep (se 1 (by rfl) ⟨2531492, by rfl⟩ : syracuseStep 3375323 = 5062985) B5062985
theorem B1687783 : Blo 1500070 1687783 := bstep (se 1 (by rfl) ⟨1265837, by rfl⟩ : syracuseStep 1687783 = 2531675) B2531675
theorem B21627161 : Blo 1500070 21627161 := bstep (se 2 (by rfl) ⟨8110185, by rfl⟩ : syracuseStep 21627161 = 16220371) B16220371
theorem B4276577 : Blo 1500070 4276577 := bstep (se 2 (by rfl) ⟨1603716, by rfl⟩ : syracuseStep 4276577 = 3207433) B3207433
theorem B2531783 : Blo 1500070 2531783 := bstep (se 1 (by rfl) ⟨1898837, by rfl⟩ : syracuseStep 2531783 = 3797675) B3797675
theorem B2851271 : Blo 1500070 2851271 := bstep (se 1 (by rfl) ⟨2138453, by rfl⟩ : syracuseStep 2851271 = 4276907) B4276907
theorem B2138567 : Blo 1500070 2138567 := bstep (se 1 (by rfl) ⟨1603925, by rfl⟩ : syracuseStep 2138567 = 3207851) B3207851
theorem B3375593 : Blo 1500070 3375593 := bstep (se 2 (by rfl) ⟨1265847, by rfl⟩ : syracuseStep 3375593 = 2531695) B2531695
theorem B3375881 : Blo 1500070 3375881 := bstep (se 2 (by rfl) ⟨1265955, by rfl⟩ : syracuseStep 3375881 = 2531911) B2531911
theorem B3203887 : Blo 1500070 3203887 := bstep (se 1 (by rfl) ⟨2402915, by rfl⟩ : syracuseStep 3203887 = 4805831) B4805831
theorem B5063471 : Blo 1500070 5063471 := bstep (se 1 (by rfl) ⟨3797603, by rfl⟩ : syracuseStep 5063471 = 7595207) B7595207
theorem B2704175 : Blo 1500070 2704175 := bstep (se 1 (by rfl) ⟨2028131, by rfl⟩ : syracuseStep 2704175 = 4056263) B4056263
theorem B1688431 : Blo 1500070 1688431 := bstep (se 1 (by rfl) ⟨1266323, by rfl⟩ : syracuseStep 1688431 = 2532647) B2532647
theorem B1803119 : Blo 1500070 1803119 := bstep (se 1 (by rfl) ⟨1352339, by rfl⟩ : syracuseStep 1803119 = 2704679) B2704679
theorem B5063579 : Blo 1500070 5063579 := bstep (se 1 (by rfl) ⟨3797684, by rfl⟩ : syracuseStep 5063579 = 7595369) B7595369
theorem B1500071 : Blo 1500070 1500071 := bstep (se 1 (by rfl) ⟨1125053, by rfl⟩ : syracuseStep 1500071 = 2250107) B2250107
theorem B1500155 : Blo 1500070 1500155 := bstep (se 1 (by rfl) ⟨1125116, by rfl⟩ : syracuseStep 1500155 = 2250233) B2250233
theorem B1803259 : Blo 1500070 1803259 := bstep (se 1 (by rfl) ⟨1352444, by rfl⟩ : syracuseStep 1803259 = 2704889) B2704889
theorem B58467379 : Blo 1500070 58467379 := bstep (se 1 (by rfl) ⟨43850534, by rfl⟩ : syracuseStep 58467379 = 87701069) B87701069
theorem B1500223 : Blo 1500070 1500223 := bstep (se 1 (by rfl) ⟨1125167, by rfl⟩ : syracuseStep 1500223 = 2250335) B2250335
theorem B4564073 : Blo 1500070 4564073 := bstep (se 2 (by rfl) ⟨1711527, by rfl⟩ : syracuseStep 4564073 = 3423055) B3423055
theorem B49996973 : Blo 1500070 49996973 := bstep (se 3 (by rfl) ⟨9374432, by rfl⟩ : syracuseStep 49996973 = 18748865) B18748865
theorem B1500367 : Blo 1500070 1500367 := bstep (se 1 (by rfl) ⟨1125275, by rfl⟩ : syracuseStep 1500367 = 2250551) B2250551
theorem B2532559 : Blo 1500070 2532559 := bstep (se 1 (by rfl) ⟨1899419, by rfl⟩ : syracuseStep 2532559 = 3798839) B3798839
theorem B468133091 : Blo 1500070 468133091 := bstep (se 1 (by rfl) ⟨351099818, by rfl⟩ : syracuseStep 468133091 = 702199637) B702199637
theorem B9127171 : Blo 1500070 9127171 := bstep (se 1 (by rfl) ⟨6845378, by rfl⟩ : syracuseStep 9127171 = 13690757) B13690757
theorem B3376457 : Blo 1500070 3376457 := bstep (se 2 (by rfl) ⟨1266171, by rfl⟩ : syracuseStep 3376457 = 2532343) B2532343
theorem B1500571 : Blo 1500070 1500571 := bstep (se 1 (by rfl) ⟨1125428, by rfl⟩ : syracuseStep 1500571 = 2250857) B2250857
theorem B1500783 : Blo 1500070 1500783 := bstep (se 1 (by rfl) ⟨1125587, by rfl⟩ : syracuseStep 1500783 = 2251175) B2251175
theorem B3204775 : Blo 1500070 3204775 := bstep (se 1 (by rfl) ⟨2403581, by rfl⟩ : syracuseStep 3204775 = 4807163) B4807163
theorem B1500839 : Blo 1500070 1500839 := bstep (se 1 (by rfl) ⟨1125629, by rfl⟩ : syracuseStep 1500839 = 2251259) B2251259
theorem B1500923 : Blo 1500070 1500923 := bstep (se 1 (by rfl) ⟨1125692, by rfl⟩ : syracuseStep 1500923 = 2251385) B2251385
theorem B1500959 : Blo 1500070 1500959 := bstep (se 1 (by rfl) ⟨1125719, by rfl⟩ : syracuseStep 1500959 = 2251439) B2251439
theorem B1500991 : Blo 1500070 1500991 := bstep (se 1 (by rfl) ⟨1125743, by rfl⟩ : syracuseStep 1500991 = 2251487) B2251487
theorem B8546249 : Blo 1500070 8546249 := bstep (se 2 (by rfl) ⟨3204843, by rfl⟩ : syracuseStep 8546249 = 6409687) B6409687
theorem B1501167 : Blo 1500070 1501167 := bstep (se 1 (by rfl) ⟨1125875, by rfl⟩ : syracuseStep 1501167 = 2251751) B2251751
theorem B1689583 : Blo 1500070 1689583 := bstep (se 1 (by rfl) ⟨1267187, by rfl⟩ : syracuseStep 1689583 = 2534375) B2534375
theorem B2533369 : Blo 1500070 2533369 := bstep (se 2 (by rfl) ⟨950013, by rfl⟩ : syracuseStep 2533369 = 1900027) B1900027
theorem B5064713 : Blo 1500070 5064713 := bstep (se 2 (by rfl) ⟨1899267, by rfl⟩ : syracuseStep 5064713 = 3798535) B3798535
theorem B11405447 : Blo 1500070 11405447 := bstep (se 1 (by rfl) ⟨8554085, by rfl⟩ : syracuseStep 11405447 = 17108171) B17108171
theorem B7596179 : Blo 1500070 7596179 := bstep (se 1 (by rfl) ⟨5697134, by rfl⟩ : syracuseStep 7596179 = 11394269) B11394269
theorem B1501339 : Blo 1500070 1501339 := bstep (se 1 (by rfl) ⟨1126004, by rfl⟩ : syracuseStep 1501339 = 2252009) B2252009
theorem B2533531 : Blo 1500070 2533531 := bstep (se 1 (by rfl) ⟨1900148, by rfl⟩ : syracuseStep 2533531 = 3800297) B3800297
theorem B1501375 : Blo 1500070 1501375 := bstep (se 1 (by rfl) ⟨1126031, by rfl⟩ : syracuseStep 1501375 = 2252063) B2252063
theorem B2533639 : Blo 1500070 2533639 := bstep (se 1 (by rfl) ⟨1900229, by rfl⟩ : syracuseStep 2533639 = 3800459) B3800459
theorem B10823959 : Blo 1500070 10823959 := bstep (se 1 (by rfl) ⟨8117969, by rfl⟩ : syracuseStep 10823959 = 16235939) B16235939
theorem B3377447 : Blo 1500070 3377447 := bstep (se 1 (by rfl) ⟨2533085, by rfl⟩ : syracuseStep 3377447 = 5066171) B5066171
theorem B2533673 : Blo 1500070 2533673 := bstep (se 2 (by rfl) ⟨950127, by rfl⟩ : syracuseStep 2533673 = 1900255) B1900255
theorem B1501487 : Blo 1500070 1501487 := bstep (se 1 (by rfl) ⟨1126115, by rfl⟩ : syracuseStep 1501487 = 2252231) B2252231
theorem B3377465 : Blo 1500070 3377465 := bstep (se 2 (by rfl) ⟨1266549, by rfl⟩ : syracuseStep 3377465 = 2533099) B2533099
theorem B5696027 : Blo 1500070 5696027 := bstep (se 1 (by rfl) ⟨4272020, by rfl⟩ : syracuseStep 5696027 = 8544041) B8544041
theorem B1501723 : Blo 1500070 1501723 := bstep (se 1 (by rfl) ⟨1126292, by rfl⟩ : syracuseStep 1501723 = 2252585) B2252585
theorem B1501727 : Blo 1500070 1501727 := bstep (se 1 (by rfl) ⟨1126295, by rfl⟩ : syracuseStep 1501727 = 2252591) B2252591
theorem B11397671 : Blo 1500070 11397671 := bstep (se 1 (by rfl) ⟨8548253, by rfl⟩ : syracuseStep 11397671 = 17096507) B17096507
theorem B12831371 : Blo 1500070 12831371 := bstep (se 1 (by rfl) ⟨9623528, by rfl⟩ : syracuseStep 12831371 = 19247057) B19247057
theorem B93678403 : Blo 1500070 93678403 := bstep (se 1 (by rfl) ⟨70258802, by rfl⟩ : syracuseStep 93678403 = 140517605) B140517605
theorem B5483351 : Blo 1500070 5483351 := bstep (se 1 (by rfl) ⟨4112513, by rfl⟩ : syracuseStep 5483351 = 8225027) B8225027
theorem B1502043 : Blo 1500070 1502043 := bstep (se 1 (by rfl) ⟨1126532, by rfl⟩ : syracuseStep 1502043 = 2253065) B2253065
theorem B18262903 : Blo 1500070 18262903 := bstep (se 1 (by rfl) ⟨13697177, by rfl⟩ : syracuseStep 18262903 = 27394355) B27394355
theorem B1952671 : Blo 1500070 1952671 := bstep (se 1 (by rfl) ⟨1464503, by rfl⟩ : syracuseStep 1952671 = 2929007) B2929007
theorem B19508161 : Blo 1500070 19508161 := bstep (se 2 (by rfl) ⟨7315560, by rfl⟩ : syracuseStep 19508161 = 14631121) B14631121
theorem B2567209 : Blo 1500070 2567209 := bstep (se 2 (by rfl) ⟨962703, by rfl⟩ : syracuseStep 2567209 = 1925407) B1925407
theorem B26365027 : Blo 1500070 26365027 := bstep (se 1 (by rfl) ⟨19773770, by rfl⟩ : syracuseStep 26365027 = 39547541) B39547541
theorem B48688361 : Blo 1500070 48688361 := bstep (se 2 (by rfl) ⟨18258135, by rfl⟩ : syracuseStep 48688361 = 36516271) B36516271
theorem B2534665 : Blo 1500070 2534665 := bstep (se 2 (by rfl) ⟨950499, by rfl⟩ : syracuseStep 2534665 = 1900999) B1900999
theorem B5066009 : Blo 1500070 5066009 := bstep (se 2 (by rfl) ⟨1899753, by rfl⟩ : syracuseStep 5066009 = 3799507) B3799507
theorem B5066063 : Blo 1500070 5066063 := bstep (se 1 (by rfl) ⟨3799547, by rfl⟩ : syracuseStep 5066063 = 7599095) B7599095
theorem B10817039 : Blo 1500070 10817039 := bstep (se 1 (by rfl) ⟨8112779, by rfl⟩ : syracuseStep 10817039 = 16225559) B16225559
theorem B3378761 : Blo 1500070 3378761 := bstep (se 2 (by rfl) ⟨1267035, by rfl⟩ : syracuseStep 3378761 = 2534071) B2534071
theorem B21630797 : Blo 1500070 21630797 := bstep (se 3 (by rfl) ⟨4055774, by rfl⟩ : syracuseStep 21630797 = 8111549) B8111549
theorem B4394857 : Blo 1500070 4394857 := bstep (se 2 (by rfl) ⟨1648071, by rfl⟩ : syracuseStep 4394857 = 3296143) B3296143
theorem B9613505 : Blo 1500070 9613505 := bstep (se 2 (by rfl) ⟨3605064, by rfl⟩ : syracuseStep 9613505 = 7210129) B7210129
theorem B5067359 : Blo 1500070 5067359 := bstep (se 1 (by rfl) ⟨3800519, by rfl⟩ : syracuseStep 5067359 = 7601039) B7601039
theorem B3207775 : Blo 1500070 3207775 := bstep (se 1 (by rfl) ⟨2405831, by rfl⟩ : syracuseStep 3207775 = 4811663) B4811663
theorem B12342041 : Blo 1500070 12342041 := bstep (se 2 (by rfl) ⟨4628265, by rfl⟩ : syracuseStep 12342041 = 9256531) B9256531
theorem B16225217 : Blo 1500070 16225217 := bstep (se 2 (by rfl) ⟨6084456, by rfl⟩ : syracuseStep 16225217 = 12168913) B12168913
theorem B1602623 : Blo 1500070 1602623 := bstep (se 1 (by rfl) ⟨1201967, by rfl⟩ : syracuseStep 1602623 = 2403935) B2403935
theorem B27399313 : Blo 1500070 27399313 := bstep (se 2 (by rfl) ⟨10274742, by rfl⟩ : syracuseStep 27399313 = 20549485) B20549485
theorem B3798191 : Blo 1500070 3798191 := bstep (se 1 (by rfl) ⟨2848643, by rfl⟩ : syracuseStep 3798191 = 5697287) B5697287
theorem B7132369 : Blo 1500070 7132369 := bstep (se 2 (by rfl) ⟨2674638, by rfl⟩ : syracuseStep 7132369 = 5349277) B5349277
theorem B9622937 : Blo 1500070 9622937 := bstep (se 2 (by rfl) ⟨3608601, by rfl⟩ : syracuseStep 9622937 = 7217203) B7217203
theorem B2250311 : Blo 1500070 2250311 := bstep (se 1 (by rfl) ⟨1687733, by rfl⟩ : syracuseStep 2250311 = 3375467) B3375467
theorem B2250407 : Blo 1500070 2250407 := bstep (se 1 (by rfl) ⟨1687805, by rfl⟩ : syracuseStep 2250407 = 3375611) B3375611
theorem B2848439 : Blo 1500070 2848439 := bstep (se 1 (by rfl) ⟨2136329, by rfl⟩ : syracuseStep 2848439 = 4272659) B4272659
theorem B2250491 : Blo 1500070 2250491 := bstep (se 1 (by rfl) ⟨1687868, by rfl⟩ : syracuseStep 2250491 = 3375737) B3375737
theorem B15406859 : Blo 1500070 15406859 := bstep (se 1 (by rfl) ⟨11555144, by rfl⟩ : syracuseStep 15406859 = 23110289) B23110289
theorem B2250527 : Blo 1500070 2250527 := bstep (se 1 (by rfl) ⟨1687895, by rfl⟩ : syracuseStep 2250527 = 3375791) B3375791
theorem B5068601 : Blo 1500070 5068601 := bstep (se 2 (by rfl) ⟨1900725, by rfl⟩ : syracuseStep 5068601 = 3801451) B3801451
theorem B2250575 : Blo 1500070 2250575 := bstep (se 1 (by rfl) ⟨1687931, by rfl⟩ : syracuseStep 2250575 = 3375863) B3375863
theorem B7600067 : Blo 1500070 7600067 := bstep (se 1 (by rfl) ⟨5700050, by rfl⟩ : syracuseStep 7600067 = 11400101) B11400101
theorem B2250695 : Blo 1500070 2250695 := bstep (se 1 (by rfl) ⟨1688021, by rfl⟩ : syracuseStep 2250695 = 3376043) B3376043
theorem B5068763 : Blo 1500070 5068763 := bstep (se 1 (by rfl) ⟨3801572, by rfl⟩ : syracuseStep 5068763 = 7603145) B7603145
theorem B1603567 : Blo 1500070 1603567 := bstep (se 1 (by rfl) ⟨1202675, by rfl⟩ : syracuseStep 1603567 = 2405351) B2405351
theorem B3799183 : Blo 1500070 3799183 := bstep (se 1 (by rfl) ⟨2849387, by rfl⟩ : syracuseStep 3799183 = 5698775) B5698775
theorem B5069033 : Blo 1500070 5069033 := bstep (se 2 (by rfl) ⟨1900887, by rfl⟩ : syracuseStep 5069033 = 3801775) B3801775
theorem B1898731 : Blo 1500070 1898731 := bstep (se 1 (by rfl) ⟨1424048, by rfl⟩ : syracuseStep 1898731 = 2848097) B2848097
theorem B7600391 : Blo 1500070 7600391 := bstep (se 1 (by rfl) ⟨5700293, by rfl⟩ : syracuseStep 7600391 = 11400587) B11400587
theorem B2251049 : Blo 1500070 2251049 := bstep (se 2 (by rfl) ⟨844143, by rfl⟩ : syracuseStep 2251049 = 1688287) B1688287
theorem B2251055 : Blo 1500070 2251055 := bstep (se 1 (by rfl) ⟨1688291, by rfl⟩ : syracuseStep 2251055 = 3376583) B3376583
theorem B4806985 : Blo 1500070 4806985 := bstep (se 2 (by rfl) ⟨1802619, by rfl⟩ : syracuseStep 4806985 = 3605239) B3605239
theorem B6412763 : Blo 1500070 6412763 := bstep (se 1 (by rfl) ⟨4809572, by rfl⟩ : syracuseStep 6412763 = 9619145) B9619145
theorem B2251295 : Blo 1500070 2251295 := bstep (se 1 (by rfl) ⟨1688471, by rfl⟩ : syracuseStep 2251295 = 3376943) B3376943
theorem B7805537 : Blo 1500070 7805537 := bstep (se 2 (by rfl) ⟨2927076, by rfl⟩ : syracuseStep 7805537 = 5854153) B5854153
theorem B5069465 : Blo 1500070 5069465 := bstep (se 2 (by rfl) ⟨1901049, by rfl⟩ : syracuseStep 5069465 = 3802099) B3802099
theorem B2251679 : Blo 1500070 2251679 := bstep (se 1 (by rfl) ⟨1688759, by rfl⟩ : syracuseStep 2251679 = 3377519) B3377519
theorem B17578939 : Blo 1500070 17578939 := bstep (se 1 (by rfl) ⟨13184204, by rfl⟩ : syracuseStep 17578939 = 26368409) B26368409
theorem B2251727 : Blo 1500070 2251727 := bstep (se 1 (by rfl) ⟨1688795, by rfl⟩ : syracuseStep 2251727 = 3377591) B3377591
theorem B8788961 : Blo 1500070 8788961 := bstep (se 2 (by rfl) ⟨3295860, by rfl⟩ : syracuseStep 8788961 = 6591721) B6591721
theorem B2251817 : Blo 1500070 2251817 := bstep (se 2 (by rfl) ⟨844431, by rfl⟩ : syracuseStep 2251817 = 1688863) B1688863
theorem B3800105 : Blo 1500070 3800105 := bstep (se 2 (by rfl) ⟨1425039, by rfl⟩ : syracuseStep 3800105 = 2850079) B2850079
theorem B2251823 : Blo 1500070 2251823 := bstep (se 1 (by rfl) ⟨1688867, by rfl⟩ : syracuseStep 2251823 = 3377735) B3377735
theorem B2251847 : Blo 1500070 2251847 := bstep (se 1 (by rfl) ⟨1688885, by rfl⟩ : syracuseStep 2251847 = 3377771) B3377771
theorem B3800135 : Blo 1500070 3800135 := bstep (se 1 (by rfl) ⟨2850101, by rfl⟩ : syracuseStep 3800135 = 5700203) B5700203
theorem B1899703 : Blo 1500070 1899703 := bstep (se 1 (by rfl) ⟨1424777, by rfl⟩ : syracuseStep 1899703 = 2849555) B2849555
theorem B4275449 : Blo 1500070 4275449 := bstep (se 2 (by rfl) ⟨1603293, by rfl⟩ : syracuseStep 4275449 = 3206587) B3206587
theorem B14417183 : Blo 1500070 14417183 := bstep (se 1 (by rfl) ⟨10812887, by rfl⟩ : syracuseStep 14417183 = 21625775) B21625775
theorem B2137423 : Blo 1500070 2137423 := bstep (se 1 (by rfl) ⟨1603067, by rfl⟩ : syracuseStep 2137423 = 3206135) B3206135
theorem B2252111 : Blo 1500070 2252111 := bstep (se 1 (by rfl) ⟨1689083, by rfl⟩ : syracuseStep 2252111 = 3378167) B3378167
theorem B2252201 : Blo 1500070 2252201 := bstep (se 2 (by rfl) ⟨844575, by rfl⟩ : syracuseStep 2252201 = 1689151) B1689151
theorem B43883975 : Blo 1500070 43883975 := bstep (se 1 (by rfl) ⟨32912981, by rfl⟩ : syracuseStep 43883975 = 65825963) B65825963
theorem B2252351 : Blo 1500070 2252351 := bstep (se 1 (by rfl) ⟨1689263, by rfl⟩ : syracuseStep 2252351 = 3378527) B3378527
theorem B4275791 : Blo 1500070 4275791 := bstep (se 1 (by rfl) ⟨3206843, by rfl⟩ : syracuseStep 4275791 = 6413687) B6413687
theorem B7601849 : Blo 1500070 7601849 := bstep (se 2 (by rfl) ⟨2850693, by rfl⟩ : syracuseStep 7601849 = 5701387) B5701387
theorem B2252615 : Blo 1500070 2252615 := bstep (se 1 (by rfl) ⟨1689461, by rfl⟩ : syracuseStep 2252615 = 3378923) B3378923
theorem B2252699 : Blo 1500070 2252699 := bstep (se 1 (by rfl) ⟨1689524, by rfl⟩ : syracuseStep 2252699 = 3379049) B3379049
theorem B14418107 : Blo 1500070 14418107 := bstep (se 1 (by rfl) ⟨10813580, by rfl⟩ : syracuseStep 14418107 = 21627161) B21627161
theorem B2851051 : Blo 1500070 2851051 := bstep (se 1 (by rfl) ⟨2138288, by rfl⟩ : syracuseStep 2851051 = 4276577) B4276577
theorem B1687855 : Blo 1500070 1687855 := bstep (se 1 (by rfl) ⟨1265891, by rfl⟩ : syracuseStep 1687855 = 2531783) B2531783
theorem B1900847 : Blo 1500070 1900847 := bstep (se 1 (by rfl) ⟨1425635, by rfl⟩ : syracuseStep 1900847 = 2851271) B2851271
theorem B2531641 : Blo 1500070 2531641 := bstep (se 2 (by rfl) ⟨949365, by rfl⟩ : syracuseStep 2531641 = 1898731) B1898731
theorem B133325261 : Blo 1500070 133325261 := bstep (se 3 (by rfl) ⟨24998486, by rfl⟩ : syracuseStep 133325261 = 49996973) B49996973
theorem B3375647 : Blo 1500070 3375647 := bstep (se 1 (by rfl) ⟨2531735, by rfl⟩ : syracuseStep 3375647 = 5063471) B5063471
theorem B1802783 : Blo 1500070 1802783 := bstep (se 1 (by rfl) ⟨1352087, by rfl⟩ : syracuseStep 1802783 = 2704175) B2704175
theorem B3375719 : Blo 1500070 3375719 := bstep (se 1 (by rfl) ⟨2531789, by rfl⟩ : syracuseStep 3375719 = 5063579) B5063579
theorem B146129669 : Blo 1500070 146129669 := bstep (se 4 (by rfl) ⟨13699656, by rfl⟩ : syracuseStep 146129669 = 27399313) B27399313
theorem B2532127 : Blo 1500070 2532127 := bstep (se 1 (by rfl) ⟨1899095, by rfl⟩ : syracuseStep 2532127 = 3798191) B3798191
theorem B4277033 : Blo 1500070 4277033 := bstep (se 2 (by rfl) ⟨1603887, by rfl⟩ : syracuseStep 4277033 = 3207775) B3207775
theorem B6415291 : Blo 1500070 6415291 := bstep (se 1 (by rfl) ⟨4811468, by rfl⟩ : syracuseStep 6415291 = 9622937) B9622937
theorem B1500207 : Blo 1500070 1500207 := bstep (se 1 (by rfl) ⟨1125155, by rfl⟩ : syracuseStep 1500207 = 2250311) B2250311
theorem B124904537 : Blo 1500070 124904537 := bstep (se 2 (by rfl) ⟨46839201, by rfl⟩ : syracuseStep 124904537 = 93678403) B93678403
theorem B1500271 : Blo 1500070 1500271 := bstep (se 1 (by rfl) ⟨1125203, by rfl⟩ : syracuseStep 1500271 = 2250407) B2250407
theorem B1500327 : Blo 1500070 1500327 := bstep (se 1 (by rfl) ⟨1125245, by rfl⟩ : syracuseStep 1500327 = 2250491) B2250491
theorem B117023933 : Blo 1500070 117023933 := bstep (se 3 (by rfl) ⟨21941987, by rfl⟩ : syracuseStep 117023933 = 43883975) B43883975
theorem B1500351 : Blo 1500070 1500351 := bstep (se 1 (by rfl) ⟨1125263, by rfl⟩ : syracuseStep 1500351 = 2250527) B2250527
theorem B5702845 : Blo 1500070 5702845 := bstep (se 3 (by rfl) ⟨1069283, by rfl⟩ : syracuseStep 5702845 = 2138567) B2138567
theorem B1500383 : Blo 1500070 1500383 := bstep (se 1 (by rfl) ⟨1125287, by rfl⟩ : syracuseStep 1500383 = 2250575) B2250575
theorem B23438585 : Blo 1500070 23438585 := bstep (se 2 (by rfl) ⟨8789469, by rfl⟩ : syracuseStep 23438585 = 17578939) B17578939
theorem B26010881 : Blo 1500070 26010881 := bstep (se 2 (by rfl) ⟨9754080, by rfl⟩ : syracuseStep 26010881 = 19508161) B19508161
theorem B1500463 : Blo 1500070 1500463 := bstep (se 1 (by rfl) ⟨1125347, by rfl⟩ : syracuseStep 1500463 = 2250695) B2250695
theorem B3376475 : Blo 1500070 3376475 := bstep (se 1 (by rfl) ⟨2532356, by rfl⟩ : syracuseStep 3376475 = 5064713) B5064713
theorem B48678245 : Blo 1500070 48678245 := bstep (se 4 (by rfl) ⟨4563585, by rfl⟩ : syracuseStep 48678245 = 9127171) B9127171
theorem B77956505 : Blo 1500070 77956505 := bstep (se 2 (by rfl) ⟨29233689, by rfl⟩ : syracuseStep 77956505 = 58467379) B58467379
theorem B7603631 : Blo 1500070 7603631 := bstep (se 1 (by rfl) ⟨5702723, by rfl⟩ : syracuseStep 7603631 = 11405447) B11405447
theorem B5064119 : Blo 1500070 5064119 := bstep (se 1 (by rfl) ⟨3798089, by rfl⟩ : syracuseStep 5064119 = 7596179) B7596179
theorem B35153369 : Blo 1500070 35153369 := bstep (se 2 (by rfl) ⟨13182513, by rfl⟩ : syracuseStep 35153369 = 26365027) B26365027
theorem B1500699 : Blo 1500070 1500699 := bstep (se 1 (by rfl) ⟨1125524, by rfl⟩ : syracuseStep 1500699 = 2251049) B2251049
theorem B1689115 : Blo 1500070 1689115 := bstep (se 1 (by rfl) ⟨1266836, by rfl⟩ : syracuseStep 1689115 = 2533673) B2533673
theorem B1500703 : Blo 1500070 1500703 := bstep (se 1 (by rfl) ⟨1125527, by rfl⟩ : syracuseStep 1500703 = 2251055) B2251055
theorem B2532937 : Blo 1500070 2532937 := bstep (se 2 (by rfl) ⟨949851, by rfl⟩ : syracuseStep 2532937 = 1899703) B1899703
theorem B3376745 : Blo 1500070 3376745 := bstep (se 2 (by rfl) ⟨1266279, by rfl⟩ : syracuseStep 3376745 = 2532559) B2532559
theorem B1500863 : Blo 1500070 1500863 := bstep (se 1 (by rfl) ⟨1125647, by rfl⟩ : syracuseStep 1500863 = 2251295) B2251295
theorem B5203691 : Blo 1500070 5203691 := bstep (se 1 (by rfl) ⟨3902768, by rfl⟩ : syracuseStep 5203691 = 7805537) B7805537
theorem B8554247 : Blo 1500070 8554247 := bstep (se 1 (by rfl) ⟨6415685, by rfl⟩ : syracuseStep 8554247 = 12831371) B12831371
theorem B3655567 : Blo 1500070 3655567 := bstep (se 1 (by rfl) ⟨2741675, by rfl⟩ : syracuseStep 3655567 = 5483351) B5483351
theorem B1501119 : Blo 1500070 1501119 := bstep (se 1 (by rfl) ⟨1125839, by rfl⟩ : syracuseStep 1501119 = 2251679) B2251679
theorem B1501151 : Blo 1500070 1501151 := bstep (se 1 (by rfl) ⟨1125863, by rfl⟩ : syracuseStep 1501151 = 2251727) B2251727
theorem B5859307 : Blo 1500070 5859307 := bstep (se 1 (by rfl) ⟨4394480, by rfl⟩ : syracuseStep 5859307 = 8788961) B8788961
theorem B1501211 : Blo 1500070 1501211 := bstep (se 1 (by rfl) ⟨1125908, by rfl⟩ : syracuseStep 1501211 = 2251817) B2251817
theorem B2533403 : Blo 1500070 2533403 := bstep (se 1 (by rfl) ⟨1900052, by rfl⟩ : syracuseStep 2533403 = 3800105) B3800105
theorem B41084957 : Blo 1500070 41084957 := bstep (se 3 (by rfl) ⟨7703429, by rfl⟩ : syracuseStep 41084957 = 15406859) B15406859
theorem B1501215 : Blo 1500070 1501215 := bstep (se 1 (by rfl) ⟨1125911, by rfl⟩ : syracuseStep 1501215 = 2251823) B2251823
theorem B1501231 : Blo 1500070 1501231 := bstep (se 1 (by rfl) ⟨1125923, by rfl⟩ : syracuseStep 1501231 = 2251847) B2251847
theorem B2533423 : Blo 1500070 2533423 := bstep (se 1 (by rfl) ⟨1900067, by rfl⟩ : syracuseStep 2533423 = 3800135) B3800135
theorem B32458907 : Blo 1500070 32458907 := bstep (se 1 (by rfl) ⟨24344180, by rfl⟩ : syracuseStep 32458907 = 48688361) B48688361
theorem B3377339 : Blo 1500070 3377339 := bstep (se 1 (by rfl) ⟨2533004, by rfl⟩ : syracuseStep 3377339 = 5066009) B5066009
theorem B9611455 : Blo 1500070 9611455 := bstep (se 1 (by rfl) ⟨7208591, by rfl⟩ : syracuseStep 9611455 = 14417183) B14417183
theorem B3377375 : Blo 1500070 3377375 := bstep (se 1 (by rfl) ⟨2533031, by rfl⟩ : syracuseStep 3377375 = 5066063) B5066063
theorem B1501407 : Blo 1500070 1501407 := bstep (se 1 (by rfl) ⟨1126055, by rfl⟩ : syracuseStep 1501407 = 2252111) B2252111
theorem B1501467 : Blo 1500070 1501467 := bstep (se 1 (by rfl) ⟨1126100, by rfl⟩ : syracuseStep 1501467 = 2252201) B2252201
theorem B7211359 : Blo 1500070 7211359 := bstep (se 1 (by rfl) ⟨5408519, by rfl⟩ : syracuseStep 7211359 = 10817039) B10817039
theorem B1501567 : Blo 1500070 1501567 := bstep (se 1 (by rfl) ⟨1126175, by rfl⟩ : syracuseStep 1501567 = 2252351) B2252351
theorem B5859809 : Blo 1500070 5859809 := bstep (se 2 (by rfl) ⟨2197428, by rfl⟩ : syracuseStep 5859809 = 4394857) B4394857
theorem B1501743 : Blo 1500070 1501743 := bstep (se 1 (by rfl) ⟨1126307, by rfl⟩ : syracuseStep 1501743 = 2252615) B2252615
theorem B14420531 : Blo 1500070 14420531 := bstep (se 1 (by rfl) ⟨10815398, by rfl⟩ : syracuseStep 14420531 = 21630797) B21630797
theorem B1501799 : Blo 1500070 1501799 := bstep (se 1 (by rfl) ⟨1126349, by rfl⟩ : syracuseStep 1501799 = 2252699) B2252699
theorem B3377825 : Blo 1500070 3377825 := bstep (se 2 (by rfl) ⟨1266684, by rfl⟩ : syracuseStep 3377825 = 2533369) B2533369
theorem B5065577 : Blo 1500070 5065577 := bstep (se 2 (by rfl) ⟨1899591, by rfl⟩ : syracuseStep 5065577 = 3799183) B3799183
theorem B3378041 : Blo 1500070 3378041 := bstep (se 2 (by rfl) ⟨1266765, by rfl⟩ : syracuseStep 3378041 = 2533531) B2533531
theorem B3378185 : Blo 1500070 3378185 := bstep (se 2 (by rfl) ⟨1266819, by rfl⟩ : syracuseStep 3378185 = 2533639) B2533639
theorem B3378239 : Blo 1500070 3378239 := bstep (se 1 (by rfl) ⟨2533679, by rfl⟩ : syracuseStep 3378239 = 5067359) B5067359
theorem B6409313 : Blo 1500070 6409313 := bstep (se 2 (by rfl) ⟨2403492, by rfl⟩ : syracuseStep 6409313 = 4806985) B4806985
theorem B25636013 : Blo 1500070 25636013 := bstep (se 3 (by rfl) ⟨4806752, by rfl⟩ : syracuseStep 25636013 = 9613505) B9613505
theorem B8228027 : Blo 1500070 8228027 := bstep (se 1 (by rfl) ⟨6171020, by rfl⟩ : syracuseStep 8228027 = 12342041) B12342041
theorem B10816811 : Blo 1500070 10816811 := bstep (se 1 (by rfl) ⟨8112608, by rfl⟩ : syracuseStep 10816811 = 16225217) B16225217
theorem B17092133 : Blo 1500070 17092133 := bstep (se 4 (by rfl) ⟨1602387, by rfl⟩ : syracuseStep 17092133 = 3204775) B3204775
theorem B4271849 : Blo 1500070 4271849 := bstep (se 2 (by rfl) ⟨1601943, by rfl⟩ : syracuseStep 4271849 = 3203887) B3203887
theorem B24350537 : Blo 1500070 24350537 := bstep (se 2 (by rfl) ⟨9131451, by rfl⟩ : syracuseStep 24350537 = 18262903) B18262903
theorem B3379067 : Blo 1500070 3379067 := bstep (se 1 (by rfl) ⟨2534300, by rfl⟩ : syracuseStep 3379067 = 5068601) B5068601
theorem B5066711 : Blo 1500070 5066711 := bstep (se 1 (by rfl) ⟨3800033, by rfl⟩ : syracuseStep 5066711 = 7600067) B7600067
theorem B5697499 : Blo 1500070 5697499 := bstep (se 1 (by rfl) ⟨4273124, by rfl⟩ : syracuseStep 5697499 = 8546249) B8546249
theorem B3379175 : Blo 1500070 3379175 := bstep (se 1 (by rfl) ⟨2534381, by rfl⟩ : syracuseStep 3379175 = 5068763) B5068763
theorem B2404345 : Blo 1500070 2404345 := bstep (se 2 (by rfl) ⟨901629, by rfl⟩ : syracuseStep 2404345 = 1803259) B1803259
theorem B3379355 : Blo 1500070 3379355 := bstep (se 1 (by rfl) ⟨2534516, by rfl⟩ : syracuseStep 3379355 = 5069033) B5069033
theorem B5066927 : Blo 1500070 5066927 := bstep (se 1 (by rfl) ⟨3800195, by rfl⟩ : syracuseStep 5066927 = 7600391) B7600391
theorem B3379553 : Blo 1500070 3379553 := bstep (se 2 (by rfl) ⟨1267332, by rfl⟩ : syracuseStep 3379553 = 2534665) B2534665
theorem B3797351 : Blo 1500070 3797351 := bstep (se 1 (by rfl) ⟨2848013, by rfl⟩ : syracuseStep 3797351 = 5696027) B5696027
theorem B7598447 : Blo 1500070 7598447 := bstep (se 1 (by rfl) ⟨5698835, by rfl⟩ : syracuseStep 7598447 = 11397671) B11397671
theorem B3379643 : Blo 1500070 3379643 := bstep (se 1 (by rfl) ⟨2534732, by rfl⟩ : syracuseStep 3379643 = 5069465) B5069465
theorem B5067899 : Blo 1500070 5067899 := bstep (se 1 (by rfl) ⟨3800924, by rfl⟩ : syracuseStep 5067899 = 7601849) B7601849
theorem B5068169 : Blo 1500070 5068169 := bstep (se 2 (by rfl) ⟨1900563, by rfl⟩ : syracuseStep 5068169 = 3801127) B3801127
theorem B2250215 : Blo 1500070 2250215 := bstep (se 1 (by rfl) ⟨1687661, by rfl⟩ : syracuseStep 2250215 = 3375323) B3375323
theorem B4273661 : Blo 1500070 4273661 := bstep (se 3 (by rfl) ⟨801311, by rfl⟩ : syracuseStep 4273661 = 1602623) B1602623
theorem B12170861 : Blo 1500070 12170861 := bstep (se 3 (by rfl) ⟨2282036, by rfl⟩ : syracuseStep 12170861 = 4564073) B4564073
theorem B2250377 : Blo 1500070 2250377 := bstep (se 2 (by rfl) ⟨843891, by rfl⟩ : syracuseStep 2250377 = 1687783) B1687783
theorem B2250395 : Blo 1500070 2250395 := bstep (se 1 (by rfl) ⟨1687796, by rfl⟩ : syracuseStep 2250395 = 3375593) B3375593
theorem B14431945 : Blo 1500070 14431945 := bstep (se 2 (by rfl) ⟨5411979, by rfl⟩ : syracuseStep 14431945 = 10823959) B10823959
theorem B2250587 : Blo 1500070 2250587 := bstep (se 1 (by rfl) ⟨1687940, by rfl⟩ : syracuseStep 2250587 = 3375881) B3375881
theorem B312088727 : Blo 1500070 312088727 := bstep (se 1 (by rfl) ⟨234066545, by rfl⟩ : syracuseStep 312088727 = 468133091) B468133091
theorem B2250971 : Blo 1500070 2250971 := bstep (se 1 (by rfl) ⟨1688228, by rfl⟩ : syracuseStep 2250971 = 3376457) B3376457
theorem B1898959 : Blo 1500070 1898959 := bstep (se 1 (by rfl) ⟨1424219, by rfl⟩ : syracuseStep 1898959 = 2848439) B2848439
theorem B2251241 : Blo 1500070 2251241 := bstep (se 2 (by rfl) ⟨844215, by rfl⟩ : syracuseStep 2251241 = 1688431) B1688431
theorem B2603561 : Blo 1500070 2603561 := bstep (se 2 (by rfl) ⟨976335, by rfl⟩ : syracuseStep 2603561 = 1952671) B1952671
theorem B3422945 : Blo 1500070 3422945 := bstep (se 2 (by rfl) ⟨1283604, by rfl⟩ : syracuseStep 3422945 = 2567209) B2567209
theorem B2251631 : Blo 1500070 2251631 := bstep (se 1 (by rfl) ⟨1688723, by rfl⟩ : syracuseStep 2251631 = 3377447) B3377447
theorem B2251643 : Blo 1500070 2251643 := bstep (se 1 (by rfl) ⟨1688732, by rfl⟩ : syracuseStep 2251643 = 3377465) B3377465
theorem B9509825 : Blo 1500070 9509825 := bstep (se 2 (by rfl) ⟨3566184, by rfl⟩ : syracuseStep 9509825 = 7132369) B7132369
theorem B4275175 : Blo 1500070 4275175 := bstep (se 1 (by rfl) ⟨3206381, by rfl⟩ : syracuseStep 4275175 = 6412763) B6412763
theorem B2849897 : Blo 1500070 2849897 := bstep (se 2 (by rfl) ⟨1068711, by rfl⟩ : syracuseStep 2849897 = 2137423) B2137423
theorem B2850299 : Blo 1500070 2850299 := bstep (se 1 (by rfl) ⟨2137724, by rfl⟩ : syracuseStep 2850299 = 4275449) B4275449
theorem B4808317 : Blo 1500070 4808317 := bstep (se 3 (by rfl) ⟨901559, by rfl⟩ : syracuseStep 4808317 = 1803119) B1803119
theorem B2252507 : Blo 1500070 2252507 := bstep (se 1 (by rfl) ⟨1689380, by rfl⟩ : syracuseStep 2252507 = 3378761) B3378761
theorem B2850527 : Blo 1500070 2850527 := bstep (se 1 (by rfl) ⟨2137895, by rfl⟩ : syracuseStep 2850527 = 4275791) B4275791
theorem B2138089 : Blo 1500070 2138089 := bstep (se 2 (by rfl) ⟨801783, by rfl⟩ : syracuseStep 2138089 = 1603567) B1603567
theorem B2252777 : Blo 1500070 2252777 := bstep (se 2 (by rfl) ⟨844791, by rfl⟩ : syracuseStep 2252777 = 1689583) B1689583
theorem B2252903 : Blo 1500070 2252903 := bstep (se 1 (by rfl) ⟨1689677, by rfl⟩ : syracuseStep 2252903 = 3379355) B3379355
theorem B2253035 : Blo 1500070 2253035 := bstep (se 1 (by rfl) ⟨1689776, by rfl⟩ : syracuseStep 2253035 = 3379553) B3379553
theorem B2531567 : Blo 1500070 2531567 := bstep (se 1 (by rfl) ⟨1898675, by rfl⟩ : syracuseStep 2531567 = 3797351) B3797351
theorem B2253095 : Blo 1500070 2253095 := bstep (se 1 (by rfl) ⟨1689821, by rfl⟩ : syracuseStep 2253095 = 3379643) B3379643
theorem B88883507 : Blo 1500070 88883507 := bstep (se 1 (by rfl) ⟨66662630, by rfl⟩ : syracuseStep 88883507 = 133325261) B133325261
theorem B3801401 : Blo 1500070 3801401 := bstep (se 2 (by rfl) ⟨1425525, by rfl⟩ : syracuseStep 3801401 = 2851051) B2851051
theorem B3375521 : Blo 1500070 3375521 := bstep (se 2 (by rfl) ⟨1265820, by rfl⟩ : syracuseStep 3375521 = 2531641) B2531641
theorem B97419779 : Blo 1500070 97419779 := bstep (se 1 (by rfl) ⟨73064834, by rfl⟩ : syracuseStep 97419779 = 146129669) B146129669
theorem B2851355 : Blo 1500070 2851355 := bstep (se 1 (by rfl) ⟨2138516, by rfl⟩ : syracuseStep 2851355 = 4277033) B4277033
theorem B2531945 : Blo 1500070 2531945 := bstep (se 2 (by rfl) ⟨949479, by rfl⟩ : syracuseStep 2531945 = 1898959) B1898959
theorem B51971003 : Blo 1500070 51971003 := bstep (se 1 (by rfl) ⟨38978252, by rfl⟩ : syracuseStep 51971003 = 77956505) B77956505
theorem B3376079 : Blo 1500070 3376079 := bstep (se 1 (by rfl) ⟨2532059, by rfl⟩ : syracuseStep 3376079 = 5064119) B5064119
theorem B1500143 : Blo 1500070 1500143 := bstep (se 1 (by rfl) ⟨1125107, by rfl⟩ : syracuseStep 1500143 = 2250215) B2250215
theorem B3376169 : Blo 1500070 3376169 := bstep (se 2 (by rfl) ⟨1266063, by rfl⟩ : syracuseStep 3376169 = 2532127) B2532127
theorem B1500251 : Blo 1500070 1500251 := bstep (se 1 (by rfl) ⟨1125188, by rfl⟩ : syracuseStep 1500251 = 2250377) B2250377
theorem B1500263 : Blo 1500070 1500263 := bstep (se 1 (by rfl) ⟨1125197, by rfl⟩ : syracuseStep 1500263 = 2250395) B2250395
theorem B5702831 : Blo 1500070 5702831 := bstep (se 1 (by rfl) ⟨4277123, by rfl⟩ : syracuseStep 5702831 = 8554247) B8554247
theorem B1500391 : Blo 1500070 1500391 := bstep (se 1 (by rfl) ⟨1125293, by rfl⟩ : syracuseStep 1500391 = 2250587) B2250587
theorem B8553721 : Blo 1500070 8553721 := bstep (se 2 (by rfl) ⟨3207645, by rfl⟩ : syracuseStep 8553721 = 6415291) B6415291
theorem B1688935 : Blo 1500070 1688935 := bstep (se 1 (by rfl) ⟨1266701, by rfl⟩ : syracuseStep 1688935 = 2533403) B2533403
theorem B1500647 : Blo 1500070 1500647 := bstep (se 1 (by rfl) ⟨1125485, by rfl⟩ : syracuseStep 1500647 = 2250971) B2250971
theorem B7603793 : Blo 1500070 7603793 := bstep (se 2 (by rfl) ⟨2851422, by rfl⟩ : syracuseStep 7603793 = 5702845) B5702845
theorem B1500827 : Blo 1500070 1500827 := bstep (se 1 (by rfl) ⟨1125620, by rfl⟩ : syracuseStep 1500827 = 2251241) B2251241
theorem B3377051 : Blo 1500070 3377051 := bstep (se 1 (by rfl) ⟨2532788, by rfl⟩ : syracuseStep 3377051 = 5065577) B5065577
theorem B1501087 : Blo 1500070 1501087 := bstep (se 1 (by rfl) ⟨1125815, by rfl⟩ : syracuseStep 1501087 = 2251631) B2251631
theorem B1501095 : Blo 1500070 1501095 := bstep (se 1 (by rfl) ⟨1125821, by rfl⟩ : syracuseStep 1501095 = 2251643) B2251643
theorem B3377249 : Blo 1500070 3377249 := bstep (se 2 (by rfl) ⟨1266468, by rfl⟩ : syracuseStep 3377249 = 2532937) B2532937
theorem B17090675 : Blo 1500070 17090675 := bstep (se 1 (by rfl) ⟨12818006, by rfl⟩ : syracuseStep 17090675 = 25636013) B25636013
theorem B7211207 : Blo 1500070 7211207 := bstep (se 1 (by rfl) ⟨5408405, by rfl⟩ : syracuseStep 7211207 = 10816811) B10816811
theorem B1501671 : Blo 1500070 1501671 := bstep (se 1 (by rfl) ⟨1126253, by rfl⟩ : syracuseStep 1501671 = 2252507) B2252507
theorem B7596665 : Blo 1500070 7596665 := bstep (se 2 (by rfl) ⟨2848749, by rfl⟩ : syracuseStep 7596665 = 5697499) B5697499
theorem B3377807 : Blo 1500070 3377807 := bstep (se 1 (by rfl) ⟨2533355, by rfl⟩ : syracuseStep 3377807 = 5066711) B5066711
theorem B1501851 : Blo 1500070 1501851 := bstep (se 1 (by rfl) ⟨1126388, by rfl⟩ : syracuseStep 1501851 = 2252777) B2252777
theorem B3205793 : Blo 1500070 3205793 := bstep (se 2 (by rfl) ⟨1202172, by rfl⟩ : syracuseStep 3205793 = 2404345) B2404345
theorem B3377897 : Blo 1500070 3377897 := bstep (se 2 (by rfl) ⟨1266711, by rfl⟩ : syracuseStep 3377897 = 2533423) B2533423
theorem B3377951 : Blo 1500070 3377951 := bstep (se 1 (by rfl) ⟨2533463, by rfl⟩ : syracuseStep 3377951 = 5066927) B5066927
theorem B9612071 : Blo 1500070 9612071 := bstep (se 1 (by rfl) ⟨7209053, by rfl⟩ : syracuseStep 9612071 = 14418107) B14418107
theorem B5065631 : Blo 1500070 5065631 := bstep (se 1 (by rfl) ⟨3799223, by rfl⟩ : syracuseStep 5065631 = 7598447) B7598447
theorem B12815273 : Blo 1500070 12815273 := bstep (se 2 (by rfl) ⟨4805727, by rfl⟩ : syracuseStep 12815273 = 9611455) B9611455
theorem B832236605 : Blo 1500070 832236605 := bstep (se 3 (by rfl) ⟨156044363, by rfl⟩ : syracuseStep 832236605 = 312088727) B312088727
theorem B21941405 : Blo 1500070 21941405 := bstep (se 3 (by rfl) ⟨4114013, by rfl⟩ : syracuseStep 21941405 = 8228027) B8228027
theorem B3378599 : Blo 1500070 3378599 := bstep (se 1 (by rfl) ⟨2533949, by rfl⟩ : syracuseStep 3378599 = 5067899) B5067899
theorem B78015955 : Blo 1500070 78015955 := bstep (se 1 (by rfl) ⟨58511966, by rfl⟩ : syracuseStep 78015955 = 117023933) B117023933
theorem B15625723 : Blo 1500070 15625723 := bstep (se 1 (by rfl) ⟨11719292, by rfl⟩ : syracuseStep 15625723 = 23438585) B23438585
theorem B32452163 : Blo 1500070 32452163 := bstep (se 1 (by rfl) ⟨24339122, by rfl⟩ : syracuseStep 32452163 = 48678245) B48678245
theorem B3378779 : Blo 1500070 3378779 := bstep (se 1 (by rfl) ⟨2534084, by rfl⟩ : syracuseStep 3378779 = 5068169) B5068169
theorem B8113907 : Blo 1500070 8113907 := bstep (se 1 (by rfl) ⟨6085430, by rfl⟩ : syracuseStep 8113907 = 12170861) B12170861
theorem B3469127 : Blo 1500070 3469127 := bstep (se 1 (by rfl) ⟨2601845, by rfl⟩ : syracuseStep 3469127 = 5203691) B5203691
theorem B27389971 : Blo 1500070 27389971 := bstep (se 1 (by rfl) ⟨20542478, by rfl⟩ : syracuseStep 27389971 = 41084957) B41084957
theorem B21639271 : Blo 1500070 21639271 := bstep (se 1 (by rfl) ⟨16229453, by rfl⟩ : syracuseStep 21639271 = 32458907) B32458907
theorem B6942829 : Blo 1500070 6942829 := bstep (se 3 (by rfl) ⟨1301780, by rfl⟩ : syracuseStep 6942829 = 2603561) B2603561
theorem B9613687 : Blo 1500070 9613687 := bstep (se 1 (by rfl) ⟨7210265, by rfl⟩ : syracuseStep 9613687 = 14420531) B14420531
theorem B2281963 : Blo 1500070 2281963 := bstep (se 1 (by rfl) ⟨1711472, by rfl⟩ : syracuseStep 2281963 = 3422945) B3422945
theorem B4272875 : Blo 1500070 4272875 := bstep (se 1 (by rfl) ⟨3204656, by rfl⟩ : syracuseStep 4272875 = 6409313) B6409313
theorem B6411089 : Blo 1500070 6411089 := bstep (se 2 (by rfl) ⟨2404158, by rfl⟩ : syracuseStep 6411089 = 4808317) B4808317
theorem B2847899 : Blo 1500070 2847899 := bstep (se 1 (by rfl) ⟨2135924, by rfl⟩ : syracuseStep 2847899 = 4271849) B4271849
theorem B16233691 : Blo 1500070 16233691 := bstep (se 1 (by rfl) ⟨12175268, by rfl⟩ : syracuseStep 16233691 = 24350537) B24350537
theorem B7812409 : Blo 1500070 7812409 := bstep (se 2 (by rfl) ⟨2929653, by rfl⟩ : syracuseStep 7812409 = 5859307) B5859307
theorem B2250431 : Blo 1500070 2250431 := bstep (se 1 (by rfl) ⟨1687823, by rfl⟩ : syracuseStep 2250431 = 3375647) B3375647
theorem B2250473 : Blo 1500070 2250473 := bstep (se 2 (by rfl) ⟨843927, by rfl⟩ : syracuseStep 2250473 = 1687855) B1687855
theorem B2250479 : Blo 1500070 2250479 := bstep (se 1 (by rfl) ⟨1687859, by rfl⟩ : syracuseStep 2250479 = 3375719) B3375719
theorem B83269691 : Blo 1500070 83269691 := bstep (se 1 (by rfl) ⟨62452268, by rfl⟩ : syracuseStep 83269691 = 124904537) B124904537
theorem B5068925 : Blo 1500070 5068925 := bstep (se 3 (by rfl) ⟨950423, by rfl⟩ : syracuseStep 5068925 = 1900847) B1900847
theorem B17340587 : Blo 1500070 17340587 := bstep (se 1 (by rfl) ⟨13005440, by rfl⟩ : syracuseStep 17340587 = 26010881) B26010881
theorem B2250983 : Blo 1500070 2250983 := bstep (se 1 (by rfl) ⟨1688237, by rfl⟩ : syracuseStep 2250983 = 3376475) B3376475
theorem B5069087 : Blo 1500070 5069087 := bstep (se 1 (by rfl) ⟨3801815, by rfl⟩ : syracuseStep 5069087 = 7603631) B7603631
theorem B23435579 : Blo 1500070 23435579 := bstep (se 1 (by rfl) ⟨17576684, by rfl⟩ : syracuseStep 23435579 = 35153369) B35153369
theorem B2849107 : Blo 1500070 2849107 := bstep (se 1 (by rfl) ⟨2136830, by rfl⟩ : syracuseStep 2849107 = 4273661) B4273661
theorem B2251163 : Blo 1500070 2251163 := bstep (se 1 (by rfl) ⟨1688372, by rfl⟩ : syracuseStep 2251163 = 3376745) B3376745
theorem B5700233 : Blo 1500070 5700233 := bstep (se 2 (by rfl) ⟨2137587, by rfl⟩ : syracuseStep 5700233 = 4275175) B4275175
theorem B4807421 : Blo 1500070 4807421 := bstep (se 3 (by rfl) ⟨901391, by rfl⟩ : syracuseStep 4807421 = 1802783) B1802783
theorem B2251559 : Blo 1500070 2251559 := bstep (se 1 (by rfl) ⟨1688669, by rfl⟩ : syracuseStep 2251559 = 3377339) B3377339
theorem B2251583 : Blo 1500070 2251583 := bstep (se 1 (by rfl) ⟨1688687, by rfl⟩ : syracuseStep 2251583 = 3377375) B3377375
theorem B3906539 : Blo 1500070 3906539 := bstep (se 1 (by rfl) ⟨2929904, by rfl⟩ : syracuseStep 3906539 = 5859809) B5859809
theorem B2251883 : Blo 1500070 2251883 := bstep (se 1 (by rfl) ⟨1688912, by rfl⟩ : syracuseStep 2251883 = 3377825) B3377825
theorem B38460581 : Blo 1500070 38460581 := bstep (se 4 (by rfl) ⟨3605679, by rfl⟩ : syracuseStep 38460581 = 7211359) B7211359
theorem B2252027 : Blo 1500070 2252027 := bstep (se 1 (by rfl) ⟨1689020, by rfl⟩ : syracuseStep 2252027 = 3378041) B3378041
theorem B6339883 : Blo 1500070 6339883 := bstep (se 1 (by rfl) ⟨4754912, by rfl⟩ : syracuseStep 6339883 = 9509825) B9509825
theorem B2252123 : Blo 1500070 2252123 := bstep (se 1 (by rfl) ⟨1689092, by rfl⟩ : syracuseStep 2252123 = 3378185) B3378185
theorem B2252153 : Blo 1500070 2252153 := bstep (se 2 (by rfl) ⟨844557, by rfl⟩ : syracuseStep 2252153 = 1689115) B1689115
theorem B2252159 : Blo 1500070 2252159 := bstep (se 1 (by rfl) ⟨1689119, by rfl⟩ : syracuseStep 2252159 = 3378239) B3378239
theorem B1899931 : Blo 1500070 1899931 := bstep (se 1 (by rfl) ⟨1424948, by rfl⟩ : syracuseStep 1899931 = 2849897) B2849897
theorem B19242593 : Blo 1500070 19242593 := bstep (se 2 (by rfl) ⟨7215972, by rfl⟩ : syracuseStep 19242593 = 14431945) B14431945
theorem B1900199 : Blo 1500070 1900199 := bstep (se 1 (by rfl) ⟨1425149, by rfl⟩ : syracuseStep 1900199 = 2850299) B2850299
theorem B11394755 : Blo 1500070 11394755 := bstep (se 1 (by rfl) ⟨8546066, by rfl⟩ : syracuseStep 11394755 = 17092133) B17092133
theorem B1900351 : Blo 1500070 1900351 := bstep (se 1 (by rfl) ⟨1425263, by rfl⟩ : syracuseStep 1900351 = 2850527) B2850527
theorem B4874089 : Blo 1500070 4874089 := bstep (se 2 (by rfl) ⟨1827783, by rfl⟩ : syracuseStep 4874089 = 3655567) B3655567
theorem B2252711 : Blo 1500070 2252711 := bstep (se 1 (by rfl) ⟨1689533, by rfl⟩ : syracuseStep 2252711 = 3379067) B3379067
theorem B2850785 : Blo 1500070 2850785 := bstep (se 2 (by rfl) ⟨1069044, by rfl⟩ : syracuseStep 2850785 = 2138089) B2138089
theorem B2252783 : Blo 1500070 2252783 := bstep (se 1 (by rfl) ⟨1689587, by rfl⟩ : syracuseStep 2252783 = 3379175) B3379175
theorem B146079845 : Blo 1500070 146079845 := bstep (se 4 (by rfl) ⟨13694985, by rfl⟩ : syracuseStep 146079845 = 27389971) B27389971
theorem B28852361 : Blo 1500070 28852361 := bstep (se 2 (by rfl) ⟨10819635, by rfl⟩ : syracuseStep 28852361 = 21639271) B21639271
theorem B9257105 : Blo 1500070 9257105 := bstep (se 2 (by rfl) ⟨3471414, by rfl⟩ : syracuseStep 9257105 = 6942829) B6942829
theorem B1687711 : Blo 1500070 1687711 := bstep (se 1 (by rfl) ⟨1265783, by rfl⟩ : syracuseStep 1687711 = 2531567) B2531567
theorem B64946519 : Blo 1500070 64946519 := bstep (se 1 (by rfl) ⟨48709889, by rfl⟩ : syracuseStep 64946519 = 97419779) B97419779
theorem B1900903 : Blo 1500070 1900903 := bstep (se 1 (by rfl) ⟨1425677, by rfl⟩ : syracuseStep 1900903 = 2851355) B2851355
theorem B1687963 : Blo 1500070 1687963 := bstep (se 1 (by rfl) ⟨1265972, by rfl⟩ : syracuseStep 1687963 = 2531945) B2531945
theorem B7594397 : Blo 1500070 7594397 := bstep (se 3 (by rfl) ⟨1423949, by rfl⟩ : syracuseStep 7594397 = 2847899) B2847899
theorem B3801887 : Blo 1500070 3801887 := bstep (se 1 (by rfl) ⟨2851415, by rfl⟩ : syracuseStep 3801887 = 5702831) B5702831
theorem B1500287 : Blo 1500070 1500287 := bstep (se 1 (by rfl) ⟨1125215, by rfl⟩ : syracuseStep 1500287 = 2250431) B2250431
theorem B1500315 : Blo 1500070 1500315 := bstep (se 1 (by rfl) ⟨1125236, by rfl⟩ : syracuseStep 1500315 = 2250473) B2250473
theorem B1500319 : Blo 1500070 1500319 := bstep (se 1 (by rfl) ⟨1125239, by rfl⟩ : syracuseStep 1500319 = 2250479) B2250479
theorem B11560391 : Blo 1500070 11560391 := bstep (se 1 (by rfl) ⟨8670293, by rfl⟩ : syracuseStep 11560391 = 17340587) B17340587
theorem B1500655 : Blo 1500070 1500655 := bstep (se 1 (by rfl) ⟨1125491, by rfl⟩ : syracuseStep 1500655 = 2250983) B2250983
theorem B1500775 : Blo 1500070 1500775 := bstep (se 1 (by rfl) ⟨1125581, by rfl⟩ : syracuseStep 1500775 = 2251163) B2251163
theorem B21644921 : Blo 1500070 21644921 := bstep (se 2 (by rfl) ⟨8116845, by rfl⟩ : syracuseStep 21644921 = 16233691) B16233691
theorem B11404961 : Blo 1500070 11404961 := bstep (se 2 (by rfl) ⟨4276860, by rfl⟩ : syracuseStep 11404961 = 8553721) B8553721
theorem B5064443 : Blo 1500070 5064443 := bstep (se 1 (by rfl) ⟨3798332, by rfl⟩ : syracuseStep 5064443 = 7596665) B7596665
theorem B3204947 : Blo 1500070 3204947 := bstep (se 1 (by rfl) ⟨2403710, by rfl⟩ : syracuseStep 3204947 = 4807421) B4807421
theorem B6408047 : Blo 1500070 6408047 := bstep (se 1 (by rfl) ⟨4806035, by rfl⟩ : syracuseStep 6408047 = 9612071) B9612071
theorem B1501039 : Blo 1500070 1501039 := bstep (se 1 (by rfl) ⟨1125779, by rfl⟩ : syracuseStep 1501039 = 2251559) B2251559
theorem B2533241 : Blo 1500070 2533241 := bstep (se 2 (by rfl) ⟨949965, by rfl⟩ : syracuseStep 2533241 = 1899931) B1899931
theorem B1501055 : Blo 1500070 1501055 := bstep (se 1 (by rfl) ⟨1125791, by rfl⟩ : syracuseStep 1501055 = 2251583) B2251583
theorem B3377087 : Blo 1500070 3377087 := bstep (se 1 (by rfl) ⟨2532815, by rfl⟩ : syracuseStep 3377087 = 5065631) B5065631
theorem B20834297 : Blo 1500070 20834297 := bstep (se 2 (by rfl) ⟨7812861, by rfl⟩ : syracuseStep 20834297 = 15625723) B15625723
theorem B1501255 : Blo 1500070 1501255 := bstep (se 1 (by rfl) ⟨1125941, by rfl⟩ : syracuseStep 1501255 = 2251883) B2251883
theorem B1501351 : Blo 1500070 1501351 := bstep (se 1 (by rfl) ⟨1126013, by rfl⟩ : syracuseStep 1501351 = 2252027) B2252027
theorem B9251005 : Blo 1500070 9251005 := bstep (se 3 (by rfl) ⟨1734563, by rfl⟩ : syracuseStep 9251005 = 3469127) B3469127
theorem B1501415 : Blo 1500070 1501415 := bstep (se 1 (by rfl) ⟨1126061, by rfl⟩ : syracuseStep 1501415 = 2252123) B2252123
theorem B1501435 : Blo 1500070 1501435 := bstep (se 1 (by rfl) ⟨1126076, by rfl⟩ : syracuseStep 1501435 = 2252153) B2252153
theorem B1501439 : Blo 1500070 1501439 := bstep (se 1 (by rfl) ⟨1126079, by rfl⟩ : syracuseStep 1501439 = 2252159) B2252159
theorem B2533801 : Blo 1500070 2533801 := bstep (se 2 (by rfl) ⟨950175, by rfl⟩ : syracuseStep 2533801 = 1900351) B1900351
theorem B7596503 : Blo 1500070 7596503 := bstep (se 1 (by rfl) ⟨5697377, by rfl⟩ : syracuseStep 7596503 = 11394755) B11394755
theorem B6498785 : Blo 1500070 6498785 := bstep (se 2 (by rfl) ⟨2437044, by rfl⟩ : syracuseStep 6498785 = 4874089) B4874089
theorem B5409271 : Blo 1500070 5409271 := bstep (se 1 (by rfl) ⟨4056953, by rfl⟩ : syracuseStep 5409271 = 8113907) B8113907
theorem B1501807 : Blo 1500070 1501807 := bstep (se 1 (by rfl) ⟨1126355, by rfl⟩ : syracuseStep 1501807 = 2252711) B2252711
theorem B1501855 : Blo 1500070 1501855 := bstep (se 1 (by rfl) ⟨1126391, by rfl⟩ : syracuseStep 1501855 = 2252783) B2252783
theorem B1501935 : Blo 1500070 1501935 := bstep (se 1 (by rfl) ⟨1126451, by rfl⟩ : syracuseStep 1501935 = 2252903) B2252903
theorem B1502023 : Blo 1500070 1502023 := bstep (se 1 (by rfl) ⟨1126517, by rfl⟩ : syracuseStep 1502023 = 2253035) B2253035
theorem B1502063 : Blo 1500070 1502063 := bstep (se 1 (by rfl) ⟨1126547, by rfl⟩ : syracuseStep 1502063 = 2253095) B2253095
theorem B2534267 : Blo 1500070 2534267 := bstep (se 1 (by rfl) ⟨1900700, by rfl⟩ : syracuseStep 2534267 = 3801401) B3801401
theorem B34647335 : Blo 1500070 34647335 := bstep (se 1 (by rfl) ⟨25985501, by rfl⟩ : syracuseStep 34647335 = 51971003) B51971003
theorem B3042617 : Blo 1500070 3042617 := bstep (se 2 (by rfl) ⟨1140981, by rfl⟩ : syracuseStep 3042617 = 2281963) B2281963
theorem B237022685 : Blo 1500070 237022685 := bstep (se 3 (by rfl) ⟨44441753, by rfl⟩ : syracuseStep 237022685 = 88883507) B88883507
theorem B55513127 : Blo 1500070 55513127 := bstep (se 1 (by rfl) ⟨41634845, by rfl⟩ : syracuseStep 55513127 = 83269691) B83269691
theorem B3379283 : Blo 1500070 3379283 := bstep (se 1 (by rfl) ⟨2534462, by rfl⟩ : syracuseStep 3379283 = 5068925) B5068925
theorem B3379391 : Blo 1500070 3379391 := bstep (se 1 (by rfl) ⟨2534543, by rfl⟩ : syracuseStep 3379391 = 5069087) B5069087
theorem B10416545 : Blo 1500070 10416545 := bstep (se 2 (by rfl) ⟨3906204, by rfl⟩ : syracuseStep 10416545 = 7812409) B7812409
theorem B5067197 : Blo 1500070 5067197 := bstep (se 3 (by rfl) ⟨950099, by rfl⟩ : syracuseStep 5067197 = 1900199) B1900199
theorem B554824403 : Blo 1500070 554824403 := bstep (se 1 (by rfl) ⟨416118302, by rfl⟩ : syracuseStep 554824403 = 832236605) B832236605
theorem B14627603 : Blo 1500070 14627603 := bstep (se 1 (by rfl) ⟨10970702, by rfl⟩ : syracuseStep 14627603 = 21941405) B21941405
theorem B2250347 : Blo 1500070 2250347 := bstep (se 1 (by rfl) ⟨1687760, by rfl⟩ : syracuseStep 2250347 = 3375521) B3375521
theorem B3798809 : Blo 1500070 3798809 := bstep (se 2 (by rfl) ⟨1424553, by rfl⟩ : syracuseStep 3798809 = 2849107) B2849107
theorem B2848583 : Blo 1500070 2848583 := bstep (se 1 (by rfl) ⟨2136437, by rfl⟩ : syracuseStep 2848583 = 4272875) B4272875
theorem B12818249 : Blo 1500070 12818249 := bstep (se 2 (by rfl) ⟨4806843, by rfl⟩ : syracuseStep 12818249 = 9613687) B9613687
theorem B4274059 : Blo 1500070 4274059 := bstep (se 1 (by rfl) ⟨3205544, by rfl⟩ : syracuseStep 4274059 = 6411089) B6411089
theorem B2250719 : Blo 1500070 2250719 := bstep (se 1 (by rfl) ⟨1688039, by rfl⟩ : syracuseStep 2250719 = 3376079) B3376079
theorem B2250779 : Blo 1500070 2250779 := bstep (se 1 (by rfl) ⟨1688084, by rfl⟩ : syracuseStep 2250779 = 3376169) B3376169
theorem B62494877 : Blo 1500070 62494877 := bstep (se 3 (by rfl) ⟨11717789, by rfl⟩ : syracuseStep 62494877 = 23435579) B23435579
theorem B5069195 : Blo 1500070 5069195 := bstep (se 1 (by rfl) ⟨3801896, by rfl⟩ : syracuseStep 5069195 = 7603793) B7603793
theorem B2251367 : Blo 1500070 2251367 := bstep (se 1 (by rfl) ⟨1688525, by rfl⟩ : syracuseStep 2251367 = 3377051) B3377051
theorem B2251499 : Blo 1500070 2251499 := bstep (se 1 (by rfl) ⟨1688624, by rfl⟩ : syracuseStep 2251499 = 3377249) B3377249
theorem B11393783 : Blo 1500070 11393783 := bstep (se 1 (by rfl) ⟨8545337, by rfl⟩ : syracuseStep 11393783 = 17090675) B17090675
theorem B4807471 : Blo 1500070 4807471 := bstep (se 1 (by rfl) ⟨3605603, by rfl⟩ : syracuseStep 4807471 = 7211207) B7211207
theorem B8453177 : Blo 1500070 8453177 := bstep (se 2 (by rfl) ⟨3169941, by rfl⟩ : syracuseStep 8453177 = 6339883) B6339883
theorem B3800155 : Blo 1500070 3800155 := bstep (se 1 (by rfl) ⟨2850116, by rfl⟩ : syracuseStep 3800155 = 5700233) B5700233
theorem B2251871 : Blo 1500070 2251871 := bstep (se 1 (by rfl) ⟨1688903, by rfl⟩ : syracuseStep 2251871 = 3377807) B3377807
theorem B2137195 : Blo 1500070 2137195 := bstep (se 1 (by rfl) ⟨1602896, by rfl⟩ : syracuseStep 2137195 = 3205793) B3205793
theorem B2251913 : Blo 1500070 2251913 := bstep (se 2 (by rfl) ⟨844467, by rfl⟩ : syracuseStep 2251913 = 1688935) B1688935
theorem B2251931 : Blo 1500070 2251931 := bstep (se 1 (by rfl) ⟨1688948, by rfl⟩ : syracuseStep 2251931 = 3377897) B3377897
theorem B2251967 : Blo 1500070 2251967 := bstep (se 1 (by rfl) ⟨1688975, by rfl⟩ : syracuseStep 2251967 = 3377951) B3377951
theorem B104021273 : Blo 1500070 104021273 := bstep (se 2 (by rfl) ⟨39007977, by rfl⟩ : syracuseStep 104021273 = 78015955) B78015955
theorem B8543515 : Blo 1500070 8543515 := bstep (se 1 (by rfl) ⟨6407636, by rfl⟩ : syracuseStep 8543515 = 12815273) B12815273
theorem B2604359 : Blo 1500070 2604359 := bstep (se 1 (by rfl) ⟨1953269, by rfl⟩ : syracuseStep 2604359 = 3906539) B3906539
theorem B25640387 : Blo 1500070 25640387 := bstep (se 1 (by rfl) ⟨19230290, by rfl⟩ : syracuseStep 25640387 = 38460581) B38460581
theorem B2252399 : Blo 1500070 2252399 := bstep (se 1 (by rfl) ⟨1689299, by rfl⟩ : syracuseStep 2252399 = 3378599) B3378599
theorem B21634775 : Blo 1500070 21634775 := bstep (se 1 (by rfl) ⟨16226081, by rfl⟩ : syracuseStep 21634775 = 32452163) B32452163
theorem B2252519 : Blo 1500070 2252519 := bstep (se 1 (by rfl) ⟨1689389, by rfl⟩ : syracuseStep 2252519 = 3378779) B3378779
theorem B12828395 : Blo 1500070 12828395 := bstep (se 1 (by rfl) ⟨9621296, by rfl⟩ : syracuseStep 12828395 = 19242593) B19242593
theorem B1900523 : Blo 1500070 1900523 := bstep (se 1 (by rfl) ⟨1425392, by rfl⟩ : syracuseStep 1900523 = 2850785) B2850785
theorem B2252855 : Blo 1500070 2252855 := bstep (se 1 (by rfl) ⟨1689641, by rfl⟩ : syracuseStep 2252855 = 3379283) B3379283
theorem B97386563 : Blo 1500070 97386563 := bstep (se 1 (by rfl) ⟨73039922, by rfl⟩ : syracuseStep 97386563 = 146079845) B146079845
theorem B19234907 : Blo 1500070 19234907 := bstep (se 1 (by rfl) ⟨14426180, by rfl⟩ : syracuseStep 19234907 = 28852361) B28852361
theorem B2252927 : Blo 1500070 2252927 := bstep (se 1 (by rfl) ⟨1689695, by rfl⟩ : syracuseStep 2252927 = 3379391) B3379391
theorem B5062931 : Blo 1500070 5062931 := bstep (se 1 (by rfl) ⟨3797198, by rfl⟩ : syracuseStep 5062931 = 7594397) B7594397
theorem B1500231 : Blo 1500070 1500231 := bstep (se 1 (by rfl) ⟨1125173, by rfl⟩ : syracuseStep 1500231 = 2250347) B2250347
theorem B7603307 : Blo 1500070 7603307 := bstep (se 1 (by rfl) ⟨5702480, by rfl⟩ : syracuseStep 7603307 = 11404961) B11404961
theorem B3376295 : Blo 1500070 3376295 := bstep (se 1 (by rfl) ⟨2532221, by rfl⟩ : syracuseStep 3376295 = 5064443) B5064443
theorem B2532539 : Blo 1500070 2532539 := bstep (se 1 (by rfl) ⟨1899404, by rfl⟩ : syracuseStep 2532539 = 3798809) B3798809
theorem B8545499 : Blo 1500070 8545499 := bstep (se 1 (by rfl) ⟨6409124, by rfl⟩ : syracuseStep 8545499 = 12818249) B12818249
theorem B1688827 : Blo 1500070 1688827 := bstep (se 1 (by rfl) ⟨1266620, by rfl⟩ : syracuseStep 1688827 = 2533241) B2533241
theorem B1500479 : Blo 1500070 1500479 := bstep (se 1 (by rfl) ⟨1125359, by rfl⟩ : syracuseStep 1500479 = 2250719) B2250719
theorem B1500519 : Blo 1500070 1500519 := bstep (se 1 (by rfl) ⟨1125389, by rfl⟩ : syracuseStep 1500519 = 2250779) B2250779
theorem B5064335 : Blo 1500070 5064335 := bstep (se 1 (by rfl) ⟨3798251, by rfl⟩ : syracuseStep 5064335 = 7596503) B7596503
theorem B1500911 : Blo 1500070 1500911 := bstep (se 1 (by rfl) ⟨1125683, by rfl⟩ : syracuseStep 1500911 = 2251367) B2251367
theorem B1500999 : Blo 1500070 1500999 := bstep (se 1 (by rfl) ⟨1125749, by rfl⟩ : syracuseStep 1500999 = 2251499) B2251499
theorem B7595855 : Blo 1500070 7595855 := bstep (se 1 (by rfl) ⟨5696891, by rfl⟩ : syracuseStep 7595855 = 11393783) B11393783
theorem B1689511 : Blo 1500070 1689511 := bstep (se 1 (by rfl) ⟨1267133, by rfl⟩ : syracuseStep 1689511 = 2534267) B2534267
theorem B1501247 : Blo 1500070 1501247 := bstep (se 1 (by rfl) ⟨1125935, by rfl⟩ : syracuseStep 1501247 = 2251871) B2251871
theorem B1501275 : Blo 1500070 1501275 := bstep (se 1 (by rfl) ⟨1125956, by rfl⟩ : syracuseStep 1501275 = 2251913) B2251913
theorem B1501287 : Blo 1500070 1501287 := bstep (se 1 (by rfl) ⟨1125965, by rfl⟩ : syracuseStep 1501287 = 2251931) B2251931
theorem B1501311 : Blo 1500070 1501311 := bstep (se 1 (by rfl) ⟨1125983, by rfl⟩ : syracuseStep 1501311 = 2251967) B2251967
theorem B69347515 : Blo 1500070 69347515 := bstep (se 1 (by rfl) ⟨52010636, by rfl⟩ : syracuseStep 69347515 = 104021273) B104021273
theorem B1501599 : Blo 1500070 1501599 := bstep (se 1 (by rfl) ⟨1126199, by rfl⟩ : syracuseStep 1501599 = 2252399) B2252399
theorem B1501679 : Blo 1500070 1501679 := bstep (se 1 (by rfl) ⟨1126259, by rfl⟩ : syracuseStep 1501679 = 2252519) B2252519
theorem B6171403 : Blo 1500070 6171403 := bstep (se 1 (by rfl) ⟨4628552, by rfl⟩ : syracuseStep 6171403 = 9257105) B9257105
theorem B43297679 : Blo 1500070 43297679 := bstep (se 1 (by rfl) ⟨32473259, by rfl⟩ : syracuseStep 43297679 = 64946519) B64946519
theorem B3378131 : Blo 1500070 3378131 := bstep (se 1 (by rfl) ⟨2533598, by rfl⟩ : syracuseStep 3378131 = 5067197) B5067197
theorem B2534537 : Blo 1500070 2534537 := bstep (se 2 (by rfl) ⟨950451, by rfl⟩ : syracuseStep 2534537 = 1900903) B1900903
theorem B9751735 : Blo 1500070 9751735 := bstep (se 1 (by rfl) ⟨7313801, by rfl⟩ : syracuseStep 9751735 = 14627603) B14627603
theorem B2534591 : Blo 1500070 2534591 := bstep (se 1 (by rfl) ⟨1900943, by rfl⟩ : syracuseStep 2534591 = 3801887) B3801887
theorem B3378401 : Blo 1500070 3378401 := bstep (se 2 (by rfl) ⟨1266900, by rfl⟩ : syracuseStep 3378401 = 2533801) B2533801
theorem B7212361 : Blo 1500070 7212361 := bstep (se 2 (by rfl) ⟨2704635, by rfl⟩ : syracuseStep 7212361 = 5409271) B5409271
theorem B8113645 : Blo 1500070 8113645 := bstep (se 3 (by rfl) ⟨1521308, by rfl⟩ : syracuseStep 8113645 = 3042617) B3042617
theorem B6409961 : Blo 1500070 6409961 := bstep (se 2 (by rfl) ⟨2403735, by rfl⟩ : syracuseStep 6409961 = 4807471) B4807471
theorem B14429947 : Blo 1500070 14429947 := bstep (se 1 (by rfl) ⟨10822460, by rfl⟩ : syracuseStep 14429947 = 21644921) B21644921
theorem B4272031 : Blo 1500070 4272031 := bstep (se 1 (by rfl) ⟨3204023, by rfl⟩ : syracuseStep 4272031 = 6408047) B6408047
theorem B13889531 : Blo 1500070 13889531 := bstep (se 1 (by rfl) ⟨10417148, by rfl⟩ : syracuseStep 13889531 = 20834297) B20834297
theorem B5066873 : Blo 1500070 5066873 := bstep (se 2 (by rfl) ⟨1900077, by rfl⟩ : syracuseStep 5066873 = 3800155) B3800155
theorem B3379463 : Blo 1500070 3379463 := bstep (se 1 (by rfl) ⟨2534597, by rfl⟩ : syracuseStep 3379463 = 5069195) B5069195
theorem B11391353 : Blo 1500070 11391353 := bstep (se 2 (by rfl) ⟨4271757, by rfl⟩ : syracuseStep 11391353 = 8543515) B8543515
theorem B23098223 : Blo 1500070 23098223 := bstep (se 1 (by rfl) ⟨17323667, by rfl⟩ : syracuseStep 23098223 = 34647335) B34647335
theorem B17093591 : Blo 1500070 17093591 := bstep (se 1 (by rfl) ⟨12820193, by rfl⟩ : syracuseStep 17093591 = 25640387) B25640387
theorem B14423183 : Blo 1500070 14423183 := bstep (se 1 (by rfl) ⟨10817387, by rfl⟩ : syracuseStep 14423183 = 21634775) B21634775
theorem B5698745 : Blo 1500070 5698745 := bstep (se 2 (by rfl) ⟨2137029, by rfl⟩ : syracuseStep 5698745 = 4274059) B4274059
theorem B5068061 : Blo 1500070 5068061 := bstep (se 3 (by rfl) ⟨950261, by rfl⟩ : syracuseStep 5068061 = 1900523) B1900523
theorem B37008751 : Blo 1500070 37008751 := bstep (se 1 (by rfl) ⟨27756563, by rfl⟩ : syracuseStep 37008751 = 55513127) B55513127
theorem B2250281 : Blo 1500070 2250281 := bstep (se 2 (by rfl) ⟨843855, by rfl⟩ : syracuseStep 2250281 = 1687711) B1687711
theorem B12334673 : Blo 1500070 12334673 := bstep (se 2 (by rfl) ⟨4625502, by rfl⟩ : syracuseStep 12334673 = 9251005) B9251005
theorem B6944363 : Blo 1500070 6944363 := bstep (se 1 (by rfl) ⟨5208272, by rfl⟩ : syracuseStep 6944363 = 10416545) B10416545
theorem B369882935 : Blo 1500070 369882935 := bstep (se 1 (by rfl) ⟨277412201, by rfl⟩ : syracuseStep 369882935 = 554824403) B554824403
theorem B2250617 : Blo 1500070 2250617 := bstep (se 2 (by rfl) ⟨843981, by rfl⟩ : syracuseStep 2250617 = 1687963) B1687963
theorem B7706927 : Blo 1500070 7706927 := bstep (se 1 (by rfl) ⟨5780195, by rfl⟩ : syracuseStep 7706927 = 11560391) B11560391
theorem B1899055 : Blo 1500070 1899055 := bstep (se 1 (by rfl) ⟨1424291, by rfl⟩ : syracuseStep 1899055 = 2848583) B2848583
theorem B2136631 : Blo 1500070 2136631 := bstep (se 1 (by rfl) ⟨1602473, by rfl⟩ : syracuseStep 2136631 = 3204947) B3204947
theorem B2251391 : Blo 1500070 2251391 := bstep (se 1 (by rfl) ⟨1688543, by rfl⟩ : syracuseStep 2251391 = 3377087) B3377087
theorem B41663251 : Blo 1500070 41663251 := bstep (se 1 (by rfl) ⟨31247438, by rfl⟩ : syracuseStep 41663251 = 62494877) B62494877
theorem B2849593 : Blo 1500070 2849593 := bstep (se 2 (by rfl) ⟨1068597, by rfl⟩ : syracuseStep 2849593 = 2137195) B2137195
theorem B4332523 : Blo 1500070 4332523 := bstep (se 1 (by rfl) ⟨3249392, by rfl⟩ : syracuseStep 4332523 = 6498785) B6498785
theorem B5635451 : Blo 1500070 5635451 := bstep (se 1 (by rfl) ⟨4226588, by rfl⟩ : syracuseStep 5635451 = 8453177) B8453177
theorem B1736239 : Blo 1500070 1736239 := bstep (se 1 (by rfl) ⟨1302179, by rfl⟩ : syracuseStep 1736239 = 2604359) B2604359
theorem B158015123 : Blo 1500070 158015123 := bstep (se 1 (by rfl) ⟨118511342, by rfl⟩ : syracuseStep 158015123 = 237022685) B237022685
theorem B8552263 : Blo 1500070 8552263 := bstep (se 1 (by rfl) ⟨6414197, by rfl⟩ : syracuseStep 8552263 = 12828395) B12828395
theorem B2252975 : Blo 1500070 2252975 := bstep (se 1 (by rfl) ⟨1689731, by rfl⟩ : syracuseStep 2252975 = 3379463) B3379463
theorem B3375287 : Blo 1500070 3375287 := bstep (se 1 (by rfl) ⟨2531465, by rfl⟩ : syracuseStep 3375287 = 5062931) B5062931
theorem B92463353 : Blo 1500070 92463353 := bstep (se 2 (by rfl) ⟨34673757, by rfl⟩ : syracuseStep 92463353 = 69347515) B69347515
theorem B7594235 : Blo 1500070 7594235 := bstep (se 1 (by rfl) ⟨5695676, by rfl⟩ : syracuseStep 7594235 = 11391353) B11391353
theorem B11395727 : Blo 1500070 11395727 := bstep (se 1 (by rfl) ⟨8546795, by rfl⟩ : syracuseStep 11395727 = 17093591) B17093591
theorem B2532073 : Blo 1500070 2532073 := bstep (se 2 (by rfl) ⟨949527, by rfl⟩ : syracuseStep 2532073 = 1899055) B1899055
theorem B1688359 : Blo 1500070 1688359 := bstep (se 1 (by rfl) ⟨1266269, by rfl⟩ : syracuseStep 1688359 = 2532539) B2532539
theorem B55551001 : Blo 1500070 55551001 := bstep (se 2 (by rfl) ⟨20831625, by rfl⟩ : syracuseStep 55551001 = 41663251) B41663251
theorem B1500187 : Blo 1500070 1500187 := bstep (se 1 (by rfl) ⟨1125140, by rfl⟩ : syracuseStep 1500187 = 2250281) B2250281
theorem B4629575 : Blo 1500070 4629575 := bstep (se 1 (by rfl) ⟨3472181, by rfl⟩ : syracuseStep 4629575 = 6944363) B6944363
theorem B3376223 : Blo 1500070 3376223 := bstep (se 1 (by rfl) ⟨2532167, by rfl⟩ : syracuseStep 3376223 = 5064335) B5064335
theorem B246588623 : Blo 1500070 246588623 := bstep (se 1 (by rfl) ⟨184941467, by rfl⟩ : syracuseStep 246588623 = 369882935) B369882935
theorem B5063903 : Blo 1500070 5063903 := bstep (se 1 (by rfl) ⟨3797927, by rfl⟩ : syracuseStep 5063903 = 7595855) B7595855
theorem B1500411 : Blo 1500070 1500411 := bstep (se 1 (by rfl) ⟨1125308, by rfl⟩ : syracuseStep 1500411 = 2250617) B2250617
theorem B5776697 : Blo 1500070 5776697 := bstep (se 2 (by rfl) ⟨2166261, by rfl⟩ : syracuseStep 5776697 = 4332523) B4332523
theorem B5137951 : Blo 1500070 5137951 := bstep (se 1 (by rfl) ⟨3853463, by rfl⟩ : syracuseStep 5137951 = 7706927) B7706927
theorem B1500927 : Blo 1500070 1500927 := bstep (se 1 (by rfl) ⟨1125695, by rfl⟩ : syracuseStep 1500927 = 2251391) B2251391
theorem B1689691 : Blo 1500070 1689691 := bstep (se 1 (by rfl) ⟨1267268, by rfl⟩ : syracuseStep 1689691 = 2534537) B2534537
theorem B1689727 : Blo 1500070 1689727 := bstep (se 1 (by rfl) ⟨1267295, by rfl⟩ : syracuseStep 1689727 = 2534591) B2534591
theorem B105343415 : Blo 1500070 105343415 := bstep (se 1 (by rfl) ⟨79007561, by rfl⟩ : syracuseStep 105343415 = 158015123) B158015123
theorem B5696041 : Blo 1500070 5696041 := bstep (se 2 (by rfl) ⟨2136015, by rfl⟩ : syracuseStep 5696041 = 4272031) B4272031
theorem B9259687 : Blo 1500070 9259687 := bstep (se 1 (by rfl) ⟨6944765, by rfl⟩ : syracuseStep 9259687 = 13889531) B13889531
theorem B1501903 : Blo 1500070 1501903 := bstep (se 1 (by rfl) ⟨1126427, by rfl⟩ : syracuseStep 1501903 = 2252855) B2252855
theorem B64924375 : Blo 1500070 64924375 := bstep (se 1 (by rfl) ⟨48693281, by rfl⟩ : syracuseStep 64924375 = 97386563) B97386563
theorem B12823271 : Blo 1500070 12823271 := bstep (se 1 (by rfl) ⟨9617453, by rfl⟩ : syracuseStep 12823271 = 19234907) B19234907
theorem B3377915 : Blo 1500070 3377915 := bstep (se 1 (by rfl) ⟨2533436, by rfl⟩ : syracuseStep 3377915 = 5066873) B5066873
theorem B1501951 : Blo 1500070 1501951 := bstep (se 1 (by rfl) ⟨1126463, by rfl⟩ : syracuseStep 1501951 = 2252927) B2252927
theorem B5696999 : Blo 1500070 5696999 := bstep (se 1 (by rfl) ⟨4272749, by rfl⟩ : syracuseStep 5696999 = 8545499) B8545499
theorem B3378707 : Blo 1500070 3378707 := bstep (se 1 (by rfl) ⟨2534030, by rfl⟩ : syracuseStep 3378707 = 5068061) B5068061
theorem B15027869 : Blo 1500070 15027869 := bstep (se 3 (by rfl) ⟨2817725, by rfl⟩ : syracuseStep 15027869 = 5635451) B5635451
theorem B8228537 : Blo 1500070 8228537 := bstep (se 2 (by rfl) ⟨3085701, by rfl⟩ : syracuseStep 8228537 = 6171403) B6171403
theorem B49345001 : Blo 1500070 49345001 := bstep (se 2 (by rfl) ⟨18504375, by rfl⟩ : syracuseStep 49345001 = 37008751) B37008751
theorem B28865119 : Blo 1500070 28865119 := bstep (se 1 (by rfl) ⟨21648839, by rfl⟩ : syracuseStep 28865119 = 43297679) B43297679
theorem B10818193 : Blo 1500070 10818193 := bstep (se 2 (by rfl) ⟨4056822, by rfl⟩ : syracuseStep 10818193 = 8113645) B8113645
theorem B2314985 : Blo 1500070 2314985 := bstep (se 2 (by rfl) ⟨868119, by rfl⟩ : syracuseStep 2314985 = 1736239) B1736239
theorem B19239929 : Blo 1500070 19239929 := bstep (se 2 (by rfl) ⟨7214973, by rfl⟩ : syracuseStep 19239929 = 14429947) B14429947
theorem B4273307 : Blo 1500070 4273307 := bstep (se 1 (by rfl) ⟨3204980, by rfl⟩ : syracuseStep 4273307 = 6409961) B6409961
theorem B5068871 : Blo 1500070 5068871 := bstep (se 1 (by rfl) ⟨3801653, by rfl⟩ : syracuseStep 5068871 = 7603307) B7603307
theorem B2848841 : Blo 1500070 2848841 := bstep (se 2 (by rfl) ⟨1068315, by rfl⟩ : syracuseStep 2848841 = 2136631) B2136631
theorem B9615455 : Blo 1500070 9615455 := bstep (se 1 (by rfl) ⟨7211591, by rfl⟩ : syracuseStep 9615455 = 14423183) B14423183
theorem B2250863 : Blo 1500070 2250863 := bstep (se 1 (by rfl) ⟨1688147, by rfl⟩ : syracuseStep 2250863 = 3376295) B3376295
theorem B3799163 : Blo 1500070 3799163 := bstep (se 1 (by rfl) ⟨2849372, by rfl⟩ : syracuseStep 3799163 = 5698745) B5698745
theorem B52009253 : Blo 1500070 52009253 := bstep (se 4 (by rfl) ⟨4875867, by rfl⟩ : syracuseStep 52009253 = 9751735) B9751735
theorem B8223115 : Blo 1500070 8223115 := bstep (se 1 (by rfl) ⟨6167336, by rfl⟩ : syracuseStep 8223115 = 12334673) B12334673
theorem B3799457 : Blo 1500070 3799457 := bstep (se 2 (by rfl) ⟨1424796, by rfl⟩ : syracuseStep 3799457 = 2849593) B2849593
theorem B2251769 : Blo 1500070 2251769 := bstep (se 2 (by rfl) ⟨844413, by rfl⟩ : syracuseStep 2251769 = 1688827) B1688827
theorem B9616481 : Blo 1500070 9616481 := bstep (se 2 (by rfl) ⟨3606180, by rfl⟩ : syracuseStep 9616481 = 7212361) B7212361
theorem B2252087 : Blo 1500070 2252087 := bstep (se 1 (by rfl) ⟨1689065, by rfl⟩ : syracuseStep 2252087 = 3378131) B3378131
theorem B2252267 : Blo 1500070 2252267 := bstep (se 1 (by rfl) ⟨1689200, by rfl⟩ : syracuseStep 2252267 = 3378401) B3378401
theorem B61595261 : Blo 1500070 61595261 := bstep (se 3 (by rfl) ⟨11549111, by rfl⟩ : syracuseStep 61595261 = 23098223) B23098223
theorem B11403017 : Blo 1500070 11403017 := bstep (se 2 (by rfl) ⟨4276131, by rfl⟩ : syracuseStep 11403017 = 8552263) B8552263
theorem B2252681 : Blo 1500070 2252681 := bstep (se 2 (by rfl) ⟨844755, by rfl⟩ : syracuseStep 2252681 = 1689511) B1689511
theorem B2252921 : Blo 1500070 2252921 := bstep (se 2 (by rfl) ⟨844845, by rfl⟩ : syracuseStep 2252921 = 1689691) B1689691
theorem B5062823 : Blo 1500070 5062823 := bstep (se 1 (by rfl) ⟨3797117, by rfl⟩ : syracuseStep 5062823 = 7594235) B7594235
theorem B2252969 : Blo 1500070 2252969 := bstep (se 2 (by rfl) ⟨844863, by rfl⟩ : syracuseStep 2252969 = 1689727) B1689727
theorem B12345533 : Blo 1500070 12345533 := bstep (se 3 (by rfl) ⟨2314787, by rfl⟩ : syracuseStep 12345533 = 4629575) B4629575
theorem B7594721 : Blo 1500070 7594721 := bstep (se 2 (by rfl) ⟨2848020, by rfl⟩ : syracuseStep 7594721 = 5696041) B5696041
theorem B38486825 : Blo 1500070 38486825 := bstep (se 2 (by rfl) ⟨14432559, by rfl⟩ : syracuseStep 38486825 = 28865119) B28865119
theorem B3375935 : Blo 1500070 3375935 := bstep (se 1 (by rfl) ⟨2531951, by rfl⟩ : syracuseStep 3375935 = 5063903) B5063903
theorem B86565833 : Blo 1500070 86565833 := bstep (se 2 (by rfl) ⟨32462187, by rfl⟩ : syracuseStep 86565833 = 64924375) B64924375
theorem B3376097 : Blo 1500070 3376097 := bstep (se 2 (by rfl) ⟨1266036, by rfl⟩ : syracuseStep 3376097 = 2532073) B2532073
theorem B1500575 : Blo 1500070 1500575 := bstep (se 1 (by rfl) ⟨1125431, by rfl⟩ : syracuseStep 1500575 = 2250863) B2250863
theorem B2532775 : Blo 1500070 2532775 := bstep (se 1 (by rfl) ⟨1899581, by rfl⟩ : syracuseStep 2532775 = 3799163) B3799163
theorem B2532971 : Blo 1500070 2532971 := bstep (se 1 (by rfl) ⟨1899728, by rfl⟩ : syracuseStep 2532971 = 3799457) B3799457
theorem B1501179 : Blo 1500070 1501179 := bstep (se 1 (by rfl) ⟨1125884, by rfl⟩ : syracuseStep 1501179 = 2251769) B2251769
theorem B6850601 : Blo 1500070 6850601 := bstep (se 2 (by rfl) ⟨2568975, by rfl⟩ : syracuseStep 6850601 = 5137951) B5137951
theorem B1501391 : Blo 1500070 1501391 := bstep (se 1 (by rfl) ⟨1126043, by rfl⟩ : syracuseStep 1501391 = 2252087) B2252087
theorem B1501511 : Blo 1500070 1501511 := bstep (se 1 (by rfl) ⟨1126133, by rfl⟩ : syracuseStep 1501511 = 2252267) B2252267
theorem B1501787 : Blo 1500070 1501787 := bstep (se 1 (by rfl) ⟨1126340, by rfl⟩ : syracuseStep 1501787 = 2252681) B2252681
theorem B1501983 : Blo 1500070 1501983 := bstep (se 1 (by rfl) ⟨1126487, by rfl⟩ : syracuseStep 1501983 = 2252975) B2252975
theorem B7597151 : Blo 1500070 7597151 := bstep (se 1 (by rfl) ⟨5697863, by rfl⟩ : syracuseStep 7597151 = 11395727) B11395727
theorem B10964153 : Blo 1500070 10964153 := bstep (se 2 (by rfl) ⟨4111557, by rfl⟩ : syracuseStep 10964153 = 8223115) B8223115
theorem B164392415 : Blo 1500070 164392415 := bstep (se 1 (by rfl) ⟨123294311, by rfl⟩ : syracuseStep 164392415 = 246588623) B246588623
theorem B15404525 : Blo 1500070 15404525 := bstep (se 3 (by rfl) ⟨2888348, by rfl⟩ : syracuseStep 15404525 = 5776697) B5776697
theorem B49384997 : Blo 1500070 49384997 := bstep (se 4 (by rfl) ⟨4629843, by rfl⟩ : syracuseStep 49384997 = 9259687) B9259687
theorem B74068001 : Blo 1500070 74068001 := bstep (se 2 (by rfl) ⟨27775500, by rfl⟩ : syracuseStep 74068001 = 55551001) B55551001
theorem B3379247 : Blo 1500070 3379247 := bstep (se 1 (by rfl) ⟨2534435, by rfl⟩ : syracuseStep 3379247 = 5068871) B5068871
theorem B6410303 : Blo 1500070 6410303 := bstep (se 1 (by rfl) ⟨4807727, by rfl⟩ : syracuseStep 6410303 = 9615455) B9615455
theorem B34672835 : Blo 1500070 34672835 := bstep (se 1 (by rfl) ⟨26004626, by rfl⟩ : syracuseStep 34672835 = 52009253) B52009253
theorem B8548847 : Blo 1500070 8548847 := bstep (se 1 (by rfl) ⟨6411635, by rfl⟩ : syracuseStep 8548847 = 12823271) B12823271
theorem B6173293 : Blo 1500070 6173293 := bstep (se 3 (by rfl) ⟨1157492, by rfl⟩ : syracuseStep 6173293 = 2314985) B2314985
theorem B6410987 : Blo 1500070 6410987 := bstep (se 1 (by rfl) ⟨4808240, by rfl⟩ : syracuseStep 6410987 = 9616481) B9616481
theorem B3797999 : Blo 1500070 3797999 := bstep (se 1 (by rfl) ⟨2848499, by rfl⟩ : syracuseStep 3797999 = 5696999) B5696999
theorem B41063507 : Blo 1500070 41063507 := bstep (se 1 (by rfl) ⟨30797630, by rfl⟩ : syracuseStep 41063507 = 61595261) B61595261
theorem B5485691 : Blo 1500070 5485691 := bstep (se 1 (by rfl) ⟨4114268, by rfl⟩ : syracuseStep 5485691 = 8228537) B8228537
theorem B2250191 : Blo 1500070 2250191 := bstep (se 1 (by rfl) ⟨1687643, by rfl⟩ : syracuseStep 2250191 = 3375287) B3375287
theorem B61642235 : Blo 1500070 61642235 := bstep (se 1 (by rfl) ⟨46231676, by rfl⟩ : syracuseStep 61642235 = 92463353) B92463353
theorem B32896667 : Blo 1500070 32896667 := bstep (se 1 (by rfl) ⟨24672500, by rfl⟩ : syracuseStep 32896667 = 49345001) B49345001
theorem B12826619 : Blo 1500070 12826619 := bstep (se 1 (by rfl) ⟨9619964, by rfl⟩ : syracuseStep 12826619 = 19239929) B19239929
theorem B2250815 : Blo 1500070 2250815 := bstep (se 1 (by rfl) ⟨1688111, by rfl⟩ : syracuseStep 2250815 = 3376223) B3376223
theorem B2848871 : Blo 1500070 2848871 := bstep (se 1 (by rfl) ⟨2136653, by rfl⟩ : syracuseStep 2848871 = 4273307) B4273307
theorem B14424257 : Blo 1500070 14424257 := bstep (se 2 (by rfl) ⟨5409096, by rfl⟩ : syracuseStep 14424257 = 10818193) B10818193
theorem B2251145 : Blo 1500070 2251145 := bstep (se 2 (by rfl) ⟨844179, by rfl⟩ : syracuseStep 2251145 = 1688359) B1688359
theorem B1899227 : Blo 1500070 1899227 := bstep (se 1 (by rfl) ⟨1424420, by rfl⟩ : syracuseStep 1899227 = 2848841) B2848841
theorem B70228943 : Blo 1500070 70228943 := bstep (se 1 (by rfl) ⟨52671707, by rfl⟩ : syracuseStep 70228943 = 105343415) B105343415
theorem B2251943 : Blo 1500070 2251943 := bstep (se 1 (by rfl) ⟨1688957, by rfl⟩ : syracuseStep 2251943 = 3377915) B3377915
theorem B2252471 : Blo 1500070 2252471 := bstep (se 1 (by rfl) ⟨1689353, by rfl⟩ : syracuseStep 2252471 = 3378707) B3378707
theorem B10018579 : Blo 1500070 10018579 := bstep (se 1 (by rfl) ⟨7513934, by rfl⟩ : syracuseStep 10018579 = 15027869) B15027869
theorem B7602011 : Blo 1500070 7602011 := bstep (se 1 (by rfl) ⟨5701508, by rfl⟩ : syracuseStep 7602011 = 11403017) B11403017
theorem B2252831 : Blo 1500070 2252831 := bstep (se 1 (by rfl) ⟨1689623, by rfl⟩ : syracuseStep 2252831 = 3379247) B3379247
theorem B3375215 : Blo 1500070 3375215 := bstep (se 1 (by rfl) ⟨2531411, by rfl⟩ : syracuseStep 3375215 = 5062823) B5062823
theorem B5063147 : Blo 1500070 5063147 := bstep (se 1 (by rfl) ⟨3797360, by rfl⟩ : syracuseStep 5063147 = 7594721) B7594721
theorem B25657883 : Blo 1500070 25657883 := bstep (se 1 (by rfl) ⟨19243412, by rfl⟩ : syracuseStep 25657883 = 38486825) B38486825
theorem B2531999 : Blo 1500070 2531999 := bstep (se 1 (by rfl) ⟨1898999, by rfl⟩ : syracuseStep 2531999 = 3797999) B3797999
theorem B1500127 : Blo 1500070 1500127 := bstep (se 1 (by rfl) ⟨1125095, by rfl⟩ : syracuseStep 1500127 = 2250191) B2250191
theorem B1688647 : Blo 1500070 1688647 := bstep (se 1 (by rfl) ⟨1266485, by rfl⟩ : syracuseStep 1688647 = 2532971) B2532971
theorem B21931111 : Blo 1500070 21931111 := bstep (se 1 (by rfl) ⟨16448333, by rfl⟩ : syracuseStep 21931111 = 32896667) B32896667
theorem B1500543 : Blo 1500070 1500543 := bstep (se 1 (by rfl) ⟨1125407, by rfl⟩ : syracuseStep 1500543 = 2250815) B2250815
theorem B1500763 : Blo 1500070 1500763 := bstep (se 1 (by rfl) ⟨1125572, by rfl⟩ : syracuseStep 1500763 = 2251145) B2251145
theorem B3377033 : Blo 1500070 3377033 := bstep (se 2 (by rfl) ⟨1266387, by rfl⟩ : syracuseStep 3377033 = 2532775) B2532775
theorem B5064605 : Blo 1500070 5064605 := bstep (se 3 (by rfl) ⟨949613, by rfl⟩ : syracuseStep 5064605 = 1899227) B1899227
theorem B46819295 : Blo 1500070 46819295 := bstep (se 1 (by rfl) ⟨35114471, by rfl⟩ : syracuseStep 46819295 = 70228943) B70228943
theorem B5064767 : Blo 1500070 5064767 := bstep (se 1 (by rfl) ⟨3798575, by rfl⟩ : syracuseStep 5064767 = 7597151) B7597151
theorem B1501295 : Blo 1500070 1501295 := bstep (se 1 (by rfl) ⟨1125971, by rfl⟩ : syracuseStep 1501295 = 2251943) B2251943
theorem B7309435 : Blo 1500070 7309435 := bstep (se 1 (by rfl) ⟨5482076, by rfl⟩ : syracuseStep 7309435 = 10964153) B10964153
theorem B109594943 : Blo 1500070 109594943 := bstep (se 1 (by rfl) ⟨82196207, by rfl⟩ : syracuseStep 109594943 = 164392415) B164392415
theorem B1501647 : Blo 1500070 1501647 := bstep (se 1 (by rfl) ⟨1126235, by rfl⟩ : syracuseStep 1501647 = 2252471) B2252471
theorem B1501947 : Blo 1500070 1501947 := bstep (se 1 (by rfl) ⟨1126460, by rfl⟩ : syracuseStep 1501947 = 2252921) B2252921
theorem B1501979 : Blo 1500070 1501979 := bstep (se 1 (by rfl) ⟨1126484, by rfl⟩ : syracuseStep 1501979 = 2252969) B2252969
theorem B7596989 : Blo 1500070 7596989 := bstep (se 3 (by rfl) ⟨1424435, by rfl⟩ : syracuseStep 7596989 = 2848871) B2848871
theorem B41094823 : Blo 1500070 41094823 := bstep (se 1 (by rfl) ⟨30821117, by rfl⟩ : syracuseStep 41094823 = 61642235) B61642235
theorem B4567067 : Blo 1500070 4567067 := bstep (se 1 (by rfl) ⟨3425300, by rfl⟩ : syracuseStep 4567067 = 6850601) B6850601
theorem B10269683 : Blo 1500070 10269683 := bstep (se 1 (by rfl) ⟨7702262, by rfl⟩ : syracuseStep 10269683 = 15404525) B15404525
theorem B13358105 : Blo 1500070 13358105 := bstep (se 2 (by rfl) ⟨5009289, by rfl⟩ : syracuseStep 13358105 = 10018579) B10018579
theorem B5068007 : Blo 1500070 5068007 := bstep (se 1 (by rfl) ⟨3801005, by rfl⟩ : syracuseStep 5068007 = 7602011) B7602011
theorem B49378667 : Blo 1500070 49378667 := bstep (se 1 (by rfl) ⟨37034000, by rfl⟩ : syracuseStep 49378667 = 74068001) B74068001
theorem B4273535 : Blo 1500070 4273535 := bstep (se 1 (by rfl) ⟨3205151, by rfl⟩ : syracuseStep 4273535 = 6410303) B6410303
theorem B8230355 : Blo 1500070 8230355 := bstep (se 1 (by rfl) ⟨6172766, by rfl⟩ : syracuseStep 8230355 = 12345533) B12345533
theorem B23115223 : Blo 1500070 23115223 := bstep (se 1 (by rfl) ⟨17336417, by rfl⟩ : syracuseStep 23115223 = 34672835) B34672835
theorem B14628509 : Blo 1500070 14628509 := bstep (se 3 (by rfl) ⟨2742845, by rfl⟩ : syracuseStep 14628509 = 5485691) B5485691
theorem B5699231 : Blo 1500070 5699231 := bstep (se 1 (by rfl) ⟨4274423, by rfl⟩ : syracuseStep 5699231 = 8548847) B8548847
theorem B4273991 : Blo 1500070 4273991 := bstep (se 1 (by rfl) ⟨3205493, by rfl⟩ : syracuseStep 4273991 = 6410987) B6410987
theorem B2250623 : Blo 1500070 2250623 := bstep (se 1 (by rfl) ⟨1687967, by rfl⟩ : syracuseStep 2250623 = 3375935) B3375935
theorem B57710555 : Blo 1500070 57710555 := bstep (se 1 (by rfl) ⟨43282916, by rfl⟩ : syracuseStep 57710555 = 86565833) B86565833
theorem B2250731 : Blo 1500070 2250731 := bstep (se 1 (by rfl) ⟨1688048, by rfl⟩ : syracuseStep 2250731 = 3376097) B3376097
theorem B27375671 : Blo 1500070 27375671 := bstep (se 1 (by rfl) ⟨20531753, by rfl⟩ : syracuseStep 27375671 = 41063507) B41063507
theorem B8231057 : Blo 1500070 8231057 := bstep (se 2 (by rfl) ⟨3086646, by rfl⟩ : syracuseStep 8231057 = 6173293) B6173293
theorem B8551079 : Blo 1500070 8551079 := bstep (se 1 (by rfl) ⟨6413309, by rfl⟩ : syracuseStep 8551079 = 12826619) B12826619
theorem B9616171 : Blo 1500070 9616171 := bstep (se 1 (by rfl) ⟨7212128, by rfl⟩ : syracuseStep 9616171 = 14424257) B14424257
theorem B32923331 : Blo 1500070 32923331 := bstep (se 1 (by rfl) ⟨24692498, by rfl⟩ : syracuseStep 32923331 = 49384997) B49384997
theorem B3375431 : Blo 1500070 3375431 := bstep (se 1 (by rfl) ⟨2531573, by rfl⟩ : syracuseStep 3375431 = 5063147) B5063147
theorem B17105255 : Blo 1500070 17105255 := bstep (se 1 (by rfl) ⟨12828941, by rfl⟩ : syracuseStep 17105255 = 25657883) B25657883
theorem B1687999 : Blo 1500070 1687999 := bstep (se 1 (by rfl) ⟨1265999, by rfl⟩ : syracuseStep 1687999 = 2531999) B2531999
theorem B8905403 : Blo 1500070 8905403 := bstep (se 1 (by rfl) ⟨6679052, by rfl⟩ : syracuseStep 8905403 = 13358105) B13358105
theorem B12821561 : Blo 1500070 12821561 := bstep (se 2 (by rfl) ⟨4808085, by rfl⟩ : syracuseStep 12821561 = 9616171) B9616171
theorem B1500415 : Blo 1500070 1500415 := bstep (se 1 (by rfl) ⟨1125311, by rfl⟩ : syracuseStep 1500415 = 2250623) B2250623
theorem B3376403 : Blo 1500070 3376403 := bstep (se 1 (by rfl) ⟨2532302, by rfl⟩ : syracuseStep 3376403 = 5064605) B5064605
theorem B31212863 : Blo 1500070 31212863 := bstep (se 1 (by rfl) ⟨23409647, by rfl⟩ : syracuseStep 31212863 = 46819295) B46819295
theorem B1500487 : Blo 1500070 1500487 := bstep (se 1 (by rfl) ⟨1125365, by rfl⟩ : syracuseStep 1500487 = 2250731) B2250731
theorem B3376511 : Blo 1500070 3376511 := bstep (se 1 (by rfl) ⟨2532383, by rfl⟩ : syracuseStep 3376511 = 5064767) B5064767
theorem B30820297 : Blo 1500070 30820297 := bstep (se 2 (by rfl) ⟨11557611, by rfl⟩ : syracuseStep 30820297 = 23115223) B23115223
theorem B5064659 : Blo 1500070 5064659 := bstep (se 1 (by rfl) ⟨3798494, by rfl⟩ : syracuseStep 5064659 = 7596989) B7596989
theorem B21948887 : Blo 1500070 21948887 := bstep (se 1 (by rfl) ⟨16461665, by rfl⟩ : syracuseStep 21948887 = 32923331) B32923331
theorem B1501887 : Blo 1500070 1501887 := bstep (se 1 (by rfl) ⟨1126415, by rfl⟩ : syracuseStep 1501887 = 2252831) B2252831
theorem B3378671 : Blo 1500070 3378671 := bstep (se 1 (by rfl) ⟨2534003, by rfl⟩ : syracuseStep 3378671 = 5068007) B5068007
theorem B9752339 : Blo 1500070 9752339 := bstep (se 1 (by rfl) ⟨7314254, by rfl⟩ : syracuseStep 9752339 = 14628509) B14628509
theorem B38473703 : Blo 1500070 38473703 := bstep (se 1 (by rfl) ⟨28855277, by rfl⟩ : syracuseStep 38473703 = 57710555) B57710555
theorem B29241481 : Blo 1500070 29241481 := bstep (se 2 (by rfl) ⟨10965555, by rfl⟩ : syracuseStep 29241481 = 21931111) B21931111
theorem B54793097 : Blo 1500070 54793097 := bstep (se 2 (by rfl) ⟨20547411, by rfl⟩ : syracuseStep 54793097 = 41094823) B41094823
theorem B3044711 : Blo 1500070 3044711 := bstep (se 1 (by rfl) ⟨2283533, by rfl⟩ : syracuseStep 3044711 = 4567067) B4567067
theorem B2250143 : Blo 1500070 2250143 := bstep (se 1 (by rfl) ⟨1687607, by rfl⟩ : syracuseStep 2250143 = 3375215) B3375215
theorem B9745913 : Blo 1500070 9745913 := bstep (se 2 (by rfl) ⟨3654717, by rfl⟩ : syracuseStep 9745913 = 7309435) B7309435
theorem B6846455 : Blo 1500070 6846455 := bstep (se 1 (by rfl) ⟨5134841, by rfl⟩ : syracuseStep 6846455 = 10269683) B10269683
theorem B2849023 : Blo 1500070 2849023 := bstep (se 1 (by rfl) ⟨2136767, by rfl⟩ : syracuseStep 2849023 = 4273535) B4273535
theorem B131676445 : Blo 1500070 131676445 := bstep (se 3 (by rfl) ⟨24689333, by rfl⟩ : syracuseStep 131676445 = 49378667) B49378667
theorem B5486903 : Blo 1500070 5486903 := bstep (se 1 (by rfl) ⟨4115177, by rfl⟩ : syracuseStep 5486903 = 8230355) B8230355
theorem B3799487 : Blo 1500070 3799487 := bstep (se 1 (by rfl) ⟨2849615, by rfl⟩ : syracuseStep 3799487 = 5699231) B5699231
theorem B2849327 : Blo 1500070 2849327 := bstep (se 1 (by rfl) ⟨2136995, by rfl⟩ : syracuseStep 2849327 = 4273991) B4273991
theorem B2251355 : Blo 1500070 2251355 := bstep (se 1 (by rfl) ⟨1688516, by rfl⟩ : syracuseStep 2251355 = 3377033) B3377033
theorem B18250447 : Blo 1500070 18250447 := bstep (se 1 (by rfl) ⟨13687835, by rfl⟩ : syracuseStep 18250447 = 27375671) B27375671
theorem B2251529 : Blo 1500070 2251529 := bstep (se 2 (by rfl) ⟨844323, by rfl⟩ : syracuseStep 2251529 = 1688647) B1688647
theorem B5487371 : Blo 1500070 5487371 := bstep (se 1 (by rfl) ⟨4115528, by rfl⟩ : syracuseStep 5487371 = 8231057) B8231057
theorem B73063295 : Blo 1500070 73063295 := bstep (se 1 (by rfl) ⟨54797471, by rfl⟩ : syracuseStep 73063295 = 109594943) B109594943
theorem B5700719 : Blo 1500070 5700719 := bstep (se 1 (by rfl) ⟨4275539, by rfl⟩ : syracuseStep 5700719 = 8551079) B8551079
theorem B11403503 : Blo 1500070 11403503 := bstep (se 1 (by rfl) ⟨8552627, by rfl⟩ : syracuseStep 11403503 = 17105255) B17105255
theorem B36528731 : Blo 1500070 36528731 := bstep (se 1 (by rfl) ⟨27396548, by rfl⟩ : syracuseStep 36528731 = 54793097) B54793097
theorem B20808575 : Blo 1500070 20808575 := bstep (se 1 (by rfl) ⟨15606431, by rfl⟩ : syracuseStep 20808575 = 31212863) B31212863
theorem B1500095 : Blo 1500070 1500095 := bstep (se 1 (by rfl) ⟨1125071, by rfl⟩ : syracuseStep 1500095 = 2250143) B2250143
theorem B3376439 : Blo 1500070 3376439 := bstep (se 1 (by rfl) ⟨2532329, by rfl⟩ : syracuseStep 3376439 = 5064659) B5064659
theorem B2532991 : Blo 1500070 2532991 := bstep (se 1 (by rfl) ⟨1899743, by rfl⟩ : syracuseStep 2532991 = 3799487) B3799487
theorem B14632591 : Blo 1500070 14632591 := bstep (se 1 (by rfl) ⟨10974443, by rfl⟩ : syracuseStep 14632591 = 21948887) B21948887
theorem B1500903 : Blo 1500070 1500903 := bstep (se 1 (by rfl) ⟨1125677, by rfl⟩ : syracuseStep 1500903 = 2251355) B2251355
theorem B1501019 : Blo 1500070 1501019 := bstep (se 1 (by rfl) ⟨1125764, by rfl⟩ : syracuseStep 1501019 = 2251529) B2251529
theorem B41093729 : Blo 1500070 41093729 := bstep (se 2 (by rfl) ⟨15410148, by rfl⟩ : syracuseStep 41093729 = 30820297) B30820297
theorem B38988641 : Blo 1500070 38988641 := bstep (se 2 (by rfl) ⟨14620740, by rfl⟩ : syracuseStep 38988641 = 29241481) B29241481
theorem B8547707 : Blo 1500070 8547707 := bstep (se 1 (by rfl) ⟨6410780, by rfl⟩ : syracuseStep 8547707 = 12821561) B12821561
theorem B24333929 : Blo 1500070 24333929 := bstep (se 2 (by rfl) ⟨9125223, by rfl⟩ : syracuseStep 24333929 = 18250447) B18250447
theorem B25989101 : Blo 1500070 25989101 := bstep (se 3 (by rfl) ⟨4872956, by rfl⟩ : syracuseStep 25989101 = 9745913) B9745913
theorem B3657935 : Blo 1500070 3657935 := bstep (se 1 (by rfl) ⟨2743451, by rfl⟩ : syracuseStep 3657935 = 5486903) B5486903
theorem B3658247 : Blo 1500070 3658247 := bstep (se 1 (by rfl) ⟨2743685, by rfl⟩ : syracuseStep 3658247 = 5487371) B5487371
theorem B6501559 : Blo 1500070 6501559 := bstep (se 1 (by rfl) ⟨4876169, by rfl⟩ : syracuseStep 6501559 = 9752339) B9752339
theorem B18257213 : Blo 1500070 18257213 := bstep (se 3 (by rfl) ⟨3423227, by rfl⟩ : syracuseStep 18257213 = 6846455) B6846455
theorem B2250287 : Blo 1500070 2250287 := bstep (se 1 (by rfl) ⟨1687715, by rfl⟩ : syracuseStep 2250287 = 3375431) B3375431
theorem B3798697 : Blo 1500070 3798697 := bstep (se 2 (by rfl) ⟨1424511, by rfl⟩ : syracuseStep 3798697 = 2849023) B2849023
theorem B5936935 : Blo 1500070 5936935 := bstep (se 1 (by rfl) ⟨4452701, by rfl⟩ : syracuseStep 5936935 = 8905403) B8905403
theorem B2250665 : Blo 1500070 2250665 := bstep (se 2 (by rfl) ⟨843999, by rfl⟩ : syracuseStep 2250665 = 1687999) B1687999
theorem B2250935 : Blo 1500070 2250935 := bstep (se 1 (by rfl) ⟨1688201, by rfl⟩ : syracuseStep 2250935 = 3376403) B3376403
theorem B2029807 : Blo 1500070 2029807 := bstep (se 1 (by rfl) ⟨1522355, by rfl⟩ : syracuseStep 2029807 = 3044711) B3044711
theorem B2251007 : Blo 1500070 2251007 := bstep (se 1 (by rfl) ⟨1688255, by rfl⟩ : syracuseStep 2251007 = 3376511) B3376511
theorem B702274373 : Blo 1500070 702274373 := bstep (se 4 (by rfl) ⟨65838222, by rfl⟩ : syracuseStep 702274373 = 131676445) B131676445
theorem B1899551 : Blo 1500070 1899551 := bstep (se 1 (by rfl) ⟨1424663, by rfl⟩ : syracuseStep 1899551 = 2849327) B2849327
theorem B48708863 : Blo 1500070 48708863 := bstep (se 1 (by rfl) ⟨36531647, by rfl⟩ : syracuseStep 48708863 = 73063295) B73063295
theorem B3800479 : Blo 1500070 3800479 := bstep (se 1 (by rfl) ⟨2850359, by rfl⟩ : syracuseStep 3800479 = 5700719) B5700719
theorem B2252447 : Blo 1500070 2252447 := bstep (se 1 (by rfl) ⟨1689335, by rfl⟩ : syracuseStep 2252447 = 3378671) B3378671
theorem B25649135 : Blo 1500070 25649135 := bstep (se 1 (by rfl) ⟨19236851, by rfl⟩ : syracuseStep 25649135 = 38473703) B38473703
theorem B7602335 : Blo 1500070 7602335 := bstep (se 1 (by rfl) ⟨5701751, by rfl⟩ : syracuseStep 7602335 = 11403503) B11403503
theorem B1500191 : Blo 1500070 1500191 := bstep (se 1 (by rfl) ⟨1125143, by rfl⟩ : syracuseStep 1500191 = 2250287) B2250287
theorem B1500443 : Blo 1500070 1500443 := bstep (se 1 (by rfl) ⟨1125332, by rfl⟩ : syracuseStep 1500443 = 2250665) B2250665
theorem B1500623 : Blo 1500070 1500623 := bstep (se 1 (by rfl) ⟨1125467, by rfl⟩ : syracuseStep 1500623 = 2250935) B2250935
theorem B1500671 : Blo 1500070 1500671 := bstep (se 1 (by rfl) ⟨1125503, by rfl⟩ : syracuseStep 1500671 = 2251007) B2251007
theorem B8668745 : Blo 1500070 8668745 := bstep (se 2 (by rfl) ⟨3250779, by rfl⟩ : syracuseStep 8668745 = 6501559) B6501559
theorem B27395819 : Blo 1500070 27395819 := bstep (se 1 (by rfl) ⟨20546864, by rfl⟩ : syracuseStep 27395819 = 41093729) B41093729
theorem B468182915 : Blo 1500070 468182915 := bstep (se 1 (by rfl) ⟨351137186, by rfl⟩ : syracuseStep 468182915 = 702274373) B702274373
theorem B3377321 : Blo 1500070 3377321 := bstep (se 2 (by rfl) ⟨1266495, by rfl⟩ : syracuseStep 3377321 = 2532991) B2532991
theorem B5064929 : Blo 1500070 5064929 := bstep (se 2 (by rfl) ⟨1899348, by rfl⟩ : syracuseStep 5064929 = 3798697) B3798697
theorem B7915913 : Blo 1500070 7915913 := bstep (se 2 (by rfl) ⟨2968467, by rfl⟩ : syracuseStep 7915913 = 5936935) B5936935
theorem B16222619 : Blo 1500070 16222619 := bstep (se 1 (by rfl) ⟨12166964, by rfl⟩ : syracuseStep 16222619 = 24333929) B24333929
theorem B1501631 : Blo 1500070 1501631 := bstep (se 1 (by rfl) ⟨1126223, by rfl⟩ : syracuseStep 1501631 = 2252447) B2252447
theorem B17099423 : Blo 1500070 17099423 := bstep (se 1 (by rfl) ⟨12824567, by rfl⟩ : syracuseStep 17099423 = 25649135) B25649135
theorem B5065469 : Blo 1500070 5065469 := bstep (se 3 (by rfl) ⟨949775, by rfl⟩ : syracuseStep 5065469 = 1899551) B1899551
theorem B2706409 : Blo 1500070 2706409 := bstep (se 2 (by rfl) ⟨1014903, by rfl⟩ : syracuseStep 2706409 = 2029807) B2029807
theorem B13872383 : Blo 1500070 13872383 := bstep (se 1 (by rfl) ⟨10404287, by rfl⟩ : syracuseStep 13872383 = 20808575) B20808575
theorem B5067305 : Blo 1500070 5067305 := bstep (se 2 (by rfl) ⟨1900239, by rfl⟩ : syracuseStep 5067305 = 3800479) B3800479
theorem B19510121 : Blo 1500070 19510121 := bstep (se 2 (by rfl) ⟨7316295, by rfl⟩ : syracuseStep 19510121 = 14632591) B14632591
theorem B5698471 : Blo 1500070 5698471 := bstep (se 1 (by rfl) ⟨4273853, by rfl⟩ : syracuseStep 5698471 = 8547707) B8547707
theorem B2438623 : Blo 1500070 2438623 := bstep (se 1 (by rfl) ⟨1828967, by rfl⟩ : syracuseStep 2438623 = 3657935) B3657935
theorem B2438831 : Blo 1500070 2438831 := bstep (se 1 (by rfl) ⟨1829123, by rfl⟩ : syracuseStep 2438831 = 3658247) B3658247
theorem B24352487 : Blo 1500070 24352487 := bstep (se 1 (by rfl) ⟨18264365, by rfl⟩ : syracuseStep 24352487 = 36528731) B36528731
theorem B2250959 : Blo 1500070 2250959 := bstep (se 1 (by rfl) ⟨1688219, by rfl⟩ : syracuseStep 2250959 = 3376439) B3376439
theorem B12171475 : Blo 1500070 12171475 := bstep (se 1 (by rfl) ⟨9128606, by rfl⟩ : syracuseStep 12171475 = 18257213) B18257213
theorem B25992427 : Blo 1500070 25992427 := bstep (se 1 (by rfl) ⟨19494320, by rfl⟩ : syracuseStep 25992427 = 38988641) B38988641
theorem B32472575 : Blo 1500070 32472575 := bstep (se 1 (by rfl) ⟨24354431, by rfl⟩ : syracuseStep 32472575 = 48708863) B48708863
theorem B17326067 : Blo 1500070 17326067 := bstep (se 1 (by rfl) ⟨12994550, by rfl⟩ : syracuseStep 17326067 = 25989101) B25989101
theorem B64914533 : Blo 1500070 64914533 := bstep (se 4 (by rfl) ⟨6085737, by rfl⟩ : syracuseStep 64914533 = 12171475) B12171475
theorem B1500639 : Blo 1500070 1500639 := bstep (se 1 (by rfl) ⟨1125479, by rfl⟩ : syracuseStep 1500639 = 2250959) B2250959
theorem B3376619 : Blo 1500070 3376619 := bstep (se 1 (by rfl) ⟨2532464, by rfl⟩ : syracuseStep 3376619 = 5064929) B5064929
theorem B5277275 : Blo 1500070 5277275 := bstep (se 1 (by rfl) ⟨3957956, by rfl⟩ : syracuseStep 5277275 = 7915913) B7915913
theorem B3376979 : Blo 1500070 3376979 := bstep (se 1 (by rfl) ⟨2532734, by rfl⟩ : syracuseStep 3376979 = 5065469) B5065469
theorem B3378203 : Blo 1500070 3378203 := bstep (se 1 (by rfl) ⟨2533652, by rfl⟩ : syracuseStep 3378203 = 5067305) B5067305
theorem B5779163 : Blo 1500070 5779163 := bstep (se 1 (by rfl) ⟨4334372, by rfl⟩ : syracuseStep 5779163 = 8668745) B8668745
theorem B1625887 : Blo 1500070 1625887 := bstep (se 1 (by rfl) ⟨1219415, by rfl⟩ : syracuseStep 1625887 = 2438831) B2438831
theorem B18263879 : Blo 1500070 18263879 := bstep (se 1 (by rfl) ⟨13697909, by rfl⟩ : syracuseStep 18263879 = 27395819) B27395819
theorem B7597961 : Blo 1500070 7597961 := bstep (se 2 (by rfl) ⟨2849235, by rfl⟩ : syracuseStep 7597961 = 5698471) B5698471
theorem B3608545 : Blo 1500070 3608545 := bstep (se 2 (by rfl) ⟨1353204, by rfl⟩ : syracuseStep 3608545 = 2706409) B2706409
theorem B34656569 : Blo 1500070 34656569 := bstep (se 2 (by rfl) ⟨12996213, by rfl⟩ : syracuseStep 34656569 = 25992427) B25992427
theorem B11399615 : Blo 1500070 11399615 := bstep (se 1 (by rfl) ⟨8549711, by rfl⟩ : syracuseStep 11399615 = 17099423) B17099423
theorem B21648383 : Blo 1500070 21648383 := bstep (se 1 (by rfl) ⟨16236287, by rfl⟩ : syracuseStep 21648383 = 32472575) B32472575
theorem B5068223 : Blo 1500070 5068223 := bstep (se 1 (by rfl) ⟨3801167, by rfl⟩ : syracuseStep 5068223 = 7602335) B7602335
theorem B13006747 : Blo 1500070 13006747 := bstep (se 1 (by rfl) ⟨9755060, by rfl⟩ : syracuseStep 13006747 = 19510121) B19510121
theorem B43260317 : Blo 1500070 43260317 := bstep (se 3 (by rfl) ⟨8111309, by rfl⟩ : syracuseStep 43260317 = 16222619) B16222619
theorem B16234991 : Blo 1500070 16234991 := bstep (se 1 (by rfl) ⟨12176243, by rfl⟩ : syracuseStep 16234991 = 24352487) B24352487
theorem B312121943 : Blo 1500070 312121943 := bstep (se 1 (by rfl) ⟨234091457, by rfl⟩ : syracuseStep 312121943 = 468182915) B468182915
theorem B2251547 : Blo 1500070 2251547 := bstep (se 1 (by rfl) ⟨1688660, by rfl⟩ : syracuseStep 2251547 = 3377321) B3377321
theorem B3251497 : Blo 1500070 3251497 := bstep (se 2 (by rfl) ⟨1219311, by rfl⟩ : syracuseStep 3251497 = 2438623) B2438623
theorem B9248255 : Blo 1500070 9248255 := bstep (se 1 (by rfl) ⟨6936191, by rfl⟩ : syracuseStep 9248255 = 13872383) B13872383
theorem B46202845 : Blo 1500070 46202845 := bstep (se 3 (by rfl) ⟨8663033, by rfl⟩ : syracuseStep 46202845 = 17326067) B17326067
theorem B10823327 : Blo 1500070 10823327 := bstep (se 1 (by rfl) ⟨8117495, by rfl⟩ : syracuseStep 10823327 = 16234991) B16234991
theorem B4335329 : Blo 1500070 4335329 := bstep (se 2 (by rfl) ⟨1625748, by rfl⟩ : syracuseStep 4335329 = 3251497) B3251497
theorem B1501031 : Blo 1500070 1501031 := bstep (se 1 (by rfl) ⟨1125773, by rfl⟩ : syracuseStep 1501031 = 2251547) B2251547
theorem B3852775 : Blo 1500070 3852775 := bstep (se 1 (by rfl) ⟨2889581, by rfl⟩ : syracuseStep 3852775 = 5779163) B5779163
theorem B12175919 : Blo 1500070 12175919 := bstep (se 1 (by rfl) ⟨9131939, by rfl⟩ : syracuseStep 12175919 = 18263879) B18263879
theorem B5065307 : Blo 1500070 5065307 := bstep (se 1 (by rfl) ⟨3798980, by rfl⟩ : syracuseStep 5065307 = 7597961) B7597961
theorem B4811393 : Blo 1500070 4811393 := bstep (se 2 (by rfl) ⟨1804272, by rfl⟩ : syracuseStep 4811393 = 3608545) B3608545
theorem B23104379 : Blo 1500070 23104379 := bstep (se 1 (by rfl) ⟨17328284, by rfl⟩ : syracuseStep 23104379 = 34656569) B34656569
theorem B3378815 : Blo 1500070 3378815 := bstep (se 1 (by rfl) ⟨2534111, by rfl⟩ : syracuseStep 3378815 = 5068223) B5068223
theorem B3518183 : Blo 1500070 3518183 := bstep (se 1 (by rfl) ⟨2638637, by rfl⟩ : syracuseStep 3518183 = 5277275) B5277275
theorem B28840211 : Blo 1500070 28840211 := bstep (se 1 (by rfl) ⟨21630158, by rfl⟩ : syracuseStep 28840211 = 43260317) B43260317
theorem B208081295 : Blo 1500070 208081295 := bstep (se 1 (by rfl) ⟨156060971, by rfl⟩ : syracuseStep 208081295 = 312121943) B312121943
theorem B6165503 : Blo 1500070 6165503 := bstep (se 1 (by rfl) ⟨4624127, by rfl⟩ : syracuseStep 6165503 = 9248255) B9248255
theorem B2167849 : Blo 1500070 2167849 := bstep (se 2 (by rfl) ⟨812943, by rfl⟩ : syracuseStep 2167849 = 1625887) B1625887
theorem B7599743 : Blo 1500070 7599743 := bstep (se 1 (by rfl) ⟨5699807, by rfl⟩ : syracuseStep 7599743 = 11399615) B11399615
theorem B14432255 : Blo 1500070 14432255 := bstep (se 1 (by rfl) ⟨10824191, by rfl⟩ : syracuseStep 14432255 = 21648383) B21648383
theorem B43276355 : Blo 1500070 43276355 := bstep (se 1 (by rfl) ⟨32457266, by rfl⟩ : syracuseStep 43276355 = 64914533) B64914533
theorem B2251079 : Blo 1500070 2251079 := bstep (se 1 (by rfl) ⟨1688309, by rfl⟩ : syracuseStep 2251079 = 3376619) B3376619
theorem B2251319 : Blo 1500070 2251319 := bstep (se 1 (by rfl) ⟨1688489, by rfl⟩ : syracuseStep 2251319 = 3376979) B3376979
theorem B2252135 : Blo 1500070 2252135 := bstep (se 1 (by rfl) ⟨1689101, by rfl⟩ : syracuseStep 2252135 = 3378203) B3378203
theorem B69369317 : Blo 1500070 69369317 := bstep (se 4 (by rfl) ⟨6503373, by rfl⟩ : syracuseStep 69369317 = 13006747) B13006747
theorem B61603793 : Blo 1500070 61603793 := bstep (se 2 (by rfl) ⟨23101422, by rfl⟩ : syracuseStep 61603793 = 46202845) B46202845
theorem B19226807 : Blo 1500070 19226807 := bstep (se 1 (by rfl) ⟨14420105, by rfl⟩ : syracuseStep 19226807 = 28840211) B28840211
theorem B5137033 : Blo 1500070 5137033 := bstep (se 2 (by rfl) ⟨1926387, by rfl⟩ : syracuseStep 5137033 = 3852775) B3852775
theorem B1500719 : Blo 1500070 1500719 := bstep (se 1 (by rfl) ⟨1125539, by rfl⟩ : syracuseStep 1500719 = 2251079) B2251079
theorem B1500879 : Blo 1500070 1500879 := bstep (se 1 (by rfl) ⟨1125659, by rfl⟩ : syracuseStep 1500879 = 2251319) B2251319
theorem B3376871 : Blo 1500070 3376871 := bstep (se 1 (by rfl) ⟨2532653, by rfl⟩ : syracuseStep 3376871 = 5065307) B5065307
theorem B1501423 : Blo 1500070 1501423 := bstep (se 1 (by rfl) ⟨1126067, by rfl⟩ : syracuseStep 1501423 = 2252135) B2252135
theorem B46246211 : Blo 1500070 46246211 := bstep (se 1 (by rfl) ⟨34684658, by rfl⟩ : syracuseStep 46246211 = 69369317) B69369317
theorem B2345455 : Blo 1500070 2345455 := bstep (se 1 (by rfl) ⟨1759091, by rfl⟩ : syracuseStep 2345455 = 3518183) B3518183
theorem B41069195 : Blo 1500070 41069195 := bstep (se 1 (by rfl) ⟨30801896, by rfl⟩ : syracuseStep 41069195 = 61603793) B61603793
theorem B11561861 : Blo 1500070 11561861 := bstep (se 4 (by rfl) ⟨1083924, by rfl⟩ : syracuseStep 11561861 = 2167849) B2167849
theorem B5066495 : Blo 1500070 5066495 := bstep (se 1 (by rfl) ⟨3799871, by rfl⟩ : syracuseStep 5066495 = 7599743) B7599743
theorem B9621503 : Blo 1500070 9621503 := bstep (se 1 (by rfl) ⟨7216127, by rfl⟩ : syracuseStep 9621503 = 14432255) B14432255
theorem B3207595 : Blo 1500070 3207595 := bstep (se 1 (by rfl) ⟨2405696, by rfl⟩ : syracuseStep 3207595 = 4811393) B4811393
theorem B138720863 : Blo 1500070 138720863 := bstep (se 1 (by rfl) ⟨104040647, by rfl⟩ : syracuseStep 138720863 = 208081295) B208081295
theorem B4110335 : Blo 1500070 4110335 := bstep (se 1 (by rfl) ⟨3082751, by rfl⟩ : syracuseStep 4110335 = 6165503) B6165503
theorem B7215551 : Blo 1500070 7215551 := bstep (se 1 (by rfl) ⟨5411663, by rfl⟩ : syracuseStep 7215551 = 10823327) B10823327
theorem B2890219 : Blo 1500070 2890219 := bstep (se 1 (by rfl) ⟨2167664, by rfl⟩ : syracuseStep 2890219 = 4335329) B4335329
theorem B28850903 : Blo 1500070 28850903 := bstep (se 1 (by rfl) ⟨21638177, by rfl⟩ : syracuseStep 28850903 = 43276355) B43276355
theorem B8117279 : Blo 1500070 8117279 := bstep (se 1 (by rfl) ⟨6087959, by rfl⟩ : syracuseStep 8117279 = 12175919) B12175919
theorem B61611677 : Blo 1500070 61611677 := bstep (se 3 (by rfl) ⟨11552189, by rfl⟩ : syracuseStep 61611677 = 23104379) B23104379
theorem B2252543 : Blo 1500070 2252543 := bstep (se 1 (by rfl) ⟨1689407, by rfl⟩ : syracuseStep 2252543 = 3378815) B3378815
theorem B4276793 : Blo 1500070 4276793 := bstep (se 2 (by rfl) ⟨1603797, by rfl⟩ : syracuseStep 4276793 = 3207595) B3207595
theorem B6849377 : Blo 1500070 6849377 := bstep (se 2 (by rfl) ⟨2568516, by rfl⟩ : syracuseStep 6849377 = 5137033) B5137033
theorem B92480575 : Blo 1500070 92480575 := bstep (se 1 (by rfl) ⟨69360431, by rfl⟩ : syracuseStep 92480575 = 138720863) B138720863
theorem B4810367 : Blo 1500070 4810367 := bstep (se 1 (by rfl) ⟨3607775, by rfl⟩ : syracuseStep 4810367 = 7215551) B7215551
theorem B27379463 : Blo 1500070 27379463 := bstep (se 1 (by rfl) ⟨20534597, by rfl⟩ : syracuseStep 27379463 = 41069195) B41069195
theorem B3377663 : Blo 1500070 3377663 := bstep (se 1 (by rfl) ⟨2533247, by rfl⟩ : syracuseStep 3377663 = 5066495) B5066495
theorem B1501695 : Blo 1500070 1501695 := bstep (se 1 (by rfl) ⟨1126271, by rfl⟩ : syracuseStep 1501695 = 2252543) B2252543
theorem B3853625 : Blo 1500070 3853625 := bstep (se 2 (by rfl) ⟨1445109, by rfl⟩ : syracuseStep 3853625 = 2890219) B2890219
theorem B6414335 : Blo 1500070 6414335 := bstep (se 1 (by rfl) ⟨4810751, by rfl⟩ : syracuseStep 6414335 = 9621503) B9621503
theorem B2740223 : Blo 1500070 2740223 := bstep (se 1 (by rfl) ⟨2055167, by rfl⟩ : syracuseStep 2740223 = 4110335) B4110335
theorem B30830807 : Blo 1500070 30830807 := bstep (se 1 (by rfl) ⟨23123105, by rfl⟩ : syracuseStep 30830807 = 46246211) B46246211
theorem B5411519 : Blo 1500070 5411519 := bstep (se 1 (by rfl) ⟨4058639, by rfl⟩ : syracuseStep 5411519 = 8117279) B8117279
theorem B12817871 : Blo 1500070 12817871 := bstep (se 1 (by rfl) ⟨9613403, by rfl⟩ : syracuseStep 12817871 = 19226807) B19226807
theorem B2251247 : Blo 1500070 2251247 := bstep (se 1 (by rfl) ⟨1688435, by rfl⟩ : syracuseStep 2251247 = 3376871) B3376871
theorem B19233935 : Blo 1500070 19233935 := bstep (se 1 (by rfl) ⟨14425451, by rfl⟩ : syracuseStep 19233935 = 28850903) B28850903
theorem B7707907 : Blo 1500070 7707907 := bstep (se 1 (by rfl) ⟨5780930, by rfl⟩ : syracuseStep 7707907 = 11561861) B11561861
theorem B41074451 : Blo 1500070 41074451 := bstep (se 1 (by rfl) ⟨30805838, by rfl⟩ : syracuseStep 41074451 = 61611677) B61611677
theorem B12509093 : Blo 1500070 12509093 := bstep (se 4 (by rfl) ⟨1172727, by rfl⟩ : syracuseStep 12509093 = 2345455) B2345455
theorem B20553871 : Blo 1500070 20553871 := bstep (se 1 (by rfl) ⟨15415403, by rfl⟩ : syracuseStep 20553871 = 30830807) B30830807
theorem B2851195 : Blo 1500070 2851195 := bstep (se 1 (by rfl) ⟨2138396, by rfl⟩ : syracuseStep 2851195 = 4276793) B4276793
theorem B8545247 : Blo 1500070 8545247 := bstep (se 1 (by rfl) ⟨6408935, by rfl⟩ : syracuseStep 8545247 = 12817871) B12817871
theorem B123307433 : Blo 1500070 123307433 := bstep (se 2 (by rfl) ⟨46240287, by rfl⟩ : syracuseStep 123307433 = 92480575) B92480575
theorem B1500831 : Blo 1500070 1500831 := bstep (se 1 (by rfl) ⟨1125623, by rfl⟩ : syracuseStep 1500831 = 2251247) B2251247
theorem B12822623 : Blo 1500070 12822623 := bstep (se 1 (by rfl) ⟨9616967, by rfl⟩ : syracuseStep 12822623 = 19233935) B19233935
theorem B4276223 : Blo 1500070 4276223 := bstep (se 1 (by rfl) ⟨3207167, by rfl⟩ : syracuseStep 4276223 = 6414335) B6414335
theorem B3607679 : Blo 1500070 3607679 := bstep (se 1 (by rfl) ⟨2705759, by rfl⟩ : syracuseStep 3607679 = 5411519) B5411519
theorem B4566251 : Blo 1500070 4566251 := bstep (se 1 (by rfl) ⟨3424688, by rfl⟩ : syracuseStep 4566251 = 6849377) B6849377
theorem B10277209 : Blo 1500070 10277209 := bstep (se 2 (by rfl) ⟨3853953, by rfl⟩ : syracuseStep 10277209 = 7707907) B7707907
theorem B73011901 : Blo 1500070 73011901 := bstep (se 3 (by rfl) ⟨13689731, by rfl⟩ : syracuseStep 73011901 = 27379463) B27379463
theorem B27382967 : Blo 1500070 27382967 := bstep (se 1 (by rfl) ⟨20537225, by rfl⟩ : syracuseStep 27382967 = 41074451) B41074451
theorem B41105333 : Blo 1500070 41105333 := bstep (se 5 (by rfl) ⟨1926812, by rfl⟩ : syracuseStep 41105333 = 3853625) B3853625
theorem B12827645 : Blo 1500070 12827645 := bstep (se 3 (by rfl) ⟨2405183, by rfl⟩ : syracuseStep 12827645 = 4810367) B4810367
theorem B2251775 : Blo 1500070 2251775 := bstep (se 1 (by rfl) ⟨1688831, by rfl⟩ : syracuseStep 2251775 = 3377663) B3377663
theorem B33357581 : Blo 1500070 33357581 := bstep (se 3 (by rfl) ⟨6254546, by rfl⟩ : syracuseStep 33357581 = 12509093) B12509093
theorem B1826815 : Blo 1500070 1826815 := bstep (se 1 (by rfl) ⟨1370111, by rfl⟩ : syracuseStep 1826815 = 2740223) B2740223
theorem B3801593 : Blo 1500070 3801593 := bstep (se 2 (by rfl) ⟨1425597, by rfl⟩ : syracuseStep 3801593 = 2851195) B2851195
theorem B27403555 : Blo 1500070 27403555 := bstep (se 1 (by rfl) ⟨20552666, by rfl⟩ : syracuseStep 27403555 = 41105333) B41105333
theorem B1501183 : Blo 1500070 1501183 := bstep (se 1 (by rfl) ⟨1125887, by rfl⟩ : syracuseStep 1501183 = 2251775) B2251775
theorem B2435753 : Blo 1500070 2435753 := bstep (se 2 (by rfl) ⟨913407, by rfl⟩ : syracuseStep 2435753 = 1826815) B1826815
theorem B27405161 : Blo 1500070 27405161 := bstep (se 2 (by rfl) ⟨10276935, by rfl⟩ : syracuseStep 27405161 = 20553871) B20553871
theorem B9620477 : Blo 1500070 9620477 := bstep (se 3 (by rfl) ⟨1803839, by rfl⟩ : syracuseStep 9620477 = 3607679) B3607679
theorem B12176669 : Blo 1500070 12176669 := bstep (se 3 (by rfl) ⟨2283125, by rfl⟩ : syracuseStep 12176669 = 4566251) B4566251
theorem B5696831 : Blo 1500070 5696831 := bstep (se 1 (by rfl) ⟨4272623, by rfl⟩ : syracuseStep 5696831 = 8545247) B8545247
theorem B18255311 : Blo 1500070 18255311 := bstep (se 1 (by rfl) ⟨13691483, by rfl⟩ : syracuseStep 18255311 = 27382967) B27382967
theorem B97349201 : Blo 1500070 97349201 := bstep (se 2 (by rfl) ⟨36505950, by rfl⟩ : syracuseStep 97349201 = 73011901) B73011901
theorem B8548415 : Blo 1500070 8548415 := bstep (se 1 (by rfl) ⟨6411311, by rfl⟩ : syracuseStep 8548415 = 12822623) B12822623
theorem B22238387 : Blo 1500070 22238387 := bstep (se 1 (by rfl) ⟨16678790, by rfl⟩ : syracuseStep 22238387 = 33357581) B33357581
theorem B13702945 : Blo 1500070 13702945 := bstep (se 2 (by rfl) ⟨5138604, by rfl⟩ : syracuseStep 13702945 = 10277209) B10277209
theorem B82204955 : Blo 1500070 82204955 := bstep (se 1 (by rfl) ⟨61653716, by rfl⟩ : syracuseStep 82204955 = 123307433) B123307433
theorem B2850815 : Blo 1500070 2850815 := bstep (se 1 (by rfl) ⟨2138111, by rfl⟩ : syracuseStep 2850815 = 4276223) B4276223
theorem B8551763 : Blo 1500070 8551763 := bstep (se 1 (by rfl) ⟨6413822, by rfl⟩ : syracuseStep 8551763 = 12827645) B12827645
theorem B36538073 : Blo 1500070 36538073 := bstep (se 2 (by rfl) ⟨13701777, by rfl⟩ : syracuseStep 36538073 = 27403555) B27403555
theorem B1623835 : Blo 1500070 1623835 := bstep (se 1 (by rfl) ⟨1217876, by rfl⟩ : syracuseStep 1623835 = 2435753) B2435753
theorem B18270107 : Blo 1500070 18270107 := bstep (se 1 (by rfl) ⟨13702580, by rfl⟩ : syracuseStep 18270107 = 27405161) B27405161
theorem B18270593 : Blo 1500070 18270593 := bstep (se 2 (by rfl) ⟨6851472, by rfl⟩ : syracuseStep 18270593 = 13702945) B13702945
theorem B64899467 : Blo 1500070 64899467 := bstep (se 1 (by rfl) ⟨48674600, by rfl⟩ : syracuseStep 64899467 = 97349201) B97349201
theorem B2534395 : Blo 1500070 2534395 := bstep (se 1 (by rfl) ⟨1900796, by rfl⟩ : syracuseStep 2534395 = 3801593) B3801593
theorem B3797887 : Blo 1500070 3797887 := bstep (se 1 (by rfl) ⟨2848415, by rfl⟩ : syracuseStep 3797887 = 5696831) B5696831
theorem B12170207 : Blo 1500070 12170207 := bstep (se 1 (by rfl) ⟨9127655, by rfl⟩ : syracuseStep 12170207 = 18255311) B18255311
theorem B5698943 : Blo 1500070 5698943 := bstep (se 1 (by rfl) ⟨4274207, by rfl⟩ : syracuseStep 5698943 = 8548415) B8548415
theorem B14825591 : Blo 1500070 14825591 := bstep (se 1 (by rfl) ⟨11119193, by rfl⟩ : syracuseStep 14825591 = 22238387) B22238387
theorem B54803303 : Blo 1500070 54803303 := bstep (se 1 (by rfl) ⟨41102477, by rfl⟩ : syracuseStep 54803303 = 82204955) B82204955
theorem B6413651 : Blo 1500070 6413651 := bstep (se 1 (by rfl) ⟨4810238, by rfl⟩ : syracuseStep 6413651 = 9620477) B9620477
theorem B8117779 : Blo 1500070 8117779 := bstep (se 1 (by rfl) ⟨6088334, by rfl⟩ : syracuseStep 8117779 = 12176669) B12176669
theorem B5701175 : Blo 1500070 5701175 := bstep (se 1 (by rfl) ⟨4275881, by rfl⟩ : syracuseStep 5701175 = 8551763) B8551763
theorem B7602173 : Blo 1500070 7602173 := bstep (se 3 (by rfl) ⟨1425407, by rfl⟩ : syracuseStep 7602173 = 2850815) B2850815
theorem B5063849 : Blo 1500070 5063849 := bstep (se 2 (by rfl) ⟨1898943, by rfl⟩ : syracuseStep 5063849 = 3797887) B3797887
theorem B10823705 : Blo 1500070 10823705 := bstep (se 2 (by rfl) ⟨4058889, by rfl⟩ : syracuseStep 10823705 = 8117779) B8117779
theorem B2165113 : Blo 1500070 2165113 := bstep (se 2 (by rfl) ⟨811917, by rfl⟩ : syracuseStep 2165113 = 1623835) B1623835
theorem B24358715 : Blo 1500070 24358715 := bstep (se 1 (by rfl) ⟨18269036, by rfl⟩ : syracuseStep 24358715 = 36538073) B36538073
theorem B3379193 : Blo 1500070 3379193 := bstep (se 2 (by rfl) ⟨1267197, by rfl⟩ : syracuseStep 3379193 = 2534395) B2534395
theorem B9883727 : Blo 1500070 9883727 := bstep (se 1 (by rfl) ⟨7412795, by rfl⟩ : syracuseStep 9883727 = 14825591) B14825591
theorem B43266311 : Blo 1500070 43266311 := bstep (se 1 (by rfl) ⟨32449733, by rfl⟩ : syracuseStep 43266311 = 64899467) B64899467
theorem B32453885 : Blo 1500070 32453885 := bstep (se 3 (by rfl) ⟨6085103, by rfl⟩ : syracuseStep 32453885 = 12170207) B12170207
theorem B5068115 : Blo 1500070 5068115 := bstep (se 1 (by rfl) ⟨3801086, by rfl⟩ : syracuseStep 5068115 = 7602173) B7602173
theorem B3799295 : Blo 1500070 3799295 := bstep (se 1 (by rfl) ⟨2849471, by rfl⟩ : syracuseStep 3799295 = 5698943) B5698943
theorem B12180071 : Blo 1500070 12180071 := bstep (se 1 (by rfl) ⟨9135053, by rfl⟩ : syracuseStep 12180071 = 18270107) B18270107
theorem B12180395 : Blo 1500070 12180395 := bstep (se 1 (by rfl) ⟨9135296, by rfl⟩ : syracuseStep 12180395 = 18270593) B18270593
theorem B36535535 : Blo 1500070 36535535 := bstep (se 1 (by rfl) ⟨27401651, by rfl⟩ : syracuseStep 36535535 = 54803303) B54803303
theorem B4275767 : Blo 1500070 4275767 := bstep (se 1 (by rfl) ⟨3206825, by rfl⟩ : syracuseStep 4275767 = 6413651) B6413651
theorem B3800783 : Blo 1500070 3800783 := bstep (se 1 (by rfl) ⟨2850587, by rfl⟩ : syracuseStep 3800783 = 5701175) B5701175
theorem B28844207 : Blo 1500070 28844207 := bstep (se 1 (by rfl) ⟨21633155, by rfl⟩ : syracuseStep 28844207 = 43266311) B43266311
theorem B3375899 : Blo 1500070 3375899 := bstep (se 1 (by rfl) ⟨2531924, by rfl⟩ : syracuseStep 3375899 = 5063849) B5063849
theorem B21635923 : Blo 1500070 21635923 := bstep (se 1 (by rfl) ⟨16226942, by rfl⟩ : syracuseStep 21635923 = 32453885) B32453885
theorem B2532863 : Blo 1500070 2532863 := bstep (se 1 (by rfl) ⟨1899647, by rfl⟩ : syracuseStep 2532863 = 3799295) B3799295
theorem B8120047 : Blo 1500070 8120047 := bstep (se 1 (by rfl) ⟨6090035, by rfl⟩ : syracuseStep 8120047 = 12180071) B12180071
theorem B8120263 : Blo 1500070 8120263 := bstep (se 1 (by rfl) ⟨6090197, by rfl⟩ : syracuseStep 8120263 = 12180395) B12180395
theorem B24357023 : Blo 1500070 24357023 := bstep (se 1 (by rfl) ⟨18267767, by rfl⟩ : syracuseStep 24357023 = 36535535) B36535535
theorem B2533855 : Blo 1500070 2533855 := bstep (se 1 (by rfl) ⟨1900391, by rfl⟩ : syracuseStep 2533855 = 3800783) B3800783
theorem B16239143 : Blo 1500070 16239143 := bstep (se 1 (by rfl) ⟨12179357, by rfl⟩ : syracuseStep 16239143 = 24358715) B24358715
theorem B6589151 : Blo 1500070 6589151 := bstep (se 1 (by rfl) ⟨4941863, by rfl⟩ : syracuseStep 6589151 = 9883727) B9883727
theorem B3378743 : Blo 1500070 3378743 := bstep (se 1 (by rfl) ⟨2534057, by rfl⟩ : syracuseStep 3378743 = 5068115) B5068115
theorem B11547269 : Blo 1500070 11547269 := bstep (se 4 (by rfl) ⟨1082556, by rfl⟩ : syracuseStep 11547269 = 2165113) B2165113
theorem B7215803 : Blo 1500070 7215803 := bstep (se 1 (by rfl) ⟨5411852, by rfl⟩ : syracuseStep 7215803 = 10823705) B10823705
theorem B11402045 : Blo 1500070 11402045 := bstep (se 3 (by rfl) ⟨2137883, by rfl⟩ : syracuseStep 11402045 = 4275767) B4275767
theorem B2252795 : Blo 1500070 2252795 := bstep (se 1 (by rfl) ⟨1689596, by rfl⟩ : syracuseStep 2252795 = 3379193) B3379193
theorem B1688575 : Blo 1500070 1688575 := bstep (se 1 (by rfl) ⟨1266431, by rfl⟩ : syracuseStep 1688575 = 2532863) B2532863
theorem B16238015 : Blo 1500070 16238015 := bstep (se 1 (by rfl) ⟨12178511, by rfl⟩ : syracuseStep 16238015 = 24357023) B24357023
theorem B4810535 : Blo 1500070 4810535 := bstep (se 1 (by rfl) ⟨3607901, by rfl⟩ : syracuseStep 4810535 = 7215803) B7215803
theorem B4392767 : Blo 1500070 4392767 := bstep (se 1 (by rfl) ⟨3294575, by rfl⟩ : syracuseStep 4392767 = 6589151) B6589151
theorem B1501863 : Blo 1500070 1501863 := bstep (se 1 (by rfl) ⟨1126397, by rfl⟩ : syracuseStep 1501863 = 2252795) B2252795
theorem B19229471 : Blo 1500070 19229471 := bstep (se 1 (by rfl) ⟨14422103, by rfl⟩ : syracuseStep 19229471 = 28844207) B28844207
theorem B3378473 : Blo 1500070 3378473 := bstep (se 2 (by rfl) ⟨1266927, by rfl⟩ : syracuseStep 3378473 = 2533855) B2533855
theorem B28847897 : Blo 1500070 28847897 := bstep (se 2 (by rfl) ⟨10817961, by rfl⟩ : syracuseStep 28847897 = 21635923) B21635923
theorem B10826095 : Blo 1500070 10826095 := bstep (se 1 (by rfl) ⟨8119571, by rfl⟩ : syracuseStep 10826095 = 16239143) B16239143
theorem B10826729 : Blo 1500070 10826729 := bstep (se 2 (by rfl) ⟨4060023, by rfl⟩ : syracuseStep 10826729 = 8120047) B8120047
theorem B10827017 : Blo 1500070 10827017 := bstep (se 2 (by rfl) ⟨4060131, by rfl⟩ : syracuseStep 10827017 = 8120263) B8120263
theorem B7698179 : Blo 1500070 7698179 := bstep (se 1 (by rfl) ⟨5773634, by rfl⟩ : syracuseStep 7698179 = 11547269) B11547269
theorem B2250599 : Blo 1500070 2250599 := bstep (se 1 (by rfl) ⟨1687949, by rfl⟩ : syracuseStep 2250599 = 3375899) B3375899
theorem B7601363 : Blo 1500070 7601363 := bstep (se 1 (by rfl) ⟨5701022, by rfl⟩ : syracuseStep 7601363 = 11402045) B11402045
theorem B2252495 : Blo 1500070 2252495 := bstep (se 1 (by rfl) ⟨1689371, by rfl⟩ : syracuseStep 2252495 = 3378743) B3378743
theorem B14434793 : Blo 1500070 14434793 := bstep (se 2 (by rfl) ⟨5413047, by rfl⟩ : syracuseStep 14434793 = 10826095) B10826095
theorem B7217819 : Blo 1500070 7217819 := bstep (se 1 (by rfl) ⟨5413364, by rfl⟩ : syracuseStep 7217819 = 10826729) B10826729
theorem B7218011 : Blo 1500070 7218011 := bstep (se 1 (by rfl) ⟨5413508, by rfl⟩ : syracuseStep 7218011 = 10827017) B10827017
theorem B1500399 : Blo 1500070 1500399 := bstep (se 1 (by rfl) ⟨1125299, by rfl⟩ : syracuseStep 1500399 = 2250599) B2250599
theorem B1501663 : Blo 1500070 1501663 := bstep (se 1 (by rfl) ⟨1126247, by rfl⟩ : syracuseStep 1501663 = 2252495) B2252495
theorem B10825343 : Blo 1500070 10825343 := bstep (se 1 (by rfl) ⟨8119007, by rfl⟩ : syracuseStep 10825343 = 16238015) B16238015
theorem B5132119 : Blo 1500070 5132119 := bstep (se 1 (by rfl) ⟨3849089, by rfl⟩ : syracuseStep 5132119 = 7698179) B7698179
theorem B3207023 : Blo 1500070 3207023 := bstep (se 1 (by rfl) ⟨2405267, by rfl⟩ : syracuseStep 3207023 = 4810535) B4810535
theorem B5067575 : Blo 1500070 5067575 := bstep (se 1 (by rfl) ⟨3800681, by rfl⟩ : syracuseStep 5067575 = 7601363) B7601363
theorem B19231931 : Blo 1500070 19231931 := bstep (se 1 (by rfl) ⟨14423948, by rfl⟩ : syracuseStep 19231931 = 28847897) B28847897
theorem B2251433 : Blo 1500070 2251433 := bstep (se 2 (by rfl) ⟨844287, by rfl⟩ : syracuseStep 2251433 = 1688575) B1688575
theorem B12819647 : Blo 1500070 12819647 := bstep (se 1 (by rfl) ⟨9614735, by rfl⟩ : syracuseStep 12819647 = 19229471) B19229471
theorem B11714045 : Blo 1500070 11714045 := bstep (se 3 (by rfl) ⟨2196383, by rfl⟩ : syracuseStep 11714045 = 4392767) B4392767
theorem B2252315 : Blo 1500070 2252315 := bstep (se 1 (by rfl) ⟨1689236, by rfl⟩ : syracuseStep 2252315 = 3378473) B3378473
theorem B12821287 : Blo 1500070 12821287 := bstep (se 1 (by rfl) ⟨9615965, by rfl⟩ : syracuseStep 12821287 = 19231931) B19231931
theorem B31237453 : Blo 1500070 31237453 := bstep (se 3 (by rfl) ⟨5857022, by rfl⟩ : syracuseStep 31237453 = 11714045) B11714045
theorem B1500955 : Blo 1500070 1500955 := bstep (se 1 (by rfl) ⟨1125716, by rfl⟩ : syracuseStep 1500955 = 2251433) B2251433
theorem B8546431 : Blo 1500070 8546431 := bstep (se 1 (by rfl) ⟨6409823, by rfl⟩ : syracuseStep 8546431 = 12819647) B12819647
theorem B1501543 : Blo 1500070 1501543 := bstep (se 1 (by rfl) ⟨1126157, by rfl⟩ : syracuseStep 1501543 = 2252315) B2252315
theorem B6842825 : Blo 1500070 6842825 := bstep (se 2 (by rfl) ⟨2566059, by rfl⟩ : syracuseStep 6842825 = 5132119) B5132119
theorem B4811879 : Blo 1500070 4811879 := bstep (se 1 (by rfl) ⟨3608909, by rfl⟩ : syracuseStep 4811879 = 7217819) B7217819
theorem B3378383 : Blo 1500070 3378383 := bstep (se 1 (by rfl) ⟨2533787, by rfl⟩ : syracuseStep 3378383 = 5067575) B5067575
theorem B19248029 : Blo 1500070 19248029 := bstep (se 3 (by rfl) ⟨3609005, by rfl⟩ : syracuseStep 19248029 = 7218011) B7218011
theorem B9623195 : Blo 1500070 9623195 := bstep (se 1 (by rfl) ⟨7217396, by rfl⟩ : syracuseStep 9623195 = 14434793) B14434793
theorem B7216895 : Blo 1500070 7216895 := bstep (se 1 (by rfl) ⟨5412671, by rfl⟩ : syracuseStep 7216895 = 10825343) B10825343
theorem B2138015 : Blo 1500070 2138015 := bstep (se 1 (by rfl) ⟨1603511, by rfl⟩ : syracuseStep 2138015 = 3207023) B3207023
theorem B11395241 : Blo 1500070 11395241 := bstep (se 2 (by rfl) ⟨4273215, by rfl⟩ : syracuseStep 11395241 = 8546431) B8546431
theorem B6415463 : Blo 1500070 6415463 := bstep (se 1 (by rfl) ⟨4811597, by rfl⟩ : syracuseStep 6415463 = 9623195) B9623195
theorem B19245053 : Blo 1500070 19245053 := bstep (se 3 (by rfl) ⟨3608447, by rfl⟩ : syracuseStep 19245053 = 7216895) B7216895
theorem B12832019 : Blo 1500070 12832019 := bstep (se 1 (by rfl) ⟨9624014, by rfl⟩ : syracuseStep 12832019 = 19248029) B19248029
theorem B3207919 : Blo 1500070 3207919 := bstep (se 1 (by rfl) ⟨2405939, by rfl⟩ : syracuseStep 3207919 = 4811879) B4811879
theorem B17095049 : Blo 1500070 17095049 := bstep (se 2 (by rfl) ⟨6410643, by rfl⟩ : syracuseStep 17095049 = 12821287) B12821287
theorem B4561883 : Blo 1500070 4561883 := bstep (se 1 (by rfl) ⟨3421412, by rfl⟩ : syracuseStep 4561883 = 6842825) B6842825
theorem B166599749 : Blo 1500070 166599749 := bstep (se 4 (by rfl) ⟨15618726, by rfl⟩ : syracuseStep 166599749 = 31237453) B31237453
theorem B2252255 : Blo 1500070 2252255 := bstep (se 1 (by rfl) ⟨1689191, by rfl⟩ : syracuseStep 2252255 = 3378383) B3378383
theorem B5701373 : Blo 1500070 5701373 := bstep (se 3 (by rfl) ⟨1069007, by rfl⟩ : syracuseStep 5701373 = 2138015) B2138015
theorem B4276975 : Blo 1500070 4276975 := bstep (se 1 (by rfl) ⟨3207731, by rfl⟩ : syracuseStep 4276975 = 6415463) B6415463
theorem B4277225 : Blo 1500070 4277225 := bstep (se 2 (by rfl) ⟨1603959, by rfl⟩ : syracuseStep 4277225 = 3207919) B3207919
theorem B12830035 : Blo 1500070 12830035 := bstep (se 1 (by rfl) ⟨9622526, by rfl⟩ : syracuseStep 12830035 = 19245053) B19245053
theorem B11396699 : Blo 1500070 11396699 := bstep (se 1 (by rfl) ⟨8547524, by rfl⟩ : syracuseStep 11396699 = 17095049) B17095049
theorem B3041255 : Blo 1500070 3041255 := bstep (se 1 (by rfl) ⟨2280941, by rfl⟩ : syracuseStep 3041255 = 4561883) B4561883
theorem B8554679 : Blo 1500070 8554679 := bstep (se 1 (by rfl) ⟨6416009, by rfl⟩ : syracuseStep 8554679 = 12832019) B12832019
theorem B1501503 : Blo 1500070 1501503 := bstep (se 1 (by rfl) ⟨1126127, by rfl⟩ : syracuseStep 1501503 = 2252255) B2252255
theorem B7596827 : Blo 1500070 7596827 := bstep (se 1 (by rfl) ⟨5697620, by rfl⟩ : syracuseStep 7596827 = 11395241) B11395241
theorem B111066499 : Blo 1500070 111066499 := bstep (se 1 (by rfl) ⟨83299874, by rfl⟩ : syracuseStep 111066499 = 166599749) B166599749
theorem B3800915 : Blo 1500070 3800915 := bstep (se 1 (by rfl) ⟨2850686, by rfl⟩ : syracuseStep 3800915 = 5701373) B5701373
theorem B5702633 : Blo 1500070 5702633 := bstep (se 2 (by rfl) ⟨2138487, by rfl⟩ : syracuseStep 5702633 = 4276975) B4276975
theorem B5703119 : Blo 1500070 5703119 := bstep (se 1 (by rfl) ⟨4277339, by rfl⟩ : syracuseStep 5703119 = 8554679) B8554679
theorem B17106713 : Blo 1500070 17106713 := bstep (se 2 (by rfl) ⟨6415017, by rfl⟩ : syracuseStep 17106713 = 12830035) B12830035
theorem B148088665 : Blo 1500070 148088665 := bstep (se 2 (by rfl) ⟨55533249, by rfl⟩ : syracuseStep 148088665 = 111066499) B111066499
theorem B5064551 : Blo 1500070 5064551 := bstep (se 1 (by rfl) ⟨3798413, by rfl⟩ : syracuseStep 5064551 = 7596827) B7596827
theorem B2533943 : Blo 1500070 2533943 := bstep (se 1 (by rfl) ⟨1900457, by rfl⟩ : syracuseStep 2533943 = 3800915) B3800915
theorem B11405933 : Blo 1500070 11405933 := bstep (se 3 (by rfl) ⟨2138612, by rfl⟩ : syracuseStep 11405933 = 4277225) B4277225
theorem B7597799 : Blo 1500070 7597799 := bstep (se 1 (by rfl) ⟨5698349, by rfl⟩ : syracuseStep 7597799 = 11396699) B11396699
theorem B2027503 : Blo 1500070 2027503 := bstep (se 1 (by rfl) ⟨1520627, by rfl⟩ : syracuseStep 2027503 = 3041255) B3041255
theorem B3801755 : Blo 1500070 3801755 := bstep (se 1 (by rfl) ⟨2851316, by rfl⟩ : syracuseStep 3801755 = 5702633) B5702633
theorem B3802079 : Blo 1500070 3802079 := bstep (se 1 (by rfl) ⟨2851559, by rfl⟩ : syracuseStep 3802079 = 5703119) B5703119
theorem B11404475 : Blo 1500070 11404475 := bstep (se 1 (by rfl) ⟨8553356, by rfl⟩ : syracuseStep 11404475 = 17106713) B17106713
theorem B3376367 : Blo 1500070 3376367 := bstep (se 1 (by rfl) ⟨2532275, by rfl⟩ : syracuseStep 3376367 = 5064551) B5064551
theorem B1689295 : Blo 1500070 1689295 := bstep (se 1 (by rfl) ⟨1266971, by rfl⟩ : syracuseStep 1689295 = 2533943) B2533943
theorem B7603955 : Blo 1500070 7603955 := bstep (se 1 (by rfl) ⟨5702966, by rfl⟩ : syracuseStep 7603955 = 11405933) B11405933
theorem B5065199 : Blo 1500070 5065199 := bstep (se 1 (by rfl) ⟨3798899, by rfl⟩ : syracuseStep 5065199 = 7597799) B7597799
theorem B197451553 : Blo 1500070 197451553 := bstep (se 2 (by rfl) ⟨74044332, by rfl⟩ : syracuseStep 197451553 = 148088665) B148088665
theorem B2703337 : Blo 1500070 2703337 := bstep (se 2 (by rfl) ⟨1013751, by rfl⟩ : syracuseStep 2703337 = 2027503) B2027503
theorem B7602983 : Blo 1500070 7602983 := bstep (se 1 (by rfl) ⟨5702237, by rfl⟩ : syracuseStep 7602983 = 11404475) B11404475
theorem B3376799 : Blo 1500070 3376799 := bstep (se 1 (by rfl) ⟨2532599, by rfl⟩ : syracuseStep 3376799 = 5065199) B5065199
theorem B263268737 : Blo 1500070 263268737 := bstep (se 2 (by rfl) ⟨98725776, by rfl⟩ : syracuseStep 263268737 = 197451553) B197451553
theorem B2534503 : Blo 1500070 2534503 := bstep (se 1 (by rfl) ⟨1900877, by rfl⟩ : syracuseStep 2534503 = 3801755) B3801755
theorem B2534719 : Blo 1500070 2534719 := bstep (se 1 (by rfl) ⟨1901039, by rfl⟩ : syracuseStep 2534719 = 3802079) B3802079
theorem B2250911 : Blo 1500070 2250911 := bstep (se 1 (by rfl) ⟨1688183, by rfl⟩ : syracuseStep 2250911 = 3376367) B3376367
theorem B5069303 : Blo 1500070 5069303 := bstep (se 1 (by rfl) ⟨3801977, by rfl⟩ : syracuseStep 5069303 = 7603955) B7603955
theorem B57671189 : Blo 1500070 57671189 := bstep (se 6 (by rfl) ⟨1351668, by rfl⟩ : syracuseStep 57671189 = 2703337) B2703337
theorem B2252393 : Blo 1500070 2252393 := bstep (se 2 (by rfl) ⟨844647, by rfl⟩ : syracuseStep 2252393 = 1689295) B1689295
theorem B1500607 : Blo 1500070 1500607 := bstep (se 1 (by rfl) ⟨1125455, by rfl⟩ : syracuseStep 1500607 = 2250911) B2250911
theorem B38447459 : Blo 1500070 38447459 := bstep (se 1 (by rfl) ⟨28835594, by rfl⟩ : syracuseStep 38447459 = 57671189) B57671189
theorem B1501595 : Blo 1500070 1501595 := bstep (se 1 (by rfl) ⟨1126196, by rfl⟩ : syracuseStep 1501595 = 2252393) B2252393
theorem B3379337 : Blo 1500070 3379337 := bstep (se 2 (by rfl) ⟨1267251, by rfl⟩ : syracuseStep 3379337 = 2534503) B2534503
theorem B3379535 : Blo 1500070 3379535 := bstep (se 1 (by rfl) ⟨2534651, by rfl⟩ : syracuseStep 3379535 = 5069303) B5069303
theorem B3379625 : Blo 1500070 3379625 := bstep (se 2 (by rfl) ⟨1267359, by rfl⟩ : syracuseStep 3379625 = 2534719) B2534719
theorem B5068655 : Blo 1500070 5068655 := bstep (se 1 (by rfl) ⟨3801491, by rfl⟩ : syracuseStep 5068655 = 7602983) B7602983
theorem B2251199 : Blo 1500070 2251199 := bstep (se 1 (by rfl) ⟨1688399, by rfl⟩ : syracuseStep 2251199 = 3376799) B3376799
theorem B175512491 : Blo 1500070 175512491 := bstep (se 1 (by rfl) ⟨131634368, by rfl⟩ : syracuseStep 175512491 = 263268737) B263268737
theorem B2252891 : Blo 1500070 2252891 := bstep (se 1 (by rfl) ⟨1689668, by rfl⟩ : syracuseStep 2252891 = 3379337) B3379337
theorem B2253023 : Blo 1500070 2253023 := bstep (se 1 (by rfl) ⟨1689767, by rfl⟩ : syracuseStep 2253023 = 3379535) B3379535
theorem B2253083 : Blo 1500070 2253083 := bstep (se 1 (by rfl) ⟨1689812, by rfl⟩ : syracuseStep 2253083 = 3379625) B3379625
theorem B1500799 : Blo 1500070 1500799 := bstep (se 1 (by rfl) ⟨1125599, by rfl⟩ : syracuseStep 1500799 = 2251199) B2251199
theorem B117008327 : Blo 1500070 117008327 := bstep (se 1 (by rfl) ⟨87756245, by rfl⟩ : syracuseStep 117008327 = 175512491) B175512491
theorem B3379103 : Blo 1500070 3379103 := bstep (se 1 (by rfl) ⟨2534327, by rfl⟩ : syracuseStep 3379103 = 5068655) B5068655
theorem B25631639 : Blo 1500070 25631639 := bstep (se 1 (by rfl) ⟨19223729, by rfl⟩ : syracuseStep 25631639 = 38447459) B38447459
theorem B78005551 : Blo 1500070 78005551 := bstep (se 1 (by rfl) ⟨58504163, by rfl⟩ : syracuseStep 78005551 = 117008327) B117008327
theorem B1501927 : Blo 1500070 1501927 := bstep (se 1 (by rfl) ⟨1126445, by rfl⟩ : syracuseStep 1501927 = 2252891) B2252891
theorem B1502015 : Blo 1500070 1502015 := bstep (se 1 (by rfl) ⟨1126511, by rfl⟩ : syracuseStep 1502015 = 2253023) B2253023
theorem B1502055 : Blo 1500070 1502055 := bstep (se 1 (by rfl) ⟨1126541, by rfl⟩ : syracuseStep 1502055 = 2253083) B2253083
theorem B17087759 : Blo 1500070 17087759 := bstep (se 1 (by rfl) ⟨12815819, by rfl⟩ : syracuseStep 17087759 = 25631639) B25631639
theorem B2252735 : Blo 1500070 2252735 := bstep (se 1 (by rfl) ⟨1689551, by rfl⟩ : syracuseStep 2252735 = 3379103) B3379103
theorem B104007401 : Blo 1500070 104007401 := bstep (se 2 (by rfl) ⟨39002775, by rfl⟩ : syracuseStep 104007401 = 78005551) B78005551
theorem B1501823 : Blo 1500070 1501823 := bstep (se 1 (by rfl) ⟨1126367, by rfl⟩ : syracuseStep 1501823 = 2252735) B2252735
theorem B11391839 : Blo 1500070 11391839 := bstep (se 1 (by rfl) ⟨8543879, by rfl⟩ : syracuseStep 11391839 = 17087759) B17087759
theorem B7594559 : Blo 1500070 7594559 := bstep (se 1 (by rfl) ⟨5695919, by rfl⟩ : syracuseStep 7594559 = 11391839) B11391839
theorem B69338267 : Blo 1500070 69338267 := bstep (se 1 (by rfl) ⟨52003700, by rfl⟩ : syracuseStep 69338267 = 104007401) B104007401
theorem B5063039 : Blo 1500070 5063039 := bstep (se 1 (by rfl) ⟨3797279, by rfl⟩ : syracuseStep 5063039 = 7594559) B7594559
theorem B46225511 : Blo 1500070 46225511 := bstep (se 1 (by rfl) ⟨34669133, by rfl⟩ : syracuseStep 46225511 = 69338267) B69338267
theorem B3375359 : Blo 1500070 3375359 := bstep (se 1 (by rfl) ⟨2531519, by rfl⟩ : syracuseStep 3375359 = 5063039) B5063039
theorem B30817007 : Blo 1500070 30817007 := bstep (se 1 (by rfl) ⟨23112755, by rfl⟩ : syracuseStep 30817007 = 46225511) B46225511
theorem B2250239 : Blo 1500070 2250239 := bstep (se 1 (by rfl) ⟨1687679, by rfl⟩ : syracuseStep 2250239 = 3375359) B3375359
theorem B20544671 : Blo 1500070 20544671 := bstep (se 1 (by rfl) ⟨15408503, by rfl⟩ : syracuseStep 20544671 = 30817007) B30817007
theorem B1500159 : Blo 1500070 1500159 := bstep (se 1 (by rfl) ⟨1125119, by rfl⟩ : syracuseStep 1500159 = 2250239) B2250239
theorem B13696447 : Blo 1500070 13696447 := bstep (se 1 (by rfl) ⟨10272335, by rfl⟩ : syracuseStep 13696447 = 20544671) B20544671
theorem B18261929 : Blo 1500070 18261929 := bstep (se 2 (by rfl) ⟨6848223, by rfl⟩ : syracuseStep 18261929 = 13696447) B13696447
theorem B12174619 : Blo 1500070 12174619 := bstep (se 1 (by rfl) ⟨9130964, by rfl⟩ : syracuseStep 12174619 = 18261929) B18261929
theorem B16232825 : Blo 1500070 16232825 := bstep (se 2 (by rfl) ⟨6087309, by rfl⟩ : syracuseStep 16232825 = 12174619) B12174619
theorem B43287533 : Blo 1500070 43287533 := bstep (se 3 (by rfl) ⟨8116412, by rfl⟩ : syracuseStep 43287533 = 16232825) B16232825
theorem B28858355 : Blo 1500070 28858355 := bstep (se 1 (by rfl) ⟨21643766, by rfl⟩ : syracuseStep 28858355 = 43287533) B43287533
theorem B19238903 : Blo 1500070 19238903 := bstep (se 1 (by rfl) ⟨14429177, by rfl⟩ : syracuseStep 19238903 = 28858355) B28858355
theorem B12825935 : Blo 1500070 12825935 := bstep (se 1 (by rfl) ⟨9619451, by rfl⟩ : syracuseStep 12825935 = 19238903) B19238903
theorem B8550623 : Blo 1500070 8550623 := bstep (se 1 (by rfl) ⟨6412967, by rfl⟩ : syracuseStep 8550623 = 12825935) B12825935
theorem B5700415 : Blo 1500070 5700415 := bstep (se 1 (by rfl) ⟨4275311, by rfl⟩ : syracuseStep 5700415 = 8550623) B8550623
theorem B7600553 : Blo 1500070 7600553 := bstep (se 2 (by rfl) ⟨2850207, by rfl⟩ : syracuseStep 7600553 = 5700415) B5700415
theorem B5067035 : Blo 1500070 5067035 := bstep (se 1 (by rfl) ⟨3800276, by rfl⟩ : syracuseStep 5067035 = 7600553) B7600553
theorem B3378023 : Blo 1500070 3378023 := bstep (se 1 (by rfl) ⟨2533517, by rfl⟩ : syracuseStep 3378023 = 5067035) B5067035
theorem B2252015 : Blo 1500070 2252015 := bstep (se 1 (by rfl) ⟨1689011, by rfl⟩ : syracuseStep 2252015 = 3378023) B3378023
theorem B1501343 : Blo 1500070 1501343 := bstep (se 1 (by rfl) ⟨1126007, by rfl⟩ : syracuseStep 1501343 = 2252015) B2252015

theorem C0 (j : ℕ) (h1 : 375017 ≤ j) (h2 : j ≤ 375516) : Blo 1500070 (4 * j + 3) := by
  interval_cases j
  · exact B1500071
  · exact B1500075
  · exact B1500079
  · exact B1500083
  · exact B1500087
  · exact B1500091
  · exact B1500095
  · exact B1500099
  · exact B1500103
  · exact B1500107
  · exact B1500111
  · exact B1500115
  · exact B1500119
  · exact B1500123
  · exact B1500127
  · exact B1500131
  · exact B1500135
  · exact B1500139
  · exact B1500143
  · exact B1500147
  · exact B1500151
  · exact B1500155
  · exact B1500159
  · exact B1500163
  · exact B1500167
  · exact B1500171
  · exact B1500175
  · exact B1500179
  · exact B1500183
  · exact B1500187
  · exact B1500191
  · exact B1500195
  · exact B1500199
  · exact B1500203
  · exact B1500207
  · exact B1500211
  · exact B1500215
  · exact B1500219
  · exact B1500223
  · exact B1500227
  · exact B1500231
  · exact B1500235
  · exact B1500239
  · exact B1500243
  · exact B1500247
  · exact B1500251
  · exact B1500255
  · exact B1500259
  · exact B1500263
  · exact B1500267
  · exact B1500271
  · exact B1500275
  · exact B1500279
  · exact B1500283
  · exact B1500287
  · exact B1500291
  · exact B1500295
  · exact B1500299
  · exact B1500303
  · exact B1500307
  · exact B1500311
  · exact B1500315
  · exact B1500319
  · exact B1500323
  · exact B1500327
  · exact B1500331
  · exact B1500335
  · exact B1500339
  · exact B1500343
  · exact B1500347
  · exact B1500351
  · exact B1500355
  · exact B1500359
  · exact B1500363
  · exact B1500367
  · exact B1500371
  · exact B1500375
  · exact B1500379
  · exact B1500383
  · exact B1500387
  · exact B1500391
  · exact B1500395
  · exact B1500399
  · exact B1500403
  · exact B1500407
  · exact B1500411
  · exact B1500415
  · exact B1500419
  · exact B1500423
  · exact B1500427
  · exact B1500431
  · exact B1500435
  · exact B1500439
  · exact B1500443
  · exact B1500447
  · exact B1500451
  · exact B1500455
  · exact B1500459
  · exact B1500463
  · exact B1500467
  · exact B1500471
  · exact B1500475
  · exact B1500479
  · exact B1500483
  · exact B1500487
  · exact B1500491
  · exact B1500495
  · exact B1500499
  · exact B1500503
  · exact B1500507
  · exact B1500511
  · exact B1500515
  · exact B1500519
  · exact B1500523
  · exact B1500527
  · exact B1500531
  · exact B1500535
  · exact B1500539
  · exact B1500543
  · exact B1500547
  · exact B1500551
  · exact B1500555
  · exact B1500559
  · exact B1500563
  · exact B1500567
  · exact B1500571
  · exact B1500575
  · exact B1500579
  · exact B1500583
  · exact B1500587
  · exact B1500591
  · exact B1500595
  · exact B1500599
  · exact B1500603
  · exact B1500607
  · exact B1500611
  · exact B1500615
  · exact B1500619
  · exact B1500623
  · exact B1500627
  · exact B1500631
  · exact B1500635
  · exact B1500639
  · exact B1500643
  · exact B1500647
  · exact B1500651
  · exact B1500655
  · exact B1500659
  · exact B1500663
  · exact B1500667
  · exact B1500671
  · exact B1500675
  · exact B1500679
  · exact B1500683
  · exact B1500687
  · exact B1500691
  · exact B1500695
  · exact B1500699
  · exact B1500703
  · exact B1500707
  · exact B1500711
  · exact B1500715
  · exact B1500719
  · exact B1500723
  · exact B1500727
  · exact B1500731
  · exact B1500735
  · exact B1500739
  · exact B1500743
  · exact B1500747
  · exact B1500751
  · exact B1500755
  · exact B1500759
  · exact B1500763
  · exact B1500767
  · exact B1500771
  · exact B1500775
  · exact B1500779
  · exact B1500783
  · exact B1500787
  · exact B1500791
  · exact B1500795
  · exact B1500799
  · exact B1500803
  · exact B1500807
  · exact B1500811
  · exact B1500815
  · exact B1500819
  · exact B1500823
  · exact B1500827
  · exact B1500831
  · exact B1500835
  · exact B1500839
  · exact B1500843
  · exact B1500847
  · exact B1500851
  · exact B1500855
  · exact B1500859
  · exact B1500863
  · exact B1500867
  · exact B1500871
  · exact B1500875
  · exact B1500879
  · exact B1500883
  · exact B1500887
  · exact B1500891
  · exact B1500895
  · exact B1500899
  · exact B1500903
  · exact B1500907
  · exact B1500911
  · exact B1500915
  · exact B1500919
  · exact B1500923
  · exact B1500927
  · exact B1500931
  · exact B1500935
  · exact B1500939
  · exact B1500943
  · exact B1500947
  · exact B1500951
  · exact B1500955
  · exact B1500959
  · exact B1500963
  · exact B1500967
  · exact B1500971
  · exact B1500975
  · exact B1500979
  · exact B1500983
  · exact B1500987
  · exact B1500991
  · exact B1500995
  · exact B1500999
  · exact B1501003
  · exact B1501007
  · exact B1501011
  · exact B1501015
  · exact B1501019
  · exact B1501023
  · exact B1501027
  · exact B1501031
  · exact B1501035
  · exact B1501039
  · exact B1501043
  · exact B1501047
  · exact B1501051
  · exact B1501055
  · exact B1501059
  · exact B1501063
  · exact B1501067
  · exact B1501071
  · exact B1501075
  · exact B1501079
  · exact B1501083
  · exact B1501087
  · exact B1501091
  · exact B1501095
  · exact B1501099
  · exact B1501103
  · exact B1501107
  · exact B1501111
  · exact B1501115
  · exact B1501119
  · exact B1501123
  · exact B1501127
  · exact B1501131
  · exact B1501135
  · exact B1501139
  · exact B1501143
  · exact B1501147
  · exact B1501151
  · exact B1501155
  · exact B1501159
  · exact B1501163
  · exact B1501167
  · exact B1501171
  · exact B1501175
  · exact B1501179
  · exact B1501183
  · exact B1501187
  · exact B1501191
  · exact B1501195
  · exact B1501199
  · exact B1501203
  · exact B1501207
  · exact B1501211
  · exact B1501215
  · exact B1501219
  · exact B1501223
  · exact B1501227
  · exact B1501231
  · exact B1501235
  · exact B1501239
  · exact B1501243
  · exact B1501247
  · exact B1501251
  · exact B1501255
  · exact B1501259
  · exact B1501263
  · exact B1501267
  · exact B1501271
  · exact B1501275
  · exact B1501279
  · exact B1501283
  · exact B1501287
  · exact B1501291
  · exact B1501295
  · exact B1501299
  · exact B1501303
  · exact B1501307
  · exact B1501311
  · exact B1501315
  · exact B1501319
  · exact B1501323
  · exact B1501327
  · exact B1501331
  · exact B1501335
  · exact B1501339
  · exact B1501343
  · exact B1501347
  · exact B1501351
  · exact B1501355
  · exact B1501359
  · exact B1501363
  · exact B1501367
  · exact B1501371
  · exact B1501375
  · exact B1501379
  · exact B1501383
  · exact B1501387
  · exact B1501391
  · exact B1501395
  · exact B1501399
  · exact B1501403
  · exact B1501407
  · exact B1501411
  · exact B1501415
  · exact B1501419
  · exact B1501423
  · exact B1501427
  · exact B1501431
  · exact B1501435
  · exact B1501439
  · exact B1501443
  · exact B1501447
  · exact B1501451
  · exact B1501455
  · exact B1501459
  · exact B1501463
  · exact B1501467
  · exact B1501471
  · exact B1501475
  · exact B1501479
  · exact B1501483
  · exact B1501487
  · exact B1501491
  · exact B1501495
  · exact B1501499
  · exact B1501503
  · exact B1501507
  · exact B1501511
  · exact B1501515
  · exact B1501519
  · exact B1501523
  · exact B1501527
  · exact B1501531
  · exact B1501535
  · exact B1501539
  · exact B1501543
  · exact B1501547
  · exact B1501551
  · exact B1501555
  · exact B1501559
  · exact B1501563
  · exact B1501567
  · exact B1501571
  · exact B1501575
  · exact B1501579
  · exact B1501583
  · exact B1501587
  · exact B1501591
  · exact B1501595
  · exact B1501599
  · exact B1501603
  · exact B1501607
  · exact B1501611
  · exact B1501615
  · exact B1501619
  · exact B1501623
  · exact B1501627
  · exact B1501631
  · exact B1501635
  · exact B1501639
  · exact B1501643
  · exact B1501647
  · exact B1501651
  · exact B1501655
  · exact B1501659
  · exact B1501663
  · exact B1501667
  · exact B1501671
  · exact B1501675
  · exact B1501679
  · exact B1501683
  · exact B1501687
  · exact B1501691
  · exact B1501695
  · exact B1501699
  · exact B1501703
  · exact B1501707
  · exact B1501711
  · exact B1501715
  · exact B1501719
  · exact B1501723
  · exact B1501727
  · exact B1501731
  · exact B1501735
  · exact B1501739
  · exact B1501743
  · exact B1501747
  · exact B1501751
  · exact B1501755
  · exact B1501759
  · exact B1501763
  · exact B1501767
  · exact B1501771
  · exact B1501775
  · exact B1501779
  · exact B1501783
  · exact B1501787
  · exact B1501791
  · exact B1501795
  · exact B1501799
  · exact B1501803
  · exact B1501807
  · exact B1501811
  · exact B1501815
  · exact B1501819
  · exact B1501823
  · exact B1501827
  · exact B1501831
  · exact B1501835
  · exact B1501839
  · exact B1501843
  · exact B1501847
  · exact B1501851
  · exact B1501855
  · exact B1501859
  · exact B1501863
  · exact B1501867
  · exact B1501871
  · exact B1501875
  · exact B1501879
  · exact B1501883
  · exact B1501887
  · exact B1501891
  · exact B1501895
  · exact B1501899
  · exact B1501903
  · exact B1501907
  · exact B1501911
  · exact B1501915
  · exact B1501919
  · exact B1501923
  · exact B1501927
  · exact B1501931
  · exact B1501935
  · exact B1501939
  · exact B1501943
  · exact B1501947
  · exact B1501951
  · exact B1501955
  · exact B1501959
  · exact B1501963
  · exact B1501967
  · exact B1501971
  · exact B1501975
  · exact B1501979
  · exact B1501983
  · exact B1501987
  · exact B1501991
  · exact B1501995
  · exact B1501999
  · exact B1502003
  · exact B1502007
  · exact B1502011
  · exact B1502015
  · exact B1502019
  · exact B1502023
  · exact B1502027
  · exact B1502031
  · exact B1502035
  · exact B1502039
  · exact B1502043
  · exact B1502047
  · exact B1502051
  · exact B1502055
  · exact B1502059
  · exact B1502063
  · exact B1502067

theorem solution (m : ℕ) (hlo : 1500070 ≤ m) (hhi : m ≤ 1502070) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 375017 ≤ j := by omega
    have hj2 : j ≤ 375516 := by omega
    have hb : Blo 1500070 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
