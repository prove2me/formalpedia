-- Prove2me | solution 1 for syracuse_descends_range_1279958_1281958
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:11:32.576296+00:00
-- url     : https://prove2.me/submissions/d180b288-6d45-46a7-b004-0088a0479560

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


theorem B3645445 : Blo 1279958 3645445 := bbase (se 4 (by rfl) ⟨341760, by rfl⟩ : syracuseStep 3645445 = 683521) (by norm_num)
theorem B2162693 : Blo 1279958 2162693 := bbase (se 4 (by rfl) ⟨202752, by rfl⟩ : syracuseStep 2162693 = 405505) (by norm_num)
theorem B1441813 : Blo 1279958 1441813 := bbase (se 6 (by rfl) ⟨33792, by rfl⟩ : syracuseStep 1441813 = 67585) (by norm_num)
theorem B2433053 : Blo 1279958 2433053 := bbase (se 3 (by rfl) ⟨456197, by rfl⟩ : syracuseStep 2433053 = 912395) (by norm_num)
theorem B1622045 : Blo 1279958 1622045 := bbase (se 3 (by rfl) ⟨304133, by rfl⟩ : syracuseStep 1622045 = 608267) (by norm_num)
theorem B3285029 : Blo 1279958 3285029 := bbase (se 4 (by rfl) ⟨307971, by rfl⟩ : syracuseStep 3285029 = 615943) (by norm_num)
theorem B9732149 : Blo 1279958 9732149 := bbase (se 5 (by rfl) ⟨456194, by rfl⟩ : syracuseStep 9732149 = 912389) (by norm_num)
theorem B1441849 : Blo 1279958 1441849 := bbase (se 2 (by rfl) ⟨540693, by rfl⟩ : syracuseStep 1441849 = 1081387) (by norm_num)
theorem B2883653 : Blo 1279958 2883653 := bbase (se 4 (by rfl) ⟨270342, by rfl⟩ : syracuseStep 2883653 = 540685) (by norm_num)
theorem B23371861 : Blo 1279958 23371861 := bbase (se 8 (by rfl) ⟨136944, by rfl⟩ : syracuseStep 23371861 = 273889) (by norm_num)
theorem B1622101 : Blo 1279958 1622101 := bbase (se 8 (by rfl) ⟨9504, by rfl⟩ : syracuseStep 1622101 = 19009) (by norm_num)
theorem B1441885 : Blo 1279958 1441885 := bbase (se 3 (by rfl) ⟨270353, by rfl⟩ : syracuseStep 1441885 = 540707) (by norm_num)
theorem B1687649 : Blo 1279958 1687649 := bbase (se 2 (by rfl) ⟨632868, by rfl⟩ : syracuseStep 1687649 = 1265737) (by norm_num)
theorem B1441921 : Blo 1279958 1441921 := bbase (se 2 (by rfl) ⟨540720, by rfl⟩ : syracuseStep 1441921 = 1081441) (by norm_num)
theorem B2162821 : Blo 1279958 2162821 := bbase (se 4 (by rfl) ⟨202764, by rfl⟩ : syracuseStep 2162821 = 405529) (by norm_num)
theorem B2883725 : Blo 1279958 2883725 := bbase (se 3 (by rfl) ⟨540698, by rfl⟩ : syracuseStep 2883725 = 1081397) (by norm_num)
theorem B1441957 : Blo 1279958 1441957 := bbase (se 4 (by rfl) ⟨135183, by rfl⟩ : syracuseStep 1441957 = 270367) (by norm_num)
theorem B1622197 : Blo 1279958 1622197 := bbase (se 5 (by rfl) ⟨76040, by rfl⟩ : syracuseStep 1622197 = 152081) (by norm_num)
theorem B6488261 : Blo 1279958 6488261 := bbase (se 4 (by rfl) ⟨608274, by rfl⟩ : syracuseStep 6488261 = 1216549) (by norm_num)
theorem B1441993 : Blo 1279958 1441993 := bbase (se 2 (by rfl) ⟨540747, by rfl⟩ : syracuseStep 1441993 = 1081495) (by norm_num)
theorem B2597069 : Blo 1279958 2597069 := bbase (se 3 (by rfl) ⟨486950, by rfl⟩ : syracuseStep 2597069 = 973901) (by norm_num)
theorem B7291093 : Blo 1279958 7291093 := bbase (se 7 (by rfl) ⟨85442, by rfl⟩ : syracuseStep 7291093 = 170885) (by norm_num)
theorem B2883797 : Blo 1279958 2883797 := bbase (se 7 (by rfl) ⟨33794, by rfl⟩ : syracuseStep 2883797 = 67589) (by norm_num)
theorem B2162909 : Blo 1279958 2162909 := bbase (se 3 (by rfl) ⟨405545, by rfl⟩ : syracuseStep 2162909 = 811091) (by norm_num)
theorem B1442029 : Blo 1279958 1442029 := bbase (se 3 (by rfl) ⟨270380, by rfl⟩ : syracuseStep 1442029 = 540761) (by norm_num)
theorem B4382981 : Blo 1279958 4382981 := bbase (se 4 (by rfl) ⟨410904, by rfl⟩ : syracuseStep 4382981 = 821809) (by norm_num)
theorem B1442065 : Blo 1279958 1442065 := bbase (se 2 (by rfl) ⟨540774, by rfl⟩ : syracuseStep 1442065 = 1081549) (by norm_num)
theorem B7389461 : Blo 1279958 7389461 := bbase (se 6 (by rfl) ⟨173190, by rfl⟩ : syracuseStep 7389461 = 346381) (by norm_num)
theorem B2883869 : Blo 1279958 2883869 := bbase (se 3 (by rfl) ⟨540725, by rfl⟩ : syracuseStep 2883869 = 1081451) (by norm_num)
theorem B4325669 : Blo 1279958 4325669 := bbase (se 4 (by rfl) ⟨405531, by rfl⟩ : syracuseStep 4325669 = 811063) (by norm_num)
theorem B3244333 : Blo 1279958 3244333 := bbase (se 3 (by rfl) ⟨608312, by rfl⟩ : syracuseStep 3244333 = 1216625) (by norm_num)
theorem B1442101 : Blo 1279958 1442101 := bbase (se 5 (by rfl) ⟨67598, by rfl⟩ : syracuseStep 1442101 = 135197) (by norm_num)
theorem B2433341 : Blo 1279958 2433341 := bbase (se 3 (by rfl) ⟨456251, by rfl⟩ : syracuseStep 2433341 = 912503) (by norm_num)
theorem B1368409 : Blo 1279958 1368409 := bbase (se 2 (by rfl) ⟨513153, by rfl⟩ : syracuseStep 1368409 = 1026307) (by norm_num)
theorem B1442137 : Blo 1279958 1442137 := bbase (se 2 (by rfl) ⟨540801, by rfl⟩ : syracuseStep 1442137 = 1081603) (by norm_num)
theorem B2163037 : Blo 1279958 2163037 := bbase (se 3 (by rfl) ⟨405569, by rfl⟩ : syracuseStep 2163037 = 811139) (by norm_num)
theorem B1622369 : Blo 1279958 1622369 := bbase (se 2 (by rfl) ⟨608388, by rfl⟩ : syracuseStep 1622369 = 1216777) (by norm_num)
theorem B2883941 : Blo 1279958 2883941 := bbase (se 4 (by rfl) ⟨270369, by rfl⟩ : syracuseStep 2883941 = 540739) (by norm_num)
theorem B1442173 : Blo 1279958 1442173 := bbase (se 3 (by rfl) ⟨270407, by rfl⟩ : syracuseStep 1442173 = 540815) (by norm_num)
theorem B1622425 : Blo 1279958 1622425 := bbase (se 2 (by rfl) ⟨608409, by rfl⟩ : syracuseStep 1622425 = 1216819) (by norm_num)
theorem B3244445 : Blo 1279958 3244445 := bbase (se 3 (by rfl) ⟨608333, by rfl⟩ : syracuseStep 3244445 = 1216667) (by norm_num)
theorem B2884013 : Blo 1279958 2884013 := bbase (se 3 (by rfl) ⟨540752, by rfl⟩ : syracuseStep 2884013 = 1081505) (by norm_num)
theorem B2163125 : Blo 1279958 2163125 := bbase (se 5 (by rfl) ⟨101396, by rfl⟩ : syracuseStep 2163125 = 202793) (by norm_num)
theorem B9724373 : Blo 1279958 9724373 := bbase (se 7 (by rfl) ⟨113957, by rfl⟩ : syracuseStep 9724373 = 227915) (by norm_num)
theorem B2433493 : Blo 1279958 2433493 := bbase (se 7 (by rfl) ⟨28517, by rfl⟩ : syracuseStep 2433493 = 57035) (by norm_num)
theorem B2884085 : Blo 1279958 2884085 := bbase (se 5 (by rfl) ⟨135191, by rfl⟩ : syracuseStep 2884085 = 270383) (by norm_num)
theorem B2163253 : Blo 1279958 2163253 := bbase (se 5 (by rfl) ⟨101402, by rfl⟩ : syracuseStep 2163253 = 202805) (by norm_num)
theorem B2884157 : Blo 1279958 2884157 := bbase (se 3 (by rfl) ⟨540779, by rfl⟩ : syracuseStep 2884157 = 1081559) (by norm_num)
theorem B3244637 : Blo 1279958 3244637 := bbase (se 3 (by rfl) ⟨608369, by rfl⟩ : syracuseStep 3244637 = 1216739) (by norm_num)
theorem B6480485 : Blo 1279958 6480485 := bbase (se 4 (by rfl) ⟨607545, by rfl⟩ : syracuseStep 6480485 = 1215091) (by norm_num)
theorem B2736757 : Blo 1279958 2736757 := bbase (se 5 (by rfl) ⟨128285, by rfl⟩ : syracuseStep 2736757 = 256571) (by norm_num)
theorem B2884229 : Blo 1279958 2884229 := bbase (se 4 (by rfl) ⟨270396, by rfl⟩ : syracuseStep 2884229 = 540793) (by norm_num)
theorem B2884301 : Blo 1279958 2884301 := bbase (se 3 (by rfl) ⟨540806, by rfl⟩ : syracuseStep 2884301 = 1081613) (by norm_num)
theorem B1368785 : Blo 1279958 1368785 := bbase (se 2 (by rfl) ⟨513294, by rfl⟩ : syracuseStep 1368785 = 1026589) (by norm_num)
theorem B4326101 : Blo 1279958 4326101 := bbase (se 7 (by rfl) ⟨50696, by rfl⟩ : syracuseStep 4326101 = 101393) (by norm_num)
theorem B7217909 : Blo 1279958 7217909 := bbase (se 5 (by rfl) ⟨338339, by rfl⟩ : syracuseStep 7217909 = 676679) (by norm_num)
theorem B2884373 : Blo 1279958 2884373 := bbase (se 6 (by rfl) ⟨67602, by rfl⟩ : syracuseStep 2884373 = 135205) (by norm_num)
theorem B1368857 : Blo 1279958 1368857 := bbase (se 2 (by rfl) ⟨513321, by rfl⟩ : syracuseStep 1368857 = 1026643) (by norm_num)
theorem B10937429 : Blo 1279958 10937429 := bbase (se 8 (by rfl) ⟨64086, by rfl⟩ : syracuseStep 10937429 = 128173) (by norm_num)
theorem B3646549 : Blo 1279958 3646549 := bbase (se 8 (by rfl) ⟨21366, by rfl⟩ : syracuseStep 3646549 = 42733) (by norm_num)
theorem B2737253 : Blo 1279958 2737253 := bbase (se 4 (by rfl) ⟨256617, by rfl⟩ : syracuseStep 2737253 = 513235) (by norm_num)
theorem B4326533 : Blo 1279958 4326533 := bbase (se 4 (by rfl) ⟨405612, by rfl⟩ : syracuseStep 4326533 = 811225) (by norm_num)
theorem B4867397 : Blo 1279958 4867397 := bbase (se 4 (by rfl) ⟨456318, by rfl⟩ : syracuseStep 4867397 = 912637) (by norm_num)
theorem B4105637 : Blo 1279958 4105637 := bbase (se 4 (by rfl) ⟨384903, by rfl⟩ : syracuseStep 4105637 = 769807) (by norm_num)
theorem B6489557 : Blo 1279958 6489557 := bbase (se 7 (by rfl) ⟨76049, by rfl⟩ : syracuseStep 6489557 = 152099) (by norm_num)
theorem B6235637 : Blo 1279958 6235637 := bbase (se 5 (by rfl) ⟨292295, by rfl⟩ : syracuseStep 6235637 = 584591) (by norm_num)
theorem B1459793 : Blo 1279958 1459793 := bbase (se 2 (by rfl) ⟨547422, by rfl⟩ : syracuseStep 1459793 = 1094845) (by norm_num)
theorem B26297941 : Blo 1279958 26297941 := bbase (se 8 (by rfl) ⟨154089, by rfl⟩ : syracuseStep 26297941 = 308179) (by norm_num)
theorem B5473925 : Blo 1279958 5473925 := bbase (se 4 (by rfl) ⟨513180, by rfl⟩ : syracuseStep 5473925 = 1026361) (by norm_num)
theorem B4679333 : Blo 1279958 4679333 := bbase (se 4 (by rfl) ⟨438687, by rfl⟩ : syracuseStep 4679333 = 877375) (by norm_num)
theorem B3163877 : Blo 1279958 3163877 := bbase (se 4 (by rfl) ⟨296613, by rfl⟩ : syracuseStep 3163877 = 593227) (by norm_num)
theorem B6481781 : Blo 1279958 6481781 := bbase (se 5 (by rfl) ⟨303833, by rfl⟩ : syracuseStep 6481781 = 607667) (by norm_num)
theorem B1730557 : Blo 1279958 1730557 := bbase (se 3 (by rfl) ⟨324479, by rfl⟩ : syracuseStep 1730557 = 648959) (by norm_num)
theorem B4859909 : Blo 1279958 4859909 := bbase (se 4 (by rfl) ⟨455616, by rfl⟩ : syracuseStep 4859909 = 911233) (by norm_num)
theorem B7293077 : Blo 1279958 7293077 := bbase (se 6 (by rfl) ⟨170931, by rfl⟩ : syracuseStep 7293077 = 341863) (by norm_num)
theorem B1460377 : Blo 1279958 1460377 := bbase (se 2 (by rfl) ⟨547641, by rfl⟩ : syracuseStep 1460377 = 1095283) (by norm_num)
theorem B2189629 : Blo 1279958 2189629 := bbase (se 3 (by rfl) ⟨410555, by rfl⟩ : syracuseStep 2189629 = 821111) (by norm_num)
theorem B6154613 : Blo 1279958 6154613 := bbase (se 5 (by rfl) ⟨288497, by rfl⟩ : syracuseStep 6154613 = 576995) (by norm_num)
theorem B2050429 : Blo 1279958 2050429 := bbase (se 3 (by rfl) ⟨384455, by rfl⟩ : syracuseStep 2050429 = 768911) (by norm_num)
theorem B4442597 : Blo 1279958 4442597 := bbase (se 4 (by rfl) ⟨416493, by rfl⟩ : syracuseStep 4442597 = 832987) (by norm_num)
theorem B20761109 : Blo 1279958 20761109 := bbase (se 6 (by rfl) ⟨486588, by rfl⟩ : syracuseStep 20761109 = 973177) (by norm_num)
theorem B3648053 : Blo 1279958 3648053 := bbase (se 5 (by rfl) ⟨171002, by rfl⟩ : syracuseStep 3648053 = 342005) (by norm_num)
theorem B8202869 : Blo 1279958 8202869 := bbase (se 5 (by rfl) ⟨384509, by rfl⟩ : syracuseStep 8202869 = 769019) (by norm_num)
theorem B2050685 : Blo 1279958 2050685 := bbase (se 3 (by rfl) ⟨384503, by rfl⟩ : syracuseStep 2050685 = 769007) (by norm_num)
theorem B7785173 : Blo 1279958 7785173 := bbase (se 7 (by rfl) ⟨91232, by rfl⟩ : syracuseStep 7785173 = 182465) (by norm_num)
theorem B4320053 : Blo 1279958 4320053 := bbase (se 5 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 4320053 = 405005) (by norm_num)
theorem B4614965 : Blo 1279958 4614965 := bbase (se 5 (by rfl) ⟨216326, by rfl⟩ : syracuseStep 4614965 = 432653) (by norm_num)
theorem B10529621 : Blo 1279958 10529621 := bbase (se 9 (by rfl) ⟨30848, by rfl⟩ : syracuseStep 10529621 = 61697) (by norm_num)
theorem B1919957 : Blo 1279958 1919957 := bbase (se 7 (by rfl) ⟨22499, by rfl⟩ : syracuseStep 1919957 = 44999) (by norm_num)
theorem B1919981 : Blo 1279958 1919981 := bbase (se 3 (by rfl) ⟨359996, by rfl⟩ : syracuseStep 1919981 = 719993) (by norm_num)
theorem B1920005 : Blo 1279958 1920005 := bbase (se 4 (by rfl) ⟨180000, by rfl⟩ : syracuseStep 1920005 = 360001) (by norm_num)
theorem B1920029 : Blo 1279958 1920029 := bbase (se 3 (by rfl) ⟨360005, by rfl⟩ : syracuseStep 1920029 = 720011) (by norm_num)
theorem B1920053 : Blo 1279958 1920053 := bbase (se 5 (by rfl) ⟨90002, by rfl⟩ : syracuseStep 1920053 = 180005) (by norm_num)
theorem B1387577 : Blo 1279958 1387577 := bbase (se 2 (by rfl) ⟨520341, by rfl⟩ : syracuseStep 1387577 = 1040683) (by norm_num)
theorem B1920077 : Blo 1279958 1920077 := bbase (se 3 (by rfl) ⟨360014, by rfl⟩ : syracuseStep 1920077 = 720029) (by norm_num)
theorem B1731677 : Blo 1279958 1731677 := bbase (se 3 (by rfl) ⟨324689, by rfl⟩ : syracuseStep 1731677 = 649379) (by norm_num)
theorem B1920101 : Blo 1279958 1920101 := bbase (se 4 (by rfl) ⟨180009, by rfl⟩ : syracuseStep 1920101 = 360019) (by norm_num)
theorem B1920125 : Blo 1279958 1920125 := bbase (se 3 (by rfl) ⟨360023, by rfl⟩ : syracuseStep 1920125 = 720047) (by norm_num)
theorem B6483077 : Blo 1279958 6483077 := bbase (se 4 (by rfl) ⟨607788, by rfl⟩ : syracuseStep 6483077 = 1215577) (by norm_num)
theorem B1920149 : Blo 1279958 1920149 := bbase (se 6 (by rfl) ⟨45003, by rfl⟩ : syracuseStep 1920149 = 90007) (by norm_num)
theorem B4861093 : Blo 1279958 4861093 := bbase (se 4 (by rfl) ⟨455727, by rfl⟩ : syracuseStep 4861093 = 911455) (by norm_num)
theorem B1920173 : Blo 1279958 1920173 := bbase (se 3 (by rfl) ⟨360032, by rfl⟩ : syracuseStep 1920173 = 720065) (by norm_num)
theorem B2772157 : Blo 1279958 2772157 := bbase (se 3 (by rfl) ⟨519779, by rfl⟩ : syracuseStep 2772157 = 1039559) (by norm_num)
theorem B1920197 : Blo 1279958 1920197 := bbase (se 4 (by rfl) ⟨180018, by rfl⟩ : syracuseStep 1920197 = 360037) (by norm_num)
theorem B1920221 : Blo 1279958 1920221 := bbase (se 3 (by rfl) ⟨360041, by rfl⟩ : syracuseStep 1920221 = 720083) (by norm_num)
theorem B4320485 : Blo 1279958 4320485 := bbase (se 4 (by rfl) ⟨405045, by rfl⟩ : syracuseStep 4320485 = 810091) (by norm_num)
theorem B1920245 : Blo 1279958 1920245 := bbase (se 5 (by rfl) ⟨90011, by rfl⟩ : syracuseStep 1920245 = 180023) (by norm_num)
theorem B3894533 : Blo 1279958 3894533 := bbase (se 4 (by rfl) ⟨365112, by rfl⟩ : syracuseStep 3894533 = 730225) (by norm_num)
theorem B1920269 : Blo 1279958 1920269 := bbase (se 3 (by rfl) ⟨360050, by rfl⟩ : syracuseStep 1920269 = 720101) (by norm_num)
theorem B1920293 : Blo 1279958 1920293 := bbase (se 4 (by rfl) ⟨180027, by rfl⟩ : syracuseStep 1920293 = 360055) (by norm_num)
theorem B1920317 : Blo 1279958 1920317 := bbase (se 3 (by rfl) ⟨360059, by rfl⟩ : syracuseStep 1920317 = 720119) (by norm_num)
theorem B2051389 : Blo 1279958 2051389 := bbase (se 3 (by rfl) ⟨384635, by rfl⟩ : syracuseStep 2051389 = 769271) (by norm_num)
theorem B1920341 : Blo 1279958 1920341 := bbase (se 11 (by rfl) ⟨1406, by rfl⟩ : syracuseStep 1920341 = 2813) (by norm_num)
theorem B1920365 : Blo 1279958 1920365 := bbase (se 3 (by rfl) ⟨360068, by rfl⟩ : syracuseStep 1920365 = 720137) (by norm_num)
theorem B5475701 : Blo 1279958 5475701 := bbase (se 5 (by rfl) ⟨256673, by rfl⟩ : syracuseStep 5475701 = 513347) (by norm_num)
theorem B1920389 : Blo 1279958 1920389 := bbase (se 4 (by rfl) ⟨180036, by rfl⟩ : syracuseStep 1920389 = 360073) (by norm_num)
theorem B10390933 : Blo 1279958 10390933 := bbase (se 6 (by rfl) ⟨243537, by rfl⟩ : syracuseStep 10390933 = 487075) (by norm_num)
theorem B1920413 : Blo 1279958 1920413 := bbase (se 3 (by rfl) ⟨360077, by rfl⟩ : syracuseStep 1920413 = 720155) (by norm_num)
theorem B1297829 : Blo 1279958 1297829 := bbase (se 4 (by rfl) ⟨121671, by rfl⟩ : syracuseStep 1297829 = 243343) (by norm_num)
theorem B1920437 : Blo 1279958 1920437 := bbase (se 5 (by rfl) ⟨90020, by rfl⟩ : syracuseStep 1920437 = 180041) (by norm_num)
theorem B1920461 : Blo 1279958 1920461 := bbase (se 3 (by rfl) ⟨360086, by rfl⟩ : syracuseStep 1920461 = 720173) (by norm_num)
theorem B4861397 : Blo 1279958 4861397 := bbase (se 7 (by rfl) ⟨56969, by rfl⟩ : syracuseStep 4861397 = 113939) (by norm_num)
theorem B5467621 : Blo 1279958 5467621 := bbase (se 4 (by rfl) ⟨512589, by rfl⟩ : syracuseStep 5467621 = 1025179) (by norm_num)
theorem B1920485 : Blo 1279958 1920485 := bbase (se 4 (by rfl) ⟨180045, by rfl⟩ : syracuseStep 1920485 = 360091) (by norm_num)
theorem B5467637 : Blo 1279958 5467637 := bbase (se 5 (by rfl) ⟨256295, by rfl⟩ : syracuseStep 5467637 = 512591) (by norm_num)
theorem B1920509 : Blo 1279958 1920509 := bbase (se 3 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 1920509 = 720191) (by norm_num)
theorem B1920533 : Blo 1279958 1920533 := bbase (se 6 (by rfl) ⟨45012, by rfl⟩ : syracuseStep 1920533 = 90025) (by norm_num)
theorem B1920557 : Blo 1279958 1920557 := bbase (se 3 (by rfl) ⟨360104, by rfl⟩ : syracuseStep 1920557 = 720209) (by norm_num)
theorem B1920581 : Blo 1279958 1920581 := bbase (se 4 (by rfl) ⟨180054, by rfl⟩ : syracuseStep 1920581 = 360109) (by norm_num)
theorem B1920605 : Blo 1279958 1920605 := bbase (se 3 (by rfl) ⟨360113, by rfl⟩ : syracuseStep 1920605 = 720227) (by norm_num)
theorem B1920629 : Blo 1279958 1920629 := bbase (se 5 (by rfl) ⟨90029, by rfl⟩ : syracuseStep 1920629 = 180059) (by norm_num)
theorem B1920653 : Blo 1279958 1920653 := bbase (se 3 (by rfl) ⟨360122, by rfl⟩ : syracuseStep 1920653 = 720245) (by norm_num)
theorem B4320917 : Blo 1279958 4320917 := bbase (se 6 (by rfl) ⟨101271, by rfl⟩ : syracuseStep 4320917 = 202543) (by norm_num)
theorem B8212117 : Blo 1279958 8212117 := bbase (se 6 (by rfl) ⟨192471, by rfl⟩ : syracuseStep 8212117 = 384943) (by norm_num)
theorem B1560217 : Blo 1279958 1560217 := bbase (se 2 (by rfl) ⟨585081, by rfl⟩ : syracuseStep 1560217 = 1170163) (by norm_num)
theorem B1920677 : Blo 1279958 1920677 := bbase (se 4 (by rfl) ⟨180063, by rfl⟩ : syracuseStep 1920677 = 360127) (by norm_num)
theorem B1920701 : Blo 1279958 1920701 := bbase (se 3 (by rfl) ⟨360131, by rfl⟩ : syracuseStep 1920701 = 720263) (by norm_num)
theorem B1920725 : Blo 1279958 1920725 := bbase (se 7 (by rfl) ⟨22508, by rfl⟩ : syracuseStep 1920725 = 45017) (by norm_num)
theorem B1732309 : Blo 1279958 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B2051813 : Blo 1279958 2051813 := bbase (se 4 (by rfl) ⟨192357, by rfl⟩ : syracuseStep 2051813 = 384715) (by norm_num)
theorem B1920749 : Blo 1279958 1920749 := bbase (se 3 (by rfl) ⟨360140, by rfl⟩ : syracuseStep 1920749 = 720281) (by norm_num)
theorem B1920773 : Blo 1279958 1920773 := bbase (se 4 (by rfl) ⟨180072, by rfl⟩ : syracuseStep 1920773 = 360145) (by norm_num)
theorem B1920797 : Blo 1279958 1920797 := bbase (se 3 (by rfl) ⟨360149, by rfl⟩ : syracuseStep 1920797 = 720299) (by norm_num)
theorem B2772773 : Blo 1279958 2772773 := bbase (se 4 (by rfl) ⟨259947, by rfl⟩ : syracuseStep 2772773 = 519895) (by norm_num)
theorem B1920821 : Blo 1279958 1920821 := bbase (se 5 (by rfl) ⟨90038, by rfl⟩ : syracuseStep 1920821 = 180077) (by norm_num)
theorem B1920845 : Blo 1279958 1920845 := bbase (se 3 (by rfl) ⟨360158, by rfl⟩ : syracuseStep 1920845 = 720317) (by norm_num)
theorem B1920869 : Blo 1279958 1920869 := bbase (se 4 (by rfl) ⟨180081, by rfl⟩ : syracuseStep 1920869 = 360163) (by norm_num)
theorem B1920893 : Blo 1279958 1920893 := bbase (se 3 (by rfl) ⟨360167, by rfl⟩ : syracuseStep 1920893 = 720335) (by norm_num)
theorem B1920917 : Blo 1279958 1920917 := bbase (se 6 (by rfl) ⟨45021, by rfl⟩ : syracuseStep 1920917 = 90043) (by norm_num)
theorem B1920941 : Blo 1279958 1920941 := bbase (se 3 (by rfl) ⟨360176, by rfl⟩ : syracuseStep 1920941 = 720353) (by norm_num)
theorem B1920965 : Blo 1279958 1920965 := bbase (se 4 (by rfl) ⟨180090, by rfl⟩ : syracuseStep 1920965 = 360181) (by norm_num)
theorem B1920989 : Blo 1279958 1920989 := bbase (se 3 (by rfl) ⟨360185, by rfl⟩ : syracuseStep 1920989 = 720371) (by norm_num)
theorem B3239909 : Blo 1279958 3239909 := bbase (se 4 (by rfl) ⟨303741, by rfl⟩ : syracuseStep 3239909 = 607483) (by norm_num)
theorem B1921013 : Blo 1279958 1921013 := bbase (se 5 (by rfl) ⟨90047, by rfl⟩ : syracuseStep 1921013 = 180095) (by norm_num)
theorem B2052101 : Blo 1279958 2052101 := bbase (se 4 (by rfl) ⟨192384, by rfl⟩ : syracuseStep 2052101 = 384769) (by norm_num)
theorem B1921037 : Blo 1279958 1921037 := bbase (se 3 (by rfl) ⟨360194, by rfl⟩ : syracuseStep 1921037 = 720389) (by norm_num)
theorem B1921061 : Blo 1279958 1921061 := bbase (se 4 (by rfl) ⟨180099, by rfl⟩ : syracuseStep 1921061 = 360199) (by norm_num)
theorem B1921085 : Blo 1279958 1921085 := bbase (se 3 (by rfl) ⟨360203, by rfl⟩ : syracuseStep 1921085 = 720407) (by norm_num)
theorem B4321349 : Blo 1279958 4321349 := bbase (se 4 (by rfl) ⟨405126, by rfl⟩ : syracuseStep 4321349 = 810253) (by norm_num)
theorem B1921109 : Blo 1279958 1921109 := bbase (se 8 (by rfl) ⟨11256, by rfl⟩ : syracuseStep 1921109 = 22513) (by norm_num)
theorem B3649637 : Blo 1279958 3649637 := bbase (se 4 (by rfl) ⟨342153, by rfl⟩ : syracuseStep 3649637 = 684307) (by norm_num)
theorem B1921133 : Blo 1279958 1921133 := bbase (se 3 (by rfl) ⟨360212, by rfl⟩ : syracuseStep 1921133 = 720425) (by norm_num)
theorem B1921157 : Blo 1279958 1921157 := bbase (se 4 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 1921157 = 360217) (by norm_num)
theorem B1921181 : Blo 1279958 1921181 := bbase (se 3 (by rfl) ⟨360221, by rfl⟩ : syracuseStep 1921181 = 720443) (by norm_num)
theorem B3240101 : Blo 1279958 3240101 := bbase (se 4 (by rfl) ⟨303759, by rfl⟩ : syracuseStep 3240101 = 607519) (by norm_num)
theorem B1921205 : Blo 1279958 1921205 := bbase (se 5 (by rfl) ⟨90056, by rfl⟩ : syracuseStep 1921205 = 180113) (by norm_num)
theorem B1921229 : Blo 1279958 1921229 := bbase (se 3 (by rfl) ⟨360230, by rfl⟩ : syracuseStep 1921229 = 720461) (by norm_num)
theorem B1822933 : Blo 1279958 1822933 := bbase (se 7 (by rfl) ⟨21362, by rfl⟩ : syracuseStep 1822933 = 42725) (by norm_num)
theorem B7794901 : Blo 1279958 7794901 := bbase (se 7 (by rfl) ⟨91346, by rfl⟩ : syracuseStep 7794901 = 182693) (by norm_num)
theorem B1921253 : Blo 1279958 1921253 := bbase (se 4 (by rfl) ⟨180117, by rfl⟩ : syracuseStep 1921253 = 360235) (by norm_num)
theorem B2052325 : Blo 1279958 2052325 := bbase (se 4 (by rfl) ⟨192405, by rfl⟩ : syracuseStep 2052325 = 384811) (by norm_num)
theorem B1921277 : Blo 1279958 1921277 := bbase (se 3 (by rfl) ⟨360239, by rfl⟩ : syracuseStep 1921277 = 720479) (by norm_num)
theorem B1921301 : Blo 1279958 1921301 := bbase (se 6 (by rfl) ⟨45030, by rfl⟩ : syracuseStep 1921301 = 90061) (by norm_num)
theorem B1921325 : Blo 1279958 1921325 := bbase (se 3 (by rfl) ⟨360248, by rfl⟩ : syracuseStep 1921325 = 720497) (by norm_num)
theorem B7295285 : Blo 1279958 7295285 := bbase (se 5 (by rfl) ⟨341966, by rfl⟩ : syracuseStep 7295285 = 683933) (by norm_num)
theorem B5845301 : Blo 1279958 5845301 := bbase (se 5 (by rfl) ⟨273998, by rfl⟩ : syracuseStep 5845301 = 547997) (by norm_num)
theorem B1921349 : Blo 1279958 1921349 := bbase (se 4 (by rfl) ⟨180126, by rfl⟩ : syracuseStep 1921349 = 360253) (by norm_num)
theorem B1298761 : Blo 1279958 1298761 := bbase (se 2 (by rfl) ⟨487035, by rfl⟩ : syracuseStep 1298761 = 974071) (by norm_num)
theorem B1921373 : Blo 1279958 1921373 := bbase (se 3 (by rfl) ⟨360257, by rfl⟩ : syracuseStep 1921373 = 720515) (by norm_num)
theorem B3076469 : Blo 1279958 3076469 := bbase (se 5 (by rfl) ⟨144209, by rfl⟩ : syracuseStep 3076469 = 288419) (by norm_num)
theorem B1921397 : Blo 1279958 1921397 := bbase (se 5 (by rfl) ⟨90065, by rfl⟩ : syracuseStep 1921397 = 180131) (by norm_num)
theorem B1921421 : Blo 1279958 1921421 := bbase (se 3 (by rfl) ⟨360266, by rfl⟩ : syracuseStep 1921421 = 720533) (by norm_num)
theorem B6484373 : Blo 1279958 6484373 := bbase (se 6 (by rfl) ⟨151977, by rfl⟩ : syracuseStep 6484373 = 303955) (by norm_num)
theorem B2879909 : Blo 1279958 2879909 := bbase (se 4 (by rfl) ⟨269991, by rfl⟩ : syracuseStep 2879909 = 539983) (by norm_num)
theorem B1921445 : Blo 1279958 1921445 := bbase (se 4 (by rfl) ⟨180135, by rfl⟩ : syracuseStep 1921445 = 360271) (by norm_num)
theorem B1921469 : Blo 1279958 1921469 := bbase (se 3 (by rfl) ⟨360275, by rfl⟩ : syracuseStep 1921469 = 720551) (by norm_num)
theorem B1642961 : Blo 1279958 1642961 := bbase (se 2 (by rfl) ⟨616110, by rfl⟩ : syracuseStep 1642961 = 1232221) (by norm_num)
theorem B1921493 : Blo 1279958 1921493 := bbase (se 7 (by rfl) ⟨22517, by rfl⟩ : syracuseStep 1921493 = 45035) (by norm_num)
theorem B2879981 : Blo 1279958 2879981 := bbase (se 3 (by rfl) ⟨539996, by rfl⟩ : syracuseStep 2879981 = 1079993) (by norm_num)
theorem B1921517 : Blo 1279958 1921517 := bbase (se 3 (by rfl) ⟨360284, by rfl⟩ : syracuseStep 1921517 = 720569) (by norm_num)
theorem B4321781 : Blo 1279958 4321781 := bbase (se 5 (by rfl) ⟨202583, by rfl⟩ : syracuseStep 4321781 = 405167) (by norm_num)
theorem B3240445 : Blo 1279958 3240445 := bbase (se 3 (by rfl) ⟨607583, by rfl⟩ : syracuseStep 3240445 = 1215167) (by norm_num)
theorem B1921541 : Blo 1279958 1921541 := bbase (se 4 (by rfl) ⟨180144, by rfl⟩ : syracuseStep 1921541 = 360289) (by norm_num)
theorem B1921565 : Blo 1279958 1921565 := bbase (se 3 (by rfl) ⟨360293, by rfl⟩ : syracuseStep 1921565 = 720587) (by norm_num)
theorem B2880053 : Blo 1279958 2880053 := bbase (se 5 (by rfl) ⟨135002, by rfl⟩ : syracuseStep 2880053 = 270005) (by norm_num)
theorem B3076661 : Blo 1279958 3076661 := bbase (se 5 (by rfl) ⟨144218, by rfl⟩ : syracuseStep 3076661 = 288437) (by norm_num)
theorem B1921589 : Blo 1279958 1921589 := bbase (se 5 (by rfl) ⟨90074, by rfl⟩ : syracuseStep 1921589 = 180149) (by norm_num)
theorem B1921613 : Blo 1279958 1921613 := bbase (se 3 (by rfl) ⟨360302, by rfl⟩ : syracuseStep 1921613 = 720605) (by norm_num)
theorem B1921637 : Blo 1279958 1921637 := bbase (se 4 (by rfl) ⟨180153, by rfl⟩ : syracuseStep 1921637 = 360307) (by norm_num)
theorem B3240557 : Blo 1279958 3240557 := bbase (se 3 (by rfl) ⟨607604, by rfl⟩ : syracuseStep 3240557 = 1215209) (by norm_num)
theorem B2880125 : Blo 1279958 2880125 := bbase (se 3 (by rfl) ⟨540023, by rfl⟩ : syracuseStep 2880125 = 1080047) (by norm_num)
theorem B1921661 : Blo 1279958 1921661 := bbase (se 3 (by rfl) ⟨360311, by rfl⟩ : syracuseStep 1921661 = 720623) (by norm_num)
theorem B1921685 : Blo 1279958 1921685 := bbase (se 6 (by rfl) ⟨45039, by rfl⟩ : syracuseStep 1921685 = 90079) (by norm_num)
theorem B16642709 : Blo 1279958 16642709 := bbase (se 6 (by rfl) ⟨390063, by rfl⟩ : syracuseStep 16642709 = 780127) (by norm_num)
theorem B1921709 : Blo 1279958 1921709 := bbase (se 3 (by rfl) ⟨360320, by rfl⟩ : syracuseStep 1921709 = 720641) (by norm_num)
theorem B2880197 : Blo 1279958 2880197 := bbase (se 4 (by rfl) ⟨270018, by rfl⟩ : syracuseStep 2880197 = 540037) (by norm_num)
theorem B1921733 : Blo 1279958 1921733 := bbase (se 4 (by rfl) ⟨180162, by rfl⟩ : syracuseStep 1921733 = 360325) (by norm_num)
theorem B1921757 : Blo 1279958 1921757 := bbase (se 3 (by rfl) ⟨360329, by rfl⟩ : syracuseStep 1921757 = 720659) (by norm_num)
theorem B4444901 : Blo 1279958 4444901 := bbase (se 4 (by rfl) ⟨416709, by rfl⟩ : syracuseStep 4444901 = 833419) (by norm_num)
theorem B1921781 : Blo 1279958 1921781 := bbase (se 5 (by rfl) ⟨90083, by rfl⟩ : syracuseStep 1921781 = 180167) (by norm_num)
theorem B3650309 : Blo 1279958 3650309 := bbase (se 4 (by rfl) ⟨342216, by rfl⟩ : syracuseStep 3650309 = 684433) (by norm_num)
theorem B2880269 : Blo 1279958 2880269 := bbase (se 3 (by rfl) ⟨540050, by rfl⟩ : syracuseStep 2880269 = 1080101) (by norm_num)
theorem B1921805 : Blo 1279958 1921805 := bbase (se 3 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 1921805 = 720677) (by norm_num)
theorem B1921829 : Blo 1279958 1921829 := bbase (se 4 (by rfl) ⟨180171, by rfl⟩ : syracuseStep 1921829 = 360343) (by norm_num)
theorem B3240749 : Blo 1279958 3240749 := bbase (se 3 (by rfl) ⟨607640, by rfl⟩ : syracuseStep 3240749 = 1215281) (by norm_num)
theorem B1921853 : Blo 1279958 1921853 := bbase (se 3 (by rfl) ⟨360347, by rfl⟩ : syracuseStep 1921853 = 720695) (by norm_num)
theorem B2880341 : Blo 1279958 2880341 := bbase (se 9 (by rfl) ⟨8438, by rfl⟩ : syracuseStep 2880341 = 16877) (by norm_num)
theorem B1921877 : Blo 1279958 1921877 := bbase (se 9 (by rfl) ⟨5630, by rfl⟩ : syracuseStep 1921877 = 11261) (by norm_num)
theorem B1921901 : Blo 1279958 1921901 := bbase (se 3 (by rfl) ⟨360356, by rfl⟩ : syracuseStep 1921901 = 720713) (by norm_num)
theorem B9237365 : Blo 1279958 9237365 := bbase (se 5 (by rfl) ⟨433001, by rfl⟩ : syracuseStep 9237365 = 866003) (by norm_num)
theorem B1921925 : Blo 1279958 1921925 := bbase (se 4 (by rfl) ⟨180180, by rfl⟩ : syracuseStep 1921925 = 360361) (by norm_num)
theorem B2880413 : Blo 1279958 2880413 := bbase (se 3 (by rfl) ⟨540077, by rfl⟩ : syracuseStep 2880413 = 1080155) (by norm_num)
theorem B1921949 : Blo 1279958 1921949 := bbase (se 3 (by rfl) ⟨360365, by rfl⟩ : syracuseStep 1921949 = 720731) (by norm_num)
theorem B4322213 : Blo 1279958 4322213 := bbase (se 4 (by rfl) ⟨405207, by rfl⟩ : syracuseStep 4322213 = 810415) (by norm_num)
theorem B1921973 : Blo 1279958 1921973 := bbase (se 5 (by rfl) ⟨90092, by rfl⟩ : syracuseStep 1921973 = 180185) (by norm_num)
theorem B1921997 : Blo 1279958 1921997 := bbase (se 3 (by rfl) ⟨360374, by rfl⟩ : syracuseStep 1921997 = 720749) (by norm_num)
theorem B2880485 : Blo 1279958 2880485 := bbase (se 4 (by rfl) ⟨270045, by rfl⟩ : syracuseStep 2880485 = 540091) (by norm_num)
theorem B1922021 : Blo 1279958 1922021 := bbase (se 4 (by rfl) ⟨180189, by rfl⟩ : syracuseStep 1922021 = 360379) (by norm_num)
theorem B1823725 : Blo 1279958 1823725 := bbase (se 3 (by rfl) ⟨341948, by rfl⟩ : syracuseStep 1823725 = 683897) (by norm_num)
theorem B2192365 : Blo 1279958 2192365 := bbase (se 3 (by rfl) ⟨411068, by rfl⟩ : syracuseStep 2192365 = 822137) (by norm_num)
theorem B1922045 : Blo 1279958 1922045 := bbase (se 3 (by rfl) ⟨360383, by rfl⟩ : syracuseStep 1922045 = 720767) (by norm_num)
theorem B1922069 : Blo 1279958 1922069 := bbase (se 6 (by rfl) ⟨45048, by rfl⟩ : syracuseStep 1922069 = 90097) (by norm_num)
theorem B2880557 : Blo 1279958 2880557 := bbase (se 3 (by rfl) ⟨540104, by rfl⟩ : syracuseStep 2880557 = 1080209) (by norm_num)
theorem B1922093 : Blo 1279958 1922093 := bbase (se 3 (by rfl) ⟨360392, by rfl⟩ : syracuseStep 1922093 = 720785) (by norm_num)
theorem B1643581 : Blo 1279958 1643581 := bbase (se 3 (by rfl) ⟨308171, by rfl⟩ : syracuseStep 1643581 = 616343) (by norm_num)
theorem B1922117 : Blo 1279958 1922117 := bbase (se 4 (by rfl) ⟨180198, by rfl⟩ : syracuseStep 1922117 = 360397) (by norm_num)
theorem B6157397 : Blo 1279958 6157397 := bbase (se 8 (by rfl) ⟨36078, by rfl⟩ : syracuseStep 6157397 = 72157) (by norm_num)
theorem B1922141 : Blo 1279958 1922141 := bbase (se 3 (by rfl) ⟨360401, by rfl⟩ : syracuseStep 1922141 = 720803) (by norm_num)
theorem B2880629 : Blo 1279958 2880629 := bbase (se 5 (by rfl) ⟨135029, by rfl⟩ : syracuseStep 2880629 = 270059) (by norm_num)
theorem B1922165 : Blo 1279958 1922165 := bbase (se 5 (by rfl) ⟨90101, by rfl⟩ : syracuseStep 1922165 = 180203) (by norm_num)
theorem B3241093 : Blo 1279958 3241093 := bbase (se 4 (by rfl) ⟨303852, by rfl⟩ : syracuseStep 3241093 = 607705) (by norm_num)
theorem B1922189 : Blo 1279958 1922189 := bbase (se 3 (by rfl) ⟨360410, by rfl⟩ : syracuseStep 1922189 = 720821) (by norm_num)
theorem B1922213 : Blo 1279958 1922213 := bbase (se 4 (by rfl) ⟨180207, by rfl⟩ : syracuseStep 1922213 = 360415) (by norm_num)
theorem B2880701 : Blo 1279958 2880701 := bbase (se 3 (by rfl) ⟨540131, by rfl⟩ : syracuseStep 2880701 = 1080263) (by norm_num)
theorem B1922237 : Blo 1279958 1922237 := bbase (se 3 (by rfl) ⟨360419, by rfl⟩ : syracuseStep 1922237 = 720839) (by norm_num)
theorem B17528021 : Blo 1279958 17528021 := bbase (se 7 (by rfl) ⟨205406, by rfl⟩ : syracuseStep 17528021 = 410813) (by norm_num)
theorem B16643285 : Blo 1279958 16643285 := bbase (se 7 (by rfl) ⟨195038, by rfl⟩ : syracuseStep 16643285 = 390077) (by norm_num)
theorem B1922261 : Blo 1279958 1922261 := bbase (se 7 (by rfl) ⟨22526, by rfl⟩ : syracuseStep 1922261 = 45053) (by norm_num)
theorem B1922285 : Blo 1279958 1922285 := bbase (se 3 (by rfl) ⟨360428, by rfl⟩ : syracuseStep 1922285 = 720857) (by norm_num)
theorem B3241205 : Blo 1279958 3241205 := bbase (se 5 (by rfl) ⟨151931, by rfl⟩ : syracuseStep 3241205 = 303863) (by norm_num)
theorem B2667773 : Blo 1279958 2667773 := bbase (se 3 (by rfl) ⟨500207, by rfl⟩ : syracuseStep 2667773 = 1000415) (by norm_num)
theorem B2880773 : Blo 1279958 2880773 := bbase (se 4 (by rfl) ⟨270072, by rfl⟩ : syracuseStep 2880773 = 540145) (by norm_num)
theorem B1922309 : Blo 1279958 1922309 := bbase (se 4 (by rfl) ⟨180216, by rfl⟩ : syracuseStep 1922309 = 360433) (by norm_num)
theorem B24638741 : Blo 1279958 24638741 := bbase (se 6 (by rfl) ⟨577470, by rfl⟩ : syracuseStep 24638741 = 1154941) (by norm_num)
theorem B1922333 : Blo 1279958 1922333 := bbase (se 3 (by rfl) ⟨360437, by rfl⟩ : syracuseStep 1922333 = 720875) (by norm_num)
theorem B1922357 : Blo 1279958 1922357 := bbase (se 5 (by rfl) ⟨90110, by rfl⟩ : syracuseStep 1922357 = 180221) (by norm_num)
theorem B1824061 : Blo 1279958 1824061 := bbase (se 3 (by rfl) ⟨342011, by rfl⟩ : syracuseStep 1824061 = 684023) (by norm_num)
theorem B4101445 : Blo 1279958 4101445 := bbase (se 4 (by rfl) ⟨384510, by rfl⟩ : syracuseStep 4101445 = 769021) (by norm_num)
theorem B2880845 : Blo 1279958 2880845 := bbase (se 3 (by rfl) ⟨540158, by rfl⟩ : syracuseStep 2880845 = 1080317) (by norm_num)
theorem B1922381 : Blo 1279958 1922381 := bbase (se 3 (by rfl) ⟨360446, by rfl⟩ : syracuseStep 1922381 = 720893) (by norm_num)
theorem B4322645 : Blo 1279958 4322645 := bbase (se 13 (by rfl) ⟨791, by rfl⟩ : syracuseStep 4322645 = 1583) (by norm_num)
theorem B1922405 : Blo 1279958 1922405 := bbase (se 4 (by rfl) ⟨180225, by rfl⟩ : syracuseStep 1922405 = 360451) (by norm_num)
theorem B1922429 : Blo 1279958 1922429 := bbase (se 3 (by rfl) ⟨360455, by rfl⟩ : syracuseStep 1922429 = 720911) (by norm_num)
theorem B2160013 : Blo 1279958 2160013 := bbase (se 3 (by rfl) ⟨405002, by rfl⟩ : syracuseStep 2160013 = 810005) (by norm_num)
theorem B2880917 : Blo 1279958 2880917 := bbase (se 6 (by rfl) ⟨67521, by rfl⟩ : syracuseStep 2880917 = 135043) (by norm_num)
theorem B1922453 : Blo 1279958 1922453 := bbase (se 6 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 1922453 = 90115) (by norm_num)
theorem B2463149 : Blo 1279958 2463149 := bbase (se 3 (by rfl) ⟨461840, by rfl⟩ : syracuseStep 2463149 = 923681) (by norm_num)
theorem B1922477 : Blo 1279958 1922477 := bbase (se 3 (by rfl) ⟨360464, by rfl⟩ : syracuseStep 1922477 = 720929) (by norm_num)
theorem B1480117 : Blo 1279958 1480117 := bbase (se 5 (by rfl) ⟨69380, by rfl⟩ : syracuseStep 1480117 = 138761) (by norm_num)
theorem B3241397 : Blo 1279958 3241397 := bbase (se 5 (by rfl) ⟨151940, by rfl⟩ : syracuseStep 3241397 = 303881) (by norm_num)
theorem B1922501 : Blo 1279958 1922501 := bbase (se 4 (by rfl) ⟨180234, by rfl⟩ : syracuseStep 1922501 = 360469) (by norm_num)
theorem B2880989 : Blo 1279958 2880989 := bbase (se 3 (by rfl) ⟨540185, by rfl⟩ : syracuseStep 2880989 = 1080371) (by norm_num)
theorem B1922525 : Blo 1279958 1922525 := bbase (se 3 (by rfl) ⟨360473, by rfl⟩ : syracuseStep 1922525 = 720947) (by norm_num)
theorem B2160101 : Blo 1279958 2160101 := bbase (se 4 (by rfl) ⟨202509, by rfl⟩ : syracuseStep 2160101 = 405019) (by norm_num)
theorem B1922549 : Blo 1279958 1922549 := bbase (se 5 (by rfl) ⟨90119, by rfl⟩ : syracuseStep 1922549 = 180239) (by norm_num)
theorem B1922573 : Blo 1279958 1922573 := bbase (se 3 (by rfl) ⟨360482, by rfl⟩ : syracuseStep 1922573 = 720965) (by norm_num)
theorem B4863509 : Blo 1279958 4863509 := bbase (se 6 (by rfl) ⟨113988, by rfl⟩ : syracuseStep 4863509 = 227977) (by norm_num)
theorem B1824277 : Blo 1279958 1824277 := bbase (se 6 (by rfl) ⟨42756, by rfl⟩ : syracuseStep 1824277 = 85513) (by norm_num)
theorem B7796245 : Blo 1279958 7796245 := bbase (se 6 (by rfl) ⟨182724, by rfl⟩ : syracuseStep 7796245 = 365449) (by norm_num)
theorem B2881061 : Blo 1279958 2881061 := bbase (se 4 (by rfl) ⟨270099, by rfl⟩ : syracuseStep 2881061 = 540199) (by norm_num)
theorem B1922597 : Blo 1279958 1922597 := bbase (se 4 (by rfl) ⟨180243, by rfl⟩ : syracuseStep 1922597 = 360487) (by norm_num)
theorem B1922621 : Blo 1279958 1922621 := bbase (se 3 (by rfl) ⟨360491, by rfl⟩ : syracuseStep 1922621 = 720983) (by norm_num)
theorem B1922645 : Blo 1279958 1922645 := bbase (se 8 (by rfl) ⟨11265, by rfl⟩ : syracuseStep 1922645 = 22531) (by norm_num)
theorem B2160229 : Blo 1279958 2160229 := bbase (se 4 (by rfl) ⟨202521, by rfl⟩ : syracuseStep 2160229 = 405043) (by norm_num)
theorem B2881133 : Blo 1279958 2881133 := bbase (se 3 (by rfl) ⟨540212, by rfl⟩ : syracuseStep 2881133 = 1080425) (by norm_num)
theorem B1922669 : Blo 1279958 1922669 := bbase (se 3 (by rfl) ⟨360500, by rfl⟩ : syracuseStep 1922669 = 721001) (by norm_num)
theorem B1922693 : Blo 1279958 1922693 := bbase (se 4 (by rfl) ⟨180252, by rfl⟩ : syracuseStep 1922693 = 360505) (by norm_num)
theorem B1922717 : Blo 1279958 1922717 := bbase (se 3 (by rfl) ⟨360509, by rfl⟩ : syracuseStep 1922717 = 721019) (by norm_num)
theorem B6485669 : Blo 1279958 6485669 := bbase (se 4 (by rfl) ⟨608031, by rfl⟩ : syracuseStep 6485669 = 1216063) (by norm_num)
theorem B2881205 : Blo 1279958 2881205 := bbase (se 5 (by rfl) ⟨135056, by rfl⟩ : syracuseStep 2881205 = 270113) (by norm_num)
theorem B1922741 : Blo 1279958 1922741 := bbase (se 5 (by rfl) ⟨90128, by rfl⟩ : syracuseStep 1922741 = 180257) (by norm_num)
theorem B2160317 : Blo 1279958 2160317 := bbase (se 3 (by rfl) ⟨405059, by rfl⟩ : syracuseStep 2160317 = 810119) (by norm_num)
theorem B2430661 : Blo 1279958 2430661 := bbase (se 4 (by rfl) ⟨227874, by rfl⟩ : syracuseStep 2430661 = 455749) (by norm_num)
theorem B5469893 : Blo 1279958 5469893 := bbase (se 4 (by rfl) ⟨512802, by rfl⟩ : syracuseStep 5469893 = 1025605) (by norm_num)
theorem B1922765 : Blo 1279958 1922765 := bbase (se 3 (by rfl) ⟨360518, by rfl⟩ : syracuseStep 1922765 = 721037) (by norm_num)
theorem B1922789 : Blo 1279958 1922789 := bbase (se 4 (by rfl) ⟨180261, by rfl⟩ : syracuseStep 1922789 = 360523) (by norm_num)
theorem B8206069 : Blo 1279958 8206069 := bbase (se 5 (by rfl) ⟨384659, by rfl⟩ : syracuseStep 8206069 = 769319) (by norm_num)
theorem B2881277 : Blo 1279958 2881277 := bbase (se 3 (by rfl) ⟨540239, by rfl⟩ : syracuseStep 2881277 = 1080479) (by norm_num)
theorem B1922813 : Blo 1279958 1922813 := bbase (se 3 (by rfl) ⟨360527, by rfl⟩ : syracuseStep 1922813 = 721055) (by norm_num)
theorem B4323077 : Blo 1279958 4323077 := bbase (se 4 (by rfl) ⟨405288, by rfl⟩ : syracuseStep 4323077 = 810577) (by norm_num)
theorem B3241741 : Blo 1279958 3241741 := bbase (se 3 (by rfl) ⟨607826, by rfl⟩ : syracuseStep 3241741 = 1215653) (by norm_num)
theorem B1922837 : Blo 1279958 1922837 := bbase (se 6 (by rfl) ⟨45066, by rfl⟩ : syracuseStep 1922837 = 90133) (by norm_num)
theorem B2733853 : Blo 1279958 2733853 := bbase (se 3 (by rfl) ⟨512597, by rfl⟩ : syracuseStep 2733853 = 1025195) (by norm_num)
theorem B1922861 : Blo 1279958 1922861 := bbase (se 3 (by rfl) ⟨360536, by rfl⟩ : syracuseStep 1922861 = 721073) (by norm_num)
theorem B4863797 : Blo 1279958 4863797 := bbase (se 5 (by rfl) ⟨227990, by rfl⟩ : syracuseStep 4863797 = 455981) (by norm_num)
theorem B2160445 : Blo 1279958 2160445 := bbase (se 3 (by rfl) ⟨405083, by rfl⟩ : syracuseStep 2160445 = 810167) (by norm_num)
theorem B2881349 : Blo 1279958 2881349 := bbase (se 4 (by rfl) ⟨270126, by rfl⟩ : syracuseStep 2881349 = 540253) (by norm_num)
theorem B1947461 : Blo 1279958 1947461 := bbase (se 4 (by rfl) ⟨182574, by rfl⟩ : syracuseStep 1947461 = 365149) (by norm_num)
theorem B1922885 : Blo 1279958 1922885 := bbase (se 4 (by rfl) ⟨180270, by rfl⟩ : syracuseStep 1922885 = 360541) (by norm_num)
theorem B2430805 : Blo 1279958 2430805 := bbase (se 9 (by rfl) ⟨7121, by rfl⟩ : syracuseStep 2430805 = 14243) (by norm_num)
theorem B1922909 : Blo 1279958 1922909 := bbase (se 3 (by rfl) ⟨360545, by rfl⟩ : syracuseStep 1922909 = 721091) (by norm_num)
theorem B1922933 : Blo 1279958 1922933 := bbase (se 5 (by rfl) ⟨90137, by rfl⟩ : syracuseStep 1922933 = 180275) (by norm_num)
theorem B3241853 : Blo 1279958 3241853 := bbase (se 3 (by rfl) ⟨607847, by rfl⟩ : syracuseStep 3241853 = 1215695) (by norm_num)
theorem B2881421 : Blo 1279958 2881421 := bbase (se 3 (by rfl) ⟨540266, by rfl⟩ : syracuseStep 2881421 = 1080533) (by norm_num)
theorem B1824653 : Blo 1279958 1824653 := bbase (se 3 (by rfl) ⟨342122, by rfl⟩ : syracuseStep 1824653 = 684245) (by norm_num)
theorem B2160533 : Blo 1279958 2160533 := bbase (se 6 (by rfl) ⟨50637, by rfl⟩ : syracuseStep 2160533 = 101275) (by norm_num)
theorem B1537985 : Blo 1279958 1537985 := bbase (se 2 (by rfl) ⟨576744, by rfl⟩ : syracuseStep 1537985 = 1153489) (by norm_num)
theorem B2881493 : Blo 1279958 2881493 := bbase (se 7 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 2881493 = 67535) (by norm_num)
theorem B2430965 : Blo 1279958 2430965 := bbase (se 5 (by rfl) ⟨113951, by rfl⟩ : syracuseStep 2430965 = 227903) (by norm_num)
theorem B2160661 : Blo 1279958 2160661 := bbase (se 6 (by rfl) ⟨50640, by rfl⟩ : syracuseStep 2160661 = 101281) (by norm_num)
theorem B2308117 : Blo 1279958 2308117 := bbase (se 6 (by rfl) ⟨54096, by rfl⟩ : syracuseStep 2308117 = 108193) (by norm_num)
theorem B2881565 : Blo 1279958 2881565 := bbase (se 3 (by rfl) ⟨540293, by rfl⟩ : syracuseStep 2881565 = 1080587) (by norm_num)
theorem B3242045 : Blo 1279958 3242045 := bbase (se 3 (by rfl) ⟨607883, by rfl⟩ : syracuseStep 3242045 = 1215767) (by norm_num)
theorem B2308189 : Blo 1279958 2308189 := bbase (se 3 (by rfl) ⟨432785, by rfl⟩ : syracuseStep 2308189 = 865571) (by norm_num)
theorem B2881637 : Blo 1279958 2881637 := bbase (se 4 (by rfl) ⟨270153, by rfl⟩ : syracuseStep 2881637 = 540307) (by norm_num)
theorem B2160749 : Blo 1279958 2160749 := bbase (se 3 (by rfl) ⟨405140, by rfl⟩ : syracuseStep 2160749 = 810281) (by norm_num)
theorem B1620101 : Blo 1279958 1620101 := bbase (se 4 (by rfl) ⟨151884, by rfl⟩ : syracuseStep 1620101 = 303769) (by norm_num)
theorem B2431109 : Blo 1279958 2431109 := bbase (se 4 (by rfl) ⟨227916, by rfl⟩ : syracuseStep 2431109 = 455833) (by norm_num)
theorem B2734229 : Blo 1279958 2734229 := bbase (se 6 (by rfl) ⟨64083, by rfl⟩ : syracuseStep 2734229 = 128167) (by norm_num)
theorem B2881709 : Blo 1279958 2881709 := bbase (se 3 (by rfl) ⟨540320, by rfl⟩ : syracuseStep 2881709 = 1080641) (by norm_num)
theorem B4323509 : Blo 1279958 4323509 := bbase (se 5 (by rfl) ⟨202664, by rfl⟩ : syracuseStep 4323509 = 405329) (by norm_num)
theorem B1620157 : Blo 1279958 1620157 := bbase (se 3 (by rfl) ⟨303779, by rfl⟩ : syracuseStep 1620157 = 607559) (by norm_num)
theorem B1439977 : Blo 1279958 1439977 := bbase (se 2 (by rfl) ⟨539991, by rfl⟩ : syracuseStep 1439977 = 1079983) (by norm_num)
theorem B2160877 : Blo 1279958 2160877 := bbase (se 3 (by rfl) ⟨405164, by rfl⟩ : syracuseStep 2160877 = 810329) (by norm_num)
theorem B1538293 : Blo 1279958 1538293 := bbase (se 5 (by rfl) ⟨72107, by rfl⟩ : syracuseStep 1538293 = 144215) (by norm_num)
theorem B2881781 : Blo 1279958 2881781 := bbase (se 5 (by rfl) ⟨135083, by rfl⟩ : syracuseStep 2881781 = 270167) (by norm_num)
theorem B9861365 : Blo 1279958 9861365 := bbase (se 5 (by rfl) ⟨462251, by rfl⟩ : syracuseStep 9861365 = 924503) (by norm_num)
theorem B1440013 : Blo 1279958 1440013 := bbase (se 3 (by rfl) ⟨270002, by rfl⟩ : syracuseStep 1440013 = 540005) (by norm_num)
theorem B1620253 : Blo 1279958 1620253 := bbase (se 3 (by rfl) ⟨303797, by rfl⟩ : syracuseStep 1620253 = 607595) (by norm_num)
theorem B1440049 : Blo 1279958 1440049 := bbase (se 2 (by rfl) ⟨540018, by rfl⟩ : syracuseStep 1440049 = 1080037) (by norm_num)
theorem B2922797 : Blo 1279958 2922797 := bbase (se 3 (by rfl) ⟨548024, by rfl⟩ : syracuseStep 2922797 = 1096049) (by norm_num)
theorem B2881853 : Blo 1279958 2881853 := bbase (se 3 (by rfl) ⟨540347, by rfl⟩ : syracuseStep 2881853 = 1080695) (by norm_num)
theorem B2160965 : Blo 1279958 2160965 := bbase (se 4 (by rfl) ⟨202590, by rfl⟩ : syracuseStep 2160965 = 405181) (by norm_num)
theorem B1440085 : Blo 1279958 1440085 := bbase (se 10 (by rfl) ⟨2109, by rfl⟩ : syracuseStep 1440085 = 4219) (by norm_num)
theorem B1440121 : Blo 1279958 1440121 := bbase (se 2 (by rfl) ⟨540045, by rfl⟩ : syracuseStep 1440121 = 1080091) (by norm_num)
theorem B2881925 : Blo 1279958 2881925 := bbase (se 4 (by rfl) ⟨270180, by rfl⟩ : syracuseStep 2881925 = 540361) (by norm_num)
theorem B1948045 : Blo 1279958 1948045 := bbase (se 3 (by rfl) ⟨365258, by rfl⟩ : syracuseStep 1948045 = 730517) (by norm_num)
theorem B3242389 : Blo 1279958 3242389 := bbase (se 6 (by rfl) ⟨75993, by rfl⟩ : syracuseStep 3242389 = 151987) (by norm_num)
theorem B1440157 : Blo 1279958 1440157 := bbase (se 3 (by rfl) ⟨270029, by rfl⟩ : syracuseStep 1440157 = 540059) (by norm_num)
theorem B1538461 : Blo 1279958 1538461 := bbase (se 3 (by rfl) ⟨288461, by rfl⟩ : syracuseStep 1538461 = 576923) (by norm_num)
theorem B2431397 : Blo 1279958 2431397 := bbase (se 4 (by rfl) ⟨227943, by rfl⟩ : syracuseStep 2431397 = 455887) (by norm_num)
theorem B1440193 : Blo 1279958 1440193 := bbase (se 2 (by rfl) ⟨540072, by rfl⟩ : syracuseStep 1440193 = 1080145) (by norm_num)
theorem B2595269 : Blo 1279958 2595269 := bbase (se 4 (by rfl) ⟨243306, by rfl⟩ : syracuseStep 2595269 = 486613) (by norm_num)
theorem B2161093 : Blo 1279958 2161093 := bbase (se 4 (by rfl) ⟨202602, by rfl⟩ : syracuseStep 2161093 = 405205) (by norm_num)
theorem B1620425 : Blo 1279958 1620425 := bbase (se 2 (by rfl) ⟨607659, by rfl⟩ : syracuseStep 1620425 = 1215319) (by norm_num)
theorem B2881997 : Blo 1279958 2881997 := bbase (se 3 (by rfl) ⟨540374, by rfl⟩ : syracuseStep 2881997 = 1080749) (by norm_num)
theorem B1440229 : Blo 1279958 1440229 := bbase (se 4 (by rfl) ⟨135021, by rfl⟩ : syracuseStep 1440229 = 270043) (by norm_num)
theorem B1620481 : Blo 1279958 1620481 := bbase (se 2 (by rfl) ⟨607680, by rfl⟩ : syracuseStep 1620481 = 1215361) (by norm_num)
theorem B3242501 : Blo 1279958 3242501 := bbase (se 4 (by rfl) ⟨303984, by rfl⟩ : syracuseStep 3242501 = 607969) (by norm_num)
theorem B3078661 : Blo 1279958 3078661 := bbase (se 4 (by rfl) ⟨288624, by rfl⟩ : syracuseStep 3078661 = 577249) (by norm_num)
theorem B1440265 : Blo 1279958 1440265 := bbase (se 2 (by rfl) ⟨540099, by rfl⟩ : syracuseStep 1440265 = 1080199) (by norm_num)
theorem B2882069 : Blo 1279958 2882069 := bbase (se 6 (by rfl) ⟨67548, by rfl⟩ : syracuseStep 2882069 = 135097) (by norm_num)
theorem B2161181 : Blo 1279958 2161181 := bbase (se 3 (by rfl) ⟨405221, by rfl⟩ : syracuseStep 2161181 = 810443) (by norm_num)
theorem B1440301 : Blo 1279958 1440301 := bbase (se 3 (by rfl) ⟨270056, by rfl⟩ : syracuseStep 1440301 = 540113) (by norm_num)
theorem B2431549 : Blo 1279958 2431549 := bbase (se 3 (by rfl) ⟨455915, by rfl⟩ : syracuseStep 2431549 = 911831) (by norm_num)
theorem B1440337 : Blo 1279958 1440337 := bbase (se 2 (by rfl) ⟨540126, by rfl⟩ : syracuseStep 1440337 = 1080253) (by norm_num)
theorem B2882141 : Blo 1279958 2882141 := bbase (se 3 (by rfl) ⟨540401, by rfl⟩ : syracuseStep 2882141 = 1080803) (by norm_num)
theorem B1620577 : Blo 1279958 1620577 := bbase (se 2 (by rfl) ⟨607716, by rfl⟩ : syracuseStep 1620577 = 1215433) (by norm_num)
theorem B1538657 : Blo 1279958 1538657 := bbase (se 2 (by rfl) ⟨576996, by rfl⟩ : syracuseStep 1538657 = 1153993) (by norm_num)
theorem B2464357 : Blo 1279958 2464357 := bbase (se 4 (by rfl) ⟨231033, by rfl⟩ : syracuseStep 2464357 = 462067) (by norm_num)
theorem B4323941 : Blo 1279958 4323941 := bbase (se 4 (by rfl) ⟨405369, by rfl⟩ : syracuseStep 4323941 = 810739) (by norm_num)
theorem B1440373 : Blo 1279958 1440373 := bbase (se 5 (by rfl) ⟨67517, by rfl⟩ : syracuseStep 1440373 = 135035) (by norm_num)
theorem B4102805 : Blo 1279958 4102805 := bbase (se 6 (by rfl) ⟨96159, by rfl⟩ : syracuseStep 4102805 = 192319) (by norm_num)
theorem B1440409 : Blo 1279958 1440409 := bbase (se 2 (by rfl) ⟨540153, by rfl⟩ : syracuseStep 1440409 = 1080307) (by norm_num)
theorem B2161309 : Blo 1279958 2161309 := bbase (se 3 (by rfl) ⟨405245, by rfl⟩ : syracuseStep 2161309 = 810491) (by norm_num)
theorem B2882213 : Blo 1279958 2882213 := bbase (se 4 (by rfl) ⟨270207, by rfl⟩ : syracuseStep 2882213 = 540415) (by norm_num)
theorem B1440445 : Blo 1279958 1440445 := bbase (se 3 (by rfl) ⟨270083, by rfl⟩ : syracuseStep 1440445 = 540167) (by norm_num)
theorem B3242693 : Blo 1279958 3242693 := bbase (se 4 (by rfl) ⟨304002, by rfl⟩ : syracuseStep 3242693 = 608005) (by norm_num)
theorem B1440481 : Blo 1279958 1440481 := bbase (se 2 (by rfl) ⟨540180, by rfl⟩ : syracuseStep 1440481 = 1080361) (by norm_num)
theorem B2882285 : Blo 1279958 2882285 := bbase (se 3 (by rfl) ⟨540428, by rfl⟩ : syracuseStep 2882285 = 1080857) (by norm_num)
theorem B2161397 : Blo 1279958 2161397 := bbase (se 5 (by rfl) ⟨101315, by rfl⟩ : syracuseStep 2161397 = 202631) (by norm_num)
theorem B1440517 : Blo 1279958 1440517 := bbase (se 4 (by rfl) ⟨135048, by rfl⟩ : syracuseStep 1440517 = 270097) (by norm_num)
theorem B1620749 : Blo 1279958 1620749 := bbase (se 3 (by rfl) ⟨303890, by rfl⟩ : syracuseStep 1620749 = 607781) (by norm_num)
theorem B4102933 : Blo 1279958 4102933 := bbase (se 6 (by rfl) ⟨96162, by rfl⟩ : syracuseStep 4102933 = 192325) (by norm_num)
theorem B1440553 : Blo 1279958 1440553 := bbase (se 2 (by rfl) ⟨540207, by rfl⟩ : syracuseStep 1440553 = 1080415) (by norm_num)
theorem B2882357 : Blo 1279958 2882357 := bbase (se 5 (by rfl) ⟨135110, by rfl⟩ : syracuseStep 2882357 = 270221) (by norm_num)
theorem B1366841 : Blo 1279958 1366841 := bbase (se 2 (by rfl) ⟨512565, by rfl⟩ : syracuseStep 1366841 = 1025131) (by norm_num)
theorem B1620805 : Blo 1279958 1620805 := bbase (se 4 (by rfl) ⟨151950, by rfl⟩ : syracuseStep 1620805 = 303901) (by norm_num)
theorem B1440589 : Blo 1279958 1440589 := bbase (se 3 (by rfl) ⟨270110, by rfl⟩ : syracuseStep 1440589 = 540221) (by norm_num)
theorem B2431853 : Blo 1279958 2431853 := bbase (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) (by norm_num)
theorem B1440625 : Blo 1279958 1440625 := bbase (se 2 (by rfl) ⟨540234, by rfl⟩ : syracuseStep 1440625 = 1080469) (by norm_num)
theorem B2161525 : Blo 1279958 2161525 := bbase (se 5 (by rfl) ⟨101321, by rfl⟩ : syracuseStep 2161525 = 202643) (by norm_num)
theorem B2882429 : Blo 1279958 2882429 := bbase (se 3 (by rfl) ⟨540455, by rfl⟩ : syracuseStep 2882429 = 1080911) (by norm_num)
theorem B1440661 : Blo 1279958 1440661 := bbase (se 6 (by rfl) ⟨33765, by rfl⟩ : syracuseStep 1440661 = 67531) (by norm_num)
theorem B1620901 : Blo 1279958 1620901 := bbase (se 4 (by rfl) ⟨151959, by rfl⟩ : syracuseStep 1620901 = 303919) (by norm_num)
theorem B6486965 : Blo 1279958 6486965 := bbase (se 5 (by rfl) ⟨304076, by rfl⟩ : syracuseStep 6486965 = 608153) (by norm_num)
theorem B1440697 : Blo 1279958 1440697 := bbase (se 2 (by rfl) ⟨540261, by rfl⟩ : syracuseStep 1440697 = 1080523) (by norm_num)
theorem B2882501 : Blo 1279958 2882501 := bbase (se 4 (by rfl) ⟨270234, by rfl⟩ : syracuseStep 2882501 = 540469) (by norm_num)
theorem B2161613 : Blo 1279958 2161613 := bbase (se 3 (by rfl) ⟨405302, by rfl⟩ : syracuseStep 2161613 = 810605) (by norm_num)
theorem B4864981 : Blo 1279958 4864981 := bbase (se 7 (by rfl) ⟨57011, by rfl⟩ : syracuseStep 4864981 = 114023) (by norm_num)
theorem B1440733 : Blo 1279958 1440733 := bbase (se 3 (by rfl) ⟨270137, by rfl⟩ : syracuseStep 1440733 = 540275) (by norm_num)
theorem B1440769 : Blo 1279958 1440769 := bbase (se 2 (by rfl) ⟨540288, by rfl⟩ : syracuseStep 1440769 = 1080577) (by norm_num)
theorem B2882573 : Blo 1279958 2882573 := bbase (se 3 (by rfl) ⟨540482, by rfl⟩ : syracuseStep 2882573 = 1080965) (by norm_num)
theorem B4103189 : Blo 1279958 4103189 := bbase (se 6 (by rfl) ⟨96168, by rfl⟩ : syracuseStep 4103189 = 192337) (by norm_num)
theorem B4324373 : Blo 1279958 4324373 := bbase (se 6 (by rfl) ⟨101352, by rfl⟩ : syracuseStep 4324373 = 202705) (by norm_num)
theorem B3243037 : Blo 1279958 3243037 := bbase (se 3 (by rfl) ⟨608069, by rfl⟩ : syracuseStep 3243037 = 1216139) (by norm_num)
theorem B1440805 : Blo 1279958 1440805 := bbase (se 4 (by rfl) ⟨135075, by rfl⟩ : syracuseStep 1440805 = 270151) (by norm_num)
theorem B7289909 : Blo 1279958 7289909 := bbase (se 5 (by rfl) ⟨341714, by rfl⟩ : syracuseStep 7289909 = 683429) (by norm_num)
theorem B3079237 : Blo 1279958 3079237 := bbase (se 4 (by rfl) ⟨288678, by rfl⟩ : syracuseStep 3079237 = 577357) (by norm_num)
theorem B1440841 : Blo 1279958 1440841 := bbase (se 2 (by rfl) ⟨540315, by rfl⟩ : syracuseStep 1440841 = 1080631) (by norm_num)
theorem B2161741 : Blo 1279958 2161741 := bbase (se 3 (by rfl) ⟨405326, by rfl⟩ : syracuseStep 2161741 = 810653) (by norm_num)
theorem B2309197 : Blo 1279958 2309197 := bbase (se 3 (by rfl) ⟨432974, by rfl⟩ : syracuseStep 2309197 = 865949) (by norm_num)
theorem B1621073 : Blo 1279958 1621073 := bbase (se 2 (by rfl) ⟨607902, by rfl⟩ : syracuseStep 1621073 = 1215805) (by norm_num)
theorem B2882645 : Blo 1279958 2882645 := bbase (se 8 (by rfl) ⟨16890, by rfl⟩ : syracuseStep 2882645 = 33781) (by norm_num)
theorem B23379029 : Blo 1279958 23379029 := bbase (se 8 (by rfl) ⟨136986, by rfl⟩ : syracuseStep 23379029 = 273973) (by norm_num)
theorem B1440877 : Blo 1279958 1440877 := bbase (se 3 (by rfl) ⟨270164, by rfl⟩ : syracuseStep 1440877 = 540329) (by norm_num)
theorem B1621129 : Blo 1279958 1621129 := bbase (se 2 (by rfl) ⟨607923, by rfl⟩ : syracuseStep 1621129 = 1215847) (by norm_num)
theorem B3243149 : Blo 1279958 3243149 := bbase (se 3 (by rfl) ⟨608090, by rfl⟩ : syracuseStep 3243149 = 1216181) (by norm_num)
theorem B1440913 : Blo 1279958 1440913 := bbase (se 2 (by rfl) ⟨540342, by rfl⟩ : syracuseStep 1440913 = 1080685) (by norm_num)
theorem B2882717 : Blo 1279958 2882717 := bbase (se 3 (by rfl) ⟨540509, by rfl⟩ : syracuseStep 2882717 = 1081019) (by norm_num)
theorem B2161829 : Blo 1279958 2161829 := bbase (se 4 (by rfl) ⟨202671, by rfl⟩ : syracuseStep 2161829 = 405343) (by norm_num)
theorem B2309285 : Blo 1279958 2309285 := bbase (se 4 (by rfl) ⟨216495, by rfl⟩ : syracuseStep 2309285 = 432991) (by norm_num)
theorem B1440949 : Blo 1279958 1440949 := bbase (se 5 (by rfl) ⟨67544, by rfl⟩ : syracuseStep 1440949 = 135089) (by norm_num)
theorem B1440985 : Blo 1279958 1440985 := bbase (se 2 (by rfl) ⟨540369, by rfl⟩ : syracuseStep 1440985 = 1080739) (by norm_num)
theorem B2882789 : Blo 1279958 2882789 := bbase (se 4 (by rfl) ⟨270261, by rfl⟩ : syracuseStep 2882789 = 540523) (by norm_num)
theorem B1621225 : Blo 1279958 1621225 := bbase (se 2 (by rfl) ⟨607959, by rfl⟩ : syracuseStep 1621225 = 1215919) (by norm_num)
theorem B1367285 : Blo 1279958 1367285 := bbase (se 5 (by rfl) ⟨64091, by rfl⟩ : syracuseStep 1367285 = 128183) (by norm_num)
theorem B1441021 : Blo 1279958 1441021 := bbase (se 3 (by rfl) ⟨270191, by rfl⟩ : syracuseStep 1441021 = 540383) (by norm_num)
theorem B4865285 : Blo 1279958 4865285 := bbase (se 4 (by rfl) ⟨456120, by rfl⟩ : syracuseStep 4865285 = 912241) (by norm_num)
theorem B1441057 : Blo 1279958 1441057 := bbase (se 2 (by rfl) ⟨540396, by rfl⟩ : syracuseStep 1441057 = 1080793) (by norm_num)
theorem B2161957 : Blo 1279958 2161957 := bbase (se 4 (by rfl) ⟨202683, by rfl⟩ : syracuseStep 2161957 = 405367) (by norm_num)
theorem B2882861 : Blo 1279958 2882861 := bbase (se 3 (by rfl) ⟨540536, by rfl⟩ : syracuseStep 2882861 = 1081073) (by norm_num)
theorem B6151477 : Blo 1279958 6151477 := bbase (se 5 (by rfl) ⟨288350, by rfl⟩ : syracuseStep 6151477 = 576701) (by norm_num)
theorem B1441093 : Blo 1279958 1441093 := bbase (se 4 (by rfl) ⟨135102, by rfl⟩ : syracuseStep 1441093 = 270205) (by norm_num)
theorem B3243341 : Blo 1279958 3243341 := bbase (se 3 (by rfl) ⟨608126, by rfl⟩ : syracuseStep 3243341 = 1216253) (by norm_num)
theorem B4930901 : Blo 1279958 4930901 := bbase (se 11 (by rfl) ⟨3611, by rfl⟩ : syracuseStep 4930901 = 7223) (by norm_num)
theorem B4619605 : Blo 1279958 4619605 := bbase (se 11 (by rfl) ⟨3383, by rfl⟩ : syracuseStep 4619605 = 6767) (by norm_num)
theorem B1441129 : Blo 1279958 1441129 := bbase (se 2 (by rfl) ⟨540423, by rfl⟩ : syracuseStep 1441129 = 1080847) (by norm_num)
theorem B2882933 : Blo 1279958 2882933 := bbase (se 5 (by rfl) ⟨135137, by rfl⟩ : syracuseStep 2882933 = 270275) (by norm_num)
theorem B2162045 : Blo 1279958 2162045 := bbase (se 3 (by rfl) ⟨405383, by rfl⟩ : syracuseStep 2162045 = 810767) (by norm_num)
theorem B1441165 : Blo 1279958 1441165 := bbase (se 3 (by rfl) ⟨270218, by rfl⟩ : syracuseStep 1441165 = 540437) (by norm_num)
theorem B3079565 : Blo 1279958 3079565 := bbase (se 3 (by rfl) ⟨577418, by rfl⟩ : syracuseStep 3079565 = 1154837) (by norm_num)
theorem B1621397 : Blo 1279958 1621397 := bbase (se 6 (by rfl) ⟨38001, by rfl⟩ : syracuseStep 1621397 = 76003) (by norm_num)
theorem B1441201 : Blo 1279958 1441201 := bbase (se 2 (by rfl) ⟨540450, by rfl⟩ : syracuseStep 1441201 = 1080901) (by norm_num)
theorem B2883005 : Blo 1279958 2883005 := bbase (se 3 (by rfl) ⟨540563, by rfl⟩ : syracuseStep 2883005 = 1081127) (by norm_num)
theorem B4324805 : Blo 1279958 4324805 := bbase (se 4 (by rfl) ⟨405450, by rfl⟩ : syracuseStep 4324805 = 810901) (by norm_num)
theorem B2309573 : Blo 1279958 2309573 := bbase (se 4 (by rfl) ⟨216522, by rfl⟩ : syracuseStep 2309573 = 433045) (by norm_num)
theorem B3079621 : Blo 1279958 3079621 := bbase (se 4 (by rfl) ⟨288714, by rfl⟩ : syracuseStep 3079621 = 577429) (by norm_num)
theorem B1621453 : Blo 1279958 1621453 := bbase (se 3 (by rfl) ⟨304022, by rfl⟩ : syracuseStep 1621453 = 608045) (by norm_num)
theorem B8764885 : Blo 1279958 8764885 := bbase (se 7 (by rfl) ⟨102713, by rfl⟩ : syracuseStep 8764885 = 205427) (by norm_num)
theorem B1441237 : Blo 1279958 1441237 := bbase (se 7 (by rfl) ⟨16889, by rfl⟩ : syracuseStep 1441237 = 33779) (by norm_num)
theorem B1367533 : Blo 1279958 1367533 := bbase (se 3 (by rfl) ⟨256412, by rfl⟩ : syracuseStep 1367533 = 512825) (by norm_num)
theorem B10673653 : Blo 1279958 10673653 := bbase (se 5 (by rfl) ⟨500327, by rfl⟩ : syracuseStep 10673653 = 1000655) (by norm_num)
theorem B1441273 : Blo 1279958 1441273 := bbase (se 2 (by rfl) ⟨540477, by rfl⟩ : syracuseStep 1441273 = 1080955) (by norm_num)
theorem B2162173 : Blo 1279958 2162173 := bbase (se 3 (by rfl) ⟨405407, by rfl⟩ : syracuseStep 2162173 = 810815) (by norm_num)
theorem B2883077 : Blo 1279958 2883077 := bbase (se 4 (by rfl) ⟨270288, by rfl⟩ : syracuseStep 2883077 = 540577) (by norm_num)
theorem B1441309 : Blo 1279958 1441309 := bbase (se 3 (by rfl) ⟨270245, by rfl⟩ : syracuseStep 1441309 = 540491) (by norm_num)
theorem B1621549 : Blo 1279958 1621549 := bbase (se 3 (by rfl) ⟨304040, by rfl⟩ : syracuseStep 1621549 = 608081) (by norm_num)
theorem B1441345 : Blo 1279958 1441345 := bbase (se 2 (by rfl) ⟨540504, by rfl⟩ : syracuseStep 1441345 = 1081009) (by norm_num)
theorem B2883149 : Blo 1279958 2883149 := bbase (se 3 (by rfl) ⟨540590, by rfl⟩ : syracuseStep 2883149 = 1081181) (by norm_num)
theorem B2162261 : Blo 1279958 2162261 := bbase (se 8 (by rfl) ⟨12669, by rfl⟩ : syracuseStep 2162261 = 25339) (by norm_num)
theorem B2432605 : Blo 1279958 2432605 := bbase (se 3 (by rfl) ⟨456113, by rfl⟩ : syracuseStep 2432605 = 912227) (by norm_num)
theorem B1441381 : Blo 1279958 1441381 := bbase (se 4 (by rfl) ⟨135129, by rfl⟩ : syracuseStep 1441381 = 270259) (by norm_num)
theorem B1441417 : Blo 1279958 1441417 := bbase (se 2 (by rfl) ⟨540531, by rfl⟩ : syracuseStep 1441417 = 1081063) (by norm_num)
theorem B2883221 : Blo 1279958 2883221 := bbase (se 6 (by rfl) ⟨67575, by rfl⟩ : syracuseStep 2883221 = 135151) (by norm_num)
theorem B2309789 : Blo 1279958 2309789 := bbase (se 3 (by rfl) ⟨433085, by rfl⟩ : syracuseStep 2309789 = 866171) (by norm_num)
theorem B3243685 : Blo 1279958 3243685 := bbase (se 4 (by rfl) ⟨304095, by rfl⟩ : syracuseStep 3243685 = 608191) (by norm_num)
theorem B1441453 : Blo 1279958 1441453 := bbase (se 3 (by rfl) ⟨270272, by rfl⟩ : syracuseStep 1441453 = 540545) (by norm_num)
theorem B3079853 : Blo 1279958 3079853 := bbase (se 3 (by rfl) ⟨577472, by rfl⟩ : syracuseStep 3079853 = 1154945) (by norm_num)
theorem B1441489 : Blo 1279958 1441489 := bbase (se 2 (by rfl) ⟨540558, by rfl⟩ : syracuseStep 1441489 = 1081117) (by norm_num)
theorem B2162389 : Blo 1279958 2162389 := bbase (se 7 (by rfl) ⟨25340, by rfl⟩ : syracuseStep 2162389 = 50681) (by norm_num)
theorem B1621721 : Blo 1279958 1621721 := bbase (se 2 (by rfl) ⟨608145, by rfl⟩ : syracuseStep 1621721 = 1216291) (by norm_num)
theorem B2883293 : Blo 1279958 2883293 := bbase (se 3 (by rfl) ⟨540617, by rfl⟩ : syracuseStep 2883293 = 1081235) (by norm_num)
theorem B2432749 : Blo 1279958 2432749 := bbase (se 3 (by rfl) ⟨456140, by rfl⟩ : syracuseStep 2432749 = 912281) (by norm_num)
theorem B1441525 : Blo 1279958 1441525 := bbase (se 5 (by rfl) ⟨67571, by rfl⟩ : syracuseStep 1441525 = 135143) (by norm_num)
theorem B2735869 : Blo 1279958 2735869 := bbase (se 3 (by rfl) ⟨512975, by rfl⟩ : syracuseStep 2735869 = 1025951) (by norm_num)
theorem B1621777 : Blo 1279958 1621777 := bbase (se 2 (by rfl) ⟨608166, by rfl⟩ : syracuseStep 1621777 = 1216333) (by norm_num)
theorem B3243797 : Blo 1279958 3243797 := bbase (se 6 (by rfl) ⟨76026, by rfl⟩ : syracuseStep 3243797 = 152053) (by norm_num)
theorem B1441561 : Blo 1279958 1441561 := bbase (se 2 (by rfl) ⟨540585, by rfl⟩ : syracuseStep 1441561 = 1081171) (by norm_num)
theorem B2883365 : Blo 1279958 2883365 := bbase (se 4 (by rfl) ⟨270315, by rfl⟩ : syracuseStep 2883365 = 540631) (by norm_num)
theorem B2162477 : Blo 1279958 2162477 := bbase (se 3 (by rfl) ⟨405464, by rfl⟩ : syracuseStep 2162477 = 810929) (by norm_num)
theorem B6922037 : Blo 1279958 6922037 := bbase (se 5 (by rfl) ⟨324470, by rfl⟩ : syracuseStep 6922037 = 648941) (by norm_num)
theorem B1441597 : Blo 1279958 1441597 := bbase (se 3 (by rfl) ⟨270299, by rfl⟩ : syracuseStep 1441597 = 540599) (by norm_num)
theorem B3284821 : Blo 1279958 3284821 := bbase (se 9 (by rfl) ⟨9623, by rfl⟩ : syracuseStep 3284821 = 19247) (by norm_num)
theorem B1441633 : Blo 1279958 1441633 := bbase (se 2 (by rfl) ⟨540612, by rfl⟩ : syracuseStep 1441633 = 1081225) (by norm_num)
theorem B2883437 : Blo 1279958 2883437 := bbase (se 3 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 2883437 = 1081289) (by norm_num)
theorem B3080045 : Blo 1279958 3080045 := bbase (se 3 (by rfl) ⟨577508, by rfl⟩ : syracuseStep 3080045 = 1155017) (by norm_num)
theorem B1621873 : Blo 1279958 1621873 := bbase (se 2 (by rfl) ⟨608202, by rfl⟩ : syracuseStep 1621873 = 1216405) (by norm_num)
theorem B4325237 : Blo 1279958 4325237 := bbase (se 5 (by rfl) ⟨202745, by rfl⟩ : syracuseStep 4325237 = 405491) (by norm_num)
theorem B1441669 : Blo 1279958 1441669 := bbase (se 4 (by rfl) ⟨135156, by rfl⟩ : syracuseStep 1441669 = 270313) (by norm_num)
theorem B2432909 : Blo 1279958 2432909 := bbase (se 3 (by rfl) ⟨456170, by rfl⟩ : syracuseStep 2432909 = 912341) (by norm_num)
theorem B1367965 : Blo 1279958 1367965 := bbase (se 3 (by rfl) ⟨256493, by rfl⟩ : syracuseStep 1367965 = 512987) (by norm_num)
theorem B1441705 : Blo 1279958 1441705 := bbase (se 2 (by rfl) ⟨540639, by rfl⟩ : syracuseStep 1441705 = 1081279) (by norm_num)
theorem B2162605 : Blo 1279958 2162605 := bbase (se 3 (by rfl) ⟨405488, by rfl⟩ : syracuseStep 2162605 = 810977) (by norm_num)
theorem B2883509 : Blo 1279958 2883509 := bbase (se 5 (by rfl) ⟨135164, by rfl⟩ : syracuseStep 2883509 = 270329) (by norm_num)
theorem B1441741 : Blo 1279958 1441741 := bbase (se 3 (by rfl) ⟨270326, by rfl⟩ : syracuseStep 1441741 = 540653) (by norm_num)
theorem B3243989 : Blo 1279958 3243989 := bbase (se 7 (by rfl) ⟨38015, by rfl⟩ : syracuseStep 3243989 = 76031) (by norm_num)
theorem B1368037 : Blo 1279958 1368037 := bbase (se 4 (by rfl) ⟨128253, by rfl⟩ : syracuseStep 1368037 = 256507) (by norm_num)
theorem B1441777 : Blo 1279958 1441777 := bbase (se 2 (by rfl) ⟨540666, by rfl⟩ : syracuseStep 1441777 = 1081333) (by norm_num)
theorem B2883581 : Blo 1279958 2883581 := bbase (se 3 (by rfl) ⟨540671, by rfl⟩ : syracuseStep 2883581 = 1081343) (by norm_num)
theorem B1441795 : Blo 1279958 1441795 := bstep (se 1 (by rfl) ⟨1081346, by rfl⟩ : syracuseStep 1441795 = 2162693) B2162693
theorem B5472269 : Blo 1279958 5472269 := bstep (se 3 (by rfl) ⟨1026050, by rfl⟩ : syracuseStep 5472269 = 2052101) B2052101
theorem B1622035 : Blo 1279958 1622035 := bstep (se 1 (by rfl) ⟨1216526, by rfl⟩ : syracuseStep 1622035 = 2433053) B2433053
theorem B6488099 : Blo 1279958 6488099 := bstep (se 1 (by rfl) ⟨4866074, by rfl⟩ : syracuseStep 6488099 = 9732149) B9732149
theorem B2433091 : Blo 1279958 2433091 := bstep (se 1 (by rfl) ⟨1824818, by rfl⟩ : syracuseStep 2433091 = 3649637) B3649637
theorem B4325453 : Blo 1279958 4325453 := bstep (se 3 (by rfl) ⟨811022, by rfl⟩ : syracuseStep 4325453 = 1622045) B1622045
theorem B31162481 : Blo 1279958 31162481 := bstep (se 2 (by rfl) ⟨11685930, by rfl⟩ : syracuseStep 31162481 = 23371861) B23371861
theorem B2162801 : Blo 1279958 2162801 := bstep (se 2 (by rfl) ⟨811050, by rfl⟩ : syracuseStep 2162801 = 1622101) B1622101
theorem B4325507 : Blo 1279958 4325507 := bstep (se 1 (by rfl) ⟨3244130, by rfl⟩ : syracuseStep 4325507 = 6488261) B6488261
theorem B1441939 : Blo 1279958 1441939 := bstep (se 1 (by rfl) ⟨1081454, by rfl⟩ : syracuseStep 1441939 = 2162909) B2162909
theorem B2883761 : Blo 1279958 2883761 := bstep (se 2 (by rfl) ⟨1081410, by rfl⟩ : syracuseStep 2883761 = 2162821) B2162821
theorem B2883779 : Blo 1279958 2883779 := bstep (se 1 (by rfl) ⟨2162834, by rfl⟩ : syracuseStep 2883779 = 4325669) B4325669
theorem B2162929 : Blo 1279958 2162929 := bstep (se 2 (by rfl) ⟨811098, by rfl⟩ : syracuseStep 2162929 = 1622197) B1622197
theorem B7299341 : Blo 1279958 7299341 := bstep (se 3 (by rfl) ⟨1368626, by rfl⟩ : syracuseStep 7299341 = 2737253) B2737253
theorem B2162963 : Blo 1279958 2162963 := bstep (se 1 (by rfl) ⟨1622222, by rfl⟩ : syracuseStep 2162963 = 3244445) B3244445
theorem B1442083 : Blo 1279958 1442083 := bstep (se 1 (by rfl) ⟨1081562, by rfl⟩ : syracuseStep 1442083 = 2163125) B2163125
theorem B2736433 : Blo 1279958 2736433 := bstep (se 2 (by rfl) ⟨1026162, by rfl⟩ : syracuseStep 2736433 = 2052325) B2052325
theorem B4325777 : Blo 1279958 4325777 := bstep (se 2 (by rfl) ⟨1622166, by rfl⟩ : syracuseStep 4325777 = 3244333) B3244333
theorem B2163091 : Blo 1279958 2163091 := bstep (se 1 (by rfl) ⟨1622318, by rfl⟩ : syracuseStep 2163091 = 3244637) B3244637
theorem B2884049 : Blo 1279958 2884049 := bstep (se 2 (by rfl) ⟨1081518, by rfl⟩ : syracuseStep 2884049 = 2163037) B2163037
theorem B2884067 : Blo 1279958 2884067 := bstep (se 1 (by rfl) ⟨2163050, by rfl⟩ : syracuseStep 2884067 = 4326101) B4326101
theorem B2433539 : Blo 1279958 2433539 := bstep (se 1 (by rfl) ⟨1825154, by rfl⟩ : syracuseStep 2433539 = 3650309) B3650309
theorem B2597393 : Blo 1279958 2597393 := bstep (se 2 (by rfl) ⟨974022, by rfl⟩ : syracuseStep 2597393 = 1948045) B1948045
theorem B2163233 : Blo 1279958 2163233 := bstep (se 2 (by rfl) ⟨811212, by rfl⟩ : syracuseStep 2163233 = 1622425) B1622425
theorem B3244657 : Blo 1279958 3244657 := bstep (se 2 (by rfl) ⟨1216746, by rfl⟩ : syracuseStep 3244657 = 2433493) B2433493
theorem B4104881 : Blo 1279958 4104881 := bstep (se 2 (by rfl) ⟨1539330, by rfl⟩ : syracuseStep 4104881 = 3078661) B3078661
theorem B7291619 : Blo 1279958 7291619 := bstep (se 1 (by rfl) ⟨5468714, by rfl⟩ : syracuseStep 7291619 = 10937429) B10937429
theorem B4104931 : Blo 1279958 4104931 := bstep (se 1 (by rfl) ⟨3078698, by rfl⟩ : syracuseStep 4104931 = 6157397) B6157397
theorem B2884337 : Blo 1279958 2884337 := bstep (se 2 (by rfl) ⟨1081626, by rfl⟩ : syracuseStep 2884337 = 2163253) B2163253
theorem B2884355 : Blo 1279958 2884355 := bstep (se 1 (by rfl) ⟨2163266, by rfl⟩ : syracuseStep 2884355 = 4326533) B4326533
theorem B3285809 : Blo 1279958 3285809 := bstep (se 2 (by rfl) ⟨1232178, by rfl⟩ : syracuseStep 3285809 = 2464357) B2464357
theorem B6488909 : Blo 1279958 6488909 := bstep (se 3 (by rfl) ⟨1216670, by rfl⟩ : syracuseStep 6488909 = 2433341) B2433341
theorem B16425827 : Blo 1279958 16425827 := bstep (se 1 (by rfl) ⟨12319370, by rfl⟩ : syracuseStep 16425827 = 24638741) B24638741
theorem B3244931 : Blo 1279958 3244931 := bstep (se 1 (by rfl) ⟨2433698, by rfl⟩ : syracuseStep 3244931 = 4867397) B4867397
theorem B4326317 : Blo 1279958 4326317 := bstep (se 3 (by rfl) ⟨811184, by rfl⟩ : syracuseStep 4326317 = 1622369) B1622369
theorem B2737091 : Blo 1279958 2737091 := bstep (se 1 (by rfl) ⟨2052818, by rfl⟩ : syracuseStep 2737091 = 4105637) B4105637
theorem B4326371 : Blo 1279958 4326371 := bstep (se 1 (by rfl) ⟨3244778, by rfl⟩ : syracuseStep 4326371 = 6489557) B6489557
theorem B3646595 : Blo 1279958 3646595 := bstep (se 1 (by rfl) ⟨2734946, by rfl⟩ : syracuseStep 3646595 = 5469893) B5469893
theorem B4105649 : Blo 1279958 4105649 := bstep (se 2 (by rfl) ⟨1539618, by rfl⟩ : syracuseStep 4105649 = 3079237) B3079237
theorem B3892781 : Blo 1279958 3892781 := bstep (se 3 (by rfl) ⟨729896, by rfl⟩ : syracuseStep 3892781 = 1459793) B1459793
theorem B6481457 : Blo 1279958 6481457 := bstep (se 2 (by rfl) ⟨2430546, by rfl⟩ : syracuseStep 6481457 = 4861093) B4861093
theorem B3696209 : Blo 1279958 3696209 := bstep (se 2 (by rfl) ⟨1386078, by rfl⟩ : syracuseStep 3696209 = 2772157) B2772157
theorem B1730179 : Blo 1279958 1730179 := bstep (se 1 (by rfl) ⟨1297634, by rfl⟩ : syracuseStep 1730179 = 2595269) B2595269
theorem B21874373 : Blo 1279958 21874373 := bstep (se 4 (by rfl) ⟨2050722, by rfl⟩ : syracuseStep 21874373 = 4101445) B4101445
theorem B8201969 : Blo 1279958 8201969 := bstep (se 2 (by rfl) ⟨3075738, by rfl⟩ : syracuseStep 8201969 = 6151477) B6151477
theorem B13854577 : Blo 1279958 13854577 := bstep (se 2 (by rfl) ⟨5195466, by rfl⟩ : syracuseStep 13854577 = 10390933) B10390933
theorem B20760461 : Blo 1279958 20760461 := bstep (se 3 (by rfl) ⟨3892586, by rfl⟩ : syracuseStep 20760461 = 7785173) B7785173
theorem B4106161 : Blo 1279958 4106161 := bstep (se 2 (by rfl) ⟨1539810, by rfl⟩ : syracuseStep 4106161 = 3079621) B3079621
theorem B1279971 : Blo 1279958 1279971 := bstep (se 1 (by rfl) ⟨959978, by rfl⟩ : syracuseStep 1279971 = 1919957) B1919957
theorem B14231537 : Blo 1279958 14231537 := bstep (se 2 (by rfl) ⟨5336826, by rfl⟩ : syracuseStep 14231537 = 10673653) B10673653
theorem B1279987 : Blo 1279958 1279987 := bstep (se 1 (by rfl) ⟨959990, by rfl⟩ : syracuseStep 1279987 = 1919981) B1919981
theorem B1280003 : Blo 1279958 1280003 := bstep (se 1 (by rfl) ⟨960002, by rfl⟩ : syracuseStep 1280003 = 1920005) B1920005
theorem B1280019 : Blo 1279958 1280019 := bstep (se 1 (by rfl) ⟨960014, by rfl⟩ : syracuseStep 1280019 = 1920029) B1920029
theorem B4859939 : Blo 1279958 4859939 := bstep (se 1 (by rfl) ⟨3644954, by rfl⟩ : syracuseStep 4859939 = 7289909) B7289909
theorem B1280035 : Blo 1279958 1280035 := bstep (se 1 (by rfl) ⟨960026, by rfl⟩ : syracuseStep 1280035 = 1920053) B1920053
theorem B1280051 : Blo 1279958 1280051 := bstep (se 1 (by rfl) ⟨960038, by rfl⟩ : syracuseStep 1280051 = 1920077) B1920077
theorem B1280067 : Blo 1279958 1280067 := bstep (se 1 (by rfl) ⟨960050, by rfl⟩ : syracuseStep 1280067 = 1920101) B1920101
theorem B1280083 : Blo 1279958 1280083 := bstep (se 1 (by rfl) ⟨960062, by rfl⟩ : syracuseStep 1280083 = 1920125) B1920125
theorem B1280099 : Blo 1279958 1280099 := bstep (se 1 (by rfl) ⟨960074, by rfl⟩ : syracuseStep 1280099 = 1920149) B1920149
theorem B35063921 : Blo 1279958 35063921 := bstep (se 2 (by rfl) ⟨13148970, by rfl⟩ : syracuseStep 35063921 = 26297941) B26297941
theorem B1280115 : Blo 1279958 1280115 := bstep (se 1 (by rfl) ⟨960086, by rfl⟩ : syracuseStep 1280115 = 1920173) B1920173
theorem B1280131 : Blo 1279958 1280131 := bstep (se 1 (by rfl) ⟨960098, by rfl⟩ : syracuseStep 1280131 = 1920197) B1920197
theorem B1280147 : Blo 1279958 1280147 := bstep (se 1 (by rfl) ⟨960110, by rfl⟩ : syracuseStep 1280147 = 1920221) B1920221
theorem B1280163 : Blo 1279958 1280163 := bstep (se 1 (by rfl) ⟨960122, by rfl⟩ : syracuseStep 1280163 = 1920245) B1920245
theorem B1280179 : Blo 1279958 1280179 := bstep (se 1 (by rfl) ⟨960134, by rfl⟩ : syracuseStep 1280179 = 1920269) B1920269
theorem B1280195 : Blo 1279958 1280195 := bstep (se 1 (by rfl) ⟨960146, by rfl⟩ : syracuseStep 1280195 = 1920293) B1920293
theorem B1280211 : Blo 1279958 1280211 := bstep (se 1 (by rfl) ⟨960158, by rfl⟩ : syracuseStep 1280211 = 1920317) B1920317
theorem B1280227 : Blo 1279958 1280227 := bstep (se 1 (by rfl) ⟨960170, by rfl⟩ : syracuseStep 1280227 = 1920341) B1920341
theorem B3287267 : Blo 1279958 3287267 := bstep (se 1 (by rfl) ⟨2465450, by rfl⟩ : syracuseStep 3287267 = 4930901) B4930901
theorem B1280243 : Blo 1279958 1280243 := bstep (se 1 (by rfl) ⟨960182, by rfl⟩ : syracuseStep 1280243 = 1920365) B1920365
theorem B1280259 : Blo 1279958 1280259 := bstep (se 1 (by rfl) ⟨960194, by rfl⟩ : syracuseStep 1280259 = 1920389) B1920389
theorem B1280275 : Blo 1279958 1280275 := bstep (se 1 (by rfl) ⟨960206, by rfl⟩ : syracuseStep 1280275 = 1920413) B1920413
theorem B1280291 : Blo 1279958 1280291 := bstep (se 1 (by rfl) ⟨960218, by rfl⟩ : syracuseStep 1280291 = 1920437) B1920437
theorem B1280307 : Blo 1279958 1280307 := bstep (se 1 (by rfl) ⟨960230, by rfl⟩ : syracuseStep 1280307 = 1920461) B1920461
theorem B1280323 : Blo 1279958 1280323 := bstep (se 1 (by rfl) ⟨960242, by rfl⟩ : syracuseStep 1280323 = 1920485) B1920485
theorem B3647825 : Blo 1279958 3647825 := bstep (se 2 (by rfl) ⟨1367934, by rfl⟩ : syracuseStep 3647825 = 2735869) B2735869
theorem B1280339 : Blo 1279958 1280339 := bstep (se 1 (by rfl) ⟨960254, by rfl⟩ : syracuseStep 1280339 = 1920509) B1920509
theorem B1280355 : Blo 1279958 1280355 := bstep (se 1 (by rfl) ⟨960266, by rfl⟩ : syracuseStep 1280355 = 1920533) B1920533
theorem B1280371 : Blo 1279958 1280371 := bstep (se 1 (by rfl) ⟨960278, by rfl⟩ : syracuseStep 1280371 = 1920557) B1920557
theorem B1280387 : Blo 1279958 1280387 := bstep (se 1 (by rfl) ⟨960290, by rfl⟩ : syracuseStep 1280387 = 1920581) B1920581
theorem B1280403 : Blo 1279958 1280403 := bstep (se 1 (by rfl) ⟨960302, by rfl⟩ : syracuseStep 1280403 = 1920605) B1920605
theorem B1280419 : Blo 1279958 1280419 := bstep (se 1 (by rfl) ⟨960314, by rfl⟩ : syracuseStep 1280419 = 1920629) B1920629
theorem B1280435 : Blo 1279958 1280435 := bstep (se 1 (by rfl) ⟨960326, by rfl⟩ : syracuseStep 1280435 = 1920653) B1920653
theorem B1280451 : Blo 1279958 1280451 := bstep (se 1 (by rfl) ⟨960338, by rfl⟩ : syracuseStep 1280451 = 1920677) B1920677
theorem B1280467 : Blo 1279958 1280467 := bstep (se 1 (by rfl) ⟨960350, by rfl⟩ : syracuseStep 1280467 = 1920701) B1920701
theorem B1280483 : Blo 1279958 1280483 := bstep (se 1 (by rfl) ⟨960362, by rfl⟩ : syracuseStep 1280483 = 1920725) B1920725
theorem B1280499 : Blo 1279958 1280499 := bstep (se 1 (by rfl) ⟨960374, by rfl⟩ : syracuseStep 1280499 = 1920749) B1920749
theorem B1280515 : Blo 1279958 1280515 := bstep (se 1 (by rfl) ⟨960386, by rfl⟩ : syracuseStep 1280515 = 1920773) B1920773
theorem B1280531 : Blo 1279958 1280531 := bstep (se 1 (by rfl) ⟨960398, by rfl⟩ : syracuseStep 1280531 = 1920797) B1920797
theorem B4614691 : Blo 1279958 4614691 := bstep (se 1 (by rfl) ⟨3461018, by rfl⟩ : syracuseStep 4614691 = 6922037) B6922037
theorem B1280547 : Blo 1279958 1280547 := bstep (se 1 (by rfl) ⟨960410, by rfl⟩ : syracuseStep 1280547 = 1920821) B1920821
theorem B1280563 : Blo 1279958 1280563 := bstep (se 1 (by rfl) ⟨960422, by rfl⟩ : syracuseStep 1280563 = 1920845) B1920845
theorem B14584373 : Blo 1279958 14584373 := bstep (se 5 (by rfl) ⟨683642, by rfl⟩ : syracuseStep 14584373 = 1367285) B1367285
theorem B1280579 : Blo 1279958 1280579 := bstep (se 1 (by rfl) ⟨960434, by rfl⟩ : syracuseStep 1280579 = 1920869) B1920869
theorem B7293509 : Blo 1279958 7293509 := bstep (se 4 (by rfl) ⟨683766, by rfl⟩ : syracuseStep 7293509 = 1367533) B1367533
theorem B11692613 : Blo 1279958 11692613 := bstep (se 4 (by rfl) ⟨1096182, by rfl⟩ : syracuseStep 11692613 = 2192365) B2192365
theorem B1280595 : Blo 1279958 1280595 := bstep (se 1 (by rfl) ⟨960446, by rfl⟩ : syracuseStep 1280595 = 1920893) B1920893
theorem B1280611 : Blo 1279958 1280611 := bstep (se 1 (by rfl) ⟨960458, by rfl⟩ : syracuseStep 1280611 = 1920917) B1920917
theorem B1280627 : Blo 1279958 1280627 := bstep (se 1 (by rfl) ⟨960470, by rfl⟩ : syracuseStep 1280627 = 1920941) B1920941
theorem B1280643 : Blo 1279958 1280643 := bstep (se 1 (by rfl) ⟨960482, by rfl⟩ : syracuseStep 1280643 = 1920965) B1920965
theorem B1280659 : Blo 1279958 1280659 := bstep (se 1 (by rfl) ⟨960494, by rfl⟩ : syracuseStep 1280659 = 1920989) B1920989
theorem B1280675 : Blo 1279958 1280675 := bstep (se 1 (by rfl) ⟨960506, by rfl⟩ : syracuseStep 1280675 = 1921013) B1921013
theorem B4860593 : Blo 1279958 4860593 := bstep (se 2 (by rfl) ⟨1822722, by rfl⟩ : syracuseStep 4860593 = 3645445) B3645445
theorem B1280691 : Blo 1279958 1280691 := bstep (se 1 (by rfl) ⟨960518, by rfl⟩ : syracuseStep 1280691 = 1921037) B1921037
theorem B2190019 : Blo 1279958 2190019 := bstep (se 1 (by rfl) ⟨1642514, by rfl⟩ : syracuseStep 2190019 = 3285029) B3285029
theorem B1280707 : Blo 1279958 1280707 := bstep (se 1 (by rfl) ⟨960530, by rfl⟩ : syracuseStep 1280707 = 1921061) B1921061
theorem B1280723 : Blo 1279958 1280723 := bstep (se 1 (by rfl) ⟨960542, by rfl⟩ : syracuseStep 1280723 = 1921085) B1921085
theorem B1280739 : Blo 1279958 1280739 := bstep (se 1 (by rfl) ⟨960554, by rfl⟩ : syracuseStep 1280739 = 1921109) B1921109
theorem B1280755 : Blo 1279958 1280755 := bstep (se 1 (by rfl) ⟨960566, by rfl⟩ : syracuseStep 1280755 = 1921133) B1921133
theorem B1280771 : Blo 1279958 1280771 := bstep (se 1 (by rfl) ⟨960578, by rfl⟩ : syracuseStep 1280771 = 1921157) B1921157
theorem B1280787 : Blo 1279958 1280787 := bstep (se 1 (by rfl) ⟨960590, by rfl⟩ : syracuseStep 1280787 = 1921181) B1921181
theorem B1280803 : Blo 1279958 1280803 := bstep (se 1 (by rfl) ⟨960602, by rfl⟩ : syracuseStep 1280803 = 1921205) B1921205
theorem B1280819 : Blo 1279958 1280819 := bstep (se 1 (by rfl) ⟨960614, by rfl⟩ : syracuseStep 1280819 = 1921229) B1921229
theorem B1731379 : Blo 1279958 1731379 := bstep (se 1 (by rfl) ⟨1298534, by rfl⟩ : syracuseStep 1731379 = 2597069) B2597069
theorem B1280835 : Blo 1279958 1280835 := bstep (se 1 (by rfl) ⟨960626, by rfl⟩ : syracuseStep 1280835 = 1921253) B1921253
theorem B1280851 : Blo 1279958 1280851 := bstep (se 1 (by rfl) ⟨960638, by rfl⟩ : syracuseStep 1280851 = 1921277) B1921277
theorem B4926307 : Blo 1279958 4926307 := bstep (se 1 (by rfl) ⟨3694730, by rfl⟩ : syracuseStep 4926307 = 7389461) B7389461
theorem B1280867 : Blo 1279958 1280867 := bstep (se 1 (by rfl) ⟨960650, by rfl⟩ : syracuseStep 1280867 = 1921301) B1921301
theorem B1280883 : Blo 1279958 1280883 := bstep (se 1 (by rfl) ⟨960662, by rfl⟩ : syracuseStep 1280883 = 1921325) B1921325
theorem B1280899 : Blo 1279958 1280899 := bstep (se 1 (by rfl) ⟨960674, by rfl⟩ : syracuseStep 1280899 = 1921349) B1921349
theorem B1280915 : Blo 1279958 1280915 := bstep (se 1 (by rfl) ⟨960686, by rfl⟩ : syracuseStep 1280915 = 1921373) B1921373
theorem B2050979 : Blo 1279958 2050979 := bstep (se 1 (by rfl) ⟨1538234, by rfl⟩ : syracuseStep 2050979 = 3076469) B3076469
theorem B1280931 : Blo 1279958 1280931 := bstep (se 1 (by rfl) ⟨960698, by rfl⟩ : syracuseStep 1280931 = 1921397) B1921397
theorem B4500397 : Blo 1279958 4500397 := bstep (se 3 (by rfl) ⟨843824, by rfl⟩ : syracuseStep 4500397 = 1687649) B1687649
theorem B1280947 : Blo 1279958 1280947 := bstep (se 1 (by rfl) ⟨960710, by rfl⟩ : syracuseStep 1280947 = 1921421) B1921421
theorem B1919939 : Blo 1279958 1919939 := bstep (se 1 (by rfl) ⟨1439954, by rfl⟩ : syracuseStep 1919939 = 2879909) B2879909
theorem B1280963 : Blo 1279958 1280963 := bstep (se 1 (by rfl) ⟨960722, by rfl⟩ : syracuseStep 1280963 = 1921445) B1921445
theorem B1280979 : Blo 1279958 1280979 := bstep (se 1 (by rfl) ⟨960734, by rfl⟩ : syracuseStep 1280979 = 1921469) B1921469
theorem B1919969 : Blo 1279958 1919969 := bstep (se 2 (by rfl) ⟨719988, by rfl⟩ : syracuseStep 1919969 = 1439977) B1439977
theorem B6482915 : Blo 1279958 6482915 := bstep (se 1 (by rfl) ⟨4862186, by rfl⟩ : syracuseStep 6482915 = 9724373) B9724373
theorem B1280995 : Blo 1279958 1280995 := bstep (se 1 (by rfl) ⟨960746, by rfl⟩ : syracuseStep 1280995 = 1921493) B1921493
theorem B2051057 : Blo 1279958 2051057 := bstep (se 2 (by rfl) ⟨769146, by rfl⟩ : syracuseStep 2051057 = 1538293) B1538293
theorem B1919987 : Blo 1279958 1919987 := bstep (se 1 (by rfl) ⟨1439990, by rfl⟩ : syracuseStep 1919987 = 2879981) B2879981
theorem B1281011 : Blo 1279958 1281011 := bstep (se 1 (by rfl) ⟨960758, by rfl⟩ : syracuseStep 1281011 = 1921517) B1921517
theorem B1281027 : Blo 1279958 1281027 := bstep (se 1 (by rfl) ⟨960770, by rfl⟩ : syracuseStep 1281027 = 1921541) B1921541
theorem B4320269 : Blo 1279958 4320269 := bstep (se 3 (by rfl) ⟨810050, by rfl⟩ : syracuseStep 4320269 = 1620101) B1620101
theorem B1920017 : Blo 1279958 1920017 := bstep (se 2 (by rfl) ⟨720006, by rfl⟩ : syracuseStep 1920017 = 1440013) B1440013
theorem B1281043 : Blo 1279958 1281043 := bstep (se 1 (by rfl) ⟨960782, by rfl⟩ : syracuseStep 1281043 = 1921565) B1921565
theorem B1920035 : Blo 1279958 1920035 := bstep (se 1 (by rfl) ⟨1440026, by rfl⟩ : syracuseStep 1920035 = 2880053) B2880053
theorem B1281059 : Blo 1279958 1281059 := bstep (se 1 (by rfl) ⟨960794, by rfl⟩ : syracuseStep 1281059 = 1921589) B1921589
theorem B1281075 : Blo 1279958 1281075 := bstep (se 1 (by rfl) ⟨960806, by rfl⟩ : syracuseStep 1281075 = 1921613) B1921613
theorem B1920065 : Blo 1279958 1920065 := bstep (se 2 (by rfl) ⟨720024, by rfl⟩ : syracuseStep 1920065 = 1440049) B1440049
theorem B4320323 : Blo 1279958 4320323 := bstep (se 1 (by rfl) ⟨3240242, by rfl⟩ : syracuseStep 4320323 = 6480485) B6480485
theorem B1281091 : Blo 1279958 1281091 := bstep (se 1 (by rfl) ⟨960818, by rfl⟩ : syracuseStep 1281091 = 1921637) B1921637
theorem B2919505 : Blo 1279958 2919505 := bstep (se 2 (by rfl) ⟨1094814, by rfl⟩ : syracuseStep 2919505 = 2189629) B2189629
theorem B1920083 : Blo 1279958 1920083 := bstep (se 1 (by rfl) ⟨1440062, by rfl⟩ : syracuseStep 1920083 = 2880125) B2880125
theorem B1281107 : Blo 1279958 1281107 := bstep (se 1 (by rfl) ⟨960830, by rfl⟩ : syracuseStep 1281107 = 1921661) B1921661
theorem B1281123 : Blo 1279958 1281123 := bstep (se 1 (by rfl) ⟨960842, by rfl⟩ : syracuseStep 1281123 = 1921685) B1921685
theorem B11095139 : Blo 1279958 11095139 := bstep (se 1 (by rfl) ⟨8321354, by rfl⟩ : syracuseStep 11095139 = 16642709) B16642709
theorem B1920113 : Blo 1279958 1920113 := bstep (se 2 (by rfl) ⟨720042, by rfl⟩ : syracuseStep 1920113 = 1440085) B1440085
theorem B1281139 : Blo 1279958 1281139 := bstep (se 1 (by rfl) ⟨960854, by rfl⟩ : syracuseStep 1281139 = 1921709) B1921709
theorem B1920131 : Blo 1279958 1920131 := bstep (se 1 (by rfl) ⟨1440098, by rfl⟩ : syracuseStep 1920131 = 2880197) B2880197
theorem B1281155 : Blo 1279958 1281155 := bstep (se 1 (by rfl) ⟨960866, by rfl⟩ : syracuseStep 1281155 = 1921733) B1921733
theorem B1281171 : Blo 1279958 1281171 := bstep (se 1 (by rfl) ⟨960878, by rfl⟩ : syracuseStep 1281171 = 1921757) B1921757
theorem B1920161 : Blo 1279958 1920161 := bstep (se 2 (by rfl) ⟨720060, by rfl⟩ : syracuseStep 1920161 = 1440121) B1440121
theorem B1281187 : Blo 1279958 1281187 := bstep (se 1 (by rfl) ⟨960890, by rfl⟩ : syracuseStep 1281187 = 1921781) B1921781
theorem B4811939 : Blo 1279958 4811939 := bstep (se 1 (by rfl) ⟨3608954, by rfl⟩ : syracuseStep 4811939 = 7217909) B7217909
theorem B1920179 : Blo 1279958 1920179 := bstep (se 1 (by rfl) ⟨1440134, by rfl⟩ : syracuseStep 1920179 = 2880269) B2880269
theorem B1281203 : Blo 1279958 1281203 := bstep (se 1 (by rfl) ⟨960902, by rfl⟩ : syracuseStep 1281203 = 1921805) B1921805
theorem B1281219 : Blo 1279958 1281219 := bstep (se 1 (by rfl) ⟨960914, by rfl⟩ : syracuseStep 1281219 = 1921829) B1921829
theorem B1920209 : Blo 1279958 1920209 := bstep (se 2 (by rfl) ⟨720078, by rfl⟩ : syracuseStep 1920209 = 1440157) B1440157
theorem B2051281 : Blo 1279958 2051281 := bstep (se 2 (by rfl) ⟨769230, by rfl⟩ : syracuseStep 2051281 = 1538461) B1538461
theorem B1281235 : Blo 1279958 1281235 := bstep (se 1 (by rfl) ⟨960926, by rfl⟩ : syracuseStep 1281235 = 1921853) B1921853
theorem B1920227 : Blo 1279958 1920227 := bstep (se 1 (by rfl) ⟨1440170, by rfl⟩ : syracuseStep 1920227 = 2880341) B2880341
theorem B1281251 : Blo 1279958 1281251 := bstep (se 1 (by rfl) ⟨960938, by rfl⟩ : syracuseStep 1281251 = 1921877) B1921877
theorem B1281267 : Blo 1279958 1281267 := bstep (se 1 (by rfl) ⟨960950, by rfl⟩ : syracuseStep 1281267 = 1921901) B1921901
theorem B1920257 : Blo 1279958 1920257 := bstep (se 2 (by rfl) ⟨720096, by rfl⟩ : syracuseStep 1920257 = 1440193) B1440193
theorem B1281283 : Blo 1279958 1281283 := bstep (se 1 (by rfl) ⟨960962, by rfl⟩ : syracuseStep 1281283 = 1921925) B1921925
theorem B1920275 : Blo 1279958 1920275 := bstep (se 1 (by rfl) ⟨1440206, by rfl⟩ : syracuseStep 1920275 = 2880413) B2880413
theorem B1281299 : Blo 1279958 1281299 := bstep (se 1 (by rfl) ⟨960974, by rfl⟩ : syracuseStep 1281299 = 1921949) B1921949
theorem B1281315 : Blo 1279958 1281315 := bstep (se 1 (by rfl) ⟨960986, by rfl⟩ : syracuseStep 1281315 = 1921973) B1921973
theorem B1920305 : Blo 1279958 1920305 := bstep (se 2 (by rfl) ⟨720114, by rfl⟩ : syracuseStep 1920305 = 1440229) B1440229
theorem B1281331 : Blo 1279958 1281331 := bstep (se 1 (by rfl) ⟨960998, by rfl⟩ : syracuseStep 1281331 = 1921997) B1921997
theorem B1920323 : Blo 1279958 1920323 := bstep (se 1 (by rfl) ⟨1440242, by rfl⟩ : syracuseStep 1920323 = 2880485) B2880485
theorem B1281347 : Blo 1279958 1281347 := bstep (se 1 (by rfl) ⟨961010, by rfl⟩ : syracuseStep 1281347 = 1922021) B1922021
theorem B7114061 : Blo 1279958 7114061 := bstep (se 3 (by rfl) ⟨1333886, by rfl⟩ : syracuseStep 7114061 = 2667773) B2667773
theorem B4320593 : Blo 1279958 4320593 := bstep (se 2 (by rfl) ⟨1620222, by rfl⟩ : syracuseStep 4320593 = 3240445) B3240445
theorem B1281363 : Blo 1279958 1281363 := bstep (se 1 (by rfl) ⟨961022, by rfl⟩ : syracuseStep 1281363 = 1922045) B1922045
theorem B1920353 : Blo 1279958 1920353 := bstep (se 2 (by rfl) ⟨720132, by rfl⟩ : syracuseStep 1920353 = 1440265) B1440265
theorem B1281379 : Blo 1279958 1281379 := bstep (se 1 (by rfl) ⟨961034, by rfl⟩ : syracuseStep 1281379 = 1922069) B1922069
theorem B1920371 : Blo 1279958 1920371 := bstep (se 1 (by rfl) ⟨1440278, by rfl⟩ : syracuseStep 1920371 = 2880557) B2880557
theorem B1281395 : Blo 1279958 1281395 := bstep (se 1 (by rfl) ⟨961046, by rfl⟩ : syracuseStep 1281395 = 1922093) B1922093
theorem B1281411 : Blo 1279958 1281411 := bstep (se 1 (by rfl) ⟨961058, by rfl⟩ : syracuseStep 1281411 = 1922117) B1922117
theorem B1920401 : Blo 1279958 1920401 := bstep (se 2 (by rfl) ⟨720150, by rfl⟩ : syracuseStep 1920401 = 1440301) B1440301
theorem B1281427 : Blo 1279958 1281427 := bstep (se 1 (by rfl) ⟨961070, by rfl⟩ : syracuseStep 1281427 = 1922141) B1922141
theorem B1920419 : Blo 1279958 1920419 := bstep (se 1 (by rfl) ⟨1440314, by rfl⟩ : syracuseStep 1920419 = 2880629) B2880629
theorem B1281443 : Blo 1279958 1281443 := bstep (se 1 (by rfl) ⟨961082, by rfl⟩ : syracuseStep 1281443 = 1922165) B1922165
theorem B1281459 : Blo 1279958 1281459 := bstep (se 1 (by rfl) ⟨961094, by rfl⟩ : syracuseStep 1281459 = 1922189) B1922189
theorem B1920449 : Blo 1279958 1920449 := bstep (se 2 (by rfl) ⟨720168, by rfl⟩ : syracuseStep 1920449 = 1440337) B1440337
theorem B1281475 : Blo 1279958 1281475 := bstep (se 1 (by rfl) ⟨961106, by rfl⟩ : syracuseStep 1281475 = 1922213) B1922213
theorem B1920467 : Blo 1279958 1920467 := bstep (se 1 (by rfl) ⟨1440350, by rfl⟩ : syracuseStep 1920467 = 2880701) B2880701
theorem B1281491 : Blo 1279958 1281491 := bstep (se 1 (by rfl) ⟨961118, by rfl⟩ : syracuseStep 1281491 = 1922237) B1922237
theorem B11685347 : Blo 1279958 11685347 := bstep (se 1 (by rfl) ⟨8764010, by rfl⟩ : syracuseStep 11685347 = 17528021) B17528021
theorem B11095523 : Blo 1279958 11095523 := bstep (se 1 (by rfl) ⟨8321642, by rfl⟩ : syracuseStep 11095523 = 16643285) B16643285
theorem B1281507 : Blo 1279958 1281507 := bstep (se 1 (by rfl) ⟨961130, by rfl⟩ : syracuseStep 1281507 = 1922261) B1922261
theorem B1920497 : Blo 1279958 1920497 := bstep (se 2 (by rfl) ⟨720186, by rfl⟩ : syracuseStep 1920497 = 1440373) B1440373
theorem B1281523 : Blo 1279958 1281523 := bstep (se 1 (by rfl) ⟨961142, by rfl⟩ : syracuseStep 1281523 = 1922285) B1922285
theorem B1920515 : Blo 1279958 1920515 := bstep (se 1 (by rfl) ⟨1440386, by rfl⟩ : syracuseStep 1920515 = 2880773) B2880773
theorem B1281539 : Blo 1279958 1281539 := bstep (se 1 (by rfl) ⟨961154, by rfl⟩ : syracuseStep 1281539 = 1922309) B1922309
theorem B1281555 : Blo 1279958 1281555 := bstep (se 1 (by rfl) ⟨961166, by rfl⟩ : syracuseStep 1281555 = 1922333) B1922333
theorem B1920545 : Blo 1279958 1920545 := bstep (se 2 (by rfl) ⟨720204, by rfl⟩ : syracuseStep 1920545 = 1440409) B1440409
theorem B1281571 : Blo 1279958 1281571 := bstep (se 1 (by rfl) ⟨961178, by rfl⟩ : syracuseStep 1281571 = 1922357) B1922357
theorem B1920563 : Blo 1279958 1920563 := bstep (se 1 (by rfl) ⟨1440422, by rfl⟩ : syracuseStep 1920563 = 2880845) B2880845
theorem B1281587 : Blo 1279958 1281587 := bstep (se 1 (by rfl) ⟨961190, by rfl⟩ : syracuseStep 1281587 = 1922381) B1922381
theorem B1281603 : Blo 1279958 1281603 := bstep (se 1 (by rfl) ⟨961202, by rfl⟩ : syracuseStep 1281603 = 1922405) B1922405
theorem B1920593 : Blo 1279958 1920593 := bstep (se 2 (by rfl) ⟨720222, by rfl⟩ : syracuseStep 1920593 = 1440445) B1440445
theorem B1281619 : Blo 1279958 1281619 := bstep (se 1 (by rfl) ⟨961214, by rfl⟩ : syracuseStep 1281619 = 1922429) B1922429
theorem B1920611 : Blo 1279958 1920611 := bstep (se 1 (by rfl) ⟨1440458, by rfl⟩ : syracuseStep 1920611 = 2880917) B2880917
theorem B1281635 : Blo 1279958 1281635 := bstep (se 1 (by rfl) ⟨961226, by rfl⟩ : syracuseStep 1281635 = 1922453) B1922453
theorem B1281651 : Blo 1279958 1281651 := bstep (se 1 (by rfl) ⟨961238, by rfl⟩ : syracuseStep 1281651 = 1922477) B1922477
theorem B1920641 : Blo 1279958 1920641 := bstep (se 2 (by rfl) ⟨720240, by rfl⟩ : syracuseStep 1920641 = 1440481) B1440481
theorem B1281667 : Blo 1279958 1281667 := bstep (se 1 (by rfl) ⟨961250, by rfl⟩ : syracuseStep 1281667 = 1922501) B1922501
theorem B14601869 : Blo 1279958 14601869 := bstep (se 3 (by rfl) ⟨2737850, by rfl⟩ : syracuseStep 14601869 = 5475701) B5475701
theorem B1920659 : Blo 1279958 1920659 := bstep (se 1 (by rfl) ⟨1440494, by rfl⟩ : syracuseStep 1920659 = 2880989) B2880989
theorem B1281683 : Blo 1279958 1281683 := bstep (se 1 (by rfl) ⟨961262, by rfl⟩ : syracuseStep 1281683 = 1922525) B1922525
theorem B1281699 : Blo 1279958 1281699 := bstep (se 1 (by rfl) ⟨961274, by rfl⟩ : syracuseStep 1281699 = 1922549) B1922549
theorem B1920689 : Blo 1279958 1920689 := bstep (se 2 (by rfl) ⟨720258, by rfl⟩ : syracuseStep 1920689 = 1440517) B1440517
theorem B1281715 : Blo 1279958 1281715 := bstep (se 1 (by rfl) ⟨961286, by rfl⟩ : syracuseStep 1281715 = 1922573) B1922573
theorem B16412341 : Blo 1279958 16412341 := bstep (se 5 (by rfl) ⟨769328, by rfl⟩ : syracuseStep 16412341 = 1538657) B1538657
theorem B1920707 : Blo 1279958 1920707 := bstep (se 1 (by rfl) ⟨1440530, by rfl⟩ : syracuseStep 1920707 = 2881061) B2881061
theorem B1281731 : Blo 1279958 1281731 := bstep (se 1 (by rfl) ⟨961298, by rfl⟩ : syracuseStep 1281731 = 1922597) B1922597
theorem B1281747 : Blo 1279958 1281747 := bstep (se 1 (by rfl) ⟨961310, by rfl⟩ : syracuseStep 1281747 = 1922621) B1922621
theorem B1920737 : Blo 1279958 1920737 := bstep (se 2 (by rfl) ⟨720276, by rfl⟩ : syracuseStep 1920737 = 1440553) B1440553
theorem B1281763 : Blo 1279958 1281763 := bstep (se 1 (by rfl) ⟨961322, by rfl⟩ : syracuseStep 1281763 = 1922645) B1922645
theorem B1920755 : Blo 1279958 1920755 := bstep (se 1 (by rfl) ⟨1440566, by rfl⟩ : syracuseStep 1920755 = 2881133) B2881133
theorem B1281779 : Blo 1279958 1281779 := bstep (se 1 (by rfl) ⟨961334, by rfl⟩ : syracuseStep 1281779 = 1922669) B1922669
theorem B3649283 : Blo 1279958 3649283 := bstep (se 1 (by rfl) ⟨2736962, by rfl⟩ : syracuseStep 3649283 = 5473925) B5473925
theorem B1281795 : Blo 1279958 1281795 := bstep (se 1 (by rfl) ⟨961346, by rfl⟩ : syracuseStep 1281795 = 1922693) B1922693
theorem B3460877 : Blo 1279958 3460877 := bstep (se 3 (by rfl) ⟨648914, by rfl⟩ : syracuseStep 3460877 = 1297829) B1297829
theorem B6483725 : Blo 1279958 6483725 := bstep (se 3 (by rfl) ⟨1215698, by rfl⟩ : syracuseStep 6483725 = 2431397) B2431397
theorem B1920785 : Blo 1279958 1920785 := bstep (se 2 (by rfl) ⟨720294, by rfl⟩ : syracuseStep 1920785 = 1440589) B1440589
theorem B1281811 : Blo 1279958 1281811 := bstep (se 1 (by rfl) ⟨961358, by rfl⟩ : syracuseStep 1281811 = 1922717) B1922717
theorem B1920803 : Blo 1279958 1920803 := bstep (se 1 (by rfl) ⟨1440602, by rfl⟩ : syracuseStep 1920803 = 2881205) B2881205
theorem B1281827 : Blo 1279958 1281827 := bstep (se 1 (by rfl) ⟨961370, by rfl⟩ : syracuseStep 1281827 = 1922741) B1922741
theorem B1281843 : Blo 1279958 1281843 := bstep (se 1 (by rfl) ⟨961382, by rfl⟩ : syracuseStep 1281843 = 1922765) B1922765
theorem B1920833 : Blo 1279958 1920833 := bstep (se 2 (by rfl) ⟨720312, by rfl⟩ : syracuseStep 1920833 = 1440625) B1440625
theorem B2109251 : Blo 1279958 2109251 := bstep (se 1 (by rfl) ⟨1581938, by rfl⟩ : syracuseStep 2109251 = 3163877) B3163877
theorem B1281859 : Blo 1279958 1281859 := bstep (se 1 (by rfl) ⟨961394, by rfl⟩ : syracuseStep 1281859 = 1922789) B1922789
theorem B1920851 : Blo 1279958 1920851 := bstep (se 1 (by rfl) ⟨1440638, by rfl⟩ : syracuseStep 1920851 = 2881277) B2881277
theorem B1281875 : Blo 1279958 1281875 := bstep (se 1 (by rfl) ⟨961406, by rfl⟩ : syracuseStep 1281875 = 1922813) B1922813
theorem B1281891 : Blo 1279958 1281891 := bstep (se 1 (by rfl) ⟨961418, by rfl⟩ : syracuseStep 1281891 = 1922837) B1922837
theorem B4321133 : Blo 1279958 4321133 := bstep (se 3 (by rfl) ⟨810212, by rfl⟩ : syracuseStep 4321133 = 1620425) B1620425
theorem B1920881 : Blo 1279958 1920881 := bstep (se 2 (by rfl) ⟨720330, by rfl⟩ : syracuseStep 1920881 = 1440661) B1440661
theorem B1281907 : Blo 1279958 1281907 := bstep (se 1 (by rfl) ⟨961430, by rfl⟩ : syracuseStep 1281907 = 1922861) B1922861
theorem B1920899 : Blo 1279958 1920899 := bstep (se 1 (by rfl) ⟨1440674, by rfl⟩ : syracuseStep 1920899 = 2881349) B2881349
theorem B1281923 : Blo 1279958 1281923 := bstep (se 1 (by rfl) ⟨961442, by rfl⟩ : syracuseStep 1281923 = 1922885) B1922885
theorem B1281939 : Blo 1279958 1281939 := bstep (se 1 (by rfl) ⟨961454, by rfl⟩ : syracuseStep 1281939 = 1922909) B1922909
theorem B1920929 : Blo 1279958 1920929 := bstep (se 2 (by rfl) ⟨720348, by rfl⟩ : syracuseStep 1920929 = 1440697) B1440697
theorem B4321187 : Blo 1279958 4321187 := bstep (se 1 (by rfl) ⟨3240890, by rfl⟩ : syracuseStep 4321187 = 6481781) B6481781
theorem B1281955 : Blo 1279958 1281955 := bstep (se 1 (by rfl) ⟨961466, by rfl⟩ : syracuseStep 1281955 = 1922933) B1922933
theorem B1920947 : Blo 1279958 1920947 := bstep (se 1 (by rfl) ⟨1440710, by rfl⟩ : syracuseStep 1920947 = 2881421) B2881421
theorem B1920977 : Blo 1279958 1920977 := bstep (se 2 (by rfl) ⟨720366, by rfl⟩ : syracuseStep 1920977 = 1440733) B1440733
theorem B1920995 : Blo 1279958 1920995 := bstep (se 1 (by rfl) ⟨1440746, by rfl⟩ : syracuseStep 1920995 = 2881493) B2881493
theorem B1921025 : Blo 1279958 1921025 := bstep (se 2 (by rfl) ⟨720384, by rfl⟩ : syracuseStep 1921025 = 1440769) B1440769
theorem B3239939 : Blo 1279958 3239939 := bstep (se 1 (by rfl) ⟨2429954, by rfl⟩ : syracuseStep 3239939 = 4859909) B4859909
theorem B1921043 : Blo 1279958 1921043 := bstep (se 1 (by rfl) ⟨1440782, by rfl⟩ : syracuseStep 1921043 = 2881565) B2881565
theorem B1921073 : Blo 1279958 1921073 := bstep (se 2 (by rfl) ⟨720402, by rfl⟩ : syracuseStep 1921073 = 1440805) B1440805
theorem B1921091 : Blo 1279958 1921091 := bstep (se 1 (by rfl) ⟨1440818, by rfl⟩ : syracuseStep 1921091 = 2881637) B2881637
theorem B2191441 : Blo 1279958 2191441 := bstep (se 2 (by rfl) ⟨821790, by rfl⟩ : syracuseStep 2191441 = 1643581) B1643581
theorem B1921121 : Blo 1279958 1921121 := bstep (se 2 (by rfl) ⟨720420, by rfl⟩ : syracuseStep 1921121 = 1440841) B1440841
theorem B1822819 : Blo 1279958 1822819 := bstep (se 1 (by rfl) ⟨1367114, by rfl⟩ : syracuseStep 1822819 = 2734229) B2734229
theorem B4862051 : Blo 1279958 4862051 := bstep (se 1 (by rfl) ⟨3646538, by rfl⟩ : syracuseStep 4862051 = 7293077) B7293077
theorem B4862065 : Blo 1279958 4862065 := bstep (se 2 (by rfl) ⟨1823274, by rfl⟩ : syracuseStep 4862065 = 3646549) B3646549
theorem B1921139 : Blo 1279958 1921139 := bstep (se 1 (by rfl) ⟨1440854, by rfl⟩ : syracuseStep 1921139 = 2881709) B2881709
theorem B8204429 : Blo 1279958 8204429 := bstep (se 3 (by rfl) ⟨1538330, by rfl⟩ : syracuseStep 8204429 = 3076661) B3076661
theorem B1921169 : Blo 1279958 1921169 := bstep (se 2 (by rfl) ⟨720438, by rfl⟩ : syracuseStep 1921169 = 1440877) B1440877
theorem B1921187 : Blo 1279958 1921187 := bstep (se 1 (by rfl) ⟨1440890, by rfl⟩ : syracuseStep 1921187 = 2881781) B2881781
theorem B6574243 : Blo 1279958 6574243 := bstep (se 1 (by rfl) ⟨4930682, by rfl⟩ : syracuseStep 6574243 = 9861365) B9861365
theorem B4321457 : Blo 1279958 4321457 := bstep (se 2 (by rfl) ⟨1620546, by rfl⟩ : syracuseStep 4321457 = 3241093) B3241093
theorem B1921217 : Blo 1279958 1921217 := bstep (se 2 (by rfl) ⟨720456, by rfl⟩ : syracuseStep 1921217 = 1440913) B1440913
theorem B1921235 : Blo 1279958 1921235 := bstep (se 1 (by rfl) ⟨1440926, by rfl⟩ : syracuseStep 1921235 = 2881853) B2881853
theorem B1921265 : Blo 1279958 1921265 := bstep (se 2 (by rfl) ⟨720474, by rfl⟩ : syracuseStep 1921265 = 1440949) B1440949
theorem B1921283 : Blo 1279958 1921283 := bstep (se 1 (by rfl) ⟨1440962, by rfl⟩ : syracuseStep 1921283 = 2881925) B2881925
theorem B1921313 : Blo 1279958 1921313 := bstep (se 2 (by rfl) ⟨720492, by rfl⟩ : syracuseStep 1921313 = 1440985) B1440985
theorem B1921331 : Blo 1279958 1921331 := bstep (se 1 (by rfl) ⟨1440998, by rfl⟩ : syracuseStep 1921331 = 2881997) B2881997
theorem B2961731 : Blo 1279958 2961731 := bstep (se 1 (by rfl) ⟨2221298, by rfl⟩ : syracuseStep 2961731 = 4442597) B4442597
theorem B10940741 : Blo 1279958 10940741 := bstep (se 4 (by rfl) ⟨1025694, by rfl⟩ : syracuseStep 10940741 = 2051389) B2051389
theorem B1921361 : Blo 1279958 1921361 := bstep (se 2 (by rfl) ⟨720510, by rfl⟩ : syracuseStep 1921361 = 1441021) B1441021
theorem B13840739 : Blo 1279958 13840739 := bstep (se 1 (by rfl) ⟨10380554, by rfl⟩ : syracuseStep 13840739 = 20761109) B20761109
theorem B1921379 : Blo 1279958 1921379 := bstep (se 1 (by rfl) ⟨1441034, by rfl⟩ : syracuseStep 1921379 = 2882069) B2882069
theorem B1921409 : Blo 1279958 1921409 := bstep (se 2 (by rfl) ⟨720528, by rfl⟩ : syracuseStep 1921409 = 1441057) B1441057
theorem B6926725 : Blo 1279958 6926725 := bstep (se 4 (by rfl) ⟨649380, by rfl⟩ : syracuseStep 6926725 = 1298761) B1298761
theorem B1921427 : Blo 1279958 1921427 := bstep (se 1 (by rfl) ⟨1441070, by rfl⟩ : syracuseStep 1921427 = 2882141) B2882141
theorem B5468579 : Blo 1279958 5468579 := bstep (se 1 (by rfl) ⟨4101434, by rfl⟩ : syracuseStep 5468579 = 8202869) B8202869
theorem B1921457 : Blo 1279958 1921457 := bstep (se 2 (by rfl) ⟨720546, by rfl⟩ : syracuseStep 1921457 = 1441093) B1441093
theorem B1921475 : Blo 1279958 1921475 := bstep (se 1 (by rfl) ⟨1441106, by rfl⟩ : syracuseStep 1921475 = 2882213) B2882213
theorem B1921505 : Blo 1279958 1921505 := bstep (se 2 (by rfl) ⟨720564, by rfl⟩ : syracuseStep 1921505 = 1441129) B1441129
theorem B1921523 : Blo 1279958 1921523 := bstep (se 1 (by rfl) ⟨1441142, by rfl⟩ : syracuseStep 1921523 = 2882285) B2882285
theorem B2880017 : Blo 1279958 2880017 := bstep (se 2 (by rfl) ⟨1080006, by rfl⟩ : syracuseStep 2880017 = 2160013) B2160013
theorem B1921553 : Blo 1279958 1921553 := bstep (se 2 (by rfl) ⟨720582, by rfl⟩ : syracuseStep 1921553 = 1441165) B1441165
theorem B2880035 : Blo 1279958 2880035 := bstep (se 1 (by rfl) ⟨2160026, by rfl⟩ : syracuseStep 2880035 = 4320053) B4320053
theorem B3076643 : Blo 1279958 3076643 := bstep (se 1 (by rfl) ⟨2307482, by rfl⟩ : syracuseStep 3076643 = 4614965) B4614965
theorem B1921571 : Blo 1279958 1921571 := bstep (se 1 (by rfl) ⟨1441178, by rfl⟩ : syracuseStep 1921571 = 2882357) B2882357
theorem B3650093 : Blo 1279958 3650093 := bstep (se 3 (by rfl) ⟨684392, by rfl⟩ : syracuseStep 3650093 = 1368785) B1368785
theorem B1921601 : Blo 1279958 1921601 := bstep (se 2 (by rfl) ⟨720600, by rfl⟩ : syracuseStep 1921601 = 1441201) B1441201
theorem B1921619 : Blo 1279958 1921619 := bstep (se 1 (by rfl) ⟨1441214, by rfl⟩ : syracuseStep 1921619 = 2882429) B2882429
theorem B11686513 : Blo 1279958 11686513 := bstep (se 2 (by rfl) ⟨4382442, by rfl⟩ : syracuseStep 11686513 = 8764885) B8764885
theorem B1921649 : Blo 1279958 1921649 := bstep (se 2 (by rfl) ⟨720618, by rfl⟩ : syracuseStep 1921649 = 1441237) B1441237
theorem B1921667 : Blo 1279958 1921667 := bstep (se 1 (by rfl) ⟨1441250, by rfl⟩ : syracuseStep 1921667 = 2882501) B2882501
theorem B1921697 : Blo 1279958 1921697 := bstep (se 2 (by rfl) ⟨720636, by rfl⟩ : syracuseStep 1921697 = 1441273) B1441273
theorem B1921715 : Blo 1279958 1921715 := bstep (se 1 (by rfl) ⟨1441286, by rfl⟩ : syracuseStep 1921715 = 2882573) B2882573
theorem B4321997 : Blo 1279958 4321997 := bstep (se 3 (by rfl) ⟨810374, by rfl⟩ : syracuseStep 4321997 = 1620749) B1620749
theorem B1921745 : Blo 1279958 1921745 := bstep (se 2 (by rfl) ⟨720654, by rfl⟩ : syracuseStep 1921745 = 1441309) B1441309
theorem B1921763 : Blo 1279958 1921763 := bstep (se 1 (by rfl) ⟨1441322, by rfl⟩ : syracuseStep 1921763 = 2882645) B2882645
theorem B15586019 : Blo 1279958 15586019 := bstep (se 1 (by rfl) ⟨11689514, by rfl⟩ : syracuseStep 15586019 = 23379029) B23379029
theorem B3650285 : Blo 1279958 3650285 := bstep (se 3 (by rfl) ⟨684428, by rfl⟩ : syracuseStep 3650285 = 1368857) B1368857
theorem B1921793 : Blo 1279958 1921793 := bstep (se 2 (by rfl) ⟨720672, by rfl⟩ : syracuseStep 1921793 = 1441345) B1441345
theorem B4322051 : Blo 1279958 4322051 := bstep (se 1 (by rfl) ⟨3241538, by rfl⟩ : syracuseStep 4322051 = 6483077) B6483077
theorem B1921811 : Blo 1279958 1921811 := bstep (se 1 (by rfl) ⟨1441358, by rfl⟩ : syracuseStep 1921811 = 2882717) B2882717
theorem B2880305 : Blo 1279958 2880305 := bstep (se 2 (by rfl) ⟨1080114, by rfl⟩ : syracuseStep 2880305 = 2160229) B2160229
theorem B1921841 : Blo 1279958 1921841 := bstep (se 2 (by rfl) ⟨720690, by rfl⟩ : syracuseStep 1921841 = 1441381) B1441381
theorem B2880323 : Blo 1279958 2880323 := bstep (se 1 (by rfl) ⟨2160242, by rfl⟩ : syracuseStep 2880323 = 4320485) B4320485
theorem B1921859 : Blo 1279958 1921859 := bstep (se 1 (by rfl) ⟨1441394, by rfl⟩ : syracuseStep 1921859 = 2882789) B2882789
theorem B1921889 : Blo 1279958 1921889 := bstep (se 2 (by rfl) ⟨720708, by rfl⟩ : syracuseStep 1921889 = 1441417) B1441417
theorem B10949489 : Blo 1279958 10949489 := bstep (se 2 (by rfl) ⟨4106058, by rfl⟩ : syracuseStep 10949489 = 8212117) B8212117
theorem B1921907 : Blo 1279958 1921907 := bstep (se 1 (by rfl) ⟨1441430, by rfl⟩ : syracuseStep 1921907 = 2882861) B2882861
theorem B1921937 : Blo 1279958 1921937 := bstep (se 2 (by rfl) ⟨720726, by rfl⟩ : syracuseStep 1921937 = 1441453) B1441453
theorem B1921955 : Blo 1279958 1921955 := bstep (se 1 (by rfl) ⟨1441466, by rfl⟩ : syracuseStep 1921955 = 2882933) B2882933
theorem B3240881 : Blo 1279958 3240881 := bstep (se 2 (by rfl) ⟨1215330, by rfl⟩ : syracuseStep 3240881 = 2430661) B2430661
theorem B2053043 : Blo 1279958 2053043 := bstep (se 1 (by rfl) ⟨1539782, by rfl⟩ : syracuseStep 2053043 = 3079565) B3079565
theorem B1921985 : Blo 1279958 1921985 := bstep (se 2 (by rfl) ⟨720744, by rfl⟩ : syracuseStep 1921985 = 1441489) B1441489
theorem B1922003 : Blo 1279958 1922003 := bstep (se 1 (by rfl) ⟨1441502, by rfl⟩ : syracuseStep 1922003 = 2883005) B2883005
theorem B3240931 : Blo 1279958 3240931 := bstep (se 1 (by rfl) ⟨2430698, by rfl⟩ : syracuseStep 3240931 = 4861397) B4861397
theorem B10941425 : Blo 1279958 10941425 := bstep (se 2 (by rfl) ⟨4103034, by rfl⟩ : syracuseStep 10941425 = 8206069) B8206069
theorem B1922033 : Blo 1279958 1922033 := bstep (se 2 (by rfl) ⟨720762, by rfl⟩ : syracuseStep 1922033 = 1441525) B1441525
theorem B1922051 : Blo 1279958 1922051 := bstep (se 1 (by rfl) ⟨1441538, by rfl⟩ : syracuseStep 1922051 = 2883077) B2883077
theorem B4322321 : Blo 1279958 4322321 := bstep (se 2 (by rfl) ⟨1620870, by rfl⟩ : syracuseStep 4322321 = 3241741) B3241741
theorem B1922081 : Blo 1279958 1922081 := bstep (se 2 (by rfl) ⟨720780, by rfl⟩ : syracuseStep 1922081 = 1441561) B1441561
theorem B1922099 : Blo 1279958 1922099 := bstep (se 1 (by rfl) ⟨1441574, by rfl⟩ : syracuseStep 1922099 = 2883149) B2883149
theorem B2880593 : Blo 1279958 2880593 := bstep (se 2 (by rfl) ⟨1080222, by rfl⟩ : syracuseStep 2880593 = 2160445) B2160445
theorem B1922129 : Blo 1279958 1922129 := bstep (se 2 (by rfl) ⟨720798, by rfl⟩ : syracuseStep 1922129 = 1441597) B1441597
theorem B2880611 : Blo 1279958 2880611 := bstep (se 1 (by rfl) ⟨2160458, by rfl⟩ : syracuseStep 2880611 = 4320917) B4320917
theorem B1922147 : Blo 1279958 1922147 := bstep (se 1 (by rfl) ⟨1441610, by rfl⟩ : syracuseStep 1922147 = 2883221) B2883221
theorem B4379761 : Blo 1279958 4379761 := bstep (se 2 (by rfl) ⟨1642410, by rfl⟩ : syracuseStep 4379761 = 3284821) B3284821
theorem B3241073 : Blo 1279958 3241073 := bstep (se 2 (by rfl) ⟨1215402, by rfl⟩ : syracuseStep 3241073 = 2430805) B2430805
theorem B2053235 : Blo 1279958 2053235 := bstep (se 1 (by rfl) ⟨1539926, by rfl⟩ : syracuseStep 2053235 = 3079853) B3079853
theorem B1922177 : Blo 1279958 1922177 := bstep (se 2 (by rfl) ⟨720816, by rfl⟩ : syracuseStep 1922177 = 1441633) B1441633
theorem B1922195 : Blo 1279958 1922195 := bstep (se 1 (by rfl) ⟨1441646, by rfl⟩ : syracuseStep 1922195 = 2883293) B2883293
theorem B4101293 : Blo 1279958 4101293 := bstep (se 3 (by rfl) ⟨768992, by rfl⟩ : syracuseStep 4101293 = 1537985) B1537985
theorem B1922225 : Blo 1279958 1922225 := bstep (se 2 (by rfl) ⟨720834, by rfl⟩ : syracuseStep 1922225 = 1441669) B1441669
theorem B1848515 : Blo 1279958 1848515 := bstep (se 1 (by rfl) ⟨1386386, by rfl⟩ : syracuseStep 1848515 = 2772773) B2772773
theorem B1922243 : Blo 1279958 1922243 := bstep (se 1 (by rfl) ⟨1441682, by rfl⟩ : syracuseStep 1922243 = 2883365) B2883365
theorem B1823953 : Blo 1279958 1823953 := bstep (se 2 (by rfl) ⟨683982, by rfl⟩ : syracuseStep 1823953 = 1367965) B1367965
theorem B1922273 : Blo 1279958 1922273 := bstep (se 2 (by rfl) ⟨720852, by rfl⟩ : syracuseStep 1922273 = 1441705) B1441705
theorem B1922291 : Blo 1279958 1922291 := bstep (se 1 (by rfl) ⟨1441718, by rfl⟩ : syracuseStep 1922291 = 2883437) B2883437
theorem B2053363 : Blo 1279958 2053363 := bstep (se 1 (by rfl) ⟨1540022, by rfl⟩ : syracuseStep 2053363 = 3080045) B3080045
theorem B1922321 : Blo 1279958 1922321 := bstep (se 2 (by rfl) ⟨720870, by rfl⟩ : syracuseStep 1922321 = 1441741) B1441741
theorem B1922339 : Blo 1279958 1922339 := bstep (se 1 (by rfl) ⟨1441754, by rfl⟩ : syracuseStep 1922339 = 2883509) B2883509
theorem B1824049 : Blo 1279958 1824049 := bstep (se 2 (by rfl) ⟨684018, by rfl⟩ : syracuseStep 1824049 = 1368037) B1368037
theorem B1922369 : Blo 1279958 1922369 := bstep (se 2 (by rfl) ⟨720888, by rfl⟩ : syracuseStep 1922369 = 1441777) B1441777
theorem B2159939 : Blo 1279958 2159939 := bstep (se 1 (by rfl) ⟨1619954, by rfl⟩ : syracuseStep 2159939 = 3239909) B3239909
theorem B2307409 : Blo 1279958 2307409 := bstep (se 2 (by rfl) ⟨865278, by rfl⟩ : syracuseStep 2307409 = 1730557) B1730557
theorem B1922387 : Blo 1279958 1922387 := bstep (se 1 (by rfl) ⟨1441790, by rfl⟩ : syracuseStep 1922387 = 2883581) B2883581
theorem B2880881 : Blo 1279958 2880881 := bstep (se 2 (by rfl) ⟨1080330, by rfl⟩ : syracuseStep 2880881 = 2160661) B2160661
theorem B3077489 : Blo 1279958 3077489 := bstep (se 2 (by rfl) ⟨1154058, by rfl⟩ : syracuseStep 3077489 = 2308117) B2308117
theorem B1922417 : Blo 1279958 1922417 := bstep (se 2 (by rfl) ⟨720906, by rfl⟩ : syracuseStep 1922417 = 1441813) B1441813
theorem B2880899 : Blo 1279958 2880899 := bstep (se 1 (by rfl) ⟨2160674, by rfl⟩ : syracuseStep 2880899 = 4321349) B4321349
theorem B1922435 : Blo 1279958 1922435 := bstep (se 1 (by rfl) ⟨1441826, by rfl⟩ : syracuseStep 1922435 = 2883653) B2883653
theorem B1922465 : Blo 1279958 1922465 := bstep (se 2 (by rfl) ⟨720924, by rfl⟩ : syracuseStep 1922465 = 1441849) B1441849
theorem B1922483 : Blo 1279958 1922483 := bstep (se 1 (by rfl) ⟨1441862, by rfl⟩ : syracuseStep 1922483 = 2883725) B2883725
theorem B2160067 : Blo 1279958 2160067 := bstep (se 1 (by rfl) ⟨1620050, by rfl⟩ : syracuseStep 2160067 = 3240101) B3240101
theorem B3077585 : Blo 1279958 3077585 := bstep (se 2 (by rfl) ⟨1154094, by rfl⟩ : syracuseStep 3077585 = 2308189) B2308189
theorem B1922513 : Blo 1279958 1922513 := bstep (se 2 (by rfl) ⟨720942, by rfl⟩ : syracuseStep 1922513 = 1441885) B1441885
theorem B1922531 : Blo 1279958 1922531 := bstep (se 1 (by rfl) ⟨1441898, by rfl⟩ : syracuseStep 1922531 = 2883797) B2883797
theorem B3700205 : Blo 1279958 3700205 := bstep (se 3 (by rfl) ⟨693788, by rfl⟩ : syracuseStep 3700205 = 1387577) B1387577
theorem B2921987 : Blo 1279958 2921987 := bstep (se 1 (by rfl) ⟨2191490, by rfl⟩ : syracuseStep 2921987 = 4382981) B4382981
theorem B1922561 : Blo 1279958 1922561 := bstep (se 2 (by rfl) ⟨720960, by rfl⟩ : syracuseStep 1922561 = 1441921) B1441921
theorem B1922579 : Blo 1279958 1922579 := bstep (se 1 (by rfl) ⟨1441934, by rfl⟩ : syracuseStep 1922579 = 2883869) B2883869
theorem B1947169 : Blo 1279958 1947169 := bstep (se 2 (by rfl) ⟨730188, by rfl⟩ : syracuseStep 1947169 = 1460377) B1460377
theorem B4863523 : Blo 1279958 4863523 := bstep (se 1 (by rfl) ⟨3647642, by rfl⟩ : syracuseStep 4863523 = 7295285) B7295285
theorem B3896867 : Blo 1279958 3896867 := bstep (se 1 (by rfl) ⟨2922650, by rfl⟩ : syracuseStep 3896867 = 5845301) B5845301
theorem B4322861 : Blo 1279958 4322861 := bstep (se 3 (by rfl) ⟨810536, by rfl⟩ : syracuseStep 4322861 = 1621073) B1621073
theorem B1922609 : Blo 1279958 1922609 := bstep (se 2 (by rfl) ⟨720978, by rfl⟩ : syracuseStep 1922609 = 1441957) B1441957
theorem B1922627 : Blo 1279958 1922627 := bstep (se 1 (by rfl) ⟨1441970, by rfl⟩ : syracuseStep 1922627 = 2883941) B2883941
theorem B4617805 : Blo 1279958 4617805 := bstep (se 3 (by rfl) ⟨865838, by rfl⟩ : syracuseStep 4617805 = 1731677) B1731677
theorem B2160209 : Blo 1279958 2160209 := bstep (se 2 (by rfl) ⟨810078, by rfl⟩ : syracuseStep 2160209 = 1620157) B1620157
theorem B1922657 : Blo 1279958 1922657 := bstep (se 2 (by rfl) ⟨720996, by rfl⟩ : syracuseStep 1922657 = 1441993) B1441993
theorem B4322915 : Blo 1279958 4322915 := bstep (se 1 (by rfl) ⟨3242186, by rfl⟩ : syracuseStep 4322915 = 6484373) B6484373
theorem B9721457 : Blo 1279958 9721457 := bstep (se 2 (by rfl) ⟨3645546, by rfl⟩ : syracuseStep 9721457 = 7291093) B7291093
theorem B2430577 : Blo 1279958 2430577 := bstep (se 2 (by rfl) ⟨911466, by rfl⟩ : syracuseStep 2430577 = 1822933) B1822933
theorem B10393201 : Blo 1279958 10393201 := bstep (se 2 (by rfl) ⟨3897450, by rfl⟩ : syracuseStep 10393201 = 7794901) B7794901
theorem B1922675 : Blo 1279958 1922675 := bstep (se 1 (by rfl) ⟨1442006, by rfl⟩ : syracuseStep 1922675 = 2884013) B2884013
theorem B2881169 : Blo 1279958 2881169 := bstep (se 2 (by rfl) ⟨1080438, by rfl⟩ : syracuseStep 2881169 = 2160877) B2160877
theorem B1922705 : Blo 1279958 1922705 := bstep (se 2 (by rfl) ⟨721014, by rfl⟩ : syracuseStep 1922705 = 1442029) B1442029
theorem B2881187 : Blo 1279958 2881187 := bstep (se 1 (by rfl) ⟨2160890, by rfl⟩ : syracuseStep 2881187 = 4321781) B4321781
theorem B1922723 : Blo 1279958 1922723 := bstep (se 1 (by rfl) ⟨1442042, by rfl⟩ : syracuseStep 1922723 = 2884085) B2884085
theorem B1922753 : Blo 1279958 1922753 := bstep (se 2 (by rfl) ⟨721032, by rfl⟩ : syracuseStep 1922753 = 1442065) B1442065
theorem B2160337 : Blo 1279958 2160337 := bstep (se 2 (by rfl) ⟨810126, by rfl⟩ : syracuseStep 2160337 = 1620253) B1620253
theorem B1922771 : Blo 1279958 1922771 := bstep (se 1 (by rfl) ⟨1442078, by rfl⟩ : syracuseStep 1922771 = 2884157) B2884157
theorem B1922801 : Blo 1279958 1922801 := bstep (se 2 (by rfl) ⟨721050, by rfl⟩ : syracuseStep 1922801 = 1442101) B1442101
theorem B2160371 : Blo 1279958 2160371 := bstep (se 1 (by rfl) ⟨1620278, by rfl⟩ : syracuseStep 2160371 = 3240557) B3240557
theorem B1922819 : Blo 1279958 1922819 := bstep (se 1 (by rfl) ⟨1442114, by rfl⟩ : syracuseStep 1922819 = 2884229) B2884229
theorem B1824545 : Blo 1279958 1824545 := bstep (se 2 (by rfl) ⟨684204, by rfl⟩ : syracuseStep 1824545 = 1368409) B1368409
theorem B1922849 : Blo 1279958 1922849 := bstep (se 2 (by rfl) ⟨721068, by rfl⟩ : syracuseStep 1922849 = 1442137) B1442137
theorem B1922867 : Blo 1279958 1922867 := bstep (se 1 (by rfl) ⟨1442150, by rfl⟩ : syracuseStep 1922867 = 2884301) B2884301
theorem B2963267 : Blo 1279958 2963267 := bstep (se 1 (by rfl) ⟨2222450, by rfl⟩ : syracuseStep 2963267 = 4444901) B4444901
theorem B2733905 : Blo 1279958 2733905 := bstep (se 2 (by rfl) ⟨1025214, by rfl⟩ : syracuseStep 2733905 = 2050429) B2050429
theorem B1922897 : Blo 1279958 1922897 := bstep (se 2 (by rfl) ⟨721086, by rfl⟩ : syracuseStep 1922897 = 1442173) B1442173
theorem B1922915 : Blo 1279958 1922915 := bstep (se 1 (by rfl) ⟨1442186, by rfl⟩ : syracuseStep 1922915 = 2884373) B2884373
theorem B4323185 : Blo 1279958 4323185 := bstep (se 2 (by rfl) ⟨1621194, by rfl⟩ : syracuseStep 4323185 = 3242389) B3242389
theorem B2160499 : Blo 1279958 2160499 := bstep (se 1 (by rfl) ⟨1620374, by rfl⟩ : syracuseStep 2160499 = 3240749) B3240749
theorem B6158243 : Blo 1279958 6158243 := bstep (se 1 (by rfl) ⟨4618682, by rfl⟩ : syracuseStep 6158243 = 9237365) B9237365
theorem B2881457 : Blo 1279958 2881457 := bstep (se 2 (by rfl) ⟨1080546, by rfl⟩ : syracuseStep 2881457 = 2161093) B2161093
theorem B2881475 : Blo 1279958 2881475 := bstep (se 1 (by rfl) ⟨2161106, by rfl⟩ : syracuseStep 2881475 = 4322213) B4322213
theorem B14596037 : Blo 1279958 14596037 := bstep (se 4 (by rfl) ⟨1368378, by rfl⟩ : syracuseStep 14596037 = 2736757) B2736757
theorem B2160641 : Blo 1279958 2160641 := bstep (se 2 (by rfl) ⟨810240, by rfl⟩ : syracuseStep 2160641 = 1620481) B1620481
theorem B3242065 : Blo 1279958 3242065 := bstep (se 2 (by rfl) ⟨1215774, by rfl⟩ : syracuseStep 3242065 = 2431549) B2431549
theorem B2160769 : Blo 1279958 2160769 := bstep (se 2 (by rfl) ⟨810288, by rfl⟩ : syracuseStep 2160769 = 1620577) B1620577
theorem B2160803 : Blo 1279958 2160803 := bstep (se 1 (by rfl) ⟨1620602, by rfl⟩ : syracuseStep 2160803 = 3241205) B3241205
theorem B2881745 : Blo 1279958 2881745 := bstep (se 2 (by rfl) ⟨1080654, by rfl⟩ : syracuseStep 2881745 = 2161309) B2161309
theorem B2881763 : Blo 1279958 2881763 := bstep (se 1 (by rfl) ⟨2161322, by rfl⟩ : syracuseStep 2881763 = 4322645) B4322645
theorem B2160931 : Blo 1279958 2160931 := bstep (se 1 (by rfl) ⟨1620698, by rfl⟩ : syracuseStep 2160931 = 3241397) B3241397
theorem B1440067 : Blo 1279958 1440067 := bstep (se 1 (by rfl) ⟨1080050, by rfl⟩ : syracuseStep 1440067 = 2160101) B2160101
theorem B3242339 : Blo 1279958 3242339 := bstep (se 1 (by rfl) ⟨2431754, by rfl⟩ : syracuseStep 3242339 = 4863509) B4863509
theorem B5470577 : Blo 1279958 5470577 := bstep (se 2 (by rfl) ⟨2051466, by rfl⟩ : syracuseStep 5470577 = 4102933) B4102933
theorem B4323725 : Blo 1279958 4323725 := bstep (se 3 (by rfl) ⟨810698, by rfl⟩ : syracuseStep 4323725 = 1621397) B1621397
theorem B2161073 : Blo 1279958 2161073 := bstep (se 2 (by rfl) ⟨810402, by rfl⟩ : syracuseStep 2161073 = 1620805) B1620805
theorem B3119555 : Blo 1279958 3119555 := bstep (se 1 (by rfl) ⟨2339666, by rfl⟩ : syracuseStep 3119555 = 4679333) B4679333
theorem B4323779 : Blo 1279958 4323779 := bstep (se 1 (by rfl) ⟨3242834, by rfl⟩ : syracuseStep 4323779 = 6485669) B6485669
theorem B9238981 : Blo 1279958 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B6568397 : Blo 1279958 6568397 := bstep (se 3 (by rfl) ⟨1231574, by rfl⟩ : syracuseStep 6568397 = 2463149) B2463149
theorem B1440211 : Blo 1279958 1440211 := bstep (se 1 (by rfl) ⟨1080158, by rfl⟩ : syracuseStep 1440211 = 2160317) B2160317
theorem B2882033 : Blo 1279958 2882033 := bstep (se 2 (by rfl) ⟨1080762, by rfl⟩ : syracuseStep 2882033 = 2161525) B2161525
theorem B2882051 : Blo 1279958 2882051 := bstep (se 1 (by rfl) ⟨2161538, by rfl⟩ : syracuseStep 2882051 = 4323077) B4323077
theorem B3242531 : Blo 1279958 3242531 := bstep (se 1 (by rfl) ⟨2431898, by rfl⟩ : syracuseStep 3242531 = 4863797) B4863797
theorem B4381229 : Blo 1279958 4381229 := bstep (se 3 (by rfl) ⟨821480, by rfl⟩ : syracuseStep 4381229 = 1642961) B1642961
theorem B2161201 : Blo 1279958 2161201 := bstep (se 2 (by rfl) ⟨810450, by rfl⟩ : syracuseStep 2161201 = 1620901) B1620901
theorem B2161235 : Blo 1279958 2161235 := bstep (se 1 (by rfl) ⟨1620926, by rfl⟩ : syracuseStep 2161235 = 3241853) B3241853
theorem B1440355 : Blo 1279958 1440355 := bstep (se 1 (by rfl) ⟨1080266, by rfl⟩ : syracuseStep 1440355 = 2160533) B2160533
theorem B6486641 : Blo 1279958 6486641 := bstep (se 2 (by rfl) ⟨2432490, by rfl⟩ : syracuseStep 6486641 = 4864981) B4864981
theorem B16628365 : Blo 1279958 16628365 := bstep (se 3 (by rfl) ⟨3117818, by rfl⟩ : syracuseStep 16628365 = 6235637) B6235637
theorem B2431633 : Blo 1279958 2431633 := bstep (se 2 (by rfl) ⟨911862, by rfl⟩ : syracuseStep 2431633 = 1823725) B1823725
theorem B1620643 : Blo 1279958 1620643 := bstep (se 1 (by rfl) ⟨1215482, by rfl⟩ : syracuseStep 1620643 = 2430965) B2430965
theorem B4324049 : Blo 1279958 4324049 := bstep (se 2 (by rfl) ⟨1621518, by rfl⟩ : syracuseStep 4324049 = 3243037) B3243037
theorem B2161363 : Blo 1279958 2161363 := bstep (se 1 (by rfl) ⟨1621022, by rfl⟩ : syracuseStep 2161363 = 3242045) B3242045
theorem B1440499 : Blo 1279958 1440499 := bstep (se 1 (by rfl) ⟨1080374, by rfl⟩ : syracuseStep 1440499 = 2160749) B2160749
theorem B1620739 : Blo 1279958 1620739 := bstep (se 1 (by rfl) ⟨1215554, by rfl⟩ : syracuseStep 1620739 = 2431109) B2431109
theorem B2882321 : Blo 1279958 2882321 := bstep (se 2 (by rfl) ⟨1080870, by rfl⟩ : syracuseStep 2882321 = 2161741) B2161741
theorem B3078929 : Blo 1279958 3078929 := bstep (se 2 (by rfl) ⟨1154598, by rfl⟩ : syracuseStep 3078929 = 2309197) B2309197
theorem B2882339 : Blo 1279958 2882339 := bstep (se 1 (by rfl) ⟨2161754, by rfl⟩ : syracuseStep 2882339 = 4323509) B4323509
theorem B2161505 : Blo 1279958 2161505 := bstep (se 2 (by rfl) ⟨810564, by rfl⟩ : syracuseStep 2161505 = 1621129) B1621129
theorem B1948531 : Blo 1279958 1948531 := bstep (se 1 (by rfl) ⟨1461398, by rfl⟩ : syracuseStep 1948531 = 2922797) B2922797
theorem B1440643 : Blo 1279958 1440643 := bstep (se 1 (by rfl) ⟨1080482, by rfl⟩ : syracuseStep 1440643 = 2160965) B2160965
theorem B4103075 : Blo 1279958 4103075 := bstep (se 1 (by rfl) ⟨3077306, by rfl⟩ : syracuseStep 4103075 = 6154613) B6154613
theorem B2161633 : Blo 1279958 2161633 := bstep (se 2 (by rfl) ⟨810612, by rfl⟩ : syracuseStep 2161633 = 1621225) B1621225
theorem B2161667 : Blo 1279958 2161667 := bstep (se 1 (by rfl) ⟨1621250, by rfl⟩ : syracuseStep 2161667 = 3242501) B3242501
theorem B1440787 : Blo 1279958 1440787 := bstep (se 1 (by rfl) ⟨1080590, by rfl⟩ : syracuseStep 1440787 = 2161181) B2161181
theorem B2432035 : Blo 1279958 2432035 := bstep (se 1 (by rfl) ⟨1824026, by rfl⟩ : syracuseStep 2432035 = 3648053) B3648053
theorem B2882609 : Blo 1279958 2882609 := bstep (se 2 (by rfl) ⟨1080978, by rfl⟩ : syracuseStep 2882609 = 2161957) B2161957
theorem B2882627 : Blo 1279958 2882627 := bstep (se 1 (by rfl) ⟨2161970, by rfl⟩ : syracuseStep 2882627 = 4323941) B4323941
theorem B2432081 : Blo 1279958 2432081 := bstep (se 2 (by rfl) ⟨912030, by rfl⟩ : syracuseStep 2432081 = 1824061) B1824061
theorem B1367123 : Blo 1279958 1367123 := bstep (se 1 (by rfl) ⟨1025342, by rfl⟩ : syracuseStep 1367123 = 2050685) B2050685
theorem B2735203 : Blo 1279958 2735203 := bstep (se 1 (by rfl) ⟨2051402, by rfl⟩ : syracuseStep 2735203 = 4102805) B4102805
theorem B6159473 : Blo 1279958 6159473 := bstep (se 2 (by rfl) ⟨2309802, by rfl⟩ : syracuseStep 6159473 = 4619605) B4619605
theorem B2161795 : Blo 1279958 2161795 := bstep (se 1 (by rfl) ⟨1621346, by rfl⟩ : syracuseStep 2161795 = 3242693) B3242693
theorem B1440931 : Blo 1279958 1440931 := bstep (se 1 (by rfl) ⟨1080698, by rfl⟩ : syracuseStep 1440931 = 2161397) B2161397
theorem B7019747 : Blo 1279958 7019747 := bstep (se 1 (by rfl) ⟨5264810, by rfl⟩ : syracuseStep 7019747 = 10529621) B10529621
theorem B4324589 : Blo 1279958 4324589 := bstep (se 3 (by rfl) ⟨810860, by rfl⟩ : syracuseStep 4324589 = 1621721) B1621721
theorem B1973489 : Blo 1279958 1973489 := bstep (se 2 (by rfl) ⟨740058, by rfl⟩ : syracuseStep 1973489 = 1480117) B1480117
theorem B1621235 : Blo 1279958 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B2161937 : Blo 1279958 2161937 := bstep (se 2 (by rfl) ⟨810726, by rfl⟩ : syracuseStep 2161937 = 1621453) B1621453
theorem B4324643 : Blo 1279958 4324643 := bstep (se 1 (by rfl) ⟨3243482, by rfl⟩ : syracuseStep 4324643 = 6486965) B6486965
theorem B7290161 : Blo 1279958 7290161 := bstep (se 2 (by rfl) ⟨2733810, by rfl⟩ : syracuseStep 7290161 = 5467621) B5467621
theorem B1441075 : Blo 1279958 1441075 := bstep (se 1 (by rfl) ⟨1080806, by rfl⟩ : syracuseStep 1441075 = 2161613) B2161613
theorem B2882897 : Blo 1279958 2882897 := bstep (se 2 (by rfl) ⟨1081086, by rfl⟩ : syracuseStep 2882897 = 2162173) B2162173
theorem B2735459 : Blo 1279958 2735459 := bstep (se 1 (by rfl) ⟨2051594, by rfl⟩ : syracuseStep 2735459 = 4103189) B4103189
theorem B2882915 : Blo 1279958 2882915 := bstep (se 1 (by rfl) ⟨2162186, by rfl⟩ : syracuseStep 2882915 = 4324373) B4324373
theorem B2432369 : Blo 1279958 2432369 := bstep (se 2 (by rfl) ⟨912138, by rfl⟩ : syracuseStep 2432369 = 1824277) B1824277
theorem B10394993 : Blo 1279958 10394993 := bstep (se 2 (by rfl) ⟨3898122, by rfl⟩ : syracuseStep 10394993 = 7796245) B7796245
theorem B2162065 : Blo 1279958 2162065 := bstep (se 2 (by rfl) ⟨810774, by rfl⟩ : syracuseStep 2162065 = 1621549) B1621549
theorem B2162099 : Blo 1279958 2162099 := bstep (se 1 (by rfl) ⟨1621574, by rfl⟩ : syracuseStep 2162099 = 3243149) B3243149
theorem B1441219 : Blo 1279958 1441219 := bstep (se 1 (by rfl) ⟨1080914, by rfl⟩ : syracuseStep 1441219 = 2161829) B2161829
theorem B1539523 : Blo 1279958 1539523 := bstep (se 1 (by rfl) ⟨1154642, by rfl⟩ : syracuseStep 1539523 = 2309285) B2309285
theorem B3243473 : Blo 1279958 3243473 := bstep (se 2 (by rfl) ⟨1216302, by rfl⟩ : syracuseStep 3243473 = 2432605) B2432605
theorem B3644909 : Blo 1279958 3644909 := bstep (se 3 (by rfl) ⟨683420, by rfl⟩ : syracuseStep 3644909 = 1366841) B1366841
theorem B2596355 : Blo 1279958 2596355 := bstep (se 1 (by rfl) ⟨1947266, by rfl⟩ : syracuseStep 2596355 = 3894533) B3894533
theorem B3243523 : Blo 1279958 3243523 := bstep (se 1 (by rfl) ⟨2432642, by rfl⟩ : syracuseStep 3243523 = 4865285) B4865285
theorem B5193229 : Blo 1279958 5193229 := bstep (se 3 (by rfl) ⟨973730, by rfl⟩ : syracuseStep 5193229 = 1947461) B1947461
theorem B2080289 : Blo 1279958 2080289 := bstep (se 2 (by rfl) ⟨780108, by rfl⟩ : syracuseStep 2080289 = 1560217) B1560217
theorem B4324913 : Blo 1279958 4324913 := bstep (se 2 (by rfl) ⟨1621842, by rfl⟩ : syracuseStep 4324913 = 3243685) B3243685
theorem B2162227 : Blo 1279958 2162227 := bstep (se 1 (by rfl) ⟨1621670, by rfl⟩ : syracuseStep 2162227 = 3243341) B3243341
theorem B1441363 : Blo 1279958 1441363 := bstep (se 1 (by rfl) ⟨1081022, by rfl⟩ : syracuseStep 1441363 = 2162045) B2162045
theorem B2883185 : Blo 1279958 2883185 := bstep (se 2 (by rfl) ⟨1081194, by rfl⟩ : syracuseStep 2883185 = 2162389) B2162389
theorem B2883203 : Blo 1279958 2883203 := bstep (se 1 (by rfl) ⟨2162402, by rfl⟩ : syracuseStep 2883203 = 4324805) B4324805
theorem B1539715 : Blo 1279958 1539715 := bstep (se 1 (by rfl) ⟨1154786, by rfl⟩ : syracuseStep 1539715 = 2309573) B2309573
theorem B3243665 : Blo 1279958 3243665 := bstep (se 2 (by rfl) ⟨1216374, by rfl⟩ : syracuseStep 3243665 = 2432749) B2432749
theorem B3645091 : Blo 1279958 3645091 := bstep (se 1 (by rfl) ⟨2733818, by rfl⟩ : syracuseStep 3645091 = 5467637) B5467637
theorem B2162369 : Blo 1279958 2162369 := bstep (se 2 (by rfl) ⟨810888, by rfl⟩ : syracuseStep 2162369 = 1621777) B1621777
theorem B4865741 : Blo 1279958 4865741 := bstep (se 3 (by rfl) ⟨912326, by rfl⟩ : syracuseStep 4865741 = 1824653) B1824653
theorem B3645137 : Blo 1279958 3645137 := bstep (se 2 (by rfl) ⟨1366926, by rfl⟩ : syracuseStep 3645137 = 2733853) B2733853
theorem B1441507 : Blo 1279958 1441507 := bstep (se 1 (by rfl) ⟨1081130, by rfl⟩ : syracuseStep 1441507 = 2162261) B2162261
theorem B1539859 : Blo 1279958 1539859 := bstep (se 1 (by rfl) ⟨1154894, by rfl⟩ : syracuseStep 1539859 = 2309789) B2309789
theorem B2162497 : Blo 1279958 2162497 := bstep (se 2 (by rfl) ⟨810936, by rfl⟩ : syracuseStep 2162497 = 1621873) B1621873
theorem B1367875 : Blo 1279958 1367875 := bstep (se 1 (by rfl) ⟨1025906, by rfl⟩ : syracuseStep 1367875 = 2051813) B2051813
theorem B2162531 : Blo 1279958 2162531 := bstep (se 1 (by rfl) ⟨1621898, by rfl⟩ : syracuseStep 2162531 = 3243797) B3243797
theorem B1441651 : Blo 1279958 1441651 := bstep (se 1 (by rfl) ⟨1081238, by rfl⟩ : syracuseStep 1441651 = 2162477) B2162477
theorem B2883473 : Blo 1279958 2883473 := bstep (se 2 (by rfl) ⟨1081302, by rfl⟩ : syracuseStep 2883473 = 2162605) B2162605
theorem B2883491 : Blo 1279958 2883491 := bstep (se 1 (by rfl) ⟨2162618, by rfl⟩ : syracuseStep 2883491 = 4325237) B4325237
theorem B1621939 : Blo 1279958 1621939 := bstep (se 1 (by rfl) ⟨1216454, by rfl⟩ : syracuseStep 1621939 = 2432909) B2432909
theorem B2162659 : Blo 1279958 2162659 := bstep (se 1 (by rfl) ⟨1621994, by rfl⟩ : syracuseStep 2162659 = 3243989) B3243989
theorem B4325399 : Blo 1279958 4325399 := bstep (se 1 (by rfl) ⟨3244049, by rfl⟩ : syracuseStep 4325399 = 6488099) B6488099
theorem B2162713 : Blo 1279958 2162713 := bstep (se 2 (by rfl) ⟨811017, by rfl⟩ : syracuseStep 2162713 = 1622035) B1622035
theorem B2883635 : Blo 1279958 2883635 := bstep (se 1 (by rfl) ⟨2162726, by rfl⟩ : syracuseStep 2883635 = 4325453) B4325453
theorem B20774987 : Blo 1279958 20774987 := bstep (se 1 (by rfl) ⟨15581240, by rfl⟩ : syracuseStep 20774987 = 31162481) B31162481
theorem B1441867 : Blo 1279958 1441867 := bstep (se 1 (by rfl) ⟨1081400, by rfl⟩ : syracuseStep 1441867 = 2162801) B2162801
theorem B2883671 : Blo 1279958 2883671 := bstep (se 1 (by rfl) ⟨2162753, by rfl⟩ : syracuseStep 2883671 = 4325507) B4325507
theorem B3244121 : Blo 1279958 3244121 := bstep (se 2 (by rfl) ⟨1216545, by rfl⟩ : syracuseStep 3244121 = 2433091) B2433091
theorem B4866227 : Blo 1279958 4866227 := bstep (se 1 (by rfl) ⟨3649670, by rfl⟩ : syracuseStep 4866227 = 7299341) B7299341
theorem B1441975 : Blo 1279958 1441975 := bstep (se 1 (by rfl) ⟨1081481, by rfl⟩ : syracuseStep 1441975 = 2162963) B2162963
theorem B1974487 : Blo 1279958 1974487 := bstep (se 1 (by rfl) ⟨1480865, by rfl⟩ : syracuseStep 1974487 = 2961731) B2961731
theorem B8765657 : Blo 1279958 8765657 := bstep (se 2 (by rfl) ⟨3287121, by rfl⟩ : syracuseStep 8765657 = 6574243) B6574243
theorem B3645661 : Blo 1279958 3645661 := bstep (se 3 (by rfl) ⟨683561, by rfl⟩ : syracuseStep 3645661 = 1367123) B1367123
theorem B2883851 : Blo 1279958 2883851 := bstep (se 1 (by rfl) ⟨2162888, by rfl⟩ : syracuseStep 2883851 = 4325777) B4325777
theorem B3645719 : Blo 1279958 3645719 := bstep (se 1 (by rfl) ⟨2734289, by rfl⟩ : syracuseStep 3645719 = 5468579) B5468579
theorem B2883905 : Blo 1279958 2883905 := bstep (se 2 (by rfl) ⟨1081464, by rfl⟩ : syracuseStep 2883905 = 2162929) B2162929
theorem B1622359 : Blo 1279958 1622359 := bstep (se 1 (by rfl) ⟨1216769, by rfl⟩ : syracuseStep 1622359 = 2433539) B2433539
theorem B1442155 : Blo 1279958 1442155 := bstep (se 1 (by rfl) ⟨1081616, by rfl⟩ : syracuseStep 1442155 = 2163233) B2163233
theorem B2433395 : Blo 1279958 2433395 := bstep (se 1 (by rfl) ⟨1825046, by rfl⟩ : syracuseStep 2433395 = 3650093) B3650093
theorem B2736587 : Blo 1279958 2736587 := bstep (se 1 (by rfl) ⟨2052440, by rfl⟩ : syracuseStep 2736587 = 4104881) B4104881
theorem B2884121 : Blo 1279958 2884121 := bstep (se 2 (by rfl) ⟨1081545, by rfl⟩ : syracuseStep 2884121 = 2163091) B2163091
theorem B4325939 : Blo 1279958 4325939 := bstep (se 1 (by rfl) ⟨3244454, by rfl⟩ : syracuseStep 4325939 = 6488909) B6488909
theorem B7299659 : Blo 1279958 7299659 := bstep (se 1 (by rfl) ⟨5474744, by rfl⟩ : syracuseStep 7299659 = 10949489) B10949489
theorem B2163287 : Blo 1279958 2163287 := bstep (se 1 (by rfl) ⟨1622465, by rfl⟩ : syracuseStep 2163287 = 3244931) B3244931
theorem B2884211 : Blo 1279958 2884211 := bstep (se 1 (by rfl) ⟨2163158, by rfl⟩ : syracuseStep 2884211 = 4326317) B4326317
theorem B1368695 : Blo 1279958 1368695 := bstep (se 1 (by rfl) ⟨1026521, by rfl⟩ : syracuseStep 1368695 = 2053043) B2053043
theorem B2884247 : Blo 1279958 2884247 := bstep (se 1 (by rfl) ⟨2163185, by rfl⟩ : syracuseStep 2884247 = 4326371) B4326371
theorem B6152921 : Blo 1279958 6152921 := bstep (se 2 (by rfl) ⟨2307345, by rfl⟩ : syracuseStep 6152921 = 4614691) B4614691
theorem B1368823 : Blo 1279958 1368823 := bstep (se 1 (by rfl) ⟨1026617, by rfl⟩ : syracuseStep 1368823 = 2053235) B2053235
theorem B15582017 : Blo 1279958 15582017 := bstep (se 2 (by rfl) ⟨5843256, by rfl⟩ : syracuseStep 15582017 = 11686513) B11686513
theorem B4326209 : Blo 1279958 4326209 := bstep (se 2 (by rfl) ⟨1622328, by rfl⟩ : syracuseStep 4326209 = 3244657) B3244657
theorem B2737099 : Blo 1279958 2737099 := bstep (se 1 (by rfl) ⟨2052824, by rfl⟩ : syracuseStep 2737099 = 4105649) B4105649
theorem B5473241 : Blo 1279958 5473241 := bstep (se 2 (by rfl) ⟨2052465, by rfl⟩ : syracuseStep 5473241 = 4104931) B4104931
theorem B2466803 : Blo 1279958 2466803 := bstep (se 1 (by rfl) ⟨1850102, by rfl⟩ : syracuseStep 2466803 = 3700205) B3700205
theorem B6480971 : Blo 1279958 6480971 := bstep (se 1 (by rfl) ⟨4860728, by rfl⟩ : syracuseStep 6480971 = 9721457) B9721457
theorem B14582915 : Blo 1279958 14582915 := bstep (se 1 (by rfl) ⟨10937186, by rfl⟩ : syracuseStep 14582915 = 21874373) B21874373
theorem B2598041 : Blo 1279958 2598041 := bstep (se 2 (by rfl) ⟨974265, by rfl⟩ : syracuseStep 2598041 = 1948531) B1948531
theorem B1975511 : Blo 1279958 1975511 := bstep (se 1 (by rfl) ⟨1481633, by rfl⟩ : syracuseStep 1975511 = 2963267) B2963267
theorem B4105495 : Blo 1279958 4105495 := bstep (se 1 (by rfl) ⟨3079121, by rfl⟩ : syracuseStep 4105495 = 6158243) B6158243
theorem B9487691 : Blo 1279958 9487691 := bstep (se 1 (by rfl) ⟨7115768, by rfl⟩ : syracuseStep 9487691 = 14231537) B14231537
theorem B5547437 : Blo 1279958 5547437 := bstep (se 3 (by rfl) ⟨1040144, by rfl⟩ : syracuseStep 5547437 = 2080289) B2080289
theorem B3892673 : Blo 1279958 3892673 := bstep (se 2 (by rfl) ⟨1459752, by rfl⟩ : syracuseStep 3892673 = 2919505) B2919505
theorem B3646937 : Blo 1279958 3646937 := bstep (se 2 (by rfl) ⟨1367601, by rfl⟩ : syracuseStep 3646937 = 2735203) B2735203
theorem B31180301 : Blo 1279958 31180301 := bstep (se 3 (by rfl) ⟨5846306, by rfl⟩ : syracuseStep 31180301 = 11692613) B11692613
theorem B3647051 : Blo 1279958 3647051 := bstep (se 1 (by rfl) ⟨2735288, by rfl⟩ : syracuseStep 3647051 = 5470577) B5470577
theorem B2737817 : Blo 1279958 2737817 := bstep (se 2 (by rfl) ⟨1026681, by rfl⟩ : syracuseStep 2737817 = 2053363) B2053363
theorem B12306181 : Blo 1279958 12306181 := bstep (se 4 (by rfl) ⟨1153704, by rfl⟩ : syracuseStep 12306181 = 2307409) B2307409
theorem B9734093 : Blo 1279958 9734093 := bstep (se 3 (by rfl) ⟨1825142, by rfl⟩ : syracuseStep 9734093 = 3650285) B3650285
theorem B1279959 : Blo 1279958 1279959 := bstep (se 1 (by rfl) ⟨959969, by rfl⟩ : syracuseStep 1279959 = 1919939) B1919939
theorem B1279979 : Blo 1279958 1279979 := bstep (se 1 (by rfl) ⟨959984, by rfl⟩ : syracuseStep 1279979 = 1919969) B1919969
theorem B1279991 : Blo 1279958 1279991 := bstep (se 1 (by rfl) ⟨959993, by rfl⟩ : syracuseStep 1279991 = 1919987) B1919987
theorem B1280011 : Blo 1279958 1280011 := bstep (se 1 (by rfl) ⟨960008, by rfl⟩ : syracuseStep 1280011 = 1920017) B1920017
theorem B6924305 : Blo 1279958 6924305 := bstep (se 2 (by rfl) ⟨2596614, by rfl⟩ : syracuseStep 6924305 = 5193229) B5193229
theorem B1280023 : Blo 1279958 1280023 := bstep (se 1 (by rfl) ⟨960017, by rfl⟩ : syracuseStep 1280023 = 1920035) B1920035
theorem B1280043 : Blo 1279958 1280043 := bstep (se 1 (by rfl) ⟨960032, by rfl⟩ : syracuseStep 1280043 = 1920065) B1920065
theorem B8210477 : Blo 1279958 8210477 := bstep (se 3 (by rfl) ⟨1539464, by rfl⟩ : syracuseStep 8210477 = 3078929) B3078929
theorem B1280055 : Blo 1279958 1280055 := bstep (se 1 (by rfl) ⟨960041, by rfl⟩ : syracuseStep 1280055 = 1920083) B1920083
theorem B1280075 : Blo 1279958 1280075 := bstep (se 1 (by rfl) ⟨960056, by rfl⟩ : syracuseStep 1280075 = 1920113) B1920113
theorem B4106315 : Blo 1279958 4106315 := bstep (se 1 (by rfl) ⟨3079736, by rfl⟩ : syracuseStep 4106315 = 6159473) B6159473
theorem B1280087 : Blo 1279958 1280087 := bstep (se 1 (by rfl) ⟨960065, by rfl⟩ : syracuseStep 1280087 = 1920131) B1920131
theorem B1280107 : Blo 1279958 1280107 := bstep (se 1 (by rfl) ⟨960080, by rfl⟩ : syracuseStep 1280107 = 1920161) B1920161
theorem B1280119 : Blo 1279958 1280119 := bstep (se 1 (by rfl) ⟨960089, by rfl⟩ : syracuseStep 1280119 = 1920179) B1920179
theorem B1280139 : Blo 1279958 1280139 := bstep (se 1 (by rfl) ⟨960104, by rfl⟩ : syracuseStep 1280139 = 1920209) B1920209
theorem B1280151 : Blo 1279958 1280151 := bstep (se 1 (by rfl) ⟨960113, by rfl⟩ : syracuseStep 1280151 = 1920227) B1920227
theorem B4679831 : Blo 1279958 4679831 := bstep (se 1 (by rfl) ⟨3509873, by rfl⟩ : syracuseStep 4679831 = 7019747) B7019747
theorem B1280171 : Blo 1279958 1280171 := bstep (se 1 (by rfl) ⟨960128, by rfl⟩ : syracuseStep 1280171 = 1920257) B1920257
theorem B1280183 : Blo 1279958 1280183 := bstep (se 1 (by rfl) ⟨960137, by rfl⟩ : syracuseStep 1280183 = 1920275) B1920275
theorem B4860107 : Blo 1279958 4860107 := bstep (se 1 (by rfl) ⟨3645080, by rfl⟩ : syracuseStep 4860107 = 7290161) B7290161
theorem B1280203 : Blo 1279958 1280203 := bstep (se 1 (by rfl) ⟨960152, by rfl⟩ : syracuseStep 1280203 = 1920305) B1920305
theorem B1280215 : Blo 1279958 1280215 := bstep (se 1 (by rfl) ⟨960161, by rfl⟩ : syracuseStep 1280215 = 1920323) B1920323
theorem B4860121 : Blo 1279958 4860121 := bstep (se 2 (by rfl) ⟨1822545, by rfl⟩ : syracuseStep 4860121 = 3645091) B3645091
theorem B1280235 : Blo 1279958 1280235 := bstep (se 1 (by rfl) ⟨960176, by rfl⟩ : syracuseStep 1280235 = 1920353) B1920353
theorem B21883121 : Blo 1279958 21883121 := bstep (se 2 (by rfl) ⟨8206170, by rfl⟩ : syracuseStep 21883121 = 16412341) B16412341
theorem B1280247 : Blo 1279958 1280247 := bstep (se 1 (by rfl) ⟨960185, by rfl⟩ : syracuseStep 1280247 = 1920371) B1920371
theorem B1280267 : Blo 1279958 1280267 := bstep (se 1 (by rfl) ⟨960200, by rfl⟩ : syracuseStep 1280267 = 1920401) B1920401
theorem B1280279 : Blo 1279958 1280279 := bstep (se 1 (by rfl) ⟨960209, by rfl⟩ : syracuseStep 1280279 = 1920419) B1920419
theorem B1280299 : Blo 1279958 1280299 := bstep (se 1 (by rfl) ⟨960224, by rfl⟩ : syracuseStep 1280299 = 1920449) B1920449
theorem B1280311 : Blo 1279958 1280311 := bstep (se 1 (by rfl) ⟨960233, by rfl⟩ : syracuseStep 1280311 = 1920467) B1920467
theorem B1280331 : Blo 1279958 1280331 := bstep (se 1 (by rfl) ⟨960248, by rfl⟩ : syracuseStep 1280331 = 1920497) B1920497
theorem B1280343 : Blo 1279958 1280343 := bstep (se 1 (by rfl) ⟨960257, by rfl⟩ : syracuseStep 1280343 = 1920515) B1920515
theorem B1730903 : Blo 1279958 1730903 := bstep (se 1 (by rfl) ⟨1298177, by rfl⟩ : syracuseStep 1730903 = 2596355) B2596355
theorem B1280363 : Blo 1279958 1280363 := bstep (se 1 (by rfl) ⟨960272, by rfl⟩ : syracuseStep 1280363 = 1920545) B1920545
theorem B1280375 : Blo 1279958 1280375 := bstep (se 1 (by rfl) ⟨960281, by rfl⟩ : syracuseStep 1280375 = 1920563) B1920563
theorem B1280395 : Blo 1279958 1280395 := bstep (se 1 (by rfl) ⟨960296, by rfl⟩ : syracuseStep 1280395 = 1920593) B1920593
theorem B1280407 : Blo 1279958 1280407 := bstep (se 1 (by rfl) ⟨960305, by rfl⟩ : syracuseStep 1280407 = 1920611) B1920611
theorem B1280427 : Blo 1279958 1280427 := bstep (se 1 (by rfl) ⟨960320, by rfl⟩ : syracuseStep 1280427 = 1920641) B1920641
theorem B9734579 : Blo 1279958 9734579 := bstep (se 1 (by rfl) ⟨7300934, by rfl⟩ : syracuseStep 9734579 = 14601869) B14601869
theorem B1280439 : Blo 1279958 1280439 := bstep (se 1 (by rfl) ⟨960329, by rfl⟩ : syracuseStep 1280439 = 1920659) B1920659
theorem B1280459 : Blo 1279958 1280459 := bstep (se 1 (by rfl) ⟨960344, by rfl⟩ : syracuseStep 1280459 = 1920689) B1920689
theorem B1280471 : Blo 1279958 1280471 := bstep (se 1 (by rfl) ⟨960353, by rfl⟩ : syracuseStep 1280471 = 1920707) B1920707
theorem B1280491 : Blo 1279958 1280491 := bstep (se 1 (by rfl) ⟨960368, by rfl⟩ : syracuseStep 1280491 = 1920737) B1920737
theorem B1280503 : Blo 1279958 1280503 := bstep (se 1 (by rfl) ⟨960377, by rfl⟩ : syracuseStep 1280503 = 1920755) B1920755
theorem B1280523 : Blo 1279958 1280523 := bstep (se 1 (by rfl) ⟨960392, by rfl⟩ : syracuseStep 1280523 = 1920785) B1920785
theorem B1280535 : Blo 1279958 1280535 := bstep (se 1 (by rfl) ⟨960401, by rfl⟩ : syracuseStep 1280535 = 1920803) B1920803
theorem B1280555 : Blo 1279958 1280555 := bstep (se 1 (by rfl) ⟨960416, by rfl⟩ : syracuseStep 1280555 = 1920833) B1920833
theorem B1280567 : Blo 1279958 1280567 := bstep (se 1 (by rfl) ⟨960425, by rfl⟩ : syracuseStep 1280567 = 1920851) B1920851
theorem B5474881 : Blo 1279958 5474881 := bstep (se 2 (by rfl) ⟨2053080, by rfl⟩ : syracuseStep 5474881 = 4106161) B4106161
theorem B1280587 : Blo 1279958 1280587 := bstep (se 1 (by rfl) ⟨960440, by rfl⟩ : syracuseStep 1280587 = 1920881) B1920881
theorem B1280599 : Blo 1279958 1280599 := bstep (se 1 (by rfl) ⟨960449, by rfl⟩ : syracuseStep 1280599 = 1920899) B1920899
theorem B1280619 : Blo 1279958 1280619 := bstep (se 1 (by rfl) ⟨960464, by rfl⟩ : syracuseStep 1280619 = 1920929) B1920929
theorem B1280631 : Blo 1279958 1280631 := bstep (se 1 (by rfl) ⟨960473, by rfl⟩ : syracuseStep 1280631 = 1920947) B1920947
theorem B1280651 : Blo 1279958 1280651 := bstep (se 1 (by rfl) ⟨960488, by rfl⟩ : syracuseStep 1280651 = 1920977) B1920977
theorem B1280663 : Blo 1279958 1280663 := bstep (se 1 (by rfl) ⟨960497, by rfl⟩ : syracuseStep 1280663 = 1920995) B1920995
theorem B1280683 : Blo 1279958 1280683 := bstep (se 1 (by rfl) ⟨960512, by rfl⟩ : syracuseStep 1280683 = 1921025) B1921025
theorem B3648179 : Blo 1279958 3648179 := bstep (se 1 (by rfl) ⟨2736134, by rfl⟩ : syracuseStep 3648179 = 5472269) B5472269
theorem B1280695 : Blo 1279958 1280695 := bstep (se 1 (by rfl) ⟨960521, by rfl⟩ : syracuseStep 1280695 = 1921043) B1921043
theorem B1280715 : Blo 1279958 1280715 := bstep (se 1 (by rfl) ⟨960536, by rfl⟩ : syracuseStep 1280715 = 1921073) B1921073
theorem B1280727 : Blo 1279958 1280727 := bstep (se 1 (by rfl) ⟨960545, by rfl⟩ : syracuseStep 1280727 = 1921091) B1921091
theorem B1280747 : Blo 1279958 1280747 := bstep (se 1 (by rfl) ⟨960560, by rfl⟩ : syracuseStep 1280747 = 1921121) B1921121
theorem B1280759 : Blo 1279958 1280759 := bstep (se 1 (by rfl) ⟨960569, by rfl⟩ : syracuseStep 1280759 = 1921139) B1921139
theorem B1280779 : Blo 1279958 1280779 := bstep (se 1 (by rfl) ⟨960584, by rfl⟩ : syracuseStep 1280779 = 1921169) B1921169
theorem B1280791 : Blo 1279958 1280791 := bstep (se 1 (by rfl) ⟨960593, by rfl⟩ : syracuseStep 1280791 = 1921187) B1921187
theorem B1280811 : Blo 1279958 1280811 := bstep (se 1 (by rfl) ⟨960608, by rfl⟩ : syracuseStep 1280811 = 1921217) B1921217
theorem B1280823 : Blo 1279958 1280823 := bstep (se 1 (by rfl) ⟨960617, by rfl⟩ : syracuseStep 1280823 = 1921235) B1921235
theorem B6482753 : Blo 1279958 6482753 := bstep (se 2 (by rfl) ⟨2431032, by rfl⟩ : syracuseStep 6482753 = 4862065) B4862065
theorem B1280843 : Blo 1279958 1280843 := bstep (se 1 (by rfl) ⟨960632, by rfl⟩ : syracuseStep 1280843 = 1921265) B1921265
theorem B1280855 : Blo 1279958 1280855 := bstep (se 1 (by rfl) ⟨960641, by rfl⟩ : syracuseStep 1280855 = 1921283) B1921283
theorem B1280875 : Blo 1279958 1280875 := bstep (se 1 (by rfl) ⟨960656, by rfl⟩ : syracuseStep 1280875 = 1921313) B1921313
theorem B1280887 : Blo 1279958 1280887 := bstep (se 1 (by rfl) ⟨960665, by rfl⟩ : syracuseStep 1280887 = 1921331) B1921331
theorem B7293827 : Blo 1279958 7293827 := bstep (se 1 (by rfl) ⟨5470370, by rfl⟩ : syracuseStep 7293827 = 10940741) B10940741
theorem B1280907 : Blo 1279958 1280907 := bstep (se 1 (by rfl) ⟨960680, by rfl⟩ : syracuseStep 1280907 = 1921361) B1921361
theorem B9227159 : Blo 1279958 9227159 := bstep (se 1 (by rfl) ⟨6920369, by rfl⟩ : syracuseStep 9227159 = 13840739) B13840739
theorem B1280919 : Blo 1279958 1280919 := bstep (se 1 (by rfl) ⟨960689, by rfl⟩ : syracuseStep 1280919 = 1921379) B1921379
theorem B1280939 : Blo 1279958 1280939 := bstep (se 1 (by rfl) ⟨960704, by rfl⟩ : syracuseStep 1280939 = 1921409) B1921409
theorem B1280951 : Blo 1279958 1280951 := bstep (se 1 (by rfl) ⟨960713, by rfl⟩ : syracuseStep 1280951 = 1921427) B1921427
theorem B1280971 : Blo 1279958 1280971 := bstep (se 1 (by rfl) ⟨960728, by rfl⟩ : syracuseStep 1280971 = 1921457) B1921457
theorem B1280983 : Blo 1279958 1280983 := bstep (se 1 (by rfl) ⟨960737, by rfl⟩ : syracuseStep 1280983 = 1921475) B1921475
theorem B1281003 : Blo 1279958 1281003 := bstep (se 1 (by rfl) ⟨960752, by rfl⟩ : syracuseStep 1281003 = 1921505) B1921505
theorem B1281015 : Blo 1279958 1281015 := bstep (se 1 (by rfl) ⟨960761, by rfl⟩ : syracuseStep 1281015 = 1921523) B1921523
theorem B1920011 : Blo 1279958 1920011 := bstep (se 1 (by rfl) ⟨1440008, by rfl⟩ : syracuseStep 1920011 = 2880017) B2880017
theorem B1281035 : Blo 1279958 1281035 := bstep (se 1 (by rfl) ⟨960776, by rfl⟩ : syracuseStep 1281035 = 1921553) B1921553
theorem B1920023 : Blo 1279958 1920023 := bstep (se 1 (by rfl) ⟨1440017, by rfl⟩ : syracuseStep 1920023 = 2880035) B2880035
theorem B2051095 : Blo 1279958 2051095 := bstep (se 1 (by rfl) ⟨1538321, by rfl⟩ : syracuseStep 2051095 = 3076643) B3076643
theorem B1281047 : Blo 1279958 1281047 := bstep (se 1 (by rfl) ⟨960785, by rfl⟩ : syracuseStep 1281047 = 1921571) B1921571
theorem B1281067 : Blo 1279958 1281067 := bstep (se 1 (by rfl) ⟨960800, by rfl⟩ : syracuseStep 1281067 = 1921601) B1921601
theorem B1281079 : Blo 1279958 1281079 := bstep (se 1 (by rfl) ⟨960809, by rfl⟩ : syracuseStep 1281079 = 1921619) B1921619
theorem B3648577 : Blo 1279958 3648577 := bstep (se 2 (by rfl) ⟨1368216, by rfl⟩ : syracuseStep 3648577 = 2736433) B2736433
theorem B1281099 : Blo 1279958 1281099 := bstep (se 1 (by rfl) ⟨960824, by rfl⟩ : syracuseStep 1281099 = 1921649) B1921649
theorem B1281111 : Blo 1279958 1281111 := bstep (se 1 (by rfl) ⟨960833, by rfl⟩ : syracuseStep 1281111 = 1921667) B1921667
theorem B1920089 : Blo 1279958 1920089 := bstep (se 2 (by rfl) ⟨720033, by rfl⟩ : syracuseStep 1920089 = 1440067) B1440067
theorem B1281131 : Blo 1279958 1281131 := bstep (se 1 (by rfl) ⟨960848, by rfl⟩ : syracuseStep 1281131 = 1921697) B1921697
theorem B1281143 : Blo 1279958 1281143 := bstep (se 1 (by rfl) ⟨960857, by rfl⟩ : syracuseStep 1281143 = 1921715) B1921715
theorem B1281163 : Blo 1279958 1281163 := bstep (se 1 (by rfl) ⟨960872, by rfl⟩ : syracuseStep 1281163 = 1921745) B1921745
theorem B4861079 : Blo 1279958 4861079 := bstep (se 1 (by rfl) ⟨3645809, by rfl⟩ : syracuseStep 4861079 = 7291619) B7291619
theorem B1281175 : Blo 1279958 1281175 := bstep (se 1 (by rfl) ⟨960881, by rfl⟩ : syracuseStep 1281175 = 1921763) B1921763
theorem B10390679 : Blo 1279958 10390679 := bstep (se 1 (by rfl) ⟨7793009, by rfl⟩ : syracuseStep 10390679 = 15586019) B15586019
theorem B1281195 : Blo 1279958 1281195 := bstep (se 1 (by rfl) ⟨960896, by rfl⟩ : syracuseStep 1281195 = 1921793) B1921793
theorem B9235633 : Blo 1279958 9235633 := bstep (se 2 (by rfl) ⟨3463362, by rfl⟩ : syracuseStep 9235633 = 6926725) B6926725
theorem B1281207 : Blo 1279958 1281207 := bstep (se 1 (by rfl) ⟨960905, by rfl⟩ : syracuseStep 1281207 = 1921811) B1921811
theorem B1920203 : Blo 1279958 1920203 := bstep (se 1 (by rfl) ⟨1440152, by rfl⟩ : syracuseStep 1920203 = 2880305) B2880305
theorem B2190539 : Blo 1279958 2190539 := bstep (se 1 (by rfl) ⟨1642904, by rfl⟩ : syracuseStep 2190539 = 3285809) B3285809
theorem B1281227 : Blo 1279958 1281227 := bstep (se 1 (by rfl) ⟨960920, by rfl⟩ : syracuseStep 1281227 = 1921841) B1921841
theorem B1920215 : Blo 1279958 1920215 := bstep (se 1 (by rfl) ⟨1440161, by rfl⟩ : syracuseStep 1920215 = 2880323) B2880323
theorem B1281239 : Blo 1279958 1281239 := bstep (se 1 (by rfl) ⟨960929, by rfl⟩ : syracuseStep 1281239 = 1921859) B1921859
theorem B1281259 : Blo 1279958 1281259 := bstep (se 1 (by rfl) ⟨960944, by rfl⟩ : syracuseStep 1281259 = 1921889) B1921889
theorem B1281271 : Blo 1279958 1281271 := bstep (se 1 (by rfl) ⟨960953, by rfl⟩ : syracuseStep 1281271 = 1921907) B1921907
theorem B23358725 : Blo 1279958 23358725 := bstep (se 4 (by rfl) ⟨2189880, by rfl⟩ : syracuseStep 23358725 = 4379761) B4379761
theorem B55430405 : Blo 1279958 55430405 := bstep (se 4 (by rfl) ⟨5196600, by rfl⟩ : syracuseStep 55430405 = 10393201) B10393201
theorem B1281291 : Blo 1279958 1281291 := bstep (se 1 (by rfl) ⟨960968, by rfl⟩ : syracuseStep 1281291 = 1921937) B1921937
theorem B1281303 : Blo 1279958 1281303 := bstep (se 1 (by rfl) ⟨960977, by rfl⟩ : syracuseStep 1281303 = 1921955) B1921955
theorem B1920281 : Blo 1279958 1920281 := bstep (se 2 (by rfl) ⟨720105, by rfl⟩ : syracuseStep 1920281 = 1440211) B1440211
theorem B1281323 : Blo 1279958 1281323 := bstep (se 1 (by rfl) ⟨960992, by rfl⟩ : syracuseStep 1281323 = 1921985) B1921985
theorem B1281335 : Blo 1279958 1281335 := bstep (se 1 (by rfl) ⟨961001, by rfl⟩ : syracuseStep 1281335 = 1922003) B1922003
theorem B7294283 : Blo 1279958 7294283 := bstep (se 1 (by rfl) ⟨5470712, by rfl⟩ : syracuseStep 7294283 = 10941425) B10941425
theorem B1281355 : Blo 1279958 1281355 := bstep (se 1 (by rfl) ⟨961016, by rfl⟩ : syracuseStep 1281355 = 1922033) B1922033
theorem B1281367 : Blo 1279958 1281367 := bstep (se 1 (by rfl) ⟨961025, by rfl⟩ : syracuseStep 1281367 = 1922051) B1922051
theorem B9227621 : Blo 1279958 9227621 := bstep (se 4 (by rfl) ⟨865089, by rfl⟩ : syracuseStep 9227621 = 1730179) B1730179
theorem B1281387 : Blo 1279958 1281387 := bstep (se 1 (by rfl) ⟨961040, by rfl⟩ : syracuseStep 1281387 = 1922081) B1922081
theorem B1281399 : Blo 1279958 1281399 := bstep (se 1 (by rfl) ⟨961049, by rfl⟩ : syracuseStep 1281399 = 1922099) B1922099
theorem B1920395 : Blo 1279958 1920395 := bstep (se 1 (by rfl) ⟨1440296, by rfl⟩ : syracuseStep 1920395 = 2880593) B2880593
theorem B1281419 : Blo 1279958 1281419 := bstep (se 1 (by rfl) ⟨961064, by rfl⟩ : syracuseStep 1281419 = 1922129) B1922129
theorem B1920407 : Blo 1279958 1920407 := bstep (se 1 (by rfl) ⟨1440305, by rfl⟩ : syracuseStep 1920407 = 2880611) B2880611
theorem B1281431 : Blo 1279958 1281431 := bstep (se 1 (by rfl) ⟨961073, by rfl⟩ : syracuseStep 1281431 = 1922147) B1922147
theorem B1281451 : Blo 1279958 1281451 := bstep (se 1 (by rfl) ⟨961088, by rfl⟩ : syracuseStep 1281451 = 1922177) B1922177
theorem B1281463 : Blo 1279958 1281463 := bstep (se 1 (by rfl) ⟨961097, by rfl⟩ : syracuseStep 1281463 = 1922195) B1922195
theorem B1281483 : Blo 1279958 1281483 := bstep (se 1 (by rfl) ⟨961112, by rfl⟩ : syracuseStep 1281483 = 1922225) B1922225
theorem B1281495 : Blo 1279958 1281495 := bstep (se 1 (by rfl) ⟨961121, by rfl⟩ : syracuseStep 1281495 = 1922243) B1922243
theorem B1920473 : Blo 1279958 1920473 := bstep (se 2 (by rfl) ⟨720177, by rfl⟩ : syracuseStep 1920473 = 1440355) B1440355
theorem B1281515 : Blo 1279958 1281515 := bstep (se 1 (by rfl) ⟨961136, by rfl⟩ : syracuseStep 1281515 = 1922273) B1922273
theorem B1281527 : Blo 1279958 1281527 := bstep (se 1 (by rfl) ⟨961145, by rfl⟩ : syracuseStep 1281527 = 1922291) B1922291
theorem B1281547 : Blo 1279958 1281547 := bstep (se 1 (by rfl) ⟨961160, by rfl⟩ : syracuseStep 1281547 = 1922321) B1922321
theorem B22171153 : Blo 1279958 22171153 := bstep (se 2 (by rfl) ⟨8314182, by rfl⟩ : syracuseStep 22171153 = 16628365) B16628365
theorem B1281559 : Blo 1279958 1281559 := bstep (se 1 (by rfl) ⟨961169, by rfl⟩ : syracuseStep 1281559 = 1922339) B1922339
theorem B1281579 : Blo 1279958 1281579 := bstep (se 1 (by rfl) ⟨961184, by rfl⟩ : syracuseStep 1281579 = 1922369) B1922369
theorem B1281591 : Blo 1279958 1281591 := bstep (se 1 (by rfl) ⟨961193, by rfl⟩ : syracuseStep 1281591 = 1922387) B1922387
theorem B1920587 : Blo 1279958 1920587 := bstep (se 1 (by rfl) ⟨1440440, by rfl⟩ : syracuseStep 1920587 = 2880881) B2880881
theorem B2051659 : Blo 1279958 2051659 := bstep (se 1 (by rfl) ⟨1538744, by rfl⟩ : syracuseStep 2051659 = 3077489) B3077489
theorem B1281611 : Blo 1279958 1281611 := bstep (se 1 (by rfl) ⟨961208, by rfl⟩ : syracuseStep 1281611 = 1922417) B1922417
theorem B1920599 : Blo 1279958 1920599 := bstep (se 1 (by rfl) ⟨1440449, by rfl⟩ : syracuseStep 1920599 = 2880899) B2880899
theorem B1281623 : Blo 1279958 1281623 := bstep (se 1 (by rfl) ⟨961217, by rfl⟩ : syracuseStep 1281623 = 1922435) B1922435
theorem B2920025 : Blo 1279958 2920025 := bstep (se 2 (by rfl) ⟨1095009, by rfl⟩ : syracuseStep 2920025 = 2190019) B2190019
theorem B1281643 : Blo 1279958 1281643 := bstep (se 1 (by rfl) ⟨961232, by rfl⟩ : syracuseStep 1281643 = 1922465) B1922465
theorem B1281655 : Blo 1279958 1281655 := bstep (se 1 (by rfl) ⟨961241, by rfl⟩ : syracuseStep 1281655 = 1922483) B1922483
theorem B2051723 : Blo 1279958 2051723 := bstep (se 1 (by rfl) ⟨1538792, by rfl⟩ : syracuseStep 2051723 = 3077585) B3077585
theorem B1281675 : Blo 1279958 1281675 := bstep (se 1 (by rfl) ⟨961256, by rfl⟩ : syracuseStep 1281675 = 1922513) B1922513
theorem B1281687 : Blo 1279958 1281687 := bstep (se 1 (by rfl) ⟨961265, by rfl⟩ : syracuseStep 1281687 = 1922531) B1922531
theorem B1920665 : Blo 1279958 1920665 := bstep (se 2 (by rfl) ⟨720249, by rfl⟩ : syracuseStep 1920665 = 1440499) B1440499
theorem B1281707 : Blo 1279958 1281707 := bstep (se 1 (by rfl) ⟨961280, by rfl⟩ : syracuseStep 1281707 = 1922561) B1922561
theorem B1281719 : Blo 1279958 1281719 := bstep (se 1 (by rfl) ⟨961289, by rfl⟩ : syracuseStep 1281719 = 1922579) B1922579
theorem B4320971 : Blo 1279958 4320971 := bstep (se 1 (by rfl) ⟨3240728, by rfl⟩ : syracuseStep 4320971 = 6481457) B6481457
theorem B1281739 : Blo 1279958 1281739 := bstep (se 1 (by rfl) ⟨961304, by rfl⟩ : syracuseStep 1281739 = 1922609) B1922609
theorem B1281751 : Blo 1279958 1281751 := bstep (se 1 (by rfl) ⟨961313, by rfl⟩ : syracuseStep 1281751 = 1922627) B1922627
theorem B1281771 : Blo 1279958 1281771 := bstep (se 1 (by rfl) ⟨961328, by rfl⟩ : syracuseStep 1281771 = 1922657) B1922657
theorem B1281783 : Blo 1279958 1281783 := bstep (se 1 (by rfl) ⟨961337, by rfl⟩ : syracuseStep 1281783 = 1922675) B1922675
theorem B1920779 : Blo 1279958 1920779 := bstep (se 1 (by rfl) ⟨1440584, by rfl⟩ : syracuseStep 1920779 = 2881169) B2881169
theorem B1281803 : Blo 1279958 1281803 := bstep (se 1 (by rfl) ⟨961352, by rfl⟩ : syracuseStep 1281803 = 1922705) B1922705
theorem B1920791 : Blo 1279958 1920791 := bstep (se 1 (by rfl) ⟨1440593, by rfl⟩ : syracuseStep 1920791 = 2881187) B2881187
theorem B1281815 : Blo 1279958 1281815 := bstep (se 1 (by rfl) ⟨961361, by rfl⟩ : syracuseStep 1281815 = 1922723) B1922723
theorem B1281835 : Blo 1279958 1281835 := bstep (se 1 (by rfl) ⟨961376, by rfl⟩ : syracuseStep 1281835 = 1922753) B1922753
theorem B1281847 : Blo 1279958 1281847 := bstep (se 1 (by rfl) ⟨961385, by rfl⟩ : syracuseStep 1281847 = 1922771) B1922771
theorem B5467979 : Blo 1279958 5467979 := bstep (se 1 (by rfl) ⟨4100984, by rfl⟩ : syracuseStep 5467979 = 8201969) B8201969
theorem B1281867 : Blo 1279958 1281867 := bstep (se 1 (by rfl) ⟨961400, by rfl⟩ : syracuseStep 1281867 = 1922801) B1922801
theorem B1281879 : Blo 1279958 1281879 := bstep (se 1 (by rfl) ⟨961409, by rfl⟩ : syracuseStep 1281879 = 1922819) B1922819
theorem B1920857 : Blo 1279958 1920857 := bstep (se 2 (by rfl) ⟨720321, by rfl⟩ : syracuseStep 1920857 = 1440643) B1440643
theorem B1281899 : Blo 1279958 1281899 := bstep (se 1 (by rfl) ⟨961424, by rfl⟩ : syracuseStep 1281899 = 1922849) B1922849
theorem B1281911 : Blo 1279958 1281911 := bstep (se 1 (by rfl) ⟨961433, by rfl⟩ : syracuseStep 1281911 = 1922867) B1922867
theorem B1822603 : Blo 1279958 1822603 := bstep (se 1 (by rfl) ⟨1366952, by rfl⟩ : syracuseStep 1822603 = 2733905) B2733905
theorem B1281931 : Blo 1279958 1281931 := bstep (se 1 (by rfl) ⟨961448, by rfl⟩ : syracuseStep 1281931 = 1922897) B1922897
theorem B6000529 : Blo 1279958 6000529 := bstep (se 2 (by rfl) ⟨2250198, by rfl⟩ : syracuseStep 6000529 = 4500397) B4500397
theorem B1281943 : Blo 1279958 1281943 := bstep (se 1 (by rfl) ⟨961457, by rfl⟩ : syracuseStep 1281943 = 1922915) B1922915
theorem B13840307 : Blo 1279958 13840307 := bstep (se 1 (by rfl) ⟨10380230, by rfl⟩ : syracuseStep 13840307 = 20760461) B20760461
theorem B1920971 : Blo 1279958 1920971 := bstep (se 1 (by rfl) ⟨1440728, by rfl⟩ : syracuseStep 1920971 = 2881457) B2881457
theorem B1920983 : Blo 1279958 1920983 := bstep (se 1 (by rfl) ⟨1440737, by rfl⟩ : syracuseStep 1920983 = 2881475) B2881475
theorem B4321241 : Blo 1279958 4321241 := bstep (se 2 (by rfl) ⟨1620465, by rfl⟩ : syracuseStep 4321241 = 3240931) B3240931
theorem B3239959 : Blo 1279958 3239959 := bstep (se 1 (by rfl) ⟨2429969, by rfl⟩ : syracuseStep 3239959 = 4859939) B4859939
theorem B1921049 : Blo 1279958 1921049 := bstep (se 2 (by rfl) ⟨720393, by rfl⟩ : syracuseStep 1921049 = 1440787) B1440787
theorem B6926381 : Blo 1279958 6926381 := bstep (se 3 (by rfl) ⟨1298696, by rfl⟩ : syracuseStep 6926381 = 2597393) B2597393
theorem B23375947 : Blo 1279958 23375947 := bstep (se 1 (by rfl) ⟨17531960, by rfl⟩ : syracuseStep 23375947 = 35063921) B35063921
theorem B10391645 : Blo 1279958 10391645 := bstep (se 3 (by rfl) ⟨1948433, by rfl⟩ : syracuseStep 10391645 = 3896867) B3896867
theorem B1921163 : Blo 1279958 1921163 := bstep (se 1 (by rfl) ⟨1440872, by rfl⟩ : syracuseStep 1921163 = 2881745) B2881745
theorem B1921175 : Blo 1279958 1921175 := bstep (se 1 (by rfl) ⟨1440881, by rfl⟩ : syracuseStep 1921175 = 2881763) B2881763
theorem B2191511 : Blo 1279958 2191511 := bstep (se 1 (by rfl) ⟨1643633, by rfl⟩ : syracuseStep 2191511 = 3287267) B3287267
theorem B1921241 : Blo 1279958 1921241 := bstep (se 2 (by rfl) ⟨720465, by rfl⟩ : syracuseStep 1921241 = 1440931) B1440931
theorem B9728261 : Blo 1279958 9728261 := bstep (se 4 (by rfl) ⟨912024, by rfl⟩ : syracuseStep 9728261 = 1824049) B1824049
theorem B4378931 : Blo 1279958 4378931 := bstep (se 1 (by rfl) ⟨3284198, by rfl⟩ : syracuseStep 4378931 = 6568397) B6568397
theorem B1921355 : Blo 1279958 1921355 := bstep (se 1 (by rfl) ⟨1441016, by rfl⟩ : syracuseStep 1921355 = 2882033) B2882033
theorem B1921367 : Blo 1279958 1921367 := bstep (se 1 (by rfl) ⟨1441025, by rfl⟩ : syracuseStep 1921367 = 2882051) B2882051
theorem B2920819 : Blo 1279958 2920819 := bstep (se 1 (by rfl) ⟨2190614, by rfl⟩ : syracuseStep 2920819 = 4381229) B4381229
theorem B4862339 : Blo 1279958 4862339 := bstep (se 1 (by rfl) ⟨3646754, by rfl⟩ : syracuseStep 4862339 = 7293509) B7293509
theorem B1921433 : Blo 1279958 1921433 := bstep (se 2 (by rfl) ⟨720537, by rfl⟩ : syracuseStep 1921433 = 1441075) B1441075
theorem B3240395 : Blo 1279958 3240395 := bstep (se 1 (by rfl) ⟨2430296, by rfl⟩ : syracuseStep 3240395 = 4860593) B4860593
theorem B1921547 : Blo 1279958 1921547 := bstep (se 1 (by rfl) ⟨1441160, by rfl⟩ : syracuseStep 1921547 = 2882321) B2882321
theorem B1921559 : Blo 1279958 1921559 := bstep (se 1 (by rfl) ⟨1441169, by rfl⟩ : syracuseStep 1921559 = 2882339) B2882339
theorem B2880089 : Blo 1279958 2880089 := bstep (se 2 (by rfl) ⟨1080033, by rfl⟩ : syracuseStep 2880089 = 2160067) B2160067
theorem B1921625 : Blo 1279958 1921625 := bstep (se 2 (by rfl) ⟨720609, by rfl⟩ : syracuseStep 1921625 = 1441219) B1441219
theorem B2052697 : Blo 1279958 2052697 := bstep (se 2 (by rfl) ⟨769761, by rfl⟩ : syracuseStep 2052697 = 1539523) B1539523
theorem B4321943 : Blo 1279958 4321943 := bstep (se 1 (by rfl) ⟨3241457, by rfl⟩ : syracuseStep 4321943 = 6482915) B6482915
theorem B2880179 : Blo 1279958 2880179 := bstep (se 1 (by rfl) ⟨2160134, by rfl⟩ : syracuseStep 2880179 = 4320269) B4320269
theorem B1921739 : Blo 1279958 1921739 := bstep (se 1 (by rfl) ⟨1441304, by rfl⟩ : syracuseStep 1921739 = 2882609) B2882609
theorem B2880215 : Blo 1279958 2880215 := bstep (se 1 (by rfl) ⟨2160161, by rfl⟩ : syracuseStep 2880215 = 4320323) B4320323
theorem B6484697 : Blo 1279958 6484697 := bstep (se 2 (by rfl) ⟨2431761, by rfl⟩ : syracuseStep 6484697 = 4863523) B4863523
theorem B1921751 : Blo 1279958 1921751 := bstep (se 1 (by rfl) ⟨1441313, by rfl⟩ : syracuseStep 1921751 = 2882627) B2882627
theorem B6157073 : Blo 1279958 6157073 := bstep (se 2 (by rfl) ⟨2308902, by rfl⟩ : syracuseStep 6157073 = 4617805) B4617805
theorem B3207959 : Blo 1279958 3207959 := bstep (se 1 (by rfl) ⟨2405969, by rfl⟩ : syracuseStep 3207959 = 4811939) B4811939
theorem B1921817 : Blo 1279958 1921817 := bstep (se 2 (by rfl) ⟨720681, by rfl⟩ : syracuseStep 1921817 = 1441363) B1441363
theorem B3240769 : Blo 1279958 3240769 := bstep (se 2 (by rfl) ⟨1215288, by rfl⟩ : syracuseStep 3240769 = 2430577) B2430577
theorem B2052953 : Blo 1279958 2052953 := bstep (se 2 (by rfl) ⟨769857, by rfl⟩ : syracuseStep 2052953 = 1539715) B1539715
theorem B2880395 : Blo 1279958 2880395 := bstep (se 1 (by rfl) ⟨2160296, by rfl⟩ : syracuseStep 2880395 = 4320593) B4320593
theorem B1921931 : Blo 1279958 1921931 := bstep (se 1 (by rfl) ⟨1441448, by rfl⟩ : syracuseStep 1921931 = 2882897) B2882897
theorem B1823639 : Blo 1279958 1823639 := bstep (se 1 (by rfl) ⟨1367729, by rfl⟩ : syracuseStep 1823639 = 2735459) B2735459
theorem B1921943 : Blo 1279958 1921943 := bstep (se 1 (by rfl) ⟨1441457, by rfl⟩ : syracuseStep 1921943 = 2882915) B2882915
theorem B2880449 : Blo 1279958 2880449 := bstep (se 2 (by rfl) ⟨1080168, by rfl⟩ : syracuseStep 2880449 = 2160337) B2160337
theorem B1922009 : Blo 1279958 1922009 := bstep (se 2 (by rfl) ⟨720753, by rfl⟩ : syracuseStep 1922009 = 1441507) B1441507
theorem B2429939 : Blo 1279958 2429939 := bstep (se 1 (by rfl) ⟨1822454, by rfl⟩ : syracuseStep 2429939 = 3644909) B3644909
theorem B2053145 : Blo 1279958 2053145 := bstep (se 2 (by rfl) ⟨769929, by rfl⟩ : syracuseStep 2053145 = 1539859) B1539859
theorem B1922123 : Blo 1279958 1922123 := bstep (se 1 (by rfl) ⟨1441592, by rfl⟩ : syracuseStep 1922123 = 2883185) B2883185
theorem B1922135 : Blo 1279958 1922135 := bstep (se 1 (by rfl) ⟨1441601, by rfl⟩ : syracuseStep 1922135 = 2883203) B2883203
theorem B1823833 : Blo 1279958 1823833 := bstep (se 2 (by rfl) ⟨683937, by rfl⟩ : syracuseStep 1823833 = 1367875) B1367875
theorem B5469277 : Blo 1279958 5469277 := bstep (se 3 (by rfl) ⟨1025489, by rfl⟩ : syracuseStep 5469277 = 2050979) B2050979
theorem B2430091 : Blo 1279958 2430091 := bstep (se 1 (by rfl) ⟨1822568, by rfl⟩ : syracuseStep 2430091 = 3645137) B3645137
theorem B2880665 : Blo 1279958 2880665 := bstep (se 2 (by rfl) ⟨1080249, by rfl⟩ : syracuseStep 2880665 = 2160499) B2160499
theorem B1922201 : Blo 1279958 1922201 := bstep (se 2 (by rfl) ⟨720825, by rfl⟩ : syracuseStep 1922201 = 1441651) B1441651
theorem B2307251 : Blo 1279958 2307251 := bstep (se 1 (by rfl) ⟨1730438, by rfl⟩ : syracuseStep 2307251 = 3460877) B3460877
theorem B4322483 : Blo 1279958 4322483 := bstep (se 1 (by rfl) ⟨3241862, by rfl⟩ : syracuseStep 4322483 = 6483725) B6483725
theorem B21050549 : Blo 1279958 21050549 := bstep (se 5 (by rfl) ⟨986744, by rfl⟩ : syracuseStep 21050549 = 1973489) B1973489
theorem B1406167 : Blo 1279958 1406167 := bstep (se 1 (by rfl) ⟨1054625, by rfl⟩ : syracuseStep 1406167 = 2109251) B2109251
theorem B2880755 : Blo 1279958 2880755 := bstep (se 1 (by rfl) ⟨2160566, by rfl⟩ : syracuseStep 2880755 = 4321133) B4321133
theorem B1922315 : Blo 1279958 1922315 := bstep (se 1 (by rfl) ⟨1441736, by rfl⟩ : syracuseStep 1922315 = 2883473) B2883473
theorem B2880791 : Blo 1279958 2880791 := bstep (se 1 (by rfl) ⟨2160593, by rfl⟩ : syracuseStep 2880791 = 4321187) B4321187
theorem B1922327 : Blo 1279958 1922327 := bstep (se 1 (by rfl) ⟨1441745, by rfl⟩ : syracuseStep 1922327 = 2883491) B2883491
theorem B2159959 : Blo 1279958 2159959 := bstep (se 1 (by rfl) ⟨1619969, by rfl⟩ : syracuseStep 2159959 = 3239939) B3239939
theorem B1922393 : Blo 1279958 1922393 := bstep (se 2 (by rfl) ⟨720897, by rfl⟩ : syracuseStep 1922393 = 1441795) B1441795
theorem B3241367 : Blo 1279958 3241367 := bstep (se 1 (by rfl) ⟨2431025, by rfl⟩ : syracuseStep 3241367 = 4862051) B4862051
theorem B5469619 : Blo 1279958 5469619 := bstep (se 1 (by rfl) ⟨4102214, by rfl⟩ : syracuseStep 5469619 = 8204429) B8204429
theorem B4322753 : Blo 1279958 4322753 := bstep (se 2 (by rfl) ⟨1621032, by rfl⟩ : syracuseStep 4322753 = 3242065) B3242065
theorem B2921921 : Blo 1279958 2921921 := bstep (se 2 (by rfl) ⟨1095720, by rfl⟩ : syracuseStep 2921921 = 2191441) B2191441
theorem B2880971 : Blo 1279958 2880971 := bstep (se 1 (by rfl) ⟨2160728, by rfl⟩ : syracuseStep 2880971 = 4321457) B4321457
theorem B1922507 : Blo 1279958 1922507 := bstep (se 1 (by rfl) ⟨1441880, by rfl⟩ : syracuseStep 1922507 = 2883761) B2883761
theorem B1922519 : Blo 1279958 1922519 := bstep (se 1 (by rfl) ⟨1441889, by rfl⟩ : syracuseStep 1922519 = 2883779) B2883779
theorem B2430425 : Blo 1279958 2430425 := bstep (se 2 (by rfl) ⟨911409, by rfl⟩ : syracuseStep 2430425 = 1822819) B1822819
theorem B2881025 : Blo 1279958 2881025 := bstep (se 2 (by rfl) ⟨1080384, by rfl⟩ : syracuseStep 2881025 = 2160769) B2160769
theorem B1922585 : Blo 1279958 1922585 := bstep (se 2 (by rfl) ⟨720969, by rfl⟩ : syracuseStep 1922585 = 1441939) B1441939
theorem B1922699 : Blo 1279958 1922699 := bstep (se 1 (by rfl) ⟨1442024, by rfl⟩ : syracuseStep 1922699 = 2884049) B2884049
theorem B1922711 : Blo 1279958 1922711 := bstep (se 1 (by rfl) ⟨1442033, by rfl⟩ : syracuseStep 1922711 = 2884067) B2884067
theorem B2881241 : Blo 1279958 2881241 := bstep (se 2 (by rfl) ⟨1080465, by rfl⟩ : syracuseStep 2881241 = 2160931) B2160931
theorem B1922777 : Blo 1279958 1922777 := bstep (se 2 (by rfl) ⟨721041, by rfl⟩ : syracuseStep 1922777 = 1442083) B1442083
theorem B2881331 : Blo 1279958 2881331 := bstep (se 1 (by rfl) ⟨2160998, by rfl⟩ : syracuseStep 2881331 = 4321997) B4321997
theorem B1922891 : Blo 1279958 1922891 := bstep (se 1 (by rfl) ⟨1442168, by rfl⟩ : syracuseStep 1922891 = 2884337) B2884337
theorem B2881367 : Blo 1279958 2881367 := bstep (se 1 (by rfl) ⟨2161025, by rfl⟩ : syracuseStep 2881367 = 4322051) B4322051
theorem B1922903 : Blo 1279958 1922903 := bstep (se 1 (by rfl) ⟨1442177, by rfl⟩ : syracuseStep 1922903 = 2884355) B2884355
theorem B4929373 : Blo 1279958 4929373 := bstep (se 3 (by rfl) ⟨924257, by rfl⟩ : syracuseStep 4929373 = 1848515) B1848515
theorem B10950551 : Blo 1279958 10950551 := bstep (se 1 (by rfl) ⟨8212913, by rfl⟩ : syracuseStep 10950551 = 16425827) B16425827
theorem B12318641 : Blo 1279958 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B2160587 : Blo 1279958 2160587 := bstep (se 1 (by rfl) ⟨1620440, by rfl⟩ : syracuseStep 2160587 = 3240881) B3240881
theorem B4323293 : Blo 1279958 4323293 := bstep (se 3 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 4323293 = 1621235) B1621235
theorem B2881547 : Blo 1279958 2881547 := bstep (se 1 (by rfl) ⟨2161160, by rfl⟩ : syracuseStep 2881547 = 4322321) B4322321
theorem B2881601 : Blo 1279958 2881601 := bstep (se 2 (by rfl) ⟨1080600, by rfl⟩ : syracuseStep 2881601 = 2161201) B2161201
theorem B2160715 : Blo 1279958 2160715 := bstep (se 1 (by rfl) ⟨1620536, by rfl⟩ : syracuseStep 2160715 = 3241073) B3241073
theorem B2431063 : Blo 1279958 2431063 := bstep (se 1 (by rfl) ⟨1823297, by rfl⟩ : syracuseStep 2431063 = 3646595) B3646595
theorem B2734195 : Blo 1279958 2734195 := bstep (se 1 (by rfl) ⟨2050646, by rfl⟩ : syracuseStep 2734195 = 4101293) B4101293
theorem B3242177 : Blo 1279958 3242177 := bstep (se 2 (by rfl) ⟨1215816, by rfl⟩ : syracuseStep 3242177 = 2431633) B2431633
theorem B1439959 : Blo 1279958 1439959 := bstep (se 1 (by rfl) ⟨1079969, by rfl⟩ : syracuseStep 1439959 = 2159939) B2159939
theorem B2160857 : Blo 1279958 2160857 := bstep (se 2 (by rfl) ⟨810321, by rfl⟩ : syracuseStep 2160857 = 1620643) B1620643
theorem B2881817 : Blo 1279958 2881817 := bstep (se 2 (by rfl) ⟨1080681, by rfl⟩ : syracuseStep 2881817 = 2161363) B2161363
theorem B6486317 : Blo 1279958 6486317 := bstep (se 3 (by rfl) ⟨1216184, by rfl⟩ : syracuseStep 6486317 = 2432369) B2432369
theorem B1947991 : Blo 1279958 1947991 := bstep (se 1 (by rfl) ⟨1460993, by rfl⟩ : syracuseStep 1947991 = 2921987) B2921987
theorem B2160985 : Blo 1279958 2160985 := bstep (se 2 (by rfl) ⟨810369, by rfl⟩ : syracuseStep 2160985 = 1620739) B1620739
theorem B2595187 : Blo 1279958 2595187 := bstep (se 1 (by rfl) ⟨1946390, by rfl⟩ : syracuseStep 2595187 = 3892781) B3892781
theorem B2881907 : Blo 1279958 2881907 := bstep (se 1 (by rfl) ⟨2161430, by rfl⟩ : syracuseStep 2881907 = 4322861) B4322861
theorem B1440139 : Blo 1279958 1440139 := bstep (se 1 (by rfl) ⟨1080104, by rfl⟩ : syracuseStep 1440139 = 2160209) B2160209
theorem B2464139 : Blo 1279958 2464139 := bstep (se 1 (by rfl) ⟨1848104, by rfl⟩ : syracuseStep 2464139 = 3696209) B3696209
theorem B2881943 : Blo 1279958 2881943 := bstep (se 1 (by rfl) ⟨2161457, by rfl⟩ : syracuseStep 2881943 = 4322915) B4322915
theorem B2308505 : Blo 1279958 2308505 := bstep (se 2 (by rfl) ⟨865689, by rfl⟩ : syracuseStep 2308505 = 1731379) B1731379
theorem B6568409 : Blo 1279958 6568409 := bstep (se 2 (by rfl) ⟨2463153, by rfl⟩ : syracuseStep 6568409 = 4926307) B4926307
theorem B1440247 : Blo 1279958 1440247 := bstep (se 1 (by rfl) ⟨1080185, by rfl⟩ : syracuseStep 1440247 = 2160371) B2160371
theorem B2882123 : Blo 1279958 2882123 := bstep (se 1 (by rfl) ⟨2161592, by rfl⟩ : syracuseStep 2882123 = 4323185) B4323185
theorem B2882177 : Blo 1279958 2882177 := bstep (se 2 (by rfl) ⟨1080816, by rfl⟩ : syracuseStep 2882177 = 2161633) B2161633
theorem B9730691 : Blo 1279958 9730691 := bstep (se 1 (by rfl) ⟨7298018, by rfl⟩ : syracuseStep 9730691 = 14596037) B14596037
theorem B1440427 : Blo 1279958 1440427 := bstep (se 1 (by rfl) ⟨1080320, by rfl⟩ : syracuseStep 1440427 = 2160641) B2160641
theorem B3242713 : Blo 1279958 3242713 := bstep (se 2 (by rfl) ⟨1216017, by rfl⟩ : syracuseStep 3242713 = 2432035) B2432035
theorem B1440535 : Blo 1279958 1440535 := bstep (se 1 (by rfl) ⟨1080401, by rfl⟩ : syracuseStep 1440535 = 2160803) B2160803
theorem B2882393 : Blo 1279958 2882393 := bstep (se 2 (by rfl) ⟨1080897, by rfl⟩ : syracuseStep 2882393 = 2161795) B2161795
theorem B2431883 : Blo 1279958 2431883 := bstep (se 1 (by rfl) ⟨1823912, by rfl⟩ : syracuseStep 2431883 = 3647825) B3647825
theorem B2161559 : Blo 1279958 2161559 := bstep (se 1 (by rfl) ⟨1621169, by rfl⟩ : syracuseStep 2161559 = 3242339) B3242339
theorem B2882483 : Blo 1279958 2882483 := bstep (se 1 (by rfl) ⟨2161862, by rfl⟩ : syracuseStep 2882483 = 4323725) B4323725
theorem B2735041 : Blo 1279958 2735041 := bstep (se 2 (by rfl) ⟨1025640, by rfl⟩ : syracuseStep 2735041 = 2051281) B2051281
theorem B2431937 : Blo 1279958 2431937 := bstep (se 2 (by rfl) ⟨911976, by rfl⟩ : syracuseStep 2431937 = 1823953) B1823953
theorem B1440715 : Blo 1279958 1440715 := bstep (se 1 (by rfl) ⟨1080536, by rfl⟩ : syracuseStep 1440715 = 2161073) B2161073
theorem B2079703 : Blo 1279958 2079703 := bstep (se 1 (by rfl) ⟨1559777, by rfl⟩ : syracuseStep 2079703 = 3119555) B3119555
theorem B2882519 : Blo 1279958 2882519 := bstep (se 1 (by rfl) ⟨2161889, by rfl⟩ : syracuseStep 2882519 = 4323779) B4323779
theorem B2161687 : Blo 1279958 2161687 := bstep (se 1 (by rfl) ⟨1621265, by rfl⟩ : syracuseStep 2161687 = 3242531) B3242531
theorem B9722915 : Blo 1279958 9722915 := bstep (se 1 (by rfl) ⟨7292186, by rfl⟩ : syracuseStep 9722915 = 14584373) B14584373
theorem B1440823 : Blo 1279958 1440823 := bstep (se 1 (by rfl) ⟨1080617, by rfl⟩ : syracuseStep 1440823 = 2161235) B2161235
theorem B4324427 : Blo 1279958 4324427 := bstep (se 1 (by rfl) ⟨3243320, by rfl⟩ : syracuseStep 4324427 = 6486641) B6486641
theorem B2882699 : Blo 1279958 2882699 := bstep (se 1 (by rfl) ⟨2162024, by rfl⟩ : syracuseStep 2882699 = 4324049) B4324049
theorem B2882753 : Blo 1279958 2882753 := bstep (se 2 (by rfl) ⟨1081032, by rfl⟩ : syracuseStep 2882753 = 2162065) B2162065
theorem B1441003 : Blo 1279958 1441003 := bstep (se 1 (by rfl) ⟨1080752, by rfl⟩ : syracuseStep 1441003 = 2161505) B2161505
theorem B2735383 : Blo 1279958 2735383 := bstep (se 1 (by rfl) ⟨2051537, by rfl⟩ : syracuseStep 2735383 = 4103075) B4103075
theorem B1367371 : Blo 1279958 1367371 := bstep (se 1 (by rfl) ⟨1025528, by rfl⟩ : syracuseStep 1367371 = 2051057) B2051057
theorem B1441111 : Blo 1279958 1441111 := bstep (se 1 (by rfl) ⟨1080833, by rfl⟩ : syracuseStep 1441111 = 2161667) B2161667
theorem B4324697 : Blo 1279958 4324697 := bstep (se 2 (by rfl) ⟨1621761, by rfl⟩ : syracuseStep 4324697 = 3243523) B3243523
theorem B2596225 : Blo 1279958 2596225 := bstep (se 2 (by rfl) ⟨973584, by rfl⟩ : syracuseStep 2596225 = 1947169) B1947169
theorem B1621387 : Blo 1279958 1621387 := bstep (se 1 (by rfl) ⟨1216040, by rfl⟩ : syracuseStep 1621387 = 2432081) B2432081
theorem B7396759 : Blo 1279958 7396759 := bstep (se 1 (by rfl) ⟨5547569, by rfl⟩ : syracuseStep 7396759 = 11095139) B11095139
theorem B2882969 : Blo 1279958 2882969 := bstep (se 2 (by rfl) ⟨1081113, by rfl⟩ : syracuseStep 2882969 = 2162227) B2162227
theorem B4865453 : Blo 1279958 4865453 := bstep (se 3 (by rfl) ⟨912272, by rfl⟩ : syracuseStep 4865453 = 1824545) B1824545
theorem B2883059 : Blo 1279958 2883059 := bstep (se 1 (by rfl) ⟨2162294, by rfl⟩ : syracuseStep 2883059 = 4324589) B4324589
theorem B1441291 : Blo 1279958 1441291 := bstep (se 1 (by rfl) ⟨1080968, by rfl⟩ : syracuseStep 1441291 = 2161937) B2161937
theorem B2883095 : Blo 1279958 2883095 := bstep (se 1 (by rfl) ⟨2162321, by rfl⟩ : syracuseStep 2883095 = 4324643) B4324643
theorem B4742707 : Blo 1279958 4742707 := bstep (se 1 (by rfl) ⟨3557030, by rfl⟩ : syracuseStep 4742707 = 7114061) B7114061
theorem B6929995 : Blo 1279958 6929995 := bstep (se 1 (by rfl) ⟨5197496, by rfl⟩ : syracuseStep 6929995 = 10394993) B10394993
theorem B1441399 : Blo 1279958 1441399 := bstep (se 1 (by rfl) ⟨1081049, by rfl⟩ : syracuseStep 1441399 = 2162099) B2162099
theorem B2162315 : Blo 1279958 2162315 := bstep (se 1 (by rfl) ⟨1621736, by rfl⟩ : syracuseStep 2162315 = 3243473) B3243473
theorem B7790231 : Blo 1279958 7790231 := bstep (se 1 (by rfl) ⟨5842673, by rfl⟩ : syracuseStep 7790231 = 11685347) B11685347
theorem B7397015 : Blo 1279958 7397015 := bstep (se 1 (by rfl) ⟨5547761, by rfl⟩ : syracuseStep 7397015 = 11095523) B11095523
theorem B2883275 : Blo 1279958 2883275 := bstep (se 1 (by rfl) ⟨2162456, by rfl⟩ : syracuseStep 2883275 = 4324913) B4324913
theorem B2883329 : Blo 1279958 2883329 := bstep (se 2 (by rfl) ⟨1081248, by rfl⟩ : syracuseStep 2883329 = 2162497) B2162497
theorem B2162443 : Blo 1279958 2162443 := bstep (se 1 (by rfl) ⟨1621832, by rfl⟩ : syracuseStep 2162443 = 3243665) B3243665
theorem B1441579 : Blo 1279958 1441579 := bstep (se 1 (by rfl) ⟨1081184, by rfl⟩ : syracuseStep 1441579 = 2162369) B2162369
theorem B3243827 : Blo 1279958 3243827 := bstep (se 1 (by rfl) ⟨2432870, by rfl⟩ : syracuseStep 3243827 = 4865741) B4865741
theorem B18472769 : Blo 1279958 18472769 := bstep (se 2 (by rfl) ⟨6927288, by rfl⟩ : syracuseStep 18472769 = 13854577) B13854577
theorem B2432855 : Blo 1279958 2432855 := bstep (se 1 (by rfl) ⟨1824641, by rfl⟩ : syracuseStep 2432855 = 3649283) B3649283
theorem B7298909 : Blo 1279958 7298909 := bstep (se 3 (by rfl) ⟨1368545, by rfl⟩ : syracuseStep 7298909 = 2737091) B2737091
theorem B1441687 : Blo 1279958 1441687 := bstep (se 1 (by rfl) ⟨1081265, by rfl⟩ : syracuseStep 1441687 = 2162531) B2162531
theorem B2162585 : Blo 1279958 2162585 := bstep (se 2 (by rfl) ⟨810969, by rfl⟩ : syracuseStep 2162585 = 1621939) B1621939
theorem B2883545 : Blo 1279958 2883545 := bstep (se 2 (by rfl) ⟨1081329, by rfl⟩ : syracuseStep 2883545 = 2162659) B2162659
theorem B2883599 : Blo 1279958 2883599 := bstep (se 1 (by rfl) ⟨2162699, by rfl⟩ : syracuseStep 2883599 = 4325399) B4325399
theorem B2883617 : Blo 1279958 2883617 := bstep (se 2 (by rfl) ⟨1081356, by rfl⟩ : syracuseStep 2883617 = 2162713) B2162713
theorem B2162747 : Blo 1279958 2162747 := bstep (se 1 (by rfl) ⟨1622060, by rfl⟩ : syracuseStep 2162747 = 3244121) B3244121
theorem B3244151 : Blo 1279958 3244151 := bstep (se 1 (by rfl) ⟨2433113, by rfl⟩ : syracuseStep 3244151 = 4866227) B4866227
theorem B3645593 : Blo 1279958 3645593 := bstep (se 2 (by rfl) ⟨1367097, by rfl⟩ : syracuseStep 3645593 = 2734195) B2734195
theorem B1622263 : Blo 1279958 1622263 := bstep (se 1 (by rfl) ⟨1216697, by rfl⟩ : syracuseStep 1622263 = 2433395) B2433395
theorem B6480161 : Blo 1279958 6480161 := bstep (se 2 (by rfl) ⟨2430060, by rfl⟩ : syracuseStep 6480161 = 4860121) B4860121
theorem B2883959 : Blo 1279958 2883959 := bstep (se 1 (by rfl) ⟨2162969, by rfl⟩ : syracuseStep 2883959 = 4325939) B4325939
theorem B4866439 : Blo 1279958 4866439 := bstep (se 1 (by rfl) ⟨3649829, by rfl⟩ : syracuseStep 4866439 = 7299659) B7299659
theorem B1442191 : Blo 1279958 1442191 := bstep (se 1 (by rfl) ⟨1081643, by rfl⟩ : syracuseStep 1442191 = 2163287) B2163287
theorem B2597321 : Blo 1279958 2597321 := bstep (se 2 (by rfl) ⟨973995, by rfl⟩ : syracuseStep 2597321 = 1947991) B1947991
theorem B2163145 : Blo 1279958 2163145 := bstep (se 2 (by rfl) ⟨811179, by rfl⟩ : syracuseStep 2163145 = 1622359) B1622359
theorem B6152669 : Blo 1279958 6152669 := bstep (se 3 (by rfl) ⟨1153625, by rfl⟩ : syracuseStep 6152669 = 2307251) B2307251
theorem B4104715 : Blo 1279958 4104715 := bstep (se 1 (by rfl) ⟨3078536, by rfl⟩ : syracuseStep 4104715 = 6157073) B6157073
theorem B10388011 : Blo 1279958 10388011 := bstep (se 1 (by rfl) ⟨7791008, by rfl⟩ : syracuseStep 10388011 = 15582017) B15582017
theorem B2884139 : Blo 1279958 2884139 := bstep (se 1 (by rfl) ⟨2163104, by rfl⟩ : syracuseStep 2884139 = 4326209) B4326209
theorem B1368635 : Blo 1279958 1368635 := bstep (se 1 (by rfl) ⟨1026476, by rfl⟩ : syracuseStep 1368635 = 2052953) B2052953
theorem B7299841 : Blo 1279958 7299841 := bstep (se 2 (by rfl) ⟨2737440, by rfl⟩ : syracuseStep 7299841 = 5474881) B5474881
theorem B2736929 : Blo 1279958 2736929 := bstep (se 2 (by rfl) ⟨1026348, by rfl⟩ : syracuseStep 2736929 = 2052697) B2052697
theorem B14033699 : Blo 1279958 14033699 := bstep (se 1 (by rfl) ⟨10525274, by rfl⟩ : syracuseStep 14033699 = 21050549) B21050549
theorem B6325127 : Blo 1279958 6325127 := bstep (se 1 (by rfl) ⟨4743845, by rfl⟩ : syracuseStep 6325127 = 9487691) B9487691
theorem B136872917 : Blo 1279958 136872917 := bstep (se 7 (by rfl) ⟨1603979, by rfl⟩ : syracuseStep 136872917 = 3207959) B3207959
theorem B6571037 : Blo 1279958 6571037 := bstep (se 3 (by rfl) ⟨1232069, by rfl⟩ : syracuseStep 6571037 = 2464139) B2464139
theorem B17515757 : Blo 1279958 17515757 := bstep (se 3 (by rfl) ⟨3284204, by rfl⟩ : syracuseStep 17515757 = 6568409) B6568409
theorem B6481133 : Blo 1279958 6481133 := bstep (se 3 (by rfl) ⟨1215212, by rfl⟩ : syracuseStep 6481133 = 2430425) B2430425
theorem B3646721 : Blo 1279958 3646721 := bstep (se 2 (by rfl) ⟨1367520, by rfl⟩ : syracuseStep 3646721 = 2735041) B2735041
theorem B7300367 : Blo 1279958 7300367 := bstep (se 1 (by rfl) ⟨5475275, by rfl⟩ : syracuseStep 7300367 = 10950551) B10950551
theorem B6489395 : Blo 1279958 6489395 := bstep (se 1 (by rfl) ⟨4867046, by rfl⟩ : syracuseStep 6489395 = 9734093) B9734093
theorem B5473651 : Blo 1279958 5473651 := bstep (se 1 (by rfl) ⟨4105238, by rfl⟩ : syracuseStep 5473651 = 8210477) B8210477
theorem B7292369 : Blo 1279958 7292369 := bstep (se 2 (by rfl) ⟨2734638, by rfl⟩ : syracuseStep 7292369 = 5469277) B5469277
theorem B12314177 : Blo 1279958 12314177 := bstep (se 2 (by rfl) ⟨4617816, by rfl⟩ : syracuseStep 12314177 = 9235633) B9235633
theorem B6489719 : Blo 1279958 6489719 := bstep (se 1 (by rfl) ⟨4867289, by rfl⟩ : syracuseStep 6489719 = 9734579) B9734579
theorem B3647177 : Blo 1279958 3647177 := bstep (se 2 (by rfl) ⟨1367691, by rfl⟩ : syracuseStep 3647177 = 2735383) B2735383
theorem B5473993 : Blo 1279958 5473993 := bstep (se 2 (by rfl) ⟨2052747, by rfl⟩ : syracuseStep 5473993 = 4105495) B4105495
theorem B7292825 : Blo 1279958 7292825 := bstep (se 2 (by rfl) ⟨2734809, by rfl⟩ : syracuseStep 7292825 = 5469619) B5469619
theorem B1280007 : Blo 1279958 1280007 := bstep (se 1 (by rfl) ⟨960005, by rfl⟩ : syracuseStep 1280007 = 1920011) B1920011
theorem B1280015 : Blo 1279958 1280015 := bstep (se 1 (by rfl) ⟨960011, by rfl⟩ : syracuseStep 1280015 = 1920023) B1920023
theorem B6481943 : Blo 1279958 6481943 := bstep (se 1 (by rfl) ⟨4861457, by rfl⟩ : syracuseStep 6481943 = 9722915) B9722915
theorem B1280059 : Blo 1279958 1280059 := bstep (se 1 (by rfl) ⟨960044, by rfl⟩ : syracuseStep 1280059 = 1920089) B1920089
theorem B1280135 : Blo 1279958 1280135 := bstep (se 1 (by rfl) ⟨960101, by rfl⟩ : syracuseStep 1280135 = 1920203) B1920203
theorem B1460359 : Blo 1279958 1460359 := bstep (se 1 (by rfl) ⟨1095269, by rfl⟩ : syracuseStep 1460359 = 2190539) B2190539
theorem B1280143 : Blo 1279958 1280143 := bstep (se 1 (by rfl) ⟨960107, by rfl⟩ : syracuseStep 1280143 = 1920215) B1920215
theorem B1280187 : Blo 1279958 1280187 := bstep (se 1 (by rfl) ⟨960140, by rfl⟩ : syracuseStep 1280187 = 1920281) B1920281
theorem B1280263 : Blo 1279958 1280263 := bstep (se 1 (by rfl) ⟨960197, by rfl⟩ : syracuseStep 1280263 = 1920395) B1920395
theorem B1280271 : Blo 1279958 1280271 := bstep (se 1 (by rfl) ⟨960203, by rfl⟩ : syracuseStep 1280271 = 1920407) B1920407
theorem B1280315 : Blo 1279958 1280315 := bstep (se 1 (by rfl) ⟨960236, by rfl⟩ : syracuseStep 1280315 = 1920473) B1920473
theorem B1280391 : Blo 1279958 1280391 := bstep (se 1 (by rfl) ⟨960293, by rfl⟩ : syracuseStep 1280391 = 1920587) B1920587
theorem B1280399 : Blo 1279958 1280399 := bstep (se 1 (by rfl) ⟨960299, by rfl⟩ : syracuseStep 1280399 = 1920599) B1920599
theorem B1280443 : Blo 1279958 1280443 := bstep (se 1 (by rfl) ⟨960332, by rfl⟩ : syracuseStep 1280443 = 1920665) B1920665
theorem B6572497 : Blo 1279958 6572497 := bstep (se 2 (by rfl) ⟨2464686, by rfl⟩ : syracuseStep 6572497 = 4929373) B4929373
theorem B1280519 : Blo 1279958 1280519 := bstep (se 1 (by rfl) ⟨960389, by rfl⟩ : syracuseStep 1280519 = 1920779) B1920779
theorem B1280527 : Blo 1279958 1280527 := bstep (se 1 (by rfl) ⟨960395, by rfl⟩ : syracuseStep 1280527 = 1920791) B1920791
theorem B12315179 : Blo 1279958 12315179 := bstep (se 1 (by rfl) ⟨9236384, by rfl⟩ : syracuseStep 12315179 = 18472769) B18472769
theorem B1280571 : Blo 1279958 1280571 := bstep (se 1 (by rfl) ⟨960428, by rfl⟩ : syracuseStep 1280571 = 1920857) B1920857
theorem B9226871 : Blo 1279958 9226871 := bstep (se 1 (by rfl) ⟨6920153, by rfl⟩ : syracuseStep 9226871 = 13840307) B13840307
theorem B1280647 : Blo 1279958 1280647 := bstep (se 1 (by rfl) ⟨960485, by rfl⟩ : syracuseStep 1280647 = 1920971) B1920971
theorem B1280655 : Blo 1279958 1280655 := bstep (se 1 (by rfl) ⟨960491, by rfl⟩ : syracuseStep 1280655 = 1920983) B1920983
theorem B1280699 : Blo 1279958 1280699 := bstep (se 1 (by rfl) ⟨960524, by rfl⟩ : syracuseStep 1280699 = 1921049) B1921049
theorem B4319945 : Blo 1279958 4319945 := bstep (se 2 (by rfl) ⟨1619979, by rfl⟩ : syracuseStep 4319945 = 3239959) B3239959
theorem B5475053 : Blo 1279958 5475053 := bstep (se 3 (by rfl) ⟨1026572, by rfl⟩ : syracuseStep 5475053 = 2053145) B2053145
theorem B1280775 : Blo 1279958 1280775 := bstep (se 1 (by rfl) ⟨960581, by rfl⟩ : syracuseStep 1280775 = 1921163) B1921163
theorem B1280783 : Blo 1279958 1280783 := bstep (se 1 (by rfl) ⟨960587, by rfl⟩ : syracuseStep 1280783 = 1921175) B1921175
theorem B1461007 : Blo 1279958 1461007 := bstep (se 1 (by rfl) ⟨1095755, by rfl⟩ : syracuseStep 1461007 = 2191511) B2191511
theorem B1280827 : Blo 1279958 1280827 := bstep (se 1 (by rfl) ⟨960620, by rfl⟩ : syracuseStep 1280827 = 1921241) B1921241
theorem B5843771 : Blo 1279958 5843771 := bstep (se 1 (by rfl) ⟨4382828, by rfl⟩ : syracuseStep 5843771 = 8765657) B8765657
theorem B2919287 : Blo 1279958 2919287 := bstep (se 1 (by rfl) ⟨2189465, by rfl⟩ : syracuseStep 2919287 = 4378931) B4378931
theorem B1280903 : Blo 1279958 1280903 := bstep (se 1 (by rfl) ⟨960677, by rfl⟩ : syracuseStep 1280903 = 1921355) B1921355
theorem B1280911 : Blo 1279958 1280911 := bstep (se 1 (by rfl) ⟨960683, by rfl⟩ : syracuseStep 1280911 = 1921367) B1921367
theorem B1280955 : Blo 1279958 1280955 := bstep (se 1 (by rfl) ⟨960716, by rfl⟩ : syracuseStep 1280955 = 1921433) B1921433
theorem B1919945 : Blo 1279958 1919945 := bstep (se 2 (by rfl) ⟨719979, by rfl⟩ : syracuseStep 1919945 = 1439959) B1439959
theorem B4860881 : Blo 1279958 4860881 := bstep (se 2 (by rfl) ⟨1822830, by rfl⟩ : syracuseStep 4860881 = 3645661) B3645661
theorem B1281031 : Blo 1279958 1281031 := bstep (se 1 (by rfl) ⟨960773, by rfl⟩ : syracuseStep 1281031 = 1921547) B1921547
theorem B1281039 : Blo 1279958 1281039 := bstep (se 1 (by rfl) ⟨960779, by rfl⟩ : syracuseStep 1281039 = 1921559) B1921559
theorem B1920059 : Blo 1279958 1920059 := bstep (se 1 (by rfl) ⟨1440044, by rfl⟩ : syracuseStep 1920059 = 2880089) B2880089
theorem B1281083 : Blo 1279958 1281083 := bstep (se 1 (by rfl) ⟨960812, by rfl⟩ : syracuseStep 1281083 = 1921625) B1921625
theorem B1920119 : Blo 1279958 1920119 := bstep (se 1 (by rfl) ⟨1440089, by rfl⟩ : syracuseStep 1920119 = 2880179) B2880179
theorem B1281159 : Blo 1279958 1281159 := bstep (se 1 (by rfl) ⟨960869, by rfl⟩ : syracuseStep 1281159 = 1921739) B1921739
theorem B1920143 : Blo 1279958 1920143 := bstep (se 1 (by rfl) ⟨1440107, by rfl⟩ : syracuseStep 1920143 = 2880215) B2880215
theorem B1281167 : Blo 1279958 1281167 := bstep (se 1 (by rfl) ⟨960875, by rfl⟩ : syracuseStep 1281167 = 1921751) B1921751
theorem B3460249 : Blo 1279958 3460249 := bstep (se 2 (by rfl) ⟨1297593, by rfl⟩ : syracuseStep 3460249 = 2595187) B2595187
theorem B3894425 : Blo 1279958 3894425 := bstep (se 2 (by rfl) ⟨1460409, by rfl⟩ : syracuseStep 3894425 = 2920819) B2920819
theorem B1920185 : Blo 1279958 1920185 := bstep (se 2 (by rfl) ⟨720069, by rfl⟩ : syracuseStep 1920185 = 1440139) B1440139
theorem B1281211 : Blo 1279958 1281211 := bstep (se 1 (by rfl) ⟨960908, by rfl⟩ : syracuseStep 1281211 = 1921817) B1921817
theorem B1920263 : Blo 1279958 1920263 := bstep (se 1 (by rfl) ⟨1440197, by rfl⟩ : syracuseStep 1920263 = 2880395) B2880395
theorem B1281287 : Blo 1279958 1281287 := bstep (se 1 (by rfl) ⟨960965, by rfl⟩ : syracuseStep 1281287 = 1921931) B1921931
theorem B1281295 : Blo 1279958 1281295 := bstep (se 1 (by rfl) ⟨960971, by rfl⟩ : syracuseStep 1281295 = 1921943) B1921943
theorem B1920299 : Blo 1279958 1920299 := bstep (se 1 (by rfl) ⟨1440224, by rfl⟩ : syracuseStep 1920299 = 2880449) B2880449
theorem B1281339 : Blo 1279958 1281339 := bstep (se 1 (by rfl) ⟨961004, by rfl⟩ : syracuseStep 1281339 = 1922009) B1922009
theorem B3648827 : Blo 1279958 3648827 := bstep (se 1 (by rfl) ⟨2736620, by rfl⟩ : syracuseStep 3648827 = 5473241) B5473241
theorem B1920329 : Blo 1279958 1920329 := bstep (se 2 (by rfl) ⟨720123, by rfl⟩ : syracuseStep 1920329 = 1440247) B1440247
theorem B4320647 : Blo 1279958 4320647 := bstep (se 1 (by rfl) ⟨3240485, by rfl⟩ : syracuseStep 4320647 = 6480971) B6480971
theorem B1281415 : Blo 1279958 1281415 := bstep (se 1 (by rfl) ⟨961061, by rfl⟩ : syracuseStep 1281415 = 1922123) B1922123
theorem B1281423 : Blo 1279958 1281423 := bstep (se 1 (by rfl) ⟨961067, by rfl⟩ : syracuseStep 1281423 = 1922135) B1922135
theorem B1920443 : Blo 1279958 1920443 := bstep (se 1 (by rfl) ⟨1440332, by rfl⟩ : syracuseStep 1920443 = 2880665) B2880665
theorem B1281467 : Blo 1279958 1281467 := bstep (se 1 (by rfl) ⟨961100, by rfl⟩ : syracuseStep 1281467 = 1922201) B1922201
theorem B1920503 : Blo 1279958 1920503 := bstep (se 1 (by rfl) ⟨1440377, by rfl⟩ : syracuseStep 1920503 = 2880755) B2880755
theorem B1281543 : Blo 1279958 1281543 := bstep (se 1 (by rfl) ⟨961157, by rfl⟩ : syracuseStep 1281543 = 1922315) B1922315
theorem B1920527 : Blo 1279958 1920527 := bstep (se 1 (by rfl) ⟨1440395, by rfl⟩ : syracuseStep 1920527 = 2880791) B2880791
theorem B1281551 : Blo 1279958 1281551 := bstep (se 1 (by rfl) ⟨961163, by rfl⟩ : syracuseStep 1281551 = 1922327) B1922327
theorem B1920569 : Blo 1279958 1920569 := bstep (se 2 (by rfl) ⟨720213, by rfl⟩ : syracuseStep 1920569 = 1440427) B1440427
theorem B1281595 : Blo 1279958 1281595 := bstep (se 1 (by rfl) ⟨961196, by rfl⟩ : syracuseStep 1281595 = 1922393) B1922393
theorem B4615741 : Blo 1279958 4615741 := bstep (se 3 (by rfl) ⟨865451, by rfl⟩ : syracuseStep 4615741 = 1730903) B1730903
theorem B3698291 : Blo 1279958 3698291 := bstep (se 1 (by rfl) ⟨2773718, by rfl⟩ : syracuseStep 3698291 = 5547437) B5547437
theorem B1920647 : Blo 1279958 1920647 := bstep (se 1 (by rfl) ⟨1440485, by rfl⟩ : syracuseStep 1920647 = 2880971) B2880971
theorem B1281671 : Blo 1279958 1281671 := bstep (se 1 (by rfl) ⟨961253, by rfl⟩ : syracuseStep 1281671 = 1922507) B1922507
theorem B1281679 : Blo 1279958 1281679 := bstep (se 1 (by rfl) ⟨961259, by rfl⟩ : syracuseStep 1281679 = 1922519) B1922519
theorem B1920683 : Blo 1279958 1920683 := bstep (se 1 (by rfl) ⟨1440512, by rfl⟩ : syracuseStep 1920683 = 2881025) B2881025
theorem B20786867 : Blo 1279958 20786867 := bstep (se 1 (by rfl) ⟨15590150, by rfl⟩ : syracuseStep 20786867 = 31180301) B31180301
theorem B1281723 : Blo 1279958 1281723 := bstep (se 1 (by rfl) ⟨961292, by rfl⟩ : syracuseStep 1281723 = 1922585) B1922585
theorem B1920713 : Blo 1279958 1920713 := bstep (se 2 (by rfl) ⟨720267, by rfl⟩ : syracuseStep 1920713 = 1440535) B1440535
theorem B6156013 : Blo 1279958 6156013 := bstep (se 3 (by rfl) ⟨1154252, by rfl⟩ : syracuseStep 6156013 = 2308505) B2308505
theorem B4321025 : Blo 1279958 4321025 := bstep (se 2 (by rfl) ⟨1620384, by rfl⟩ : syracuseStep 4321025 = 3240769) B3240769
theorem B1281799 : Blo 1279958 1281799 := bstep (se 1 (by rfl) ⟨961349, by rfl⟩ : syracuseStep 1281799 = 1922699) B1922699
theorem B1281807 : Blo 1279958 1281807 := bstep (se 1 (by rfl) ⟨961355, by rfl⟩ : syracuseStep 1281807 = 1922711) B1922711
theorem B7499557 : Blo 1279958 7499557 := bstep (se 4 (by rfl) ⟨703083, by rfl⟩ : syracuseStep 7499557 = 1406167) B1406167
theorem B1920827 : Blo 1279958 1920827 := bstep (se 1 (by rfl) ⟨1440620, by rfl⟩ : syracuseStep 1920827 = 2881241) B2881241
theorem B1281851 : Blo 1279958 1281851 := bstep (se 1 (by rfl) ⟨961388, by rfl⟩ : syracuseStep 1281851 = 1922777) B1922777
theorem B1920887 : Blo 1279958 1920887 := bstep (se 1 (by rfl) ⟨1440665, by rfl⟩ : syracuseStep 1920887 = 2881331) B2881331
theorem B1281927 : Blo 1279958 1281927 := bstep (se 1 (by rfl) ⟨961445, by rfl⟩ : syracuseStep 1281927 = 1922891) B1922891
theorem B1920911 : Blo 1279958 1920911 := bstep (se 1 (by rfl) ⟨1440683, by rfl⟩ : syracuseStep 1920911 = 2881367) B2881367
theorem B1281935 : Blo 1279958 1281935 := bstep (se 1 (by rfl) ⟨961451, by rfl⟩ : syracuseStep 1281935 = 1922903) B1922903
theorem B1920953 : Blo 1279958 1920953 := bstep (se 2 (by rfl) ⟨720357, by rfl⟩ : syracuseStep 1920953 = 1440715) B1440715
theorem B3649465 : Blo 1279958 3649465 := bstep (se 2 (by rfl) ⟨1368549, by rfl⟩ : syracuseStep 3649465 = 2737099) B2737099
theorem B2772937 : Blo 1279958 2772937 := bstep (se 2 (by rfl) ⟨1039851, by rfl⟩ : syracuseStep 2772937 = 2079703) B2079703
theorem B8212427 : Blo 1279958 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B1921031 : Blo 1279958 1921031 := bstep (se 1 (by rfl) ⟨1440773, by rfl⟩ : syracuseStep 1921031 = 2881547) B2881547
theorem B4616203 : Blo 1279958 4616203 := bstep (se 1 (by rfl) ⟨3462152, by rfl⟩ : syracuseStep 4616203 = 6924305) B6924305
theorem B1921067 : Blo 1279958 1921067 := bstep (se 1 (by rfl) ⟨1440800, by rfl⟩ : syracuseStep 1921067 = 2881601) B2881601
theorem B1921097 : Blo 1279958 1921097 := bstep (se 2 (by rfl) ⟨720411, by rfl⟩ : syracuseStep 1921097 = 1440823) B1440823
theorem B3240071 : Blo 1279958 3240071 := bstep (se 1 (by rfl) ⟨2430053, by rfl⟩ : syracuseStep 3240071 = 4860107) B4860107
theorem B3240121 : Blo 1279958 3240121 := bstep (se 2 (by rfl) ⟨1215045, by rfl⟩ : syracuseStep 3240121 = 2430091) B2430091
theorem B1921211 : Blo 1279958 1921211 := bstep (se 1 (by rfl) ⟨1440908, by rfl⟩ : syracuseStep 1921211 = 2881817) B2881817
theorem B1921271 : Blo 1279958 1921271 := bstep (se 1 (by rfl) ⟨1440953, by rfl⟩ : syracuseStep 1921271 = 2881907) B2881907
theorem B1921295 : Blo 1279958 1921295 := bstep (se 1 (by rfl) ⟨1440971, by rfl⟩ : syracuseStep 1921295 = 2881943) B2881943
theorem B1921337 : Blo 1279958 1921337 := bstep (se 2 (by rfl) ⟨720501, by rfl⟩ : syracuseStep 1921337 = 1441003) B1441003
theorem B3649853 : Blo 1279958 3649853 := bstep (se 3 (by rfl) ⟨684347, by rfl⟩ : syracuseStep 3649853 = 1368695) B1368695
theorem B1921415 : Blo 1279958 1921415 := bstep (se 1 (by rfl) ⟨1441061, by rfl⟩ : syracuseStep 1921415 = 2882123) B2882123
theorem B1921451 : Blo 1279958 1921451 := bstep (se 1 (by rfl) ⟨1441088, by rfl⟩ : syracuseStep 1921451 = 2882177) B2882177
theorem B1823161 : Blo 1279958 1823161 := bstep (se 2 (by rfl) ⟨683685, by rfl⟩ : syracuseStep 1823161 = 1367371) B1367371
theorem B2879945 : Blo 1279958 2879945 := bstep (se 2 (by rfl) ⟨1079979, by rfl⟩ : syracuseStep 2879945 = 2159959) B2159959
theorem B1921481 : Blo 1279958 1921481 := bstep (se 2 (by rfl) ⟨720555, by rfl⟩ : syracuseStep 1921481 = 1441111) B1441111
theorem B3461633 : Blo 1279958 3461633 := bstep (se 2 (by rfl) ⟨1298112, by rfl⟩ : syracuseStep 3461633 = 2596225) B2596225
theorem B4321835 : Blo 1279958 4321835 := bstep (se 1 (by rfl) ⟨3241376, by rfl⟩ : syracuseStep 4321835 = 6482753) B6482753
theorem B1921595 : Blo 1279958 1921595 := bstep (se 1 (by rfl) ⟨1441196, by rfl⟩ : syracuseStep 1921595 = 2882393) B2882393
theorem B168489557 : Blo 1279958 168489557 := bstep (se 8 (by rfl) ⟨987243, by rfl⟩ : syracuseStep 168489557 = 1974487) B1974487
theorem B4862551 : Blo 1279958 4862551 := bstep (se 1 (by rfl) ⟨3646913, by rfl⟩ : syracuseStep 4862551 = 7293827) B7293827
theorem B1921655 : Blo 1279958 1921655 := bstep (se 1 (by rfl) ⟨1441241, by rfl⟩ : syracuseStep 1921655 = 2882483) B2882483
theorem B1921679 : Blo 1279958 1921679 := bstep (se 1 (by rfl) ⟨1441259, by rfl⟩ : syracuseStep 1921679 = 2882519) B2882519
theorem B1921721 : Blo 1279958 1921721 := bstep (se 2 (by rfl) ⟨720645, by rfl⟩ : syracuseStep 1921721 = 1441291) B1441291
theorem B29561537 : Blo 1279958 29561537 := bstep (se 2 (by rfl) ⟨11085576, by rfl⟩ : syracuseStep 29561537 = 22171153) B22171153
theorem B1921799 : Blo 1279958 1921799 := bstep (se 1 (by rfl) ⟨1441349, by rfl⟩ : syracuseStep 1921799 = 2882699) B2882699
theorem B3240719 : Blo 1279958 3240719 := bstep (se 1 (by rfl) ⟨2430539, by rfl⟩ : syracuseStep 3240719 = 4861079) B4861079
theorem B6927119 : Blo 1279958 6927119 := bstep (se 1 (by rfl) ⟨5195339, by rfl⟩ : syracuseStep 6927119 = 10390679) B10390679
theorem B1921835 : Blo 1279958 1921835 := bstep (se 1 (by rfl) ⟨1441376, by rfl⟩ : syracuseStep 1921835 = 2882753) B2882753
theorem B1921865 : Blo 1279958 1921865 := bstep (se 2 (by rfl) ⟨720699, by rfl⟩ : syracuseStep 1921865 = 1441399) B1441399
theorem B4862855 : Blo 1279958 4862855 := bstep (se 1 (by rfl) ⟨3647141, by rfl⟩ : syracuseStep 4862855 = 7294283) B7294283
theorem B1921979 : Blo 1279958 1921979 := bstep (se 1 (by rfl) ⟨1441484, by rfl⟩ : syracuseStep 1921979 = 2882969) B2882969
theorem B1922039 : Blo 1279958 1922039 := bstep (se 1 (by rfl) ⟨1441529, by rfl⟩ : syracuseStep 1922039 = 2883059) B2883059
theorem B1922063 : Blo 1279958 1922063 := bstep (se 1 (by rfl) ⟨1441547, by rfl⟩ : syracuseStep 1922063 = 2883095) B2883095
theorem B6485021 : Blo 1279958 6485021 := bstep (se 3 (by rfl) ⟨1215941, by rfl⟩ : syracuseStep 6485021 = 2431883) B2431883
theorem B1922105 : Blo 1279958 1922105 := bstep (se 2 (by rfl) ⟨720789, by rfl⟩ : syracuseStep 1922105 = 1441579) B1441579
theorem B1946683 : Blo 1279958 1946683 := bstep (se 1 (by rfl) ⟨1460012, by rfl⟩ : syracuseStep 1946683 = 2920025) B2920025
theorem B4863037 : Blo 1279958 4863037 := bstep (se 3 (by rfl) ⟨911819, by rfl⟩ : syracuseStep 4863037 = 1823639) B1823639
theorem B2880647 : Blo 1279958 2880647 := bstep (se 1 (by rfl) ⟨2160485, by rfl⟩ : syracuseStep 2880647 = 4320971) B4320971
theorem B1922183 : Blo 1279958 1922183 := bstep (se 1 (by rfl) ⟨1441637, by rfl⟩ : syracuseStep 1922183 = 2883275) B2883275
theorem B1922219 : Blo 1279958 1922219 := bstep (se 1 (by rfl) ⟨1441664, by rfl⟩ : syracuseStep 1922219 = 2883329) B2883329
theorem B2430137 : Blo 1279958 2430137 := bstep (se 2 (by rfl) ⟨911301, by rfl⟩ : syracuseStep 2430137 = 1822603) B1822603
theorem B8000705 : Blo 1279958 8000705 := bstep (se 2 (by rfl) ⟨3000264, by rfl⟩ : syracuseStep 8000705 = 6000529) B6000529
theorem B1922249 : Blo 1279958 1922249 := bstep (se 2 (by rfl) ⟨720843, by rfl⟩ : syracuseStep 1922249 = 1441687) B1441687
theorem B2880827 : Blo 1279958 2880827 := bstep (se 1 (by rfl) ⟨2160620, by rfl⟩ : syracuseStep 2880827 = 4321241) B4321241
theorem B1922363 : Blo 1279958 1922363 := bstep (se 1 (by rfl) ⟨1441772, by rfl⟩ : syracuseStep 1922363 = 2883545) B2883545
theorem B4617587 : Blo 1279958 4617587 := bstep (se 1 (by rfl) ⟨3463190, by rfl⟩ : syracuseStep 4617587 = 6926381) B6926381
theorem B1922423 : Blo 1279958 1922423 := bstep (se 1 (by rfl) ⟨1441817, by rfl⟩ : syracuseStep 1922423 = 2883635) B2883635
theorem B13849991 : Blo 1279958 13849991 := bstep (se 1 (by rfl) ⟨10387493, by rfl⟩ : syracuseStep 13849991 = 20774987) B20774987
theorem B1922447 : Blo 1279958 1922447 := bstep (se 1 (by rfl) ⟨1441835, by rfl⟩ : syracuseStep 1922447 = 2883671) B2883671
theorem B6927763 : Blo 1279958 6927763 := bstep (se 1 (by rfl) ⟨5195822, by rfl⟩ : syracuseStep 6927763 = 10391645) B10391645
theorem B2880953 : Blo 1279958 2880953 := bstep (se 2 (by rfl) ⟨1080357, by rfl⟩ : syracuseStep 2880953 = 2160715) B2160715
theorem B31167929 : Blo 1279958 31167929 := bstep (se 2 (by rfl) ⟨11687973, by rfl⟩ : syracuseStep 31167929 = 23375947) B23375947
theorem B1922489 : Blo 1279958 1922489 := bstep (se 2 (by rfl) ⟨720933, by rfl⟩ : syracuseStep 1922489 = 1441867) B1441867
theorem B3241417 : Blo 1279958 3241417 := bstep (se 2 (by rfl) ⟨1215531, by rfl⟩ : syracuseStep 3241417 = 2431063) B2431063
theorem B6485507 : Blo 1279958 6485507 := bstep (se 1 (by rfl) ⟨4864130, by rfl⟩ : syracuseStep 6485507 = 9728261) B9728261
theorem B1922567 : Blo 1279958 1922567 := bstep (se 1 (by rfl) ⟨1441925, by rfl⟩ : syracuseStep 1922567 = 2883851) B2883851
theorem B2430479 : Blo 1279958 2430479 := bstep (se 1 (by rfl) ⟨1822859, by rfl⟩ : syracuseStep 2430479 = 3645719) B3645719
theorem B10950173 : Blo 1279958 10950173 := bstep (se 3 (by rfl) ⟨2053157, by rfl⟩ : syracuseStep 10950173 = 4106315) B4106315
theorem B1922603 : Blo 1279958 1922603 := bstep (se 1 (by rfl) ⟨1441952, by rfl⟩ : syracuseStep 1922603 = 2883905) B2883905
theorem B1922633 : Blo 1279958 1922633 := bstep (se 2 (by rfl) ⟨720987, by rfl⟩ : syracuseStep 1922633 = 1441975) B1441975
theorem B3241559 : Blo 1279958 3241559 := bstep (se 1 (by rfl) ⟨2431169, by rfl⟩ : syracuseStep 3241559 = 4862339) B4862339
theorem B2160263 : Blo 1279958 2160263 := bstep (se 1 (by rfl) ⟨1620197, by rfl⟩ : syracuseStep 2160263 = 3240395) B3240395
theorem B1824391 : Blo 1279958 1824391 := bstep (se 1 (by rfl) ⟨1368293, by rfl⟩ : syracuseStep 1824391 = 2736587) B2736587
theorem B1922747 : Blo 1279958 1922747 := bstep (se 1 (by rfl) ⟨1442060, by rfl⟩ : syracuseStep 1922747 = 2884121) B2884121
theorem B6928109 : Blo 1279958 6928109 := bstep (se 3 (by rfl) ⟨1299020, by rfl⟩ : syracuseStep 6928109 = 2598041) B2598041
theorem B1922807 : Blo 1279958 1922807 := bstep (se 1 (by rfl) ⟨1442105, by rfl⟩ : syracuseStep 1922807 = 2884211) B2884211
theorem B2881295 : Blo 1279958 2881295 := bstep (se 1 (by rfl) ⟨2160971, by rfl⟩ : syracuseStep 2881295 = 4321943) B4321943
theorem B1922831 : Blo 1279958 1922831 := bstep (se 1 (by rfl) ⟨1442123, by rfl⟩ : syracuseStep 1922831 = 2884247) B2884247
theorem B2881313 : Blo 1279958 2881313 := bstep (se 2 (by rfl) ⟨1080492, by rfl⟩ : syracuseStep 2881313 = 2160985) B2160985
theorem B1922873 : Blo 1279958 1922873 := bstep (se 2 (by rfl) ⟨721077, by rfl⟩ : syracuseStep 1922873 = 1442155) B1442155
theorem B4101947 : Blo 1279958 4101947 := bstep (se 1 (by rfl) ⟨3076460, by rfl⟩ : syracuseStep 4101947 = 6152921) B6152921
theorem B4323131 : Blo 1279958 4323131 := bstep (se 1 (by rfl) ⟨3242348, by rfl⟩ : syracuseStep 4323131 = 6484697) B6484697
theorem B1644535 : Blo 1279958 1644535 := bstep (se 1 (by rfl) ⟨1233401, by rfl⟩ : syracuseStep 1644535 = 2466803) B2466803
theorem B9721943 : Blo 1279958 9721943 := bstep (se 1 (by rfl) ⟨7291457, by rfl⟩ : syracuseStep 9721943 = 14582915) B14582915
theorem B2881655 : Blo 1279958 2881655 := bstep (se 1 (by rfl) ⟨2161241, by rfl⟩ : syracuseStep 2881655 = 4322483) B4322483
theorem B1317007 : Blo 1279958 1317007 := bstep (se 1 (by rfl) ⟨987755, by rfl⟩ : syracuseStep 1317007 = 1975511) B1975511
theorem B2160911 : Blo 1279958 2160911 := bstep (se 1 (by rfl) ⟨1620683, by rfl⟩ : syracuseStep 2160911 = 3241367) B3241367
theorem B4323617 : Blo 1279958 4323617 := bstep (se 2 (by rfl) ⟨1621356, by rfl⟩ : syracuseStep 4323617 = 3242713) B3242713
theorem B2595115 : Blo 1279958 2595115 := bstep (se 1 (by rfl) ⟨1946336, by rfl⟩ : syracuseStep 2595115 = 3892673) B3892673
theorem B2881835 : Blo 1279958 2881835 := bstep (se 1 (by rfl) ⟨2161376, by rfl⟩ : syracuseStep 2881835 = 4322753) B4322753
theorem B1947947 : Blo 1279958 1947947 := bstep (se 1 (by rfl) ⟨1460960, by rfl⟩ : syracuseStep 1947947 = 2921921) B2921921
theorem B2431291 : Blo 1279958 2431291 := bstep (se 1 (by rfl) ⟨1823468, by rfl⟩ : syracuseStep 2431291 = 3646937) B3646937
theorem B1825097 : Blo 1279958 1825097 := bstep (se 2 (by rfl) ⟨684411, by rfl⟩ : syracuseStep 1825097 = 1368823) B1368823
theorem B2431367 : Blo 1279958 2431367 := bstep (se 1 (by rfl) ⟨1823525, by rfl⟩ : syracuseStep 2431367 = 3647051) B3647051
theorem B1825211 : Blo 1279958 1825211 := bstep (se 1 (by rfl) ⟨1368908, by rfl⟩ : syracuseStep 1825211 = 2737817) B2737817
theorem B1440391 : Blo 1279958 1440391 := bstep (se 1 (by rfl) ⟨1080293, by rfl⟩ : syracuseStep 1440391 = 2160587) B2160587
theorem B2882195 : Blo 1279958 2882195 := bstep (se 1 (by rfl) ⟨2161646, by rfl⟩ : syracuseStep 2882195 = 4323293) B4323293
theorem B2734793 : Blo 1279958 2734793 := bstep (se 2 (by rfl) ⟨1025547, by rfl⟩ : syracuseStep 2734793 = 2051095) B2051095
theorem B2882249 : Blo 1279958 2882249 := bstep (se 2 (by rfl) ⟨1080843, by rfl⟩ : syracuseStep 2882249 = 2161687) B2161687
theorem B4864769 : Blo 1279958 4864769 := bstep (se 2 (by rfl) ⟨1824288, by rfl⟩ : syracuseStep 4864769 = 3648577) B3648577
theorem B3119887 : Blo 1279958 3119887 := bstep (se 1 (by rfl) ⟨2339915, by rfl⟩ : syracuseStep 3119887 = 4679831) B4679831
theorem B2431777 : Blo 1279958 2431777 := bstep (se 2 (by rfl) ⟨911916, by rfl⟩ : syracuseStep 2431777 = 1823833) B1823833
theorem B2161451 : Blo 1279958 2161451 := bstep (se 1 (by rfl) ⟨1621088, by rfl⟩ : syracuseStep 2161451 = 3242177) B3242177
theorem B1440571 : Blo 1279958 1440571 := bstep (se 1 (by rfl) ⟨1080428, by rfl⟩ : syracuseStep 1440571 = 2160857) B2160857
theorem B14588747 : Blo 1279958 14588747 := bstep (se 1 (by rfl) ⟨10941560, by rfl⟩ : syracuseStep 14588747 = 21883121) B21883121
theorem B4324211 : Blo 1279958 4324211 := bstep (se 1 (by rfl) ⟨3243158, by rfl⟩ : syracuseStep 4324211 = 6486317) B6486317
theorem B19725373 : Blo 1279958 19725373 := bstep (se 3 (by rfl) ⟨3698507, by rfl⟩ : syracuseStep 19725373 = 7397015) B7397015
theorem B6487127 : Blo 1279958 6487127 := bstep (se 1 (by rfl) ⟨4865345, by rfl⟩ : syracuseStep 6487127 = 9730691) B9730691
theorem B2432119 : Blo 1279958 2432119 := bstep (se 1 (by rfl) ⟨1824089, by rfl⟩ : syracuseStep 2432119 = 3648179) B3648179
theorem B2161849 : Blo 1279958 2161849 := bstep (se 2 (by rfl) ⟨810693, by rfl⟩ : syracuseStep 2161849 = 1621387) B1621387
theorem B9862345 : Blo 1279958 9862345 := bstep (se 2 (by rfl) ⟨3698379, by rfl⟩ : syracuseStep 9862345 = 7396759) B7396759
theorem B6151439 : Blo 1279958 6151439 := bstep (se 1 (by rfl) ⟨4613579, by rfl⟩ : syracuseStep 6151439 = 9227159) B9227159
theorem B1441039 : Blo 1279958 1441039 := bstep (se 1 (by rfl) ⟨1080779, by rfl⟩ : syracuseStep 1441039 = 2161559) B2161559
theorem B1621291 : Blo 1279958 1621291 := bstep (se 1 (by rfl) ⟨1215968, by rfl⟩ : syracuseStep 1621291 = 2431937) B2431937
theorem B2882951 : Blo 1279958 2882951 := bstep (se 1 (by rfl) ⟨2162213, by rfl⟩ : syracuseStep 2882951 = 4324427) B4324427
theorem B6323609 : Blo 1279958 6323609 := bstep (se 2 (by rfl) ⟨2371353, by rfl⟩ : syracuseStep 6323609 = 4742707) B4742707
theorem B2735545 : Blo 1279958 2735545 := bstep (se 2 (by rfl) ⟨1025829, by rfl⟩ : syracuseStep 2735545 = 2051659) B2051659
theorem B9239993 : Blo 1279958 9239993 := bstep (se 2 (by rfl) ⟨3464997, by rfl⟩ : syracuseStep 9239993 = 6929995) B6929995
theorem B15572483 : Blo 1279958 15572483 := bstep (se 1 (by rfl) ⟨11679362, by rfl⟩ : syracuseStep 15572483 = 23358725) B23358725
theorem B36953603 : Blo 1279958 36953603 := bstep (se 1 (by rfl) ⟨27715202, by rfl⟩ : syracuseStep 36953603 = 55430405) B55430405
theorem B2883131 : Blo 1279958 2883131 := bstep (se 1 (by rfl) ⟨2162348, by rfl⟩ : syracuseStep 2883131 = 4324697) B4324697
theorem B6487613 : Blo 1279958 6487613 := bstep (se 3 (by rfl) ⟨1216427, by rfl⟩ : syracuseStep 6487613 = 2432855) B2432855
theorem B6151747 : Blo 1279958 6151747 := bstep (se 1 (by rfl) ⟨4613810, by rfl⟩ : syracuseStep 6151747 = 9227621) B9227621
theorem B3243635 : Blo 1279958 3243635 := bstep (se 1 (by rfl) ⟨2432726, by rfl⟩ : syracuseStep 3243635 = 4865453) B4865453
theorem B16408241 : Blo 1279958 16408241 := bstep (se 2 (by rfl) ⟨6153090, by rfl⟩ : syracuseStep 16408241 = 12306181) B12306181
theorem B2883257 : Blo 1279958 2883257 := bstep (se 2 (by rfl) ⟨1081221, by rfl⟩ : syracuseStep 2883257 = 2162443) B2162443
theorem B1367815 : Blo 1279958 1367815 := bstep (se 1 (by rfl) ⟨1025861, by rfl⟩ : syracuseStep 1367815 = 2051723) B2051723
theorem B1441543 : Blo 1279958 1441543 := bstep (se 1 (by rfl) ⟨1081157, by rfl⟩ : syracuseStep 1441543 = 2162315) B2162315
theorem B5193487 : Blo 1279958 5193487 := bstep (se 1 (by rfl) ⟨3895115, by rfl⟩ : syracuseStep 5193487 = 7790231) B7790231
theorem B2162551 : Blo 1279958 2162551 := bstep (se 1 (by rfl) ⟨1621913, by rfl⟩ : syracuseStep 2162551 = 3243827) B3243827
theorem B3645319 : Blo 1279958 3645319 := bstep (se 1 (by rfl) ⟨2733989, by rfl⟩ : syracuseStep 3645319 = 5467979) B5467979
theorem B4865939 : Blo 1279958 4865939 := bstep (se 1 (by rfl) ⟨3649454, by rfl⟩ : syracuseStep 4865939 = 7298909) B7298909
theorem B1441723 : Blo 1279958 1441723 := bstep (se 1 (by rfl) ⟨1081292, by rfl⟩ : syracuseStep 1441723 = 2162585) B2162585
theorem B6479837 : Blo 1279958 6479837 := bstep (se 3 (by rfl) ⟨1214969, by rfl⟩ : syracuseStep 6479837 = 2429939) B2429939
theorem B1441831 : Blo 1279958 1441831 := bstep (se 1 (by rfl) ⟨1081373, by rfl⟩ : syracuseStep 1441831 = 2162747) B2162747
theorem B2162767 : Blo 1279958 2162767 := bstep (se 1 (by rfl) ⟨1622075, by rfl⟩ : syracuseStep 2162767 = 3244151) B3244151
theorem B2433235 : Blo 1279958 2433235 := bstep (se 1 (by rfl) ⟨1824926, by rfl⟩ : syracuseStep 2433235 = 3649853) B3649853
theorem B2163017 : Blo 1279958 2163017 := bstep (se 2 (by rfl) ⟨811131, by rfl⟩ : syracuseStep 2163017 = 1622263) B1622263
theorem B6488585 : Blo 1279958 6488585 := bstep (se 2 (by rfl) ⟨2433219, by rfl⟩ : syracuseStep 6488585 = 4866439) B4866439
theorem B9355799 : Blo 1279958 9355799 := bstep (se 1 (by rfl) ⟨7016849, by rfl⟩ : syracuseStep 9355799 = 14033699) B14033699
theorem B2884193 : Blo 1279958 2884193 := bstep (se 2 (by rfl) ⟨1081572, by rfl⟩ : syracuseStep 2884193 = 2163145) B2163145
theorem B5472953 : Blo 1279958 5472953 := bstep (se 2 (by rfl) ⟨2052357, by rfl⟩ : syracuseStep 5472953 = 4104715) B4104715
theorem B5194525 : Blo 1279958 5194525 := bstep (se 3 (by rfl) ⟨973973, by rfl⟩ : syracuseStep 5194525 = 1947947) B1947947
theorem B4866911 : Blo 1279958 4866911 := bstep (se 1 (by rfl) ⟨3650183, by rfl⟩ : syracuseStep 4866911 = 7300367) B7300367
theorem B4866925 : Blo 1279958 4866925 := bstep (se 3 (by rfl) ⟨912548, by rfl⟩ : syracuseStep 4866925 = 1825097) B1825097
theorem B4326263 : Blo 1279958 4326263 := bstep (se 1 (by rfl) ⟨3244697, by rfl⟩ : syracuseStep 4326263 = 6489395) B6489395
theorem B9233327 : Blo 1279958 9233327 := bstep (se 1 (by rfl) ⟨6924995, by rfl⟩ : syracuseStep 9233327 = 13849991) B13849991
theorem B9733121 : Blo 1279958 9733121 := bstep (se 2 (by rfl) ⟨3649920, by rfl⟩ : syracuseStep 9733121 = 7299841) B7299841
theorem B7300115 : Blo 1279958 7300115 := bstep (se 1 (by rfl) ⟨5475086, by rfl⟩ : syracuseStep 7300115 = 10950173) B10950173
theorem B8209451 : Blo 1279958 8209451 := bstep (se 1 (by rfl) ⟨6157088, by rfl⟩ : syracuseStep 8209451 = 12314177) B12314177
theorem B4326479 : Blo 1279958 4326479 := bstep (se 1 (by rfl) ⟨3244859, by rfl⟩ : syracuseStep 4326479 = 6489719) B6489719
theorem B4867229 : Blo 1279958 4867229 := bstep (se 3 (by rfl) ⟨912605, by rfl⟩ : syracuseStep 4867229 = 1825211) B1825211
theorem B6481295 : Blo 1279958 6481295 := bstep (se 1 (by rfl) ⟨4860971, by rfl⟩ : syracuseStep 6481295 = 9721943) B9721943
theorem B27698597 : Blo 1279958 27698597 := bstep (se 4 (by rfl) ⟨2596743, by rfl⟩ : syracuseStep 27698597 = 5193487) B5193487
theorem B7792037 : Blo 1279958 7792037 := bstep (se 4 (by rfl) ⟨730503, by rfl⟩ : syracuseStep 7792037 = 1461007) B1461007
theorem B4613665 : Blo 1279958 4613665 := bstep (se 2 (by rfl) ⟨1730124, by rfl⟩ : syracuseStep 4613665 = 3460249) B3460249
theorem B13149793 : Blo 1279958 13149793 := bstep (se 2 (by rfl) ⟨4931172, by rfl⟩ : syracuseStep 13149793 = 9862345) B9862345
theorem B8210119 : Blo 1279958 8210119 := bstep (se 1 (by rfl) ⟨6157589, by rfl⟩ : syracuseStep 8210119 = 12315179) B12315179
theorem B9725831 : Blo 1279958 9725831 := bstep (se 1 (by rfl) ⟨7294373, by rfl⟩ : syracuseStep 9725831 = 14588747) B14588747
theorem B3647393 : Blo 1279958 3647393 := bstep (se 2 (by rfl) ⟨1367772, by rfl⟩ : syracuseStep 3647393 = 2735545) B2735545
theorem B1279963 : Blo 1279958 1279963 := bstep (se 1 (by rfl) ⟨959972, by rfl⟩ : syracuseStep 1279963 = 1919945) B1919945
theorem B1280039 : Blo 1279958 1280039 := bstep (se 1 (by rfl) ⟨960029, by rfl⟩ : syracuseStep 1280039 = 1920059) B1920059
theorem B1280079 : Blo 1279958 1280079 := bstep (se 1 (by rfl) ⟨960059, by rfl⟩ : syracuseStep 1280079 = 1920119) B1920119
theorem B6154321 : Blo 1279958 6154321 := bstep (se 2 (by rfl) ⟨2307870, by rfl⟩ : syracuseStep 6154321 = 4615741) B4615741
theorem B8202329 : Blo 1279958 8202329 := bstep (se 2 (by rfl) ⟨3075873, by rfl⟩ : syracuseStep 8202329 = 6151747) B6151747
theorem B1280095 : Blo 1279958 1280095 := bstep (se 1 (by rfl) ⟨960071, by rfl⟩ : syracuseStep 1280095 = 1920143) B1920143
theorem B1280123 : Blo 1279958 1280123 := bstep (se 1 (by rfl) ⟨960092, by rfl⟩ : syracuseStep 1280123 = 1920185) B1920185
theorem B1280175 : Blo 1279958 1280175 := bstep (se 1 (by rfl) ⟨960131, by rfl⟩ : syracuseStep 1280175 = 1920263) B1920263
theorem B1280199 : Blo 1279958 1280199 := bstep (se 1 (by rfl) ⟨960149, by rfl⟩ : syracuseStep 1280199 = 1920299) B1920299
theorem B1280219 : Blo 1279958 1280219 := bstep (se 1 (by rfl) ⟨960164, by rfl⟩ : syracuseStep 1280219 = 1920329) B1920329
theorem B1280295 : Blo 1279958 1280295 := bstep (se 1 (by rfl) ⟨960221, by rfl⟩ : syracuseStep 1280295 = 1920443) B1920443
theorem B1280335 : Blo 1279958 1280335 := bstep (se 1 (by rfl) ⟨960251, by rfl⟩ : syracuseStep 1280335 = 1920503) B1920503
theorem B10381655 : Blo 1279958 10381655 := bstep (se 1 (by rfl) ⟨7786241, by rfl⟩ : syracuseStep 10381655 = 15572483) B15572483
theorem B24635735 : Blo 1279958 24635735 := bstep (se 1 (by rfl) ⟨18476801, by rfl⟩ : syracuseStep 24635735 = 36953603) B36953603
theorem B1280351 : Blo 1279958 1280351 := bstep (se 1 (by rfl) ⟨960263, by rfl⟩ : syracuseStep 1280351 = 1920527) B1920527
theorem B1280379 : Blo 1279958 1280379 := bstep (se 1 (by rfl) ⟨960284, by rfl⟩ : syracuseStep 1280379 = 1920569) B1920569
theorem B1280431 : Blo 1279958 1280431 := bstep (se 1 (by rfl) ⟨960323, by rfl⟩ : syracuseStep 1280431 = 1920647) B1920647
theorem B1280455 : Blo 1279958 1280455 := bstep (se 1 (by rfl) ⟨960341, by rfl⟩ : syracuseStep 1280455 = 1920683) B1920683
theorem B10938827 : Blo 1279958 10938827 := bstep (se 1 (by rfl) ⟨8204120, by rfl⟩ : syracuseStep 10938827 = 16408241) B16408241
theorem B1280475 : Blo 1279958 1280475 := bstep (se 1 (by rfl) ⟨960356, by rfl⟩ : syracuseStep 1280475 = 1920713) B1920713
theorem B4860425 : Blo 1279958 4860425 := bstep (se 2 (by rfl) ⟨1822659, by rfl⟩ : syracuseStep 4860425 = 3645319) B3645319
theorem B1280551 : Blo 1279958 1280551 := bstep (se 1 (by rfl) ⟨960413, by rfl⟩ : syracuseStep 1280551 = 1920827) B1920827
theorem B1280591 : Blo 1279958 1280591 := bstep (se 1 (by rfl) ⟨960443, by rfl⟩ : syracuseStep 1280591 = 1920887) B1920887
theorem B1280607 : Blo 1279958 1280607 := bstep (se 1 (by rfl) ⟨960455, by rfl⟩ : syracuseStep 1280607 = 1920911) B1920911
theorem B3697249 : Blo 1279958 3697249 := bstep (se 2 (by rfl) ⟨1386468, by rfl⟩ : syracuseStep 3697249 = 2772937) B2772937
theorem B1280635 : Blo 1279958 1280635 := bstep (se 1 (by rfl) ⟨960476, by rfl⟩ : syracuseStep 1280635 = 1920953) B1920953
theorem B5474951 : Blo 1279958 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B4319891 : Blo 1279958 4319891 := bstep (se 1 (by rfl) ⟨3239918, by rfl⟩ : syracuseStep 4319891 = 6479837) B6479837
theorem B1280687 : Blo 1279958 1280687 := bstep (se 1 (by rfl) ⟨960515, by rfl⟩ : syracuseStep 1280687 = 1921031) B1921031
theorem B6154937 : Blo 1279958 6154937 := bstep (se 2 (by rfl) ⟨2308101, by rfl⟩ : syracuseStep 6154937 = 4616203) B4616203
theorem B1280711 : Blo 1279958 1280711 := bstep (se 1 (by rfl) ⟨960533, by rfl⟩ : syracuseStep 1280711 = 1921067) B1921067
theorem B1280731 : Blo 1279958 1280731 := bstep (se 1 (by rfl) ⟨960548, by rfl⟩ : syracuseStep 1280731 = 1921097) B1921097
theorem B1280807 : Blo 1279958 1280807 := bstep (se 1 (by rfl) ⟨960605, by rfl⟩ : syracuseStep 1280807 = 1921211) B1921211
theorem B1280847 : Blo 1279958 1280847 := bstep (se 1 (by rfl) ⟨960635, by rfl⟩ : syracuseStep 1280847 = 1921271) B1921271
theorem B1280863 : Blo 1279958 1280863 := bstep (se 1 (by rfl) ⟨960647, by rfl⟩ : syracuseStep 1280863 = 1921295) B1921295
theorem B1756009 : Blo 1279958 1756009 := bstep (se 2 (by rfl) ⟨658503, by rfl⟩ : syracuseStep 1756009 = 1317007) B1317007
theorem B4320107 : Blo 1279958 4320107 := bstep (se 1 (by rfl) ⟨3240080, by rfl⟩ : syracuseStep 4320107 = 6480161) B6480161
theorem B1280891 : Blo 1279958 1280891 := bstep (se 1 (by rfl) ⟨960668, by rfl⟩ : syracuseStep 1280891 = 1921337) B1921337
theorem B4320161 : Blo 1279958 4320161 := bstep (se 2 (by rfl) ⟨1620060, by rfl⟩ : syracuseStep 4320161 = 3240121) B3240121
theorem B1280943 : Blo 1279958 1280943 := bstep (se 1 (by rfl) ⟨960707, by rfl⟩ : syracuseStep 1280943 = 1921415) B1921415
theorem B1280967 : Blo 1279958 1280967 := bstep (se 1 (by rfl) ⟨960725, by rfl⟩ : syracuseStep 1280967 = 1921451) B1921451
theorem B1919963 : Blo 1279958 1919963 := bstep (se 1 (by rfl) ⟨1439972, by rfl⟩ : syracuseStep 1919963 = 2879945) B2879945
theorem B1280987 : Blo 1279958 1280987 := bstep (se 1 (by rfl) ⟨960740, by rfl⟩ : syracuseStep 1280987 = 1921481) B1921481
theorem B1731547 : Blo 1279958 1731547 := bstep (se 1 (by rfl) ⟨1298660, by rfl⟩ : syracuseStep 1731547 = 2597321) B2597321
theorem B1281063 : Blo 1279958 1281063 := bstep (se 1 (by rfl) ⟨960797, by rfl⟩ : syracuseStep 1281063 = 1921595) B1921595
theorem B3460153 : Blo 1279958 3460153 := bstep (se 2 (by rfl) ⟨1297557, by rfl⟩ : syracuseStep 3460153 = 2595115) B2595115
theorem B1281103 : Blo 1279958 1281103 := bstep (se 1 (by rfl) ⟨960827, by rfl⟩ : syracuseStep 1281103 = 1921655) B1921655
theorem B1281119 : Blo 1279958 1281119 := bstep (se 1 (by rfl) ⟨960839, by rfl⟩ : syracuseStep 1281119 = 1921679) B1921679
theorem B1281147 : Blo 1279958 1281147 := bstep (se 1 (by rfl) ⟨960860, by rfl⟩ : syracuseStep 1281147 = 1921721) B1921721
theorem B21335213 : Blo 1279958 21335213 := bstep (se 3 (by rfl) ⟨4000352, by rfl⟩ : syracuseStep 21335213 = 8000705) B8000705
theorem B1281199 : Blo 1279958 1281199 := bstep (se 1 (by rfl) ⟨960899, by rfl⟩ : syracuseStep 1281199 = 1921799) B1921799
theorem B1281223 : Blo 1279958 1281223 := bstep (se 1 (by rfl) ⟨960917, by rfl⟩ : syracuseStep 1281223 = 1921835) B1921835
theorem B1281243 : Blo 1279958 1281243 := bstep (se 1 (by rfl) ⟨960932, by rfl⟩ : syracuseStep 1281243 = 1921865) B1921865
theorem B1281319 : Blo 1279958 1281319 := bstep (se 1 (by rfl) ⟨960989, by rfl⟩ : syracuseStep 1281319 = 1921979) B1921979
theorem B1281359 : Blo 1279958 1281359 := bstep (se 1 (by rfl) ⟨961019, by rfl⟩ : syracuseStep 1281359 = 1922039) B1922039
theorem B1281375 : Blo 1279958 1281375 := bstep (se 1 (by rfl) ⟨961031, by rfl⟩ : syracuseStep 1281375 = 1922063) B1922063
theorem B1281403 : Blo 1279958 1281403 := bstep (se 1 (by rfl) ⟨961052, by rfl⟩ : syracuseStep 1281403 = 1922105) B1922105
theorem B1920431 : Blo 1279958 1920431 := bstep (se 1 (by rfl) ⟨1440323, by rfl⟩ : syracuseStep 1920431 = 2880647) B2880647
theorem B1281455 : Blo 1279958 1281455 := bstep (se 1 (by rfl) ⟨961091, by rfl⟩ : syracuseStep 1281455 = 1922183) B1922183
theorem B1281479 : Blo 1279958 1281479 := bstep (se 1 (by rfl) ⟨961109, by rfl⟩ : syracuseStep 1281479 = 1922219) B1922219
theorem B6483401 : Blo 1279958 6483401 := bstep (se 2 (by rfl) ⟨2431275, by rfl⟩ : syracuseStep 6483401 = 4862551) B4862551
theorem B1281499 : Blo 1279958 1281499 := bstep (se 1 (by rfl) ⟨961124, by rfl⟩ : syracuseStep 1281499 = 1922249) B1922249
theorem B11677171 : Blo 1279958 11677171 := bstep (se 1 (by rfl) ⟨8757878, by rfl⟩ : syracuseStep 11677171 = 17515757) B17515757
theorem B4320755 : Blo 1279958 4320755 := bstep (se 1 (by rfl) ⟨3240566, by rfl⟩ : syracuseStep 4320755 = 6481133) B6481133
theorem B1920521 : Blo 1279958 1920521 := bstep (se 2 (by rfl) ⟨720195, by rfl⟩ : syracuseStep 1920521 = 1440391) B1440391
theorem B1920551 : Blo 1279958 1920551 := bstep (se 1 (by rfl) ⟨1440413, by rfl⟩ : syracuseStep 1920551 = 2880827) B2880827
theorem B1281575 : Blo 1279958 1281575 := bstep (se 1 (by rfl) ⟨961181, by rfl⟩ : syracuseStep 1281575 = 1922363) B1922363
theorem B1281615 : Blo 1279958 1281615 := bstep (se 1 (by rfl) ⟨961211, by rfl⟩ : syracuseStep 1281615 = 1922423) B1922423
theorem B1281631 : Blo 1279958 1281631 := bstep (se 1 (by rfl) ⟨961223, by rfl⟩ : syracuseStep 1281631 = 1922447) B1922447
theorem B1920635 : Blo 1279958 1920635 := bstep (se 1 (by rfl) ⟨1440476, by rfl⟩ : syracuseStep 1920635 = 2880953) B2880953
theorem B20778619 : Blo 1279958 20778619 := bstep (se 1 (by rfl) ⟨15583964, by rfl⟩ : syracuseStep 20778619 = 31167929) B31167929
theorem B1281659 : Blo 1279958 1281659 := bstep (se 1 (by rfl) ⟨961244, by rfl⟩ : syracuseStep 1281659 = 1922489) B1922489
theorem B4861579 : Blo 1279958 4861579 := bstep (se 1 (by rfl) ⟨3646184, by rfl⟩ : syracuseStep 4861579 = 7292369) B7292369
theorem B1281711 : Blo 1279958 1281711 := bstep (se 1 (by rfl) ⟨961283, by rfl⟩ : syracuseStep 1281711 = 1922567) B1922567
theorem B1281735 : Blo 1279958 1281735 := bstep (se 1 (by rfl) ⟨961301, by rfl⟩ : syracuseStep 1281735 = 1922603) B1922603
theorem B1281755 : Blo 1279958 1281755 := bstep (se 1 (by rfl) ⟨961316, by rfl⟩ : syracuseStep 1281755 = 1922633) B1922633
theorem B1920761 : Blo 1279958 1920761 := bstep (se 2 (by rfl) ⟨720285, by rfl⟩ : syracuseStep 1920761 = 1440571) B1440571
theorem B1281831 : Blo 1279958 1281831 := bstep (se 1 (by rfl) ⟨961373, by rfl⟩ : syracuseStep 1281831 = 1922747) B1922747
theorem B1281871 : Blo 1279958 1281871 := bstep (se 1 (by rfl) ⟨961403, by rfl⟩ : syracuseStep 1281871 = 1922807) B1922807
theorem B1920863 : Blo 1279958 1920863 := bstep (se 1 (by rfl) ⟨1440647, by rfl⟩ : syracuseStep 1920863 = 2881295) B2881295
theorem B1281887 : Blo 1279958 1281887 := bstep (se 1 (by rfl) ⟨961415, by rfl⟩ : syracuseStep 1281887 = 1922831) B1922831
theorem B1920875 : Blo 1279958 1920875 := bstep (se 1 (by rfl) ⟨1440656, by rfl⟩ : syracuseStep 1920875 = 2881313) B2881313
theorem B1281915 : Blo 1279958 1281915 := bstep (se 1 (by rfl) ⟨961436, by rfl⟩ : syracuseStep 1281915 = 1922873) B1922873
theorem B4861883 : Blo 1279958 4861883 := bstep (se 1 (by rfl) ⟨3646412, by rfl⟩ : syracuseStep 4861883 = 7292825) B7292825
theorem B4321295 : Blo 1279958 4321295 := bstep (se 1 (by rfl) ⟨3240971, by rfl⟩ : syracuseStep 4321295 = 6481943) B6481943
theorem B1921103 : Blo 1279958 1921103 := bstep (se 1 (by rfl) ⟨1440827, by rfl⟩ : syracuseStep 1921103 = 2881655) B2881655
theorem B6484049 : Blo 1279958 6484049 := bstep (se 2 (by rfl) ⟨2431518, by rfl⟩ : syracuseStep 6484049 = 4863037) B4863037
theorem B26300497 : Blo 1279958 26300497 := bstep (se 2 (by rfl) ⟨9862686, by rfl⟩ : syracuseStep 26300497 = 19725373) B19725373
theorem B3649693 : Blo 1279958 3649693 := bstep (se 3 (by rfl) ⟨684317, by rfl⟩ : syracuseStep 3649693 = 1368635) B1368635
theorem B1921223 : Blo 1279958 1921223 := bstep (se 1 (by rfl) ⟨1440917, by rfl⟩ : syracuseStep 1921223 = 2881835) B2881835
theorem B1921385 : Blo 1279958 1921385 := bstep (se 2 (by rfl) ⟨720519, by rfl⟩ : syracuseStep 1921385 = 1441039) B1441039
theorem B1921463 : Blo 1279958 1921463 := bstep (se 1 (by rfl) ⟨1441097, by rfl⟩ : syracuseStep 1921463 = 2882195) B2882195
theorem B2879963 : Blo 1279958 2879963 := bstep (se 1 (by rfl) ⟨2159972, by rfl⟩ : syracuseStep 2879963 = 4319945) B4319945
theorem B1823195 : Blo 1279958 1823195 := bstep (se 1 (by rfl) ⟨1367396, by rfl⟩ : syracuseStep 1823195 = 2734793) B2734793
theorem B1921499 : Blo 1279958 1921499 := bstep (se 1 (by rfl) ⟨1441124, by rfl⟩ : syracuseStep 1921499 = 2882249) B2882249
theorem B3650035 : Blo 1279958 3650035 := bstep (se 1 (by rfl) ⟨2737526, by rfl⟩ : syracuseStep 3650035 = 5475053) B5475053
theorem B9237017 : Blo 1279958 9237017 := bstep (se 2 (by rfl) ⟨3463881, by rfl⟩ : syracuseStep 9237017 = 6927763) B6927763
theorem B3895847 : Blo 1279958 3895847 := bstep (se 1 (by rfl) ⟨2921885, by rfl⟩ : syracuseStep 3895847 = 5843771) B5843771
theorem B1946191 : Blo 1279958 1946191 := bstep (se 1 (by rfl) ⟨1459643, by rfl⟩ : syracuseStep 1946191 = 2919287) B2919287
theorem B4321889 : Blo 1279958 4321889 := bstep (se 2 (by rfl) ⟨1620708, by rfl⟩ : syracuseStep 4321889 = 3241417) B3241417
theorem B3240587 : Blo 1279958 3240587 := bstep (se 1 (by rfl) ⟨2430440, by rfl⟩ : syracuseStep 3240587 = 4860881) B4860881
theorem B4100959 : Blo 1279958 4100959 := bstep (se 1 (by rfl) ⟨3075719, by rfl⟩ : syracuseStep 4100959 = 6151439) B6151439
theorem B2880431 : Blo 1279958 2880431 := bstep (se 1 (by rfl) ⟨2160323, by rfl⟩ : syracuseStep 2880431 = 4320647) B4320647
theorem B1921967 : Blo 1279958 1921967 := bstep (se 1 (by rfl) ⟨1441475, by rfl⟩ : syracuseStep 1921967 = 2882951) B2882951
theorem B4215739 : Blo 1279958 4215739 := bstep (se 1 (by rfl) ⟨3161804, by rfl⟩ : syracuseStep 4215739 = 6323609) B6323609
theorem B1823753 : Blo 1279958 1823753 := bstep (se 2 (by rfl) ⟨683907, by rfl⟩ : syracuseStep 1823753 = 1367815) B1367815
theorem B1922057 : Blo 1279958 1922057 := bstep (se 2 (by rfl) ⟨720771, by rfl⟩ : syracuseStep 1922057 = 1441543) B1441543
theorem B1922087 : Blo 1279958 1922087 := bstep (se 1 (by rfl) ⟨1441565, by rfl⟩ : syracuseStep 1922087 = 2883131) B2883131
theorem B9999409 : Blo 1279958 9999409 := bstep (se 2 (by rfl) ⟨3749778, by rfl⟩ : syracuseStep 9999409 = 7499557) B7499557
theorem B13857911 : Blo 1279958 13857911 := bstep (se 1 (by rfl) ⟨10393433, by rfl⟩ : syracuseStep 13857911 = 20786867) B20786867
theorem B1922171 : Blo 1279958 1922171 := bstep (se 1 (by rfl) ⟨1441628, by rfl⟩ : syracuseStep 1922171 = 2883257) B2883257
theorem B2880683 : Blo 1279958 2880683 := bstep (se 1 (by rfl) ⟨2160512, by rfl⟩ : syracuseStep 2880683 = 4321025) B4321025
theorem B1922297 : Blo 1279958 1922297 := bstep (se 2 (by rfl) ⟨720861, by rfl⟩ : syracuseStep 1922297 = 1441723) B1441723
theorem B8770853 : Blo 1279958 8770853 := bstep (se 4 (by rfl) ⟨822267, by rfl⟩ : syracuseStep 8770853 = 1644535) B1644535
theorem B1922399 : Blo 1279958 1922399 := bstep (se 1 (by rfl) ⟨1441799, by rfl⟩ : syracuseStep 1922399 = 2883599) B2883599
theorem B1922411 : Blo 1279958 1922411 := bstep (se 1 (by rfl) ⟨1441808, by rfl⟩ : syracuseStep 1922411 = 2883617) B2883617
theorem B2160047 : Blo 1279958 2160047 := bstep (se 1 (by rfl) ⟨1620035, by rfl⟩ : syracuseStep 2160047 = 3240071) B3240071
theorem B2430395 : Blo 1279958 2430395 := bstep (se 1 (by rfl) ⟨1822796, by rfl⟩ : syracuseStep 2430395 = 3645593) B3645593
theorem B1922639 : Blo 1279958 1922639 := bstep (se 1 (by rfl) ⟨1441979, by rfl⟩ : syracuseStep 1922639 = 2883959) B2883959
theorem B4101779 : Blo 1279958 4101779 := bstep (se 1 (by rfl) ⟨3076334, by rfl⟩ : syracuseStep 4101779 = 6152669) B6152669
theorem B2307755 : Blo 1279958 2307755 := bstep (se 1 (by rfl) ⟨1730816, by rfl⟩ : syracuseStep 2307755 = 3461633) B3461633
theorem B2881223 : Blo 1279958 2881223 := bstep (se 1 (by rfl) ⟨2160917, by rfl⟩ : syracuseStep 2881223 = 4321835) B4321835
theorem B1922759 : Blo 1279958 1922759 := bstep (se 1 (by rfl) ⟨1442069, by rfl⟩ : syracuseStep 1922759 = 2884139) B2884139
theorem B112326371 : Blo 1279958 112326371 := bstep (se 1 (by rfl) ⟨84244778, by rfl⟩ : syracuseStep 112326371 = 168489557) B168489557
theorem B3241721 : Blo 1279958 3241721 := bstep (se 2 (by rfl) ⟨1215645, by rfl⟩ : syracuseStep 3241721 = 2431291) B2431291
theorem B2160479 : Blo 1279958 2160479 := bstep (se 1 (by rfl) ⟨1620359, by rfl⟩ : syracuseStep 2160479 = 3240719) B3240719
theorem B4618079 : Blo 1279958 4618079 := bstep (se 1 (by rfl) ⟨3463559, by rfl⟩ : syracuseStep 4618079 = 6927119) B6927119
theorem B1922921 : Blo 1279958 1922921 := bstep (se 2 (by rfl) ⟨721095, by rfl⟩ : syracuseStep 1922921 = 1442191) B1442191
theorem B1824619 : Blo 1279958 1824619 := bstep (se 1 (by rfl) ⟨1368464, by rfl⟩ : syracuseStep 1824619 = 2736929) B2736929
theorem B2430881 : Blo 1279958 2430881 := bstep (se 2 (by rfl) ⟨911580, by rfl⟩ : syracuseStep 2430881 = 1823161) B1823161
theorem B3241903 : Blo 1279958 3241903 := bstep (se 1 (by rfl) ⟨2431427, by rfl⟩ : syracuseStep 3241903 = 4862855) B4862855
theorem B4216751 : Blo 1279958 4216751 := bstep (se 1 (by rfl) ⟨3162563, by rfl⟩ : syracuseStep 4216751 = 6325127) B6325127
theorem B8763329 : Blo 1279958 8763329 := bstep (se 2 (by rfl) ⟨3286248, by rfl⟩ : syracuseStep 8763329 = 6572497) B6572497
theorem B91248611 : Blo 1279958 91248611 := bstep (se 1 (by rfl) ⟨68436458, by rfl⟩ : syracuseStep 91248611 = 136872917) B136872917
theorem B4380691 : Blo 1279958 4380691 := bstep (se 1 (by rfl) ⟨3285518, by rfl⟩ : syracuseStep 4380691 = 6571037) B6571037
theorem B4323347 : Blo 1279958 4323347 := bstep (se 1 (by rfl) ⟨3242510, by rfl⟩ : syracuseStep 4323347 = 6485021) B6485021
theorem B7788581 : Blo 1279958 7788581 := bstep (se 4 (by rfl) ⟨730179, by rfl⟩ : syracuseStep 7788581 = 1460359) B1460359
theorem B13850681 : Blo 1279958 13850681 := bstep (se 2 (by rfl) ⟨5194005, by rfl⟩ : syracuseStep 13850681 = 10388011) B10388011
theorem B1620091 : Blo 1279958 1620091 := bstep (se 1 (by rfl) ⟨1215068, by rfl⟩ : syracuseStep 1620091 = 2430137) B2430137
theorem B9730205 : Blo 1279958 9730205 := bstep (se 3 (by rfl) ⟨1824413, by rfl⟩ : syracuseStep 9730205 = 3648827) B3648827
theorem B2431147 : Blo 1279958 2431147 := bstep (se 1 (by rfl) ⟨1823360, by rfl⟩ : syracuseStep 2431147 = 3646721) B3646721
theorem B3078391 : Blo 1279958 3078391 := bstep (se 1 (by rfl) ⟨2308793, by rfl⟩ : syracuseStep 3078391 = 4617587) B4617587
theorem B4323671 : Blo 1279958 4323671 := bstep (se 1 (by rfl) ⟨3242753, by rfl⟩ : syracuseStep 4323671 = 6485507) B6485507
theorem B1620319 : Blo 1279958 1620319 := bstep (se 1 (by rfl) ⟨1215239, by rfl⟩ : syracuseStep 1620319 = 2430479) B2430479
theorem B4159849 : Blo 1279958 4159849 := bstep (se 2 (by rfl) ⟨1559943, by rfl⟩ : syracuseStep 4159849 = 3119887) B3119887
theorem B3242369 : Blo 1279958 3242369 := bstep (se 2 (by rfl) ⟨1215888, by rfl⟩ : syracuseStep 3242369 = 2431777) B2431777
theorem B2161039 : Blo 1279958 2161039 := bstep (se 1 (by rfl) ⟨1620779, by rfl⟩ : syracuseStep 2161039 = 3241559) B3241559
theorem B1440175 : Blo 1279958 1440175 := bstep (se 1 (by rfl) ⟨1080131, by rfl⟩ : syracuseStep 1440175 = 2160263) B2160263
theorem B2431451 : Blo 1279958 2431451 := bstep (se 1 (by rfl) ⟨1823588, by rfl⟩ : syracuseStep 2431451 = 3647177) B3647177
theorem B4618739 : Blo 1279958 4618739 := bstep (se 1 (by rfl) ⟨3464054, by rfl⟩ : syracuseStep 4618739 = 6928109) B6928109
theorem B2734631 : Blo 1279958 2734631 := bstep (se 1 (by rfl) ⟨2050973, by rfl⟩ : syracuseStep 2734631 = 4101947) B4101947
theorem B2882087 : Blo 1279958 2882087 := bstep (se 1 (by rfl) ⟨2161565, by rfl⟩ : syracuseStep 2882087 = 4323131) B4323131
theorem B2595577 : Blo 1279958 2595577 := bstep (se 2 (by rfl) ⟨973341, by rfl⟩ : syracuseStep 2595577 = 1946683) B1946683
theorem B3242825 : Blo 1279958 3242825 := bstep (se 2 (by rfl) ⟨1216059, by rfl⟩ : syracuseStep 3242825 = 2432119) B2432119
theorem B1440607 : Blo 1279958 1440607 := bstep (se 1 (by rfl) ⟨1080455, by rfl⟩ : syracuseStep 1440607 = 2160911) B2160911
theorem B2882411 : Blo 1279958 2882411 := bstep (se 1 (by rfl) ⟨2161808, by rfl⟩ : syracuseStep 2882411 = 4323617) B4323617
theorem B2882465 : Blo 1279958 2882465 := bstep (se 2 (by rfl) ⟨1080924, by rfl⟩ : syracuseStep 2882465 = 2161849) B2161849
theorem B1620911 : Blo 1279958 1620911 := bstep (se 1 (by rfl) ⟨1215683, by rfl⟩ : syracuseStep 1620911 = 2431367) B2431367
theorem B2161721 : Blo 1279958 2161721 := bstep (se 2 (by rfl) ⟨810645, by rfl⟩ : syracuseStep 2161721 = 1621291) B1621291
theorem B6151247 : Blo 1279958 6151247 := bstep (se 1 (by rfl) ⟨4613435, by rfl⟩ : syracuseStep 6151247 = 9226871) B9226871
theorem B7298201 : Blo 1279958 7298201 := bstep (se 2 (by rfl) ⟨2736825, by rfl⟩ : syracuseStep 7298201 = 5473651) B5473651
theorem B3243179 : Blo 1279958 3243179 := bstep (se 1 (by rfl) ⟨2432384, by rfl⟩ : syracuseStep 3243179 = 4864769) B4864769
theorem B78830765 : Blo 1279958 78830765 := bstep (se 3 (by rfl) ⟨14780768, by rfl⟩ : syracuseStep 78830765 = 29561537) B29561537
theorem B1440967 : Blo 1279958 1440967 := bstep (se 1 (by rfl) ⟨1080725, by rfl⟩ : syracuseStep 1440967 = 2161451) B2161451
theorem B2882807 : Blo 1279958 2882807 := bstep (se 1 (by rfl) ⟨2162105, by rfl⟩ : syracuseStep 2882807 = 4324211) B4324211
theorem B4324751 : Blo 1279958 4324751 := bstep (se 1 (by rfl) ⟨3243563, by rfl⟩ : syracuseStep 4324751 = 6487127) B6487127
theorem B2596283 : Blo 1279958 2596283 := bstep (se 1 (by rfl) ⟨1947212, by rfl⟩ : syracuseStep 2596283 = 3894425) B3894425
theorem B2432521 : Blo 1279958 2432521 := bstep (se 2 (by rfl) ⟨912195, by rfl⟩ : syracuseStep 2432521 = 1824391) B1824391
theorem B7298657 : Blo 1279958 7298657 := bstep (se 2 (by rfl) ⟨2736996, by rfl⟩ : syracuseStep 7298657 = 5473993) B5473993
theorem B6159995 : Blo 1279958 6159995 := bstep (se 1 (by rfl) ⟨4619996, by rfl⟩ : syracuseStep 6159995 = 9239993) B9239993
theorem B8208017 : Blo 1279958 8208017 := bstep (se 2 (by rfl) ⟨3078006, by rfl⟩ : syracuseStep 8208017 = 6156013) B6156013
theorem B4325075 : Blo 1279958 4325075 := bstep (se 1 (by rfl) ⟨3243806, by rfl⟩ : syracuseStep 4325075 = 6487613) B6487613
theorem B2465527 : Blo 1279958 2465527 := bstep (se 1 (by rfl) ⟨1849145, by rfl⟩ : syracuseStep 2465527 = 3698291) B3698291
theorem B2162423 : Blo 1279958 2162423 := bstep (se 1 (by rfl) ⟨1621817, by rfl⟩ : syracuseStep 2162423 = 3243635) B3243635
theorem B2883401 : Blo 1279958 2883401 := bstep (se 2 (by rfl) ⟨1081275, by rfl⟩ : syracuseStep 2883401 = 2162551) B2162551
theorem B4865953 : Blo 1279958 4865953 := bstep (se 2 (by rfl) ⟨1824732, by rfl⟩ : syracuseStep 4865953 = 3649465) B3649465
theorem B3243959 : Blo 1279958 3243959 := bstep (se 1 (by rfl) ⟨2432969, by rfl⟩ : syracuseStep 3243959 = 4865939) B4865939
theorem B5840921 : Blo 1279958 5840921 := bstep (se 2 (by rfl) ⟨2190345, by rfl⟩ : syracuseStep 5840921 = 4380691) B4380691
theorem B2883689 : Blo 1279958 2883689 := bstep (se 2 (by rfl) ⟨1081383, by rfl⟩ : syracuseStep 2883689 = 2162767) B2162767
theorem B4866257 : Blo 1279958 4866257 := bstep (se 2 (by rfl) ⟨1824846, by rfl⟩ : syracuseStep 4866257 = 3649693) B3649693
theorem B1442011 : Blo 1279958 1442011 := bstep (se 1 (by rfl) ⟨1081508, by rfl⟩ : syracuseStep 1442011 = 2163017) B2163017
theorem B3244313 : Blo 1279958 3244313 := bstep (se 2 (by rfl) ⟨1216617, by rfl⟩ : syracuseStep 3244313 = 2433235) B2433235
theorem B4104521 : Blo 1279958 4104521 := bstep (se 2 (by rfl) ⟨1539195, by rfl⟩ : syracuseStep 4104521 = 3078391) B3078391
theorem B4325723 : Blo 1279958 4325723 := bstep (se 1 (by rfl) ⟨3244292, by rfl⟩ : syracuseStep 4325723 = 6488585) B6488585
theorem B2597231 : Blo 1279958 2597231 := bstep (se 1 (by rfl) ⟨1947923, by rfl⟩ : syracuseStep 2597231 = 3895847) B3895847
theorem B5546465 : Blo 1279958 5546465 := bstep (se 2 (by rfl) ⟨2079924, by rfl⟩ : syracuseStep 5546465 = 4159849) B4159849
theorem B3244607 : Blo 1279958 3244607 := bstep (se 1 (by rfl) ⟨2433455, by rfl⟩ : syracuseStep 3244607 = 4866911) B4866911
theorem B2884175 : Blo 1279958 2884175 := bstep (se 1 (by rfl) ⟨2163131, by rfl⟩ : syracuseStep 2884175 = 4326263) B4326263
theorem B4866713 : Blo 1279958 4866713 := bstep (se 2 (by rfl) ⟨1825017, by rfl⟩ : syracuseStep 4866713 = 3650035) B3650035
theorem B6488747 : Blo 1279958 6488747 := bstep (se 1 (by rfl) ⟨4866560, by rfl⟩ : syracuseStep 6488747 = 9733121) B9733121
theorem B4866743 : Blo 1279958 4866743 := bstep (se 1 (by rfl) ⟨3650057, by rfl⟩ : syracuseStep 4866743 = 7300115) B7300115
theorem B2884319 : Blo 1279958 2884319 := bstep (se 1 (by rfl) ⟨2163239, by rfl⟩ : syracuseStep 2884319 = 4326479) B4326479
theorem B3244819 : Blo 1279958 3244819 := bstep (se 1 (by rfl) ⟨2433614, by rfl⟩ : syracuseStep 3244819 = 4867229) B4867229
theorem B18465731 : Blo 1279958 18465731 := bstep (se 1 (by rfl) ⟨13849298, by rfl⟩ : syracuseStep 18465731 = 27698597) B27698597
theorem B5194691 : Blo 1279958 5194691 := bstep (se 1 (by rfl) ⟨3896018, by rfl⟩ : syracuseStep 5194691 = 7792037) B7792037
theorem B6489233 : Blo 1279958 6489233 := bstep (se 2 (by rfl) ⟨2433462, by rfl⟩ : syracuseStep 6489233 = 4866925) B4866925
theorem B74884247 : Blo 1279958 74884247 := bstep (se 1 (by rfl) ⟨56163185, by rfl⟩ : syracuseStep 74884247 = 112326371) B112326371
theorem B5620985 : Blo 1279958 5620985 := bstep (se 2 (by rfl) ⟨2107869, by rfl⟩ : syracuseStep 5620985 = 4215739) B4215739
theorem B2811167 : Blo 1279958 2811167 := bstep (se 1 (by rfl) ⟨2108375, by rfl⟩ : syracuseStep 2811167 = 4216751) B4216751
theorem B5842219 : Blo 1279958 5842219 := bstep (se 1 (by rfl) ⟨4381664, by rfl⟩ : syracuseStep 5842219 = 8763329) B8763329
theorem B4613537 : Blo 1279958 4613537 := bstep (se 2 (by rfl) ⟨1730076, by rfl⟩ : syracuseStep 4613537 = 3460153) B3460153
theorem B7292551 : Blo 1279958 7292551 := bstep (se 1 (by rfl) ⟨5469413, by rfl⟩ : syracuseStep 7292551 = 10938827) B10938827
theorem B10938077 : Blo 1279958 10938077 := bstep (se 3 (by rfl) ⟨2050889, by rfl⟩ : syracuseStep 10938077 = 4101779) B4101779
theorem B6154013 : Blo 1279958 6154013 := bstep (se 3 (by rfl) ⟨1153877, by rfl⟩ : syracuseStep 6154013 = 2307755) B2307755
theorem B1279975 : Blo 1279958 1279975 := bstep (se 1 (by rfl) ⟨959981, by rfl⟩ : syracuseStep 1279975 = 1919963) B1919963
theorem B52553843 : Blo 1279958 52553843 := bstep (se 1 (by rfl) ⟨39415382, by rfl⟩ : syracuseStep 52553843 = 78830765) B78830765
theorem B14223475 : Blo 1279958 14223475 := bstep (se 1 (by rfl) ⟨10667606, by rfl⟩ : syracuseStep 14223475 = 21335213) B21335213
theorem B17533057 : Blo 1279958 17533057 := bstep (se 2 (by rfl) ⟨6574896, by rfl⟩ : syracuseStep 17533057 = 13149793) B13149793
theorem B6482105 : Blo 1279958 6482105 := bstep (se 2 (by rfl) ⟨2430789, by rfl⟩ : syracuseStep 6482105 = 4861579) B4861579
theorem B10946825 : Blo 1279958 10946825 := bstep (se 2 (by rfl) ⟨4105059, by rfl⟩ : syracuseStep 10946825 = 8210119) B8210119
theorem B1280287 : Blo 1279958 1280287 := bstep (se 1 (by rfl) ⟨960215, by rfl⟩ : syracuseStep 1280287 = 1920431) B1920431
theorem B1730855 : Blo 1279958 1730855 := bstep (se 1 (by rfl) ⟨1298141, by rfl⟩ : syracuseStep 1730855 = 2596283) B2596283
theorem B3287369 : Blo 1279958 3287369 := bstep (se 2 (by rfl) ⟨1232763, by rfl⟩ : syracuseStep 3287369 = 2465527) B2465527
theorem B1280347 : Blo 1279958 1280347 := bstep (se 1 (by rfl) ⟨960260, by rfl⟩ : syracuseStep 1280347 = 1920521) B1920521
theorem B1280367 : Blo 1279958 1280367 := bstep (se 1 (by rfl) ⟨960275, by rfl⟩ : syracuseStep 1280367 = 1920551) B1920551
theorem B1280423 : Blo 1279958 1280423 := bstep (se 1 (by rfl) ⟨960317, by rfl⟩ : syracuseStep 1280423 = 1920635) B1920635
theorem B4106663 : Blo 1279958 4106663 := bstep (se 1 (by rfl) ⟨3079997, by rfl⟩ : syracuseStep 4106663 = 6159995) B6159995
theorem B9234917 : Blo 1279958 9234917 := bstep (se 4 (by rfl) ⟨865773, by rfl⟩ : syracuseStep 9234917 = 1731547) B1731547
theorem B1280507 : Blo 1279958 1280507 := bstep (se 1 (by rfl) ⟨960380, by rfl⟩ : syracuseStep 1280507 = 1920761) B1920761
theorem B1280575 : Blo 1279958 1280575 := bstep (se 1 (by rfl) ⟨960431, by rfl⟩ : syracuseStep 1280575 = 1920863) B1920863
theorem B1280583 : Blo 1279958 1280583 := bstep (se 1 (by rfl) ⟨960437, by rfl⟩ : syracuseStep 1280583 = 1920875) B1920875
theorem B243329629 : Blo 1279958 243329629 := bstep (se 3 (by rfl) ⟨45624305, by rfl⟩ : syracuseStep 243329629 = 91248611) B91248611
theorem B1280735 : Blo 1279958 1280735 := bstep (se 1 (by rfl) ⟨960551, by rfl⟩ : syracuseStep 1280735 = 1921103) B1921103
theorem B21891869 : Blo 1279958 21891869 := bstep (se 3 (by rfl) ⟨4104725, by rfl⟩ : syracuseStep 21891869 = 8209451) B8209451
theorem B1280815 : Blo 1279958 1280815 := bstep (se 1 (by rfl) ⟨960611, by rfl⟩ : syracuseStep 1280815 = 1921223) B1921223
theorem B1280923 : Blo 1279958 1280923 := bstep (se 1 (by rfl) ⟨960692, by rfl⟩ : syracuseStep 1280923 = 1921385) B1921385
theorem B1280975 : Blo 1279958 1280975 := bstep (se 1 (by rfl) ⟨960731, by rfl⟩ : syracuseStep 1280975 = 1921463) B1921463
theorem B1919975 : Blo 1279958 1919975 := bstep (se 1 (by rfl) ⟨1439981, by rfl⟩ : syracuseStep 1919975 = 2879963) B2879963
theorem B1280999 : Blo 1279958 1280999 := bstep (se 1 (by rfl) ⟨960749, by rfl⟩ : syracuseStep 1280999 = 1921499) B1921499
theorem B6237199 : Blo 1279958 6237199 := bstep (se 1 (by rfl) ⟨4677899, by rfl⟩ : syracuseStep 6237199 = 9355799) B9355799
theorem B3648635 : Blo 1279958 3648635 := bstep (se 1 (by rfl) ⟨2736476, by rfl⟩ : syracuseStep 3648635 = 5472953) B5472953
theorem B1920233 : Blo 1279958 1920233 := bstep (se 2 (by rfl) ⟨720087, by rfl⟩ : syracuseStep 1920233 = 1440175) B1440175
theorem B1920287 : Blo 1279958 1920287 := bstep (se 1 (by rfl) ⟨1440215, by rfl⟩ : syracuseStep 1920287 = 2880431) B2880431
theorem B6155551 : Blo 1279958 6155551 := bstep (se 1 (by rfl) ⟨4616663, by rfl⟩ : syracuseStep 6155551 = 9233327) B9233327
theorem B1281311 : Blo 1279958 1281311 := bstep (se 1 (by rfl) ⟨960983, by rfl⟩ : syracuseStep 1281311 = 1921967) B1921967
theorem B1281371 : Blo 1279958 1281371 := bstep (se 1 (by rfl) ⟨961028, by rfl⟩ : syracuseStep 1281371 = 1922057) B1922057
theorem B1281391 : Blo 1279958 1281391 := bstep (se 1 (by rfl) ⟨961043, by rfl⟩ : syracuseStep 1281391 = 1922087) B1922087
theorem B1281447 : Blo 1279958 1281447 := bstep (se 1 (by rfl) ⟨961085, by rfl⟩ : syracuseStep 1281447 = 1922171) B1922171
theorem B1920455 : Blo 1279958 1920455 := bstep (se 1 (by rfl) ⟨1440341, by rfl⟩ : syracuseStep 1920455 = 2880683) B2880683
theorem B1281531 : Blo 1279958 1281531 := bstep (se 1 (by rfl) ⟨961148, by rfl⟩ : syracuseStep 1281531 = 1922297) B1922297
theorem B27684413 : Blo 1279958 27684413 := bstep (se 3 (by rfl) ⟨5190827, by rfl⟩ : syracuseStep 27684413 = 10381655) B10381655
theorem B1281599 : Blo 1279958 1281599 := bstep (se 1 (by rfl) ⟨961199, by rfl⟩ : syracuseStep 1281599 = 1922399) B1922399
theorem B1281607 : Blo 1279958 1281607 := bstep (se 1 (by rfl) ⟨961205, by rfl⟩ : syracuseStep 1281607 = 1922411) B1922411
theorem B4320863 : Blo 1279958 4320863 := bstep (se 1 (by rfl) ⟨3240647, by rfl⟩ : syracuseStep 4320863 = 6481295) B6481295
theorem B3460769 : Blo 1279958 3460769 := bstep (se 2 (by rfl) ⟨1297788, by rfl⟩ : syracuseStep 3460769 = 2595577) B2595577
theorem B6926033 : Blo 1279958 6926033 := bstep (se 2 (by rfl) ⟨2597262, by rfl⟩ : syracuseStep 6926033 = 5194525) B5194525
theorem B1281759 : Blo 1279958 1281759 := bstep (se 1 (by rfl) ⟨961319, by rfl⟩ : syracuseStep 1281759 = 1922639) B1922639
theorem B5467945 : Blo 1279958 5467945 := bstep (se 2 (by rfl) ⟨2050479, by rfl⟩ : syracuseStep 5467945 = 4100959) B4100959
theorem B1920809 : Blo 1279958 1920809 := bstep (se 2 (by rfl) ⟨720303, by rfl⟩ : syracuseStep 1920809 = 1440607) B1440607
theorem B1920815 : Blo 1279958 1920815 := bstep (se 1 (by rfl) ⟨1440611, by rfl⟩ : syracuseStep 1920815 = 2881223) B2881223
theorem B1281839 : Blo 1279958 1281839 := bstep (se 1 (by rfl) ⟨961379, by rfl⟩ : syracuseStep 1281839 = 1922759) B1922759
theorem B1281947 : Blo 1279958 1281947 := bstep (se 1 (by rfl) ⟨961460, by rfl⟩ : syracuseStep 1281947 = 1922921) B1922921
theorem B4861853 : Blo 1279958 4861853 := bstep (se 3 (by rfl) ⟨911597, by rfl⟩ : syracuseStep 4861853 = 1823195) B1823195
theorem B6483887 : Blo 1279958 6483887 := bstep (se 1 (by rfl) ⟨4862915, by rfl⟩ : syracuseStep 6483887 = 9725831) B9725831
theorem B12316637 : Blo 1279958 12316637 := bstep (se 3 (by rfl) ⟨2309369, by rfl⟩ : syracuseStep 12316637 = 4618739) B4618739
theorem B5468219 : Blo 1279958 5468219 := bstep (se 1 (by rfl) ⟨4101164, by rfl⟩ : syracuseStep 5468219 = 8202329) B8202329
theorem B13332545 : Blo 1279958 13332545 := bstep (se 2 (by rfl) ⟨4999704, by rfl⟩ : syracuseStep 13332545 = 9999409) B9999409
theorem B1921289 : Blo 1279958 1921289 := bstep (se 2 (by rfl) ⟨720483, by rfl⟩ : syracuseStep 1921289 = 1440967) B1440967
theorem B3240283 : Blo 1279958 3240283 := bstep (se 1 (by rfl) ⟨2430212, by rfl⟩ : syracuseStep 3240283 = 4860425) B4860425
theorem B1823087 : Blo 1279958 1823087 := bstep (se 1 (by rfl) ⟨1367315, by rfl⟩ : syracuseStep 1823087 = 2734631) B2734631
theorem B1921391 : Blo 1279958 1921391 := bstep (se 1 (by rfl) ⟨1441043, by rfl⟩ : syracuseStep 1921391 = 2882087) B2882087
theorem B3649967 : Blo 1279958 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B2879927 : Blo 1279958 2879927 := bstep (se 1 (by rfl) ⟨2159945, by rfl⟩ : syracuseStep 2879927 = 4319891) B4319891
theorem B2880071 : Blo 1279958 2880071 := bstep (se 1 (by rfl) ⟨2160053, by rfl⟩ : syracuseStep 2880071 = 4320107) B4320107
theorem B1921607 : Blo 1279958 1921607 := bstep (se 1 (by rfl) ⟨1441205, by rfl⟩ : syracuseStep 1921607 = 2882411) B2882411
theorem B2880107 : Blo 1279958 2880107 := bstep (se 1 (by rfl) ⟨2160080, by rfl⟩ : syracuseStep 2880107 = 4320161) B4320161
theorem B1921643 : Blo 1279958 1921643 := bstep (se 1 (by rfl) ⟨1441232, by rfl⟩ : syracuseStep 1921643 = 2882465) B2882465
theorem B15569561 : Blo 1279958 15569561 := bstep (se 2 (by rfl) ⟨5838585, by rfl⟩ : syracuseStep 15569561 = 11677171) B11677171
theorem B4100831 : Blo 1279958 4100831 := bstep (se 1 (by rfl) ⟨3075623, by rfl⟩ : syracuseStep 4100831 = 6151247) B6151247
theorem B1921871 : Blo 1279958 1921871 := bstep (se 1 (by rfl) ⟨1441403, by rfl⟩ : syracuseStep 1921871 = 2882807) B2882807
theorem B4322267 : Blo 1279958 4322267 := bstep (se 1 (by rfl) ⟨3241700, by rfl⟩ : syracuseStep 4322267 = 6483401) B6483401
theorem B2880503 : Blo 1279958 2880503 := bstep (se 1 (by rfl) ⟨2160377, by rfl⟩ : syracuseStep 2880503 = 4320755) B4320755
theorem B4322429 : Blo 1279958 4322429 := bstep (se 3 (by rfl) ⟨810455, by rfl⟩ : syracuseStep 4322429 = 1620911) B1620911
theorem B1922267 : Blo 1279958 1922267 := bstep (se 1 (by rfl) ⟨1441700, by rfl⟩ : syracuseStep 1922267 = 2883401) B2883401
theorem B4322537 : Blo 1279958 4322537 := bstep (se 2 (by rfl) ⟨1620951, by rfl⟩ : syracuseStep 4322537 = 3241903) B3241903
theorem B3241255 : Blo 1279958 3241255 := bstep (se 1 (by rfl) ⟨2430941, by rfl⟩ : syracuseStep 3241255 = 4861883) B4861883
theorem B2880863 : Blo 1279958 2880863 := bstep (se 1 (by rfl) ⟨2160647, by rfl⟩ : syracuseStep 2880863 = 4321295) B4321295
theorem B4863341 : Blo 1279958 4863341 := bstep (se 3 (by rfl) ⟨911876, by rfl⟩ : syracuseStep 4863341 = 1823753) B1823753
theorem B1922441 : Blo 1279958 1922441 := bstep (se 2 (by rfl) ⟨720915, by rfl⟩ : syracuseStep 1922441 = 1441831) B1441831
theorem B4322699 : Blo 1279958 4322699 := bstep (se 1 (by rfl) ⟨3242024, by rfl⟩ : syracuseStep 4322699 = 6484049) B6484049
theorem B8205761 : Blo 1279958 8205761 := bstep (se 2 (by rfl) ⟨3077160, by rfl⟩ : syracuseStep 8205761 = 6154321) B6154321
theorem B35067329 : Blo 1279958 35067329 := bstep (se 2 (by rfl) ⟨13150248, by rfl⟩ : syracuseStep 35067329 = 26300497) B26300497
theorem B36935149 : Blo 1279958 36935149 := bstep (se 3 (by rfl) ⟨6925340, by rfl⟩ : syracuseStep 36935149 = 13850681) B13850681
theorem B2160121 : Blo 1279958 2160121 := bstep (se 2 (by rfl) ⟨810045, by rfl⟩ : syracuseStep 2160121 = 1620091) B1620091
theorem B3241529 : Blo 1279958 3241529 := bstep (se 2 (by rfl) ⟨1215573, by rfl⟩ : syracuseStep 3241529 = 2431147) B2431147
theorem B2881259 : Blo 1279958 2881259 := bstep (se 1 (by rfl) ⟨2160944, by rfl⟩ : syracuseStep 2881259 = 4321889) B4321889
theorem B1922795 : Blo 1279958 1922795 := bstep (se 1 (by rfl) ⟨1442096, by rfl⟩ : syracuseStep 1922795 = 2884193) B2884193
theorem B2160391 : Blo 1279958 2160391 := bstep (se 1 (by rfl) ⟨1620293, by rfl⟩ : syracuseStep 2160391 = 3240587) B3240587
theorem B2160425 : Blo 1279958 2160425 := bstep (se 2 (by rfl) ⟨810159, by rfl⟩ : syracuseStep 2160425 = 1620319) B1620319
theorem B2881385 : Blo 1279958 2881385 := bstep (se 2 (by rfl) ⟨1080519, by rfl⟩ : syracuseStep 2881385 = 2161039) B2161039
theorem B9238607 : Blo 1279958 9238607 := bstep (se 1 (by rfl) ⟨6928955, by rfl⟩ : syracuseStep 9238607 = 13857911) B13857911
theorem B2594921 : Blo 1279958 2594921 := bstep (se 2 (by rfl) ⟨973095, by rfl⟩ : syracuseStep 2594921 = 1946191) B1946191
theorem B4929665 : Blo 1279958 4929665 := bstep (se 2 (by rfl) ⟨1848624, by rfl⟩ : syracuseStep 4929665 = 3697249) B3697249
theorem B5847235 : Blo 1279958 5847235 := bstep (se 1 (by rfl) ⟨4385426, by rfl⟩ : syracuseStep 5847235 = 8770853) B8770853
theorem B1440031 : Blo 1279958 1440031 := bstep (se 1 (by rfl) ⟨1080023, by rfl⟩ : syracuseStep 1440031 = 2160047) B2160047
theorem B1620263 : Blo 1279958 1620263 := bstep (se 1 (by rfl) ⟨1215197, by rfl⟩ : syracuseStep 1620263 = 2430395) B2430395
theorem B2341345 : Blo 1279958 2341345 := bstep (se 2 (by rfl) ⟨878004, by rfl⟩ : syracuseStep 2341345 = 1756009) B1756009
theorem B2161147 : Blo 1279958 2161147 := bstep (se 1 (by rfl) ⟨1620860, by rfl⟩ : syracuseStep 2161147 = 3241721) B3241721
theorem B1440319 : Blo 1279958 1440319 := bstep (se 1 (by rfl) ⟨1080239, by rfl⟩ : syracuseStep 1440319 = 2160479) B2160479
theorem B3078719 : Blo 1279958 3078719 := bstep (se 1 (by rfl) ⟨2309039, by rfl⟩ : syracuseStep 3078719 = 4618079) B4618079
theorem B1620587 : Blo 1279958 1620587 := bstep (se 1 (by rfl) ⟨1215440, by rfl⟩ : syracuseStep 1620587 = 2430881) B2430881
theorem B2431595 : Blo 1279958 2431595 := bstep (se 1 (by rfl) ⟨1823696, by rfl⟩ : syracuseStep 2431595 = 3647393) B3647393
theorem B2882231 : Blo 1279958 2882231 := bstep (se 1 (by rfl) ⟨2161673, by rfl⟩ : syracuseStep 2882231 = 4323347) B4323347
theorem B5192387 : Blo 1279958 5192387 := bstep (se 1 (by rfl) ⟨3894290, by rfl⟩ : syracuseStep 5192387 = 7788581) B7788581
theorem B24632045 : Blo 1279958 24632045 := bstep (se 3 (by rfl) ⟨4618508, by rfl⟩ : syracuseStep 24632045 = 9237017) B9237017
theorem B6486803 : Blo 1279958 6486803 := bstep (se 1 (by rfl) ⟨4865102, by rfl⟩ : syracuseStep 6486803 = 9730205) B9730205
theorem B2882447 : Blo 1279958 2882447 := bstep (se 1 (by rfl) ⟨2161835, by rfl⟩ : syracuseStep 2882447 = 4323671) B4323671
theorem B16423823 : Blo 1279958 16423823 := bstep (se 1 (by rfl) ⟨12317867, by rfl⟩ : syracuseStep 16423823 = 24635735) B24635735
theorem B2161579 : Blo 1279958 2161579 := bstep (se 1 (by rfl) ⟨1621184, by rfl⟩ : syracuseStep 2161579 = 3242369) B3242369
theorem B1620967 : Blo 1279958 1620967 := bstep (se 1 (by rfl) ⟨1215725, by rfl⟩ : syracuseStep 1620967 = 2431451) B2431451
theorem B4103291 : Blo 1279958 4103291 := bstep (se 1 (by rfl) ⟨3077468, by rfl⟩ : syracuseStep 4103291 = 6154937) B6154937
theorem B2161883 : Blo 1279958 2161883 := bstep (se 1 (by rfl) ⟨1621412, by rfl⟩ : syracuseStep 2161883 = 3242825) B3242825
theorem B3243361 : Blo 1279958 3243361 := bstep (se 2 (by rfl) ⟨1216260, by rfl⟩ : syracuseStep 3243361 = 2432521) B2432521
theorem B1441147 : Blo 1279958 1441147 := bstep (se 1 (by rfl) ⟨1080860, by rfl⟩ : syracuseStep 1441147 = 2161721) B2161721
theorem B6151553 : Blo 1279958 6151553 := bstep (se 2 (by rfl) ⟨2306832, by rfl⟩ : syracuseStep 6151553 = 4613665) B4613665
theorem B4865467 : Blo 1279958 4865467 := bstep (se 1 (by rfl) ⟨3649100, by rfl⟩ : syracuseStep 4865467 = 7298201) B7298201
theorem B2162119 : Blo 1279958 2162119 := bstep (se 1 (by rfl) ⟨1621589, by rfl⟩ : syracuseStep 2162119 = 3243179) B3243179
theorem B27704825 : Blo 1279958 27704825 := bstep (se 2 (by rfl) ⟨10389309, by rfl⟩ : syracuseStep 27704825 = 20778619) B20778619
theorem B2883167 : Blo 1279958 2883167 := bstep (se 1 (by rfl) ⟨2162375, by rfl⟩ : syracuseStep 2883167 = 4324751) B4324751
theorem B4865771 : Blo 1279958 4865771 := bstep (se 1 (by rfl) ⟨3649328, by rfl⟩ : syracuseStep 4865771 = 7298657) B7298657
theorem B5472011 : Blo 1279958 5472011 := bstep (se 1 (by rfl) ⟨4104008, by rfl⟩ : syracuseStep 5472011 = 8208017) B8208017
theorem B2883383 : Blo 1279958 2883383 := bstep (se 1 (by rfl) ⟨2162537, by rfl⟩ : syracuseStep 2883383 = 4325075) B4325075
theorem B2432825 : Blo 1279958 2432825 := bstep (se 2 (by rfl) ⟨912309, by rfl⟩ : syracuseStep 2432825 = 1824619) B1824619
theorem B1441615 : Blo 1279958 1441615 := bstep (se 1 (by rfl) ⟨1081211, by rfl⟩ : syracuseStep 1441615 = 2162423) B2162423
theorem B6487937 : Blo 1279958 6487937 := bstep (se 2 (by rfl) ⟨2432976, by rfl⟩ : syracuseStep 6487937 = 4865953) B4865953
theorem B2162639 : Blo 1279958 2162639 := bstep (se 1 (by rfl) ⟨1621979, by rfl⟩ : syracuseStep 2162639 = 3243959) B3243959
theorem B3645479 : Blo 1279958 3645479 := bstep (se 1 (by rfl) ⟨2734109, by rfl⟩ : syracuseStep 3645479 = 5468219) B5468219
theorem B8888363 : Blo 1279958 8888363 := bstep (se 1 (by rfl) ⟨6666272, by rfl⟩ : syracuseStep 8888363 = 13332545) B13332545
theorem B3244171 : Blo 1279958 3244171 := bstep (se 1 (by rfl) ⟨2433128, by rfl⟩ : syracuseStep 3244171 = 4866257) B4866257
theorem B2162875 : Blo 1279958 2162875 := bstep (se 1 (by rfl) ⟨1622156, by rfl⟩ : syracuseStep 2162875 = 3244313) B3244313
theorem B2736347 : Blo 1279958 2736347 := bstep (se 1 (by rfl) ⟨2052260, by rfl⟩ : syracuseStep 2736347 = 4104521) B4104521
theorem B2883815 : Blo 1279958 2883815 := bstep (se 1 (by rfl) ⟨2162861, by rfl⟩ : syracuseStep 2883815 = 4325723) B4325723
theorem B2433311 : Blo 1279958 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B2163071 : Blo 1279958 2163071 := bstep (se 1 (by rfl) ⟨1622303, by rfl⟩ : syracuseStep 2163071 = 3244607) B3244607
theorem B10379707 : Blo 1279958 10379707 := bstep (se 1 (by rfl) ⟨7784780, by rfl⟩ : syracuseStep 10379707 = 15569561) B15569561
theorem B3244475 : Blo 1279958 3244475 := bstep (se 1 (by rfl) ⟨2433356, by rfl⟩ : syracuseStep 3244475 = 4866713) B4866713
theorem B4325831 : Blo 1279958 4325831 := bstep (se 1 (by rfl) ⟨3244373, by rfl⟩ : syracuseStep 4325831 = 6488747) B6488747
theorem B3244495 : Blo 1279958 3244495 := bstep (se 1 (by rfl) ⟨2433371, by rfl⟩ : syracuseStep 3244495 = 4866743) B4866743
theorem B75858533 : Blo 1279958 75858533 := bstep (se 4 (by rfl) ⟨7111737, by rfl⟩ : syracuseStep 75858533 = 14223475) B14223475
theorem B3121793 : Blo 1279958 3121793 := bstep (se 2 (by rfl) ⟨1170672, by rfl⟩ : syracuseStep 3121793 = 2341345) B2341345
theorem B4326155 : Blo 1279958 4326155 := bstep (se 1 (by rfl) ⟨3244616, by rfl⟩ : syracuseStep 4326155 = 6489233) B6489233
theorem B49922831 : Blo 1279958 49922831 := bstep (se 1 (by rfl) ⟨37442123, by rfl⟩ : syracuseStep 49922831 = 74884247) B74884247
theorem B4326425 : Blo 1279958 4326425 := bstep (se 2 (by rfl) ⟨1622409, by rfl⟩ : syracuseStep 4326425 = 3244819) B3244819
theorem B7292051 : Blo 1279958 7292051 := bstep (se 1 (by rfl) ⟨5469038, by rfl⟩ : syracuseStep 7292051 = 10938077) B10938077
theorem B8316265 : Blo 1279958 8316265 := bstep (se 2 (by rfl) ⟨3118599, by rfl⟩ : syracuseStep 8316265 = 6237199) B6237199
theorem B2737775 : Blo 1279958 2737775 := bstep (se 1 (by rfl) ⟨2053331, by rfl⟩ : syracuseStep 2737775 = 4106663) B4106663
theorem B1279983 : Blo 1279958 1279983 := bstep (se 1 (by rfl) ⟨959987, by rfl⟩ : syracuseStep 1279983 = 1919975) B1919975
theorem B16410701 : Blo 1279958 16410701 := bstep (se 3 (by rfl) ⟨3077006, by rfl⟩ : syracuseStep 16410701 = 6154013) B6154013
theorem B1280155 : Blo 1279958 1280155 := bstep (se 1 (by rfl) ⟨960116, by rfl⟩ : syracuseStep 1280155 = 1920233) B1920233
theorem B1280191 : Blo 1279958 1280191 := bstep (se 1 (by rfl) ⟨960143, by rfl⟩ : syracuseStep 1280191 = 1920287) B1920287
theorem B1280303 : Blo 1279958 1280303 := bstep (se 1 (by rfl) ⟨960227, by rfl⟩ : syracuseStep 1280303 = 1920455) B1920455
theorem B3648007 : Blo 1279958 3648007 := bstep (se 1 (by rfl) ⟨2736005, by rfl⟩ : syracuseStep 3648007 = 5472011) B5472011
theorem B1280539 : Blo 1279958 1280539 := bstep (se 1 (by rfl) ⟨960404, by rfl⟩ : syracuseStep 1280539 = 1920809) B1920809
theorem B1280543 : Blo 1279958 1280543 := bstep (se 1 (by rfl) ⟨960407, by rfl⟩ : syracuseStep 1280543 = 1920815) B1920815
theorem B32844365 : Blo 1279958 32844365 := bstep (se 3 (by rfl) ⟨6158318, by rfl⟩ : syracuseStep 32844365 = 12316637) B12316637
theorem B15575789 : Blo 1279958 15575789 := bstep (se 3 (by rfl) ⟨2920460, by rfl⟩ : syracuseStep 15575789 = 5840921) B5840921
theorem B1280859 : Blo 1279958 1280859 := bstep (se 1 (by rfl) ⟨960644, by rfl⟩ : syracuseStep 1280859 = 1921289) B1921289
theorem B1280927 : Blo 1279958 1280927 := bstep (se 1 (by rfl) ⟨960695, by rfl⟩ : syracuseStep 1280927 = 1921391) B1921391
theorem B1919951 : Blo 1279958 1919951 := bstep (se 1 (by rfl) ⟨1439963, by rfl⟩ : syracuseStep 1919951 = 2879927) B2879927
theorem B3697643 : Blo 1279958 3697643 := bstep (se 1 (by rfl) ⟨2773232, by rfl⟩ : syracuseStep 3697643 = 5546465) B5546465
theorem B1920041 : Blo 1279958 1920041 := bstep (se 2 (by rfl) ⟨720015, by rfl⟩ : syracuseStep 1920041 = 1440031) B1440031
theorem B1920047 : Blo 1279958 1920047 := bstep (se 1 (by rfl) ⟨1440035, by rfl⟩ : syracuseStep 1920047 = 2880071) B2880071
theorem B1281071 : Blo 1279958 1281071 := bstep (se 1 (by rfl) ⟨960803, by rfl⟩ : syracuseStep 1281071 = 1921607) B1921607
theorem B1920071 : Blo 1279958 1920071 := bstep (se 1 (by rfl) ⟨1440053, by rfl⟩ : syracuseStep 1920071 = 2880107) B2880107
theorem B1281095 : Blo 1279958 1281095 := bstep (se 1 (by rfl) ⟨960821, by rfl⟩ : syracuseStep 1281095 = 1921643) B1921643
theorem B4320377 : Blo 1279958 4320377 := bstep (se 2 (by rfl) ⟨1620141, by rfl⟩ : syracuseStep 4320377 = 3240283) B3240283
theorem B1281247 : Blo 1279958 1281247 := bstep (se 1 (by rfl) ⟨960935, by rfl⟩ : syracuseStep 1281247 = 1921871) B1921871
theorem B1920335 : Blo 1279958 1920335 := bstep (se 1 (by rfl) ⟨1440251, by rfl⟩ : syracuseStep 1920335 = 2880503) B2880503
theorem B1920425 : Blo 1279958 1920425 := bstep (se 2 (by rfl) ⟨720159, by rfl⟩ : syracuseStep 1920425 = 1440319) B1440319
theorem B4320701 : Blo 1279958 4320701 := bstep (se 3 (by rfl) ⟨810131, by rfl⟩ : syracuseStep 4320701 = 1620263) B1620263
theorem B4615613 : Blo 1279958 4615613 := bstep (se 3 (by rfl) ⟨865427, by rfl⟩ : syracuseStep 4615613 = 1730855) B1730855
theorem B324439505 : Blo 1279958 324439505 := bstep (se 2 (by rfl) ⟨121664814, by rfl⟩ : syracuseStep 324439505 = 243329629) B243329629
theorem B1281511 : Blo 1279958 1281511 := bstep (se 1 (by rfl) ⟨961133, by rfl⟩ : syracuseStep 1281511 = 1922267) B1922267
theorem B3747323 : Blo 1279958 3747323 := bstep (se 1 (by rfl) ⟨2810492, by rfl⟩ : syracuseStep 3747323 = 5620985) B5620985
theorem B1920575 : Blo 1279958 1920575 := bstep (se 1 (by rfl) ⟨1440431, by rfl⟩ : syracuseStep 1920575 = 2880863) B2880863
theorem B1281627 : Blo 1279958 1281627 := bstep (se 1 (by rfl) ⟨961220, by rfl⟩ : syracuseStep 1281627 = 1922441) B1922441
theorem B4861565 : Blo 1279958 4861565 := bstep (se 3 (by rfl) ⟨911543, by rfl⟩ : syracuseStep 4861565 = 1823087) B1823087
theorem B6925949 : Blo 1279958 6925949 := bstep (se 3 (by rfl) ⟨1298615, by rfl⟩ : syracuseStep 6925949 = 2597231) B2597231
theorem B1920839 : Blo 1279958 1920839 := bstep (se 1 (by rfl) ⟨1440629, by rfl⟩ : syracuseStep 1920839 = 2881259) B2881259
theorem B1281863 : Blo 1279958 1281863 := bstep (se 1 (by rfl) ⟨961397, by rfl⟩ : syracuseStep 1281863 = 1922795) B1922795
theorem B1920923 : Blo 1279958 1920923 := bstep (se 1 (by rfl) ⟨1440692, by rfl⟩ : syracuseStep 1920923 = 2881385) B2881385
theorem B4321403 : Blo 1279958 4321403 := bstep (se 1 (by rfl) ⟨3241052, by rfl⟩ : syracuseStep 4321403 = 6482105) B6482105
theorem B2191579 : Blo 1279958 2191579 := bstep (se 1 (by rfl) ⟨1643684, by rfl⟩ : syracuseStep 2191579 = 3287369) B3287369
theorem B4321565 : Blo 1279958 4321565 := bstep (se 3 (by rfl) ⟨810293, by rfl⟩ : syracuseStep 4321565 = 1620587) B1620587
theorem B6156611 : Blo 1279958 6156611 := bstep (se 1 (by rfl) ⟨4617458, by rfl⟩ : syracuseStep 6156611 = 9234917) B9234917
theorem B2052479 : Blo 1279958 2052479 := bstep (se 1 (by rfl) ⟨1539359, by rfl⟩ : syracuseStep 2052479 = 3078719) B3078719
theorem B4321673 : Blo 1279958 4321673 := bstep (se 2 (by rfl) ⟨1620627, by rfl⟩ : syracuseStep 4321673 = 3241255) B3241255
theorem B1921487 : Blo 1279958 1921487 := bstep (se 1 (by rfl) ⟨1441115, by rfl⟩ : syracuseStep 1921487 = 2882231) B2882231
theorem B3461591 : Blo 1279958 3461591 := bstep (se 1 (by rfl) ⟨2596193, by rfl⟩ : syracuseStep 3461591 = 5192387) B5192387
theorem B16421363 : Blo 1279958 16421363 := bstep (se 1 (by rfl) ⟨12316022, by rfl⟩ : syracuseStep 16421363 = 24632045) B24632045
theorem B1921529 : Blo 1279958 1921529 := bstep (se 2 (by rfl) ⟨720573, by rfl⟩ : syracuseStep 1921529 = 1441147) B1441147
theorem B14594579 : Blo 1279958 14594579 := bstep (se 1 (by rfl) ⟨10945934, by rfl⟩ : syracuseStep 14594579 = 21891869) B21891869
theorem B18469421 : Blo 1279958 18469421 := bstep (se 3 (by rfl) ⟨3463016, by rfl⟩ : syracuseStep 18469421 = 6926033) B6926033
theorem B1921631 : Blo 1279958 1921631 := bstep (se 1 (by rfl) ⟨1441223, by rfl⟩ : syracuseStep 1921631 = 2882447) B2882447
theorem B10949215 : Blo 1279958 10949215 := bstep (se 1 (by rfl) ⟨8211911, by rfl⟩ : syracuseStep 10949215 = 16423823) B16423823
theorem B49246865 : Blo 1279958 49246865 := bstep (se 2 (by rfl) ⟨18467574, by rfl⟩ : syracuseStep 49246865 = 36935149) B36935149
theorem B2880161 : Blo 1279958 2880161 := bstep (se 2 (by rfl) ⟨1080060, by rfl⟩ : syracuseStep 2880161 = 2160121) B2160121
theorem B4101035 : Blo 1279958 4101035 := bstep (se 1 (by rfl) ⟨3075776, by rfl⟩ : syracuseStep 4101035 = 6151553) B6151553
theorem B18469883 : Blo 1279958 18469883 := bstep (se 1 (by rfl) ⟨13852412, by rfl⟩ : syracuseStep 18469883 = 27704825) B27704825
theorem B2880521 : Blo 1279958 2880521 := bstep (se 2 (by rfl) ⟨1080195, by rfl⟩ : syracuseStep 2880521 = 2160391) B2160391
theorem B2880575 : Blo 1279958 2880575 := bstep (se 1 (by rfl) ⟨2160431, by rfl⟩ : syracuseStep 2880575 = 4320863) B4320863
theorem B1922111 : Blo 1279958 1922111 := bstep (se 1 (by rfl) ⟨1441583, by rfl⟩ : syracuseStep 1922111 = 2883167) B2883167
theorem B1922153 : Blo 1279958 1922153 := bstep (se 2 (by rfl) ⟨720807, by rfl⟩ : syracuseStep 1922153 = 1441615) B1441615
theorem B2307179 : Blo 1279958 2307179 := bstep (se 1 (by rfl) ⟨1730384, by rfl⟩ : syracuseStep 2307179 = 3460769) B3460769
theorem B1922255 : Blo 1279958 1922255 := bstep (se 1 (by rfl) ⟨1441691, by rfl⟩ : syracuseStep 1922255 = 2883383) B2883383
theorem B3241235 : Blo 1279958 3241235 := bstep (se 1 (by rfl) ⟨2430926, by rfl⟩ : syracuseStep 3241235 = 4861853) B4861853
theorem B4322591 : Blo 1279958 4322591 := bstep (se 1 (by rfl) ⟨3241943, by rfl⟩ : syracuseStep 4322591 = 6483887) B6483887
theorem B1922459 : Blo 1279958 1922459 := bstep (se 1 (by rfl) ⟨1441844, by rfl⟩ : syracuseStep 1922459 = 2883689) B2883689
theorem B23377409 : Blo 1279958 23377409 := bstep (se 2 (by rfl) ⟨8766528, by rfl⟩ : syracuseStep 23377409 = 17533057) B17533057
theorem B6919789 : Blo 1279958 6919789 := bstep (se 3 (by rfl) ⟨1297460, by rfl⟩ : syracuseStep 6919789 = 2594921) B2594921
theorem B1922681 : Blo 1279958 1922681 := bstep (se 2 (by rfl) ⟨721005, by rfl⟩ : syracuseStep 1922681 = 1442011) B1442011
theorem B13145773 : Blo 1279958 13145773 := bstep (se 3 (by rfl) ⟨2464832, by rfl⟩ : syracuseStep 13145773 = 4929665) B4929665
theorem B1922783 : Blo 1279958 1922783 := bstep (se 1 (by rfl) ⟨1442087, by rfl⟩ : syracuseStep 1922783 = 2884175) B2884175
theorem B2733887 : Blo 1279958 2733887 := bstep (se 1 (by rfl) ⟨2050415, by rfl⟩ : syracuseStep 2733887 = 4100831) B4100831
theorem B1922879 : Blo 1279958 1922879 := bstep (se 1 (by rfl) ⟨1442159, by rfl⟩ : syracuseStep 1922879 = 2884319) B2884319
theorem B12310487 : Blo 1279958 12310487 := bstep (se 1 (by rfl) ⟨9232865, by rfl⟩ : syracuseStep 12310487 = 18465731) B18465731
theorem B3463127 : Blo 1279958 3463127 := bstep (se 1 (by rfl) ⟨2597345, by rfl⟩ : syracuseStep 3463127 = 5194691) B5194691
theorem B2881511 : Blo 1279958 2881511 := bstep (se 1 (by rfl) ⟨2161133, by rfl⟩ : syracuseStep 2881511 = 4322267) B4322267
theorem B2881529 : Blo 1279958 2881529 := bstep (se 2 (by rfl) ⟨1080573, by rfl⟩ : syracuseStep 2881529 = 2161147) B2161147
theorem B2881619 : Blo 1279958 2881619 := bstep (se 1 (by rfl) ⟨2161214, by rfl⟩ : syracuseStep 2881619 = 4322429) B4322429
theorem B2881691 : Blo 1279958 2881691 := bstep (se 1 (by rfl) ⟨2161268, by rfl⟩ : syracuseStep 2881691 = 4322537) B4322537
theorem B1874111 : Blo 1279958 1874111 := bstep (se 1 (by rfl) ⟨1405583, by rfl⟩ : syracuseStep 1874111 = 2811167) B2811167
theorem B3242227 : Blo 1279958 3242227 := bstep (se 1 (by rfl) ⟨2431670, by rfl⟩ : syracuseStep 3242227 = 4863341) B4863341
theorem B2881799 : Blo 1279958 2881799 := bstep (se 1 (by rfl) ⟨2161349, by rfl⟩ : syracuseStep 2881799 = 4322699) B4322699
theorem B5470507 : Blo 1279958 5470507 := bstep (se 1 (by rfl) ⟨4102880, by rfl⟩ : syracuseStep 5470507 = 8205761) B8205761
theorem B23378219 : Blo 1279958 23378219 := bstep (se 1 (by rfl) ⟨17533664, by rfl⟩ : syracuseStep 23378219 = 35067329) B35067329
theorem B31185253 : Blo 1279958 31185253 := bstep (se 4 (by rfl) ⟨2923617, by rfl⟩ : syracuseStep 31185253 = 5847235) B5847235
theorem B2161019 : Blo 1279958 2161019 := bstep (se 1 (by rfl) ⟨1620764, by rfl⟩ : syracuseStep 2161019 = 3241529) B3241529
theorem B12302765 : Blo 1279958 12302765 := bstep (se 3 (by rfl) ⟨2306768, by rfl⟩ : syracuseStep 12302765 = 4613537) B4613537
theorem B1440283 : Blo 1279958 1440283 := bstep (se 1 (by rfl) ⟨1080212, by rfl⟩ : syracuseStep 1440283 = 2160425) B2160425
theorem B2882105 : Blo 1279958 2882105 := bstep (se 2 (by rfl) ⟨1080789, by rfl⟩ : syracuseStep 2882105 = 2161579) B2161579
theorem B2161289 : Blo 1279958 2161289 := bstep (se 2 (by rfl) ⟨810483, by rfl⟩ : syracuseStep 2161289 = 1620967) B1620967
theorem B6159071 : Blo 1279958 6159071 := bstep (se 1 (by rfl) ⟨4619303, by rfl⟩ : syracuseStep 6159071 = 9238607) B9238607
theorem B35035895 : Blo 1279958 35035895 := bstep (se 1 (by rfl) ⟨26276921, by rfl⟩ : syracuseStep 35035895 = 52553843) B52553843
theorem B7297883 : Blo 1279958 7297883 := bstep (se 1 (by rfl) ⟨5473412, by rfl⟩ : syracuseStep 7297883 = 10946825) B10946825
theorem B8207401 : Blo 1279958 8207401 := bstep (se 2 (by rfl) ⟨3077775, by rfl⟩ : syracuseStep 8207401 = 6155551) B6155551
theorem B7789625 : Blo 1279958 7789625 := bstep (se 2 (by rfl) ⟨2921109, by rfl⟩ : syracuseStep 7789625 = 5842219) B5842219
theorem B1621063 : Blo 1279958 1621063 := bstep (se 1 (by rfl) ⟨1215797, by rfl⟩ : syracuseStep 1621063 = 2431595) B2431595
theorem B4324481 : Blo 1279958 4324481 := bstep (se 2 (by rfl) ⟨1621680, by rfl⟩ : syracuseStep 4324481 = 3243361) B3243361
theorem B4324535 : Blo 1279958 4324535 := bstep (se 1 (by rfl) ⟨3243401, by rfl⟩ : syracuseStep 4324535 = 6486803) B6486803
theorem B6487289 : Blo 1279958 6487289 := bstep (se 2 (by rfl) ⟨2432733, by rfl⟩ : syracuseStep 6487289 = 4865467) B4865467
theorem B2882825 : Blo 1279958 2882825 := bstep (se 2 (by rfl) ⟨1081059, by rfl⟩ : syracuseStep 2882825 = 2162119) B2162119
theorem B2735527 : Blo 1279958 2735527 := bstep (se 1 (by rfl) ⟨2051645, by rfl⟩ : syracuseStep 2735527 = 4103291) B4103291
theorem B2432423 : Blo 1279958 2432423 := bstep (se 1 (by rfl) ⟨1824317, by rfl⟩ : syracuseStep 2432423 = 3648635) B3648635
theorem B1441255 : Blo 1279958 1441255 := bstep (se 1 (by rfl) ⟨1080941, by rfl⟩ : syracuseStep 1441255 = 2161883) B2161883
theorem B9723401 : Blo 1279958 9723401 := bstep (se 2 (by rfl) ⟨3646275, by rfl⟩ : syracuseStep 9723401 = 7292551) B7292551
theorem B18456275 : Blo 1279958 18456275 := bstep (se 1 (by rfl) ⟨13842206, by rfl⟩ : syracuseStep 18456275 = 27684413) B27684413
theorem B7290593 : Blo 1279958 7290593 := bstep (se 2 (by rfl) ⟨2733972, by rfl⟩ : syracuseStep 7290593 = 5467945) B5467945
theorem B3243847 : Blo 1279958 3243847 := bstep (se 1 (by rfl) ⟨2432885, by rfl⟩ : syracuseStep 3243847 = 4865771) B4865771
theorem B1621883 : Blo 1279958 1621883 := bstep (se 1 (by rfl) ⟨1216412, by rfl⟩ : syracuseStep 1621883 = 2432825) B2432825
theorem B4325291 : Blo 1279958 4325291 := bstep (se 1 (by rfl) ⟨3243968, by rfl⟩ : syracuseStep 4325291 = 6487937) B6487937
theorem B1441759 : Blo 1279958 1441759 := bstep (se 1 (by rfl) ⟨1081319, by rfl⟩ : syracuseStep 1441759 = 2162639) B2162639
theorem B4325561 : Blo 1279958 4325561 := bstep (se 2 (by rfl) ⟨1622085, by rfl⟩ : syracuseStep 4325561 = 3244171) B3244171
theorem B1622207 : Blo 1279958 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B4104407 : Blo 1279958 4104407 := bstep (se 1 (by rfl) ⟨3078305, by rfl⟩ : syracuseStep 4104407 = 6156611) B6156611
theorem B2883833 : Blo 1279958 2883833 := bstep (se 2 (by rfl) ⟨1081437, by rfl⟩ : syracuseStep 2883833 = 2162875) B2162875
theorem B1442047 : Blo 1279958 1442047 := bstep (se 1 (by rfl) ⟨1081535, by rfl⟩ : syracuseStep 1442047 = 2163071) B2163071
theorem B2162983 : Blo 1279958 2162983 := bstep (se 1 (by rfl) ⟨1622237, by rfl⟩ : syracuseStep 2162983 = 3244475) B3244475
theorem B2883887 : Blo 1279958 2883887 := bstep (se 1 (by rfl) ⟨2162915, by rfl⟩ : syracuseStep 2883887 = 4325831) B4325831
theorem B12312947 : Blo 1279958 12312947 := bstep (se 1 (by rfl) ⟨9234710, by rfl⟩ : syracuseStep 12312947 = 18469421) B18469421
theorem B4997629 : Blo 1279958 4997629 := bstep (se 3 (by rfl) ⟨937055, by rfl⟩ : syracuseStep 4997629 = 1874111) B1874111
theorem B2884103 : Blo 1279958 2884103 := bstep (se 1 (by rfl) ⟨2163077, by rfl⟩ : syracuseStep 2884103 = 4326155) B4326155
theorem B4325993 : Blo 1279958 4325993 := bstep (se 2 (by rfl) ⟨1622247, by rfl⟩ : syracuseStep 4325993 = 3244495) B3244495
theorem B12313255 : Blo 1279958 12313255 := bstep (se 1 (by rfl) ⟨9234941, by rfl⟩ : syracuseStep 12313255 = 18469883) B18469883
theorem B2884283 : Blo 1279958 2884283 := bstep (se 1 (by rfl) ⟨2163212, by rfl⟩ : syracuseStep 2884283 = 4326425) B4326425
theorem B14598953 : Blo 1279958 14598953 := bstep (se 2 (by rfl) ⟨5474607, by rfl⟩ : syracuseStep 14598953 = 10949215) B10949215
theorem B5473277 : Blo 1279958 5473277 := bstep (se 3 (by rfl) ⟨1026239, by rfl⟩ : syracuseStep 5473277 = 2052479) B2052479
theorem B8201843 : Blo 1279958 8201843 := bstep (se 1 (by rfl) ⟨6151382, by rfl⟩ : syracuseStep 8201843 = 12302765) B12302765
theorem B4106047 : Blo 1279958 4106047 := bstep (se 1 (by rfl) ⟨3079535, by rfl⟩ : syracuseStep 4106047 = 6159071) B6159071
theorem B23357263 : Blo 1279958 23357263 := bstep (se 1 (by rfl) ⟨17517947, by rfl⟩ : syracuseStep 23357263 = 35035895) B35035895
theorem B3647369 : Blo 1279958 3647369 := bstep (se 2 (by rfl) ⟨1367763, by rfl⟩ : syracuseStep 3647369 = 2735527) B2735527
theorem B1279967 : Blo 1279958 1279967 := bstep (se 1 (by rfl) ⟨959975, by rfl⟩ : syracuseStep 1279967 = 1919951) B1919951
theorem B1280027 : Blo 1279958 1280027 := bstep (se 1 (by rfl) ⟨960020, by rfl⟩ : syracuseStep 1280027 = 1920041) B1920041
theorem B1280031 : Blo 1279958 1280031 := bstep (se 1 (by rfl) ⟨960023, by rfl⟩ : syracuseStep 1280031 = 1920047) B1920047
theorem B1280047 : Blo 1279958 1280047 := bstep (se 1 (by rfl) ⟨960035, by rfl⟩ : syracuseStep 1280047 = 1920071) B1920071
theorem B9226385 : Blo 1279958 9226385 := bstep (se 2 (by rfl) ⟨3459894, by rfl⟩ : syracuseStep 9226385 = 6919789) B6919789
theorem B1280223 : Blo 1279958 1280223 := bstep (se 1 (by rfl) ⟨960167, by rfl⟩ : syracuseStep 1280223 = 1920335) B1920335
theorem B1280283 : Blo 1279958 1280283 := bstep (se 1 (by rfl) ⟨960212, by rfl⟩ : syracuseStep 1280283 = 1920425) B1920425
theorem B6482267 : Blo 1279958 6482267 := bstep (se 1 (by rfl) ⟨4861700, by rfl⟩ : syracuseStep 6482267 = 9723401) B9723401
theorem B1280383 : Blo 1279958 1280383 := bstep (se 1 (by rfl) ⟨960287, by rfl⟩ : syracuseStep 1280383 = 1920575) B1920575
theorem B4860395 : Blo 1279958 4860395 := bstep (se 1 (by rfl) ⟨3645296, by rfl⟩ : syracuseStep 4860395 = 7290593) B7290593
theorem B1280559 : Blo 1279958 1280559 := bstep (se 1 (by rfl) ⟨960419, by rfl⟩ : syracuseStep 1280559 = 1920839) B1920839
theorem B1280615 : Blo 1279958 1280615 := bstep (se 1 (by rfl) ⟨960461, by rfl⟩ : syracuseStep 1280615 = 1920923) B1920923
theorem B5925575 : Blo 1279958 5925575 := bstep (se 1 (by rfl) ⟨4444181, by rfl⟩ : syracuseStep 5925575 = 8888363) B8888363
theorem B133196501 : Blo 1279958 133196501 := bstep (se 7 (by rfl) ⟨1560896, by rfl⟩ : syracuseStep 133196501 = 3121793) B3121793
theorem B1280991 : Blo 1279958 1280991 := bstep (se 1 (by rfl) ⟨960743, by rfl⟩ : syracuseStep 1280991 = 1921487) B1921487
theorem B10947575 : Blo 1279958 10947575 := bstep (se 1 (by rfl) ⟨8210681, by rfl⟩ : syracuseStep 10947575 = 16421363) B16421363
theorem B1281019 : Blo 1279958 1281019 := bstep (se 1 (by rfl) ⟨960764, by rfl⟩ : syracuseStep 1281019 = 1921529) B1921529
theorem B7294009 : Blo 1279958 7294009 := bstep (se 2 (by rfl) ⟨2735253, by rfl⟩ : syracuseStep 7294009 = 5470507) B5470507
theorem B1281087 : Blo 1279958 1281087 := bstep (se 1 (by rfl) ⟨960815, by rfl⟩ : syracuseStep 1281087 = 1921631) B1921631
theorem B50572355 : Blo 1279958 50572355 := bstep (se 1 (by rfl) ⟨37929266, by rfl⟩ : syracuseStep 50572355 = 75858533) B75858533
theorem B1920107 : Blo 1279958 1920107 := bstep (se 1 (by rfl) ⟨1440080, by rfl⟩ : syracuseStep 1920107 = 2880161) B2880161
theorem B1920347 : Blo 1279958 1920347 := bstep (se 1 (by rfl) ⟨1440260, by rfl⟩ : syracuseStep 1920347 = 2880521) B2880521
theorem B1920377 : Blo 1279958 1920377 := bstep (se 2 (by rfl) ⟨720141, by rfl⟩ : syracuseStep 1920377 = 1440283) B1440283
theorem B1920383 : Blo 1279958 1920383 := bstep (se 1 (by rfl) ⟨1440287, by rfl⟩ : syracuseStep 1920383 = 2880575) B2880575
theorem B1281407 : Blo 1279958 1281407 := bstep (se 1 (by rfl) ⟨961055, by rfl⟩ : syracuseStep 1281407 = 1922111) B1922111
theorem B1281435 : Blo 1279958 1281435 := bstep (se 1 (by rfl) ⟨961076, by rfl⟩ : syracuseStep 1281435 = 1922153) B1922153
theorem B4861367 : Blo 1279958 4861367 := bstep (se 1 (by rfl) ⟨3646025, by rfl⟩ : syracuseStep 4861367 = 7292051) B7292051
theorem B1281503 : Blo 1279958 1281503 := bstep (se 1 (by rfl) ⟨961127, by rfl⟩ : syracuseStep 1281503 = 1922255) B1922255
theorem B1281639 : Blo 1279958 1281639 := bstep (se 1 (by rfl) ⟨961229, by rfl⟩ : syracuseStep 1281639 = 1922459) B1922459
theorem B15584939 : Blo 1279958 15584939 := bstep (se 1 (by rfl) ⟨11688704, by rfl⟩ : syracuseStep 15584939 = 23377409) B23377409
theorem B1281787 : Blo 1279958 1281787 := bstep (se 1 (by rfl) ⟨961340, by rfl⟩ : syracuseStep 1281787 = 1922681) B1922681
theorem B1281855 : Blo 1279958 1281855 := bstep (se 1 (by rfl) ⟨961391, by rfl⟩ : syracuseStep 1281855 = 1922783) B1922783
theorem B1822591 : Blo 1279958 1822591 := bstep (se 1 (by rfl) ⟨1366943, by rfl⟩ : syracuseStep 1822591 = 2733887) B2733887
theorem B1281919 : Blo 1279958 1281919 := bstep (se 1 (by rfl) ⟨961439, by rfl⟩ : syracuseStep 1281919 = 1922879) B1922879
theorem B1921007 : Blo 1279958 1921007 := bstep (se 1 (by rfl) ⟨1440755, by rfl⟩ : syracuseStep 1921007 = 2881511) B2881511
theorem B1921019 : Blo 1279958 1921019 := bstep (se 1 (by rfl) ⟨1440764, by rfl⟩ : syracuseStep 1921019 = 2881529) B2881529
theorem B10940467 : Blo 1279958 10940467 := bstep (se 1 (by rfl) ⟨8205350, by rfl⟩ : syracuseStep 10940467 = 16410701) B16410701
theorem B1921079 : Blo 1279958 1921079 := bstep (se 1 (by rfl) ⟨1440809, by rfl⟩ : syracuseStep 1921079 = 2881619) B2881619
theorem B1921127 : Blo 1279958 1921127 := bstep (se 1 (by rfl) ⟨1440845, by rfl⟩ : syracuseStep 1921127 = 2881691) B2881691
theorem B1921199 : Blo 1279958 1921199 := bstep (se 1 (by rfl) ⟨1440899, by rfl⟩ : syracuseStep 1921199 = 2881799) B2881799
theorem B15585479 : Blo 1279958 15585479 := bstep (se 1 (by rfl) ⟨11689109, by rfl⟩ : syracuseStep 15585479 = 23378219) B23378219
theorem B1921403 : Blo 1279958 1921403 := bstep (se 1 (by rfl) ⟨1441052, by rfl⟩ : syracuseStep 1921403 = 2882105) B2882105
theorem B11088353 : Blo 1279958 11088353 := bstep (se 2 (by rfl) ⟨4158132, by rfl⟩ : syracuseStep 11088353 = 8316265) B8316265
theorem B10383859 : Blo 1279958 10383859 := bstep (se 1 (by rfl) ⟨7787894, by rfl⟩ : syracuseStep 10383859 = 15575789) B15575789
theorem B1921673 : Blo 1279958 1921673 := bstep (se 2 (by rfl) ⟨720627, by rfl⟩ : syracuseStep 1921673 = 1441255) B1441255
theorem B2880251 : Blo 1279958 2880251 := bstep (se 1 (by rfl) ⟨2160188, by rfl⟩ : syracuseStep 2880251 = 4320377) B4320377
theorem B1921883 : Blo 1279958 1921883 := bstep (se 1 (by rfl) ⟨1441412, by rfl⟩ : syracuseStep 1921883 = 2882825) B2882825
theorem B17527697 : Blo 1279958 17527697 := bstep (se 2 (by rfl) ⟨6572886, by rfl⟩ : syracuseStep 17527697 = 13145773) B13145773
theorem B2880467 : Blo 1279958 2880467 := bstep (se 1 (by rfl) ⟨2160350, by rfl⟩ : syracuseStep 2880467 = 4320701) B4320701
theorem B3077075 : Blo 1279958 3077075 := bstep (se 1 (by rfl) ⟨2307806, by rfl⟩ : syracuseStep 3077075 = 4615613) B4615613
theorem B55358437 : Blo 1279958 55358437 := bstep (se 4 (by rfl) ⟨5189853, by rfl⟩ : syracuseStep 55358437 = 10379707) B10379707
theorem B3241043 : Blo 1279958 3241043 := bstep (se 1 (by rfl) ⟨2430782, by rfl⟩ : syracuseStep 3241043 = 4861565) B4861565
theorem B4617299 : Blo 1279958 4617299 := bstep (se 1 (by rfl) ⟨3462974, by rfl⟩ : syracuseStep 4617299 = 6925949) B6925949
theorem B1922345 : Blo 1279958 1922345 := bstep (se 2 (by rfl) ⟨720879, by rfl⟩ : syracuseStep 1922345 = 1441759) B1441759
theorem B2430319 : Blo 1279958 2430319 := bstep (se 1 (by rfl) ⟨1822739, by rfl⟩ : syracuseStep 2430319 = 3645479) B3645479
theorem B2880935 : Blo 1279958 2880935 := bstep (se 1 (by rfl) ⟨2160701, by rfl⟩ : syracuseStep 2880935 = 4321403) B4321403
theorem B1922543 : Blo 1279958 1922543 := bstep (se 1 (by rfl) ⟨1441907, by rfl⟩ : syracuseStep 1922543 = 2883815) B2883815
theorem B2881043 : Blo 1279958 2881043 := bstep (se 1 (by rfl) ⟨2160782, by rfl⟩ : syracuseStep 2881043 = 4321565) B4321565
theorem B2881115 : Blo 1279958 2881115 := bstep (se 1 (by rfl) ⟨2160836, by rfl⟩ : syracuseStep 2881115 = 4321673) B4321673
theorem B2307727 : Blo 1279958 2307727 := bstep (se 1 (by rfl) ⟨1730795, by rfl⟩ : syracuseStep 2307727 = 3461591) B3461591
theorem B4322969 : Blo 1279958 4322969 := bstep (se 2 (by rfl) ⟨1621113, by rfl⟩ : syracuseStep 4322969 = 3242227) B3242227
theorem B9729719 : Blo 1279958 9729719 := bstep (se 1 (by rfl) ⟨7297289, by rfl⟩ : syracuseStep 9729719 = 14594579) B14594579
theorem B32831243 : Blo 1279958 32831243 := bstep (se 1 (by rfl) ⟨24623432, by rfl⟩ : syracuseStep 32831243 = 49246865) B49246865
theorem B41580337 : Blo 1279958 41580337 := bstep (se 2 (by rfl) ⟨15592626, by rfl⟩ : syracuseStep 41580337 = 31185253) B31185253
theorem B33281887 : Blo 1279958 33281887 := bstep (se 1 (by rfl) ⟨24961415, by rfl⟩ : syracuseStep 33281887 = 49922831) B49922831
theorem B7296925 : Blo 1279958 7296925 := bstep (se 3 (by rfl) ⟨1368173, by rfl⟩ : syracuseStep 7296925 = 2736347) B2736347
theorem B4864009 : Blo 1279958 4864009 := bstep (se 2 (by rfl) ⟨1824003, by rfl⟩ : syracuseStep 4864009 = 3648007) B3648007
theorem B1538119 : Blo 1279958 1538119 := bstep (se 1 (by rfl) ⟨1153589, by rfl⟩ : syracuseStep 1538119 = 2307179) B2307179
theorem B2160823 : Blo 1279958 2160823 := bstep (se 1 (by rfl) ⟨1620617, by rfl⟩ : syracuseStep 2160823 = 3241235) B3241235
theorem B2881727 : Blo 1279958 2881727 := bstep (se 1 (by rfl) ⟨2161295, by rfl⟩ : syracuseStep 2881727 = 4322591) B4322591
theorem B1825183 : Blo 1279958 1825183 := bstep (se 1 (by rfl) ⟨1368887, by rfl⟩ : syracuseStep 1825183 = 2737775) B2737775
theorem B11688421 : Blo 1279958 11688421 := bstep (se 4 (by rfl) ⟨1095789, by rfl⟩ : syracuseStep 11688421 = 2191579) B2191579
theorem B8206991 : Blo 1279958 8206991 := bstep (se 1 (by rfl) ⟨6155243, by rfl⟩ : syracuseStep 8206991 = 12310487) B12310487
theorem B2308751 : Blo 1279958 2308751 := bstep (se 1 (by rfl) ⟨1731563, by rfl⟩ : syracuseStep 2308751 = 3463127) B3463127
theorem B10943201 : Blo 1279958 10943201 := bstep (se 2 (by rfl) ⟨4103700, by rfl⟩ : syracuseStep 10943201 = 8207401) B8207401
theorem B2161417 : Blo 1279958 2161417 := bstep (se 2 (by rfl) ⟨810531, by rfl⟩ : syracuseStep 2161417 = 1621063) B1621063
theorem B1440679 : Blo 1279958 1440679 := bstep (se 1 (by rfl) ⟨1080509, by rfl⟩ : syracuseStep 1440679 = 2161019) B2161019
theorem B21896243 : Blo 1279958 21896243 := bstep (se 1 (by rfl) ⟨16422182, by rfl⟩ : syracuseStep 21896243 = 32844365) B32844365
theorem B1440859 : Blo 1279958 1440859 := bstep (se 1 (by rfl) ⟨1080644, by rfl⟩ : syracuseStep 1440859 = 2161289) B2161289
theorem B4865255 : Blo 1279958 4865255 := bstep (se 1 (by rfl) ⟨3648941, by rfl⟩ : syracuseStep 4865255 = 7297883) B7297883
theorem B2465095 : Blo 1279958 2465095 := bstep (se 1 (by rfl) ⟨1848821, by rfl⟩ : syracuseStep 2465095 = 3697643) B3697643
theorem B5193083 : Blo 1279958 5193083 := bstep (se 1 (by rfl) ⟨3894812, by rfl⟩ : syracuseStep 5193083 = 7789625) B7789625
theorem B2882987 : Blo 1279958 2882987 := bstep (se 1 (by rfl) ⟨2162240, by rfl⟩ : syracuseStep 2882987 = 4324481) B4324481
theorem B2883023 : Blo 1279958 2883023 := bstep (se 1 (by rfl) ⟨2162267, by rfl⟩ : syracuseStep 2883023 = 4324535) B4324535
theorem B4324859 : Blo 1279958 4324859 := bstep (se 1 (by rfl) ⟨3243644, by rfl⟩ : syracuseStep 4324859 = 6487289) B6487289
theorem B1621615 : Blo 1279958 1621615 := bstep (se 1 (by rfl) ⟨1216211, by rfl⟩ : syracuseStep 1621615 = 2432423) B2432423
theorem B216293003 : Blo 1279958 216293003 := bstep (se 1 (by rfl) ⟨162219752, by rfl⟩ : syracuseStep 216293003 = 324439505) B324439505
theorem B4325021 : Blo 1279958 4325021 := bstep (se 3 (by rfl) ⟨810941, by rfl⟩ : syracuseStep 4325021 = 1621883) B1621883
theorem B2498215 : Blo 1279958 2498215 := bstep (se 1 (by rfl) ⟨1873661, by rfl⟩ : syracuseStep 2498215 = 3747323) B3747323
theorem B4325129 : Blo 1279958 4325129 := bstep (se 2 (by rfl) ⟨1621923, by rfl⟩ : syracuseStep 4325129 = 3243847) B3243847
theorem B10936093 : Blo 1279958 10936093 := bstep (se 3 (by rfl) ⟨2050517, by rfl⟩ : syracuseStep 10936093 = 4101035) B4101035
theorem B12304183 : Blo 1279958 12304183 := bstep (se 1 (by rfl) ⟨9228137, by rfl⟩ : syracuseStep 12304183 = 18456275) B18456275
theorem B2883527 : Blo 1279958 2883527 := bstep (se 1 (by rfl) ⟨2162645, by rfl⟩ : syracuseStep 2883527 = 4325291) B4325291
theorem B2883707 : Blo 1279958 2883707 := bstep (se 1 (by rfl) ⟨2162780, by rfl⟩ : syracuseStep 2883707 = 4325561) B4325561
theorem B2736271 : Blo 1279958 2736271 := bstep (se 1 (by rfl) ⟨2052203, by rfl⟩ : syracuseStep 2736271 = 4104407) B4104407
theorem B8208631 : Blo 1279958 8208631 := bstep (se 1 (by rfl) ⟨6156473, by rfl⟩ : syracuseStep 8208631 = 12312947) B12312947
theorem B2883977 : Blo 1279958 2883977 := bstep (se 2 (by rfl) ⟨1081491, by rfl⟩ : syracuseStep 2883977 = 2162983) B2162983
theorem B2883995 : Blo 1279958 2883995 := bstep (se 1 (by rfl) ⟨2162996, by rfl⟩ : syracuseStep 2883995 = 4325993) B4325993
theorem B4325885 : Blo 1279958 4325885 := bstep (se 3 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 4325885 = 1622207) B1622207
theorem B9732635 : Blo 1279958 9732635 := bstep (se 1 (by rfl) ⟨7299476, by rfl⟩ : syracuseStep 9732635 = 14598953) B14598953
theorem B2433577 : Blo 1279958 2433577 := bstep (se 2 (by rfl) ⟨912591, by rfl⟩ : syracuseStep 2433577 = 1825183) B1825183
theorem B16417673 : Blo 1279958 16417673 := bstep (se 2 (by rfl) ⟨6156627, by rfl⟩ : syracuseStep 16417673 = 12313255) B12313255
theorem B73811249 : Blo 1279958 73811249 := bstep (se 2 (by rfl) ⟨27679218, by rfl⟩ : syracuseStep 73811249 = 55358437) B55358437
theorem B9725345 : Blo 1279958 9725345 := bstep (se 2 (by rfl) ⟨3647004, by rfl⟩ : syracuseStep 9725345 = 7294009) B7294009
theorem B3286793 : Blo 1279958 3286793 := bstep (se 2 (by rfl) ⟨1232547, by rfl⟩ : syracuseStep 3286793 = 2465095) B2465095
theorem B3950383 : Blo 1279958 3950383 := bstep (se 1 (by rfl) ⟨2962787, by rfl⟩ : syracuseStep 3950383 = 5925575) B5925575
theorem B1280071 : Blo 1279958 1280071 := bstep (se 1 (by rfl) ⟨960053, by rfl⟩ : syracuseStep 1280071 = 1920107) B1920107
theorem B1280231 : Blo 1279958 1280231 := bstep (se 1 (by rfl) ⟨960173, by rfl⟩ : syracuseStep 1280231 = 1920347) B1920347
theorem B1280251 : Blo 1279958 1280251 := bstep (se 1 (by rfl) ⟨960188, by rfl⟩ : syracuseStep 1280251 = 1920377) B1920377
theorem B1280255 : Blo 1279958 1280255 := bstep (se 1 (by rfl) ⟨960191, by rfl⟩ : syracuseStep 1280255 = 1920383) B1920383
theorem B9726317 : Blo 1279958 9726317 := bstep (se 3 (by rfl) ⟨1823684, by rfl⟩ : syracuseStep 9726317 = 3647369) B3647369
theorem B5474729 : Blo 1279958 5474729 := bstep (se 2 (by rfl) ⟨2053023, by rfl⟩ : syracuseStep 5474729 = 4106047) B4106047
theorem B10389959 : Blo 1279958 10389959 := bstep (se 1 (by rfl) ⟨7792469, by rfl⟩ : syracuseStep 10389959 = 15584939) B15584939
theorem B55380581 : Blo 1279958 55380581 := bstep (se 4 (by rfl) ⟨5191929, by rfl⟩ : syracuseStep 55380581 = 10383859) B10383859
theorem B1280671 : Blo 1279958 1280671 := bstep (se 1 (by rfl) ⟨960503, by rfl⟩ : syracuseStep 1280671 = 1921007) B1921007
theorem B1280679 : Blo 1279958 1280679 := bstep (se 1 (by rfl) ⟨960509, by rfl⟩ : syracuseStep 1280679 = 1921019) B1921019
theorem B1280719 : Blo 1279958 1280719 := bstep (se 1 (by rfl) ⟨960539, by rfl⟩ : syracuseStep 1280719 = 1921079) B1921079
theorem B1280751 : Blo 1279958 1280751 := bstep (se 1 (by rfl) ⟨960563, by rfl⟩ : syracuseStep 1280751 = 1921127) B1921127
theorem B1280799 : Blo 1279958 1280799 := bstep (se 1 (by rfl) ⟨960599, by rfl⟩ : syracuseStep 1280799 = 1921199) B1921199
theorem B10390319 : Blo 1279958 10390319 := bstep (se 1 (by rfl) ⟨7792739, by rfl⟩ : syracuseStep 10390319 = 15585479) B15585479
theorem B134859613 : Blo 1279958 134859613 := bstep (se 3 (by rfl) ⟨25286177, by rfl⟩ : syracuseStep 134859613 = 50572355) B50572355
theorem B1280935 : Blo 1279958 1280935 := bstep (se 1 (by rfl) ⟨960701, by rfl⟩ : syracuseStep 1280935 = 1921403) B1921403
theorem B7392235 : Blo 1279958 7392235 := bstep (se 1 (by rfl) ⟨5544176, by rfl⟩ : syracuseStep 7392235 = 11088353) B11088353
theorem B8203301 : Blo 1279958 8203301 := bstep (se 4 (by rfl) ⟨769059, by rfl⟩ : syracuseStep 8203301 = 1538119) B1538119
theorem B1281115 : Blo 1279958 1281115 := bstep (se 1 (by rfl) ⟨960836, by rfl⟩ : syracuseStep 1281115 = 1921673) B1921673
theorem B1920167 : Blo 1279958 1920167 := bstep (se 1 (by rfl) ⟨1440125, by rfl⟩ : syracuseStep 1920167 = 2880251) B2880251
theorem B1281255 : Blo 1279958 1281255 := bstep (se 1 (by rfl) ⟨960941, by rfl⟩ : syracuseStep 1281255 = 1921883) B1921883
theorem B11685131 : Blo 1279958 11685131 := bstep (se 1 (by rfl) ⟨8763848, by rfl⟩ : syracuseStep 11685131 = 17527697) B17527697
theorem B15584561 : Blo 1279958 15584561 := bstep (se 2 (by rfl) ⟨5844210, by rfl⟩ : syracuseStep 15584561 = 11688421) B11688421
theorem B1920311 : Blo 1279958 1920311 := bstep (se 1 (by rfl) ⟨1440233, by rfl⟩ : syracuseStep 1920311 = 2880467) B2880467
theorem B6663505 : Blo 1279958 6663505 := bstep (se 2 (by rfl) ⟨2498814, by rfl⟩ : syracuseStep 6663505 = 4997629) B4997629
theorem B3648851 : Blo 1279958 3648851 := bstep (se 1 (by rfl) ⟨2736638, by rfl⟩ : syracuseStep 3648851 = 5473277) B5473277
theorem B1281563 : Blo 1279958 1281563 := bstep (se 1 (by rfl) ⟨961172, by rfl⟩ : syracuseStep 1281563 = 1922345) B1922345
theorem B1920623 : Blo 1279958 1920623 := bstep (se 1 (by rfl) ⟨1440467, by rfl⟩ : syracuseStep 1920623 = 2880935) B2880935
theorem B13848221 : Blo 1279958 13848221 := bstep (se 3 (by rfl) ⟨2596541, by rfl⟩ : syracuseStep 13848221 = 5193083) B5193083
theorem B1281695 : Blo 1279958 1281695 := bstep (se 1 (by rfl) ⟨961271, by rfl⟩ : syracuseStep 1281695 = 1922543) B1922543
theorem B1920695 : Blo 1279958 1920695 := bstep (se 1 (by rfl) ⟨1440521, by rfl⟩ : syracuseStep 1920695 = 2881043) B2881043
theorem B1920743 : Blo 1279958 1920743 := bstep (se 1 (by rfl) ⟨1440557, by rfl⟩ : syracuseStep 1920743 = 2881115) B2881115
theorem B5467895 : Blo 1279958 5467895 := bstep (se 1 (by rfl) ⟨4100921, by rfl⟩ : syracuseStep 5467895 = 8201843) B8201843
theorem B1920905 : Blo 1279958 1920905 := bstep (se 2 (by rfl) ⟨720339, by rfl⟩ : syracuseStep 1920905 = 1440679) B1440679
theorem B1921145 : Blo 1279958 1921145 := bstep (se 2 (by rfl) ⟨720429, by rfl⟩ : syracuseStep 1921145 = 1440859) B1440859
theorem B1921151 : Blo 1279958 1921151 := bstep (se 1 (by rfl) ⟨1440863, by rfl⟩ : syracuseStep 1921151 = 2881727) B2881727
theorem B4321511 : Blo 1279958 4321511 := bstep (se 1 (by rfl) ⟨3241133, by rfl⟩ : syracuseStep 4321511 = 6482267) B6482267
theorem B3240263 : Blo 1279958 3240263 := bstep (se 1 (by rfl) ⟨2430197, by rfl⟩ : syracuseStep 3240263 = 4860395) B4860395
theorem B88797667 : Blo 1279958 88797667 := bstep (se 1 (by rfl) ⟨66598250, by rfl⟩ : syracuseStep 88797667 = 133196501) B133196501
theorem B3240425 : Blo 1279958 3240425 := bstep (se 2 (by rfl) ⟨1215159, by rfl⟩ : syracuseStep 3240425 = 2430319) B2430319
theorem B7295467 : Blo 1279958 7295467 := bstep (se 1 (by rfl) ⟨5471600, by rfl⟩ : syracuseStep 7295467 = 10943201) B10943201
theorem B9720485 : Blo 1279958 9720485 := bstep (se 4 (by rfl) ⟨911295, by rfl⟩ : syracuseStep 9720485 = 1822591) B1822591
theorem B3076969 : Blo 1279958 3076969 := bstep (se 2 (by rfl) ⟨1153863, by rfl⟩ : syracuseStep 3076969 = 2307727) B2307727
theorem B3330953 : Blo 1279958 3330953 := bstep (se 2 (by rfl) ⟨1249107, by rfl⟩ : syracuseStep 3330953 = 2498215) B2498215
theorem B1921991 : Blo 1279958 1921991 := bstep (se 1 (by rfl) ⟨1441493, by rfl⟩ : syracuseStep 1921991 = 2882987) B2882987
theorem B3240911 : Blo 1279958 3240911 := bstep (se 1 (by rfl) ⟨2430683, by rfl⟩ : syracuseStep 3240911 = 4861367) B4861367
theorem B1922015 : Blo 1279958 1922015 := bstep (se 1 (by rfl) ⟨1441511, by rfl⟩ : syracuseStep 1922015 = 2883023) B2883023
theorem B55440449 : Blo 1279958 55440449 := bstep (se 2 (by rfl) ⟨20790168, by rfl⟩ : syracuseStep 55440449 = 41580337) B41580337
theorem B16405577 : Blo 1279958 16405577 := bstep (se 2 (by rfl) ⟨6152091, by rfl⟩ : syracuseStep 16405577 = 12304183) B12304183
theorem B31143017 : Blo 1279958 31143017 := bstep (se 2 (by rfl) ⟨11678631, by rfl⟩ : syracuseStep 31143017 = 23357263) B23357263
theorem B9729233 : Blo 1279958 9729233 := bstep (se 2 (by rfl) ⟨3648462, by rfl⟩ : syracuseStep 9729233 = 7296925) B7296925
theorem B8205533 : Blo 1279958 8205533 := bstep (se 3 (by rfl) ⟨1538537, by rfl⟩ : syracuseStep 8205533 = 3077075) B3077075
theorem B1922351 : Blo 1279958 1922351 := bstep (se 1 (by rfl) ⟨1441763, by rfl⟩ : syracuseStep 1922351 = 2883527) B2883527
theorem B6485345 : Blo 1279958 6485345 := bstep (se 2 (by rfl) ⟨2432004, by rfl⟩ : syracuseStep 6485345 = 4864009) B4864009
theorem B14587289 : Blo 1279958 14587289 := bstep (se 2 (by rfl) ⟨5470233, by rfl⟩ : syracuseStep 14587289 = 10940467) B10940467
theorem B1922555 : Blo 1279958 1922555 := bstep (se 1 (by rfl) ⟨1441916, by rfl⟩ : syracuseStep 1922555 = 2883833) B2883833
theorem B1922591 : Blo 1279958 1922591 := bstep (se 1 (by rfl) ⟨1441943, by rfl⟩ : syracuseStep 1922591 = 2883887) B2883887
theorem B2881097 : Blo 1279958 2881097 := bstep (se 2 (by rfl) ⟨1080411, by rfl⟩ : syracuseStep 2881097 = 2160823) B2160823
theorem B1922729 : Blo 1279958 1922729 := bstep (se 2 (by rfl) ⟨721023, by rfl⟩ : syracuseStep 1922729 = 1442047) B1442047
theorem B1922735 : Blo 1279958 1922735 := bstep (se 1 (by rfl) ⟨1442051, by rfl⟩ : syracuseStep 1922735 = 2884103) B2884103
theorem B1922855 : Blo 1279958 1922855 := bstep (se 1 (by rfl) ⟨1442141, by rfl⟩ : syracuseStep 1922855 = 2884283) B2884283
theorem B2160695 : Blo 1279958 2160695 := bstep (se 1 (by rfl) ⟨1620521, by rfl⟩ : syracuseStep 2160695 = 3241043) B3241043
theorem B3078199 : Blo 1279958 3078199 := bstep (se 1 (by rfl) ⟨2308649, by rfl⟩ : syracuseStep 3078199 = 4617299) B4617299
theorem B2881889 : Blo 1279958 2881889 := bstep (se 2 (by rfl) ⟨1080708, by rfl⟩ : syracuseStep 2881889 = 2161417) B2161417
theorem B2881979 : Blo 1279958 2881979 := bstep (se 1 (by rfl) ⟨2161484, by rfl⟩ : syracuseStep 2881979 = 4322969) B4322969
theorem B6486479 : Blo 1279958 6486479 := bstep (se 1 (by rfl) ⟨4864859, by rfl⟩ : syracuseStep 6486479 = 9729719) B9729719
theorem B21887495 : Blo 1279958 21887495 := bstep (se 1 (by rfl) ⟨16415621, by rfl⟩ : syracuseStep 21887495 = 32831243) B32831243
theorem B6150923 : Blo 1279958 6150923 := bstep (se 1 (by rfl) ⟨4613192, by rfl⟩ : syracuseStep 6150923 = 9226385) B9226385
theorem B5471327 : Blo 1279958 5471327 := bstep (se 1 (by rfl) ⟨4103495, by rfl⟩ : syracuseStep 5471327 = 8206991) B8206991
theorem B1539167 : Blo 1279958 1539167 := bstep (se 1 (by rfl) ⟨1154375, by rfl⟩ : syracuseStep 1539167 = 2308751) B2308751
theorem B7298383 : Blo 1279958 7298383 := bstep (se 1 (by rfl) ⟨5473787, by rfl⟩ : syracuseStep 7298383 = 10947575) B10947575
theorem B14597495 : Blo 1279958 14597495 := bstep (se 1 (by rfl) ⟨10948121, by rfl⟩ : syracuseStep 14597495 = 21896243) B21896243
theorem B2162153 : Blo 1279958 2162153 := bstep (se 2 (by rfl) ⟨810807, by rfl⟩ : syracuseStep 2162153 = 1621615) B1621615
theorem B3243503 : Blo 1279958 3243503 := bstep (se 1 (by rfl) ⟨2432627, by rfl⟩ : syracuseStep 3243503 = 4865255) B4865255
theorem B2883239 : Blo 1279958 2883239 := bstep (se 1 (by rfl) ⟨2162429, by rfl⟩ : syracuseStep 2883239 = 4324859) B4324859
theorem B14581457 : Blo 1279958 14581457 := bstep (se 2 (by rfl) ⟨5468046, by rfl⟩ : syracuseStep 14581457 = 10936093) B10936093
theorem B144195335 : Blo 1279958 144195335 := bstep (se 1 (by rfl) ⟨108146501, by rfl⟩ : syracuseStep 144195335 = 216293003) B216293003
theorem B2883347 : Blo 1279958 2883347 := bstep (se 1 (by rfl) ⟨2162510, by rfl⟩ : syracuseStep 2883347 = 4325021) B4325021
theorem B44375849 : Blo 1279958 44375849 := bstep (se 2 (by rfl) ⟨16640943, by rfl⟩ : syracuseStep 44375849 = 33281887) B33281887
theorem B2883419 : Blo 1279958 2883419 := bstep (se 1 (by rfl) ⟨2162564, by rfl⟩ : syracuseStep 2883419 = 4325129) B4325129
theorem B4104265 : Blo 1279958 4104265 := bstep (se 2 (by rfl) ⟨1539099, by rfl⟩ : syracuseStep 4104265 = 3078199) B3078199
theorem B14590205 : Blo 1279958 14590205 := bstep (se 3 (by rfl) ⟨2735663, by rfl⟩ : syracuseStep 14590205 = 5471327) B5471327
theorem B4104445 : Blo 1279958 4104445 := bstep (se 3 (by rfl) ⟨769583, by rfl⟩ : syracuseStep 4104445 = 1539167) B1539167
theorem B10944841 : Blo 1279958 10944841 := bstep (se 2 (by rfl) ⟨4104315, by rfl⟩ : syracuseStep 10944841 = 8208631) B8208631
theorem B2883923 : Blo 1279958 2883923 := bstep (se 1 (by rfl) ⟨2162942, by rfl⟩ : syracuseStep 2883923 = 4325885) B4325885
theorem B6488423 : Blo 1279958 6488423 := bstep (se 1 (by rfl) ⟨4866317, by rfl⟩ : syracuseStep 6488423 = 9732635) B9732635
theorem B6480323 : Blo 1279958 6480323 := bstep (se 1 (by rfl) ⟨4860242, by rfl⟩ : syracuseStep 6480323 = 9720485) B9720485
theorem B2220635 : Blo 1279958 2220635 := bstep (se 1 (by rfl) ⟨1665476, by rfl⟩ : syracuseStep 2220635 = 3330953) B3330953
theorem B10945115 : Blo 1279958 10945115 := bstep (se 1 (by rfl) ⟨8208836, by rfl⟩ : syracuseStep 10945115 = 16417673) B16417673
theorem B10937051 : Blo 1279958 10937051 := bstep (se 1 (by rfl) ⟨8202788, by rfl⟩ : syracuseStep 10937051 = 16405577) B16405577
theorem B3244769 : Blo 1279958 3244769 := bstep (se 2 (by rfl) ⟨1216788, by rfl⟩ : syracuseStep 3244769 = 2433577) B2433577
theorem B9724859 : Blo 1279958 9724859 := bstep (se 1 (by rfl) ⟨7293644, by rfl⟩ : syracuseStep 9724859 = 14587289) B14587289
theorem B9856313 : Blo 1279958 9856313 := bstep (se 2 (by rfl) ⟨3696117, by rfl⟩ : syracuseStep 9856313 = 7392235) B7392235
theorem B14591663 : Blo 1279958 14591663 := bstep (se 1 (by rfl) ⟨10943747, by rfl⟩ : syracuseStep 14591663 = 21887495) B21887495
theorem B1280111 : Blo 1279958 1280111 := bstep (se 1 (by rfl) ⟨960083, by rfl⟩ : syracuseStep 1280111 = 1920167) B1920167
theorem B10389707 : Blo 1279958 10389707 := bstep (se 1 (by rfl) ⟨7792280, by rfl⟩ : syracuseStep 10389707 = 15584561) B15584561
theorem B1280207 : Blo 1279958 1280207 := bstep (se 1 (by rfl) ⟨960155, by rfl⟩ : syracuseStep 1280207 = 1920311) B1920311
theorem B1280415 : Blo 1279958 1280415 := bstep (se 1 (by rfl) ⟨960311, by rfl⟩ : syracuseStep 1280415 = 1920623) B1920623
theorem B1280463 : Blo 1279958 1280463 := bstep (se 1 (by rfl) ⟨960347, by rfl⟩ : syracuseStep 1280463 = 1920695) B1920695
theorem B1280495 : Blo 1279958 1280495 := bstep (se 1 (by rfl) ⟨960371, by rfl⟩ : syracuseStep 1280495 = 1920743) B1920743
theorem B29583899 : Blo 1279958 29583899 := bstep (se 1 (by rfl) ⟨22187924, by rfl⟩ : syracuseStep 29583899 = 44375849) B44375849
theorem B1280603 : Blo 1279958 1280603 := bstep (se 1 (by rfl) ⟨960452, by rfl⟩ : syracuseStep 1280603 = 1920905) B1920905
theorem B1280763 : Blo 1279958 1280763 := bstep (se 1 (by rfl) ⟨960572, by rfl⟩ : syracuseStep 1280763 = 1921145) B1921145
theorem B1280767 : Blo 1279958 1280767 := bstep (se 1 (by rfl) ⟨960575, by rfl⟩ : syracuseStep 1280767 = 1921151) B1921151
theorem B3648361 : Blo 1279958 3648361 := bstep (se 2 (by rfl) ⟨1368135, by rfl⟩ : syracuseStep 3648361 = 2736271) B2736271
theorem B1281327 : Blo 1279958 1281327 := bstep (se 1 (by rfl) ⟨960995, by rfl⟩ : syracuseStep 1281327 = 1921991) B1921991
theorem B9727289 : Blo 1279958 9727289 := bstep (se 2 (by rfl) ⟨3647733, by rfl⟩ : syracuseStep 9727289 = 7295467) B7295467
theorem B1281343 : Blo 1279958 1281343 := bstep (se 1 (by rfl) ⟨961007, by rfl⟩ : syracuseStep 1281343 = 1922015) B1922015
theorem B20762011 : Blo 1279958 20762011 := bstep (se 1 (by rfl) ⟨15571508, by rfl⟩ : syracuseStep 20762011 = 31143017) B31143017
theorem B1281567 : Blo 1279958 1281567 := bstep (se 1 (by rfl) ⟨961175, by rfl⟩ : syracuseStep 1281567 = 1922351) B1922351
theorem B6483563 : Blo 1279958 6483563 := bstep (se 1 (by rfl) ⟨4862672, by rfl⟩ : syracuseStep 6483563 = 9725345) B9725345
theorem B1281703 : Blo 1279958 1281703 := bstep (se 1 (by rfl) ⟨961277, by rfl⟩ : syracuseStep 1281703 = 1922555) B1922555
theorem B1281727 : Blo 1279958 1281727 := bstep (se 1 (by rfl) ⟨961295, by rfl⟩ : syracuseStep 1281727 = 1922591) B1922591
theorem B1920731 : Blo 1279958 1920731 := bstep (se 1 (by rfl) ⟨1440548, by rfl⟩ : syracuseStep 1920731 = 2881097) B2881097
theorem B1281819 : Blo 1279958 1281819 := bstep (se 1 (by rfl) ⟨961364, by rfl⟩ : syracuseStep 1281819 = 1922729) B1922729
theorem B1281823 : Blo 1279958 1281823 := bstep (se 1 (by rfl) ⟨961367, by rfl⟩ : syracuseStep 1281823 = 1922735) B1922735
theorem B2191195 : Blo 1279958 2191195 := bstep (se 1 (by rfl) ⟨1643396, by rfl⟩ : syracuseStep 2191195 = 3286793) B3286793
theorem B1281903 : Blo 1279958 1281903 := bstep (se 1 (by rfl) ⟨961427, by rfl⟩ : syracuseStep 1281903 = 1922855) B1922855
theorem B1921259 : Blo 1279958 1921259 := bstep (se 1 (by rfl) ⟨1440944, by rfl⟩ : syracuseStep 1921259 = 2881889) B2881889
theorem B6484211 : Blo 1279958 6484211 := bstep (se 1 (by rfl) ⟨4863158, by rfl⟩ : syracuseStep 6484211 = 9726317) B9726317
theorem B3649819 : Blo 1279958 3649819 := bstep (se 1 (by rfl) ⟨2737364, by rfl⟩ : syracuseStep 3649819 = 5474729) B5474729
theorem B1921319 : Blo 1279958 1921319 := bstep (se 1 (by rfl) ⟨1440989, by rfl⟩ : syracuseStep 1921319 = 2881979) B2881979
theorem B6926639 : Blo 1279958 6926639 := bstep (se 1 (by rfl) ⟨5194979, by rfl⟩ : syracuseStep 6926639 = 10389959) B10389959
theorem B8884673 : Blo 1279958 8884673 := bstep (se 2 (by rfl) ⟨3331752, by rfl⟩ : syracuseStep 8884673 = 6663505) B6663505
theorem B4100615 : Blo 1279958 4100615 := bstep (se 1 (by rfl) ⟨3075461, by rfl⟩ : syracuseStep 4100615 = 6150923) B6150923
theorem B6926879 : Blo 1279958 6926879 := bstep (se 1 (by rfl) ⟨5195159, by rfl⟩ : syracuseStep 6926879 = 10390319) B10390319
theorem B5468867 : Blo 1279958 5468867 := bstep (se 1 (by rfl) ⟨4101650, by rfl⟩ : syracuseStep 5468867 = 8203301) B8203301
theorem B1922159 : Blo 1279958 1922159 := bstep (se 1 (by rfl) ⟨1441619, by rfl⟩ : syracuseStep 1922159 = 2883239) B2883239
theorem B9720971 : Blo 1279958 9720971 := bstep (se 1 (by rfl) ⟨7290728, by rfl⟩ : syracuseStep 9720971 = 14581457) B14581457
theorem B96130223 : Blo 1279958 96130223 := bstep (se 1 (by rfl) ⟨72097667, by rfl⟩ : syracuseStep 96130223 = 144195335) B144195335
theorem B1922231 : Blo 1279958 1922231 := bstep (se 1 (by rfl) ⟨1441673, by rfl⟩ : syracuseStep 1922231 = 2883347) B2883347
theorem B1922279 : Blo 1279958 1922279 := bstep (se 1 (by rfl) ⟨1441709, by rfl⟩ : syracuseStep 1922279 = 2883419) B2883419
theorem B1922471 : Blo 1279958 1922471 := bstep (se 1 (by rfl) ⟨1441853, by rfl⟩ : syracuseStep 1922471 = 2883707) B2883707
theorem B2881007 : Blo 1279958 2881007 := bstep (se 1 (by rfl) ⟨2160755, by rfl⟩ : syracuseStep 2881007 = 4321511) B4321511
theorem B2160175 : Blo 1279958 2160175 := bstep (se 1 (by rfl) ⟨1620131, by rfl⟩ : syracuseStep 2160175 = 3240263) B3240263
theorem B1922651 : Blo 1279958 1922651 := bstep (se 1 (by rfl) ⟨1441988, by rfl⟩ : syracuseStep 1922651 = 2883977) B2883977
theorem B1922663 : Blo 1279958 1922663 := bstep (se 1 (by rfl) ⟨1441997, by rfl⟩ : syracuseStep 1922663 = 2883995) B2883995
theorem B2160283 : Blo 1279958 2160283 := bstep (se 1 (by rfl) ⟨1620212, by rfl⟩ : syracuseStep 2160283 = 3240425) B3240425
theorem B118396889 : Blo 1279958 118396889 := bstep (se 2 (by rfl) ⟨44398833, by rfl⟩ : syracuseStep 118396889 = 88797667) B88797667
theorem B2160607 : Blo 1279958 2160607 := bstep (se 1 (by rfl) ⟨1620455, by rfl⟩ : syracuseStep 2160607 = 3240911) B3240911
theorem B36960299 : Blo 1279958 36960299 := bstep (se 1 (by rfl) ⟨27720224, by rfl⟩ : syracuseStep 36960299 = 55440449) B55440449
theorem B6486155 : Blo 1279958 6486155 := bstep (se 1 (by rfl) ⟨4864616, by rfl⟩ : syracuseStep 6486155 = 9729233) B9729233
theorem B5470355 : Blo 1279958 5470355 := bstep (se 1 (by rfl) ⟨4102766, by rfl⟩ : syracuseStep 5470355 = 8205533) B8205533
theorem B49207499 : Blo 1279958 49207499 := bstep (se 1 (by rfl) ⟨36905624, by rfl⟩ : syracuseStep 49207499 = 73811249) B73811249
theorem B4323563 : Blo 1279958 4323563 := bstep (se 1 (by rfl) ⟨3242672, by rfl⟩ : syracuseStep 4323563 = 6485345) B6485345
theorem B179812817 : Blo 1279958 179812817 := bstep (se 2 (by rfl) ⟨67429806, by rfl⟩ : syracuseStep 179812817 = 134859613) B134859613
theorem B4102625 : Blo 1279958 4102625 := bstep (se 2 (by rfl) ⟨1538484, by rfl⟩ : syracuseStep 4102625 = 3076969) B3076969
theorem B1440463 : Blo 1279958 1440463 := bstep (se 1 (by rfl) ⟨1080347, by rfl⟩ : syracuseStep 1440463 = 2160695) B2160695
theorem B4324319 : Blo 1279958 4324319 := bstep (se 1 (by rfl) ⟨3243239, by rfl⟩ : syracuseStep 4324319 = 6486479) B6486479
theorem B36920387 : Blo 1279958 36920387 := bstep (se 1 (by rfl) ⟨27690290, by rfl⟩ : syracuseStep 36920387 = 55380581) B55380581
theorem B9731177 : Blo 1279958 9731177 := bstep (se 2 (by rfl) ⟨3649191, by rfl⟩ : syracuseStep 9731177 = 7298383) B7298383
theorem B7790087 : Blo 1279958 7790087 := bstep (se 1 (by rfl) ⟨5842565, by rfl⟩ : syracuseStep 7790087 = 11685131) B11685131
theorem B2432567 : Blo 1279958 2432567 := bstep (se 1 (by rfl) ⟨1824425, by rfl⟩ : syracuseStep 2432567 = 3648851) B3648851
theorem B9731663 : Blo 1279958 9731663 := bstep (se 1 (by rfl) ⟨7298747, by rfl⟩ : syracuseStep 9731663 = 14597495) B14597495
theorem B1441435 : Blo 1279958 1441435 := bstep (se 1 (by rfl) ⟨1081076, by rfl⟩ : syracuseStep 1441435 = 2162153) B2162153
theorem B2162335 : Blo 1279958 2162335 := bstep (se 1 (by rfl) ⟨1621751, by rfl⟩ : syracuseStep 2162335 = 3243503) B3243503
theorem B5267177 : Blo 1279958 5267177 := bstep (se 2 (by rfl) ⟨1975191, by rfl⟩ : syracuseStep 5267177 = 3950383) B3950383
theorem B9232147 : Blo 1279958 9232147 := bstep (se 1 (by rfl) ⟨6924110, by rfl⟩ : syracuseStep 9232147 = 13848221) B13848221
theorem B3645263 : Blo 1279958 3645263 := bstep (se 1 (by rfl) ⟨2733947, by rfl⟩ : syracuseStep 3645263 = 5467895) B5467895
theorem B5472353 : Blo 1279958 5472353 := bstep (se 2 (by rfl) ⟨2052132, by rfl⟩ : syracuseStep 5472353 = 4104265) B4104265
theorem B4325615 : Blo 1279958 4325615 := bstep (se 1 (by rfl) ⟨3244211, by rfl⟩ : syracuseStep 4325615 = 6488423) B6488423
theorem B5923115 : Blo 1279958 5923115 := bstep (se 1 (by rfl) ⟨4442336, by rfl⟩ : syracuseStep 5923115 = 8884673) B8884673
theorem B5472593 : Blo 1279958 5472593 := bstep (se 2 (by rfl) ⟨2052222, by rfl⟩ : syracuseStep 5472593 = 4104445) B4104445
theorem B4866425 : Blo 1279958 4866425 := bstep (se 2 (by rfl) ⟨1824909, by rfl⟩ : syracuseStep 4866425 = 3649819) B3649819
theorem B3645911 : Blo 1279958 3645911 := bstep (se 1 (by rfl) ⟨2734433, by rfl⟩ : syracuseStep 3645911 = 5468867) B5468867
theorem B7291367 : Blo 1279958 7291367 := bstep (se 1 (by rfl) ⟨5468525, by rfl⟩ : syracuseStep 7291367 = 10937051) B10937051
theorem B2163179 : Blo 1279958 2163179 := bstep (se 1 (by rfl) ⟨1622384, by rfl⟩ : syracuseStep 2163179 = 3244769) B3244769
theorem B6480647 : Blo 1279958 6480647 := bstep (se 1 (by rfl) ⟨4860485, by rfl⟩ : syracuseStep 6480647 = 9720971) B9720971
theorem B64086815 : Blo 1279958 64086815 := bstep (se 1 (by rfl) ⟨48065111, by rfl⟩ : syracuseStep 64086815 = 96130223) B96130223
theorem B6570875 : Blo 1279958 6570875 := bstep (se 1 (by rfl) ⟨4928156, by rfl⟩ : syracuseStep 6570875 = 9856313) B9856313
theorem B78931259 : Blo 1279958 78931259 := bstep (se 1 (by rfl) ⟨59198444, by rfl⟩ : syracuseStep 78931259 = 118396889) B118396889
theorem B3646903 : Blo 1279958 3646903 := bstep (se 1 (by rfl) ⟨2735177, by rfl⟩ : syracuseStep 3646903 = 5470355) B5470355
theorem B119875211 : Blo 1279958 119875211 := bstep (se 1 (by rfl) ⟨89906408, by rfl⟩ : syracuseStep 119875211 = 179812817) B179812817
theorem B27682681 : Blo 1279958 27682681 := bstep (se 2 (by rfl) ⟨10381005, by rfl⟩ : syracuseStep 27682681 = 20762011) B20762011
theorem B1280487 : Blo 1279958 1280487 := bstep (se 1 (by rfl) ⟨960365, by rfl⟩ : syracuseStep 1280487 = 1920731) B1920731
theorem B1280839 : Blo 1279958 1280839 := bstep (se 1 (by rfl) ⟨960629, by rfl⟩ : syracuseStep 1280839 = 1921259) B1921259
theorem B9726803 : Blo 1279958 9726803 := bstep (se 1 (by rfl) ⟨7295102, by rfl⟩ : syracuseStep 9726803 = 14590205) B14590205
theorem B1280879 : Blo 1279958 1280879 := bstep (se 1 (by rfl) ⟨960659, by rfl⟩ : syracuseStep 1280879 = 1921319) B1921319
theorem B4320215 : Blo 1279958 4320215 := bstep (se 1 (by rfl) ⟨3240161, by rfl⟩ : syracuseStep 4320215 = 6480323) B6480323
theorem B14593121 : Blo 1279958 14593121 := bstep (se 2 (by rfl) ⟨5472420, by rfl⟩ : syracuseStep 14593121 = 10944841) B10944841
theorem B6483239 : Blo 1279958 6483239 := bstep (se 1 (by rfl) ⟨4862429, by rfl⟩ : syracuseStep 6483239 = 9724859) B9724859
theorem B1281439 : Blo 1279958 1281439 := bstep (se 1 (by rfl) ⟨961079, by rfl⟩ : syracuseStep 1281439 = 1922159) B1922159
theorem B1281487 : Blo 1279958 1281487 := bstep (se 1 (by rfl) ⟨961115, by rfl⟩ : syracuseStep 1281487 = 1922231) B1922231
theorem B1281519 : Blo 1279958 1281519 := bstep (se 1 (by rfl) ⟨961139, by rfl⟩ : syracuseStep 1281519 = 1922279) B1922279
theorem B1920617 : Blo 1279958 1920617 := bstep (se 2 (by rfl) ⟨720231, by rfl⟩ : syracuseStep 1920617 = 1440463) B1440463
theorem B1281647 : Blo 1279958 1281647 := bstep (se 1 (by rfl) ⟨961235, by rfl⟩ : syracuseStep 1281647 = 1922471) B1922471
theorem B1920671 : Blo 1279958 1920671 := bstep (se 1 (by rfl) ⟨1440503, by rfl⟩ : syracuseStep 1920671 = 2881007) B2881007
theorem B1281767 : Blo 1279958 1281767 := bstep (se 1 (by rfl) ⟨961325, by rfl⟩ : syracuseStep 1281767 = 1922651) B1922651
theorem B1281775 : Blo 1279958 1281775 := bstep (se 1 (by rfl) ⟨961331, by rfl⟩ : syracuseStep 1281775 = 1922663) B1922663
theorem B9727775 : Blo 1279958 9727775 := bstep (se 1 (by rfl) ⟨7295831, by rfl⟩ : syracuseStep 9727775 = 14591663) B14591663
theorem B32804999 : Blo 1279958 32804999 := bstep (se 1 (by rfl) ⟨24603749, by rfl⟩ : syracuseStep 32804999 = 49207499) B49207499
theorem B6926471 : Blo 1279958 6926471 := bstep (se 1 (by rfl) ⟨5194853, by rfl⟩ : syracuseStep 6926471 = 10389707) B10389707
theorem B19722599 : Blo 1279958 19722599 := bstep (se 1 (by rfl) ⟨14791949, by rfl⟩ : syracuseStep 19722599 = 29583899) B29583899
theorem B24613591 : Blo 1279958 24613591 := bstep (se 1 (by rfl) ⟨18460193, by rfl⟩ : syracuseStep 24613591 = 36920387) B36920387
theorem B2880233 : Blo 1279958 2880233 := bstep (se 2 (by rfl) ⟨1080087, by rfl⟩ : syracuseStep 2880233 = 2160175) B2160175
theorem B2880377 : Blo 1279958 2880377 := bstep (se 2 (by rfl) ⟨1080141, by rfl⟩ : syracuseStep 2880377 = 2160283) B2160283
theorem B1921913 : Blo 1279958 1921913 := bstep (se 2 (by rfl) ⟨720717, by rfl⟩ : syracuseStep 1921913 = 1441435) B1441435
theorem B6484859 : Blo 1279958 6484859 := bstep (se 1 (by rfl) ⟨4863644, by rfl⟩ : syracuseStep 6484859 = 9727289) B9727289
theorem B12309529 : Blo 1279958 12309529 := bstep (se 2 (by rfl) ⟨4616073, by rfl⟩ : syracuseStep 12309529 = 9232147) B9232147
theorem B4322375 : Blo 1279958 4322375 := bstep (se 1 (by rfl) ⟨3241781, by rfl⟩ : syracuseStep 4322375 = 6483563) B6483563
theorem B2921593 : Blo 1279958 2921593 := bstep (se 2 (by rfl) ⟨1095597, by rfl⟩ : syracuseStep 2921593 = 2191195) B2191195
theorem B3511451 : Blo 1279958 3511451 := bstep (se 1 (by rfl) ⟨2633588, by rfl⟩ : syracuseStep 3511451 = 5267177) B5267177
theorem B2430175 : Blo 1279958 2430175 := bstep (se 1 (by rfl) ⟨1822631, by rfl⟩ : syracuseStep 2430175 = 3645263) B3645263
theorem B2880809 : Blo 1279958 2880809 := bstep (se 2 (by rfl) ⟨1080303, by rfl⟩ : syracuseStep 2880809 = 2160607) B2160607
theorem B4322807 : Blo 1279958 4322807 := bstep (se 1 (by rfl) ⟨3242105, by rfl⟩ : syracuseStep 4322807 = 6484211) B6484211
theorem B1922615 : Blo 1279958 1922615 := bstep (se 1 (by rfl) ⟨1441961, by rfl⟩ : syracuseStep 1922615 = 2883923) B2883923
theorem B2733743 : Blo 1279958 2733743 := bstep (se 1 (by rfl) ⟨2050307, by rfl⟩ : syracuseStep 2733743 = 4100615) B4100615
theorem B4617919 : Blo 1279958 4617919 := bstep (se 1 (by rfl) ⟨3463439, by rfl⟩ : syracuseStep 4617919 = 6926879) B6926879
theorem B1480423 : Blo 1279958 1480423 := bstep (se 1 (by rfl) ⟨1110317, by rfl⟩ : syracuseStep 1480423 = 2220635) B2220635
theorem B7296743 : Blo 1279958 7296743 := bstep (se 1 (by rfl) ⟨5472557, by rfl⟩ : syracuseStep 7296743 = 10945115) B10945115
theorem B18471037 : Blo 1279958 18471037 := bstep (se 3 (by rfl) ⟨3463319, by rfl⟩ : syracuseStep 18471037 = 6926639) B6926639
theorem B4864481 : Blo 1279958 4864481 := bstep (se 2 (by rfl) ⟨1824180, by rfl⟩ : syracuseStep 4864481 = 3648361) B3648361
theorem B24640199 : Blo 1279958 24640199 := bstep (se 1 (by rfl) ⟨18480149, by rfl⟩ : syracuseStep 24640199 = 36960299) B36960299
theorem B4324103 : Blo 1279958 4324103 := bstep (se 1 (by rfl) ⟨3243077, by rfl⟩ : syracuseStep 4324103 = 6486155) B6486155
theorem B2882375 : Blo 1279958 2882375 := bstep (se 1 (by rfl) ⟨2161781, by rfl⟩ : syracuseStep 2882375 = 4323563) B4323563
theorem B2735083 : Blo 1279958 2735083 := bstep (se 1 (by rfl) ⟨2051312, by rfl⟩ : syracuseStep 2735083 = 4102625) B4102625
theorem B2882879 : Blo 1279958 2882879 := bstep (se 1 (by rfl) ⟨2162159, by rfl⟩ : syracuseStep 2882879 = 4324319) B4324319
theorem B6487451 : Blo 1279958 6487451 := bstep (se 1 (by rfl) ⟨4865588, by rfl⟩ : syracuseStep 6487451 = 9731177) B9731177
theorem B2883113 : Blo 1279958 2883113 := bstep (se 2 (by rfl) ⟨1081167, by rfl⟩ : syracuseStep 2883113 = 2162335) B2162335
theorem B5193391 : Blo 1279958 5193391 := bstep (se 1 (by rfl) ⟨3895043, by rfl⟩ : syracuseStep 5193391 = 7790087) B7790087
theorem B1621711 : Blo 1279958 1621711 := bstep (se 1 (by rfl) ⟨1216283, by rfl⟩ : syracuseStep 1621711 = 2432567) B2432567
theorem B6487775 : Blo 1279958 6487775 := bstep (se 1 (by rfl) ⟨4865831, by rfl⟩ : syracuseStep 6487775 = 9731663) B9731663
theorem B2883743 : Blo 1279958 2883743 := bstep (se 1 (by rfl) ⟨2162807, by rfl⟩ : syracuseStep 2883743 = 4325615) B4325615
theorem B3948743 : Blo 1279958 3948743 := bstep (se 1 (by rfl) ⟨2961557, by rfl⟩ : syracuseStep 3948743 = 5923115) B5923115
theorem B13148399 : Blo 1279958 13148399 := bstep (se 1 (by rfl) ⟨9861299, by rfl⟩ : syracuseStep 13148399 = 19722599) B19722599
theorem B3244283 : Blo 1279958 3244283 := bstep (se 1 (by rfl) ⟨2433212, by rfl⟩ : syracuseStep 3244283 = 4866425) B4866425
theorem B1442119 : Blo 1279958 1442119 := bstep (se 1 (by rfl) ⟨1081589, by rfl⟩ : syracuseStep 1442119 = 2163179) B2163179
theorem B9363869 : Blo 1279958 9363869 := bstep (se 3 (by rfl) ⟨1755725, by rfl⟩ : syracuseStep 9363869 = 3511451) B3511451
theorem B32818121 : Blo 1279958 32818121 := bstep (se 2 (by rfl) ⟨12306795, by rfl⟩ : syracuseStep 32818121 = 24613591) B24613591
theorem B3646777 : Blo 1279958 3646777 := bstep (se 2 (by rfl) ⟨1367541, by rfl⟩ : syracuseStep 3646777 = 2735083) B2735083
theorem B16426799 : Blo 1279958 16426799 := bstep (se 1 (by rfl) ⟨12320099, by rfl⟩ : syracuseStep 16426799 = 24640199) B24640199
theorem B6924521 : Blo 1279958 6924521 := bstep (se 2 (by rfl) ⟨2596695, by rfl⟩ : syracuseStep 6924521 = 5193391) B5193391
theorem B1280411 : Blo 1279958 1280411 := bstep (se 1 (by rfl) ⟨960308, by rfl⟩ : syracuseStep 1280411 = 1920617) B1920617
theorem B1280447 : Blo 1279958 1280447 := bstep (se 1 (by rfl) ⟨960335, by rfl⟩ : syracuseStep 1280447 = 1920671) B1920671
theorem B3648235 : Blo 1279958 3648235 := bstep (se 1 (by rfl) ⟨2736176, by rfl⟩ : syracuseStep 3648235 = 5472353) B5472353
theorem B24628049 : Blo 1279958 24628049 := bstep (se 2 (by rfl) ⟨9235518, by rfl⟩ : syracuseStep 24628049 = 18471037) B18471037
theorem B3648395 : Blo 1279958 3648395 := bstep (se 1 (by rfl) ⟨2736296, by rfl⟩ : syracuseStep 3648395 = 5472593) B5472593
theorem B4860911 : Blo 1279958 4860911 := bstep (se 1 (by rfl) ⟨3645683, by rfl⟩ : syracuseStep 4860911 = 7291367) B7291367
theorem B1920155 : Blo 1279958 1920155 := bstep (se 1 (by rfl) ⟨1440116, by rfl⟩ : syracuseStep 1920155 = 2880233) B2880233
theorem B4320431 : Blo 1279958 4320431 := bstep (se 1 (by rfl) ⟨3240323, by rfl⟩ : syracuseStep 4320431 = 6480647) B6480647
theorem B1920251 : Blo 1279958 1920251 := bstep (se 1 (by rfl) ⟨1440188, by rfl⟩ : syracuseStep 1920251 = 2880377) B2880377
theorem B1281275 : Blo 1279958 1281275 := bstep (se 1 (by rfl) ⟨960956, by rfl⟩ : syracuseStep 1281275 = 1921913) B1921913
theorem B1920539 : Blo 1279958 1920539 := bstep (se 1 (by rfl) ⟨1440404, by rfl⟩ : syracuseStep 1920539 = 2880809) B2880809
theorem B52620839 : Blo 1279958 52620839 := bstep (se 1 (by rfl) ⟨39465629, by rfl⟩ : syracuseStep 52620839 = 78931259) B78931259
theorem B1281743 : Blo 1279958 1281743 := bstep (se 1 (by rfl) ⟨961307, by rfl⟩ : syracuseStep 1281743 = 1922615) B1922615
theorem B79916807 : Blo 1279958 79916807 := bstep (se 1 (by rfl) ⟨59937605, by rfl⟩ : syracuseStep 79916807 = 119875211) B119875211
theorem B1822495 : Blo 1279958 1822495 := bstep (se 1 (by rfl) ⟨1366871, by rfl⟩ : syracuseStep 1822495 = 2733743) B2733743
theorem B16412705 : Blo 1279958 16412705 := bstep (se 2 (by rfl) ⟨6154764, by rfl⟩ : syracuseStep 16412705 = 12309529) B12309529
theorem B3895457 : Blo 1279958 3895457 := bstep (se 2 (by rfl) ⟨1460796, by rfl⟩ : syracuseStep 3895457 = 2921593) B2921593
theorem B3240233 : Blo 1279958 3240233 := bstep (se 2 (by rfl) ⟨1215087, by rfl⟩ : syracuseStep 3240233 = 2430175) B2430175
theorem B1921583 : Blo 1279958 1921583 := bstep (se 1 (by rfl) ⟨1441187, by rfl⟩ : syracuseStep 1921583 = 2882375) B2882375
theorem B6484535 : Blo 1279958 6484535 := bstep (se 1 (by rfl) ⟨4863401, by rfl⟩ : syracuseStep 6484535 = 9726803) B9726803
theorem B4862537 : Blo 1279958 4862537 := bstep (se 2 (by rfl) ⟨1823451, by rfl⟩ : syracuseStep 4862537 = 3646903) B3646903
theorem B2880143 : Blo 1279958 2880143 := bstep (se 1 (by rfl) ⟨2160107, by rfl⟩ : syracuseStep 2880143 = 4320215) B4320215
theorem B9728747 : Blo 1279958 9728747 := bstep (se 1 (by rfl) ⟨7296560, by rfl⟩ : syracuseStep 9728747 = 14593121) B14593121
theorem B170898173 : Blo 1279958 170898173 := bstep (se 3 (by rfl) ⟨32043407, by rfl⟩ : syracuseStep 170898173 = 64086815) B64086815
theorem B4322159 : Blo 1279958 4322159 := bstep (se 1 (by rfl) ⟨3241619, by rfl⟩ : syracuseStep 4322159 = 6483239) B6483239
theorem B1921919 : Blo 1279958 1921919 := bstep (se 1 (by rfl) ⟨1441439, by rfl⟩ : syracuseStep 1921919 = 2882879) B2882879
theorem B6157225 : Blo 1279958 6157225 := bstep (se 2 (by rfl) ⟨2308959, by rfl⟩ : syracuseStep 6157225 = 4617919) B4617919
theorem B1922075 : Blo 1279958 1922075 := bstep (se 1 (by rfl) ⟨1441556, by rfl⟩ : syracuseStep 1922075 = 2883113) B2883113
theorem B36910241 : Blo 1279958 36910241 := bstep (se 2 (by rfl) ⟨13841340, by rfl⟩ : syracuseStep 36910241 = 27682681) B27682681
theorem B6485183 : Blo 1279958 6485183 := bstep (se 1 (by rfl) ⟨4863887, by rfl⟩ : syracuseStep 6485183 = 9727775) B9727775
theorem B21869999 : Blo 1279958 21869999 := bstep (se 1 (by rfl) ⟨16402499, by rfl⟩ : syracuseStep 21869999 = 32804999) B32804999
theorem B4617647 : Blo 1279958 4617647 := bstep (se 1 (by rfl) ⟨3463235, by rfl⟩ : syracuseStep 4617647 = 6926471) B6926471
theorem B4380583 : Blo 1279958 4380583 := bstep (se 1 (by rfl) ⟨3285437, by rfl⟩ : syracuseStep 4380583 = 6570875) B6570875
theorem B4323239 : Blo 1279958 4323239 := bstep (se 1 (by rfl) ⟨3242429, by rfl⟩ : syracuseStep 4323239 = 6484859) B6484859
theorem B2881583 : Blo 1279958 2881583 := bstep (se 1 (by rfl) ⟨2161187, by rfl⟩ : syracuseStep 2881583 = 4322375) B4322375
theorem B2881871 : Blo 1279958 2881871 := bstep (se 1 (by rfl) ⟨2161403, by rfl⟩ : syracuseStep 2881871 = 4322807) B4322807
theorem B4864495 : Blo 1279958 4864495 := bstep (se 1 (by rfl) ⟨3648371, by rfl⟩ : syracuseStep 4864495 = 7296743) B7296743
theorem B9722429 : Blo 1279958 9722429 := bstep (se 3 (by rfl) ⟨1822955, by rfl⟩ : syracuseStep 9722429 = 3645911) B3645911
theorem B3242987 : Blo 1279958 3242987 := bstep (se 1 (by rfl) ⟨2432240, by rfl⟩ : syracuseStep 3242987 = 4864481) B4864481
theorem B2882735 : Blo 1279958 2882735 := bstep (se 1 (by rfl) ⟨2162051, by rfl⟩ : syracuseStep 2882735 = 4324103) B4324103
theorem B4324967 : Blo 1279958 4324967 := bstep (se 1 (by rfl) ⟨3243725, by rfl⟩ : syracuseStep 4324967 = 6487451) B6487451
theorem B2162281 : Blo 1279958 2162281 := bstep (se 2 (by rfl) ⟨810855, by rfl⟩ : syracuseStep 2162281 = 1621711) B1621711
theorem B1973897 : Blo 1279958 1973897 := bstep (se 2 (by rfl) ⟨740211, by rfl⟩ : syracuseStep 1973897 = 1480423) B1480423
theorem B4325183 : Blo 1279958 4325183 := bstep (se 1 (by rfl) ⟨3243887, by rfl⟩ : syracuseStep 4325183 = 6487775) B6487775
theorem B8765599 : Blo 1279958 8765599 := bstep (se 1 (by rfl) ⟨6574199, by rfl⟩ : syracuseStep 8765599 = 13148399) B13148399
theorem B2162855 : Blo 1279958 2162855 := bstep (se 1 (by rfl) ⟨1622141, by rfl⟩ : syracuseStep 2162855 = 3244283) B3244283
theorem B6242579 : Blo 1279958 6242579 := bstep (se 1 (by rfl) ⟨4681934, by rfl⟩ : syracuseStep 6242579 = 9363869) B9363869
theorem B10387885 : Blo 1279958 10387885 := bstep (se 3 (by rfl) ⟨1947728, by rfl⟩ : syracuseStep 10387885 = 3895457) B3895457
theorem B8209633 : Blo 1279958 8209633 := bstep (se 2 (by rfl) ⟨3078612, by rfl⟩ : syracuseStep 8209633 = 6157225) B6157225
theorem B6481619 : Blo 1279958 6481619 := bstep (se 1 (by rfl) ⟨4861214, by rfl⟩ : syracuseStep 6481619 = 9722429) B9722429
theorem B16418699 : Blo 1279958 16418699 := bstep (se 1 (by rfl) ⟨12314024, by rfl⟩ : syracuseStep 16418699 = 24628049) B24628049
theorem B1280103 : Blo 1279958 1280103 := bstep (se 1 (by rfl) ⟨960077, by rfl⟩ : syracuseStep 1280103 = 1920155) B1920155
theorem B1280167 : Blo 1279958 1280167 := bstep (se 1 (by rfl) ⟨960125, by rfl⟩ : syracuseStep 1280167 = 1920251) B1920251
theorem B1280359 : Blo 1279958 1280359 := bstep (se 1 (by rfl) ⟨960269, by rfl⟩ : syracuseStep 1280359 = 1920539) B1920539
theorem B35080559 : Blo 1279958 35080559 := bstep (se 1 (by rfl) ⟨26310419, by rfl⟩ : syracuseStep 35080559 = 52620839) B52620839
theorem B2632495 : Blo 1279958 2632495 := bstep (se 1 (by rfl) ⟨1974371, by rfl⟩ : syracuseStep 2632495 = 3948743) B3948743
theorem B1281055 : Blo 1279958 1281055 := bstep (se 1 (by rfl) ⟨960791, by rfl⟩ : syracuseStep 1281055 = 1921583) B1921583
theorem B1920095 : Blo 1279958 1920095 := bstep (se 1 (by rfl) ⟨1440071, by rfl⟩ : syracuseStep 1920095 = 2880143) B2880143
theorem B1281279 : Blo 1279958 1281279 := bstep (se 1 (by rfl) ⟨960959, by rfl⟩ : syracuseStep 1281279 = 1921919) B1921919
theorem B1281383 : Blo 1279958 1281383 := bstep (se 1 (by rfl) ⟨961037, by rfl⟩ : syracuseStep 1281383 = 1922075) B1922075
theorem B1921055 : Blo 1279958 1921055 := bstep (se 1 (by rfl) ⟨1440791, by rfl⟩ : syracuseStep 1921055 = 2881583) B2881583
theorem B4616347 : Blo 1279958 4616347 := bstep (se 1 (by rfl) ⟨3462260, by rfl⟩ : syracuseStep 4616347 = 6924521) B6924521
theorem B1921247 : Blo 1279958 1921247 := bstep (se 1 (by rfl) ⟨1440935, by rfl⟩ : syracuseStep 1921247 = 2881871) B2881871
theorem B4862369 : Blo 1279958 4862369 := bstep (se 2 (by rfl) ⟨1823388, by rfl⟩ : syracuseStep 4862369 = 3646777) B3646777
theorem B3240607 : Blo 1279958 3240607 := bstep (se 1 (by rfl) ⟨2430455, by rfl⟩ : syracuseStep 3240607 = 4860911) B4860911
theorem B213111485 : Blo 1279958 213111485 := bstep (se 3 (by rfl) ⟨39958403, by rfl⟩ : syracuseStep 213111485 = 79916807) B79916807
theorem B2880287 : Blo 1279958 2880287 := bstep (se 1 (by rfl) ⟨2160215, by rfl⟩ : syracuseStep 2880287 = 4320431) B4320431
theorem B1921823 : Blo 1279958 1921823 := bstep (se 1 (by rfl) ⟨1441367, by rfl⟩ : syracuseStep 1921823 = 2882735) B2882735
theorem B2429993 : Blo 1279958 2429993 := bstep (se 2 (by rfl) ⟨911247, by rfl⟩ : syracuseStep 2429993 = 1822495) B1822495
theorem B1315931 : Blo 1279958 1315931 := bstep (se 1 (by rfl) ⟨986948, by rfl⟩ : syracuseStep 1315931 = 1973897) B1973897
theorem B10941803 : Blo 1279958 10941803 := bstep (se 1 (by rfl) ⟨8206352, by rfl⟩ : syracuseStep 10941803 = 16412705) B16412705
theorem B1922495 : Blo 1279958 1922495 := bstep (se 1 (by rfl) ⟨1441871, by rfl⟩ : syracuseStep 1922495 = 2883743) B2883743
theorem B2160155 : Blo 1279958 2160155 := bstep (se 1 (by rfl) ⟨1620116, by rfl⟩ : syracuseStep 2160155 = 3240233) B3240233
theorem B4323023 : Blo 1279958 4323023 := bstep (se 1 (by rfl) ⟨3242267, by rfl⟩ : syracuseStep 4323023 = 6484535) B6484535
theorem B3241691 : Blo 1279958 3241691 := bstep (se 1 (by rfl) ⟨2431268, by rfl⟩ : syracuseStep 3241691 = 4862537) B4862537
theorem B1922825 : Blo 1279958 1922825 := bstep (se 2 (by rfl) ⟨721059, by rfl⟩ : syracuseStep 1922825 = 1442119) B1442119
theorem B6485831 : Blo 1279958 6485831 := bstep (se 1 (by rfl) ⟨4864373, by rfl⟩ : syracuseStep 6485831 = 9728747) B9728747
theorem B113932115 : Blo 1279958 113932115 := bstep (se 1 (by rfl) ⟨85449086, by rfl⟩ : syracuseStep 113932115 = 170898173) B170898173
theorem B2881439 : Blo 1279958 2881439 := bstep (se 1 (by rfl) ⟨2161079, by rfl⟩ : syracuseStep 2881439 = 4322159) B4322159
theorem B21878747 : Blo 1279958 21878747 := bstep (se 1 (by rfl) ⟨16409060, by rfl⟩ : syracuseStep 21878747 = 32818121) B32818121
theorem B6485993 : Blo 1279958 6485993 := bstep (se 2 (by rfl) ⟨2432247, by rfl⟩ : syracuseStep 6485993 = 4864495) B4864495
theorem B24606827 : Blo 1279958 24606827 := bstep (se 1 (by rfl) ⟨18455120, by rfl⟩ : syracuseStep 24606827 = 36910241) B36910241
theorem B4323455 : Blo 1279958 4323455 := bstep (se 1 (by rfl) ⟨3242591, by rfl⟩ : syracuseStep 4323455 = 6485183) B6485183
theorem B14579999 : Blo 1279958 14579999 := bstep (se 1 (by rfl) ⟨10934999, by rfl⟩ : syracuseStep 14579999 = 21869999) B21869999
theorem B3078431 : Blo 1279958 3078431 := bstep (se 1 (by rfl) ⟨2308823, by rfl⟩ : syracuseStep 3078431 = 4617647) B4617647
theorem B4864313 : Blo 1279958 4864313 := bstep (se 2 (by rfl) ⟨1824117, by rfl⟩ : syracuseStep 4864313 = 3648235) B3648235
theorem B10951199 : Blo 1279958 10951199 := bstep (se 1 (by rfl) ⟨8213399, by rfl⟩ : syracuseStep 10951199 = 16426799) B16426799
theorem B2882159 : Blo 1279958 2882159 := bstep (se 1 (by rfl) ⟨2161619, by rfl⟩ : syracuseStep 2882159 = 4323239) B4323239
theorem B2432263 : Blo 1279958 2432263 := bstep (se 1 (by rfl) ⟨1824197, by rfl⟩ : syracuseStep 2432263 = 3648395) B3648395
theorem B2161991 : Blo 1279958 2161991 := bstep (se 1 (by rfl) ⟨1621493, by rfl⟩ : syracuseStep 2161991 = 3242987) B3242987
theorem B2883041 : Blo 1279958 2883041 := bstep (se 2 (by rfl) ⟨1081140, by rfl⟩ : syracuseStep 2883041 = 2162281) B2162281
theorem B2883311 : Blo 1279958 2883311 := bstep (se 1 (by rfl) ⟨2162483, by rfl⟩ : syracuseStep 2883311 = 4324967) B4324967
theorem B2883455 : Blo 1279958 2883455 := bstep (se 1 (by rfl) ⟨2162591, by rfl⟩ : syracuseStep 2883455 = 4325183) B4325183
theorem B5840777 : Blo 1279958 5840777 := bstep (se 2 (by rfl) ⟨2190291, by rfl⟩ : syracuseStep 5840777 = 4380583) B4380583
theorem B1441903 : Blo 1279958 1441903 := bstep (se 1 (by rfl) ⟨1081427, by rfl⟩ : syracuseStep 1441903 = 2162855) B2162855
theorem B4161719 : Blo 1279958 4161719 := bstep (se 1 (by rfl) ⟨3121289, by rfl⟩ : syracuseStep 4161719 = 6242579) B6242579
theorem B142074323 : Blo 1279958 142074323 := bstep (se 1 (by rfl) ⟨106555742, by rfl⟩ : syracuseStep 142074323 = 213111485) B213111485
theorem B10945799 : Blo 1279958 10945799 := bstep (se 1 (by rfl) ⟨8209349, by rfl⟩ : syracuseStep 10945799 = 16418699) B16418699
theorem B10946177 : Blo 1279958 10946177 := bstep (se 2 (by rfl) ⟨4104816, by rfl⟩ : syracuseStep 10946177 = 8209633) B8209633
theorem B7300799 : Blo 1279958 7300799 := bstep (se 1 (by rfl) ⟨5475599, by rfl⟩ : syracuseStep 7300799 = 10951199) B10951199
theorem B1280063 : Blo 1279958 1280063 := bstep (se 1 (by rfl) ⟨960047, by rfl⟩ : syracuseStep 1280063 = 1920095) B1920095
theorem B3893851 : Blo 1279958 3893851 := bstep (se 1 (by rfl) ⟨2920388, by rfl⟩ : syracuseStep 3893851 = 5840777) B5840777
theorem B1280703 : Blo 1279958 1280703 := bstep (se 1 (by rfl) ⟨960527, by rfl⟩ : syracuseStep 1280703 = 1921055) B1921055
theorem B1280831 : Blo 1279958 1280831 := bstep (se 1 (by rfl) ⟨960623, by rfl⟩ : syracuseStep 1280831 = 1921247) B1921247
theorem B6155129 : Blo 1279958 6155129 := bstep (se 2 (by rfl) ⟨2308173, by rfl⟩ : syracuseStep 6155129 = 4616347) B4616347
theorem B3509149 : Blo 1279958 3509149 := bstep (se 3 (by rfl) ⟨657965, by rfl⟩ : syracuseStep 3509149 = 1315931) B1315931
theorem B1920191 : Blo 1279958 1920191 := bstep (se 1 (by rfl) ⟨1440143, by rfl⟩ : syracuseStep 1920191 = 2880287) B2880287
theorem B1281215 : Blo 1279958 1281215 := bstep (se 1 (by rfl) ⟨960911, by rfl⟩ : syracuseStep 1281215 = 1921823) B1921823
theorem B4320809 : Blo 1279958 4320809 := bstep (se 2 (by rfl) ⟨1620303, by rfl⟩ : syracuseStep 4320809 = 3240607) B3240607
theorem B7294535 : Blo 1279958 7294535 := bstep (se 1 (by rfl) ⟨5470901, by rfl⟩ : syracuseStep 7294535 = 10941803) B10941803
theorem B1281663 : Blo 1279958 1281663 := bstep (se 1 (by rfl) ⟨961247, by rfl⟩ : syracuseStep 1281663 = 1922495) B1922495
theorem B3509993 : Blo 1279958 3509993 := bstep (se 2 (by rfl) ⟨1316247, by rfl⟩ : syracuseStep 3509993 = 2632495) B2632495
theorem B4321079 : Blo 1279958 4321079 := bstep (se 1 (by rfl) ⟨3240809, by rfl⟩ : syracuseStep 4321079 = 6481619) B6481619
theorem B1281883 : Blo 1279958 1281883 := bstep (se 1 (by rfl) ⟨961412, by rfl⟩ : syracuseStep 1281883 = 1922825) B1922825
theorem B1920959 : Blo 1279958 1920959 := bstep (se 1 (by rfl) ⟨1440719, by rfl⟩ : syracuseStep 1920959 = 2881439) B2881439
theorem B14585831 : Blo 1279958 14585831 := bstep (se 1 (by rfl) ⟨10939373, by rfl⟩ : syracuseStep 14585831 = 21878747) B21878747
theorem B16404551 : Blo 1279958 16404551 := bstep (se 1 (by rfl) ⟨12303413, by rfl⟩ : syracuseStep 16404551 = 24606827) B24606827
theorem B9719999 : Blo 1279958 9719999 := bstep (se 1 (by rfl) ⟨7289999, by rfl⟩ : syracuseStep 9719999 = 14579999) B14579999
theorem B2052287 : Blo 1279958 2052287 := bstep (se 1 (by rfl) ⟨1539215, by rfl⟩ : syracuseStep 2052287 = 3078431) B3078431
theorem B1921439 : Blo 1279958 1921439 := bstep (se 1 (by rfl) ⟨1441079, by rfl⟩ : syracuseStep 1921439 = 2882159) B2882159
theorem B1922027 : Blo 1279958 1922027 := bstep (se 1 (by rfl) ⟨1441520, by rfl⟩ : syracuseStep 1922027 = 2883041) B2883041
theorem B1922207 : Blo 1279958 1922207 := bstep (se 1 (by rfl) ⟨1441655, by rfl⟩ : syracuseStep 1922207 = 2883311) B2883311
theorem B1922303 : Blo 1279958 1922303 := bstep (se 1 (by rfl) ⟨1441727, by rfl⟩ : syracuseStep 1922303 = 2883455) B2883455
theorem B11687465 : Blo 1279958 11687465 := bstep (se 2 (by rfl) ⟨4382799, by rfl⟩ : syracuseStep 11687465 = 8765599) B8765599
theorem B3241579 : Blo 1279958 3241579 := bstep (se 1 (by rfl) ⟨2431184, by rfl⟩ : syracuseStep 3241579 = 4862369) B4862369
theorem B13850513 : Blo 1279958 13850513 := bstep (se 2 (by rfl) ⟨5193942, by rfl⟩ : syracuseStep 13850513 = 10387885) B10387885
theorem B1619995 : Blo 1279958 1619995 := bstep (se 1 (by rfl) ⟨1214996, by rfl⟩ : syracuseStep 1619995 = 2429993) B2429993
theorem B1440103 : Blo 1279958 1440103 := bstep (se 1 (by rfl) ⟨1080077, by rfl⟩ : syracuseStep 1440103 = 2160155) B2160155
theorem B2882015 : Blo 1279958 2882015 := bstep (se 1 (by rfl) ⟨2161511, by rfl⟩ : syracuseStep 2882015 = 4323023) B4323023
theorem B2161127 : Blo 1279958 2161127 := bstep (se 1 (by rfl) ⟨1620845, by rfl⟩ : syracuseStep 2161127 = 3241691) B3241691
theorem B4323887 : Blo 1279958 4323887 := bstep (se 1 (by rfl) ⟨3242915, by rfl⟩ : syracuseStep 4323887 = 6485831) B6485831
theorem B75954743 : Blo 1279958 75954743 := bstep (se 1 (by rfl) ⟨56966057, by rfl⟩ : syracuseStep 75954743 = 113932115) B113932115
theorem B4323995 : Blo 1279958 4323995 := bstep (se 1 (by rfl) ⟨3242996, by rfl⟩ : syracuseStep 4323995 = 6485993) B6485993
theorem B2882303 : Blo 1279958 2882303 := bstep (se 1 (by rfl) ⟨2161727, by rfl⟩ : syracuseStep 2882303 = 4323455) B4323455
theorem B3242875 : Blo 1279958 3242875 := bstep (se 1 (by rfl) ⟨2432156, by rfl⟩ : syracuseStep 3242875 = 4864313) B4864313
theorem B23387039 : Blo 1279958 23387039 := bstep (se 1 (by rfl) ⟨17540279, by rfl⟩ : syracuseStep 23387039 = 35080559) B35080559
theorem B3243017 : Blo 1279958 3243017 := bstep (se 2 (by rfl) ⟨1216131, by rfl⟩ : syracuseStep 3243017 = 2432263) B2432263
theorem B1441327 : Blo 1279958 1441327 := bstep (se 1 (by rfl) ⟨1080995, by rfl⟩ : syracuseStep 1441327 = 2161991) B2161991
theorem B10936367 : Blo 1279958 10936367 := bstep (se 1 (by rfl) ⟨8202275, by rfl⟩ : syracuseStep 10936367 = 16404551) B16404551
theorem B6479999 : Blo 1279958 6479999 := bstep (se 1 (by rfl) ⟨4859999, by rfl⟩ : syracuseStep 6479999 = 9719999) B9719999
theorem B1368191 : Blo 1279958 1368191 := bstep (se 1 (by rfl) ⟨1026143, by rfl⟩ : syracuseStep 1368191 = 2052287) B2052287
theorem B94716215 : Blo 1279958 94716215 := bstep (se 1 (by rfl) ⟨71037161, by rfl⟩ : syracuseStep 94716215 = 142074323) B142074323
theorem B20767205 : Blo 1279958 20767205 := bstep (se 4 (by rfl) ⟨1946925, by rfl⟩ : syracuseStep 20767205 = 3893851) B3893851
theorem B7791643 : Blo 1279958 7791643 := bstep (se 1 (by rfl) ⟨5843732, by rfl⟩ : syracuseStep 7791643 = 11687465) B11687465
theorem B4867199 : Blo 1279958 4867199 := bstep (se 1 (by rfl) ⟨3650399, by rfl⟩ : syracuseStep 4867199 = 7300799) B7300799
theorem B4678865 : Blo 1279958 4678865 := bstep (se 2 (by rfl) ⟨1754574, by rfl⟩ : syracuseStep 4678865 = 3509149) B3509149
theorem B9233675 : Blo 1279958 9233675 := bstep (se 1 (by rfl) ⟨6925256, by rfl⟩ : syracuseStep 9233675 = 13850513) B13850513
theorem B50636495 : Blo 1279958 50636495 := bstep (se 1 (by rfl) ⟨37977371, by rfl⟩ : syracuseStep 50636495 = 75954743) B75954743
theorem B15591359 : Blo 1279958 15591359 := bstep (se 1 (by rfl) ⟨11693519, by rfl⟩ : syracuseStep 15591359 = 23387039) B23387039
theorem B1280127 : Blo 1279958 1280127 := bstep (se 1 (by rfl) ⟨960095, by rfl⟩ : syracuseStep 1280127 = 1920191) B1920191
theorem B1280639 : Blo 1279958 1280639 := bstep (se 1 (by rfl) ⟨960479, by rfl⟩ : syracuseStep 1280639 = 1920959) B1920959
theorem B1280959 : Blo 1279958 1280959 := bstep (se 1 (by rfl) ⟨960719, by rfl⟩ : syracuseStep 1280959 = 1921439) B1921439
theorem B1920137 : Blo 1279958 1920137 := bstep (se 2 (by rfl) ⟨720051, by rfl⟩ : syracuseStep 1920137 = 1440103) B1440103
theorem B1281351 : Blo 1279958 1281351 := bstep (se 1 (by rfl) ⟨961013, by rfl⟩ : syracuseStep 1281351 = 1922027) B1922027
theorem B1281471 : Blo 1279958 1281471 := bstep (se 1 (by rfl) ⟨961103, by rfl⟩ : syracuseStep 1281471 = 1922207) B1922207
theorem B1281535 : Blo 1279958 1281535 := bstep (se 1 (by rfl) ⟨961151, by rfl⟩ : syracuseStep 1281535 = 1922303) B1922303
theorem B1921343 : Blo 1279958 1921343 := bstep (se 1 (by rfl) ⟨1441007, by rfl⟩ : syracuseStep 1921343 = 2882015) B2882015
theorem B1921535 : Blo 1279958 1921535 := bstep (se 1 (by rfl) ⟨1441151, by rfl⟩ : syracuseStep 1921535 = 2882303) B2882303
theorem B9359981 : Blo 1279958 9359981 := bstep (se 3 (by rfl) ⟨1754996, by rfl⟩ : syracuseStep 9359981 = 3509993) B3509993
theorem B1921769 : Blo 1279958 1921769 := bstep (se 2 (by rfl) ⟨720663, by rfl⟩ : syracuseStep 1921769 = 1441327) B1441327
theorem B4322105 : Blo 1279958 4322105 := bstep (se 2 (by rfl) ⟨1620789, by rfl⟩ : syracuseStep 4322105 = 3241579) B3241579
theorem B16413677 : Blo 1279958 16413677 := bstep (se 3 (by rfl) ⟨3077564, by rfl⟩ : syracuseStep 16413677 = 6155129) B6155129
theorem B2880539 : Blo 1279958 2880539 := bstep (se 1 (by rfl) ⟨2160404, by rfl⟩ : syracuseStep 2880539 = 4320809) B4320809
theorem B4863023 : Blo 1279958 4863023 := bstep (se 1 (by rfl) ⟨3647267, by rfl⟩ : syracuseStep 4863023 = 7294535) B7294535
theorem B2880719 : Blo 1279958 2880719 := bstep (se 1 (by rfl) ⟨2160539, by rfl⟩ : syracuseStep 2880719 = 4321079) B4321079
theorem B2159993 : Blo 1279958 2159993 := bstep (se 2 (by rfl) ⟨809997, by rfl⟩ : syracuseStep 2159993 = 1619995) B1619995
theorem B1922537 : Blo 1279958 1922537 := bstep (se 2 (by rfl) ⟨720951, by rfl⟩ : syracuseStep 1922537 = 1441903) B1441903
theorem B11097917 : Blo 1279958 11097917 := bstep (se 3 (by rfl) ⟨2080859, by rfl⟩ : syracuseStep 11097917 = 4161719) B4161719
theorem B7297199 : Blo 1279958 7297199 := bstep (se 1 (by rfl) ⟨5472899, by rfl⟩ : syracuseStep 7297199 = 10945799) B10945799
theorem B7297451 : Blo 1279958 7297451 := bstep (se 1 (by rfl) ⟨5473088, by rfl⟩ : syracuseStep 7297451 = 10946177) B10946177
theorem B4323833 : Blo 1279958 4323833 := bstep (se 2 (by rfl) ⟨1621437, by rfl⟩ : syracuseStep 4323833 = 3242875) B3242875
theorem B1440751 : Blo 1279958 1440751 := bstep (se 1 (by rfl) ⟨1080563, by rfl⟩ : syracuseStep 1440751 = 2161127) B2161127
theorem B2882591 : Blo 1279958 2882591 := bstep (se 1 (by rfl) ⟨2161943, by rfl⟩ : syracuseStep 2882591 = 4323887) B4323887
theorem B2882663 : Blo 1279958 2882663 := bstep (se 1 (by rfl) ⟨2161997, by rfl⟩ : syracuseStep 2882663 = 4323995) B4323995
theorem B2162011 : Blo 1279958 2162011 := bstep (se 1 (by rfl) ⟨1621508, by rfl⟩ : syracuseStep 2162011 = 3243017) B3243017
theorem B9723887 : Blo 1279958 9723887 := bstep (se 1 (by rfl) ⟨7292915, by rfl⟩ : syracuseStep 9723887 = 14585831) B14585831
theorem B7290911 : Blo 1279958 7290911 := bstep (se 1 (by rfl) ⟨5468183, by rfl⟩ : syracuseStep 7290911 = 10936367) B10936367
theorem B63144143 : Blo 1279958 63144143 := bstep (se 1 (by rfl) ⟨47358107, by rfl⟩ : syracuseStep 63144143 = 94716215) B94716215
theorem B13844803 : Blo 1279958 13844803 := bstep (se 1 (by rfl) ⟨10383602, by rfl⟩ : syracuseStep 13844803 = 20767205) B20767205
theorem B3244799 : Blo 1279958 3244799 := bstep (se 1 (by rfl) ⟨2433599, by rfl⟩ : syracuseStep 3244799 = 4867199) B4867199
theorem B7398611 : Blo 1279958 7398611 := bstep (se 1 (by rfl) ⟨5548958, by rfl⟩ : syracuseStep 7398611 = 11097917) B11097917
theorem B1280091 : Blo 1279958 1280091 := bstep (se 1 (by rfl) ⟨960068, by rfl⟩ : syracuseStep 1280091 = 1920137) B1920137
theorem B6482591 : Blo 1279958 6482591 := bstep (se 1 (by rfl) ⟨4861943, by rfl⟩ : syracuseStep 6482591 = 9723887) B9723887
theorem B4319999 : Blo 1279958 4319999 := bstep (se 1 (by rfl) ⟨3239999, by rfl⟩ : syracuseStep 4319999 = 6479999) B6479999
theorem B1280895 : Blo 1279958 1280895 := bstep (se 1 (by rfl) ⟨960671, by rfl⟩ : syracuseStep 1280895 = 1921343) B1921343
theorem B3648509 : Blo 1279958 3648509 := bstep (se 3 (by rfl) ⟨684095, by rfl⟩ : syracuseStep 3648509 = 1368191) B1368191
theorem B1281023 : Blo 1279958 1281023 := bstep (se 1 (by rfl) ⟨960767, by rfl⟩ : syracuseStep 1281023 = 1921535) B1921535
theorem B1281179 : Blo 1279958 1281179 := bstep (se 1 (by rfl) ⟨960884, by rfl⟩ : syracuseStep 1281179 = 1921769) B1921769
theorem B1920359 : Blo 1279958 1920359 := bstep (se 1 (by rfl) ⟨1440269, by rfl⟩ : syracuseStep 1920359 = 2880539) B2880539
theorem B1920479 : Blo 1279958 1920479 := bstep (se 1 (by rfl) ⟨1440359, by rfl⟩ : syracuseStep 1920479 = 2880719) B2880719
theorem B6155783 : Blo 1279958 6155783 := bstep (se 1 (by rfl) ⟨4616837, by rfl⟩ : syracuseStep 6155783 = 9233675) B9233675
theorem B1281691 : Blo 1279958 1281691 := bstep (se 1 (by rfl) ⟨961268, by rfl⟩ : syracuseStep 1281691 = 1922537) B1922537
theorem B1921001 : Blo 1279958 1921001 := bstep (se 2 (by rfl) ⟨720375, by rfl⟩ : syracuseStep 1921001 = 1440751) B1440751
theorem B1921727 : Blo 1279958 1921727 := bstep (se 1 (by rfl) ⟨1441295, by rfl⟩ : syracuseStep 1921727 = 2882591) B2882591
theorem B1921775 : Blo 1279958 1921775 := bstep (se 1 (by rfl) ⟨1441331, by rfl⟩ : syracuseStep 1921775 = 2882663) B2882663
theorem B41555429 : Blo 1279958 41555429 := bstep (se 4 (by rfl) ⟨3895821, by rfl⟩ : syracuseStep 41555429 = 7791643) B7791643
theorem B6239987 : Blo 1279958 6239987 := bstep (se 1 (by rfl) ⟨4679990, by rfl⟩ : syracuseStep 6239987 = 9359981) B9359981
theorem B2881403 : Blo 1279958 2881403 := bstep (se 1 (by rfl) ⟨2161052, by rfl⟩ : syracuseStep 2881403 = 4322105) B4322105
theorem B10942451 : Blo 1279958 10942451 := bstep (se 1 (by rfl) ⟨8206838, by rfl⟩ : syracuseStep 10942451 = 16413677) B16413677
theorem B3242015 : Blo 1279958 3242015 := bstep (se 1 (by rfl) ⟨2431511, by rfl⟩ : syracuseStep 3242015 = 4863023) B4863023
theorem B3119243 : Blo 1279958 3119243 := bstep (se 1 (by rfl) ⟨2339432, by rfl⟩ : syracuseStep 3119243 = 4678865) B4678865
theorem B1439995 : Blo 1279958 1439995 := bstep (se 1 (by rfl) ⟨1079996, by rfl⟩ : syracuseStep 1439995 = 2159993) B2159993
theorem B33757663 : Blo 1279958 33757663 := bstep (se 1 (by rfl) ⟨25318247, by rfl⟩ : syracuseStep 33757663 = 50636495) B50636495
theorem B10394239 : Blo 1279958 10394239 := bstep (se 1 (by rfl) ⟨7795679, by rfl⟩ : syracuseStep 10394239 = 15591359) B15591359
theorem B4864799 : Blo 1279958 4864799 := bstep (se 1 (by rfl) ⟨3648599, by rfl⟩ : syracuseStep 4864799 = 7297199) B7297199
theorem B4864967 : Blo 1279958 4864967 := bstep (se 1 (by rfl) ⟨3648725, by rfl⟩ : syracuseStep 4864967 = 7297451) B7297451
theorem B2882555 : Blo 1279958 2882555 := bstep (se 1 (by rfl) ⟨2161916, by rfl⟩ : syracuseStep 2882555 = 4323833) B4323833
theorem B2882681 : Blo 1279958 2882681 := bstep (se 2 (by rfl) ⟨1081005, by rfl⟩ : syracuseStep 2882681 = 2162011) B2162011
theorem B2163199 : Blo 1279958 2163199 := bstep (se 1 (by rfl) ⟨1622399, by rfl⟩ : syracuseStep 2163199 = 3244799) B3244799
theorem B4932407 : Blo 1279958 4932407 := bstep (se 1 (by rfl) ⟨3699305, by rfl⟩ : syracuseStep 4932407 = 7398611) B7398611
theorem B1280239 : Blo 1279958 1280239 := bstep (se 1 (by rfl) ⟨960179, by rfl⟩ : syracuseStep 1280239 = 1920359) B1920359
theorem B1280319 : Blo 1279958 1280319 := bstep (se 1 (by rfl) ⟨960239, by rfl⟩ : syracuseStep 1280319 = 1920479) B1920479
theorem B1280667 : Blo 1279958 1280667 := bstep (se 1 (by rfl) ⟨960500, by rfl⟩ : syracuseStep 1280667 = 1921001) B1921001
theorem B4860607 : Blo 1279958 4860607 := bstep (se 1 (by rfl) ⟨3645455, by rfl⟩ : syracuseStep 4860607 = 7290911) B7290911
theorem B1919993 : Blo 1279958 1919993 := bstep (se 2 (by rfl) ⟨719997, by rfl⟩ : syracuseStep 1919993 = 1439995) B1439995
theorem B8317981 : Blo 1279958 8317981 := bstep (se 3 (by rfl) ⟨1559621, by rfl⟩ : syracuseStep 8317981 = 3119243) B3119243
theorem B18459737 : Blo 1279958 18459737 := bstep (se 2 (by rfl) ⟨6922401, by rfl⟩ : syracuseStep 18459737 = 13844803) B13844803
theorem B1281151 : Blo 1279958 1281151 := bstep (se 1 (by rfl) ⟨960863, by rfl⟩ : syracuseStep 1281151 = 1921727) B1921727
theorem B1281183 : Blo 1279958 1281183 := bstep (se 1 (by rfl) ⟨960887, by rfl⟩ : syracuseStep 1281183 = 1921775) B1921775
theorem B45010217 : Blo 1279958 45010217 := bstep (se 2 (by rfl) ⟨16878831, by rfl⟩ : syracuseStep 45010217 = 33757663) B33757663
theorem B1920935 : Blo 1279958 1920935 := bstep (se 1 (by rfl) ⟨1440701, by rfl⟩ : syracuseStep 1920935 = 2881403) B2881403
theorem B7294967 : Blo 1279958 7294967 := bstep (se 1 (by rfl) ⟨5471225, by rfl⟩ : syracuseStep 7294967 = 10942451) B10942451
theorem B4321727 : Blo 1279958 4321727 := bstep (se 1 (by rfl) ⟨3241295, by rfl⟩ : syracuseStep 4321727 = 6482591) B6482591
theorem B2879999 : Blo 1279958 2879999 := bstep (se 1 (by rfl) ⟨2159999, by rfl⟩ : syracuseStep 2879999 = 4319999) B4319999
theorem B1921703 : Blo 1279958 1921703 := bstep (se 1 (by rfl) ⟨1441277, by rfl⟩ : syracuseStep 1921703 = 2882555) B2882555
theorem B1921787 : Blo 1279958 1921787 := bstep (se 1 (by rfl) ⟨1441340, by rfl⟩ : syracuseStep 1921787 = 2882681) B2882681
theorem B42096095 : Blo 1279958 42096095 := bstep (se 1 (by rfl) ⟨31572071, by rfl⟩ : syracuseStep 42096095 = 63144143) B63144143
theorem B13858985 : Blo 1279958 13858985 := bstep (se 2 (by rfl) ⟨5197119, by rfl⟩ : syracuseStep 13858985 = 10394239) B10394239
theorem B27703619 : Blo 1279958 27703619 := bstep (se 1 (by rfl) ⟨20777714, by rfl⟩ : syracuseStep 27703619 = 41555429) B41555429
theorem B4159991 : Blo 1279958 4159991 := bstep (se 1 (by rfl) ⟨3119993, by rfl⟩ : syracuseStep 4159991 = 6239987) B6239987
theorem B2161343 : Blo 1279958 2161343 := bstep (se 1 (by rfl) ⟨1621007, by rfl⟩ : syracuseStep 2161343 = 3242015) B3242015
theorem B3243199 : Blo 1279958 3243199 := bstep (se 1 (by rfl) ⟨2432399, by rfl⟩ : syracuseStep 3243199 = 4864799) B4864799
theorem B3243311 : Blo 1279958 3243311 := bstep (se 1 (by rfl) ⟨2432483, by rfl⟩ : syracuseStep 3243311 = 4864967) B4864967
theorem B2432339 : Blo 1279958 2432339 := bstep (se 1 (by rfl) ⟨1824254, by rfl⟩ : syracuseStep 2432339 = 3648509) B3648509
theorem B4103855 : Blo 1279958 4103855 := bstep (se 1 (by rfl) ⟨3077891, by rfl⟩ : syracuseStep 4103855 = 6155783) B6155783
theorem B2884265 : Blo 1279958 2884265 := bstep (se 2 (by rfl) ⟨1081599, by rfl⟩ : syracuseStep 2884265 = 2163199) B2163199
theorem B6480809 : Blo 1279958 6480809 := bstep (se 2 (by rfl) ⟨2430303, by rfl⟩ : syracuseStep 6480809 = 4860607) B4860607
theorem B1279995 : Blo 1279958 1279995 := bstep (se 1 (by rfl) ⟨959996, by rfl⟩ : syracuseStep 1279995 = 1919993) B1919993
theorem B12306491 : Blo 1279958 12306491 := bstep (se 1 (by rfl) ⟨9229868, by rfl⟩ : syracuseStep 12306491 = 18459737) B18459737
theorem B1280623 : Blo 1279958 1280623 := bstep (se 1 (by rfl) ⟨960467, by rfl⟩ : syracuseStep 1280623 = 1920935) B1920935
theorem B44362565 : Blo 1279958 44362565 := bstep (se 4 (by rfl) ⟨4158990, by rfl⟩ : syracuseStep 44362565 = 8317981) B8317981
theorem B1919999 : Blo 1279958 1919999 := bstep (se 1 (by rfl) ⟨1439999, by rfl⟩ : syracuseStep 1919999 = 2879999) B2879999
theorem B36957293 : Blo 1279958 36957293 := bstep (se 3 (by rfl) ⟨6929492, by rfl⟩ : syracuseStep 36957293 = 13858985) B13858985
theorem B1281135 : Blo 1279958 1281135 := bstep (se 1 (by rfl) ⟨960851, by rfl⟩ : syracuseStep 1281135 = 1921703) B1921703
theorem B1281191 : Blo 1279958 1281191 := bstep (se 1 (by rfl) ⟨960893, by rfl⟩ : syracuseStep 1281191 = 1921787) B1921787
theorem B3288271 : Blo 1279958 3288271 := bstep (se 1 (by rfl) ⟨2466203, by rfl⟩ : syracuseStep 3288271 = 4932407) B4932407
theorem B18469079 : Blo 1279958 18469079 := bstep (se 1 (by rfl) ⟨13851809, by rfl⟩ : syracuseStep 18469079 = 27703619) B27703619
theorem B2773327 : Blo 1279958 2773327 := bstep (se 1 (by rfl) ⟨2079995, by rfl⟩ : syracuseStep 2773327 = 4159991) B4159991
theorem B4863311 : Blo 1279958 4863311 := bstep (se 1 (by rfl) ⟨3647483, by rfl⟩ : syracuseStep 4863311 = 7294967) B7294967
theorem B2881151 : Blo 1279958 2881151 := bstep (se 1 (by rfl) ⟨2160863, by rfl⟩ : syracuseStep 2881151 = 4321727) B4321727
theorem B28064063 : Blo 1279958 28064063 := bstep (se 1 (by rfl) ⟨21048047, by rfl⟩ : syracuseStep 28064063 = 42096095) B42096095
theorem B4324265 : Blo 1279958 4324265 := bstep (se 2 (by rfl) ⟨1621599, by rfl⟩ : syracuseStep 4324265 = 3243199) B3243199
theorem B1440895 : Blo 1279958 1440895 := bstep (se 1 (by rfl) ⟨1080671, by rfl⟩ : syracuseStep 1440895 = 2161343) B2161343
theorem B30006811 : Blo 1279958 30006811 := bstep (se 1 (by rfl) ⟨22505108, by rfl⟩ : syracuseStep 30006811 = 45010217) B45010217
theorem B2162207 : Blo 1279958 2162207 := bstep (se 1 (by rfl) ⟨1621655, by rfl⟩ : syracuseStep 2162207 = 3243311) B3243311
theorem B1621559 : Blo 1279958 1621559 := bstep (se 1 (by rfl) ⟨1216169, by rfl⟩ : syracuseStep 1621559 = 2432339) B2432339
theorem B2735903 : Blo 1279958 2735903 := bstep (se 1 (by rfl) ⟨2051927, by rfl⟩ : syracuseStep 2735903 = 4103855) B4103855
theorem B12312719 : Blo 1279958 12312719 := bstep (se 1 (by rfl) ⟨9234539, by rfl⟩ : syracuseStep 12312719 = 18469079) B18469079
theorem B4384361 : Blo 1279958 4384361 := bstep (se 2 (by rfl) ⟨1644135, by rfl⟩ : syracuseStep 4384361 = 3288271) B3288271
theorem B29575043 : Blo 1279958 29575043 := bstep (se 1 (by rfl) ⟨22181282, by rfl⟩ : syracuseStep 29575043 = 44362565) B44362565
theorem B1279999 : Blo 1279958 1279999 := bstep (se 1 (by rfl) ⟨959999, by rfl⟩ : syracuseStep 1279999 = 1919999) B1919999
theorem B3697769 : Blo 1279958 3697769 := bstep (se 2 (by rfl) ⟨1386663, by rfl⟩ : syracuseStep 3697769 = 2773327) B2773327
theorem B4320539 : Blo 1279958 4320539 := bstep (se 1 (by rfl) ⟨3240404, by rfl⟩ : syracuseStep 4320539 = 6480809) B6480809
theorem B1920767 : Blo 1279958 1920767 := bstep (se 1 (by rfl) ⟨1440575, by rfl⟩ : syracuseStep 1920767 = 2881151) B2881151
theorem B8204327 : Blo 1279958 8204327 := bstep (se 1 (by rfl) ⟨6153245, by rfl⟩ : syracuseStep 8204327 = 12306491) B12306491
theorem B1921193 : Blo 1279958 1921193 := bstep (se 2 (by rfl) ⟨720447, by rfl⟩ : syracuseStep 1921193 = 1440895) B1440895
theorem B24638195 : Blo 1279958 24638195 := bstep (se 1 (by rfl) ⟨18478646, by rfl⟩ : syracuseStep 24638195 = 36957293) B36957293
theorem B7295741 : Blo 1279958 7295741 := bstep (se 3 (by rfl) ⟨1367951, by rfl⟩ : syracuseStep 7295741 = 2735903) B2735903
theorem B1922843 : Blo 1279958 1922843 := bstep (se 1 (by rfl) ⟨1442132, by rfl⟩ : syracuseStep 1922843 = 2884265) B2884265
theorem B3242207 : Blo 1279958 3242207 := bstep (se 1 (by rfl) ⟨2431655, by rfl⟩ : syracuseStep 3242207 = 4863311) B4863311
theorem B4324157 : Blo 1279958 4324157 := bstep (se 3 (by rfl) ⟨810779, by rfl⟩ : syracuseStep 4324157 = 1621559) B1621559
theorem B18709375 : Blo 1279958 18709375 := bstep (se 1 (by rfl) ⟨14032031, by rfl⟩ : syracuseStep 18709375 = 28064063) B28064063
theorem B2882843 : Blo 1279958 2882843 := bstep (se 1 (by rfl) ⟨2162132, by rfl⟩ : syracuseStep 2882843 = 4324265) B4324265
theorem B40009081 : Blo 1279958 40009081 := bstep (se 2 (by rfl) ⟨15003405, by rfl⟩ : syracuseStep 40009081 = 30006811) B30006811
theorem B1441471 : Blo 1279958 1441471 := bstep (se 1 (by rfl) ⟨1081103, by rfl⟩ : syracuseStep 1441471 = 2162207) B2162207
theorem B8208479 : Blo 1279958 8208479 := bstep (se 1 (by rfl) ⟨6156359, by rfl⟩ : syracuseStep 8208479 = 12312719) B12312719
theorem B16425463 : Blo 1279958 16425463 := bstep (se 1 (by rfl) ⟨12319097, by rfl⟩ : syracuseStep 16425463 = 24638195) B24638195
theorem B24945833 : Blo 1279958 24945833 := bstep (se 2 (by rfl) ⟨9354687, by rfl⟩ : syracuseStep 24945833 = 18709375) B18709375
theorem B1280511 : Blo 1279958 1280511 := bstep (se 1 (by rfl) ⟨960383, by rfl⟩ : syracuseStep 1280511 = 1920767) B1920767
theorem B1280795 : Blo 1279958 1280795 := bstep (se 1 (by rfl) ⟨960596, by rfl⟩ : syracuseStep 1280795 = 1921193) B1921193
theorem B1281895 : Blo 1279958 1281895 := bstep (se 1 (by rfl) ⟨961421, by rfl⟩ : syracuseStep 1281895 = 1922843) B1922843
theorem B2880359 : Blo 1279958 2880359 := bstep (se 1 (by rfl) ⟨2160269, by rfl⟩ : syracuseStep 2880359 = 4320539) B4320539
theorem B1921895 : Blo 1279958 1921895 := bstep (se 1 (by rfl) ⟨1441421, by rfl⟩ : syracuseStep 1921895 = 2882843) B2882843
theorem B1921961 : Blo 1279958 1921961 := bstep (se 2 (by rfl) ⟨720735, by rfl⟩ : syracuseStep 1921961 = 1441471) B1441471
theorem B5469551 : Blo 1279958 5469551 := bstep (se 1 (by rfl) ⟨4102163, by rfl⟩ : syracuseStep 5469551 = 8204327) B8204327
theorem B9860717 : Blo 1279958 9860717 := bstep (se 3 (by rfl) ⟨1848884, by rfl⟩ : syracuseStep 9860717 = 3697769) B3697769
theorem B4863827 : Blo 1279958 4863827 := bstep (se 1 (by rfl) ⟨3647870, by rfl⟩ : syracuseStep 4863827 = 7295741) B7295741
theorem B2922907 : Blo 1279958 2922907 := bstep (se 1 (by rfl) ⟨2192180, by rfl⟩ : syracuseStep 2922907 = 4384361) B4384361
theorem B19716695 : Blo 1279958 19716695 := bstep (se 1 (by rfl) ⟨14787521, by rfl⟩ : syracuseStep 19716695 = 29575043) B29575043
theorem B2161471 : Blo 1279958 2161471 := bstep (se 1 (by rfl) ⟨1621103, by rfl⟩ : syracuseStep 2161471 = 3242207) B3242207
theorem B53345441 : Blo 1279958 53345441 := bstep (se 2 (by rfl) ⟨20004540, by rfl⟩ : syracuseStep 53345441 = 40009081) B40009081
theorem B2882771 : Blo 1279958 2882771 := bstep (se 1 (by rfl) ⟨2162078, by rfl⟩ : syracuseStep 2882771 = 4324157) B4324157
theorem B5472319 : Blo 1279958 5472319 := bstep (se 1 (by rfl) ⟨4104239, by rfl⟩ : syracuseStep 5472319 = 8208479) B8208479
theorem B3646367 : Blo 1279958 3646367 := bstep (se 1 (by rfl) ⟨2734775, by rfl⟩ : syracuseStep 3646367 = 5469551) B5469551
theorem B35563627 : Blo 1279958 35563627 := bstep (se 1 (by rfl) ⟨26672720, by rfl⟩ : syracuseStep 35563627 = 53345441) B53345441
theorem B66522221 : Blo 1279958 66522221 := bstep (se 3 (by rfl) ⟨12472916, by rfl⟩ : syracuseStep 66522221 = 24945833) B24945833
theorem B1920239 : Blo 1279958 1920239 := bstep (se 1 (by rfl) ⟨1440179, by rfl⟩ : syracuseStep 1920239 = 2880359) B2880359
theorem B1281263 : Blo 1279958 1281263 := bstep (se 1 (by rfl) ⟨960947, by rfl⟩ : syracuseStep 1281263 = 1921895) B1921895
theorem B1281307 : Blo 1279958 1281307 := bstep (se 1 (by rfl) ⟨960980, by rfl⟩ : syracuseStep 1281307 = 1921961) B1921961
theorem B21900617 : Blo 1279958 21900617 := bstep (se 2 (by rfl) ⟨8212731, by rfl⟩ : syracuseStep 21900617 = 16425463) B16425463
theorem B6573811 : Blo 1279958 6573811 := bstep (se 1 (by rfl) ⟨4930358, by rfl⟩ : syracuseStep 6573811 = 9860717) B9860717
theorem B13144463 : Blo 1279958 13144463 := bstep (se 1 (by rfl) ⟨9858347, by rfl⟩ : syracuseStep 13144463 = 19716695) B19716695
theorem B1921847 : Blo 1279958 1921847 := bstep (se 1 (by rfl) ⟨1441385, by rfl⟩ : syracuseStep 1921847 = 2882771) B2882771
theorem B3897209 : Blo 1279958 3897209 := bstep (se 2 (by rfl) ⟨1461453, by rfl⟩ : syracuseStep 3897209 = 2922907) B2922907
theorem B2881961 : Blo 1279958 2881961 := bstep (se 2 (by rfl) ⟨1080735, by rfl⟩ : syracuseStep 2881961 = 2161471) B2161471
theorem B3242551 : Blo 1279958 3242551 := bstep (se 1 (by rfl) ⟨2431913, by rfl⟩ : syracuseStep 3242551 = 4863827) B4863827
theorem B2598139 : Blo 1279958 2598139 := bstep (se 1 (by rfl) ⟨1948604, by rfl⟩ : syracuseStep 2598139 = 3897209) B3897209
theorem B1280159 : Blo 1279958 1280159 := bstep (se 1 (by rfl) ⟨960119, by rfl⟩ : syracuseStep 1280159 = 1920239) B1920239
theorem B14600411 : Blo 1279958 14600411 := bstep (se 1 (by rfl) ⟨10950308, by rfl⟩ : syracuseStep 14600411 = 21900617) B21900617
theorem B47418169 : Blo 1279958 47418169 := bstep (se 2 (by rfl) ⟨17781813, by rfl⟩ : syracuseStep 47418169 = 35563627) B35563627
theorem B1281231 : Blo 1279958 1281231 := bstep (se 1 (by rfl) ⟨960923, by rfl⟩ : syracuseStep 1281231 = 1921847) B1921847
theorem B1921307 : Blo 1279958 1921307 := bstep (se 1 (by rfl) ⟨1440980, by rfl⟩ : syracuseStep 1921307 = 2881961) B2881961
theorem B44348147 : Blo 1279958 44348147 := bstep (se 1 (by rfl) ⟨33261110, by rfl⟩ : syracuseStep 44348147 = 66522221) B66522221
theorem B7296425 : Blo 1279958 7296425 := bstep (se 2 (by rfl) ⟨2736159, by rfl⟩ : syracuseStep 7296425 = 5472319) B5472319
theorem B8762975 : Blo 1279958 8762975 := bstep (se 1 (by rfl) ⟨6572231, by rfl⟩ : syracuseStep 8762975 = 13144463) B13144463
theorem B2430911 : Blo 1279958 2430911 := bstep (se 1 (by rfl) ⟨1823183, by rfl⟩ : syracuseStep 2430911 = 3646367) B3646367
theorem B4323401 : Blo 1279958 4323401 := bstep (se 2 (by rfl) ⟨1621275, by rfl⟩ : syracuseStep 4323401 = 3242551) B3242551
theorem B8765081 : Blo 1279958 8765081 := bstep (se 2 (by rfl) ⟨3286905, by rfl⟩ : syracuseStep 8765081 = 6573811) B6573811
theorem B29565431 : Blo 1279958 29565431 := bstep (se 1 (by rfl) ⟨22174073, by rfl⟩ : syracuseStep 29565431 = 44348147) B44348147
theorem B5841983 : Blo 1279958 5841983 := bstep (se 1 (by rfl) ⟨4381487, by rfl⟩ : syracuseStep 5841983 = 8762975) B8762975
theorem B9733607 : Blo 1279958 9733607 := bstep (se 1 (by rfl) ⟨7300205, by rfl⟩ : syracuseStep 9733607 = 14600411) B14600411
theorem B5843387 : Blo 1279958 5843387 := bstep (se 1 (by rfl) ⟨4382540, by rfl⟩ : syracuseStep 5843387 = 8765081) B8765081
theorem B6482429 : Blo 1279958 6482429 := bstep (se 3 (by rfl) ⟨1215455, by rfl⟩ : syracuseStep 6482429 = 2430911) B2430911
theorem B1280871 : Blo 1279958 1280871 := bstep (se 1 (by rfl) ⟨960653, by rfl⟩ : syracuseStep 1280871 = 1921307) B1921307
theorem B13856741 : Blo 1279958 13856741 := bstep (se 4 (by rfl) ⟨1299069, by rfl⟩ : syracuseStep 13856741 = 2598139) B2598139
theorem B4864283 : Blo 1279958 4864283 := bstep (se 1 (by rfl) ⟨3648212, by rfl⟩ : syracuseStep 4864283 = 7296425) B7296425
theorem B63224225 : Blo 1279958 63224225 := bstep (se 2 (by rfl) ⟨23709084, by rfl⟩ : syracuseStep 63224225 = 47418169) B47418169
theorem B2882267 : Blo 1279958 2882267 := bstep (se 1 (by rfl) ⟨2161700, by rfl⟩ : syracuseStep 2882267 = 4323401) B4323401
theorem B19710287 : Blo 1279958 19710287 := bstep (se 1 (by rfl) ⟨14782715, by rfl⟩ : syracuseStep 19710287 = 29565431) B29565431
theorem B6489071 : Blo 1279958 6489071 := bstep (se 1 (by rfl) ⟨4866803, by rfl⟩ : syracuseStep 6489071 = 9733607) B9733607
theorem B15582365 : Blo 1279958 15582365 := bstep (se 3 (by rfl) ⟨2921693, by rfl⟩ : syracuseStep 15582365 = 5843387) B5843387
theorem B42149483 : Blo 1279958 42149483 := bstep (se 1 (by rfl) ⟨31612112, by rfl⟩ : syracuseStep 42149483 = 63224225) B63224225
theorem B3894655 : Blo 1279958 3894655 := bstep (se 1 (by rfl) ⟨2920991, by rfl⟩ : syracuseStep 3894655 = 5841983) B5841983
theorem B4321619 : Blo 1279958 4321619 := bstep (se 1 (by rfl) ⟨3241214, by rfl⟩ : syracuseStep 4321619 = 6482429) B6482429
theorem B1921511 : Blo 1279958 1921511 := bstep (se 1 (by rfl) ⟨1441133, by rfl⟩ : syracuseStep 1921511 = 2882267) B2882267
theorem B9237827 : Blo 1279958 9237827 := bstep (se 1 (by rfl) ⟨6928370, by rfl⟩ : syracuseStep 9237827 = 13856741) B13856741
theorem B3242855 : Blo 1279958 3242855 := bstep (se 1 (by rfl) ⟨2432141, by rfl⟩ : syracuseStep 3242855 = 4864283) B4864283
theorem B13140191 : Blo 1279958 13140191 := bstep (se 1 (by rfl) ⟨9855143, by rfl⟩ : syracuseStep 13140191 = 19710287) B19710287
theorem B4326047 : Blo 1279958 4326047 := bstep (se 1 (by rfl) ⟨3244535, by rfl⟩ : syracuseStep 4326047 = 6489071) B6489071
theorem B10388243 : Blo 1279958 10388243 := bstep (se 1 (by rfl) ⟨7791182, by rfl⟩ : syracuseStep 10388243 = 15582365) B15582365
theorem B28099655 : Blo 1279958 28099655 := bstep (se 1 (by rfl) ⟨21074741, by rfl⟩ : syracuseStep 28099655 = 42149483) B42149483
theorem B1281007 : Blo 1279958 1281007 := bstep (se 1 (by rfl) ⟨960755, by rfl⟩ : syracuseStep 1281007 = 1921511) B1921511
theorem B2881079 : Blo 1279958 2881079 := bstep (se 1 (by rfl) ⟨2160809, by rfl⟩ : syracuseStep 2881079 = 4321619) B4321619
theorem B6158551 : Blo 1279958 6158551 := bstep (se 1 (by rfl) ⟨4618913, by rfl⟩ : syracuseStep 6158551 = 9237827) B9237827
theorem B5192873 : Blo 1279958 5192873 := bstep (se 2 (by rfl) ⟨1947327, by rfl⟩ : syracuseStep 5192873 = 3894655) B3894655
theorem B2161903 : Blo 1279958 2161903 := bstep (se 1 (by rfl) ⟨1621427, by rfl⟩ : syracuseStep 2161903 = 3242855) B3242855
theorem B2884031 : Blo 1279958 2884031 := bstep (se 1 (by rfl) ⟨2163023, by rfl⟩ : syracuseStep 2884031 = 4326047) B4326047
theorem B8211401 : Blo 1279958 8211401 := bstep (se 2 (by rfl) ⟨3079275, by rfl⟩ : syracuseStep 8211401 = 6158551) B6158551
theorem B6925495 : Blo 1279958 6925495 := bstep (se 1 (by rfl) ⟨5194121, by rfl⟩ : syracuseStep 6925495 = 10388243) B10388243
theorem B35040509 : Blo 1279958 35040509 := bstep (se 3 (by rfl) ⟨6570095, by rfl⟩ : syracuseStep 35040509 = 13140191) B13140191
theorem B1920719 : Blo 1279958 1920719 := bstep (se 1 (by rfl) ⟨1440539, by rfl⟩ : syracuseStep 1920719 = 2881079) B2881079
theorem B3461915 : Blo 1279958 3461915 := bstep (se 1 (by rfl) ⟨2596436, by rfl⟩ : syracuseStep 3461915 = 5192873) B5192873
theorem B18733103 : Blo 1279958 18733103 := bstep (se 1 (by rfl) ⟨14049827, by rfl⟩ : syracuseStep 18733103 = 28099655) B28099655
theorem B2882537 : Blo 1279958 2882537 := bstep (se 2 (by rfl) ⟨1080951, by rfl⟩ : syracuseStep 2882537 = 2161903) B2161903
theorem B9233993 : Blo 1279958 9233993 := bstep (se 2 (by rfl) ⟨3462747, by rfl⟩ : syracuseStep 9233993 = 6925495) B6925495
theorem B5474267 : Blo 1279958 5474267 := bstep (se 1 (by rfl) ⟨4105700, by rfl⟩ : syracuseStep 5474267 = 8211401) B8211401
theorem B1280479 : Blo 1279958 1280479 := bstep (se 1 (by rfl) ⟨960359, by rfl⟩ : syracuseStep 1280479 = 1920719) B1920719
theorem B12488735 : Blo 1279958 12488735 := bstep (se 1 (by rfl) ⟨9366551, by rfl⟩ : syracuseStep 12488735 = 18733103) B18733103
theorem B1921691 : Blo 1279958 1921691 := bstep (se 1 (by rfl) ⟨1441268, by rfl⟩ : syracuseStep 1921691 = 2882537) B2882537
theorem B23360339 : Blo 1279958 23360339 := bstep (se 1 (by rfl) ⟨17520254, by rfl⟩ : syracuseStep 23360339 = 35040509) B35040509
theorem B1922687 : Blo 1279958 1922687 := bstep (se 1 (by rfl) ⟨1442015, by rfl⟩ : syracuseStep 1922687 = 2884031) B2884031
theorem B2307943 : Blo 1279958 2307943 := bstep (se 1 (by rfl) ⟨1730957, by rfl⟩ : syracuseStep 2307943 = 3461915) B3461915
theorem B15573559 : Blo 1279958 15573559 := bstep (se 1 (by rfl) ⟨11680169, by rfl⟩ : syracuseStep 15573559 = 23360339) B23360339
theorem B8325823 : Blo 1279958 8325823 := bstep (se 1 (by rfl) ⟨6244367, by rfl⟩ : syracuseStep 8325823 = 12488735) B12488735
theorem B1281127 : Blo 1279958 1281127 := bstep (se 1 (by rfl) ⟨960845, by rfl⟩ : syracuseStep 1281127 = 1921691) B1921691
theorem B6155995 : Blo 1279958 6155995 := bstep (se 1 (by rfl) ⟨4616996, by rfl⟩ : syracuseStep 6155995 = 9233993) B9233993
theorem B1281791 : Blo 1279958 1281791 := bstep (se 1 (by rfl) ⟨961343, by rfl⟩ : syracuseStep 1281791 = 1922687) B1922687
theorem B3649511 : Blo 1279958 3649511 := bstep (se 1 (by rfl) ⟨2737133, by rfl⟩ : syracuseStep 3649511 = 5474267) B5474267
theorem B12309029 : Blo 1279958 12309029 := bstep (se 4 (by rfl) ⟨1153971, by rfl⟩ : syracuseStep 12309029 = 2307943) B2307943
theorem B11101097 : Blo 1279958 11101097 := bstep (se 2 (by rfl) ⟨4162911, by rfl⟩ : syracuseStep 11101097 = 8325823) B8325823
theorem B8206019 : Blo 1279958 8206019 := bstep (se 1 (by rfl) ⟨6154514, by rfl⟩ : syracuseStep 8206019 = 12309029) B12309029
theorem B20764745 : Blo 1279958 20764745 := bstep (se 2 (by rfl) ⟨7786779, by rfl⟩ : syracuseStep 20764745 = 15573559) B15573559
theorem B8207993 : Blo 1279958 8207993 := bstep (se 2 (by rfl) ⟨3077997, by rfl⟩ : syracuseStep 8207993 = 6155995) B6155995
theorem B2433007 : Blo 1279958 2433007 := bstep (se 1 (by rfl) ⟨1824755, by rfl⟩ : syracuseStep 2433007 = 3649511) B3649511
theorem B29602925 : Blo 1279958 29602925 := bstep (se 3 (by rfl) ⟨5550548, by rfl⟩ : syracuseStep 29602925 = 11101097) B11101097
theorem B5470679 : Blo 1279958 5470679 := bstep (se 1 (by rfl) ⟨4103009, by rfl⟩ : syracuseStep 5470679 = 8206019) B8206019
theorem B13843163 : Blo 1279958 13843163 := bstep (se 1 (by rfl) ⟨10382372, by rfl⟩ : syracuseStep 13843163 = 20764745) B20764745
theorem B5471995 : Blo 1279958 5471995 := bstep (se 1 (by rfl) ⟨4103996, by rfl⟩ : syracuseStep 5471995 = 8207993) B8207993
theorem B3244009 : Blo 1279958 3244009 := bstep (se 2 (by rfl) ⟨1216503, by rfl⟩ : syracuseStep 3244009 = 2433007) B2433007
theorem B19735283 : Blo 1279958 19735283 := bstep (se 1 (by rfl) ⟨14801462, by rfl⟩ : syracuseStep 19735283 = 29602925) B29602925
theorem B3647119 : Blo 1279958 3647119 := bstep (se 1 (by rfl) ⟨2735339, by rfl⟩ : syracuseStep 3647119 = 5470679) B5470679
theorem B9228775 : Blo 1279958 9228775 := bstep (se 1 (by rfl) ⟨6921581, by rfl⟩ : syracuseStep 9228775 = 13843163) B13843163
theorem B7295993 : Blo 1279958 7295993 := bstep (se 2 (by rfl) ⟨2735997, by rfl⟩ : syracuseStep 7295993 = 5471995) B5471995
theorem B4325345 : Blo 1279958 4325345 := bstep (se 2 (by rfl) ⟨1622004, by rfl⟩ : syracuseStep 4325345 = 3244009) B3244009
theorem B12305033 : Blo 1279958 12305033 := bstep (se 2 (by rfl) ⟨4614387, by rfl⟩ : syracuseStep 12305033 = 9228775) B9228775
theorem B52627421 : Blo 1279958 52627421 := bstep (se 3 (by rfl) ⟨9867641, by rfl⟩ : syracuseStep 52627421 = 19735283) B19735283
theorem B4862825 : Blo 1279958 4862825 := bstep (se 2 (by rfl) ⟨1823559, by rfl⟩ : syracuseStep 4862825 = 3647119) B3647119
theorem B4863995 : Blo 1279958 4863995 := bstep (se 1 (by rfl) ⟨3647996, by rfl⟩ : syracuseStep 4863995 = 7295993) B7295993
theorem B2883563 : Blo 1279958 2883563 := bstep (se 1 (by rfl) ⟨2162672, by rfl⟩ : syracuseStep 2883563 = 4325345) B4325345
theorem B8203355 : Blo 1279958 8203355 := bstep (se 1 (by rfl) ⟨6152516, by rfl⟩ : syracuseStep 8203355 = 12305033) B12305033
theorem B1922375 : Blo 1279958 1922375 := bstep (se 1 (by rfl) ⟨1441781, by rfl⟩ : syracuseStep 1922375 = 2883563) B2883563
theorem B3241883 : Blo 1279958 3241883 := bstep (se 1 (by rfl) ⟨2431412, by rfl⟩ : syracuseStep 3241883 = 4862825) B4862825
theorem B35084947 : Blo 1279958 35084947 := bstep (se 1 (by rfl) ⟨26313710, by rfl⟩ : syracuseStep 35084947 = 52627421) B52627421
theorem B3242663 : Blo 1279958 3242663 := bstep (se 1 (by rfl) ⟨2431997, by rfl⟩ : syracuseStep 3242663 = 4863995) B4863995
theorem B46779929 : Blo 1279958 46779929 := bstep (se 2 (by rfl) ⟨17542473, by rfl⟩ : syracuseStep 46779929 = 35084947) B35084947
theorem B1281583 : Blo 1279958 1281583 := bstep (se 1 (by rfl) ⟨961187, by rfl⟩ : syracuseStep 1281583 = 1922375) B1922375
theorem B5468903 : Blo 1279958 5468903 := bstep (se 1 (by rfl) ⟨4101677, by rfl⟩ : syracuseStep 5468903 = 8203355) B8203355
theorem B2161255 : Blo 1279958 2161255 := bstep (se 1 (by rfl) ⟨1620941, by rfl⟩ : syracuseStep 2161255 = 3241883) B3241883
theorem B2161775 : Blo 1279958 2161775 := bstep (se 1 (by rfl) ⟨1621331, by rfl⟩ : syracuseStep 2161775 = 3242663) B3242663
theorem B3645935 : Blo 1279958 3645935 := bstep (se 1 (by rfl) ⟨2734451, by rfl⟩ : syracuseStep 3645935 = 5468903) B5468903
theorem B2881673 : Blo 1279958 2881673 := bstep (se 2 (by rfl) ⟨1080627, by rfl⟩ : syracuseStep 2881673 = 2161255) B2161255
theorem B1441183 : Blo 1279958 1441183 := bstep (se 1 (by rfl) ⟨1080887, by rfl⟩ : syracuseStep 1441183 = 2161775) B2161775
theorem B31186619 : Blo 1279958 31186619 := bstep (se 1 (by rfl) ⟨23389964, by rfl⟩ : syracuseStep 31186619 = 46779929) B46779929
theorem B1921115 : Blo 1279958 1921115 := bstep (se 1 (by rfl) ⟨1440836, by rfl⟩ : syracuseStep 1921115 = 2881673) B2881673
theorem B1921577 : Blo 1279958 1921577 := bstep (se 2 (by rfl) ⟨720591, by rfl⟩ : syracuseStep 1921577 = 1441183) B1441183
theorem B2430623 : Blo 1279958 2430623 := bstep (se 1 (by rfl) ⟨1822967, by rfl⟩ : syracuseStep 2430623 = 3645935) B3645935
theorem B20791079 : Blo 1279958 20791079 := bstep (se 1 (by rfl) ⟨15593309, by rfl⟩ : syracuseStep 20791079 = 31186619) B31186619
theorem B1280743 : Blo 1279958 1280743 := bstep (se 1 (by rfl) ⟨960557, by rfl⟩ : syracuseStep 1280743 = 1921115) B1921115
theorem B1281051 : Blo 1279958 1281051 := bstep (se 1 (by rfl) ⟨960788, by rfl⟩ : syracuseStep 1281051 = 1921577) B1921577
theorem B1620415 : Blo 1279958 1620415 := bstep (se 1 (by rfl) ⟨1215311, by rfl⟩ : syracuseStep 1620415 = 2430623) B2430623
theorem B13860719 : Blo 1279958 13860719 := bstep (se 1 (by rfl) ⟨10395539, by rfl⟩ : syracuseStep 13860719 = 20791079) B20791079
theorem B2160553 : Blo 1279958 2160553 := bstep (se 2 (by rfl) ⟨810207, by rfl⟩ : syracuseStep 2160553 = 1620415) B1620415
theorem B9240479 : Blo 1279958 9240479 := bstep (se 1 (by rfl) ⟨6930359, by rfl⟩ : syracuseStep 9240479 = 13860719) B13860719
theorem B2880737 : Blo 1279958 2880737 := bstep (se 2 (by rfl) ⟨1080276, by rfl⟩ : syracuseStep 2880737 = 2160553) B2160553
theorem B6160319 : Blo 1279958 6160319 := bstep (se 1 (by rfl) ⟨4620239, by rfl⟩ : syracuseStep 6160319 = 9240479) B9240479
theorem B4106879 : Blo 1279958 4106879 := bstep (se 1 (by rfl) ⟨3080159, by rfl⟩ : syracuseStep 4106879 = 6160319) B6160319
theorem B1920491 : Blo 1279958 1920491 := bstep (se 1 (by rfl) ⟨1440368, by rfl⟩ : syracuseStep 1920491 = 2880737) B2880737
theorem B2737919 : Blo 1279958 2737919 := bstep (se 1 (by rfl) ⟨2053439, by rfl⟩ : syracuseStep 2737919 = 4106879) B4106879
theorem B1280327 : Blo 1279958 1280327 := bstep (se 1 (by rfl) ⟨960245, by rfl⟩ : syracuseStep 1280327 = 1920491) B1920491
theorem B7301117 : Blo 1279958 7301117 := bstep (se 3 (by rfl) ⟨1368959, by rfl⟩ : syracuseStep 7301117 = 2737919) B2737919
theorem B4867411 : Blo 1279958 4867411 := bstep (se 1 (by rfl) ⟨3650558, by rfl⟩ : syracuseStep 4867411 = 7301117) B7301117
theorem B6489881 : Blo 1279958 6489881 := bstep (se 2 (by rfl) ⟨2433705, by rfl⟩ : syracuseStep 6489881 = 4867411) B4867411
theorem B4326587 : Blo 1279958 4326587 := bstep (se 1 (by rfl) ⟨3244940, by rfl⟩ : syracuseStep 4326587 = 6489881) B6489881
theorem B2884391 : Blo 1279958 2884391 := bstep (se 1 (by rfl) ⟨2163293, by rfl⟩ : syracuseStep 2884391 = 4326587) B4326587
theorem B1922927 : Blo 1279958 1922927 := bstep (se 1 (by rfl) ⟨1442195, by rfl⟩ : syracuseStep 1922927 = 2884391) B2884391
theorem B1281951 : Blo 1279958 1281951 := bstep (se 1 (by rfl) ⟨961463, by rfl⟩ : syracuseStep 1281951 = 1922927) B1922927

theorem C0 (j : ℕ) (h1 : 319989 ≤ j) (h2 : j ≤ 320488) : Blo 1279958 (4 * j + 3) := by
  interval_cases j
  · exact B1279959
  · exact B1279963
  · exact B1279967
  · exact B1279971
  · exact B1279975
  · exact B1279979
  · exact B1279983
  · exact B1279987
  · exact B1279991
  · exact B1279995
  · exact B1279999
  · exact B1280003
  · exact B1280007
  · exact B1280011
  · exact B1280015
  · exact B1280019
  · exact B1280023
  · exact B1280027
  · exact B1280031
  · exact B1280035
  · exact B1280039
  · exact B1280043
  · exact B1280047
  · exact B1280051
  · exact B1280055
  · exact B1280059
  · exact B1280063
  · exact B1280067
  · exact B1280071
  · exact B1280075
  · exact B1280079
  · exact B1280083
  · exact B1280087
  · exact B1280091
  · exact B1280095
  · exact B1280099
  · exact B1280103
  · exact B1280107
  · exact B1280111
  · exact B1280115
  · exact B1280119
  · exact B1280123
  · exact B1280127
  · exact B1280131
  · exact B1280135
  · exact B1280139
  · exact B1280143
  · exact B1280147
  · exact B1280151
  · exact B1280155
  · exact B1280159
  · exact B1280163
  · exact B1280167
  · exact B1280171
  · exact B1280175
  · exact B1280179
  · exact B1280183
  · exact B1280187
  · exact B1280191
  · exact B1280195
  · exact B1280199
  · exact B1280203
  · exact B1280207
  · exact B1280211
  · exact B1280215
  · exact B1280219
  · exact B1280223
  · exact B1280227
  · exact B1280231
  · exact B1280235
  · exact B1280239
  · exact B1280243
  · exact B1280247
  · exact B1280251
  · exact B1280255
  · exact B1280259
  · exact B1280263
  · exact B1280267
  · exact B1280271
  · exact B1280275
  · exact B1280279
  · exact B1280283
  · exact B1280287
  · exact B1280291
  · exact B1280295
  · exact B1280299
  · exact B1280303
  · exact B1280307
  · exact B1280311
  · exact B1280315
  · exact B1280319
  · exact B1280323
  · exact B1280327
  · exact B1280331
  · exact B1280335
  · exact B1280339
  · exact B1280343
  · exact B1280347
  · exact B1280351
  · exact B1280355
  · exact B1280359
  · exact B1280363
  · exact B1280367
  · exact B1280371
  · exact B1280375
  · exact B1280379
  · exact B1280383
  · exact B1280387
  · exact B1280391
  · exact B1280395
  · exact B1280399
  · exact B1280403
  · exact B1280407
  · exact B1280411
  · exact B1280415
  · exact B1280419
  · exact B1280423
  · exact B1280427
  · exact B1280431
  · exact B1280435
  · exact B1280439
  · exact B1280443
  · exact B1280447
  · exact B1280451
  · exact B1280455
  · exact B1280459
  · exact B1280463
  · exact B1280467
  · exact B1280471
  · exact B1280475
  · exact B1280479
  · exact B1280483
  · exact B1280487
  · exact B1280491
  · exact B1280495
  · exact B1280499
  · exact B1280503
  · exact B1280507
  · exact B1280511
  · exact B1280515
  · exact B1280519
  · exact B1280523
  · exact B1280527
  · exact B1280531
  · exact B1280535
  · exact B1280539
  · exact B1280543
  · exact B1280547
  · exact B1280551
  · exact B1280555
  · exact B1280559
  · exact B1280563
  · exact B1280567
  · exact B1280571
  · exact B1280575
  · exact B1280579
  · exact B1280583
  · exact B1280587
  · exact B1280591
  · exact B1280595
  · exact B1280599
  · exact B1280603
  · exact B1280607
  · exact B1280611
  · exact B1280615
  · exact B1280619
  · exact B1280623
  · exact B1280627
  · exact B1280631
  · exact B1280635
  · exact B1280639
  · exact B1280643
  · exact B1280647
  · exact B1280651
  · exact B1280655
  · exact B1280659
  · exact B1280663
  · exact B1280667
  · exact B1280671
  · exact B1280675
  · exact B1280679
  · exact B1280683
  · exact B1280687
  · exact B1280691
  · exact B1280695
  · exact B1280699
  · exact B1280703
  · exact B1280707
  · exact B1280711
  · exact B1280715
  · exact B1280719
  · exact B1280723
  · exact B1280727
  · exact B1280731
  · exact B1280735
  · exact B1280739
  · exact B1280743
  · exact B1280747
  · exact B1280751
  · exact B1280755
  · exact B1280759
  · exact B1280763
  · exact B1280767
  · exact B1280771
  · exact B1280775
  · exact B1280779
  · exact B1280783
  · exact B1280787
  · exact B1280791
  · exact B1280795
  · exact B1280799
  · exact B1280803
  · exact B1280807
  · exact B1280811
  · exact B1280815
  · exact B1280819
  · exact B1280823
  · exact B1280827
  · exact B1280831
  · exact B1280835
  · exact B1280839
  · exact B1280843
  · exact B1280847
  · exact B1280851
  · exact B1280855
  · exact B1280859
  · exact B1280863
  · exact B1280867
  · exact B1280871
  · exact B1280875
  · exact B1280879
  · exact B1280883
  · exact B1280887
  · exact B1280891
  · exact B1280895
  · exact B1280899
  · exact B1280903
  · exact B1280907
  · exact B1280911
  · exact B1280915
  · exact B1280919
  · exact B1280923
  · exact B1280927
  · exact B1280931
  · exact B1280935
  · exact B1280939
  · exact B1280943
  · exact B1280947
  · exact B1280951
  · exact B1280955
  · exact B1280959
  · exact B1280963
  · exact B1280967
  · exact B1280971
  · exact B1280975
  · exact B1280979
  · exact B1280983
  · exact B1280987
  · exact B1280991
  · exact B1280995
  · exact B1280999
  · exact B1281003
  · exact B1281007
  · exact B1281011
  · exact B1281015
  · exact B1281019
  · exact B1281023
  · exact B1281027
  · exact B1281031
  · exact B1281035
  · exact B1281039
  · exact B1281043
  · exact B1281047
  · exact B1281051
  · exact B1281055
  · exact B1281059
  · exact B1281063
  · exact B1281067
  · exact B1281071
  · exact B1281075
  · exact B1281079
  · exact B1281083
  · exact B1281087
  · exact B1281091
  · exact B1281095
  · exact B1281099
  · exact B1281103
  · exact B1281107
  · exact B1281111
  · exact B1281115
  · exact B1281119
  · exact B1281123
  · exact B1281127
  · exact B1281131
  · exact B1281135
  · exact B1281139
  · exact B1281143
  · exact B1281147
  · exact B1281151
  · exact B1281155
  · exact B1281159
  · exact B1281163
  · exact B1281167
  · exact B1281171
  · exact B1281175
  · exact B1281179
  · exact B1281183
  · exact B1281187
  · exact B1281191
  · exact B1281195
  · exact B1281199
  · exact B1281203
  · exact B1281207
  · exact B1281211
  · exact B1281215
  · exact B1281219
  · exact B1281223
  · exact B1281227
  · exact B1281231
  · exact B1281235
  · exact B1281239
  · exact B1281243
  · exact B1281247
  · exact B1281251
  · exact B1281255
  · exact B1281259
  · exact B1281263
  · exact B1281267
  · exact B1281271
  · exact B1281275
  · exact B1281279
  · exact B1281283
  · exact B1281287
  · exact B1281291
  · exact B1281295
  · exact B1281299
  · exact B1281303
  · exact B1281307
  · exact B1281311
  · exact B1281315
  · exact B1281319
  · exact B1281323
  · exact B1281327
  · exact B1281331
  · exact B1281335
  · exact B1281339
  · exact B1281343
  · exact B1281347
  · exact B1281351
  · exact B1281355
  · exact B1281359
  · exact B1281363
  · exact B1281367
  · exact B1281371
  · exact B1281375
  · exact B1281379
  · exact B1281383
  · exact B1281387
  · exact B1281391
  · exact B1281395
  · exact B1281399
  · exact B1281403
  · exact B1281407
  · exact B1281411
  · exact B1281415
  · exact B1281419
  · exact B1281423
  · exact B1281427
  · exact B1281431
  · exact B1281435
  · exact B1281439
  · exact B1281443
  · exact B1281447
  · exact B1281451
  · exact B1281455
  · exact B1281459
  · exact B1281463
  · exact B1281467
  · exact B1281471
  · exact B1281475
  · exact B1281479
  · exact B1281483
  · exact B1281487
  · exact B1281491
  · exact B1281495
  · exact B1281499
  · exact B1281503
  · exact B1281507
  · exact B1281511
  · exact B1281515
  · exact B1281519
  · exact B1281523
  · exact B1281527
  · exact B1281531
  · exact B1281535
  · exact B1281539
  · exact B1281543
  · exact B1281547
  · exact B1281551
  · exact B1281555
  · exact B1281559
  · exact B1281563
  · exact B1281567
  · exact B1281571
  · exact B1281575
  · exact B1281579
  · exact B1281583
  · exact B1281587
  · exact B1281591
  · exact B1281595
  · exact B1281599
  · exact B1281603
  · exact B1281607
  · exact B1281611
  · exact B1281615
  · exact B1281619
  · exact B1281623
  · exact B1281627
  · exact B1281631
  · exact B1281635
  · exact B1281639
  · exact B1281643
  · exact B1281647
  · exact B1281651
  · exact B1281655
  · exact B1281659
  · exact B1281663
  · exact B1281667
  · exact B1281671
  · exact B1281675
  · exact B1281679
  · exact B1281683
  · exact B1281687
  · exact B1281691
  · exact B1281695
  · exact B1281699
  · exact B1281703
  · exact B1281707
  · exact B1281711
  · exact B1281715
  · exact B1281719
  · exact B1281723
  · exact B1281727
  · exact B1281731
  · exact B1281735
  · exact B1281739
  · exact B1281743
  · exact B1281747
  · exact B1281751
  · exact B1281755
  · exact B1281759
  · exact B1281763
  · exact B1281767
  · exact B1281771
  · exact B1281775
  · exact B1281779
  · exact B1281783
  · exact B1281787
  · exact B1281791
  · exact B1281795
  · exact B1281799
  · exact B1281803
  · exact B1281807
  · exact B1281811
  · exact B1281815
  · exact B1281819
  · exact B1281823
  · exact B1281827
  · exact B1281831
  · exact B1281835
  · exact B1281839
  · exact B1281843
  · exact B1281847
  · exact B1281851
  · exact B1281855
  · exact B1281859
  · exact B1281863
  · exact B1281867
  · exact B1281871
  · exact B1281875
  · exact B1281879
  · exact B1281883
  · exact B1281887
  · exact B1281891
  · exact B1281895
  · exact B1281899
  · exact B1281903
  · exact B1281907
  · exact B1281911
  · exact B1281915
  · exact B1281919
  · exact B1281923
  · exact B1281927
  · exact B1281931
  · exact B1281935
  · exact B1281939
  · exact B1281943
  · exact B1281947
  · exact B1281951
  · exact B1281955

theorem solution (m : ℕ) (hlo : 1279958 ≤ m) (hhi : m ≤ 1281958) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 319989 ≤ j := by omega
    have hj2 : j ≤ 320488 := by omega
    have hb : Blo 1279958 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
