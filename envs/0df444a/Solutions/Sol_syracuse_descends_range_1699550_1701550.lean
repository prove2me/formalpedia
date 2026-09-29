-- Prove2me | solution 1 for syracuse_descends_range_1699550_1701550
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:25:34.283268+00:00
-- url     : https://prove2.me/submissions/9619e1e2-e0ce-4bcb-8829-80f87231c162

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


theorem B8609813 : Blo 1699550 8609813 := bbase (se 6 (by rfl) ⟨201792, by rfl⟩ : syracuseStep 8609813 = 403585) (by norm_num)
theorem B4087837 : Blo 1699550 4087837 := bbase (se 3 (by rfl) ⟨766469, by rfl⟩ : syracuseStep 4087837 = 1532939) (by norm_num)
theorem B3825701 : Blo 1699550 3825701 := bbase (se 4 (by rfl) ⟨358659, by rfl⟩ : syracuseStep 3825701 = 717319) (by norm_num)
theorem B5742629 : Blo 1699550 5742629 := bbase (se 4 (by rfl) ⟨538371, by rfl⟩ : syracuseStep 5742629 = 1076743) (by norm_num)
theorem B3227701 : Blo 1699550 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B3063917 : Blo 1699550 3063917 := bbase (se 3 (by rfl) ⟨574484, by rfl⟩ : syracuseStep 3063917 = 1148969) (by norm_num)
theorem B3825773 : Blo 1699550 3825773 := bbase (se 3 (by rfl) ⟨717332, by rfl⟩ : syracuseStep 3825773 = 1434665) (by norm_num)
theorem B6455477 : Blo 1699550 6455477 := bbase (se 5 (by rfl) ⟨302600, by rfl⟩ : syracuseStep 6455477 = 605201) (by norm_num)
theorem B3825845 : Blo 1699550 3825845 := bbase (se 5 (by rfl) ⟨179336, by rfl⟩ : syracuseStep 3825845 = 358673) (by norm_num)
theorem B3227845 : Blo 1699550 3227845 := bbase (se 4 (by rfl) ⟨302610, by rfl⟩ : syracuseStep 3227845 = 605221) (by norm_num)
theorem B11043029 : Blo 1699550 11043029 := bbase (se 7 (by rfl) ⟨129410, by rfl⟩ : syracuseStep 11043029 = 258821) (by norm_num)
theorem B3825917 : Blo 1699550 3825917 := bbase (se 3 (by rfl) ⟨717359, by rfl⟩ : syracuseStep 3825917 = 1434719) (by norm_num)
theorem B7266581 : Blo 1699550 7266581 := bbase (se 6 (by rfl) ⟨170310, by rfl⟩ : syracuseStep 7266581 = 340621) (by norm_num)
theorem B3825989 : Blo 1699550 3825989 := bbase (se 4 (by rfl) ⟨358686, by rfl⟩ : syracuseStep 3825989 = 717373) (by norm_num)
theorem B14524757 : Blo 1699550 14524757 := bbase (se 10 (by rfl) ⟨21276, by rfl⟩ : syracuseStep 14524757 = 42553) (by norm_num)
theorem B3228005 : Blo 1699550 3228005 := bbase (se 4 (by rfl) ⟨302625, by rfl⟩ : syracuseStep 3228005 = 605251) (by norm_num)
theorem B3826061 : Blo 1699550 3826061 := bbase (se 3 (by rfl) ⟨717386, by rfl⟩ : syracuseStep 3826061 = 1434773) (by norm_num)
theorem B3826133 : Blo 1699550 3826133 := bbase (se 7 (by rfl) ⟨44837, by rfl⟩ : syracuseStep 3826133 = 89675) (by norm_num)
theorem B3228149 : Blo 1699550 3228149 := bbase (se 5 (by rfl) ⟨151319, by rfl⟩ : syracuseStep 3228149 = 302639) (by norm_num)
theorem B2908685 : Blo 1699550 2908685 := bbase (se 3 (by rfl) ⟨545378, by rfl⟩ : syracuseStep 2908685 = 1090757) (by norm_num)
theorem B3826205 : Blo 1699550 3826205 := bbase (se 3 (by rfl) ⟨717413, by rfl⟩ : syracuseStep 3826205 = 1434827) (by norm_num)
theorem B3826277 : Blo 1699550 3826277 := bbase (se 4 (by rfl) ⟨358713, by rfl⟩ : syracuseStep 3826277 = 717427) (by norm_num)
theorem B3826349 : Blo 1699550 3826349 := bbase (se 3 (by rfl) ⟨717440, by rfl⟩ : syracuseStep 3826349 = 1434881) (by norm_num)
theorem B19366613 : Blo 1699550 19366613 := bbase (se 7 (by rfl) ⟨226952, by rfl⟩ : syracuseStep 19366613 = 453905) (by norm_num)
theorem B3826421 : Blo 1699550 3826421 := bbase (se 5 (by rfl) ⟨179363, by rfl⟩ : syracuseStep 3826421 = 358727) (by norm_num)
theorem B3228437 : Blo 1699550 3228437 := bbase (se 6 (by rfl) ⟨75666, by rfl⟩ : syracuseStep 3228437 = 151333) (by norm_num)
theorem B29868821 : Blo 1699550 29868821 := bbase (se 6 (by rfl) ⟨700050, by rfl⟩ : syracuseStep 29868821 = 1400101) (by norm_num)
theorem B3826493 : Blo 1699550 3826493 := bbase (se 3 (by rfl) ⟨717467, by rfl⟩ : syracuseStep 3826493 = 1434935) (by norm_num)
theorem B2868061 : Blo 1699550 2868061 := bbase (se 3 (by rfl) ⟨537761, by rfl⟩ : syracuseStep 2868061 = 1075523) (by norm_num)
theorem B16352117 : Blo 1699550 16352117 := bbase (se 5 (by rfl) ⟨766505, by rfl⟩ : syracuseStep 16352117 = 1533011) (by norm_num)
theorem B3826565 : Blo 1699550 3826565 := bbase (se 4 (by rfl) ⟨358740, by rfl⟩ : syracuseStep 3826565 = 717481) (by norm_num)
theorem B3228589 : Blo 1699550 3228589 := bbase (se 3 (by rfl) ⟨605360, by rfl⟩ : syracuseStep 3228589 = 1210721) (by norm_num)
theorem B2868149 : Blo 1699550 2868149 := bbase (se 5 (by rfl) ⟨134444, by rfl⟩ : syracuseStep 2868149 = 268889) (by norm_num)
theorem B3826637 : Blo 1699550 3826637 := bbase (se 3 (by rfl) ⟨717494, by rfl⟩ : syracuseStep 3826637 = 1434989) (by norm_num)
theorem B7267333 : Blo 1699550 7267333 := bbase (se 4 (by rfl) ⟨681312, by rfl⟩ : syracuseStep 7267333 = 1362625) (by norm_num)
theorem B3826709 : Blo 1699550 3826709 := bbase (se 6 (by rfl) ⟨89688, by rfl⟩ : syracuseStep 3826709 = 179377) (by norm_num)
theorem B2868277 : Blo 1699550 2868277 := bbase (se 5 (by rfl) ⟨134450, by rfl⟩ : syracuseStep 2868277 = 268901) (by norm_num)
theorem B3826781 : Blo 1699550 3826781 := bbase (se 3 (by rfl) ⟨717521, by rfl⟩ : syracuseStep 3826781 = 1435043) (by norm_num)
theorem B2868365 : Blo 1699550 2868365 := bbase (se 3 (by rfl) ⟨537818, by rfl⟩ : syracuseStep 2868365 = 1075637) (by norm_num)
theorem B3826853 : Blo 1699550 3826853 := bbase (se 4 (by rfl) ⟨358767, by rfl⟩ : syracuseStep 3826853 = 717535) (by norm_num)
theorem B3228893 : Blo 1699550 3228893 := bbase (se 3 (by rfl) ⟨605417, by rfl⟩ : syracuseStep 3228893 = 1210835) (by norm_num)
theorem B3826925 : Blo 1699550 3826925 := bbase (se 3 (by rfl) ⟨717548, by rfl⟩ : syracuseStep 3826925 = 1435097) (by norm_num)
theorem B2868493 : Blo 1699550 2868493 := bbase (se 3 (by rfl) ⟨537842, by rfl⟩ : syracuseStep 2868493 = 1075685) (by norm_num)
theorem B8611109 : Blo 1699550 8611109 := bbase (se 4 (by rfl) ⟨807291, by rfl⟩ : syracuseStep 8611109 = 1614583) (by norm_num)
theorem B3826997 : Blo 1699550 3826997 := bbase (se 5 (by rfl) ⟨179390, by rfl⟩ : syracuseStep 3826997 = 358781) (by norm_num)
theorem B3630413 : Blo 1699550 3630413 := bbase (se 3 (by rfl) ⟨680702, by rfl⟩ : syracuseStep 3630413 = 1361405) (by norm_num)
theorem B4302173 : Blo 1699550 4302173 := bbase (se 3 (by rfl) ⟨806657, by rfl⟩ : syracuseStep 4302173 = 1613315) (by norm_num)
theorem B2868581 : Blo 1699550 2868581 := bbase (se 4 (by rfl) ⟨268929, by rfl⟩ : syracuseStep 2868581 = 537859) (by norm_num)
theorem B3827069 : Blo 1699550 3827069 := bbase (se 3 (by rfl) ⟨717575, by rfl⟩ : syracuseStep 3827069 = 1435151) (by norm_num)
theorem B3827141 : Blo 1699550 3827141 := bbase (se 4 (by rfl) ⟨358794, by rfl⟩ : syracuseStep 3827141 = 717589) (by norm_num)
theorem B3630557 : Blo 1699550 3630557 := bbase (se 3 (by rfl) ⟨680729, by rfl⟩ : syracuseStep 3630557 = 1361459) (by norm_num)
theorem B2868709 : Blo 1699550 2868709 := bbase (se 4 (by rfl) ⟨268941, by rfl⟩ : syracuseStep 2868709 = 537883) (by norm_num)
theorem B12920309 : Blo 1699550 12920309 := bbase (se 5 (by rfl) ⟨605639, by rfl⟩ : syracuseStep 12920309 = 1211279) (by norm_num)
theorem B3827213 : Blo 1699550 3827213 := bbase (se 3 (by rfl) ⟨717602, by rfl⟩ : syracuseStep 3827213 = 1435205) (by norm_num)
theorem B2868797 : Blo 1699550 2868797 := bbase (se 3 (by rfl) ⟨537899, by rfl⟩ : syracuseStep 2868797 = 1075799) (by norm_num)
theorem B2549333 : Blo 1699550 2549333 := bbase (se 8 (by rfl) ⟨14937, by rfl⟩ : syracuseStep 2549333 = 29875) (by norm_num)
theorem B3827285 : Blo 1699550 3827285 := bbase (se 8 (by rfl) ⟨22425, by rfl⟩ : syracuseStep 3827285 = 44851) (by norm_num)
theorem B2549357 : Blo 1699550 2549357 := bbase (se 3 (by rfl) ⟨478004, by rfl⟩ : syracuseStep 2549357 = 956009) (by norm_num)
theorem B2549381 : Blo 1699550 2549381 := bbase (se 4 (by rfl) ⟨239004, by rfl⟩ : syracuseStep 2549381 = 478009) (by norm_num)
theorem B2762381 : Blo 1699550 2762381 := bbase (se 3 (by rfl) ⟨517946, by rfl⟩ : syracuseStep 2762381 = 1035893) (by norm_num)
theorem B9684629 : Blo 1699550 9684629 := bbase (se 6 (by rfl) ⟨226983, by rfl⟩ : syracuseStep 9684629 = 453967) (by norm_num)
theorem B2549405 : Blo 1699550 2549405 := bbase (se 3 (by rfl) ⟨478013, by rfl⟩ : syracuseStep 2549405 = 956027) (by norm_num)
theorem B3827357 : Blo 1699550 3827357 := bbase (se 3 (by rfl) ⟨717629, by rfl⟩ : syracuseStep 3827357 = 1435259) (by norm_num)
theorem B2549429 : Blo 1699550 2549429 := bbase (se 5 (by rfl) ⟨119504, by rfl⟩ : syracuseStep 2549429 = 239009) (by norm_num)
theorem B4302517 : Blo 1699550 4302517 := bbase (se 5 (by rfl) ⟨201680, by rfl⟩ : syracuseStep 4302517 = 403361) (by norm_num)
theorem B2868925 : Blo 1699550 2868925 := bbase (se 3 (by rfl) ⟨537923, by rfl⟩ : syracuseStep 2868925 = 1075847) (by norm_num)
theorem B2549453 : Blo 1699550 2549453 := bbase (se 3 (by rfl) ⟨478022, by rfl⟩ : syracuseStep 2549453 = 956045) (by norm_num)
theorem B5736149 : Blo 1699550 5736149 := bbase (se 7 (by rfl) ⟨67220, by rfl⟩ : syracuseStep 5736149 = 134441) (by norm_num)
theorem B2549477 : Blo 1699550 2549477 := bbase (se 4 (by rfl) ⟨239013, by rfl⟩ : syracuseStep 2549477 = 478027) (by norm_num)
theorem B4908773 : Blo 1699550 4908773 := bbase (se 4 (by rfl) ⟨460197, by rfl⟩ : syracuseStep 4908773 = 920395) (by norm_num)
theorem B3827429 : Blo 1699550 3827429 := bbase (se 4 (by rfl) ⟨358821, by rfl⟩ : syracuseStep 3827429 = 717643) (by norm_num)
theorem B7268069 : Blo 1699550 7268069 := bbase (se 4 (by rfl) ⟨681381, by rfl⟩ : syracuseStep 7268069 = 1362763) (by norm_num)
theorem B2180857 : Blo 1699550 2180857 := bbase (se 2 (by rfl) ⟨817821, by rfl⟩ : syracuseStep 2180857 = 1635643) (by norm_num)
theorem B2549501 : Blo 1699550 2549501 := bbase (se 3 (by rfl) ⟨478031, by rfl⟩ : syracuseStep 2549501 = 956063) (by norm_num)
theorem B2549525 : Blo 1699550 2549525 := bbase (se 6 (by rfl) ⟨59754, by rfl⟩ : syracuseStep 2549525 = 119509) (by norm_num)
theorem B13264661 : Blo 1699550 13264661 := bbase (se 6 (by rfl) ⟨310890, by rfl⟩ : syracuseStep 13264661 = 621781) (by norm_num)
theorem B2869013 : Blo 1699550 2869013 := bbase (se 6 (by rfl) ⟨67242, by rfl⟩ : syracuseStep 2869013 = 134485) (by norm_num)
theorem B4302629 : Blo 1699550 4302629 := bbase (se 4 (by rfl) ⟨403371, by rfl⟩ : syracuseStep 4302629 = 806743) (by norm_num)
theorem B2549549 : Blo 1699550 2549549 := bbase (se 3 (by rfl) ⟨478040, by rfl⟩ : syracuseStep 2549549 = 956081) (by norm_num)
theorem B3827501 : Blo 1699550 3827501 := bbase (se 3 (by rfl) ⟨717656, by rfl⟩ : syracuseStep 3827501 = 1435313) (by norm_num)
theorem B2549573 : Blo 1699550 2549573 := bbase (se 4 (by rfl) ⟨239022, by rfl⟩ : syracuseStep 2549573 = 478045) (by norm_num)
theorem B2549597 : Blo 1699550 2549597 := bbase (se 3 (by rfl) ⟨478049, by rfl⟩ : syracuseStep 2549597 = 956099) (by norm_num)
theorem B2549621 : Blo 1699550 2549621 := bbase (se 5 (by rfl) ⟨119513, by rfl⟩ : syracuseStep 2549621 = 239027) (by norm_num)
theorem B3827573 : Blo 1699550 3827573 := bbase (se 5 (by rfl) ⟨179417, by rfl⟩ : syracuseStep 3827573 = 358835) (by norm_num)
theorem B2549645 : Blo 1699550 2549645 := bbase (se 3 (by rfl) ⟨478058, by rfl⟩ : syracuseStep 2549645 = 956117) (by norm_num)
theorem B2869141 : Blo 1699550 2869141 := bbase (se 6 (by rfl) ⟨67245, by rfl⟩ : syracuseStep 2869141 = 134491) (by norm_num)
theorem B12912533 : Blo 1699550 12912533 := bbase (se 6 (by rfl) ⟨302637, by rfl⟩ : syracuseStep 12912533 = 605275) (by norm_num)
theorem B2549669 : Blo 1699550 2549669 := bbase (se 4 (by rfl) ⟨239031, by rfl⟩ : syracuseStep 2549669 = 478063) (by norm_num)
theorem B2549693 : Blo 1699550 2549693 := bbase (se 3 (by rfl) ⟨478067, by rfl⟩ : syracuseStep 2549693 = 956135) (by norm_num)
theorem B3827645 : Blo 1699550 3827645 := bbase (se 3 (by rfl) ⟨717683, by rfl⟩ : syracuseStep 3827645 = 1435367) (by norm_num)
theorem B7759813 : Blo 1699550 7759813 := bbase (se 4 (by rfl) ⟨727482, by rfl⟩ : syracuseStep 7759813 = 1454965) (by norm_num)
theorem B3229645 : Blo 1699550 3229645 := bbase (se 3 (by rfl) ⟨605558, by rfl⟩ : syracuseStep 3229645 = 1211117) (by norm_num)
theorem B39782357 : Blo 1699550 39782357 := bbase (se 7 (by rfl) ⟨466199, by rfl⟩ : syracuseStep 39782357 = 932399) (by norm_num)
theorem B2549717 : Blo 1699550 2549717 := bbase (se 7 (by rfl) ⟨29879, by rfl⟩ : syracuseStep 2549717 = 59759) (by norm_num)
theorem B21792725 : Blo 1699550 21792725 := bbase (se 7 (by rfl) ⟨255383, by rfl⟩ : syracuseStep 21792725 = 510767) (by norm_num)
theorem B4302821 : Blo 1699550 4302821 := bbase (se 4 (by rfl) ⟨403389, by rfl⟩ : syracuseStep 4302821 = 806779) (by norm_num)
theorem B2549741 : Blo 1699550 2549741 := bbase (se 3 (by rfl) ⟨478076, by rfl⟩ : syracuseStep 2549741 = 956153) (by norm_num)
theorem B2869229 : Blo 1699550 2869229 := bbase (se 3 (by rfl) ⟨537980, by rfl⟩ : syracuseStep 2869229 = 1075961) (by norm_num)
theorem B2549765 : Blo 1699550 2549765 := bbase (se 4 (by rfl) ⟨239040, by rfl⟩ : syracuseStep 2549765 = 478081) (by norm_num)
theorem B3827717 : Blo 1699550 3827717 := bbase (se 4 (by rfl) ⟨358848, by rfl⟩ : syracuseStep 3827717 = 717697) (by norm_num)
theorem B2549789 : Blo 1699550 2549789 := bbase (se 3 (by rfl) ⟨478085, by rfl⟩ : syracuseStep 2549789 = 956171) (by norm_num)
theorem B2549813 : Blo 1699550 2549813 := bbase (se 5 (by rfl) ⟨119522, by rfl⟩ : syracuseStep 2549813 = 239045) (by norm_num)
theorem B2549837 : Blo 1699550 2549837 := bbase (se 3 (by rfl) ⟨478094, by rfl⟩ : syracuseStep 2549837 = 956189) (by norm_num)
theorem B3827789 : Blo 1699550 3827789 := bbase (se 3 (by rfl) ⟨717710, by rfl⟩ : syracuseStep 3827789 = 1435421) (by norm_num)
theorem B7759957 : Blo 1699550 7759957 := bbase (se 8 (by rfl) ⟨45468, by rfl⟩ : syracuseStep 7759957 = 90937) (by norm_num)
theorem B3229789 : Blo 1699550 3229789 := bbase (se 3 (by rfl) ⟨605585, by rfl⟩ : syracuseStep 3229789 = 1211171) (by norm_num)
theorem B2549861 : Blo 1699550 2549861 := bbase (se 4 (by rfl) ⟨239049, by rfl⟩ : syracuseStep 2549861 = 478099) (by norm_num)
theorem B2869357 : Blo 1699550 2869357 := bbase (se 3 (by rfl) ⟨538004, by rfl⟩ : syracuseStep 2869357 = 1076009) (by norm_num)
theorem B2549885 : Blo 1699550 2549885 := bbase (se 3 (by rfl) ⟨478103, by rfl⟩ : syracuseStep 2549885 = 956207) (by norm_num)
theorem B7260293 : Blo 1699550 7260293 := bbase (se 4 (by rfl) ⟨680652, by rfl⟩ : syracuseStep 7260293 = 1361305) (by norm_num)
theorem B5736581 : Blo 1699550 5736581 := bbase (se 4 (by rfl) ⟨537804, by rfl⟩ : syracuseStep 5736581 = 1075609) (by norm_num)
theorem B4909189 : Blo 1699550 4909189 := bbase (se 4 (by rfl) ⟨460236, by rfl⟩ : syracuseStep 4909189 = 920473) (by norm_num)
theorem B2549909 : Blo 1699550 2549909 := bbase (se 6 (by rfl) ⟨59763, by rfl⟩ : syracuseStep 2549909 = 119527) (by norm_num)
theorem B3827861 : Blo 1699550 3827861 := bbase (se 6 (by rfl) ⟨89715, by rfl⟩ : syracuseStep 3827861 = 179431) (by norm_num)
theorem B2549933 : Blo 1699550 2549933 := bbase (se 3 (by rfl) ⟨478112, by rfl⟩ : syracuseStep 2549933 = 956225) (by norm_num)
theorem B2549957 : Blo 1699550 2549957 := bbase (se 4 (by rfl) ⟨239058, by rfl⟩ : syracuseStep 2549957 = 478117) (by norm_num)
theorem B3631301 : Blo 1699550 3631301 := bbase (se 4 (by rfl) ⟨340434, by rfl⟩ : syracuseStep 3631301 = 680869) (by norm_num)
theorem B2869445 : Blo 1699550 2869445 := bbase (se 4 (by rfl) ⟨269010, by rfl⟩ : syracuseStep 2869445 = 538021) (by norm_num)
theorem B7760069 : Blo 1699550 7760069 := bbase (se 4 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 7760069 = 1455013) (by norm_num)
theorem B2549981 : Blo 1699550 2549981 := bbase (se 3 (by rfl) ⟨478121, by rfl⟩ : syracuseStep 2549981 = 956243) (by norm_num)
theorem B3827933 : Blo 1699550 3827933 := bbase (se 3 (by rfl) ⟨717737, by rfl⟩ : syracuseStep 3827933 = 1435475) (by norm_num)
theorem B2550005 : Blo 1699550 2550005 := bbase (se 5 (by rfl) ⟨119531, by rfl⟩ : syracuseStep 2550005 = 239063) (by norm_num)
theorem B6457589 : Blo 1699550 6457589 := bbase (se 5 (by rfl) ⟨302699, by rfl⟩ : syracuseStep 6457589 = 605399) (by norm_num)
theorem B3229949 : Blo 1699550 3229949 := bbase (se 3 (by rfl) ⟨605615, by rfl⟩ : syracuseStep 3229949 = 1211231) (by norm_num)
theorem B2550029 : Blo 1699550 2550029 := bbase (se 3 (by rfl) ⟨478130, by rfl⟩ : syracuseStep 2550029 = 956261) (by norm_num)
theorem B2550053 : Blo 1699550 2550053 := bbase (se 4 (by rfl) ⟨239067, by rfl⟩ : syracuseStep 2550053 = 478135) (by norm_num)
theorem B3828005 : Blo 1699550 3828005 := bbase (se 4 (by rfl) ⟨358875, by rfl⟩ : syracuseStep 3828005 = 717751) (by norm_num)
theorem B4303165 : Blo 1699550 4303165 := bbase (se 3 (by rfl) ⟨806843, by rfl⟩ : syracuseStep 4303165 = 1613687) (by norm_num)
theorem B2550077 : Blo 1699550 2550077 := bbase (se 3 (by rfl) ⟨478139, by rfl⟩ : syracuseStep 2550077 = 956279) (by norm_num)
theorem B2869573 : Blo 1699550 2869573 := bbase (se 4 (by rfl) ⟨269022, by rfl⟩ : syracuseStep 2869573 = 538045) (by norm_num)
theorem B2550101 : Blo 1699550 2550101 := bbase (se 10 (by rfl) ⟨3735, by rfl⟩ : syracuseStep 2550101 = 7471) (by norm_num)
theorem B2550125 : Blo 1699550 2550125 := bbase (se 3 (by rfl) ⟨478148, by rfl⟩ : syracuseStep 2550125 = 956297) (by norm_num)
theorem B3828077 : Blo 1699550 3828077 := bbase (se 3 (by rfl) ⟨717764, by rfl⟩ : syracuseStep 3828077 = 1435529) (by norm_num)
theorem B2550149 : Blo 1699550 2550149 := bbase (se 4 (by rfl) ⟨239076, by rfl⟩ : syracuseStep 2550149 = 478153) (by norm_num)
theorem B3230093 : Blo 1699550 3230093 := bbase (se 3 (by rfl) ⟨605642, by rfl⟩ : syracuseStep 3230093 = 1211285) (by norm_num)
theorem B2550173 : Blo 1699550 2550173 := bbase (se 3 (by rfl) ⟨478157, by rfl⟩ : syracuseStep 2550173 = 956315) (by norm_num)
theorem B2869661 : Blo 1699550 2869661 := bbase (se 3 (by rfl) ⟨538061, by rfl⟩ : syracuseStep 2869661 = 1076123) (by norm_num)
theorem B4303277 : Blo 1699550 4303277 := bbase (se 3 (by rfl) ⟨806864, by rfl⟩ : syracuseStep 4303277 = 1613729) (by norm_num)
theorem B2550197 : Blo 1699550 2550197 := bbase (se 5 (by rfl) ⟨119540, by rfl⟩ : syracuseStep 2550197 = 239081) (by norm_num)
theorem B3828149 : Blo 1699550 3828149 := bbase (se 5 (by rfl) ⟨179444, by rfl⟩ : syracuseStep 3828149 = 358889) (by norm_num)
theorem B2550221 : Blo 1699550 2550221 := bbase (se 3 (by rfl) ⟨478166, by rfl⟩ : syracuseStep 2550221 = 956333) (by norm_num)
theorem B2550245 : Blo 1699550 2550245 := bbase (se 4 (by rfl) ⟨239085, by rfl⟩ : syracuseStep 2550245 = 478171) (by norm_num)
theorem B2550269 : Blo 1699550 2550269 := bbase (se 3 (by rfl) ⟨478175, by rfl⟩ : syracuseStep 2550269 = 956351) (by norm_num)
theorem B3828221 : Blo 1699550 3828221 := bbase (se 3 (by rfl) ⟨717791, by rfl⟩ : syracuseStep 3828221 = 1435583) (by norm_num)
theorem B2042381 : Blo 1699550 2042381 := bbase (se 3 (by rfl) ⟨382946, by rfl⟩ : syracuseStep 2042381 = 765893) (by norm_num)
theorem B2550293 : Blo 1699550 2550293 := bbase (se 6 (by rfl) ⟨59772, by rfl⟩ : syracuseStep 2550293 = 119545) (by norm_num)
theorem B6457877 : Blo 1699550 6457877 := bbase (se 6 (by rfl) ⟨151356, by rfl⟩ : syracuseStep 6457877 = 302713) (by norm_num)
theorem B2869789 : Blo 1699550 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B4975141 : Blo 1699550 4975141 := bbase (se 4 (by rfl) ⟨466419, by rfl⟩ : syracuseStep 4975141 = 932839) (by norm_num)
theorem B4844069 : Blo 1699550 4844069 := bbase (se 4 (by rfl) ⟨454131, by rfl⟩ : syracuseStep 4844069 = 908263) (by norm_num)
theorem B2550317 : Blo 1699550 2550317 := bbase (se 3 (by rfl) ⟨478184, by rfl⟩ : syracuseStep 2550317 = 956369) (by norm_num)
theorem B5737013 : Blo 1699550 5737013 := bbase (se 5 (by rfl) ⟨268922, by rfl⟩ : syracuseStep 5737013 = 537845) (by norm_num)
theorem B8612405 : Blo 1699550 8612405 := bbase (se 5 (by rfl) ⟨403706, by rfl⟩ : syracuseStep 8612405 = 807413) (by norm_num)
theorem B2181697 : Blo 1699550 2181697 := bbase (se 2 (by rfl) ⟨818136, by rfl⟩ : syracuseStep 2181697 = 1636273) (by norm_num)
theorem B2550341 : Blo 1699550 2550341 := bbase (se 4 (by rfl) ⟨239094, by rfl⟩ : syracuseStep 2550341 = 478189) (by norm_num)
theorem B3828293 : Blo 1699550 3828293 := bbase (se 4 (by rfl) ⟨358902, by rfl⟩ : syracuseStep 3828293 = 717805) (by norm_num)
theorem B2042453 : Blo 1699550 2042453 := bbase (se 8 (by rfl) ⟨11967, by rfl⟩ : syracuseStep 2042453 = 23935) (by norm_num)
theorem B2550365 : Blo 1699550 2550365 := bbase (se 3 (by rfl) ⟨478193, by rfl⟩ : syracuseStep 2550365 = 956387) (by norm_num)
theorem B4303469 : Blo 1699550 4303469 := bbase (se 3 (by rfl) ⟨806900, by rfl⟩ : syracuseStep 4303469 = 1613801) (by norm_num)
theorem B2550389 : Blo 1699550 2550389 := bbase (se 5 (by rfl) ⟨119549, by rfl⟩ : syracuseStep 2550389 = 239099) (by norm_num)
theorem B2869877 : Blo 1699550 2869877 := bbase (se 5 (by rfl) ⟨134525, by rfl⟩ : syracuseStep 2869877 = 269051) (by norm_num)
theorem B3877517 : Blo 1699550 3877517 := bbase (se 3 (by rfl) ⟨727034, by rfl⟩ : syracuseStep 3877517 = 1454069) (by norm_num)
theorem B2550413 : Blo 1699550 2550413 := bbase (se 3 (by rfl) ⟨478202, by rfl⟩ : syracuseStep 2550413 = 956405) (by norm_num)
theorem B3828365 : Blo 1699550 3828365 := bbase (se 3 (by rfl) ⟨717818, by rfl⟩ : syracuseStep 3828365 = 1435637) (by norm_num)
theorem B3148445 : Blo 1699550 3148445 := bbase (se 3 (by rfl) ⟨590333, by rfl⟩ : syracuseStep 3148445 = 1180667) (by norm_num)
theorem B2550437 : Blo 1699550 2550437 := bbase (se 4 (by rfl) ⟨239103, by rfl⟩ : syracuseStep 2550437 = 478207) (by norm_num)
theorem B2550461 : Blo 1699550 2550461 := bbase (se 3 (by rfl) ⟨478211, by rfl⟩ : syracuseStep 2550461 = 956423) (by norm_num)
theorem B1723081 : Blo 1699550 1723081 := bbase (se 2 (by rfl) ⟨646155, by rfl⟩ : syracuseStep 1723081 = 1292311) (by norm_num)
theorem B2550485 : Blo 1699550 2550485 := bbase (se 7 (by rfl) ⟨29888, by rfl⟩ : syracuseStep 2550485 = 59777) (by norm_num)
theorem B5819093 : Blo 1699550 5819093 := bbase (se 7 (by rfl) ⟨68192, by rfl⟩ : syracuseStep 5819093 = 136385) (by norm_num)
theorem B3828437 : Blo 1699550 3828437 := bbase (se 7 (by rfl) ⟨44864, by rfl⟩ : syracuseStep 3828437 = 89729) (by norm_num)
theorem B2550509 : Blo 1699550 2550509 := bbase (se 3 (by rfl) ⟨478220, by rfl⟩ : syracuseStep 2550509 = 956441) (by norm_num)
theorem B2870005 : Blo 1699550 2870005 := bbase (se 5 (by rfl) ⟨134531, by rfl⟩ : syracuseStep 2870005 = 269063) (by norm_num)
theorem B2550533 : Blo 1699550 2550533 := bbase (se 4 (by rfl) ⟨239112, by rfl⟩ : syracuseStep 2550533 = 478225) (by norm_num)
theorem B2550557 : Blo 1699550 2550557 := bbase (se 3 (by rfl) ⟨478229, by rfl⟩ : syracuseStep 2550557 = 956459) (by norm_num)
theorem B2550581 : Blo 1699550 2550581 := bbase (se 5 (by rfl) ⟨119558, by rfl⟩ : syracuseStep 2550581 = 239117) (by norm_num)
theorem B2550605 : Blo 1699550 2550605 := bbase (se 3 (by rfl) ⟨478238, by rfl⟩ : syracuseStep 2550605 = 956477) (by norm_num)
theorem B2870093 : Blo 1699550 2870093 := bbase (se 3 (by rfl) ⟨538142, by rfl⟩ : syracuseStep 2870093 = 1076285) (by norm_num)
theorem B2550629 : Blo 1699550 2550629 := bbase (se 4 (by rfl) ⟨239121, by rfl⟩ : syracuseStep 2550629 = 478243) (by norm_num)
theorem B2550653 : Blo 1699550 2550653 := bbase (se 3 (by rfl) ⟨478247, by rfl⟩ : syracuseStep 2550653 = 956495) (by norm_num)
theorem B2042761 : Blo 1699550 2042761 := bbase (se 2 (by rfl) ⟨766035, by rfl⟩ : syracuseStep 2042761 = 1532071) (by norm_num)
theorem B2550677 : Blo 1699550 2550677 := bbase (se 6 (by rfl) ⟨59781, by rfl⟩ : syracuseStep 2550677 = 119563) (by norm_num)
theorem B2550701 : Blo 1699550 2550701 := bbase (se 3 (by rfl) ⟨478256, by rfl⟩ : syracuseStep 2550701 = 956513) (by norm_num)
theorem B3632053 : Blo 1699550 3632053 := bbase (se 5 (by rfl) ⟨170252, by rfl⟩ : syracuseStep 3632053 = 340505) (by norm_num)
theorem B4303813 : Blo 1699550 4303813 := bbase (se 4 (by rfl) ⟨403482, by rfl⟩ : syracuseStep 4303813 = 806965) (by norm_num)
theorem B2550725 : Blo 1699550 2550725 := bbase (se 4 (by rfl) ⟨239130, by rfl⟩ : syracuseStep 2550725 = 478261) (by norm_num)
theorem B2870221 : Blo 1699550 2870221 := bbase (se 3 (by rfl) ⟨538166, by rfl⟩ : syracuseStep 2870221 = 1076333) (by norm_num)
theorem B8604629 : Blo 1699550 8604629 := bbase (se 7 (by rfl) ⟨100835, by rfl⟩ : syracuseStep 8604629 = 201671) (by norm_num)
theorem B2550749 : Blo 1699550 2550749 := bbase (se 3 (by rfl) ⟨478265, by rfl⟩ : syracuseStep 2550749 = 956531) (by norm_num)
theorem B5737445 : Blo 1699550 5737445 := bbase (se 4 (by rfl) ⟨537885, by rfl⟩ : syracuseStep 5737445 = 1075771) (by norm_num)
theorem B2550773 : Blo 1699550 2550773 := bbase (se 5 (by rfl) ⟨119567, by rfl⟩ : syracuseStep 2550773 = 239135) (by norm_num)
theorem B2182145 : Blo 1699550 2182145 := bbase (se 2 (by rfl) ⟨818304, by rfl⟩ : syracuseStep 2182145 = 1636609) (by norm_num)
theorem B2550797 : Blo 1699550 2550797 := bbase (se 3 (by rfl) ⟨478274, by rfl⟩ : syracuseStep 2550797 = 956549) (by norm_num)
theorem B2550821 : Blo 1699550 2550821 := bbase (se 4 (by rfl) ⟨239139, by rfl⟩ : syracuseStep 2550821 = 478279) (by norm_num)
theorem B2870309 : Blo 1699550 2870309 := bbase (se 4 (by rfl) ⟨269091, by rfl⟩ : syracuseStep 2870309 = 538183) (by norm_num)
theorem B2042929 : Blo 1699550 2042929 := bbase (se 2 (by rfl) ⟨766098, by rfl⟩ : syracuseStep 2042929 = 1532197) (by norm_num)
theorem B4303925 : Blo 1699550 4303925 := bbase (se 5 (by rfl) ⟨201746, by rfl⟩ : syracuseStep 4303925 = 403493) (by norm_num)
theorem B2550845 : Blo 1699550 2550845 := bbase (se 3 (by rfl) ⟨478283, by rfl⟩ : syracuseStep 2550845 = 956567) (by norm_num)
theorem B3632197 : Blo 1699550 3632197 := bbase (se 4 (by rfl) ⟨340518, by rfl⟩ : syracuseStep 3632197 = 681037) (by norm_num)
theorem B2550869 : Blo 1699550 2550869 := bbase (se 8 (by rfl) ⟨14946, by rfl⟩ : syracuseStep 2550869 = 29893) (by norm_num)
theorem B4140125 : Blo 1699550 4140125 := bbase (se 3 (by rfl) ⟨776273, by rfl⟩ : syracuseStep 4140125 = 1552547) (by norm_num)
theorem B2042977 : Blo 1699550 2042977 := bbase (se 2 (by rfl) ⟨766116, by rfl⟩ : syracuseStep 2042977 = 1532233) (by norm_num)
theorem B7261285 : Blo 1699550 7261285 := bbase (se 4 (by rfl) ⟨680745, by rfl⟩ : syracuseStep 7261285 = 1361491) (by norm_num)
theorem B2550893 : Blo 1699550 2550893 := bbase (se 3 (by rfl) ⟨478292, by rfl⟩ : syracuseStep 2550893 = 956585) (by norm_num)
theorem B2550917 : Blo 1699550 2550917 := bbase (se 4 (by rfl) ⟨239148, by rfl⟩ : syracuseStep 2550917 = 478297) (by norm_num)
theorem B5450885 : Blo 1699550 5450885 := bbase (se 4 (by rfl) ⟨511020, by rfl⟩ : syracuseStep 5450885 = 1022041) (by norm_num)
theorem B2550941 : Blo 1699550 2550941 := bbase (se 3 (by rfl) ⟨478301, by rfl⟩ : syracuseStep 2550941 = 956603) (by norm_num)
theorem B2870437 : Blo 1699550 2870437 := bbase (se 4 (by rfl) ⟨269103, by rfl⟩ : syracuseStep 2870437 = 538207) (by norm_num)
theorem B2550965 : Blo 1699550 2550965 := bbase (se 5 (by rfl) ⟨119576, by rfl⟩ : syracuseStep 2550965 = 239153) (by norm_num)
theorem B2043073 : Blo 1699550 2043073 := bbase (se 2 (by rfl) ⟨766152, by rfl⟩ : syracuseStep 2043073 = 1532305) (by norm_num)
theorem B4598981 : Blo 1699550 4598981 := bbase (se 4 (by rfl) ⟨431154, by rfl⟩ : syracuseStep 4598981 = 862309) (by norm_num)
theorem B1912009 : Blo 1699550 1912009 := bbase (se 2 (by rfl) ⟨717003, by rfl⟩ : syracuseStep 1912009 = 1434007) (by norm_num)
theorem B2550989 : Blo 1699550 2550989 := bbase (se 3 (by rfl) ⟨478310, by rfl⟩ : syracuseStep 2550989 = 956621) (by norm_num)
theorem B28331221 : Blo 1699550 28331221 := bbase (se 7 (by rfl) ⟨332006, by rfl⟩ : syracuseStep 28331221 = 664013) (by norm_num)
theorem B7859429 : Blo 1699550 7859429 := bbase (se 4 (by rfl) ⟨736821, by rfl⟩ : syracuseStep 7859429 = 1473643) (by norm_num)
theorem B2551013 : Blo 1699550 2551013 := bbase (se 4 (by rfl) ⟨239157, by rfl⟩ : syracuseStep 2551013 = 478315) (by norm_num)
theorem B1912045 : Blo 1699550 1912045 := bbase (se 3 (by rfl) ⟨358508, by rfl⟩ : syracuseStep 1912045 = 717017) (by norm_num)
theorem B4304117 : Blo 1699550 4304117 := bbase (se 5 (by rfl) ⟨201755, by rfl⟩ : syracuseStep 4304117 = 403511) (by norm_num)
theorem B8285429 : Blo 1699550 8285429 := bbase (se 5 (by rfl) ⟨388379, by rfl⟩ : syracuseStep 8285429 = 776759) (by norm_num)
theorem B2551037 : Blo 1699550 2551037 := bbase (se 3 (by rfl) ⟨478319, by rfl⟩ : syracuseStep 2551037 = 956639) (by norm_num)
theorem B2870525 : Blo 1699550 2870525 := bbase (se 3 (by rfl) ⟨538223, by rfl⟩ : syracuseStep 2870525 = 1076447) (by norm_num)
theorem B1912081 : Blo 1699550 1912081 := bbase (se 2 (by rfl) ⟨717030, by rfl⟩ : syracuseStep 1912081 = 1434061) (by norm_num)
theorem B2551061 : Blo 1699550 2551061 := bbase (se 6 (by rfl) ⟨59790, by rfl⟩ : syracuseStep 2551061 = 119581) (by norm_num)
theorem B2551085 : Blo 1699550 2551085 := bbase (se 3 (by rfl) ⟨478328, by rfl⟩ : syracuseStep 2551085 = 956657) (by norm_num)
theorem B1912117 : Blo 1699550 1912117 := bbase (se 5 (by rfl) ⟨89630, by rfl⟩ : syracuseStep 1912117 = 179261) (by norm_num)
theorem B2551109 : Blo 1699550 2551109 := bbase (se 4 (by rfl) ⟨239166, by rfl⟩ : syracuseStep 2551109 = 478333) (by norm_num)
theorem B2723149 : Blo 1699550 2723149 := bbase (se 3 (by rfl) ⟨510590, by rfl⟩ : syracuseStep 2723149 = 1021181) (by norm_num)
theorem B1912153 : Blo 1699550 1912153 := bbase (se 2 (by rfl) ⟨717057, by rfl⟩ : syracuseStep 1912153 = 1434115) (by norm_num)
theorem B2551133 : Blo 1699550 2551133 := bbase (se 3 (by rfl) ⟨478337, by rfl⟩ : syracuseStep 2551133 = 956675) (by norm_num)
theorem B2551157 : Blo 1699550 2551157 := bbase (se 5 (by rfl) ⟨119585, by rfl⟩ : syracuseStep 2551157 = 239171) (by norm_num)
theorem B1912189 : Blo 1699550 1912189 := bbase (se 3 (by rfl) ⟨358535, by rfl⟩ : syracuseStep 1912189 = 717071) (by norm_num)
theorem B2870653 : Blo 1699550 2870653 := bbase (se 3 (by rfl) ⟨538247, by rfl⟩ : syracuseStep 2870653 = 1076495) (by norm_num)
theorem B2551181 : Blo 1699550 2551181 := bbase (se 3 (by rfl) ⟨478346, by rfl⟩ : syracuseStep 2551181 = 956693) (by norm_num)
theorem B5737877 : Blo 1699550 5737877 := bbase (se 6 (by rfl) ⟨134481, by rfl⟩ : syracuseStep 5737877 = 268963) (by norm_num)
theorem B1912225 : Blo 1699550 1912225 := bbase (se 2 (by rfl) ⟨717084, by rfl⟩ : syracuseStep 1912225 = 1434169) (by norm_num)
theorem B2551205 : Blo 1699550 2551205 := bbase (se 4 (by rfl) ⟨239175, by rfl⟩ : syracuseStep 2551205 = 478351) (by norm_num)
theorem B2551229 : Blo 1699550 2551229 := bbase (se 3 (by rfl) ⟨478355, by rfl⟩ : syracuseStep 2551229 = 956711) (by norm_num)
theorem B3632573 : Blo 1699550 3632573 := bbase (se 3 (by rfl) ⟨681107, by rfl⟩ : syracuseStep 3632573 = 1362215) (by norm_num)
theorem B1912261 : Blo 1699550 1912261 := bbase (se 4 (by rfl) ⟨179274, by rfl⟩ : syracuseStep 1912261 = 358549) (by norm_num)
theorem B2551253 : Blo 1699550 2551253 := bbase (se 7 (by rfl) ⟨29897, by rfl⟩ : syracuseStep 2551253 = 59795) (by norm_num)
theorem B2870741 : Blo 1699550 2870741 := bbase (se 7 (by rfl) ⟨33641, by rfl⟩ : syracuseStep 2870741 = 67283) (by norm_num)
theorem B1912297 : Blo 1699550 1912297 := bbase (se 2 (by rfl) ⟨717111, by rfl⟩ : syracuseStep 1912297 = 1434223) (by norm_num)
theorem B2551277 : Blo 1699550 2551277 := bbase (se 3 (by rfl) ⟨478364, by rfl⟩ : syracuseStep 2551277 = 956729) (by norm_num)
theorem B15519221 : Blo 1699550 15519221 := bbase (se 5 (by rfl) ⟨727463, by rfl⟩ : syracuseStep 15519221 = 1454927) (by norm_num)
theorem B2551301 : Blo 1699550 2551301 := bbase (se 4 (by rfl) ⟨239184, by rfl⟩ : syracuseStep 2551301 = 478369) (by norm_num)
theorem B1912333 : Blo 1699550 1912333 := bbase (se 3 (by rfl) ⟨358562, by rfl⟩ : syracuseStep 1912333 = 717125) (by norm_num)
theorem B2551325 : Blo 1699550 2551325 := bbase (se 3 (by rfl) ⟨478373, by rfl⟩ : syracuseStep 2551325 = 956747) (by norm_num)
theorem B1912369 : Blo 1699550 1912369 := bbase (se 2 (by rfl) ⟨717138, by rfl⟩ : syracuseStep 1912369 = 1434277) (by norm_num)
theorem B2551349 : Blo 1699550 2551349 := bbase (se 5 (by rfl) ⟨119594, by rfl⟩ : syracuseStep 2551349 = 239189) (by norm_num)
theorem B4304461 : Blo 1699550 4304461 := bbase (se 3 (by rfl) ⟨807086, by rfl⟩ : syracuseStep 4304461 = 1614173) (by norm_num)
theorem B2551373 : Blo 1699550 2551373 := bbase (se 3 (by rfl) ⟨478382, by rfl⟩ : syracuseStep 2551373 = 956765) (by norm_num)
theorem B12250709 : Blo 1699550 12250709 := bbase (se 8 (by rfl) ⟨71781, by rfl⟩ : syracuseStep 12250709 = 143563) (by norm_num)
theorem B1912405 : Blo 1699550 1912405 := bbase (se 8 (by rfl) ⟨11205, by rfl⟩ : syracuseStep 1912405 = 22411) (by norm_num)
theorem B2870869 : Blo 1699550 2870869 := bbase (se 8 (by rfl) ⟨16821, by rfl⟩ : syracuseStep 2870869 = 33643) (by norm_num)
theorem B1724005 : Blo 1699550 1724005 := bbase (se 4 (by rfl) ⟨161625, by rfl⟩ : syracuseStep 1724005 = 323251) (by norm_num)
theorem B2551397 : Blo 1699550 2551397 := bbase (se 4 (by rfl) ⟨239193, by rfl⟩ : syracuseStep 2551397 = 478387) (by norm_num)
theorem B1912441 : Blo 1699550 1912441 := bbase (se 2 (by rfl) ⟨717165, by rfl⟩ : syracuseStep 1912441 = 1434331) (by norm_num)
theorem B2551421 : Blo 1699550 2551421 := bbase (se 3 (by rfl) ⟨478391, by rfl⟩ : syracuseStep 2551421 = 956783) (by norm_num)
theorem B2551445 : Blo 1699550 2551445 := bbase (se 6 (by rfl) ⟨59799, by rfl⟩ : syracuseStep 2551445 = 119599) (by norm_num)
theorem B1912477 : Blo 1699550 1912477 := bbase (se 3 (by rfl) ⟨358589, by rfl⟩ : syracuseStep 1912477 = 717179) (by norm_num)
theorem B2551469 : Blo 1699550 2551469 := bbase (se 3 (by rfl) ⟨478400, by rfl⟩ : syracuseStep 2551469 = 956801) (by norm_num)
theorem B2870957 : Blo 1699550 2870957 := bbase (se 3 (by rfl) ⟨538304, by rfl⟩ : syracuseStep 2870957 = 1076609) (by norm_num)
theorem B6459061 : Blo 1699550 6459061 := bbase (se 5 (by rfl) ⟨302768, by rfl⟩ : syracuseStep 6459061 = 605537) (by norm_num)
theorem B4304573 : Blo 1699550 4304573 := bbase (se 3 (by rfl) ⟨807107, by rfl⟩ : syracuseStep 4304573 = 1614215) (by norm_num)
theorem B1912513 : Blo 1699550 1912513 := bbase (se 2 (by rfl) ⟨717192, by rfl⟩ : syracuseStep 1912513 = 1434385) (by norm_num)
theorem B2551493 : Blo 1699550 2551493 := bbase (se 4 (by rfl) ⟨239202, by rfl⟩ : syracuseStep 2551493 = 478405) (by norm_num)
theorem B4845253 : Blo 1699550 4845253 := bbase (se 4 (by rfl) ⟨454242, by rfl⟩ : syracuseStep 4845253 = 908485) (by norm_num)
theorem B2551517 : Blo 1699550 2551517 := bbase (se 3 (by rfl) ⟨478409, by rfl⟩ : syracuseStep 2551517 = 956819) (by norm_num)
theorem B1912549 : Blo 1699550 1912549 := bbase (se 4 (by rfl) ⟨179301, by rfl⟩ : syracuseStep 1912549 = 358603) (by norm_num)
theorem B2551541 : Blo 1699550 2551541 := bbase (se 5 (by rfl) ⟨119603, by rfl⟩ : syracuseStep 2551541 = 239207) (by norm_num)
theorem B2043649 : Blo 1699550 2043649 := bbase (se 2 (by rfl) ⟨766368, by rfl⟩ : syracuseStep 2043649 = 1532737) (by norm_num)
theorem B1912585 : Blo 1699550 1912585 := bbase (se 2 (by rfl) ⟨717219, by rfl⟩ : syracuseStep 1912585 = 1434439) (by norm_num)
theorem B2551565 : Blo 1699550 2551565 := bbase (se 3 (by rfl) ⟨478418, by rfl⟩ : syracuseStep 2551565 = 956837) (by norm_num)
theorem B2551589 : Blo 1699550 2551589 := bbase (se 4 (by rfl) ⟨239211, by rfl⟩ : syracuseStep 2551589 = 478423) (by norm_num)
theorem B1912621 : Blo 1699550 1912621 := bbase (se 3 (by rfl) ⟨358616, by rfl⟩ : syracuseStep 1912621 = 717233) (by norm_num)
theorem B3632941 : Blo 1699550 3632941 := bbase (se 3 (by rfl) ⟨681176, by rfl⟩ : syracuseStep 3632941 = 1362353) (by norm_num)
theorem B2871085 : Blo 1699550 2871085 := bbase (se 3 (by rfl) ⟨538328, by rfl⟩ : syracuseStep 2871085 = 1076657) (by norm_num)
theorem B2551613 : Blo 1699550 2551613 := bbase (se 3 (by rfl) ⟨478427, by rfl⟩ : syracuseStep 2551613 = 956855) (by norm_num)
theorem B5738309 : Blo 1699550 5738309 := bbase (se 4 (by rfl) ⟨537966, by rfl⟩ : syracuseStep 5738309 = 1075933) (by norm_num)
theorem B8613701 : Blo 1699550 8613701 := bbase (se 4 (by rfl) ⟨807534, by rfl⟩ : syracuseStep 8613701 = 1615069) (by norm_num)
theorem B1912657 : Blo 1699550 1912657 := bbase (se 2 (by rfl) ⟨717246, by rfl⟩ : syracuseStep 1912657 = 1434493) (by norm_num)
theorem B2551637 : Blo 1699550 2551637 := bbase (se 9 (by rfl) ⟨7475, by rfl⟩ : syracuseStep 2551637 = 14951) (by norm_num)
theorem B4845413 : Blo 1699550 4845413 := bbase (se 4 (by rfl) ⟨454257, by rfl⟩ : syracuseStep 4845413 = 908515) (by norm_num)
theorem B2551661 : Blo 1699550 2551661 := bbase (se 3 (by rfl) ⟨478436, by rfl⟩ : syracuseStep 2551661 = 956873) (by norm_num)
theorem B1912693 : Blo 1699550 1912693 := bbase (se 5 (by rfl) ⟨89657, by rfl⟩ : syracuseStep 1912693 = 179315) (by norm_num)
theorem B4304765 : Blo 1699550 4304765 := bbase (se 3 (by rfl) ⟨807143, by rfl⟩ : syracuseStep 4304765 = 1614287) (by norm_num)
theorem B2551685 : Blo 1699550 2551685 := bbase (se 4 (by rfl) ⟨239220, by rfl⟩ : syracuseStep 2551685 = 478441) (by norm_num)
theorem B2871173 : Blo 1699550 2871173 := bbase (se 4 (by rfl) ⟨269172, by rfl⟩ : syracuseStep 2871173 = 538345) (by norm_num)
theorem B1912729 : Blo 1699550 1912729 := bbase (se 2 (by rfl) ⟨717273, by rfl⟩ : syracuseStep 1912729 = 1434547) (by norm_num)
theorem B2551709 : Blo 1699550 2551709 := bbase (se 3 (by rfl) ⟨478445, by rfl⟩ : syracuseStep 2551709 = 956891) (by norm_num)
theorem B2551733 : Blo 1699550 2551733 := bbase (se 5 (by rfl) ⟨119612, by rfl⟩ : syracuseStep 2551733 = 239225) (by norm_num)
theorem B1912765 : Blo 1699550 1912765 := bbase (se 3 (by rfl) ⟨358643, by rfl⟩ : syracuseStep 1912765 = 717287) (by norm_num)
theorem B2551757 : Blo 1699550 2551757 := bbase (se 3 (by rfl) ⟨478454, by rfl⟩ : syracuseStep 2551757 = 956909) (by norm_num)
theorem B1912801 : Blo 1699550 1912801 := bbase (se 2 (by rfl) ⟨717300, by rfl⟩ : syracuseStep 1912801 = 1434601) (by norm_num)
theorem B2551781 : Blo 1699550 2551781 := bbase (se 4 (by rfl) ⟨239229, by rfl⟩ : syracuseStep 2551781 = 478459) (by norm_num)
theorem B6459365 : Blo 1699550 6459365 := bbase (se 4 (by rfl) ⟨605565, by rfl⟩ : syracuseStep 6459365 = 1211131) (by norm_num)
theorem B2551805 : Blo 1699550 2551805 := bbase (se 3 (by rfl) ⟨478463, by rfl⟩ : syracuseStep 2551805 = 956927) (by norm_num)
theorem B1912837 : Blo 1699550 1912837 := bbase (se 4 (by rfl) ⟨179328, by rfl⟩ : syracuseStep 1912837 = 358657) (by norm_num)
theorem B2871301 : Blo 1699550 2871301 := bbase (se 4 (by rfl) ⟨269184, by rfl⟩ : syracuseStep 2871301 = 538369) (by norm_num)
theorem B2551829 : Blo 1699550 2551829 := bbase (se 6 (by rfl) ⟨59808, by rfl⟩ : syracuseStep 2551829 = 119617) (by norm_num)
theorem B1912873 : Blo 1699550 1912873 := bbase (se 2 (by rfl) ⟨717327, by rfl⟩ : syracuseStep 1912873 = 1434655) (by norm_num)
theorem B2551853 : Blo 1699550 2551853 := bbase (se 3 (by rfl) ⟨478472, by rfl⟩ : syracuseStep 2551853 = 956945) (by norm_num)
theorem B2551877 : Blo 1699550 2551877 := bbase (se 4 (by rfl) ⟨239238, by rfl⟩ : syracuseStep 2551877 = 478477) (by norm_num)
theorem B1912909 : Blo 1699550 1912909 := bbase (se 3 (by rfl) ⟨358670, by rfl⟩ : syracuseStep 1912909 = 717341) (by norm_num)
theorem B2551901 : Blo 1699550 2551901 := bbase (se 3 (by rfl) ⟨478481, by rfl⟩ : syracuseStep 2551901 = 956963) (by norm_num)
theorem B1912945 : Blo 1699550 1912945 := bbase (se 2 (by rfl) ⟨717354, by rfl⟩ : syracuseStep 1912945 = 1434709) (by norm_num)
theorem B2551925 : Blo 1699550 2551925 := bbase (se 5 (by rfl) ⟨119621, by rfl⟩ : syracuseStep 2551925 = 239243) (by norm_num)
theorem B2297981 : Blo 1699550 2297981 := bbase (se 3 (by rfl) ⟨430871, by rfl⟩ : syracuseStep 2297981 = 861743) (by norm_num)
theorem B2551949 : Blo 1699550 2551949 := bbase (se 3 (by rfl) ⟨478490, by rfl⟩ : syracuseStep 2551949 = 956981) (by norm_num)
theorem B1912981 : Blo 1699550 1912981 := bbase (se 6 (by rfl) ⟨44835, by rfl⟩ : syracuseStep 1912981 = 89671) (by norm_num)
theorem B2551973 : Blo 1699550 2551973 := bbase (se 4 (by rfl) ⟨239247, by rfl⟩ : syracuseStep 2551973 = 478495) (by norm_num)
theorem B3879085 : Blo 1699550 3879085 := bbase (se 3 (by rfl) ⟨727328, by rfl⟩ : syracuseStep 3879085 = 1454657) (by norm_num)
theorem B1913017 : Blo 1699550 1913017 := bbase (se 2 (by rfl) ⟨717381, by rfl⟩ : syracuseStep 1913017 = 1434763) (by norm_num)
theorem B2551997 : Blo 1699550 2551997 := bbase (se 3 (by rfl) ⟨478499, by rfl⟩ : syracuseStep 2551997 = 956999) (by norm_num)
theorem B2420941 : Blo 1699550 2420941 := bbase (se 3 (by rfl) ⟨453926, by rfl⟩ : syracuseStep 2420941 = 907853) (by norm_num)
theorem B4305109 : Blo 1699550 4305109 := bbase (se 7 (by rfl) ⟨50450, by rfl⟩ : syracuseStep 4305109 = 100901) (by norm_num)
theorem B2552021 : Blo 1699550 2552021 := bbase (se 7 (by rfl) ⟨29906, by rfl⟩ : syracuseStep 2552021 = 59813) (by norm_num)
theorem B1913053 : Blo 1699550 1913053 := bbase (se 3 (by rfl) ⟨358697, by rfl⟩ : syracuseStep 1913053 = 717395) (by norm_num)
theorem B8605925 : Blo 1699550 8605925 := bbase (se 4 (by rfl) ⟨806805, by rfl⟩ : syracuseStep 8605925 = 1613611) (by norm_num)
theorem B2552045 : Blo 1699550 2552045 := bbase (se 3 (by rfl) ⟨478508, by rfl⟩ : syracuseStep 2552045 = 957017) (by norm_num)
theorem B5738741 : Blo 1699550 5738741 := bbase (se 5 (by rfl) ⟨269003, by rfl⟩ : syracuseStep 5738741 = 538007) (by norm_num)
theorem B1913089 : Blo 1699550 1913089 := bbase (se 2 (by rfl) ⟨717408, by rfl⟩ : syracuseStep 1913089 = 1434817) (by norm_num)
theorem B2552069 : Blo 1699550 2552069 := bbase (se 4 (by rfl) ⟨239256, by rfl⟩ : syracuseStep 2552069 = 478513) (by norm_num)
theorem B2298133 : Blo 1699550 2298133 := bbase (se 6 (by rfl) ⟨53862, by rfl⟩ : syracuseStep 2298133 = 107725) (by norm_num)
theorem B2552093 : Blo 1699550 2552093 := bbase (se 3 (by rfl) ⟨478517, by rfl⟩ : syracuseStep 2552093 = 957035) (by norm_num)
theorem B1913125 : Blo 1699550 1913125 := bbase (se 4 (by rfl) ⟨179355, by rfl⟩ : syracuseStep 1913125 = 358711) (by norm_num)
theorem B4084013 : Blo 1699550 4084013 := bbase (se 3 (by rfl) ⟨765752, by rfl⟩ : syracuseStep 4084013 = 1531505) (by norm_num)
theorem B2552117 : Blo 1699550 2552117 := bbase (se 5 (by rfl) ⟨119630, by rfl⟩ : syracuseStep 2552117 = 239261) (by norm_num)
theorem B4305221 : Blo 1699550 4305221 := bbase (se 4 (by rfl) ⟨403614, by rfl⟩ : syracuseStep 4305221 = 807229) (by norm_num)
theorem B1913161 : Blo 1699550 1913161 := bbase (se 2 (by rfl) ⟨717435, by rfl⟩ : syracuseStep 1913161 = 1434871) (by norm_num)
theorem B2552141 : Blo 1699550 2552141 := bbase (se 3 (by rfl) ⟨478526, by rfl⟩ : syracuseStep 2552141 = 957053) (by norm_num)
theorem B4084069 : Blo 1699550 4084069 := bbase (se 4 (by rfl) ⟨382881, by rfl⟩ : syracuseStep 4084069 = 765763) (by norm_num)
theorem B2552165 : Blo 1699550 2552165 := bbase (se 4 (by rfl) ⟨239265, by rfl⟩ : syracuseStep 2552165 = 478531) (by norm_num)
theorem B1913197 : Blo 1699550 1913197 := bbase (se 3 (by rfl) ⟨358724, by rfl⟩ : syracuseStep 1913197 = 717449) (by norm_num)
theorem B2552189 : Blo 1699550 2552189 := bbase (se 3 (by rfl) ⟨478535, by rfl⟩ : syracuseStep 2552189 = 957071) (by norm_num)
theorem B1913233 : Blo 1699550 1913233 := bbase (se 2 (by rfl) ⟨717462, by rfl⟩ : syracuseStep 1913233 = 1434925) (by norm_num)
theorem B1814933 : Blo 1699550 1814933 := bbase (se 6 (by rfl) ⟨42537, by rfl⟩ : syracuseStep 1814933 = 85075) (by norm_num)
theorem B2552213 : Blo 1699550 2552213 := bbase (se 6 (by rfl) ⟨59817, by rfl⟩ : syracuseStep 2552213 = 119635) (by norm_num)
theorem B2552237 : Blo 1699550 2552237 := bbase (se 3 (by rfl) ⟨478544, by rfl⟩ : syracuseStep 2552237 = 957089) (by norm_num)
theorem B1913269 : Blo 1699550 1913269 := bbase (se 5 (by rfl) ⟨89684, by rfl⟩ : syracuseStep 1913269 = 179369) (by norm_num)
theorem B2552261 : Blo 1699550 2552261 := bbase (se 4 (by rfl) ⟨239274, by rfl⟩ : syracuseStep 2552261 = 478549) (by norm_num)
theorem B20672981 : Blo 1699550 20672981 := bbase (se 7 (by rfl) ⟨242261, by rfl⟩ : syracuseStep 20672981 = 484523) (by norm_num)
theorem B1913305 : Blo 1699550 1913305 := bbase (se 2 (by rfl) ⟨717489, by rfl⟩ : syracuseStep 1913305 = 1434979) (by norm_num)
theorem B1815005 : Blo 1699550 1815005 := bbase (se 3 (by rfl) ⟨340313, by rfl⟩ : syracuseStep 1815005 = 680627) (by norm_num)
theorem B2552285 : Blo 1699550 2552285 := bbase (se 3 (by rfl) ⟨478553, by rfl⟩ : syracuseStep 2552285 = 957107) (by norm_num)
theorem B2552309 : Blo 1699550 2552309 := bbase (se 5 (by rfl) ⟨119639, by rfl⟩ : syracuseStep 2552309 = 239279) (by norm_num)
theorem B1913341 : Blo 1699550 1913341 := bbase (se 3 (by rfl) ⟨358751, by rfl⟩ : syracuseStep 1913341 = 717503) (by norm_num)
theorem B4305413 : Blo 1699550 4305413 := bbase (se 4 (by rfl) ⟨403632, by rfl⟩ : syracuseStep 4305413 = 807265) (by norm_num)
theorem B1913377 : Blo 1699550 1913377 := bbase (se 2 (by rfl) ⟨717516, by rfl⟩ : syracuseStep 1913377 = 1435033) (by norm_num)
theorem B3494453 : Blo 1699550 3494453 := bbase (se 5 (by rfl) ⟨163802, by rfl⟩ : syracuseStep 3494453 = 327605) (by norm_num)
theorem B1913413 : Blo 1699550 1913413 := bbase (se 4 (by rfl) ⟨179382, by rfl⟩ : syracuseStep 1913413 = 358765) (by norm_num)
theorem B1913449 : Blo 1699550 1913449 := bbase (se 2 (by rfl) ⟨717543, by rfl⟩ : syracuseStep 1913449 = 1435087) (by norm_num)
theorem B1913485 : Blo 1699550 1913485 := bbase (se 3 (by rfl) ⟨358778, by rfl⟩ : syracuseStep 1913485 = 717557) (by norm_num)
theorem B1815193 : Blo 1699550 1815193 := bbase (se 2 (by rfl) ⟨680697, by rfl⟩ : syracuseStep 1815193 = 1361395) (by norm_num)
theorem B5739173 : Blo 1699550 5739173 := bbase (se 4 (by rfl) ⟨538047, by rfl⟩ : syracuseStep 5739173 = 1076095) (by norm_num)
theorem B1913521 : Blo 1699550 1913521 := bbase (se 2 (by rfl) ⟨717570, by rfl⟩ : syracuseStep 1913521 = 1435141) (by norm_num)
theorem B2724533 : Blo 1699550 2724533 := bbase (se 5 (by rfl) ⟨127712, by rfl⟩ : syracuseStep 2724533 = 255425) (by norm_num)
theorem B1913557 : Blo 1699550 1913557 := bbase (se 7 (by rfl) ⟨22424, by rfl⟩ : syracuseStep 1913557 = 44849) (by norm_num)
theorem B4084445 : Blo 1699550 4084445 := bbase (se 3 (by rfl) ⟨765833, by rfl⟩ : syracuseStep 4084445 = 1531667) (by norm_num)
theorem B2151137 : Blo 1699550 2151137 := bbase (se 2 (by rfl) ⟨806676, by rfl⟩ : syracuseStep 2151137 = 1613353) (by norm_num)
theorem B1913593 : Blo 1699550 1913593 := bbase (se 2 (by rfl) ⟨717597, by rfl⟩ : syracuseStep 1913593 = 1435195) (by norm_num)
theorem B2151193 : Blo 1699550 2151193 := bbase (se 2 (by rfl) ⟨806697, by rfl⟩ : syracuseStep 2151193 = 1613395) (by norm_num)
theorem B2421533 : Blo 1699550 2421533 := bbase (se 3 (by rfl) ⟨454037, by rfl⟩ : syracuseStep 2421533 = 908075) (by norm_num)
theorem B1913629 : Blo 1699550 1913629 := bbase (se 3 (by rfl) ⟨358805, by rfl⟩ : syracuseStep 1913629 = 717611) (by norm_num)
theorem B1913665 : Blo 1699550 1913665 := bbase (se 2 (by rfl) ⟨717624, by rfl⟩ : syracuseStep 1913665 = 1435249) (by norm_num)
theorem B1815377 : Blo 1699550 1815377 := bbase (se 2 (by rfl) ⟨680766, by rfl⟩ : syracuseStep 1815377 = 1361533) (by norm_num)
theorem B4305757 : Blo 1699550 4305757 := bbase (se 3 (by rfl) ⟨807329, by rfl⟩ : syracuseStep 4305757 = 1614659) (by norm_num)
theorem B1913701 : Blo 1699550 1913701 := bbase (se 4 (by rfl) ⟨179409, by rfl⟩ : syracuseStep 1913701 = 358819) (by norm_num)
theorem B2421613 : Blo 1699550 2421613 := bbase (se 3 (by rfl) ⟨454052, by rfl⟩ : syracuseStep 2421613 = 908105) (by norm_num)
theorem B2724725 : Blo 1699550 2724725 := bbase (se 5 (by rfl) ⟨127721, by rfl⟩ : syracuseStep 2724725 = 255443) (by norm_num)
theorem B2151289 : Blo 1699550 2151289 := bbase (se 2 (by rfl) ⟨806733, by rfl⟩ : syracuseStep 2151289 = 1613467) (by norm_num)
theorem B1913737 : Blo 1699550 1913737 := bbase (se 2 (by rfl) ⟨717651, by rfl⟩ : syracuseStep 1913737 = 1435303) (by norm_num)
theorem B1913773 : Blo 1699550 1913773 := bbase (se 3 (by rfl) ⟨358832, by rfl⟩ : syracuseStep 1913773 = 717665) (by norm_num)
theorem B8172485 : Blo 1699550 8172485 := bbase (se 4 (by rfl) ⟨766170, by rfl⟩ : syracuseStep 8172485 = 1532341) (by norm_num)
theorem B4084685 : Blo 1699550 4084685 := bbase (se 3 (by rfl) ⟨765878, by rfl⟩ : syracuseStep 4084685 = 1531757) (by norm_num)
theorem B4305869 : Blo 1699550 4305869 := bbase (se 3 (by rfl) ⟨807350, by rfl⟩ : syracuseStep 4305869 = 1614701) (by norm_num)
theorem B1913809 : Blo 1699550 1913809 := bbase (se 2 (by rfl) ⟨717678, by rfl⟩ : syracuseStep 1913809 = 1435357) (by norm_num)
theorem B31011797 : Blo 1699550 31011797 := bbase (se 7 (by rfl) ⟨363419, by rfl⟩ : syracuseStep 31011797 = 726839) (by norm_num)
theorem B3445733 : Blo 1699550 3445733 := bbase (se 4 (by rfl) ⟨323037, by rfl⟩ : syracuseStep 3445733 = 646075) (by norm_num)
theorem B2241509 : Blo 1699550 2241509 := bbase (se 4 (by rfl) ⟨210141, by rfl⟩ : syracuseStep 2241509 = 420283) (by norm_num)
theorem B2421733 : Blo 1699550 2421733 := bbase (se 4 (by rfl) ⟨227037, by rfl⟩ : syracuseStep 2421733 = 454075) (by norm_num)
theorem B1913845 : Blo 1699550 1913845 := bbase (se 5 (by rfl) ⟨89711, by rfl⟩ : syracuseStep 1913845 = 179423) (by norm_num)
theorem B26186773 : Blo 1699550 26186773 := bbase (se 6 (by rfl) ⟨613752, by rfl⟩ : syracuseStep 26186773 = 1227505) (by norm_num)
theorem B1913881 : Blo 1699550 1913881 := bbase (se 2 (by rfl) ⟨717705, by rfl⟩ : syracuseStep 1913881 = 1435411) (by norm_num)
theorem B2151461 : Blo 1699550 2151461 := bbase (se 4 (by rfl) ⟨201699, by rfl⟩ : syracuseStep 2151461 = 403399) (by norm_num)
theorem B1913917 : Blo 1699550 1913917 := bbase (se 3 (by rfl) ⟨358859, by rfl⟩ : syracuseStep 1913917 = 717719) (by norm_num)
theorem B2241605 : Blo 1699550 2241605 := bbase (se 4 (by rfl) ⟨210150, by rfl⟩ : syracuseStep 2241605 = 420301) (by norm_num)
theorem B2421829 : Blo 1699550 2421829 := bbase (se 4 (by rfl) ⟨227046, by rfl⟩ : syracuseStep 2421829 = 454093) (by norm_num)
theorem B5739605 : Blo 1699550 5739605 := bbase (se 8 (by rfl) ⟨33630, by rfl⟩ : syracuseStep 5739605 = 67261) (by norm_num)
theorem B2151517 : Blo 1699550 2151517 := bbase (se 3 (by rfl) ⟨403409, by rfl⟩ : syracuseStep 2151517 = 806819) (by norm_num)
theorem B1913953 : Blo 1699550 1913953 := bbase (se 2 (by rfl) ⟨717732, by rfl⟩ : syracuseStep 1913953 = 1435465) (by norm_num)
theorem B1913989 : Blo 1699550 1913989 := bbase (se 4 (by rfl) ⟨179436, by rfl⟩ : syracuseStep 1913989 = 358873) (by norm_num)
theorem B4306061 : Blo 1699550 4306061 := bbase (se 3 (by rfl) ⟨807386, by rfl⟩ : syracuseStep 4306061 = 1614773) (by norm_num)
theorem B1914025 : Blo 1699550 1914025 := bbase (se 2 (by rfl) ⟨717759, by rfl⟩ : syracuseStep 1914025 = 1435519) (by norm_num)
theorem B2151613 : Blo 1699550 2151613 := bbase (se 3 (by rfl) ⟨403427, by rfl⟩ : syracuseStep 2151613 = 806855) (by norm_num)
theorem B1914061 : Blo 1699550 1914061 := bbase (se 3 (by rfl) ⟨358886, by rfl⟩ : syracuseStep 1914061 = 717773) (by norm_num)
theorem B1914097 : Blo 1699550 1914097 := bbase (se 2 (by rfl) ⟨717786, by rfl⟩ : syracuseStep 1914097 = 1435573) (by norm_num)
theorem B1914133 : Blo 1699550 1914133 := bbase (se 6 (by rfl) ⟨44862, by rfl⟩ : syracuseStep 1914133 = 89725) (by norm_num)
theorem B5387573 : Blo 1699550 5387573 := bbase (se 5 (by rfl) ⟨252542, by rfl⟩ : syracuseStep 5387573 = 505085) (by norm_num)
theorem B1914169 : Blo 1699550 1914169 := bbase (se 2 (by rfl) ⟨717813, by rfl⟩ : syracuseStep 1914169 = 1435627) (by norm_num)
theorem B1914205 : Blo 1699550 1914205 := bbase (se 3 (by rfl) ⟨358913, by rfl⟩ : syracuseStep 1914205 = 717827) (by norm_num)
theorem B2151785 : Blo 1699550 2151785 := bbase (se 2 (by rfl) ⟨806919, by rfl⟩ : syracuseStep 2151785 = 1613839) (by norm_num)
theorem B1914241 : Blo 1699550 1914241 := bbase (se 2 (by rfl) ⟨717840, by rfl⟩ : syracuseStep 1914241 = 1435681) (by norm_num)
theorem B3880325 : Blo 1699550 3880325 := bbase (se 4 (by rfl) ⟨363780, by rfl⟩ : syracuseStep 3880325 = 727561) (by norm_num)
theorem B2151841 : Blo 1699550 2151841 := bbase (se 2 (by rfl) ⟨806940, by rfl⟩ : syracuseStep 2151841 = 1613881) (by norm_num)
theorem B7566805 : Blo 1699550 7566805 := bbase (se 7 (by rfl) ⟨88673, by rfl⟩ : syracuseStep 7566805 = 177347) (by norm_num)
theorem B4306405 : Blo 1699550 4306405 := bbase (se 4 (by rfl) ⟨403725, by rfl⟩ : syracuseStep 4306405 = 807451) (by norm_num)
theorem B8607221 : Blo 1699550 8607221 := bbase (se 5 (by rfl) ⟨403463, by rfl⟩ : syracuseStep 8607221 = 806927) (by norm_num)
theorem B2151937 : Blo 1699550 2151937 := bbase (se 2 (by rfl) ⟨806976, by rfl⟩ : syracuseStep 2151937 = 1613953) (by norm_num)
theorem B5740037 : Blo 1699550 5740037 := bbase (se 4 (by rfl) ⟨538128, by rfl⟩ : syracuseStep 5740037 = 1076257) (by norm_num)
theorem B2422325 : Blo 1699550 2422325 := bbase (se 5 (by rfl) ⟨113546, by rfl⟩ : syracuseStep 2422325 = 227093) (by norm_num)
theorem B1816129 : Blo 1699550 1816129 := bbase (se 2 (by rfl) ⟨681048, by rfl⟩ : syracuseStep 1816129 = 1362097) (by norm_num)
theorem B4306517 : Blo 1699550 4306517 := bbase (se 8 (by rfl) ⟨25233, by rfl⟩ : syracuseStep 4306517 = 50467) (by norm_num)
theorem B3446405 : Blo 1699550 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B1816201 : Blo 1699550 1816201 := bbase (se 2 (by rfl) ⟨681075, by rfl⟩ : syracuseStep 1816201 = 1362151) (by norm_num)
theorem B2152109 : Blo 1699550 2152109 := bbase (se 3 (by rfl) ⟨403520, by rfl⟩ : syracuseStep 2152109 = 807041) (by norm_num)
theorem B2152165 : Blo 1699550 2152165 := bbase (se 4 (by rfl) ⟨201765, by rfl⟩ : syracuseStep 2152165 = 403531) (by norm_num)
theorem B6543109 : Blo 1699550 6543109 := bbase (se 4 (by rfl) ⟨613416, by rfl⟩ : syracuseStep 6543109 = 1226833) (by norm_num)
theorem B4306709 : Blo 1699550 4306709 := bbase (se 6 (by rfl) ⟨100938, by rfl⟩ : syracuseStep 4306709 = 201877) (by norm_num)
theorem B1816381 : Blo 1699550 1816381 := bbase (se 3 (by rfl) ⟨340571, by rfl⟩ : syracuseStep 1816381 = 681143) (by norm_num)
theorem B2152261 : Blo 1699550 2152261 := bbase (se 4 (by rfl) ⟨201774, by rfl⟩ : syracuseStep 2152261 = 403549) (by norm_num)
theorem B5740469 : Blo 1699550 5740469 := bbase (se 5 (by rfl) ⟨269084, by rfl⟩ : syracuseStep 5740469 = 538169) (by norm_num)
theorem B2152433 : Blo 1699550 2152433 := bbase (se 2 (by rfl) ⟨807162, by rfl⟩ : syracuseStep 2152433 = 1614325) (by norm_num)
theorem B2152489 : Blo 1699550 2152489 := bbase (se 2 (by rfl) ⟨807183, by rfl⟩ : syracuseStep 2152489 = 1614367) (by norm_num)
theorem B10893365 : Blo 1699550 10893365 := bbase (se 5 (by rfl) ⟨510626, by rfl⟩ : syracuseStep 10893365 = 1021253) (by norm_num)
theorem B2619461 : Blo 1699550 2619461 := bbase (se 4 (by rfl) ⟨245574, by rfl⟩ : syracuseStep 2619461 = 491149) (by norm_num)
theorem B4364381 : Blo 1699550 4364381 := bbase (se 3 (by rfl) ⟨818321, by rfl⟩ : syracuseStep 4364381 = 1636643) (by norm_num)
theorem B5445733 : Blo 1699550 5445733 := bbase (se 4 (by rfl) ⟨510537, by rfl⟩ : syracuseStep 5445733 = 1021075) (by norm_num)
theorem B7362677 : Blo 1699550 7362677 := bbase (se 5 (by rfl) ⟨345125, by rfl⟩ : syracuseStep 7362677 = 690251) (by norm_num)
theorem B2152585 : Blo 1699550 2152585 := bbase (se 2 (by rfl) ⟨807219, by rfl⟩ : syracuseStep 2152585 = 1614439) (by norm_num)
theorem B1841329 : Blo 1699550 1841329 := bbase (se 2 (by rfl) ⟨690498, by rfl⟩ : syracuseStep 1841329 = 1380997) (by norm_num)
theorem B1816825 : Blo 1699550 1816825 := bbase (se 2 (by rfl) ⟨681309, by rfl⟩ : syracuseStep 1816825 = 1362619) (by norm_num)
theorem B3447037 : Blo 1699550 3447037 := bbase (se 3 (by rfl) ⟨646319, by rfl⟩ : syracuseStep 3447037 = 1292639) (by norm_num)
theorem B2152757 : Blo 1699550 2152757 := bbase (se 5 (by rfl) ⟨100910, by rfl⟩ : syracuseStep 2152757 = 201821) (by norm_num)
theorem B3733813 : Blo 1699550 3733813 := bbase (se 5 (by rfl) ⟨175022, by rfl⟩ : syracuseStep 3733813 = 350045) (by norm_num)
theorem B3447101 : Blo 1699550 3447101 := bbase (se 3 (by rfl) ⟨646331, by rfl⟩ : syracuseStep 3447101 = 1292663) (by norm_num)
theorem B5740901 : Blo 1699550 5740901 := bbase (se 4 (by rfl) ⟨538209, by rfl⟩ : syracuseStep 5740901 = 1076419) (by norm_num)
theorem B2152813 : Blo 1699550 2152813 := bbase (se 3 (by rfl) ⟨403652, by rfl⟩ : syracuseStep 2152813 = 807305) (by norm_num)
theorem B1816949 : Blo 1699550 1816949 := bbase (se 5 (by rfl) ⟨85169, by rfl⟩ : syracuseStep 1816949 = 170339) (by norm_num)
theorem B14522773 : Blo 1699550 14522773 := bbase (se 6 (by rfl) ⟨340377, by rfl⟩ : syracuseStep 14522773 = 680755) (by norm_num)
theorem B6125989 : Blo 1699550 6125989 := bbase (se 4 (by rfl) ⟨574311, by rfl⟩ : syracuseStep 6125989 = 1148623) (by norm_num)
theorem B3824045 : Blo 1699550 3824045 := bbase (se 3 (by rfl) ⟨717008, by rfl⟩ : syracuseStep 3824045 = 1434017) (by norm_num)
theorem B6453701 : Blo 1699550 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B2152909 : Blo 1699550 2152909 := bbase (se 3 (by rfl) ⟨403670, by rfl⟩ : syracuseStep 2152909 = 807341) (by norm_num)
theorem B3824117 : Blo 1699550 3824117 := bbase (se 5 (by rfl) ⟨179255, by rfl⟩ : syracuseStep 3824117 = 358511) (by norm_num)
theorem B3824189 : Blo 1699550 3824189 := bbase (se 3 (by rfl) ⟨717035, by rfl⟩ : syracuseStep 3824189 = 1434071) (by norm_num)
theorem B4422221 : Blo 1699550 4422221 := bbase (se 3 (by rfl) ⟨829166, by rfl⟩ : syracuseStep 4422221 = 1658333) (by norm_num)
theorem B1940053 : Blo 1699550 1940053 := bbase (se 8 (by rfl) ⟨11367, by rfl⟩ : syracuseStep 1940053 = 22735) (by norm_num)
theorem B4840037 : Blo 1699550 4840037 := bbase (se 4 (by rfl) ⟨453753, by rfl⟩ : syracuseStep 4840037 = 907507) (by norm_num)
theorem B2153081 : Blo 1699550 2153081 := bbase (se 2 (by rfl) ⟨807405, by rfl⟩ : syracuseStep 2153081 = 1614811) (by norm_num)
theorem B1940089 : Blo 1699550 1940089 := bbase (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) (by norm_num)
theorem B3824261 : Blo 1699550 3824261 := bbase (se 4 (by rfl) ⟨358524, by rfl⟩ : syracuseStep 3824261 = 717049) (by norm_num)
theorem B2153137 : Blo 1699550 2153137 := bbase (se 2 (by rfl) ⟨807426, by rfl⟩ : syracuseStep 2153137 = 1614853) (by norm_num)
theorem B3824333 : Blo 1699550 3824333 := bbase (se 3 (by rfl) ⟨717062, by rfl⟩ : syracuseStep 3824333 = 1434125) (by norm_num)
theorem B6453989 : Blo 1699550 6453989 := bbase (se 4 (by rfl) ⟨605061, by rfl⟩ : syracuseStep 6453989 = 1210123) (by norm_num)
theorem B8608517 : Blo 1699550 8608517 := bbase (se 4 (by rfl) ⟨807048, by rfl⟩ : syracuseStep 8608517 = 1614097) (by norm_num)
theorem B2153233 : Blo 1699550 2153233 := bbase (se 2 (by rfl) ⟨807462, by rfl⟩ : syracuseStep 2153233 = 1614925) (by norm_num)
theorem B3824405 : Blo 1699550 3824405 := bbase (se 6 (by rfl) ⟨89634, by rfl⟩ : syracuseStep 3824405 = 179269) (by norm_num)
theorem B5741333 : Blo 1699550 5741333 := bbase (se 6 (by rfl) ⟨134562, by rfl⟩ : syracuseStep 5741333 = 269125) (by norm_num)
theorem B3824477 : Blo 1699550 3824477 := bbase (se 3 (by rfl) ⟨717089, by rfl⟩ : syracuseStep 3824477 = 1434179) (by norm_num)
theorem B6126437 : Blo 1699550 6126437 := bbase (se 4 (by rfl) ⟨574353, by rfl⟩ : syracuseStep 6126437 = 1148707) (by norm_num)
theorem B3226493 : Blo 1699550 3226493 := bbase (se 3 (by rfl) ⟨604967, by rfl⟩ : syracuseStep 3226493 = 1209935) (by norm_num)
theorem B3824549 : Blo 1699550 3824549 := bbase (se 4 (by rfl) ⟨358551, by rfl⟩ : syracuseStep 3824549 = 717103) (by norm_num)
theorem B2153405 : Blo 1699550 2153405 := bbase (se 3 (by rfl) ⟨403763, by rfl⟩ : syracuseStep 2153405 = 807527) (by norm_num)
theorem B3062765 : Blo 1699550 3062765 := bbase (se 3 (by rfl) ⟨574268, by rfl⟩ : syracuseStep 3062765 = 1148537) (by norm_num)
theorem B3824621 : Blo 1699550 3824621 := bbase (se 3 (by rfl) ⟨717116, by rfl⟩ : syracuseStep 3824621 = 1434233) (by norm_num)
theorem B2153461 : Blo 1699550 2153461 := bbase (se 5 (by rfl) ⟨100943, by rfl⟩ : syracuseStep 2153461 = 201887) (by norm_num)
theorem B3226645 : Blo 1699550 3226645 := bbase (se 6 (by rfl) ⟨75624, by rfl⟩ : syracuseStep 3226645 = 151249) (by norm_num)
theorem B4840469 : Blo 1699550 4840469 := bbase (se 6 (by rfl) ⟨113448, by rfl⟩ : syracuseStep 4840469 = 226897) (by norm_num)
theorem B3824693 : Blo 1699550 3824693 := bbase (se 5 (by rfl) ⟨179282, by rfl⟩ : syracuseStep 3824693 = 358565) (by norm_num)
theorem B49699925 : Blo 1699550 49699925 := bbase (se 8 (by rfl) ⟨291210, by rfl⟩ : syracuseStep 49699925 = 582421) (by norm_num)
theorem B4660325 : Blo 1699550 4660325 := bbase (se 4 (by rfl) ⟨436905, by rfl⟩ : syracuseStep 4660325 = 873811) (by norm_num)
theorem B10345589 : Blo 1699550 10345589 := bbase (se 5 (by rfl) ⟨484949, by rfl⟩ : syracuseStep 10345589 = 969899) (by norm_num)
theorem B3062909 : Blo 1699550 3062909 := bbase (se 3 (by rfl) ⟨574295, by rfl⟩ : syracuseStep 3062909 = 1148591) (by norm_num)
theorem B3824765 : Blo 1699550 3824765 := bbase (se 3 (by rfl) ⟨717143, by rfl⟩ : syracuseStep 3824765 = 1434287) (by norm_num)
theorem B3824837 : Blo 1699550 3824837 := bbase (se 4 (by rfl) ⟨358578, by rfl⟩ : syracuseStep 3824837 = 717157) (by norm_num)
theorem B5741765 : Blo 1699550 5741765 := bbase (se 4 (by rfl) ⟨538290, by rfl⟩ : syracuseStep 5741765 = 1076581) (by norm_num)
theorem B3824909 : Blo 1699550 3824909 := bbase (se 3 (by rfl) ⟨717170, by rfl⟩ : syracuseStep 3824909 = 1434341) (by norm_num)
theorem B3226949 : Blo 1699550 3226949 := bbase (se 4 (by rfl) ⟨302526, by rfl⟩ : syracuseStep 3226949 = 605053) (by norm_num)
theorem B3824981 : Blo 1699550 3824981 := bbase (se 11 (by rfl) ⟨2801, by rfl⟩ : syracuseStep 3824981 = 5603) (by norm_num)
theorem B3825053 : Blo 1699550 3825053 := bbase (se 3 (by rfl) ⟨717197, by rfl⟩ : syracuseStep 3825053 = 1434395) (by norm_num)
theorem B44203477 : Blo 1699550 44203477 := bbase (se 7 (by rfl) ⟨518009, by rfl⟩ : syracuseStep 44203477 = 1036019) (by norm_num)
theorem B3825125 : Blo 1699550 3825125 := bbase (se 4 (by rfl) ⟨358605, by rfl⟩ : syracuseStep 3825125 = 717211) (by norm_num)
theorem B3825197 : Blo 1699550 3825197 := bbase (se 3 (by rfl) ⟨717224, by rfl⟩ : syracuseStep 3825197 = 1434449) (by norm_num)
theorem B6381125 : Blo 1699550 6381125 := bbase (se 4 (by rfl) ⟨598230, by rfl⟩ : syracuseStep 6381125 = 1196461) (by norm_num)
theorem B6897221 : Blo 1699550 6897221 := bbase (se 4 (by rfl) ⟨646614, by rfl⟩ : syracuseStep 6897221 = 1293229) (by norm_num)
theorem B3825269 : Blo 1699550 3825269 := bbase (se 5 (by rfl) ⟨179309, by rfl⟩ : syracuseStep 3825269 = 358619) (by norm_num)
theorem B5742197 : Blo 1699550 5742197 := bbase (se 5 (by rfl) ⟨269165, by rfl⟩ : syracuseStep 5742197 = 538331) (by norm_num)
theorem B3825341 : Blo 1699550 3825341 := bbase (se 3 (by rfl) ⟨717251, by rfl⟩ : syracuseStep 3825341 = 1434503) (by norm_num)
theorem B4841221 : Blo 1699550 4841221 := bbase (se 4 (by rfl) ⟨453864, by rfl⟩ : syracuseStep 4841221 = 907729) (by norm_num)
theorem B3825413 : Blo 1699550 3825413 := bbase (se 4 (by rfl) ⟨358632, by rfl⟩ : syracuseStep 3825413 = 717265) (by norm_num)
theorem B7757621 : Blo 1699550 7757621 := bbase (se 5 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 7757621 = 727277) (by norm_num)
theorem B10485557 : Blo 1699550 10485557 := bbase (se 5 (by rfl) ⟨491510, by rfl⟩ : syracuseStep 10485557 = 983021) (by norm_num)
theorem B3063629 : Blo 1699550 3063629 := bbase (se 3 (by rfl) ⟨574430, by rfl⟩ : syracuseStep 3063629 = 1148861) (by norm_num)
theorem B3825485 : Blo 1699550 3825485 := bbase (se 3 (by rfl) ⟨717278, by rfl⟩ : syracuseStep 3825485 = 1434557) (by norm_num)
theorem B6455173 : Blo 1699550 6455173 := bbase (se 4 (by rfl) ⟨605172, by rfl⟩ : syracuseStep 6455173 = 1210345) (by norm_num)
theorem B3825557 : Blo 1699550 3825557 := bbase (se 6 (by rfl) ⟨89661, by rfl⟩ : syracuseStep 3825557 = 179323) (by norm_num)
theorem B3448757 : Blo 1699550 3448757 := bbase (se 5 (by rfl) ⟨161660, by rfl⟩ : syracuseStep 3448757 = 323321) (by norm_num)
theorem B3825629 : Blo 1699550 3825629 := bbase (se 3 (by rfl) ⟨717305, by rfl⟩ : syracuseStep 3825629 = 1434611) (by norm_num)
theorem B7266293 : Blo 1699550 7266293 := bbase (se 5 (by rfl) ⟨340607, by rfl⟩ : syracuseStep 7266293 = 681215) (by norm_num)
theorem B10346609 : Blo 1699550 10346609 := bstep (se 2 (by rfl) ⟨3879978, by rfl⟩ : syracuseStep 10346609 = 7759957) B7759957
theorem B3825809 : Blo 1699550 3825809 := bstep (se 2 (by rfl) ⟨1434678, by rfl⟩ : syracuseStep 3825809 = 2869357) B2869357
theorem B3825827 : Blo 1699550 3825827 := bstep (se 1 (by rfl) ⟨2869370, by rfl⟩ : syracuseStep 3825827 = 5738741) B5738741
theorem B6545585 : Blo 1699550 6545585 := bstep (se 2 (by rfl) ⟨2454594, by rfl⟩ : syracuseStep 6545585 = 4909189) B4909189
theorem B9683171 : Blo 1699550 9683171 := bstep (se 1 (by rfl) ⟨7262378, by rfl⟩ : syracuseStep 9683171 = 14524757) B14524757
theorem B3227921 : Blo 1699550 3227921 := bstep (se 2 (by rfl) ⟨1210470, by rfl⟩ : syracuseStep 3227921 = 2420941) B2420941
theorem B6127949 : Blo 1699550 6127949 := bstep (se 3 (by rfl) ⟨1148990, by rfl⟩ : syracuseStep 6127949 = 2297981) B2297981
theorem B4596049 : Blo 1699550 4596049 := bstep (se 2 (by rfl) ⟨1723518, by rfl⟩ : syracuseStep 4596049 = 3447037) B3447037
theorem B3064177 : Blo 1699550 3064177 := bstep (se 2 (by rfl) ⟨1149066, by rfl⟩ : syracuseStep 3064177 = 2298133) B2298133
theorem B3826097 : Blo 1699550 3826097 := bstep (se 2 (by rfl) ⟨1434786, by rfl⟩ : syracuseStep 3826097 = 2869573) B2869573
theorem B3826115 : Blo 1699550 3826115 := bstep (se 1 (by rfl) ⟨2869586, by rfl⟩ : syracuseStep 3826115 = 5739173) B5739173
theorem B12911075 : Blo 1699550 12911075 := bstep (se 1 (by rfl) ⟨9683306, by rfl⟩ : syracuseStep 12911075 = 19366613) B19366613
theorem B8167985 : Blo 1699550 8167985 := bstep (se 2 (by rfl) ⟨3062994, by rfl⟩ : syracuseStep 8167985 = 6125989) B6125989
theorem B37274165 : Blo 1699550 37274165 := bstep (se 5 (by rfl) ⟨1747226, by rfl⟩ : syracuseStep 37274165 = 3494453) B3494453
theorem B5448323 : Blo 1699550 5448323 := bstep (se 1 (by rfl) ⟨4086242, by rfl⟩ : syracuseStep 5448323 = 8172485) B8172485
theorem B22094477 : Blo 1699550 22094477 := bstep (se 3 (by rfl) ⟨4142714, by rfl⟩ : syracuseStep 22094477 = 8285429) B8285429
theorem B3826385 : Blo 1699550 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B3826403 : Blo 1699550 3826403 := bstep (se 1 (by rfl) ⟨2869802, by rfl⟩ : syracuseStep 3826403 = 5739605) B5739605
theorem B9192269 : Blo 1699550 9192269 := bstep (se 3 (by rfl) ⟨1723550, by rfl⟩ : syracuseStep 9192269 = 3447101) B3447101
theorem B2868115 : Blo 1699550 2868115 := bstep (se 1 (by rfl) ⟨2151086, by rfl⟩ : syracuseStep 2868115 = 4302173) B4302173
theorem B3826673 : Blo 1699550 3826673 := bstep (se 2 (by rfl) ⟨1435002, by rfl⟩ : syracuseStep 3826673 = 2870005) B2870005
theorem B3826691 : Blo 1699550 3826691 := bstep (se 1 (by rfl) ⟨2870018, by rfl⟩ : syracuseStep 3826691 = 5740037) B5740037
theorem B10347533 : Blo 1699550 10347533 := bstep (se 3 (by rfl) ⟨1940162, by rfl⟩ : syracuseStep 10347533 = 3880325) B3880325
theorem B2868257 : Blo 1699550 2868257 := bstep (se 2 (by rfl) ⟨1075596, by rfl⟩ : syracuseStep 2868257 = 2151193) B2151193
theorem B6456419 : Blo 1699550 6456419 := bstep (se 1 (by rfl) ⟨4842314, by rfl⟩ : syracuseStep 6456419 = 9684629) B9684629
theorem B3228817 : Blo 1699550 3228817 := bstep (se 2 (by rfl) ⟨1210806, by rfl⟩ : syracuseStep 3228817 = 2421613) B2421613
theorem B2868385 : Blo 1699550 2868385 := bstep (se 2 (by rfl) ⟨1075644, by rfl⟩ : syracuseStep 2868385 = 2151289) B2151289
theorem B2868419 : Blo 1699550 2868419 := bstep (se 1 (by rfl) ⟨2151314, by rfl⟩ : syracuseStep 2868419 = 4302629) B4302629
theorem B4842737 : Blo 1699550 4842737 := bstep (se 2 (by rfl) ⟨1816026, by rfl⟩ : syracuseStep 4842737 = 3632053) B3632053
theorem B3826961 : Blo 1699550 3826961 := bstep (se 2 (by rfl) ⟨1435110, by rfl⟩ : syracuseStep 3826961 = 2870221) B2870221
theorem B3826979 : Blo 1699550 3826979 := bstep (se 1 (by rfl) ⟨2870234, by rfl⟩ : syracuseStep 3826979 = 5740469) B5740469
theorem B3228977 : Blo 1699550 3228977 := bstep (se 2 (by rfl) ⟨1210866, by rfl⟩ : syracuseStep 3228977 = 2421733) B2421733
theorem B2868547 : Blo 1699550 2868547 := bstep (se 1 (by rfl) ⟨2151410, by rfl⟩ : syracuseStep 2868547 = 4302821) B4302821
theorem B4302193 : Blo 1699550 4302193 := bstep (se 2 (by rfl) ⟨1613322, by rfl⟩ : syracuseStep 4302193 = 3226645) B3226645
theorem B34915697 : Blo 1699550 34915697 := bstep (se 2 (by rfl) ⟨13093386, by rfl⟩ : syracuseStep 34915697 = 26186773) B26186773
theorem B1746307 : Blo 1699550 1746307 := bstep (se 1 (by rfl) ⟨1309730, by rfl⟩ : syracuseStep 1746307 = 2619461) B2619461
theorem B4908451 : Blo 1699550 4908451 := bstep (se 1 (by rfl) ⟨3681338, by rfl⟩ : syracuseStep 4908451 = 7362677) B7362677
theorem B4842929 : Blo 1699550 4842929 := bstep (se 2 (by rfl) ⟨1816098, by rfl⟩ : syracuseStep 4842929 = 3632197) B3632197
theorem B2868689 : Blo 1699550 2868689 := bstep (se 2 (by rfl) ⟨1075758, by rfl⟩ : syracuseStep 2868689 = 2151517) B2151517
theorem B3827249 : Blo 1699550 3827249 := bstep (se 2 (by rfl) ⟨1435218, by rfl⟩ : syracuseStep 3827249 = 2870437) B2870437
theorem B3827267 : Blo 1699550 3827267 := bstep (se 1 (by rfl) ⟨2870450, by rfl⟩ : syracuseStep 3827267 = 5740901) B5740901
theorem B2868817 : Blo 1699550 2868817 := bstep (se 2 (by rfl) ⟨1075806, by rfl⟩ : syracuseStep 2868817 = 2151613) B2151613
theorem B2549345 : Blo 1699550 2549345 := bstep (se 2 (by rfl) ⟨956004, by rfl⟩ : syracuseStep 2549345 = 1912009) B1912009
theorem B37774961 : Blo 1699550 37774961 := bstep (se 2 (by rfl) ⟨14165610, by rfl⟩ : syracuseStep 37774961 = 28331221) B28331221
theorem B2549363 : Blo 1699550 2549363 := bstep (se 1 (by rfl) ⟨1912022, by rfl⟩ : syracuseStep 2549363 = 3824045) B3824045
theorem B2868851 : Blo 1699550 2868851 := bstep (se 1 (by rfl) ⟨2151638, by rfl⟩ : syracuseStep 2868851 = 4303277) B4303277
theorem B4302467 : Blo 1699550 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B2549393 : Blo 1699550 2549393 := bstep (se 2 (by rfl) ⟨956022, by rfl⟩ : syracuseStep 2549393 = 1912045) B1912045
theorem B2549411 : Blo 1699550 2549411 := bstep (se 1 (by rfl) ⟨1912058, by rfl⟩ : syracuseStep 2549411 = 3824117) B3824117
theorem B2549441 : Blo 1699550 2549441 := bstep (se 2 (by rfl) ⟨956040, by rfl⟩ : syracuseStep 2549441 = 1912081) B1912081
theorem B3229379 : Blo 1699550 3229379 := bstep (se 1 (by rfl) ⟨2422034, by rfl⟩ : syracuseStep 3229379 = 4844069) B4844069
theorem B10340045 : Blo 1699550 10340045 := bstep (se 3 (by rfl) ⟨1938758, by rfl⟩ : syracuseStep 10340045 = 3877517) B3877517
theorem B7366349 : Blo 1699550 7366349 := bstep (se 3 (by rfl) ⟨1381190, by rfl⟩ : syracuseStep 7366349 = 2762381) B2762381
theorem B2549459 : Blo 1699550 2549459 := bstep (se 1 (by rfl) ⟨1912094, by rfl⟩ : syracuseStep 2549459 = 3824189) B3824189
theorem B2549489 : Blo 1699550 2549489 := bstep (se 2 (by rfl) ⟨956058, by rfl⟩ : syracuseStep 2549489 = 1912117) B1912117
theorem B2868979 : Blo 1699550 2868979 := bstep (se 1 (by rfl) ⟨2151734, by rfl⟩ : syracuseStep 2868979 = 4303469) B4303469
theorem B2549507 : Blo 1699550 2549507 := bstep (se 1 (by rfl) ⟨1912130, by rfl⟩ : syracuseStep 2549507 = 3824261) B3824261
theorem B3630865 : Blo 1699550 3630865 := bstep (se 2 (by rfl) ⟨1361574, by rfl⟩ : syracuseStep 3630865 = 2723149) B2723149
theorem B2098963 : Blo 1699550 2098963 := bstep (se 1 (by rfl) ⟨1574222, by rfl⟩ : syracuseStep 2098963 = 3148445) B3148445
theorem B2549537 : Blo 1699550 2549537 := bstep (se 2 (by rfl) ⟨956076, by rfl⟩ : syracuseStep 2549537 = 1912153) B1912153
theorem B2549555 : Blo 1699550 2549555 := bstep (se 1 (by rfl) ⟨1912166, by rfl⟩ : syracuseStep 2549555 = 3824333) B3824333
theorem B4302659 : Blo 1699550 4302659 := bstep (se 1 (by rfl) ⟨3226994, by rfl⟩ : syracuseStep 4302659 = 6453989) B6453989
theorem B2549585 : Blo 1699550 2549585 := bstep (se 2 (by rfl) ⟨956094, by rfl⟩ : syracuseStep 2549585 = 1912189) B1912189
theorem B3827537 : Blo 1699550 3827537 := bstep (se 2 (by rfl) ⟨1435326, by rfl⟩ : syracuseStep 3827537 = 2870653) B2870653
theorem B2549603 : Blo 1699550 2549603 := bstep (se 1 (by rfl) ⟨1912202, by rfl⟩ : syracuseStep 2549603 = 3824405) B3824405
theorem B3827555 : Blo 1699550 3827555 := bstep (se 1 (by rfl) ⟨2870666, by rfl⟩ : syracuseStep 3827555 = 5741333) B5741333
theorem B2549633 : Blo 1699550 2549633 := bstep (se 2 (by rfl) ⟨956112, by rfl⟩ : syracuseStep 2549633 = 1912225) B1912225
theorem B2869121 : Blo 1699550 2869121 := bstep (se 2 (by rfl) ⟨1075920, by rfl⟩ : syracuseStep 2869121 = 2151841) B2151841
theorem B2549651 : Blo 1699550 2549651 := bstep (se 1 (by rfl) ⟨1912238, by rfl⟩ : syracuseStep 2549651 = 3824477) B3824477
theorem B5736365 : Blo 1699550 5736365 := bstep (se 3 (by rfl) ⟨1075568, by rfl⟩ : syracuseStep 5736365 = 2151137) B2151137
theorem B2549681 : Blo 1699550 2549681 := bstep (se 2 (by rfl) ⟨956130, by rfl⟩ : syracuseStep 2549681 = 1912261) B1912261
theorem B2549699 : Blo 1699550 2549699 := bstep (se 1 (by rfl) ⟨1912274, by rfl⟩ : syracuseStep 2549699 = 3824549) B3824549
theorem B2549729 : Blo 1699550 2549729 := bstep (se 2 (by rfl) ⟨956148, by rfl⟩ : syracuseStep 2549729 = 1912297) B1912297
theorem B5736419 : Blo 1699550 5736419 := bstep (se 1 (by rfl) ⟨4302314, by rfl⟩ : syracuseStep 5736419 = 8604629) B8604629
theorem B2041843 : Blo 1699550 2041843 := bstep (se 1 (by rfl) ⟨1531382, by rfl⟩ : syracuseStep 2041843 = 3062765) B3062765
theorem B2549747 : Blo 1699550 2549747 := bstep (se 1 (by rfl) ⟨1912310, by rfl⟩ : syracuseStep 2549747 = 3824621) B3824621
theorem B2869249 : Blo 1699550 2869249 := bstep (se 2 (by rfl) ⟨1075968, by rfl⟩ : syracuseStep 2869249 = 2151937) B2151937
theorem B2549777 : Blo 1699550 2549777 := bstep (se 2 (by rfl) ⟨956166, by rfl⟩ : syracuseStep 2549777 = 1912333) B1912333
theorem B2549795 : Blo 1699550 2549795 := bstep (se 1 (by rfl) ⟨1912346, by rfl⟩ : syracuseStep 2549795 = 3824693) B3824693
theorem B2869283 : Blo 1699550 2869283 := bstep (se 1 (by rfl) ⟨2151962, by rfl⟩ : syracuseStep 2869283 = 4303925) B4303925
theorem B2549825 : Blo 1699550 2549825 := bstep (se 2 (by rfl) ⟨956184, by rfl⟩ : syracuseStep 2549825 = 1912369) B1912369
theorem B3106883 : Blo 1699550 3106883 := bstep (se 1 (by rfl) ⟨2330162, by rfl⟩ : syracuseStep 3106883 = 4660325) B4660325
theorem B6457421 : Blo 1699550 6457421 := bstep (se 3 (by rfl) ⟨1210766, by rfl⟩ : syracuseStep 6457421 = 2421533) B2421533
theorem B2041939 : Blo 1699550 2041939 := bstep (se 1 (by rfl) ⟨1531454, by rfl⟩ : syracuseStep 2041939 = 3062909) B3062909
theorem B2549843 : Blo 1699550 2549843 := bstep (se 1 (by rfl) ⟨1912382, by rfl⟩ : syracuseStep 2549843 = 3824765) B3824765
theorem B2549873 : Blo 1699550 2549873 := bstep (se 2 (by rfl) ⟨956202, by rfl⟩ : syracuseStep 2549873 = 1912405) B1912405
theorem B3827825 : Blo 1699550 3827825 := bstep (se 2 (by rfl) ⟨1435434, by rfl⟩ : syracuseStep 3827825 = 2870869) B2870869
theorem B2549891 : Blo 1699550 2549891 := bstep (se 1 (by rfl) ⟨1912418, by rfl⟩ : syracuseStep 2549891 = 3824837) B3824837
theorem B3827843 : Blo 1699550 3827843 := bstep (se 1 (by rfl) ⟨2870882, by rfl⟩ : syracuseStep 3827843 = 5741765) B5741765
theorem B3065987 : Blo 1699550 3065987 := bstep (se 1 (by rfl) ⟨2299490, by rfl⟩ : syracuseStep 3065987 = 4598981) B4598981
theorem B2549921 : Blo 1699550 2549921 := bstep (se 2 (by rfl) ⟨956220, by rfl⟩ : syracuseStep 2549921 = 1912441) B1912441
theorem B2869411 : Blo 1699550 2869411 := bstep (se 1 (by rfl) ⟨2152058, by rfl⟩ : syracuseStep 2869411 = 4304117) B4304117
theorem B2549939 : Blo 1699550 2549939 := bstep (se 1 (by rfl) ⟨1912454, by rfl⟩ : syracuseStep 2549939 = 3824909) B3824909
theorem B2549969 : Blo 1699550 2549969 := bstep (se 2 (by rfl) ⟨956238, by rfl⟩ : syracuseStep 2549969 = 1912477) B1912477
theorem B2549987 : Blo 1699550 2549987 := bstep (se 1 (by rfl) ⟨1912490, by rfl⟩ : syracuseStep 2549987 = 3824981) B3824981
theorem B5736689 : Blo 1699550 5736689 := bstep (se 2 (by rfl) ⟨2151258, by rfl⟩ : syracuseStep 5736689 = 4302517) B4302517
theorem B8612081 : Blo 1699550 8612081 := bstep (se 2 (by rfl) ⟨3229530, by rfl⟩ : syracuseStep 8612081 = 6459061) B6459061
theorem B2550017 : Blo 1699550 2550017 := bstep (se 2 (by rfl) ⟨956256, by rfl⟩ : syracuseStep 2550017 = 1912513) B1912513
theorem B2550035 : Blo 1699550 2550035 := bstep (se 1 (by rfl) ⟨1912526, by rfl⟩ : syracuseStep 2550035 = 3825053) B3825053
theorem B2550065 : Blo 1699550 2550065 := bstep (se 2 (by rfl) ⟨956274, by rfl⟩ : syracuseStep 2550065 = 1912549) B1912549
theorem B2869553 : Blo 1699550 2869553 := bstep (se 2 (by rfl) ⟨1076082, by rfl⟩ : syracuseStep 2869553 = 2152165) B2152165
theorem B2550083 : Blo 1699550 2550083 := bstep (se 1 (by rfl) ⟨1912562, by rfl⟩ : syracuseStep 2550083 = 3825125) B3825125
theorem B8603981 : Blo 1699550 8603981 := bstep (se 3 (by rfl) ⟨1613246, by rfl⟩ : syracuseStep 8603981 = 3226493) B3226493
theorem B2550113 : Blo 1699550 2550113 := bstep (se 2 (by rfl) ⟨956292, by rfl⟩ : syracuseStep 2550113 = 1912585) B1912585
theorem B2550131 : Blo 1699550 2550131 := bstep (se 1 (by rfl) ⟨1912598, by rfl⟩ : syracuseStep 2550131 = 3825197) B3825197
theorem B4254083 : Blo 1699550 4254083 := bstep (se 1 (by rfl) ⟨3190562, by rfl⟩ : syracuseStep 4254083 = 6381125) B6381125
theorem B4598147 : Blo 1699550 4598147 := bstep (se 1 (by rfl) ⟨3448610, by rfl⟩ : syracuseStep 4598147 = 6897221) B6897221
theorem B2550161 : Blo 1699550 2550161 := bstep (se 2 (by rfl) ⟨956310, by rfl⟩ : syracuseStep 2550161 = 1912621) B1912621
theorem B4843921 : Blo 1699550 4843921 := bstep (se 2 (by rfl) ⟨1816470, by rfl⟩ : syracuseStep 4843921 = 3632941) B3632941
theorem B3828113 : Blo 1699550 3828113 := bstep (se 2 (by rfl) ⟨1435542, by rfl⟩ : syracuseStep 3828113 = 2871085) B2871085
theorem B2550179 : Blo 1699550 2550179 := bstep (se 1 (by rfl) ⟨1912634, by rfl⟩ : syracuseStep 2550179 = 3825269) B3825269
theorem B3828131 : Blo 1699550 3828131 := bstep (se 1 (by rfl) ⟨2871098, by rfl⟩ : syracuseStep 3828131 = 5742197) B5742197
theorem B2869681 : Blo 1699550 2869681 := bstep (se 2 (by rfl) ⟨1076130, by rfl⟩ : syracuseStep 2869681 = 2152261) B2152261
theorem B2550209 : Blo 1699550 2550209 := bstep (se 2 (by rfl) ⟨956328, by rfl⟩ : syracuseStep 2550209 = 1912657) B1912657
theorem B2550227 : Blo 1699550 2550227 := bstep (se 1 (by rfl) ⟨1912670, by rfl⟩ : syracuseStep 2550227 = 3825341) B3825341
theorem B2869715 : Blo 1699550 2869715 := bstep (se 1 (by rfl) ⟨2152286, by rfl⟩ : syracuseStep 2869715 = 4304573) B4304573
theorem B2550257 : Blo 1699550 2550257 := bstep (se 2 (by rfl) ⟨956346, by rfl⟩ : syracuseStep 2550257 = 1912693) B1912693
theorem B2550275 : Blo 1699550 2550275 := bstep (se 1 (by rfl) ⟨1912706, by rfl⟩ : syracuseStep 2550275 = 3825413) B3825413
theorem B41388565 : Blo 1699550 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B2550305 : Blo 1699550 2550305 := bstep (se 2 (by rfl) ⟨956364, by rfl⟩ : syracuseStep 2550305 = 1912729) B1912729
theorem B5171747 : Blo 1699550 5171747 := bstep (se 1 (by rfl) ⟨3878810, by rfl⟩ : syracuseStep 5171747 = 7757621) B7757621
theorem B6990371 : Blo 1699550 6990371 := bstep (se 1 (by rfl) ⟨5242778, by rfl⟩ : syracuseStep 6990371 = 10485557) B10485557
theorem B2042419 : Blo 1699550 2042419 := bstep (se 1 (by rfl) ⟨1531814, by rfl⟩ : syracuseStep 2042419 = 3063629) B3063629
theorem B2550323 : Blo 1699550 2550323 := bstep (se 1 (by rfl) ⟨1912742, by rfl⟩ : syracuseStep 2550323 = 3825485) B3825485
theorem B3230275 : Blo 1699550 3230275 := bstep (se 1 (by rfl) ⟨2422706, by rfl⟩ : syracuseStep 3230275 = 4845413) B4845413
theorem B2550353 : Blo 1699550 2550353 := bstep (se 2 (by rfl) ⟨956382, by rfl⟩ : syracuseStep 2550353 = 1912765) B1912765
theorem B2869843 : Blo 1699550 2869843 := bstep (se 1 (by rfl) ⟨2152382, by rfl⟩ : syracuseStep 2869843 = 4304765) B4304765
theorem B2550371 : Blo 1699550 2550371 := bstep (se 1 (by rfl) ⟨1912778, by rfl⟩ : syracuseStep 2550371 = 3825557) B3825557
theorem B2550401 : Blo 1699550 2550401 := bstep (se 2 (by rfl) ⟨956400, by rfl⟩ : syracuseStep 2550401 = 1912801) B1912801
theorem B2550419 : Blo 1699550 2550419 := bstep (se 1 (by rfl) ⟨1912814, by rfl⟩ : syracuseStep 2550419 = 3825629) B3825629
theorem B4844195 : Blo 1699550 4844195 := bstep (se 1 (by rfl) ⟨3633146, by rfl⟩ : syracuseStep 4844195 = 7266293) B7266293
theorem B5819053 : Blo 1699550 5819053 := bstep (se 3 (by rfl) ⟨1091072, by rfl⟩ : syracuseStep 5819053 = 2182145) B2182145
theorem B2550449 : Blo 1699550 2550449 := bstep (se 2 (by rfl) ⟨956418, by rfl⟩ : syracuseStep 2550449 = 1912837) B1912837
theorem B3828401 : Blo 1699550 3828401 := bstep (se 2 (by rfl) ⟨1435650, by rfl⟩ : syracuseStep 3828401 = 2871301) B2871301
theorem B2550467 : Blo 1699550 2550467 := bstep (se 1 (by rfl) ⟨1912850, by rfl⟩ : syracuseStep 2550467 = 3825701) B3825701
theorem B3828419 : Blo 1699550 3828419 := bstep (se 1 (by rfl) ⟨2871314, by rfl⟩ : syracuseStep 3828419 = 5742629) B5742629
theorem B5450449 : Blo 1699550 5450449 := bstep (se 2 (by rfl) ⟨2043918, by rfl⟩ : syracuseStep 5450449 = 4087837) B4087837
theorem B2550497 : Blo 1699550 2550497 := bstep (se 2 (by rfl) ⟨956436, by rfl⟩ : syracuseStep 2550497 = 1912873) B1912873
theorem B2869985 : Blo 1699550 2869985 := bstep (se 2 (by rfl) ⟨1076244, by rfl⟩ : syracuseStep 2869985 = 2152489) B2152489
theorem B4303601 : Blo 1699550 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B2550515 : Blo 1699550 2550515 := bstep (se 1 (by rfl) ⟨1912886, by rfl⟩ : syracuseStep 2550515 = 3825773) B3825773
theorem B5737229 : Blo 1699550 5737229 := bstep (se 3 (by rfl) ⟨1075730, by rfl⟩ : syracuseStep 5737229 = 2151461) B2151461
theorem B2550545 : Blo 1699550 2550545 := bstep (se 2 (by rfl) ⟨956454, by rfl⟩ : syracuseStep 2550545 = 1912909) B1912909
theorem B4303651 : Blo 1699550 4303651 := bstep (se 1 (by rfl) ⟨3227738, by rfl⟩ : syracuseStep 4303651 = 6455477) B6455477
theorem B2550563 : Blo 1699550 2550563 := bstep (se 1 (by rfl) ⟨1912922, by rfl⟩ : syracuseStep 2550563 = 3825845) B3825845
theorem B7260977 : Blo 1699550 7260977 := bstep (se 2 (by rfl) ⟨2722866, by rfl⟩ : syracuseStep 7260977 = 5445733) B5445733
theorem B2550593 : Blo 1699550 2550593 := bstep (se 2 (by rfl) ⟨956472, by rfl⟩ : syracuseStep 2550593 = 1912945) B1912945
theorem B5737283 : Blo 1699550 5737283 := bstep (se 1 (by rfl) ⟨4302962, by rfl⟩ : syracuseStep 5737283 = 8605925) B8605925
theorem B2550611 : Blo 1699550 2550611 := bstep (se 1 (by rfl) ⟨1912958, by rfl⟩ : syracuseStep 2550611 = 3825917) B3825917
theorem B2870113 : Blo 1699550 2870113 := bstep (se 2 (by rfl) ⟨1076292, by rfl⟩ : syracuseStep 2870113 = 2152585) B2152585
theorem B4844387 : Blo 1699550 4844387 := bstep (se 1 (by rfl) ⟨3633290, by rfl⟩ : syracuseStep 4844387 = 7266581) B7266581
theorem B2550641 : Blo 1699550 2550641 := bstep (se 2 (by rfl) ⟨956490, by rfl⟩ : syracuseStep 2550641 = 1912981) B1912981
theorem B2722675 : Blo 1699550 2722675 := bstep (se 1 (by rfl) ⟨2042006, by rfl⟩ : syracuseStep 2722675 = 4084013) B4084013
theorem B2550659 : Blo 1699550 2550659 := bstep (se 1 (by rfl) ⟨1912994, by rfl⟩ : syracuseStep 2550659 = 3825989) B3825989
theorem B2870147 : Blo 1699550 2870147 := bstep (se 1 (by rfl) ⟨2152610, by rfl⟩ : syracuseStep 2870147 = 4305221) B4305221
theorem B5172113 : Blo 1699550 5172113 := bstep (se 2 (by rfl) ⟨1939542, by rfl⟩ : syracuseStep 5172113 = 3879085) B3879085
theorem B2550689 : Blo 1699550 2550689 := bstep (se 2 (by rfl) ⟨956508, by rfl⟩ : syracuseStep 2550689 = 1913017) B1913017
theorem B4303793 : Blo 1699550 4303793 := bstep (se 2 (by rfl) ⟨1613922, by rfl⟩ : syracuseStep 4303793 = 3227845) B3227845
theorem B2550707 : Blo 1699550 2550707 := bstep (se 1 (by rfl) ⟨1913030, by rfl⟩ : syracuseStep 2550707 = 3826061) B3826061
theorem B8170445 : Blo 1699550 8170445 := bstep (se 3 (by rfl) ⟨1531958, by rfl⟩ : syracuseStep 8170445 = 3063917) B3063917
theorem B2550737 : Blo 1699550 2550737 := bstep (se 2 (by rfl) ⟨956526, by rfl⟩ : syracuseStep 2550737 = 1913053) B1913053
theorem B13781987 : Blo 1699550 13781987 := bstep (se 1 (by rfl) ⟨10336490, by rfl⟩ : syracuseStep 13781987 = 20672981) B20672981
theorem B2550755 : Blo 1699550 2550755 := bstep (se 1 (by rfl) ⟨1913066, by rfl⟩ : syracuseStep 2550755 = 3826133) B3826133
theorem B2550785 : Blo 1699550 2550785 := bstep (se 2 (by rfl) ⟨956544, by rfl⟩ : syracuseStep 2550785 = 1913089) B1913089
theorem B2870275 : Blo 1699550 2870275 := bstep (se 1 (by rfl) ⟨2152706, by rfl⟩ : syracuseStep 2870275 = 4305413) B4305413
theorem B19360781 : Blo 1699550 19360781 := bstep (se 3 (by rfl) ⟨3630146, by rfl⟩ : syracuseStep 19360781 = 7260293) B7260293
theorem B2550803 : Blo 1699550 2550803 := bstep (se 1 (by rfl) ⟨1913102, by rfl⟩ : syracuseStep 2550803 = 3826205) B3826205
theorem B2550833 : Blo 1699550 2550833 := bstep (se 2 (by rfl) ⟨956562, by rfl⟩ : syracuseStep 2550833 = 1913125) B1913125
theorem B2550851 : Blo 1699550 2550851 := bstep (se 1 (by rfl) ⟨1913138, by rfl⟩ : syracuseStep 2550851 = 3826277) B3826277
theorem B5737553 : Blo 1699550 5737553 := bstep (se 2 (by rfl) ⟨2151582, by rfl⟩ : syracuseStep 5737553 = 4303165) B4303165
theorem B2550881 : Blo 1699550 2550881 := bstep (se 2 (by rfl) ⟨956580, by rfl⟩ : syracuseStep 2550881 = 1913161) B1913161
theorem B2550899 : Blo 1699550 2550899 := bstep (se 1 (by rfl) ⟨1913174, by rfl⟩ : syracuseStep 2550899 = 3826349) B3826349
theorem B2550929 : Blo 1699550 2550929 := bstep (se 2 (by rfl) ⟨956598, by rfl⟩ : syracuseStep 2550929 = 1913197) B1913197
theorem B2870417 : Blo 1699550 2870417 := bstep (se 2 (by rfl) ⟨1076406, by rfl⟩ : syracuseStep 2870417 = 2152813) B2152813
theorem B2550947 : Blo 1699550 2550947 := bstep (se 1 (by rfl) ⟨1913210, by rfl⟩ : syracuseStep 2550947 = 3826421) B3826421
theorem B2550977 : Blo 1699550 2550977 := bstep (se 2 (by rfl) ⟨956616, by rfl⟩ : syracuseStep 2550977 = 1913233) B1913233
theorem B2550995 : Blo 1699550 2550995 := bstep (se 1 (by rfl) ⟨1913246, by rfl⟩ : syracuseStep 2550995 = 3826493) B3826493
theorem B2551025 : Blo 1699550 2551025 := bstep (se 2 (by rfl) ⟨956634, by rfl⟩ : syracuseStep 2551025 = 1913269) B1913269
theorem B2551043 : Blo 1699550 2551043 := bstep (se 1 (by rfl) ⟨1913282, by rfl⟩ : syracuseStep 2551043 = 3826565) B3826565
theorem B2870545 : Blo 1699550 2870545 := bstep (se 2 (by rfl) ⟨1076454, by rfl⟩ : syracuseStep 2870545 = 2152909) B2152909
theorem B2551073 : Blo 1699550 2551073 := bstep (se 2 (by rfl) ⟨956652, by rfl⟩ : syracuseStep 2551073 = 1913305) B1913305
theorem B1912099 : Blo 1699550 1912099 := bstep (se 1 (by rfl) ⟨1434074, by rfl⟩ : syracuseStep 1912099 = 2868149) B2868149
theorem B2723123 : Blo 1699550 2723123 := bstep (se 1 (by rfl) ⟨2042342, by rfl⟩ : syracuseStep 2723123 = 4084685) B4084685
theorem B2551091 : Blo 1699550 2551091 := bstep (se 1 (by rfl) ⟨1913318, by rfl⟩ : syracuseStep 2551091 = 3826637) B3826637
theorem B2870579 : Blo 1699550 2870579 := bstep (se 1 (by rfl) ⟨2152934, by rfl⟩ : syracuseStep 2870579 = 4305869) B4305869
theorem B2297155 : Blo 1699550 2297155 := bstep (se 1 (by rfl) ⟨1722866, by rfl⟩ : syracuseStep 2297155 = 3445733) B3445733
theorem B2551121 : Blo 1699550 2551121 := bstep (se 2 (by rfl) ⟨956670, by rfl⟩ : syracuseStep 2551121 = 1913341) B1913341
theorem B2551139 : Blo 1699550 2551139 := bstep (se 1 (by rfl) ⟨1913354, by rfl⟩ : syracuseStep 2551139 = 3826709) B3826709
theorem B2551169 : Blo 1699550 2551169 := bstep (se 2 (by rfl) ⟨956688, by rfl⟩ : syracuseStep 2551169 = 1913377) B1913377
theorem B9686405 : Blo 1699550 9686405 := bstep (se 4 (by rfl) ⟨908100, by rfl⟩ : syracuseStep 9686405 = 1816201) B1816201
theorem B2551187 : Blo 1699550 2551187 := bstep (se 1 (by rfl) ⟨1913390, by rfl⟩ : syracuseStep 2551187 = 3826781) B3826781
theorem B2551217 : Blo 1699550 2551217 := bstep (se 2 (by rfl) ⟨956706, by rfl⟩ : syracuseStep 2551217 = 1913413) B1913413
theorem B1912243 : Blo 1699550 1912243 := bstep (se 1 (by rfl) ⟨1434182, by rfl⟩ : syracuseStep 1912243 = 2868365) B2868365
theorem B2870707 : Blo 1699550 2870707 := bstep (se 1 (by rfl) ⟨2153030, by rfl⟩ : syracuseStep 2870707 = 4306061) B4306061
theorem B2551235 : Blo 1699550 2551235 := bstep (se 1 (by rfl) ⟨1913426, by rfl⟩ : syracuseStep 2551235 = 3826853) B3826853
theorem B2551265 : Blo 1699550 2551265 := bstep (se 2 (by rfl) ⟨956724, by rfl⟩ : syracuseStep 2551265 = 1913449) B1913449
theorem B2551283 : Blo 1699550 2551283 := bstep (se 1 (by rfl) ⟨1913462, by rfl⟩ : syracuseStep 2551283 = 3826925) B3826925
theorem B2551313 : Blo 1699550 2551313 := bstep (se 2 (by rfl) ⟨956742, by rfl⟩ : syracuseStep 2551313 = 1913485) B1913485
theorem B2551331 : Blo 1699550 2551331 := bstep (se 1 (by rfl) ⟨1913498, by rfl⟩ : syracuseStep 2551331 = 3826997) B3826997
theorem B3591715 : Blo 1699550 3591715 := bstep (se 1 (by rfl) ⟨2693786, by rfl⟩ : syracuseStep 3591715 = 5387573) B5387573
theorem B2420275 : Blo 1699550 2420275 := bstep (se 1 (by rfl) ⟨1815206, by rfl⟩ : syracuseStep 2420275 = 3630413) B3630413
theorem B2551361 : Blo 1699550 2551361 := bstep (se 2 (by rfl) ⟨956760, by rfl⟩ : syracuseStep 2551361 = 1913521) B1913521
theorem B2870849 : Blo 1699550 2870849 := bstep (se 2 (by rfl) ⟨1076568, by rfl⟩ : syracuseStep 2870849 = 2153137) B2153137
theorem B1912387 : Blo 1699550 1912387 := bstep (se 1 (by rfl) ⟨1434290, by rfl⟩ : syracuseStep 1912387 = 2868581) B2868581
theorem B2551379 : Blo 1699550 2551379 := bstep (se 1 (by rfl) ⟨1913534, by rfl⟩ : syracuseStep 2551379 = 3827069) B3827069
theorem B2297441 : Blo 1699550 2297441 := bstep (se 2 (by rfl) ⟨861540, by rfl⟩ : syracuseStep 2297441 = 1723081) B1723081
theorem B5738093 : Blo 1699550 5738093 := bstep (se 3 (by rfl) ⟨1075892, by rfl⟩ : syracuseStep 5738093 = 2151785) B2151785
theorem B2551409 : Blo 1699550 2551409 := bstep (se 2 (by rfl) ⟨956778, by rfl⟩ : syracuseStep 2551409 = 1913557) B1913557
theorem B2551427 : Blo 1699550 2551427 := bstep (se 1 (by rfl) ⟨1913570, by rfl⟩ : syracuseStep 2551427 = 3827141) B3827141
theorem B4845197 : Blo 1699550 4845197 := bstep (se 3 (by rfl) ⟨908474, by rfl⟩ : syracuseStep 4845197 = 1816949) B1816949
theorem B2420371 : Blo 1699550 2420371 := bstep (se 1 (by rfl) ⟨1815278, by rfl⟩ : syracuseStep 2420371 = 3630557) B3630557
theorem B2551457 : Blo 1699550 2551457 := bstep (se 2 (by rfl) ⟨956796, by rfl⟩ : syracuseStep 2551457 = 1913593) B1913593
theorem B5738147 : Blo 1699550 5738147 := bstep (se 1 (by rfl) ⟨4303610, by rfl⟩ : syracuseStep 5738147 = 8607221) B8607221
theorem B8613539 : Blo 1699550 8613539 := bstep (se 1 (by rfl) ⟨6460154, by rfl⟩ : syracuseStep 8613539 = 12920309) B12920309
theorem B2551475 : Blo 1699550 2551475 := bstep (se 1 (by rfl) ⟨1913606, by rfl⟩ : syracuseStep 2551475 = 3827213) B3827213
theorem B2870977 : Blo 1699550 2870977 := bstep (se 2 (by rfl) ⟨1076616, by rfl⟩ : syracuseStep 2870977 = 2153233) B2153233
theorem B2551505 : Blo 1699550 2551505 := bstep (se 2 (by rfl) ⟨956814, by rfl⟩ : syracuseStep 2551505 = 1913629) B1913629
theorem B1912531 : Blo 1699550 1912531 := bstep (se 1 (by rfl) ⟨1434398, by rfl⟩ : syracuseStep 1912531 = 2868797) B2868797
theorem B1699555 : Blo 1699550 1699555 := bstep (se 1 (by rfl) ⟨1274666, by rfl⟩ : syracuseStep 1699555 = 2549333) B2549333
theorem B2551523 : Blo 1699550 2551523 := bstep (se 1 (by rfl) ⟨1913642, by rfl⟩ : syracuseStep 2551523 = 3827285) B3827285
theorem B2871011 : Blo 1699550 2871011 := bstep (se 1 (by rfl) ⟨2153258, by rfl⟩ : syracuseStep 2871011 = 4306517) B4306517
theorem B1699571 : Blo 1699550 1699571 := bstep (se 1 (by rfl) ⟨1274678, by rfl⟩ : syracuseStep 1699571 = 2549357) B2549357
theorem B2551553 : Blo 1699550 2551553 := bstep (se 2 (by rfl) ⟨956832, by rfl⟩ : syracuseStep 2551553 = 1913665) B1913665
theorem B1699587 : Blo 1699550 1699587 := bstep (se 1 (by rfl) ⟨1274690, by rfl⟩ : syracuseStep 1699587 = 2549381) B2549381
theorem B2297603 : Blo 1699550 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B1699603 : Blo 1699550 1699603 := bstep (se 1 (by rfl) ⟨1274702, by rfl⟩ : syracuseStep 1699603 = 2549405) B2549405
theorem B2551571 : Blo 1699550 2551571 := bstep (se 1 (by rfl) ⟨1913678, by rfl⟩ : syracuseStep 2551571 = 3827357) B3827357
theorem B1699619 : Blo 1699550 1699619 := bstep (se 1 (by rfl) ⟨1274714, by rfl⟩ : syracuseStep 1699619 = 2549429) B2549429
theorem B2551601 : Blo 1699550 2551601 := bstep (se 2 (by rfl) ⟨956850, by rfl⟩ : syracuseStep 2551601 = 1913701) B1913701
theorem B1699635 : Blo 1699550 1699635 := bstep (se 1 (by rfl) ⟨1274726, by rfl⟩ : syracuseStep 1699635 = 2549453) B2549453
theorem B1699651 : Blo 1699550 1699651 := bstep (se 1 (by rfl) ⟨1274738, by rfl⟩ : syracuseStep 1699651 = 2549477) B2549477
theorem B2551619 : Blo 1699550 2551619 := bstep (se 1 (by rfl) ⟨1913714, by rfl⟩ : syracuseStep 2551619 = 3827429) B3827429
theorem B4845379 : Blo 1699550 4845379 := bstep (se 1 (by rfl) ⟨3634034, by rfl⟩ : syracuseStep 4845379 = 7268069) B7268069
theorem B9686861 : Blo 1699550 9686861 := bstep (se 3 (by rfl) ⟨1816286, by rfl⟩ : syracuseStep 9686861 = 3632573) B3632573
theorem B1699667 : Blo 1699550 1699667 := bstep (se 1 (by rfl) ⟨1274750, by rfl⟩ : syracuseStep 1699667 = 2549501) B2549501
theorem B2723681 : Blo 1699550 2723681 := bstep (se 2 (by rfl) ⟨1021380, by rfl⟩ : syracuseStep 2723681 = 2042761) B2042761
theorem B1699683 : Blo 1699550 1699683 := bstep (se 1 (by rfl) ⟨1274762, by rfl⟩ : syracuseStep 1699683 = 2549525) B2549525
theorem B8843107 : Blo 1699550 8843107 := bstep (se 1 (by rfl) ⟨6632330, by rfl⟩ : syracuseStep 8843107 = 13264661) B13264661
theorem B1912675 : Blo 1699550 1912675 := bstep (se 1 (by rfl) ⟨1434506, by rfl⟩ : syracuseStep 1912675 = 2869013) B2869013
theorem B2551649 : Blo 1699550 2551649 := bstep (se 2 (by rfl) ⟨956868, by rfl⟩ : syracuseStep 2551649 = 1913737) B1913737
theorem B2871139 : Blo 1699550 2871139 := bstep (se 1 (by rfl) ⟨2153354, by rfl⟩ : syracuseStep 2871139 = 4306709) B4306709
theorem B1699699 : Blo 1699550 1699699 := bstep (se 1 (by rfl) ⟨1274774, by rfl⟩ : syracuseStep 1699699 = 2549549) B2549549
theorem B2551667 : Blo 1699550 2551667 := bstep (se 1 (by rfl) ⟨1913750, by rfl⟩ : syracuseStep 2551667 = 3827501) B3827501
theorem B1699715 : Blo 1699550 1699715 := bstep (se 1 (by rfl) ⟨1274786, by rfl⟩ : syracuseStep 1699715 = 2549573) B2549573
theorem B4304785 : Blo 1699550 4304785 := bstep (se 2 (by rfl) ⟨1614294, by rfl⟩ : syracuseStep 4304785 = 3228589) B3228589
theorem B1699731 : Blo 1699550 1699731 := bstep (se 1 (by rfl) ⟨1274798, by rfl⟩ : syracuseStep 1699731 = 2549597) B2549597
theorem B2551697 : Blo 1699550 2551697 := bstep (se 2 (by rfl) ⟨956886, by rfl⟩ : syracuseStep 2551697 = 1913773) B1913773
theorem B1699747 : Blo 1699550 1699747 := bstep (se 1 (by rfl) ⟨1274810, by rfl⟩ : syracuseStep 1699747 = 2549621) B2549621
theorem B2551715 : Blo 1699550 2551715 := bstep (se 1 (by rfl) ⟨1913786, by rfl⟩ : syracuseStep 2551715 = 3827573) B3827573
theorem B5738417 : Blo 1699550 5738417 := bstep (se 2 (by rfl) ⟨2151906, by rfl⟩ : syracuseStep 5738417 = 4303813) B4303813
theorem B1699763 : Blo 1699550 1699763 := bstep (se 1 (by rfl) ⟨1274822, by rfl⟩ : syracuseStep 1699763 = 2549645) B2549645
theorem B2551745 : Blo 1699550 2551745 := bstep (se 2 (by rfl) ⟨956904, by rfl⟩ : syracuseStep 2551745 = 1913809) B1913809
theorem B1699779 : Blo 1699550 1699779 := bstep (se 1 (by rfl) ⟨1274834, by rfl⟩ : syracuseStep 1699779 = 2549669) B2549669
theorem B1699795 : Blo 1699550 1699795 := bstep (se 1 (by rfl) ⟨1274846, by rfl⟩ : syracuseStep 1699795 = 2549693) B2549693
theorem B2551763 : Blo 1699550 2551763 := bstep (se 1 (by rfl) ⟨1913822, by rfl⟩ : syracuseStep 2551763 = 3827645) B3827645
theorem B26521571 : Blo 1699550 26521571 := bstep (se 1 (by rfl) ⟨19891178, by rfl⟩ : syracuseStep 26521571 = 39782357) B39782357
theorem B1699811 : Blo 1699550 1699811 := bstep (se 1 (by rfl) ⟨1274858, by rfl⟩ : syracuseStep 1699811 = 2549717) B2549717
theorem B14528483 : Blo 1699550 14528483 := bstep (se 1 (by rfl) ⟨10896362, by rfl⟩ : syracuseStep 14528483 = 21792725) B21792725
theorem B2551793 : Blo 1699550 2551793 := bstep (se 2 (by rfl) ⟨956922, by rfl⟩ : syracuseStep 2551793 = 1913845) B1913845
theorem B2871281 : Blo 1699550 2871281 := bstep (se 2 (by rfl) ⟨1076730, by rfl⟩ : syracuseStep 2871281 = 2153461) B2153461
theorem B1699827 : Blo 1699550 1699827 := bstep (se 1 (by rfl) ⟨1274870, by rfl⟩ : syracuseStep 1699827 = 2549741) B2549741
theorem B1912819 : Blo 1699550 1912819 := bstep (se 1 (by rfl) ⟨1434614, by rfl⟩ : syracuseStep 1912819 = 2869229) B2869229
theorem B1699843 : Blo 1699550 1699843 := bstep (se 1 (by rfl) ⟨1274882, by rfl⟩ : syracuseStep 1699843 = 2549765) B2549765
theorem B2551811 : Blo 1699550 2551811 := bstep (se 1 (by rfl) ⟨1913858, by rfl⟩ : syracuseStep 2551811 = 3827717) B3827717
theorem B10899461 : Blo 1699550 10899461 := bstep (se 4 (by rfl) ⟨1021824, by rfl⟩ : syracuseStep 10899461 = 2043649) B2043649
theorem B1699859 : Blo 1699550 1699859 := bstep (se 1 (by rfl) ⟨1274894, by rfl⟩ : syracuseStep 1699859 = 2549789) B2549789
theorem B46542869 : Blo 1699550 46542869 := bstep (se 6 (by rfl) ⟨1090848, by rfl⟩ : syracuseStep 46542869 = 2181697) B2181697
theorem B2551841 : Blo 1699550 2551841 := bstep (se 2 (by rfl) ⟨956940, by rfl⟩ : syracuseStep 2551841 = 1913881) B1913881
theorem B1699875 : Blo 1699550 1699875 := bstep (se 1 (by rfl) ⟨1274906, by rfl⟩ : syracuseStep 1699875 = 2549813) B2549813
theorem B7262243 : Blo 1699550 7262243 := bstep (se 1 (by rfl) ⟨5446682, by rfl⟩ : syracuseStep 7262243 = 10893365) B10893365
theorem B1699891 : Blo 1699550 1699891 := bstep (se 1 (by rfl) ⟨1274918, by rfl⟩ : syracuseStep 1699891 = 2549837) B2549837
theorem B2551859 : Blo 1699550 2551859 := bstep (se 1 (by rfl) ⟨1913894, by rfl⟩ : syracuseStep 2551859 = 3827789) B3827789
theorem B2723905 : Blo 1699550 2723905 := bstep (se 2 (by rfl) ⟨1021464, by rfl⟩ : syracuseStep 2723905 = 2042929) B2042929
theorem B1699907 : Blo 1699550 1699907 := bstep (se 1 (by rfl) ⟨1274930, by rfl⟩ : syracuseStep 1699907 = 2549861) B2549861
theorem B2551889 : Blo 1699550 2551889 := bstep (se 2 (by rfl) ⟨956958, by rfl⟩ : syracuseStep 2551889 = 1913917) B1913917
theorem B1699923 : Blo 1699550 1699923 := bstep (se 1 (by rfl) ⟨1274942, by rfl⟩ : syracuseStep 1699923 = 2549885) B2549885
theorem B1699939 : Blo 1699550 1699939 := bstep (se 1 (by rfl) ⟨1274954, by rfl⟩ : syracuseStep 1699939 = 2549909) B2549909
theorem B2551907 : Blo 1699550 2551907 := bstep (se 1 (by rfl) ⟨1913930, by rfl⟩ : syracuseStep 2551907 = 3827861) B3827861
theorem B1699955 : Blo 1699550 1699955 := bstep (se 1 (by rfl) ⟨1274966, by rfl⟩ : syracuseStep 1699955 = 2549933) B2549933
theorem B2723969 : Blo 1699550 2723969 := bstep (se 2 (by rfl) ⟨1021488, by rfl⟩ : syracuseStep 2723969 = 2042977) B2042977
theorem B2551937 : Blo 1699550 2551937 := bstep (se 2 (by rfl) ⟨956976, by rfl⟩ : syracuseStep 2551937 = 1913953) B1913953
theorem B1699971 : Blo 1699550 1699971 := bstep (se 1 (by rfl) ⟨1274978, by rfl⟩ : syracuseStep 1699971 = 2549957) B2549957
theorem B2420867 : Blo 1699550 2420867 := bstep (se 1 (by rfl) ⟨1815650, by rfl⟩ : syracuseStep 2420867 = 3631301) B3631301
theorem B1912963 : Blo 1699550 1912963 := bstep (se 1 (by rfl) ⟨1434722, by rfl⟩ : syracuseStep 1912963 = 2869445) B2869445
theorem B5173379 : Blo 1699550 5173379 := bstep (se 1 (by rfl) ⟨3880034, by rfl⟩ : syracuseStep 5173379 = 7760069) B7760069
theorem B6459533 : Blo 1699550 6459533 := bstep (se 3 (by rfl) ⟨1211162, by rfl⟩ : syracuseStep 6459533 = 2422325) B2422325
theorem B1699987 : Blo 1699550 1699987 := bstep (se 1 (by rfl) ⟨1274990, by rfl⟩ : syracuseStep 1699987 = 2549981) B2549981
theorem B2551955 : Blo 1699550 2551955 := bstep (se 1 (by rfl) ⟨1913966, by rfl⟩ : syracuseStep 2551955 = 3827933) B3827933
theorem B1700003 : Blo 1699550 1700003 := bstep (se 1 (by rfl) ⟨1275002, by rfl⟩ : syracuseStep 1700003 = 2550005) B2550005
theorem B4305059 : Blo 1699550 4305059 := bstep (se 1 (by rfl) ⟨3228794, by rfl⟩ : syracuseStep 4305059 = 6457589) B6457589
theorem B2551985 : Blo 1699550 2551985 := bstep (se 2 (by rfl) ⟨956994, by rfl⟩ : syracuseStep 2551985 = 1913989) B1913989
theorem B1700019 : Blo 1699550 1700019 := bstep (se 1 (by rfl) ⟨1275014, by rfl⟩ : syracuseStep 1700019 = 2550029) B2550029
theorem B1700035 : Blo 1699550 1700035 := bstep (se 1 (by rfl) ⟨1275026, by rfl⟩ : syracuseStep 1700035 = 2550053) B2550053
theorem B2552003 : Blo 1699550 2552003 := bstep (se 1 (by rfl) ⟨1914002, by rfl⟩ : syracuseStep 2552003 = 3828005) B3828005
theorem B1700051 : Blo 1699550 1700051 := bstep (se 1 (by rfl) ⟨1275038, by rfl⟩ : syracuseStep 1700051 = 2550077) B2550077
theorem B2552033 : Blo 1699550 2552033 := bstep (se 2 (by rfl) ⟨957012, by rfl⟩ : syracuseStep 2552033 = 1914025) B1914025
theorem B1700067 : Blo 1699550 1700067 := bstep (se 1 (by rfl) ⟨1275050, by rfl⟩ : syracuseStep 1700067 = 2550101) B2550101
theorem B1700083 : Blo 1699550 1700083 := bstep (se 1 (by rfl) ⟨1275062, by rfl⟩ : syracuseStep 1700083 = 2550125) B2550125
theorem B2552051 : Blo 1699550 2552051 := bstep (se 1 (by rfl) ⟨1914038, by rfl⟩ : syracuseStep 2552051 = 3828077) B3828077
theorem B2724097 : Blo 1699550 2724097 := bstep (se 2 (by rfl) ⟨1021536, by rfl⟩ : syracuseStep 2724097 = 2043073) B2043073
theorem B1700099 : Blo 1699550 1700099 := bstep (se 1 (by rfl) ⟨1275074, by rfl⟩ : syracuseStep 1700099 = 2550149) B2550149
theorem B2552081 : Blo 1699550 2552081 := bstep (se 2 (by rfl) ⟨957030, by rfl⟩ : syracuseStep 2552081 = 1914061) B1914061
theorem B1700115 : Blo 1699550 1700115 := bstep (se 1 (by rfl) ⟨1275086, by rfl⟩ : syracuseStep 1700115 = 2550173) B2550173
theorem B1913107 : Blo 1699550 1913107 := bstep (se 1 (by rfl) ⟨1434830, by rfl⟩ : syracuseStep 1913107 = 2869661) B2869661
theorem B1700131 : Blo 1699550 1700131 := bstep (se 1 (by rfl) ⟨1275098, by rfl⟩ : syracuseStep 1700131 = 2550197) B2550197
theorem B2552099 : Blo 1699550 2552099 := bstep (se 1 (by rfl) ⟨1914074, by rfl⟩ : syracuseStep 2552099 = 3828149) B3828149
theorem B1700147 : Blo 1699550 1700147 := bstep (se 1 (by rfl) ⟨1275110, by rfl⟩ : syracuseStep 1700147 = 2550221) B2550221
theorem B2552129 : Blo 1699550 2552129 := bstep (se 2 (by rfl) ⟨957048, by rfl⟩ : syracuseStep 2552129 = 1914097) B1914097
theorem B1700163 : Blo 1699550 1700163 := bstep (se 1 (by rfl) ⟨1275122, by rfl⟩ : syracuseStep 1700163 = 2550245) B2550245
theorem B1700179 : Blo 1699550 1700179 := bstep (se 1 (by rfl) ⟨1275134, by rfl⟩ : syracuseStep 1700179 = 2550269) B2550269
theorem B2552147 : Blo 1699550 2552147 := bstep (se 1 (by rfl) ⟨1914110, by rfl⟩ : syracuseStep 2552147 = 3828221) B3828221
theorem B1700195 : Blo 1699550 1700195 := bstep (se 1 (by rfl) ⟨1275146, by rfl⟩ : syracuseStep 1700195 = 2550293) B2550293
theorem B4305251 : Blo 1699550 4305251 := bstep (se 1 (by rfl) ⟨3228938, by rfl⟩ : syracuseStep 4305251 = 6457877) B6457877
theorem B2552177 : Blo 1699550 2552177 := bstep (se 2 (by rfl) ⟨957066, by rfl⟩ : syracuseStep 2552177 = 1914133) B1914133
theorem B1700211 : Blo 1699550 1700211 := bstep (se 1 (by rfl) ⟨1275158, by rfl⟩ : syracuseStep 1700211 = 2550317) B2550317
theorem B1700227 : Blo 1699550 1700227 := bstep (se 1 (by rfl) ⟨1275170, by rfl⟩ : syracuseStep 1700227 = 2550341) B2550341
theorem B2552195 : Blo 1699550 2552195 := bstep (se 1 (by rfl) ⟨1914146, by rfl⟩ : syracuseStep 2552195 = 3828293) B3828293
theorem B1700243 : Blo 1699550 1700243 := bstep (se 1 (by rfl) ⟨1275182, by rfl⟩ : syracuseStep 1700243 = 2550365) B2550365
theorem B2552225 : Blo 1699550 2552225 := bstep (se 2 (by rfl) ⟨957084, by rfl⟩ : syracuseStep 2552225 = 1914169) B1914169
theorem B1700259 : Blo 1699550 1700259 := bstep (se 1 (by rfl) ⟨1275194, by rfl⟩ : syracuseStep 1700259 = 2550389) B2550389
theorem B1913251 : Blo 1699550 1913251 := bstep (se 1 (by rfl) ⟨1434938, by rfl⟩ : syracuseStep 1913251 = 2869877) B2869877
theorem B1700275 : Blo 1699550 1700275 := bstep (se 1 (by rfl) ⟨1275206, by rfl⟩ : syracuseStep 1700275 = 2550413) B2550413
theorem B2552243 : Blo 1699550 2552243 := bstep (se 1 (by rfl) ⟨1914182, by rfl⟩ : syracuseStep 2552243 = 3828365) B3828365
theorem B1700291 : Blo 1699550 1700291 := bstep (se 1 (by rfl) ⟨1275218, by rfl⟩ : syracuseStep 1700291 = 2550437) B2550437
theorem B5738957 : Blo 1699550 5738957 := bstep (se 3 (by rfl) ⟨1076054, by rfl⟩ : syracuseStep 5738957 = 2152109) B2152109
theorem B2552273 : Blo 1699550 2552273 := bstep (se 2 (by rfl) ⟨957102, by rfl⟩ : syracuseStep 2552273 = 1914205) B1914205
theorem B1700307 : Blo 1699550 1700307 := bstep (se 1 (by rfl) ⟨1275230, by rfl⟩ : syracuseStep 1700307 = 2550461) B2550461
theorem B1700323 : Blo 1699550 1700323 := bstep (se 1 (by rfl) ⟨1275242, by rfl⟩ : syracuseStep 1700323 = 2550485) B2550485
theorem B3879395 : Blo 1699550 3879395 := bstep (se 1 (by rfl) ⟨2909546, by rfl⟩ : syracuseStep 3879395 = 5819093) B5819093
theorem B2552291 : Blo 1699550 2552291 := bstep (se 1 (by rfl) ⟨1914218, by rfl⟩ : syracuseStep 2552291 = 3828437) B3828437
theorem B1700339 : Blo 1699550 1700339 := bstep (se 1 (by rfl) ⟨1275254, by rfl⟩ : syracuseStep 1700339 = 2550509) B2550509
theorem B2552321 : Blo 1699550 2552321 := bstep (se 2 (by rfl) ⟨957120, by rfl⟩ : syracuseStep 2552321 = 1914241) B1914241
theorem B1700355 : Blo 1699550 1700355 := bstep (se 1 (by rfl) ⟨1275266, by rfl⟩ : syracuseStep 1700355 = 2550533) B2550533
theorem B5739011 : Blo 1699550 5739011 := bstep (se 1 (by rfl) ⟨4304258, by rfl⟩ : syracuseStep 5739011 = 8608517) B8608517
theorem B1700371 : Blo 1699550 1700371 := bstep (se 1 (by rfl) ⟨1275278, by rfl⟩ : syracuseStep 1700371 = 2550557) B2550557
theorem B1700387 : Blo 1699550 1700387 := bstep (se 1 (by rfl) ⟨1275290, by rfl⟩ : syracuseStep 1700387 = 2550581) B2550581
theorem B1700403 : Blo 1699550 1700403 := bstep (se 1 (by rfl) ⟨1275302, by rfl⟩ : syracuseStep 1700403 = 2550605) B2550605
theorem B1913395 : Blo 1699550 1913395 := bstep (se 1 (by rfl) ⟨1435046, by rfl⟩ : syracuseStep 1913395 = 2870093) B2870093
theorem B4084291 : Blo 1699550 4084291 := bstep (se 1 (by rfl) ⟨3063218, by rfl⟩ : syracuseStep 4084291 = 6126437) B6126437
theorem B1700419 : Blo 1699550 1700419 := bstep (se 1 (by rfl) ⟨1275314, by rfl⟩ : syracuseStep 1700419 = 2550629) B2550629
theorem B10891853 : Blo 1699550 10891853 := bstep (se 3 (by rfl) ⟨2042222, by rfl⟩ : syracuseStep 10891853 = 4084445) B4084445
theorem B1700435 : Blo 1699550 1700435 := bstep (se 1 (by rfl) ⟨1275326, by rfl⟩ : syracuseStep 1700435 = 2550653) B2550653
theorem B1700451 : Blo 1699550 1700451 := bstep (se 1 (by rfl) ⟨1275338, by rfl⟩ : syracuseStep 1700451 = 2550677) B2550677
theorem B10089073 : Blo 1699550 10089073 := bstep (se 2 (by rfl) ⟨3783402, by rfl⟩ : syracuseStep 10089073 = 7566805) B7566805
theorem B58937969 : Blo 1699550 58937969 := bstep (se 2 (by rfl) ⟨22101738, by rfl⟩ : syracuseStep 58937969 = 44203477) B44203477
theorem B1700467 : Blo 1699550 1700467 := bstep (se 1 (by rfl) ⟨1275350, by rfl⟩ : syracuseStep 1700467 = 2550701) B2550701
theorem B1700483 : Blo 1699550 1700483 := bstep (se 1 (by rfl) ⟨1275362, by rfl⟩ : syracuseStep 1700483 = 2550725) B2550725
theorem B1700499 : Blo 1699550 1700499 := bstep (se 1 (by rfl) ⟨1275374, by rfl⟩ : syracuseStep 1700499 = 2550749) B2550749
theorem B1700515 : Blo 1699550 1700515 := bstep (se 1 (by rfl) ⟨1275386, by rfl⟩ : syracuseStep 1700515 = 2550773) B2550773
theorem B1700531 : Blo 1699550 1700531 := bstep (se 1 (by rfl) ⟨1275398, by rfl⟩ : syracuseStep 1700531 = 2550797) B2550797
theorem B1700547 : Blo 1699550 1700547 := bstep (se 1 (by rfl) ⟨1275410, by rfl⟩ : syracuseStep 1700547 = 2550821) B2550821
theorem B1913539 : Blo 1699550 1913539 := bstep (se 1 (by rfl) ⟨1435154, by rfl⟩ : syracuseStep 1913539 = 2870309) B2870309
theorem B1700563 : Blo 1699550 1700563 := bstep (se 1 (by rfl) ⟨1275422, by rfl⟩ : syracuseStep 1700563 = 2550845) B2550845
theorem B33133283 : Blo 1699550 33133283 := bstep (se 1 (by rfl) ⟨24849962, by rfl⟩ : syracuseStep 33133283 = 49699925) B49699925
theorem B1700579 : Blo 1699550 1700579 := bstep (se 1 (by rfl) ⟨1275434, by rfl⟩ : syracuseStep 1700579 = 2550869) B2550869
theorem B1700595 : Blo 1699550 1700595 := bstep (se 1 (by rfl) ⟨1275446, by rfl⟩ : syracuseStep 1700595 = 2550893) B2550893
theorem B2421505 : Blo 1699550 2421505 := bstep (se 2 (by rfl) ⟨908064, by rfl⟩ : syracuseStep 2421505 = 1816129) B1816129
theorem B1700611 : Blo 1699550 1700611 := bstep (se 1 (by rfl) ⟨1275458, by rfl⟩ : syracuseStep 1700611 = 2550917) B2550917
theorem B3633923 : Blo 1699550 3633923 := bstep (se 1 (by rfl) ⟨2725442, by rfl⟩ : syracuseStep 3633923 = 5450885) B5450885
theorem B5739281 : Blo 1699550 5739281 := bstep (se 2 (by rfl) ⟨2152230, by rfl⟩ : syracuseStep 5739281 = 4304461) B4304461
theorem B1700627 : Blo 1699550 1700627 := bstep (se 1 (by rfl) ⟨1275470, by rfl⟩ : syracuseStep 1700627 = 2550941) B2550941
theorem B1700643 : Blo 1699550 1700643 := bstep (se 1 (by rfl) ⟨1275482, by rfl⟩ : syracuseStep 1700643 = 2550965) B2550965
theorem B2298673 : Blo 1699550 2298673 := bstep (se 2 (by rfl) ⟨862002, by rfl⟩ : syracuseStep 2298673 = 1724005) B1724005
theorem B1700659 : Blo 1699550 1700659 := bstep (se 1 (by rfl) ⟨1275494, by rfl⟩ : syracuseStep 1700659 = 2550989) B2550989
theorem B5239619 : Blo 1699550 5239619 := bstep (se 1 (by rfl) ⟨3929714, by rfl⟩ : syracuseStep 5239619 = 7859429) B7859429
theorem B1700675 : Blo 1699550 1700675 := bstep (se 1 (by rfl) ⟨1275506, by rfl⟩ : syracuseStep 1700675 = 2551013) B2551013
theorem B1700691 : Blo 1699550 1700691 := bstep (se 1 (by rfl) ⟨1275518, by rfl⟩ : syracuseStep 1700691 = 2551037) B2551037
theorem B1913683 : Blo 1699550 1913683 := bstep (se 1 (by rfl) ⟨1435262, by rfl⟩ : syracuseStep 1913683 = 2870525) B2870525
theorem B1700707 : Blo 1699550 1700707 := bstep (se 1 (by rfl) ⟨1275530, by rfl⟩ : syracuseStep 1700707 = 2551061) B2551061
theorem B1700723 : Blo 1699550 1700723 := bstep (se 1 (by rfl) ⟨1275542, by rfl⟩ : syracuseStep 1700723 = 2551085) B2551085
theorem B2151299 : Blo 1699550 2151299 := bstep (se 1 (by rfl) ⟨1613474, by rfl⟩ : syracuseStep 2151299 = 3226949) B3226949
theorem B1700739 : Blo 1699550 1700739 := bstep (se 1 (by rfl) ⟨1275554, by rfl⟩ : syracuseStep 1700739 = 2551109) B2551109
theorem B1700755 : Blo 1699550 1700755 := bstep (se 1 (by rfl) ⟨1275566, by rfl⟩ : syracuseStep 1700755 = 2551133) B2551133
theorem B1700771 : Blo 1699550 1700771 := bstep (se 1 (by rfl) ⟨1275578, by rfl⟩ : syracuseStep 1700771 = 2551157) B2551157
theorem B6460337 : Blo 1699550 6460337 := bstep (se 2 (by rfl) ⟨2422626, by rfl⟩ : syracuseStep 6460337 = 4845253) B4845253
theorem B1700787 : Blo 1699550 1700787 := bstep (se 1 (by rfl) ⟨1275590, by rfl⟩ : syracuseStep 1700787 = 2551181) B2551181
theorem B1700803 : Blo 1699550 1700803 := bstep (se 1 (by rfl) ⟨1275602, by rfl⟩ : syracuseStep 1700803 = 2551205) B2551205
theorem B1700819 : Blo 1699550 1700819 := bstep (se 1 (by rfl) ⟨1275614, by rfl⟩ : syracuseStep 1700819 = 2551229) B2551229
theorem B1700835 : Blo 1699550 1700835 := bstep (se 1 (by rfl) ⟨1275626, by rfl⟩ : syracuseStep 1700835 = 2551253) B2551253
theorem B1913827 : Blo 1699550 1913827 := bstep (se 1 (by rfl) ⟨1435370, by rfl⟩ : syracuseStep 1913827 = 2870741) B2870741
theorem B1700851 : Blo 1699550 1700851 := bstep (se 1 (by rfl) ⟨1275638, by rfl⟩ : syracuseStep 1700851 = 2551277) B2551277
theorem B1700867 : Blo 1699550 1700867 := bstep (se 1 (by rfl) ⟨1275650, by rfl⟩ : syracuseStep 1700867 = 2551301) B2551301
theorem B1700883 : Blo 1699550 1700883 := bstep (se 1 (by rfl) ⟨1275662, by rfl⟩ : syracuseStep 1700883 = 2551325) B2551325
theorem B1700899 : Blo 1699550 1700899 := bstep (se 1 (by rfl) ⟨1275674, by rfl⟩ : syracuseStep 1700899 = 2551349) B2551349
theorem B1700915 : Blo 1699550 1700915 := bstep (se 1 (by rfl) ⟨1275686, by rfl⟩ : syracuseStep 1700915 = 2551373) B2551373
theorem B23909429 : Blo 1699550 23909429 := bstep (se 5 (by rfl) ⟨1120754, by rfl⟩ : syracuseStep 23909429 = 2241509) B2241509
theorem B1700931 : Blo 1699550 1700931 := bstep (se 1 (by rfl) ⟨1275698, by rfl⟩ : syracuseStep 1700931 = 2551397) B2551397
theorem B2421841 : Blo 1699550 2421841 := bstep (se 2 (by rfl) ⟨908190, by rfl⟩ : syracuseStep 2421841 = 1816381) B1816381
theorem B1700947 : Blo 1699550 1700947 := bstep (se 1 (by rfl) ⟨1275710, by rfl⟩ : syracuseStep 1700947 = 2551421) B2551421
theorem B1700963 : Blo 1699550 1700963 := bstep (se 1 (by rfl) ⟨1275722, by rfl⟩ : syracuseStep 1700963 = 2551445) B2551445
theorem B1700979 : Blo 1699550 1700979 := bstep (se 1 (by rfl) ⟨1275734, by rfl⟩ : syracuseStep 1700979 = 2551469) B2551469
theorem B1913971 : Blo 1699550 1913971 := bstep (se 1 (by rfl) ⟨1435478, by rfl⟩ : syracuseStep 1913971 = 2870957) B2870957
theorem B1700995 : Blo 1699550 1700995 := bstep (se 1 (by rfl) ⟨1275746, by rfl⟩ : syracuseStep 1700995 = 2551493) B2551493
theorem B9196685 : Blo 1699550 9196685 := bstep (se 3 (by rfl) ⟨1724378, by rfl⟩ : syracuseStep 9196685 = 3448757) B3448757
theorem B1701011 : Blo 1699550 1701011 := bstep (se 1 (by rfl) ⟨1275758, by rfl⟩ : syracuseStep 1701011 = 2551517) B2551517
theorem B1701027 : Blo 1699550 1701027 := bstep (se 1 (by rfl) ⟨1275770, by rfl⟩ : syracuseStep 1701027 = 2551541) B2551541
theorem B8606897 : Blo 1699550 8606897 := bstep (se 2 (by rfl) ⟨3227586, by rfl⟩ : syracuseStep 8606897 = 6455173) B6455173
theorem B1701043 : Blo 1699550 1701043 := bstep (se 1 (by rfl) ⟨1275782, by rfl⟩ : syracuseStep 1701043 = 2551565) B2551565
theorem B1701059 : Blo 1699550 1701059 := bstep (se 1 (by rfl) ⟨1275794, by rfl⟩ : syracuseStep 1701059 = 2551589) B2551589
theorem B1701075 : Blo 1699550 1701075 := bstep (se 1 (by rfl) ⟨1275806, by rfl⟩ : syracuseStep 1701075 = 2551613) B2551613
theorem B1701091 : Blo 1699550 1701091 := bstep (se 1 (by rfl) ⟨1275818, by rfl⟩ : syracuseStep 1701091 = 2551637) B2551637
theorem B1701107 : Blo 1699550 1701107 := bstep (se 1 (by rfl) ⟨1275830, by rfl⟩ : syracuseStep 1701107 = 2551661) B2551661
theorem B1701123 : Blo 1699550 1701123 := bstep (se 1 (by rfl) ⟨1275842, by rfl⟩ : syracuseStep 1701123 = 2551685) B2551685
theorem B1914115 : Blo 1699550 1914115 := bstep (se 1 (by rfl) ⟨1435586, by rfl⟩ : syracuseStep 1914115 = 2871173) B2871173
theorem B4306193 : Blo 1699550 4306193 := bstep (se 2 (by rfl) ⟨1614822, by rfl⟩ : syracuseStep 4306193 = 3229645) B3229645
theorem B1701139 : Blo 1699550 1701139 := bstep (se 1 (by rfl) ⟨1275854, by rfl⟩ : syracuseStep 1701139 = 2551709) B2551709
theorem B1701155 : Blo 1699550 1701155 := bstep (se 1 (by rfl) ⟨1275866, by rfl⟩ : syracuseStep 1701155 = 2551733) B2551733
theorem B5739821 : Blo 1699550 5739821 := bstep (se 3 (by rfl) ⟨1076216, by rfl⟩ : syracuseStep 5739821 = 2152433) B2152433
theorem B1701171 : Blo 1699550 1701171 := bstep (se 1 (by rfl) ⟨1275878, by rfl⟩ : syracuseStep 1701171 = 2551757) B2551757
theorem B1701187 : Blo 1699550 1701187 := bstep (se 1 (by rfl) ⟨1275890, by rfl⟩ : syracuseStep 1701187 = 2551781) B2551781
theorem B4306243 : Blo 1699550 4306243 := bstep (se 1 (by rfl) ⟨3229682, by rfl⟩ : syracuseStep 4306243 = 6459365) B6459365
theorem B1701203 : Blo 1699550 1701203 := bstep (se 1 (by rfl) ⟨1275902, by rfl⟩ : syracuseStep 1701203 = 2551805) B2551805
theorem B5739875 : Blo 1699550 5739875 := bstep (se 1 (by rfl) ⟨4304906, by rfl⟩ : syracuseStep 5739875 = 8609813) B8609813
theorem B1701219 : Blo 1699550 1701219 := bstep (se 1 (by rfl) ⟨1275914, by rfl⟩ : syracuseStep 1701219 = 2551829) B2551829
theorem B1701235 : Blo 1699550 1701235 := bstep (se 1 (by rfl) ⟨1275926, by rfl⟩ : syracuseStep 1701235 = 2551853) B2551853
theorem B1701251 : Blo 1699550 1701251 := bstep (se 1 (by rfl) ⟨1275938, by rfl⟩ : syracuseStep 1701251 = 2551877) B2551877
theorem B1701267 : Blo 1699550 1701267 := bstep (se 1 (by rfl) ⟨1275950, by rfl⟩ : syracuseStep 1701267 = 2551901) B2551901
theorem B1701283 : Blo 1699550 1701283 := bstep (se 1 (by rfl) ⟨1275962, by rfl⟩ : syracuseStep 1701283 = 2551925) B2551925
theorem B1701299 : Blo 1699550 1701299 := bstep (se 1 (by rfl) ⟨1275974, by rfl⟩ : syracuseStep 1701299 = 2551949) B2551949
theorem B1701315 : Blo 1699550 1701315 := bstep (se 1 (by rfl) ⟨1275986, by rfl⟩ : syracuseStep 1701315 = 2551973) B2551973
theorem B4306385 : Blo 1699550 4306385 := bstep (se 2 (by rfl) ⟨1614894, by rfl⟩ : syracuseStep 4306385 = 3229789) B3229789
theorem B1701331 : Blo 1699550 1701331 := bstep (se 1 (by rfl) ⟨1275998, by rfl⟩ : syracuseStep 1701331 = 2551997) B2551997
theorem B7362019 : Blo 1699550 7362019 := bstep (se 1 (by rfl) ⟨5521514, by rfl⟩ : syracuseStep 7362019 = 11043029) B11043029
theorem B1701347 : Blo 1699550 1701347 := bstep (se 1 (by rfl) ⟨1276010, by rfl⟩ : syracuseStep 1701347 = 2552021) B2552021
theorem B1701363 : Blo 1699550 1701363 := bstep (se 1 (by rfl) ⟨1276022, by rfl⟩ : syracuseStep 1701363 = 2552045) B2552045
theorem B1701379 : Blo 1699550 1701379 := bstep (se 1 (by rfl) ⟨1276034, by rfl⟩ : syracuseStep 1701379 = 2552069) B2552069
theorem B5977613 : Blo 1699550 5977613 := bstep (se 3 (by rfl) ⟨1120802, by rfl⟩ : syracuseStep 5977613 = 2241605) B2241605
theorem B1701395 : Blo 1699550 1701395 := bstep (se 1 (by rfl) ⟨1276046, by rfl⟩ : syracuseStep 1701395 = 2552093) B2552093
theorem B1701411 : Blo 1699550 1701411 := bstep (se 1 (by rfl) ⟨1276058, by rfl⟩ : syracuseStep 1701411 = 2552117) B2552117
theorem B1701427 : Blo 1699550 1701427 := bstep (se 1 (by rfl) ⟨1276070, by rfl⟩ : syracuseStep 1701427 = 2552141) B2552141
theorem B2455105 : Blo 1699550 2455105 := bstep (se 2 (by rfl) ⟨920664, by rfl⟩ : syracuseStep 2455105 = 1841329) B1841329
theorem B2152003 : Blo 1699550 2152003 := bstep (se 1 (by rfl) ⟨1614002, by rfl⟩ : syracuseStep 2152003 = 3228005) B3228005
theorem B1701443 : Blo 1699550 1701443 := bstep (se 1 (by rfl) ⟨1276082, by rfl⟩ : syracuseStep 1701443 = 2552165) B2552165
theorem B11638349 : Blo 1699550 11638349 := bstep (se 3 (by rfl) ⟨2182190, by rfl⟩ : syracuseStep 11638349 = 4364381) B4364381
theorem B1701459 : Blo 1699550 1701459 := bstep (se 1 (by rfl) ⟨1276094, by rfl⟩ : syracuseStep 1701459 = 2552189) B2552189
theorem B1701475 : Blo 1699550 1701475 := bstep (se 1 (by rfl) ⟨1276106, by rfl⟩ : syracuseStep 1701475 = 2552213) B2552213
theorem B5740145 : Blo 1699550 5740145 := bstep (se 2 (by rfl) ⟨2152554, by rfl⟩ : syracuseStep 5740145 = 4305109) B4305109
theorem B1701491 : Blo 1699550 1701491 := bstep (se 1 (by rfl) ⟨1276118, by rfl⟩ : syracuseStep 1701491 = 2552237) B2552237
theorem B1701507 : Blo 1699550 1701507 := bstep (se 1 (by rfl) ⟨1276130, by rfl⟩ : syracuseStep 1701507 = 2552261) B2552261
theorem B1701523 : Blo 1699550 1701523 := bstep (se 1 (by rfl) ⟨1276142, by rfl⟩ : syracuseStep 1701523 = 2552285) B2552285
theorem B2422433 : Blo 1699550 2422433 := bstep (se 2 (by rfl) ⟨908412, by rfl⟩ : syracuseStep 2422433 = 1816825) B1816825
theorem B2152099 : Blo 1699550 2152099 := bstep (se 1 (by rfl) ⟨1614074, by rfl⟩ : syracuseStep 2152099 = 3228149) B3228149
theorem B1701539 : Blo 1699550 1701539 := bstep (se 1 (by rfl) ⟨1276154, by rfl⟩ : syracuseStep 1701539 = 2552309) B2552309
theorem B1939123 : Blo 1699550 1939123 := bstep (se 1 (by rfl) ⟨1454342, by rfl⟩ : syracuseStep 1939123 = 2908685) B2908685
theorem B12916421 : Blo 1699550 12916421 := bstep (se 4 (by rfl) ⟨1210914, by rfl⟩ : syracuseStep 12916421 = 2421829) B2421829
theorem B4978417 : Blo 1699550 4978417 := bstep (se 2 (by rfl) ⟨1866906, by rfl⟩ : syracuseStep 4978417 = 3733813) B3733813
theorem B1816355 : Blo 1699550 1816355 := bstep (se 1 (by rfl) ⟨1362266, by rfl⟩ : syracuseStep 1816355 = 2724533) B2724533
theorem B5445425 : Blo 1699550 5445425 := bstep (se 2 (by rfl) ⟨2042034, by rfl⟩ : syracuseStep 5445425 = 4084069) B4084069
theorem B19912547 : Blo 1699550 19912547 := bstep (se 1 (by rfl) ⟨14934410, by rfl⟩ : syracuseStep 19912547 = 29868821) B29868821
theorem B19363697 : Blo 1699550 19363697 := bstep (se 2 (by rfl) ⟨7261386, by rfl⟩ : syracuseStep 19363697 = 14522773) B14522773
theorem B10901411 : Blo 1699550 10901411 := bstep (se 1 (by rfl) ⟨8176058, by rfl⟩ : syracuseStep 10901411 = 16352117) B16352117
theorem B20674531 : Blo 1699550 20674531 := bstep (se 1 (by rfl) ⟨15505898, by rfl⟩ : syracuseStep 20674531 = 31011797) B31011797
theorem B6633521 : Blo 1699550 6633521 := bstep (se 2 (by rfl) ⟨2487570, by rfl⟩ : syracuseStep 6633521 = 4975141) B4975141
theorem B2586737 : Blo 1699550 2586737 := bstep (se 2 (by rfl) ⟨970026, by rfl⟩ : syracuseStep 2586737 = 1940053) B1940053
theorem B9681029 : Blo 1699550 9681029 := bstep (se 4 (by rfl) ⟨907596, by rfl⟩ : syracuseStep 9681029 = 1815193) B1815193
theorem B5740685 : Blo 1699550 5740685 := bstep (se 3 (by rfl) ⟨1076378, by rfl⟩ : syracuseStep 5740685 = 2152757) B2152757
theorem B2152595 : Blo 1699550 2152595 := bstep (se 1 (by rfl) ⟨1614446, by rfl⟩ : syracuseStep 2152595 = 3228893) B3228893
theorem B5740739 : Blo 1699550 5740739 := bstep (se 1 (by rfl) ⟨4305554, by rfl⟩ : syracuseStep 5740739 = 8611109) B8611109
theorem B4839821 : Blo 1699550 4839821 := bstep (se 3 (by rfl) ⟨907466, by rfl⟩ : syracuseStep 4839821 = 1814933) B1814933
theorem B3824081 : Blo 1699550 3824081 := bstep (se 2 (by rfl) ⟨1434030, by rfl⟩ : syracuseStep 3824081 = 2868061) B2868061
theorem B5741009 : Blo 1699550 5741009 := bstep (se 2 (by rfl) ⟨2152878, by rfl⟩ : syracuseStep 5741009 = 4305757) B4305757
theorem B3824099 : Blo 1699550 3824099 := bstep (se 1 (by rfl) ⟨2868074, by rfl⟩ : syracuseStep 3824099 = 5736149) B5736149
theorem B4840013 : Blo 1699550 4840013 := bstep (se 3 (by rfl) ⟨907502, by rfl⟩ : syracuseStep 4840013 = 1815005) B1815005
theorem B8608355 : Blo 1699550 8608355 := bstep (se 1 (by rfl) ⟨6456266, by rfl⟩ : syracuseStep 8608355 = 12912533) B12912533
theorem B9689777 : Blo 1699550 9689777 := bstep (se 2 (by rfl) ⟨3633666, by rfl⟩ : syracuseStep 9689777 = 7267333) B7267333
theorem B5446349 : Blo 1699550 5446349 := bstep (se 3 (by rfl) ⟨1021190, by rfl⟩ : syracuseStep 5446349 = 2042381) B2042381
theorem B3824369 : Blo 1699550 3824369 := bstep (se 2 (by rfl) ⟨1434138, by rfl⟩ : syracuseStep 3824369 = 2868277) B2868277
theorem B3824387 : Blo 1699550 3824387 := bstep (se 1 (by rfl) ⟨2868290, by rfl⟩ : syracuseStep 3824387 = 5736581) B5736581
theorem B9681713 : Blo 1699550 9681713 := bstep (se 2 (by rfl) ⟨3630642, by rfl⟩ : syracuseStep 9681713 = 7261285) B7261285
theorem B2153299 : Blo 1699550 2153299 := bstep (se 1 (by rfl) ⟨1614974, by rfl⟩ : syracuseStep 2153299 = 3229949) B3229949
theorem B5446541 : Blo 1699550 5446541 := bstep (se 3 (by rfl) ⟨1021226, by rfl⟩ : syracuseStep 5446541 = 2042453) B2042453
theorem B2153395 : Blo 1699550 2153395 := bstep (se 1 (by rfl) ⟨1615046, by rfl⟩ : syracuseStep 2153395 = 3230093) B3230093
theorem B5741549 : Blo 1699550 5741549 := bstep (se 3 (by rfl) ⟨1076540, by rfl⟩ : syracuseStep 5741549 = 2153081) B2153081
theorem B3824657 : Blo 1699550 3824657 := bstep (se 2 (by rfl) ⟨1434246, by rfl⟩ : syracuseStep 3824657 = 2868493) B2868493
theorem B3824675 : Blo 1699550 3824675 := bstep (se 1 (by rfl) ⟨2868506, by rfl⟩ : syracuseStep 3824675 = 5737013) B5737013
theorem B5741603 : Blo 1699550 5741603 := bstep (se 1 (by rfl) ⟨4306202, by rfl⟩ : syracuseStep 5741603 = 8612405) B8612405
theorem B2948147 : Blo 1699550 2948147 := bstep (se 1 (by rfl) ⟨2211110, by rfl⟩ : syracuseStep 2948147 = 4422221) B4422221
theorem B3226691 : Blo 1699550 3226691 := bstep (se 1 (by rfl) ⟨2420018, by rfl⟩ : syracuseStep 3226691 = 4840037) B4840037
theorem B13090061 : Blo 1699550 13090061 := bstep (se 3 (by rfl) ⟨2454386, by rfl⟩ : syracuseStep 13090061 = 4908773) B4908773
theorem B3824945 : Blo 1699550 3824945 := bstep (se 2 (by rfl) ⟨1434354, by rfl⟩ : syracuseStep 3824945 = 2868709) B2868709
theorem B5741873 : Blo 1699550 5741873 := bstep (se 2 (by rfl) ⟨2153202, by rfl⟩ : syracuseStep 5741873 = 4306405) B4306405
theorem B3824963 : Blo 1699550 3824963 := bstep (se 1 (by rfl) ⟨2868722, by rfl⟩ : syracuseStep 3824963 = 5737445) B5737445
theorem B3226979 : Blo 1699550 3226979 := bstep (se 1 (by rfl) ⟨2420234, by rfl⟩ : syracuseStep 3226979 = 4840469) B4840469
theorem B8609165 : Blo 1699550 8609165 := bstep (se 3 (by rfl) ⟨1614218, by rfl⟩ : syracuseStep 8609165 = 3228437) B3228437
theorem B2760083 : Blo 1699550 2760083 := bstep (se 1 (by rfl) ⟨2070062, by rfl⟩ : syracuseStep 2760083 = 4140125) B4140125
theorem B6897059 : Blo 1699550 6897059 := bstep (se 1 (by rfl) ⟨5172794, by rfl⟩ : syracuseStep 6897059 = 10345589) B10345589
theorem B4841005 : Blo 1699550 4841005 := bstep (se 3 (by rfl) ⟨907688, by rfl⟩ : syracuseStep 4841005 = 1815377) B1815377
theorem B3825233 : Blo 1699550 3825233 := bstep (se 2 (by rfl) ⟨1434462, by rfl⟩ : syracuseStep 3825233 = 2868925) B2868925
theorem B3825251 : Blo 1699550 3825251 := bstep (se 1 (by rfl) ⟨2868938, by rfl⟩ : syracuseStep 3825251 = 5737877) B5737877
theorem B7265933 : Blo 1699550 7265933 := bstep (se 3 (by rfl) ⟨1362362, by rfl⟩ : syracuseStep 7265933 = 2724725) B2724725
theorem B2907809 : Blo 1699550 2907809 := bstep (se 2 (by rfl) ⟨1090428, by rfl⟩ : syracuseStep 2907809 = 2180857) B2180857
theorem B10346147 : Blo 1699550 10346147 := bstep (se 1 (by rfl) ⟨7759610, by rfl⟩ : syracuseStep 10346147 = 15519221) B15519221
theorem B6454961 : Blo 1699550 6454961 := bstep (se 2 (by rfl) ⟨2420610, by rfl⟩ : syracuseStep 6454961 = 4841221) B4841221
theorem B8724145 : Blo 1699550 8724145 := bstep (se 2 (by rfl) ⟨3271554, by rfl⟩ : syracuseStep 8724145 = 6543109) B6543109
theorem B8167139 : Blo 1699550 8167139 := bstep (se 1 (by rfl) ⟨6125354, by rfl⟩ : syracuseStep 8167139 = 12250709) B12250709
theorem B5742413 : Blo 1699550 5742413 := bstep (se 3 (by rfl) ⟨1076702, by rfl⟩ : syracuseStep 5742413 = 2153405) B2153405
theorem B3825521 : Blo 1699550 3825521 := bstep (se 2 (by rfl) ⟨1434570, by rfl⟩ : syracuseStep 3825521 = 2869141) B2869141
theorem B3825539 : Blo 1699550 3825539 := bstep (se 1 (by rfl) ⟨2869154, by rfl⟩ : syracuseStep 3825539 = 5738309) B5738309
theorem B5742467 : Blo 1699550 5742467 := bstep (se 1 (by rfl) ⟨4306850, by rfl⟩ : syracuseStep 5742467 = 8613701) B8613701
theorem B10346417 : Blo 1699550 10346417 := bstep (se 2 (by rfl) ⟨3879906, by rfl⟩ : syracuseStep 10346417 = 7759813) B7759813
theorem B3825665 : Blo 1699550 3825665 := bstep (se 2 (by rfl) ⟨1434624, by rfl⟩ : syracuseStep 3825665 = 2869249) B2869249
theorem B29065229 : Blo 1699550 29065229 := bstep (se 3 (by rfl) ⟨5449730, by rfl⟩ : syracuseStep 29065229 = 10899461) B10899461
theorem B4841495 : Blo 1699550 4841495 := bstep (se 1 (by rfl) ⟨3631121, by rfl⟩ : syracuseStep 4841495 = 7262243) B7262243
theorem B6897739 : Blo 1699550 6897739 := bstep (se 1 (by rfl) ⟨5173304, by rfl⟩ : syracuseStep 6897739 = 10346609) B10346609
theorem B3448919 : Blo 1699550 3448919 := bstep (se 1 (by rfl) ⟨2586689, by rfl⟩ : syracuseStep 3448919 = 5173379) B5173379
theorem B63758477 : Blo 1699550 63758477 := bstep (se 3 (by rfl) ⟨11954714, by rfl⟩ : syracuseStep 63758477 = 23909429) B23909429
theorem B6455447 : Blo 1699550 6455447 := bstep (se 1 (by rfl) ⟨4841585, by rfl⟩ : syracuseStep 6455447 = 9683171) B9683171
theorem B3825881 : Blo 1699550 3825881 := bstep (se 2 (by rfl) ⟨1434705, by rfl⟩ : syracuseStep 3825881 = 2869411) B2869411
theorem B6897965 : Blo 1699550 6897965 := bstep (se 3 (by rfl) ⟨1293368, by rfl⟩ : syracuseStep 6897965 = 2586737) B2586737
theorem B3825971 : Blo 1699550 3825971 := bstep (se 1 (by rfl) ⟨2869478, by rfl⟩ : syracuseStep 3825971 = 5738957) B5738957
theorem B3826007 : Blo 1699550 3826007 := bstep (se 1 (by rfl) ⟨2869505, by rfl⟩ : syracuseStep 3826007 = 5739011) B5739011
theorem B6455645 : Blo 1699550 6455645 := bstep (se 3 (by rfl) ⟨1210433, by rfl⟩ : syracuseStep 6455645 = 2420867) B2420867
theorem B14729651 : Blo 1699550 14729651 := bstep (se 1 (by rfl) ⟨11047238, by rfl⟩ : syracuseStep 14729651 = 22094477) B22094477
theorem B6128065 : Blo 1699550 6128065 := bstep (se 2 (by rfl) ⟨2298024, by rfl⟩ : syracuseStep 6128065 = 4596049) B4596049
theorem B3826187 : Blo 1699550 3826187 := bstep (se 1 (by rfl) ⟨2869640, by rfl⟩ : syracuseStep 3826187 = 5739281) B5739281
theorem B6128179 : Blo 1699550 6128179 := bstep (se 1 (by rfl) ⟨4596134, by rfl⟩ : syracuseStep 6128179 = 9192269) B9192269
theorem B3826241 : Blo 1699550 3826241 := bstep (se 2 (by rfl) ⟨1434840, by rfl⟩ : syracuseStep 3826241 = 2869681) B2869681
theorem B6898355 : Blo 1699550 6898355 := bstep (se 1 (by rfl) ⟨5173766, by rfl⟩ : syracuseStep 6898355 = 10347533) B10347533
theorem B3826457 : Blo 1699550 3826457 := bstep (se 2 (by rfl) ⟨1434921, by rfl⟩ : syracuseStep 3826457 = 2869843) B2869843
theorem B13452097 : Blo 1699550 13452097 := bstep (se 2 (by rfl) ⟨5044536, by rfl⟩ : syracuseStep 13452097 = 10089073) B10089073
theorem B3228491 : Blo 1699550 3228491 := bstep (se 1 (by rfl) ⟨2421368, by rfl⟩ : syracuseStep 3228491 = 4842737) B4842737
theorem B3826547 : Blo 1699550 3826547 := bstep (se 1 (by rfl) ⟨2869910, by rfl⟩ : syracuseStep 3826547 = 5739821) B5739821
theorem B7758737 : Blo 1699550 7758737 := bstep (se 2 (by rfl) ⟨2909526, by rfl⟩ : syracuseStep 7758737 = 5819053) B5819053
theorem B3826583 : Blo 1699550 3826583 := bstep (se 1 (by rfl) ⟨2869937, by rfl⟩ : syracuseStep 3826583 = 5739875) B5739875
theorem B7267265 : Blo 1699550 7267265 := bstep (se 2 (by rfl) ⟨2725224, by rfl⟩ : syracuseStep 7267265 = 5450449) B5450449
theorem B3228673 : Blo 1699550 3228673 := bstep (se 2 (by rfl) ⟨1210752, by rfl⟩ : syracuseStep 3228673 = 2421505) B2421505
theorem B7758899 : Blo 1699550 7758899 := bstep (se 1 (by rfl) ⟨5819174, by rfl⟩ : syracuseStep 7758899 = 11638349) B11638349
theorem B3064897 : Blo 1699550 3064897 := bstep (se 2 (by rfl) ⟨1149336, by rfl⟩ : syracuseStep 3064897 = 2298673) B2298673
theorem B25183307 : Blo 1699550 25183307 := bstep (se 1 (by rfl) ⟨18887480, by rfl⟩ : syracuseStep 25183307 = 37774961) B37774961
theorem B3826763 : Blo 1699550 3826763 := bstep (se 1 (by rfl) ⟨2870072, by rfl⟩ : syracuseStep 3826763 = 5740145) B5740145
theorem B2868311 : Blo 1699550 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B3826817 : Blo 1699550 3826817 := bstep (se 2 (by rfl) ⟨1435056, by rfl⟩ : syracuseStep 3826817 = 2870113) B2870113
theorem B8610947 : Blo 1699550 8610947 := bstep (se 1 (by rfl) ⟨6458210, by rfl⟩ : syracuseStep 8610947 = 12916421) B12916421
theorem B3630233 : Blo 1699550 3630233 := bstep (se 2 (by rfl) ⟨1361337, by rfl⟩ : syracuseStep 3630233 = 2722675) B2722675
theorem B2868439 : Blo 1699550 2868439 := bstep (se 1 (by rfl) ⟨2151329, by rfl⟩ : syracuseStep 2868439 = 4302659) B4302659
theorem B7267607 : Blo 1699550 7267607 := bstep (se 1 (by rfl) ⟨5450705, by rfl⟩ : syracuseStep 7267607 = 10901411) B10901411
theorem B3827033 : Blo 1699550 3827033 := bstep (se 2 (by rfl) ⟨1435137, by rfl⟩ : syracuseStep 3827033 = 2870275) B2870275
theorem B3827123 : Blo 1699550 3827123 := bstep (se 1 (by rfl) ⟨2870342, by rfl⟩ : syracuseStep 3827123 = 5740685) B5740685
theorem B3229121 : Blo 1699550 3229121 := bstep (se 2 (by rfl) ⟨1210920, by rfl⟩ : syracuseStep 3229121 = 2421841) B2421841
theorem B3827159 : Blo 1699550 3827159 := bstep (se 1 (by rfl) ⟨2870369, by rfl⟩ : syracuseStep 3827159 = 5740739) B5740739
theorem B5735987 : Blo 1699550 5735987 := bstep (se 1 (by rfl) ⟨4301990, by rfl⟩ : syracuseStep 5735987 = 8603981) B8603981
theorem B2836055 : Blo 1699550 2836055 := bstep (se 1 (by rfl) ⟨2127041, by rfl⟩ : syracuseStep 2836055 = 4254083) B4254083
theorem B2549387 : Blo 1699550 2549387 := bstep (se 1 (by rfl) ⟨1912040, by rfl⟩ : syracuseStep 2549387 = 3824081) B3824081
theorem B3827339 : Blo 1699550 3827339 := bstep (se 1 (by rfl) ⟨2870504, by rfl⟩ : syracuseStep 3827339 = 5741009) B5741009
theorem B2549399 : Blo 1699550 2549399 := bstep (se 1 (by rfl) ⟨1912049, by rfl⟩ : syracuseStep 2549399 = 3824099) B3824099
theorem B3827393 : Blo 1699550 3827393 := bstep (se 2 (by rfl) ⟨1435272, by rfl⟩ : syracuseStep 3827393 = 2870545) B2870545
theorem B2549465 : Blo 1699550 2549465 := bstep (se 2 (by rfl) ⟨956049, by rfl⟩ : syracuseStep 2549465 = 1912099) B1912099
theorem B3229463 : Blo 1699550 3229463 := bstep (se 1 (by rfl) ⟨2422097, by rfl⟩ : syracuseStep 3229463 = 4844195) B4844195
theorem B3630899 : Blo 1699550 3630899 := bstep (se 1 (by rfl) ⟨2723174, by rfl⟩ : syracuseStep 3630899 = 5446349) B5446349
theorem B5736257 : Blo 1699550 5736257 := bstep (se 2 (by rfl) ⟨2151096, by rfl⟩ : syracuseStep 5736257 = 4302193) B4302193
theorem B2549579 : Blo 1699550 2549579 := bstep (se 1 (by rfl) ⟨1912184, by rfl⟩ : syracuseStep 2549579 = 3824369) B3824369
theorem B2869067 : Blo 1699550 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B2549591 : Blo 1699550 2549591 := bstep (se 1 (by rfl) ⟨1912193, by rfl⟩ : syracuseStep 2549591 = 3824387) B3824387
theorem B2328409 : Blo 1699550 2328409 := bstep (se 2 (by rfl) ⟨873153, by rfl⟩ : syracuseStep 2328409 = 1746307) B1746307
theorem B2549657 : Blo 1699550 2549657 := bstep (se 2 (by rfl) ⟨956121, by rfl⟩ : syracuseStep 2549657 = 1912243) B1912243
theorem B3827609 : Blo 1699550 3827609 := bstep (se 2 (by rfl) ⟨1435353, by rfl⟩ : syracuseStep 3827609 = 2870707) B2870707
theorem B2869195 : Blo 1699550 2869195 := bstep (se 1 (by rfl) ⟨2151896, by rfl⟩ : syracuseStep 2869195 = 4303793) B4303793
theorem B3827699 : Blo 1699550 3827699 := bstep (se 1 (by rfl) ⟨2870774, by rfl⟩ : syracuseStep 3827699 = 5741549) B5741549
theorem B2549771 : Blo 1699550 2549771 := bstep (se 1 (by rfl) ⟨1912328, by rfl⟩ : syracuseStep 2549771 = 3824657) B3824657
theorem B2549783 : Blo 1699550 2549783 := bstep (se 1 (by rfl) ⟨1912337, by rfl⟩ : syracuseStep 2549783 = 3824675) B3824675
theorem B3827735 : Blo 1699550 3827735 := bstep (se 1 (by rfl) ⟨2870801, by rfl⟩ : syracuseStep 3827735 = 5741603) B5741603
theorem B2549849 : Blo 1699550 2549849 := bstep (se 2 (by rfl) ⟨956193, by rfl⟩ : syracuseStep 2549849 = 1912387) B1912387
theorem B2869337 : Blo 1699550 2869337 := bstep (se 2 (by rfl) ⟨1076001, by rfl⟩ : syracuseStep 2869337 = 2152003) B2152003
theorem B4843613 : Blo 1699550 4843613 := bstep (se 3 (by rfl) ⟨908177, by rfl⟩ : syracuseStep 4843613 = 1816355) B1816355
theorem B8726707 : Blo 1699550 8726707 := bstep (se 1 (by rfl) ⟨6545030, by rfl⟩ : syracuseStep 8726707 = 13090061) B13090061
theorem B2549963 : Blo 1699550 2549963 := bstep (se 1 (by rfl) ⟨1912472, by rfl⟩ : syracuseStep 2549963 = 3824945) B3824945
theorem B3827915 : Blo 1699550 3827915 := bstep (se 1 (by rfl) ⟨2870936, by rfl⟩ : syracuseStep 3827915 = 5741873) B5741873
theorem B2549975 : Blo 1699550 2549975 := bstep (se 1 (by rfl) ⟨1912481, by rfl⟩ : syracuseStep 2549975 = 3824963) B3824963
theorem B2869465 : Blo 1699550 2869465 := bstep (se 2 (by rfl) ⟨1076049, by rfl⟩ : syracuseStep 2869465 = 2152099) B2152099
theorem B3827969 : Blo 1699550 3827969 := bstep (se 2 (by rfl) ⟨1435488, by rfl⟩ : syracuseStep 3827969 = 2870977) B2870977
theorem B6457603 : Blo 1699550 6457603 := bstep (se 1 (by rfl) ⟨4843202, by rfl⟩ : syracuseStep 6457603 = 9686405) B9686405
theorem B4598039 : Blo 1699550 4598039 := bstep (se 1 (by rfl) ⟨3448529, by rfl⟩ : syracuseStep 4598039 = 6897059) B6897059
theorem B2550041 : Blo 1699550 2550041 := bstep (se 2 (by rfl) ⟨956265, by rfl⟩ : syracuseStep 2550041 = 1912531) B1912531
theorem B6637889 : Blo 1699550 6637889 := bstep (se 2 (by rfl) ⟨2489208, by rfl⟩ : syracuseStep 6637889 = 4978417) B4978417
theorem B5736797 : Blo 1699550 5736797 := bstep (se 3 (by rfl) ⟨1075649, by rfl⟩ : syracuseStep 5736797 = 2151299) B2151299
theorem B2550155 : Blo 1699550 2550155 := bstep (se 1 (by rfl) ⟨1912616, by rfl⟩ : syracuseStep 2550155 = 3825233) B3825233
theorem B2550167 : Blo 1699550 2550167 := bstep (se 1 (by rfl) ⟨1912625, by rfl⟩ : syracuseStep 2550167 = 3825251) B3825251
theorem B4843955 : Blo 1699550 4843955 := bstep (se 1 (by rfl) ⟨3632966, by rfl⟩ : syracuseStep 4843955 = 7265933) B7265933
theorem B3230131 : Blo 1699550 3230131 := bstep (se 1 (by rfl) ⟨2422598, by rfl⟩ : syracuseStep 3230131 = 4845197) B4845197
theorem B4303307 : Blo 1699550 4303307 := bstep (se 1 (by rfl) ⟨3227480, by rfl⟩ : syracuseStep 4303307 = 6454961) B6454961
theorem B11790809 : Blo 1699550 11790809 := bstep (se 2 (by rfl) ⟨4421553, by rfl⟩ : syracuseStep 11790809 = 8843107) B8843107
theorem B2550233 : Blo 1699550 2550233 := bstep (se 2 (by rfl) ⟨956337, by rfl⟩ : syracuseStep 2550233 = 1912675) B1912675
theorem B3828185 : Blo 1699550 3828185 := bstep (se 2 (by rfl) ⟨1435569, by rfl⟩ : syracuseStep 3828185 = 2871139) B2871139
theorem B6457907 : Blo 1699550 6457907 := bstep (se 1 (by rfl) ⟨4843430, by rfl⟩ : syracuseStep 6457907 = 9686861) B9686861
theorem B3828275 : Blo 1699550 3828275 := bstep (se 1 (by rfl) ⟨2871206, by rfl⟩ : syracuseStep 3828275 = 5742413) B5742413
theorem B2550347 : Blo 1699550 2550347 := bstep (se 1 (by rfl) ⟨1912760, by rfl⟩ : syracuseStep 2550347 = 3825521) B3825521
theorem B2550359 : Blo 1699550 2550359 := bstep (se 1 (by rfl) ⟨1912769, by rfl⟩ : syracuseStep 2550359 = 3825539) B3825539
theorem B3828311 : Blo 1699550 3828311 := bstep (se 1 (by rfl) ⟨2871233, by rfl⟩ : syracuseStep 3828311 = 5742467) B5742467
theorem B70724189 : Blo 1699550 70724189 := bstep (se 3 (by rfl) ⟨13260785, by rfl⟩ : syracuseStep 70724189 = 26521571) B26521571
theorem B9685655 : Blo 1699550 9685655 := bstep (se 1 (by rfl) ⟨7264241, by rfl⟩ : syracuseStep 9685655 = 14528483) B14528483
theorem B2722457 : Blo 1699550 2722457 := bstep (se 2 (by rfl) ⟨1020921, by rfl⟩ : syracuseStep 2722457 = 2041843) B2041843
theorem B2550425 : Blo 1699550 2550425 := bstep (se 2 (by rfl) ⟨956409, by rfl⟩ : syracuseStep 2550425 = 1912819) B1912819
theorem B3631873 : Blo 1699550 3631873 := bstep (se 2 (by rfl) ⟨1361952, by rfl⟩ : syracuseStep 3631873 = 2723905) B2723905
theorem B2550539 : Blo 1699550 2550539 := bstep (se 1 (by rfl) ⟨1912904, by rfl⟩ : syracuseStep 2550539 = 3825809) B3825809
theorem B2550551 : Blo 1699550 2550551 := bstep (se 1 (by rfl) ⟨1912913, by rfl⟩ : syracuseStep 2550551 = 3825827) B3825827
theorem B2870039 : Blo 1699550 2870039 := bstep (se 1 (by rfl) ⟨2152529, by rfl⟩ : syracuseStep 2870039 = 4305059) B4305059
theorem B2722585 : Blo 1699550 2722585 := bstep (se 2 (by rfl) ⟨1020969, by rfl⟩ : syracuseStep 2722585 = 2041939) B2041939
theorem B2550617 : Blo 1699550 2550617 := bstep (se 2 (by rfl) ⟨956481, by rfl⟩ : syracuseStep 2550617 = 1912963) B1912963
theorem B2870167 : Blo 1699550 2870167 := bstep (se 1 (by rfl) ⟨2152625, by rfl⟩ : syracuseStep 2870167 = 4305251) B4305251
theorem B2550731 : Blo 1699550 2550731 := bstep (se 1 (by rfl) ⟨1913048, by rfl⟩ : syracuseStep 2550731 = 3826097) B3826097
theorem B2550743 : Blo 1699550 2550743 := bstep (se 1 (by rfl) ⟨1913057, by rfl⟩ : syracuseStep 2550743 = 3826115) B3826115
theorem B3632129 : Blo 1699550 3632129 := bstep (se 2 (by rfl) ⟨1362048, by rfl⟩ : syracuseStep 3632129 = 2724097) B2724097
theorem B2550809 : Blo 1699550 2550809 := bstep (se 2 (by rfl) ⟨956553, by rfl⟩ : syracuseStep 2550809 = 1913107) B1913107
theorem B24849443 : Blo 1699550 24849443 := bstep (se 1 (by rfl) ⟨18637082, by rfl⟩ : syracuseStep 24849443 = 37274165) B37274165
theorem B7261235 : Blo 1699550 7261235 := bstep (se 1 (by rfl) ⟨5445926, by rfl⟩ : syracuseStep 7261235 = 10891853) B10891853
theorem B39291979 : Blo 1699550 39291979 := bstep (se 1 (by rfl) ⟨29468984, by rfl⟩ : syracuseStep 39291979 = 58937969) B58937969
theorem B3632215 : Blo 1699550 3632215 := bstep (se 1 (by rfl) ⟨2724161, by rfl⟩ : syracuseStep 3632215 = 5448323) B5448323
theorem B2550923 : Blo 1699550 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B22088855 : Blo 1699550 22088855 := bstep (se 1 (by rfl) ⟨16566641, by rfl⟩ : syracuseStep 22088855 = 33133283) B33133283
theorem B2550935 : Blo 1699550 2550935 := bstep (se 1 (by rfl) ⟨1913201, by rfl⟩ : syracuseStep 2550935 = 3826403) B3826403
theorem B6458561 : Blo 1699550 6458561 := bstep (se 2 (by rfl) ⟨2421960, by rfl⟩ : syracuseStep 6458561 = 4843921) B4843921
theorem B3493079 : Blo 1699550 3493079 := bstep (se 1 (by rfl) ⟨2619809, by rfl⟩ : syracuseStep 3493079 = 5239619) B5239619
theorem B2551001 : Blo 1699550 2551001 := bstep (se 2 (by rfl) ⟨956625, by rfl⟩ : syracuseStep 2551001 = 1913251) B1913251
theorem B2551115 : Blo 1699550 2551115 := bstep (se 1 (by rfl) ⟨1913336, by rfl⟩ : syracuseStep 2551115 = 3826673) B3826673
theorem B2551127 : Blo 1699550 2551127 := bstep (se 1 (by rfl) ⟨1913345, by rfl⟩ : syracuseStep 2551127 = 3826691) B3826691
theorem B1912171 : Blo 1699550 1912171 := bstep (se 1 (by rfl) ⟨1434128, by rfl⟩ : syracuseStep 1912171 = 2868257) B2868257
theorem B55184753 : Blo 1699550 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B4304279 : Blo 1699550 4304279 := bstep (se 1 (by rfl) ⟨3228209, by rfl⟩ : syracuseStep 4304279 = 6456419) B6456419
theorem B2723225 : Blo 1699550 2723225 := bstep (se 2 (by rfl) ⟨1021209, by rfl⟩ : syracuseStep 2723225 = 2042419) B2042419
theorem B2551193 : Blo 1699550 2551193 := bstep (se 2 (by rfl) ⟨956697, by rfl⟩ : syracuseStep 2551193 = 1913395) B1913395
theorem B6131123 : Blo 1699550 6131123 := bstep (se 1 (by rfl) ⟨4598342, by rfl⟩ : syracuseStep 6131123 = 9196685) B9196685
theorem B5737931 : Blo 1699550 5737931 := bstep (se 1 (by rfl) ⟨4303448, by rfl⟩ : syracuseStep 5737931 = 8606897) B8606897
theorem B1912279 : Blo 1699550 1912279 := bstep (se 1 (by rfl) ⟨1434209, by rfl⟩ : syracuseStep 1912279 = 2868419) B2868419
theorem B2551307 : Blo 1699550 2551307 := bstep (se 1 (by rfl) ⟨1913480, by rfl⟩ : syracuseStep 2551307 = 3826961) B3826961
theorem B2870795 : Blo 1699550 2870795 := bstep (se 1 (by rfl) ⟨2153096, by rfl⟩ : syracuseStep 2870795 = 4306193) B4306193
theorem B2551319 : Blo 1699550 2551319 := bstep (se 1 (by rfl) ⟨1913489, by rfl⟩ : syracuseStep 2551319 = 3826979) B3826979
theorem B23277131 : Blo 1699550 23277131 := bstep (se 1 (by rfl) ⟨17457848, by rfl⟩ : syracuseStep 23277131 = 34915697) B34915697
theorem B2551385 : Blo 1699550 2551385 := bstep (se 2 (by rfl) ⟨956769, by rfl⟩ : syracuseStep 2551385 = 1913539) B1913539
theorem B8605277 : Blo 1699550 8605277 := bstep (se 3 (by rfl) ⟨1613489, by rfl⟩ : syracuseStep 8605277 = 3226979) B3226979
theorem B10341989 : Blo 1699550 10341989 := bstep (se 4 (by rfl) ⟨969561, by rfl⟩ : syracuseStep 10341989 = 1939123) B1939123
theorem B1912459 : Blo 1699550 1912459 := bstep (se 1 (by rfl) ⟨1434344, by rfl⟩ : syracuseStep 1912459 = 2868689) B2868689
theorem B2870923 : Blo 1699550 2870923 := bstep (se 1 (by rfl) ⟨2153192, by rfl⟩ : syracuseStep 2870923 = 4306385) B4306385
theorem B3985075 : Blo 1699550 3985075 := bstep (se 1 (by rfl) ⟨2988806, by rfl⟩ : syracuseStep 3985075 = 5977613) B5977613
theorem B2551499 : Blo 1699550 2551499 := bstep (se 1 (by rfl) ⟨1913624, by rfl⟩ : syracuseStep 2551499 = 3827249) B3827249
theorem B2551511 : Blo 1699550 2551511 := bstep (se 1 (by rfl) ⟨1913633, by rfl⟩ : syracuseStep 2551511 = 3827267) B3827267
theorem B5738201 : Blo 1699550 5738201 := bstep (se 2 (by rfl) ⟨2151825, by rfl⟩ : syracuseStep 5738201 = 4303651) B4303651
theorem B1699563 : Blo 1699550 1699563 := bstep (se 1 (by rfl) ⟨1274672, by rfl⟩ : syracuseStep 1699563 = 2549345) B2549345
theorem B1699575 : Blo 1699550 1699575 := bstep (se 1 (by rfl) ⟨1274681, by rfl⟩ : syracuseStep 1699575 = 2549363) B2549363
theorem B1912567 : Blo 1699550 1912567 := bstep (se 1 (by rfl) ⟨1434425, by rfl⟩ : syracuseStep 1912567 = 2868851) B2868851
theorem B1699595 : Blo 1699550 1699595 := bstep (se 1 (by rfl) ⟨1274696, by rfl⟩ : syracuseStep 1699595 = 2549393) B2549393
theorem B1699607 : Blo 1699550 1699607 := bstep (se 1 (by rfl) ⟨1274705, by rfl⟩ : syracuseStep 1699607 = 2549411) B2549411
theorem B2551577 : Blo 1699550 2551577 := bstep (se 2 (by rfl) ⟨956841, by rfl⟩ : syracuseStep 2551577 = 1913683) B1913683
theorem B2871065 : Blo 1699550 2871065 := bstep (se 2 (by rfl) ⟨1076649, by rfl⟩ : syracuseStep 2871065 = 2153299) B2153299
theorem B1699627 : Blo 1699550 1699627 := bstep (se 1 (by rfl) ⟨1274720, by rfl⟩ : syracuseStep 1699627 = 2549441) B2549441
theorem B12914477 : Blo 1699550 12914477 := bstep (se 3 (by rfl) ⟨2421464, by rfl⟩ : syracuseStep 12914477 = 4842929) B4842929
theorem B6893363 : Blo 1699550 6893363 := bstep (se 1 (by rfl) ⟨5170022, by rfl⟩ : syracuseStep 6893363 = 10340045) B10340045
theorem B1699639 : Blo 1699550 1699639 := bstep (se 1 (by rfl) ⟨1274729, by rfl⟩ : syracuseStep 1699639 = 2549459) B2549459
theorem B1699659 : Blo 1699550 1699659 := bstep (se 1 (by rfl) ⟨1274744, by rfl⟩ : syracuseStep 1699659 = 2549489) B2549489
theorem B1699671 : Blo 1699550 1699671 := bstep (se 1 (by rfl) ⟨1274753, by rfl⟩ : syracuseStep 1699671 = 2549507) B2549507
theorem B1699691 : Blo 1699550 1699691 := bstep (se 1 (by rfl) ⟨1274768, by rfl⟩ : syracuseStep 1699691 = 2549537) B2549537
theorem B1699703 : Blo 1699550 1699703 := bstep (se 1 (by rfl) ⟨1274777, by rfl⟩ : syracuseStep 1699703 = 2549555) B2549555
theorem B1699723 : Blo 1699550 1699723 := bstep (se 1 (by rfl) ⟨1274792, by rfl⟩ : syracuseStep 1699723 = 2549585) B2549585
theorem B2551691 : Blo 1699550 2551691 := bstep (se 1 (by rfl) ⟨1913768, by rfl⟩ : syracuseStep 2551691 = 3827537) B3827537
theorem B1699735 : Blo 1699550 1699735 := bstep (se 1 (by rfl) ⟨1274801, by rfl⟩ : syracuseStep 1699735 = 2549603) B2549603
theorem B2551703 : Blo 1699550 2551703 := bstep (se 1 (by rfl) ⟨1913777, by rfl⟩ : syracuseStep 2551703 = 3827555) B3827555
theorem B13275031 : Blo 1699550 13275031 := bstep (se 1 (by rfl) ⟨9956273, by rfl⟩ : syracuseStep 13275031 = 19912547) B19912547
theorem B2871193 : Blo 1699550 2871193 := bstep (se 2 (by rfl) ⟨1076697, by rfl⟩ : syracuseStep 2871193 = 2153395) B2153395
theorem B1699755 : Blo 1699550 1699755 := bstep (se 1 (by rfl) ⟨1274816, by rfl⟩ : syracuseStep 1699755 = 2549633) B2549633
theorem B1912747 : Blo 1699550 1912747 := bstep (se 1 (by rfl) ⟨1434560, by rfl⟩ : syracuseStep 1912747 = 2869121) B2869121
theorem B1699767 : Blo 1699550 1699767 := bstep (se 1 (by rfl) ⟨1274825, by rfl⟩ : syracuseStep 1699767 = 2549651) B2549651
theorem B1699787 : Blo 1699550 1699787 := bstep (se 1 (by rfl) ⟨1274840, by rfl⟩ : syracuseStep 1699787 = 2549681) B2549681
theorem B1699799 : Blo 1699550 1699799 := bstep (se 1 (by rfl) ⟨1274849, by rfl⟩ : syracuseStep 1699799 = 2549699) B2549699
theorem B2551769 : Blo 1699550 2551769 := bstep (se 2 (by rfl) ⟨956913, by rfl⟩ : syracuseStep 2551769 = 1913827) B1913827
theorem B1699819 : Blo 1699550 1699819 := bstep (se 1 (by rfl) ⟨1274864, by rfl⟩ : syracuseStep 1699819 = 2549729) B2549729
theorem B1699831 : Blo 1699550 1699831 := bstep (se 1 (by rfl) ⟨1274873, by rfl⟩ : syracuseStep 1699831 = 2549747) B2549747
theorem B1699851 : Blo 1699550 1699851 := bstep (se 1 (by rfl) ⟨1274888, by rfl⟩ : syracuseStep 1699851 = 2549777) B2549777
theorem B1699863 : Blo 1699550 1699863 := bstep (se 1 (by rfl) ⟨1274897, by rfl⟩ : syracuseStep 1699863 = 2549795) B2549795
theorem B1912855 : Blo 1699550 1912855 := bstep (se 1 (by rfl) ⟨1434641, by rfl⟩ : syracuseStep 1912855 = 2869283) B2869283
theorem B1699883 : Blo 1699550 1699883 := bstep (se 1 (by rfl) ⟨1274912, by rfl⟩ : syracuseStep 1699883 = 2549825) B2549825
theorem B4304947 : Blo 1699550 4304947 := bstep (se 1 (by rfl) ⟨3228710, by rfl⟩ : syracuseStep 4304947 = 6457421) B6457421
theorem B1699895 : Blo 1699550 1699895 := bstep (se 1 (by rfl) ⟨1274921, by rfl⟩ : syracuseStep 1699895 = 2549843) B2549843
theorem B1699915 : Blo 1699550 1699915 := bstep (se 1 (by rfl) ⟨1274936, by rfl⟩ : syracuseStep 1699915 = 2549873) B2549873
theorem B2551883 : Blo 1699550 2551883 := bstep (se 1 (by rfl) ⟨1913912, by rfl⟩ : syracuseStep 2551883 = 3827825) B3827825
theorem B1699927 : Blo 1699550 1699927 := bstep (se 1 (by rfl) ⟨1274945, by rfl⟩ : syracuseStep 1699927 = 2549891) B2549891
theorem B2551895 : Blo 1699550 2551895 := bstep (se 1 (by rfl) ⟨1913921, by rfl⟩ : syracuseStep 2551895 = 3827843) B3827843
theorem B2043991 : Blo 1699550 2043991 := bstep (se 1 (by rfl) ⟨1532993, by rfl⟩ : syracuseStep 2043991 = 3065987) B3065987
theorem B13791325 : Blo 1699550 13791325 := bstep (se 3 (by rfl) ⟨2585873, by rfl⟩ : syracuseStep 13791325 = 5171747) B5171747
theorem B11194469 : Blo 1699550 11194469 := bstep (se 4 (by rfl) ⟨1049481, by rfl⟩ : syracuseStep 11194469 = 2098963) B2098963
theorem B1699947 : Blo 1699550 1699947 := bstep (se 1 (by rfl) ⟨1274960, by rfl⟩ : syracuseStep 1699947 = 2549921) B2549921
theorem B1699959 : Blo 1699550 1699959 := bstep (se 1 (by rfl) ⟨1274969, by rfl⟩ : syracuseStep 1699959 = 2549939) B2549939
theorem B1699979 : Blo 1699550 1699979 := bstep (se 1 (by rfl) ⟨1274984, by rfl⟩ : syracuseStep 1699979 = 2549969) B2549969
theorem B1699991 : Blo 1699550 1699991 := bstep (se 1 (by rfl) ⟨1274993, by rfl⟩ : syracuseStep 1699991 = 2549987) B2549987
theorem B2551961 : Blo 1699550 2551961 := bstep (se 2 (by rfl) ⟨956985, by rfl⟩ : syracuseStep 2551961 = 1913971) B1913971
theorem B1700011 : Blo 1699550 1700011 := bstep (se 1 (by rfl) ⟨1275008, by rfl⟩ : syracuseStep 1700011 = 2550017) B2550017
theorem B1700023 : Blo 1699550 1700023 := bstep (se 1 (by rfl) ⟨1275017, by rfl⟩ : syracuseStep 1700023 = 2550035) B2550035
theorem B4305089 : Blo 1699550 4305089 := bstep (se 2 (by rfl) ⟨1614408, by rfl⟩ : syracuseStep 4305089 = 3228817) B3228817
theorem B1700043 : Blo 1699550 1700043 := bstep (se 1 (by rfl) ⟨1275032, by rfl⟩ : syracuseStep 1700043 = 2550065) B2550065
theorem B1913035 : Blo 1699550 1913035 := bstep (se 1 (by rfl) ⟨1434776, by rfl⟩ : syracuseStep 1913035 = 2869553) B2869553
theorem B12906701 : Blo 1699550 12906701 := bstep (se 3 (by rfl) ⟨2420006, by rfl⟩ : syracuseStep 12906701 = 4840013) B4840013
theorem B1700055 : Blo 1699550 1700055 := bstep (se 1 (by rfl) ⟨1275041, by rfl⟩ : syracuseStep 1700055 = 2550083) B2550083
theorem B1700075 : Blo 1699550 1700075 := bstep (se 1 (by rfl) ⟨1275056, by rfl⟩ : syracuseStep 1700075 = 2550113) B2550113
theorem B1700087 : Blo 1699550 1700087 := bstep (se 1 (by rfl) ⟨1275065, by rfl⟩ : syracuseStep 1700087 = 2550131) B2550131
theorem B1700107 : Blo 1699550 1700107 := bstep (se 1 (by rfl) ⟨1275080, by rfl⟩ : syracuseStep 1700107 = 2550161) B2550161
theorem B2552075 : Blo 1699550 2552075 := bstep (se 1 (by rfl) ⟨1914056, by rfl⟩ : syracuseStep 2552075 = 3828113) B3828113
theorem B1700119 : Blo 1699550 1700119 := bstep (se 1 (by rfl) ⟨1275089, by rfl⟩ : syracuseStep 1700119 = 2550179) B2550179
theorem B2552087 : Blo 1699550 2552087 := bstep (se 1 (by rfl) ⟨1914065, by rfl⟩ : syracuseStep 2552087 = 3828131) B3828131
theorem B1700139 : Blo 1699550 1700139 := bstep (se 1 (by rfl) ⟨1275104, by rfl⟩ : syracuseStep 1700139 = 2550209) B2550209
theorem B1700151 : Blo 1699550 1700151 := bstep (se 1 (by rfl) ⟨1275113, by rfl⟩ : syracuseStep 1700151 = 2550227) B2550227
theorem B1913143 : Blo 1699550 1913143 := bstep (se 1 (by rfl) ⟨1434857, by rfl⟩ : syracuseStep 1913143 = 2869715) B2869715
theorem B1700171 : Blo 1699550 1700171 := bstep (se 1 (by rfl) ⟨1275128, by rfl⟩ : syracuseStep 1700171 = 2550257) B2550257
theorem B1700183 : Blo 1699550 1700183 := bstep (se 1 (by rfl) ⟨1275137, by rfl⟩ : syracuseStep 1700183 = 2550275) B2550275
theorem B2552153 : Blo 1699550 2552153 := bstep (se 2 (by rfl) ⟨957057, by rfl⟩ : syracuseStep 2552153 = 1914115) B1914115
theorem B1700203 : Blo 1699550 1700203 := bstep (se 1 (by rfl) ⟨1275152, by rfl⟩ : syracuseStep 1700203 = 2550305) B2550305
theorem B1700215 : Blo 1699550 1700215 := bstep (se 1 (by rfl) ⟨1275161, by rfl⟩ : syracuseStep 1700215 = 2550323) B2550323
theorem B1700235 : Blo 1699550 1700235 := bstep (se 1 (by rfl) ⟨1275176, by rfl⟩ : syracuseStep 1700235 = 2550353) B2550353
theorem B1700247 : Blo 1699550 1700247 := bstep (se 1 (by rfl) ⟨1275185, by rfl⟩ : syracuseStep 1700247 = 2550371) B2550371
theorem B5738903 : Blo 1699550 5738903 := bstep (se 1 (by rfl) ⟨4304177, by rfl⟩ : syracuseStep 5738903 = 8608355) B8608355
theorem B1700267 : Blo 1699550 1700267 := bstep (se 1 (by rfl) ⟨1275200, by rfl⟩ : syracuseStep 1700267 = 2550401) B2550401
theorem B6459821 : Blo 1699550 6459821 := bstep (se 3 (by rfl) ⟨1211216, by rfl⟩ : syracuseStep 6459821 = 2422433) B2422433
theorem B1700279 : Blo 1699550 1700279 := bstep (se 1 (by rfl) ⟨1275209, by rfl⟩ : syracuseStep 1700279 = 2550419) B2550419
theorem B1700299 : Blo 1699550 1700299 := bstep (se 1 (by rfl) ⟨1275224, by rfl⟩ : syracuseStep 1700299 = 2550449) B2550449
theorem B6459851 : Blo 1699550 6459851 := bstep (se 1 (by rfl) ⟨4844888, by rfl⟩ : syracuseStep 6459851 = 9689777) B9689777
theorem B2552267 : Blo 1699550 2552267 := bstep (se 1 (by rfl) ⟨1914200, by rfl⟩ : syracuseStep 2552267 = 3828401) B3828401
theorem B1700311 : Blo 1699550 1700311 := bstep (se 1 (by rfl) ⟨1275233, by rfl⟩ : syracuseStep 1700311 = 2550467) B2550467
theorem B2552279 : Blo 1699550 2552279 := bstep (se 1 (by rfl) ⟨1914209, by rfl⟩ : syracuseStep 2552279 = 3828419) B3828419
theorem B1700331 : Blo 1699550 1700331 := bstep (se 1 (by rfl) ⟨1275248, by rfl⟩ : syracuseStep 1700331 = 2550497) B2550497
theorem B1913323 : Blo 1699550 1913323 := bstep (se 1 (by rfl) ⟨1434992, by rfl⟩ : syracuseStep 1913323 = 2869985) B2869985
theorem B1700343 : Blo 1699550 1700343 := bstep (se 1 (by rfl) ⟨1275257, by rfl⟩ : syracuseStep 1700343 = 2550515) B2550515
theorem B1700363 : Blo 1699550 1700363 := bstep (se 1 (by rfl) ⟨1275272, by rfl⟩ : syracuseStep 1700363 = 2550545) B2550545
theorem B1700375 : Blo 1699550 1700375 := bstep (se 1 (by rfl) ⟨1275281, by rfl⟩ : syracuseStep 1700375 = 2550563) B2550563
theorem B1700395 : Blo 1699550 1700395 := bstep (se 1 (by rfl) ⟨1275296, by rfl⟩ : syracuseStep 1700395 = 2550593) B2550593
theorem B1700407 : Blo 1699550 1700407 := bstep (se 1 (by rfl) ⟨1275305, by rfl⟩ : syracuseStep 1700407 = 2550611) B2550611
theorem B1700427 : Blo 1699550 1700427 := bstep (se 1 (by rfl) ⟨1275320, by rfl⟩ : syracuseStep 1700427 = 2550641) B2550641
theorem B1700439 : Blo 1699550 1700439 := bstep (se 1 (by rfl) ⟨1275329, by rfl⟩ : syracuseStep 1700439 = 2550659) B2550659
theorem B1913431 : Blo 1699550 1913431 := bstep (se 1 (by rfl) ⟨1435073, by rfl⟩ : syracuseStep 1913431 = 2870147) B2870147
theorem B1700459 : Blo 1699550 1700459 := bstep (se 1 (by rfl) ⟨1275344, by rfl⟩ : syracuseStep 1700459 = 2550689) B2550689
theorem B1700471 : Blo 1699550 1700471 := bstep (se 1 (by rfl) ⟨1275353, by rfl⟩ : syracuseStep 1700471 = 2550707) B2550707
theorem B1700491 : Blo 1699550 1700491 := bstep (se 1 (by rfl) ⟨1275368, by rfl⟩ : syracuseStep 1700491 = 2550737) B2550737
theorem B9187991 : Blo 1699550 9187991 := bstep (se 1 (by rfl) ⟨6890993, by rfl⟩ : syracuseStep 9187991 = 13781987) B13781987
theorem B1700503 : Blo 1699550 1700503 := bstep (se 1 (by rfl) ⟨1275377, by rfl⟩ : syracuseStep 1700503 = 2550755) B2550755
theorem B1700523 : Blo 1699550 1700523 := bstep (se 1 (by rfl) ⟨1275392, by rfl⟩ : syracuseStep 1700523 = 2550785) B2550785
theorem B12907187 : Blo 1699550 12907187 := bstep (se 1 (by rfl) ⟨9680390, by rfl⟩ : syracuseStep 12907187 = 19360781) B19360781
theorem B1700535 : Blo 1699550 1700535 := bstep (se 1 (by rfl) ⟨1275401, by rfl⟩ : syracuseStep 1700535 = 2550803) B2550803
theorem B1700555 : Blo 1699550 1700555 := bstep (se 1 (by rfl) ⟨1275416, by rfl⟩ : syracuseStep 1700555 = 2550833) B2550833
theorem B2151127 : Blo 1699550 2151127 := bstep (se 1 (by rfl) ⟨1613345, by rfl⟩ : syracuseStep 2151127 = 3226691) B3226691
theorem B1700567 : Blo 1699550 1700567 := bstep (se 1 (by rfl) ⟨1275425, by rfl⟩ : syracuseStep 1700567 = 2550851) B2550851
theorem B4788953 : Blo 1699550 4788953 := bstep (se 2 (by rfl) ⟨1795857, by rfl⟩ : syracuseStep 4788953 = 3591715) B3591715
theorem B1700587 : Blo 1699550 1700587 := bstep (se 1 (by rfl) ⟨1275440, by rfl⟩ : syracuseStep 1700587 = 2550881) B2550881
theorem B1700599 : Blo 1699550 1700599 := bstep (se 1 (by rfl) ⟨1275449, by rfl⟩ : syracuseStep 1700599 = 2550899) B2550899
theorem B3273473 : Blo 1699550 3273473 := bstep (se 2 (by rfl) ⟨1227552, by rfl⟩ : syracuseStep 3273473 = 2455105) B2455105
theorem B1700619 : Blo 1699550 1700619 := bstep (se 1 (by rfl) ⟨1275464, by rfl⟩ : syracuseStep 1700619 = 2550929) B2550929
theorem B1913611 : Blo 1699550 1913611 := bstep (se 1 (by rfl) ⟨1435208, by rfl⟩ : syracuseStep 1913611 = 2870417) B2870417
theorem B1700631 : Blo 1699550 1700631 := bstep (se 1 (by rfl) ⟨1275473, by rfl⟩ : syracuseStep 1700631 = 2550947) B2550947
theorem B1700651 : Blo 1699550 1700651 := bstep (se 1 (by rfl) ⟨1275488, by rfl⟩ : syracuseStep 1700651 = 2550977) B2550977
theorem B14521133 : Blo 1699550 14521133 := bstep (se 3 (by rfl) ⟨2722712, by rfl⟩ : syracuseStep 14521133 = 5445425) B5445425
theorem B1700663 : Blo 1699550 1700663 := bstep (se 1 (by rfl) ⟨1275497, by rfl⟩ : syracuseStep 1700663 = 2550995) B2550995
theorem B1700683 : Blo 1699550 1700683 := bstep (se 1 (by rfl) ⟨1275512, by rfl⟩ : syracuseStep 1700683 = 2551025) B2551025
theorem B1700695 : Blo 1699550 1700695 := bstep (se 1 (by rfl) ⟨1275521, by rfl⟩ : syracuseStep 1700695 = 2551043) B2551043
theorem B1700715 : Blo 1699550 1700715 := bstep (se 1 (by rfl) ⟨1275536, by rfl⟩ : syracuseStep 1700715 = 2551073) B2551073
theorem B1815415 : Blo 1699550 1815415 := bstep (se 1 (by rfl) ⟨1361561, by rfl⟩ : syracuseStep 1815415 = 2723123) B2723123
theorem B1700727 : Blo 1699550 1700727 := bstep (se 1 (by rfl) ⟨1275545, by rfl⟩ : syracuseStep 1700727 = 2551091) B2551091
theorem B1913719 : Blo 1699550 1913719 := bstep (se 1 (by rfl) ⟨1435289, by rfl⟩ : syracuseStep 1913719 = 2870579) B2870579
theorem B1700747 : Blo 1699550 1700747 := bstep (se 1 (by rfl) ⟨1275560, by rfl⟩ : syracuseStep 1700747 = 2551121) B2551121
theorem B1700759 : Blo 1699550 1700759 := bstep (se 1 (by rfl) ⟨1275569, by rfl⟩ : syracuseStep 1700759 = 2551139) B2551139
theorem B1700779 : Blo 1699550 1700779 := bstep (se 1 (by rfl) ⟨1275584, by rfl⟩ : syracuseStep 1700779 = 2551169) B2551169
theorem B5739443 : Blo 1699550 5739443 := bstep (se 1 (by rfl) ⟨4304582, by rfl⟩ : syracuseStep 5739443 = 8609165) B8609165
theorem B1840055 : Blo 1699550 1840055 := bstep (se 1 (by rfl) ⟨1380041, by rfl⟩ : syracuseStep 1840055 = 2760083) B2760083
theorem B1700791 : Blo 1699550 1700791 := bstep (se 1 (by rfl) ⟨1275593, by rfl⟩ : syracuseStep 1700791 = 2551187) B2551187
theorem B1700811 : Blo 1699550 1700811 := bstep (se 1 (by rfl) ⟨1275608, by rfl⟩ : syracuseStep 1700811 = 2551217) B2551217
theorem B1700823 : Blo 1699550 1700823 := bstep (se 1 (by rfl) ⟨1275617, by rfl⟩ : syracuseStep 1700823 = 2551235) B2551235
theorem B1700843 : Blo 1699550 1700843 := bstep (se 1 (by rfl) ⟨1275632, by rfl⟩ : syracuseStep 1700843 = 2551265) B2551265
theorem B1700855 : Blo 1699550 1700855 := bstep (se 1 (by rfl) ⟨1275641, by rfl⟩ : syracuseStep 1700855 = 2551283) B2551283
theorem B1700875 : Blo 1699550 1700875 := bstep (se 1 (by rfl) ⟨1275656, by rfl⟩ : syracuseStep 1700875 = 2551313) B2551313
theorem B1700887 : Blo 1699550 1700887 := bstep (se 1 (by rfl) ⟨1275665, by rfl⟩ : syracuseStep 1700887 = 2551331) B2551331
theorem B1700907 : Blo 1699550 1700907 := bstep (se 1 (by rfl) ⟨1275680, by rfl⟩ : syracuseStep 1700907 = 2551361) B2551361
theorem B13792301 : Blo 1699550 13792301 := bstep (se 3 (by rfl) ⟨2586056, by rfl⟩ : syracuseStep 13792301 = 5172113) B5172113
theorem B1913899 : Blo 1699550 1913899 := bstep (se 1 (by rfl) ⟨1435424, by rfl⟩ : syracuseStep 1913899 = 2870849) B2870849
theorem B1700919 : Blo 1699550 1700919 := bstep (se 1 (by rfl) ⟨1275689, by rfl⟩ : syracuseStep 1700919 = 2551379) B2551379
theorem B1700939 : Blo 1699550 1700939 := bstep (se 1 (by rfl) ⟨1275704, by rfl⟩ : syracuseStep 1700939 = 2551409) B2551409
theorem B1700951 : Blo 1699550 1700951 := bstep (se 1 (by rfl) ⟨1275713, by rfl⟩ : syracuseStep 1700951 = 2551427) B2551427
theorem B6460505 : Blo 1699550 6460505 := bstep (se 2 (by rfl) ⟨2422689, by rfl⟩ : syracuseStep 6460505 = 4845379) B4845379
theorem B1938539 : Blo 1699550 1938539 := bstep (se 1 (by rfl) ⟨1453904, by rfl⟩ : syracuseStep 1938539 = 2907809) B2907809
theorem B1700971 : Blo 1699550 1700971 := bstep (se 1 (by rfl) ⟨1275728, by rfl⟩ : syracuseStep 1700971 = 2551457) B2551457
theorem B1700983 : Blo 1699550 1700983 := bstep (se 1 (by rfl) ⟨1275737, by rfl⟩ : syracuseStep 1700983 = 2551475) B2551475
theorem B1701003 : Blo 1699550 1701003 := bstep (se 1 (by rfl) ⟨1275752, by rfl⟩ : syracuseStep 1701003 = 2551505) B2551505
theorem B5444759 : Blo 1699550 5444759 := bstep (se 1 (by rfl) ⟨4083569, by rfl⟩ : syracuseStep 5444759 = 8167139) B8167139
theorem B1701015 : Blo 1699550 1701015 := bstep (se 1 (by rfl) ⟨1275761, by rfl⟩ : syracuseStep 1701015 = 2551523) B2551523
theorem B1914007 : Blo 1699550 1914007 := bstep (se 1 (by rfl) ⟨1435505, by rfl⟩ : syracuseStep 1914007 = 2871011) B2871011
theorem B1701035 : Blo 1699550 1701035 := bstep (se 1 (by rfl) ⟨1275776, by rfl⟩ : syracuseStep 1701035 = 2551553) B2551553
theorem B1701047 : Blo 1699550 1701047 := bstep (se 1 (by rfl) ⟨1275785, by rfl⟩ : syracuseStep 1701047 = 2551571) B2551571
theorem B5739713 : Blo 1699550 5739713 := bstep (se 2 (by rfl) ⟨2152392, by rfl⟩ : syracuseStep 5739713 = 4304785) B4304785
theorem B1701067 : Blo 1699550 1701067 := bstep (se 1 (by rfl) ⟨1275800, by rfl⟩ : syracuseStep 1701067 = 2551601) B2551601
theorem B1701079 : Blo 1699550 1701079 := bstep (se 1 (by rfl) ⟨1275809, by rfl⟩ : syracuseStep 1701079 = 2551619) B2551619
theorem B1815787 : Blo 1699550 1815787 := bstep (se 1 (by rfl) ⟨1361840, by rfl⟩ : syracuseStep 1815787 = 2723681) B2723681
theorem B1701099 : Blo 1699550 1701099 := bstep (se 1 (by rfl) ⟨1275824, by rfl⟩ : syracuseStep 1701099 = 2551649) B2551649
theorem B1701111 : Blo 1699550 1701111 := bstep (se 1 (by rfl) ⟨1275833, by rfl⟩ : syracuseStep 1701111 = 2551667) B2551667
theorem B1701131 : Blo 1699550 1701131 := bstep (se 1 (by rfl) ⟨1275848, by rfl⟩ : syracuseStep 1701131 = 2551697) B2551697
theorem B1701143 : Blo 1699550 1701143 := bstep (se 1 (by rfl) ⟨1275857, by rfl⟩ : syracuseStep 1701143 = 2551715) B2551715
theorem B1701163 : Blo 1699550 1701163 := bstep (se 1 (by rfl) ⟨1275872, by rfl⟩ : syracuseStep 1701163 = 2551745) B2551745
theorem B1701175 : Blo 1699550 1701175 := bstep (se 1 (by rfl) ⟨1275881, by rfl⟩ : syracuseStep 1701175 = 2551763) B2551763
theorem B1701195 : Blo 1699550 1701195 := bstep (se 1 (by rfl) ⟨1275896, by rfl⟩ : syracuseStep 1701195 = 2551793) B2551793
theorem B1914187 : Blo 1699550 1914187 := bstep (se 1 (by rfl) ⟨1435640, by rfl⟩ : syracuseStep 1914187 = 2871281) B2871281
theorem B1701207 : Blo 1699550 1701207 := bstep (se 1 (by rfl) ⟨1275905, by rfl⟩ : syracuseStep 1701207 = 2551811) B2551811
theorem B31028579 : Blo 1699550 31028579 := bstep (se 1 (by rfl) ⟨23271434, by rfl⟩ : syracuseStep 31028579 = 46542869) B46542869
theorem B1701227 : Blo 1699550 1701227 := bstep (se 1 (by rfl) ⟨1275920, by rfl⟩ : syracuseStep 1701227 = 2551841) B2551841
theorem B1701239 : Blo 1699550 1701239 := bstep (se 1 (by rfl) ⟨1275929, by rfl⟩ : syracuseStep 1701239 = 2551859) B2551859
theorem B1701259 : Blo 1699550 1701259 := bstep (se 1 (by rfl) ⟨1275944, by rfl⟩ : syracuseStep 1701259 = 2551889) B2551889
theorem B1701271 : Blo 1699550 1701271 := bstep (se 1 (by rfl) ⟨1275953, by rfl⟩ : syracuseStep 1701271 = 2551907) B2551907
theorem B1701291 : Blo 1699550 1701291 := bstep (se 1 (by rfl) ⟨1275968, by rfl⟩ : syracuseStep 1701291 = 2551937) B2551937
theorem B4306355 : Blo 1699550 4306355 := bstep (se 1 (by rfl) ⟨3229766, by rfl⟩ : syracuseStep 4306355 = 6459533) B6459533
theorem B1701303 : Blo 1699550 1701303 := bstep (se 1 (by rfl) ⟨1275977, by rfl⟩ : syracuseStep 1701303 = 2551955) B2551955
theorem B4363723 : Blo 1699550 4363723 := bstep (se 1 (by rfl) ⟨3272792, by rfl⟩ : syracuseStep 4363723 = 6545585) B6545585
theorem B1701323 : Blo 1699550 1701323 := bstep (se 1 (by rfl) ⟨1275992, by rfl⟩ : syracuseStep 1701323 = 2551985) B2551985
theorem B1701335 : Blo 1699550 1701335 := bstep (se 1 (by rfl) ⟨1276001, by rfl⟩ : syracuseStep 1701335 = 2552003) B2552003
theorem B1701355 : Blo 1699550 1701355 := bstep (se 1 (by rfl) ⟨1276016, by rfl⟩ : syracuseStep 1701355 = 2552033) B2552033
theorem B1701367 : Blo 1699550 1701367 := bstep (se 1 (by rfl) ⟨1276025, by rfl⟩ : syracuseStep 1701367 = 2552051) B2552051
theorem B2151947 : Blo 1699550 2151947 := bstep (se 1 (by rfl) ⟨1613960, by rfl⟩ : syracuseStep 2151947 = 3227921) B3227921
theorem B1701387 : Blo 1699550 1701387 := bstep (se 1 (by rfl) ⟨1276040, by rfl⟩ : syracuseStep 1701387 = 2552081) B2552081
theorem B1701399 : Blo 1699550 1701399 := bstep (se 1 (by rfl) ⟨1276049, by rfl⟩ : syracuseStep 1701399 = 2552099) B2552099
theorem B1701419 : Blo 1699550 1701419 := bstep (se 1 (by rfl) ⟨1276064, by rfl⟩ : syracuseStep 1701419 = 2552129) B2552129
theorem B4085299 : Blo 1699550 4085299 := bstep (se 1 (by rfl) ⟨3063974, by rfl⟩ : syracuseStep 4085299 = 6127949) B6127949
theorem B1701431 : Blo 1699550 1701431 := bstep (se 1 (by rfl) ⟨1276073, by rfl⟩ : syracuseStep 1701431 = 2552147) B2552147
theorem B1701451 : Blo 1699550 1701451 := bstep (se 1 (by rfl) ⟨1276088, by rfl⟩ : syracuseStep 1701451 = 2552177) B2552177
theorem B1701463 : Blo 1699550 1701463 := bstep (se 1 (by rfl) ⟨1276097, by rfl⟩ : syracuseStep 1701463 = 2552195) B2552195
theorem B1701483 : Blo 1699550 1701483 := bstep (se 1 (by rfl) ⟨1276112, by rfl⟩ : syracuseStep 1701483 = 2552225) B2552225
theorem B1701495 : Blo 1699550 1701495 := bstep (se 1 (by rfl) ⟨1276121, by rfl⟩ : syracuseStep 1701495 = 2552243) B2552243
theorem B1701515 : Blo 1699550 1701515 := bstep (se 1 (by rfl) ⟨1276136, by rfl⟩ : syracuseStep 1701515 = 2552273) B2552273
theorem B8607383 : Blo 1699550 8607383 := bstep (se 1 (by rfl) ⟨6455537, by rfl⟩ : syracuseStep 8607383 = 12911075) B12911075
theorem B2586263 : Blo 1699550 2586263 := bstep (se 1 (by rfl) ⟨1939697, by rfl⟩ : syracuseStep 2586263 = 3879395) B3879395
theorem B1701527 : Blo 1699550 1701527 := bstep (se 1 (by rfl) ⟨1276145, by rfl⟩ : syracuseStep 1701527 = 2552291) B2552291
theorem B1701547 : Blo 1699550 1701547 := bstep (se 1 (by rfl) ⟨1276160, by rfl⟩ : syracuseStep 1701547 = 2552321) B2552321
theorem B7263917 : Blo 1699550 7263917 := bstep (se 3 (by rfl) ⟨1361984, by rfl⟩ : syracuseStep 7263917 = 2723969) B2723969
theorem B5445323 : Blo 1699550 5445323 := bstep (se 1 (by rfl) ⟨4083992, by rfl⟩ : syracuseStep 5445323 = 8167985) B8167985
theorem B5740253 : Blo 1699550 5740253 := bstep (se 3 (by rfl) ⟨1076297, by rfl⟩ : syracuseStep 5740253 = 2152595) B2152595
theorem B4085569 : Blo 1699550 4085569 := bstep (se 2 (by rfl) ⟨1532088, by rfl⟩ : syracuseStep 4085569 = 3064177) B3064177
theorem B4306891 : Blo 1699550 4306891 := bstep (se 1 (by rfl) ⟨3230168, by rfl⟩ : syracuseStep 4306891 = 6460337) B6460337
theorem B5445721 : Blo 1699550 5445721 := bstep (se 2 (by rfl) ⟨2042145, by rfl⟩ : syracuseStep 5445721 = 4084291) B4084291
theorem B4307033 : Blo 1699550 4307033 := bstep (se 2 (by rfl) ⟨1615137, by rfl⟩ : syracuseStep 4307033 = 3230275) B3230275
theorem B12908645 : Blo 1699550 12908645 := bstep (se 4 (by rfl) ⟨1210185, by rfl⟩ : syracuseStep 12908645 = 2420371) B2420371
theorem B2152651 : Blo 1699550 2152651 := bstep (se 1 (by rfl) ⟨1614488, by rfl⟩ : syracuseStep 2152651 = 3228977) B3228977
theorem B12261725 : Blo 1699550 12261725 := bstep (se 3 (by rfl) ⟨2299073, by rfl⟩ : syracuseStep 12261725 = 4598147) B4598147
theorem B2152919 : Blo 1699550 2152919 := bstep (se 1 (by rfl) ⟨1614689, by rfl⟩ : syracuseStep 2152919 = 3229379) B3229379
theorem B3824153 : Blo 1699550 3824153 := bstep (se 2 (by rfl) ⟨1434057, by rfl⟩ : syracuseStep 3824153 = 2868115) B2868115
theorem B12909131 : Blo 1699550 12909131 := bstep (se 1 (by rfl) ⟨9681848, by rfl⟩ : syracuseStep 12909131 = 19363697) B19363697
theorem B3824243 : Blo 1699550 3824243 := bstep (se 1 (by rfl) ⟨2868182, by rfl⟩ : syracuseStep 3824243 = 5736365) B5736365
theorem B3824279 : Blo 1699550 3824279 := bstep (se 1 (by rfl) ⟨2868209, by rfl⟩ : syracuseStep 3824279 = 5736419) B5736419
theorem B4422347 : Blo 1699550 4422347 := bstep (se 1 (by rfl) ⟨3316760, by rfl⟩ : syracuseStep 4422347 = 6633521) B6633521
theorem B2071255 : Blo 1699550 2071255 := bstep (se 1 (by rfl) ⟨1553441, by rfl⟩ : syracuseStep 2071255 = 3106883) B3106883
theorem B6454019 : Blo 1699550 6454019 := bstep (se 1 (by rfl) ⟨4840514, by rfl⟩ : syracuseStep 6454019 = 9681029) B9681029
theorem B3824459 : Blo 1699550 3824459 := bstep (se 1 (by rfl) ⟨2868344, by rfl⟩ : syracuseStep 3824459 = 5736689) B5736689
theorem B5741387 : Blo 1699550 5741387 := bstep (se 1 (by rfl) ⟨4306040, by rfl⟩ : syracuseStep 5741387 = 8612081) B8612081
theorem B3824513 : Blo 1699550 3824513 := bstep (se 2 (by rfl) ⟨1434192, by rfl⟩ : syracuseStep 3824513 = 2868385) B2868385
theorem B6126509 : Blo 1699550 6126509 := bstep (se 3 (by rfl) ⟨1148720, by rfl⟩ : syracuseStep 6126509 = 2297441) B2297441
theorem B3226547 : Blo 1699550 3226547 := bstep (se 1 (by rfl) ⟨2419910, by rfl⟩ : syracuseStep 3226547 = 4839821) B4839821
theorem B4660247 : Blo 1699550 4660247 := bstep (se 1 (by rfl) ⟨3495185, by rfl⟩ : syracuseStep 4660247 = 6990371) B6990371
theorem B3062873 : Blo 1699550 3062873 := bstep (se 2 (by rfl) ⟨1148577, by rfl⟩ : syracuseStep 3062873 = 2297155) B2297155
theorem B3824729 : Blo 1699550 3824729 := bstep (se 2 (by rfl) ⟨1434273, by rfl⟩ : syracuseStep 3824729 = 2868547) B2868547
theorem B5741657 : Blo 1699550 5741657 := bstep (se 2 (by rfl) ⟨2153121, by rfl⟩ : syracuseStep 5741657 = 4306243) B4306243
theorem B3824819 : Blo 1699550 3824819 := bstep (se 1 (by rfl) ⟨2868614, by rfl⟩ : syracuseStep 3824819 = 5737229) B5737229
theorem B4840651 : Blo 1699550 4840651 := bstep (se 1 (by rfl) ⟨3630488, by rfl⟩ : syracuseStep 4840651 = 7260977) B7260977
theorem B6454475 : Blo 1699550 6454475 := bstep (se 1 (by rfl) ⟨4840856, by rfl⟩ : syracuseStep 6454475 = 9681713) B9681713
theorem B19643597 : Blo 1699550 19643597 := bstep (se 3 (by rfl) ⟨3683174, by rfl⟩ : syracuseStep 19643597 = 7366349) B7366349
theorem B3824855 : Blo 1699550 3824855 := bstep (se 1 (by rfl) ⟨2868641, by rfl⟩ : syracuseStep 3824855 = 5737283) B5737283
theorem B6544601 : Blo 1699550 6544601 := bstep (se 2 (by rfl) ⟨2454225, by rfl⟩ : syracuseStep 6544601 = 4908451) B4908451
theorem B5446963 : Blo 1699550 5446963 := bstep (se 1 (by rfl) ⟨4085222, by rfl⟩ : syracuseStep 5446963 = 8170445) B8170445
theorem B6126941 : Blo 1699550 6126941 := bstep (se 3 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 6126941 = 2297603) B2297603
theorem B9690461 : Blo 1699550 9690461 := bstep (se 3 (by rfl) ⟨1816961, by rfl⟩ : syracuseStep 9690461 = 3633923) B3633923
theorem B1965431 : Blo 1699550 1965431 := bstep (se 1 (by rfl) ⟨1474073, by rfl⟩ : syracuseStep 1965431 = 2948147) B2948147
theorem B3825035 : Blo 1699550 3825035 := bstep (se 1 (by rfl) ⟨2868776, by rfl⟩ : syracuseStep 3825035 = 5737553) B5737553
theorem B6454673 : Blo 1699550 6454673 := bstep (se 2 (by rfl) ⟨2420502, by rfl⟩ : syracuseStep 6454673 = 4841005) B4841005
theorem B3227033 : Blo 1699550 3227033 := bstep (se 2 (by rfl) ⟨1210137, by rfl⟩ : syracuseStep 3227033 = 2420275) B2420275
theorem B3825089 : Blo 1699550 3825089 := bstep (se 2 (by rfl) ⟨1434408, by rfl⟩ : syracuseStep 3825089 = 2868817) B2868817
theorem B11632193 : Blo 1699550 11632193 := bstep (se 2 (by rfl) ⟨4362072, by rfl⟩ : syracuseStep 11632193 = 8724145) B8724145
theorem B12918365 : Blo 1699550 12918365 := bstep (se 3 (by rfl) ⟨2422193, by rfl⟩ : syracuseStep 12918365 = 4844387) B4844387
theorem B3825305 : Blo 1699550 3825305 := bstep (se 2 (by rfl) ⟨1434489, by rfl⟩ : syracuseStep 3825305 = 2868979) B2868979
theorem B4841153 : Blo 1699550 4841153 := bstep (se 2 (by rfl) ⟨1815432, by rfl⟩ : syracuseStep 4841153 = 3630865) B3630865
theorem B14524109 : Blo 1699550 14524109 := bstep (se 3 (by rfl) ⟨2723270, by rfl⟩ : syracuseStep 14524109 = 5446541) B5446541
theorem B3825395 : Blo 1699550 3825395 := bstep (se 1 (by rfl) ⟨2869046, by rfl⟩ : syracuseStep 3825395 = 5738093) B5738093
theorem B3825431 : Blo 1699550 3825431 := bstep (se 1 (by rfl) ⟨2869073, by rfl⟩ : syracuseStep 3825431 = 5738147) B5738147
theorem B6897431 : Blo 1699550 6897431 := bstep (se 1 (by rfl) ⟨5173073, by rfl⟩ : syracuseStep 6897431 = 10346147) B10346147
theorem B5742359 : Blo 1699550 5742359 := bstep (se 1 (by rfl) ⟨4306769, by rfl⟩ : syracuseStep 5742359 = 8613539) B8613539
theorem B110264165 : Blo 1699550 110264165 := bstep (se 4 (by rfl) ⟨10337265, by rfl⟩ : syracuseStep 110264165 = 20674531) B20674531
theorem B39264101 : Blo 1699550 39264101 := bstep (se 4 (by rfl) ⟨3681009, by rfl⟩ : syracuseStep 39264101 = 7362019) B7362019
theorem B3825611 : Blo 1699550 3825611 := bstep (se 1 (by rfl) ⟨2869208, by rfl⟩ : syracuseStep 3825611 = 5738417) B5738417
theorem B6897611 : Blo 1699550 6897611 := bstep (se 1 (by rfl) ⟨5173208, by rfl⟩ : syracuseStep 6897611 = 10346417) B10346417
theorem B3227663 : Blo 1699550 3227663 := bstep (se 1 (by rfl) ⟨2420747, by rfl⟩ : syracuseStep 3227663 = 4841495) B4841495
theorem B7462979 : Blo 1699550 7462979 := bstep (se 1 (by rfl) ⟨5597234, by rfl⟩ : syracuseStep 7462979 = 11194469) B11194469
theorem B8167661 : Blo 1699550 8167661 := bstep (se 3 (by rfl) ⟨1531436, by rfl⟩ : syracuseStep 8167661 = 3062873) B3062873
theorem B3825935 : Blo 1699550 3825935 := bstep (se 1 (by rfl) ⟨2869451, by rfl⟩ : syracuseStep 3825935 = 5738903) B5738903
theorem B5169437 : Blo 1699550 5169437 := bstep (se 3 (by rfl) ⟨969269, by rfl⟩ : syracuseStep 5169437 = 1938539) B1938539
theorem B3825953 : Blo 1699550 3825953 := bstep (se 2 (by rfl) ⟨1434732, by rfl⟩ : syracuseStep 3825953 = 2869465) B2869465
theorem B8610137 : Blo 1699550 8610137 := bstep (se 2 (by rfl) ⟨3228801, by rfl⟩ : syracuseStep 8610137 = 6457603) B6457603
theorem B3826295 : Blo 1699550 3826295 := bstep (se 1 (by rfl) ⟨2869721, by rfl⟩ : syracuseStep 3826295 = 5739443) B5739443
theorem B3826475 : Blo 1699550 3826475 := bstep (se 1 (by rfl) ⟨2869856, by rfl⟩ : syracuseStep 3826475 = 5739713) B5739713
theorem B20685719 : Blo 1699550 20685719 := bstep (se 1 (by rfl) ⟨15514289, by rfl⟩ : syracuseStep 20685719 = 31028579) B31028579
theorem B2868169 : Blo 1699550 2868169 := bstep (se 2 (by rfl) ⟨1075563, by rfl⟩ : syracuseStep 2868169 = 2151127) B2151127
theorem B2761673 : Blo 1699550 2761673 := bstep (se 2 (by rfl) ⟨1035627, by rfl⟩ : syracuseStep 2761673 = 2071255) B2071255
theorem B4842497 : Blo 1699550 4842497 := bstep (se 2 (by rfl) ⟨1815936, by rfl⟩ : syracuseStep 4842497 = 3631873) B3631873
theorem B3630113 : Blo 1699550 3630113 := bstep (se 2 (by rfl) ⟨1361292, by rfl⟩ : syracuseStep 3630113 = 2722585) B2722585
theorem B4842611 : Blo 1699550 4842611 := bstep (se 1 (by rfl) ⟨3631958, by rfl⟩ : syracuseStep 4842611 = 7263917) B7263917
theorem B3630215 : Blo 1699550 3630215 := bstep (se 1 (by rfl) ⟨2722661, by rfl⟩ : syracuseStep 3630215 = 5445323) B5445323
theorem B3826835 : Blo 1699550 3826835 := bstep (se 1 (by rfl) ⟨2870126, by rfl⟩ : syracuseStep 3826835 = 5740253) B5740253
theorem B3826889 : Blo 1699550 3826889 := bstep (se 2 (by rfl) ⟨1435083, by rfl⟩ : syracuseStep 3826889 = 2870167) B2870167
theorem B9684197 : Blo 1699550 9684197 := bstep (se 4 (by rfl) ⟨907893, by rfl⟩ : syracuseStep 9684197 = 1815787) B1815787
theorem B3229075 : Blo 1699550 3229075 := bstep (se 1 (by rfl) ⟨2421806, by rfl⟩ : syracuseStep 3229075 = 4843613) B4843613
theorem B52389305 : Blo 1699550 52389305 := bstep (se 2 (by rfl) ⟨19645989, by rfl⟩ : syracuseStep 52389305 = 39291979) B39291979
theorem B4842953 : Blo 1699550 4842953 := bstep (se 2 (by rfl) ⟨1816107, by rfl⟩ : syracuseStep 4842953 = 3632215) B3632215
theorem B3065359 : Blo 1699550 3065359 := bstep (se 1 (by rfl) ⟨2299019, by rfl⟩ : syracuseStep 3065359 = 4598039) B4598039
theorem B7562813 : Blo 1699550 7562813 := bstep (se 3 (by rfl) ⟨1418027, by rfl⟩ : syracuseStep 7562813 = 2836055) B2836055
theorem B3229303 : Blo 1699550 3229303 := bstep (se 1 (by rfl) ⟨2421977, by rfl⟩ : syracuseStep 3229303 = 4843955) B4843955
theorem B2868871 : Blo 1699550 2868871 := bstep (se 1 (by rfl) ⟨2151653, by rfl⟩ : syracuseStep 2868871 = 4303307) B4303307
theorem B2549435 : Blo 1699550 2549435 := bstep (se 1 (by rfl) ⟨1912076, by rfl⟩ : syracuseStep 2549435 = 3824153) B3824153
theorem B2549495 : Blo 1699550 2549495 := bstep (se 1 (by rfl) ⟨1912121, by rfl⟩ : syracuseStep 2549495 = 3824243) B3824243
theorem B2549519 : Blo 1699550 2549519 := bstep (se 1 (by rfl) ⟨1912139, by rfl⟩ : syracuseStep 2549519 = 3824279) B3824279
theorem B6457103 : Blo 1699550 6457103 := bstep (se 1 (by rfl) ⟨4842827, by rfl⟩ : syracuseStep 6457103 = 9685655) B9685655
theorem B2549561 : Blo 1699550 2549561 := bstep (se 2 (by rfl) ⟨956085, by rfl⟩ : syracuseStep 2549561 = 1912171) B1912171
theorem B4302679 : Blo 1699550 4302679 := bstep (se 1 (by rfl) ⟨3227009, by rfl⟩ : syracuseStep 4302679 = 6454019) B6454019
theorem B2549639 : Blo 1699550 2549639 := bstep (se 1 (by rfl) ⟨1912229, by rfl⟩ : syracuseStep 2549639 = 3824459) B3824459
theorem B3827591 : Blo 1699550 3827591 := bstep (se 1 (by rfl) ⟨2870693, by rfl⟩ : syracuseStep 3827591 = 5741387) B5741387
theorem B2549675 : Blo 1699550 2549675 := bstep (se 1 (by rfl) ⟨1912256, by rfl⟩ : syracuseStep 2549675 = 3824513) B3824513
theorem B2549705 : Blo 1699550 2549705 := bstep (se 2 (by rfl) ⟨956139, by rfl⟩ : syracuseStep 2549705 = 1912279) B1912279
theorem B3106831 : Blo 1699550 3106831 := bstep (se 1 (by rfl) ⟨2330123, by rfl⟩ : syracuseStep 3106831 = 4660247) B4660247
theorem B16566295 : Blo 1699550 16566295 := bstep (se 1 (by rfl) ⟨12424721, by rfl⟩ : syracuseStep 16566295 = 24849443) B24849443
theorem B2549819 : Blo 1699550 2549819 := bstep (se 1 (by rfl) ⟨1912364, by rfl⟩ : syracuseStep 2549819 = 3824729) B3824729
theorem B3827771 : Blo 1699550 3827771 := bstep (se 1 (by rfl) ⟨2870828, by rfl⟩ : syracuseStep 3827771 = 5741657) B5741657
theorem B18393149 : Blo 1699550 18393149 := bstep (se 3 (by rfl) ⟨3448715, by rfl⟩ : syracuseStep 18393149 = 6897431) B6897431
theorem B2549879 : Blo 1699550 2549879 := bstep (se 1 (by rfl) ⟨1912409, by rfl⟩ : syracuseStep 2549879 = 3824819) B3824819
theorem B4302983 : Blo 1699550 4302983 := bstep (se 1 (by rfl) ⟨3227237, by rfl⟩ : syracuseStep 4302983 = 6454475) B6454475
theorem B2328719 : Blo 1699550 2328719 := bstep (se 1 (by rfl) ⟨1746539, by rfl⟩ : syracuseStep 2328719 = 3493079) B3493079
theorem B2549903 : Blo 1699550 2549903 := bstep (se 1 (by rfl) ⟨1912427, by rfl⟩ : syracuseStep 2549903 = 3824855) B3824855
theorem B2549945 : Blo 1699550 2549945 := bstep (se 2 (by rfl) ⟨956229, by rfl⟩ : syracuseStep 2549945 = 1912459) B1912459
theorem B3827897 : Blo 1699550 3827897 := bstep (se 2 (by rfl) ⟨1435461, by rfl⟩ : syracuseStep 3827897 = 2870923) B2870923
theorem B2550023 : Blo 1699550 2550023 := bstep (se 1 (by rfl) ⟨1912517, by rfl⟩ : syracuseStep 2550023 = 3825035) B3825035
theorem B4303115 : Blo 1699550 4303115 := bstep (se 1 (by rfl) ⟨3227336, by rfl⟩ : syracuseStep 4303115 = 6454673) B6454673
theorem B2869519 : Blo 1699550 2869519 := bstep (se 1 (by rfl) ⟨2152139, by rfl⟩ : syracuseStep 2869519 = 4304279) B4304279
theorem B2550059 : Blo 1699550 2550059 := bstep (se 1 (by rfl) ⟨1912544, by rfl⟩ : syracuseStep 2550059 = 3825089) B3825089
theorem B2550089 : Blo 1699550 2550089 := bstep (se 2 (by rfl) ⟨956283, by rfl⟩ : syracuseStep 2550089 = 1912567) B1912567
theorem B15518087 : Blo 1699550 15518087 := bstep (se 1 (by rfl) ⟨11638565, by rfl⟩ : syracuseStep 15518087 = 23277131) B23277131
theorem B5736851 : Blo 1699550 5736851 := bstep (se 1 (by rfl) ⟨4302638, by rfl⟩ : syracuseStep 5736851 = 8605277) B8605277
theorem B8612243 : Blo 1699550 8612243 := bstep (se 1 (by rfl) ⟨6459182, by rfl⟩ : syracuseStep 8612243 = 12918365) B12918365
theorem B2550203 : Blo 1699550 2550203 := bstep (se 1 (by rfl) ⟨1912652, by rfl⟩ : syracuseStep 2550203 = 3825305) B3825305
theorem B2550263 : Blo 1699550 2550263 := bstep (se 1 (by rfl) ⟨1912697, by rfl⟩ : syracuseStep 2550263 = 3825395) B3825395
theorem B2550287 : Blo 1699550 2550287 := bstep (se 1 (by rfl) ⟨1912715, by rfl⟩ : syracuseStep 2550287 = 3825431) B3825431
theorem B3828239 : Blo 1699550 3828239 := bstep (se 1 (by rfl) ⟨2871179, by rfl⟩ : syracuseStep 3828239 = 5742359) B5742359
theorem B3828257 : Blo 1699550 3828257 := bstep (se 2 (by rfl) ⟨1435596, by rfl⟩ : syracuseStep 3828257 = 2871193) B2871193
theorem B2550329 : Blo 1699550 2550329 := bstep (se 2 (by rfl) ⟨956373, by rfl⟩ : syracuseStep 2550329 = 1912747) B1912747
theorem B73509443 : Blo 1699550 73509443 := bstep (se 1 (by rfl) ⟨55132082, by rfl⟩ : syracuseStep 73509443 = 110264165) B110264165
theorem B26176067 : Blo 1699550 26176067 := bstep (se 1 (by rfl) ⟨19632050, by rfl⟩ : syracuseStep 26176067 = 39264101) B39264101
theorem B2550407 : Blo 1699550 2550407 := bstep (se 1 (by rfl) ⟨1912805, by rfl⟩ : syracuseStep 2550407 = 3825611) B3825611
theorem B4598407 : Blo 1699550 4598407 := bstep (se 1 (by rfl) ⟨3448805, by rfl⟩ : syracuseStep 4598407 = 6897611) B6897611
theorem B2550443 : Blo 1699550 2550443 := bstep (se 1 (by rfl) ⟨1912832, by rfl⟩ : syracuseStep 2550443 = 3825665) B3825665
theorem B19376819 : Blo 1699550 19376819 := bstep (se 1 (by rfl) ⟨14532614, by rfl⟩ : syracuseStep 19376819 = 29065229) B29065229
theorem B2550473 : Blo 1699550 2550473 := bstep (se 2 (by rfl) ⟨956427, by rfl⟩ : syracuseStep 2550473 = 1912855) B1912855
theorem B4303631 : Blo 1699550 4303631 := bstep (se 1 (by rfl) ⟨3227723, by rfl⟩ : syracuseStep 4303631 = 6455447) B6455447
theorem B7260961 : Blo 1699550 7260961 := bstep (se 2 (by rfl) ⟨2722860, by rfl⟩ : syracuseStep 7260961 = 5445721) B5445721
theorem B2870059 : Blo 1699550 2870059 := bstep (se 1 (by rfl) ⟨2152544, by rfl⟩ : syracuseStep 2870059 = 4305089) B4305089
theorem B8604467 : Blo 1699550 8604467 := bstep (se 1 (by rfl) ⟨6453350, by rfl⟩ : syracuseStep 8604467 = 12906701) B12906701
theorem B2550587 : Blo 1699550 2550587 := bstep (se 1 (by rfl) ⟨1912940, by rfl⟩ : syracuseStep 2550587 = 3825881) B3825881
theorem B2550647 : Blo 1699550 2550647 := bstep (se 1 (by rfl) ⟨1912985, by rfl⟩ : syracuseStep 2550647 = 3825971) B3825971
theorem B2550671 : Blo 1699550 2550671 := bstep (se 1 (by rfl) ⟨1913003, by rfl⟩ : syracuseStep 2550671 = 3826007) B3826007
theorem B4303763 : Blo 1699550 4303763 := bstep (se 1 (by rfl) ⟨3227822, by rfl⟩ : syracuseStep 4303763 = 6455645) B6455645
theorem B2550713 : Blo 1699550 2550713 := bstep (se 2 (by rfl) ⟨956517, by rfl⟩ : syracuseStep 2550713 = 1913035) B1913035
theorem B2870201 : Blo 1699550 2870201 := bstep (se 2 (by rfl) ⟨1076325, by rfl⟩ : syracuseStep 2870201 = 2152651) B2152651
theorem B16346117 : Blo 1699550 16346117 := bstep (se 4 (by rfl) ⟨1532448, by rfl⟩ : syracuseStep 16346117 = 3064897) B3064897
theorem B2550791 : Blo 1699550 2550791 := bstep (se 1 (by rfl) ⟨1913093, by rfl⟩ : syracuseStep 2550791 = 3826187) B3826187
theorem B2550827 : Blo 1699550 2550827 := bstep (se 1 (by rfl) ⟨1913120, by rfl⟩ : syracuseStep 2550827 = 3826241) B3826241
theorem B14519357 : Blo 1699550 14519357 := bstep (se 3 (by rfl) ⟨2722379, by rfl⟩ : syracuseStep 14519357 = 5444759) B5444759
theorem B2550857 : Blo 1699550 2550857 := bstep (se 2 (by rfl) ⟨956571, by rfl⟩ : syracuseStep 2550857 = 1913143) B1913143
theorem B8604791 : Blo 1699550 8604791 := bstep (se 1 (by rfl) ⟨6453593, by rfl⟩ : syracuseStep 8604791 = 12907187) B12907187
theorem B4598903 : Blo 1699550 4598903 := bstep (se 1 (by rfl) ⟨3449177, by rfl⟩ : syracuseStep 4598903 = 6898355) B6898355
theorem B2182315 : Blo 1699550 2182315 := bstep (se 1 (by rfl) ⟨1636736, by rfl⟩ : syracuseStep 2182315 = 3273473) B3273473
theorem B2550971 : Blo 1699550 2550971 := bstep (se 1 (by rfl) ⟨1913228, by rfl⟩ : syracuseStep 2550971 = 3826457) B3826457
theorem B2551031 : Blo 1699550 2551031 := bstep (se 1 (by rfl) ⟨1913273, by rfl⟩ : syracuseStep 2551031 = 3826547) B3826547
theorem B8170753 : Blo 1699550 8170753 := bstep (se 2 (by rfl) ⟨3064032, by rfl⟩ : syracuseStep 8170753 = 6128065) B6128065
theorem B5172491 : Blo 1699550 5172491 := bstep (se 1 (by rfl) ⟨3879368, by rfl⟩ : syracuseStep 5172491 = 7758737) B7758737
theorem B2551055 : Blo 1699550 2551055 := bstep (se 1 (by rfl) ⟨1913291, by rfl⟩ : syracuseStep 2551055 = 3826583) B3826583
theorem B4844843 : Blo 1699550 4844843 := bstep (se 1 (by rfl) ⟨3633632, by rfl⟩ : syracuseStep 4844843 = 7267265) B7267265
theorem B2551097 : Blo 1699550 2551097 := bstep (se 2 (by rfl) ⟨956661, by rfl⟩ : syracuseStep 2551097 = 1913323) B1913323
theorem B9194867 : Blo 1699550 9194867 := bstep (se 1 (by rfl) ⟨6896150, by rfl⟩ : syracuseStep 9194867 = 13792301) B13792301
theorem B5172599 : Blo 1699550 5172599 := bstep (se 1 (by rfl) ⟨3879449, by rfl⟩ : syracuseStep 5172599 = 7758899) B7758899
theorem B16788871 : Blo 1699550 16788871 := bstep (se 1 (by rfl) ⟨12591653, by rfl⟩ : syracuseStep 16788871 = 25183307) B25183307
theorem B2551175 : Blo 1699550 2551175 := bstep (se 1 (by rfl) ⟨1913381, by rfl⟩ : syracuseStep 2551175 = 3826763) B3826763
theorem B1912207 : Blo 1699550 1912207 := bstep (se 1 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 1912207 = 2868311) B2868311
theorem B2551211 : Blo 1699550 2551211 := bstep (se 1 (by rfl) ⟨1913408, by rfl⟩ : syracuseStep 2551211 = 3826817) B3826817
theorem B2420155 : Blo 1699550 2420155 := bstep (se 1 (by rfl) ⟨1815116, by rfl⟩ : syracuseStep 2420155 = 3630233) B3630233
theorem B2551241 : Blo 1699550 2551241 := bstep (se 2 (by rfl) ⟨956715, by rfl⟩ : syracuseStep 2551241 = 1913431) B1913431
theorem B18394573 : Blo 1699550 18394573 := bstep (se 3 (by rfl) ⟨3448982, by rfl⟩ : syracuseStep 18394573 = 6897965) B6897965
theorem B4845071 : Blo 1699550 4845071 := bstep (se 1 (by rfl) ⟨3633803, by rfl⟩ : syracuseStep 4845071 = 7267607) B7267607
theorem B2551355 : Blo 1699550 2551355 := bstep (se 1 (by rfl) ⟨1913516, by rfl⟩ : syracuseStep 2551355 = 3827033) B3827033
theorem B16338509 : Blo 1699550 16338509 := bstep (se 3 (by rfl) ⟨3063470, by rfl⟩ : syracuseStep 16338509 = 6126941) B6126941
theorem B46542437 : Blo 1699550 46542437 := bstep (se 4 (by rfl) ⟨4363353, by rfl⟩ : syracuseStep 46542437 = 8726707) B8726707
theorem B2551415 : Blo 1699550 2551415 := bstep (se 1 (by rfl) ⟨1913561, by rfl⟩ : syracuseStep 2551415 = 3827123) B3827123
theorem B2870903 : Blo 1699550 2870903 := bstep (se 1 (by rfl) ⟨2153177, by rfl⟩ : syracuseStep 2870903 = 4306355) B4306355
theorem B2551439 : Blo 1699550 2551439 := bstep (se 1 (by rfl) ⟨1913579, by rfl⟩ : syracuseStep 2551439 = 3827159) B3827159
theorem B2551481 : Blo 1699550 2551481 := bstep (se 2 (by rfl) ⟨956805, by rfl⟩ : syracuseStep 2551481 = 1913611) B1913611
theorem B17936129 : Blo 1699550 17936129 := bstep (se 2 (by rfl) ⟨6726048, by rfl⟩ : syracuseStep 17936129 = 13452097) B13452097
theorem B1699591 : Blo 1699550 1699591 := bstep (se 1 (by rfl) ⟨1274693, by rfl⟩ : syracuseStep 1699591 = 2549387) B2549387
theorem B2551559 : Blo 1699550 2551559 := bstep (se 1 (by rfl) ⟨1913669, by rfl⟩ : syracuseStep 2551559 = 3827339) B3827339
theorem B1699599 : Blo 1699550 1699599 := bstep (se 1 (by rfl) ⟨1274699, by rfl⟩ : syracuseStep 1699599 = 2549399) B2549399
theorem B5738255 : Blo 1699550 5738255 := bstep (se 1 (by rfl) ⟨4303691, by rfl⟩ : syracuseStep 5738255 = 8607383) B8607383
theorem B2551595 : Blo 1699550 2551595 := bstep (se 1 (by rfl) ⟨1913696, by rfl⟩ : syracuseStep 2551595 = 3827393) B3827393
theorem B1699643 : Blo 1699550 1699643 := bstep (se 1 (by rfl) ⟨1274732, by rfl⟩ : syracuseStep 1699643 = 2549465) B2549465
theorem B2551625 : Blo 1699550 2551625 := bstep (se 2 (by rfl) ⟨956859, by rfl⟩ : syracuseStep 2551625 = 1913719) B1913719
theorem B2420599 : Blo 1699550 2420599 := bstep (se 1 (by rfl) ⟨1815449, by rfl⟩ : syracuseStep 2420599 = 3630899) B3630899
theorem B1699719 : Blo 1699550 1699719 := bstep (se 1 (by rfl) ⟨1274789, by rfl⟩ : syracuseStep 1699719 = 2549579) B2549579
theorem B1912711 : Blo 1699550 1912711 := bstep (se 1 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 1912711 = 2869067) B2869067
theorem B1699727 : Blo 1699550 1699727 := bstep (se 1 (by rfl) ⟨1274795, by rfl⟩ : syracuseStep 1699727 = 2549591) B2549591
theorem B1699771 : Blo 1699550 1699771 := bstep (se 1 (by rfl) ⟨1274828, by rfl⟩ : syracuseStep 1699771 = 2549657) B2549657
theorem B2551739 : Blo 1699550 2551739 := bstep (se 1 (by rfl) ⟨1913804, by rfl⟩ : syracuseStep 2551739 = 3827609) B3827609
theorem B2551799 : Blo 1699550 2551799 := bstep (se 1 (by rfl) ⟨1913849, by rfl⟩ : syracuseStep 2551799 = 3827699) B3827699
theorem B4304897 : Blo 1699550 4304897 := bstep (se 2 (by rfl) ⟨1614336, by rfl⟩ : syracuseStep 4304897 = 3228673) B3228673
theorem B1699847 : Blo 1699550 1699847 := bstep (se 1 (by rfl) ⟨1274885, by rfl⟩ : syracuseStep 1699847 = 2549771) B2549771
theorem B1699855 : Blo 1699550 1699855 := bstep (se 1 (by rfl) ⟨1274891, by rfl⟩ : syracuseStep 1699855 = 2549783) B2549783
theorem B2551823 : Blo 1699550 2551823 := bstep (se 1 (by rfl) ⟨1913867, by rfl⟩ : syracuseStep 2551823 = 3827735) B3827735
theorem B5738525 : Blo 1699550 5738525 := bstep (se 3 (by rfl) ⟨1075973, by rfl⟩ : syracuseStep 5738525 = 2151947) B2151947
theorem B2551865 : Blo 1699550 2551865 := bstep (se 2 (by rfl) ⟨956949, by rfl⟩ : syracuseStep 2551865 = 1913899) B1913899
theorem B1699899 : Blo 1699550 1699899 := bstep (se 1 (by rfl) ⟨1274924, by rfl⟩ : syracuseStep 1699899 = 2549849) B2549849
theorem B1912891 : Blo 1699550 1912891 := bstep (se 1 (by rfl) ⟨1434668, by rfl⟩ : syracuseStep 1912891 = 2869337) B2869337
theorem B2871355 : Blo 1699550 2871355 := bstep (se 1 (by rfl) ⟨2153516, by rfl⟩ : syracuseStep 2871355 = 4307033) B4307033
theorem B8605763 : Blo 1699550 8605763 := bstep (se 1 (by rfl) ⟨6454322, by rfl⟩ : syracuseStep 8605763 = 12908645) B12908645
theorem B1699975 : Blo 1699550 1699975 := bstep (se 1 (by rfl) ⟨1274981, by rfl⟩ : syracuseStep 1699975 = 2549963) B2549963
theorem B2551943 : Blo 1699550 2551943 := bstep (se 1 (by rfl) ⟨1913957, by rfl⟩ : syracuseStep 2551943 = 3827915) B3827915
theorem B1699983 : Blo 1699550 1699983 := bstep (se 1 (by rfl) ⟨1274987, by rfl⟩ : syracuseStep 1699983 = 2549975) B2549975
theorem B2551979 : Blo 1699550 2551979 := bstep (se 1 (by rfl) ⟨1913984, by rfl⟩ : syracuseStep 2551979 = 3827969) B3827969
theorem B1700027 : Blo 1699550 1700027 := bstep (se 1 (by rfl) ⟨1275020, by rfl⟩ : syracuseStep 1700027 = 2550041) B2550041
theorem B2552009 : Blo 1699550 2552009 := bstep (se 2 (by rfl) ⟨957003, by rfl⟩ : syracuseStep 2552009 = 1914007) B1914007
theorem B1700103 : Blo 1699550 1700103 := bstep (se 1 (by rfl) ⟨1275077, by rfl⟩ : syracuseStep 1700103 = 2550155) B2550155
theorem B1700111 : Blo 1699550 1700111 := bstep (se 1 (by rfl) ⟨1275083, by rfl⟩ : syracuseStep 1700111 = 2550167) B2550167
theorem B7860539 : Blo 1699550 7860539 := bstep (se 1 (by rfl) ⟨5895404, by rfl⟩ : syracuseStep 7860539 = 11790809) B11790809
theorem B1700155 : Blo 1699550 1700155 := bstep (se 1 (by rfl) ⟨1275116, by rfl⟩ : syracuseStep 1700155 = 2550233) B2550233
theorem B2552123 : Blo 1699550 2552123 := bstep (se 1 (by rfl) ⟨1914092, by rfl⟩ : syracuseStep 2552123 = 3828185) B3828185
theorem B4305271 : Blo 1699550 4305271 := bstep (se 1 (by rfl) ⟨3228953, by rfl⟩ : syracuseStep 4305271 = 6457907) B6457907
theorem B2552183 : Blo 1699550 2552183 := bstep (se 1 (by rfl) ⟨1914137, by rfl⟩ : syracuseStep 2552183 = 3828275) B3828275
theorem B8606087 : Blo 1699550 8606087 := bstep (se 1 (by rfl) ⟨6454565, by rfl⟩ : syracuseStep 8606087 = 12909131) B12909131
theorem B1700231 : Blo 1699550 1700231 := bstep (se 1 (by rfl) ⟨1275173, by rfl⟩ : syracuseStep 1700231 = 2550347) B2550347
theorem B1700239 : Blo 1699550 1700239 := bstep (se 1 (by rfl) ⟨1275179, by rfl⟩ : syracuseStep 1700239 = 2550359) B2550359
theorem B2552207 : Blo 1699550 2552207 := bstep (se 1 (by rfl) ⟨1914155, by rfl⟩ : syracuseStep 2552207 = 3828311) B3828311
theorem B47149459 : Blo 1699550 47149459 := bstep (se 1 (by rfl) ⟨35362094, by rfl⟩ : syracuseStep 47149459 = 70724189) B70724189
theorem B7262617 : Blo 1699550 7262617 := bstep (se 2 (by rfl) ⟨2723481, by rfl⟩ : syracuseStep 7262617 = 5446963) B5446963
theorem B2552249 : Blo 1699550 2552249 := bstep (se 2 (by rfl) ⟨957093, by rfl⟩ : syracuseStep 2552249 = 1914187) B1914187
theorem B1814971 : Blo 1699550 1814971 := bstep (se 1 (by rfl) ⟨1361228, by rfl⟩ : syracuseStep 1814971 = 2722457) B2722457
theorem B1700283 : Blo 1699550 1700283 := bstep (se 1 (by rfl) ⟨1275212, by rfl⟩ : syracuseStep 1700283 = 2550425) B2550425
theorem B1700359 : Blo 1699550 1700359 := bstep (se 1 (by rfl) ⟨1275269, by rfl⟩ : syracuseStep 1700359 = 2550539) B2550539
theorem B1700367 : Blo 1699550 1700367 := bstep (se 1 (by rfl) ⟨1275275, by rfl⟩ : syracuseStep 1700367 = 2550551) B2550551
theorem B1913359 : Blo 1699550 1913359 := bstep (se 1 (by rfl) ⟨1435019, by rfl⟩ : syracuseStep 1913359 = 2870039) B2870039
theorem B1700411 : Blo 1699550 1700411 := bstep (se 1 (by rfl) ⟨1275308, by rfl⟩ : syracuseStep 1700411 = 2550617) B2550617
theorem B4084339 : Blo 1699550 4084339 := bstep (se 1 (by rfl) ⟨3063254, by rfl⟩ : syracuseStep 4084339 = 6126509) B6126509
theorem B2151031 : Blo 1699550 2151031 := bstep (se 1 (by rfl) ⟨1613273, by rfl⟩ : syracuseStep 2151031 = 3226547) B3226547
theorem B1700487 : Blo 1699550 1700487 := bstep (se 1 (by rfl) ⟨1275365, by rfl⟩ : syracuseStep 1700487 = 2550731) B2550731
theorem B1700495 : Blo 1699550 1700495 := bstep (se 1 (by rfl) ⟨1275371, by rfl⟩ : syracuseStep 1700495 = 2550743) B2550743
theorem B2421419 : Blo 1699550 2421419 := bstep (se 1 (by rfl) ⟨1816064, by rfl⟩ : syracuseStep 2421419 = 3632129) B3632129
theorem B1700539 : Blo 1699550 1700539 := bstep (se 1 (by rfl) ⟨1275404, by rfl⟩ : syracuseStep 1700539 = 2550809) B2550809
theorem B1700615 : Blo 1699550 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B14725903 : Blo 1699550 14725903 := bstep (se 1 (by rfl) ⟨11044427, by rfl⟩ : syracuseStep 14725903 = 22088855) B22088855
theorem B1700623 : Blo 1699550 1700623 := bstep (se 1 (by rfl) ⟨1275467, by rfl⟩ : syracuseStep 1700623 = 2550935) B2550935
theorem B4305707 : Blo 1699550 4305707 := bstep (se 1 (by rfl) ⟨3229280, by rfl⟩ : syracuseStep 4305707 = 6458561) B6458561
theorem B13095731 : Blo 1699550 13095731 := bstep (se 1 (by rfl) ⟨9821798, by rfl⟩ : syracuseStep 13095731 = 19643597) B19643597
theorem B4363067 : Blo 1699550 4363067 := bstep (se 1 (by rfl) ⟨3272300, by rfl⟩ : syracuseStep 4363067 = 6544601) B6544601
theorem B1700667 : Blo 1699550 1700667 := bstep (se 1 (by rfl) ⟨1275500, by rfl⟩ : syracuseStep 1700667 = 2551001) B2551001
theorem B1700743 : Blo 1699550 1700743 := bstep (se 1 (by rfl) ⟨1275557, by rfl⟩ : syracuseStep 1700743 = 2551115) B2551115
theorem B1700751 : Blo 1699550 1700751 := bstep (se 1 (by rfl) ⟨1275563, by rfl⟩ : syracuseStep 1700751 = 2551127) B2551127
theorem B6460307 : Blo 1699550 6460307 := bstep (se 1 (by rfl) ⟨4845230, by rfl⟩ : syracuseStep 6460307 = 9690461) B9690461
theorem B5313433 : Blo 1699550 5313433 := bstep (se 2 (by rfl) ⟨1992537, by rfl⟩ : syracuseStep 5313433 = 3985075) B3985075
theorem B2151355 : Blo 1699550 2151355 := bstep (se 1 (by rfl) ⟨1613516, by rfl⟩ : syracuseStep 2151355 = 3227033) B3227033
theorem B1700795 : Blo 1699550 1700795 := bstep (se 1 (by rfl) ⟨1275596, by rfl⟩ : syracuseStep 1700795 = 2551193) B2551193
theorem B1700871 : Blo 1699550 1700871 := bstep (se 1 (by rfl) ⟨1275653, by rfl⟩ : syracuseStep 1700871 = 2551307) B2551307
theorem B1913863 : Blo 1699550 1913863 := bstep (se 1 (by rfl) ⟨1435397, by rfl⟩ : syracuseStep 1913863 = 2870795) B2870795
theorem B1700879 : Blo 1699550 1700879 := bstep (se 1 (by rfl) ⟨1275659, by rfl⟩ : syracuseStep 1700879 = 2551319) B2551319
theorem B7754795 : Blo 1699550 7754795 := bstep (se 1 (by rfl) ⟨5816096, by rfl⟩ : syracuseStep 7754795 = 11632193) B11632193
theorem B1700923 : Blo 1699550 1700923 := bstep (se 1 (by rfl) ⟨1275692, by rfl⟩ : syracuseStep 1700923 = 2551385) B2551385
theorem B6894659 : Blo 1699550 6894659 := bstep (se 1 (by rfl) ⟨5170994, by rfl⟩ : syracuseStep 6894659 = 10341989) B10341989
theorem B1700999 : Blo 1699550 1700999 := bstep (se 1 (by rfl) ⟨1275749, by rfl⟩ : syracuseStep 1700999 = 2551499) B2551499
theorem B1701007 : Blo 1699550 1701007 := bstep (se 1 (by rfl) ⟨1275755, by rfl⟩ : syracuseStep 1701007 = 2551511) B2551511
theorem B1701051 : Blo 1699550 1701051 := bstep (se 1 (by rfl) ⟨1275788, by rfl⟩ : syracuseStep 1701051 = 2551577) B2551577
theorem B1914043 : Blo 1699550 1914043 := bstep (se 1 (by rfl) ⟨1435532, by rfl⟩ : syracuseStep 1914043 = 2871065) B2871065
theorem B17700041 : Blo 1699550 17700041 := bstep (se 2 (by rfl) ⟨6637515, by rfl⟩ : syracuseStep 17700041 = 13275031) B13275031
theorem B1701127 : Blo 1699550 1701127 := bstep (se 1 (by rfl) ⟨1275845, by rfl⟩ : syracuseStep 1701127 = 2551691) B2551691
theorem B1701135 : Blo 1699550 1701135 := bstep (se 1 (by rfl) ⟨1275851, by rfl⟩ : syracuseStep 1701135 = 2551703) B2551703
theorem B1701179 : Blo 1699550 1701179 := bstep (se 1 (by rfl) ⟨1275884, by rfl⟩ : syracuseStep 1701179 = 2551769) B2551769
theorem B1701255 : Blo 1699550 1701255 := bstep (se 1 (by rfl) ⟨1275941, by rfl⟩ : syracuseStep 1701255 = 2551883) B2551883
theorem B2299279 : Blo 1699550 2299279 := bstep (se 1 (by rfl) ⟨1724459, by rfl⟩ : syracuseStep 2299279 = 3448919) B3448919
theorem B1701263 : Blo 1699550 1701263 := bstep (se 1 (by rfl) ⟨1275947, by rfl⟩ : syracuseStep 1701263 = 2551895) B2551895
theorem B5739929 : Blo 1699550 5739929 := bstep (se 2 (by rfl) ⟨2152473, by rfl⟩ : syracuseStep 5739929 = 4304947) B4304947
theorem B42505651 : Blo 1699550 42505651 := bstep (se 1 (by rfl) ⟨31879238, by rfl⟩ : syracuseStep 42505651 = 63758477) B63758477
theorem B9196985 : Blo 1699550 9196985 := bstep (se 2 (by rfl) ⟨3448869, by rfl⟩ : syracuseStep 9196985 = 6897739) B6897739
theorem B1701307 : Blo 1699550 1701307 := bstep (se 1 (by rfl) ⟨1275980, by rfl⟩ : syracuseStep 1701307 = 2551961) B2551961
theorem B2725321 : Blo 1699550 2725321 := bstep (se 2 (by rfl) ⟨1021995, by rfl⟩ : syracuseStep 2725321 = 2043991) B2043991
theorem B18388433 : Blo 1699550 18388433 := bstep (se 2 (by rfl) ⟨6895662, by rfl⟩ : syracuseStep 18388433 = 13791325) B13791325
theorem B1701383 : Blo 1699550 1701383 := bstep (se 1 (by rfl) ⟨1276037, by rfl⟩ : syracuseStep 1701383 = 2552075) B2552075
theorem B1701391 : Blo 1699550 1701391 := bstep (se 1 (by rfl) ⟨1276043, by rfl⟩ : syracuseStep 1701391 = 2552087) B2552087
theorem B1701435 : Blo 1699550 1701435 := bstep (se 1 (by rfl) ⟨1276076, by rfl⟩ : syracuseStep 1701435 = 2552153) B2552153
theorem B21788261 : Blo 1699550 21788261 := bstep (se 4 (by rfl) ⟨2042649, by rfl⟩ : syracuseStep 21788261 = 4085299) B4085299
theorem B32683621 : Blo 1699550 32683621 := bstep (se 4 (by rfl) ⟨3064089, by rfl⟩ : syracuseStep 32683621 = 6128179) B6128179
theorem B4306547 : Blo 1699550 4306547 := bstep (se 1 (by rfl) ⟨3229910, by rfl⟩ : syracuseStep 4306547 = 6459821) B6459821
theorem B9819767 : Blo 1699550 9819767 := bstep (se 1 (by rfl) ⟨7364825, by rfl⟩ : syracuseStep 9819767 = 14729651) B14729651
theorem B4306567 : Blo 1699550 4306567 := bstep (se 1 (by rfl) ⟨3229925, by rfl⟩ : syracuseStep 4306567 = 6459851) B6459851
theorem B1701511 : Blo 1699550 1701511 := bstep (se 1 (by rfl) ⟨1276133, by rfl⟩ : syracuseStep 1701511 = 2552267) B2552267
theorem B1701519 : Blo 1699550 1701519 := bstep (se 1 (by rfl) ⟨1276139, by rfl⟩ : syracuseStep 1701519 = 2552279) B2552279
theorem B6125327 : Blo 1699550 6125327 := bstep (se 1 (by rfl) ⟨4593995, by rfl⟩ : syracuseStep 6125327 = 9187991) B9187991
theorem B3192635 : Blo 1699550 3192635 := bstep (se 1 (by rfl) ⟨2394476, by rfl⟩ : syracuseStep 3192635 = 4788953) B4788953
theorem B9680755 : Blo 1699550 9680755 := bstep (se 1 (by rfl) ⟨7260566, by rfl⟩ : syracuseStep 9680755 = 14521133) B14521133
theorem B2152327 : Blo 1699550 2152327 := bstep (se 1 (by rfl) ⟨1614245, by rfl⟩ : syracuseStep 2152327 = 3228491) B3228491
theorem B4306841 : Blo 1699550 4306841 := bstep (se 2 (by rfl) ⟨1615065, by rfl⟩ : syracuseStep 4306841 = 3230131) B3230131
theorem B4307003 : Blo 1699550 4307003 := bstep (se 1 (by rfl) ⟨3230252, by rfl⟩ : syracuseStep 4307003 = 6460505) B6460505
theorem B5740631 : Blo 1699550 5740631 := bstep (se 1 (by rfl) ⟨4305473, by rfl⟩ : syracuseStep 5740631 = 8610947) B8610947
theorem B17701037 : Blo 1699550 17701037 := bstep (se 3 (by rfl) ⟨3318944, by rfl⟩ : syracuseStep 17701037 = 6637889) B6637889
theorem B2152747 : Blo 1699550 2152747 := bstep (se 1 (by rfl) ⟨1614560, by rfl⟩ : syracuseStep 2152747 = 3229121) B3229121
theorem B5241149 : Blo 1699550 5241149 := bstep (se 3 (by rfl) ⟨982715, by rfl⟩ : syracuseStep 5241149 = 1965431) B1965431
theorem B3823991 : Blo 1699550 3823991 := bstep (se 1 (by rfl) ⟨2867993, by rfl⟩ : syracuseStep 3823991 = 5735987) B5735987
theorem B2152975 : Blo 1699550 2152975 := bstep (se 1 (by rfl) ⟨1614731, by rfl⟩ : syracuseStep 2152975 = 3229463) B3229463
theorem B3824171 : Blo 1699550 3824171 := bstep (se 1 (by rfl) ⟨2868128, by rfl⟩ : syracuseStep 3824171 = 5736257) B5736257
theorem B5741117 : Blo 1699550 5741117 := bstep (se 3 (by rfl) ⟨1076459, by rfl⟩ : syracuseStep 5741117 = 2152919) B2152919
theorem B3824531 : Blo 1699550 3824531 := bstep (se 1 (by rfl) ⟨2868398, by rfl⟩ : syracuseStep 3824531 = 5736797) B5736797
theorem B8174483 : Blo 1699550 8174483 := bstep (se 1 (by rfl) ⟨6130862, by rfl⟩ : syracuseStep 8174483 = 12261725) B12261725
theorem B29047733 : Blo 1699550 29047733 := bstep (se 5 (by rfl) ⟨1361612, by rfl⟩ : syracuseStep 29047733 = 2723225) B2723225
theorem B6454201 : Blo 1699550 6454201 := bstep (se 2 (by rfl) ⟨2420325, by rfl⟩ : syracuseStep 6454201 = 4840651) B4840651
theorem B3824585 : Blo 1699550 3824585 := bstep (se 2 (by rfl) ⟨1434219, by rfl⟩ : syracuseStep 3824585 = 2868439) B2868439
theorem B6896701 : Blo 1699550 6896701 := bstep (se 3 (by rfl) ⟨1293131, by rfl⟩ : syracuseStep 6896701 = 2586263) B2586263
theorem B12418181 : Blo 1699550 12418181 := bstep (se 4 (by rfl) ⟨1164204, by rfl⟩ : syracuseStep 12418181 = 2328409) B2328409
theorem B2948231 : Blo 1699550 2948231 := bstep (se 1 (by rfl) ⟨2211173, by rfl⟩ : syracuseStep 2948231 = 4422347) B4422347
theorem B9682213 : Blo 1699550 9682213 := bstep (se 4 (by rfl) ⟨907707, by rfl⟩ : syracuseStep 9682213 = 1815415) B1815415
theorem B4840823 : Blo 1699550 4840823 := bstep (se 1 (by rfl) ⟨3630617, by rfl⟩ : syracuseStep 4840823 = 7261235) B7261235
theorem B36789835 : Blo 1699550 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B4087415 : Blo 1699550 4087415 := bstep (se 1 (by rfl) ⟨3065561, by rfl⟩ : syracuseStep 4087415 = 6131123) B6131123
theorem B3825287 : Blo 1699550 3825287 := bstep (se 1 (by rfl) ⟨2868965, by rfl⟩ : syracuseStep 3825287 = 5737931) B5737931
theorem B23273189 : Blo 1699550 23273189 := bstep (se 4 (by rfl) ⟨2181861, by rfl⟩ : syracuseStep 23273189 = 4363723) B4363723
theorem B5447425 : Blo 1699550 5447425 := bstep (se 2 (by rfl) ⟨2042784, by rfl⟩ : syracuseStep 5447425 = 4085569) B4085569
theorem B3227435 : Blo 1699550 3227435 := bstep (se 1 (by rfl) ⟨2420576, by rfl⟩ : syracuseStep 3227435 = 4841153) B4841153
theorem B9682739 : Blo 1699550 9682739 := bstep (se 1 (by rfl) ⟨7262054, by rfl⟩ : syracuseStep 9682739 = 14524109) B14524109
theorem B3825467 : Blo 1699550 3825467 := bstep (se 1 (by rfl) ⟨2869100, by rfl⟩ : syracuseStep 3825467 = 5738201) B5738201
theorem B4906813 : Blo 1699550 4906813 := bstep (se 3 (by rfl) ⟨920027, by rfl⟩ : syracuseStep 4906813 = 1840055) B1840055
theorem B8609651 : Blo 1699550 8609651 := bstep (se 1 (by rfl) ⟨6457238, by rfl⟩ : syracuseStep 8609651 = 12914477) B12914477
theorem B4595575 : Blo 1699550 4595575 := bstep (se 1 (by rfl) ⟨3446681, by rfl⟩ : syracuseStep 4595575 = 6893363) B6893363
theorem B3825593 : Blo 1699550 3825593 := bstep (se 2 (by rfl) ⟨1434597, by rfl⟩ : syracuseStep 3825593 = 2869195) B2869195
theorem B5742521 : Blo 1699550 5742521 := bstep (se 2 (by rfl) ⟨2153445, by rfl⟩ : syracuseStep 5742521 = 4306891) B4306891
theorem B3825683 : Blo 1699550 3825683 := bstep (se 1 (by rfl) ⟨2869262, by rfl⟩ : syracuseStep 3825683 = 5738525) B5738525
theorem B3826025 : Blo 1699550 3826025 := bstep (se 2 (by rfl) ⟨1434759, by rfl⟩ : syracuseStep 3826025 = 2869519) B2869519
theorem B9683489 : Blo 1699550 9683489 := bstep (se 2 (by rfl) ⟨3631308, by rfl⟩ : syracuseStep 9683489 = 7262617) B7262617
theorem B2908711 : Blo 1699550 2908711 := bstep (se 1 (by rfl) ⟨2181533, by rfl⟩ : syracuseStep 2908711 = 4363067) B4363067
theorem B3228331 : Blo 1699550 3228331 := bstep (se 1 (by rfl) ⟨2421248, by rfl⟩ : syracuseStep 3228331 = 4842497) B4842497
theorem B5169863 : Blo 1699550 5169863 := bstep (se 1 (by rfl) ⟨3877397, by rfl⟩ : syracuseStep 5169863 = 7754795) B7754795
theorem B4596439 : Blo 1699550 4596439 := bstep (se 1 (by rfl) ⟨3447329, by rfl⟩ : syracuseStep 4596439 = 6894659) B6894659
theorem B3228407 : Blo 1699550 3228407 := bstep (se 1 (by rfl) ⟨2421305, by rfl⟩ : syracuseStep 3228407 = 4842611) B4842611
theorem B6456131 : Blo 1699550 6456131 := bstep (se 1 (by rfl) ⟨4842098, by rfl⟩ : syracuseStep 6456131 = 9684197) B9684197
theorem B2868041 : Blo 1699550 2868041 := bstep (se 2 (by rfl) ⟨1075515, by rfl⟩ : syracuseStep 2868041 = 2151031) B2151031
theorem B3826619 : Blo 1699550 3826619 := bstep (se 1 (by rfl) ⟨2869964, by rfl⟩ : syracuseStep 3826619 = 5739929) B5739929
theorem B3228635 : Blo 1699550 3228635 := bstep (se 1 (by rfl) ⟨2421476, by rfl⟩ : syracuseStep 3228635 = 4842953) B4842953
theorem B3826745 : Blo 1699550 3826745 := bstep (se 2 (by rfl) ⟨1435029, by rfl⟩ : syracuseStep 3826745 = 2870059) B2870059
theorem B14525507 : Blo 1699550 14525507 := bstep (se 1 (by rfl) ⟨10894130, by rfl⟩ : syracuseStep 14525507 = 21788261) B21788261
theorem B6546511 : Blo 1699550 6546511 := bstep (se 1 (by rfl) ⟨4909883, by rfl⟩ : syracuseStep 6546511 = 9819767) B9819767
theorem B2868473 : Blo 1699550 2868473 := bstep (se 2 (by rfl) ⟨1075677, by rfl⟩ : syracuseStep 2868473 = 2151355) B2151355
theorem B3827087 : Blo 1699550 3827087 := bstep (se 1 (by rfl) ⟨2870315, by rfl⟩ : syracuseStep 3827087 = 5740631) B5740631
theorem B2868655 : Blo 1699550 2868655 := bstep (se 1 (by rfl) ⟨2151491, by rfl⟩ : syracuseStep 2868655 = 4302983) B4302983
theorem B24839669 : Blo 1699550 24839669 := bstep (se 5 (by rfl) ⟨1164359, by rfl⟩ : syracuseStep 24839669 = 2328719) B2328719
theorem B2868743 : Blo 1699550 2868743 := bstep (se 1 (by rfl) ⟨2151557, by rfl⟩ : syracuseStep 2868743 = 4303115) B4303115
theorem B2909753 : Blo 1699550 2909753 := bstep (se 2 (by rfl) ⟨1091157, by rfl⟩ : syracuseStep 2909753 = 2182315) B2182315
theorem B2549327 : Blo 1699550 2549327 := bstep (se 1 (by rfl) ⟨1911995, by rfl⟩ : syracuseStep 2549327 = 3823991) B3823991
theorem B2549447 : Blo 1699550 2549447 := bstep (se 1 (by rfl) ⟨1912085, by rfl⟩ : syracuseStep 2549447 = 3824171) B3824171
theorem B49006295 : Blo 1699550 49006295 := bstep (se 1 (by rfl) ⟨36754721, by rfl⟩ : syracuseStep 49006295 = 73509443) B73509443
theorem B17450711 : Blo 1699550 17450711 := bstep (se 1 (by rfl) ⟨13088033, by rfl⟩ : syracuseStep 17450711 = 26176067) B26176067
theorem B3827411 : Blo 1699550 3827411 := bstep (se 1 (by rfl) ⟨2870558, by rfl⟩ : syracuseStep 3827411 = 5741117) B5741117
theorem B6457117 : Blo 1699550 6457117 := bstep (se 3 (by rfl) ⟨1210709, by rfl⟩ : syracuseStep 6457117 = 2421419) B2421419
theorem B2869087 : Blo 1699550 2869087 := bstep (se 1 (by rfl) ⟨2151815, by rfl⟩ : syracuseStep 2869087 = 4303631) B4303631
theorem B2549609 : Blo 1699550 2549609 := bstep (se 2 (by rfl) ⟨956103, by rfl⟩ : syracuseStep 2549609 = 1912207) B1912207
theorem B3065705 : Blo 1699550 3065705 := bstep (se 2 (by rfl) ⟨1149639, by rfl⟩ : syracuseStep 3065705 = 2299279) B2299279
theorem B5736311 : Blo 1699550 5736311 := bstep (se 1 (by rfl) ⟨4302233, by rfl⟩ : syracuseStep 5736311 = 8604467) B8604467
theorem B56674201 : Blo 1699550 56674201 := bstep (se 2 (by rfl) ⟨21252825, by rfl⟩ : syracuseStep 56674201 = 42505651) B42505651
theorem B2549687 : Blo 1699550 2549687 := bstep (se 1 (by rfl) ⟨1912265, by rfl⟩ : syracuseStep 2549687 = 3824531) B3824531
theorem B2869175 : Blo 1699550 2869175 := bstep (se 1 (by rfl) ⟨2151881, by rfl⟩ : syracuseStep 2869175 = 4303763) B4303763
theorem B5449655 : Blo 1699550 5449655 := bstep (se 1 (by rfl) ⟨4087241, by rfl⟩ : syracuseStep 5449655 = 8174483) B8174483
theorem B2549723 : Blo 1699550 2549723 := bstep (se 1 (by rfl) ⟨1912292, by rfl⟩ : syracuseStep 2549723 = 3824585) B3824585
theorem B10897411 : Blo 1699550 10897411 := bstep (se 1 (by rfl) ⟨8173058, by rfl⟩ : syracuseStep 10897411 = 16346117) B16346117
theorem B5736527 : Blo 1699550 5736527 := bstep (se 1 (by rfl) ⟨4302395, by rfl⟩ : syracuseStep 5736527 = 8604791) B8604791
theorem B3065935 : Blo 1699550 3065935 := bstep (se 1 (by rfl) ⟨2299451, by rfl⟩ : syracuseStep 3065935 = 4598903) B4598903
theorem B251463781 : Blo 1699550 251463781 := bstep (se 4 (by rfl) ⟨23574729, by rfl⟩ : syracuseStep 251463781 = 47149459) B47149459
theorem B3229895 : Blo 1699550 3229895 := bstep (se 1 (by rfl) ⟨2422421, by rfl⟩ : syracuseStep 3229895 = 4844843) B4844843
theorem B6129911 : Blo 1699550 6129911 := bstep (se 1 (by rfl) ⟨4597433, by rfl⟩ : syracuseStep 6129911 = 9194867) B9194867
theorem B3230047 : Blo 1699550 3230047 := bstep (se 1 (by rfl) ⟨2422535, by rfl⟩ : syracuseStep 3230047 = 4845071) B4845071
theorem B2550191 : Blo 1699550 2550191 := bstep (se 1 (by rfl) ⟨1912643, by rfl⟩ : syracuseStep 2550191 = 3825287) B3825287
theorem B5736905 : Blo 1699550 5736905 := bstep (se 2 (by rfl) ⟨2151339, by rfl⟩ : syracuseStep 5736905 = 4302679) B4302679
theorem B2550281 : Blo 1699550 2550281 := bstep (se 2 (by rfl) ⟨956355, by rfl⟩ : syracuseStep 2550281 = 1912711) B1912711
theorem B2869769 : Blo 1699550 2869769 := bstep (se 2 (by rfl) ⟨1076163, by rfl⟩ : syracuseStep 2869769 = 2152327) B2152327
theorem B2550311 : Blo 1699550 2550311 := bstep (se 1 (by rfl) ⟨1912733, by rfl⟩ : syracuseStep 2550311 = 3825467) B3825467
theorem B2550395 : Blo 1699550 2550395 := bstep (se 1 (by rfl) ⟨1912796, by rfl⟩ : syracuseStep 2550395 = 3825593) B3825593
theorem B3828347 : Blo 1699550 3828347 := bstep (se 1 (by rfl) ⟨2871260, by rfl⟩ : syracuseStep 3828347 = 5742521) B5742521
theorem B2869931 : Blo 1699550 2869931 := bstep (se 1 (by rfl) ⟨2152448, by rfl⟩ : syracuseStep 2869931 = 4304897) B4304897
theorem B22088393 : Blo 1699550 22088393 := bstep (se 2 (by rfl) ⟨8283147, by rfl⟩ : syracuseStep 22088393 = 16566295) B16566295
theorem B5737175 : Blo 1699550 5737175 := bstep (se 1 (by rfl) ⟨4302881, by rfl⟩ : syracuseStep 5737175 = 8605763) B8605763
theorem B4975319 : Blo 1699550 4975319 := bstep (se 1 (by rfl) ⟨3731489, by rfl⟩ : syracuseStep 4975319 = 7462979) B7462979
theorem B2550521 : Blo 1699550 2550521 := bstep (se 2 (by rfl) ⟨956445, by rfl⟩ : syracuseStep 2550521 = 1912891) B1912891
theorem B3828473 : Blo 1699550 3828473 := bstep (se 2 (by rfl) ⟨1435677, by rfl⟩ : syracuseStep 3828473 = 2871355) B2871355
theorem B2550623 : Blo 1699550 2550623 := bstep (se 1 (by rfl) ⟨1912967, by rfl⟩ : syracuseStep 2550623 = 3825935) B3825935
theorem B2550635 : Blo 1699550 2550635 := bstep (se 1 (by rfl) ⟨1912976, by rfl⟩ : syracuseStep 2550635 = 3825953) B3825953
theorem B5737391 : Blo 1699550 5737391 := bstep (se 1 (by rfl) ⟨4303043, by rfl⟩ : syracuseStep 5737391 = 8606087) B8606087
theorem B2870329 : Blo 1699550 2870329 := bstep (se 2 (by rfl) ⟨1076373, by rfl⟩ : syracuseStep 2870329 = 2152747) B2152747
theorem B2550863 : Blo 1699550 2550863 := bstep (se 1 (by rfl) ⟨1913147, by rfl⟩ : syracuseStep 2550863 = 3826295) B3826295
theorem B2550983 : Blo 1699550 2550983 := bstep (se 1 (by rfl) ⟨1913237, by rfl⟩ : syracuseStep 2550983 = 3826475) B3826475
theorem B2870471 : Blo 1699550 2870471 := bstep (se 1 (by rfl) ⟨2152853, by rfl⟩ : syracuseStep 2870471 = 4305707) B4305707
theorem B2419961 : Blo 1699550 2419961 := bstep (se 2 (by rfl) ⟨907485, by rfl⟩ : syracuseStep 2419961 = 1814971) B1814971
theorem B2551145 : Blo 1699550 2551145 := bstep (se 2 (by rfl) ⟨956679, by rfl⟩ : syracuseStep 2551145 = 1913359) B1913359
theorem B2420075 : Blo 1699550 2420075 := bstep (se 1 (by rfl) ⟨1815056, by rfl⟩ : syracuseStep 2420075 = 3630113) B3630113
theorem B2870633 : Blo 1699550 2870633 := bstep (se 2 (by rfl) ⟨1076487, by rfl⟩ : syracuseStep 2870633 = 2152975) B2152975
theorem B2551223 : Blo 1699550 2551223 := bstep (se 1 (by rfl) ⟨1913417, by rfl⟩ : syracuseStep 2551223 = 3826835) B3826835
theorem B2551259 : Blo 1699550 2551259 := bstep (se 1 (by rfl) ⟨1913444, by rfl⟩ : syracuseStep 2551259 = 3826889) B3826889
theorem B11800027 : Blo 1699550 11800027 := bstep (se 1 (by rfl) ⟨8850020, by rfl⟩ : syracuseStep 11800027 = 17700041) B17700041
theorem B6131209 : Blo 1699550 6131209 := bstep (se 2 (by rfl) ⟨2299203, by rfl⟩ : syracuseStep 6131209 = 4598407) B4598407
theorem B6131323 : Blo 1699550 6131323 := bstep (se 1 (by rfl) ⟨4598492, by rfl⟩ : syracuseStep 6131323 = 9196985) B9196985
theorem B34926203 : Blo 1699550 34926203 := bstep (se 1 (by rfl) ⟨26194652, by rfl⟩ : syracuseStep 34926203 = 52389305) B52389305
theorem B12258955 : Blo 1699550 12258955 := bstep (se 1 (by rfl) ⟨9194216, by rfl⟩ : syracuseStep 12258955 = 18388433) B18388433
theorem B2871031 : Blo 1699550 2871031 := bstep (se 1 (by rfl) ⟨2153273, by rfl⟩ : syracuseStep 2871031 = 4306547) B4306547
theorem B1699623 : Blo 1699550 1699623 := bstep (se 1 (by rfl) ⟨1274717, by rfl⟩ : syracuseStep 1699623 = 2549435) B2549435
theorem B1699663 : Blo 1699550 1699663 := bstep (se 1 (by rfl) ⟨1274747, by rfl⟩ : syracuseStep 1699663 = 2549495) B2549495
theorem B4083551 : Blo 1699550 4083551 := bstep (se 1 (by rfl) ⟨3062663, by rfl⟩ : syracuseStep 4083551 = 6125327) B6125327
theorem B1699679 : Blo 1699550 1699679 := bstep (se 1 (by rfl) ⟨1274759, by rfl⟩ : syracuseStep 1699679 = 2549519) B2549519
theorem B4304735 : Blo 1699550 4304735 := bstep (se 1 (by rfl) ⟨3228551, by rfl⟩ : syracuseStep 4304735 = 6457103) B6457103
theorem B1699707 : Blo 1699550 1699707 := bstep (se 1 (by rfl) ⟨1274780, by rfl⟩ : syracuseStep 1699707 = 2549561) B2549561
theorem B8605601 : Blo 1699550 8605601 := bstep (se 2 (by rfl) ⟨3227100, by rfl⟩ : syracuseStep 8605601 = 6454201) B6454201
theorem B1699759 : Blo 1699550 1699759 := bstep (se 1 (by rfl) ⟨1274819, by rfl⟩ : syracuseStep 1699759 = 2549639) B2549639
theorem B2551727 : Blo 1699550 2551727 := bstep (se 1 (by rfl) ⟨1913795, by rfl⟩ : syracuseStep 2551727 = 3827591) B3827591
theorem B2871227 : Blo 1699550 2871227 := bstep (se 1 (by rfl) ⟨2153420, by rfl⟩ : syracuseStep 2871227 = 4306841) B4306841
theorem B1699783 : Blo 1699550 1699783 := bstep (se 1 (by rfl) ⟨1274837, by rfl⟩ : syracuseStep 1699783 = 2549675) B2549675
theorem B1699803 : Blo 1699550 1699803 := bstep (se 1 (by rfl) ⟨1274852, by rfl⟩ : syracuseStep 1699803 = 2549705) B2549705
theorem B2551817 : Blo 1699550 2551817 := bstep (se 2 (by rfl) ⟨956931, by rfl⟩ : syracuseStep 2551817 = 1913863) B1913863
theorem B1699879 : Blo 1699550 1699879 := bstep (se 1 (by rfl) ⟨1274909, by rfl⟩ : syracuseStep 1699879 = 2549819) B2549819
theorem B2551847 : Blo 1699550 2551847 := bstep (se 1 (by rfl) ⟨1913885, by rfl⟩ : syracuseStep 2551847 = 3827771) B3827771
theorem B2871335 : Blo 1699550 2871335 := bstep (se 1 (by rfl) ⟨2153501, by rfl⟩ : syracuseStep 2871335 = 4307003) B4307003
theorem B1699919 : Blo 1699550 1699919 := bstep (se 1 (by rfl) ⟨1274939, by rfl⟩ : syracuseStep 1699919 = 2549879) B2549879
theorem B9195601 : Blo 1699550 9195601 := bstep (se 2 (by rfl) ⟨3448350, by rfl⟩ : syracuseStep 9195601 = 6896701) B6896701
theorem B1699935 : Blo 1699550 1699935 := bstep (se 1 (by rfl) ⟨1274951, by rfl⟩ : syracuseStep 1699935 = 2549903) B2549903
theorem B11800691 : Blo 1699550 11800691 := bstep (se 1 (by rfl) ⟨8850518, by rfl⟩ : syracuseStep 11800691 = 17701037) B17701037
theorem B1699963 : Blo 1699550 1699963 := bstep (se 1 (by rfl) ⟨1274972, by rfl⟩ : syracuseStep 1699963 = 2549945) B2549945
theorem B2551931 : Blo 1699550 2551931 := bstep (se 1 (by rfl) ⟨1913948, by rfl⟩ : syracuseStep 2551931 = 3827897) B3827897
theorem B1700015 : Blo 1699550 1700015 := bstep (se 1 (by rfl) ⟨1275011, by rfl⟩ : syracuseStep 1700015 = 2550023) B2550023
theorem B1700039 : Blo 1699550 1700039 := bstep (se 1 (by rfl) ⟨1275029, by rfl⟩ : syracuseStep 1700039 = 2550059) B2550059
theorem B3494099 : Blo 1699550 3494099 := bstep (se 1 (by rfl) ⟨2620574, by rfl⟩ : syracuseStep 3494099 = 5241149) B5241149
theorem B1700059 : Blo 1699550 1700059 := bstep (se 1 (by rfl) ⟨1275044, by rfl⟩ : syracuseStep 1700059 = 2550089) B2550089
theorem B2552057 : Blo 1699550 2552057 := bstep (se 2 (by rfl) ⟨957021, by rfl⟩ : syracuseStep 2552057 = 1914043) B1914043
theorem B1700135 : Blo 1699550 1700135 := bstep (se 1 (by rfl) ⟨1275101, by rfl⟩ : syracuseStep 1700135 = 2550203) B2550203
theorem B1700175 : Blo 1699550 1700175 := bstep (se 1 (by rfl) ⟨1275131, by rfl⟩ : syracuseStep 1700175 = 2550263) B2550263
theorem B1700191 : Blo 1699550 1700191 := bstep (se 1 (by rfl) ⟨1275143, by rfl⟩ : syracuseStep 1700191 = 2550287) B2550287
theorem B2552159 : Blo 1699550 2552159 := bstep (se 1 (by rfl) ⟨1914119, by rfl⟩ : syracuseStep 2552159 = 3828239) B3828239
theorem B2552171 : Blo 1699550 2552171 := bstep (se 1 (by rfl) ⟨1914128, by rfl⟩ : syracuseStep 2552171 = 3828257) B3828257
theorem B1700219 : Blo 1699550 1700219 := bstep (se 1 (by rfl) ⟨1275164, by rfl⟩ : syracuseStep 1700219 = 2550329) B2550329
theorem B1700271 : Blo 1699550 1700271 := bstep (se 1 (by rfl) ⟨1275203, by rfl⟩ : syracuseStep 1700271 = 2550407) B2550407
theorem B1700295 : Blo 1699550 1700295 := bstep (se 1 (by rfl) ⟨1275221, by rfl⟩ : syracuseStep 1700295 = 2550443) B2550443
theorem B1700315 : Blo 1699550 1700315 := bstep (se 1 (by rfl) ⟨1275236, by rfl⟩ : syracuseStep 1700315 = 2550473) B2550473
theorem B22385161 : Blo 1699550 22385161 := bstep (se 2 (by rfl) ⟨8394435, by rfl⟩ : syracuseStep 22385161 = 16788871) B16788871
theorem B4305433 : Blo 1699550 4305433 := bstep (se 2 (by rfl) ⟨1614537, by rfl⟩ : syracuseStep 4305433 = 3229075) B3229075
theorem B1700391 : Blo 1699550 1700391 := bstep (se 1 (by rfl) ⟨1275293, by rfl⟩ : syracuseStep 1700391 = 2550587) B2550587
theorem B1700431 : Blo 1699550 1700431 := bstep (se 1 (by rfl) ⟨1275323, by rfl⟩ : syracuseStep 1700431 = 2550647) B2550647
theorem B1700447 : Blo 1699550 1700447 := bstep (se 1 (by rfl) ⟨1275335, by rfl⟩ : syracuseStep 1700447 = 2550671) B2550671
theorem B3633761 : Blo 1699550 3633761 := bstep (se 2 (by rfl) ⟨1362660, by rfl⟩ : syracuseStep 3633761 = 2725321) B2725321
theorem B1700475 : Blo 1699550 1700475 := bstep (se 1 (by rfl) ⟨1275356, by rfl⟩ : syracuseStep 1700475 = 2550713) B2550713
theorem B1913467 : Blo 1699550 1913467 := bstep (se 1 (by rfl) ⟨1435100, by rfl⟩ : syracuseStep 1913467 = 2870201) B2870201
theorem B1700527 : Blo 1699550 1700527 := bstep (se 1 (by rfl) ⟨1275395, by rfl⟩ : syracuseStep 1700527 = 2550791) B2550791
theorem B1700551 : Blo 1699550 1700551 := bstep (se 1 (by rfl) ⟨1275413, by rfl⟩ : syracuseStep 1700551 = 2550827) B2550827
theorem B9679571 : Blo 1699550 9679571 := bstep (se 1 (by rfl) ⟨7259678, by rfl⟩ : syracuseStep 9679571 = 14519357) B14519357
theorem B1700571 : Blo 1699550 1700571 := bstep (se 1 (by rfl) ⟨1275428, by rfl⟩ : syracuseStep 1700571 = 2550857) B2550857
theorem B8278787 : Blo 1699550 8278787 := bstep (se 1 (by rfl) ⟨6209090, by rfl⟩ : syracuseStep 8278787 = 12418181) B12418181
theorem B1700647 : Blo 1699550 1700647 := bstep (se 1 (by rfl) ⟨1275485, by rfl⟩ : syracuseStep 1700647 = 2550971) B2550971
theorem B43578161 : Blo 1699550 43578161 := bstep (se 2 (by rfl) ⟨16341810, by rfl⟩ : syracuseStep 43578161 = 32683621) B32683621
theorem B4305737 : Blo 1699550 4305737 := bstep (se 2 (by rfl) ⟨1614651, by rfl⟩ : syracuseStep 4305737 = 3229303) B3229303
theorem B1700687 : Blo 1699550 1700687 := bstep (se 1 (by rfl) ⟨1275515, by rfl⟩ : syracuseStep 1700687 = 2551031) B2551031
theorem B1700703 : Blo 1699550 1700703 := bstep (se 1 (by rfl) ⟨1275527, by rfl⟩ : syracuseStep 1700703 = 2551055) B2551055
theorem B1700731 : Blo 1699550 1700731 := bstep (se 1 (by rfl) ⟨1275548, by rfl⟩ : syracuseStep 1700731 = 2551097) B2551097
theorem B1700783 : Blo 1699550 1700783 := bstep (se 1 (by rfl) ⟨1275587, by rfl⟩ : syracuseStep 1700783 = 2551175) B2551175
theorem B1700807 : Blo 1699550 1700807 := bstep (se 1 (by rfl) ⟨1275605, by rfl⟩ : syracuseStep 1700807 = 2551211) B2551211
theorem B1700827 : Blo 1699550 1700827 := bstep (se 1 (by rfl) ⟨1275620, by rfl⟩ : syracuseStep 1700827 = 2551241) B2551241
theorem B7263233 : Blo 1699550 7263233 := bstep (se 2 (by rfl) ⟨2723712, by rfl⟩ : syracuseStep 7263233 = 5447425) B5447425
theorem B1700903 : Blo 1699550 1700903 := bstep (se 1 (by rfl) ⟨1275677, by rfl⟩ : syracuseStep 1700903 = 2551355) B2551355
theorem B10892339 : Blo 1699550 10892339 := bstep (se 1 (by rfl) ⟨8169254, by rfl⟩ : syracuseStep 10892339 = 16338509) B16338509
theorem B55161917 : Blo 1699550 55161917 := bstep (se 3 (by rfl) ⟨10342859, by rfl⟩ : syracuseStep 55161917 = 20685719) B20685719
theorem B31028291 : Blo 1699550 31028291 := bstep (se 1 (by rfl) ⟨23271218, by rfl⟩ : syracuseStep 31028291 = 46542437) B46542437
theorem B1700943 : Blo 1699550 1700943 := bstep (se 1 (by rfl) ⟨1275707, by rfl⟩ : syracuseStep 1700943 = 2551415) B2551415
theorem B2724943 : Blo 1699550 2724943 := bstep (se 1 (by rfl) ⟨2043707, by rfl⟩ : syracuseStep 2724943 = 4087415) B4087415
theorem B6542417 : Blo 1699550 6542417 := bstep (se 2 (by rfl) ⟨2453406, by rfl⟩ : syracuseStep 6542417 = 4906813) B4906813
theorem B1913935 : Blo 1699550 1913935 := bstep (se 1 (by rfl) ⟨1435451, by rfl⟩ : syracuseStep 1913935 = 2870903) B2870903
theorem B1700959 : Blo 1699550 1700959 := bstep (se 1 (by rfl) ⟨1275719, by rfl⟩ : syracuseStep 1700959 = 2551439) B2551439
theorem B1700987 : Blo 1699550 1700987 := bstep (se 1 (by rfl) ⟨1275740, by rfl⟩ : syracuseStep 1700987 = 2551481) B2551481
theorem B12907673 : Blo 1699550 12907673 := bstep (se 2 (by rfl) ⟨4840377, by rfl⟩ : syracuseStep 12907673 = 9680755) B9680755
theorem B11957419 : Blo 1699550 11957419 := bstep (se 1 (by rfl) ⟨8968064, by rfl⟩ : syracuseStep 11957419 = 17936129) B17936129
theorem B1701039 : Blo 1699550 1701039 := bstep (se 1 (by rfl) ⟨1275779, by rfl⟩ : syracuseStep 1701039 = 2551559) B2551559
theorem B2151623 : Blo 1699550 2151623 := bstep (se 1 (by rfl) ⟨1613717, by rfl⟩ : syracuseStep 2151623 = 3227435) B3227435
theorem B1701063 : Blo 1699550 1701063 := bstep (se 1 (by rfl) ⟨1275797, by rfl⟩ : syracuseStep 1701063 = 2551595) B2551595
theorem B1701083 : Blo 1699550 1701083 := bstep (se 1 (by rfl) ⟨1275812, by rfl⟩ : syracuseStep 1701083 = 2551625) B2551625
theorem B5739767 : Blo 1699550 5739767 := bstep (se 1 (by rfl) ⟨4304825, by rfl⟩ : syracuseStep 5739767 = 8609651) B8609651
theorem B1701159 : Blo 1699550 1701159 := bstep (se 1 (by rfl) ⟨1275869, by rfl⟩ : syracuseStep 1701159 = 2551739) B2551739
theorem B1701199 : Blo 1699550 1701199 := bstep (se 1 (by rfl) ⟨1275899, by rfl⟩ : syracuseStep 1701199 = 2551799) B2551799
theorem B2151775 : Blo 1699550 2151775 := bstep (se 1 (by rfl) ⟨1613831, by rfl⟩ : syracuseStep 2151775 = 3227663) B3227663
theorem B1701215 : Blo 1699550 1701215 := bstep (se 1 (by rfl) ⟨1275911, by rfl⟩ : syracuseStep 1701215 = 2551823) B2551823
theorem B4142441 : Blo 1699550 4142441 := bstep (se 2 (by rfl) ⟨1553415, by rfl⟩ : syracuseStep 4142441 = 3106831) B3106831
theorem B1701243 : Blo 1699550 1701243 := bstep (se 1 (by rfl) ⟨1275932, by rfl⟩ : syracuseStep 1701243 = 2551865) B2551865
theorem B1701295 : Blo 1699550 1701295 := bstep (se 1 (by rfl) ⟨1275971, by rfl⟩ : syracuseStep 1701295 = 2551943) B2551943
theorem B1701319 : Blo 1699550 1701319 := bstep (se 1 (by rfl) ⟨1275989, by rfl⟩ : syracuseStep 1701319 = 2551979) B2551979
theorem B1701339 : Blo 1699550 1701339 := bstep (se 1 (by rfl) ⟨1276004, by rfl⟩ : syracuseStep 1701339 = 2552009) B2552009
theorem B5445107 : Blo 1699550 5445107 := bstep (se 1 (by rfl) ⟨4083830, by rfl⟩ : syracuseStep 5445107 = 8167661) B8167661
theorem B3446291 : Blo 1699550 3446291 := bstep (se 1 (by rfl) ⟨2584718, by rfl⟩ : syracuseStep 3446291 = 5169437) B5169437
theorem B5240359 : Blo 1699550 5240359 := bstep (se 1 (by rfl) ⟨3930269, by rfl⟩ : syracuseStep 5240359 = 7860539) B7860539
theorem B1701415 : Blo 1699550 1701415 := bstep (se 1 (by rfl) ⟨1276061, by rfl⟩ : syracuseStep 1701415 = 2552123) B2552123
theorem B5740091 : Blo 1699550 5740091 := bstep (se 1 (by rfl) ⟨4305068, by rfl⟩ : syracuseStep 5740091 = 8610137) B8610137
theorem B1701455 : Blo 1699550 1701455 := bstep (se 1 (by rfl) ⟨1276091, by rfl⟩ : syracuseStep 1701455 = 2552183) B2552183
theorem B1701471 : Blo 1699550 1701471 := bstep (se 1 (by rfl) ⟨1276103, by rfl⟩ : syracuseStep 1701471 = 2552207) B2552207
theorem B1701499 : Blo 1699550 1701499 := bstep (se 1 (by rfl) ⟨1276124, by rfl⟩ : syracuseStep 1701499 = 2552249) B2552249
theorem B9680573 : Blo 1699550 9680573 := bstep (se 3 (by rfl) ⟨1815107, by rfl⟩ : syracuseStep 9680573 = 3630215) B3630215
theorem B5740361 : Blo 1699550 5740361 := bstep (se 2 (by rfl) ⟨2152635, by rfl⟩ : syracuseStep 5740361 = 4305271) B4305271
theorem B8730487 : Blo 1699550 8730487 := bstep (se 1 (by rfl) ⟨6547865, by rfl⟩ : syracuseStep 8730487 = 13095731) B13095731
theorem B4306871 : Blo 1699550 4306871 := bstep (se 1 (by rfl) ⟨3230153, by rfl⟩ : syracuseStep 4306871 = 6460307) B6460307
theorem B5445785 : Blo 1699550 5445785 := bstep (se 2 (by rfl) ⟨2042169, by rfl⟩ : syracuseStep 5445785 = 4084339) B4084339
theorem B19634537 : Blo 1699550 19634537 := bstep (se 2 (by rfl) ⟨7362951, by rfl⟩ : syracuseStep 19634537 = 14725903) B14725903
theorem B9681281 : Blo 1699550 9681281 := bstep (se 2 (by rfl) ⟨3630480, by rfl⟩ : syracuseStep 9681281 = 7260961) B7260961
theorem B7084577 : Blo 1699550 7084577 := bstep (se 2 (by rfl) ⟨2656716, by rfl⟩ : syracuseStep 7084577 = 5313433) B5313433
theorem B2128423 : Blo 1699550 2128423 := bstep (se 1 (by rfl) ⟨1596317, by rfl⟩ : syracuseStep 2128423 = 3192635) B3192635
theorem B3824225 : Blo 1699550 3824225 := bstep (se 2 (by rfl) ⟨1434084, by rfl⟩ : syracuseStep 3824225 = 2868169) B2868169
theorem B12262099 : Blo 1699550 12262099 := bstep (se 1 (by rfl) ⟨9196574, by rfl⟩ : syracuseStep 12262099 = 18393149) B18393149
theorem B20167501 : Blo 1699550 20167501 := bstep (se 3 (by rfl) ⟨3781406, by rfl⟩ : syracuseStep 20167501 = 7562813) B7562813
theorem B10345391 : Blo 1699550 10345391 := bstep (se 1 (by rfl) ⟨7759043, by rfl⟩ : syracuseStep 10345391 = 15518087) B15518087
theorem B3824567 : Blo 1699550 3824567 := bstep (se 1 (by rfl) ⟨2868425, by rfl⟩ : syracuseStep 3824567 = 5736851) B5736851
theorem B5741495 : Blo 1699550 5741495 := bstep (se 1 (by rfl) ⟨4306121, by rfl⟩ : syracuseStep 5741495 = 8612243) B8612243
theorem B10894337 : Blo 1699550 10894337 := bstep (se 2 (by rfl) ⟨4085376, by rfl⟩ : syracuseStep 10894337 = 8170753) B8170753
theorem B12909617 : Blo 1699550 12909617 := bstep (se 2 (by rfl) ⟨4841106, by rfl⟩ : syracuseStep 12909617 = 9682213) B9682213
theorem B12917879 : Blo 1699550 12917879 := bstep (se 1 (by rfl) ⟨9688409, by rfl⟩ : syracuseStep 12917879 = 19376819) B19376819
theorem B3226873 : Blo 1699550 3226873 := bstep (se 2 (by rfl) ⟨1210077, by rfl⟩ : syracuseStep 3226873 = 2420155) B2420155
theorem B24526097 : Blo 1699550 24526097 := bstep (se 2 (by rfl) ⟨9197286, by rfl⟩ : syracuseStep 24526097 = 18394573) B18394573
theorem B19365155 : Blo 1699550 19365155 := bstep (se 1 (by rfl) ⟨14523866, by rfl⟩ : syracuseStep 19365155 = 29047733) B29047733
theorem B4087145 : Blo 1699550 4087145 := bstep (se 2 (by rfl) ⟨1532679, by rfl⟩ : syracuseStep 4087145 = 3065359) B3065359
theorem B1965487 : Blo 1699550 1965487 := bstep (se 1 (by rfl) ⟨1474115, by rfl⟩ : syracuseStep 1965487 = 2948231) B2948231
theorem B49053113 : Blo 1699550 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B3448327 : Blo 1699550 3448327 := bstep (se 1 (by rfl) ⟨2586245, by rfl⟩ : syracuseStep 3448327 = 5172491) B5172491
theorem B3825161 : Blo 1699550 3825161 := bstep (se 2 (by rfl) ⟨1434435, by rfl⟩ : syracuseStep 3825161 = 2868871) B2868871
theorem B5742089 : Blo 1699550 5742089 := bstep (se 2 (by rfl) ⟨2153283, by rfl⟩ : syracuseStep 5742089 = 4306567) B4306567
theorem B3227215 : Blo 1699550 3227215 := bstep (se 1 (by rfl) ⟨2420411, by rfl⟩ : syracuseStep 3227215 = 4840823) B4840823
theorem B3448399 : Blo 1699550 3448399 := bstep (se 1 (by rfl) ⟨2586299, by rfl⟩ : syracuseStep 3448399 = 5172599) B5172599
theorem B15515459 : Blo 1699550 15515459 := bstep (se 1 (by rfl) ⟨11636594, by rfl⟩ : syracuseStep 15515459 = 23273189) B23273189
theorem B3227465 : Blo 1699550 3227465 := bstep (se 2 (by rfl) ⟨1210299, by rfl⟩ : syracuseStep 3227465 = 2420599) B2420599
theorem B6127433 : Blo 1699550 6127433 := bstep (se 2 (by rfl) ⟨2297787, by rfl⟩ : syracuseStep 6127433 = 4595575) B4595575
theorem B3825503 : Blo 1699550 3825503 := bstep (se 1 (by rfl) ⟨2869127, by rfl⟩ : syracuseStep 3825503 = 5738255) B5738255
theorem B7364461 : Blo 1699550 7364461 := bstep (se 3 (by rfl) ⟨1380836, by rfl⟩ : syracuseStep 7364461 = 2761673) B2761673
theorem B6455159 : Blo 1699550 6455159 := bstep (se 1 (by rfl) ⟨4841369, by rfl⟩ : syracuseStep 6455159 = 9682739) B9682739
theorem B4087913 : Blo 1699550 4087913 := bstep (se 2 (by rfl) ⟨1532967, by rfl⟩ : syracuseStep 4087913 = 3065935) B3065935
theorem B6455659 : Blo 1699550 6455659 := bstep (se 1 (by rfl) ⟨4841744, by rfl⟩ : syracuseStep 6455659 = 9683489) B9683489
theorem B34914725 : Blo 1699550 34914725 := bstep (se 4 (by rfl) ⟨3273255, by rfl⟩ : syracuseStep 34914725 = 6546511) B6546511
theorem B4842155 : Blo 1699550 4842155 := bstep (se 1 (by rfl) ⟨3631616, by rfl⟩ : syracuseStep 4842155 = 7263233) B7263233
theorem B36774611 : Blo 1699550 36774611 := bstep (se 1 (by rfl) ⟨27580958, by rfl⟩ : syracuseStep 36774611 = 55161917) B55161917
theorem B9683671 : Blo 1699550 9683671 := bstep (se 1 (by rfl) ⟨7262753, by rfl⟩ : syracuseStep 9683671 = 14525507) B14525507
theorem B20685527 : Blo 1699550 20685527 := bstep (se 1 (by rfl) ⟨15514145, by rfl⟩ : syracuseStep 20685527 = 31028291) B31028291
theorem B3826511 : Blo 1699550 3826511 := bstep (se 1 (by rfl) ⟨2869883, by rfl⟩ : syracuseStep 3826511 = 5739767) B5739767
theorem B2761627 : Blo 1699550 2761627 := bstep (se 1 (by rfl) ⟨2071220, by rfl⟩ : syracuseStep 2761627 = 4142441) B4142441
theorem B6128585 : Blo 1699550 6128585 := bstep (se 2 (by rfl) ⟨2298219, by rfl⟩ : syracuseStep 6128585 = 4596439) B4596439
theorem B3630071 : Blo 1699550 3630071 := bstep (se 1 (by rfl) ⟨2722553, by rfl⟩ : syracuseStep 3630071 = 5445107) B5445107
theorem B3826727 : Blo 1699550 3826727 := bstep (se 1 (by rfl) ⟨2870045, by rfl⟩ : syracuseStep 3826727 = 5740091) B5740091
theorem B32670863 : Blo 1699550 32670863 := bstep (se 1 (by rfl) ⟨24503147, by rfl⟩ : syracuseStep 32670863 = 49006295) B49006295
theorem B11633807 : Blo 1699550 11633807 := bstep (se 1 (by rfl) ⟨8725355, by rfl⟩ : syracuseStep 11633807 = 17450711) B17450711
theorem B3826907 : Blo 1699550 3826907 := bstep (se 1 (by rfl) ⟨2870180, by rfl⟩ : syracuseStep 3826907 = 5740361) B5740361
theorem B3827105 : Blo 1699550 3827105 := bstep (se 2 (by rfl) ⟨1435164, by rfl⟩ : syracuseStep 3827105 = 2870329) B2870329
theorem B3630523 : Blo 1699550 3630523 := bstep (se 1 (by rfl) ⟨2722892, by rfl⟩ : syracuseStep 3630523 = 5445785) B5445785
theorem B15943225 : Blo 1699550 15943225 := bstep (se 2 (by rfl) ⟨5978709, by rfl⟩ : syracuseStep 15943225 = 11957419) B11957419
theorem B4302497 : Blo 1699550 4302497 := bstep (se 2 (by rfl) ⟨1613436, by rfl⟩ : syracuseStep 4302497 = 3226873) B3226873
theorem B2549483 : Blo 1699550 2549483 := bstep (se 1 (by rfl) ⟨1912112, by rfl⟩ : syracuseStep 2549483 = 3824225) B3824225
theorem B2869033 : Blo 1699550 2869033 := bstep (se 2 (by rfl) ⟨1075887, by rfl⟩ : syracuseStep 2869033 = 2151775) B2151775
theorem B2549711 : Blo 1699550 2549711 := bstep (se 1 (by rfl) ⟨1912283, by rfl⟩ : syracuseStep 2549711 = 3824567) B3824567
theorem B3827663 : Blo 1699550 3827663 := bstep (se 1 (by rfl) ⟨2870747, by rfl⟩ : syracuseStep 3827663 = 5741495) B5741495
theorem B4597769 : Blo 1699550 4597769 := bstep (se 2 (by rfl) ⟨1724163, by rfl⟩ : syracuseStep 4597769 = 3448327) B3448327
theorem B8611919 : Blo 1699550 8611919 := bstep (se 1 (by rfl) ⟨6458939, by rfl⟩ : syracuseStep 8611919 = 12917879) B12917879
theorem B4302953 : Blo 1699550 4302953 := bstep (se 2 (by rfl) ⟨1613607, by rfl⟩ : syracuseStep 4302953 = 3227215) B3227215
theorem B4597865 : Blo 1699550 4597865 := bstep (se 2 (by rfl) ⟨1724199, by rfl⟩ : syracuseStep 4597865 = 3448399) B3448399
theorem B16345273 : Blo 1699550 16345273 := bstep (se 2 (by rfl) ⟨6129477, by rfl⟩ : syracuseStep 16345273 = 12258955) B12258955
theorem B3828041 : Blo 1699550 3828041 := bstep (se 2 (by rfl) ⟨1435515, by rfl⟩ : syracuseStep 3828041 = 2871031) B2871031
theorem B2550107 : Blo 1699550 2550107 := bstep (se 1 (by rfl) ⟨1912580, by rfl⟩ : syracuseStep 2550107 = 3825161) B3825161
theorem B3828059 : Blo 1699550 3828059 := bstep (se 1 (by rfl) ⟨2871044, by rfl⟩ : syracuseStep 3828059 = 5742089) B5742089
theorem B23284135 : Blo 1699550 23284135 := bstep (se 1 (by rfl) ⟨17463101, by rfl⟩ : syracuseStep 23284135 = 34926203) B34926203
theorem B75565601 : Blo 1699550 75565601 := bstep (se 2 (by rfl) ⟨28337100, by rfl⟩ : syracuseStep 75565601 = 56674201) B56674201
theorem B2722367 : Blo 1699550 2722367 := bstep (se 1 (by rfl) ⟨2041775, by rfl⟩ : syracuseStep 2722367 = 4083551) B4083551
theorem B2550335 : Blo 1699550 2550335 := bstep (se 1 (by rfl) ⟨1912751, by rfl⟩ : syracuseStep 2550335 = 3825503) B3825503
theorem B2869823 : Blo 1699550 2869823 := bstep (se 1 (by rfl) ⟨2152367, by rfl⟩ : syracuseStep 2869823 = 4304735) B4304735
theorem B4303439 : Blo 1699550 4303439 := bstep (se 1 (by rfl) ⟨3227579, by rfl⟩ : syracuseStep 4303439 = 6455159) B6455159
theorem B5737067 : Blo 1699550 5737067 := bstep (se 1 (by rfl) ⟨4302800, by rfl⟩ : syracuseStep 5737067 = 8605601) B8605601
theorem B2550455 : Blo 1699550 2550455 := bstep (se 1 (by rfl) ⟨1912841, by rfl⟩ : syracuseStep 2550455 = 3825683) B3825683
theorem B7867127 : Blo 1699550 7867127 := bstep (se 1 (by rfl) ⟨5900345, by rfl⟩ : syracuseStep 7867127 = 11800691) B11800691
theorem B335285041 : Blo 1699550 335285041 := bstep (se 2 (by rfl) ⟨125731890, by rfl⟩ : syracuseStep 335285041 = 251463781) B251463781
theorem B2329399 : Blo 1699550 2329399 := bstep (se 1 (by rfl) ⟨1747049, by rfl⟩ : syracuseStep 2329399 = 3494099) B3494099
theorem B2550683 : Blo 1699550 2550683 := bstep (se 1 (by rfl) ⟨1913012, by rfl⟩ : syracuseStep 2550683 = 3826025) B3826025
theorem B5737661 : Blo 1699550 5737661 := bstep (se 3 (by rfl) ⟨1075811, by rfl⟩ : syracuseStep 5737661 = 2151623) B2151623
theorem B8613053 : Blo 1699550 8613053 := bstep (se 3 (by rfl) ⟨1614947, by rfl⟩ : syracuseStep 8613053 = 3229895) B3229895
theorem B29052107 : Blo 1699550 29052107 := bstep (se 1 (by rfl) ⟨21789080, by rfl⟩ : syracuseStep 29052107 = 43578161) B43578161
theorem B4304087 : Blo 1699550 4304087 := bstep (se 1 (by rfl) ⟨3228065, by rfl⟩ : syracuseStep 4304087 = 6456131) B6456131
theorem B1912027 : Blo 1699550 1912027 := bstep (se 1 (by rfl) ⟨1434020, by rfl⟩ : syracuseStep 1912027 = 2868041) B2868041
theorem B2870491 : Blo 1699550 2870491 := bstep (se 1 (by rfl) ⟨2152868, by rfl⟩ : syracuseStep 2870491 = 4305737) B4305737
theorem B2551079 : Blo 1699550 2551079 := bstep (se 1 (by rfl) ⟨1913309, by rfl⟩ : syracuseStep 2551079 = 3826619) B3826619
theorem B7261559 : Blo 1699550 7261559 := bstep (se 1 (by rfl) ⟨5446169, by rfl⟩ : syracuseStep 7261559 = 10892339) B10892339
theorem B2551163 : Blo 1699550 2551163 := bstep (se 1 (by rfl) ⟨1913372, by rfl⟩ : syracuseStep 2551163 = 3826745) B3826745
theorem B3878281 : Blo 1699550 3878281 := bstep (se 2 (by rfl) ⟨1454355, by rfl⟩ : syracuseStep 3878281 = 2908711) B2908711
theorem B4361611 : Blo 1699550 4361611 := bstep (se 1 (by rfl) ⟨3271208, by rfl⟩ : syracuseStep 4361611 = 6542417) B6542417
theorem B2837897 : Blo 1699550 2837897 := bstep (se 2 (by rfl) ⟨1064211, by rfl⟩ : syracuseStep 2837897 = 2128423) B2128423
theorem B8605115 : Blo 1699550 8605115 := bstep (se 1 (by rfl) ⟨6453836, by rfl⟩ : syracuseStep 8605115 = 12907673) B12907673
theorem B2551289 : Blo 1699550 2551289 := bstep (se 2 (by rfl) ⟨956733, by rfl⟩ : syracuseStep 2551289 = 1913467) B1913467
theorem B1912315 : Blo 1699550 1912315 := bstep (se 1 (by rfl) ⟨1434236, by rfl⟩ : syracuseStep 1912315 = 2868473) B2868473
theorem B4304441 : Blo 1699550 4304441 := bstep (se 2 (by rfl) ⟨1614165, by rfl⟩ : syracuseStep 4304441 = 3228331) B3228331
theorem B2551391 : Blo 1699550 2551391 := bstep (se 1 (by rfl) ⟨1913543, by rfl⟩ : syracuseStep 2551391 = 3827087) B3827087
theorem B1912495 : Blo 1699550 1912495 := bstep (se 1 (by rfl) ⟨1434371, by rfl⟩ : syracuseStep 1912495 = 2868743) B2868743
theorem B2297527 : Blo 1699550 2297527 := bstep (se 1 (by rfl) ⟨1723145, by rfl⟩ : syracuseStep 2297527 = 3446291) B3446291
theorem B1699551 : Blo 1699550 1699551 := bstep (se 1 (by rfl) ⟨1274663, by rfl⟩ : syracuseStep 1699551 = 2549327) B2549327
theorem B26890001 : Blo 1699550 26890001 := bstep (se 2 (by rfl) ⟨10083750, by rfl⟩ : syracuseStep 26890001 = 20167501) B20167501
theorem B1699631 : Blo 1699550 1699631 := bstep (se 1 (by rfl) ⟨1274723, by rfl⟩ : syracuseStep 1699631 = 2549447) B2549447
theorem B2551607 : Blo 1699550 2551607 := bstep (se 1 (by rfl) ⟨1913705, by rfl⟩ : syracuseStep 2551607 = 3827411) B3827411
theorem B1699739 : Blo 1699550 1699739 := bstep (se 1 (by rfl) ⟨1274804, by rfl⟩ : syracuseStep 1699739 = 2549609) B2549609
theorem B2043803 : Blo 1699550 2043803 := bstep (se 1 (by rfl) ⟨1532852, by rfl⟩ : syracuseStep 2043803 = 3065705) B3065705
theorem B1699791 : Blo 1699550 1699791 := bstep (se 1 (by rfl) ⟨1274843, by rfl⟩ : syracuseStep 1699791 = 2549687) B2549687
theorem B1912783 : Blo 1699550 1912783 := bstep (se 1 (by rfl) ⟨1434587, by rfl⟩ : syracuseStep 1912783 = 2869175) B2869175
theorem B3633103 : Blo 1699550 3633103 := bstep (se 1 (by rfl) ⟨2724827, by rfl⟩ : syracuseStep 3633103 = 5449655) B5449655
theorem B2871247 : Blo 1699550 2871247 := bstep (se 1 (by rfl) ⟨2153435, by rfl⟩ : syracuseStep 2871247 = 4306871) B4306871
theorem B1699815 : Blo 1699550 1699815 := bstep (se 1 (by rfl) ⟨1274861, by rfl⟩ : syracuseStep 1699815 = 2549723) B2549723
theorem B3633257 : Blo 1699550 3633257 := bstep (se 2 (by rfl) ⟨1362471, by rfl⟩ : syracuseStep 3633257 = 2724943) B2724943
theorem B2551913 : Blo 1699550 2551913 := bstep (se 2 (by rfl) ⟨956967, by rfl⟩ : syracuseStep 2551913 = 1913935) B1913935
theorem B1700127 : Blo 1699550 1700127 := bstep (se 1 (by rfl) ⟨1275095, by rfl⟩ : syracuseStep 1700127 = 2550191) B2550191
theorem B1700187 : Blo 1699550 1700187 := bstep (se 1 (by rfl) ⟨1275140, by rfl⟩ : syracuseStep 1700187 = 2550281) B2550281
theorem B1913179 : Blo 1699550 1913179 := bstep (se 1 (by rfl) ⟨1434884, by rfl⟩ : syracuseStep 1913179 = 2869769) B2869769
theorem B4723051 : Blo 1699550 4723051 := bstep (se 1 (by rfl) ⟨3542288, by rfl⟩ : syracuseStep 4723051 = 7084577) B7084577
theorem B1700207 : Blo 1699550 1700207 := bstep (se 1 (by rfl) ⟨1275155, by rfl⟩ : syracuseStep 1700207 = 2550311) B2550311
theorem B1700263 : Blo 1699550 1700263 := bstep (se 1 (by rfl) ⟨1275197, by rfl⟩ : syracuseStep 1700263 = 2550395) B2550395
theorem B2552231 : Blo 1699550 2552231 := bstep (se 1 (by rfl) ⟨1914173, by rfl⟩ : syracuseStep 2552231 = 3828347) B3828347
theorem B1913287 : Blo 1699550 1913287 := bstep (se 1 (by rfl) ⟨1434965, by rfl⟩ : syracuseStep 1913287 = 2869931) B2869931
theorem B14725595 : Blo 1699550 14725595 := bstep (se 1 (by rfl) ⟨11044196, by rfl⟩ : syracuseStep 14725595 = 22088393) B22088393
theorem B1700347 : Blo 1699550 1700347 := bstep (se 1 (by rfl) ⟨1275260, by rfl⟩ : syracuseStep 1700347 = 2550521) B2550521
theorem B2552315 : Blo 1699550 2552315 := bstep (se 1 (by rfl) ⟨1914236, by rfl⟩ : syracuseStep 2552315 = 3828473) B3828473
theorem B1700415 : Blo 1699550 1700415 := bstep (se 1 (by rfl) ⟨1275311, by rfl⟩ : syracuseStep 1700415 = 2550623) B2550623
theorem B1700423 : Blo 1699550 1700423 := bstep (se 1 (by rfl) ⟨1275317, by rfl⟩ : syracuseStep 1700423 = 2550635) B2550635
theorem B15733369 : Blo 1699550 15733369 := bstep (se 2 (by rfl) ⟨5900013, by rfl⟩ : syracuseStep 15733369 = 11800027) B11800027
theorem B7262891 : Blo 1699550 7262891 := bstep (se 1 (by rfl) ⟨5447168, by rfl⟩ : syracuseStep 7262891 = 10894337) B10894337
theorem B8606411 : Blo 1699550 8606411 := bstep (se 1 (by rfl) ⟨6454808, by rfl⟩ : syracuseStep 8606411 = 12909617) B12909617
theorem B1700575 : Blo 1699550 1700575 := bstep (se 1 (by rfl) ⟨1275431, by rfl⟩ : syracuseStep 1700575 = 2550863) B2550863
theorem B1700655 : Blo 1699550 1700655 := bstep (se 1 (by rfl) ⟨1275491, by rfl⟩ : syracuseStep 1700655 = 2550983) B2550983
theorem B1913647 : Blo 1699550 1913647 := bstep (se 1 (by rfl) ⟨1435235, by rfl⟩ : syracuseStep 1913647 = 2870471) B2870471
theorem B8606573 : Blo 1699550 8606573 := bstep (se 3 (by rfl) ⟨1613732, by rfl⟩ : syracuseStep 8606573 = 3227465) B3227465
theorem B1700763 : Blo 1699550 1700763 := bstep (se 1 (by rfl) ⟨1275572, by rfl⟩ : syracuseStep 1700763 = 2551145) B2551145
theorem B2724763 : Blo 1699550 2724763 := bstep (se 1 (by rfl) ⟨2043572, by rfl⟩ : syracuseStep 2724763 = 4087145) B4087145
theorem B1913755 : Blo 1699550 1913755 := bstep (se 1 (by rfl) ⟨1435316, by rfl⟩ : syracuseStep 1913755 = 2870633) B2870633
theorem B1700815 : Blo 1699550 1700815 := bstep (se 1 (by rfl) ⟨1275611, by rfl⟩ : syracuseStep 1700815 = 2551223) B2551223
theorem B1700839 : Blo 1699550 1700839 := bstep (se 1 (by rfl) ⟨1275629, by rfl⟩ : syracuseStep 1700839 = 2551259) B2551259
theorem B9819281 : Blo 1699550 9819281 := bstep (se 2 (by rfl) ⟨3682230, by rfl⟩ : syracuseStep 9819281 = 7364461) B7364461
theorem B10343639 : Blo 1699550 10343639 := bstep (se 1 (by rfl) ⟨7757729, by rfl⟩ : syracuseStep 10343639 = 15515459) B15515459
theorem B4084955 : Blo 1699550 4084955 := bstep (se 1 (by rfl) ⟨3063716, by rfl⟩ : syracuseStep 4084955 = 6127433) B6127433
theorem B1701151 : Blo 1699550 1701151 := bstep (se 1 (by rfl) ⟨1275863, by rfl⟩ : syracuseStep 1701151 = 2551727) B2551727
theorem B1914151 : Blo 1699550 1914151 := bstep (se 1 (by rfl) ⟨1435613, by rfl⟩ : syracuseStep 1914151 = 2871227) B2871227
theorem B14529881 : Blo 1699550 14529881 := bstep (se 2 (by rfl) ⟨5448705, by rfl⟩ : syracuseStep 14529881 = 10897411) B10897411
theorem B1701211 : Blo 1699550 1701211 := bstep (se 1 (by rfl) ⟨1275908, by rfl⟩ : syracuseStep 1701211 = 2551817) B2551817
theorem B1701231 : Blo 1699550 1701231 := bstep (se 1 (by rfl) ⟨1275923, by rfl⟩ : syracuseStep 1701231 = 2551847) B2551847
theorem B1914223 : Blo 1699550 1914223 := bstep (se 1 (by rfl) ⟨1435667, by rfl⟩ : syracuseStep 1914223 = 2871335) B2871335
theorem B119387525 : Blo 1699550 119387525 := bstep (se 4 (by rfl) ⟨11192580, by rfl⟩ : syracuseStep 119387525 = 22385161) B22385161
theorem B1701287 : Blo 1699550 1701287 := bstep (se 1 (by rfl) ⟨1275965, by rfl⟩ : syracuseStep 1701287 = 2551931) B2551931
theorem B12260801 : Blo 1699550 12260801 := bstep (se 2 (by rfl) ⟨4597800, by rfl⟩ : syracuseStep 12260801 = 9195601) B9195601
theorem B1701371 : Blo 1699550 1701371 := bstep (se 1 (by rfl) ⟨1276028, by rfl⟩ : syracuseStep 1701371 = 2552057) B2552057
theorem B1701439 : Blo 1699550 1701439 := bstep (se 1 (by rfl) ⟨1276079, by rfl⟩ : syracuseStep 1701439 = 2552159) B2552159
theorem B1701447 : Blo 1699550 1701447 := bstep (se 1 (by rfl) ⟨1276085, by rfl⟩ : syracuseStep 1701447 = 2552171) B2552171
theorem B4306729 : Blo 1699550 4306729 := bstep (se 2 (by rfl) ⟨1615023, by rfl⟩ : syracuseStep 4306729 = 3230047) B3230047
theorem B6453047 : Blo 1699550 6453047 := bstep (se 1 (by rfl) ⟨4839785, by rfl⟩ : syracuseStep 6453047 = 9679571) B9679571
theorem B2152271 : Blo 1699550 2152271 := bstep (se 1 (by rfl) ⟨1614203, by rfl⟩ : syracuseStep 2152271 = 3228407) B3228407
theorem B5519191 : Blo 1699550 5519191 := bstep (se 1 (by rfl) ⟨4139393, by rfl⟩ : syracuseStep 5519191 = 8278787) B8278787
theorem B2152423 : Blo 1699550 2152423 := bstep (se 1 (by rfl) ⟨1614317, by rfl⟩ : syracuseStep 2152423 = 3228635) B3228635
theorem B6453229 : Blo 1699550 6453229 := bstep (se 3 (by rfl) ⟨1209980, by rfl⟩ : syracuseStep 6453229 = 2419961) B2419961
theorem B5740577 : Blo 1699550 5740577 := bstep (se 2 (by rfl) ⟨2152716, by rfl⟩ : syracuseStep 5740577 = 4305433) B4305433
theorem B16349465 : Blo 1699550 16349465 := bstep (se 2 (by rfl) ⟨6131049, by rfl⟩ : syracuseStep 16349465 = 12262099) B12262099
theorem B6453533 : Blo 1699550 6453533 := bstep (se 3 (by rfl) ⟨1210037, by rfl⟩ : syracuseStep 6453533 = 2420075) B2420075
theorem B1939835 : Blo 1699550 1939835 := bstep (se 1 (by rfl) ⟨1454876, by rfl⟩ : syracuseStep 1939835 = 2909753) B2909753
theorem B6453715 : Blo 1699550 6453715 := bstep (se 1 (by rfl) ⟨4840286, by rfl⟩ : syracuseStep 6453715 = 9680573) B9680573
theorem B3824207 : Blo 1699550 3824207 := bstep (se 1 (by rfl) ⟨2868155, by rfl⟩ : syracuseStep 3824207 = 5736311) B5736311
theorem B66239117 : Blo 1699550 66239117 := bstep (se 3 (by rfl) ⟨12419834, by rfl⟩ : syracuseStep 66239117 = 24839669) B24839669
theorem B3824351 : Blo 1699550 3824351 := bstep (se 1 (by rfl) ⟨2868263, by rfl⟩ : syracuseStep 3824351 = 5736527) B5736527
theorem B4086607 : Blo 1699550 4086607 := bstep (se 1 (by rfl) ⟨3064955, by rfl⟩ : syracuseStep 4086607 = 6129911) B6129911
theorem B13089691 : Blo 1699550 13089691 := bstep (se 1 (by rfl) ⟨9817268, by rfl⟩ : syracuseStep 13089691 = 19634537) B19634537
theorem B6454187 : Blo 1699550 6454187 := bstep (se 1 (by rfl) ⟨4840640, by rfl⟩ : syracuseStep 6454187 = 9681281) B9681281
theorem B9690029 : Blo 1699550 9690029 := bstep (se 3 (by rfl) ⟨1816880, by rfl⟩ : syracuseStep 9690029 = 3633761) B3633761
theorem B3824603 : Blo 1699550 3824603 := bstep (se 1 (by rfl) ⟨2868452, by rfl⟩ : syracuseStep 3824603 = 5736905) B5736905
theorem B3824783 : Blo 1699550 3824783 := bstep (se 1 (by rfl) ⟨2868587, by rfl⟩ : syracuseStep 3824783 = 5737175) B5737175
theorem B3316879 : Blo 1699550 3316879 := bstep (se 1 (by rfl) ⟨2487659, by rfl⟩ : syracuseStep 3316879 = 4975319) B4975319
theorem B13786301 : Blo 1699550 13786301 := bstep (se 3 (by rfl) ⟨2584931, by rfl⟩ : syracuseStep 13786301 = 5169863) B5169863
theorem B3824873 : Blo 1699550 3824873 := bstep (se 2 (by rfl) ⟨1434327, by rfl⟩ : syracuseStep 3824873 = 2868655) B2868655
theorem B2620649 : Blo 1699550 2620649 := bstep (se 2 (by rfl) ⟨982743, by rfl⟩ : syracuseStep 2620649 = 1965487) B1965487
theorem B3824927 : Blo 1699550 3824927 := bstep (se 1 (by rfl) ⟨2868695, by rfl⟩ : syracuseStep 3824927 = 5737391) B5737391
theorem B6896927 : Blo 1699550 6896927 := bstep (se 1 (by rfl) ⟨5172695, by rfl⟩ : syracuseStep 6896927 = 10345391) B10345391
theorem B46562597 : Blo 1699550 46562597 := bstep (se 4 (by rfl) ⟨4365243, by rfl⟩ : syracuseStep 46562597 = 8730487) B8730487
theorem B8174945 : Blo 1699550 8174945 := bstep (se 2 (by rfl) ⟨3065604, by rfl⟩ : syracuseStep 8174945 = 6131209) B6131209
theorem B6987145 : Blo 1699550 6987145 := bstep (se 2 (by rfl) ⟨2620179, by rfl⟩ : syracuseStep 6987145 = 5240359) B5240359
theorem B8175097 : Blo 1699550 8175097 := bstep (se 2 (by rfl) ⟨3065661, by rfl⟩ : syracuseStep 8175097 = 6131323) B6131323
theorem B16350731 : Blo 1699550 16350731 := bstep (se 1 (by rfl) ⟨12263048, by rfl⟩ : syracuseStep 16350731 = 24526097) B24526097
theorem B12910103 : Blo 1699550 12910103 := bstep (se 1 (by rfl) ⟨9682577, by rfl⟩ : syracuseStep 12910103 = 19365155) B19365155
theorem B32702075 : Blo 1699550 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B8609489 : Blo 1699550 8609489 := bstep (se 2 (by rfl) ⟨3228558, by rfl⟩ : syracuseStep 8609489 = 6457117) B6457117
theorem B3825449 : Blo 1699550 3825449 := bstep (se 2 (by rfl) ⟨1434543, by rfl⟩ : syracuseStep 3825449 = 2869087) B2869087
theorem B31023485 : Blo 1699550 31023485 := bstep (se 3 (by rfl) ⟨5816903, by rfl⟩ : syracuseStep 31023485 = 11633807) B11633807
theorem B4841927 : Blo 1699550 4841927 := bstep (se 1 (by rfl) ⟨3631445, by rfl⟩ : syracuseStep 4841927 = 7262891) B7262891
theorem B3228103 : Blo 1699550 3228103 := bstep (se 1 (by rfl) ⟨2421077, by rfl⟩ : syracuseStep 3228103 = 4842155) B4842155
theorem B27583037 : Blo 1699550 27583037 := bstep (se 3 (by rfl) ⟨5171819, by rfl⟩ : syracuseStep 27583037 = 10343639) B10343639
theorem B18391805 : Blo 1699550 18391805 := bstep (se 3 (by rfl) ⟨3448463, by rfl⟩ : syracuseStep 18391805 = 6896927) B6896927
theorem B6546187 : Blo 1699550 6546187 := bstep (se 1 (by rfl) ⟨4909640, by rfl⟩ : syracuseStep 6546187 = 9819281) B9819281
theorem B12911561 : Blo 1699550 12911561 := bstep (se 2 (by rfl) ⟨4841835, by rfl⟩ : syracuseStep 12911561 = 9683671) B9683671
theorem B447046721 : Blo 1699550 447046721 := bstep (se 2 (by rfl) ⟨167642520, by rfl⟩ : syracuseStep 447046721 = 335285041) B335285041
theorem B5448809 : Blo 1699550 5448809 := bstep (se 2 (by rfl) ⟨2043303, by rfl⟩ : syracuseStep 5448809 = 4086607) B4086607
theorem B2868331 : Blo 1699550 2868331 := bstep (se 1 (by rfl) ⟨2151248, by rfl⟩ : syracuseStep 2868331 = 4302497) B4302497
theorem B4302031 : Blo 1699550 4302031 := bstep (se 1 (by rfl) ⟨3226523, by rfl⟩ : syracuseStep 4302031 = 6453047) B6453047
theorem B2551673 : Blo 1699550 2551673 := bstep (se 2 (by rfl) ⟨956877, by rfl⟩ : syracuseStep 2551673 = 1913755) B1913755
theorem B3827051 : Blo 1699550 3827051 := bstep (se 1 (by rfl) ⟨2870288, by rfl⟩ : syracuseStep 3827051 = 5740577) B5740577
theorem B2868635 : Blo 1699550 2868635 := bstep (se 1 (by rfl) ⟨2151476, by rfl⟩ : syracuseStep 2868635 = 4302953) B4302953
theorem B3065243 : Blo 1699550 3065243 := bstep (se 1 (by rfl) ⟨2298932, by rfl⟩ : syracuseStep 3065243 = 4597865) B4597865
theorem B7259645 : Blo 1699550 7259645 := bstep (se 3 (by rfl) ⟨1361183, by rfl⟩ : syracuseStep 7259645 = 2722367) B2722367
theorem B4302355 : Blo 1699550 4302355 := bstep (se 1 (by rfl) ⟨3226766, by rfl⟩ : syracuseStep 4302355 = 6453533) B6453533
theorem B2549369 : Blo 1699550 2549369 := bstep (se 2 (by rfl) ⟨956013, by rfl⟩ : syracuseStep 2549369 = 1912027) B1912027
theorem B3827321 : Blo 1699550 3827321 := bstep (se 2 (by rfl) ⟨1435245, by rfl⟩ : syracuseStep 3827321 = 2870491) B2870491
theorem B111814357 : Blo 1699550 111814357 := bstep (se 7 (by rfl) ⟨1310324, by rfl⟩ : syracuseStep 111814357 = 2620649) B2620649
theorem B2868959 : Blo 1699550 2868959 := bstep (se 1 (by rfl) ⟨2151719, by rfl⟩ : syracuseStep 2868959 = 4303439) B4303439
theorem B2549471 : Blo 1699550 2549471 := bstep (se 1 (by rfl) ⟨1912103, by rfl⟩ : syracuseStep 2549471 = 3824207) B3824207
theorem B2549567 : Blo 1699550 2549567 := bstep (se 1 (by rfl) ⟨1912175, by rfl⟩ : syracuseStep 2549567 = 3824351) B3824351
theorem B5244751 : Blo 1699550 5244751 := bstep (se 1 (by rfl) ⟨3933563, by rfl⟩ : syracuseStep 5244751 = 7867127) B7867127
theorem B9316193 : Blo 1699550 9316193 := bstep (se 2 (by rfl) ⟨3493572, by rfl⟩ : syracuseStep 9316193 = 6987145) B6987145
theorem B5171041 : Blo 1699550 5171041 := bstep (se 2 (by rfl) ⟨1939140, by rfl⟩ : syracuseStep 5171041 = 3878281) B3878281
theorem B4302791 : Blo 1699550 4302791 := bstep (se 1 (by rfl) ⟨3227093, by rfl⟩ : syracuseStep 4302791 = 6454187) B6454187
theorem B2549735 : Blo 1699550 2549735 := bstep (se 1 (by rfl) ⟨1912301, by rfl⟩ : syracuseStep 2549735 = 3824603) B3824603
theorem B2549753 : Blo 1699550 2549753 := bstep (se 2 (by rfl) ⟨956157, by rfl⟩ : syracuseStep 2549753 = 1912315) B1912315
theorem B2549855 : Blo 1699550 2549855 := bstep (se 1 (by rfl) ⟨1912391, by rfl⟩ : syracuseStep 2549855 = 3824783) B3824783
theorem B19368071 : Blo 1699550 19368071 := bstep (se 1 (by rfl) ⟨14526053, by rfl⟩ : syracuseStep 19368071 = 29052107) B29052107
theorem B2869391 : Blo 1699550 2869391 := bstep (se 1 (by rfl) ⟨2152043, by rfl⟩ : syracuseStep 2869391 = 4304087) B4304087
theorem B2549915 : Blo 1699550 2549915 := bstep (se 1 (by rfl) ⟨1912436, by rfl⟩ : syracuseStep 2549915 = 3824873) B3824873
theorem B2549951 : Blo 1699550 2549951 := bstep (se 1 (by rfl) ⟨1912463, by rfl⟩ : syracuseStep 2549951 = 3824927) B3824927
theorem B31041731 : Blo 1699550 31041731 := bstep (se 1 (by rfl) ⟨23281298, by rfl⟩ : syracuseStep 31041731 = 46562597) B46562597
theorem B2549993 : Blo 1699550 2549993 := bstep (se 2 (by rfl) ⟨956247, by rfl⟩ : syracuseStep 2549993 = 1912495) B1912495
theorem B5449963 : Blo 1699550 5449963 := bstep (se 1 (by rfl) ⟨4087472, by rfl⟩ : syracuseStep 5449963 = 8174945) B8174945
theorem B5736743 : Blo 1699550 5736743 := bstep (se 1 (by rfl) ⟨4302557, by rfl⟩ : syracuseStep 5736743 = 8605115) B8605115
theorem B2869627 : Blo 1699550 2869627 := bstep (se 1 (by rfl) ⟨2152220, by rfl⟩ : syracuseStep 2869627 = 4304441) B4304441
theorem B5450141 : Blo 1699550 5450141 := bstep (se 3 (by rfl) ⟨1021901, by rfl⟩ : syracuseStep 5450141 = 2043803) B2043803
theorem B21801383 : Blo 1699550 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B7358921 : Blo 1699550 7358921 := bstep (se 2 (by rfl) ⟨2759595, by rfl⟩ : syracuseStep 7358921 = 5519191) B5519191
theorem B17926667 : Blo 1699550 17926667 := bstep (se 1 (by rfl) ⟨13445000, by rfl⟩ : syracuseStep 17926667 = 26890001) B26890001
theorem B2550299 : Blo 1699550 2550299 := bstep (se 1 (by rfl) ⟨1912724, by rfl⟩ : syracuseStep 2550299 = 3825449) B3825449
theorem B2550377 : Blo 1699550 2550377 := bstep (se 2 (by rfl) ⟨956391, by rfl⟩ : syracuseStep 2550377 = 1912783) B1912783
theorem B4844137 : Blo 1699550 4844137 := bstep (se 2 (by rfl) ⟨1816551, by rfl⟩ : syracuseStep 4844137 = 3633103) B3633103
theorem B3828329 : Blo 1699550 3828329 := bstep (se 2 (by rfl) ⟨1435623, by rfl⟩ : syracuseStep 3828329 = 2871247) B2871247
theorem B2869897 : Blo 1699550 2869897 := bstep (se 2 (by rfl) ⟨1076211, by rfl⟩ : syracuseStep 2869897 = 2152423) B2152423
theorem B8604305 : Blo 1699550 8604305 := bstep (se 2 (by rfl) ⟨3226614, by rfl⟩ : syracuseStep 8604305 = 6453229) B6453229
theorem B21793697 : Blo 1699550 21793697 := bstep (se 2 (by rfl) ⟨8172636, by rfl⟩ : syracuseStep 21793697 = 16345273) B16345273
theorem B23276483 : Blo 1699550 23276483 := bstep (se 1 (by rfl) ⟨17457362, by rfl⟩ : syracuseStep 23276483 = 34914725) B34914725
theorem B2550905 : Blo 1699550 2550905 := bstep (se 2 (by rfl) ⟨956589, by rfl⟩ : syracuseStep 2550905 = 1913179) B1913179
theorem B5737607 : Blo 1699550 5737607 := bstep (se 1 (by rfl) ⟨4303205, by rfl⟩ : syracuseStep 5737607 = 8606411) B8606411
theorem B13790351 : Blo 1699550 13790351 := bstep (se 1 (by rfl) ⟨10342763, by rfl⟩ : syracuseStep 13790351 = 20685527) B20685527
theorem B2551007 : Blo 1699550 2551007 := bstep (se 1 (by rfl) ⟨1913255, by rfl⟩ : syracuseStep 2551007 = 3826511) B3826511
theorem B5737715 : Blo 1699550 5737715 := bstep (se 1 (by rfl) ⟨4303286, by rfl⟩ : syracuseStep 5737715 = 8606573) B8606573
theorem B2551049 : Blo 1699550 2551049 := bstep (se 2 (by rfl) ⟨956643, by rfl⟩ : syracuseStep 2551049 = 1913287) B1913287
theorem B8604953 : Blo 1699550 8604953 := bstep (se 2 (by rfl) ⟨3226857, by rfl⟩ : syracuseStep 8604953 = 6453715) B6453715
theorem B2420047 : Blo 1699550 2420047 := bstep (se 1 (by rfl) ⟨1815035, by rfl⟩ : syracuseStep 2420047 = 3630071) B3630071
theorem B2551151 : Blo 1699550 2551151 := bstep (se 1 (by rfl) ⟨1913363, by rfl⟩ : syracuseStep 2551151 = 3826727) B3826727
theorem B17690021 : Blo 1699550 17690021 := bstep (se 4 (by rfl) ⟨1658439, by rfl⟩ : syracuseStep 17690021 = 3316879) B3316879
theorem B2723303 : Blo 1699550 2723303 := bstep (se 1 (by rfl) ⟨2042477, by rfl⟩ : syracuseStep 2723303 = 4084955) B4084955
theorem B2551271 : Blo 1699550 2551271 := bstep (se 1 (by rfl) ⟨1913453, by rfl⟩ : syracuseStep 2551271 = 3826907) B3826907
theorem B9686587 : Blo 1699550 9686587 := bstep (se 1 (by rfl) ⟨7264940, by rfl⟩ : syracuseStep 9686587 = 14529881) B14529881
theorem B2551403 : Blo 1699550 2551403 := bstep (se 1 (by rfl) ⟨1913552, by rfl⟩ : syracuseStep 2551403 = 3827105) B3827105
theorem B5172893 : Blo 1699550 5172893 := bstep (se 3 (by rfl) ⟨969917, by rfl⟩ : syracuseStep 5172893 = 1939835) B1939835
theorem B2551529 : Blo 1699550 2551529 := bstep (se 2 (by rfl) ⟨956823, by rfl⟩ : syracuseStep 2551529 = 1913647) B1913647
theorem B1699655 : Blo 1699550 1699655 := bstep (se 1 (by rfl) ⟨1274741, by rfl⟩ : syracuseStep 1699655 = 2549483) B2549483
theorem B17452921 : Blo 1699550 17452921 := bstep (se 2 (by rfl) ⟨6544845, by rfl⟩ : syracuseStep 17452921 = 13089691) B13089691
theorem B3682169 : Blo 1699550 3682169 := bstep (se 2 (by rfl) ⟨1380813, by rfl⟩ : syracuseStep 3682169 = 2761627) B2761627
theorem B3633017 : Blo 1699550 3633017 := bstep (se 2 (by rfl) ⟨1362381, by rfl⟩ : syracuseStep 3633017 = 2724763) B2724763
theorem B39268253 : Blo 1699550 39268253 := bstep (se 3 (by rfl) ⟨7362797, by rfl⟩ : syracuseStep 39268253 = 14725595) B14725595
theorem B1699807 : Blo 1699550 1699807 := bstep (se 1 (by rfl) ⟨1274855, by rfl⟩ : syracuseStep 1699807 = 2549711) B2549711
theorem B2551775 : Blo 1699550 2551775 := bstep (se 1 (by rfl) ⟨1913831, by rfl⟩ : syracuseStep 2551775 = 3827663) B3827663
theorem B1273466933 : Blo 1699550 1273466933 := bstep (se 5 (by rfl) ⟨59693762, by rfl⟩ : syracuseStep 1273466933 = 119387525) B119387525
theorem B10899643 : Blo 1699550 10899643 := bstep (se 1 (by rfl) ⟨8174732, by rfl⟩ : syracuseStep 10899643 = 16349465) B16349465
theorem B2552027 : Blo 1699550 2552027 := bstep (se 1 (by rfl) ⟨1914020, by rfl⟩ : syracuseStep 2552027 = 3828041) B3828041
theorem B1700071 : Blo 1699550 1700071 := bstep (se 1 (by rfl) ⟨1275053, by rfl⟩ : syracuseStep 1700071 = 2550107) B2550107
theorem B2552039 : Blo 1699550 2552039 := bstep (se 1 (by rfl) ⟨1914029, by rfl⟩ : syracuseStep 2552039 = 3828059) B3828059
theorem B12423461 : Blo 1699550 12423461 := bstep (se 4 (by rfl) ⟨1164699, by rfl⟩ : syracuseStep 12423461 = 2329399) B2329399
theorem B50377067 : Blo 1699550 50377067 := bstep (se 1 (by rfl) ⟨37782800, by rfl⟩ : syracuseStep 50377067 = 75565601) B75565601
theorem B1700223 : Blo 1699550 1700223 := bstep (se 1 (by rfl) ⟨1275167, by rfl⟩ : syracuseStep 1700223 = 2550335) B2550335
theorem B1913215 : Blo 1699550 1913215 := bstep (se 1 (by rfl) ⟨1434911, by rfl⟩ : syracuseStep 1913215 = 2869823) B2869823
theorem B2552201 : Blo 1699550 2552201 := bstep (se 2 (by rfl) ⟨957075, by rfl⟩ : syracuseStep 2552201 = 1914151) B1914151
theorem B44159411 : Blo 1699550 44159411 := bstep (se 1 (by rfl) ⟨33119558, by rfl⟩ : syracuseStep 44159411 = 66239117) B66239117
theorem B1700303 : Blo 1699550 1700303 := bstep (se 1 (by rfl) ⟨1275227, by rfl⟩ : syracuseStep 1700303 = 2550455) B2550455
theorem B2552297 : Blo 1699550 2552297 := bstep (se 2 (by rfl) ⟨957111, by rfl⟩ : syracuseStep 2552297 = 1914223) B1914223
theorem B1700455 : Blo 1699550 1700455 := bstep (se 1 (by rfl) ⟨1275341, by rfl⟩ : syracuseStep 1700455 = 2550683) B2550683
theorem B6460019 : Blo 1699550 6460019 := bstep (se 1 (by rfl) ⟨4845014, by rfl⟩ : syracuseStep 6460019 = 9690029) B9690029
theorem B10900129 : Blo 1699550 10900129 := bstep (se 2 (by rfl) ⟨4087548, by rfl⟩ : syracuseStep 10900129 = 8175097) B8175097
theorem B1700719 : Blo 1699550 1700719 := bstep (se 1 (by rfl) ⟨1275539, by rfl⟩ : syracuseStep 1700719 = 2551079) B2551079
theorem B5739389 : Blo 1699550 5739389 := bstep (se 3 (by rfl) ⟨1076135, by rfl⟩ : syracuseStep 5739389 = 2152271) B2152271
theorem B1700775 : Blo 1699550 1700775 := bstep (se 1 (by rfl) ⟨1275581, by rfl⟩ : syracuseStep 1700775 = 2551163) B2551163
theorem B1700859 : Blo 1699550 1700859 := bstep (se 1 (by rfl) ⟨1275644, by rfl⟩ : syracuseStep 1700859 = 2551289) B2551289
theorem B10900487 : Blo 1699550 10900487 := bstep (se 1 (by rfl) ⟨8175365, by rfl⟩ : syracuseStep 10900487 = 16350731) B16350731
theorem B8606735 : Blo 1699550 8606735 := bstep (se 1 (by rfl) ⟨6455051, by rfl⟩ : syracuseStep 8606735 = 12910103) B12910103
theorem B1700927 : Blo 1699550 1700927 := bstep (se 1 (by rfl) ⟨1275695, by rfl⟩ : syracuseStep 1700927 = 2551391) B2551391
theorem B5739659 : Blo 1699550 5739659 := bstep (se 1 (by rfl) ⟨4304744, by rfl⟩ : syracuseStep 5739659 = 8609489) B8609489
theorem B1701071 : Blo 1699550 1701071 := bstep (se 1 (by rfl) ⟨1275803, by rfl⟩ : syracuseStep 1701071 = 2551607) B2551607
theorem B12260717 : Blo 1699550 12260717 := bstep (se 3 (by rfl) ⟨2298884, by rfl⟩ : syracuseStep 12260717 = 4597769) B4597769
theorem B2422171 : Blo 1699550 2422171 := bstep (se 1 (by rfl) ⟨1816628, by rfl⟩ : syracuseStep 2422171 = 3633257) B3633257
theorem B1701275 : Blo 1699550 1701275 := bstep (se 1 (by rfl) ⟨1275956, by rfl⟩ : syracuseStep 1701275 = 2551913) B2551913
theorem B1701487 : Blo 1699550 1701487 := bstep (se 1 (by rfl) ⟨1276115, by rfl⟩ : syracuseStep 1701487 = 2552231) B2552231
theorem B1701543 : Blo 1699550 1701543 := bstep (se 1 (by rfl) ⟨1276157, by rfl⟩ : syracuseStep 1701543 = 2552315) B2552315
theorem B24516407 : Blo 1699550 24516407 := bstep (se 1 (by rfl) ⟨18387305, by rfl⟩ : syracuseStep 24516407 = 36774611) B36774611
theorem B8607545 : Blo 1699550 8607545 := bstep (se 2 (by rfl) ⟨3227829, by rfl⟩ : syracuseStep 8607545 = 6455659) B6455659
theorem B6297401 : Blo 1699550 6297401 := bstep (se 2 (by rfl) ⟨2361525, by rfl⟩ : syracuseStep 6297401 = 4723051) B4723051
theorem B36763469 : Blo 1699550 36763469 := bstep (se 3 (by rfl) ⟨6893150, by rfl⟩ : syracuseStep 36763469 = 13786301) B13786301
theorem B31045513 : Blo 1699550 31045513 := bstep (se 2 (by rfl) ⟨11642067, by rfl⟩ : syracuseStep 31045513 = 23284135) B23284135
theorem B4085723 : Blo 1699550 4085723 := bstep (se 1 (by rfl) ⟨3064292, by rfl⟩ : syracuseStep 4085723 = 6128585) B6128585
theorem B21780575 : Blo 1699550 21780575 := bstep (se 1 (by rfl) ⟨16335431, by rfl⟩ : syracuseStep 21780575 = 32670863) B32670863
theorem B20977825 : Blo 1699550 20977825 := bstep (se 2 (by rfl) ⟨7866684, by rfl⟩ : syracuseStep 20977825 = 15733369) B15733369
theorem B12253477 : Blo 1699550 12253477 := bstep (se 4 (by rfl) ⟨1148763, by rfl⟩ : syracuseStep 12253477 = 2297527) B2297527
theorem B8173867 : Blo 1699550 8173867 := bstep (se 1 (by rfl) ⟨6130400, by rfl⟩ : syracuseStep 8173867 = 12260801) B12260801
theorem B43604405 : Blo 1699550 43604405 := bstep (se 5 (by rfl) ⟨2043956, by rfl⟩ : syracuseStep 43604405 = 4087913) B4087913
theorem B5741279 : Blo 1699550 5741279 := bstep (se 1 (by rfl) ⟨4305959, by rfl⟩ : syracuseStep 5741279 = 8611919) B8611919
theorem B3824711 : Blo 1699550 3824711 := bstep (se 1 (by rfl) ⟨2868533, by rfl⟩ : syracuseStep 3824711 = 5737067) B5737067
theorem B5815481 : Blo 1699550 5815481 := bstep (se 2 (by rfl) ⟨2180805, by rfl⟩ : syracuseStep 5815481 = 4361611) B4361611
theorem B4840697 : Blo 1699550 4840697 := bstep (se 2 (by rfl) ⟨1815261, by rfl⟩ : syracuseStep 4840697 = 3630523) B3630523
theorem B21257633 : Blo 1699550 21257633 := bstep (se 2 (by rfl) ⟨7971612, by rfl⟩ : syracuseStep 21257633 = 15943225) B15943225
theorem B3825107 : Blo 1699550 3825107 := bstep (se 1 (by rfl) ⟨2868830, by rfl⟩ : syracuseStep 3825107 = 5737661) B5737661
theorem B5742035 : Blo 1699550 5742035 := bstep (se 1 (by rfl) ⟨4306526, by rfl⟩ : syracuseStep 5742035 = 8613053) B8613053
theorem B4841039 : Blo 1699550 4841039 := bstep (se 1 (by rfl) ⟨3630779, by rfl⟩ : syracuseStep 4841039 = 7261559) B7261559
theorem B1891931 : Blo 1699550 1891931 := bstep (se 1 (by rfl) ⟨1418948, by rfl⟩ : syracuseStep 1891931 = 2837897) B2837897
theorem B3825377 : Blo 1699550 3825377 := bstep (se 2 (by rfl) ⟨1434516, by rfl⟩ : syracuseStep 3825377 = 2869033) B2869033
theorem B5742305 : Blo 1699550 5742305 := bstep (se 2 (by rfl) ⟨2153364, by rfl⟩ : syracuseStep 5742305 = 4306729) B4306729
theorem B848977955 : Blo 1699550 848977955 := bstep (se 1 (by rfl) ⟨636733466, by rfl⟩ : syracuseStep 848977955 = 1273466933) B1273466933
theorem B14532857 : Blo 1699550 14532857 := bstep (se 2 (by rfl) ⟨5449821, by rfl⟩ : syracuseStep 14532857 = 10899643) B10899643
theorem B3227951 : Blo 1699550 3227951 := bstep (se 1 (by rfl) ⟨2420963, by rfl⟩ : syracuseStep 3227951 = 4841927) B4841927
theorem B7266617 : Blo 1699550 7266617 := bstep (se 2 (by rfl) ⟨2724981, by rfl⟩ : syracuseStep 7266617 = 5449963) B5449963
theorem B36774269 : Blo 1699550 36774269 := bstep (se 3 (by rfl) ⟨6895175, by rfl⟩ : syracuseStep 36774269 = 13790351) B13790351
theorem B15507949 : Blo 1699550 15507949 := bstep (se 3 (by rfl) ⟨2907740, by rfl⟩ : syracuseStep 15507949 = 5815481) B5815481
theorem B3826169 : Blo 1699550 3826169 := bstep (se 2 (by rfl) ⟨1434813, by rfl⟩ : syracuseStep 3826169 = 2869627) B2869627
theorem B3826259 : Blo 1699550 3826259 := bstep (se 1 (by rfl) ⟨2869694, by rfl⟩ : syracuseStep 3826259 = 5739389) B5739389
theorem B7266991 : Blo 1699550 7266991 := bstep (se 1 (by rfl) ⟨5450243, by rfl⟩ : syracuseStep 7266991 = 10900487) B10900487
theorem B3826439 : Blo 1699550 3826439 := bstep (se 1 (by rfl) ⟨2869829, by rfl⟩ : syracuseStep 3826439 = 5739659) B5739659
theorem B33129229 : Blo 1699550 33129229 := bstep (se 3 (by rfl) ⟨6211730, by rfl⟩ : syracuseStep 33129229 = 12423461) B12423461
theorem B3826529 : Blo 1699550 3826529 := bstep (se 2 (by rfl) ⟨1434948, by rfl⟩ : syracuseStep 3826529 = 2869897) B2869897
theorem B14533505 : Blo 1699550 14533505 := bstep (se 2 (by rfl) ⟨5450064, by rfl⟩ : syracuseStep 14533505 = 10900129) B10900129
theorem B16344271 : Blo 1699550 16344271 := bstep (se 1 (by rfl) ⟨12258203, by rfl⟩ : syracuseStep 16344271 = 24516407) B24516407
theorem B2868527 : Blo 1699550 2868527 := bstep (se 1 (by rfl) ⟨2151395, by rfl⟩ : syracuseStep 2868527 = 4302791) B4302791
theorem B12912047 : Blo 1699550 12912047 := bstep (se 1 (by rfl) ⟨9684035, by rfl⟩ : syracuseStep 12912047 = 19368071) B19368071
theorem B20694487 : Blo 1699550 20694487 := bstep (se 1 (by rfl) ⟨15520865, by rfl⟩ : syracuseStep 20694487 = 31041731) B31041731
theorem B5736041 : Blo 1699550 5736041 := bstep (se 2 (by rfl) ⟨2151015, by rfl⟩ : syracuseStep 5736041 = 4302031) B4302031
theorem B14534255 : Blo 1699550 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B5736203 : Blo 1699550 5736203 := bstep (se 1 (by rfl) ⟨4302152, by rfl⟩ : syracuseStep 5736203 = 8604305) B8604305
theorem B3827519 : Blo 1699550 3827519 := bstep (se 1 (by rfl) ⟨2870639, by rfl⟩ : syracuseStep 3827519 = 5741279) B5741279
theorem B3229561 : Blo 1699550 3229561 := bstep (se 2 (by rfl) ⟨1211085, by rfl⟩ : syracuseStep 3229561 = 2422171) B2422171
theorem B15517655 : Blo 1699550 15517655 := bstep (se 1 (by rfl) ⟨11638241, by rfl⟩ : syracuseStep 15517655 = 23276483) B23276483
theorem B5736473 : Blo 1699550 5736473 := bstep (se 2 (by rfl) ⟨2151177, by rfl⟩ : syracuseStep 5736473 = 4302355) B4302355
theorem B2549807 : Blo 1699550 2549807 := bstep (se 1 (by rfl) ⟨1912355, by rfl⟩ : syracuseStep 2549807 = 3824711) B3824711
theorem B5736635 : Blo 1699550 5736635 := bstep (se 1 (by rfl) ⟨4302476, by rfl⟩ : syracuseStep 5736635 = 8604953) B8604953
theorem B2550071 : Blo 1699550 2550071 := bstep (se 1 (by rfl) ⟨1912553, by rfl⟩ : syracuseStep 2550071 = 3825107) B3825107
theorem B3828023 : Blo 1699550 3828023 := bstep (se 1 (by rfl) ⟨2871017, by rfl⟩ : syracuseStep 3828023 = 5742035) B5742035
theorem B2550251 : Blo 1699550 2550251 := bstep (se 1 (by rfl) ⟨1912688, by rfl⟩ : syracuseStep 2550251 = 3825377) B3825377
theorem B3828203 : Blo 1699550 3828203 := bstep (se 1 (by rfl) ⟨2871152, by rfl⟩ : syracuseStep 3828203 = 5742305) B5742305
theorem B27970433 : Blo 1699550 27970433 := bstep (se 2 (by rfl) ⟨10488912, by rfl⟩ : syracuseStep 27970433 = 20977825) B20977825
theorem B16337969 : Blo 1699550 16337969 := bstep (se 2 (by rfl) ⟨6126738, by rfl⟩ : syracuseStep 16337969 = 12253477) B12253477
theorem B10898489 : Blo 1699550 10898489 := bstep (se 2 (by rfl) ⟨4086933, by rfl⟩ : syracuseStep 10898489 = 8173867) B8173867
theorem B2550953 : Blo 1699550 2550953 := bstep (se 2 (by rfl) ⟨956607, by rfl⟩ : syracuseStep 2550953 = 1913215) B1913215
theorem B4304137 : Blo 1699550 4304137 := bstep (se 2 (by rfl) ⟨1614051, by rfl⟩ : syracuseStep 4304137 = 3228103) B3228103
theorem B5737823 : Blo 1699550 5737823 := bstep (se 1 (by rfl) ⟨4303367, by rfl⟩ : syracuseStep 5737823 = 8606735) B8606735
theorem B3632539 : Blo 1699550 3632539 := bstep (se 1 (by rfl) ⟨2724404, by rfl⟩ : syracuseStep 3632539 = 5448809) B5448809
theorem B6458849 : Blo 1699550 6458849 := bstep (se 2 (by rfl) ⟨2422068, by rfl⟩ : syracuseStep 6458849 = 4844137) B4844137
theorem B2551367 : Blo 1699550 2551367 := bstep (se 1 (by rfl) ⟨1913525, by rfl⟩ : syracuseStep 2551367 = 3827051) B3827051
theorem B1912423 : Blo 1699550 1912423 := bstep (se 1 (by rfl) ⟨1434317, by rfl⟩ : syracuseStep 1912423 = 2868635) B2868635
theorem B8728249 : Blo 1699550 8728249 := bstep (se 2 (by rfl) ⟨3273093, by rfl⟩ : syracuseStep 8728249 = 6546187) B6546187
theorem B1699579 : Blo 1699550 1699579 := bstep (se 1 (by rfl) ⟨1274684, by rfl⟩ : syracuseStep 1699579 = 2549369) B2549369
theorem B2551547 : Blo 1699550 2551547 := bstep (se 1 (by rfl) ⟨1913660, by rfl⟩ : syracuseStep 2551547 = 3827321) B3827321
theorem B1699647 : Blo 1699550 1699647 := bstep (se 1 (by rfl) ⟨1274735, by rfl⟩ : syracuseStep 1699647 = 2549471) B2549471
theorem B1912639 : Blo 1699550 1912639 := bstep (se 1 (by rfl) ⟨1434479, by rfl⟩ : syracuseStep 1912639 = 2868959) B2868959
theorem B5738363 : Blo 1699550 5738363 := bstep (se 1 (by rfl) ⟨4303772, by rfl⟩ : syracuseStep 5738363 = 8607545) B8607545
theorem B4198267 : Blo 1699550 4198267 := bstep (se 1 (by rfl) ⟨3148700, by rfl⟩ : syracuseStep 4198267 = 6297401) B6297401
theorem B1699711 : Blo 1699550 1699711 := bstep (se 1 (by rfl) ⟨1274783, by rfl⟩ : syracuseStep 1699711 = 2549567) B2549567
theorem B2723815 : Blo 1699550 2723815 := bstep (se 1 (by rfl) ⟨2042861, by rfl⟩ : syracuseStep 2723815 = 4085723) B4085723
theorem B1699823 : Blo 1699550 1699823 := bstep (se 1 (by rfl) ⟨1274867, by rfl⟩ : syracuseStep 1699823 = 2549735) B2549735
theorem B1699835 : Blo 1699550 1699835 := bstep (se 1 (by rfl) ⟨1274876, by rfl⟩ : syracuseStep 1699835 = 2549753) B2549753
theorem B14520383 : Blo 1699550 14520383 := bstep (se 1 (by rfl) ⟨10890287, by rfl⟩ : syracuseStep 14520383 = 21780575) B21780575
theorem B1699903 : Blo 1699550 1699903 := bstep (se 1 (by rfl) ⟨1274927, by rfl⟩ : syracuseStep 1699903 = 2549855) B2549855
theorem B1912927 : Blo 1699550 1912927 := bstep (se 1 (by rfl) ⟨1434695, by rfl⟩ : syracuseStep 1912927 = 2869391) B2869391
theorem B1699943 : Blo 1699550 1699943 := bstep (se 1 (by rfl) ⟨1274957, by rfl⟩ : syracuseStep 1699943 = 2549915) B2549915
theorem B1699967 : Blo 1699550 1699967 := bstep (se 1 (by rfl) ⟨1274975, by rfl⟩ : syracuseStep 1699967 = 2549951) B2549951
theorem B1699995 : Blo 1699550 1699995 := bstep (se 1 (by rfl) ⟨1274996, by rfl⟩ : syracuseStep 1699995 = 2549993) B2549993
theorem B3633427 : Blo 1699550 3633427 := bstep (se 1 (by rfl) ⟨2725070, by rfl⟩ : syracuseStep 3633427 = 5450141) B5450141
theorem B29069603 : Blo 1699550 29069603 := bstep (se 1 (by rfl) ⟨21802202, by rfl⟩ : syracuseStep 29069603 = 43604405) B43604405
theorem B1700199 : Blo 1699550 1700199 := bstep (se 1 (by rfl) ⟨1275149, by rfl⟩ : syracuseStep 1700199 = 2550299) B2550299
theorem B1700251 : Blo 1699550 1700251 := bstep (se 1 (by rfl) ⟨1275188, by rfl⟩ : syracuseStep 1700251 = 2550377) B2550377
theorem B2552219 : Blo 1699550 2552219 := bstep (se 1 (by rfl) ⟨1914164, by rfl⟩ : syracuseStep 2552219 = 3828329) B3828329
theorem B14529131 : Blo 1699550 14529131 := bstep (se 1 (by rfl) ⟨10896848, by rfl⟩ : syracuseStep 14529131 = 21793697) B21793697
theorem B12915449 : Blo 1699550 12915449 := bstep (se 2 (by rfl) ⟨4843293, by rfl⟩ : syracuseStep 12915449 = 9686587) B9686587
theorem B1700603 : Blo 1699550 1700603 := bstep (se 1 (by rfl) ⟨1275452, by rfl⟩ : syracuseStep 1700603 = 2550905) B2550905
theorem B1700671 : Blo 1699550 1700671 := bstep (se 1 (by rfl) ⟨1275503, by rfl⟩ : syracuseStep 1700671 = 2551007) B2551007
theorem B1700699 : Blo 1699550 1700699 := bstep (se 1 (by rfl) ⟨1275524, by rfl⟩ : syracuseStep 1700699 = 2551049) B2551049
theorem B1700767 : Blo 1699550 1700767 := bstep (se 1 (by rfl) ⟨1275575, by rfl⟩ : syracuseStep 1700767 = 2551151) B2551151
theorem B24843181 : Blo 1699550 24843181 := bstep (se 3 (by rfl) ⟨4658096, by rfl⟩ : syracuseStep 24843181 = 9316193) B9316193
theorem B11793347 : Blo 1699550 11793347 := bstep (se 1 (by rfl) ⟨8845010, by rfl⟩ : syracuseStep 11793347 = 17690021) B17690021
theorem B9688045 : Blo 1699550 9688045 := bstep (se 3 (by rfl) ⟨1816508, by rfl⟩ : syracuseStep 9688045 = 3633017) B3633017
theorem B1815535 : Blo 1699550 1815535 := bstep (se 1 (by rfl) ⟨1361651, by rfl⟩ : syracuseStep 1815535 = 2723303) B2723303
theorem B1700847 : Blo 1699550 1700847 := bstep (se 1 (by rfl) ⟨1275635, by rfl⟩ : syracuseStep 1700847 = 2551271) B2551271
theorem B1700935 : Blo 1699550 1700935 := bstep (se 1 (by rfl) ⟨1275701, by rfl⟩ : syracuseStep 1700935 = 2551403) B2551403
theorem B6993001 : Blo 1699550 6993001 := bstep (se 2 (by rfl) ⟨2622375, by rfl⟩ : syracuseStep 6993001 = 5244751) B5244751
theorem B6894721 : Blo 1699550 6894721 := bstep (se 2 (by rfl) ⟨2585520, by rfl⟩ : syracuseStep 6894721 = 5171041) B5171041
theorem B1701019 : Blo 1699550 1701019 := bstep (se 1 (by rfl) ⟨1275764, by rfl⟩ : syracuseStep 1701019 = 2551529) B2551529
theorem B23270561 : Blo 1699550 23270561 := bstep (se 2 (by rfl) ⟨8726460, by rfl⟩ : syracuseStep 23270561 = 17452921) B17452921
theorem B2454779 : Blo 1699550 2454779 := bstep (se 1 (by rfl) ⟨1841084, by rfl⟩ : syracuseStep 2454779 = 3682169) B3682169
theorem B1701115 : Blo 1699550 1701115 := bstep (se 1 (by rfl) ⟨1275836, by rfl⟩ : syracuseStep 1701115 = 2551673) B2551673
theorem B26178835 : Blo 1699550 26178835 := bstep (se 1 (by rfl) ⟨19634126, by rfl⟩ : syracuseStep 26178835 = 39268253) B39268253
theorem B1701183 : Blo 1699550 1701183 := bstep (se 1 (by rfl) ⟨1275887, by rfl⟩ : syracuseStep 1701183 = 2551775) B2551775
theorem B1701351 : Blo 1699550 1701351 := bstep (se 1 (by rfl) ⟨1276013, by rfl⟩ : syracuseStep 1701351 = 2552027) B2552027
theorem B1701359 : Blo 1699550 1701359 := bstep (se 1 (by rfl) ⟨1276019, by rfl⟩ : syracuseStep 1701359 = 2552039) B2552039
theorem B33584711 : Blo 1699550 33584711 := bstep (se 1 (by rfl) ⟨25188533, by rfl⟩ : syracuseStep 33584711 = 50377067) B50377067
theorem B20682323 : Blo 1699550 20682323 := bstep (se 1 (by rfl) ⟨15511742, by rfl⟩ : syracuseStep 20682323 = 31023485) B31023485
theorem B1701467 : Blo 1699550 1701467 := bstep (se 1 (by rfl) ⟨1276100, by rfl⟩ : syracuseStep 1701467 = 2552201) B2552201
theorem B29439607 : Blo 1699550 29439607 := bstep (se 1 (by rfl) ⟨22079705, by rfl⟩ : syracuseStep 29439607 = 44159411) B44159411
theorem B1701531 : Blo 1699550 1701531 := bstep (se 1 (by rfl) ⟨1276148, by rfl⟩ : syracuseStep 1701531 = 2552297) B2552297
theorem B18388691 : Blo 1699550 18388691 := bstep (se 1 (by rfl) ⟨13791518, by rfl⟩ : syracuseStep 18388691 = 27583037) B27583037
theorem B4306679 : Blo 1699550 4306679 := bstep (se 1 (by rfl) ⟨3230009, by rfl⟩ : syracuseStep 4306679 = 6460019) B6460019
theorem B12261203 : Blo 1699550 12261203 := bstep (se 1 (by rfl) ⟨9195902, by rfl⟩ : syracuseStep 12261203 = 18391805) B18391805
theorem B8607707 : Blo 1699550 8607707 := bstep (se 1 (by rfl) ⟨6455780, by rfl⟩ : syracuseStep 8607707 = 12911561) B12911561
theorem B298031147 : Blo 1699550 298031147 := bstep (se 1 (by rfl) ⟨223523360, by rfl⟩ : syracuseStep 298031147 = 447046721) B447046721
theorem B8173811 : Blo 1699550 8173811 := bstep (se 1 (by rfl) ⟨6130358, by rfl⟩ : syracuseStep 8173811 = 12260717) B12260717
theorem B4839763 : Blo 1699550 4839763 := bstep (se 1 (by rfl) ⟨3629822, by rfl⟩ : syracuseStep 4839763 = 7259645) B7259645
theorem B8173981 : Blo 1699550 8173981 := bstep (se 3 (by rfl) ⟨1532621, by rfl⟩ : syracuseStep 8173981 = 3065243) B3065243
theorem B24508979 : Blo 1699550 24508979 := bstep (se 1 (by rfl) ⟨18381734, by rfl⟩ : syracuseStep 24508979 = 36763469) B36763469
theorem B3824441 : Blo 1699550 3824441 := bstep (se 2 (by rfl) ⟨1434165, by rfl⟩ : syracuseStep 3824441 = 2868331) B2868331
theorem B3824495 : Blo 1699550 3824495 := bstep (se 1 (by rfl) ⟨2868371, by rfl⟩ : syracuseStep 3824495 = 5736743) B5736743
theorem B5045149 : Blo 1699550 5045149 := bstep (se 3 (by rfl) ⟨945965, by rfl⟩ : syracuseStep 5045149 = 1891931) B1891931
theorem B4905947 : Blo 1699550 4905947 := bstep (se 1 (by rfl) ⟨3679460, by rfl⟩ : syracuseStep 4905947 = 7358921) B7358921
theorem B11951111 : Blo 1699550 11951111 := bstep (se 1 (by rfl) ⟨8963333, by rfl⟩ : syracuseStep 11951111 = 17926667) B17926667
theorem B3226729 : Blo 1699550 3226729 := bstep (se 2 (by rfl) ⟨1210023, by rfl⟩ : syracuseStep 3226729 = 2420047) B2420047
theorem B3825071 : Blo 1699550 3825071 := bstep (se 1 (by rfl) ⟨2868803, by rfl⟩ : syracuseStep 3825071 = 5737607) B5737607
theorem B3825143 : Blo 1699550 3825143 := bstep (se 1 (by rfl) ⟨2868857, by rfl⟩ : syracuseStep 3825143 = 5737715) B5737715
theorem B3227131 : Blo 1699550 3227131 := bstep (se 1 (by rfl) ⟨2420348, by rfl⟩ : syracuseStep 3227131 = 4840697) B4840697
theorem B14171755 : Blo 1699550 14171755 := bstep (se 1 (by rfl) ⟨10628816, by rfl⟩ : syracuseStep 14171755 = 21257633) B21257633
theorem B149085809 : Blo 1699550 149085809 := bstep (se 2 (by rfl) ⟨55907178, by rfl⟩ : syracuseStep 149085809 = 111814357) B111814357
theorem B3227359 : Blo 1699550 3227359 := bstep (se 1 (by rfl) ⟨2420519, by rfl⟩ : syracuseStep 3227359 = 4841039) B4841039
theorem B3448595 : Blo 1699550 3448595 := bstep (se 1 (by rfl) ⟨2586446, by rfl⟩ : syracuseStep 3448595 = 5172893) B5172893
theorem B41394017 : Blo 1699550 41394017 := bstep (se 2 (by rfl) ⟨15522756, by rfl⟩ : syracuseStep 41394017 = 31045513) B31045513
theorem B565985303 : Blo 1699550 565985303 := bstep (se 1 (by rfl) ⟨424488977, by rfl⟩ : syracuseStep 565985303 = 848977955) B848977955
theorem B8610299 : Blo 1699550 8610299 := bstep (se 1 (by rfl) ⟨6457724, by rfl⟩ : syracuseStep 8610299 = 12915449) B12915449
theorem B20677265 : Blo 1699550 20677265 := bstep (se 2 (by rfl) ⟨7753974, by rfl⟩ : syracuseStep 20677265 = 15507949) B15507949
theorem B6546077 : Blo 1699550 6546077 := bstep (se 3 (by rfl) ⟨1227389, by rfl⟩ : syracuseStep 6546077 = 2454779) B2454779
theorem B44172305 : Blo 1699550 44172305 := bstep (se 2 (by rfl) ⟨16564614, by rfl⟩ : syracuseStep 44172305 = 33129229) B33129229
theorem B13788215 : Blo 1699550 13788215 := bstep (se 1 (by rfl) ⟨10341161, by rfl⟩ : syracuseStep 13788215 = 20682323) B20682323
theorem B6726865 : Blo 1699550 6726865 := bstep (se 2 (by rfl) ⟨2522574, by rfl⟩ : syracuseStep 6726865 = 5045149) B5045149
theorem B4302305 : Blo 1699550 4302305 := bstep (se 2 (by rfl) ⟨1613364, by rfl⟩ : syracuseStep 4302305 = 3226729) B3226729
theorem B9324001 : Blo 1699550 9324001 := bstep (se 2 (by rfl) ⟨3496500, by rfl⟩ : syracuseStep 9324001 = 6993001) B6993001
theorem B5449207 : Blo 1699550 5449207 := bstep (se 1 (by rfl) ⟨4086905, by rfl⟩ : syracuseStep 5449207 = 8173811) B8173811
theorem B9192961 : Blo 1699550 9192961 := bstep (se 2 (by rfl) ⟨3447360, by rfl⟩ : syracuseStep 9192961 = 6894721) B6894721
theorem B21792361 : Blo 1699550 21792361 := bstep (se 2 (by rfl) ⟨8172135, by rfl⟩ : syracuseStep 21792361 = 16344271) B16344271
theorem B4843385 : Blo 1699550 4843385 := bstep (se 2 (by rfl) ⟨1816269, by rfl⟩ : syracuseStep 4843385 = 3632539) B3632539
theorem B2549627 : Blo 1699550 2549627 := bstep (se 1 (by rfl) ⟨1912220, by rfl⟩ : syracuseStep 2549627 = 3824441) B3824441
theorem B2549663 : Blo 1699550 2549663 := bstep (se 1 (by rfl) ⟨1912247, by rfl⟩ : syracuseStep 2549663 = 3824495) B3824495
theorem B18646955 : Blo 1699550 18646955 := bstep (se 1 (by rfl) ⟨13985216, by rfl⟩ : syracuseStep 18646955 = 27970433) B27970433
theorem B27592649 : Blo 1699550 27592649 := bstep (se 2 (by rfl) ⟨10347243, by rfl⟩ : syracuseStep 27592649 = 20694487) B20694487
theorem B22390757 : Blo 1699550 22390757 := bstep (se 4 (by rfl) ⟨2099133, by rfl⟩ : syracuseStep 22390757 = 4198267) B4198267
theorem B3270631 : Blo 1699550 3270631 := bstep (se 1 (by rfl) ⟨2452973, by rfl⟩ : syracuseStep 3270631 = 4905947) B4905947
theorem B4302841 : Blo 1699550 4302841 := bstep (se 2 (by rfl) ⟨1613565, by rfl⟩ : syracuseStep 4302841 = 3227131) B3227131
theorem B2549897 : Blo 1699550 2549897 := bstep (se 2 (by rfl) ⟨956211, by rfl⟩ : syracuseStep 2549897 = 1912423) B1912423
theorem B2550047 : Blo 1699550 2550047 := bstep (se 1 (by rfl) ⟨1912535, by rfl⟩ : syracuseStep 2550047 = 3825071) B3825071
theorem B4303145 : Blo 1699550 4303145 := bstep (se 2 (by rfl) ⟨1613679, by rfl⟩ : syracuseStep 4303145 = 3227359) B3227359
theorem B2550095 : Blo 1699550 2550095 := bstep (se 1 (by rfl) ⟨1912571, by rfl⟩ : syracuseStep 2550095 = 3825143) B3825143
theorem B2550185 : Blo 1699550 2550185 := bstep (se 2 (by rfl) ⟨956319, by rfl⟩ : syracuseStep 2550185 = 1912639) B1912639
theorem B3631753 : Blo 1699550 3631753 := bstep (se 2 (by rfl) ⟨1361907, by rfl⟩ : syracuseStep 3631753 = 2723815) B2723815
theorem B2550569 : Blo 1699550 2550569 := bstep (se 2 (by rfl) ⟨956463, by rfl⟩ : syracuseStep 2550569 = 1912927) B1912927
theorem B4844411 : Blo 1699550 4844411 := bstep (se 1 (by rfl) ⟨3633308, by rfl⟩ : syracuseStep 4844411 = 7266617) B7266617
theorem B2550779 : Blo 1699550 2550779 := bstep (se 1 (by rfl) ⟨1913084, by rfl⟩ : syracuseStep 2550779 = 3826169) B3826169
theorem B2550839 : Blo 1699550 2550839 := bstep (se 1 (by rfl) ⟨1913129, by rfl⟩ : syracuseStep 2550839 = 3826259) B3826259
theorem B9686087 : Blo 1699550 9686087 := bstep (se 1 (by rfl) ⟨7264565, by rfl⟩ : syracuseStep 9686087 = 14529131) B14529131
theorem B2550959 : Blo 1699550 2550959 := bstep (se 1 (by rfl) ⟨1913219, by rfl⟩ : syracuseStep 2550959 = 3826439) B3826439
theorem B10898641 : Blo 1699550 10898641 := bstep (se 2 (by rfl) ⟨4086990, by rfl⟩ : syracuseStep 10898641 = 8173981) B8173981
theorem B2551019 : Blo 1699550 2551019 := bstep (se 1 (by rfl) ⟨1913264, by rfl⟩ : syracuseStep 2551019 = 3826529) B3826529
theorem B1912351 : Blo 1699550 1912351 := bstep (se 1 (by rfl) ⟨1434263, by rfl⟩ : syracuseStep 1912351 = 2868527) B2868527
theorem B12259127 : Blo 1699550 12259127 := bstep (se 1 (by rfl) ⟨9194345, by rfl⟩ : syracuseStep 12259127 = 18388691) B18388691
theorem B2871119 : Blo 1699550 2871119 := bstep (se 1 (by rfl) ⟨2153339, by rfl⟩ : syracuseStep 2871119 = 4306679) B4306679
theorem B2551679 : Blo 1699550 2551679 := bstep (se 1 (by rfl) ⟨1913759, by rfl⟩ : syracuseStep 2551679 = 3827519) B3827519
theorem B33124241 : Blo 1699550 33124241 := bstep (se 2 (by rfl) ⟨12421590, by rfl⟩ : syracuseStep 33124241 = 24843181) B24843181
theorem B5738471 : Blo 1699550 5738471 := bstep (se 1 (by rfl) ⟨4303853, by rfl⟩ : syracuseStep 5738471 = 8607707) B8607707
theorem B2420713 : Blo 1699550 2420713 := bstep (se 2 (by rfl) ⟨907767, by rfl⟩ : syracuseStep 2420713 = 1815535) B1815535
theorem B1699871 : Blo 1699550 1699871 := bstep (se 1 (by rfl) ⟨1274903, by rfl⟩ : syracuseStep 1699871 = 2549807) B2549807
theorem B19378277 : Blo 1699550 19378277 := bstep (se 4 (by rfl) ⟨1816713, by rfl⟩ : syracuseStep 19378277 = 3633427) B3633427
theorem B89559229 : Blo 1699550 89559229 := bstep (se 3 (by rfl) ⟨16792355, by rfl⟩ : syracuseStep 89559229 = 33584711) B33584711
theorem B1700047 : Blo 1699550 1700047 := bstep (se 1 (by rfl) ⟨1275035, by rfl⟩ : syracuseStep 1700047 = 2550071) B2550071
theorem B2552015 : Blo 1699550 2552015 := bstep (se 1 (by rfl) ⟨1914011, by rfl⟩ : syracuseStep 2552015 = 3828023) B3828023
theorem B1700167 : Blo 1699550 1700167 := bstep (se 1 (by rfl) ⟨1275125, by rfl⟩ : syracuseStep 1700167 = 2550251) B2550251
theorem B2552135 : Blo 1699550 2552135 := bstep (se 1 (by rfl) ⟨1914101, by rfl⟩ : syracuseStep 2552135 = 3828203) B3828203
theorem B5738849 : Blo 1699550 5738849 := bstep (se 2 (by rfl) ⟨2152068, by rfl⟩ : syracuseStep 5738849 = 4304137) B4304137
theorem B16339319 : Blo 1699550 16339319 := bstep (se 1 (by rfl) ⟨12254489, by rfl⟩ : syracuseStep 16339319 = 24508979) B24508979
theorem B7967407 : Blo 1699550 7967407 := bstep (se 1 (by rfl) ⟨5975555, by rfl⟩ : syracuseStep 7967407 = 11951111) B11951111
theorem B10891979 : Blo 1699550 10891979 := bstep (se 1 (by rfl) ⟨8168984, by rfl⟩ : syracuseStep 10891979 = 16337969) B16337969
theorem B9196253 : Blo 1699550 9196253 := bstep (se 3 (by rfl) ⟨1724297, by rfl⟩ : syracuseStep 9196253 = 3448595) B3448595
theorem B1700635 : Blo 1699550 1700635 := bstep (se 1 (by rfl) ⟨1275476, by rfl⟩ : syracuseStep 1700635 = 2550953) B2550953
theorem B18895673 : Blo 1699550 18895673 := bstep (se 2 (by rfl) ⟨7085877, by rfl⟩ : syracuseStep 18895673 = 14171755) B14171755
theorem B39252809 : Blo 1699550 39252809 := bstep (se 2 (by rfl) ⟨14719803, by rfl⟩ : syracuseStep 39252809 = 29439607) B29439607
theorem B11637665 : Blo 1699550 11637665 := bstep (se 2 (by rfl) ⟨4364124, by rfl⟩ : syracuseStep 11637665 = 8728249) B8728249
theorem B4305899 : Blo 1699550 4305899 := bstep (se 1 (by rfl) ⟨3229424, by rfl⟩ : syracuseStep 4305899 = 6458849) B6458849
theorem B1700911 : Blo 1699550 1700911 := bstep (se 1 (by rfl) ⟨1275683, by rfl⟩ : syracuseStep 1700911 = 2551367) B2551367
theorem B99390539 : Blo 1699550 99390539 := bstep (se 1 (by rfl) ⟨74542904, by rfl⟩ : syracuseStep 99390539 = 149085809) B149085809
theorem B4306081 : Blo 1699550 4306081 := bstep (se 2 (by rfl) ⟨1614780, by rfl⟩ : syracuseStep 4306081 = 3229561) B3229561
theorem B1701031 : Blo 1699550 1701031 := bstep (se 1 (by rfl) ⟨1275773, by rfl⟩ : syracuseStep 1701031 = 2551547) B2551547
theorem B27596011 : Blo 1699550 27596011 := bstep (se 1 (by rfl) ⟨20697008, by rfl⟩ : syracuseStep 27596011 = 41394017) B41394017
theorem B9680255 : Blo 1699550 9680255 := bstep (se 1 (by rfl) ⟨7260191, by rfl⟩ : syracuseStep 9680255 = 14520383) B14520383
theorem B9688571 : Blo 1699550 9688571 := bstep (se 1 (by rfl) ⟨7266428, by rfl⟩ : syracuseStep 9688571 = 14532857) B14532857
theorem B19379735 : Blo 1699550 19379735 := bstep (se 1 (by rfl) ⟨14534801, by rfl⟩ : syracuseStep 19379735 = 29069603) B29069603
theorem B24516179 : Blo 1699550 24516179 := bstep (se 1 (by rfl) ⟨18387134, by rfl⟩ : syracuseStep 24516179 = 36774269) B36774269
theorem B1701479 : Blo 1699550 1701479 := bstep (se 1 (by rfl) ⟨1276109, by rfl⟩ : syracuseStep 1701479 = 2552219) B2552219
theorem B6453017 : Blo 1699550 6453017 := bstep (se 2 (by rfl) ⟨2419881, by rfl⟩ : syracuseStep 6453017 = 4839763) B4839763
theorem B9689003 : Blo 1699550 9689003 := bstep (se 1 (by rfl) ⟨7266752, by rfl⟩ : syracuseStep 9689003 = 14533505) B14533505
theorem B7862231 : Blo 1699550 7862231 := bstep (se 1 (by rfl) ⟨5896673, by rfl⟩ : syracuseStep 7862231 = 11793347) B11793347
theorem B15513707 : Blo 1699550 15513707 := bstep (se 1 (by rfl) ⟨11635280, by rfl⟩ : syracuseStep 15513707 = 23270561) B23270561
theorem B8607869 : Blo 1699550 8607869 := bstep (se 3 (by rfl) ⟨1613975, by rfl⟩ : syracuseStep 8607869 = 3227951) B3227951
theorem B9689321 : Blo 1699550 9689321 := bstep (se 2 (by rfl) ⟨3633495, by rfl⟩ : syracuseStep 9689321 = 7266991) B7266991
theorem B8608031 : Blo 1699550 8608031 := bstep (se 1 (by rfl) ⟨6456023, by rfl⟩ : syracuseStep 8608031 = 12912047) B12912047
theorem B3824027 : Blo 1699550 3824027 := bstep (se 1 (by rfl) ⟨2868020, by rfl⟩ : syracuseStep 3824027 = 5736041) B5736041
theorem B9689503 : Blo 1699550 9689503 := bstep (se 1 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 9689503 = 14534255) B14534255
theorem B3824135 : Blo 1699550 3824135 := bstep (se 1 (by rfl) ⟨2868101, by rfl⟩ : syracuseStep 3824135 = 5736203) B5736203
theorem B8174135 : Blo 1699550 8174135 := bstep (se 1 (by rfl) ⟨6130601, by rfl⟩ : syracuseStep 8174135 = 12261203) B12261203
theorem B10345103 : Blo 1699550 10345103 := bstep (se 1 (by rfl) ⟨7758827, by rfl⟩ : syracuseStep 10345103 = 15517655) B15517655
theorem B12917393 : Blo 1699550 12917393 := bstep (se 2 (by rfl) ⟨4844022, by rfl⟩ : syracuseStep 12917393 = 9688045) B9688045
theorem B3824315 : Blo 1699550 3824315 := bstep (se 1 (by rfl) ⟨2868236, by rfl⟩ : syracuseStep 3824315 = 5736473) B5736473
theorem B198687431 : Blo 1699550 198687431 := bstep (se 1 (by rfl) ⟨149015573, by rfl⟩ : syracuseStep 198687431 = 298031147) B298031147
theorem B3824423 : Blo 1699550 3824423 := bstep (se 1 (by rfl) ⟨2868317, by rfl⟩ : syracuseStep 3824423 = 5736635) B5736635
theorem B34905113 : Blo 1699550 34905113 := bstep (se 2 (by rfl) ⟨13089417, by rfl⟩ : syracuseStep 34905113 = 26178835) B26178835
theorem B7265659 : Blo 1699550 7265659 := bstep (se 1 (by rfl) ⟨5449244, by rfl⟩ : syracuseStep 7265659 = 10898489) B10898489
theorem B3825215 : Blo 1699550 3825215 := bstep (se 1 (by rfl) ⟨2868911, by rfl⟩ : syracuseStep 3825215 = 5737823) B5737823
theorem B3825575 : Blo 1699550 3825575 := bstep (se 1 (by rfl) ⟨2869181, by rfl⟩ : syracuseStep 3825575 = 5738363) B5738363
theorem B377323535 : Blo 1699550 377323535 := bstep (se 1 (by rfl) ⟨282992651, by rfl⟩ : syracuseStep 377323535 = 565985303) B565985303
theorem B12918851 : Blo 1699550 12918851 := bstep (se 1 (by rfl) ⟨9689138, by rfl⟩ : syracuseStep 12918851 = 19378277) B19378277
theorem B3825899 : Blo 1699550 3825899 := bstep (se 1 (by rfl) ⟨2869424, by rfl⟩ : syracuseStep 3825899 = 5738849) B5738849
theorem B41369885 : Blo 1699550 41369885 := bstep (se 3 (by rfl) ⟨7756853, by rfl⟩ : syracuseStep 41369885 = 15513707) B15513707
theorem B12919337 : Blo 1699550 12919337 := bstep (se 2 (by rfl) ⟨4844751, by rfl⟩ : syracuseStep 12919337 = 9689503) B9689503
theorem B7758443 : Blo 1699550 7758443 := bstep (se 1 (by rfl) ⟨5818832, by rfl⟩ : syracuseStep 7758443 = 11637665) B11637665
theorem B9192143 : Blo 1699550 9192143 := bstep (se 1 (by rfl) ⟨6894107, by rfl⟩ : syracuseStep 9192143 = 13788215) B13788215
theorem B4842337 : Blo 1699550 4842337 := bstep (se 2 (by rfl) ⟨1815876, by rfl⟩ : syracuseStep 4842337 = 3631753) B3631753
theorem B2868203 : Blo 1699550 2868203 := bstep (se 1 (by rfl) ⟨2151152, by rfl⟩ : syracuseStep 2868203 = 4302305) B4302305
theorem B12919823 : Blo 1699550 12919823 := bstep (se 1 (by rfl) ⟨9689867, by rfl⟩ : syracuseStep 12919823 = 19379735) B19379735
theorem B16344119 : Blo 1699550 16344119 := bstep (se 1 (by rfl) ⟨12258089, by rfl⟩ : syracuseStep 16344119 = 24516179) B24516179
theorem B4302011 : Blo 1699550 4302011 := bstep (se 1 (by rfl) ⟨3226508, by rfl⟩ : syracuseStep 4302011 = 6453017) B6453017
theorem B3228923 : Blo 1699550 3228923 := bstep (se 1 (by rfl) ⟨2421692, by rfl⟩ : syracuseStep 3228923 = 4843385) B4843385
theorem B14927171 : Blo 1699550 14927171 := bstep (se 1 (by rfl) ⟨11195378, by rfl⟩ : syracuseStep 14927171 = 22390757) B22390757
theorem B2868763 : Blo 1699550 2868763 := bstep (se 1 (by rfl) ⟨2151572, by rfl⟩ : syracuseStep 2868763 = 4303145) B4303145
theorem B2549351 : Blo 1699550 2549351 := bstep (se 1 (by rfl) ⟨1912013, by rfl⟩ : syracuseStep 2549351 = 3824027) B3824027
theorem B2549423 : Blo 1699550 2549423 := bstep (se 1 (by rfl) ⟨1912067, by rfl⟩ : syracuseStep 2549423 = 3824135) B3824135
theorem B8611595 : Blo 1699550 8611595 := bstep (se 1 (by rfl) ⟨6458696, by rfl⟩ : syracuseStep 8611595 = 12917393) B12917393
theorem B2549543 : Blo 1699550 2549543 := bstep (se 1 (by rfl) ⟨1912157, by rfl⟩ : syracuseStep 2549543 = 3824315) B3824315
theorem B132458287 : Blo 1699550 132458287 := bstep (se 1 (by rfl) ⟨99343715, by rfl⟩ : syracuseStep 132458287 = 198687431) B198687431
theorem B2549615 : Blo 1699550 2549615 := bstep (se 1 (by rfl) ⟨1912211, by rfl⟩ : syracuseStep 2549615 = 3824423) B3824423
theorem B3229607 : Blo 1699550 3229607 := bstep (se 1 (by rfl) ⟨2422205, by rfl⟩ : syracuseStep 3229607 = 4844411) B4844411
theorem B12257281 : Blo 1699550 12257281 := bstep (se 2 (by rfl) ⟨4596480, by rfl⟩ : syracuseStep 12257281 = 9192961) B9192961
theorem B2549801 : Blo 1699550 2549801 := bstep (se 2 (by rfl) ⟨956175, by rfl⟩ : syracuseStep 2549801 = 1912351) B1912351
theorem B6457391 : Blo 1699550 6457391 := bstep (se 1 (by rfl) ⟨4843043, by rfl⟩ : syracuseStep 6457391 = 9686087) B9686087
theorem B2550143 : Blo 1699550 2550143 := bstep (se 1 (by rfl) ⟨1912607, by rfl⟩ : syracuseStep 2550143 = 3825215) B3825215
theorem B20965949 : Blo 1699550 20965949 := bstep (se 3 (by rfl) ⟨3931115, by rfl⟩ : syracuseStep 20965949 = 7862231) B7862231
theorem B2550383 : Blo 1699550 2550383 := bstep (se 1 (by rfl) ⟨1912787, by rfl⟩ : syracuseStep 2550383 = 3825575) B3825575
theorem B4360841 : Blo 1699550 4360841 := bstep (se 2 (by rfl) ⟨1635315, by rfl⟩ : syracuseStep 4360841 = 3270631) B3270631
theorem B5737121 : Blo 1699550 5737121 := bstep (se 2 (by rfl) ⟨2151420, by rfl⟩ : syracuseStep 5737121 = 4302841) B4302841
theorem B7261319 : Blo 1699550 7261319 := bstep (se 1 (by rfl) ⟨5445989, by rfl⟩ : syracuseStep 7261319 = 10891979) B10891979
theorem B6130835 : Blo 1699550 6130835 := bstep (se 1 (by rfl) ⟨4598126, by rfl⟩ : syracuseStep 6130835 = 9196253) B9196253
theorem B2870599 : Blo 1699550 2870599 := bstep (se 1 (by rfl) ⟨2152949, by rfl⟩ : syracuseStep 2870599 = 4305899) B4305899
theorem B66260359 : Blo 1699550 66260359 := bstep (se 1 (by rfl) ⟨49695269, by rfl⟩ : syracuseStep 66260359 = 99390539) B99390539
theorem B6459047 : Blo 1699550 6459047 := bstep (se 1 (by rfl) ⟨4844285, by rfl⟩ : syracuseStep 6459047 = 9688571) B9688571
theorem B1699751 : Blo 1699550 1699751 := bstep (se 1 (by rfl) ⟨1274813, by rfl⟩ : syracuseStep 1699751 = 2549627) B2549627
theorem B1699775 : Blo 1699550 1699775 := bstep (se 1 (by rfl) ⟨1274831, by rfl⟩ : syracuseStep 1699775 = 2549663) B2549663
theorem B6459335 : Blo 1699550 6459335 := bstep (se 1 (by rfl) ⟨4844501, by rfl⟩ : syracuseStep 6459335 = 9689003) B9689003
theorem B12431303 : Blo 1699550 12431303 := bstep (se 1 (by rfl) ⟨9323477, by rfl⟩ : syracuseStep 12431303 = 18646955) B18646955
theorem B18395099 : Blo 1699550 18395099 := bstep (se 1 (by rfl) ⟨13796324, by rfl⟩ : syracuseStep 18395099 = 27592649) B27592649
theorem B5738579 : Blo 1699550 5738579 := bstep (se 1 (by rfl) ⟨4303934, by rfl⟩ : syracuseStep 5738579 = 8607869) B8607869
theorem B1699931 : Blo 1699550 1699931 := bstep (se 1 (by rfl) ⟨1274948, by rfl⟩ : syracuseStep 1699931 = 2549897) B2549897
theorem B6459547 : Blo 1699550 6459547 := bstep (se 1 (by rfl) ⟨4844660, by rfl⟩ : syracuseStep 6459547 = 9689321) B9689321
theorem B1700031 : Blo 1699550 1700031 := bstep (se 1 (by rfl) ⟨1275023, by rfl⟩ : syracuseStep 1700031 = 2550047) B2550047
theorem B5738687 : Blo 1699550 5738687 := bstep (se 1 (by rfl) ⟨4304015, by rfl⟩ : syracuseStep 5738687 = 8608031) B8608031
theorem B1700063 : Blo 1699550 1700063 := bstep (se 1 (by rfl) ⟨1275047, by rfl⟩ : syracuseStep 1700063 = 2550095) B2550095
theorem B1700123 : Blo 1699550 1700123 := bstep (se 1 (by rfl) ⟨1275092, by rfl⟩ : syracuseStep 1700123 = 2550185) B2550185
theorem B36794681 : Blo 1699550 36794681 := bstep (se 2 (by rfl) ⟨13798005, by rfl⟩ : syracuseStep 36794681 = 27596011) B27596011
theorem B9687545 : Blo 1699550 9687545 := bstep (se 2 (by rfl) ⟨3632829, by rfl⟩ : syracuseStep 9687545 = 7265659) B7265659
theorem B1700379 : Blo 1699550 1700379 := bstep (se 1 (by rfl) ⟨1275284, by rfl⟩ : syracuseStep 1700379 = 2550569) B2550569
theorem B12432001 : Blo 1699550 12432001 := bstep (se 2 (by rfl) ⟨4662000, by rfl⟩ : syracuseStep 12432001 = 9324001) B9324001
theorem B1700519 : Blo 1699550 1700519 := bstep (se 1 (by rfl) ⟨1275389, by rfl⟩ : syracuseStep 1700519 = 2550779) B2550779
theorem B23270075 : Blo 1699550 23270075 := bstep (se 1 (by rfl) ⟨17452556, by rfl⟩ : syracuseStep 23270075 = 34905113) B34905113
theorem B1700559 : Blo 1699550 1700559 := bstep (se 1 (by rfl) ⟨1275419, by rfl⟩ : syracuseStep 1700559 = 2550839) B2550839
theorem B1700639 : Blo 1699550 1700639 := bstep (se 1 (by rfl) ⟨1275479, by rfl⟩ : syracuseStep 1700639 = 2550959) B2550959
theorem B1700679 : Blo 1699550 1700679 := bstep (se 1 (by rfl) ⟨1275509, by rfl⟩ : syracuseStep 1700679 = 2551019) B2551019
theorem B104674157 : Blo 1699550 104674157 := bstep (se 3 (by rfl) ⟨19626404, by rfl⟩ : syracuseStep 104674157 = 39252809) B39252809
theorem B88331309 : Blo 1699550 88331309 := bstep (se 3 (by rfl) ⟨16562120, by rfl⟩ : syracuseStep 88331309 = 33124241) B33124241
theorem B8172751 : Blo 1699550 8172751 := bstep (se 1 (by rfl) ⟨6129563, by rfl⟩ : syracuseStep 8172751 = 12259127) B12259127
theorem B1914079 : Blo 1699550 1914079 := bstep (se 1 (by rfl) ⟨1435559, by rfl⟩ : syracuseStep 1914079 = 2871119) B2871119
theorem B1701119 : Blo 1699550 1701119 := bstep (se 1 (by rfl) ⟨1275839, by rfl⟩ : syracuseStep 1701119 = 2551679) B2551679
theorem B1701343 : Blo 1699550 1701343 := bstep (se 1 (by rfl) ⟨1276007, by rfl⟩ : syracuseStep 1701343 = 2552015) B2552015
theorem B1701423 : Blo 1699550 1701423 := bstep (se 1 (by rfl) ⟨1276067, by rfl⟩ : syracuseStep 1701423 = 2552135) B2552135
theorem B10892879 : Blo 1699550 10892879 := bstep (se 1 (by rfl) ⟨8169659, by rfl⟩ : syracuseStep 10892879 = 16339319) B16339319
theorem B119412305 : Blo 1699550 119412305 := bstep (se 2 (by rfl) ⟨44779614, by rfl⟩ : syracuseStep 119412305 = 89559229) B89559229
theorem B5740199 : Blo 1699550 5740199 := bstep (se 1 (by rfl) ⟨4305149, by rfl⟩ : syracuseStep 5740199 = 8610299) B8610299
theorem B13784843 : Blo 1699550 13784843 := bstep (se 1 (by rfl) ⟨10338632, by rfl⟩ : syracuseStep 13784843 = 20677265) B20677265
theorem B4364051 : Blo 1699550 4364051 := bstep (se 1 (by rfl) ⟨3273038, by rfl⟩ : syracuseStep 4364051 = 6546077) B6546077
theorem B12597115 : Blo 1699550 12597115 := bstep (se 1 (by rfl) ⟨9447836, by rfl⟩ : syracuseStep 12597115 = 18895673) B18895673
theorem B29448203 : Blo 1699550 29448203 := bstep (se 1 (by rfl) ⟨22086152, by rfl⟩ : syracuseStep 29448203 = 44172305) B44172305
theorem B10623209 : Blo 1699550 10623209 := bstep (se 2 (by rfl) ⟨3983703, by rfl⟩ : syracuseStep 10623209 = 7967407) B7967407
theorem B6453503 : Blo 1699550 6453503 := bstep (se 1 (by rfl) ⟨4840127, by rfl⟩ : syracuseStep 6453503 = 9680255) B9680255
theorem B21797693 : Blo 1699550 21797693 := bstep (se 3 (by rfl) ⟨4087067, by rfl⟩ : syracuseStep 21797693 = 8174135) B8174135
theorem B5741441 : Blo 1699550 5741441 := bstep (se 2 (by rfl) ⟨2153040, by rfl⟩ : syracuseStep 5741441 = 4306081) B4306081
theorem B14531521 : Blo 1699550 14531521 := bstep (se 2 (by rfl) ⟨5449320, by rfl⟩ : syracuseStep 14531521 = 10898641) B10898641
theorem B8969153 : Blo 1699550 8969153 := bstep (se 2 (by rfl) ⟨3363432, by rfl⟩ : syracuseStep 8969153 = 6726865) B6726865
theorem B6896735 : Blo 1699550 6896735 := bstep (se 1 (by rfl) ⟨5172551, by rfl⟩ : syracuseStep 6896735 = 10345103) B10345103
theorem B7265609 : Blo 1699550 7265609 := bstep (se 2 (by rfl) ⟨2724603, by rfl⟩ : syracuseStep 7265609 = 5449207) B5449207
theorem B29056481 : Blo 1699550 29056481 := bstep (se 2 (by rfl) ⟨10896180, by rfl⟩ : syracuseStep 29056481 = 21792361) B21792361
theorem B3227617 : Blo 1699550 3227617 := bstep (se 2 (by rfl) ⟨1210356, by rfl⟩ : syracuseStep 3227617 = 2420713) B2420713
theorem B3825647 : Blo 1699550 3825647 := bstep (se 1 (by rfl) ⟨2869235, by rfl⟩ : syracuseStep 3825647 = 5738471) B5738471
theorem B16343041 : Blo 1699550 16343041 := bstep (se 2 (by rfl) ⟨6128640, by rfl⟩ : syracuseStep 16343041 = 12257281) B12257281
theorem B78528541 : Blo 1699550 78528541 := bstep (se 3 (by rfl) ⟨14724101, by rfl⟩ : syracuseStep 78528541 = 29448203) B29448203
theorem B3825719 : Blo 1699550 3825719 := bstep (se 1 (by rfl) ⟨2869289, by rfl⟩ : syracuseStep 3825719 = 5738579) B5738579
theorem B3825791 : Blo 1699550 3825791 := bstep (se 1 (by rfl) ⟨2869343, by rfl⟩ : syracuseStep 3825791 = 5738687) B5738687
theorem B6128095 : Blo 1699550 6128095 := bstep (se 1 (by rfl) ⟨4596071, by rfl⟩ : syracuseStep 6128095 = 9192143) B9192143
theorem B28328557 : Blo 1699550 28328557 := bstep (se 3 (by rfl) ⟨5311604, by rfl⟩ : syracuseStep 28328557 = 10623209) B10623209
theorem B8610461 : Blo 1699550 8610461 := bstep (se 3 (by rfl) ⟨1614461, by rfl⟩ : syracuseStep 8610461 = 3228923) B3228923
theorem B10896079 : Blo 1699550 10896079 := bstep (se 1 (by rfl) ⟨8172059, by rfl⟩ : syracuseStep 10896079 = 16344119) B16344119
theorem B2868007 : Blo 1699550 2868007 := bstep (se 1 (by rfl) ⟨2151005, by rfl⟩ : syracuseStep 2868007 = 4302011) B4302011
theorem B39805789 : Blo 1699550 39805789 := bstep (se 3 (by rfl) ⟨7463585, by rfl⟩ : syracuseStep 39805789 = 14927171) B14927171
theorem B3826799 : Blo 1699550 3826799 := bstep (se 1 (by rfl) ⟨2870099, by rfl⟩ : syracuseStep 3826799 = 5740199) B5740199
theorem B6456449 : Blo 1699550 6456449 := bstep (se 2 (by rfl) ⟨2421168, by rfl⟩ : syracuseStep 6456449 = 4842337) B4842337
theorem B19375361 : Blo 1699550 19375361 := bstep (se 2 (by rfl) ⟨7265760, by rfl⟩ : syracuseStep 19375361 = 14531521) B14531521
theorem B4302335 : Blo 1699550 4302335 := bstep (se 1 (by rfl) ⟨3226751, by rfl⟩ : syracuseStep 4302335 = 6453503) B6453503
theorem B10897001 : Blo 1699550 10897001 := bstep (se 2 (by rfl) ⟨4086375, by rfl⟩ : syracuseStep 10897001 = 8172751) B8172751
theorem B13977299 : Blo 1699550 13977299 := bstep (se 1 (by rfl) ⟨10482974, by rfl⟩ : syracuseStep 13977299 = 20965949) B20965949
theorem B3827465 : Blo 1699550 3827465 := bstep (se 2 (by rfl) ⟨1435299, by rfl⟩ : syracuseStep 3827465 = 2870599) B2870599
theorem B3827627 : Blo 1699550 3827627 := bstep (se 1 (by rfl) ⟨2870720, by rfl⟩ : syracuseStep 3827627 = 5741441) B5741441
theorem B4597823 : Blo 1699550 4597823 := bstep (se 1 (by rfl) ⟨3448367, by rfl⟩ : syracuseStep 4597823 = 6896735) B6896735
theorem B4843739 : Blo 1699550 4843739 := bstep (se 1 (by rfl) ⟨3632804, by rfl⟩ : syracuseStep 4843739 = 7265609) B7265609
theorem B16796153 : Blo 1699550 16796153 := bstep (se 2 (by rfl) ⟨6298557, by rfl⟩ : syracuseStep 16796153 = 12597115) B12597115
theorem B4303489 : Blo 1699550 4303489 := bstep (se 2 (by rfl) ⟨1613808, by rfl⟩ : syracuseStep 4303489 = 3227617) B3227617
theorem B2550431 : Blo 1699550 2550431 := bstep (se 1 (by rfl) ⟨1912823, by rfl⟩ : syracuseStep 2550431 = 3825647) B3825647
theorem B8612567 : Blo 1699550 8612567 := bstep (se 1 (by rfl) ⟨6459425, by rfl⟩ : syracuseStep 8612567 = 12918851) B12918851
theorem B2550599 : Blo 1699550 2550599 := bstep (se 1 (by rfl) ⟨1912949, by rfl⟩ : syracuseStep 2550599 = 3825899) B3825899
theorem B8612729 : Blo 1699550 8612729 := bstep (se 2 (by rfl) ⟨3229773, by rfl⟩ : syracuseStep 8612729 = 6459547) B6459547
theorem B24529787 : Blo 1699550 24529787 := bstep (se 1 (by rfl) ⟨18397340, by rfl⟩ : syracuseStep 24529787 = 36794681) B36794681
theorem B6458363 : Blo 1699550 6458363 := bstep (se 1 (by rfl) ⟨4843772, by rfl⟩ : syracuseStep 6458363 = 9687545) B9687545
theorem B8612891 : Blo 1699550 8612891 := bstep (se 1 (by rfl) ⟨6459668, by rfl⟩ : syracuseStep 8612891 = 12919337) B12919337
theorem B69782771 : Blo 1699550 69782771 := bstep (se 1 (by rfl) ⟨52337078, by rfl⟩ : syracuseStep 69782771 = 104674157) B104674157
theorem B1912135 : Blo 1699550 1912135 := bstep (se 1 (by rfl) ⟨1434101, by rfl⟩ : syracuseStep 1912135 = 2868203) B2868203
theorem B8613215 : Blo 1699550 8613215 := bstep (se 1 (by rfl) ⟨6459911, by rfl⟩ : syracuseStep 8613215 = 12919823) B12919823
theorem B58887539 : Blo 1699550 58887539 := bstep (se 1 (by rfl) ⟨44165654, by rfl⟩ : syracuseStep 58887539 = 88331309) B88331309
theorem B16576001 : Blo 1699550 16576001 := bstep (se 2 (by rfl) ⟨6216000, by rfl⟩ : syracuseStep 16576001 = 12432001) B12432001
theorem B7261919 : Blo 1699550 7261919 := bstep (se 1 (by rfl) ⟨5446439, by rfl⟩ : syracuseStep 7261919 = 10892879) B10892879
theorem B1699567 : Blo 1699550 1699567 := bstep (se 1 (by rfl) ⟨1274675, by rfl⟩ : syracuseStep 1699567 = 2549351) B2549351
theorem B1699615 : Blo 1699550 1699615 := bstep (se 1 (by rfl) ⟨1274711, by rfl⟩ : syracuseStep 1699615 = 2549423) B2549423
theorem B1699695 : Blo 1699550 1699695 := bstep (se 1 (by rfl) ⟨1274771, by rfl⟩ : syracuseStep 1699695 = 2549543) B2549543
theorem B1699743 : Blo 1699550 1699743 := bstep (se 1 (by rfl) ⟨1274807, by rfl⟩ : syracuseStep 1699743 = 2549615) B2549615
theorem B1699867 : Blo 1699550 1699867 := bstep (se 1 (by rfl) ⟨1274900, by rfl⟩ : syracuseStep 1699867 = 2549801) B2549801
theorem B4304927 : Blo 1699550 4304927 := bstep (se 1 (by rfl) ⟨3228695, by rfl⟩ : syracuseStep 4304927 = 6457391) B6457391
theorem B1700095 : Blo 1699550 1700095 := bstep (se 1 (by rfl) ⟨1275071, by rfl⟩ : syracuseStep 1700095 = 2550143) B2550143
theorem B20689181 : Blo 1699550 20689181 := bstep (se 3 (by rfl) ⟨3879221, by rfl⟩ : syracuseStep 20689181 = 7758443) B7758443
theorem B2552105 : Blo 1699550 2552105 := bstep (se 2 (by rfl) ⟨957039, by rfl⟩ : syracuseStep 2552105 = 1914079) B1914079
theorem B1700255 : Blo 1699550 1700255 := bstep (se 1 (by rfl) ⟨1275191, by rfl⟩ : syracuseStep 1700255 = 2550383) B2550383
theorem B88347145 : Blo 1699550 88347145 := bstep (se 2 (by rfl) ⟨33130179, by rfl⟩ : syracuseStep 88347145 = 66260359) B66260359
theorem B95670965 : Blo 1699550 95670965 := bstep (se 5 (by rfl) ⟨4484576, by rfl⟩ : syracuseStep 95670965 = 8969153) B8969153
theorem B11637469 : Blo 1699550 11637469 := bstep (se 3 (by rfl) ⟨2182025, by rfl⟩ : syracuseStep 11637469 = 4364051) B4364051
theorem B19370987 : Blo 1699550 19370987 := bstep (se 1 (by rfl) ⟨14528240, by rfl⟩ : syracuseStep 19370987 = 29056481) B29056481
theorem B4306031 : Blo 1699550 4306031 := bstep (se 1 (by rfl) ⟨3229523, by rfl⟩ : syracuseStep 4306031 = 6459047) B6459047
theorem B4306223 : Blo 1699550 4306223 := bstep (se 1 (by rfl) ⟨3229667, by rfl⟩ : syracuseStep 4306223 = 6459335) B6459335
theorem B8287535 : Blo 1699550 8287535 := bstep (se 1 (by rfl) ⟨6215651, by rfl⟩ : syracuseStep 8287535 = 12431303) B12431303
theorem B251549023 : Blo 1699550 251549023 := bstep (se 1 (by rfl) ⟨188661767, by rfl⟩ : syracuseStep 251549023 = 377323535) B377323535
theorem B27579923 : Blo 1699550 27579923 := bstep (se 1 (by rfl) ⟨20684942, by rfl⟩ : syracuseStep 27579923 = 41369885) B41369885
theorem B15513383 : Blo 1699550 15513383 := bstep (se 1 (by rfl) ⟨11635037, by rfl⟩ : syracuseStep 15513383 = 23270075) B23270075
theorem B79608203 : Blo 1699550 79608203 := bstep (se 1 (by rfl) ⟨59706152, by rfl⟩ : syracuseStep 79608203 = 119412305) B119412305
theorem B9189895 : Blo 1699550 9189895 := bstep (se 1 (by rfl) ⟨6892421, by rfl⟩ : syracuseStep 9189895 = 13784843) B13784843
theorem B5741063 : Blo 1699550 5741063 := bstep (se 1 (by rfl) ⟨4305797, by rfl⟩ : syracuseStep 5741063 = 8611595) B8611595
theorem B2153071 : Blo 1699550 2153071 := bstep (se 1 (by rfl) ⟨1614803, by rfl⟩ : syracuseStep 2153071 = 3229607) B3229607
theorem B2907227 : Blo 1699550 2907227 := bstep (se 1 (by rfl) ⟨2180420, by rfl⟩ : syracuseStep 2907227 = 4360841) B4360841
theorem B3824747 : Blo 1699550 3824747 := bstep (se 1 (by rfl) ⟨2868560, by rfl⟩ : syracuseStep 3824747 = 5737121) B5737121
theorem B14531795 : Blo 1699550 14531795 := bstep (se 1 (by rfl) ⟨10898846, by rfl⟩ : syracuseStep 14531795 = 21797693) B21797693
theorem B3825017 : Blo 1699550 3825017 := bstep (se 2 (by rfl) ⟨1434381, by rfl⟩ : syracuseStep 3825017 = 2868763) B2868763
theorem B4840879 : Blo 1699550 4840879 := bstep (se 1 (by rfl) ⟨3630659, by rfl⟩ : syracuseStep 4840879 = 7261319) B7261319
theorem B4087223 : Blo 1699550 4087223 := bstep (se 1 (by rfl) ⟨3065417, by rfl⟩ : syracuseStep 4087223 = 6130835) B6130835
theorem B176611049 : Blo 1699550 176611049 := bstep (se 2 (by rfl) ⟨66229143, by rfl⟩ : syracuseStep 176611049 = 132458287) B132458287
theorem B12263399 : Blo 1699550 12263399 := bstep (se 1 (by rfl) ⟨9197549, by rfl⟩ : syracuseStep 12263399 = 18395099) B18395099
theorem B21790721 : Blo 1699550 21790721 := bstep (se 2 (by rfl) ⟨8171520, by rfl⟩ : syracuseStep 21790721 = 16343041) B16343041
theorem B15516625 : Blo 1699550 15516625 := bstep (se 2 (by rfl) ⟨5818734, by rfl⟩ : syracuseStep 15516625 = 11637469) B11637469
theorem B2868223 : Blo 1699550 2868223 := bstep (se 1 (by rfl) ⟨2151167, by rfl⟩ : syracuseStep 2868223 = 4302335) B4302335
theorem B3065215 : Blo 1699550 3065215 := bstep (se 1 (by rfl) ⟨2298911, by rfl⟩ : syracuseStep 3065215 = 4597823) B4597823
theorem B3229159 : Blo 1699550 3229159 := bstep (se 1 (by rfl) ⟨2421869, by rfl⟩ : syracuseStep 3229159 = 4843739) B4843739
theorem B3827375 : Blo 1699550 3827375 := bstep (se 1 (by rfl) ⟨2870531, by rfl⟩ : syracuseStep 3827375 = 5741063) B5741063
theorem B2549513 : Blo 1699550 2549513 := bstep (se 2 (by rfl) ⟨956067, by rfl⟩ : syracuseStep 2549513 = 1912135) B1912135
theorem B335398697 : Blo 1699550 335398697 := bstep (se 2 (by rfl) ⟨125774511, by rfl⟩ : syracuseStep 335398697 = 251549023) B251549023
theorem B16353191 : Blo 1699550 16353191 := bstep (se 1 (by rfl) ⟨12264893, by rfl⟩ : syracuseStep 16353191 = 24529787) B24529787
theorem B2549831 : Blo 1699550 2549831 := bstep (se 1 (by rfl) ⟨1912373, by rfl⟩ : syracuseStep 2549831 = 3824747) B3824747
theorem B39258359 : Blo 1699550 39258359 := bstep (se 1 (by rfl) ⟨29443769, by rfl⟩ : syracuseStep 39258359 = 58887539) B58887539
theorem B2550011 : Blo 1699550 2550011 := bstep (se 1 (by rfl) ⟨1912508, by rfl⟩ : syracuseStep 2550011 = 3825017) B3825017
theorem B2869951 : Blo 1699550 2869951 := bstep (se 1 (by rfl) ⟨2152463, by rfl⟩ : syracuseStep 2869951 = 4304927) B4304927
theorem B2550479 : Blo 1699550 2550479 := bstep (se 1 (by rfl) ⟨1912859, by rfl⟩ : syracuseStep 2550479 = 3825719) B3825719
theorem B104704721 : Blo 1699550 104704721 := bstep (se 2 (by rfl) ⟨39264270, by rfl⟩ : syracuseStep 104704721 = 78528541) B78528541
theorem B2550527 : Blo 1699550 2550527 := bstep (se 1 (by rfl) ⟨1912895, by rfl⟩ : syracuseStep 2550527 = 3825791) B3825791
theorem B8170793 : Blo 1699550 8170793 := bstep (se 2 (by rfl) ⟨3064047, by rfl⟩ : syracuseStep 8170793 = 6128095) B6128095
theorem B12913991 : Blo 1699550 12913991 := bstep (se 1 (by rfl) ⟨9685493, by rfl⟩ : syracuseStep 12913991 = 19370987) B19370987
theorem B117796193 : Blo 1699550 117796193 := bstep (se 2 (by rfl) ⟨44173572, by rfl⟩ : syracuseStep 117796193 = 88347145) B88347145
theorem B2551199 : Blo 1699550 2551199 := bstep (se 1 (by rfl) ⟨1913399, by rfl⟩ : syracuseStep 2551199 = 3826799) B3826799
theorem B2870687 : Blo 1699550 2870687 := bstep (se 1 (by rfl) ⟨2153015, by rfl⟩ : syracuseStep 2870687 = 4306031) B4306031
theorem B4304299 : Blo 1699550 4304299 := bstep (se 1 (by rfl) ⟨3228224, by rfl⟩ : syracuseStep 4304299 = 6456449) B6456449
theorem B2870761 : Blo 1699550 2870761 := bstep (se 2 (by rfl) ⟨1076535, by rfl⟩ : syracuseStep 2870761 = 2153071) B2153071
theorem B5737985 : Blo 1699550 5737985 := bstep (se 2 (by rfl) ⟨2151744, by rfl⟩ : syracuseStep 5737985 = 4303489) B4303489
theorem B2870815 : Blo 1699550 2870815 := bstep (se 1 (by rfl) ⟨2153111, by rfl⟩ : syracuseStep 2870815 = 4306223) B4306223
theorem B5525023 : Blo 1699550 5525023 := bstep (se 1 (by rfl) ⟨4143767, by rfl⟩ : syracuseStep 5525023 = 8287535) B8287535
theorem B14528105 : Blo 1699550 14528105 := bstep (se 2 (by rfl) ⟨5448039, by rfl⟩ : syracuseStep 14528105 = 10896079) B10896079
theorem B18386615 : Blo 1699550 18386615 := bstep (se 1 (by rfl) ⟨13789961, by rfl⟩ : syracuseStep 18386615 = 27579923) B27579923
theorem B9318199 : Blo 1699550 9318199 := bstep (se 1 (by rfl) ⟨6988649, by rfl⟩ : syracuseStep 9318199 = 13977299) B13977299
theorem B2551643 : Blo 1699550 2551643 := bstep (se 1 (by rfl) ⟨1913732, by rfl⟩ : syracuseStep 2551643 = 3827465) B3827465
theorem B10342255 : Blo 1699550 10342255 := bstep (se 1 (by rfl) ⟨7756691, by rfl⟩ : syracuseStep 10342255 = 15513383) B15513383
theorem B2551751 : Blo 1699550 2551751 := bstep (se 1 (by rfl) ⟨1913813, by rfl⟩ : syracuseStep 2551751 = 3827627) B3827627
theorem B53072135 : Blo 1699550 53072135 := bstep (se 1 (by rfl) ⟨39804101, by rfl⟩ : syracuseStep 53072135 = 79608203) B79608203
theorem B1700287 : Blo 1699550 1700287 := bstep (se 1 (by rfl) ⟨1275215, by rfl⟩ : syracuseStep 1700287 = 2550431) B2550431
theorem B1700399 : Blo 1699550 1700399 := bstep (se 1 (by rfl) ⟨1275299, by rfl⟩ : syracuseStep 1700399 = 2550599) B2550599
theorem B4305575 : Blo 1699550 4305575 := bstep (se 1 (by rfl) ⟨3229181, by rfl⟩ : syracuseStep 4305575 = 6458363) B6458363
theorem B1938151 : Blo 1699550 1938151 := bstep (se 1 (by rfl) ⟨1453613, by rfl⟩ : syracuseStep 1938151 = 2907227) B2907227
theorem B9687863 : Blo 1699550 9687863 := bstep (se 1 (by rfl) ⟨7265897, by rfl⟩ : syracuseStep 9687863 = 14531795) B14531795
theorem B2724815 : Blo 1699550 2724815 := bstep (se 1 (by rfl) ⟨2043611, by rfl⟩ : syracuseStep 2724815 = 4087223) B4087223
theorem B117740699 : Blo 1699550 117740699 := bstep (se 1 (by rfl) ⟨88305524, by rfl⟩ : syracuseStep 117740699 = 176611049) B176611049
theorem B13792787 : Blo 1699550 13792787 := bstep (se 1 (by rfl) ⟨10344590, by rfl⟩ : syracuseStep 13792787 = 20689181) B20689181
theorem B1701403 : Blo 1699550 1701403 := bstep (se 1 (by rfl) ⟨1276052, by rfl⟩ : syracuseStep 1701403 = 2552105) B2552105
theorem B5740307 : Blo 1699550 5740307 := bstep (se 1 (by rfl) ⟨4305230, by rfl⟩ : syracuseStep 5740307 = 8610461) B8610461
theorem B63780643 : Blo 1699550 63780643 := bstep (se 1 (by rfl) ⟨47835482, by rfl⟩ : syracuseStep 63780643 = 95670965) B95670965
theorem B12253193 : Blo 1699550 12253193 := bstep (se 2 (by rfl) ⟨4594947, by rfl⟩ : syracuseStep 12253193 = 9189895) B9189895
theorem B37771409 : Blo 1699550 37771409 := bstep (se 2 (by rfl) ⟨14164278, by rfl⟩ : syracuseStep 37771409 = 28328557) B28328557
theorem B12916907 : Blo 1699550 12916907 := bstep (se 1 (by rfl) ⟨9687680, by rfl⟩ : syracuseStep 12916907 = 19375361) B19375361
theorem B3824009 : Blo 1699550 3824009 := bstep (se 2 (by rfl) ⟨1434003, by rfl⟩ : syracuseStep 3824009 = 2868007) B2868007
theorem B7264667 : Blo 1699550 7264667 := bstep (se 1 (by rfl) ⟨5448500, by rfl⟩ : syracuseStep 7264667 = 10897001) B10897001
theorem B53074385 : Blo 1699550 53074385 := bstep (se 2 (by rfl) ⟨19902894, by rfl⟩ : syracuseStep 53074385 = 39805789) B39805789
theorem B11197435 : Blo 1699550 11197435 := bstep (se 1 (by rfl) ⟨8398076, by rfl⟩ : syracuseStep 11197435 = 16796153) B16796153
theorem B5741711 : Blo 1699550 5741711 := bstep (se 1 (by rfl) ⟨4306283, by rfl⟩ : syracuseStep 5741711 = 8612567) B8612567
theorem B6454505 : Blo 1699550 6454505 := bstep (se 2 (by rfl) ⟨2420439, by rfl⟩ : syracuseStep 6454505 = 4840879) B4840879
theorem B5741819 : Blo 1699550 5741819 := bstep (se 1 (by rfl) ⟨4306364, by rfl⟩ : syracuseStep 5741819 = 8612729) B8612729
theorem B5741927 : Blo 1699550 5741927 := bstep (se 1 (by rfl) ⟨4306445, by rfl⟩ : syracuseStep 5741927 = 8612891) B8612891
theorem B46521847 : Blo 1699550 46521847 := bstep (se 1 (by rfl) ⟨34891385, by rfl⟩ : syracuseStep 46521847 = 69782771) B69782771
theorem B5742143 : Blo 1699550 5742143 := bstep (se 1 (by rfl) ⟨4306607, by rfl⟩ : syracuseStep 5742143 = 8613215) B8613215
theorem B11050667 : Blo 1699550 11050667 := bstep (se 1 (by rfl) ⟨8288000, by rfl⟩ : syracuseStep 11050667 = 16576001) B16576001
theorem B4841279 : Blo 1699550 4841279 := bstep (se 1 (by rfl) ⟨3630959, by rfl⟩ : syracuseStep 4841279 = 7261919) B7261919
theorem B8175599 : Blo 1699550 8175599 := bstep (se 1 (by rfl) ⟨6131699, by rfl⟩ : syracuseStep 8175599 = 12263399) B12263399
theorem B35381423 : Blo 1699550 35381423 := bstep (se 1 (by rfl) ⟨26536067, by rfl⟩ : syracuseStep 35381423 = 53072135) B53072135
theorem B3826601 : Blo 1699550 3826601 := bstep (se 2 (by rfl) ⟨1434975, by rfl⟩ : syracuseStep 3826601 = 2869951) B2869951
theorem B3826871 : Blo 1699550 3826871 := bstep (se 1 (by rfl) ⟨2870153, by rfl⟩ : syracuseStep 3826871 = 5740307) B5740307
theorem B8168795 : Blo 1699550 8168795 := bstep (se 1 (by rfl) ⟨6126596, by rfl⟩ : syracuseStep 8168795 = 12253193) B12253193
theorem B8611271 : Blo 1699550 8611271 := bstep (se 1 (by rfl) ⟨6458453, by rfl⟩ : syracuseStep 8611271 = 12916907) B12916907
theorem B2549339 : Blo 1699550 2549339 := bstep (se 1 (by rfl) ⟨1912004, by rfl⟩ : syracuseStep 2549339 = 3824009) B3824009
theorem B35382923 : Blo 1699550 35382923 := bstep (se 1 (by rfl) ⟨26537192, by rfl⟩ : syracuseStep 35382923 = 53074385) B53074385
theorem B3827681 : Blo 1699550 3827681 := bstep (se 2 (by rfl) ⟨1435380, by rfl⟩ : syracuseStep 3827681 = 2870761) B2870761
theorem B3827753 : Blo 1699550 3827753 := bstep (se 2 (by rfl) ⟨1435407, by rfl⟩ : syracuseStep 3827753 = 2870815) B2870815
theorem B7366697 : Blo 1699550 7366697 := bstep (se 2 (by rfl) ⟨2762511, by rfl⟩ : syracuseStep 7366697 = 5525023) B5525023
theorem B3827807 : Blo 1699550 3827807 := bstep (se 1 (by rfl) ⟨2870855, by rfl⟩ : syracuseStep 3827807 = 5741711) B5741711
theorem B4303003 : Blo 1699550 4303003 := bstep (se 1 (by rfl) ⟨3227252, by rfl⟩ : syracuseStep 4303003 = 6454505) B6454505
theorem B3827879 : Blo 1699550 3827879 := bstep (se 1 (by rfl) ⟨2870909, by rfl⟩ : syracuseStep 3827879 = 5741819) B5741819
theorem B78530795 : Blo 1699550 78530795 := bstep (se 1 (by rfl) ⟨58898096, by rfl⟩ : syracuseStep 78530795 = 117796193) B117796193
theorem B3827951 : Blo 1699550 3827951 := bstep (se 1 (by rfl) ⟨2870963, by rfl⟩ : syracuseStep 3827951 = 5741927) B5741927
theorem B3828095 : Blo 1699550 3828095 := bstep (se 1 (by rfl) ⟨2871071, by rfl⟩ : syracuseStep 3828095 = 5742143) B5742143
theorem B9685403 : Blo 1699550 9685403 := bstep (se 1 (by rfl) ⟨7264052, by rfl⟩ : syracuseStep 9685403 = 14528105) B14528105
theorem B7367111 : Blo 1699550 7367111 := bstep (se 1 (by rfl) ⟨5525333, by rfl⟩ : syracuseStep 7367111 = 11050667) B11050667
theorem B12257743 : Blo 1699550 12257743 := bstep (se 1 (by rfl) ⟨9193307, by rfl⟩ : syracuseStep 12257743 = 18386615) B18386615
theorem B13789673 : Blo 1699550 13789673 := bstep (se 2 (by rfl) ⟨5171127, by rfl⟩ : syracuseStep 13789673 = 10342255) B10342255
theorem B5450399 : Blo 1699550 5450399 := bstep (se 1 (by rfl) ⟨4087799, by rfl⟩ : syracuseStep 5450399 = 8175599) B8175599
theorem B14527147 : Blo 1699550 14527147 := bstep (se 1 (by rfl) ⟨10895360, by rfl⟩ : syracuseStep 14527147 = 21790721) B21790721
theorem B2870383 : Blo 1699550 2870383 := bstep (se 1 (by rfl) ⟨2152787, by rfl⟩ : syracuseStep 2870383 = 4305575) B4305575
theorem B6458575 : Blo 1699550 6458575 := bstep (se 1 (by rfl) ⟨4843931, by rfl⟩ : syracuseStep 6458575 = 9687863) B9687863
theorem B9195191 : Blo 1699550 9195191 := bstep (se 1 (by rfl) ⟨6896393, by rfl⟩ : syracuseStep 9195191 = 13792787) B13792787
theorem B2551583 : Blo 1699550 2551583 := bstep (se 1 (by rfl) ⟨1913687, by rfl⟩ : syracuseStep 2551583 = 3827375) B3827375
theorem B1699675 : Blo 1699550 1699675 := bstep (se 1 (by rfl) ⟨1274756, by rfl⟩ : syracuseStep 1699675 = 2549513) B2549513
theorem B20688833 : Blo 1699550 20688833 := bstep (se 2 (by rfl) ⟨7758312, by rfl⟩ : syracuseStep 20688833 = 15516625) B15516625
theorem B14929913 : Blo 1699550 14929913 := bstep (se 2 (by rfl) ⟨5598717, by rfl⟩ : syracuseStep 14929913 = 11197435) B11197435
theorem B1699887 : Blo 1699550 1699887 := bstep (se 1 (by rfl) ⟨1274915, by rfl⟩ : syracuseStep 1699887 = 2549831) B2549831
theorem B1700007 : Blo 1699550 1700007 := bstep (se 1 (by rfl) ⟨1275005, by rfl⟩ : syracuseStep 1700007 = 2550011) B2550011
theorem B1700319 : Blo 1699550 1700319 := bstep (se 1 (by rfl) ⟨1275239, by rfl⟩ : syracuseStep 1700319 = 2550479) B2550479
theorem B1700351 : Blo 1699550 1700351 := bstep (se 1 (by rfl) ⟨1275263, by rfl⟩ : syracuseStep 1700351 = 2550527) B2550527
theorem B5739065 : Blo 1699550 5739065 := bstep (se 2 (by rfl) ⟨2152149, by rfl⟩ : syracuseStep 5739065 = 4304299) B4304299
theorem B4305545 : Blo 1699550 4305545 := bstep (se 2 (by rfl) ⟨1614579, by rfl⟩ : syracuseStep 4305545 = 3229159) B3229159
theorem B1700799 : Blo 1699550 1700799 := bstep (se 1 (by rfl) ⟨1275599, by rfl⟩ : syracuseStep 1700799 = 2551199) B2551199
theorem B1913791 : Blo 1699550 1913791 := bstep (se 1 (by rfl) ⟨1435343, by rfl⟩ : syracuseStep 1913791 = 2870687) B2870687
theorem B12424265 : Blo 1699550 12424265 := bstep (se 2 (by rfl) ⟨4659099, by rfl⟩ : syracuseStep 12424265 = 9318199) B9318199
theorem B1701095 : Blo 1699550 1701095 := bstep (se 1 (by rfl) ⟨1275821, by rfl⟩ : syracuseStep 1701095 = 2551643) B2551643
theorem B248116517 : Blo 1699550 248116517 := bstep (se 4 (by rfl) ⟨23260923, by rfl⟩ : syracuseStep 248116517 = 46521847) B46521847
theorem B1701167 : Blo 1699550 1701167 := bstep (se 1 (by rfl) ⟨1275875, by rfl⟩ : syracuseStep 1701167 = 2551751) B2551751
theorem B1816543 : Blo 1699550 1816543 := bstep (se 1 (by rfl) ⟨1362407, by rfl⟩ : syracuseStep 1816543 = 2724815) B2724815
theorem B78493799 : Blo 1699550 78493799 := bstep (se 1 (by rfl) ⟨58870349, by rfl⟩ : syracuseStep 78493799 = 117740699) B117740699
theorem B19372445 : Blo 1699550 19372445 := bstep (se 3 (by rfl) ⟨3632333, by rfl⟩ : syracuseStep 19372445 = 7264667) B7264667
theorem B223599131 : Blo 1699550 223599131 := bstep (se 1 (by rfl) ⟨167699348, by rfl⟩ : syracuseStep 223599131 = 335398697) B335398697
theorem B10336805 : Blo 1699550 10336805 := bstep (se 4 (by rfl) ⟨969075, by rfl⟩ : syracuseStep 10336805 = 1938151) B1938151
theorem B10902127 : Blo 1699550 10902127 := bstep (se 1 (by rfl) ⟨8176595, by rfl⟩ : syracuseStep 10902127 = 16353191) B16353191
theorem B3824297 : Blo 1699550 3824297 := bstep (se 2 (by rfl) ⟨1434111, by rfl⟩ : syracuseStep 3824297 = 2868223) B2868223
theorem B25180939 : Blo 1699550 25180939 := bstep (se 1 (by rfl) ⟨18885704, by rfl⟩ : syracuseStep 25180939 = 37771409) B37771409
theorem B26172239 : Blo 1699550 26172239 := bstep (se 1 (by rfl) ⟨19629179, by rfl⟩ : syracuseStep 26172239 = 39258359) B39258359
theorem B69803147 : Blo 1699550 69803147 := bstep (se 1 (by rfl) ⟨52352360, by rfl⟩ : syracuseStep 69803147 = 104704721) B104704721
theorem B4086953 : Blo 1699550 4086953 := bstep (se 2 (by rfl) ⟨1532607, by rfl⟩ : syracuseStep 4086953 = 3065215) B3065215
theorem B5447195 : Blo 1699550 5447195 := bstep (se 1 (by rfl) ⟨4085396, by rfl⟩ : syracuseStep 5447195 = 8170793) B8170793
theorem B8609327 : Blo 1699550 8609327 := bstep (se 1 (by rfl) ⟨6456995, by rfl⟩ : syracuseStep 8609327 = 12913991) B12913991
theorem B3825323 : Blo 1699550 3825323 := bstep (se 1 (by rfl) ⟨2868992, by rfl⟩ : syracuseStep 3825323 = 5737985) B5737985
theorem B85040857 : Blo 1699550 85040857 := bstep (se 2 (by rfl) ⟨31890321, by rfl⟩ : syracuseStep 85040857 = 63780643) B63780643
theorem B3227519 : Blo 1699550 3227519 := bstep (se 1 (by rfl) ⟨2420639, by rfl⟩ : syracuseStep 3227519 = 4841279) B4841279
theorem B3826043 : Blo 1699550 3826043 := bstep (se 1 (by rfl) ⟨2869532, by rfl⟩ : syracuseStep 3826043 = 5739065) B5739065
theorem B16343657 : Blo 1699550 16343657 := bstep (se 2 (by rfl) ⟨6128871, by rfl⟩ : syracuseStep 16343657 = 12257743) B12257743
theorem B8282843 : Blo 1699550 8282843 := bstep (se 1 (by rfl) ⟨6212132, by rfl⟩ : syracuseStep 8282843 = 12424265) B12424265
theorem B453551237 : Blo 1699550 453551237 := bstep (se 4 (by rfl) ⟨42520428, by rfl⟩ : syracuseStep 453551237 = 85040857) B85040857
theorem B3827177 : Blo 1699550 3827177 := bstep (se 2 (by rfl) ⟨1435191, by rfl⟩ : syracuseStep 3827177 = 2870383) B2870383
theorem B6456935 : Blo 1699550 6456935 := bstep (se 1 (by rfl) ⟨4842701, by rfl⟩ : syracuseStep 6456935 = 9685403) B9685403
theorem B8611433 : Blo 1699550 8611433 := bstep (se 2 (by rfl) ⟨3229287, by rfl⟩ : syracuseStep 8611433 = 6458575) B6458575
theorem B9193115 : Blo 1699550 9193115 := bstep (se 1 (by rfl) ⟨6894836, by rfl⟩ : syracuseStep 9193115 = 13789673) B13789673
theorem B6891203 : Blo 1699550 6891203 := bstep (se 1 (by rfl) ⟨5168402, by rfl⟩ : syracuseStep 6891203 = 10336805) B10336805
theorem B2549531 : Blo 1699550 2549531 := bstep (se 1 (by rfl) ⟨1912148, by rfl⟩ : syracuseStep 2549531 = 3824297) B3824297
theorem B3631463 : Blo 1699550 3631463 := bstep (se 1 (by rfl) ⟨2723597, by rfl⟩ : syracuseStep 3631463 = 5447195) B5447195
theorem B2550215 : Blo 1699550 2550215 := bstep (se 1 (by rfl) ⟨1912661, by rfl⟩ : syracuseStep 2550215 = 3825323) B3825323
theorem B6130127 : Blo 1699550 6130127 := bstep (se 1 (by rfl) ⟨4597595, by rfl⟩ : syracuseStep 6130127 = 9195191) B9195191
theorem B23587615 : Blo 1699550 23587615 := bstep (se 1 (by rfl) ⟨17690711, by rfl⟩ : syracuseStep 23587615 = 35381423) B35381423
theorem B5737337 : Blo 1699550 5737337 := bstep (se 2 (by rfl) ⟨2151501, by rfl⟩ : syracuseStep 5737337 = 4303003) B4303003
theorem B2870363 : Blo 1699550 2870363 := bstep (se 1 (by rfl) ⟨2152772, by rfl⟩ : syracuseStep 2870363 = 4305545) B4305545
theorem B2551067 : Blo 1699550 2551067 := bstep (se 1 (by rfl) ⟨1913300, by rfl⟩ : syracuseStep 2551067 = 3826601) B3826601
theorem B2551247 : Blo 1699550 2551247 := bstep (se 1 (by rfl) ⟨1913435, by rfl⟩ : syracuseStep 2551247 = 3826871) B3826871
theorem B14536169 : Blo 1699550 14536169 := bstep (se 2 (by rfl) ⟨5451063, by rfl⟩ : syracuseStep 14536169 = 10902127) B10902127
theorem B19369529 : Blo 1699550 19369529 := bstep (se 2 (by rfl) ⟨7263573, by rfl⟩ : syracuseStep 19369529 = 14527147) B14527147
theorem B33574585 : Blo 1699550 33574585 := bstep (se 2 (by rfl) ⟨12590469, by rfl⟩ : syracuseStep 33574585 = 25180939) B25180939
theorem B1699559 : Blo 1699550 1699559 := bstep (se 1 (by rfl) ⟨1274669, by rfl⟩ : syracuseStep 1699559 = 2549339) B2549339
theorem B23588615 : Blo 1699550 23588615 := bstep (se 1 (by rfl) ⟨17691461, by rfl⟩ : syracuseStep 23588615 = 35382923) B35382923
theorem B2551721 : Blo 1699550 2551721 := bstep (se 2 (by rfl) ⟨956895, by rfl⟩ : syracuseStep 2551721 = 1913791) B1913791
theorem B2551787 : Blo 1699550 2551787 := bstep (se 1 (by rfl) ⟨1913840, by rfl⟩ : syracuseStep 2551787 = 3827681) B3827681
theorem B2551835 : Blo 1699550 2551835 := bstep (se 1 (by rfl) ⟨1913876, by rfl⟩ : syracuseStep 2551835 = 3827753) B3827753
theorem B4911131 : Blo 1699550 4911131 := bstep (se 1 (by rfl) ⟨3683348, by rfl⟩ : syracuseStep 4911131 = 7366697) B7366697
theorem B2551871 : Blo 1699550 2551871 := bstep (se 1 (by rfl) ⟨1913903, by rfl⟩ : syracuseStep 2551871 = 3827807) B3827807
theorem B2551919 : Blo 1699550 2551919 := bstep (se 1 (by rfl) ⟨1913939, by rfl⟩ : syracuseStep 2551919 = 3827879) B3827879
theorem B2551967 : Blo 1699550 2551967 := bstep (se 1 (by rfl) ⟨1913975, by rfl⟩ : syracuseStep 2551967 = 3827951) B3827951
theorem B2552063 : Blo 1699550 2552063 := bstep (se 1 (by rfl) ⟨1914047, by rfl⟩ : syracuseStep 2552063 = 3828095) B3828095
theorem B12914963 : Blo 1699550 12914963 := bstep (se 1 (by rfl) ⟨9686222, by rfl⟩ : syracuseStep 12914963 = 19372445) B19372445
theorem B4911407 : Blo 1699550 4911407 := bstep (se 1 (by rfl) ⟨3683555, by rfl⟩ : syracuseStep 4911407 = 7367111) B7367111
theorem B149066087 : Blo 1699550 149066087 := bstep (se 1 (by rfl) ⟨111799565, by rfl⟩ : syracuseStep 149066087 = 223599131) B223599131
theorem B3633599 : Blo 1699550 3633599 := bstep (se 1 (by rfl) ⟨2725199, by rfl⟩ : syracuseStep 3633599 = 5450399) B5450399
theorem B46535431 : Blo 1699550 46535431 := bstep (se 1 (by rfl) ⟨34901573, by rfl⟩ : syracuseStep 46535431 = 69803147) B69803147
theorem B2724635 : Blo 1699550 2724635 := bstep (se 1 (by rfl) ⟨2043476, by rfl⟩ : syracuseStep 2724635 = 4086953) B4086953
theorem B69792637 : Blo 1699550 69792637 := bstep (se 3 (by rfl) ⟨13086119, by rfl⟩ : syracuseStep 69792637 = 26172239) B26172239
theorem B5739551 : Blo 1699550 5739551 := bstep (se 1 (by rfl) ⟨4304663, by rfl⟩ : syracuseStep 5739551 = 8609327) B8609327
theorem B1701055 : Blo 1699550 1701055 := bstep (se 1 (by rfl) ⟨1275791, by rfl⟩ : syracuseStep 1701055 = 2551583) B2551583
theorem B2151679 : Blo 1699550 2151679 := bstep (se 1 (by rfl) ⟨1613759, by rfl⟩ : syracuseStep 2151679 = 3227519) B3227519
theorem B2422057 : Blo 1699550 2422057 := bstep (se 2 (by rfl) ⟨908271, by rfl⟩ : syracuseStep 2422057 = 1816543) B1816543
theorem B13792555 : Blo 1699550 13792555 := bstep (se 1 (by rfl) ⟨10344416, by rfl⟩ : syracuseStep 13792555 = 20688833) B20688833
theorem B165411011 : Blo 1699550 165411011 := bstep (se 1 (by rfl) ⟨124058258, by rfl⟩ : syracuseStep 165411011 = 248116517) B248116517
theorem B5445863 : Blo 1699550 5445863 := bstep (se 1 (by rfl) ⟨4084397, by rfl⟩ : syracuseStep 5445863 = 8168795) B8168795
theorem B5740847 : Blo 1699550 5740847 := bstep (se 1 (by rfl) ⟨4305635, by rfl⟩ : syracuseStep 5740847 = 8611271) B8611271
theorem B52329199 : Blo 1699550 52329199 := bstep (se 1 (by rfl) ⟨39246899, by rfl⟩ : syracuseStep 52329199 = 78493799) B78493799
theorem B52353863 : Blo 1699550 52353863 := bstep (se 1 (by rfl) ⟨39265397, by rfl⟩ : syracuseStep 52353863 = 78530795) B78530795
theorem B9953275 : Blo 1699550 9953275 := bstep (se 1 (by rfl) ⟨7464956, by rfl⟩ : syracuseStep 9953275 = 14929913) B14929913
theorem B8609975 : Blo 1699550 8609975 := bstep (se 1 (by rfl) ⟨6457481, by rfl⟩ : syracuseStep 8609975 = 12914963) B12914963
theorem B10895771 : Blo 1699550 10895771 := bstep (se 1 (by rfl) ⟨8171828, by rfl⟩ : syracuseStep 10895771 = 16343657) B16343657
theorem B5521895 : Blo 1699550 5521895 := bstep (se 1 (by rfl) ⟨4141421, by rfl⟩ : syracuseStep 5521895 = 8282843) B8282843
theorem B3826367 : Blo 1699550 3826367 := bstep (se 1 (by rfl) ⟨2869775, by rfl⟩ : syracuseStep 3826367 = 5739551) B5739551
theorem B302367491 : Blo 1699550 302367491 := bstep (se 1 (by rfl) ⟨226775618, by rfl⟩ : syracuseStep 302367491 = 453551237) B453551237
theorem B397509565 : Blo 1699550 397509565 := bstep (se 3 (by rfl) ⟨74533043, by rfl⟩ : syracuseStep 397509565 = 149066087) B149066087
theorem B69772265 : Blo 1699550 69772265 := bstep (se 2 (by rfl) ⟨26164599, by rfl⟩ : syracuseStep 69772265 = 52329199) B52329199
theorem B62047241 : Blo 1699550 62047241 := bstep (se 2 (by rfl) ⟨23267715, by rfl⟩ : syracuseStep 62047241 = 46535431) B46535431
theorem B31450153 : Blo 1699550 31450153 := bstep (se 2 (by rfl) ⟨11793807, by rfl⟩ : syracuseStep 31450153 = 23587615) B23587615
theorem B110274007 : Blo 1699550 110274007 := bstep (se 1 (by rfl) ⟨82705505, by rfl⟩ : syracuseStep 110274007 = 165411011) B165411011
theorem B3630575 : Blo 1699550 3630575 := bstep (se 1 (by rfl) ⟨2722931, by rfl⟩ : syracuseStep 3630575 = 5445863) B5445863
theorem B3827231 : Blo 1699550 3827231 := bstep (se 1 (by rfl) ⟨2870423, by rfl⟩ : syracuseStep 3827231 = 5740847) B5740847
theorem B2868905 : Blo 1699550 2868905 := bstep (se 2 (by rfl) ⟨1075839, by rfl⟩ : syracuseStep 2868905 = 2151679) B2151679
theorem B3229409 : Blo 1699550 3229409 := bstep (se 2 (by rfl) ⟨1211028, by rfl⟩ : syracuseStep 3229409 = 2422057) B2422057
theorem B18376541 : Blo 1699550 18376541 := bstep (se 3 (by rfl) ⟨3445601, by rfl⟩ : syracuseStep 18376541 = 6891203) B6891203
theorem B12913019 : Blo 1699550 12913019 := bstep (se 1 (by rfl) ⟨9684764, by rfl⟩ : syracuseStep 12913019 = 19369529) B19369529
theorem B2550695 : Blo 1699550 2550695 := bstep (se 1 (by rfl) ⟨1913021, by rfl⟩ : syracuseStep 2550695 = 3826043) B3826043
theorem B2551451 : Blo 1699550 2551451 := bstep (se 1 (by rfl) ⟨1913588, by rfl⟩ : syracuseStep 2551451 = 3827177) B3827177
theorem B4304623 : Blo 1699550 4304623 := bstep (se 1 (by rfl) ⟨3228467, by rfl⟩ : syracuseStep 4304623 = 6456935) B6456935
theorem B93056849 : Blo 1699550 93056849 := bstep (se 2 (by rfl) ⟨34896318, by rfl⟩ : syracuseStep 93056849 = 69792637) B69792637
theorem B1699687 : Blo 1699550 1699687 := bstep (se 1 (by rfl) ⟨1274765, by rfl⟩ : syracuseStep 1699687 = 2549531) B2549531
theorem B16347005 : Blo 1699550 16347005 := bstep (se 3 (by rfl) ⟨3065063, by rfl⟩ : syracuseStep 16347005 = 6130127) B6130127
theorem B2420975 : Blo 1699550 2420975 := bstep (se 1 (by rfl) ⟨1815731, by rfl⟩ : syracuseStep 2420975 = 3631463) B3631463
theorem B1700143 : Blo 1699550 1700143 := bstep (se 1 (by rfl) ⟨1275107, by rfl⟩ : syracuseStep 1700143 = 2550215) B2550215
theorem B24514973 : Blo 1699550 24514973 := bstep (se 3 (by rfl) ⟨4596557, by rfl⟩ : syracuseStep 24514973 = 9193115) B9193115
theorem B34902575 : Blo 1699550 34902575 := bstep (se 1 (by rfl) ⟨26176931, by rfl⟩ : syracuseStep 34902575 = 52353863) B52353863
theorem B62902973 : Blo 1699550 62902973 := bstep (se 3 (by rfl) ⟨11794307, by rfl⟩ : syracuseStep 62902973 = 23588615) B23588615
theorem B1913575 : Blo 1699550 1913575 := bstep (se 1 (by rfl) ⟨1435181, by rfl⟩ : syracuseStep 1913575 = 2870363) B2870363
theorem B1700711 : Blo 1699550 1700711 := bstep (se 1 (by rfl) ⟨1275533, by rfl⟩ : syracuseStep 1700711 = 2551067) B2551067
theorem B44766113 : Blo 1699550 44766113 := bstep (se 2 (by rfl) ⟨16787292, by rfl⟩ : syracuseStep 44766113 = 33574585) B33574585
theorem B13271033 : Blo 1699550 13271033 := bstep (se 2 (by rfl) ⟨4976637, by rfl⟩ : syracuseStep 13271033 = 9953275) B9953275
theorem B1700831 : Blo 1699550 1700831 := bstep (se 1 (by rfl) ⟨1275623, by rfl⟩ : syracuseStep 1700831 = 2551247) B2551247
theorem B1701147 : Blo 1699550 1701147 := bstep (se 1 (by rfl) ⟨1275860, by rfl⟩ : syracuseStep 1701147 = 2551721) B2551721
theorem B1701191 : Blo 1699550 1701191 := bstep (se 1 (by rfl) ⟨1275893, by rfl⟩ : syracuseStep 1701191 = 2551787) B2551787
theorem B1701223 : Blo 1699550 1701223 := bstep (se 1 (by rfl) ⟨1275917, by rfl⟩ : syracuseStep 1701223 = 2551835) B2551835
theorem B1701247 : Blo 1699550 1701247 := bstep (se 1 (by rfl) ⟨1275935, by rfl⟩ : syracuseStep 1701247 = 2551871) B2551871
theorem B13096349 : Blo 1699550 13096349 := bstep (se 3 (by rfl) ⟨2455565, by rfl⟩ : syracuseStep 13096349 = 4911131) B4911131
theorem B1701279 : Blo 1699550 1701279 := bstep (se 1 (by rfl) ⟨1275959, by rfl⟩ : syracuseStep 1701279 = 2551919) B2551919
theorem B1701311 : Blo 1699550 1701311 := bstep (se 1 (by rfl) ⟨1275983, by rfl⟩ : syracuseStep 1701311 = 2551967) B2551967
theorem B1701375 : Blo 1699550 1701375 := bstep (se 1 (by rfl) ⟨1276031, by rfl⟩ : syracuseStep 1701375 = 2552063) B2552063
theorem B3274271 : Blo 1699550 3274271 := bstep (se 1 (by rfl) ⟨2455703, by rfl⟩ : syracuseStep 3274271 = 4911407) B4911407
theorem B2422399 : Blo 1699550 2422399 := bstep (se 1 (by rfl) ⟨1816799, by rfl⟩ : syracuseStep 2422399 = 3633599) B3633599
theorem B5740955 : Blo 1699550 5740955 := bstep (se 1 (by rfl) ⟨4305716, by rfl⟩ : syracuseStep 5740955 = 8611433) B8611433
theorem B18390073 : Blo 1699550 18390073 := bstep (se 2 (by rfl) ⟨6896277, by rfl⟩ : syracuseStep 18390073 = 13792555) B13792555
theorem B3824891 : Blo 1699550 3824891 := bstep (se 1 (by rfl) ⟨2868668, by rfl⟩ : syracuseStep 3824891 = 5737337) B5737337
theorem B7265693 : Blo 1699550 7265693 := bstep (se 3 (by rfl) ⟨1362317, by rfl⟩ : syracuseStep 7265693 = 2724635) B2724635
theorem B9690779 : Blo 1699550 9690779 := bstep (se 1 (by rfl) ⟨7268084, by rfl⟩ : syracuseStep 9690779 = 14536169) B14536169
theorem B16343315 : Blo 1699550 16343315 := bstep (se 1 (by rfl) ⟨12257486, by rfl⟩ : syracuseStep 16343315 = 24514973) B24514973
theorem B41935315 : Blo 1699550 41935315 := bstep (se 1 (by rfl) ⟨31451486, by rfl⟩ : syracuseStep 41935315 = 62902973) B62902973
theorem B6455933 : Blo 1699550 6455933 := bstep (se 3 (by rfl) ⟨1210487, by rfl⟩ : syracuseStep 6455933 = 2420975) B2420975
theorem B46514843 : Blo 1699550 46514843 := bstep (se 1 (by rfl) ⟨34886132, by rfl⟩ : syracuseStep 46514843 = 69772265) B69772265
theorem B24520097 : Blo 1699550 24520097 := bstep (se 2 (by rfl) ⟨9195036, by rfl⟩ : syracuseStep 24520097 = 18390073) B18390073
theorem B3827303 : Blo 1699550 3827303 := bstep (se 1 (by rfl) ⟨2870477, by rfl⟩ : syracuseStep 3827303 = 5740955) B5740955
theorem B477505205 : Blo 1699550 477505205 := bstep (se 5 (by rfl) ⟨22383056, by rfl⟩ : syracuseStep 477505205 = 44766113) B44766113
theorem B8611757 : Blo 1699550 8611757 := bstep (se 3 (by rfl) ⟨1614704, by rfl⟩ : syracuseStep 8611757 = 3229409) B3229409
theorem B147032009 : Blo 1699550 147032009 := bstep (se 2 (by rfl) ⟨55137003, by rfl⟩ : syracuseStep 147032009 = 110274007) B110274007
theorem B2549927 : Blo 1699550 2549927 := bstep (se 1 (by rfl) ⟨1912445, by rfl⟩ : syracuseStep 2549927 = 3824891) B3824891
theorem B3229865 : Blo 1699550 3229865 := bstep (se 2 (by rfl) ⟨1211199, by rfl⟩ : syracuseStep 3229865 = 2422399) B2422399
theorem B4843795 : Blo 1699550 4843795 := bstep (se 1 (by rfl) ⟨3632846, by rfl⟩ : syracuseStep 4843795 = 7265693) B7265693
theorem B10898003 : Blo 1699550 10898003 := bstep (se 1 (by rfl) ⟨8173502, by rfl⟩ : syracuseStep 10898003 = 16347005) B16347005
theorem B3681263 : Blo 1699550 3681263 := bstep (se 1 (by rfl) ⟨2760947, by rfl⟩ : syracuseStep 3681263 = 5521895) B5521895
theorem B23268383 : Blo 1699550 23268383 := bstep (se 1 (by rfl) ⟨17451287, by rfl⟩ : syracuseStep 23268383 = 34902575) B34902575
theorem B2550911 : Blo 1699550 2550911 := bstep (se 1 (by rfl) ⟨1913183, by rfl⟩ : syracuseStep 2550911 = 3826367) B3826367
theorem B41364827 : Blo 1699550 41364827 := bstep (se 1 (by rfl) ⟨31023620, by rfl⟩ : syracuseStep 41364827 = 62047241) B62047241
theorem B2551433 : Blo 1699550 2551433 := bstep (se 2 (by rfl) ⟨956787, by rfl⟩ : syracuseStep 2551433 = 1913575) B1913575
theorem B2420383 : Blo 1699550 2420383 := bstep (se 1 (by rfl) ⟨1815287, by rfl⟩ : syracuseStep 2420383 = 3630575) B3630575
theorem B2551487 : Blo 1699550 2551487 := bstep (se 1 (by rfl) ⟨1913615, by rfl⟩ : syracuseStep 2551487 = 3827231) B3827231
theorem B2182847 : Blo 1699550 2182847 := bstep (se 1 (by rfl) ⟨1637135, by rfl⟩ : syracuseStep 2182847 = 3274271) B3274271
theorem B1912603 : Blo 1699550 1912603 := bstep (se 1 (by rfl) ⟨1434452, by rfl⟩ : syracuseStep 1912603 = 2868905) B2868905
theorem B12251027 : Blo 1699550 12251027 := bstep (se 1 (by rfl) ⟨9188270, by rfl⟩ : syracuseStep 12251027 = 18376541) B18376541
theorem B1700463 : Blo 1699550 1700463 := bstep (se 1 (by rfl) ⟨1275347, by rfl⟩ : syracuseStep 1700463 = 2550695) B2550695
theorem B5739497 : Blo 1699550 5739497 := bstep (se 2 (by rfl) ⟨2152311, by rfl⟩ : syracuseStep 5739497 = 4304623) B4304623
theorem B1700967 : Blo 1699550 1700967 := bstep (se 1 (by rfl) ⟨1275725, by rfl⟩ : syracuseStep 1700967 = 2551451) B2551451
theorem B6460519 : Blo 1699550 6460519 := bstep (se 1 (by rfl) ⟨4845389, by rfl⟩ : syracuseStep 6460519 = 9690779) B9690779
theorem B5739983 : Blo 1699550 5739983 := bstep (se 1 (by rfl) ⟨4304987, by rfl⟩ : syracuseStep 5739983 = 8609975) B8609975
theorem B7263847 : Blo 1699550 7263847 := bstep (se 1 (by rfl) ⟨5447885, by rfl⟩ : syracuseStep 7263847 = 10895771) B10895771
theorem B201578327 : Blo 1699550 201578327 := bstep (se 1 (by rfl) ⟨151183745, by rfl⟩ : syracuseStep 201578327 = 302367491) B302367491
theorem B8730899 : Blo 1699550 8730899 := bstep (se 1 (by rfl) ⟨6548174, by rfl⟩ : syracuseStep 8730899 = 13096349) B13096349
theorem B530012753 : Blo 1699550 530012753 := bstep (se 2 (by rfl) ⟨198754782, by rfl⟩ : syracuseStep 530012753 = 397509565) B397509565
theorem B41933537 : Blo 1699550 41933537 := bstep (se 2 (by rfl) ⟨15725076, by rfl⟩ : syracuseStep 41933537 = 31450153) B31450153
theorem B8608679 : Blo 1699550 8608679 := bstep (se 1 (by rfl) ⟨6456509, by rfl⟩ : syracuseStep 8608679 = 12913019) B12913019
theorem B62037899 : Blo 1699550 62037899 := bstep (se 1 (by rfl) ⟨46528424, by rfl⟩ : syracuseStep 62037899 = 93056849) B93056849
theorem B8847355 : Blo 1699550 8847355 := bstep (se 1 (by rfl) ⟨6635516, by rfl⟩ : syracuseStep 8847355 = 13271033) B13271033
theorem B10895543 : Blo 1699550 10895543 := bstep (se 1 (by rfl) ⟨8171657, by rfl⟩ : syracuseStep 10895543 = 16343315) B16343315
theorem B3826331 : Blo 1699550 3826331 := bstep (se 1 (by rfl) ⟨2869748, by rfl⟩ : syracuseStep 3826331 = 5739497) B5739497
theorem B3826655 : Blo 1699550 3826655 := bstep (se 1 (by rfl) ⟨2869991, by rfl⟩ : syracuseStep 3826655 = 5739983) B5739983
theorem B9685129 : Blo 1699550 9685129 := bstep (se 2 (by rfl) ⟨3631923, by rfl⟩ : syracuseStep 9685129 = 7263847) B7263847
theorem B27576551 : Blo 1699550 27576551 := bstep (se 1 (by rfl) ⟨20682413, by rfl⟩ : syracuseStep 27576551 = 41364827) B41364827
theorem B2550137 : Blo 1699550 2550137 := bstep (se 2 (by rfl) ⟨956301, by rfl⟩ : syracuseStep 2550137 = 1912603) B1912603
theorem B6458393 : Blo 1699550 6458393 := bstep (se 2 (by rfl) ⟨2421897, by rfl⟩ : syracuseStep 6458393 = 4843795) B4843795
theorem B4303955 : Blo 1699550 4303955 := bstep (se 1 (by rfl) ⟨3227966, by rfl⟩ : syracuseStep 4303955 = 6455933) B6455933
theorem B31009895 : Blo 1699550 31009895 := bstep (se 1 (by rfl) ⟨23257421, by rfl⟩ : syracuseStep 31009895 = 46514843) B46514843
theorem B55913753 : Blo 1699550 55913753 := bstep (se 2 (by rfl) ⟨20967657, by rfl⟩ : syracuseStep 55913753 = 41935315) B41935315
theorem B2551535 : Blo 1699550 2551535 := bstep (se 1 (by rfl) ⟨1913651, by rfl⟩ : syracuseStep 2551535 = 3827303) B3827303
theorem B318336803 : Blo 1699550 318336803 := bstep (se 1 (by rfl) ⟨238752602, by rfl⟩ : syracuseStep 318336803 = 477505205) B477505205
theorem B134385551 : Blo 1699550 134385551 := bstep (se 1 (by rfl) ⟨100789163, by rfl⟩ : syracuseStep 134385551 = 201578327) B201578327
theorem B98021339 : Blo 1699550 98021339 := bstep (se 1 (by rfl) ⟨73516004, by rfl⟩ : syracuseStep 98021339 = 147032009) B147032009
theorem B1699951 : Blo 1699550 1699951 := bstep (se 1 (by rfl) ⟨1274963, by rfl⟩ : syracuseStep 1699951 = 2549927) B2549927
theorem B8614025 : Blo 1699550 8614025 := bstep (se 2 (by rfl) ⟨3230259, by rfl⟩ : syracuseStep 8614025 = 6460519) B6460519
theorem B5820599 : Blo 1699550 5820599 := bstep (se 1 (by rfl) ⟨4365449, by rfl⟩ : syracuseStep 5820599 = 8730899) B8730899
theorem B353341835 : Blo 1699550 353341835 := bstep (se 1 (by rfl) ⟨265006376, by rfl⟩ : syracuseStep 353341835 = 530012753) B530012753
theorem B27955691 : Blo 1699550 27955691 := bstep (se 1 (by rfl) ⟨20966768, by rfl⟩ : syracuseStep 27955691 = 41933537) B41933537
theorem B5820925 : Blo 1699550 5820925 := bstep (se 3 (by rfl) ⟨1091423, by rfl⟩ : syracuseStep 5820925 = 2182847) B2182847
theorem B5739119 : Blo 1699550 5739119 := bstep (se 1 (by rfl) ⟨4304339, by rfl⟩ : syracuseStep 5739119 = 8608679) B8608679
theorem B2454175 : Blo 1699550 2454175 := bstep (se 1 (by rfl) ⟨1840631, by rfl⟩ : syracuseStep 2454175 = 3681263) B3681263
theorem B15512255 : Blo 1699550 15512255 := bstep (se 1 (by rfl) ⟨11634191, by rfl⟩ : syracuseStep 15512255 = 23268383) B23268383
theorem B1700607 : Blo 1699550 1700607 := bstep (se 1 (by rfl) ⟨1275455, by rfl⟩ : syracuseStep 1700607 = 2550911) B2550911
theorem B1700955 : Blo 1699550 1700955 := bstep (se 1 (by rfl) ⟨1275716, by rfl⟩ : syracuseStep 1700955 = 2551433) B2551433
theorem B1700991 : Blo 1699550 1700991 := bstep (se 1 (by rfl) ⟨1275743, by rfl⟩ : syracuseStep 1700991 = 2551487) B2551487
theorem B41358599 : Blo 1699550 41358599 := bstep (se 1 (by rfl) ⟨31018949, by rfl⟩ : syracuseStep 41358599 = 62037899) B62037899
theorem B65386925 : Blo 1699550 65386925 := bstep (se 3 (by rfl) ⟨12260048, by rfl⟩ : syracuseStep 65386925 = 24520097) B24520097
theorem B5741171 : Blo 1699550 5741171 := bstep (se 1 (by rfl) ⟨4305878, by rfl⟩ : syracuseStep 5741171 = 8611757) B8611757
theorem B2153243 : Blo 1699550 2153243 := bstep (se 1 (by rfl) ⟨1614932, by rfl⟩ : syracuseStep 2153243 = 3229865) B3229865
theorem B7265335 : Blo 1699550 7265335 := bstep (se 1 (by rfl) ⟨5449001, by rfl⟩ : syracuseStep 7265335 = 10898003) B10898003
theorem B3227177 : Blo 1699550 3227177 := bstep (se 2 (by rfl) ⟨1210191, by rfl⟩ : syracuseStep 3227177 = 2420383) B2420383
theorem B32669405 : Blo 1699550 32669405 := bstep (se 3 (by rfl) ⟨6125513, by rfl⟩ : syracuseStep 32669405 = 12251027) B12251027
theorem B11796473 : Blo 1699550 11796473 := bstep (se 2 (by rfl) ⟨4423677, by rfl⟩ : syracuseStep 11796473 = 8847355) B8847355
theorem B5742683 : Blo 1699550 5742683 := bstep (se 1 (by rfl) ⟨4307012, by rfl⟩ : syracuseStep 5742683 = 8614025) B8614025
theorem B235561223 : Blo 1699550 235561223 := bstep (se 1 (by rfl) ⟨176670917, by rfl⟩ : syracuseStep 235561223 = 353341835) B353341835
theorem B18637127 : Blo 1699550 18637127 := bstep (se 1 (by rfl) ⟨13977845, by rfl⟩ : syracuseStep 18637127 = 27955691) B27955691
theorem B3826079 : Blo 1699550 3826079 := bstep (se 1 (by rfl) ⟨2869559, by rfl⟩ : syracuseStep 3826079 = 5739119) B5739119
theorem B149103341 : Blo 1699550 149103341 := bstep (se 3 (by rfl) ⟨27956876, by rfl⟩ : syracuseStep 149103341 = 55913753) B55913753
theorem B18384367 : Blo 1699550 18384367 := bstep (se 1 (by rfl) ⟨13788275, by rfl⟩ : syracuseStep 18384367 = 27576551) B27576551
theorem B43591283 : Blo 1699550 43591283 := bstep (se 1 (by rfl) ⟨32693462, by rfl⟩ : syracuseStep 43591283 = 65386925) B65386925
theorem B3827447 : Blo 1699550 3827447 := bstep (se 1 (by rfl) ⟨2870585, by rfl⟩ : syracuseStep 3827447 = 5741171) B5741171
theorem B2869303 : Blo 1699550 2869303 := bstep (se 1 (by rfl) ⟨2151977, by rfl⟩ : syracuseStep 2869303 = 4303955) B4303955
theorem B212224535 : Blo 1699550 212224535 := bstep (se 1 (by rfl) ⟨159168401, by rfl⟩ : syracuseStep 212224535 = 318336803) B318336803
theorem B89590367 : Blo 1699550 89590367 := bstep (se 1 (by rfl) ⟨67192775, by rfl⟩ : syracuseStep 89590367 = 134385551) B134385551
theorem B12913505 : Blo 1699550 12913505 := bstep (se 2 (by rfl) ⟨4842564, by rfl⟩ : syracuseStep 12913505 = 9685129) B9685129
theorem B2550887 : Blo 1699550 2550887 := bstep (se 1 (by rfl) ⟨1913165, by rfl⟩ : syracuseStep 2550887 = 3826331) B3826331
theorem B10341503 : Blo 1699550 10341503 := bstep (se 1 (by rfl) ⟨7756127, by rfl⟩ : syracuseStep 10341503 = 15512255) B15512255
theorem B2551103 : Blo 1699550 2551103 := bstep (se 1 (by rfl) ⟨1913327, by rfl⟩ : syracuseStep 2551103 = 3826655) B3826655
theorem B7761233 : Blo 1699550 7761233 := bstep (se 2 (by rfl) ⟨2910462, by rfl⟩ : syracuseStep 7761233 = 5820925) B5820925
theorem B3272233 : Blo 1699550 3272233 := bstep (se 2 (by rfl) ⟨1227087, by rfl⟩ : syracuseStep 3272233 = 2454175) B2454175
theorem B9687113 : Blo 1699550 9687113 := bstep (se 2 (by rfl) ⟨3632667, by rfl⟩ : syracuseStep 9687113 = 7265335) B7265335
theorem B1700091 : Blo 1699550 1700091 := bstep (se 1 (by rfl) ⟨1275068, by rfl⟩ : syracuseStep 1700091 = 2550137) B2550137
theorem B4305595 : Blo 1699550 4305595 := bstep (se 1 (by rfl) ⟨3229196, by rfl⟩ : syracuseStep 4305595 = 6458393) B6458393
theorem B20673263 : Blo 1699550 20673263 := bstep (se 1 (by rfl) ⟨15504947, by rfl⟩ : syracuseStep 20673263 = 31009895) B31009895
theorem B2151451 : Blo 1699550 2151451 := bstep (se 1 (by rfl) ⟨1613588, by rfl⟩ : syracuseStep 2151451 = 3227177) B3227177
theorem B21779603 : Blo 1699550 21779603 := bstep (se 1 (by rfl) ⟨16334702, by rfl⟩ : syracuseStep 21779603 = 32669405) B32669405
theorem B1701023 : Blo 1699550 1701023 := bstep (se 1 (by rfl) ⟨1275767, by rfl⟩ : syracuseStep 1701023 = 2551535) B2551535
theorem B7263695 : Blo 1699550 7263695 := bstep (se 1 (by rfl) ⟨5447771, by rfl⟩ : syracuseStep 7263695 = 10895543) B10895543
theorem B3880399 : Blo 1699550 3880399 := bstep (se 1 (by rfl) ⟨2910299, by rfl⟩ : syracuseStep 3880399 = 5820599) B5820599
theorem B27572399 : Blo 1699550 27572399 := bstep (se 1 (by rfl) ⟨20679299, by rfl⟩ : syracuseStep 27572399 = 41358599) B41358599
theorem B5741981 : Blo 1699550 5741981 := bstep (se 3 (by rfl) ⟨1076621, by rfl⟩ : syracuseStep 5741981 = 2153243) B2153243
theorem B65347559 : Blo 1699550 65347559 := bstep (se 1 (by rfl) ⟨49010669, by rfl⟩ : syracuseStep 65347559 = 98021339) B98021339
theorem B31457261 : Blo 1699550 31457261 := bstep (se 3 (by rfl) ⟨5898236, by rfl⟩ : syracuseStep 31457261 = 11796473) B11796473
theorem B3825737 : Blo 1699550 3825737 := bstep (se 2 (by rfl) ⟨1434651, by rfl⟩ : syracuseStep 3825737 = 2869303) B2869303
theorem B99402227 : Blo 1699550 99402227 := bstep (se 1 (by rfl) ⟨74551670, by rfl⟩ : syracuseStep 99402227 = 149103341) B149103341
theorem B628163261 : Blo 1699550 628163261 := bstep (se 3 (by rfl) ⟨117780611, by rfl⟩ : syracuseStep 628163261 = 235561223) B235561223
theorem B4842463 : Blo 1699550 4842463 := bstep (se 1 (by rfl) ⟨3631847, by rfl⟩ : syracuseStep 4842463 = 7263695) B7263695
theorem B2868601 : Blo 1699550 2868601 := bstep (se 2 (by rfl) ⟨1075725, by rfl⟩ : syracuseStep 2868601 = 2151451) B2151451
theorem B24512489 : Blo 1699550 24512489 := bstep (se 2 (by rfl) ⟨9192183, by rfl⟩ : syracuseStep 24512489 = 18384367) B18384367
theorem B3827987 : Blo 1699550 3827987 := bstep (se 1 (by rfl) ⟨2870990, by rfl⟩ : syracuseStep 3827987 = 5741981) B5741981
theorem B6458075 : Blo 1699550 6458075 := bstep (se 1 (by rfl) ⟨4843556, by rfl⟩ : syracuseStep 6458075 = 9687113) B9687113
theorem B3828455 : Blo 1699550 3828455 := bstep (se 1 (by rfl) ⟨2871341, by rfl⟩ : syracuseStep 3828455 = 5742683) B5742683
theorem B2550719 : Blo 1699550 2550719 := bstep (se 1 (by rfl) ⟨1913039, by rfl⟩ : syracuseStep 2550719 = 3826079) B3826079
theorem B14519735 : Blo 1699550 14519735 := bstep (se 1 (by rfl) ⟨10889801, by rfl⟩ : syracuseStep 14519735 = 21779603) B21779603
theorem B29060855 : Blo 1699550 29060855 := bstep (se 1 (by rfl) ⟨21795641, by rfl⟩ : syracuseStep 29060855 = 43591283) B43591283
theorem B2551631 : Blo 1699550 2551631 := bstep (se 1 (by rfl) ⟨1913723, by rfl⟩ : syracuseStep 2551631 = 3827447) B3827447
theorem B5173865 : Blo 1699550 5173865 := bstep (se 2 (by rfl) ⟨1940199, by rfl⟩ : syracuseStep 5173865 = 3880399) B3880399
theorem B55128701 : Blo 1699550 55128701 := bstep (se 3 (by rfl) ⟨10336631, by rfl⟩ : syracuseStep 55128701 = 20673263) B20673263
theorem B4362977 : Blo 1699550 4362977 := bstep (se 2 (by rfl) ⟨1636116, by rfl⟩ : syracuseStep 4362977 = 3272233) B3272233
theorem B1700591 : Blo 1699550 1700591 := bstep (se 1 (by rfl) ⟨1275443, by rfl⟩ : syracuseStep 1700591 = 2550887) B2550887
theorem B6894335 : Blo 1699550 6894335 := bstep (se 1 (by rfl) ⟨5170751, by rfl⟩ : syracuseStep 6894335 = 10341503) B10341503
theorem B1700735 : Blo 1699550 1700735 := bstep (se 1 (by rfl) ⟨1275551, by rfl⟩ : syracuseStep 1700735 = 2551103) B2551103
theorem B5174155 : Blo 1699550 5174155 := bstep (se 1 (by rfl) ⟨3880616, by rfl⟩ : syracuseStep 5174155 = 7761233) B7761233
theorem B12424751 : Blo 1699550 12424751 := bstep (se 1 (by rfl) ⟨9318563, by rfl⟩ : syracuseStep 12424751 = 18637127) B18637127
theorem B5740793 : Blo 1699550 5740793 := bstep (se 2 (by rfl) ⟨2152797, by rfl⟩ : syracuseStep 5740793 = 4305595) B4305595
theorem B18381599 : Blo 1699550 18381599 := bstep (se 1 (by rfl) ⟨13786199, by rfl⟩ : syracuseStep 18381599 = 27572399) B27572399
theorem B141483023 : Blo 1699550 141483023 := bstep (se 1 (by rfl) ⟨106112267, by rfl⟩ : syracuseStep 141483023 = 212224535) B212224535
theorem B59726911 : Blo 1699550 59726911 := bstep (se 1 (by rfl) ⟨44795183, by rfl⟩ : syracuseStep 59726911 = 89590367) B89590367
theorem B8609003 : Blo 1699550 8609003 := bstep (se 1 (by rfl) ⟨6456752, by rfl⟩ : syracuseStep 8609003 = 12913505) B12913505
theorem B83886029 : Blo 1699550 83886029 := bstep (se 3 (by rfl) ⟨15728630, by rfl⟩ : syracuseStep 83886029 = 31457261) B31457261
theorem B43565039 : Blo 1699550 43565039 := bstep (se 1 (by rfl) ⟨32673779, by rfl⟩ : syracuseStep 43565039 = 65347559) B65347559
theorem B3449243 : Blo 1699550 3449243 := bstep (se 1 (by rfl) ⟨2586932, by rfl⟩ : syracuseStep 3449243 = 5173865) B5173865
theorem B418775507 : Blo 1699550 418775507 := bstep (se 1 (by rfl) ⟨314081630, by rfl⟩ : syracuseStep 418775507 = 628163261) B628163261
theorem B2908651 : Blo 1699550 2908651 := bstep (se 1 (by rfl) ⟨2181488, by rfl⟩ : syracuseStep 2908651 = 4362977) B4362977
theorem B4596223 : Blo 1699550 4596223 := bstep (se 1 (by rfl) ⟨3447167, by rfl⟩ : syracuseStep 4596223 = 6894335) B6894335
theorem B8283167 : Blo 1699550 8283167 := bstep (se 1 (by rfl) ⟨6212375, by rfl⟩ : syracuseStep 8283167 = 12424751) B12424751
theorem B6898873 : Blo 1699550 6898873 := bstep (se 2 (by rfl) ⟨2587077, by rfl⟩ : syracuseStep 6898873 = 5174155) B5174155
theorem B6456617 : Blo 1699550 6456617 := bstep (se 2 (by rfl) ⟨2421231, by rfl⟩ : syracuseStep 6456617 = 4842463) B4842463
theorem B79635881 : Blo 1699550 79635881 := bstep (se 2 (by rfl) ⟨29863455, by rfl⟩ : syracuseStep 79635881 = 59726911) B59726911
theorem B3827195 : Blo 1699550 3827195 := bstep (se 1 (by rfl) ⟨2870396, by rfl⟩ : syracuseStep 3827195 = 5740793) B5740793
theorem B29043359 : Blo 1699550 29043359 := bstep (se 1 (by rfl) ⟨21782519, by rfl⟩ : syracuseStep 29043359 = 43565039) B43565039
theorem B2550491 : Blo 1699550 2550491 := bstep (se 1 (by rfl) ⟨1912868, by rfl⟩ : syracuseStep 2550491 = 3825737) B3825737
theorem B66268151 : Blo 1699550 66268151 := bstep (se 1 (by rfl) ⟨49701113, by rfl⟩ : syracuseStep 66268151 = 99402227) B99402227
theorem B36752467 : Blo 1699550 36752467 := bstep (se 1 (by rfl) ⟨27564350, by rfl⟩ : syracuseStep 36752467 = 55128701) B55128701
theorem B2551991 : Blo 1699550 2551991 := bstep (se 1 (by rfl) ⟨1913993, by rfl⟩ : syracuseStep 2551991 = 3827987) B3827987
theorem B4305383 : Blo 1699550 4305383 := bstep (se 1 (by rfl) ⟨3229037, by rfl⟩ : syracuseStep 4305383 = 6458075) B6458075
theorem B2552303 : Blo 1699550 2552303 := bstep (se 1 (by rfl) ⟨1914227, by rfl⟩ : syracuseStep 2552303 = 3828455) B3828455
theorem B1700479 : Blo 1699550 1700479 := bstep (se 1 (by rfl) ⟨1275359, by rfl⟩ : syracuseStep 1700479 = 2550719) B2550719
theorem B5739335 : Blo 1699550 5739335 := bstep (se 1 (by rfl) ⟨4304501, by rfl⟩ : syracuseStep 5739335 = 8609003) B8609003
theorem B9679823 : Blo 1699550 9679823 := bstep (se 1 (by rfl) ⟨7259867, by rfl⟩ : syracuseStep 9679823 = 14519735) B14519735
theorem B1701087 : Blo 1699550 1701087 := bstep (se 1 (by rfl) ⟨1275815, by rfl⟩ : syracuseStep 1701087 = 2551631) B2551631
theorem B55924019 : Blo 1699550 55924019 := bstep (se 1 (by rfl) ⟨41943014, by rfl⟩ : syracuseStep 55924019 = 83886029) B83886029
theorem B16341659 : Blo 1699550 16341659 := bstep (se 1 (by rfl) ⟨12256244, by rfl⟩ : syracuseStep 16341659 = 24512489) B24512489
theorem B3824801 : Blo 1699550 3824801 := bstep (se 2 (by rfl) ⟨1434300, by rfl⟩ : syracuseStep 3824801 = 2868601) B2868601
theorem B12254399 : Blo 1699550 12254399 := bstep (se 1 (by rfl) ⟨9190799, by rfl⟩ : syracuseStep 12254399 = 18381599) B18381599
theorem B94322015 : Blo 1699550 94322015 := bstep (se 1 (by rfl) ⟨70741511, by rfl⟩ : syracuseStep 94322015 = 141483023) B141483023
theorem B19373903 : Blo 1699550 19373903 := bstep (se 1 (by rfl) ⟨14530427, by rfl⟩ : syracuseStep 19373903 = 29060855) B29060855
theorem B279183671 : Blo 1699550 279183671 := bstep (se 1 (by rfl) ⟨209387753, by rfl⟩ : syracuseStep 279183671 = 418775507) B418775507
theorem B3826223 : Blo 1699550 3826223 := bstep (se 1 (by rfl) ⟨2869667, by rfl⟩ : syracuseStep 3826223 = 5739335) B5739335
theorem B6128297 : Blo 1699550 6128297 := bstep (se 2 (by rfl) ⟨2298111, by rfl⟩ : syracuseStep 6128297 = 4596223) B4596223
theorem B5522111 : Blo 1699550 5522111 := bstep (se 1 (by rfl) ⟨4141583, by rfl⟩ : syracuseStep 5522111 = 8283167) B8283167
theorem B37282679 : Blo 1699550 37282679 := bstep (se 1 (by rfl) ⟨27962009, by rfl⟩ : syracuseStep 37282679 = 55924019) B55924019
theorem B2549867 : Blo 1699550 2549867 := bstep (se 1 (by rfl) ⟨1912400, by rfl⟩ : syracuseStep 2549867 = 3824801) B3824801
theorem B8169599 : Blo 1699550 8169599 := bstep (se 1 (by rfl) ⟨6127199, by rfl⟩ : syracuseStep 8169599 = 12254399) B12254399
theorem B2870255 : Blo 1699550 2870255 := bstep (se 1 (by rfl) ⟨2152691, by rfl⟩ : syracuseStep 2870255 = 4305383) B4305383
theorem B3878201 : Blo 1699550 3878201 := bstep (se 2 (by rfl) ⟨1454325, by rfl⟩ : syracuseStep 3878201 = 2908651) B2908651
theorem B4304411 : Blo 1699550 4304411 := bstep (se 1 (by rfl) ⟨3228308, by rfl⟩ : syracuseStep 4304411 = 6456617) B6456617
theorem B2551463 : Blo 1699550 2551463 := bstep (se 1 (by rfl) ⟨1913597, by rfl⟩ : syracuseStep 2551463 = 3827195) B3827195
theorem B19362239 : Blo 1699550 19362239 := bstep (se 1 (by rfl) ⟨14521679, by rfl⟩ : syracuseStep 19362239 = 29043359) B29043359
theorem B1700327 : Blo 1699550 1700327 := bstep (se 1 (by rfl) ⟨1275245, by rfl⟩ : syracuseStep 1700327 = 2550491) B2550491
theorem B12915935 : Blo 1699550 12915935 := bstep (se 1 (by rfl) ⟨9686951, by rfl⟩ : syracuseStep 12915935 = 19373903) B19373903
theorem B1701327 : Blo 1699550 1701327 := bstep (se 1 (by rfl) ⟨1275995, by rfl⟩ : syracuseStep 1701327 = 2551991) B2551991
theorem B1701535 : Blo 1699550 1701535 := bstep (se 1 (by rfl) ⟨1276151, by rfl⟩ : syracuseStep 1701535 = 2552303) B2552303
theorem B6453215 : Blo 1699550 6453215 := bstep (se 1 (by rfl) ⟨4839911, by rfl⟩ : syracuseStep 6453215 = 9679823) B9679823
theorem B53090587 : Blo 1699550 53090587 := bstep (se 1 (by rfl) ⟨39817940, by rfl⟩ : syracuseStep 53090587 = 79635881) B79635881
theorem B9197981 : Blo 1699550 9197981 := bstep (se 3 (by rfl) ⟨1724621, by rfl⟩ : syracuseStep 9197981 = 3449243) B3449243
theorem B49003289 : Blo 1699550 49003289 := bstep (se 2 (by rfl) ⟨18376233, by rfl⟩ : syracuseStep 49003289 = 36752467) B36752467
theorem B9198497 : Blo 1699550 9198497 := bstep (se 2 (by rfl) ⟨3449436, by rfl⟩ : syracuseStep 9198497 = 6898873) B6898873
theorem B10894439 : Blo 1699550 10894439 := bstep (se 1 (by rfl) ⟨8170829, by rfl⟩ : syracuseStep 10894439 = 16341659) B16341659
theorem B44178767 : Blo 1699550 44178767 := bstep (se 1 (by rfl) ⟨33134075, by rfl⟩ : syracuseStep 44178767 = 66268151) B66268151
theorem B62881343 : Blo 1699550 62881343 := bstep (se 1 (by rfl) ⟨47161007, by rfl⟩ : syracuseStep 62881343 = 94322015) B94322015
theorem B186122447 : Blo 1699550 186122447 := bstep (se 1 (by rfl) ⟨139591835, by rfl⟩ : syracuseStep 186122447 = 279183671) B279183671
theorem B70787449 : Blo 1699550 70787449 := bstep (se 2 (by rfl) ⟨26545293, by rfl⟩ : syracuseStep 70787449 = 53090587) B53090587
theorem B24855119 : Blo 1699550 24855119 := bstep (se 1 (by rfl) ⟨18641339, by rfl⟩ : syracuseStep 24855119 = 37282679) B37282679
theorem B8610623 : Blo 1699550 8610623 := bstep (se 1 (by rfl) ⟨6457967, by rfl⟩ : syracuseStep 8610623 = 12915935) B12915935
theorem B4302143 : Blo 1699550 4302143 := bstep (se 1 (by rfl) ⟨3226607, by rfl⟩ : syracuseStep 4302143 = 6453215) B6453215
theorem B29452511 : Blo 1699550 29452511 := bstep (se 1 (by rfl) ⟨22089383, by rfl⟩ : syracuseStep 29452511 = 44178767) B44178767
theorem B2869607 : Blo 1699550 2869607 := bstep (se 1 (by rfl) ⟨2152205, by rfl⟩ : syracuseStep 2869607 = 4304411) B4304411
theorem B41920895 : Blo 1699550 41920895 := bstep (se 1 (by rfl) ⟨31440671, by rfl⟩ : syracuseStep 41920895 = 62881343) B62881343
theorem B21785597 : Blo 1699550 21785597 := bstep (se 3 (by rfl) ⟨4084799, by rfl⟩ : syracuseStep 21785597 = 8169599) B8169599
theorem B2550815 : Blo 1699550 2550815 := bstep (se 1 (by rfl) ⟨1913111, by rfl⟩ : syracuseStep 2550815 = 3826223) B3826223
theorem B3681407 : Blo 1699550 3681407 := bstep (se 1 (by rfl) ⟨2761055, by rfl⟩ : syracuseStep 3681407 = 5522111) B5522111
theorem B1699911 : Blo 1699550 1699911 := bstep (se 1 (by rfl) ⟨1274933, by rfl⟩ : syracuseStep 1699911 = 2549867) B2549867
theorem B6131987 : Blo 1699550 6131987 := bstep (se 1 (by rfl) ⟨4598990, by rfl⟩ : syracuseStep 6131987 = 9197981) B9197981
theorem B6132331 : Blo 1699550 6132331 := bstep (se 1 (by rfl) ⟨4599248, by rfl⟩ : syracuseStep 6132331 = 9198497) B9198497
theorem B1913503 : Blo 1699550 1913503 := bstep (se 1 (by rfl) ⟨1435127, by rfl⟩ : syracuseStep 1913503 = 2870255) B2870255
theorem B7262959 : Blo 1699550 7262959 := bstep (se 1 (by rfl) ⟨5447219, by rfl⟩ : syracuseStep 7262959 = 10894439) B10894439
theorem B2585467 : Blo 1699550 2585467 := bstep (se 1 (by rfl) ⟨1939100, by rfl⟩ : syracuseStep 2585467 = 3878201) B3878201
theorem B1700975 : Blo 1699550 1700975 := bstep (se 1 (by rfl) ⟨1275731, by rfl⟩ : syracuseStep 1700975 = 2551463) B2551463
theorem B12908159 : Blo 1699550 12908159 := bstep (se 1 (by rfl) ⟨9681119, by rfl⟩ : syracuseStep 12908159 = 19362239) B19362239
theorem B4085531 : Blo 1699550 4085531 := bstep (se 1 (by rfl) ⟨3064148, by rfl⟩ : syracuseStep 4085531 = 6128297) B6128297
theorem B32668859 : Blo 1699550 32668859 := bstep (se 1 (by rfl) ⟨24501644, by rfl⟩ : syracuseStep 32668859 = 49003289) B49003289
theorem B4087991 : Blo 1699550 4087991 := bstep (se 1 (by rfl) ⟨3065993, by rfl⟩ : syracuseStep 4087991 = 6131987) B6131987
theorem B2868095 : Blo 1699550 2868095 := bstep (se 1 (by rfl) ⟨2151071, by rfl⟩ : syracuseStep 2868095 = 4302143) B4302143
theorem B9683945 : Blo 1699550 9683945 := bstep (se 2 (by rfl) ⟨3631479, by rfl⟩ : syracuseStep 9683945 = 7262959) B7262959
theorem B9817085 : Blo 1699550 9817085 := bstep (se 3 (by rfl) ⟨1840703, by rfl⟩ : syracuseStep 9817085 = 3681407) B3681407
theorem B32705765 : Blo 1699550 32705765 := bstep (se 4 (by rfl) ⟨3066165, by rfl⟩ : syracuseStep 32705765 = 6132331) B6132331
theorem B2551337 : Blo 1699550 2551337 := bstep (se 2 (by rfl) ⟨956751, by rfl⟩ : syracuseStep 2551337 = 1913503) B1913503
theorem B8605439 : Blo 1699550 8605439 := bstep (se 1 (by rfl) ⟨6454079, by rfl⟩ : syracuseStep 8605439 = 12908159) B12908159
theorem B2723687 : Blo 1699550 2723687 := bstep (se 1 (by rfl) ⟨2042765, by rfl⟩ : syracuseStep 2723687 = 4085531) B4085531
theorem B1913071 : Blo 1699550 1913071 := bstep (se 1 (by rfl) ⟨1434803, by rfl⟩ : syracuseStep 1913071 = 2869607) B2869607
theorem B27947263 : Blo 1699550 27947263 := bstep (se 1 (by rfl) ⟨20960447, by rfl⟩ : syracuseStep 27947263 = 41920895) B41920895
theorem B377533061 : Blo 1699550 377533061 := bstep (se 4 (by rfl) ⟨35393724, by rfl⟩ : syracuseStep 377533061 = 70787449) B70787449
theorem B1700543 : Blo 1699550 1700543 := bstep (se 1 (by rfl) ⟨1275407, by rfl⟩ : syracuseStep 1700543 = 2550815) B2550815
theorem B21779239 : Blo 1699550 21779239 := bstep (se 1 (by rfl) ⟨16334429, by rfl⟩ : syracuseStep 21779239 = 32668859) B32668859
theorem B124081631 : Blo 1699550 124081631 := bstep (se 1 (by rfl) ⟨93061223, by rfl⟩ : syracuseStep 124081631 = 186122447) B186122447
theorem B16570079 : Blo 1699550 16570079 := bstep (se 1 (by rfl) ⟨12427559, by rfl⟩ : syracuseStep 16570079 = 24855119) B24855119
theorem B5740415 : Blo 1699550 5740415 := bstep (se 1 (by rfl) ⟨4305311, by rfl⟩ : syracuseStep 5740415 = 8610623) B8610623
theorem B3447289 : Blo 1699550 3447289 := bstep (se 2 (by rfl) ⟨1292733, by rfl⟩ : syracuseStep 3447289 = 2585467) B2585467
theorem B19635007 : Blo 1699550 19635007 := bstep (se 1 (by rfl) ⟨14726255, by rfl⟩ : syracuseStep 19635007 = 29452511) B29452511
theorem B14523731 : Blo 1699550 14523731 := bstep (se 1 (by rfl) ⟨10892798, by rfl⟩ : syracuseStep 14523731 = 21785597) B21785597
theorem B6455963 : Blo 1699550 6455963 := bstep (se 1 (by rfl) ⟨4841972, by rfl⟩ : syracuseStep 6455963 = 9683945) B9683945
theorem B3826943 : Blo 1699550 3826943 := bstep (se 1 (by rfl) ⟨2870207, by rfl⟩ : syracuseStep 3826943 = 5740415) B5740415
theorem B5736959 : Blo 1699550 5736959 := bstep (se 1 (by rfl) ⟨4302719, by rfl⟩ : syracuseStep 5736959 = 8605439) B8605439
theorem B18385541 : Blo 1699550 18385541 := bstep (se 4 (by rfl) ⟨1723644, by rfl⟩ : syracuseStep 18385541 = 3447289) B3447289
theorem B2550761 : Blo 1699550 2550761 := bstep (se 2 (by rfl) ⟨956535, by rfl⟩ : syracuseStep 2550761 = 1913071) B1913071
theorem B1912063 : Blo 1699550 1912063 := bstep (se 1 (by rfl) ⟨1434047, by rfl⟩ : syracuseStep 1912063 = 2868095) B2868095
theorem B11046719 : Blo 1699550 11046719 := bstep (se 1 (by rfl) ⟨8285039, by rfl⟩ : syracuseStep 11046719 = 16570079) B16570079
theorem B21803843 : Blo 1699550 21803843 := bstep (se 1 (by rfl) ⟨16352882, by rfl⟩ : syracuseStep 21803843 = 32705765) B32705765
theorem B1700891 : Blo 1699550 1700891 := bstep (se 1 (by rfl) ⟨1275668, by rfl⟩ : syracuseStep 1700891 = 2551337) B2551337
theorem B1815791 : Blo 1699550 1815791 := bstep (se 1 (by rfl) ⟨1361843, by rfl⟩ : syracuseStep 1815791 = 2723687) B2723687
theorem B2725327 : Blo 1699550 2725327 := bstep (se 1 (by rfl) ⟨2043995, by rfl⟩ : syracuseStep 2725327 = 4087991) B4087991
theorem B37263017 : Blo 1699550 37263017 := bstep (se 2 (by rfl) ⟨13973631, by rfl⟩ : syracuseStep 37263017 = 27947263) B27947263
theorem B251688707 : Blo 1699550 251688707 := bstep (se 1 (by rfl) ⟨188766530, by rfl⟩ : syracuseStep 251688707 = 377533061) B377533061
theorem B82721087 : Blo 1699550 82721087 := bstep (se 1 (by rfl) ⟨62040815, by rfl⟩ : syracuseStep 82721087 = 124081631) B124081631
theorem B29038985 : Blo 1699550 29038985 := bstep (se 2 (by rfl) ⟨10889619, by rfl⟩ : syracuseStep 29038985 = 21779239) B21779239
theorem B26180009 : Blo 1699550 26180009 := bstep (se 2 (by rfl) ⟨9817503, by rfl⟩ : syracuseStep 26180009 = 19635007) B19635007
theorem B6544723 : Blo 1699550 6544723 := bstep (se 1 (by rfl) ⟨4908542, by rfl⟩ : syracuseStep 6544723 = 9817085) B9817085
theorem B9682487 : Blo 1699550 9682487 := bstep (se 1 (by rfl) ⟨7261865, by rfl⟩ : syracuseStep 9682487 = 14523731) B14523731
theorem B4842109 : Blo 1699550 4842109 := bstep (se 3 (by rfl) ⟨907895, by rfl⟩ : syracuseStep 4842109 = 1815791) B1815791
theorem B19359323 : Blo 1699550 19359323 := bstep (se 1 (by rfl) ⟨14519492, by rfl⟩ : syracuseStep 19359323 = 29038985) B29038985
theorem B2549417 : Blo 1699550 2549417 := bstep (se 2 (by rfl) ⟨956031, by rfl⟩ : syracuseStep 2549417 = 1912063) B1912063
theorem B12257027 : Blo 1699550 12257027 := bstep (se 1 (by rfl) ⟨9192770, by rfl⟩ : syracuseStep 12257027 = 18385541) B18385541
theorem B8726297 : Blo 1699550 8726297 := bstep (se 2 (by rfl) ⟨3272361, by rfl⟩ : syracuseStep 8726297 = 6544723) B6544723
theorem B4303975 : Blo 1699550 4303975 := bstep (se 1 (by rfl) ⟨3227981, by rfl⟩ : syracuseStep 4303975 = 6455963) B6455963
theorem B14535895 : Blo 1699550 14535895 := bstep (se 1 (by rfl) ⟨10901921, by rfl⟩ : syracuseStep 14535895 = 21803843) B21803843
theorem B2551295 : Blo 1699550 2551295 := bstep (se 1 (by rfl) ⟨1913471, by rfl⟩ : syracuseStep 2551295 = 3826943) B3826943
theorem B24842011 : Blo 1699550 24842011 := bstep (se 1 (by rfl) ⟨18631508, by rfl⟩ : syracuseStep 24842011 = 37263017) B37263017
theorem B167792471 : Blo 1699550 167792471 := bstep (se 1 (by rfl) ⟨125844353, by rfl⟩ : syracuseStep 167792471 = 251688707) B251688707
theorem B17453339 : Blo 1699550 17453339 := bstep (se 1 (by rfl) ⟨13090004, by rfl⟩ : syracuseStep 17453339 = 26180009) B26180009
theorem B3633769 : Blo 1699550 3633769 := bstep (se 2 (by rfl) ⟨1362663, by rfl⟩ : syracuseStep 3633769 = 2725327) B2725327
theorem B1700507 : Blo 1699550 1700507 := bstep (se 1 (by rfl) ⟨1275380, by rfl⟩ : syracuseStep 1700507 = 2550761) B2550761
theorem B55147391 : Blo 1699550 55147391 := bstep (se 1 (by rfl) ⟨41360543, by rfl⟩ : syracuseStep 55147391 = 82721087) B82721087
theorem B3824639 : Blo 1699550 3824639 := bstep (se 1 (by rfl) ⟨2868479, by rfl⟩ : syracuseStep 3824639 = 5736959) B5736959
theorem B6454991 : Blo 1699550 6454991 := bstep (se 1 (by rfl) ⟨4841243, by rfl⟩ : syracuseStep 6454991 = 9682487) B9682487
theorem B7364479 : Blo 1699550 7364479 := bstep (se 1 (by rfl) ⟨5523359, by rfl⟩ : syracuseStep 7364479 = 11046719) B11046719
theorem B6456145 : Blo 1699550 6456145 := bstep (se 2 (by rfl) ⟨2421054, by rfl⟩ : syracuseStep 6456145 = 4842109) B4842109
theorem B2549759 : Blo 1699550 2549759 := bstep (se 1 (by rfl) ⟨1912319, by rfl⟩ : syracuseStep 2549759 = 3824639) B3824639
theorem B33122681 : Blo 1699550 33122681 := bstep (se 2 (by rfl) ⟨12421005, by rfl⟩ : syracuseStep 33122681 = 24842011) B24842011
theorem B4303327 : Blo 1699550 4303327 := bstep (se 1 (by rfl) ⟨3227495, by rfl⟩ : syracuseStep 4303327 = 6454991) B6454991
theorem B11635559 : Blo 1699550 11635559 := bstep (se 1 (by rfl) ⟨8726669, by rfl⟩ : syracuseStep 11635559 = 17453339) B17453339
theorem B4845025 : Blo 1699550 4845025 := bstep (se 2 (by rfl) ⟨1816884, by rfl⟩ : syracuseStep 4845025 = 3633769) B3633769
theorem B12906215 : Blo 1699550 12906215 := bstep (se 1 (by rfl) ⟨9679661, by rfl⟩ : syracuseStep 12906215 = 19359323) B19359323
theorem B1699611 : Blo 1699550 1699611 := bstep (se 1 (by rfl) ⟨1274708, by rfl⟩ : syracuseStep 1699611 = 2549417) B2549417
theorem B8171351 : Blo 1699550 8171351 := bstep (se 1 (by rfl) ⟨6128513, by rfl⟩ : syracuseStep 8171351 = 12257027) B12257027
theorem B5738633 : Blo 1699550 5738633 := bstep (se 2 (by rfl) ⟨2151987, by rfl⟩ : syracuseStep 5738633 = 4303975) B4303975
theorem B23270125 : Blo 1699550 23270125 := bstep (se 3 (by rfl) ⟨4363148, by rfl⟩ : syracuseStep 23270125 = 8726297) B8726297
theorem B1700863 : Blo 1699550 1700863 := bstep (se 1 (by rfl) ⟨1275647, by rfl⟩ : syracuseStep 1700863 = 2551295) B2551295
theorem B9819305 : Blo 1699550 9819305 := bstep (se 2 (by rfl) ⟨3682239, by rfl⟩ : syracuseStep 9819305 = 7364479) B7364479
theorem B19381193 : Blo 1699550 19381193 := bstep (se 2 (by rfl) ⟨7267947, by rfl⟩ : syracuseStep 19381193 = 14535895) B14535895
theorem B36764927 : Blo 1699550 36764927 := bstep (se 1 (by rfl) ⟨27573695, by rfl⟩ : syracuseStep 36764927 = 55147391) B55147391
theorem B111861647 : Blo 1699550 111861647 := bstep (se 1 (by rfl) ⟨83896235, by rfl⟩ : syracuseStep 111861647 = 167792471) B167792471
theorem B3825755 : Blo 1699550 3825755 := bstep (se 1 (by rfl) ⟨2869316, by rfl⟩ : syracuseStep 3825755 = 5738633) B5738633
theorem B6546203 : Blo 1699550 6546203 := bstep (se 1 (by rfl) ⟨4909652, by rfl⟩ : syracuseStep 6546203 = 9819305) B9819305
theorem B12920795 : Blo 1699550 12920795 := bstep (se 1 (by rfl) ⟨9690596, by rfl⟩ : syracuseStep 12920795 = 19381193) B19381193
theorem B8604143 : Blo 1699550 8604143 := bstep (se 1 (by rfl) ⟨6453107, by rfl⟩ : syracuseStep 8604143 = 12906215) B12906215
theorem B74574431 : Blo 1699550 74574431 := bstep (se 1 (by rfl) ⟨55930823, by rfl⟩ : syracuseStep 74574431 = 111861647) B111861647
theorem B5737769 : Blo 1699550 5737769 := bstep (se 2 (by rfl) ⟨2151663, by rfl⟩ : syracuseStep 5737769 = 4303327) B4303327
theorem B31026833 : Blo 1699550 31026833 := bstep (se 2 (by rfl) ⟨11635062, by rfl⟩ : syracuseStep 31026833 = 23270125) B23270125
theorem B1699839 : Blo 1699550 1699839 := bstep (se 1 (by rfl) ⟨1274879, by rfl⟩ : syracuseStep 1699839 = 2549759) B2549759
theorem B22081787 : Blo 1699550 22081787 := bstep (se 1 (by rfl) ⟨16561340, by rfl⟩ : syracuseStep 22081787 = 33122681) B33122681
theorem B6460033 : Blo 1699550 6460033 := bstep (se 2 (by rfl) ⟨2422512, by rfl⟩ : syracuseStep 6460033 = 4845025) B4845025
theorem B8608193 : Blo 1699550 8608193 := bstep (se 2 (by rfl) ⟨3228072, by rfl⟩ : syracuseStep 8608193 = 6456145) B6456145
theorem B7757039 : Blo 1699550 7757039 := bstep (se 1 (by rfl) ⟨5817779, by rfl⟩ : syracuseStep 7757039 = 11635559) B11635559
theorem B24509951 : Blo 1699550 24509951 := bstep (se 1 (by rfl) ⟨18382463, by rfl⟩ : syracuseStep 24509951 = 36764927) B36764927
theorem B5447567 : Blo 1699550 5447567 := bstep (se 1 (by rfl) ⟨4085675, by rfl⟩ : syracuseStep 5447567 = 8171351) B8171351
theorem B14721191 : Blo 1699550 14721191 := bstep (se 1 (by rfl) ⟨11040893, by rfl⟩ : syracuseStep 14721191 = 22081787) B22081787
theorem B5736095 : Blo 1699550 5736095 := bstep (se 1 (by rfl) ⟨4302071, by rfl⟩ : syracuseStep 5736095 = 8604143) B8604143
theorem B5171359 : Blo 1699550 5171359 := bstep (se 1 (by rfl) ⟨3878519, by rfl⟩ : syracuseStep 5171359 = 7757039) B7757039
theorem B3631711 : Blo 1699550 3631711 := bstep (se 1 (by rfl) ⟨2723783, by rfl⟩ : syracuseStep 3631711 = 5447567) B5447567
theorem B2550503 : Blo 1699550 2550503 := bstep (se 1 (by rfl) ⟨1912877, by rfl⟩ : syracuseStep 2550503 = 3825755) B3825755
theorem B8613377 : Blo 1699550 8613377 := bstep (se 2 (by rfl) ⟨3230016, by rfl⟩ : syracuseStep 8613377 = 6460033) B6460033
theorem B8613863 : Blo 1699550 8613863 := bstep (se 1 (by rfl) ⟨6460397, by rfl⟩ : syracuseStep 8613863 = 12920795) B12920795
theorem B5738795 : Blo 1699550 5738795 := bstep (se 1 (by rfl) ⟨4304096, by rfl⟩ : syracuseStep 5738795 = 8608193) B8608193
theorem B16339967 : Blo 1699550 16339967 := bstep (se 1 (by rfl) ⟨12254975, by rfl⟩ : syracuseStep 16339967 = 24509951) B24509951
theorem B4364135 : Blo 1699550 4364135 := bstep (se 1 (by rfl) ⟨3273101, by rfl⟩ : syracuseStep 4364135 = 6546203) B6546203
theorem B49716287 : Blo 1699550 49716287 := bstep (se 1 (by rfl) ⟨37287215, by rfl⟩ : syracuseStep 49716287 = 74574431) B74574431
theorem B3825179 : Blo 1699550 3825179 := bstep (se 1 (by rfl) ⟨2868884, by rfl⟩ : syracuseStep 3825179 = 5737769) B5737769
theorem B20684555 : Blo 1699550 20684555 := bstep (se 1 (by rfl) ⟨15513416, by rfl⟩ : syracuseStep 20684555 = 31026833) B31026833
theorem B9814127 : Blo 1699550 9814127 := bstep (se 1 (by rfl) ⟨7360595, by rfl⟩ : syracuseStep 9814127 = 14721191) B14721191
theorem B3825863 : Blo 1699550 3825863 := bstep (se 1 (by rfl) ⟨2869397, by rfl⟩ : syracuseStep 3825863 = 5738795) B5738795
theorem B4842281 : Blo 1699550 4842281 := bstep (se 2 (by rfl) ⟨1815855, by rfl⟩ : syracuseStep 4842281 = 3631711) B3631711
theorem B2909423 : Blo 1699550 2909423 := bstep (se 1 (by rfl) ⟨2182067, by rfl⟩ : syracuseStep 2909423 = 4364135) B4364135
theorem B2550119 : Blo 1699550 2550119 := bstep (se 1 (by rfl) ⟨1912589, by rfl⟩ : syracuseStep 2550119 = 3825179) B3825179
theorem B13789703 : Blo 1699550 13789703 := bstep (se 1 (by rfl) ⟨10342277, by rfl⟩ : syracuseStep 13789703 = 20684555) B20684555
theorem B1700335 : Blo 1699550 1700335 := bstep (se 1 (by rfl) ⟨1275251, by rfl⟩ : syracuseStep 1700335 = 2550503) B2550503
theorem B6895145 : Blo 1699550 6895145 := bstep (se 2 (by rfl) ⟨2585679, by rfl⟩ : syracuseStep 6895145 = 5171359) B5171359
theorem B10893311 : Blo 1699550 10893311 := bstep (se 1 (by rfl) ⟨8169983, by rfl⟩ : syracuseStep 10893311 = 16339967) B16339967
theorem B3824063 : Blo 1699550 3824063 := bstep (se 1 (by rfl) ⟨2868047, by rfl⟩ : syracuseStep 3824063 = 5736095) B5736095
theorem B33144191 : Blo 1699550 33144191 := bstep (se 1 (by rfl) ⟨24858143, by rfl⟩ : syracuseStep 33144191 = 49716287) B49716287
theorem B5742251 : Blo 1699550 5742251 := bstep (se 1 (by rfl) ⟨4306688, by rfl⟩ : syracuseStep 5742251 = 8613377) B8613377
theorem B5742575 : Blo 1699550 5742575 := bstep (se 1 (by rfl) ⟨4306931, by rfl⟩ : syracuseStep 5742575 = 8613863) B8613863
theorem B3228187 : Blo 1699550 3228187 := bstep (se 1 (by rfl) ⟨2421140, by rfl⟩ : syracuseStep 3228187 = 4842281) B4842281
theorem B4596763 : Blo 1699550 4596763 := bstep (se 1 (by rfl) ⟨3447572, by rfl⟩ : syracuseStep 4596763 = 6895145) B6895145
theorem B2549375 : Blo 1699550 2549375 := bstep (se 1 (by rfl) ⟨1912031, by rfl⟩ : syracuseStep 2549375 = 3824063) B3824063
theorem B9193135 : Blo 1699550 9193135 := bstep (se 1 (by rfl) ⟨6894851, by rfl⟩ : syracuseStep 9193135 = 13789703) B13789703
theorem B22096127 : Blo 1699550 22096127 := bstep (se 1 (by rfl) ⟨16572095, by rfl⟩ : syracuseStep 22096127 = 33144191) B33144191
theorem B3828167 : Blo 1699550 3828167 := bstep (se 1 (by rfl) ⟨2871125, by rfl⟩ : syracuseStep 3828167 = 5742251) B5742251
theorem B3828383 : Blo 1699550 3828383 := bstep (se 1 (by rfl) ⟨2871287, by rfl⟩ : syracuseStep 3828383 = 5742575) B5742575
theorem B2550575 : Blo 1699550 2550575 := bstep (se 1 (by rfl) ⟨1912931, by rfl⟩ : syracuseStep 2550575 = 3825863) B3825863
theorem B7262207 : Blo 1699550 7262207 := bstep (se 1 (by rfl) ⟨5446655, by rfl⟩ : syracuseStep 7262207 = 10893311) B10893311
theorem B1700079 : Blo 1699550 1700079 := bstep (se 1 (by rfl) ⟨1275059, by rfl⟩ : syracuseStep 1700079 = 2550119) B2550119
theorem B1939615 : Blo 1699550 1939615 := bstep (se 1 (by rfl) ⟨1454711, by rfl⟩ : syracuseStep 1939615 = 2909423) B2909423
theorem B104684021 : Blo 1699550 104684021 := bstep (se 5 (by rfl) ⟨4907063, by rfl⟩ : syracuseStep 104684021 = 9814127) B9814127
theorem B6129017 : Blo 1699550 6129017 := bstep (se 2 (by rfl) ⟨2298381, by rfl⟩ : syracuseStep 6129017 = 4596763) B4596763
theorem B14730751 : Blo 1699550 14730751 := bstep (se 1 (by rfl) ⟨11048063, by rfl⟩ : syracuseStep 14730751 = 22096127) B22096127
theorem B69789347 : Blo 1699550 69789347 := bstep (se 1 (by rfl) ⟨52342010, by rfl⟩ : syracuseStep 69789347 = 104684021) B104684021
theorem B12257513 : Blo 1699550 12257513 := bstep (se 2 (by rfl) ⟨4596567, by rfl⟩ : syracuseStep 12257513 = 9193135) B9193135
theorem B4304249 : Blo 1699550 4304249 := bstep (se 2 (by rfl) ⟨1614093, by rfl⟩ : syracuseStep 4304249 = 3228187) B3228187
theorem B1699583 : Blo 1699550 1699583 := bstep (se 1 (by rfl) ⟨1274687, by rfl⟩ : syracuseStep 1699583 = 2549375) B2549375
theorem B2552111 : Blo 1699550 2552111 := bstep (se 1 (by rfl) ⟨1914083, by rfl⟩ : syracuseStep 2552111 = 3828167) B3828167
theorem B2552255 : Blo 1699550 2552255 := bstep (se 1 (by rfl) ⟨1914191, by rfl⟩ : syracuseStep 2552255 = 3828383) B3828383
theorem B1700383 : Blo 1699550 1700383 := bstep (se 1 (by rfl) ⟨1275287, by rfl⟩ : syracuseStep 1700383 = 2550575) B2550575
theorem B10344613 : Blo 1699550 10344613 := bstep (se 4 (by rfl) ⟨969807, by rfl⟩ : syracuseStep 10344613 = 1939615) B1939615
theorem B4841471 : Blo 1699550 4841471 := bstep (se 1 (by rfl) ⟨3631103, by rfl⟩ : syracuseStep 4841471 = 7262207) B7262207
theorem B2869499 : Blo 1699550 2869499 := bstep (se 1 (by rfl) ⟨2152124, by rfl⟩ : syracuseStep 2869499 = 4304249) B4304249
theorem B78564005 : Blo 1699550 78564005 := bstep (se 4 (by rfl) ⟨7365375, by rfl⟩ : syracuseStep 78564005 = 14730751) B14730751
theorem B46526231 : Blo 1699550 46526231 := bstep (se 1 (by rfl) ⟨34894673, by rfl⟩ : syracuseStep 46526231 = 69789347) B69789347
theorem B8171675 : Blo 1699550 8171675 := bstep (se 1 (by rfl) ⟨6128756, by rfl⟩ : syracuseStep 8171675 = 12257513) B12257513
theorem B1701407 : Blo 1699550 1701407 := bstep (se 1 (by rfl) ⟨1276055, by rfl⟩ : syracuseStep 1701407 = 2552111) B2552111
theorem B13792817 : Blo 1699550 13792817 := bstep (se 2 (by rfl) ⟨5172306, by rfl⟩ : syracuseStep 13792817 = 10344613) B10344613
theorem B1701503 : Blo 1699550 1701503 := bstep (se 1 (by rfl) ⟨1276127, by rfl⟩ : syracuseStep 1701503 = 2552255) B2552255
theorem B4086011 : Blo 1699550 4086011 := bstep (se 1 (by rfl) ⟨3064508, by rfl⟩ : syracuseStep 4086011 = 6129017) B6129017
theorem B12910589 : Blo 1699550 12910589 := bstep (se 3 (by rfl) ⟨2420735, by rfl⟩ : syracuseStep 12910589 = 4841471) B4841471
theorem B5447783 : Blo 1699550 5447783 := bstep (se 1 (by rfl) ⟨4085837, by rfl⟩ : syracuseStep 5447783 = 8171675) B8171675
theorem B10896029 : Blo 1699550 10896029 := bstep (se 3 (by rfl) ⟨2043005, by rfl⟩ : syracuseStep 10896029 = 4086011) B4086011
theorem B31017487 : Blo 1699550 31017487 := bstep (se 1 (by rfl) ⟨23263115, by rfl⟩ : syracuseStep 31017487 = 46526231) B46526231
theorem B9195211 : Blo 1699550 9195211 := bstep (se 1 (by rfl) ⟨6896408, by rfl⟩ : syracuseStep 9195211 = 13792817) B13792817
theorem B1912999 : Blo 1699550 1912999 := bstep (se 1 (by rfl) ⟨1434749, by rfl⟩ : syracuseStep 1912999 = 2869499) B2869499
theorem B52376003 : Blo 1699550 52376003 := bstep (se 1 (by rfl) ⟨39282002, by rfl⟩ : syracuseStep 52376003 = 78564005) B78564005
theorem B8607059 : Blo 1699550 8607059 := bstep (se 1 (by rfl) ⟨6455294, by rfl⟩ : syracuseStep 8607059 = 12910589) B12910589
theorem B2550665 : Blo 1699550 2550665 := bstep (se 2 (by rfl) ⟨956499, by rfl⟩ : syracuseStep 2550665 = 1912999) B1912999
theorem B14527421 : Blo 1699550 14527421 := bstep (se 3 (by rfl) ⟨2723891, by rfl⟩ : syracuseStep 14527421 = 5447783) B5447783
theorem B34917335 : Blo 1699550 34917335 := bstep (se 1 (by rfl) ⟨26188001, by rfl⟩ : syracuseStep 34917335 = 52376003) B52376003
theorem B41356649 : Blo 1699550 41356649 := bstep (se 2 (by rfl) ⟨15508743, by rfl⟩ : syracuseStep 41356649 = 31017487) B31017487
theorem B5738039 : Blo 1699550 5738039 := bstep (se 1 (by rfl) ⟨4303529, by rfl⟩ : syracuseStep 5738039 = 8607059) B8607059
theorem B12260281 : Blo 1699550 12260281 := bstep (se 2 (by rfl) ⟨4597605, by rfl⟩ : syracuseStep 12260281 = 9195211) B9195211
theorem B7264019 : Blo 1699550 7264019 := bstep (se 1 (by rfl) ⟨5448014, by rfl⟩ : syracuseStep 7264019 = 10896029) B10896029
theorem B4842679 : Blo 1699550 4842679 := bstep (se 1 (by rfl) ⟨3632009, by rfl⟩ : syracuseStep 4842679 = 7264019) B7264019
theorem B9684947 : Blo 1699550 9684947 := bstep (se 1 (by rfl) ⟨7263710, by rfl⟩ : syracuseStep 9684947 = 14527421) B14527421
theorem B16347041 : Blo 1699550 16347041 := bstep (se 2 (by rfl) ⟨6130140, by rfl⟩ : syracuseStep 16347041 = 12260281) B12260281
theorem B1700443 : Blo 1699550 1700443 := bstep (se 1 (by rfl) ⟨1275332, by rfl⟩ : syracuseStep 1700443 = 2550665) B2550665
theorem B23278223 : Blo 1699550 23278223 := bstep (se 1 (by rfl) ⟨17458667, by rfl⟩ : syracuseStep 23278223 = 34917335) B34917335
theorem B27571099 : Blo 1699550 27571099 := bstep (se 1 (by rfl) ⟨20678324, by rfl⟩ : syracuseStep 27571099 = 41356649) B41356649
theorem B3825359 : Blo 1699550 3825359 := bstep (se 1 (by rfl) ⟨2869019, by rfl⟩ : syracuseStep 3825359 = 5738039) B5738039
theorem B6456631 : Blo 1699550 6456631 := bstep (se 1 (by rfl) ⟨4842473, by rfl⟩ : syracuseStep 6456631 = 9684947) B9684947
theorem B6456905 : Blo 1699550 6456905 := bstep (se 2 (by rfl) ⟨2421339, by rfl⟩ : syracuseStep 6456905 = 4842679) B4842679
theorem B2550239 : Blo 1699550 2550239 := bstep (se 1 (by rfl) ⟨1912679, by rfl⟩ : syracuseStep 2550239 = 3825359) B3825359
theorem B10898027 : Blo 1699550 10898027 := bstep (se 1 (by rfl) ⟨8173520, by rfl⟩ : syracuseStep 10898027 = 16347041) B16347041
theorem B36761465 : Blo 1699550 36761465 := bstep (se 2 (by rfl) ⟨13785549, by rfl⟩ : syracuseStep 36761465 = 27571099) B27571099
theorem B62075261 : Blo 1699550 62075261 := bstep (se 3 (by rfl) ⟨11639111, by rfl⟩ : syracuseStep 62075261 = 23278223) B23278223
theorem B4304603 : Blo 1699550 4304603 := bstep (se 1 (by rfl) ⟨3228452, by rfl⟩ : syracuseStep 4304603 = 6456905) B6456905
theorem B1700159 : Blo 1699550 1700159 := bstep (se 1 (by rfl) ⟨1275119, by rfl⟩ : syracuseStep 1700159 = 2550239) B2550239
theorem B24507643 : Blo 1699550 24507643 := bstep (se 1 (by rfl) ⟨18380732, by rfl⟩ : syracuseStep 24507643 = 36761465) B36761465
theorem B165534029 : Blo 1699550 165534029 := bstep (se 3 (by rfl) ⟨31037630, by rfl⟩ : syracuseStep 165534029 = 62075261) B62075261
theorem B7265351 : Blo 1699550 7265351 := bstep (se 1 (by rfl) ⟨5449013, by rfl⟩ : syracuseStep 7265351 = 10898027) B10898027
theorem B8608841 : Blo 1699550 8608841 := bstep (se 2 (by rfl) ⟨3228315, by rfl⟩ : syracuseStep 8608841 = 6456631) B6456631
theorem B110356019 : Blo 1699550 110356019 := bstep (se 1 (by rfl) ⟨82767014, by rfl⟩ : syracuseStep 110356019 = 165534029) B165534029
theorem B4843567 : Blo 1699550 4843567 := bstep (se 1 (by rfl) ⟨3632675, by rfl⟩ : syracuseStep 4843567 = 7265351) B7265351
theorem B2869735 : Blo 1699550 2869735 := bstep (se 1 (by rfl) ⟨2152301, by rfl⟩ : syracuseStep 2869735 = 4304603) B4304603
theorem B5739227 : Blo 1699550 5739227 := bstep (se 1 (by rfl) ⟨4304420, by rfl⟩ : syracuseStep 5739227 = 8608841) B8608841
theorem B32676857 : Blo 1699550 32676857 := bstep (se 2 (by rfl) ⟨12253821, by rfl⟩ : syracuseStep 32676857 = 24507643) B24507643
theorem B3826151 : Blo 1699550 3826151 := bstep (se 1 (by rfl) ⟨2869613, by rfl⟩ : syracuseStep 3826151 = 5739227) B5739227
theorem B3826313 : Blo 1699550 3826313 := bstep (se 2 (by rfl) ⟨1434867, by rfl⟩ : syracuseStep 3826313 = 2869735) B2869735
theorem B21784571 : Blo 1699550 21784571 := bstep (se 1 (by rfl) ⟨16338428, by rfl⟩ : syracuseStep 21784571 = 32676857) B32676857
theorem B6458089 : Blo 1699550 6458089 := bstep (se 2 (by rfl) ⟨2421783, by rfl⟩ : syracuseStep 6458089 = 4843567) B4843567
theorem B73570679 : Blo 1699550 73570679 := bstep (se 1 (by rfl) ⟨55178009, by rfl⟩ : syracuseStep 73570679 = 110356019) B110356019
theorem B8610785 : Blo 1699550 8610785 := bstep (se 2 (by rfl) ⟨3229044, by rfl⟩ : syracuseStep 8610785 = 6458089) B6458089
theorem B49047119 : Blo 1699550 49047119 := bstep (se 1 (by rfl) ⟨36785339, by rfl⟩ : syracuseStep 49047119 = 73570679) B73570679
theorem B2550767 : Blo 1699550 2550767 := bstep (se 1 (by rfl) ⟨1913075, by rfl⟩ : syracuseStep 2550767 = 3826151) B3826151
theorem B2550875 : Blo 1699550 2550875 := bstep (se 1 (by rfl) ⟨1913156, by rfl⟩ : syracuseStep 2550875 = 3826313) B3826313
theorem B14523047 : Blo 1699550 14523047 := bstep (se 1 (by rfl) ⟨10892285, by rfl⟩ : syracuseStep 14523047 = 21784571) B21784571
theorem B32698079 : Blo 1699550 32698079 := bstep (se 1 (by rfl) ⟨24523559, by rfl⟩ : syracuseStep 32698079 = 49047119) B49047119
theorem B1700511 : Blo 1699550 1700511 := bstep (se 1 (by rfl) ⟨1275383, by rfl⟩ : syracuseStep 1700511 = 2550767) B2550767
theorem B1700583 : Blo 1699550 1700583 := bstep (se 1 (by rfl) ⟨1275437, by rfl⟩ : syracuseStep 1700583 = 2550875) B2550875
theorem B5740523 : Blo 1699550 5740523 := bstep (se 1 (by rfl) ⟨4305392, by rfl⟩ : syracuseStep 5740523 = 8610785) B8610785
theorem B9682031 : Blo 1699550 9682031 := bstep (se 1 (by rfl) ⟨7261523, by rfl⟩ : syracuseStep 9682031 = 14523047) B14523047
theorem B3827015 : Blo 1699550 3827015 := bstep (se 1 (by rfl) ⟨2870261, by rfl⟩ : syracuseStep 3827015 = 5740523) B5740523
theorem B6454687 : Blo 1699550 6454687 := bstep (se 1 (by rfl) ⟨4841015, by rfl⟩ : syracuseStep 6454687 = 9682031) B9682031
theorem B21798719 : Blo 1699550 21798719 := bstep (se 1 (by rfl) ⟨16349039, by rfl⟩ : syracuseStep 21798719 = 32698079) B32698079
theorem B2551343 : Blo 1699550 2551343 := bstep (se 1 (by rfl) ⟨1913507, by rfl⟩ : syracuseStep 2551343 = 3827015) B3827015
theorem B8606249 : Blo 1699550 8606249 := bstep (se 2 (by rfl) ⟨3227343, by rfl⟩ : syracuseStep 8606249 = 6454687) B6454687
theorem B14532479 : Blo 1699550 14532479 := bstep (se 1 (by rfl) ⟨10899359, by rfl⟩ : syracuseStep 14532479 = 21798719) B21798719
theorem B5737499 : Blo 1699550 5737499 := bstep (se 1 (by rfl) ⟨4303124, by rfl⟩ : syracuseStep 5737499 = 8606249) B8606249
theorem B1700895 : Blo 1699550 1700895 := bstep (se 1 (by rfl) ⟨1275671, by rfl⟩ : syracuseStep 1700895 = 2551343) B2551343
theorem B9688319 : Blo 1699550 9688319 := bstep (se 1 (by rfl) ⟨7266239, by rfl⟩ : syracuseStep 9688319 = 14532479) B14532479
theorem B6458879 : Blo 1699550 6458879 := bstep (se 1 (by rfl) ⟨4844159, by rfl⟩ : syracuseStep 6458879 = 9688319) B9688319
theorem B3824999 : Blo 1699550 3824999 := bstep (se 1 (by rfl) ⟨2868749, by rfl⟩ : syracuseStep 3824999 = 5737499) B5737499
theorem B2549999 : Blo 1699550 2549999 := bstep (se 1 (by rfl) ⟨1912499, by rfl⟩ : syracuseStep 2549999 = 3824999) B3824999
theorem B4305919 : Blo 1699550 4305919 := bstep (se 1 (by rfl) ⟨3229439, by rfl⟩ : syracuseStep 4305919 = 6458879) B6458879
theorem B1699999 : Blo 1699550 1699999 := bstep (se 1 (by rfl) ⟨1274999, by rfl⟩ : syracuseStep 1699999 = 2549999) B2549999
theorem B5741225 : Blo 1699550 5741225 := bstep (se 2 (by rfl) ⟨2152959, by rfl⟩ : syracuseStep 5741225 = 4305919) B4305919
theorem B3827483 : Blo 1699550 3827483 := bstep (se 1 (by rfl) ⟨2870612, by rfl⟩ : syracuseStep 3827483 = 5741225) B5741225
theorem B2551655 : Blo 1699550 2551655 := bstep (se 1 (by rfl) ⟨1913741, by rfl⟩ : syracuseStep 2551655 = 3827483) B3827483
theorem B1701103 : Blo 1699550 1701103 := bstep (se 1 (by rfl) ⟨1275827, by rfl⟩ : syracuseStep 1701103 = 2551655) B2551655

theorem C0 (j : ℕ) (h1 : 424887 ≤ j) (h2 : j ≤ 425386) : Blo 1699550 (4 * j + 3) := by
  interval_cases j
  · exact B1699551
  · exact B1699555
  · exact B1699559
  · exact B1699563
  · exact B1699567
  · exact B1699571
  · exact B1699575
  · exact B1699579
  · exact B1699583
  · exact B1699587
  · exact B1699591
  · exact B1699595
  · exact B1699599
  · exact B1699603
  · exact B1699607
  · exact B1699611
  · exact B1699615
  · exact B1699619
  · exact B1699623
  · exact B1699627
  · exact B1699631
  · exact B1699635
  · exact B1699639
  · exact B1699643
  · exact B1699647
  · exact B1699651
  · exact B1699655
  · exact B1699659
  · exact B1699663
  · exact B1699667
  · exact B1699671
  · exact B1699675
  · exact B1699679
  · exact B1699683
  · exact B1699687
  · exact B1699691
  · exact B1699695
  · exact B1699699
  · exact B1699703
  · exact B1699707
  · exact B1699711
  · exact B1699715
  · exact B1699719
  · exact B1699723
  · exact B1699727
  · exact B1699731
  · exact B1699735
  · exact B1699739
  · exact B1699743
  · exact B1699747
  · exact B1699751
  · exact B1699755
  · exact B1699759
  · exact B1699763
  · exact B1699767
  · exact B1699771
  · exact B1699775
  · exact B1699779
  · exact B1699783
  · exact B1699787
  · exact B1699791
  · exact B1699795
  · exact B1699799
  · exact B1699803
  · exact B1699807
  · exact B1699811
  · exact B1699815
  · exact B1699819
  · exact B1699823
  · exact B1699827
  · exact B1699831
  · exact B1699835
  · exact B1699839
  · exact B1699843
  · exact B1699847
  · exact B1699851
  · exact B1699855
  · exact B1699859
  · exact B1699863
  · exact B1699867
  · exact B1699871
  · exact B1699875
  · exact B1699879
  · exact B1699883
  · exact B1699887
  · exact B1699891
  · exact B1699895
  · exact B1699899
  · exact B1699903
  · exact B1699907
  · exact B1699911
  · exact B1699915
  · exact B1699919
  · exact B1699923
  · exact B1699927
  · exact B1699931
  · exact B1699935
  · exact B1699939
  · exact B1699943
  · exact B1699947
  · exact B1699951
  · exact B1699955
  · exact B1699959
  · exact B1699963
  · exact B1699967
  · exact B1699971
  · exact B1699975
  · exact B1699979
  · exact B1699983
  · exact B1699987
  · exact B1699991
  · exact B1699995
  · exact B1699999
  · exact B1700003
  · exact B1700007
  · exact B1700011
  · exact B1700015
  · exact B1700019
  · exact B1700023
  · exact B1700027
  · exact B1700031
  · exact B1700035
  · exact B1700039
  · exact B1700043
  · exact B1700047
  · exact B1700051
  · exact B1700055
  · exact B1700059
  · exact B1700063
  · exact B1700067
  · exact B1700071
  · exact B1700075
  · exact B1700079
  · exact B1700083
  · exact B1700087
  · exact B1700091
  · exact B1700095
  · exact B1700099
  · exact B1700103
  · exact B1700107
  · exact B1700111
  · exact B1700115
  · exact B1700119
  · exact B1700123
  · exact B1700127
  · exact B1700131
  · exact B1700135
  · exact B1700139
  · exact B1700143
  · exact B1700147
  · exact B1700151
  · exact B1700155
  · exact B1700159
  · exact B1700163
  · exact B1700167
  · exact B1700171
  · exact B1700175
  · exact B1700179
  · exact B1700183
  · exact B1700187
  · exact B1700191
  · exact B1700195
  · exact B1700199
  · exact B1700203
  · exact B1700207
  · exact B1700211
  · exact B1700215
  · exact B1700219
  · exact B1700223
  · exact B1700227
  · exact B1700231
  · exact B1700235
  · exact B1700239
  · exact B1700243
  · exact B1700247
  · exact B1700251
  · exact B1700255
  · exact B1700259
  · exact B1700263
  · exact B1700267
  · exact B1700271
  · exact B1700275
  · exact B1700279
  · exact B1700283
  · exact B1700287
  · exact B1700291
  · exact B1700295
  · exact B1700299
  · exact B1700303
  · exact B1700307
  · exact B1700311
  · exact B1700315
  · exact B1700319
  · exact B1700323
  · exact B1700327
  · exact B1700331
  · exact B1700335
  · exact B1700339
  · exact B1700343
  · exact B1700347
  · exact B1700351
  · exact B1700355
  · exact B1700359
  · exact B1700363
  · exact B1700367
  · exact B1700371
  · exact B1700375
  · exact B1700379
  · exact B1700383
  · exact B1700387
  · exact B1700391
  · exact B1700395
  · exact B1700399
  · exact B1700403
  · exact B1700407
  · exact B1700411
  · exact B1700415
  · exact B1700419
  · exact B1700423
  · exact B1700427
  · exact B1700431
  · exact B1700435
  · exact B1700439
  · exact B1700443
  · exact B1700447
  · exact B1700451
  · exact B1700455
  · exact B1700459
  · exact B1700463
  · exact B1700467
  · exact B1700471
  · exact B1700475
  · exact B1700479
  · exact B1700483
  · exact B1700487
  · exact B1700491
  · exact B1700495
  · exact B1700499
  · exact B1700503
  · exact B1700507
  · exact B1700511
  · exact B1700515
  · exact B1700519
  · exact B1700523
  · exact B1700527
  · exact B1700531
  · exact B1700535
  · exact B1700539
  · exact B1700543
  · exact B1700547
  · exact B1700551
  · exact B1700555
  · exact B1700559
  · exact B1700563
  · exact B1700567
  · exact B1700571
  · exact B1700575
  · exact B1700579
  · exact B1700583
  · exact B1700587
  · exact B1700591
  · exact B1700595
  · exact B1700599
  · exact B1700603
  · exact B1700607
  · exact B1700611
  · exact B1700615
  · exact B1700619
  · exact B1700623
  · exact B1700627
  · exact B1700631
  · exact B1700635
  · exact B1700639
  · exact B1700643
  · exact B1700647
  · exact B1700651
  · exact B1700655
  · exact B1700659
  · exact B1700663
  · exact B1700667
  · exact B1700671
  · exact B1700675
  · exact B1700679
  · exact B1700683
  · exact B1700687
  · exact B1700691
  · exact B1700695
  · exact B1700699
  · exact B1700703
  · exact B1700707
  · exact B1700711
  · exact B1700715
  · exact B1700719
  · exact B1700723
  · exact B1700727
  · exact B1700731
  · exact B1700735
  · exact B1700739
  · exact B1700743
  · exact B1700747
  · exact B1700751
  · exact B1700755
  · exact B1700759
  · exact B1700763
  · exact B1700767
  · exact B1700771
  · exact B1700775
  · exact B1700779
  · exact B1700783
  · exact B1700787
  · exact B1700791
  · exact B1700795
  · exact B1700799
  · exact B1700803
  · exact B1700807
  · exact B1700811
  · exact B1700815
  · exact B1700819
  · exact B1700823
  · exact B1700827
  · exact B1700831
  · exact B1700835
  · exact B1700839
  · exact B1700843
  · exact B1700847
  · exact B1700851
  · exact B1700855
  · exact B1700859
  · exact B1700863
  · exact B1700867
  · exact B1700871
  · exact B1700875
  · exact B1700879
  · exact B1700883
  · exact B1700887
  · exact B1700891
  · exact B1700895
  · exact B1700899
  · exact B1700903
  · exact B1700907
  · exact B1700911
  · exact B1700915
  · exact B1700919
  · exact B1700923
  · exact B1700927
  · exact B1700931
  · exact B1700935
  · exact B1700939
  · exact B1700943
  · exact B1700947
  · exact B1700951
  · exact B1700955
  · exact B1700959
  · exact B1700963
  · exact B1700967
  · exact B1700971
  · exact B1700975
  · exact B1700979
  · exact B1700983
  · exact B1700987
  · exact B1700991
  · exact B1700995
  · exact B1700999
  · exact B1701003
  · exact B1701007
  · exact B1701011
  · exact B1701015
  · exact B1701019
  · exact B1701023
  · exact B1701027
  · exact B1701031
  · exact B1701035
  · exact B1701039
  · exact B1701043
  · exact B1701047
  · exact B1701051
  · exact B1701055
  · exact B1701059
  · exact B1701063
  · exact B1701067
  · exact B1701071
  · exact B1701075
  · exact B1701079
  · exact B1701083
  · exact B1701087
  · exact B1701091
  · exact B1701095
  · exact B1701099
  · exact B1701103
  · exact B1701107
  · exact B1701111
  · exact B1701115
  · exact B1701119
  · exact B1701123
  · exact B1701127
  · exact B1701131
  · exact B1701135
  · exact B1701139
  · exact B1701143
  · exact B1701147
  · exact B1701151
  · exact B1701155
  · exact B1701159
  · exact B1701163
  · exact B1701167
  · exact B1701171
  · exact B1701175
  · exact B1701179
  · exact B1701183
  · exact B1701187
  · exact B1701191
  · exact B1701195
  · exact B1701199
  · exact B1701203
  · exact B1701207
  · exact B1701211
  · exact B1701215
  · exact B1701219
  · exact B1701223
  · exact B1701227
  · exact B1701231
  · exact B1701235
  · exact B1701239
  · exact B1701243
  · exact B1701247
  · exact B1701251
  · exact B1701255
  · exact B1701259
  · exact B1701263
  · exact B1701267
  · exact B1701271
  · exact B1701275
  · exact B1701279
  · exact B1701283
  · exact B1701287
  · exact B1701291
  · exact B1701295
  · exact B1701299
  · exact B1701303
  · exact B1701307
  · exact B1701311
  · exact B1701315
  · exact B1701319
  · exact B1701323
  · exact B1701327
  · exact B1701331
  · exact B1701335
  · exact B1701339
  · exact B1701343
  · exact B1701347
  · exact B1701351
  · exact B1701355
  · exact B1701359
  · exact B1701363
  · exact B1701367
  · exact B1701371
  · exact B1701375
  · exact B1701379
  · exact B1701383
  · exact B1701387
  · exact B1701391
  · exact B1701395
  · exact B1701399
  · exact B1701403
  · exact B1701407
  · exact B1701411
  · exact B1701415
  · exact B1701419
  · exact B1701423
  · exact B1701427
  · exact B1701431
  · exact B1701435
  · exact B1701439
  · exact B1701443
  · exact B1701447
  · exact B1701451
  · exact B1701455
  · exact B1701459
  · exact B1701463
  · exact B1701467
  · exact B1701471
  · exact B1701475
  · exact B1701479
  · exact B1701483
  · exact B1701487
  · exact B1701491
  · exact B1701495
  · exact B1701499
  · exact B1701503
  · exact B1701507
  · exact B1701511
  · exact B1701515
  · exact B1701519
  · exact B1701523
  · exact B1701527
  · exact B1701531
  · exact B1701535
  · exact B1701539
  · exact B1701543
  · exact B1701547

theorem solution (m : ℕ) (hlo : 1699550 ≤ m) (hhi : m ≤ 1701550) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 424887 ≤ j := by omega
    have hj2 : j ≤ 425386 := by omega
    have hb : Blo 1699550 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
