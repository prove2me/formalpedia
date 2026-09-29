-- Prove2me | solution 1 for syracuse_descends_range_1530462_1532462
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:04:43.376595+00:00
-- url     : https://prove2.me/submissions/10feb7e0-291c-4725-bf1d-50e97c88091f

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


theorem B3874837 : Blo 1530462 3874837 := bbase (se 6 (by rfl) ⟨90816, by rfl⟩ : syracuseStep 3874837 = 181633) (by norm_num)
theorem B5816357 : Blo 1530462 5816357 := bbase (se 4 (by rfl) ⟨545283, by rfl⟩ : syracuseStep 5816357 = 1090567) (by norm_num)
theorem B3874949 : Blo 1530462 3874949 := bbase (se 4 (by rfl) ⟨363276, by rfl⟩ : syracuseStep 3874949 = 726553) (by norm_num)
theorem B5169365 : Blo 1530462 5169365 := bbase (se 7 (by rfl) ⟨60578, by rfl⟩ : syracuseStep 5169365 = 121157) (by norm_num)
theorem B3875141 : Blo 1530462 3875141 := bbase (se 4 (by rfl) ⟨363294, by rfl⟩ : syracuseStep 3875141 = 726589) (by norm_num)
theorem B2425205 : Blo 1530462 2425205 := bbase (se 5 (by rfl) ⟨113681, by rfl⟩ : syracuseStep 2425205 = 227363) (by norm_num)
theorem B2179477 : Blo 1530462 2179477 := bbase (se 6 (by rfl) ⟨51081, by rfl⟩ : syracuseStep 2179477 = 102163) (by norm_num)
theorem B3678637 : Blo 1530462 3678637 := bbase (se 3 (by rfl) ⟨689744, by rfl⟩ : syracuseStep 3678637 = 1379489) (by norm_num)
theorem B2761133 : Blo 1530462 2761133 := bbase (se 3 (by rfl) ⟨517712, by rfl⟩ : syracuseStep 2761133 = 1035425) (by norm_num)
theorem B11043317 : Blo 1530462 11043317 := bbase (se 5 (by rfl) ⟨517655, by rfl⟩ : syracuseStep 11043317 = 1035311) (by norm_num)
theorem B3105301 : Blo 1530462 3105301 := bbase (se 6 (by rfl) ⟨72780, by rfl⟩ : syracuseStep 3105301 = 145561) (by norm_num)
theorem B3727901 : Blo 1530462 3727901 := bbase (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) (by norm_num)
theorem B3269173 : Blo 1530462 3269173 := bbase (se 5 (by rfl) ⟨153242, by rfl⟩ : syracuseStep 3269173 = 306485) (by norm_num)
theorem B2761285 : Blo 1530462 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B27927125 : Blo 1530462 27927125 := bbase (se 8 (by rfl) ⟨163635, by rfl⟩ : syracuseStep 27927125 = 327271) (by norm_num)
theorem B7357061 : Blo 1530462 7357061 := bbase (se 4 (by rfl) ⟨689724, by rfl⟩ : syracuseStep 7357061 = 1379449) (by norm_num)
theorem B5169797 : Blo 1530462 5169797 := bbase (se 4 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 5169797 = 969337) (by norm_num)
theorem B3875485 : Blo 1530462 3875485 := bbase (se 3 (by rfl) ⟨726653, by rfl⟩ : syracuseStep 3875485 = 1453307) (by norm_num)
theorem B8282837 : Blo 1530462 8282837 := bbase (se 7 (by rfl) ⟨97064, by rfl⟩ : syracuseStep 8282837 = 194129) (by norm_num)
theorem B2908885 : Blo 1530462 2908885 := bbase (se 7 (by rfl) ⟨34088, by rfl⟩ : syracuseStep 2908885 = 68177) (by norm_num)
theorem B1573597 : Blo 1530462 1573597 := bbase (se 3 (by rfl) ⟨295049, by rfl⟩ : syracuseStep 1573597 = 590099) (by norm_num)
theorem B2179813 : Blo 1530462 2179813 := bbase (se 4 (by rfl) ⟨204357, by rfl⟩ : syracuseStep 2179813 = 408715) (by norm_num)
theorem B3875597 : Blo 1530462 3875597 := bbase (se 3 (by rfl) ⟨726674, by rfl⟩ : syracuseStep 3875597 = 1453349) (by norm_num)
theorem B13075253 : Blo 1530462 13075253 := bbase (se 5 (by rfl) ⟨612902, by rfl⟩ : syracuseStep 13075253 = 1225805) (by norm_num)
theorem B9806645 : Blo 1530462 9806645 := bbase (se 5 (by rfl) ⟨459686, by rfl⟩ : syracuseStep 9806645 = 919373) (by norm_num)
theorem B1745737 : Blo 1530462 1745737 := bbase (se 2 (by rfl) ⟨654651, by rfl⟩ : syracuseStep 1745737 = 1309303) (by norm_num)
theorem B4907861 : Blo 1530462 4907861 := bbase (se 9 (by rfl) ⟨14378, by rfl⟩ : syracuseStep 4907861 = 28757) (by norm_num)
theorem B2909029 : Blo 1530462 2909029 := bbase (se 4 (by rfl) ⟨272721, by rfl⟩ : syracuseStep 2909029 = 545443) (by norm_num)
theorem B7750565 : Blo 1530462 7750565 := bbase (se 4 (by rfl) ⟨726615, by rfl⟩ : syracuseStep 7750565 = 1453231) (by norm_num)
theorem B2180029 : Blo 1530462 2180029 := bbase (se 3 (by rfl) ⟨408755, by rfl⟩ : syracuseStep 2180029 = 817511) (by norm_num)
theorem B3875789 : Blo 1530462 3875789 := bbase (se 3 (by rfl) ⟨726710, by rfl⟩ : syracuseStep 3875789 = 1453421) (by norm_num)
theorem B7357445 : Blo 1530462 7357445 := bbase (se 4 (by rfl) ⟨689760, by rfl⟩ : syracuseStep 7357445 = 1379521) (by norm_num)
theorem B2909189 : Blo 1530462 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B3679253 : Blo 1530462 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B4138037 : Blo 1530462 4138037 := bbase (se 5 (by rfl) ⟨193970, by rfl⟩ : syracuseStep 4138037 = 387941) (by norm_num)
theorem B5170229 : Blo 1530462 5170229 := bbase (se 5 (by rfl) ⟨242354, by rfl⟩ : syracuseStep 5170229 = 484709) (by norm_num)
theorem B5235845 : Blo 1530462 5235845 := bbase (se 4 (by rfl) ⟨490860, by rfl⟩ : syracuseStep 5235845 = 981721) (by norm_num)
theorem B1746085 : Blo 1530462 1746085 := bbase (se 4 (by rfl) ⟨163695, by rfl⟩ : syracuseStep 1746085 = 327391) (by norm_num)
theorem B5817541 : Blo 1530462 5817541 := bbase (se 4 (by rfl) ⟨545394, by rfl⟩ : syracuseStep 5817541 = 1090789) (by norm_num)
theorem B3679453 : Blo 1530462 3679453 := bbase (se 3 (by rfl) ⟨689897, by rfl⟩ : syracuseStep 3679453 = 1379795) (by norm_num)
theorem B3876133 : Blo 1530462 3876133 := bbase (se 4 (by rfl) ⟨363387, by rfl⟩ : syracuseStep 3876133 = 726775) (by norm_num)
theorem B2180405 : Blo 1530462 2180405 := bbase (se 5 (by rfl) ⟨102206, by rfl⟩ : syracuseStep 2180405 = 204413) (by norm_num)
theorem B4359557 : Blo 1530462 4359557 := bbase (se 4 (by rfl) ⟨408708, by rfl⟩ : syracuseStep 4359557 = 817417) (by norm_num)
theorem B3876245 : Blo 1530462 3876245 := bbase (se 6 (by rfl) ⟨90849, by rfl⟩ : syracuseStep 3876245 = 181699) (by norm_num)
theorem B3270061 : Blo 1530462 3270061 := bbase (se 3 (by rfl) ⟨613136, by rfl⟩ : syracuseStep 3270061 = 1226273) (by norm_num)
theorem B1721785 : Blo 1530462 1721785 := bbase (se 2 (by rfl) ⟨645669, by rfl⟩ : syracuseStep 1721785 = 1291339) (by norm_num)
theorem B1721821 : Blo 1530462 1721821 := bbase (se 3 (by rfl) ⟨322841, by rfl⟩ : syracuseStep 1721821 = 645683) (by norm_num)
theorem B5170661 : Blo 1530462 5170661 := bbase (se 4 (by rfl) ⟨484749, by rfl⟩ : syracuseStep 5170661 = 969499) (by norm_num)
theorem B5817845 : Blo 1530462 5817845 := bbase (se 5 (by rfl) ⟨272711, by rfl⟩ : syracuseStep 5817845 = 545423) (by norm_num)
theorem B1721857 : Blo 1530462 1721857 := bbase (se 2 (by rfl) ⟨645696, by rfl⟩ : syracuseStep 1721857 = 1291393) (by norm_num)
theorem B1721893 : Blo 1530462 1721893 := bbase (se 4 (by rfl) ⟨161427, by rfl⟩ : syracuseStep 1721893 = 322855) (by norm_num)
theorem B1721929 : Blo 1530462 1721929 := bbase (se 2 (by rfl) ⟨645723, by rfl⟩ : syracuseStep 1721929 = 1291447) (by norm_num)
theorem B3876437 : Blo 1530462 3876437 := bbase (se 8 (by rfl) ⟨22713, by rfl⟩ : syracuseStep 3876437 = 45427) (by norm_num)
theorem B1721965 : Blo 1530462 1721965 := bbase (se 3 (by rfl) ⟨322868, by rfl⟩ : syracuseStep 1721965 = 645737) (by norm_num)
theorem B1722001 : Blo 1530462 1722001 := bbase (se 2 (by rfl) ⟨645750, by rfl⟩ : syracuseStep 1722001 = 1291501) (by norm_num)
theorem B3106453 : Blo 1530462 3106453 := bbase (se 6 (by rfl) ⟨72807, by rfl⟩ : syracuseStep 3106453 = 145615) (by norm_num)
theorem B1722037 : Blo 1530462 1722037 := bbase (se 5 (by rfl) ⟨80720, by rfl⟩ : syracuseStep 1722037 = 161441) (by norm_num)
theorem B14714581 : Blo 1530462 14714581 := bbase (se 7 (by rfl) ⟨172436, by rfl⟩ : syracuseStep 14714581 = 344873) (by norm_num)
theorem B8840917 : Blo 1530462 8840917 := bbase (se 7 (by rfl) ⟨103604, by rfl⟩ : syracuseStep 8840917 = 207209) (by norm_num)
theorem B3106517 : Blo 1530462 3106517 := bbase (se 7 (by rfl) ⟨36404, by rfl⟩ : syracuseStep 3106517 = 72809) (by norm_num)
theorem B1722073 : Blo 1530462 1722073 := bbase (se 2 (by rfl) ⟨645777, by rfl⟩ : syracuseStep 1722073 = 1291555) (by norm_num)
theorem B1722109 : Blo 1530462 1722109 := bbase (se 3 (by rfl) ⟨322895, by rfl⟩ : syracuseStep 1722109 = 645791) (by norm_num)
theorem B6211333 : Blo 1530462 6211333 := bbase (se 4 (by rfl) ⟨582312, by rfl⟩ : syracuseStep 6211333 = 1164625) (by norm_num)
theorem B6211349 : Blo 1530462 6211349 := bbase (se 6 (by rfl) ⟨145578, by rfl⟩ : syracuseStep 6211349 = 291157) (by norm_num)
theorem B1722145 : Blo 1530462 1722145 := bbase (se 2 (by rfl) ⟨645804, by rfl⟩ : syracuseStep 1722145 = 1291609) (by norm_num)
theorem B15714101 : Blo 1530462 15714101 := bbase (se 5 (by rfl) ⟨736598, by rfl⟩ : syracuseStep 15714101 = 1473197) (by norm_num)
theorem B1722181 : Blo 1530462 1722181 := bbase (se 4 (by rfl) ⟨161454, by rfl⟩ : syracuseStep 1722181 = 322909) (by norm_num)
theorem B1722217 : Blo 1530462 1722217 := bbase (se 2 (by rfl) ⟨645831, by rfl⟩ : syracuseStep 1722217 = 1291663) (by norm_num)
theorem B1722253 : Blo 1530462 1722253 := bbase (se 3 (by rfl) ⟨322922, by rfl⟩ : syracuseStep 1722253 = 645845) (by norm_num)
theorem B2295701 : Blo 1530462 2295701 := bbase (se 6 (by rfl) ⟨53805, by rfl⟩ : syracuseStep 2295701 = 107611) (by norm_num)
theorem B5171093 : Blo 1530462 5171093 := bbase (se 6 (by rfl) ⟨121197, by rfl⟩ : syracuseStep 5171093 = 242395) (by norm_num)
theorem B3270557 : Blo 1530462 3270557 := bbase (se 3 (by rfl) ⟨613229, by rfl⟩ : syracuseStep 3270557 = 1226459) (by norm_num)
theorem B2295725 : Blo 1530462 2295725 := bbase (se 3 (by rfl) ⟨430448, by rfl⟩ : syracuseStep 2295725 = 860897) (by norm_num)
theorem B3876781 : Blo 1530462 3876781 := bbase (se 3 (by rfl) ⟨726896, by rfl⟩ : syracuseStep 3876781 = 1453793) (by norm_num)
theorem B1722289 : Blo 1530462 1722289 := bbase (se 2 (by rfl) ⟨645858, by rfl⟩ : syracuseStep 1722289 = 1291717) (by norm_num)
theorem B2295749 : Blo 1530462 2295749 := bbase (se 4 (by rfl) ⟨215226, by rfl⟩ : syracuseStep 2295749 = 430453) (by norm_num)
theorem B8718293 : Blo 1530462 8718293 := bbase (se 7 (by rfl) ⟨102167, by rfl⟩ : syracuseStep 8718293 = 204335) (by norm_num)
theorem B1722325 : Blo 1530462 1722325 := bbase (se 7 (by rfl) ⟨20183, by rfl⟩ : syracuseStep 1722325 = 40367) (by norm_num)
theorem B2295773 : Blo 1530462 2295773 := bbase (se 3 (by rfl) ⟨430457, by rfl⟩ : syracuseStep 2295773 = 860915) (by norm_num)
theorem B2295797 : Blo 1530462 2295797 := bbase (se 5 (by rfl) ⟨107615, by rfl⟩ : syracuseStep 2295797 = 215231) (by norm_num)
theorem B6989813 : Blo 1530462 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B1722361 : Blo 1530462 1722361 := bbase (se 2 (by rfl) ⟨645885, by rfl⟩ : syracuseStep 1722361 = 1291771) (by norm_num)
theorem B3680261 : Blo 1530462 3680261 := bbase (se 4 (by rfl) ⟨345024, by rfl⟩ : syracuseStep 3680261 = 690049) (by norm_num)
theorem B2295821 : Blo 1530462 2295821 := bbase (se 3 (by rfl) ⟨430466, by rfl⟩ : syracuseStep 2295821 = 860933) (by norm_num)
theorem B1722397 : Blo 1530462 1722397 := bbase (se 3 (by rfl) ⟨322949, by rfl⟩ : syracuseStep 1722397 = 645899) (by norm_num)
theorem B3876893 : Blo 1530462 3876893 := bbase (se 3 (by rfl) ⟨726917, by rfl⟩ : syracuseStep 3876893 = 1453835) (by norm_num)
theorem B2295845 : Blo 1530462 2295845 := bbase (se 4 (by rfl) ⟨215235, by rfl⟩ : syracuseStep 2295845 = 430471) (by norm_num)
theorem B2295869 : Blo 1530462 2295869 := bbase (se 3 (by rfl) ⟨430475, by rfl⟩ : syracuseStep 2295869 = 860951) (by norm_num)
theorem B1722433 : Blo 1530462 1722433 := bbase (se 2 (by rfl) ⟨645912, by rfl⟩ : syracuseStep 1722433 = 1291825) (by norm_num)
theorem B2295893 : Blo 1530462 2295893 := bbase (se 8 (by rfl) ⟨13452, by rfl⟩ : syracuseStep 2295893 = 26905) (by norm_num)
theorem B1722469 : Blo 1530462 1722469 := bbase (se 4 (by rfl) ⟨161481, by rfl⟩ : syracuseStep 1722469 = 322963) (by norm_num)
theorem B2295917 : Blo 1530462 2295917 := bbase (se 3 (by rfl) ⟨430484, by rfl⟩ : syracuseStep 2295917 = 860969) (by norm_num)
theorem B2295941 : Blo 1530462 2295941 := bbase (se 4 (by rfl) ⟨215244, by rfl⟩ : syracuseStep 2295941 = 430489) (by norm_num)
theorem B1722505 : Blo 1530462 1722505 := bbase (se 2 (by rfl) ⟨645939, by rfl⟩ : syracuseStep 1722505 = 1291879) (by norm_num)
theorem B2295965 : Blo 1530462 2295965 := bbase (se 3 (by rfl) ⟨430493, by rfl⟩ : syracuseStep 2295965 = 860987) (by norm_num)
theorem B2017445 : Blo 1530462 2017445 := bbase (se 4 (by rfl) ⟨189135, by rfl⟩ : syracuseStep 2017445 = 378271) (by norm_num)
theorem B1722541 : Blo 1530462 1722541 := bbase (se 3 (by rfl) ⟨322976, by rfl⟩ : syracuseStep 1722541 = 645953) (by norm_num)
theorem B2295989 : Blo 1530462 2295989 := bbase (se 5 (by rfl) ⟨107624, by rfl⟩ : syracuseStep 2295989 = 215249) (by norm_num)
theorem B7751861 : Blo 1530462 7751861 := bbase (se 5 (by rfl) ⟨363368, by rfl⟩ : syracuseStep 7751861 = 726737) (by norm_num)
theorem B2582725 : Blo 1530462 2582725 := bbase (se 4 (by rfl) ⟨242130, by rfl⟩ : syracuseStep 2582725 = 484261) (by norm_num)
theorem B2296013 : Blo 1530462 2296013 := bbase (se 3 (by rfl) ⟨430502, by rfl⟩ : syracuseStep 2296013 = 861005) (by norm_num)
theorem B1722577 : Blo 1530462 1722577 := bbase (se 2 (by rfl) ⟨645966, by rfl⟩ : syracuseStep 1722577 = 1291933) (by norm_num)
theorem B3877085 : Blo 1530462 3877085 := bbase (se 3 (by rfl) ⟨726953, by rfl⟩ : syracuseStep 3877085 = 1453907) (by norm_num)
theorem B2296037 : Blo 1530462 2296037 := bbase (se 4 (by rfl) ⟨215253, by rfl⟩ : syracuseStep 2296037 = 430507) (by norm_num)
theorem B1722613 : Blo 1530462 1722613 := bbase (se 5 (by rfl) ⟨80747, by rfl⟩ : syracuseStep 1722613 = 161495) (by norm_num)
theorem B2296061 : Blo 1530462 2296061 := bbase (se 3 (by rfl) ⟨430511, by rfl⟩ : syracuseStep 2296061 = 861023) (by norm_num)
theorem B6539525 : Blo 1530462 6539525 := bbase (se 4 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 6539525 = 1226161) (by norm_num)
theorem B2296085 : Blo 1530462 2296085 := bbase (se 6 (by rfl) ⟨53814, by rfl⟩ : syracuseStep 2296085 = 107629) (by norm_num)
theorem B1722649 : Blo 1530462 1722649 := bbase (se 2 (by rfl) ⟨645993, by rfl⟩ : syracuseStep 1722649 = 1291987) (by norm_num)
theorem B2582813 : Blo 1530462 2582813 := bbase (se 3 (by rfl) ⟨484277, by rfl⟩ : syracuseStep 2582813 = 968555) (by norm_num)
theorem B2296109 : Blo 1530462 2296109 := bbase (se 3 (by rfl) ⟨430520, by rfl⟩ : syracuseStep 2296109 = 861041) (by norm_num)
theorem B1722685 : Blo 1530462 1722685 := bbase (se 3 (by rfl) ⟨323003, by rfl⟩ : syracuseStep 1722685 = 646007) (by norm_num)
theorem B2296133 : Blo 1530462 2296133 := bbase (se 4 (by rfl) ⟨215262, by rfl⟩ : syracuseStep 2296133 = 430525) (by norm_num)
theorem B5171525 : Blo 1530462 5171525 := bbase (se 4 (by rfl) ⟨484830, by rfl⟩ : syracuseStep 5171525 = 969661) (by norm_num)
theorem B2296157 : Blo 1530462 2296157 := bbase (se 3 (by rfl) ⟨430529, by rfl⟩ : syracuseStep 2296157 = 861059) (by norm_num)
theorem B1722721 : Blo 1530462 1722721 := bbase (se 2 (by rfl) ⟨646020, by rfl⟩ : syracuseStep 1722721 = 1292041) (by norm_num)
theorem B2296181 : Blo 1530462 2296181 := bbase (se 5 (by rfl) ⟨107633, by rfl⟩ : syracuseStep 2296181 = 215267) (by norm_num)
theorem B1722757 : Blo 1530462 1722757 := bbase (se 4 (by rfl) ⟨161508, by rfl⟩ : syracuseStep 1722757 = 323017) (by norm_num)
theorem B2296205 : Blo 1530462 2296205 := bbase (se 3 (by rfl) ⟨430538, by rfl⟩ : syracuseStep 2296205 = 861077) (by norm_num)
theorem B2582941 : Blo 1530462 2582941 := bbase (se 3 (by rfl) ⟨484301, by rfl⟩ : syracuseStep 2582941 = 968603) (by norm_num)
theorem B2296229 : Blo 1530462 2296229 := bbase (se 4 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 2296229 = 430543) (by norm_num)
theorem B1722793 : Blo 1530462 1722793 := bbase (se 2 (by rfl) ⟨646047, by rfl⟩ : syracuseStep 1722793 = 1292095) (by norm_num)
theorem B7858613 : Blo 1530462 7858613 := bbase (se 5 (by rfl) ⟨368372, by rfl⟩ : syracuseStep 7858613 = 736745) (by norm_num)
theorem B2329013 : Blo 1530462 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B2296253 : Blo 1530462 2296253 := bbase (se 3 (by rfl) ⟨430547, by rfl⟩ : syracuseStep 2296253 = 861095) (by norm_num)
theorem B1722829 : Blo 1530462 1722829 := bbase (se 3 (by rfl) ⟨323030, by rfl⟩ : syracuseStep 1722829 = 646061) (by norm_num)
theorem B2296277 : Blo 1530462 2296277 := bbase (se 7 (by rfl) ⟨26909, by rfl⟩ : syracuseStep 2296277 = 53819) (by norm_num)
theorem B2296301 : Blo 1530462 2296301 := bbase (se 3 (by rfl) ⟨430556, by rfl⟩ : syracuseStep 2296301 = 861113) (by norm_num)
theorem B1722865 : Blo 1530462 1722865 := bbase (se 2 (by rfl) ⟨646074, by rfl⟩ : syracuseStep 1722865 = 1292149) (by norm_num)
theorem B2583029 : Blo 1530462 2583029 := bbase (se 5 (by rfl) ⟨121079, by rfl⟩ : syracuseStep 2583029 = 242159) (by norm_num)
theorem B2296325 : Blo 1530462 2296325 := bbase (se 4 (by rfl) ⟨215280, by rfl⟩ : syracuseStep 2296325 = 430561) (by norm_num)
theorem B1722901 : Blo 1530462 1722901 := bbase (se 6 (by rfl) ⟨40380, by rfl⟩ : syracuseStep 1722901 = 80761) (by norm_num)
theorem B2296349 : Blo 1530462 2296349 := bbase (se 3 (by rfl) ⟨430565, by rfl⟩ : syracuseStep 2296349 = 861131) (by norm_num)
theorem B2296373 : Blo 1530462 2296373 := bbase (se 5 (by rfl) ⟨107642, by rfl⟩ : syracuseStep 2296373 = 215285) (by norm_num)
theorem B3877429 : Blo 1530462 3877429 := bbase (se 5 (by rfl) ⟨181754, by rfl⟩ : syracuseStep 3877429 = 363509) (by norm_num)
theorem B1722937 : Blo 1530462 1722937 := bbase (se 2 (by rfl) ⟨646101, by rfl⟩ : syracuseStep 1722937 = 1292203) (by norm_num)
theorem B2296397 : Blo 1530462 2296397 := bbase (se 3 (by rfl) ⟨430574, by rfl⟩ : syracuseStep 2296397 = 861149) (by norm_num)
theorem B1722973 : Blo 1530462 1722973 := bbase (se 3 (by rfl) ⟨323057, by rfl⟩ : syracuseStep 1722973 = 646115) (by norm_num)
theorem B2296421 : Blo 1530462 2296421 := bbase (se 4 (by rfl) ⟨215289, by rfl⟩ : syracuseStep 2296421 = 430579) (by norm_num)
theorem B2583157 : Blo 1530462 2583157 := bbase (se 5 (by rfl) ⟨121085, by rfl⟩ : syracuseStep 2583157 = 242171) (by norm_num)
theorem B2296445 : Blo 1530462 2296445 := bbase (se 3 (by rfl) ⟨430583, by rfl⟩ : syracuseStep 2296445 = 861167) (by norm_num)
theorem B1723009 : Blo 1530462 1723009 := bbase (se 2 (by rfl) ⟨646128, by rfl⟩ : syracuseStep 1723009 = 1292257) (by norm_num)
theorem B2296469 : Blo 1530462 2296469 := bbase (se 6 (by rfl) ⟨53823, by rfl⟩ : syracuseStep 2296469 = 107647) (by norm_num)
theorem B1723045 : Blo 1530462 1723045 := bbase (se 4 (by rfl) ⟨161535, by rfl⟩ : syracuseStep 1723045 = 323071) (by norm_num)
theorem B3877541 : Blo 1530462 3877541 := bbase (se 4 (by rfl) ⟨363519, by rfl⟩ : syracuseStep 3877541 = 727039) (by norm_num)
theorem B2296493 : Blo 1530462 2296493 := bbase (se 3 (by rfl) ⟨430592, by rfl⟩ : syracuseStep 2296493 = 861185) (by norm_num)
theorem B2296517 : Blo 1530462 2296517 := bbase (se 4 (by rfl) ⟨215298, by rfl⟩ : syracuseStep 2296517 = 430597) (by norm_num)
theorem B2181829 : Blo 1530462 2181829 := bbase (se 4 (by rfl) ⟨204546, by rfl⟩ : syracuseStep 2181829 = 409093) (by norm_num)
theorem B1723081 : Blo 1530462 1723081 := bbase (se 2 (by rfl) ⟨646155, by rfl⟩ : syracuseStep 1723081 = 1292311) (by norm_num)
theorem B2583245 : Blo 1530462 2583245 := bbase (se 3 (by rfl) ⟨484358, by rfl⟩ : syracuseStep 2583245 = 968717) (by norm_num)
theorem B2296541 : Blo 1530462 2296541 := bbase (se 3 (by rfl) ⟨430601, by rfl⟩ : syracuseStep 2296541 = 861203) (by norm_num)
theorem B1723117 : Blo 1530462 1723117 := bbase (se 3 (by rfl) ⟨323084, by rfl⟩ : syracuseStep 1723117 = 646169) (by norm_num)
theorem B2296565 : Blo 1530462 2296565 := bbase (se 5 (by rfl) ⟨107651, by rfl⟩ : syracuseStep 2296565 = 215303) (by norm_num)
theorem B5171957 : Blo 1530462 5171957 := bbase (se 5 (by rfl) ⟨242435, by rfl⟩ : syracuseStep 5171957 = 484871) (by norm_num)
theorem B3681029 : Blo 1530462 3681029 := bbase (se 4 (by rfl) ⟨345096, by rfl⟩ : syracuseStep 3681029 = 690193) (by norm_num)
theorem B2296589 : Blo 1530462 2296589 := bbase (se 3 (by rfl) ⟨430610, by rfl⟩ : syracuseStep 2296589 = 861221) (by norm_num)
theorem B1723153 : Blo 1530462 1723153 := bbase (se 2 (by rfl) ⟨646182, by rfl⟩ : syracuseStep 1723153 = 1292365) (by norm_num)
theorem B3271445 : Blo 1530462 3271445 := bbase (se 6 (by rfl) ⟨76674, by rfl⟩ : syracuseStep 3271445 = 153349) (by norm_num)
theorem B2296613 : Blo 1530462 2296613 := bbase (se 4 (by rfl) ⟨215307, by rfl⟩ : syracuseStep 2296613 = 430615) (by norm_num)
theorem B2452277 : Blo 1530462 2452277 := bbase (se 5 (by rfl) ⟨114950, by rfl⟩ : syracuseStep 2452277 = 229901) (by norm_num)
theorem B1723189 : Blo 1530462 1723189 := bbase (se 5 (by rfl) ⟨80774, by rfl⟩ : syracuseStep 1723189 = 161549) (by norm_num)
theorem B2296637 : Blo 1530462 2296637 := bbase (se 3 (by rfl) ⟨430619, by rfl⟩ : syracuseStep 2296637 = 861239) (by norm_num)
theorem B2583373 : Blo 1530462 2583373 := bbase (se 3 (by rfl) ⟨484382, by rfl⟩ : syracuseStep 2583373 = 968765) (by norm_num)
theorem B2296661 : Blo 1530462 2296661 := bbase (se 9 (by rfl) ⟨6728, by rfl⟩ : syracuseStep 2296661 = 13457) (by norm_num)
theorem B1723225 : Blo 1530462 1723225 := bbase (se 2 (by rfl) ⟨646209, by rfl⟩ : syracuseStep 1723225 = 1292419) (by norm_num)
theorem B3877733 : Blo 1530462 3877733 := bbase (se 4 (by rfl) ⟨363537, by rfl⟩ : syracuseStep 3877733 = 727075) (by norm_num)
theorem B2296685 : Blo 1530462 2296685 := bbase (se 3 (by rfl) ⟨430628, by rfl⟩ : syracuseStep 2296685 = 861257) (by norm_num)
theorem B1723261 : Blo 1530462 1723261 := bbase (se 3 (by rfl) ⟨323111, by rfl⟩ : syracuseStep 1723261 = 646223) (by norm_num)
theorem B2296709 : Blo 1530462 2296709 := bbase (se 4 (by rfl) ⟨215316, by rfl⟩ : syracuseStep 2296709 = 430633) (by norm_num)
theorem B3443597 : Blo 1530462 3443597 := bbase (se 3 (by rfl) ⟨645674, by rfl⟩ : syracuseStep 3443597 = 1291349) (by norm_num)
theorem B3271565 : Blo 1530462 3271565 := bbase (se 3 (by rfl) ⟨613418, by rfl⟩ : syracuseStep 3271565 = 1226837) (by norm_num)
theorem B2296733 : Blo 1530462 2296733 := bbase (se 3 (by rfl) ⟨430637, by rfl⟩ : syracuseStep 2296733 = 861275) (by norm_num)
theorem B1723297 : Blo 1530462 1723297 := bbase (se 2 (by rfl) ⟨646236, by rfl⟩ : syracuseStep 1723297 = 1292473) (by norm_num)
theorem B2583461 : Blo 1530462 2583461 := bbase (se 4 (by rfl) ⟨242199, by rfl⟩ : syracuseStep 2583461 = 484399) (by norm_num)
theorem B2296757 : Blo 1530462 2296757 := bbase (se 5 (by rfl) ⟨107660, by rfl⟩ : syracuseStep 2296757 = 215321) (by norm_num)
theorem B4361141 : Blo 1530462 4361141 := bbase (se 5 (by rfl) ⟨204428, by rfl⟩ : syracuseStep 4361141 = 408857) (by norm_num)
theorem B1723333 : Blo 1530462 1723333 := bbase (se 4 (by rfl) ⟨161562, by rfl⟩ : syracuseStep 1723333 = 323125) (by norm_num)
theorem B2296781 : Blo 1530462 2296781 := bbase (se 3 (by rfl) ⟨430646, by rfl⟩ : syracuseStep 2296781 = 861293) (by norm_num)
theorem B3443669 : Blo 1530462 3443669 := bbase (se 7 (by rfl) ⟨40355, by rfl⟩ : syracuseStep 3443669 = 80711) (by norm_num)
theorem B2296805 : Blo 1530462 2296805 := bbase (se 4 (by rfl) ⟨215325, by rfl⟩ : syracuseStep 2296805 = 430651) (by norm_num)
theorem B1723369 : Blo 1530462 1723369 := bbase (se 2 (by rfl) ⟨646263, by rfl⟩ : syracuseStep 1723369 = 1292527) (by norm_num)
theorem B8842229 : Blo 1530462 8842229 := bbase (se 5 (by rfl) ⟨414479, by rfl⟩ : syracuseStep 8842229 = 828959) (by norm_num)
theorem B5598197 : Blo 1530462 5598197 := bbase (se 5 (by rfl) ⟨262415, by rfl⟩ : syracuseStep 5598197 = 524831) (by norm_num)
theorem B2296829 : Blo 1530462 2296829 := bbase (se 3 (by rfl) ⟨430655, by rfl⟩ : syracuseStep 2296829 = 861311) (by norm_num)
theorem B1723405 : Blo 1530462 1723405 := bbase (se 3 (by rfl) ⟨323138, by rfl⟩ : syracuseStep 1723405 = 646277) (by norm_num)
theorem B2296853 : Blo 1530462 2296853 := bbase (se 6 (by rfl) ⟨53832, by rfl⟩ : syracuseStep 2296853 = 107665) (by norm_num)
theorem B3443741 : Blo 1530462 3443741 := bbase (se 3 (by rfl) ⟨645701, by rfl⟩ : syracuseStep 3443741 = 1291403) (by norm_num)
theorem B2583589 : Blo 1530462 2583589 := bbase (se 4 (by rfl) ⟨242211, by rfl⟩ : syracuseStep 2583589 = 484423) (by norm_num)
theorem B2296877 : Blo 1530462 2296877 := bbase (se 3 (by rfl) ⟨430664, by rfl⟩ : syracuseStep 2296877 = 861329) (by norm_num)
theorem B1723441 : Blo 1530462 1723441 := bbase (se 2 (by rfl) ⟨646290, by rfl⟩ : syracuseStep 1723441 = 1292581) (by norm_num)
theorem B12414005 : Blo 1530462 12414005 := bbase (se 5 (by rfl) ⟨581906, by rfl⟩ : syracuseStep 12414005 = 1163813) (by norm_num)
theorem B2296901 : Blo 1530462 2296901 := bbase (se 4 (by rfl) ⟨215334, by rfl⟩ : syracuseStep 2296901 = 430669) (by norm_num)
theorem B1723477 : Blo 1530462 1723477 := bbase (se 8 (by rfl) ⟨10098, by rfl⟩ : syracuseStep 1723477 = 20197) (by norm_num)
theorem B2296925 : Blo 1530462 2296925 := bbase (se 3 (by rfl) ⟨430673, by rfl⟩ : syracuseStep 2296925 = 861347) (by norm_num)
theorem B3443813 : Blo 1530462 3443813 := bbase (se 4 (by rfl) ⟨322857, by rfl⟩ : syracuseStep 3443813 = 645715) (by norm_num)
theorem B2296949 : Blo 1530462 2296949 := bbase (se 5 (by rfl) ⟨107669, by rfl⟩ : syracuseStep 2296949 = 215339) (by norm_num)
theorem B1723513 : Blo 1530462 1723513 := bbase (se 2 (by rfl) ⟨646317, by rfl⟩ : syracuseStep 1723513 = 1292635) (by norm_num)
theorem B2583677 : Blo 1530462 2583677 := bbase (se 3 (by rfl) ⟨484439, by rfl⟩ : syracuseStep 2583677 = 968879) (by norm_num)
theorem B2296973 : Blo 1530462 2296973 := bbase (se 3 (by rfl) ⟨430682, by rfl⟩ : syracuseStep 2296973 = 861365) (by norm_num)
theorem B1723549 : Blo 1530462 1723549 := bbase (se 3 (by rfl) ⟨323165, by rfl⟩ : syracuseStep 1723549 = 646331) (by norm_num)
theorem B2296997 : Blo 1530462 2296997 := bbase (se 4 (by rfl) ⟨215343, by rfl⟩ : syracuseStep 2296997 = 430687) (by norm_num)
theorem B3443885 : Blo 1530462 3443885 := bbase (se 3 (by rfl) ⟨645728, by rfl⟩ : syracuseStep 3443885 = 1291457) (by norm_num)
theorem B2297021 : Blo 1530462 2297021 := bbase (se 3 (by rfl) ⟨430691, by rfl⟩ : syracuseStep 2297021 = 861383) (by norm_num)
theorem B3878077 : Blo 1530462 3878077 := bbase (se 3 (by rfl) ⟨727139, by rfl⟩ : syracuseStep 3878077 = 1454279) (by norm_num)
theorem B1723585 : Blo 1530462 1723585 := bbase (se 2 (by rfl) ⟨646344, by rfl⟩ : syracuseStep 1723585 = 1292689) (by norm_num)
theorem B2297045 : Blo 1530462 2297045 := bbase (se 7 (by rfl) ⟨26918, by rfl⟩ : syracuseStep 2297045 = 53837) (by norm_num)
theorem B1723621 : Blo 1530462 1723621 := bbase (se 4 (by rfl) ⟨161589, by rfl⟩ : syracuseStep 1723621 = 323179) (by norm_num)
theorem B2297069 : Blo 1530462 2297069 := bbase (se 3 (by rfl) ⟨430700, by rfl⟩ : syracuseStep 2297069 = 861401) (by norm_num)
theorem B3443957 : Blo 1530462 3443957 := bbase (se 5 (by rfl) ⟨161435, by rfl⟩ : syracuseStep 3443957 = 322871) (by norm_num)
theorem B6540533 : Blo 1530462 6540533 := bbase (se 5 (by rfl) ⟨306587, by rfl⟩ : syracuseStep 6540533 = 613175) (by norm_num)
theorem B2583805 : Blo 1530462 2583805 := bbase (se 3 (by rfl) ⟨484463, by rfl⟩ : syracuseStep 2583805 = 968927) (by norm_num)
theorem B2297093 : Blo 1530462 2297093 := bbase (se 4 (by rfl) ⟨215352, by rfl⟩ : syracuseStep 2297093 = 430705) (by norm_num)
theorem B1723657 : Blo 1530462 1723657 := bbase (se 2 (by rfl) ⟨646371, by rfl⟩ : syracuseStep 1723657 = 1292743) (by norm_num)
theorem B1551637 : Blo 1530462 1551637 := bbase (se 6 (by rfl) ⟨36366, by rfl⟩ : syracuseStep 1551637 = 72733) (by norm_num)
theorem B2297117 : Blo 1530462 2297117 := bbase (se 3 (by rfl) ⟨430709, by rfl⟩ : syracuseStep 2297117 = 861419) (by norm_num)
theorem B3878189 : Blo 1530462 3878189 := bbase (se 3 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 3878189 = 1454321) (by norm_num)
theorem B1723693 : Blo 1530462 1723693 := bbase (se 3 (by rfl) ⟨323192, by rfl⟩ : syracuseStep 1723693 = 646385) (by norm_num)
theorem B2452789 : Blo 1530462 2452789 := bbase (se 5 (by rfl) ⟨114974, by rfl⟩ : syracuseStep 2452789 = 229949) (by norm_num)
theorem B2297141 : Blo 1530462 2297141 := bbase (se 5 (by rfl) ⟨107678, by rfl⟩ : syracuseStep 2297141 = 215357) (by norm_num)
theorem B3444029 : Blo 1530462 3444029 := bbase (se 3 (by rfl) ⟨645755, by rfl⟩ : syracuseStep 3444029 = 1291511) (by norm_num)
theorem B2297165 : Blo 1530462 2297165 := bbase (se 3 (by rfl) ⟨430718, by rfl⟩ : syracuseStep 2297165 = 861437) (by norm_num)
theorem B1723729 : Blo 1530462 1723729 := bbase (se 2 (by rfl) ⟨646398, by rfl⟩ : syracuseStep 1723729 = 1292797) (by norm_num)
theorem B2583893 : Blo 1530462 2583893 := bbase (se 11 (by rfl) ⟨1892, by rfl⟩ : syracuseStep 2583893 = 3785) (by norm_num)
theorem B2297189 : Blo 1530462 2297189 := bbase (se 4 (by rfl) ⟨215361, by rfl⟩ : syracuseStep 2297189 = 430723) (by norm_num)
theorem B1723765 : Blo 1530462 1723765 := bbase (se 5 (by rfl) ⟨80801, by rfl⟩ : syracuseStep 1723765 = 161603) (by norm_num)
theorem B2297213 : Blo 1530462 2297213 := bbase (se 3 (by rfl) ⟨430727, by rfl⟩ : syracuseStep 2297213 = 861455) (by norm_num)
theorem B3444101 : Blo 1530462 3444101 := bbase (se 4 (by rfl) ⟨322884, by rfl⟩ : syracuseStep 3444101 = 645769) (by norm_num)
theorem B2297237 : Blo 1530462 2297237 := bbase (se 6 (by rfl) ⟨53841, by rfl⟩ : syracuseStep 2297237 = 107683) (by norm_num)
theorem B1723801 : Blo 1530462 1723801 := bbase (se 2 (by rfl) ⟨646425, by rfl⟩ : syracuseStep 1723801 = 1292851) (by norm_num)
theorem B2297261 : Blo 1530462 2297261 := bbase (se 3 (by rfl) ⟨430736, by rfl⟩ : syracuseStep 2297261 = 861473) (by norm_num)
theorem B4656565 : Blo 1530462 4656565 := bbase (se 5 (by rfl) ⟨218276, by rfl⟩ : syracuseStep 4656565 = 436553) (by norm_num)
theorem B1723837 : Blo 1530462 1723837 := bbase (se 3 (by rfl) ⟨323219, by rfl⟩ : syracuseStep 1723837 = 646439) (by norm_num)
theorem B7753157 : Blo 1530462 7753157 := bbase (se 4 (by rfl) ⟨726858, by rfl⟩ : syracuseStep 7753157 = 1453717) (by norm_num)
theorem B2297285 : Blo 1530462 2297285 := bbase (se 4 (by rfl) ⟨215370, by rfl⟩ : syracuseStep 2297285 = 430741) (by norm_num)
theorem B3444173 : Blo 1530462 3444173 := bbase (se 3 (by rfl) ⟨645782, by rfl⟩ : syracuseStep 3444173 = 1291565) (by norm_num)
theorem B2584021 : Blo 1530462 2584021 := bbase (se 7 (by rfl) ⟨30281, by rfl⟩ : syracuseStep 2584021 = 60563) (by norm_num)
theorem B2297309 : Blo 1530462 2297309 := bbase (se 3 (by rfl) ⟨430745, by rfl⟩ : syracuseStep 2297309 = 861491) (by norm_num)
theorem B1723873 : Blo 1530462 1723873 := bbase (se 2 (by rfl) ⟨646452, by rfl⟩ : syracuseStep 1723873 = 1292905) (by norm_num)
theorem B3878381 : Blo 1530462 3878381 := bbase (se 3 (by rfl) ⟨727196, by rfl⟩ : syracuseStep 3878381 = 1454393) (by norm_num)
theorem B2297333 : Blo 1530462 2297333 := bbase (se 5 (by rfl) ⟨107687, by rfl⟩ : syracuseStep 2297333 = 215375) (by norm_num)
theorem B3272197 : Blo 1530462 3272197 := bbase (se 4 (by rfl) ⟨306768, by rfl⟩ : syracuseStep 3272197 = 613537) (by norm_num)
theorem B1723909 : Blo 1530462 1723909 := bbase (se 4 (by rfl) ⟨161616, by rfl⟩ : syracuseStep 1723909 = 323233) (by norm_num)
theorem B2297357 : Blo 1530462 2297357 := bbase (se 3 (by rfl) ⟨430754, by rfl⟩ : syracuseStep 2297357 = 861509) (by norm_num)
theorem B3444245 : Blo 1530462 3444245 := bbase (se 6 (by rfl) ⟨80724, by rfl⟩ : syracuseStep 3444245 = 161449) (by norm_num)
theorem B22081045 : Blo 1530462 22081045 := bbase (se 6 (by rfl) ⟨517524, by rfl⟩ : syracuseStep 22081045 = 1035049) (by norm_num)
theorem B2297381 : Blo 1530462 2297381 := bbase (se 4 (by rfl) ⟨215379, by rfl⟩ : syracuseStep 2297381 = 430759) (by norm_num)
theorem B1723945 : Blo 1530462 1723945 := bbase (se 2 (by rfl) ⟨646479, by rfl⟩ : syracuseStep 1723945 = 1292959) (by norm_num)
theorem B2584109 : Blo 1530462 2584109 := bbase (se 3 (by rfl) ⟨484520, by rfl⟩ : syracuseStep 2584109 = 969041) (by norm_num)
theorem B1838641 : Blo 1530462 1838641 := bbase (se 2 (by rfl) ⟨689490, by rfl⟩ : syracuseStep 1838641 = 1378981) (by norm_num)
theorem B2297405 : Blo 1530462 2297405 := bbase (se 3 (by rfl) ⟨430763, by rfl⟩ : syracuseStep 2297405 = 861527) (by norm_num)
theorem B1838669 : Blo 1530462 1838669 := bbase (se 3 (by rfl) ⟨344750, by rfl⟩ : syracuseStep 1838669 = 689501) (by norm_num)
theorem B1723981 : Blo 1530462 1723981 := bbase (se 3 (by rfl) ⟨323246, by rfl⟩ : syracuseStep 1723981 = 646493) (by norm_num)
theorem B2297429 : Blo 1530462 2297429 := bbase (se 8 (by rfl) ⟨13461, by rfl⟩ : syracuseStep 2297429 = 26923) (by norm_num)
theorem B4361813 : Blo 1530462 4361813 := bbase (se 8 (by rfl) ⟨25557, by rfl⟩ : syracuseStep 4361813 = 51115) (by norm_num)
theorem B3444317 : Blo 1530462 3444317 := bbase (se 3 (by rfl) ⟨645809, by rfl⟩ : syracuseStep 3444317 = 1291619) (by norm_num)
theorem B2297453 : Blo 1530462 2297453 := bbase (se 3 (by rfl) ⟨430772, by rfl⟩ : syracuseStep 2297453 = 861545) (by norm_num)
theorem B1724017 : Blo 1530462 1724017 := bbase (se 2 (by rfl) ⟨646506, by rfl⟩ : syracuseStep 1724017 = 1293013) (by norm_num)
theorem B1937029 : Blo 1530462 1937029 := bbase (se 4 (by rfl) ⟨181596, by rfl⟩ : syracuseStep 1937029 = 363193) (by norm_num)
theorem B2297477 : Blo 1530462 2297477 := bbase (se 4 (by rfl) ⟨215388, by rfl⟩ : syracuseStep 2297477 = 430777) (by norm_num)
theorem B2297501 : Blo 1530462 2297501 := bbase (se 3 (by rfl) ⟨430781, by rfl⟩ : syracuseStep 2297501 = 861563) (by norm_num)
theorem B3444389 : Blo 1530462 3444389 := bbase (se 4 (by rfl) ⟨322911, by rfl⟩ : syracuseStep 3444389 = 645823) (by norm_num)
theorem B2584237 : Blo 1530462 2584237 := bbase (se 3 (by rfl) ⟨484544, by rfl⟩ : syracuseStep 2584237 = 969089) (by norm_num)
theorem B2297525 : Blo 1530462 2297525 := bbase (se 5 (by rfl) ⟨107696, by rfl⟩ : syracuseStep 2297525 = 215393) (by norm_num)
theorem B4419269 : Blo 1530462 4419269 := bbase (se 4 (by rfl) ⟨414306, by rfl⟩ : syracuseStep 4419269 = 828613) (by norm_num)
theorem B2297549 : Blo 1530462 2297549 := bbase (se 3 (by rfl) ⟨430790, by rfl⟩ : syracuseStep 2297549 = 861581) (by norm_num)
theorem B19615445 : Blo 1530462 19615445 := bbase (se 7 (by rfl) ⟨229868, by rfl⟩ : syracuseStep 19615445 = 459737) (by norm_num)
theorem B1937125 : Blo 1530462 1937125 := bbase (se 4 (by rfl) ⟨181605, by rfl⟩ : syracuseStep 1937125 = 363211) (by norm_num)
theorem B2297573 : Blo 1530462 2297573 := bbase (se 4 (by rfl) ⟨215397, by rfl⟩ : syracuseStep 2297573 = 430795) (by norm_num)
theorem B3444461 : Blo 1530462 3444461 := bbase (se 3 (by rfl) ⟨645836, by rfl⟩ : syracuseStep 3444461 = 1291673) (by norm_num)
theorem B2297597 : Blo 1530462 2297597 := bbase (se 3 (by rfl) ⟨430799, by rfl⟩ : syracuseStep 2297597 = 861599) (by norm_num)
theorem B2584325 : Blo 1530462 2584325 := bbase (se 4 (by rfl) ⟨242280, by rfl⟩ : syracuseStep 2584325 = 484561) (by norm_num)
theorem B3731213 : Blo 1530462 3731213 := bbase (se 3 (by rfl) ⟨699602, by rfl⟩ : syracuseStep 3731213 = 1399205) (by norm_num)
theorem B2297621 : Blo 1530462 2297621 := bbase (se 6 (by rfl) ⟨53850, by rfl⟩ : syracuseStep 2297621 = 107701) (by norm_num)
theorem B10481429 : Blo 1530462 10481429 := bbase (se 6 (by rfl) ⟨245658, by rfl⟩ : syracuseStep 10481429 = 491317) (by norm_num)
theorem B2297645 : Blo 1530462 2297645 := bbase (se 3 (by rfl) ⟨430808, by rfl⟩ : syracuseStep 2297645 = 861617) (by norm_num)
theorem B3444533 : Blo 1530462 3444533 := bbase (se 5 (by rfl) ⟨161462, by rfl⟩ : syracuseStep 3444533 = 322925) (by norm_num)
theorem B2297669 : Blo 1530462 2297669 := bbase (se 4 (by rfl) ⟨215406, by rfl⟩ : syracuseStep 2297669 = 430813) (by norm_num)
theorem B3878725 : Blo 1530462 3878725 := bbase (se 4 (by rfl) ⟨363630, by rfl⟩ : syracuseStep 3878725 = 727261) (by norm_num)
theorem B2297693 : Blo 1530462 2297693 := bbase (se 3 (by rfl) ⟨430817, by rfl⟩ : syracuseStep 2297693 = 861635) (by norm_num)
theorem B2297717 : Blo 1530462 2297717 := bbase (se 5 (by rfl) ⟨107705, by rfl⟩ : syracuseStep 2297717 = 215411) (by norm_num)
theorem B3444605 : Blo 1530462 3444605 := bbase (se 3 (by rfl) ⟨645863, by rfl⟩ : syracuseStep 3444605 = 1291727) (by norm_num)
theorem B2584453 : Blo 1530462 2584453 := bbase (se 4 (by rfl) ⟨242292, by rfl⟩ : syracuseStep 2584453 = 484585) (by norm_num)
theorem B2297741 : Blo 1530462 2297741 := bbase (se 3 (by rfl) ⟨430826, by rfl⟩ : syracuseStep 2297741 = 861653) (by norm_num)
theorem B1937297 : Blo 1530462 1937297 := bbase (se 2 (by rfl) ⟨726486, by rfl⟩ : syracuseStep 1937297 = 1452973) (by norm_num)
theorem B2297765 : Blo 1530462 2297765 := bbase (se 4 (by rfl) ⟨215415, by rfl⟩ : syracuseStep 2297765 = 430831) (by norm_num)
theorem B3878837 : Blo 1530462 3878837 := bbase (se 5 (by rfl) ⟨181820, by rfl⟩ : syracuseStep 3878837 = 363641) (by norm_num)
theorem B2297789 : Blo 1530462 2297789 := bbase (se 3 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 2297789 = 861671) (by norm_num)
theorem B3444677 : Blo 1530462 3444677 := bbase (se 4 (by rfl) ⟨322938, by rfl⟩ : syracuseStep 3444677 = 645877) (by norm_num)
theorem B1937353 : Blo 1530462 1937353 := bbase (se 2 (by rfl) ⟨726507, by rfl⟩ : syracuseStep 1937353 = 1453015) (by norm_num)
theorem B5812181 : Blo 1530462 5812181 := bbase (se 7 (by rfl) ⟨68111, by rfl⟩ : syracuseStep 5812181 = 136223) (by norm_num)
theorem B2297813 : Blo 1530462 2297813 := bbase (se 7 (by rfl) ⟨26927, by rfl⟩ : syracuseStep 2297813 = 53855) (by norm_num)
theorem B2584541 : Blo 1530462 2584541 := bbase (se 3 (by rfl) ⟨484601, by rfl⟩ : syracuseStep 2584541 = 969203) (by norm_num)
theorem B2297837 : Blo 1530462 2297837 := bbase (se 3 (by rfl) ⟨430844, by rfl⟩ : syracuseStep 2297837 = 861689) (by norm_num)
theorem B4362245 : Blo 1530462 4362245 := bbase (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) (by norm_num)
theorem B2297861 : Blo 1530462 2297861 := bbase (se 4 (by rfl) ⟨215424, by rfl⟩ : syracuseStep 2297861 = 430849) (by norm_num)
theorem B3444749 : Blo 1530462 3444749 := bbase (se 3 (by rfl) ⟨645890, by rfl⟩ : syracuseStep 3444749 = 1291781) (by norm_num)
theorem B2297885 : Blo 1530462 2297885 := bbase (se 3 (by rfl) ⟨430853, by rfl⟩ : syracuseStep 2297885 = 861707) (by norm_num)
theorem B1937449 : Blo 1530462 1937449 := bbase (se 2 (by rfl) ⟨726543, by rfl⟩ : syracuseStep 1937449 = 1453087) (by norm_num)
theorem B2297909 : Blo 1530462 2297909 := bbase (se 5 (by rfl) ⟨107714, by rfl⟩ : syracuseStep 2297909 = 215429) (by norm_num)
theorem B1839169 : Blo 1530462 1839169 := bbase (se 2 (by rfl) ⟨689688, by rfl⟩ : syracuseStep 1839169 = 1379377) (by norm_num)
theorem B2297933 : Blo 1530462 2297933 := bbase (se 3 (by rfl) ⟨430862, by rfl⟩ : syracuseStep 2297933 = 861725) (by norm_num)
theorem B3444821 : Blo 1530462 3444821 := bbase (se 8 (by rfl) ⟨20184, by rfl⟩ : syracuseStep 3444821 = 40369) (by norm_num)
theorem B2584669 : Blo 1530462 2584669 := bbase (se 3 (by rfl) ⟨484625, by rfl⟩ : syracuseStep 2584669 = 969251) (by norm_num)
theorem B2297957 : Blo 1530462 2297957 := bbase (se 4 (by rfl) ⟨215433, by rfl⟩ : syracuseStep 2297957 = 430867) (by norm_num)
theorem B3879029 : Blo 1530462 3879029 := bbase (se 5 (by rfl) ⟨181829, by rfl⟩ : syracuseStep 3879029 = 363659) (by norm_num)
theorem B1863805 : Blo 1530462 1863805 := bbase (se 3 (by rfl) ⟨349463, by rfl⟩ : syracuseStep 1863805 = 698927) (by norm_num)
theorem B2297981 : Blo 1530462 2297981 := bbase (se 3 (by rfl) ⟨430871, by rfl⟩ : syracuseStep 2297981 = 861743) (by norm_num)
theorem B3494021 : Blo 1530462 3494021 := bbase (se 4 (by rfl) ⟨327564, by rfl⟩ : syracuseStep 3494021 = 655129) (by norm_num)
theorem B2298005 : Blo 1530462 2298005 := bbase (se 6 (by rfl) ⟨53859, by rfl⟩ : syracuseStep 2298005 = 107719) (by norm_num)
theorem B3444893 : Blo 1530462 3444893 := bbase (se 3 (by rfl) ⟨645917, by rfl⟩ : syracuseStep 3444893 = 1291835) (by norm_num)
theorem B2298029 : Blo 1530462 2298029 := bbase (se 3 (by rfl) ⟨430880, by rfl⟩ : syracuseStep 2298029 = 861761) (by norm_num)
theorem B4657333 : Blo 1530462 4657333 := bbase (se 5 (by rfl) ⟨218312, by rfl⟩ : syracuseStep 4657333 = 436625) (by norm_num)
theorem B2584757 : Blo 1530462 2584757 := bbase (se 5 (by rfl) ⟨121160, by rfl⟩ : syracuseStep 2584757 = 242321) (by norm_num)
theorem B2298053 : Blo 1530462 2298053 := bbase (se 4 (by rfl) ⟨215442, by rfl⟩ : syracuseStep 2298053 = 430885) (by norm_num)
theorem B1937621 : Blo 1530462 1937621 := bbase (se 7 (by rfl) ⟨22706, by rfl⟩ : syracuseStep 1937621 = 45413) (by norm_num)
theorem B2298077 : Blo 1530462 2298077 := bbase (se 3 (by rfl) ⟨430889, by rfl⟩ : syracuseStep 2298077 = 861779) (by norm_num)
theorem B3444965 : Blo 1530462 3444965 := bbase (se 4 (by rfl) ⟨322965, by rfl⟩ : syracuseStep 3444965 = 645931) (by norm_num)
theorem B5812469 : Blo 1530462 5812469 := bbase (se 5 (by rfl) ⟨272459, by rfl⟩ : syracuseStep 5812469 = 544919) (by norm_num)
theorem B8392949 : Blo 1530462 8392949 := bbase (se 5 (by rfl) ⟨393419, by rfl⟩ : syracuseStep 8392949 = 786839) (by norm_num)
theorem B2298101 : Blo 1530462 2298101 := bbase (se 5 (by rfl) ⟨107723, by rfl⟩ : syracuseStep 2298101 = 215447) (by norm_num)
theorem B1937677 : Blo 1530462 1937677 := bbase (se 3 (by rfl) ⟨363314, by rfl⟩ : syracuseStep 1937677 = 726629) (by norm_num)
theorem B2298125 : Blo 1530462 2298125 := bbase (se 3 (by rfl) ⟨430898, by rfl⟩ : syracuseStep 2298125 = 861797) (by norm_num)
theorem B2453789 : Blo 1530462 2453789 := bbase (se 3 (by rfl) ⟨460085, by rfl⟩ : syracuseStep 2453789 = 920171) (by norm_num)
theorem B2298149 : Blo 1530462 2298149 := bbase (se 4 (by rfl) ⟨215451, by rfl⟩ : syracuseStep 2298149 = 430903) (by norm_num)
theorem B3445037 : Blo 1530462 3445037 := bbase (se 3 (by rfl) ⟨645944, by rfl⟩ : syracuseStep 3445037 = 1291889) (by norm_num)
theorem B2584885 : Blo 1530462 2584885 := bbase (se 5 (by rfl) ⟨121166, by rfl⟩ : syracuseStep 2584885 = 242333) (by norm_num)
theorem B2298173 : Blo 1530462 2298173 := bbase (se 3 (by rfl) ⟨430907, by rfl⟩ : syracuseStep 2298173 = 861815) (by norm_num)
theorem B1634629 : Blo 1530462 1634629 := bbase (se 4 (by rfl) ⟨153246, by rfl⟩ : syracuseStep 1634629 = 306493) (by norm_num)
theorem B2298197 : Blo 1530462 2298197 := bbase (se 10 (by rfl) ⟨3366, by rfl⟩ : syracuseStep 2298197 = 6733) (by norm_num)
theorem B1937773 : Blo 1530462 1937773 := bbase (se 3 (by rfl) ⟨363332, by rfl⟩ : syracuseStep 1937773 = 726665) (by norm_num)
theorem B2298221 : Blo 1530462 2298221 := bbase (se 3 (by rfl) ⟨430916, by rfl⟩ : syracuseStep 2298221 = 861833) (by norm_num)
theorem B3445109 : Blo 1530462 3445109 := bbase (se 5 (by rfl) ⟨161489, by rfl⟩ : syracuseStep 3445109 = 322979) (by norm_num)
theorem B9318773 : Blo 1530462 9318773 := bbase (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) (by norm_num)
theorem B1634689 : Blo 1530462 1634689 := bbase (se 2 (by rfl) ⟨613008, by rfl⟩ : syracuseStep 1634689 = 1226017) (by norm_num)
theorem B2298245 : Blo 1530462 2298245 := bbase (se 4 (by rfl) ⟨215460, by rfl⟩ : syracuseStep 2298245 = 430921) (by norm_num)
theorem B2584973 : Blo 1530462 2584973 := bbase (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) (by norm_num)
theorem B2453917 : Blo 1530462 2453917 := bbase (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) (by norm_num)
theorem B2298269 : Blo 1530462 2298269 := bbase (se 3 (by rfl) ⟨430925, by rfl⟩ : syracuseStep 2298269 = 861851) (by norm_num)
theorem B5165477 : Blo 1530462 5165477 := bbase (se 4 (by rfl) ⟨484263, by rfl⟩ : syracuseStep 5165477 = 968527) (by norm_num)
theorem B2298293 : Blo 1530462 2298293 := bbase (se 5 (by rfl) ⟨107732, by rfl⟩ : syracuseStep 2298293 = 215465) (by norm_num)
theorem B3445181 : Blo 1530462 3445181 := bbase (se 3 (by rfl) ⟨645971, by rfl⟩ : syracuseStep 3445181 = 1291943) (by norm_num)
theorem B2298317 : Blo 1530462 2298317 := bbase (se 3 (by rfl) ⟨430934, by rfl⟩ : syracuseStep 2298317 = 861869) (by norm_num)
theorem B2453981 : Blo 1530462 2453981 := bbase (se 3 (by rfl) ⟨460121, by rfl⟩ : syracuseStep 2453981 = 920243) (by norm_num)
theorem B2298341 : Blo 1530462 2298341 := bbase (se 4 (by rfl) ⟨215469, by rfl⟩ : syracuseStep 2298341 = 430939) (by norm_num)
theorem B2298365 : Blo 1530462 2298365 := bbase (se 3 (by rfl) ⟨430943, by rfl⟩ : syracuseStep 2298365 = 861887) (by norm_num)
theorem B3445253 : Blo 1530462 3445253 := bbase (se 4 (by rfl) ⟨322992, by rfl⟩ : syracuseStep 3445253 = 645985) (by norm_num)
theorem B2585101 : Blo 1530462 2585101 := bbase (se 3 (by rfl) ⟨484706, by rfl⟩ : syracuseStep 2585101 = 969413) (by norm_num)
theorem B2298389 : Blo 1530462 2298389 := bbase (se 6 (by rfl) ⟨53868, by rfl⟩ : syracuseStep 2298389 = 107737) (by norm_num)
theorem B1937945 : Blo 1530462 1937945 := bbase (se 2 (by rfl) ⟨726729, by rfl⟩ : syracuseStep 1937945 = 1453459) (by norm_num)
theorem B2298413 : Blo 1530462 2298413 := bbase (se 3 (by rfl) ⟨430952, by rfl⟩ : syracuseStep 2298413 = 861905) (by norm_num)
theorem B2298437 : Blo 1530462 2298437 := bbase (se 4 (by rfl) ⟨215478, by rfl⟩ : syracuseStep 2298437 = 430957) (by norm_num)
theorem B3445325 : Blo 1530462 3445325 := bbase (se 3 (by rfl) ⟨645998, by rfl⟩ : syracuseStep 3445325 = 1291997) (by norm_num)
theorem B1938001 : Blo 1530462 1938001 := bbase (se 2 (by rfl) ⟨726750, by rfl⟩ : syracuseStep 1938001 = 1453501) (by norm_num)
theorem B9810517 : Blo 1530462 9810517 := bbase (se 8 (by rfl) ⟨57483, by rfl⟩ : syracuseStep 9810517 = 114967) (by norm_num)
theorem B2298461 : Blo 1530462 2298461 := bbase (se 3 (by rfl) ⟨430961, by rfl⟩ : syracuseStep 2298461 = 861923) (by norm_num)
theorem B2585189 : Blo 1530462 2585189 := bbase (se 4 (by rfl) ⟨242361, by rfl⟩ : syracuseStep 2585189 = 484723) (by norm_num)
theorem B2298485 : Blo 1530462 2298485 := bbase (se 5 (by rfl) ⟨107741, by rfl⟩ : syracuseStep 2298485 = 215483) (by norm_num)
theorem B2298509 : Blo 1530462 2298509 := bbase (se 3 (by rfl) ⟨430970, by rfl⟩ : syracuseStep 2298509 = 861941) (by norm_num)
theorem B3445397 : Blo 1530462 3445397 := bbase (se 6 (by rfl) ⟨80751, by rfl⟩ : syracuseStep 3445397 = 161503) (by norm_num)
theorem B17453717 : Blo 1530462 17453717 := bbase (se 6 (by rfl) ⟨409071, by rfl⟩ : syracuseStep 17453717 = 818143) (by norm_num)
theorem B3928733 : Blo 1530462 3928733 := bbase (se 3 (by rfl) ⟨736637, by rfl⟩ : syracuseStep 3928733 = 1473275) (by norm_num)
theorem B2298533 : Blo 1530462 2298533 := bbase (se 4 (by rfl) ⟨215487, by rfl⟩ : syracuseStep 2298533 = 430975) (by norm_num)
theorem B1938097 : Blo 1530462 1938097 := bbase (se 2 (by rfl) ⟨726786, by rfl⟩ : syracuseStep 1938097 = 1453573) (by norm_num)
theorem B1635005 : Blo 1530462 1635005 := bbase (se 3 (by rfl) ⟨306563, by rfl⟩ : syracuseStep 1635005 = 613127) (by norm_num)
theorem B2298557 : Blo 1530462 2298557 := bbase (se 3 (by rfl) ⟨430979, by rfl⟩ : syracuseStep 2298557 = 861959) (by norm_num)
theorem B7754453 : Blo 1530462 7754453 := bbase (se 7 (by rfl) ⟨90872, by rfl⟩ : syracuseStep 7754453 = 181745) (by norm_num)
theorem B2298581 : Blo 1530462 2298581 := bbase (se 7 (by rfl) ⟨26936, by rfl⟩ : syracuseStep 2298581 = 53873) (by norm_num)
theorem B3445469 : Blo 1530462 3445469 := bbase (se 3 (by rfl) ⟨646025, by rfl⟩ : syracuseStep 3445469 = 1292051) (by norm_num)
theorem B2585317 : Blo 1530462 2585317 := bbase (se 4 (by rfl) ⟨242373, by rfl⟩ : syracuseStep 2585317 = 484747) (by norm_num)
theorem B2298605 : Blo 1530462 2298605 := bbase (se 3 (by rfl) ⟨430988, by rfl⟩ : syracuseStep 2298605 = 861977) (by norm_num)
theorem B2487029 : Blo 1530462 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B4362997 : Blo 1530462 4362997 := bbase (se 5 (by rfl) ⟨204515, by rfl⟩ : syracuseStep 4362997 = 409031) (by norm_num)
theorem B2298629 : Blo 1530462 2298629 := bbase (se 4 (by rfl) ⟨215496, by rfl⟩ : syracuseStep 2298629 = 430993) (by norm_num)
theorem B2618141 : Blo 1530462 2618141 := bbase (se 3 (by rfl) ⟨490901, by rfl⟩ : syracuseStep 2618141 = 981803) (by norm_num)
theorem B2298653 : Blo 1530462 2298653 := bbase (se 3 (by rfl) ⟨430997, by rfl⟩ : syracuseStep 2298653 = 861995) (by norm_num)
theorem B3445541 : Blo 1530462 3445541 := bbase (se 4 (by rfl) ⟨323019, by rfl⟩ : syracuseStep 3445541 = 646039) (by norm_num)
theorem B4903733 : Blo 1530462 4903733 := bbase (se 5 (by rfl) ⟨229862, by rfl⟩ : syracuseStep 4903733 = 459725) (by norm_num)
theorem B2298677 : Blo 1530462 2298677 := bbase (se 5 (by rfl) ⟨107750, by rfl⟩ : syracuseStep 2298677 = 215501) (by norm_num)
theorem B2585405 : Blo 1530462 2585405 := bbase (se 3 (by rfl) ⟨484763, by rfl⟩ : syracuseStep 2585405 = 969527) (by norm_num)
theorem B5165909 : Blo 1530462 5165909 := bbase (se 9 (by rfl) ⟨15134, by rfl⟩ : syracuseStep 5165909 = 30269) (by norm_num)
theorem B26178389 : Blo 1530462 26178389 := bbase (se 9 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 26178389 = 153389) (by norm_num)
theorem B1938269 : Blo 1530462 1938269 := bbase (se 3 (by rfl) ⟨363425, by rfl⟩ : syracuseStep 1938269 = 726851) (by norm_num)
theorem B3445613 : Blo 1530462 3445613 := bbase (se 3 (by rfl) ⟨646052, by rfl⟩ : syracuseStep 3445613 = 1292105) (by norm_num)
theorem B1938325 : Blo 1530462 1938325 := bbase (se 6 (by rfl) ⟨45429, by rfl⟩ : syracuseStep 1938325 = 90859) (by norm_num)
theorem B3445685 : Blo 1530462 3445685 := bbase (se 5 (by rfl) ⟨161516, by rfl⟩ : syracuseStep 3445685 = 323033) (by norm_num)
theorem B11629493 : Blo 1530462 11629493 := bbase (se 5 (by rfl) ⟨545132, by rfl⟩ : syracuseStep 11629493 = 1090265) (by norm_num)
theorem B2585533 : Blo 1530462 2585533 := bbase (se 3 (by rfl) ⟨484787, by rfl⟩ : syracuseStep 2585533 = 969575) (by norm_num)
theorem B6542309 : Blo 1530462 6542309 := bbase (se 4 (by rfl) ⟨613341, by rfl⟩ : syracuseStep 6542309 = 1226683) (by norm_num)
theorem B1938421 : Blo 1530462 1938421 := bbase (se 5 (by rfl) ⟨90863, by rfl⟩ : syracuseStep 1938421 = 181727) (by norm_num)
theorem B3445757 : Blo 1530462 3445757 := bbase (se 3 (by rfl) ⟨646079, by rfl⟩ : syracuseStep 3445757 = 1292159) (by norm_num)
theorem B2585621 : Blo 1530462 2585621 := bbase (se 6 (by rfl) ⟨60600, by rfl⟩ : syracuseStep 2585621 = 121201) (by norm_num)
theorem B3445829 : Blo 1530462 3445829 := bbase (se 4 (by rfl) ⟨323046, by rfl⟩ : syracuseStep 3445829 = 646093) (by norm_num)
theorem B2946133 : Blo 1530462 2946133 := bbase (se 8 (by rfl) ⟨17262, by rfl⟩ : syracuseStep 2946133 = 34525) (by norm_num)
theorem B1635449 : Blo 1530462 1635449 := bbase (se 2 (by rfl) ⟨613293, by rfl⟩ : syracuseStep 1635449 = 1226587) (by norm_num)
theorem B3445901 : Blo 1530462 3445901 := bbase (se 3 (by rfl) ⟨646106, by rfl⟩ : syracuseStep 3445901 = 1292213) (by norm_num)
theorem B2585749 : Blo 1530462 2585749 := bbase (se 6 (by rfl) ⟨60603, by rfl⟩ : syracuseStep 2585749 = 121207) (by norm_num)
theorem B1938593 : Blo 1530462 1938593 := bbase (se 2 (by rfl) ⟨726972, by rfl⟩ : syracuseStep 1938593 = 1453945) (by norm_num)
theorem B1635509 : Blo 1530462 1635509 := bbase (se 5 (by rfl) ⟨76664, by rfl⟩ : syracuseStep 1635509 = 153329) (by norm_num)
theorem B3445973 : Blo 1530462 3445973 := bbase (se 7 (by rfl) ⟨40382, by rfl⟩ : syracuseStep 3445973 = 80765) (by norm_num)
theorem B1938649 : Blo 1530462 1938649 := bbase (se 2 (by rfl) ⟨726993, by rfl⟩ : syracuseStep 1938649 = 1453987) (by norm_num)
theorem B1840357 : Blo 1530462 1840357 := bbase (se 4 (by rfl) ⟨172533, by rfl⟩ : syracuseStep 1840357 = 345067) (by norm_num)
theorem B2585837 : Blo 1530462 2585837 := bbase (se 3 (by rfl) ⟨484844, by rfl⟩ : syracuseStep 2585837 = 969689) (by norm_num)
theorem B5166341 : Blo 1530462 5166341 := bbase (se 4 (by rfl) ⟨484344, by rfl⟩ : syracuseStep 5166341 = 968689) (by norm_num)
theorem B3446045 : Blo 1530462 3446045 := bbase (se 3 (by rfl) ⟨646133, by rfl⟩ : syracuseStep 3446045 = 1292267) (by norm_num)
theorem B1635637 : Blo 1530462 1635637 := bbase (se 5 (by rfl) ⟨76670, by rfl⟩ : syracuseStep 1635637 = 153341) (by norm_num)
theorem B1938745 : Blo 1530462 1938745 := bbase (se 2 (by rfl) ⟨727029, by rfl⟩ : syracuseStep 1938745 = 1454059) (by norm_num)
theorem B7460165 : Blo 1530462 7460165 := bbase (se 4 (by rfl) ⟨699390, by rfl⟩ : syracuseStep 7460165 = 1398781) (by norm_num)
theorem B3446117 : Blo 1530462 3446117 := bbase (se 4 (by rfl) ⟨323073, by rfl⟩ : syracuseStep 3446117 = 646147) (by norm_num)
theorem B2585965 : Blo 1530462 2585965 := bbase (se 3 (by rfl) ⟨484868, by rfl⟩ : syracuseStep 2585965 = 969737) (by norm_num)
theorem B5813653 : Blo 1530462 5813653 := bbase (se 6 (by rfl) ⟨136257, by rfl⟩ : syracuseStep 5813653 = 272515) (by norm_num)
theorem B1840549 : Blo 1530462 1840549 := bbase (se 4 (by rfl) ⟨172551, by rfl⟩ : syracuseStep 1840549 = 345103) (by norm_num)
theorem B3446189 : Blo 1530462 3446189 := bbase (se 3 (by rfl) ⟨646160, by rfl⟩ : syracuseStep 3446189 = 1292321) (by norm_num)
theorem B1938917 : Blo 1530462 1938917 := bbase (se 4 (by rfl) ⟨181773, by rfl⟩ : syracuseStep 1938917 = 363547) (by norm_num)
theorem B3446261 : Blo 1530462 3446261 := bbase (se 5 (by rfl) ⟨161543, by rfl⟩ : syracuseStep 3446261 = 323087) (by norm_num)
theorem B1840649 : Blo 1530462 1840649 := bbase (se 2 (by rfl) ⟨690243, by rfl⟩ : syracuseStep 1840649 = 1380487) (by norm_num)
theorem B1938973 : Blo 1530462 1938973 := bbase (se 3 (by rfl) ⟨363557, by rfl⟩ : syracuseStep 1938973 = 727115) (by norm_num)
theorem B3446333 : Blo 1530462 3446333 := bbase (se 3 (by rfl) ⟨646187, by rfl⟩ : syracuseStep 3446333 = 1292375) (by norm_num)
theorem B5240389 : Blo 1530462 5240389 := bbase (se 4 (by rfl) ⟨491286, by rfl⟩ : syracuseStep 5240389 = 982573) (by norm_num)
theorem B2758229 : Blo 1530462 2758229 := bbase (se 8 (by rfl) ⟨16161, by rfl⟩ : syracuseStep 2758229 = 32323) (by norm_num)
theorem B3929717 : Blo 1530462 3929717 := bbase (se 5 (by rfl) ⟨184205, by rfl⟩ : syracuseStep 3929717 = 368411) (by norm_num)
theorem B1939069 : Blo 1530462 1939069 := bbase (se 3 (by rfl) ⟨363575, by rfl⟩ : syracuseStep 1939069 = 727151) (by norm_num)
theorem B2905733 : Blo 1530462 2905733 := bbase (se 4 (by rfl) ⟨272412, by rfl⟩ : syracuseStep 2905733 = 544825) (by norm_num)
theorem B3446405 : Blo 1530462 3446405 := bbase (se 4 (by rfl) ⟨323100, by rfl⟩ : syracuseStep 3446405 = 646201) (by norm_num)
theorem B5166773 : Blo 1530462 5166773 := bbase (se 5 (by rfl) ⟨242192, by rfl⟩ : syracuseStep 5166773 = 484385) (by norm_num)
theorem B5813957 : Blo 1530462 5813957 := bbase (se 4 (by rfl) ⟨545058, by rfl⟩ : syracuseStep 5813957 = 1090117) (by norm_num)
theorem B3446477 : Blo 1530462 3446477 := bbase (se 3 (by rfl) ⟨646214, by rfl⟩ : syracuseStep 3446477 = 1292429) (by norm_num)
theorem B1636081 : Blo 1530462 1636081 := bbase (se 2 (by rfl) ⟨613530, by rfl⟩ : syracuseStep 1636081 = 1227061) (by norm_num)
theorem B3446549 : Blo 1530462 3446549 := bbase (se 6 (by rfl) ⟨80778, by rfl⟩ : syracuseStep 3446549 = 161557) (by norm_num)
theorem B2905885 : Blo 1530462 2905885 := bbase (se 3 (by rfl) ⟨544853, by rfl⟩ : syracuseStep 2905885 = 1089707) (by norm_num)
theorem B1939241 : Blo 1530462 1939241 := bbase (se 2 (by rfl) ⟨727215, by rfl⟩ : syracuseStep 1939241 = 1454431) (by norm_num)
theorem B3446621 : Blo 1530462 3446621 := bbase (se 3 (by rfl) ⟨646241, by rfl⟩ : syracuseStep 3446621 = 1292483) (by norm_num)
theorem B1963873 : Blo 1530462 1963873 := bbase (se 2 (by rfl) ⟨736452, by rfl⟩ : syracuseStep 1963873 = 1472905) (by norm_num)
theorem B1939297 : Blo 1530462 1939297 := bbase (se 2 (by rfl) ⟨727236, by rfl⟩ : syracuseStep 1939297 = 1454473) (by norm_num)
theorem B1636201 : Blo 1530462 1636201 := bbase (se 2 (by rfl) ⟨613575, by rfl⟩ : syracuseStep 1636201 = 1227151) (by norm_num)
theorem B3446693 : Blo 1530462 3446693 := bbase (se 4 (by rfl) ⟨323127, by rfl⟩ : syracuseStep 3446693 = 646255) (by norm_num)
theorem B1939393 : Blo 1530462 1939393 := bbase (se 2 (by rfl) ⟨727272, by rfl⟩ : syracuseStep 1939393 = 1454545) (by norm_num)
theorem B7755749 : Blo 1530462 7755749 := bbase (se 4 (by rfl) ⟨727101, by rfl⟩ : syracuseStep 7755749 = 1454203) (by norm_num)
theorem B3446765 : Blo 1530462 3446765 := bbase (se 3 (by rfl) ⟨646268, by rfl⟩ : syracuseStep 3446765 = 1292537) (by norm_num)
theorem B4421669 : Blo 1530462 4421669 := bbase (se 4 (by rfl) ⟨414531, by rfl⟩ : syracuseStep 4421669 = 829063) (by norm_num)
theorem B3446837 : Blo 1530462 3446837 := bbase (se 5 (by rfl) ⟨161570, by rfl⟩ : syracuseStep 3446837 = 323141) (by norm_num)
theorem B2906189 : Blo 1530462 2906189 := bbase (se 3 (by rfl) ⟨544910, by rfl⟩ : syracuseStep 2906189 = 1089821) (by norm_num)
theorem B18626645 : Blo 1530462 18626645 := bbase (se 8 (by rfl) ⟨109140, by rfl⟩ : syracuseStep 18626645 = 218281) (by norm_num)
theorem B5167205 : Blo 1530462 5167205 := bbase (se 4 (by rfl) ⟨484425, by rfl⟩ : syracuseStep 5167205 = 968851) (by norm_num)
theorem B1636453 : Blo 1530462 1636453 := bbase (se 4 (by rfl) ⟨153417, by rfl⟩ : syracuseStep 1636453 = 306835) (by norm_num)
theorem B1636457 : Blo 1530462 1636457 := bbase (se 2 (by rfl) ⟨613671, by rfl⟩ : syracuseStep 1636457 = 1227343) (by norm_num)
theorem B3446909 : Blo 1530462 3446909 := bbase (se 3 (by rfl) ⟨646295, by rfl⟩ : syracuseStep 3446909 = 1292591) (by norm_num)
theorem B4905157 : Blo 1530462 4905157 := bbase (se 4 (by rfl) ⟨459858, by rfl⟩ : syracuseStep 4905157 = 919717) (by norm_num)
theorem B3446981 : Blo 1530462 3446981 := bbase (se 4 (by rfl) ⟨323154, by rfl⟩ : syracuseStep 3446981 = 646309) (by norm_num)
theorem B6207749 : Blo 1530462 6207749 := bbase (se 4 (by rfl) ⟨581976, by rfl⟩ : syracuseStep 6207749 = 1163953) (by norm_num)
theorem B3447053 : Blo 1530462 3447053 := bbase (se 3 (by rfl) ⟨646322, by rfl⟩ : syracuseStep 3447053 = 1292645) (by norm_num)
theorem B3447125 : Blo 1530462 3447125 := bbase (se 10 (by rfl) ⟨5049, by rfl⟩ : syracuseStep 3447125 = 10099) (by norm_num)
theorem B2070893 : Blo 1530462 2070893 := bbase (se 3 (by rfl) ⟨388292, by rfl⟩ : syracuseStep 2070893 = 776585) (by norm_num)
theorem B1964417 : Blo 1530462 1964417 := bbase (se 2 (by rfl) ⟨736656, by rfl⟩ : syracuseStep 1964417 = 1473313) (by norm_num)
theorem B7747973 : Blo 1530462 7747973 := bbase (se 4 (by rfl) ⟨726372, by rfl⟩ : syracuseStep 7747973 = 1452745) (by norm_num)
theorem B3447197 : Blo 1530462 3447197 := bbase (se 3 (by rfl) ⟨646349, by rfl⟩ : syracuseStep 3447197 = 1292699) (by norm_num)
theorem B3447269 : Blo 1530462 3447269 := bbase (se 4 (by rfl) ⟨323181, by rfl⟩ : syracuseStep 3447269 = 646363) (by norm_num)
theorem B5167637 : Blo 1530462 5167637 := bbase (se 6 (by rfl) ⟨121116, by rfl⟩ : syracuseStep 5167637 = 242233) (by norm_num)
theorem B3447341 : Blo 1530462 3447341 := bbase (se 3 (by rfl) ⟨646376, by rfl⟩ : syracuseStep 3447341 = 1292753) (by norm_num)
theorem B11188853 : Blo 1530462 11188853 := bbase (se 5 (by rfl) ⟨524477, by rfl⟩ : syracuseStep 11188853 = 1048955) (by norm_num)
theorem B3447413 : Blo 1530462 3447413 := bbase (se 5 (by rfl) ⟨161597, by rfl⟩ : syracuseStep 3447413 = 323195) (by norm_num)
theorem B3447485 : Blo 1530462 3447485 := bbase (se 3 (by rfl) ⟨646403, by rfl⟩ : syracuseStep 3447485 = 1292807) (by norm_num)
theorem B5896901 : Blo 1530462 5896901 := bbase (se 4 (by rfl) ⟨552834, by rfl⟩ : syracuseStep 5896901 = 1105669) (by norm_num)
theorem B39770837 : Blo 1530462 39770837 := bbase (se 7 (by rfl) ⟨466064, by rfl⟩ : syracuseStep 39770837 = 932129) (by norm_num)
theorem B3447557 : Blo 1530462 3447557 := bbase (se 4 (by rfl) ⟨323208, by rfl⟩ : syracuseStep 3447557 = 646417) (by norm_num)
theorem B5520149 : Blo 1530462 5520149 := bbase (se 6 (by rfl) ⟨129378, by rfl⟩ : syracuseStep 5520149 = 258757) (by norm_num)
theorem B2906941 : Blo 1530462 2906941 := bbase (se 3 (by rfl) ⟨545051, by rfl⟩ : syracuseStep 2906941 = 1090103) (by norm_num)
theorem B3447629 : Blo 1530462 3447629 := bbase (se 3 (by rfl) ⟨646430, by rfl⟩ : syracuseStep 3447629 = 1292861) (by norm_num)
theorem B3447701 : Blo 1530462 3447701 := bbase (se 6 (by rfl) ⟨80805, by rfl⟩ : syracuseStep 3447701 = 161611) (by norm_num)
theorem B2947997 : Blo 1530462 2947997 := bbase (se 3 (by rfl) ⟨552749, by rfl⟩ : syracuseStep 2947997 = 1105499) (by norm_num)
theorem B5168069 : Blo 1530462 5168069 := bbase (se 4 (by rfl) ⟨484506, by rfl⟩ : syracuseStep 5168069 = 969013) (by norm_num)
theorem B2907085 : Blo 1530462 2907085 := bbase (se 3 (by rfl) ⟨545078, by rfl⟩ : syracuseStep 2907085 = 1090157) (by norm_num)
theorem B7076821 : Blo 1530462 7076821 := bbase (se 7 (by rfl) ⟨82931, by rfl⟩ : syracuseStep 7076821 = 165863) (by norm_num)
theorem B3447773 : Blo 1530462 3447773 := bbase (se 3 (by rfl) ⟨646457, by rfl⟩ : syracuseStep 3447773 = 1292915) (by norm_num)
theorem B3447845 : Blo 1530462 3447845 := bbase (se 4 (by rfl) ⟨323235, by rfl⟩ : syracuseStep 3447845 = 646471) (by norm_num)
theorem B15711317 : Blo 1530462 15711317 := bbase (se 8 (by rfl) ⟨92058, by rfl⟩ : syracuseStep 15711317 = 184117) (by norm_num)
theorem B2907245 : Blo 1530462 2907245 := bbase (se 3 (by rfl) ⟨545108, by rfl⟩ : syracuseStep 2907245 = 1090217) (by norm_num)
theorem B3447917 : Blo 1530462 3447917 := bbase (se 3 (by rfl) ⟨646484, by rfl⟩ : syracuseStep 3447917 = 1292969) (by norm_num)
theorem B3447989 : Blo 1530462 3447989 := bbase (se 5 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 3447989 = 323249) (by norm_num)
theorem B7757045 : Blo 1530462 7757045 := bbase (se 5 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 7757045 = 727223) (by norm_num)
theorem B2907389 : Blo 1530462 2907389 := bbase (se 3 (by rfl) ⟨545135, by rfl⟩ : syracuseStep 2907389 = 1090271) (by norm_num)
theorem B5168501 : Blo 1530462 5168501 := bbase (se 5 (by rfl) ⟨242273, by rfl⟩ : syracuseStep 5168501 = 484547) (by norm_num)
theorem B3874189 : Blo 1530462 3874189 := bbase (se 3 (by rfl) ⟨726410, by rfl⟩ : syracuseStep 3874189 = 1452821) (by norm_num)
theorem B1965485 : Blo 1530462 1965485 := bbase (se 3 (by rfl) ⟨368528, by rfl⟩ : syracuseStep 1965485 = 737057) (by norm_num)
theorem B3980773 : Blo 1530462 3980773 := bbase (se 4 (by rfl) ⟨373197, by rfl⟩ : syracuseStep 3980773 = 746395) (by norm_num)
theorem B5897717 : Blo 1530462 5897717 := bbase (se 5 (by rfl) ⟨276455, by rfl⟩ : syracuseStep 5897717 = 552911) (by norm_num)
theorem B3874301 : Blo 1530462 3874301 := bbase (se 3 (by rfl) ⟨726431, by rfl⟩ : syracuseStep 3874301 = 1452863) (by norm_num)
theorem B1965593 : Blo 1530462 1965593 := bbase (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) (by norm_num)
theorem B2907677 : Blo 1530462 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B2301509 : Blo 1530462 2301509 := bbase (se 4 (by rfl) ⟨215766, by rfl⟩ : syracuseStep 2301509 = 431533) (by norm_num)
theorem B6209141 : Blo 1530462 6209141 := bbase (se 5 (by rfl) ⟨291053, by rfl⟩ : syracuseStep 6209141 = 582107) (by norm_num)
theorem B7749269 : Blo 1530462 7749269 := bbase (se 6 (by rfl) ⟨181623, by rfl⟩ : syracuseStep 7749269 = 363247) (by norm_num)
theorem B2907829 : Blo 1530462 2907829 := bbase (se 5 (by rfl) ⟨136304, by rfl⟩ : syracuseStep 2907829 = 272609) (by norm_num)
theorem B3874493 : Blo 1530462 3874493 := bbase (se 3 (by rfl) ⟨726467, by rfl⟩ : syracuseStep 3874493 = 1452935) (by norm_num)
theorem B4906757 : Blo 1530462 4906757 := bbase (se 4 (by rfl) ⟨460008, by rfl⟩ : syracuseStep 4906757 = 920017) (by norm_num)
theorem B5816069 : Blo 1530462 5816069 := bbase (se 4 (by rfl) ⟨545256, by rfl⟩ : syracuseStep 5816069 = 1090513) (by norm_num)
theorem B5168933 : Blo 1530462 5168933 := bbase (se 4 (by rfl) ⟨484587, by rfl⟩ : syracuseStep 5168933 = 969175) (by norm_num)
theorem B1769293 : Blo 1530462 1769293 := bbase (se 3 (by rfl) ⟨331742, by rfl⟩ : syracuseStep 1769293 = 663485) (by norm_num)
theorem B1965925 : Blo 1530462 1965925 := bbase (se 4 (by rfl) ⟨184305, by rfl⟩ : syracuseStep 1965925 = 368611) (by norm_num)
theorem B3104669 : Blo 1530462 3104669 := bbase (se 3 (by rfl) ⟨582125, by rfl⟩ : syracuseStep 3104669 = 1164251) (by norm_num)
theorem B2908133 : Blo 1530462 2908133 := bbase (se 4 (by rfl) ⟨272637, by rfl⟩ : syracuseStep 2908133 = 545275) (by norm_num)
theorem B2908163 : Blo 1530462 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B1531907 : Blo 1530462 1531907 := bstep (se 1 (by rfl) ⟨1148930, by rfl⟩ : syracuseStep 1531907 = 2297861) B2297861
theorem B1531923 : Blo 1530462 1531923 := bstep (se 1 (by rfl) ⟨1148942, by rfl⟩ : syracuseStep 1531923 = 2297885) B2297885
theorem B1531939 : Blo 1530462 1531939 := bstep (se 1 (by rfl) ⟨1148954, by rfl⟩ : syracuseStep 1531939 = 2297909) B2297909
theorem B1531955 : Blo 1530462 1531955 := bstep (se 1 (by rfl) ⟨1148966, by rfl⟩ : syracuseStep 1531955 = 2297933) B2297933
theorem B1531971 : Blo 1530462 1531971 := bstep (se 1 (by rfl) ⟨1148978, by rfl⟩ : syracuseStep 1531971 = 2297957) B2297957
theorem B1531987 : Blo 1530462 1531987 := bstep (se 1 (by rfl) ⟨1148990, by rfl⟩ : syracuseStep 1531987 = 2297981) B2297981
theorem B1532003 : Blo 1530462 1532003 := bstep (se 1 (by rfl) ⟨1149002, by rfl⟩ : syracuseStep 1532003 = 2298005) B2298005
theorem B1532019 : Blo 1530462 1532019 := bstep (se 1 (by rfl) ⟨1149014, by rfl⟩ : syracuseStep 1532019 = 2298029) B2298029
theorem B1532035 : Blo 1530462 1532035 := bstep (se 1 (by rfl) ⟨1149026, by rfl⟩ : syracuseStep 1532035 = 2298053) B2298053
theorem B1532051 : Blo 1530462 1532051 := bstep (se 1 (by rfl) ⟨1149038, by rfl⟩ : syracuseStep 1532051 = 2298077) B2298077
theorem B3874979 : Blo 1530462 3874979 := bstep (se 1 (by rfl) ⟨2906234, by rfl⟩ : syracuseStep 3874979 = 5812469) B5812469
theorem B5595299 : Blo 1530462 5595299 := bstep (se 1 (by rfl) ⟨4196474, by rfl⟩ : syracuseStep 5595299 = 8392949) B8392949
theorem B1532067 : Blo 1530462 1532067 := bstep (se 1 (by rfl) ⟨1149050, by rfl⟩ : syracuseStep 1532067 = 2298101) B2298101
theorem B1532083 : Blo 1530462 1532083 := bstep (se 1 (by rfl) ⟨1149062, by rfl⟩ : syracuseStep 1532083 = 2298125) B2298125
theorem B1532099 : Blo 1530462 1532099 := bstep (se 1 (by rfl) ⟨1149074, by rfl⟩ : syracuseStep 1532099 = 2298149) B2298149
theorem B1532115 : Blo 1530462 1532115 := bstep (se 1 (by rfl) ⟨1149086, by rfl⟩ : syracuseStep 1532115 = 2298173) B2298173
theorem B1532131 : Blo 1530462 1532131 := bstep (se 1 (by rfl) ⟨1149098, by rfl⟩ : syracuseStep 1532131 = 2298197) B2298197
theorem B6209777 : Blo 1530462 6209777 := bstep (se 2 (by rfl) ⟨2328666, by rfl⟩ : syracuseStep 6209777 = 4657333) B4657333
theorem B1532147 : Blo 1530462 1532147 := bstep (se 1 (by rfl) ⟨1149110, by rfl⟩ : syracuseStep 1532147 = 2298221) B2298221
theorem B1532163 : Blo 1530462 1532163 := bstep (se 1 (by rfl) ⟨1149122, by rfl⟩ : syracuseStep 1532163 = 2298245) B2298245
theorem B1532179 : Blo 1530462 1532179 := bstep (se 1 (by rfl) ⟨1149134, by rfl⟩ : syracuseStep 1532179 = 2298269) B2298269
theorem B1532195 : Blo 1530462 1532195 := bstep (se 1 (by rfl) ⟨1149146, by rfl⟩ : syracuseStep 1532195 = 2298293) B2298293
theorem B1532211 : Blo 1530462 1532211 := bstep (se 1 (by rfl) ⟨1149158, by rfl⟩ : syracuseStep 1532211 = 2298317) B2298317
theorem B1532227 : Blo 1530462 1532227 := bstep (se 1 (by rfl) ⟨1149170, by rfl⟩ : syracuseStep 1532227 = 2298341) B2298341
theorem B1532243 : Blo 1530462 1532243 := bstep (se 1 (by rfl) ⟨1149182, by rfl⟩ : syracuseStep 1532243 = 2298365) B2298365
theorem B1532259 : Blo 1530462 1532259 := bstep (se 1 (by rfl) ⟨1149194, by rfl⟩ : syracuseStep 1532259 = 2298389) B2298389
theorem B1532275 : Blo 1530462 1532275 := bstep (se 1 (by rfl) ⟨1149206, by rfl⟩ : syracuseStep 1532275 = 2298413) B2298413
theorem B1532291 : Blo 1530462 1532291 := bstep (se 1 (by rfl) ⟨1149218, by rfl⟩ : syracuseStep 1532291 = 2298437) B2298437
theorem B1532307 : Blo 1530462 1532307 := bstep (se 1 (by rfl) ⟨1149230, by rfl⟩ : syracuseStep 1532307 = 2298461) B2298461
theorem B1532323 : Blo 1530462 1532323 := bstep (se 1 (by rfl) ⟨1149242, by rfl⟩ : syracuseStep 1532323 = 2298485) B2298485
theorem B5169581 : Blo 1530462 5169581 := bstep (se 3 (by rfl) ⟨969296, by rfl⟩ : syracuseStep 5169581 = 1938593) B1938593
theorem B2179505 : Blo 1530462 2179505 := bstep (se 2 (by rfl) ⟨817314, by rfl⟩ : syracuseStep 2179505 = 1634629) B1634629
theorem B1532339 : Blo 1530462 1532339 := bstep (se 1 (by rfl) ⟨1149254, by rfl⟩ : syracuseStep 1532339 = 2298509) B2298509
theorem B1532355 : Blo 1530462 1532355 := bstep (se 1 (by rfl) ⟨1149266, by rfl⟩ : syracuseStep 1532355 = 2298533) B2298533
theorem B1532371 : Blo 1530462 1532371 := bstep (se 1 (by rfl) ⟨1149278, by rfl⟩ : syracuseStep 1532371 = 2298557) B2298557
theorem B5169635 : Blo 1530462 5169635 := bstep (se 1 (by rfl) ⟨3877226, by rfl⟩ : syracuseStep 5169635 = 7754453) B7754453
theorem B5521891 : Blo 1530462 5521891 := bstep (se 1 (by rfl) ⟨4141418, by rfl⟩ : syracuseStep 5521891 = 8282837) B8282837
theorem B1532387 : Blo 1530462 1532387 := bstep (se 1 (by rfl) ⟨1149290, by rfl⟩ : syracuseStep 1532387 = 2298581) B2298581
theorem B1532403 : Blo 1530462 1532403 := bstep (se 1 (by rfl) ⟨1149302, by rfl⟩ : syracuseStep 1532403 = 2298605) B2298605
theorem B2179585 : Blo 1530462 2179585 := bstep (se 2 (by rfl) ⟨817344, by rfl⟩ : syracuseStep 2179585 = 1634689) B1634689
theorem B1532419 : Blo 1530462 1532419 := bstep (se 1 (by rfl) ⟨1149314, by rfl⟩ : syracuseStep 1532419 = 2298629) B2298629
theorem B1532435 : Blo 1530462 1532435 := bstep (se 1 (by rfl) ⟨1149326, by rfl⟩ : syracuseStep 1532435 = 2298653) B2298653
theorem B8716835 : Blo 1530462 8716835 := bstep (se 1 (by rfl) ⟨6537626, by rfl⟩ : syracuseStep 8716835 = 13075253) B13075253
theorem B6537763 : Blo 1530462 6537763 := bstep (se 1 (by rfl) ⟨4903322, by rfl⟩ : syracuseStep 6537763 = 9806645) B9806645
theorem B3269155 : Blo 1530462 3269155 := bstep (se 1 (by rfl) ⟨2451866, by rfl⟩ : syracuseStep 3269155 = 4903733) B4903733
theorem B1532451 : Blo 1530462 1532451 := bstep (se 1 (by rfl) ⟨1149338, by rfl⟩ : syracuseStep 1532451 = 2298677) B2298677
theorem B4358897 : Blo 1530462 4358897 := bstep (se 2 (by rfl) ⟨1634586, by rfl⟩ : syracuseStep 4358897 = 3269173) B3269173
theorem B5169905 : Blo 1530462 5169905 := bstep (se 2 (by rfl) ⟨1938714, by rfl⟩ : syracuseStep 5169905 = 3877429) B3877429
theorem B19612469 : Blo 1530462 19612469 := bstep (se 5 (by rfl) ⟨919334, by rfl⟩ : syracuseStep 19612469 = 1838669) B1838669
theorem B4973443 : Blo 1530462 4973443 := bstep (se 1 (by rfl) ⟨3730082, by rfl⟩ : syracuseStep 4973443 = 7460165) B7460165
theorem B2909105 : Blo 1530462 2909105 := bstep (se 2 (by rfl) ⟨1090914, by rfl⟩ : syracuseStep 2909105 = 2181829) B2181829
theorem B5522381 : Blo 1530462 5522381 := bstep (se 3 (by rfl) ⟨1035446, by rfl⟩ : syracuseStep 5522381 = 2070893) B2070893
theorem B2098129 : Blo 1530462 2098129 := bstep (se 2 (by rfl) ⟨786798, by rfl⟩ : syracuseStep 2098129 = 1573597) B1573597
theorem B5817329 : Blo 1530462 5817329 := bstep (se 2 (by rfl) ⟨2181498, by rfl⟩ : syracuseStep 5817329 = 4362997) B4362997
theorem B3875921 : Blo 1530462 3875921 := bstep (se 2 (by rfl) ⟨1453470, by rfl⟩ : syracuseStep 3875921 = 2906941) B2906941
theorem B3875971 : Blo 1530462 3875971 := bstep (se 1 (by rfl) ⟨2906978, by rfl⟩ : syracuseStep 3875971 = 5813957) B5813957
theorem B6210701 : Blo 1530462 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B8725765 : Blo 1530462 8725765 := bstep (se 4 (by rfl) ⟨818040, by rfl⟩ : syracuseStep 8725765 = 1636081) B1636081
theorem B5170445 : Blo 1530462 5170445 := bstep (se 3 (by rfl) ⟨969458, by rfl⟩ : syracuseStep 5170445 = 1938917) B1938917
theorem B3876113 : Blo 1530462 3876113 := bstep (se 2 (by rfl) ⟨1453542, by rfl⟩ : syracuseStep 3876113 = 2907085) B2907085
theorem B2180371 : Blo 1530462 2180371 := bstep (se 1 (by rfl) ⟨1635278, by rfl⟩ : syracuseStep 2180371 = 3270557) B3270557
theorem B5170499 : Blo 1530462 5170499 := bstep (se 1 (by rfl) ⟨3877874, by rfl⟩ : syracuseStep 5170499 = 7755749) B7755749
theorem B4359683 : Blo 1530462 4359683 := bstep (se 1 (by rfl) ⟨3269762, by rfl⟩ : syracuseStep 4359683 = 6539525) B6539525
theorem B4138499 : Blo 1530462 4138499 := bstep (se 1 (by rfl) ⟨3103874, by rfl⟩ : syracuseStep 4138499 = 6207749) B6207749
theorem B1721875 : Blo 1530462 1721875 := bstep (se 1 (by rfl) ⟨1291406, by rfl⟩ : syracuseStep 1721875 = 2582813) B2582813
theorem B37242389 : Blo 1530462 37242389 := bstep (se 6 (by rfl) ⟨872868, by rfl⟩ : syracuseStep 37242389 = 1745737) B1745737
theorem B2328113 : Blo 1530462 2328113 := bstep (se 2 (by rfl) ⟨873042, by rfl⟩ : syracuseStep 2328113 = 1746085) B1746085
theorem B5170769 : Blo 1530462 5170769 := bstep (se 2 (by rfl) ⟨1939038, by rfl⟩ : syracuseStep 5170769 = 3878077) B3878077
theorem B16557709 : Blo 1530462 16557709 := bstep (se 3 (by rfl) ⟨3104570, by rfl⟩ : syracuseStep 16557709 = 6209141) B6209141
theorem B1722019 : Blo 1530462 1722019 := bstep (se 1 (by rfl) ⟨1291514, by rfl⟩ : syracuseStep 1722019 = 2583029) B2583029
theorem B3270385 : Blo 1530462 3270385 := bstep (se 2 (by rfl) ⟨1226394, by rfl⟩ : syracuseStep 3270385 = 2452789) B2452789
theorem B2180849 : Blo 1530462 2180849 := bstep (se 2 (by rfl) ⟨817818, by rfl⟩ : syracuseStep 2180849 = 1635637) B1635637
theorem B1722163 : Blo 1530462 1722163 := bstep (se 1 (by rfl) ⟨1291622, by rfl⟩ : syracuseStep 1722163 = 2583245) B2583245
theorem B4360013 : Blo 1530462 4360013 := bstep (se 3 (by rfl) ⟨817502, by rfl⟩ : syracuseStep 4360013 = 1635005) B1635005
theorem B3680099 : Blo 1530462 3680099 := bstep (se 1 (by rfl) ⟨2760074, by rfl⟩ : syracuseStep 3680099 = 5520149) B5520149
theorem B2180963 : Blo 1530462 2180963 := bstep (se 1 (by rfl) ⟨1635722, by rfl⟩ : syracuseStep 2180963 = 3271445) B3271445
theorem B7751537 : Blo 1530462 7751537 := bstep (se 2 (by rfl) ⟨2906826, by rfl⟩ : syracuseStep 7751537 = 5813653) B5813653
theorem B8284045 : Blo 1530462 8284045 := bstep (se 3 (by rfl) ⟨1553258, by rfl⟩ : syracuseStep 8284045 = 3106517) B3106517
theorem B4360081 : Blo 1530462 4360081 := bstep (se 2 (by rfl) ⟨1635030, by rfl⟩ : syracuseStep 4360081 = 3270061) B3270061
theorem B2295713 : Blo 1530462 2295713 := bstep (se 2 (by rfl) ⟨860892, by rfl⟩ : syracuseStep 2295713 = 1721785) B1721785
theorem B2295731 : Blo 1530462 2295731 := bstep (se 1 (by rfl) ⟨1721798, by rfl⟩ : syracuseStep 2295731 = 3443597) B3443597
theorem B2181043 : Blo 1530462 2181043 := bstep (se 1 (by rfl) ⟨1635782, by rfl⟩ : syracuseStep 2181043 = 3271565) B3271565
theorem B1722307 : Blo 1530462 1722307 := bstep (se 1 (by rfl) ⟨1291730, by rfl⟩ : syracuseStep 1722307 = 2583461) B2583461
theorem B2295761 : Blo 1530462 2295761 := bstep (se 2 (by rfl) ⟨860910, by rfl⟩ : syracuseStep 2295761 = 1721821) B1721821
theorem B2295779 : Blo 1530462 2295779 := bstep (se 1 (by rfl) ⟨1721834, by rfl⟩ : syracuseStep 2295779 = 3443669) B3443669
theorem B2295809 : Blo 1530462 2295809 := bstep (se 2 (by rfl) ⟨860928, by rfl⟩ : syracuseStep 2295809 = 1721857) B1721857
theorem B13084685 : Blo 1530462 13084685 := bstep (se 3 (by rfl) ⟨2453378, by rfl⟩ : syracuseStep 13084685 = 4906757) B4906757
theorem B2295827 : Blo 1530462 2295827 := bstep (se 1 (by rfl) ⟨1721870, by rfl⟩ : syracuseStep 2295827 = 3443741) B3443741
theorem B8276003 : Blo 1530462 8276003 := bstep (se 1 (by rfl) ⟨6207002, by rfl⟩ : syracuseStep 8276003 = 12414005) B12414005
theorem B2295857 : Blo 1530462 2295857 := bstep (se 2 (by rfl) ⟨860946, by rfl⟩ : syracuseStep 2295857 = 1721893) B1721893
theorem B2451521 : Blo 1530462 2451521 := bstep (se 2 (by rfl) ⟨919320, by rfl⟩ : syracuseStep 2451521 = 1838641) B1838641
theorem B2295875 : Blo 1530462 2295875 := bstep (se 1 (by rfl) ⟨1721906, by rfl⟩ : syracuseStep 2295875 = 3443813) B3443813
theorem B6981709 : Blo 1530462 6981709 := bstep (se 3 (by rfl) ⟨1309070, by rfl⟩ : syracuseStep 6981709 = 2618141) B2618141
theorem B1722451 : Blo 1530462 1722451 := bstep (se 1 (by rfl) ⟨1291838, by rfl⟩ : syracuseStep 1722451 = 2583677) B2583677
theorem B2295905 : Blo 1530462 2295905 := bstep (se 2 (by rfl) ⟨860964, by rfl⟩ : syracuseStep 2295905 = 1721929) B1721929
theorem B5171309 : Blo 1530462 5171309 := bstep (se 3 (by rfl) ⟨969620, by rfl⟩ : syracuseStep 5171309 = 1939241) B1939241
theorem B2295923 : Blo 1530462 2295923 := bstep (se 1 (by rfl) ⟨1721942, by rfl⟩ : syracuseStep 2295923 = 3443885) B3443885
theorem B2295953 : Blo 1530462 2295953 := bstep (se 2 (by rfl) ⟨860982, by rfl⟩ : syracuseStep 2295953 = 1721965) B1721965
theorem B2295971 : Blo 1530462 2295971 := bstep (se 1 (by rfl) ⟨1721978, by rfl⟩ : syracuseStep 2295971 = 3443957) B3443957
theorem B4360355 : Blo 1530462 4360355 := bstep (se 1 (by rfl) ⟨3270266, by rfl⟩ : syracuseStep 4360355 = 6540533) B6540533
theorem B5171363 : Blo 1530462 5171363 := bstep (se 1 (by rfl) ⟨3878522, by rfl⟩ : syracuseStep 5171363 = 7757045) B7757045
theorem B2582705 : Blo 1530462 2582705 := bstep (se 2 (by rfl) ⟨968514, by rfl⟩ : syracuseStep 2582705 = 1937029) B1937029
theorem B2296001 : Blo 1530462 2296001 := bstep (se 2 (by rfl) ⟨861000, by rfl⟩ : syracuseStep 2296001 = 1722001) B1722001
theorem B2296019 : Blo 1530462 2296019 := bstep (se 1 (by rfl) ⟨1722014, by rfl⟩ : syracuseStep 2296019 = 3444029) B3444029
theorem B1722595 : Blo 1530462 1722595 := bstep (se 1 (by rfl) ⟨1291946, by rfl⟩ : syracuseStep 1722595 = 2583893) B2583893
theorem B2296049 : Blo 1530462 2296049 := bstep (se 2 (by rfl) ⟨861018, by rfl⟩ : syracuseStep 2296049 = 1722037) B1722037
theorem B3877105 : Blo 1530462 3877105 := bstep (se 2 (by rfl) ⟨1453914, by rfl⟩ : syracuseStep 3877105 = 2907829) B2907829
theorem B2296067 : Blo 1530462 2296067 := bstep (se 1 (by rfl) ⟨1722050, by rfl⟩ : syracuseStep 2296067 = 3444101) B3444101
theorem B2296097 : Blo 1530462 2296097 := bstep (se 2 (by rfl) ⟨861036, by rfl⟩ : syracuseStep 2296097 = 1722073) B1722073
theorem B2582833 : Blo 1530462 2582833 := bstep (se 2 (by rfl) ⟨968562, by rfl⟩ : syracuseStep 2582833 = 1937125) B1937125
theorem B2296115 : Blo 1530462 2296115 := bstep (se 1 (by rfl) ⟨1722086, by rfl⟩ : syracuseStep 2296115 = 3444173) B3444173
theorem B2296145 : Blo 1530462 2296145 := bstep (se 2 (by rfl) ⟨861054, by rfl⟩ : syracuseStep 2296145 = 1722109) B1722109
theorem B2582867 : Blo 1530462 2582867 := bstep (se 1 (by rfl) ⟨1937150, by rfl⟩ : syracuseStep 2582867 = 3874301) B3874301
theorem B2296163 : Blo 1530462 2296163 := bstep (se 1 (by rfl) ⟨1722122, by rfl⟩ : syracuseStep 2296163 = 3444245) B3444245
theorem B1722739 : Blo 1530462 1722739 := bstep (se 1 (by rfl) ⟨1292054, by rfl⟩ : syracuseStep 1722739 = 2584109) B2584109
theorem B2296193 : Blo 1530462 2296193 := bstep (se 2 (by rfl) ⟨861072, by rfl⟩ : syracuseStep 2296193 = 1722145) B1722145
theorem B1534339 : Blo 1530462 1534339 := bstep (se 1 (by rfl) ⟨1150754, by rfl⟩ : syracuseStep 1534339 = 2301509) B2301509
theorem B2296211 : Blo 1530462 2296211 := bstep (se 1 (by rfl) ⟨1722158, by rfl⟩ : syracuseStep 2296211 = 3444317) B3444317
theorem B2296241 : Blo 1530462 2296241 := bstep (se 2 (by rfl) ⟨861090, by rfl⟩ : syracuseStep 2296241 = 1722181) B1722181
theorem B5171633 : Blo 1530462 5171633 := bstep (se 2 (by rfl) ⟨1939362, by rfl⟩ : syracuseStep 5171633 = 3878725) B3878725
theorem B2296259 : Blo 1530462 2296259 := bstep (se 1 (by rfl) ⟨1722194, by rfl⟩ : syracuseStep 2296259 = 3444389) B3444389
theorem B2582995 : Blo 1530462 2582995 := bstep (se 1 (by rfl) ⟨1937246, by rfl⟩ : syracuseStep 2582995 = 3874493) B3874493
theorem B2296289 : Blo 1530462 2296289 := bstep (se 2 (by rfl) ⟨861108, by rfl⟩ : syracuseStep 2296289 = 1722217) B1722217
theorem B2181601 : Blo 1530462 2181601 := bstep (se 2 (by rfl) ⟨818100, by rfl⟩ : syracuseStep 2181601 = 1636201) B1636201
theorem B13076963 : Blo 1530462 13076963 := bstep (se 1 (by rfl) ⟨9807722, by rfl⟩ : syracuseStep 13076963 = 19615445) B19615445
theorem B2296307 : Blo 1530462 2296307 := bstep (se 1 (by rfl) ⟨1722230, by rfl⟩ : syracuseStep 2296307 = 3444461) B3444461
theorem B1722883 : Blo 1530462 1722883 := bstep (se 1 (by rfl) ⟨1292162, by rfl⟩ : syracuseStep 1722883 = 2584325) B2584325
theorem B3877379 : Blo 1530462 3877379 := bstep (se 1 (by rfl) ⟨2908034, by rfl⟩ : syracuseStep 3877379 = 5816069) B5816069
theorem B2296337 : Blo 1530462 2296337 := bstep (se 2 (by rfl) ⟨861126, by rfl⟩ : syracuseStep 2296337 = 1722253) B1722253
theorem B2296355 : Blo 1530462 2296355 := bstep (se 1 (by rfl) ⟨1722266, by rfl⟩ : syracuseStep 2296355 = 3444533) B3444533
theorem B26528309 : Blo 1530462 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B2296385 : Blo 1530462 2296385 := bstep (se 2 (by rfl) ⟨861144, by rfl⟩ : syracuseStep 2296385 = 1722289) B1722289
theorem B2296403 : Blo 1530462 2296403 := bstep (se 1 (by rfl) ⟨1722302, by rfl⟩ : syracuseStep 2296403 = 3444605) B3444605
theorem B2583137 : Blo 1530462 2583137 := bstep (se 2 (by rfl) ⟨968676, by rfl⟩ : syracuseStep 2583137 = 1937353) B1937353
theorem B2296433 : Blo 1530462 2296433 := bstep (se 2 (by rfl) ⟨861162, by rfl⟩ : syracuseStep 2296433 = 1722325) B1722325
theorem B2296451 : Blo 1530462 2296451 := bstep (se 1 (by rfl) ⟨1722338, by rfl⟩ : syracuseStep 2296451 = 3444677) B3444677
theorem B1723027 : Blo 1530462 1723027 := bstep (se 1 (by rfl) ⟨1292270, by rfl⟩ : syracuseStep 1723027 = 2584541) B2584541
theorem B2296481 : Blo 1530462 2296481 := bstep (se 2 (by rfl) ⟨861180, by rfl⟩ : syracuseStep 2296481 = 1722361) B1722361
theorem B2296499 : Blo 1530462 2296499 := bstep (se 1 (by rfl) ⟨1722374, by rfl⟩ : syracuseStep 2296499 = 3444749) B3444749
theorem B3877571 : Blo 1530462 3877571 := bstep (se 1 (by rfl) ⟨2908178, by rfl⟩ : syracuseStep 3877571 = 5816357) B5816357
theorem B2296529 : Blo 1530462 2296529 := bstep (se 2 (by rfl) ⟨861198, by rfl⟩ : syracuseStep 2296529 = 1722397) B1722397
theorem B2583265 : Blo 1530462 2583265 := bstep (se 2 (by rfl) ⟨968724, by rfl⟩ : syracuseStep 2583265 = 1937449) B1937449
theorem B2296547 : Blo 1530462 2296547 := bstep (se 1 (by rfl) ⟨1722410, by rfl⟩ : syracuseStep 2296547 = 3444821) B3444821
theorem B2296577 : Blo 1530462 2296577 := bstep (se 2 (by rfl) ⟨861216, by rfl⟩ : syracuseStep 2296577 = 1722433) B1722433
theorem B2583299 : Blo 1530462 2583299 := bstep (se 1 (by rfl) ⟨1937474, by rfl⟩ : syracuseStep 2583299 = 3874949) B3874949
theorem B11791117 : Blo 1530462 11791117 := bstep (se 3 (by rfl) ⟨2210834, by rfl⟩ : syracuseStep 11791117 = 4421669) B4421669
theorem B2296595 : Blo 1530462 2296595 := bstep (se 1 (by rfl) ⟨1722446, by rfl⟩ : syracuseStep 2296595 = 3444893) B3444893
theorem B1723171 : Blo 1530462 1723171 := bstep (se 1 (by rfl) ⟨1292378, by rfl⟩ : syracuseStep 1723171 = 2584757) B2584757
theorem B2296625 : Blo 1530462 2296625 := bstep (se 2 (by rfl) ⟨861234, by rfl⟩ : syracuseStep 2296625 = 1722469) B1722469
theorem B2296643 : Blo 1530462 2296643 := bstep (se 1 (by rfl) ⟨1722482, by rfl⟩ : syracuseStep 2296643 = 3444965) B3444965
theorem B2485073 : Blo 1530462 2485073 := bstep (se 2 (by rfl) ⟨931902, by rfl⟩ : syracuseStep 2485073 = 1863805) B1863805
theorem B2296673 : Blo 1530462 2296673 := bstep (se 2 (by rfl) ⟨861252, by rfl⟩ : syracuseStep 2296673 = 1722505) B1722505
theorem B2296691 : Blo 1530462 2296691 := bstep (se 1 (by rfl) ⟨1722518, by rfl⟩ : syracuseStep 2296691 = 3445037) B3445037
theorem B2583427 : Blo 1530462 2583427 := bstep (se 1 (by rfl) ⟨1937570, by rfl⟩ : syracuseStep 2583427 = 3875141) B3875141
theorem B49671053 : Blo 1530462 49671053 := bstep (se 3 (by rfl) ⟨9313322, by rfl⟩ : syracuseStep 49671053 = 18626645) B18626645
theorem B2296721 : Blo 1530462 2296721 := bstep (se 2 (by rfl) ⟨861270, by rfl⟩ : syracuseStep 2296721 = 1722541) B1722541
theorem B2296739 : Blo 1530462 2296739 := bstep (se 1 (by rfl) ⟨1722554, by rfl⟩ : syracuseStep 2296739 = 3445109) B3445109
theorem B1616803 : Blo 1530462 1616803 := bstep (se 1 (by rfl) ⟨1212602, by rfl⟩ : syracuseStep 1616803 = 2425205) B2425205
theorem B3443633 : Blo 1530462 3443633 := bstep (se 2 (by rfl) ⟨1291362, by rfl⟩ : syracuseStep 3443633 = 2582725) B2582725
theorem B6540209 : Blo 1530462 6540209 := bstep (se 2 (by rfl) ⟨2452578, by rfl⟩ : syracuseStep 6540209 = 4905157) B4905157
theorem B1723315 : Blo 1530462 1723315 := bstep (se 1 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 1723315 = 2584973) B2584973
theorem B2296769 : Blo 1530462 2296769 := bstep (se 2 (by rfl) ⟨861288, by rfl⟩ : syracuseStep 2296769 = 1722577) B1722577
theorem B3443651 : Blo 1530462 3443651 := bstep (se 1 (by rfl) ⟨2582738, by rfl⟩ : syracuseStep 3443651 = 5165477) B5165477
theorem B2296787 : Blo 1530462 2296787 := bstep (se 1 (by rfl) ⟨1722590, by rfl⟩ : syracuseStep 2296787 = 3445181) B3445181
theorem B4361197 : Blo 1530462 4361197 := bstep (se 3 (by rfl) ⟨817724, by rfl⟩ : syracuseStep 4361197 = 1635449) B1635449
theorem B2296817 : Blo 1530462 2296817 := bstep (se 2 (by rfl) ⟨861306, by rfl⟩ : syracuseStep 2296817 = 1722613) B1722613
theorem B2296835 : Blo 1530462 2296835 := bstep (se 1 (by rfl) ⟨1722626, by rfl⟩ : syracuseStep 2296835 = 3445253) B3445253
theorem B9808901 : Blo 1530462 9808901 := bstep (se 4 (by rfl) ⟨919584, by rfl⟩ : syracuseStep 9808901 = 1839169) B1839169
theorem B13962253 : Blo 1530462 13962253 := bstep (se 3 (by rfl) ⟨2617922, by rfl⟩ : syracuseStep 13962253 = 5235845) B5235845
theorem B2583569 : Blo 1530462 2583569 := bstep (se 2 (by rfl) ⟨968838, by rfl⟩ : syracuseStep 2583569 = 1937677) B1937677
theorem B2296865 : Blo 1530462 2296865 := bstep (se 2 (by rfl) ⟨861324, by rfl⟩ : syracuseStep 2296865 = 1722649) B1722649
theorem B2296883 : Blo 1530462 2296883 := bstep (se 1 (by rfl) ⟨1722662, by rfl⟩ : syracuseStep 2296883 = 3445325) B3445325
theorem B1723459 : Blo 1530462 1723459 := bstep (se 1 (by rfl) ⟨1292594, by rfl⟩ : syracuseStep 1723459 = 2585189) B2585189
theorem B2296913 : Blo 1530462 2296913 := bstep (se 2 (by rfl) ⟨861342, by rfl⟩ : syracuseStep 2296913 = 1722685) B1722685
theorem B2296931 : Blo 1530462 2296931 := bstep (se 1 (by rfl) ⟨1722698, by rfl⟩ : syracuseStep 2296931 = 3445397) B3445397
theorem B11635811 : Blo 1530462 11635811 := bstep (se 1 (by rfl) ⟨8726858, by rfl⟩ : syracuseStep 11635811 = 17453717) B17453717
theorem B2296961 : Blo 1530462 2296961 := bstep (se 2 (by rfl) ⟨861360, by rfl⟩ : syracuseStep 2296961 = 1722721) B1722721
theorem B4361357 : Blo 1530462 4361357 := bstep (se 3 (by rfl) ⟨817754, by rfl⟩ : syracuseStep 4361357 = 1635509) B1635509
theorem B2583697 : Blo 1530462 2583697 := bstep (se 2 (by rfl) ⟨968886, by rfl⟩ : syracuseStep 2583697 = 1937773) B1937773
theorem B2296979 : Blo 1530462 2296979 := bstep (se 1 (by rfl) ⟨1722734, by rfl⟩ : syracuseStep 2296979 = 3445469) B3445469
theorem B2297009 : Blo 1530462 2297009 := bstep (se 2 (by rfl) ⟨861378, by rfl⟩ : syracuseStep 2297009 = 1722757) B1722757
theorem B2583731 : Blo 1530462 2583731 := bstep (se 1 (by rfl) ⟨1937798, by rfl⟩ : syracuseStep 2583731 = 3875597) B3875597
theorem B2297027 : Blo 1530462 2297027 := bstep (se 1 (by rfl) ⟨1722770, by rfl⟩ : syracuseStep 2297027 = 3445541) B3445541
theorem B8727749 : Blo 1530462 8727749 := bstep (se 4 (by rfl) ⟨818226, by rfl⟩ : syracuseStep 8727749 = 1636453) B1636453
theorem B3443921 : Blo 1530462 3443921 := bstep (se 2 (by rfl) ⟨1291470, by rfl⟩ : syracuseStep 3443921 = 2582941) B2582941
theorem B3271889 : Blo 1530462 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B1723603 : Blo 1530462 1723603 := bstep (se 1 (by rfl) ⟨1292702, by rfl⟩ : syracuseStep 1723603 = 2585405) B2585405
theorem B2297057 : Blo 1530462 2297057 := bstep (se 2 (by rfl) ⟨861396, by rfl⟩ : syracuseStep 2297057 = 1722793) B1722793
theorem B3443939 : Blo 1530462 3443939 := bstep (se 1 (by rfl) ⟨2582954, by rfl⟩ : syracuseStep 3443939 = 5165909) B5165909
theorem B3271907 : Blo 1530462 3271907 := bstep (se 1 (by rfl) ⟨2453930, by rfl⟩ : syracuseStep 3271907 = 4907861) B4907861
theorem B17452259 : Blo 1530462 17452259 := bstep (se 1 (by rfl) ⟨13089194, by rfl⟩ : syracuseStep 17452259 = 26178389) B26178389
theorem B2297075 : Blo 1530462 2297075 := bstep (se 1 (by rfl) ⟨1722806, by rfl⟩ : syracuseStep 2297075 = 3445613) B3445613
theorem B2297105 : Blo 1530462 2297105 := bstep (se 2 (by rfl) ⟨861414, by rfl⟩ : syracuseStep 2297105 = 1722829) B1722829
theorem B2297123 : Blo 1530462 2297123 := bstep (se 1 (by rfl) ⟨1722842, by rfl⟩ : syracuseStep 2297123 = 3445685) B3445685
theorem B7752995 : Blo 1530462 7752995 := bstep (se 1 (by rfl) ⟨5814746, by rfl⟩ : syracuseStep 7752995 = 11629493) B11629493
theorem B2583859 : Blo 1530462 2583859 := bstep (se 1 (by rfl) ⟨1937894, by rfl⟩ : syracuseStep 2583859 = 3875789) B3875789
theorem B2297153 : Blo 1530462 2297153 := bstep (se 2 (by rfl) ⟨861432, by rfl⟩ : syracuseStep 2297153 = 1722865) B1722865
theorem B4361539 : Blo 1530462 4361539 := bstep (se 1 (by rfl) ⟨3271154, by rfl⟩ : syracuseStep 4361539 = 6542309) B6542309
theorem B2297171 : Blo 1530462 2297171 := bstep (se 1 (by rfl) ⟨1722878, by rfl⟩ : syracuseStep 2297171 = 3445757) B3445757
theorem B2452835 : Blo 1530462 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B1723747 : Blo 1530462 1723747 := bstep (se 1 (by rfl) ⟨1292810, by rfl⟩ : syracuseStep 1723747 = 2585621) B2585621
theorem B2297201 : Blo 1530462 2297201 := bstep (se 2 (by rfl) ⟨861450, by rfl⟩ : syracuseStep 2297201 = 1722901) B1722901
theorem B4140401 : Blo 1530462 4140401 := bstep (se 2 (by rfl) ⟨1552650, by rfl⟩ : syracuseStep 4140401 = 3105301) B3105301
theorem B2297219 : Blo 1530462 2297219 := bstep (se 1 (by rfl) ⟨1722914, by rfl⟩ : syracuseStep 2297219 = 3445829) B3445829
theorem B2297249 : Blo 1530462 2297249 := bstep (se 2 (by rfl) ⟨861468, by rfl⟩ : syracuseStep 2297249 = 1722937) B1722937
theorem B3681713 : Blo 1530462 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B2297267 : Blo 1530462 2297267 := bstep (se 1 (by rfl) ⟨1722950, by rfl⟩ : syracuseStep 2297267 = 3445901) B3445901
theorem B2584001 : Blo 1530462 2584001 := bstep (se 2 (by rfl) ⟨969000, by rfl⟩ : syracuseStep 2584001 = 1938001) B1938001
theorem B2297297 : Blo 1530462 2297297 := bstep (se 2 (by rfl) ⟨861486, by rfl⟩ : syracuseStep 2297297 = 1722973) B1722973
theorem B2297315 : Blo 1530462 2297315 := bstep (se 1 (by rfl) ⟨1722986, by rfl⟩ : syracuseStep 2297315 = 3445973) B3445973
theorem B3444209 : Blo 1530462 3444209 := bstep (se 2 (by rfl) ⟨1291578, by rfl⟩ : syracuseStep 3444209 = 2583157) B2583157
theorem B1723891 : Blo 1530462 1723891 := bstep (se 1 (by rfl) ⟨1292918, by rfl⟩ : syracuseStep 1723891 = 2585837) B2585837
theorem B2297345 : Blo 1530462 2297345 := bstep (se 2 (by rfl) ⟨861504, by rfl⟩ : syracuseStep 2297345 = 1723009) B1723009
theorem B3444227 : Blo 1530462 3444227 := bstep (se 1 (by rfl) ⟨2583170, by rfl⟩ : syracuseStep 3444227 = 5166341) B5166341
theorem B2297363 : Blo 1530462 2297363 := bstep (se 1 (by rfl) ⟨1723022, by rfl⟩ : syracuseStep 2297363 = 3446045) B3446045
theorem B2297393 : Blo 1530462 2297393 := bstep (se 2 (by rfl) ⟨861522, by rfl⟩ : syracuseStep 2297393 = 1723045) B1723045
theorem B2584129 : Blo 1530462 2584129 := bstep (se 2 (by rfl) ⟨969048, by rfl⟩ : syracuseStep 2584129 = 1938097) B1938097
theorem B2297411 : Blo 1530462 2297411 := bstep (se 1 (by rfl) ⟨1723058, by rfl⟩ : syracuseStep 2297411 = 3446117) B3446117
theorem B2297441 : Blo 1530462 2297441 := bstep (se 2 (by rfl) ⟨861540, by rfl⟩ : syracuseStep 2297441 = 1723081) B1723081
theorem B2584163 : Blo 1530462 2584163 := bstep (se 1 (by rfl) ⟨1938122, by rfl⟩ : syracuseStep 2584163 = 3876245) B3876245
theorem B3878513 : Blo 1530462 3878513 := bstep (se 2 (by rfl) ⟨1454442, by rfl⟩ : syracuseStep 3878513 = 2908885) B2908885
theorem B2297459 : Blo 1530462 2297459 := bstep (se 1 (by rfl) ⟨1723094, by rfl⟩ : syracuseStep 2297459 = 3446189) B3446189
theorem B24850061 : Blo 1530462 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B2297489 : Blo 1530462 2297489 := bstep (se 2 (by rfl) ⟨861558, by rfl⟩ : syracuseStep 2297489 = 1723117) B1723117
theorem B2297507 : Blo 1530462 2297507 := bstep (se 1 (by rfl) ⟨1723130, by rfl⟩ : syracuseStep 2297507 = 3446261) B3446261
theorem B3878563 : Blo 1530462 3878563 := bstep (se 1 (by rfl) ⟨2908922, by rfl⟩ : syracuseStep 3878563 = 5817845) B5817845
theorem B5238445 : Blo 1530462 5238445 := bstep (se 3 (by rfl) ⟨982208, by rfl⟩ : syracuseStep 5238445 = 1964417) B1964417
theorem B2297537 : Blo 1530462 2297537 := bstep (se 2 (by rfl) ⟨861576, by rfl⟩ : syracuseStep 2297537 = 1723153) B1723153
theorem B2297555 : Blo 1530462 2297555 := bstep (se 1 (by rfl) ⟨1723166, by rfl⟩ : syracuseStep 2297555 = 3446333) B3446333
theorem B1838819 : Blo 1530462 1838819 := bstep (se 1 (by rfl) ⟨1379114, by rfl⟩ : syracuseStep 1838819 = 2758229) B2758229
theorem B2584291 : Blo 1530462 2584291 := bstep (se 1 (by rfl) ⟨1938218, by rfl⟩ : syracuseStep 2584291 = 3876437) B3876437
theorem B2297585 : Blo 1530462 2297585 := bstep (se 2 (by rfl) ⟨861594, by rfl⟩ : syracuseStep 2297585 = 1723189) B1723189
theorem B2297603 : Blo 1530462 2297603 := bstep (se 1 (by rfl) ⟨1723202, by rfl⟩ : syracuseStep 2297603 = 3446405) B3446405
theorem B3444497 : Blo 1530462 3444497 := bstep (se 2 (by rfl) ⟨1291686, by rfl⟩ : syracuseStep 3444497 = 2583373) B2583373
theorem B2297633 : Blo 1530462 2297633 := bstep (se 2 (by rfl) ⟨861612, by rfl⟩ : syracuseStep 2297633 = 1723225) B1723225
theorem B3444515 : Blo 1530462 3444515 := bstep (se 1 (by rfl) ⟨2583386, by rfl⟩ : syracuseStep 3444515 = 5166773) B5166773
theorem B3878705 : Blo 1530462 3878705 := bstep (se 2 (by rfl) ⟨1454514, by rfl⟩ : syracuseStep 3878705 = 2909029) B2909029
theorem B2297651 : Blo 1530462 2297651 := bstep (se 1 (by rfl) ⟨1723238, by rfl⟩ : syracuseStep 2297651 = 3446477) B3446477
theorem B2297681 : Blo 1530462 2297681 := bstep (se 2 (by rfl) ⟨861630, by rfl⟩ : syracuseStep 2297681 = 1723261) B1723261
theorem B2297699 : Blo 1530462 2297699 := bstep (se 1 (by rfl) ⟨1723274, by rfl⟩ : syracuseStep 2297699 = 3446549) B3446549
theorem B4140899 : Blo 1530462 4140899 := bstep (se 1 (by rfl) ⟨3105674, by rfl⟩ : syracuseStep 4140899 = 6211349) B6211349
theorem B2584433 : Blo 1530462 2584433 := bstep (se 2 (by rfl) ⟨969162, by rfl⟩ : syracuseStep 2584433 = 1938325) B1938325
theorem B2297729 : Blo 1530462 2297729 := bstep (se 2 (by rfl) ⟨861648, by rfl⟩ : syracuseStep 2297729 = 1723297) B1723297
theorem B2297747 : Blo 1530462 2297747 := bstep (se 1 (by rfl) ⟨1723310, by rfl⟩ : syracuseStep 2297747 = 3446621) B3446621
theorem B2297777 : Blo 1530462 2297777 := bstep (se 2 (by rfl) ⟨861666, by rfl⟩ : syracuseStep 2297777 = 1723333) B1723333
theorem B2297795 : Blo 1530462 2297795 := bstep (se 1 (by rfl) ⟨1723346, by rfl⟩ : syracuseStep 2297795 = 3446693) B3446693
theorem B2297825 : Blo 1530462 2297825 := bstep (se 2 (by rfl) ⟨861684, by rfl⟩ : syracuseStep 2297825 = 1723369) B1723369
theorem B5812195 : Blo 1530462 5812195 := bstep (se 1 (by rfl) ⟨4359146, by rfl⟩ : syracuseStep 5812195 = 8718293) B8718293
theorem B2584561 : Blo 1530462 2584561 := bstep (se 2 (by rfl) ⟨969210, by rfl⟩ : syracuseStep 2584561 = 1938421) B1938421
theorem B2297843 : Blo 1530462 2297843 := bstep (se 1 (by rfl) ⟨1723382, by rfl⟩ : syracuseStep 2297843 = 3446765) B3446765
theorem B2453507 : Blo 1530462 2453507 := bstep (se 1 (by rfl) ⟨1840130, by rfl⟩ : syracuseStep 2453507 = 3680261) B3680261
theorem B2297873 : Blo 1530462 2297873 := bstep (se 2 (by rfl) ⟨861702, by rfl⟩ : syracuseStep 2297873 = 1723405) B1723405
theorem B2584595 : Blo 1530462 2584595 := bstep (se 1 (by rfl) ⟨1938446, by rfl⟩ : syracuseStep 2584595 = 3876893) B3876893
theorem B2297891 : Blo 1530462 2297891 := bstep (se 1 (by rfl) ⟨1723418, by rfl⟩ : syracuseStep 2297891 = 3446837) B3446837
theorem B3444785 : Blo 1530462 3444785 := bstep (se 2 (by rfl) ⟨1291794, by rfl⟩ : syracuseStep 3444785 = 2583589) B2583589
theorem B1937459 : Blo 1530462 1937459 := bstep (se 1 (by rfl) ⟨1453094, by rfl⟩ : syracuseStep 1937459 = 2906189) B2906189
theorem B37269557 : Blo 1530462 37269557 := bstep (se 5 (by rfl) ⟨1747010, by rfl⟩ : syracuseStep 37269557 = 3494021) B3494021
theorem B2297921 : Blo 1530462 2297921 := bstep (se 2 (by rfl) ⟨861720, by rfl⟩ : syracuseStep 2297921 = 1723441) B1723441
theorem B3444803 : Blo 1530462 3444803 := bstep (se 1 (by rfl) ⟨2583602, by rfl⟩ : syracuseStep 3444803 = 5167205) B5167205
theorem B9941069 : Blo 1530462 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B7753805 : Blo 1530462 7753805 := bstep (se 3 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 7753805 = 2907677) B2907677
theorem B2297939 : Blo 1530462 2297939 := bstep (se 1 (by rfl) ⟨1723454, by rfl⟩ : syracuseStep 2297939 = 3446909) B3446909
theorem B3928177 : Blo 1530462 3928177 := bstep (se 2 (by rfl) ⟨1473066, by rfl⟩ : syracuseStep 3928177 = 2946133) B2946133
theorem B2297969 : Blo 1530462 2297969 := bstep (se 2 (by rfl) ⟨861738, by rfl⟩ : syracuseStep 2297969 = 1723477) B1723477
theorem B2297987 : Blo 1530462 2297987 := bstep (se 1 (by rfl) ⟨1723490, by rfl⟩ : syracuseStep 2297987 = 3446981) B3446981
theorem B2584723 : Blo 1530462 2584723 := bstep (se 1 (by rfl) ⟨1938542, by rfl⟩ : syracuseStep 2584723 = 3877085) B3877085
theorem B2298017 : Blo 1530462 2298017 := bstep (se 2 (by rfl) ⟨861756, by rfl⟩ : syracuseStep 2298017 = 1723513) B1723513
theorem B2298035 : Blo 1530462 2298035 := bstep (se 1 (by rfl) ⟨1723526, by rfl⟩ : syracuseStep 2298035 = 3447053) B3447053
theorem B2298065 : Blo 1530462 2298065 := bstep (se 2 (by rfl) ⟨861774, by rfl⟩ : syracuseStep 2298065 = 1723549) B1723549
theorem B2298083 : Blo 1530462 2298083 := bstep (se 1 (by rfl) ⟨1723562, by rfl⟩ : syracuseStep 2298083 = 3447125) B3447125
theorem B2298113 : Blo 1530462 2298113 := bstep (se 2 (by rfl) ⟨861792, by rfl⟩ : syracuseStep 2298113 = 1723585) B1723585
theorem B5165315 : Blo 1530462 5165315 := bstep (se 1 (by rfl) ⟨3873986, by rfl⟩ : syracuseStep 5165315 = 7747973) B7747973
theorem B2298131 : Blo 1530462 2298131 := bstep (se 1 (by rfl) ⟨1723598, by rfl⟩ : syracuseStep 2298131 = 3447197) B3447197
theorem B2584865 : Blo 1530462 2584865 := bstep (se 2 (by rfl) ⟨969324, by rfl⟩ : syracuseStep 2584865 = 1938649) B1938649
theorem B5239075 : Blo 1530462 5239075 := bstep (se 1 (by rfl) ⟨3929306, by rfl⟩ : syracuseStep 5239075 = 7858613) B7858613
theorem B2453809 : Blo 1530462 2453809 := bstep (se 2 (by rfl) ⟨920178, by rfl⟩ : syracuseStep 2453809 = 1840357) B1840357
theorem B2298161 : Blo 1530462 2298161 := bstep (se 2 (by rfl) ⟨861810, by rfl⟩ : syracuseStep 2298161 = 1723621) B1723621
theorem B2298179 : Blo 1530462 2298179 := bstep (se 1 (by rfl) ⟨1723634, by rfl⟩ : syracuseStep 2298179 = 3447269) B3447269
theorem B3445073 : Blo 1530462 3445073 := bstep (se 2 (by rfl) ⟨1291902, by rfl⟩ : syracuseStep 3445073 = 2583805) B2583805
theorem B2298209 : Blo 1530462 2298209 := bstep (se 2 (by rfl) ⟨861828, by rfl⟩ : syracuseStep 2298209 = 1723657) B1723657
theorem B3445091 : Blo 1530462 3445091 := bstep (se 1 (by rfl) ⟨2583818, by rfl⟩ : syracuseStep 3445091 = 5167637) B5167637
theorem B2068849 : Blo 1530462 2068849 := bstep (se 2 (by rfl) ⟨775818, by rfl⟩ : syracuseStep 2068849 = 1551637) B1551637
theorem B2298227 : Blo 1530462 2298227 := bstep (se 1 (by rfl) ⟨1723670, by rfl⟩ : syracuseStep 2298227 = 3447341) B3447341
theorem B2298257 : Blo 1530462 2298257 := bstep (se 2 (by rfl) ⟨861846, by rfl⟩ : syracuseStep 2298257 = 1723693) B1723693
theorem B2584993 : Blo 1530462 2584993 := bstep (se 2 (by rfl) ⟨969372, by rfl⟩ : syracuseStep 2584993 = 1938745) B1938745
theorem B7459235 : Blo 1530462 7459235 := bstep (se 1 (by rfl) ⟨5594426, by rfl⟩ : syracuseStep 7459235 = 11188853) B11188853
theorem B2298275 : Blo 1530462 2298275 := bstep (se 1 (by rfl) ⟨1723706, by rfl⟩ : syracuseStep 2298275 = 3447413) B3447413
theorem B2298305 : Blo 1530462 2298305 := bstep (se 2 (by rfl) ⟨861864, by rfl⟩ : syracuseStep 2298305 = 1723729) B1723729
theorem B2585027 : Blo 1530462 2585027 := bstep (se 1 (by rfl) ⟨1938770, by rfl⟩ : syracuseStep 2585027 = 3877541) B3877541
theorem B2298323 : Blo 1530462 2298323 := bstep (se 1 (by rfl) ⟨1723742, by rfl⟩ : syracuseStep 2298323 = 3447485) B3447485
theorem B26513891 : Blo 1530462 26513891 := bstep (se 1 (by rfl) ⟨19885418, by rfl⟩ : syracuseStep 26513891 = 39770837) B39770837
theorem B2298353 : Blo 1530462 2298353 := bstep (se 2 (by rfl) ⟨861882, by rfl⟩ : syracuseStep 2298353 = 1723765) B1723765
theorem B2454019 : Blo 1530462 2454019 := bstep (se 1 (by rfl) ⟨1840514, by rfl⟩ : syracuseStep 2454019 = 3681029) B3681029
theorem B2298371 : Blo 1530462 2298371 := bstep (se 1 (by rfl) ⟨1723778, by rfl⟩ : syracuseStep 2298371 = 3447557) B3447557
theorem B5165585 : Blo 1530462 5165585 := bstep (se 2 (by rfl) ⟨1937094, by rfl⟩ : syracuseStep 5165585 = 3874189) B3874189
theorem B2298401 : Blo 1530462 2298401 := bstep (se 2 (by rfl) ⟨861900, by rfl⟩ : syracuseStep 2298401 = 1723801) B1723801
theorem B1634851 : Blo 1530462 1634851 := bstep (se 1 (by rfl) ⟨1226138, by rfl⟩ : syracuseStep 1634851 = 2452277) B2452277
theorem B2454065 : Blo 1530462 2454065 := bstep (se 2 (by rfl) ⟨920274, by rfl⟩ : syracuseStep 2454065 = 1840549) B1840549
theorem B2298419 : Blo 1530462 2298419 := bstep (se 1 (by rfl) ⟨1723814, by rfl⟩ : syracuseStep 2298419 = 3447629) B3447629
theorem B2585155 : Blo 1530462 2585155 := bstep (se 1 (by rfl) ⟨1938866, by rfl⟩ : syracuseStep 2585155 = 3877733) B3877733
theorem B2298449 : Blo 1530462 2298449 := bstep (se 2 (by rfl) ⟨861918, by rfl⟩ : syracuseStep 2298449 = 1723837) B1723837
theorem B2298467 : Blo 1530462 2298467 := bstep (se 1 (by rfl) ⟨1723850, by rfl⟩ : syracuseStep 2298467 = 3447701) B3447701
theorem B3445361 : Blo 1530462 3445361 := bstep (se 2 (by rfl) ⟨1292010, by rfl⟩ : syracuseStep 3445361 = 2584021) B2584021
theorem B2298497 : Blo 1530462 2298497 := bstep (se 2 (by rfl) ⟨861936, by rfl⟩ : syracuseStep 2298497 = 1723873) B1723873
theorem B3445379 : Blo 1530462 3445379 := bstep (se 1 (by rfl) ⟨2584034, by rfl⟩ : syracuseStep 3445379 = 5168069) B5168069
theorem B2298515 : Blo 1530462 2298515 := bstep (se 1 (by rfl) ⟨1723886, by rfl⟩ : syracuseStep 2298515 = 3447773) B3447773
theorem B5894819 : Blo 1530462 5894819 := bstep (se 1 (by rfl) ⟨4421114, by rfl⟩ : syracuseStep 5894819 = 8842229) B8842229
theorem B3732131 : Blo 1530462 3732131 := bstep (se 1 (by rfl) ⟨2799098, by rfl⟩ : syracuseStep 3732131 = 5598197) B5598197
theorem B4362929 : Blo 1530462 4362929 := bstep (se 2 (by rfl) ⟨1636098, by rfl⟩ : syracuseStep 4362929 = 3272197) B3272197
theorem B2298545 : Blo 1530462 2298545 := bstep (se 2 (by rfl) ⟨861954, by rfl⟩ : syracuseStep 2298545 = 1723909) B1723909
theorem B2298563 : Blo 1530462 2298563 := bstep (se 1 (by rfl) ⟨1723922, by rfl⟩ : syracuseStep 2298563 = 3447845) B3447845
theorem B2585297 : Blo 1530462 2585297 := bstep (se 2 (by rfl) ⟨969486, by rfl⟩ : syracuseStep 2585297 = 1938973) B1938973
theorem B2298593 : Blo 1530462 2298593 := bstep (se 2 (by rfl) ⟨861972, by rfl⟩ : syracuseStep 2298593 = 1723945) B1723945
theorem B10474211 : Blo 1530462 10474211 := bstep (se 1 (by rfl) ⟨7855658, by rfl⟩ : syracuseStep 10474211 = 15711317) B15711317
theorem B1938163 : Blo 1530462 1938163 := bstep (se 1 (by rfl) ⟨1453622, by rfl⟩ : syracuseStep 1938163 = 2907245) B2907245
theorem B2298611 : Blo 1530462 2298611 := bstep (se 1 (by rfl) ⟨1723958, by rfl⟩ : syracuseStep 2298611 = 3447917) B3447917
theorem B2298641 : Blo 1530462 2298641 := bstep (se 2 (by rfl) ⟨861990, by rfl⟩ : syracuseStep 2298641 = 1723981) B1723981
theorem B2298659 : Blo 1530462 2298659 := bstep (se 1 (by rfl) ⟨1723994, by rfl⟩ : syracuseStep 2298659 = 3447989) B3447989
theorem B2298689 : Blo 1530462 2298689 := bstep (se 2 (by rfl) ⟨862008, by rfl⟩ : syracuseStep 2298689 = 1724017) B1724017
theorem B2585425 : Blo 1530462 2585425 := bstep (se 2 (by rfl) ⟨969534, by rfl⟩ : syracuseStep 2585425 = 1939069) B1939069
theorem B1938259 : Blo 1530462 1938259 := bstep (se 1 (by rfl) ⟨1453694, by rfl⟩ : syracuseStep 1938259 = 2907389) B2907389
theorem B4141937 : Blo 1530462 4141937 := bstep (se 2 (by rfl) ⟨1553226, by rfl⟩ : syracuseStep 4141937 = 3106453) B3106453
theorem B2585459 : Blo 1530462 2585459 := bstep (se 1 (by rfl) ⟨1939094, by rfl⟩ : syracuseStep 2585459 = 3878189) B3878189
theorem B3445649 : Blo 1530462 3445649 := bstep (se 2 (by rfl) ⟨1292118, by rfl⟩ : syracuseStep 3445649 = 2584237) B2584237
theorem B3445667 : Blo 1530462 3445667 := bstep (se 1 (by rfl) ⟨2584250, by rfl⟩ : syracuseStep 3445667 = 5168501) B5168501
theorem B2585587 : Blo 1530462 2585587 := bstep (se 1 (by rfl) ⟨1939190, by rfl⟩ : syracuseStep 2585587 = 3878381) B3878381
theorem B5166125 : Blo 1530462 5166125 := bstep (se 3 (by rfl) ⟨968648, by rfl⟩ : syracuseStep 5166125 = 1937297) B1937297
theorem B8279117 : Blo 1530462 8279117 := bstep (se 3 (by rfl) ⟨1552334, by rfl⟩ : syracuseStep 8279117 = 3104669) B3104669
theorem B5166179 : Blo 1530462 5166179 := bstep (se 1 (by rfl) ⟨3874634, by rfl⟩ : syracuseStep 5166179 = 7749269) B7749269
theorem B2618497 : Blo 1530462 2618497 := bstep (se 2 (by rfl) ⟨981936, by rfl⟩ : syracuseStep 2618497 = 1963873) B1963873
theorem B2585729 : Blo 1530462 2585729 := bstep (se 2 (by rfl) ⟨969648, by rfl⟩ : syracuseStep 2585729 = 1939297) B1939297
theorem B2946179 : Blo 1530462 2946179 := bstep (se 1 (by rfl) ⟨2209634, by rfl⟩ : syracuseStep 2946179 = 4419269) B4419269
theorem B3445937 : Blo 1530462 3445937 := bstep (se 2 (by rfl) ⟨1292226, by rfl⟩ : syracuseStep 3445937 = 2584453) B2584453
theorem B2487475 : Blo 1530462 2487475 := bstep (se 1 (by rfl) ⟨1865606, by rfl⟩ : syracuseStep 2487475 = 3731213) B3731213
theorem B3445955 : Blo 1530462 3445955 := bstep (se 1 (by rfl) ⟨2584466, by rfl⟩ : syracuseStep 3445955 = 5168933) B5168933
theorem B2585857 : Blo 1530462 2585857 := bstep (se 2 (by rfl) ⟨969696, by rfl⟩ : syracuseStep 2585857 = 1939393) B1939393
theorem B2585891 : Blo 1530462 2585891 := bstep (se 1 (by rfl) ⟨1939418, by rfl⟩ : syracuseStep 2585891 = 3878837) B3878837
theorem B1938755 : Blo 1530462 1938755 := bstep (se 1 (by rfl) ⟨1454066, by rfl⟩ : syracuseStep 1938755 = 2908133) B2908133
theorem B5166449 : Blo 1530462 5166449 := bstep (se 2 (by rfl) ⟨1937418, by rfl⟩ : syracuseStep 5166449 = 3874837) B3874837
theorem B2586019 : Blo 1530462 2586019 := bstep (se 1 (by rfl) ⟨1939514, by rfl⟩ : syracuseStep 2586019 = 3879029) B3879029
theorem B19633589 : Blo 1530462 19633589 := bstep (se 5 (by rfl) ⟨920324, by rfl⟩ : syracuseStep 19633589 = 1840649) B1840649
theorem B3446225 : Blo 1530462 3446225 := bstep (se 2 (by rfl) ⟨1292334, by rfl⟩ : syracuseStep 3446225 = 2584669) B2584669
theorem B3446243 : Blo 1530462 3446243 := bstep (se 1 (by rfl) ⟨2584682, by rfl⟩ : syracuseStep 3446243 = 5169365) B5169365
theorem B1635859 : Blo 1530462 1635859 := bstep (se 1 (by rfl) ⟨1226894, by rfl⟩ : syracuseStep 1635859 = 2453789) B2453789
theorem B4363885 : Blo 1530462 4363885 := bstep (se 3 (by rfl) ⟨818228, by rfl⟩ : syracuseStep 4363885 = 1636457) B1636457
theorem B18618083 : Blo 1530462 18618083 := bstep (se 1 (by rfl) ⟨13963562, by rfl⟩ : syracuseStep 18618083 = 27927125) B27927125
theorem B3446513 : Blo 1530462 3446513 := bstep (se 2 (by rfl) ⟨1292442, by rfl⟩ : syracuseStep 3446513 = 2584885) B2584885
theorem B4904707 : Blo 1530462 4904707 := bstep (se 1 (by rfl) ⟨3678530, by rfl⟩ : syracuseStep 4904707 = 7357061) B7357061
theorem B3446531 : Blo 1530462 3446531 := bstep (se 1 (by rfl) ⟨2584898, by rfl⟩ : syracuseStep 3446531 = 5169797) B5169797
theorem B5379853 : Blo 1530462 5379853 := bstep (se 3 (by rfl) ⟨1008722, by rfl⟩ : syracuseStep 5379853 = 2017445) B2017445
theorem B2619155 : Blo 1530462 2619155 := bstep (se 1 (by rfl) ⟨1964366, by rfl⟩ : syracuseStep 2619155 = 3928733) B3928733
theorem B2905969 : Blo 1530462 2905969 := bstep (se 2 (by rfl) ⟨1089738, by rfl⟩ : syracuseStep 2905969 = 2179477) B2179477
theorem B5166989 : Blo 1530462 5166989 := bstep (se 3 (by rfl) ⟨968810, by rfl⟩ : syracuseStep 5166989 = 1937621) B1937621
theorem B4904849 : Blo 1530462 4904849 := bstep (se 2 (by rfl) ⟨1839318, by rfl⟩ : syracuseStep 4904849 = 3678637) B3678637
theorem B5167043 : Blo 1530462 5167043 := bstep (se 1 (by rfl) ⟨3875282, by rfl⟩ : syracuseStep 5167043 = 7750565) B7750565
theorem B4904963 : Blo 1530462 4904963 := bstep (se 1 (by rfl) ⟨3678722, by rfl⟩ : syracuseStep 4904963 = 7357445) B7357445
theorem B1939459 : Blo 1530462 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B3446801 : Blo 1530462 3446801 := bstep (se 2 (by rfl) ⟨1292550, by rfl⟩ : syracuseStep 3446801 = 2585101) B2585101
theorem B2758691 : Blo 1530462 2758691 := bstep (se 1 (by rfl) ⟨2069018, by rfl⟩ : syracuseStep 2758691 = 4138037) B4138037
theorem B3446819 : Blo 1530462 3446819 := bstep (se 1 (by rfl) ⟨2585114, by rfl⟩ : syracuseStep 3446819 = 5170229) B5170229
theorem B13080689 : Blo 1530462 13080689 := bstep (se 2 (by rfl) ⟨4905258, by rfl⟩ : syracuseStep 13080689 = 9810517) B9810517
theorem B5814413 : Blo 1530462 5814413 := bstep (se 3 (by rfl) ⟨1090202, by rfl⟩ : syracuseStep 5814413 = 2180405) B2180405
theorem B5167313 : Blo 1530462 5167313 := bstep (se 2 (by rfl) ⟨1937742, by rfl⟩ : syracuseStep 5167313 = 3875485) B3875485
theorem B2906371 : Blo 1530462 2906371 := bstep (se 1 (by rfl) ⟨2179778, by rfl⟩ : syracuseStep 2906371 = 4359557) B4359557
theorem B2906417 : Blo 1530462 2906417 := bstep (se 2 (by rfl) ⟨1089906, by rfl⟩ : syracuseStep 2906417 = 2179813) B2179813
theorem B3447089 : Blo 1530462 3447089 := bstep (se 2 (by rfl) ⟨1292658, by rfl⟩ : syracuseStep 3447089 = 2585317) B2585317
theorem B3447107 : Blo 1530462 3447107 := bstep (se 1 (by rfl) ⟨2585330, by rfl⟩ : syracuseStep 3447107 = 5170661) B5170661
theorem B2619811 : Blo 1530462 2619811 := bstep (se 1 (by rfl) ⟨1964858, by rfl⟩ : syracuseStep 2619811 = 3929717) B3929717
theorem B5241293 : Blo 1530462 5241293 := bstep (se 3 (by rfl) ⟨982742, by rfl⟩ : syracuseStep 5241293 = 1965485) B1965485
theorem B7363021 : Blo 1530462 7363021 := bstep (se 3 (by rfl) ⟨1380566, by rfl⟩ : syracuseStep 7363021 = 2761133) B2761133
theorem B10476067 : Blo 1530462 10476067 := bstep (se 1 (by rfl) ⟨7857050, by rfl⟩ : syracuseStep 10476067 = 15714101) B15714101
theorem B6543949 : Blo 1530462 6543949 := bstep (se 3 (by rfl) ⟨1226990, by rfl⟩ : syracuseStep 6543949 = 2453981) B2453981
theorem B2906705 : Blo 1530462 2906705 := bstep (se 2 (by rfl) ⟨1090014, by rfl⟩ : syracuseStep 2906705 = 2180029) B2180029
theorem B3447377 : Blo 1530462 3447377 := bstep (se 2 (by rfl) ⟨1292766, by rfl⟩ : syracuseStep 3447377 = 2585533) B2585533
theorem B1530467 : Blo 1530462 1530467 := bstep (se 1 (by rfl) ⟨1147850, by rfl⟩ : syracuseStep 1530467 = 2295701) B2295701
theorem B3447395 : Blo 1530462 3447395 := bstep (se 1 (by rfl) ⟨2585546, by rfl⟩ : syracuseStep 3447395 = 5171093) B5171093
theorem B9435761 : Blo 1530462 9435761 := bstep (se 2 (by rfl) ⟨3538410, by rfl⟩ : syracuseStep 9435761 = 7076821) B7076821
theorem B1530483 : Blo 1530462 1530483 := bstep (se 1 (by rfl) ⟨1147862, by rfl⟩ : syracuseStep 1530483 = 2295725) B2295725
theorem B1530499 : Blo 1530462 1530499 := bstep (se 1 (by rfl) ⟨1147874, by rfl⟩ : syracuseStep 1530499 = 2295749) B2295749
theorem B29448845 : Blo 1530462 29448845 := bstep (se 3 (by rfl) ⟨5521658, by rfl⟩ : syracuseStep 29448845 = 11043317) B11043317
theorem B1530515 : Blo 1530462 1530515 := bstep (se 1 (by rfl) ⟨1147886, by rfl⟩ : syracuseStep 1530515 = 2295773) B2295773
theorem B1530531 : Blo 1530462 1530531 := bstep (se 1 (by rfl) ⟨1147898, by rfl⟩ : syracuseStep 1530531 = 2295797) B2295797
theorem B4659875 : Blo 1530462 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B1530547 : Blo 1530462 1530547 := bstep (se 1 (by rfl) ⟨1147910, by rfl⟩ : syracuseStep 1530547 = 2295821) B2295821
theorem B1530563 : Blo 1530462 1530563 := bstep (se 1 (by rfl) ⟨1147922, by rfl⟩ : syracuseStep 1530563 = 2295845) B2295845
theorem B1530579 : Blo 1530462 1530579 := bstep (se 1 (by rfl) ⟨1147934, by rfl⟩ : syracuseStep 1530579 = 2295869) B2295869
theorem B1530595 : Blo 1530462 1530595 := bstep (se 1 (by rfl) ⟨1147946, by rfl⟩ : syracuseStep 1530595 = 2295893) B2295893
theorem B5167853 : Blo 1530462 5167853 := bstep (se 3 (by rfl) ⟨968972, by rfl⟩ : syracuseStep 5167853 = 1937945) B1937945
theorem B5241581 : Blo 1530462 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B1530611 : Blo 1530462 1530611 := bstep (se 1 (by rfl) ⟨1147958, by rfl⟩ : syracuseStep 1530611 = 2295917) B2295917
theorem B1530627 : Blo 1530462 1530627 := bstep (se 1 (by rfl) ⟨1147970, by rfl⟩ : syracuseStep 1530627 = 2295941) B2295941
theorem B1530643 : Blo 1530462 1530643 := bstep (se 1 (by rfl) ⟨1147982, by rfl⟩ : syracuseStep 1530643 = 2295965) B2295965
theorem B1530659 : Blo 1530462 1530659 := bstep (se 1 (by rfl) ⟨1147994, by rfl⟩ : syracuseStep 1530659 = 2295989) B2295989
theorem B5167907 : Blo 1530462 5167907 := bstep (se 1 (by rfl) ⟨3875930, by rfl⟩ : syracuseStep 5167907 = 7751861) B7751861
theorem B1530675 : Blo 1530462 1530675 := bstep (se 1 (by rfl) ⟨1148006, by rfl⟩ : syracuseStep 1530675 = 2296013) B2296013
theorem B1530691 : Blo 1530462 1530691 := bstep (se 1 (by rfl) ⟨1148018, by rfl⟩ : syracuseStep 1530691 = 2296037) B2296037
theorem B1530707 : Blo 1530462 1530707 := bstep (se 1 (by rfl) ⟨1148030, by rfl⟩ : syracuseStep 1530707 = 2296061) B2296061
theorem B1530723 : Blo 1530462 1530723 := bstep (se 1 (by rfl) ⟨1148042, by rfl⟩ : syracuseStep 1530723 = 2296085) B2296085
theorem B3447665 : Blo 1530462 3447665 := bstep (se 2 (by rfl) ⟨1292874, by rfl⟩ : syracuseStep 3447665 = 2585749) B2585749
theorem B1530739 : Blo 1530462 1530739 := bstep (se 1 (by rfl) ⟨1148054, by rfl⟩ : syracuseStep 1530739 = 2296109) B2296109
theorem B1530755 : Blo 1530462 1530755 := bstep (se 1 (by rfl) ⟨1148066, by rfl⟩ : syracuseStep 1530755 = 2296133) B2296133
theorem B3447683 : Blo 1530462 3447683 := bstep (se 1 (by rfl) ⟨2585762, by rfl⟩ : syracuseStep 3447683 = 5171525) B5171525
theorem B1530771 : Blo 1530462 1530771 := bstep (se 1 (by rfl) ⟨1148078, by rfl⟩ : syracuseStep 1530771 = 2296157) B2296157
theorem B1530787 : Blo 1530462 1530787 := bstep (se 1 (by rfl) ⟨1148090, by rfl⟩ : syracuseStep 1530787 = 2296181) B2296181
theorem B7756721 : Blo 1530462 7756721 := bstep (se 2 (by rfl) ⟨2908770, by rfl⟩ : syracuseStep 7756721 = 5817541) B5817541
theorem B1530803 : Blo 1530462 1530803 := bstep (se 1 (by rfl) ⟨1148102, by rfl⟩ : syracuseStep 1530803 = 2296205) B2296205
theorem B1530819 : Blo 1530462 1530819 := bstep (se 1 (by rfl) ⟨1148114, by rfl⟩ : syracuseStep 1530819 = 2296229) B2296229
theorem B4905937 : Blo 1530462 4905937 := bstep (se 2 (by rfl) ⟨1839726, by rfl⟩ : syracuseStep 4905937 = 3679453) B3679453
theorem B1530835 : Blo 1530462 1530835 := bstep (se 1 (by rfl) ⟨1148126, by rfl⟩ : syracuseStep 1530835 = 2296253) B2296253
theorem B1530851 : Blo 1530462 1530851 := bstep (se 1 (by rfl) ⟨1148138, by rfl⟩ : syracuseStep 1530851 = 2296277) B2296277
theorem B1530867 : Blo 1530462 1530867 := bstep (se 1 (by rfl) ⟨1148150, by rfl⟩ : syracuseStep 1530867 = 2296301) B2296301
theorem B1530883 : Blo 1530462 1530883 := bstep (se 1 (by rfl) ⟨1148162, by rfl⟩ : syracuseStep 1530883 = 2296325) B2296325
theorem B7748621 : Blo 1530462 7748621 := bstep (se 3 (by rfl) ⟨1452866, by rfl⟩ : syracuseStep 7748621 = 2905733) B2905733
theorem B1530899 : Blo 1530462 1530899 := bstep (se 1 (by rfl) ⟨1148174, by rfl⟩ : syracuseStep 1530899 = 2296349) B2296349
theorem B1530915 : Blo 1530462 1530915 := bstep (se 1 (by rfl) ⟨1148186, by rfl⟩ : syracuseStep 1530915 = 2296373) B2296373
theorem B5168177 : Blo 1530462 5168177 := bstep (se 2 (by rfl) ⟨1938066, by rfl⟩ : syracuseStep 5168177 = 3876133) B3876133
theorem B1530931 : Blo 1530462 1530931 := bstep (se 1 (by rfl) ⟨1148198, by rfl⟩ : syracuseStep 1530931 = 2296397) B2296397
theorem B1530947 : Blo 1530462 1530947 := bstep (se 1 (by rfl) ⟨1148210, by rfl⟩ : syracuseStep 1530947 = 2296421) B2296421
theorem B1530963 : Blo 1530462 1530963 := bstep (se 1 (by rfl) ⟨1148222, by rfl⟩ : syracuseStep 1530963 = 2296445) B2296445
theorem B1530979 : Blo 1530462 1530979 := bstep (se 1 (by rfl) ⟨1148234, by rfl⟩ : syracuseStep 1530979 = 2296469) B2296469
theorem B1530995 : Blo 1530462 1530995 := bstep (se 1 (by rfl) ⟨1148246, by rfl⟩ : syracuseStep 1530995 = 2296493) B2296493
theorem B1531011 : Blo 1530462 1531011 := bstep (se 1 (by rfl) ⟨1148258, by rfl⟩ : syracuseStep 1531011 = 2296517) B2296517
theorem B3931267 : Blo 1530462 3931267 := bstep (se 1 (by rfl) ⟨2948450, by rfl⟩ : syracuseStep 3931267 = 5896901) B5896901
theorem B3447953 : Blo 1530462 3447953 := bstep (se 2 (by rfl) ⟨1292982, by rfl⟩ : syracuseStep 3447953 = 2585965) B2585965
theorem B1531027 : Blo 1530462 1531027 := bstep (se 1 (by rfl) ⟨1148270, by rfl⟩ : syracuseStep 1531027 = 2296541) B2296541
theorem B1531043 : Blo 1530462 1531043 := bstep (se 1 (by rfl) ⟨1148282, by rfl⟩ : syracuseStep 1531043 = 2296565) B2296565
theorem B3447971 : Blo 1530462 3447971 := bstep (se 1 (by rfl) ⟨2585978, by rfl⟩ : syracuseStep 3447971 = 5171957) B5171957
theorem B1531059 : Blo 1530462 1531059 := bstep (se 1 (by rfl) ⟨1148294, by rfl⟩ : syracuseStep 1531059 = 2296589) B2296589
theorem B1531075 : Blo 1530462 1531075 := bstep (se 1 (by rfl) ⟨1148306, by rfl⟩ : syracuseStep 1531075 = 2296613) B2296613
theorem B1531091 : Blo 1530462 1531091 := bstep (se 1 (by rfl) ⟨1148318, by rfl⟩ : syracuseStep 1531091 = 2296637) B2296637
theorem B1531107 : Blo 1530462 1531107 := bstep (se 1 (by rfl) ⟨1148330, by rfl⟩ : syracuseStep 1531107 = 2296661) B2296661
theorem B6208753 : Blo 1530462 6208753 := bstep (se 2 (by rfl) ⟨2328282, by rfl⟩ : syracuseStep 6208753 = 4656565) B4656565
theorem B1531123 : Blo 1530462 1531123 := bstep (se 1 (by rfl) ⟨1148342, by rfl⟩ : syracuseStep 1531123 = 2296685) B2296685
theorem B1531139 : Blo 1530462 1531139 := bstep (se 1 (by rfl) ⟨1148354, by rfl⟩ : syracuseStep 1531139 = 2296709) B2296709
theorem B1531155 : Blo 1530462 1531155 := bstep (se 1 (by rfl) ⟨1148366, by rfl⟩ : syracuseStep 1531155 = 2296733) B2296733
theorem B1965331 : Blo 1530462 1965331 := bstep (se 1 (by rfl) ⟨1473998, by rfl⟩ : syracuseStep 1965331 = 2947997) B2947997
theorem B1531171 : Blo 1530462 1531171 := bstep (se 1 (by rfl) ⟨1148378, by rfl⟩ : syracuseStep 1531171 = 2296757) B2296757
theorem B2907427 : Blo 1530462 2907427 := bstep (se 1 (by rfl) ⟨2180570, by rfl⟩ : syracuseStep 2907427 = 4361141) B4361141
theorem B5307697 : Blo 1530462 5307697 := bstep (se 2 (by rfl) ⟨1990386, by rfl⟩ : syracuseStep 5307697 = 3980773) B3980773
theorem B1531187 : Blo 1530462 1531187 := bstep (se 1 (by rfl) ⟨1148390, by rfl⟩ : syracuseStep 1531187 = 2296781) B2296781
theorem B1531203 : Blo 1530462 1531203 := bstep (se 1 (by rfl) ⟨1148402, by rfl⟩ : syracuseStep 1531203 = 2296805) B2296805
theorem B1531219 : Blo 1530462 1531219 := bstep (se 1 (by rfl) ⟨1148414, by rfl⟩ : syracuseStep 1531219 = 2296829) B2296829
theorem B1531235 : Blo 1530462 1531235 := bstep (se 1 (by rfl) ⟨1148426, by rfl⟩ : syracuseStep 1531235 = 2296853) B2296853
theorem B29441393 : Blo 1530462 29441393 := bstep (se 2 (by rfl) ⟨11040522, by rfl⟩ : syracuseStep 29441393 = 22081045) B22081045
theorem B1531251 : Blo 1530462 1531251 := bstep (se 1 (by rfl) ⟨1148438, by rfl⟩ : syracuseStep 1531251 = 2296877) B2296877
theorem B1531267 : Blo 1530462 1531267 := bstep (se 1 (by rfl) ⟨1148450, by rfl⟩ : syracuseStep 1531267 = 2296901) B2296901
theorem B1531283 : Blo 1530462 1531283 := bstep (se 1 (by rfl) ⟨1148462, by rfl⟩ : syracuseStep 1531283 = 2296925) B2296925
theorem B1531299 : Blo 1530462 1531299 := bstep (se 1 (by rfl) ⟨1148474, by rfl⟩ : syracuseStep 1531299 = 2296949) B2296949
theorem B6987185 : Blo 1530462 6987185 := bstep (se 2 (by rfl) ⟨2620194, by rfl⟩ : syracuseStep 6987185 = 5240389) B5240389
theorem B1531315 : Blo 1530462 1531315 := bstep (se 1 (by rfl) ⟨1148486, by rfl⟩ : syracuseStep 1531315 = 2296973) B2296973
theorem B1531331 : Blo 1530462 1531331 := bstep (se 1 (by rfl) ⟨1148498, by rfl⟩ : syracuseStep 1531331 = 2296997) B2296997
theorem B1531347 : Blo 1530462 1531347 := bstep (se 1 (by rfl) ⟨1148510, by rfl⟩ : syracuseStep 1531347 = 2297021) B2297021
theorem B1531363 : Blo 1530462 1531363 := bstep (se 1 (by rfl) ⟨1148522, by rfl⟩ : syracuseStep 1531363 = 2297045) B2297045
theorem B1531379 : Blo 1530462 1531379 := bstep (se 1 (by rfl) ⟨1148534, by rfl⟩ : syracuseStep 1531379 = 2297069) B2297069
theorem B1531395 : Blo 1530462 1531395 := bstep (se 1 (by rfl) ⟨1148546, by rfl⟩ : syracuseStep 1531395 = 2297093) B2297093
theorem B1531411 : Blo 1530462 1531411 := bstep (se 1 (by rfl) ⟨1148558, by rfl⟩ : syracuseStep 1531411 = 2297117) B2297117
theorem B1531427 : Blo 1530462 1531427 := bstep (se 1 (by rfl) ⟨1148570, by rfl⟩ : syracuseStep 1531427 = 2297141) B2297141
theorem B1531443 : Blo 1530462 1531443 := bstep (se 1 (by rfl) ⟨1148582, by rfl⟩ : syracuseStep 1531443 = 2297165) B2297165
theorem B1531459 : Blo 1530462 1531459 := bstep (se 1 (by rfl) ⟨1148594, by rfl⟩ : syracuseStep 1531459 = 2297189) B2297189
theorem B5168717 : Blo 1530462 5168717 := bstep (se 3 (by rfl) ⟨969134, by rfl⟩ : syracuseStep 5168717 = 1938269) B1938269
theorem B1531475 : Blo 1530462 1531475 := bstep (se 1 (by rfl) ⟨1148606, by rfl⟩ : syracuseStep 1531475 = 2297213) B2297213
theorem B1531491 : Blo 1530462 1531491 := bstep (se 1 (by rfl) ⟨1148618, by rfl⟩ : syracuseStep 1531491 = 2297237) B2297237
theorem B19619441 : Blo 1530462 19619441 := bstep (se 2 (by rfl) ⟨7357290, by rfl⟩ : syracuseStep 19619441 = 14714581) B14714581
theorem B11787889 : Blo 1530462 11787889 := bstep (se 2 (by rfl) ⟨4420458, by rfl⟩ : syracuseStep 11787889 = 8840917) B8840917
theorem B1531507 : Blo 1530462 1531507 := bstep (se 1 (by rfl) ⟨1148630, by rfl⟩ : syracuseStep 1531507 = 2297261) B2297261
theorem B5168771 : Blo 1530462 5168771 := bstep (se 1 (by rfl) ⟨3876578, by rfl⟩ : syracuseStep 5168771 = 7753157) B7753157
theorem B1531523 : Blo 1530462 1531523 := bstep (se 1 (by rfl) ⟨1148642, by rfl⟩ : syracuseStep 1531523 = 2297285) B2297285
theorem B1531539 : Blo 1530462 1531539 := bstep (se 1 (by rfl) ⟨1148654, by rfl⟩ : syracuseStep 1531539 = 2297309) B2297309
theorem B1531555 : Blo 1530462 1531555 := bstep (se 1 (by rfl) ⟨1148666, by rfl⟩ : syracuseStep 1531555 = 2297333) B2297333
theorem B3931811 : Blo 1530462 3931811 := bstep (se 1 (by rfl) ⟨2948858, by rfl⟩ : syracuseStep 3931811 = 5897717) B5897717
theorem B8281777 : Blo 1530462 8281777 := bstep (se 2 (by rfl) ⟨3105666, by rfl⟩ : syracuseStep 8281777 = 6211333) B6211333
theorem B1531571 : Blo 1530462 1531571 := bstep (se 1 (by rfl) ⟨1148678, by rfl⟩ : syracuseStep 1531571 = 2297357) B2297357
theorem B1531587 : Blo 1530462 1531587 := bstep (se 1 (by rfl) ⟨1148690, by rfl⟩ : syracuseStep 1531587 = 2297381) B2297381
theorem B3874513 : Blo 1530462 3874513 := bstep (se 2 (by rfl) ⟨1452942, by rfl⟩ : syracuseStep 3874513 = 2905885) B2905885
theorem B1531603 : Blo 1530462 1531603 := bstep (se 1 (by rfl) ⟨1148702, by rfl⟩ : syracuseStep 1531603 = 2297405) B2297405
theorem B1531619 : Blo 1530462 1531619 := bstep (se 1 (by rfl) ⟨1148714, by rfl⟩ : syracuseStep 1531619 = 2297429) B2297429
theorem B2907875 : Blo 1530462 2907875 := bstep (se 1 (by rfl) ⟨2180906, by rfl⟩ : syracuseStep 2907875 = 4361813) B4361813
theorem B1531635 : Blo 1530462 1531635 := bstep (se 1 (by rfl) ⟨1148726, by rfl⟩ : syracuseStep 1531635 = 2297453) B2297453
theorem B1531651 : Blo 1530462 1531651 := bstep (se 1 (by rfl) ⟨1148738, by rfl⟩ : syracuseStep 1531651 = 2297477) B2297477
theorem B2359057 : Blo 1530462 2359057 := bstep (se 2 (by rfl) ⟨884646, by rfl⟩ : syracuseStep 2359057 = 1769293) B1769293
theorem B1531667 : Blo 1530462 1531667 := bstep (se 1 (by rfl) ⟨1148750, by rfl⟩ : syracuseStep 1531667 = 2297501) B2297501
theorem B1531683 : Blo 1530462 1531683 := bstep (se 1 (by rfl) ⟨1148762, by rfl⟩ : syracuseStep 1531683 = 2297525) B2297525
theorem B2621233 : Blo 1530462 2621233 := bstep (se 2 (by rfl) ⟨982962, by rfl⟩ : syracuseStep 2621233 = 1965925) B1965925
theorem B1531699 : Blo 1530462 1531699 := bstep (se 1 (by rfl) ⟨1148774, by rfl⟩ : syracuseStep 1531699 = 2297549) B2297549
theorem B1531715 : Blo 1530462 1531715 := bstep (se 1 (by rfl) ⟨1148786, by rfl⟩ : syracuseStep 1531715 = 2297573) B2297573
theorem B1531731 : Blo 1530462 1531731 := bstep (se 1 (by rfl) ⟨1148798, by rfl⟩ : syracuseStep 1531731 = 2297597) B2297597
theorem B1531747 : Blo 1530462 1531747 := bstep (se 1 (by rfl) ⟨1148810, by rfl⟩ : syracuseStep 1531747 = 2297621) B2297621
theorem B6987619 : Blo 1530462 6987619 := bstep (se 1 (by rfl) ⟨5240714, by rfl⟩ : syracuseStep 6987619 = 10481429) B10481429
theorem B1531763 : Blo 1530462 1531763 := bstep (se 1 (by rfl) ⟨1148822, by rfl⟩ : syracuseStep 1531763 = 2297645) B2297645
theorem B1531779 : Blo 1530462 1531779 := bstep (se 1 (by rfl) ⟨1148834, by rfl⟩ : syracuseStep 1531779 = 2297669) B2297669
theorem B5169041 : Blo 1530462 5169041 := bstep (se 2 (by rfl) ⟨1938390, by rfl⟩ : syracuseStep 5169041 = 3876781) B3876781
theorem B1531795 : Blo 1530462 1531795 := bstep (se 1 (by rfl) ⟨1148846, by rfl⟩ : syracuseStep 1531795 = 2297693) B2297693
theorem B1531811 : Blo 1530462 1531811 := bstep (se 1 (by rfl) ⟨1148858, by rfl⟩ : syracuseStep 1531811 = 2297717) B2297717
theorem B1531827 : Blo 1530462 1531827 := bstep (se 1 (by rfl) ⟨1148870, by rfl⟩ : syracuseStep 1531827 = 2297741) B2297741
theorem B1531843 : Blo 1530462 1531843 := bstep (se 1 (by rfl) ⟨1148882, by rfl⟩ : syracuseStep 1531843 = 2297765) B2297765
theorem B1531859 : Blo 1530462 1531859 := bstep (se 1 (by rfl) ⟨1148894, by rfl⟩ : syracuseStep 1531859 = 2297789) B2297789
theorem B3874787 : Blo 1530462 3874787 := bstep (se 1 (by rfl) ⟨2906090, by rfl⟩ : syracuseStep 3874787 = 5812181) B5812181
theorem B1531875 : Blo 1530462 1531875 := bstep (se 1 (by rfl) ⟨1148906, by rfl⟩ : syracuseStep 1531875 = 2297813) B2297813
theorem B1531891 : Blo 1530462 1531891 := bstep (se 1 (by rfl) ⟨1148918, by rfl⟩ : syracuseStep 1531891 = 2297837) B2297837
theorem B1531915 : Blo 1530462 1531915 := bstep (se 1 (by rfl) ⟨1148936, by rfl⟩ : syracuseStep 1531915 = 2297873) B2297873
theorem B1531927 : Blo 1530462 1531927 := bstep (se 1 (by rfl) ⟨1148945, by rfl⟩ : syracuseStep 1531927 = 2297891) B2297891
theorem B24846371 : Blo 1530462 24846371 := bstep (se 1 (by rfl) ⟨18634778, by rfl⟩ : syracuseStep 24846371 = 37269557) B37269557
theorem B1531947 : Blo 1530462 1531947 := bstep (se 1 (by rfl) ⟨1148960, by rfl⟩ : syracuseStep 1531947 = 2297921) B2297921
theorem B5169203 : Blo 1530462 5169203 := bstep (se 1 (by rfl) ⟨3876902, by rfl⟩ : syracuseStep 5169203 = 7753805) B7753805
theorem B1531959 : Blo 1530462 1531959 := bstep (se 1 (by rfl) ⟨1148969, by rfl⟩ : syracuseStep 1531959 = 2297939) B2297939
theorem B1531979 : Blo 1530462 1531979 := bstep (se 1 (by rfl) ⟨1148984, by rfl⟩ : syracuseStep 1531979 = 2297969) B2297969
theorem B1531991 : Blo 1530462 1531991 := bstep (se 1 (by rfl) ⟨1148993, by rfl⟩ : syracuseStep 1531991 = 2297987) B2297987
theorem B8724581 : Blo 1530462 8724581 := bstep (se 4 (by rfl) ⟨817929, by rfl⟩ : syracuseStep 8724581 = 1635859) B1635859
theorem B1532011 : Blo 1530462 1532011 := bstep (se 1 (by rfl) ⟨1149008, by rfl⟩ : syracuseStep 1532011 = 2298017) B2298017
theorem B1532023 : Blo 1530462 1532023 := bstep (se 1 (by rfl) ⟨1149017, by rfl⟩ : syracuseStep 1532023 = 2298035) B2298035
theorem B1532043 : Blo 1530462 1532043 := bstep (se 1 (by rfl) ⟨1149032, by rfl⟩ : syracuseStep 1532043 = 2298065) B2298065
theorem B1532055 : Blo 1530462 1532055 := bstep (se 1 (by rfl) ⟨1149041, by rfl⟩ : syracuseStep 1532055 = 2298083) B2298083
theorem B1532075 : Blo 1530462 1532075 := bstep (se 1 (by rfl) ⟨1149056, by rfl⟩ : syracuseStep 1532075 = 2298113) B2298113
theorem B1532087 : Blo 1530462 1532087 := bstep (se 1 (by rfl) ⟨1149065, by rfl⟩ : syracuseStep 1532087 = 2298131) B2298131
theorem B1532107 : Blo 1530462 1532107 := bstep (se 1 (by rfl) ⟨1149080, by rfl⟩ : syracuseStep 1532107 = 2298161) B2298161
theorem B26509517 : Blo 1530462 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B1532119 : Blo 1530462 1532119 := bstep (se 1 (by rfl) ⟨1149089, by rfl⟩ : syracuseStep 1532119 = 2298179) B2298179
theorem B1532139 : Blo 1530462 1532139 := bstep (se 1 (by rfl) ⟨1149104, by rfl⟩ : syracuseStep 1532139 = 2298209) B2298209
theorem B1532151 : Blo 1530462 1532151 := bstep (se 1 (by rfl) ⟨1149113, by rfl⟩ : syracuseStep 1532151 = 2298227) B2298227
theorem B1532171 : Blo 1530462 1532171 := bstep (se 1 (by rfl) ⟨1149128, by rfl⟩ : syracuseStep 1532171 = 2298257) B2298257
theorem B4972823 : Blo 1530462 4972823 := bstep (se 1 (by rfl) ⟨3729617, by rfl⟩ : syracuseStep 4972823 = 7459235) B7459235
theorem B1532183 : Blo 1530462 1532183 := bstep (se 1 (by rfl) ⟨1149137, by rfl⟩ : syracuseStep 1532183 = 2298275) B2298275
theorem B1532203 : Blo 1530462 1532203 := bstep (se 1 (by rfl) ⟨1149152, by rfl⟩ : syracuseStep 1532203 = 2298305) B2298305
theorem B1532215 : Blo 1530462 1532215 := bstep (se 1 (by rfl) ⟨1149161, by rfl⟩ : syracuseStep 1532215 = 2298323) B2298323
theorem B5169473 : Blo 1530462 5169473 := bstep (se 2 (by rfl) ⟨1938552, by rfl⟩ : syracuseStep 5169473 = 3877105) B3877105
theorem B1532235 : Blo 1530462 1532235 := bstep (se 1 (by rfl) ⟨1149176, by rfl⟩ : syracuseStep 1532235 = 2298353) B2298353
theorem B1532247 : Blo 1530462 1532247 := bstep (se 1 (by rfl) ⟨1149185, by rfl⟩ : syracuseStep 1532247 = 2298371) B2298371
theorem B3875161 : Blo 1530462 3875161 := bstep (se 2 (by rfl) ⟨1453185, by rfl⟩ : syracuseStep 3875161 = 2906371) B2906371
theorem B1532267 : Blo 1530462 1532267 := bstep (se 1 (by rfl) ⟨1149200, by rfl⟩ : syracuseStep 1532267 = 2298401) B2298401
theorem B1532279 : Blo 1530462 1532279 := bstep (se 1 (by rfl) ⟨1149209, by rfl⟩ : syracuseStep 1532279 = 2298419) B2298419
theorem B1532299 : Blo 1530462 1532299 := bstep (se 1 (by rfl) ⟨1149224, by rfl⟩ : syracuseStep 1532299 = 2298449) B2298449
theorem B1532311 : Blo 1530462 1532311 := bstep (se 1 (by rfl) ⟨1149233, by rfl⟩ : syracuseStep 1532311 = 2298467) B2298467
theorem B1532331 : Blo 1530462 1532331 := bstep (se 1 (by rfl) ⟨1149248, by rfl⟩ : syracuseStep 1532331 = 2298497) B2298497
theorem B1532343 : Blo 1530462 1532343 := bstep (se 1 (by rfl) ⟨1149257, by rfl⟩ : syracuseStep 1532343 = 2298515) B2298515
theorem B2908619 : Blo 1530462 2908619 := bstep (se 1 (by rfl) ⟨2181464, by rfl⟩ : syracuseStep 2908619 = 4362929) B4362929
theorem B1532363 : Blo 1530462 1532363 := bstep (se 1 (by rfl) ⟨1149272, by rfl⟩ : syracuseStep 1532363 = 2298545) B2298545
theorem B1532375 : Blo 1530462 1532375 := bstep (se 1 (by rfl) ⟨1149281, by rfl⟩ : syracuseStep 1532375 = 2298563) B2298563
theorem B1532395 : Blo 1530462 1532395 := bstep (se 1 (by rfl) ⟨1149296, by rfl⟩ : syracuseStep 1532395 = 2298593) B2298593
theorem B1532407 : Blo 1530462 1532407 := bstep (se 1 (by rfl) ⟨1149305, by rfl⟩ : syracuseStep 1532407 = 2298611) B2298611
theorem B1532427 : Blo 1530462 1532427 := bstep (se 1 (by rfl) ⟨1149320, by rfl⟩ : syracuseStep 1532427 = 2298641) B2298641
theorem B1532439 : Blo 1530462 1532439 := bstep (se 1 (by rfl) ⟨1149329, by rfl⟩ : syracuseStep 1532439 = 2298659) B2298659
theorem B13074979 : Blo 1530462 13074979 := bstep (se 1 (by rfl) ⟨9806234, by rfl⟩ : syracuseStep 13074979 = 19612469) B19612469
theorem B1532459 : Blo 1530462 1532459 := bstep (se 1 (by rfl) ⟨1149344, by rfl⟩ : syracuseStep 1532459 = 2298689) B2298689
theorem B2761291 : Blo 1530462 2761291 := bstep (se 1 (by rfl) ⟨2070968, by rfl⟩ : syracuseStep 2761291 = 4141937) B4141937
theorem B2908801 : Blo 1530462 2908801 := bstep (se 2 (by rfl) ⟨1090800, by rfl⟩ : syracuseStep 2908801 = 2181601) B2181601
theorem B8717017 : Blo 1530462 8717017 := bstep (se 2 (by rfl) ⟨3268881, by rfl⟩ : syracuseStep 8717017 = 6537763) B6537763
theorem B4358873 : Blo 1530462 4358873 := bstep (se 2 (by rfl) ⟨1634577, by rfl⟩ : syracuseStep 4358873 = 3269155) B3269155
theorem B2179801 : Blo 1530462 2179801 := bstep (se 2 (by rfl) ⟨817425, by rfl⟩ : syracuseStep 2179801 = 1634851) B1634851
theorem B13968089 : Blo 1530462 13968089 := bstep (se 2 (by rfl) ⟨5238033, by rfl⟩ : syracuseStep 13968089 = 10476067) B10476067
theorem B8725265 : Blo 1530462 8725265 := bstep (se 2 (by rfl) ⟨3271974, by rfl⟩ : syracuseStep 8725265 = 6543949) B6543949
theorem B5170013 : Blo 1530462 5170013 := bstep (se 3 (by rfl) ⟨969377, by rfl⟩ : syracuseStep 5170013 = 1938755) B1938755
theorem B15721489 : Blo 1530462 15721489 := bstep (se 2 (by rfl) ⟨5895558, by rfl⟩ : syracuseStep 15721489 = 11791117) B11791117
theorem B12412055 : Blo 1530462 12412055 := bstep (se 1 (by rfl) ⟨9309041, by rfl⟩ : syracuseStep 12412055 = 18618083) B18618083
theorem B44164277 : Blo 1530462 44164277 := bstep (se 5 (by rfl) ⟨2070200, by rfl⟩ : syracuseStep 44164277 = 4140401) B4140401
theorem B17442053 : Blo 1530462 17442053 := bstep (se 4 (by rfl) ⟨1635192, by rfl⟩ : syracuseStep 17442053 = 3270385) B3270385
theorem B3269899 : Blo 1530462 3269899 := bstep (se 1 (by rfl) ⟨2452424, by rfl⟩ : syracuseStep 3269899 = 4904849) B4904849
theorem B3269975 : Blo 1530462 3269975 := bstep (se 1 (by rfl) ⟨2452481, by rfl⟩ : syracuseStep 3269975 = 4904963) B4904963
theorem B11035997 : Blo 1530462 11035997 := bstep (se 3 (by rfl) ⟨2069249, by rfl⟩ : syracuseStep 11035997 = 4138499) B4138499
theorem B99313037 : Blo 1530462 99313037 := bstep (se 3 (by rfl) ⟨18621194, by rfl⟩ : syracuseStep 99313037 = 37242389) B37242389
theorem B3876275 : Blo 1530462 3876275 := bstep (se 1 (by rfl) ⟨2907206, by rfl⟩ : syracuseStep 3876275 = 5814413) B5814413
theorem B1721803 : Blo 1530462 1721803 := bstep (se 1 (by rfl) ⟨1291352, by rfl⟩ : syracuseStep 1721803 = 2582705) B2582705
theorem B7751213 : Blo 1530462 7751213 := bstep (se 3 (by rfl) ⟨1453352, by rfl⟩ : syracuseStep 7751213 = 2906705) B2906705
theorem B1721911 : Blo 1530462 1721911 := bstep (se 1 (by rfl) ⟨1291433, by rfl⟩ : syracuseStep 1721911 = 2582867) B2582867
theorem B8717975 : Blo 1530462 8717975 := bstep (se 1 (by rfl) ⟨6538481, by rfl⟩ : syracuseStep 8717975 = 13076963) B13076963
theorem B11634353 : Blo 1530462 11634353 := bstep (se 2 (by rfl) ⟨4362882, by rfl⟩ : syracuseStep 11634353 = 8725765) B8725765
theorem B3876569 : Blo 1530462 3876569 := bstep (se 2 (by rfl) ⟨1453713, by rfl⟩ : syracuseStep 3876569 = 2907427) B2907427
theorem B1722091 : Blo 1530462 1722091 := bstep (se 1 (by rfl) ⟨1291568, by rfl⟩ : syracuseStep 1722091 = 2583137) B2583137
theorem B3106583 : Blo 1530462 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B1722199 : Blo 1530462 1722199 := bstep (se 1 (by rfl) ⟨1291649, by rfl⟩ : syracuseStep 1722199 = 2583299) B2583299
theorem B33114035 : Blo 1530462 33114035 := bstep (se 1 (by rfl) ⟨24835526, by rfl⟩ : syracuseStep 33114035 = 49671053) B49671053
theorem B2295755 : Blo 1530462 2295755 := bstep (se 1 (by rfl) ⟨1721816, by rfl⟩ : syracuseStep 2295755 = 3443633) B3443633
theorem B4360139 : Blo 1530462 4360139 := bstep (se 1 (by rfl) ⟨3270104, by rfl⟩ : syracuseStep 4360139 = 6540209) B6540209
theorem B5171147 : Blo 1530462 5171147 := bstep (se 1 (by rfl) ⟨3878360, by rfl⟩ : syracuseStep 5171147 = 7756721) B7756721
theorem B2295767 : Blo 1530462 2295767 := bstep (se 1 (by rfl) ⟨1721825, by rfl⟩ : syracuseStep 2295767 = 3443651) B3443651
theorem B6539267 : Blo 1530462 6539267 := bstep (se 1 (by rfl) ⟨4904450, by rfl⟩ : syracuseStep 6539267 = 9808901) B9808901
theorem B1722379 : Blo 1530462 1722379 := bstep (se 1 (by rfl) ⟨1291784, by rfl⟩ : syracuseStep 1722379 = 2583569) B2583569
theorem B2295833 : Blo 1530462 2295833 := bstep (se 2 (by rfl) ⟨860937, by rfl⟩ : syracuseStep 2295833 = 1721875) B1721875
theorem B1722487 : Blo 1530462 1722487 := bstep (se 1 (by rfl) ⟨1291865, by rfl⟩ : syracuseStep 1722487 = 2583731) B2583731
theorem B5818499 : Blo 1530462 5818499 := bstep (se 1 (by rfl) ⟨4363874, by rfl⟩ : syracuseStep 5818499 = 8727749) B8727749
theorem B2295947 : Blo 1530462 2295947 := bstep (se 1 (by rfl) ⟨1721960, by rfl⟩ : syracuseStep 2295947 = 3443921) B3443921
theorem B2181259 : Blo 1530462 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B5818513 : Blo 1530462 5818513 := bstep (se 2 (by rfl) ⟨2181942, by rfl⟩ : syracuseStep 5818513 = 4363885) B4363885
theorem B2295959 : Blo 1530462 2295959 := bstep (se 1 (by rfl) ⟨1721969, by rfl⟩ : syracuseStep 2295959 = 3443939) B3443939
theorem B2181271 : Blo 1530462 2181271 := bstep (se 1 (by rfl) ⟨1635953, by rfl⟩ : syracuseStep 2181271 = 3271907) B3271907
theorem B11634839 : Blo 1530462 11634839 := bstep (se 1 (by rfl) ⟨8726129, by rfl⟩ : syracuseStep 11634839 = 17452259) B17452259
theorem B2296025 : Blo 1530462 2296025 := bstep (se 2 (by rfl) ⟨861009, by rfl⟩ : syracuseStep 2296025 = 1722019) B1722019
theorem B5171417 : Blo 1530462 5171417 := bstep (se 2 (by rfl) ⟨1939281, by rfl⟩ : syracuseStep 5171417 = 3878563) B3878563
theorem B1722667 : Blo 1530462 1722667 := bstep (se 1 (by rfl) ⟨1292000, by rfl⟩ : syracuseStep 1722667 = 2584001) B2584001
theorem B2296139 : Blo 1530462 2296139 := bstep (se 1 (by rfl) ⟨1722104, by rfl⟩ : syracuseStep 2296139 = 3444209) B3444209
theorem B2296151 : Blo 1530462 2296151 := bstep (se 1 (by rfl) ⟨1722113, by rfl⟩ : syracuseStep 2296151 = 3444227) B3444227
theorem B6539609 : Blo 1530462 6539609 := bstep (se 2 (by rfl) ⟨2452353, by rfl⟩ : syracuseStep 6539609 = 4904707) B4904707
theorem B1722775 : Blo 1530462 1722775 := bstep (se 1 (by rfl) ⟨1292081, by rfl⟩ : syracuseStep 1722775 = 2584163) B2584163
theorem B2296217 : Blo 1530462 2296217 := bstep (se 2 (by rfl) ⟨861081, by rfl⟩ : syracuseStep 2296217 = 1722163) B1722163
theorem B16566707 : Blo 1530462 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B9316825 : Blo 1530462 9316825 := bstep (se 2 (by rfl) ⟨3493809, by rfl⟩ : syracuseStep 9316825 = 6987619) B6987619
theorem B2296331 : Blo 1530462 2296331 := bstep (se 1 (by rfl) ⟨1722248, by rfl⟩ : syracuseStep 2296331 = 3444497) B3444497
theorem B11045393 : Blo 1530462 11045393 := bstep (se 2 (by rfl) ⟨4142022, by rfl⟩ : syracuseStep 11045393 = 8284045) B8284045
theorem B2296343 : Blo 1530462 2296343 := bstep (se 1 (by rfl) ⟨1722257, by rfl⟩ : syracuseStep 2296343 = 3444515) B3444515
theorem B1722955 : Blo 1530462 1722955 := bstep (se 1 (by rfl) ⟨1292216, by rfl⟩ : syracuseStep 1722955 = 2584433) B2584433
theorem B2296409 : Blo 1530462 2296409 := bstep (se 2 (by rfl) ⟨861153, by rfl⟩ : syracuseStep 2296409 = 1722307) B1722307
theorem B2583191 : Blo 1530462 2583191 := bstep (se 1 (by rfl) ⟨1937393, by rfl⟩ : syracuseStep 2583191 = 3874787) B3874787
theorem B1723063 : Blo 1530462 1723063 := bstep (se 1 (by rfl) ⟨1292297, by rfl⟩ : syracuseStep 1723063 = 2584595) B2584595
theorem B2296523 : Blo 1530462 2296523 := bstep (se 1 (by rfl) ⟨1722392, by rfl⟩ : syracuseStep 2296523 = 3444785) B3444785
theorem B2296535 : Blo 1530462 2296535 := bstep (se 1 (by rfl) ⟨1722401, by rfl⟩ : syracuseStep 2296535 = 3444803) B3444803
theorem B9308945 : Blo 1530462 9308945 := bstep (se 2 (by rfl) ⟨3490854, by rfl⟩ : syracuseStep 9308945 = 6981709) B6981709
theorem B2583319 : Blo 1530462 2583319 := bstep (se 1 (by rfl) ⟨1937489, by rfl⟩ : syracuseStep 2583319 = 3874979) B3874979
theorem B2296601 : Blo 1530462 2296601 := bstep (se 2 (by rfl) ⟨861225, by rfl⟩ : syracuseStep 2296601 = 1722451) B1722451
theorem B5237569 : Blo 1530462 5237569 := bstep (se 2 (by rfl) ⟨1964088, by rfl⟩ : syracuseStep 5237569 = 3928177) B3928177
theorem B4139851 : Blo 1530462 4139851 := bstep (se 1 (by rfl) ⟨3104888, by rfl⟩ : syracuseStep 4139851 = 6209777) B6209777
theorem B3443543 : Blo 1530462 3443543 := bstep (se 1 (by rfl) ⟨2582657, by rfl⟩ : syracuseStep 3443543 = 5165315) B5165315
theorem B1723243 : Blo 1530462 1723243 := bstep (se 1 (by rfl) ⟨1292432, by rfl⟩ : syracuseStep 1723243 = 2584865) B2584865
theorem B2296715 : Blo 1530462 2296715 := bstep (se 1 (by rfl) ⟨1722536, by rfl⟩ : syracuseStep 2296715 = 3445073) B3445073
theorem B2296727 : Blo 1530462 2296727 := bstep (se 1 (by rfl) ⟨1722545, by rfl⟩ : syracuseStep 2296727 = 3445091) B3445091
theorem B1723351 : Blo 1530462 1723351 := bstep (se 1 (by rfl) ⟨1292513, by rfl⟩ : syracuseStep 1723351 = 2585027) B2585027
theorem B2296793 : Blo 1530462 2296793 := bstep (se 2 (by rfl) ⟨861297, by rfl⟩ : syracuseStep 2296793 = 1722595) B1722595
theorem B3443723 : Blo 1530462 3443723 := bstep (se 1 (by rfl) ⟨2582792, by rfl⟩ : syracuseStep 3443723 = 5165585) B5165585
theorem B5811223 : Blo 1530462 5811223 := bstep (se 1 (by rfl) ⟨4358417, by rfl⟩ : syracuseStep 5811223 = 8716835) B8716835
theorem B3443777 : Blo 1530462 3443777 := bstep (se 2 (by rfl) ⟨1291416, by rfl⟩ : syracuseStep 3443777 = 2582833) B2582833
theorem B3271745 : Blo 1530462 3271745 := bstep (se 2 (by rfl) ⟨1226904, by rfl⟩ : syracuseStep 3271745 = 2453809) B2453809
theorem B2296907 : Blo 1530462 2296907 := bstep (se 1 (by rfl) ⟨1722680, by rfl⟩ : syracuseStep 2296907 = 3445361) B3445361
theorem B2296919 : Blo 1530462 2296919 := bstep (se 1 (by rfl) ⟨1722689, by rfl⟩ : syracuseStep 2296919 = 3445379) B3445379
theorem B1723531 : Blo 1530462 1723531 := bstep (se 1 (by rfl) ⟨1292648, by rfl⟩ : syracuseStep 1723531 = 2585297) B2585297
theorem B6982807 : Blo 1530462 6982807 := bstep (se 1 (by rfl) ⟨5237105, by rfl⟩ : syracuseStep 6982807 = 10474211) B10474211
theorem B2296985 : Blo 1530462 2296985 := bstep (se 2 (by rfl) ⟨861369, by rfl⟩ : syracuseStep 2296985 = 1722739) B1722739
theorem B3493081 : Blo 1530462 3493081 := bstep (se 2 (by rfl) ⟨1309905, by rfl⟩ : syracuseStep 3493081 = 2619811) B2619811
theorem B1723639 : Blo 1530462 1723639 := bstep (se 1 (by rfl) ⟨1292729, by rfl⟩ : syracuseStep 1723639 = 2585459) B2585459
theorem B2297099 : Blo 1530462 2297099 := bstep (se 1 (by rfl) ⟨1722824, by rfl⟩ : syracuseStep 2297099 = 3445649) B3445649
theorem B9817361 : Blo 1530462 9817361 := bstep (se 2 (by rfl) ⟨3681510, by rfl⟩ : syracuseStep 9817361 = 7363021) B7363021
theorem B2297111 : Blo 1530462 2297111 := bstep (se 1 (by rfl) ⟨1722833, by rfl⟩ : syracuseStep 2297111 = 3445667) B3445667
theorem B3443993 : Blo 1530462 3443993 := bstep (se 2 (by rfl) ⟨1291497, by rfl⟩ : syracuseStep 3443993 = 2582995) B2582995
theorem B3681587 : Blo 1530462 3681587 := bstep (se 1 (by rfl) ⟨2761190, by rfl⟩ : syracuseStep 3681587 = 5522381) B5522381
theorem B3878219 : Blo 1530462 3878219 := bstep (se 1 (by rfl) ⟨2908664, by rfl⟩ : syracuseStep 3878219 = 5817329) B5817329
theorem B2297177 : Blo 1530462 2297177 := bstep (se 2 (by rfl) ⟨861441, by rfl⟩ : syracuseStep 2297177 = 1722883) B1722883
theorem B3444083 : Blo 1530462 3444083 := bstep (se 1 (by rfl) ⟨2583062, by rfl⟩ : syracuseStep 3444083 = 5166125) B5166125
theorem B2583947 : Blo 1530462 2583947 := bstep (se 1 (by rfl) ⟨1937960, by rfl⟩ : syracuseStep 2583947 = 3875921) B3875921
theorem B3444119 : Blo 1530462 3444119 := bstep (se 1 (by rfl) ⟨2583089, by rfl⟩ : syracuseStep 3444119 = 5166179) B5166179
theorem B1723819 : Blo 1530462 1723819 := bstep (se 1 (by rfl) ⟨1292864, by rfl⟩ : syracuseStep 1723819 = 2585729) B2585729
theorem B4140467 : Blo 1530462 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B2297291 : Blo 1530462 2297291 := bstep (se 1 (by rfl) ⟨1722968, by rfl⟩ : syracuseStep 2297291 = 3445937) B3445937
theorem B2297303 : Blo 1530462 2297303 := bstep (se 1 (by rfl) ⟨1722977, by rfl⟩ : syracuseStep 2297303 = 3445955) B3445955
theorem B2584075 : Blo 1530462 2584075 := bstep (se 1 (by rfl) ⟨1938056, by rfl⟩ : syracuseStep 2584075 = 3876113) B3876113
theorem B1723927 : Blo 1530462 1723927 := bstep (se 1 (by rfl) ⟨1292945, by rfl⟩ : syracuseStep 1723927 = 2585891) B2585891
theorem B2297369 : Blo 1530462 2297369 := bstep (se 2 (by rfl) ⟨861513, by rfl⟩ : syracuseStep 2297369 = 1723027) B1723027
theorem B3444299 : Blo 1530462 3444299 := bstep (se 1 (by rfl) ⟨2583224, by rfl⟩ : syracuseStep 3444299 = 5166449) B5166449
theorem B3444353 : Blo 1530462 3444353 := bstep (se 2 (by rfl) ⟨1291632, by rfl⟩ : syracuseStep 3444353 = 2583265) B2583265
theorem B2297483 : Blo 1530462 2297483 := bstep (se 1 (by rfl) ⟨1723112, by rfl⟩ : syracuseStep 2297483 = 3446225) B3446225
theorem B2297495 : Blo 1530462 2297495 := bstep (se 1 (by rfl) ⟨1723121, by rfl⟩ : syracuseStep 2297495 = 3446243) B3446243
theorem B2584217 : Blo 1530462 2584217 := bstep (se 2 (by rfl) ⟨969081, by rfl⟩ : syracuseStep 2584217 = 1938163) B1938163
theorem B2297561 : Blo 1530462 2297561 := bstep (se 2 (by rfl) ⟨861585, by rfl⟩ : syracuseStep 2297561 = 1723171) B1723171
theorem B2584345 : Blo 1530462 2584345 := bstep (se 2 (by rfl) ⟨969129, by rfl⟩ : syracuseStep 2584345 = 1938259) B1938259
theorem B5812013 : Blo 1530462 5812013 := bstep (se 3 (by rfl) ⟨1089752, by rfl⟩ : syracuseStep 5812013 = 2179505) B2179505
theorem B2297675 : Blo 1530462 2297675 := bstep (se 1 (by rfl) ⟨1723256, by rfl⟩ : syracuseStep 2297675 = 3446513) B3446513
theorem B2297687 : Blo 1530462 2297687 := bstep (se 1 (by rfl) ⟨1723265, by rfl⟩ : syracuseStep 2297687 = 3446531) B3446531
theorem B3444569 : Blo 1530462 3444569 := bstep (se 2 (by rfl) ⟨1291713, by rfl⟩ : syracuseStep 3444569 = 2583427) B2583427
theorem B2453399 : Blo 1530462 2453399 := bstep (se 1 (by rfl) ⟨1840049, by rfl⟩ : syracuseStep 2453399 = 3680099) B3680099
theorem B2297753 : Blo 1530462 2297753 := bstep (se 2 (by rfl) ⟨861657, by rfl⟩ : syracuseStep 2297753 = 1723315) B1723315
theorem B3444659 : Blo 1530462 3444659 := bstep (se 1 (by rfl) ⟨2583494, by rfl⟩ : syracuseStep 3444659 = 5166989) B5166989
theorem B6541249 : Blo 1530462 6541249 := bstep (se 2 (by rfl) ⟨2452968, by rfl⟩ : syracuseStep 6541249 = 4905937) B4905937
theorem B2797505 : Blo 1530462 2797505 := bstep (se 2 (by rfl) ⟨1049064, by rfl⟩ : syracuseStep 2797505 = 2098129) B2098129
theorem B3444695 : Blo 1530462 3444695 := bstep (se 1 (by rfl) ⟨2583521, by rfl⟩ : syracuseStep 3444695 = 5167043) B5167043
theorem B2297867 : Blo 1530462 2297867 := bstep (se 1 (by rfl) ⟨1723400, by rfl⟩ : syracuseStep 2297867 = 3446801) B3446801
theorem B18616337 : Blo 1530462 18616337 := bstep (se 2 (by rfl) ⟨6981126, by rfl⟩ : syracuseStep 18616337 = 13962253) B13962253
theorem B5517335 : Blo 1530462 5517335 := bstep (se 1 (by rfl) ⟨4138001, by rfl⟩ : syracuseStep 5517335 = 8276003) B8276003
theorem B1839127 : Blo 1530462 1839127 := bstep (se 1 (by rfl) ⟨1379345, by rfl⟩ : syracuseStep 1839127 = 2758691) B2758691
theorem B2297879 : Blo 1530462 2297879 := bstep (se 1 (by rfl) ⟨1723409, by rfl⟩ : syracuseStep 2297879 = 3446819) B3446819
theorem B1634347 : Blo 1530462 1634347 := bstep (se 1 (by rfl) ⟨1225760, by rfl⟩ : syracuseStep 1634347 = 2451521) B2451521
theorem B8720459 : Blo 1530462 8720459 := bstep (se 1 (by rfl) ⟨6540344, by rfl⟩ : syracuseStep 8720459 = 13080689) B13080689
theorem B2297945 : Blo 1530462 2297945 := bstep (se 2 (by rfl) ⟨861729, by rfl⟩ : syracuseStep 2297945 = 1723459) B1723459
theorem B3444875 : Blo 1530462 3444875 := bstep (se 1 (by rfl) ⟨2583656, by rfl⟩ : syracuseStep 3444875 = 5167313) B5167313
theorem B3444929 : Blo 1530462 3444929 := bstep (se 2 (by rfl) ⟨1291848, by rfl⟩ : syracuseStep 3444929 = 2583697) B2583697
theorem B1937611 : Blo 1530462 1937611 := bstep (se 1 (by rfl) ⟨1453208, by rfl⟩ : syracuseStep 1937611 = 2906417) B2906417
theorem B2298059 : Blo 1530462 2298059 := bstep (se 1 (by rfl) ⟨1723544, by rfl⟩ : syracuseStep 2298059 = 3447089) B3447089
theorem B2298071 : Blo 1530462 2298071 := bstep (se 1 (by rfl) ⟨1723553, by rfl⟩ : syracuseStep 2298071 = 3447107) B3447107
theorem B13979909 : Blo 1530462 13979909 := bstep (se 4 (by rfl) ⟨1310616, by rfl⟩ : syracuseStep 13979909 = 2621233) B2621233
theorem B2298137 : Blo 1530462 2298137 := bstep (se 2 (by rfl) ⟨861801, by rfl⟩ : syracuseStep 2298137 = 1723603) B1723603
theorem B3494195 : Blo 1530462 3494195 := bstep (se 1 (by rfl) ⟨2620646, by rfl⟩ : syracuseStep 3494195 = 5241293) B5241293
theorem B8278337 : Blo 1530462 8278337 := bstep (se 2 (by rfl) ⟨3104376, by rfl⟩ : syracuseStep 8278337 = 6208753) B6208753
theorem B2584919 : Blo 1530462 2584919 := bstep (se 1 (by rfl) ⟨1938689, by rfl⟩ : syracuseStep 2584919 = 3877379) B3877379
theorem B59683189 : Blo 1530462 59683189 := bstep (se 5 (by rfl) ⟨2797649, by rfl⟩ : syracuseStep 59683189 = 5595299) B5595299
theorem B2298251 : Blo 1530462 2298251 := bstep (se 1 (by rfl) ⟨1723688, by rfl⟩ : syracuseStep 2298251 = 3447377) B3447377
theorem B2298263 : Blo 1530462 2298263 := bstep (se 1 (by rfl) ⟨1723697, by rfl⟩ : syracuseStep 2298263 = 3447395) B3447395
theorem B3445145 : Blo 1530462 3445145 := bstep (se 2 (by rfl) ⟨1291929, by rfl⟩ : syracuseStep 3445145 = 2583859) B2583859
theorem B19632563 : Blo 1530462 19632563 := bstep (se 1 (by rfl) ⟨14724422, by rfl⟩ : syracuseStep 19632563 = 29448845) B29448845
theorem B2585047 : Blo 1530462 2585047 := bstep (se 1 (by rfl) ⟨1938785, by rfl⟩ : syracuseStep 2585047 = 3877571) B3877571
theorem B2298329 : Blo 1530462 2298329 := bstep (se 2 (by rfl) ⟨861873, by rfl⟩ : syracuseStep 2298329 = 1723747) B1723747
theorem B3445235 : Blo 1530462 3445235 := bstep (se 1 (by rfl) ⟨2583926, by rfl⟩ : syracuseStep 3445235 = 5167853) B5167853
theorem B3494387 : Blo 1530462 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B3445271 : Blo 1530462 3445271 := bstep (se 1 (by rfl) ⟨2583953, by rfl⟩ : syracuseStep 3445271 = 5167907) B5167907
theorem B2298443 : Blo 1530462 2298443 := bstep (se 1 (by rfl) ⟨1723832, by rfl⟩ : syracuseStep 2298443 = 3447665) B3447665
theorem B2298455 : Blo 1530462 2298455 := bstep (se 1 (by rfl) ⟨1723841, by rfl⟩ : syracuseStep 2298455 = 3447683) B3447683
theorem B4903517 : Blo 1530462 4903517 := bstep (se 3 (by rfl) ⟨919409, by rfl⟩ : syracuseStep 4903517 = 1838819) B1838819
theorem B2298521 : Blo 1530462 2298521 := bstep (se 2 (by rfl) ⟨861945, by rfl⟩ : syracuseStep 2298521 = 1723891) B1723891
theorem B5165747 : Blo 1530462 5165747 := bstep (se 1 (by rfl) ⟨3874310, by rfl⟩ : syracuseStep 5165747 = 7748621) B7748621
theorem B3445451 : Blo 1530462 3445451 := bstep (se 1 (by rfl) ⟨2584088, by rfl⟩ : syracuseStep 3445451 = 5168177) B5168177
theorem B6984413 : Blo 1530462 6984413 := bstep (se 3 (by rfl) ⟨1309577, by rfl⟩ : syracuseStep 6984413 = 2619155) B2619155
theorem B3445505 : Blo 1530462 3445505 := bstep (se 2 (by rfl) ⟨1292064, by rfl⟩ : syracuseStep 3445505 = 2584129) B2584129
theorem B2298635 : Blo 1530462 2298635 := bstep (se 1 (by rfl) ⟨1723976, by rfl⟩ : syracuseStep 2298635 = 3447953) B3447953
theorem B2298647 : Blo 1530462 2298647 := bstep (se 1 (by rfl) ⟨1723985, by rfl⟩ : syracuseStep 2298647 = 3447971) B3447971
theorem B15717185 : Blo 1530462 15717185 := bstep (se 2 (by rfl) ⟨5893944, by rfl⟩ : syracuseStep 15717185 = 11787889) B11787889
theorem B8622949 : Blo 1530462 8622949 := bstep (se 4 (by rfl) ⟨808401, by rfl⟩ : syracuseStep 8622949 = 1616803) B1616803
theorem B6984593 : Blo 1530462 6984593 := bstep (se 2 (by rfl) ⟨2619222, by rfl⟩ : syracuseStep 6984593 = 5238445) B5238445
theorem B1635223 : Blo 1530462 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B5166017 : Blo 1530462 5166017 := bstep (se 2 (by rfl) ⟨1937256, by rfl⟩ : syracuseStep 5166017 = 3874513) B3874513
theorem B4658123 : Blo 1530462 4658123 := bstep (se 1 (by rfl) ⟨3493592, by rfl⟩ : syracuseStep 4658123 = 6987185) B6987185
theorem B2454475 : Blo 1530462 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B3445721 : Blo 1530462 3445721 := bstep (se 2 (by rfl) ⟨1292145, by rfl⟩ : syracuseStep 3445721 = 2584291) B2584291
theorem B7173137 : Blo 1530462 7173137 := bstep (se 2 (by rfl) ⟨2689926, by rfl⟩ : syracuseStep 7173137 = 5379853) B5379853
theorem B3445811 : Blo 1530462 3445811 := bstep (se 1 (by rfl) ⟨2584358, by rfl⟩ : syracuseStep 3445811 = 5168717) B5168717
theorem B13079627 : Blo 1530462 13079627 := bstep (se 1 (by rfl) ⟨9809720, by rfl⟩ : syracuseStep 13079627 = 19619441) B19619441
theorem B2585675 : Blo 1530462 2585675 := bstep (se 1 (by rfl) ⟨1939256, by rfl⟩ : syracuseStep 2585675 = 3878513) B3878513
theorem B3445847 : Blo 1530462 3445847 := bstep (se 1 (by rfl) ⟨2584385, by rfl⟩ : syracuseStep 3445847 = 5168771) B5168771
theorem B1938583 : Blo 1530462 1938583 := bstep (se 1 (by rfl) ⟨1453937, by rfl⟩ : syracuseStep 1938583 = 2907875) B2907875
theorem B5813441 : Blo 1530462 5813441 := bstep (se 2 (by rfl) ⟨2180040, by rfl⟩ : syracuseStep 5813441 = 4360081) B4360081
theorem B2585803 : Blo 1530462 2585803 := bstep (se 1 (by rfl) ⟨1939352, by rfl⟩ : syracuseStep 2585803 = 3878705) B3878705
theorem B3446027 : Blo 1530462 3446027 := bstep (se 1 (by rfl) ⟨2584520, by rfl⟩ : syracuseStep 3446027 = 5169041) B5169041
theorem B3446081 : Blo 1530462 3446081 := bstep (se 2 (by rfl) ⟨1292280, by rfl⟩ : syracuseStep 3446081 = 2584561) B2584561
theorem B1635671 : Blo 1530462 1635671 := bstep (se 1 (by rfl) ⟨1226753, by rfl⟩ : syracuseStep 1635671 = 2453507) B2453507
theorem B2585945 : Blo 1530462 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B7755101 : Blo 1530462 7755101 := bstep (se 3 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 7755101 = 2908163) B2908163
theorem B13088101 : Blo 1530462 13088101 := bstep (se 4 (by rfl) ⟨1227009, by rfl⟩ : syracuseStep 13088101 = 2454019) B2454019
theorem B5166557 : Blo 1530462 5166557 := bstep (se 3 (by rfl) ⟨968729, by rfl⟩ : syracuseStep 5166557 = 1937459) B1937459
theorem B3446297 : Blo 1530462 3446297 := bstep (se 2 (by rfl) ⟨1292361, by rfl⟩ : syracuseStep 3446297 = 2584723) B2584723
theorem B3446387 : Blo 1530462 3446387 := bstep (se 1 (by rfl) ⟨2584790, by rfl⟩ : syracuseStep 3446387 = 5169581) B5169581
theorem B17675927 : Blo 1530462 17675927 := bstep (se 1 (by rfl) ⟨13256945, by rfl⟩ : syracuseStep 17675927 = 26513891) B26513891
theorem B3446423 : Blo 1530462 3446423 := bstep (se 1 (by rfl) ⟨2584817, by rfl⟩ : syracuseStep 3446423 = 5169635) B5169635
theorem B1636043 : Blo 1530462 1636043 := bstep (se 1 (by rfl) ⟨1227032, by rfl⟩ : syracuseStep 1636043 = 2454065) B2454065
theorem B6985433 : Blo 1530462 6985433 := bstep (se 2 (by rfl) ⟨2619537, by rfl⟩ : syracuseStep 6985433 = 5239075) B5239075
theorem B3929879 : Blo 1530462 3929879 := bstep (se 1 (by rfl) ⟨2947409, by rfl⟩ : syracuseStep 3929879 = 5894819) B5894819
theorem B2488087 : Blo 1530462 2488087 := bstep (se 1 (by rfl) ⟨1866065, by rfl⟩ : syracuseStep 2488087 = 3732131) B3732131
theorem B2758465 : Blo 1530462 2758465 := bstep (se 2 (by rfl) ⟨1034424, by rfl⟩ : syracuseStep 2758465 = 2068849) B2068849
theorem B2905931 : Blo 1530462 2905931 := bstep (se 1 (by rfl) ⟨2179448, by rfl⟩ : syracuseStep 2905931 = 4358897) B4358897
theorem B3446603 : Blo 1530462 3446603 := bstep (se 1 (by rfl) ⟨2584952, by rfl⟩ : syracuseStep 3446603 = 5169905) B5169905
theorem B2045785 : Blo 1530462 2045785 := bstep (se 2 (by rfl) ⟨767169, by rfl⟩ : syracuseStep 2045785 = 1534339) B1534339
theorem B3446657 : Blo 1530462 3446657 := bstep (se 2 (by rfl) ⟨1292496, by rfl⟩ : syracuseStep 3446657 = 2584993) B2584993
theorem B1939403 : Blo 1530462 1939403 := bstep (se 1 (by rfl) ⟨1454552, by rfl⟩ : syracuseStep 1939403 = 2909105) B2909105
theorem B7362521 : Blo 1530462 7362521 := bstep (se 2 (by rfl) ⟨2760945, by rfl⟩ : syracuseStep 7362521 = 5521891) B5521891
theorem B2906113 : Blo 1530462 2906113 := bstep (se 2 (by rfl) ⟨1089792, by rfl⟩ : syracuseStep 2906113 = 2179585) B2179585
theorem B13965317 : Blo 1530462 13965317 := bstep (se 4 (by rfl) ⟨1309248, by rfl⟩ : syracuseStep 13965317 = 2618497) B2618497
theorem B5519411 : Blo 1530462 5519411 := bstep (se 1 (by rfl) ⟨4139558, by rfl⟩ : syracuseStep 5519411 = 8279117) B8279117
theorem B1964119 : Blo 1530462 1964119 := bstep (se 1 (by rfl) ⟨1473089, by rfl⟩ : syracuseStep 1964119 = 2946179) B2946179
theorem B3446873 : Blo 1530462 3446873 := bstep (se 2 (by rfl) ⟨1292577, by rfl⟩ : syracuseStep 3446873 = 2585155) B2585155
theorem B3446963 : Blo 1530462 3446963 := bstep (se 1 (by rfl) ⟨2585222, by rfl⟩ : syracuseStep 3446963 = 5170445) B5170445
theorem B3446999 : Blo 1530462 3446999 := bstep (se 1 (by rfl) ⟨2585249, by rfl⟩ : syracuseStep 3446999 = 5170499) B5170499
theorem B13089059 : Blo 1530462 13089059 := bstep (se 1 (by rfl) ⟨9816794, by rfl⟩ : syracuseStep 13089059 = 19633589) B19633589
theorem B2906455 : Blo 1530462 2906455 := bstep (se 1 (by rfl) ⟨2179841, by rfl⟩ : syracuseStep 2906455 = 4359683) B4359683
theorem B3447179 : Blo 1530462 3447179 := bstep (se 1 (by rfl) ⟨2585384, by rfl⟩ : syracuseStep 3447179 = 5170769) B5170769
theorem B3447233 : Blo 1530462 3447233 := bstep (se 2 (by rfl) ⟨1292712, by rfl⟩ : syracuseStep 3447233 = 2585425) B2585425
theorem B2906675 : Blo 1530462 2906675 := bstep (se 1 (by rfl) ⟨2180006, by rfl⟩ : syracuseStep 2906675 = 4360013) B4360013
theorem B5167691 : Blo 1530462 5167691 := bstep (se 1 (by rfl) ⟨3875768, by rfl⟩ : syracuseStep 5167691 = 7751537) B7751537
theorem B1530475 : Blo 1530462 1530475 := bstep (se 1 (by rfl) ⟨1147856, by rfl⟩ : syracuseStep 1530475 = 2295713) B2295713
theorem B1530487 : Blo 1530462 1530487 := bstep (se 1 (by rfl) ⟨1147865, by rfl⟩ : syracuseStep 1530487 = 2295731) B2295731
theorem B1530507 : Blo 1530462 1530507 := bstep (se 1 (by rfl) ⟨1147880, by rfl⟩ : syracuseStep 1530507 = 2295761) B2295761
theorem B5814929 : Blo 1530462 5814929 := bstep (se 2 (by rfl) ⟨2180598, by rfl⟩ : syracuseStep 5814929 = 4361197) B4361197
theorem B1530519 : Blo 1530462 1530519 := bstep (se 1 (by rfl) ⟨1147889, by rfl⟩ : syracuseStep 1530519 = 2295779) B2295779
theorem B3447449 : Blo 1530462 3447449 := bstep (se 2 (by rfl) ⟨1292793, by rfl⟩ : syracuseStep 3447449 = 2585587) B2585587
theorem B1530539 : Blo 1530462 1530539 := bstep (se 1 (by rfl) ⟨1147904, by rfl⟩ : syracuseStep 1530539 = 2295809) B2295809
theorem B8723123 : Blo 1530462 8723123 := bstep (se 1 (by rfl) ⟨6542342, by rfl⟩ : syracuseStep 8723123 = 13084685) B13084685
theorem B1530551 : Blo 1530462 1530551 := bstep (se 1 (by rfl) ⟨1147913, by rfl⟩ : syracuseStep 1530551 = 2295827) B2295827
theorem B1530571 : Blo 1530462 1530571 := bstep (se 1 (by rfl) ⟨1147928, by rfl⟩ : syracuseStep 1530571 = 2295857) B2295857
theorem B1530583 : Blo 1530462 1530583 := bstep (se 1 (by rfl) ⟨1147937, by rfl⟩ : syracuseStep 1530583 = 2295875) B2295875
theorem B1530603 : Blo 1530462 1530603 := bstep (se 1 (by rfl) ⟨1147952, by rfl⟩ : syracuseStep 1530603 = 2295905) B2295905
theorem B3447539 : Blo 1530462 3447539 := bstep (se 1 (by rfl) ⟨2585654, by rfl⟩ : syracuseStep 3447539 = 5171309) B5171309
theorem B1530615 : Blo 1530462 1530615 := bstep (se 1 (by rfl) ⟨1147961, by rfl⟩ : syracuseStep 1530615 = 2295923) B2295923
theorem B1530635 : Blo 1530462 1530635 := bstep (se 1 (by rfl) ⟨1147976, by rfl⟩ : syracuseStep 1530635 = 2295953) B2295953
theorem B1530647 : Blo 1530462 1530647 := bstep (se 1 (by rfl) ⟨1147985, by rfl⟩ : syracuseStep 1530647 = 2295971) B2295971
theorem B2906903 : Blo 1530462 2906903 := bstep (se 1 (by rfl) ⟨2180177, by rfl⟩ : syracuseStep 2906903 = 4360355) B4360355
theorem B3447575 : Blo 1530462 3447575 := bstep (se 1 (by rfl) ⟨2585681, by rfl⟩ : syracuseStep 3447575 = 5171363) B5171363
theorem B1530667 : Blo 1530462 1530667 := bstep (se 1 (by rfl) ⟨1148000, by rfl⟩ : syracuseStep 1530667 = 2296001) B2296001
theorem B6208301 : Blo 1530462 6208301 := bstep (se 3 (by rfl) ⟨1164056, by rfl⟩ : syracuseStep 6208301 = 2328113) B2328113
theorem B1530679 : Blo 1530462 1530679 := bstep (se 1 (by rfl) ⟨1148009, by rfl⟩ : syracuseStep 1530679 = 2296019) B2296019
theorem B1530699 : Blo 1530462 1530699 := bstep (se 1 (by rfl) ⟨1148024, by rfl⟩ : syracuseStep 1530699 = 2296049) B2296049
theorem B1530711 : Blo 1530462 1530711 := bstep (se 1 (by rfl) ⟨1148033, by rfl⟩ : syracuseStep 1530711 = 2296067) B2296067
theorem B5167961 : Blo 1530462 5167961 := bstep (se 2 (by rfl) ⟨1937985, by rfl⟩ : syracuseStep 5167961 = 3875971) B3875971
theorem B5241689 : Blo 1530462 5241689 := bstep (se 2 (by rfl) ⟨1965633, by rfl⟩ : syracuseStep 5241689 = 3931267) B3931267
theorem B1530731 : Blo 1530462 1530731 := bstep (se 1 (by rfl) ⟨1148048, by rfl⟩ : syracuseStep 1530731 = 2296097) B2296097
theorem B1530743 : Blo 1530462 1530743 := bstep (se 1 (by rfl) ⟨1148057, by rfl⟩ : syracuseStep 1530743 = 2296115) B2296115
theorem B1530763 : Blo 1530462 1530763 := bstep (se 1 (by rfl) ⟨1148072, by rfl⟩ : syracuseStep 1530763 = 2296145) B2296145
theorem B1530775 : Blo 1530462 1530775 := bstep (se 1 (by rfl) ⟨1148081, by rfl⟩ : syracuseStep 1530775 = 2296163) B2296163
theorem B3316633 : Blo 1530462 3316633 := bstep (se 2 (by rfl) ⟨1243737, by rfl⟩ : syracuseStep 3316633 = 2487475) B2487475
theorem B1530795 : Blo 1530462 1530795 := bstep (se 1 (by rfl) ⟨1148096, by rfl⟩ : syracuseStep 1530795 = 2296193) B2296193
theorem B1530807 : Blo 1530462 1530807 := bstep (se 1 (by rfl) ⟨1148105, by rfl⟩ : syracuseStep 1530807 = 2296211) B2296211
theorem B1530827 : Blo 1530462 1530827 := bstep (se 1 (by rfl) ⟨1148120, by rfl⟩ : syracuseStep 1530827 = 2296241) B2296241
theorem B3447755 : Blo 1530462 3447755 := bstep (se 1 (by rfl) ⟨2585816, by rfl⟩ : syracuseStep 3447755 = 5171633) B5171633
theorem B1530839 : Blo 1530462 1530839 := bstep (se 1 (by rfl) ⟨1148129, by rfl⟩ : syracuseStep 1530839 = 2296259) B2296259
theorem B1530859 : Blo 1530462 1530859 := bstep (se 1 (by rfl) ⟨1148144, by rfl⟩ : syracuseStep 1530859 = 2296289) B2296289
theorem B1530871 : Blo 1530462 1530871 := bstep (se 1 (by rfl) ⟨1148153, by rfl⟩ : syracuseStep 1530871 = 2296307) B2296307
theorem B3447809 : Blo 1530462 3447809 := bstep (se 2 (by rfl) ⟨1292928, by rfl⟩ : syracuseStep 3447809 = 2585857) B2585857
theorem B1530891 : Blo 1530462 1530891 := bstep (se 1 (by rfl) ⟨1148168, by rfl⟩ : syracuseStep 1530891 = 2296337) B2296337
theorem B1530903 : Blo 1530462 1530903 := bstep (se 1 (by rfl) ⟨1148177, by rfl⟩ : syracuseStep 1530903 = 2296355) B2296355
theorem B2907161 : Blo 1530462 2907161 := bstep (se 2 (by rfl) ⟨1090185, by rfl⟩ : syracuseStep 2907161 = 2180371) B2180371
theorem B2620441 : Blo 1530462 2620441 := bstep (se 2 (by rfl) ⟨982665, by rfl⟩ : syracuseStep 2620441 = 1965331) B1965331
theorem B17685539 : Blo 1530462 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B1530923 : Blo 1530462 1530923 := bstep (se 1 (by rfl) ⟨1148192, by rfl⟩ : syracuseStep 1530923 = 2296385) B2296385
theorem B1530935 : Blo 1530462 1530935 := bstep (se 1 (by rfl) ⟨1148201, by rfl⟩ : syracuseStep 1530935 = 2296403) B2296403
theorem B7076929 : Blo 1530462 7076929 := bstep (se 2 (by rfl) ⟨2653848, by rfl⟩ : syracuseStep 7076929 = 5307697) B5307697
theorem B6290507 : Blo 1530462 6290507 := bstep (se 1 (by rfl) ⟨4717880, by rfl⟩ : syracuseStep 6290507 = 9435761) B9435761
theorem B1530955 : Blo 1530462 1530955 := bstep (se 1 (by rfl) ⟨1148216, by rfl⟩ : syracuseStep 1530955 = 2296433) B2296433
theorem B1530967 : Blo 1530462 1530967 := bstep (se 1 (by rfl) ⟨1148225, by rfl⟩ : syracuseStep 1530967 = 2296451) B2296451
theorem B5815385 : Blo 1530462 5815385 := bstep (se 2 (by rfl) ⟨2180769, by rfl⟩ : syracuseStep 5815385 = 4361539) B4361539
theorem B1530987 : Blo 1530462 1530987 := bstep (se 1 (by rfl) ⟨1148240, by rfl⟩ : syracuseStep 1530987 = 2296481) B2296481
theorem B1530999 : Blo 1530462 1530999 := bstep (se 1 (by rfl) ⟨1148249, by rfl⟩ : syracuseStep 1530999 = 2296499) B2296499
theorem B1531019 : Blo 1530462 1531019 := bstep (se 1 (by rfl) ⟨1148264, by rfl⟩ : syracuseStep 1531019 = 2296529) B2296529
theorem B1531031 : Blo 1530462 1531031 := bstep (se 1 (by rfl) ⟨1148273, by rfl⟩ : syracuseStep 1531031 = 2296547) B2296547
theorem B1531051 : Blo 1530462 1531051 := bstep (se 1 (by rfl) ⟨1148288, by rfl⟩ : syracuseStep 1531051 = 2296577) B2296577
theorem B1531063 : Blo 1530462 1531063 := bstep (se 1 (by rfl) ⟨1148297, by rfl⟩ : syracuseStep 1531063 = 2296595) B2296595
theorem B1531083 : Blo 1530462 1531083 := bstep (se 1 (by rfl) ⟨1148312, by rfl⟩ : syracuseStep 1531083 = 2296625) B2296625
theorem B1531095 : Blo 1530462 1531095 := bstep (se 1 (by rfl) ⟨1148321, by rfl⟩ : syracuseStep 1531095 = 2296643) B2296643
theorem B3448025 : Blo 1530462 3448025 := bstep (se 2 (by rfl) ⟨1293009, by rfl⟩ : syracuseStep 3448025 = 2586019) B2586019
theorem B1531115 : Blo 1530462 1531115 := bstep (se 1 (by rfl) ⟨1148336, by rfl⟩ : syracuseStep 1531115 = 2296673) B2296673
theorem B1531127 : Blo 1530462 1531127 := bstep (se 1 (by rfl) ⟨1148345, by rfl⟩ : syracuseStep 1531127 = 2296691) B2296691
theorem B1531147 : Blo 1530462 1531147 := bstep (se 1 (by rfl) ⟨1148360, by rfl⟩ : syracuseStep 1531147 = 2296721) B2296721
theorem B1531159 : Blo 1530462 1531159 := bstep (se 1 (by rfl) ⟨1148369, by rfl⟩ : syracuseStep 1531159 = 2296739) B2296739
theorem B1531179 : Blo 1530462 1531179 := bstep (se 1 (by rfl) ⟨1148384, by rfl⟩ : syracuseStep 1531179 = 2296769) B2296769
theorem B5815597 : Blo 1530462 5815597 := bstep (se 3 (by rfl) ⟨1090424, by rfl⟩ : syracuseStep 5815597 = 2180849) B2180849
theorem B1531191 : Blo 1530462 1531191 := bstep (se 1 (by rfl) ⟨1148393, by rfl⟩ : syracuseStep 1531191 = 2296787) B2296787
theorem B1531211 : Blo 1530462 1531211 := bstep (se 1 (by rfl) ⟨1148408, by rfl⟩ : syracuseStep 1531211 = 2296817) B2296817
theorem B1531223 : Blo 1530462 1531223 := bstep (se 1 (by rfl) ⟨1148417, by rfl⟩ : syracuseStep 1531223 = 2296835) B2296835
theorem B26525029 : Blo 1530462 26525029 := bstep (se 4 (by rfl) ⟨2486721, by rfl⟩ : syracuseStep 26525029 = 4973443) B4973443
theorem B1531243 : Blo 1530462 1531243 := bstep (se 1 (by rfl) ⟨1148432, by rfl⟩ : syracuseStep 1531243 = 2296865) B2296865
theorem B1531255 : Blo 1530462 1531255 := bstep (se 1 (by rfl) ⟨1148441, by rfl⟩ : syracuseStep 1531255 = 2296883) B2296883
theorem B1531275 : Blo 1530462 1531275 := bstep (se 1 (by rfl) ⟨1148456, by rfl⟩ : syracuseStep 1531275 = 2296913) B2296913
theorem B1531287 : Blo 1530462 1531287 := bstep (se 1 (by rfl) ⟨1148465, by rfl⟩ : syracuseStep 1531287 = 2296931) B2296931
theorem B7757207 : Blo 1530462 7757207 := bstep (se 1 (by rfl) ⟨5817905, by rfl⟩ : syracuseStep 7757207 = 11635811) B11635811
theorem B1531307 : Blo 1530462 1531307 := bstep (se 1 (by rfl) ⟨1148480, by rfl⟩ : syracuseStep 1531307 = 2296961) B2296961
theorem B2907571 : Blo 1530462 2907571 := bstep (se 1 (by rfl) ⟨2180678, by rfl⟩ : syracuseStep 2907571 = 4361357) B4361357
theorem B1531319 : Blo 1530462 1531319 := bstep (se 1 (by rfl) ⟨1148489, by rfl⟩ : syracuseStep 1531319 = 2296979) B2296979
theorem B1531339 : Blo 1530462 1531339 := bstep (se 1 (by rfl) ⟨1148504, by rfl⟩ : syracuseStep 1531339 = 2297009) B2297009
theorem B1531351 : Blo 1530462 1531351 := bstep (se 1 (by rfl) ⟨1148513, by rfl⟩ : syracuseStep 1531351 = 2297027) B2297027
theorem B1531371 : Blo 1530462 1531371 := bstep (se 1 (by rfl) ⟨1148528, by rfl⟩ : syracuseStep 1531371 = 2297057) B2297057
theorem B1531383 : Blo 1530462 1531383 := bstep (se 1 (by rfl) ⟨1148537, by rfl⟩ : syracuseStep 1531383 = 2297075) B2297075
theorem B1531403 : Blo 1530462 1531403 := bstep (se 1 (by rfl) ⟨1148552, by rfl⟩ : syracuseStep 1531403 = 2297105) B2297105
theorem B22076945 : Blo 1530462 22076945 := bstep (se 2 (by rfl) ⟨8278854, by rfl⟩ : syracuseStep 22076945 = 16557709) B16557709
theorem B1531415 : Blo 1530462 1531415 := bstep (se 1 (by rfl) ⟨1148561, by rfl⟩ : syracuseStep 1531415 = 2297123) B2297123
theorem B5168663 : Blo 1530462 5168663 := bstep (se 1 (by rfl) ⟨3876497, by rfl⟩ : syracuseStep 5168663 = 7752995) B7752995
theorem B1531435 : Blo 1530462 1531435 := bstep (se 1 (by rfl) ⟨1148576, by rfl⟩ : syracuseStep 1531435 = 2297153) B2297153
theorem B6626861 : Blo 1530462 6626861 := bstep (se 3 (by rfl) ⟨1242536, by rfl⟩ : syracuseStep 6626861 = 2485073) B2485073
theorem B1531447 : Blo 1530462 1531447 := bstep (se 1 (by rfl) ⟨1148585, by rfl⟩ : syracuseStep 1531447 = 2297171) B2297171
theorem B11042369 : Blo 1530462 11042369 := bstep (se 2 (by rfl) ⟨4140888, by rfl⟩ : syracuseStep 11042369 = 8281777) B8281777
theorem B1531467 : Blo 1530462 1531467 := bstep (se 1 (by rfl) ⟨1148600, by rfl⟩ : syracuseStep 1531467 = 2297201) B2297201
theorem B19627595 : Blo 1530462 19627595 := bstep (se 1 (by rfl) ⟨14720696, by rfl⟩ : syracuseStep 19627595 = 29441393) B29441393
theorem B1531479 : Blo 1530462 1531479 := bstep (se 1 (by rfl) ⟨1148609, by rfl⟩ : syracuseStep 1531479 = 2297219) B2297219
theorem B5815901 : Blo 1530462 5815901 := bstep (se 3 (by rfl) ⟨1090481, by rfl⟩ : syracuseStep 5815901 = 2180963) B2180963
theorem B1531499 : Blo 1530462 1531499 := bstep (se 1 (by rfl) ⟨1148624, by rfl⟩ : syracuseStep 1531499 = 2297249) B2297249
theorem B1531511 : Blo 1530462 1531511 := bstep (se 1 (by rfl) ⟨1148633, by rfl⟩ : syracuseStep 1531511 = 2297267) B2297267
theorem B1531531 : Blo 1530462 1531531 := bstep (se 1 (by rfl) ⟨1148648, by rfl⟩ : syracuseStep 1531531 = 2297297) B2297297
theorem B1531543 : Blo 1530462 1531543 := bstep (se 1 (by rfl) ⟨1148657, by rfl⟩ : syracuseStep 1531543 = 2297315) B2297315
theorem B1531563 : Blo 1530462 1531563 := bstep (se 1 (by rfl) ⟨1148672, by rfl⟩ : syracuseStep 1531563 = 2297345) B2297345
theorem B1531575 : Blo 1530462 1531575 := bstep (se 1 (by rfl) ⟨1148681, by rfl⟩ : syracuseStep 1531575 = 2297363) B2297363
theorem B3145409 : Blo 1530462 3145409 := bstep (se 2 (by rfl) ⟨1179528, by rfl⟩ : syracuseStep 3145409 = 2359057) B2359057
theorem B1531595 : Blo 1530462 1531595 := bstep (se 1 (by rfl) ⟨1148696, by rfl⟩ : syracuseStep 1531595 = 2297393) B2297393
theorem B1531607 : Blo 1530462 1531607 := bstep (se 1 (by rfl) ⟨1148705, by rfl⟩ : syracuseStep 1531607 = 2297411) B2297411
theorem B1531627 : Blo 1530462 1531627 := bstep (se 1 (by rfl) ⟨1148720, by rfl⟩ : syracuseStep 1531627 = 2297441) B2297441
theorem B1531639 : Blo 1530462 1531639 := bstep (se 1 (by rfl) ⟨1148729, by rfl⟩ : syracuseStep 1531639 = 2297459) B2297459
theorem B1531659 : Blo 1530462 1531659 := bstep (se 1 (by rfl) ⟨1148744, by rfl⟩ : syracuseStep 1531659 = 2297489) B2297489
theorem B1531671 : Blo 1530462 1531671 := bstep (se 1 (by rfl) ⟨1148753, by rfl⟩ : syracuseStep 1531671 = 2297507) B2297507
theorem B2621207 : Blo 1530462 2621207 := bstep (se 1 (by rfl) ⟨1965905, by rfl⟩ : syracuseStep 2621207 = 3931811) B3931811
theorem B1531691 : Blo 1530462 1531691 := bstep (se 1 (by rfl) ⟨1148768, by rfl⟩ : syracuseStep 1531691 = 2297537) B2297537
theorem B1531703 : Blo 1530462 1531703 := bstep (se 1 (by rfl) ⟨1148777, by rfl⟩ : syracuseStep 1531703 = 2297555) B2297555
theorem B3874625 : Blo 1530462 3874625 := bstep (se 2 (by rfl) ⟨1452984, by rfl⟩ : syracuseStep 3874625 = 2905969) B2905969
theorem B1531723 : Blo 1530462 1531723 := bstep (se 1 (by rfl) ⟨1148792, by rfl⟩ : syracuseStep 1531723 = 2297585) B2297585
theorem B1531735 : Blo 1530462 1531735 := bstep (se 1 (by rfl) ⟨1148801, by rfl⟩ : syracuseStep 1531735 = 2297603) B2297603
theorem B1531755 : Blo 1530462 1531755 := bstep (se 1 (by rfl) ⟨1148816, by rfl⟩ : syracuseStep 1531755 = 2297633) B2297633
theorem B1531767 : Blo 1530462 1531767 := bstep (se 1 (by rfl) ⟨1148825, by rfl⟩ : syracuseStep 1531767 = 2297651) B2297651
theorem B1531787 : Blo 1530462 1531787 := bstep (se 1 (by rfl) ⟨1148840, by rfl⟩ : syracuseStep 1531787 = 2297681) B2297681
theorem B1531799 : Blo 1530462 1531799 := bstep (se 1 (by rfl) ⟨1148849, by rfl⟩ : syracuseStep 1531799 = 2297699) B2297699
theorem B2760599 : Blo 1530462 2760599 := bstep (se 1 (by rfl) ⟨2070449, by rfl⟩ : syracuseStep 2760599 = 4140899) B4140899
theorem B2908057 : Blo 1530462 2908057 := bstep (se 2 (by rfl) ⟨1090521, by rfl⟩ : syracuseStep 2908057 = 2181043) B2181043
theorem B1531819 : Blo 1530462 1531819 := bstep (se 1 (by rfl) ⟨1148864, by rfl⟩ : syracuseStep 1531819 = 2297729) B2297729
theorem B1531831 : Blo 1530462 1531831 := bstep (se 1 (by rfl) ⟨1148873, by rfl⟩ : syracuseStep 1531831 = 2297747) B2297747
theorem B1531851 : Blo 1530462 1531851 := bstep (se 1 (by rfl) ⟨1148888, by rfl⟩ : syracuseStep 1531851 = 2297777) B2297777
theorem B1531863 : Blo 1530462 1531863 := bstep (se 1 (by rfl) ⟨1148897, by rfl⟩ : syracuseStep 1531863 = 2297795) B2297795
theorem B7749593 : Blo 1530462 7749593 := bstep (se 2 (by rfl) ⟨2906097, by rfl⟩ : syracuseStep 7749593 = 5812195) B5812195
theorem B1531883 : Blo 1530462 1531883 := bstep (se 1 (by rfl) ⟨1148912, by rfl⟩ : syracuseStep 1531883 = 2297825) B2297825
theorem B1531895 : Blo 1530462 1531895 := bstep (se 1 (by rfl) ⟨1148921, by rfl⟩ : syracuseStep 1531895 = 2297843) B2297843
theorem B3874817 : Blo 1530462 3874817 := bstep (se 2 (by rfl) ⟨1453056, by rfl⟩ : syracuseStep 3874817 = 2906113) B2906113
theorem B1531911 : Blo 1530462 1531911 := bstep (se 1 (by rfl) ⟨1148933, by rfl⟩ : syracuseStep 1531911 = 2297867) B2297867
theorem B12410891 : Blo 1530462 12410891 := bstep (se 1 (by rfl) ⟨9308168, by rfl⟩ : syracuseStep 12410891 = 18616337) B18616337
theorem B3678223 : Blo 1530462 3678223 := bstep (se 1 (by rfl) ⟨2758667, by rfl⟩ : syracuseStep 3678223 = 5517335) B5517335
theorem B1531919 : Blo 1530462 1531919 := bstep (se 1 (by rfl) ⟨1148939, by rfl⟩ : syracuseStep 1531919 = 2297879) B2297879
theorem B16564247 : Blo 1530462 16564247 := bstep (se 1 (by rfl) ⟨12423185, by rfl⟩ : syracuseStep 16564247 = 24846371) B24846371
theorem B1531963 : Blo 1530462 1531963 := bstep (se 1 (by rfl) ⟨1148972, by rfl⟩ : syracuseStep 1531963 = 2297945) B2297945
theorem B5816387 : Blo 1530462 5816387 := bstep (se 1 (by rfl) ⟨4362290, by rfl⟩ : syracuseStep 5816387 = 8724581) B8724581
theorem B1532039 : Blo 1530462 1532039 := bstep (se 1 (by rfl) ⟨1149029, by rfl⟩ : syracuseStep 1532039 = 2298059) B2298059
theorem B1532047 : Blo 1530462 1532047 := bstep (se 1 (by rfl) ⟨1149035, by rfl⟩ : syracuseStep 1532047 = 2298071) B2298071
theorem B1532091 : Blo 1530462 1532091 := bstep (se 1 (by rfl) ⟨1149068, by rfl⟩ : syracuseStep 1532091 = 2298137) B2298137
theorem B7758017 : Blo 1530462 7758017 := bstep (se 2 (by rfl) ⟨2909256, by rfl⟩ : syracuseStep 7758017 = 5818513) B5818513
theorem B2908361 : Blo 1530462 2908361 := bstep (se 2 (by rfl) ⟨1090635, by rfl⟩ : syracuseStep 2908361 = 2181271) B2181271
theorem B8716517 : Blo 1530462 8716517 := bstep (se 4 (by rfl) ⟨817173, by rfl⟩ : syracuseStep 8716517 = 1634347) B1634347
theorem B1532167 : Blo 1530462 1532167 := bstep (se 1 (by rfl) ⟨1149125, by rfl⟩ : syracuseStep 1532167 = 2298251) B2298251
theorem B1532175 : Blo 1530462 1532175 := bstep (se 1 (by rfl) ⟨1149131, by rfl⟩ : syracuseStep 1532175 = 2298263) B2298263
theorem B1532219 : Blo 1530462 1532219 := bstep (se 1 (by rfl) ⟨1149164, by rfl⟩ : syracuseStep 1532219 = 2298329) B2298329
theorem B1532295 : Blo 1530462 1532295 := bstep (se 1 (by rfl) ⟨1149221, by rfl⟩ : syracuseStep 1532295 = 2298443) B2298443
theorem B1532303 : Blo 1530462 1532303 := bstep (se 1 (by rfl) ⟨1149227, by rfl⟩ : syracuseStep 1532303 = 2298455) B2298455
theorem B3269011 : Blo 1530462 3269011 := bstep (se 1 (by rfl) ⟨2451758, by rfl⟩ : syracuseStep 3269011 = 4903517) B4903517
theorem B1532347 : Blo 1530462 1532347 := bstep (se 1 (by rfl) ⟨1149260, by rfl⟩ : syracuseStep 1532347 = 2298521) B2298521
theorem B3875273 : Blo 1530462 3875273 := bstep (se 2 (by rfl) ⟨1453227, by rfl⟩ : syracuseStep 3875273 = 2906455) B2906455
theorem B79577585 : Blo 1530462 79577585 := bstep (se 2 (by rfl) ⟨29841594, by rfl⟩ : syracuseStep 79577585 = 59683189) B59683189
theorem B1532423 : Blo 1530462 1532423 := bstep (se 1 (by rfl) ⟨1149317, by rfl⟩ : syracuseStep 1532423 = 2298635) B2298635
theorem B5816843 : Blo 1530462 5816843 := bstep (se 1 (by rfl) ⟨4362632, by rfl⟩ : syracuseStep 5816843 = 8725265) B8725265
theorem B1532431 : Blo 1530462 1532431 := bstep (se 1 (by rfl) ⟨1149323, by rfl⟩ : syracuseStep 1532431 = 2298647) B2298647
theorem B10478123 : Blo 1530462 10478123 := bstep (se 1 (by rfl) ⟨7858592, by rfl⟩ : syracuseStep 10478123 = 15717185) B15717185
theorem B3105415 : Blo 1530462 3105415 := bstep (se 1 (by rfl) ⟨2329061, by rfl⟩ : syracuseStep 3105415 = 4658123) B4658123
theorem B17433305 : Blo 1530462 17433305 := bstep (se 2 (by rfl) ⟨6537489, by rfl⟩ : syracuseStep 17433305 = 13074979) B13074979
theorem B11633381 : Blo 1530462 11633381 := bstep (se 4 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 11633381 = 2181259) B2181259
theorem B8274703 : Blo 1530462 8274703 := bstep (se 1 (by rfl) ⟨6206027, by rfl⟩ : syracuseStep 8274703 = 12412055) B12412055
theorem B29442851 : Blo 1530462 29442851 := bstep (se 1 (by rfl) ⟨22082138, by rfl⟩ : syracuseStep 29442851 = 44164277) B44164277
theorem B3875627 : Blo 1530462 3875627 := bstep (se 1 (by rfl) ⟨2906720, by rfl⟩ : syracuseStep 3875627 = 5813441) B5813441
theorem B7357331 : Blo 1530462 7357331 := bstep (se 1 (by rfl) ⟨5517998, by rfl⟩ : syracuseStep 7357331 = 11035997) B11035997
theorem B5170067 : Blo 1530462 5170067 := bstep (se 1 (by rfl) ⟨3877550, by rfl⟩ : syracuseStep 5170067 = 7755101) B7755101
theorem B66208691 : Blo 1530462 66208691 := bstep (se 1 (by rfl) ⟨49656518, by rfl⟩ : syracuseStep 66208691 = 99313037) B99313037
theorem B11625605 : Blo 1530462 11625605 := bstep (se 4 (by rfl) ⟨1089900, by rfl⟩ : syracuseStep 11625605 = 2179801) B2179801
theorem B2180297 : Blo 1530462 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B4908347 : Blo 1530462 4908347 := bstep (se 1 (by rfl) ⟨3681260, by rfl⟩ : syracuseStep 4908347 = 7362521) B7362521
theorem B4359511 : Blo 1530462 4359511 := bstep (se 1 (by rfl) ⟨3269633, by rfl⟩ : syracuseStep 4359511 = 6539267) B6539267
theorem B3679607 : Blo 1530462 3679607 := bstep (se 1 (by rfl) ⟨2759705, by rfl⟩ : syracuseStep 3679607 = 5519411) B5519411
theorem B8726039 : Blo 1530462 8726039 := bstep (se 1 (by rfl) ⟨6544529, by rfl⟩ : syracuseStep 8726039 = 13089059) B13089059
theorem B4359739 : Blo 1530462 4359739 := bstep (se 1 (by rfl) ⟨3269804, by rfl⟩ : syracuseStep 4359739 = 6539609) B6539609
theorem B11044471 : Blo 1530462 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B4359865 : Blo 1530462 4359865 := bstep (se 2 (by rfl) ⟨1634949, by rfl⟩ : syracuseStep 4359865 = 3269899) B3269899
theorem B3876619 : Blo 1530462 3876619 := bstep (se 1 (by rfl) ⟨2907464, by rfl⟩ : syracuseStep 3876619 = 5814929) B5814929
theorem B1722127 : Blo 1530462 1722127 := bstep (se 1 (by rfl) ⟨1291595, by rfl⟩ : syracuseStep 1722127 = 2583191) B2583191
theorem B35366705 : Blo 1530462 35366705 := bstep (se 2 (by rfl) ⟨13262514, by rfl⟩ : syracuseStep 35366705 = 26525029) B26525029
theorem B17450801 : Blo 1530462 17450801 := bstep (se 2 (by rfl) ⟨6544050, by rfl⟩ : syracuseStep 17450801 = 13088101) B13088101
theorem B4138867 : Blo 1530462 4138867 := bstep (se 1 (by rfl) ⟨3104150, by rfl⟩ : syracuseStep 4138867 = 6208301) B6208301
theorem B2295695 : Blo 1530462 2295695 := bstep (se 1 (by rfl) ⟨1721771, by rfl⟩ : syracuseStep 2295695 = 3443543) B3443543
theorem B3876761 : Blo 1530462 3876761 := bstep (se 2 (by rfl) ⟨1453785, by rfl⟩ : syracuseStep 3876761 = 2907571) B2907571
theorem B2295737 : Blo 1530462 2295737 := bstep (se 2 (by rfl) ⟨860901, by rfl⟩ : syracuseStep 2295737 = 1721803) B1721803
theorem B2295815 : Blo 1530462 2295815 := bstep (se 1 (by rfl) ⟨1721861, by rfl⟩ : syracuseStep 2295815 = 3443723) B3443723
theorem B11790359 : Blo 1530462 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B2295851 : Blo 1530462 2295851 := bstep (se 1 (by rfl) ⟨1721888, by rfl⟩ : syracuseStep 2295851 = 3443777) B3443777
theorem B2181163 : Blo 1530462 2181163 := bstep (se 1 (by rfl) ⟨1635872, by rfl⟩ : syracuseStep 2181163 = 3271745) B3271745
theorem B24823853 : Blo 1530462 24823853 := bstep (se 3 (by rfl) ⟨4654472, by rfl⟩ : syracuseStep 24823853 = 9308945) B9308945
theorem B3876923 : Blo 1530462 3876923 := bstep (se 1 (by rfl) ⟨2907692, by rfl⟩ : syracuseStep 3876923 = 5815385) B5815385
theorem B10479677 : Blo 1530462 10479677 := bstep (se 3 (by rfl) ⟨1964939, by rfl⟩ : syracuseStep 10479677 = 3929879) B3929879
theorem B6989885 : Blo 1530462 6989885 := bstep (se 3 (by rfl) ⟨1310603, by rfl⟩ : syracuseStep 6989885 = 2621207) B2621207
theorem B2295881 : Blo 1530462 2295881 := bstep (se 2 (by rfl) ⟨860955, by rfl⟩ : syracuseStep 2295881 = 1721911) B1721911
theorem B17688709 : Blo 1530462 17688709 := bstep (se 4 (by rfl) ⟨1658316, by rfl⟩ : syracuseStep 17688709 = 3316633) B3316633
theorem B2295995 : Blo 1530462 2295995 := bstep (se 1 (by rfl) ⟨1721996, by rfl⟩ : syracuseStep 2295995 = 3443993) B3443993
theorem B2296055 : Blo 1530462 2296055 := bstep (se 1 (by rfl) ⟨1722041, by rfl⟩ : syracuseStep 2296055 = 3444083) B3444083
theorem B1722631 : Blo 1530462 1722631 := bstep (se 1 (by rfl) ⟨1291973, by rfl⟩ : syracuseStep 1722631 = 2583947) B2583947
theorem B2296079 : Blo 1530462 2296079 := bstep (se 1 (by rfl) ⟨1722059, by rfl⟩ : syracuseStep 2296079 = 3444119) B3444119
theorem B5171471 : Blo 1530462 5171471 := bstep (se 1 (by rfl) ⟨3878603, by rfl⟩ : syracuseStep 5171471 = 7757207) B7757207
theorem B2296121 : Blo 1530462 2296121 := bstep (se 2 (by rfl) ⟨861045, by rfl⟩ : syracuseStep 2296121 = 1722091) B1722091
theorem B4417907 : Blo 1530462 4417907 := bstep (se 1 (by rfl) ⟨3313430, by rfl⟩ : syracuseStep 4417907 = 6626861) B6626861
theorem B2296199 : Blo 1530462 2296199 := bstep (se 1 (by rfl) ⟨1722149, by rfl⟩ : syracuseStep 2296199 = 3444299) B3444299
theorem B13085063 : Blo 1530462 13085063 := bstep (se 1 (by rfl) ⟨9813797, by rfl⟩ : syracuseStep 13085063 = 19627595) B19627595
theorem B3877267 : Blo 1530462 3877267 := bstep (se 1 (by rfl) ⟨2907950, by rfl⟩ : syracuseStep 3877267 = 5815901) B5815901
theorem B2296235 : Blo 1530462 2296235 := bstep (se 1 (by rfl) ⟨1722176, by rfl⟩ : syracuseStep 2296235 = 3444353) B3444353
theorem B1722811 : Blo 1530462 1722811 := bstep (se 1 (by rfl) ⟨1292108, by rfl⟩ : syracuseStep 1722811 = 2584217) B2584217
theorem B2296265 : Blo 1530462 2296265 := bstep (se 2 (by rfl) ⟨861099, by rfl⟩ : syracuseStep 2296265 = 1722199) B1722199
theorem B5171741 : Blo 1530462 5171741 := bstep (se 3 (by rfl) ⟨969701, by rfl⟩ : syracuseStep 5171741 = 1939403) B1939403
theorem B3877409 : Blo 1530462 3877409 := bstep (se 2 (by rfl) ⟨1454028, by rfl⟩ : syracuseStep 3877409 = 2908057) B2908057
theorem B2583083 : Blo 1530462 2583083 := bstep (se 1 (by rfl) ⟨1937312, by rfl⟩ : syracuseStep 2583083 = 3874625) B3874625
theorem B2296379 : Blo 1530462 2296379 := bstep (se 1 (by rfl) ⟨1722284, by rfl⟩ : syracuseStep 2296379 = 3444569) B3444569
theorem B2296439 : Blo 1530462 2296439 := bstep (se 1 (by rfl) ⟨1722329, by rfl⟩ : syracuseStep 2296439 = 3444659) B3444659
theorem B2296463 : Blo 1530462 2296463 := bstep (se 1 (by rfl) ⟨1722347, by rfl⟩ : syracuseStep 2296463 = 3444695) B3444695
theorem B2296505 : Blo 1530462 2296505 := bstep (se 2 (by rfl) ⟨861189, by rfl⟩ : syracuseStep 2296505 = 1722379) B1722379
theorem B2452169 : Blo 1530462 2452169 := bstep (se 2 (by rfl) ⟨919563, by rfl⟩ : syracuseStep 2452169 = 1839127) B1839127
theorem B2296583 : Blo 1530462 2296583 := bstep (se 1 (by rfl) ⟨1722437, by rfl⟩ : syracuseStep 2296583 = 3444875) B3444875
theorem B2296619 : Blo 1530462 2296619 := bstep (se 1 (by rfl) ⟨1722464, by rfl⟩ : syracuseStep 2296619 = 3444929) B3444929
theorem B17673011 : Blo 1530462 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B2296649 : Blo 1530462 2296649 := bstep (se 2 (by rfl) ⟨861243, by rfl⟩ : syracuseStep 2296649 = 1722487) B1722487
theorem B2329463 : Blo 1530462 2329463 := bstep (se 1 (by rfl) ⟨1747097, by rfl⟩ : syracuseStep 2329463 = 3494195) B3494195
theorem B1723279 : Blo 1530462 1723279 := bstep (se 1 (by rfl) ⟨1292459, by rfl⟩ : syracuseStep 1723279 = 2584919) B2584919
theorem B2583481 : Blo 1530462 2583481 := bstep (se 2 (by rfl) ⟨968805, by rfl⟩ : syracuseStep 2583481 = 1937611) B1937611
theorem B2296763 : Blo 1530462 2296763 := bstep (se 1 (by rfl) ⟨1722572, by rfl⟩ : syracuseStep 2296763 = 3445145) B3445145
theorem B2296823 : Blo 1530462 2296823 := bstep (se 1 (by rfl) ⟨1722617, by rfl⟩ : syracuseStep 2296823 = 3445235) B3445235
theorem B2329591 : Blo 1530462 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B2296847 : Blo 1530462 2296847 := bstep (se 1 (by rfl) ⟨1722635, by rfl⟩ : syracuseStep 2296847 = 3445271) B3445271
theorem B2296889 : Blo 1530462 2296889 := bstep (se 2 (by rfl) ⟨861333, by rfl⟩ : syracuseStep 2296889 = 1722667) B1722667
theorem B3443831 : Blo 1530462 3443831 := bstep (se 1 (by rfl) ⟨2582873, by rfl⟩ : syracuseStep 3443831 = 5165747) B5165747
theorem B2296967 : Blo 1530462 2296967 := bstep (se 1 (by rfl) ⟨1722725, by rfl⟩ : syracuseStep 2296967 = 3445451) B3445451
theorem B4656275 : Blo 1530462 4656275 := bstep (se 1 (by rfl) ⟨3492206, by rfl⟩ : syracuseStep 4656275 = 6984413) B6984413
theorem B2297003 : Blo 1530462 2297003 := bstep (se 1 (by rfl) ⟨1722752, by rfl⟩ : syracuseStep 2297003 = 3445505) B3445505
theorem B2297033 : Blo 1530462 2297033 := bstep (se 2 (by rfl) ⟨861387, by rfl⟩ : syracuseStep 2297033 = 1722775) B1722775
theorem B4656395 : Blo 1530462 4656395 := bstep (se 1 (by rfl) ⟨3492296, by rfl⟩ : syracuseStep 4656395 = 6984593) B6984593
theorem B3444011 : Blo 1530462 3444011 := bstep (se 1 (by rfl) ⟨2583008, by rfl⟩ : syracuseStep 3444011 = 5166017) B5166017
theorem B2297147 : Blo 1530462 2297147 := bstep (se 1 (by rfl) ⟨1722860, by rfl⟩ : syracuseStep 2297147 = 3445721) B3445721
theorem B2297207 : Blo 1530462 2297207 := bstep (se 1 (by rfl) ⟨1722905, by rfl⟩ : syracuseStep 2297207 = 3445811) B3445811
theorem B8719751 : Blo 1530462 8719751 := bstep (se 1 (by rfl) ⟨6539813, by rfl⟩ : syracuseStep 8719751 = 13079627) B13079627
theorem B1723783 : Blo 1530462 1723783 := bstep (se 1 (by rfl) ⟨1292837, by rfl⟩ : syracuseStep 1723783 = 2585675) B2585675
theorem B2297231 : Blo 1530462 2297231 := bstep (se 1 (by rfl) ⟨1722923, by rfl⟩ : syracuseStep 2297231 = 3445847) B3445847
theorem B2297273 : Blo 1530462 2297273 := bstep (se 2 (by rfl) ⟨861477, by rfl⟩ : syracuseStep 2297273 = 1722955) B1722955
theorem B3681721 : Blo 1530462 3681721 := bstep (se 2 (by rfl) ⟨1380645, by rfl⟩ : syracuseStep 3681721 = 2761291) B2761291
theorem B3878401 : Blo 1530462 3878401 := bstep (se 2 (by rfl) ⟨1454400, by rfl⟩ : syracuseStep 3878401 = 2908801) B2908801
theorem B11628035 : Blo 1530462 11628035 := bstep (se 1 (by rfl) ⟨8721026, by rfl⟩ : syracuseStep 11628035 = 17442053) B17442053
theorem B2297351 : Blo 1530462 2297351 := bstep (se 1 (by rfl) ⟨1723013, by rfl⟩ : syracuseStep 2297351 = 3446027) B3446027
theorem B2297387 : Blo 1530462 2297387 := bstep (se 1 (by rfl) ⟨1723040, by rfl⟩ : syracuseStep 2297387 = 3446081) B3446081
theorem B1723963 : Blo 1530462 1723963 := bstep (se 1 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 1723963 = 2585945) B2585945
theorem B8719933 : Blo 1530462 8719933 := bstep (se 3 (by rfl) ⟨1634987, by rfl⟩ : syracuseStep 8719933 = 3269975) B3269975
theorem B4361789 : Blo 1530462 4361789 := bstep (se 3 (by rfl) ⟨817835, by rfl⟩ : syracuseStep 4361789 = 1635671) B1635671
theorem B2297417 : Blo 1530462 2297417 := bstep (se 2 (by rfl) ⟨861531, by rfl⟩ : syracuseStep 2297417 = 1723063) B1723063
theorem B2584183 : Blo 1530462 2584183 := bstep (se 1 (by rfl) ⟨1938137, by rfl⟩ : syracuseStep 2584183 = 3876275) B3876275
theorem B3444371 : Blo 1530462 3444371 := bstep (se 1 (by rfl) ⟨2583278, by rfl⟩ : syracuseStep 3444371 = 5166557) B5166557
theorem B2297531 : Blo 1530462 2297531 := bstep (se 1 (by rfl) ⟨1723148, by rfl⟩ : syracuseStep 2297531 = 3446297) B3446297
theorem B3444425 : Blo 1530462 3444425 := bstep (se 2 (by rfl) ⟨1291659, by rfl⟩ : syracuseStep 3444425 = 2583319) B2583319
theorem B2297591 : Blo 1530462 2297591 := bstep (se 1 (by rfl) ⟨1723193, by rfl⟩ : syracuseStep 2297591 = 3446387) B3446387
theorem B6983425 : Blo 1530462 6983425 := bstep (se 2 (by rfl) ⟨2618784, by rfl⟩ : syracuseStep 6983425 = 5237569) B5237569
theorem B5811983 : Blo 1530462 5811983 := bstep (se 1 (by rfl) ⟨4358987, by rfl⟩ : syracuseStep 5811983 = 8717975) B8717975
theorem B11783951 : Blo 1530462 11783951 := bstep (se 1 (by rfl) ⟨8837963, by rfl⟩ : syracuseStep 11783951 = 17675927) B17675927
theorem B2297615 : Blo 1530462 2297615 := bstep (se 1 (by rfl) ⟨1723211, by rfl⟩ : syracuseStep 2297615 = 3446423) B3446423
theorem B11497265 : Blo 1530462 11497265 := bstep (se 2 (by rfl) ⟨4311474, by rfl⟩ : syracuseStep 11497265 = 8622949) B8622949
theorem B2297657 : Blo 1530462 2297657 := bstep (se 2 (by rfl) ⟨861621, by rfl⟩ : syracuseStep 2297657 = 1723243) B1723243
theorem B4656955 : Blo 1530462 4656955 := bstep (se 1 (by rfl) ⟨3492716, by rfl⟩ : syracuseStep 4656955 = 6985433) B6985433
theorem B2584379 : Blo 1530462 2584379 := bstep (se 1 (by rfl) ⟨1938284, by rfl⟩ : syracuseStep 2584379 = 3876569) B3876569
theorem B1937287 : Blo 1530462 1937287 := bstep (se 1 (by rfl) ⟨1452965, by rfl⟩ : syracuseStep 1937287 = 2905931) B2905931
theorem B2297735 : Blo 1530462 2297735 := bstep (se 1 (by rfl) ⟨1723301, by rfl⟩ : syracuseStep 2297735 = 3446603) B3446603
theorem B2297771 : Blo 1530462 2297771 := bstep (se 1 (by rfl) ⟨1723328, by rfl⟩ : syracuseStep 2297771 = 3446657) B3446657
theorem B3272633 : Blo 1530462 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B2297801 : Blo 1530462 2297801 := bstep (se 2 (by rfl) ⟨861675, by rfl⟩ : syracuseStep 2297801 = 1723351) B1723351
theorem B9310211 : Blo 1530462 9310211 := bstep (se 1 (by rfl) ⟨6982658, by rfl⟩ : syracuseStep 9310211 = 13965317) B13965317
theorem B3493921 : Blo 1530462 3493921 := bstep (se 2 (by rfl) ⟨1310220, by rfl⟩ : syracuseStep 3493921 = 2620441) B2620441
theorem B2297915 : Blo 1530462 2297915 := bstep (se 1 (by rfl) ⟨1723436, by rfl⟩ : syracuseStep 2297915 = 3446873) B3446873
theorem B3878999 : Blo 1530462 3878999 := bstep (se 1 (by rfl) ⟨2909249, by rfl⟩ : syracuseStep 3878999 = 5818499) B5818499
theorem B2297975 : Blo 1530462 2297975 := bstep (se 1 (by rfl) ⟨1723481, by rfl⟩ : syracuseStep 2297975 = 3446963) B3446963
theorem B2297999 : Blo 1530462 2297999 := bstep (se 1 (by rfl) ⟨1723499, by rfl⟩ : syracuseStep 2297999 = 3446999) B3446999
theorem B2298041 : Blo 1530462 2298041 := bstep (se 2 (by rfl) ⟨861765, by rfl⟩ : syracuseStep 2298041 = 1723531) B1723531
theorem B9310409 : Blo 1530462 9310409 := bstep (se 2 (by rfl) ⟨3491403, by rfl⟩ : syracuseStep 9310409 = 6982807) B6982807
theorem B2584777 : Blo 1530462 2584777 := bstep (se 2 (by rfl) ⟨969291, by rfl⟩ : syracuseStep 2584777 = 1938583) B1938583
theorem B2298119 : Blo 1530462 2298119 := bstep (se 1 (by rfl) ⟨1723589, by rfl⟩ : syracuseStep 2298119 = 3447179) B3447179
theorem B4657441 : Blo 1530462 4657441 := bstep (se 2 (by rfl) ⟨1746540, by rfl⟩ : syracuseStep 4657441 = 3493081) B3493081
theorem B2298155 : Blo 1530462 2298155 := bstep (se 1 (by rfl) ⟨1723616, by rfl⟩ : syracuseStep 2298155 = 3447233) B3447233
theorem B2298185 : Blo 1530462 2298185 := bstep (se 2 (by rfl) ⟨861819, by rfl⟩ : syracuseStep 2298185 = 1723639) B1723639
theorem B1937783 : Blo 1530462 1937783 := bstep (se 1 (by rfl) ⟨1453337, by rfl⟩ : syracuseStep 1937783 = 2906675) B2906675
theorem B3445127 : Blo 1530462 3445127 := bstep (se 1 (by rfl) ⟨2583845, by rfl⟩ : syracuseStep 3445127 = 5167691) B5167691
theorem B7754129 : Blo 1530462 7754129 := bstep (se 2 (by rfl) ⟨2907798, by rfl⟩ : syracuseStep 7754129 = 5815597) B5815597
theorem B2298299 : Blo 1530462 2298299 := bstep (se 1 (by rfl) ⟨1723724, by rfl⟩ : syracuseStep 2298299 = 3447449) B3447449
theorem B2298359 : Blo 1530462 2298359 := bstep (se 1 (by rfl) ⟨1723769, by rfl⟩ : syracuseStep 2298359 = 3447539) B3447539
theorem B1937935 : Blo 1530462 1937935 := bstep (se 1 (by rfl) ⟨1453451, by rfl⟩ : syracuseStep 1937935 = 2906903) B2906903
theorem B2298383 : Blo 1530462 2298383 := bstep (se 1 (by rfl) ⟨1723787, by rfl⟩ : syracuseStep 2298383 = 3447575) B3447575
theorem B198758933 : Blo 1530462 198758933 := bstep (se 6 (by rfl) ⟨4658412, by rfl⟩ : syracuseStep 198758933 = 9316825) B9316825
theorem B4362781 : Blo 1530462 4362781 := bstep (se 3 (by rfl) ⟨818021, by rfl⟩ : syracuseStep 4362781 = 1636043) B1636043
theorem B2298425 : Blo 1530462 2298425 := bstep (se 2 (by rfl) ⟨861909, by rfl⟩ : syracuseStep 2298425 = 1723819) B1723819
theorem B3445307 : Blo 1530462 3445307 := bstep (se 1 (by rfl) ⟨2583980, by rfl⟩ : syracuseStep 3445307 = 5167961) B5167961
theorem B3494459 : Blo 1530462 3494459 := bstep (se 1 (by rfl) ⟨2620844, by rfl⟩ : syracuseStep 3494459 = 5241689) B5241689
theorem B2298503 : Blo 1530462 2298503 := bstep (se 1 (by rfl) ⟨1723877, by rfl⟩ : syracuseStep 2298503 = 3447755) B3447755
theorem B2298539 : Blo 1530462 2298539 := bstep (se 1 (by rfl) ⟨1723904, by rfl⟩ : syracuseStep 2298539 = 3447809) B3447809
theorem B3445433 : Blo 1530462 3445433 := bstep (se 2 (by rfl) ⟨1292037, by rfl⟩ : syracuseStep 3445433 = 2584075) B2584075
theorem B1938107 : Blo 1530462 1938107 := bstep (se 1 (by rfl) ⟨1453580, by rfl⟩ : syracuseStep 1938107 = 2907161) B2907161
theorem B2298569 : Blo 1530462 2298569 := bstep (se 2 (by rfl) ⟨861963, by rfl⟩ : syracuseStep 2298569 = 1723927) B1723927
theorem B2298683 : Blo 1530462 2298683 := bstep (se 1 (by rfl) ⟨1724012, by rfl⟩ : syracuseStep 2298683 = 3448025) B3448025
theorem B2454391 : Blo 1530462 2454391 := bstep (se 1 (by rfl) ⟨1840793, by rfl⟩ : syracuseStep 2454391 = 3681587) B3681587
theorem B2585479 : Blo 1530462 2585479 := bstep (se 1 (by rfl) ⟨1939109, by rfl⟩ : syracuseStep 2585479 = 3878219) B3878219
theorem B14717963 : Blo 1530462 14717963 := bstep (se 1 (by rfl) ⟨11038472, by rfl⟩ : syracuseStep 14717963 = 22076945) B22076945
theorem B3445775 : Blo 1530462 3445775 := bstep (se 1 (by rfl) ⟨2584331, by rfl⟩ : syracuseStep 3445775 = 5168663) B5168663
theorem B3445793 : Blo 1530462 3445793 := bstep (se 2 (by rfl) ⟨1292172, by rfl⟩ : syracuseStep 3445793 = 2584345) B2584345
theorem B7361579 : Blo 1530462 7361579 := bstep (se 1 (by rfl) ⟨5521184, by rfl⟩ : syracuseStep 7361579 = 11042369) B11042369
theorem B7361597 : Blo 1530462 7361597 := bstep (se 3 (by rfl) ⟨1380299, by rfl⟩ : syracuseStep 7361597 = 2760599) B2760599
theorem B8721665 : Blo 1530462 8721665 := bstep (se 2 (by rfl) ⟨3270624, by rfl⟩ : syracuseStep 8721665 = 6541249) B6541249
theorem B1635599 : Blo 1530462 1635599 := bstep (se 1 (by rfl) ⟨1226699, by rfl⟩ : syracuseStep 1635599 = 2453399) B2453399
theorem B1865003 : Blo 1530462 1865003 := bstep (se 1 (by rfl) ⟨1398752, by rfl⟩ : syracuseStep 1865003 = 2797505) B2797505
theorem B5166395 : Blo 1530462 5166395 := bstep (se 1 (by rfl) ⟨3874796, by rfl⟩ : syracuseStep 5166395 = 7749593) B7749593
theorem B3446135 : Blo 1530462 3446135 := bstep (se 1 (by rfl) ⟨2584601, by rfl⟩ : syracuseStep 3446135 = 5169203) B5169203
theorem B5813639 : Blo 1530462 5813639 := bstep (se 1 (by rfl) ⟨4360229, by rfl⟩ : syracuseStep 5813639 = 8720459) B8720459
theorem B2618825 : Blo 1530462 2618825 := bstep (se 2 (by rfl) ⟨982059, by rfl⟩ : syracuseStep 2618825 = 1964119) B1964119
theorem B3315215 : Blo 1530462 3315215 := bstep (se 1 (by rfl) ⟨2486411, by rfl⟩ : syracuseStep 3315215 = 4972823) B4972823
theorem B16774685 : Blo 1530462 16774685 := bstep (se 3 (by rfl) ⟨3145253, by rfl⟩ : syracuseStep 16774685 = 6290507) B6290507
theorem B5518891 : Blo 1530462 5518891 := bstep (se 1 (by rfl) ⟨4139168, by rfl⟩ : syracuseStep 5518891 = 8278337) B8278337
theorem B3446315 : Blo 1530462 3446315 := bstep (se 1 (by rfl) ⟨2584736, by rfl⟩ : syracuseStep 3446315 = 5169473) B5169473
theorem B13088375 : Blo 1530462 13088375 := bstep (se 1 (by rfl) ⟨9816281, by rfl⟩ : syracuseStep 13088375 = 19632563) B19632563
theorem B1939079 : Blo 1530462 1939079 := bstep (se 1 (by rfl) ⟨1454309, by rfl⟩ : syracuseStep 1939079 = 2908619) B2908619
theorem B5166881 : Blo 1530462 5166881 := bstep (se 2 (by rfl) ⟨1937580, by rfl⟩ : syracuseStep 5166881 = 3875161) B3875161
theorem B9312059 : Blo 1530462 9312059 := bstep (se 1 (by rfl) ⟨6984044, by rfl⟩ : syracuseStep 9312059 = 13968089) B13968089
theorem B3446675 : Blo 1530462 3446675 := bstep (se 1 (by rfl) ⟨2585006, by rfl⟩ : syracuseStep 3446675 = 5170013) B5170013
theorem B3446729 : Blo 1530462 3446729 := bstep (se 2 (by rfl) ⟨1292523, by rfl⟩ : syracuseStep 3446729 = 2585047) B2585047
theorem B4782091 : Blo 1530462 4782091 := bstep (se 1 (by rfl) ⟨3586568, by rfl⟩ : syracuseStep 4782091 = 7173137) B7173137
theorem B37279757 : Blo 1530462 37279757 := bstep (se 3 (by rfl) ⟨6989954, by rfl⟩ : syracuseStep 37279757 = 13979909) B13979909
theorem B11622689 : Blo 1530462 11622689 := bstep (se 2 (by rfl) ⟨4358508, by rfl⟩ : syracuseStep 11622689 = 8717017) B8717017
theorem B5167475 : Blo 1530462 5167475 := bstep (se 1 (by rfl) ⟨3875606, by rfl⟩ : syracuseStep 5167475 = 7751213) B7751213
theorem B5519801 : Blo 1530462 5519801 := bstep (se 2 (by rfl) ⟨2069925, by rfl⟩ : syracuseStep 5519801 = 4139851) B4139851
theorem B7756235 : Blo 1530462 7756235 := bstep (se 1 (by rfl) ⟨5817176, by rfl⟩ : syracuseStep 7756235 = 11634353) B11634353
theorem B2071055 : Blo 1530462 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B22076023 : Blo 1530462 22076023 := bstep (se 1 (by rfl) ⟨16557017, by rfl⟩ : syracuseStep 22076023 = 33114035) B33114035
theorem B1530503 : Blo 1530462 1530503 := bstep (se 1 (by rfl) ⟨1147877, by rfl⟩ : syracuseStep 1530503 = 2295755) B2295755
theorem B2906759 : Blo 1530462 2906759 := bstep (se 1 (by rfl) ⟨2180069, by rfl⟩ : syracuseStep 2906759 = 4360139) B4360139
theorem B3447431 : Blo 1530462 3447431 := bstep (se 1 (by rfl) ⟨2585573, by rfl⟩ : syracuseStep 3447431 = 5171147) B5171147
theorem B1530511 : Blo 1530462 1530511 := bstep (se 1 (by rfl) ⟨1147883, by rfl⟩ : syracuseStep 1530511 = 2295767) B2295767
theorem B1530555 : Blo 1530462 1530555 := bstep (se 1 (by rfl) ⟨1147916, by rfl⟩ : syracuseStep 1530555 = 2295833) B2295833
theorem B20961985 : Blo 1530462 20961985 := bstep (se 2 (by rfl) ⟨7860744, by rfl⟩ : syracuseStep 20961985 = 15721489) B15721489
theorem B7748297 : Blo 1530462 7748297 := bstep (se 2 (by rfl) ⟨2905611, by rfl⟩ : syracuseStep 7748297 = 5811223) B5811223
theorem B9435905 : Blo 1530462 9435905 := bstep (se 2 (by rfl) ⟨3538464, by rfl⟩ : syracuseStep 9435905 = 7076929) B7076929
theorem B1530631 : Blo 1530462 1530631 := bstep (se 1 (by rfl) ⟨1147973, by rfl⟩ : syracuseStep 1530631 = 2295947) B2295947
theorem B1530639 : Blo 1530462 1530639 := bstep (se 1 (by rfl) ⟨1147979, by rfl⟩ : syracuseStep 1530639 = 2295959) B2295959
theorem B7756559 : Blo 1530462 7756559 := bstep (se 1 (by rfl) ⟨5817419, by rfl⟩ : syracuseStep 7756559 = 11634839) B11634839
theorem B1530683 : Blo 1530462 1530683 := bstep (se 1 (by rfl) ⟨1148012, by rfl⟩ : syracuseStep 1530683 = 2296025) B2296025
theorem B3447611 : Blo 1530462 3447611 := bstep (se 1 (by rfl) ⟨2585708, by rfl⟩ : syracuseStep 3447611 = 5171417) B5171417
theorem B1530759 : Blo 1530462 1530759 := bstep (se 1 (by rfl) ⟨1148069, by rfl⟩ : syracuseStep 1530759 = 2296139) B2296139
theorem B1530767 : Blo 1530462 1530767 := bstep (se 1 (by rfl) ⟨1148075, by rfl⟩ : syracuseStep 1530767 = 2296151) B2296151
theorem B3447737 : Blo 1530462 3447737 := bstep (se 2 (by rfl) ⟨1292901, by rfl⟩ : syracuseStep 3447737 = 2585803) B2585803
theorem B1530811 : Blo 1530462 1530811 := bstep (se 1 (by rfl) ⟨1148108, by rfl⟩ : syracuseStep 1530811 = 2296217) B2296217
theorem B14711813 : Blo 1530462 14711813 := bstep (se 4 (by rfl) ⟨1379232, by rfl⟩ : syracuseStep 14711813 = 2758465) B2758465
theorem B1530887 : Blo 1530462 1530887 := bstep (se 1 (by rfl) ⟨1148165, by rfl⟩ : syracuseStep 1530887 = 2296331) B2296331
theorem B7363595 : Blo 1530462 7363595 := bstep (se 1 (by rfl) ⟨5522696, by rfl⟩ : syracuseStep 7363595 = 11045393) B11045393
theorem B1530895 : Blo 1530462 1530895 := bstep (se 1 (by rfl) ⟨1148171, by rfl⟩ : syracuseStep 1530895 = 2296343) B2296343
theorem B1530939 : Blo 1530462 1530939 := bstep (se 1 (by rfl) ⟨1148204, by rfl⟩ : syracuseStep 1530939 = 2296409) B2296409
theorem B5815415 : Blo 1530462 5815415 := bstep (se 1 (by rfl) ⟨4361561, by rfl⟩ : syracuseStep 5815415 = 8723123) B8723123
theorem B1531015 : Blo 1530462 1531015 := bstep (se 1 (by rfl) ⟨1148261, by rfl⟩ : syracuseStep 1531015 = 2296523) B2296523
theorem B1531023 : Blo 1530462 1531023 := bstep (se 1 (by rfl) ⟨1148267, by rfl⟩ : syracuseStep 1531023 = 2296535) B2296535
theorem B1531067 : Blo 1530462 1531067 := bstep (se 1 (by rfl) ⟨1148300, by rfl⟩ : syracuseStep 1531067 = 2296601) B2296601
theorem B11623661 : Blo 1530462 11623661 := bstep (se 3 (by rfl) ⟨2179436, by rfl⟩ : syracuseStep 11623661 = 4358873) B4358873
theorem B1531143 : Blo 1530462 1531143 := bstep (se 1 (by rfl) ⟨1148357, by rfl⟩ : syracuseStep 1531143 = 2296715) B2296715
theorem B1531151 : Blo 1530462 1531151 := bstep (se 1 (by rfl) ⟨1148363, by rfl⟩ : syracuseStep 1531151 = 2296727) B2296727
theorem B1531195 : Blo 1530462 1531195 := bstep (se 1 (by rfl) ⟨1148396, by rfl⟩ : syracuseStep 1531195 = 2296793) B2296793
theorem B1531271 : Blo 1530462 1531271 := bstep (se 1 (by rfl) ⟨1148453, by rfl⟩ : syracuseStep 1531271 = 2296907) B2296907
theorem B1531279 : Blo 1530462 1531279 := bstep (se 1 (by rfl) ⟨1148459, by rfl⟩ : syracuseStep 1531279 = 2296919) B2296919
theorem B1531323 : Blo 1530462 1531323 := bstep (se 1 (by rfl) ⟨1148492, by rfl⟩ : syracuseStep 1531323 = 2296985) B2296985
theorem B1531399 : Blo 1530462 1531399 := bstep (se 1 (by rfl) ⟨1148549, by rfl⟩ : syracuseStep 1531399 = 2297099) B2297099
theorem B6544907 : Blo 1530462 6544907 := bstep (se 1 (by rfl) ⟨4908680, by rfl⟩ : syracuseStep 6544907 = 9817361) B9817361
theorem B1531407 : Blo 1530462 1531407 := bstep (se 1 (by rfl) ⟨1148555, by rfl⟩ : syracuseStep 1531407 = 2297111) B2297111
theorem B1531451 : Blo 1530462 1531451 := bstep (se 1 (by rfl) ⟨1148588, by rfl⟩ : syracuseStep 1531451 = 2297177) B2297177
theorem B2760311 : Blo 1530462 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B1531527 : Blo 1530462 1531527 := bstep (se 1 (by rfl) ⟨1148645, by rfl⟩ : syracuseStep 1531527 = 2297291) B2297291
theorem B1531535 : Blo 1530462 1531535 := bstep (se 1 (by rfl) ⟨1148651, by rfl⟩ : syracuseStep 1531535 = 2297303) B2297303
theorem B1531579 : Blo 1530462 1531579 := bstep (se 1 (by rfl) ⟨1148684, by rfl⟩ : syracuseStep 1531579 = 2297369) B2297369
theorem B3317449 : Blo 1530462 3317449 := bstep (se 2 (by rfl) ⟨1244043, by rfl⟩ : syracuseStep 3317449 = 2488087) B2488087
theorem B1531655 : Blo 1530462 1531655 := bstep (se 1 (by rfl) ⟨1148741, by rfl⟩ : syracuseStep 1531655 = 2297483) B2297483
theorem B1531663 : Blo 1530462 1531663 := bstep (se 1 (by rfl) ⟨1148747, by rfl⟩ : syracuseStep 1531663 = 2297495) B2297495
theorem B2727713 : Blo 1530462 2727713 := bstep (se 2 (by rfl) ⟨1022892, by rfl⟩ : syracuseStep 2727713 = 2045785) B2045785
theorem B2096939 : Blo 1530462 2096939 := bstep (se 1 (by rfl) ⟨1572704, by rfl⟩ : syracuseStep 2096939 = 3145409) B3145409
theorem B1531707 : Blo 1530462 1531707 := bstep (se 1 (by rfl) ⟨1148780, by rfl⟩ : syracuseStep 1531707 = 2297561) B2297561
theorem B3874675 : Blo 1530462 3874675 := bstep (se 1 (by rfl) ⟨2906006, by rfl⟩ : syracuseStep 3874675 = 5812013) B5812013
theorem B1531783 : Blo 1530462 1531783 := bstep (se 1 (by rfl) ⟨1148837, by rfl⟩ : syracuseStep 1531783 = 2297675) B2297675
theorem B1531791 : Blo 1530462 1531791 := bstep (se 1 (by rfl) ⟨1148843, by rfl⟩ : syracuseStep 1531791 = 2297687) B2297687
theorem B1531835 : Blo 1530462 1531835 := bstep (se 1 (by rfl) ⟨1148876, by rfl⟩ : syracuseStep 1531835 = 2297753) B2297753
theorem B8273927 : Blo 1530462 8273927 := bstep (se 1 (by rfl) ⟨6205445, by rfl⟩ : syracuseStep 8273927 = 12410891) B12410891
theorem B11042831 : Blo 1530462 11042831 := bstep (se 1 (by rfl) ⟨8282123, by rfl⟩ : syracuseStep 11042831 = 16564247) B16564247
theorem B39247901 : Blo 1530462 39247901 := bstep (se 3 (by rfl) ⟨7358981, by rfl⟩ : syracuseStep 39247901 = 14717963) B14717963
theorem B19636253 : Blo 1530462 19636253 := bstep (se 3 (by rfl) ⟨3681797, by rfl⟩ : syracuseStep 19636253 = 7363595) B7363595
theorem B1531943 : Blo 1530462 1531943 := bstep (se 1 (by rfl) ⟨1148957, by rfl⟩ : syracuseStep 1531943 = 2297915) B2297915
theorem B2908217 : Blo 1530462 2908217 := bstep (se 2 (by rfl) ⟨1090581, by rfl⟩ : syracuseStep 2908217 = 2181163) B2181163
theorem B1531983 : Blo 1530462 1531983 := bstep (se 1 (by rfl) ⟨1148987, by rfl⟩ : syracuseStep 1531983 = 2297975) B2297975
theorem B1531999 : Blo 1530462 1531999 := bstep (se 1 (by rfl) ⟨1148999, by rfl⟩ : syracuseStep 1531999 = 2297999) B2297999
theorem B1532027 : Blo 1530462 1532027 := bstep (se 1 (by rfl) ⟨1149020, by rfl⟩ : syracuseStep 1532027 = 2298041) B2298041
theorem B1532079 : Blo 1530462 1532079 := bstep (se 1 (by rfl) ⟨1149059, by rfl⟩ : syracuseStep 1532079 = 2298119) B2298119
theorem B23584945 : Blo 1530462 23584945 := bstep (se 2 (by rfl) ⟨8844354, by rfl⟩ : syracuseStep 23584945 = 17688709) B17688709
theorem B1532103 : Blo 1530462 1532103 := bstep (se 1 (by rfl) ⟨1149077, by rfl⟩ : syracuseStep 1532103 = 2298155) B2298155
theorem B1532123 : Blo 1530462 1532123 := bstep (se 1 (by rfl) ⟨1149092, by rfl⟩ : syracuseStep 1532123 = 2298185) B2298185
theorem B5169419 : Blo 1530462 5169419 := bstep (se 1 (by rfl) ⟨3877064, by rfl⟩ : syracuseStep 5169419 = 7754129) B7754129
theorem B1532199 : Blo 1530462 1532199 := bstep (se 1 (by rfl) ⟨1149149, by rfl⟩ : syracuseStep 1532199 = 2298299) B2298299
theorem B53051723 : Blo 1530462 53051723 := bstep (se 1 (by rfl) ⟨39788792, by rfl⟩ : syracuseStep 53051723 = 79577585) B79577585
theorem B1532239 : Blo 1530462 1532239 := bstep (se 1 (by rfl) ⟨1149179, by rfl⟩ : syracuseStep 1532239 = 2298359) B2298359
theorem B1532255 : Blo 1530462 1532255 := bstep (se 1 (by rfl) ⟨1149191, by rfl⟩ : syracuseStep 1532255 = 2298383) B2298383
theorem B132505955 : Blo 1530462 132505955 := bstep (se 1 (by rfl) ⟨99379466, by rfl⟩ : syracuseStep 132505955 = 198758933) B198758933
theorem B1532283 : Blo 1530462 1532283 := bstep (se 1 (by rfl) ⟨1149212, by rfl⟩ : syracuseStep 1532283 = 2298425) B2298425
theorem B6209921 : Blo 1530462 6209921 := bstep (se 2 (by rfl) ⟨2328720, by rfl⟩ : syracuseStep 6209921 = 4657441) B4657441
theorem B1532335 : Blo 1530462 1532335 := bstep (se 1 (by rfl) ⟨1149251, by rfl⟩ : syracuseStep 1532335 = 2298503) B2298503
theorem B1532359 : Blo 1530462 1532359 := bstep (se 1 (by rfl) ⟨1149269, by rfl⟩ : syracuseStep 1532359 = 2298539) B2298539
theorem B1532379 : Blo 1530462 1532379 := bstep (se 1 (by rfl) ⟨1149284, by rfl⟩ : syracuseStep 1532379 = 2298569) B2298569
theorem B19628567 : Blo 1530462 19628567 := bstep (se 1 (by rfl) ⟨14721425, by rfl⟩ : syracuseStep 19628567 = 29442851) B29442851
theorem B4358681 : Blo 1530462 4358681 := bstep (se 2 (by rfl) ⟨1634505, by rfl⟩ : syracuseStep 4358681 = 3269011) B3269011
theorem B5169689 : Blo 1530462 5169689 := bstep (se 2 (by rfl) ⟨1938633, by rfl⟩ : syracuseStep 5169689 = 3877267) B3877267
theorem B1532455 : Blo 1530462 1532455 := bstep (se 1 (by rfl) ⟨1149341, by rfl⟩ : syracuseStep 1532455 = 2298683) B2298683
theorem B44139127 : Blo 1530462 44139127 := bstep (se 1 (by rfl) ⟨33104345, by rfl⟩ : syracuseStep 44139127 = 66208691) B66208691
theorem B4907719 : Blo 1530462 4907719 := bstep (se 1 (by rfl) ⟨3680789, by rfl⟩ : syracuseStep 4907719 = 7361579) B7361579
theorem B5817041 : Blo 1530462 5817041 := bstep (se 2 (by rfl) ⟨2181390, by rfl⟩ : syracuseStep 5817041 = 4362781) B4362781
theorem B4907731 : Blo 1530462 4907731 := bstep (se 1 (by rfl) ⟨3680798, by rfl⟩ : syracuseStep 4907731 = 7361597) B7361597
theorem B7750403 : Blo 1530462 7750403 := bstep (se 1 (by rfl) ⟨5812802, by rfl⟩ : syracuseStep 7750403 = 11625605) B11625605
theorem B4973341 : Blo 1530462 4973341 := bstep (se 3 (by rfl) ⟨932501, by rfl⟩ : syracuseStep 4973341 = 1865003) B1865003
theorem B29434697 : Blo 1530462 29434697 := bstep (se 2 (by rfl) ⟨11038011, by rfl⟩ : syracuseStep 29434697 = 22076023) B22076023
theorem B3875759 : Blo 1530462 3875759 := bstep (se 1 (by rfl) ⟨2906819, by rfl⟩ : syracuseStep 3875759 = 5813639) B5813639
theorem B11781085 : Blo 1530462 11781085 := bstep (se 3 (by rfl) ⟨2208953, by rfl⟩ : syracuseStep 11781085 = 4417907) B4417907
theorem B5817359 : Blo 1530462 5817359 := bstep (se 1 (by rfl) ⟨4363019, by rfl⟩ : syracuseStep 5817359 = 8726039) B8726039
theorem B11183123 : Blo 1530462 11183123 := bstep (se 1 (by rfl) ⟨8387342, by rfl⟩ : syracuseStep 11183123 = 16774685) B16774685
theorem B8725583 : Blo 1530462 8725583 := bstep (se 1 (by rfl) ⟨6544187, by rfl⟩ : syracuseStep 8725583 = 13088375) B13088375
theorem B23577803 : Blo 1530462 23577803 := bstep (se 1 (by rfl) ⟨17683352, by rfl⟩ : syracuseStep 23577803 = 35366705) B35366705
theorem B11633867 : Blo 1530462 11633867 := bstep (se 1 (by rfl) ⟨8725400, by rfl⟩ : syracuseStep 11633867 = 17450801) B17450801
theorem B3106121 : Blo 1530462 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B16549235 : Blo 1530462 16549235 := bstep (se 1 (by rfl) ⟨12411926, by rfl⟩ : syracuseStep 16549235 = 24823853) B24823853
theorem B8840573 : Blo 1530462 8840573 := bstep (se 3 (by rfl) ⟨1657607, by rfl⟩ : syracuseStep 8840573 = 3315215) B3315215
theorem B5522813 : Blo 1530462 5522813 := bstep (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) B2071055
theorem B3679867 : Blo 1530462 3679867 := bstep (se 1 (by rfl) ⟨2759900, by rfl⟩ : syracuseStep 3679867 = 5519801) B5519801
theorem B5170823 : Blo 1530462 5170823 := bstep (se 1 (by rfl) ⟨3878117, by rfl⟩ : syracuseStep 5170823 = 7756235) B7756235
theorem B5170877 : Blo 1530462 5170877 := bstep (se 3 (by rfl) ⟨969539, by rfl⟩ : syracuseStep 5170877 = 1939079) B1939079
theorem B1722055 : Blo 1530462 1722055 := bstep (se 1 (by rfl) ⟨1291541, by rfl⟩ : syracuseStep 1722055 = 2583083) B2583083
theorem B5171039 : Blo 1530462 5171039 := bstep (se 1 (by rfl) ⟨3878279, by rfl⟩ : syracuseStep 5171039 = 7756559) B7756559
theorem B11782007 : Blo 1530462 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B4908961 : Blo 1530462 4908961 := bstep (se 2 (by rfl) ⟨1840860, by rfl⟩ : syracuseStep 4908961 = 3681721) B3681721
theorem B5171201 : Blo 1530462 5171201 := bstep (se 2 (by rfl) ⟨1939200, by rfl⟩ : syracuseStep 5171201 = 3878401) B3878401
theorem B9807875 : Blo 1530462 9807875 := bstep (se 1 (by rfl) ⟨7355906, by rfl⟩ : syracuseStep 9807875 = 14711813) B14711813
theorem B7358521 : Blo 1530462 7358521 := bstep (se 2 (by rfl) ⟨2759445, by rfl⟩ : syracuseStep 7358521 = 5518891) B5518891
theorem B2295887 : Blo 1530462 2295887 := bstep (se 1 (by rfl) ⟨1721915, by rfl⟩ : syracuseStep 2295887 = 3443831) B3443831
theorem B3876943 : Blo 1530462 3876943 := bstep (se 1 (by rfl) ⟨2907707, by rfl⟩ : syracuseStep 3876943 = 5815415) B5815415
theorem B11626577 : Blo 1530462 11626577 := bstep (se 2 (by rfl) ⟨4359966, by rfl⟩ : syracuseStep 11626577 = 8719933) B8719933
theorem B2296007 : Blo 1530462 2296007 := bstep (se 1 (by rfl) ⟨1722005, by rfl⟩ : syracuseStep 2296007 = 3444011) B3444011
theorem B7752023 : Blo 1530462 7752023 := bstep (se 1 (by rfl) ⟨5814017, by rfl⟩ : syracuseStep 7752023 = 11628035) B11628035
theorem B2296169 : Blo 1530462 2296169 := bstep (se 2 (by rfl) ⟨861063, by rfl⟩ : syracuseStep 2296169 = 1722127) B1722127
theorem B2296247 : Blo 1530462 2296247 := bstep (se 1 (by rfl) ⟨1722185, by rfl⟩ : syracuseStep 2296247 = 3444371) B3444371
theorem B2296283 : Blo 1530462 2296283 := bstep (se 1 (by rfl) ⟨1722212, by rfl⟩ : syracuseStep 2296283 = 3444425) B3444425
theorem B2583049 : Blo 1530462 2583049 := bstep (se 2 (by rfl) ⟨968643, by rfl⟩ : syracuseStep 2583049 = 1937287) B1937287
theorem B1722919 : Blo 1530462 1722919 := bstep (se 1 (by rfl) ⟨1292189, by rfl⟩ : syracuseStep 1722919 = 2584379) B2584379
theorem B2181755 : Blo 1530462 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B2583211 : Blo 1530462 2583211 := bstep (se 1 (by rfl) ⟨1937408, by rfl⟩ : syracuseStep 2583211 = 3874817) B3874817
theorem B6376121 : Blo 1530462 6376121 := bstep (se 2 (by rfl) ⟨2391045, by rfl⟩ : syracuseStep 6376121 = 4782091) B4782091
theorem B3877591 : Blo 1530462 3877591 := bstep (se 1 (by rfl) ⟨2908193, by rfl⟩ : syracuseStep 3877591 = 5816387) B5816387
theorem B5172011 : Blo 1530462 5172011 := bstep (se 1 (by rfl) ⟨3879008, by rfl⟩ : syracuseStep 5172011 = 7758017) B7758017
theorem B5811011 : Blo 1530462 5811011 := bstep (se 1 (by rfl) ⟨4358258, by rfl⟩ : syracuseStep 5811011 = 8716517) B8716517
theorem B27945805 : Blo 1530462 27945805 := bstep (se 3 (by rfl) ⟨5239838, by rfl⟩ : syracuseStep 27945805 = 10479677) B10479677
theorem B2296751 : Blo 1530462 2296751 := bstep (se 1 (by rfl) ⟨1722563, by rfl⟩ : syracuseStep 2296751 = 3445127) B3445127
theorem B2583515 : Blo 1530462 2583515 := bstep (se 1 (by rfl) ⟨1937636, by rfl⟩ : syracuseStep 2583515 = 3875273) B3875273
theorem B3877895 : Blo 1530462 3877895 := bstep (se 1 (by rfl) ⟨2908421, by rfl⟩ : syracuseStep 3877895 = 5816843) B5816843
theorem B2296841 : Blo 1530462 2296841 := bstep (se 2 (by rfl) ⟨861315, by rfl⟩ : syracuseStep 2296841 = 1722631) B1722631
theorem B2296871 : Blo 1530462 2296871 := bstep (se 1 (by rfl) ⟨1722653, by rfl⟩ : syracuseStep 2296871 = 3445307) B3445307
theorem B2296955 : Blo 1530462 2296955 := bstep (se 1 (by rfl) ⟨1722716, by rfl⟩ : syracuseStep 2296955 = 3445433) B3445433
theorem B2583751 : Blo 1530462 2583751 := bstep (se 1 (by rfl) ⟨1937813, by rfl⟩ : syracuseStep 2583751 = 3875627) B3875627
theorem B2297081 : Blo 1530462 2297081 := bstep (se 2 (by rfl) ⟨861405, by rfl⟩ : syracuseStep 2297081 = 1722811) B1722811
theorem B2297183 : Blo 1530462 2297183 := bstep (se 1 (by rfl) ⟨1722887, by rfl⟩ : syracuseStep 2297183 = 3445775) B3445775
theorem B2583913 : Blo 1530462 2583913 := bstep (se 2 (by rfl) ⟨968967, by rfl⟩ : syracuseStep 2583913 = 1937935) B1937935
theorem B2297195 : Blo 1530462 2297195 := bstep (se 1 (by rfl) ⟨1722896, by rfl⟩ : syracuseStep 2297195 = 3445793) B3445793
theorem B4361597 : Blo 1530462 4361597 := bstep (se 3 (by rfl) ⟨817799, by rfl⟩ : syracuseStep 4361597 = 1635599) B1635599
theorem B4140553 : Blo 1530462 4140553 := bstep (se 2 (by rfl) ⟨1552707, by rfl⟩ : syracuseStep 4140553 = 3105415) B3105415
theorem B3444263 : Blo 1530462 3444263 := bstep (se 1 (by rfl) ⟨2583197, by rfl⟩ : syracuseStep 3444263 = 5166395) B5166395
theorem B3272231 : Blo 1530462 3272231 := bstep (se 1 (by rfl) ⟨2454173, by rfl⟩ : syracuseStep 3272231 = 4908347) B4908347
theorem B2297423 : Blo 1530462 2297423 := bstep (se 1 (by rfl) ⟨1723067, by rfl⟩ : syracuseStep 2297423 = 3446135) B3446135
theorem B2297543 : Blo 1530462 2297543 := bstep (se 1 (by rfl) ⟨1723157, by rfl⟩ : syracuseStep 2297543 = 3446315) B3446315
theorem B2297705 : Blo 1530462 2297705 := bstep (se 2 (by rfl) ⟨861639, by rfl⟩ : syracuseStep 2297705 = 1723279) B1723279
theorem B3444587 : Blo 1530462 3444587 := bstep (se 1 (by rfl) ⟨2583440, by rfl⟩ : syracuseStep 3444587 = 5166881) B5166881
theorem B6983533 : Blo 1530462 6983533 := bstep (se 3 (by rfl) ⟨1309412, by rfl⟩ : syracuseStep 6983533 = 2618825) B2618825
theorem B3444641 : Blo 1530462 3444641 := bstep (se 2 (by rfl) ⟨1291740, by rfl⟩ : syracuseStep 3444641 = 2583481) B2583481
theorem B2297783 : Blo 1530462 2297783 := bstep (se 1 (by rfl) ⟨1723337, by rfl⟩ : syracuseStep 2297783 = 3446675) B3446675
theorem B2584507 : Blo 1530462 2584507 := bstep (se 1 (by rfl) ⟨1938380, by rfl⟩ : syracuseStep 2584507 = 3876761) B3876761
theorem B2297819 : Blo 1530462 2297819 := bstep (se 1 (by rfl) ⟨1723364, by rfl⟩ : syracuseStep 2297819 = 3446729) B3446729
theorem B7860239 : Blo 1530462 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B2584615 : Blo 1530462 2584615 := bstep (se 1 (by rfl) ⟨1938461, by rfl⟩ : syracuseStep 2584615 = 3876923) B3876923
theorem B9318557 : Blo 1530462 9318557 := bstep (se 3 (by rfl) ⟨1747229, by rfl⟩ : syracuseStep 9318557 = 3494459) B3494459
theorem B3444983 : Blo 1530462 3444983 := bstep (se 1 (by rfl) ⟨2583737, by rfl⟩ : syracuseStep 3444983 = 5167475) B5167475
theorem B2584939 : Blo 1530462 2584939 := bstep (se 1 (by rfl) ⟨1938704, by rfl⟩ : syracuseStep 2584939 = 3877409) B3877409
theorem B1937839 : Blo 1530462 1937839 := bstep (se 1 (by rfl) ⟨1453379, by rfl⟩ : syracuseStep 1937839 = 2906759) B2906759
theorem B2298287 : Blo 1530462 2298287 := bstep (se 1 (by rfl) ⟨1723715, by rfl⟩ : syracuseStep 2298287 = 3447431) B3447431
theorem B5812681 : Blo 1530462 5812681 := bstep (se 2 (by rfl) ⟨2179755, by rfl⟩ : syracuseStep 5812681 = 4359511) B4359511
theorem B5165531 : Blo 1530462 5165531 := bstep (se 1 (by rfl) ⟨3874148, by rfl⟩ : syracuseStep 5165531 = 7748297) B7748297
theorem B1634779 : Blo 1530462 1634779 := bstep (se 1 (by rfl) ⟨1226084, by rfl⟩ : syracuseStep 1634779 = 2452169) B2452169
theorem B2298377 : Blo 1530462 2298377 := bstep (se 2 (by rfl) ⟨861891, by rfl⟩ : syracuseStep 2298377 = 1723783) B1723783
theorem B2298407 : Blo 1530462 2298407 := bstep (se 1 (by rfl) ⟨1723805, by rfl⟩ : syracuseStep 2298407 = 3447611) B3447611
theorem B1552975 : Blo 1530462 1552975 := bstep (se 1 (by rfl) ⟨1164731, by rfl⟩ : syracuseStep 1552975 = 2329463) B2329463
theorem B2298491 : Blo 1530462 2298491 := bstep (se 1 (by rfl) ⟨1723868, by rfl⟩ : syracuseStep 2298491 = 3447737) B3447737
theorem B5812985 : Blo 1530462 5812985 := bstep (se 2 (by rfl) ⟨2179869, by rfl⟩ : syracuseStep 5812985 = 4359739) B4359739
theorem B2298617 : Blo 1530462 2298617 := bstep (se 2 (by rfl) ⟨861981, by rfl⟩ : syracuseStep 2298617 = 1723963) B1723963
theorem B5591837 : Blo 1530462 5591837 := bstep (se 3 (by rfl) ⟨1048469, by rfl⟩ : syracuseStep 5591837 = 2096939) B2096939
theorem B3445577 : Blo 1530462 3445577 := bstep (se 2 (by rfl) ⟨1292091, by rfl⟩ : syracuseStep 3445577 = 2584183) B2584183
theorem B14725961 : Blo 1530462 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B5813153 : Blo 1530462 5813153 := bstep (se 2 (by rfl) ⟨2179932, by rfl⟩ : syracuseStep 5813153 = 4359865) B4359865
theorem B5813167 : Blo 1530462 5813167 := bstep (se 1 (by rfl) ⟨4359875, by rfl⟩ : syracuseStep 5813167 = 8719751) B8719751
theorem B9311233 : Blo 1530462 9311233 := bstep (se 2 (by rfl) ⟨3491712, by rfl⟩ : syracuseStep 9311233 = 6983425) B6983425
theorem B4363271 : Blo 1530462 4363271 := bstep (se 1 (by rfl) ⟨3272453, by rfl⟩ : syracuseStep 4363271 = 6544907) B6544907
theorem B1840207 : Blo 1530462 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B5166233 : Blo 1530462 5166233 := bstep (se 2 (by rfl) ⟨1937337, by rfl⟩ : syracuseStep 5166233 = 3874675) B3874675
theorem B5518489 : Blo 1530462 5518489 := bstep (se 2 (by rfl) ⟨2069433, by rfl⟩ : syracuseStep 5518489 = 4138867) B4138867
theorem B7664843 : Blo 1530462 7664843 := bstep (se 1 (by rfl) ⟨5748632, by rfl⟩ : syracuseStep 7664843 = 11497265) B11497265
theorem B6206807 : Blo 1530462 6206807 := bstep (se 1 (by rfl) ⟨4655105, by rfl⟩ : syracuseStep 6206807 = 9310211) B9310211
theorem B4904297 : Blo 1530462 4904297 := bstep (se 2 (by rfl) ⟨1839111, by rfl⟩ : syracuseStep 4904297 = 3678223) B3678223
theorem B4658561 : Blo 1530462 4658561 := bstep (se 2 (by rfl) ⟨1746960, by rfl⟩ : syracuseStep 4658561 = 3493921) B3493921
theorem B2585999 : Blo 1530462 2585999 := bstep (se 1 (by rfl) ⟨1939499, by rfl⟩ : syracuseStep 2585999 = 3878999) B3878999
theorem B6206939 : Blo 1530462 6206939 := bstep (se 1 (by rfl) ⟨4655204, by rfl⟩ : syracuseStep 6206939 = 9310409) B9310409
theorem B1938907 : Blo 1530462 1938907 := bstep (se 1 (by rfl) ⟨1454180, by rfl⟩ : syracuseStep 1938907 = 2908361) B2908361
theorem B3446369 : Blo 1530462 3446369 := bstep (se 2 (by rfl) ⟨1292388, by rfl⟩ : syracuseStep 3446369 = 2584777) B2584777
theorem B6985415 : Blo 1530462 6985415 := bstep (se 1 (by rfl) ⟨5239061, by rfl⟩ : syracuseStep 6985415 = 10478123) B10478123
theorem B11622203 : Blo 1530462 11622203 := bstep (se 1 (by rfl) ⟨8716652, by rfl⟩ : syracuseStep 11622203 = 17433305) B17433305
theorem B7755587 : Blo 1530462 7755587 := bstep (se 1 (by rfl) ⟨5816690, by rfl⟩ : syracuseStep 7755587 = 11633381) B11633381
theorem B5814125 : Blo 1530462 5814125 := bstep (se 3 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 5814125 = 2180297) B2180297
theorem B4904887 : Blo 1530462 4904887 := bstep (se 1 (by rfl) ⟨3678665, by rfl⟩ : syracuseStep 4904887 = 7357331) B7357331
theorem B3446711 : Blo 1530462 3446711 := bstep (se 1 (by rfl) ⟨2585033, by rfl⟩ : syracuseStep 3446711 = 5170067) B5170067
theorem B5814443 : Blo 1530462 5814443 := bstep (se 1 (by rfl) ⟨4360832, by rfl⟩ : syracuseStep 5814443 = 8721665) B8721665
theorem B27949313 : Blo 1530462 27949313 := bstep (se 2 (by rfl) ⟨10480992, by rfl⟩ : syracuseStep 27949313 = 20961985) B20961985
theorem B5167421 : Blo 1530462 5167421 := bstep (se 3 (by rfl) ⟨968891, by rfl⟩ : syracuseStep 5167421 = 1937783) B1937783
theorem B9812285 : Blo 1530462 9812285 := bstep (se 3 (by rfl) ⟨1839803, by rfl⟩ : syracuseStep 9812285 = 3679607) B3679607
theorem B11032937 : Blo 1530462 11032937 := bstep (se 2 (by rfl) ⟨4137351, by rfl⟩ : syracuseStep 11032937 = 8274703) B8274703
theorem B3447305 : Blo 1530462 3447305 := bstep (se 2 (by rfl) ⟨1292739, by rfl⟩ : syracuseStep 3447305 = 2585479) B2585479
theorem B6208039 : Blo 1530462 6208039 := bstep (se 1 (by rfl) ⟨4656029, by rfl⟩ : syracuseStep 6208039 = 9312059) B9312059
theorem B1530463 : Blo 1530462 1530463 := bstep (se 1 (by rfl) ⟨1147847, by rfl⟩ : syracuseStep 1530463 = 2295695) B2295695
theorem B1530491 : Blo 1530462 1530491 := bstep (se 1 (by rfl) ⟨1147868, by rfl⟩ : syracuseStep 1530491 = 2295737) B2295737
theorem B1530543 : Blo 1530462 1530543 := bstep (se 1 (by rfl) ⟨1147907, by rfl⟩ : syracuseStep 1530543 = 2295815) B2295815
theorem B24853171 : Blo 1530462 24853171 := bstep (se 1 (by rfl) ⟨18639878, by rfl⟩ : syracuseStep 24853171 = 37279757) B37279757
theorem B1530567 : Blo 1530462 1530567 := bstep (se 1 (by rfl) ⟨1147925, by rfl⟩ : syracuseStep 1530567 = 2295851) B2295851
theorem B4659923 : Blo 1530462 4659923 := bstep (se 1 (by rfl) ⟨3494942, by rfl⟩ : syracuseStep 4659923 = 6989885) B6989885
theorem B1530587 : Blo 1530462 1530587 := bstep (se 1 (by rfl) ⟨1147940, by rfl⟩ : syracuseStep 1530587 = 2295881) B2295881
theorem B1530663 : Blo 1530462 1530663 := bstep (se 1 (by rfl) ⟨1147997, by rfl⟩ : syracuseStep 1530663 = 2295995) B2295995
theorem B11631437 : Blo 1530462 11631437 := bstep (se 3 (by rfl) ⟨2180894, by rfl⟩ : syracuseStep 11631437 = 4361789) B4361789
theorem B1530703 : Blo 1530462 1530703 := bstep (se 1 (by rfl) ⟨1148027, by rfl⟩ : syracuseStep 1530703 = 2296055) B2296055
theorem B1530719 : Blo 1530462 1530719 := bstep (se 1 (by rfl) ⟨1148039, by rfl⟩ : syracuseStep 1530719 = 2296079) B2296079
theorem B3447647 : Blo 1530462 3447647 := bstep (se 1 (by rfl) ⟨2585735, by rfl⟩ : syracuseStep 3447647 = 5171471) B5171471
theorem B7748459 : Blo 1530462 7748459 := bstep (se 1 (by rfl) ⟨5811344, by rfl⟩ : syracuseStep 7748459 = 11622689) B11622689
theorem B1530747 : Blo 1530462 1530747 := bstep (se 1 (by rfl) ⟨1148060, by rfl⟩ : syracuseStep 1530747 = 2296121) B2296121
theorem B1530799 : Blo 1530462 1530799 := bstep (se 1 (by rfl) ⟨1148099, by rfl⟩ : syracuseStep 1530799 = 2296199) B2296199
theorem B8723375 : Blo 1530462 8723375 := bstep (se 1 (by rfl) ⟨6542531, by rfl⟩ : syracuseStep 8723375 = 13085063) B13085063
theorem B1530823 : Blo 1530462 1530823 := bstep (se 1 (by rfl) ⟨1148117, by rfl⟩ : syracuseStep 1530823 = 2296235) B2296235
theorem B1530843 : Blo 1530462 1530843 := bstep (se 1 (by rfl) ⟨1148132, by rfl⟩ : syracuseStep 1530843 = 2296265) B2296265
theorem B3447827 : Blo 1530462 3447827 := bstep (se 1 (by rfl) ⟨2585870, by rfl⟩ : syracuseStep 3447827 = 5171741) B5171741
theorem B1530919 : Blo 1530462 1530919 := bstep (se 1 (by rfl) ⟨1148189, by rfl⟩ : syracuseStep 1530919 = 2296379) B2296379
theorem B1530959 : Blo 1530462 1530959 := bstep (se 1 (by rfl) ⟨1148219, by rfl⟩ : syracuseStep 1530959 = 2296439) B2296439
theorem B1530975 : Blo 1530462 1530975 := bstep (se 1 (by rfl) ⟨1148231, by rfl⟩ : syracuseStep 1530975 = 2296463) B2296463
theorem B1531003 : Blo 1530462 1531003 := bstep (se 1 (by rfl) ⟨1148252, by rfl⟩ : syracuseStep 1531003 = 2296505) B2296505
theorem B5168285 : Blo 1530462 5168285 := bstep (se 3 (by rfl) ⟨969053, by rfl⟩ : syracuseStep 5168285 = 1938107) B1938107
theorem B6290603 : Blo 1530462 6290603 := bstep (se 1 (by rfl) ⟨4717952, by rfl⟩ : syracuseStep 6290603 = 9435905) B9435905
theorem B1531055 : Blo 1530462 1531055 := bstep (se 1 (by rfl) ⟨1148291, by rfl⟩ : syracuseStep 1531055 = 2296583) B2296583
theorem B1531079 : Blo 1530462 1531079 := bstep (se 1 (by rfl) ⟨1148309, by rfl⟩ : syracuseStep 1531079 = 2296619) B2296619
theorem B1531099 : Blo 1530462 1531099 := bstep (se 1 (by rfl) ⟨1148324, by rfl⟩ : syracuseStep 1531099 = 2296649) B2296649
theorem B13090085 : Blo 1530462 13090085 := bstep (se 4 (by rfl) ⟨1227195, by rfl⟩ : syracuseStep 13090085 = 2454391) B2454391
theorem B1531175 : Blo 1530462 1531175 := bstep (se 1 (by rfl) ⟨1148381, by rfl⟩ : syracuseStep 1531175 = 2296763) B2296763
theorem B1531215 : Blo 1530462 1531215 := bstep (se 1 (by rfl) ⟨1148411, by rfl⟩ : syracuseStep 1531215 = 2296823) B2296823
theorem B1531231 : Blo 1530462 1531231 := bstep (se 1 (by rfl) ⟨1148423, by rfl⟩ : syracuseStep 1531231 = 2296847) B2296847
theorem B1531259 : Blo 1530462 1531259 := bstep (se 1 (by rfl) ⟨1148444, by rfl⟩ : syracuseStep 1531259 = 2296889) B2296889
theorem B7273901 : Blo 1530462 7273901 := bstep (se 3 (by rfl) ⟨1363856, by rfl⟩ : syracuseStep 7273901 = 2727713) B2727713
theorem B1531311 : Blo 1530462 1531311 := bstep (se 1 (by rfl) ⟨1148483, by rfl⟩ : syracuseStep 1531311 = 2296967) B2296967
theorem B3104183 : Blo 1530462 3104183 := bstep (se 1 (by rfl) ⟨2328137, by rfl⟩ : syracuseStep 3104183 = 4656275) B4656275
theorem B1531335 : Blo 1530462 1531335 := bstep (se 1 (by rfl) ⟨1148501, by rfl⟩ : syracuseStep 1531335 = 2297003) B2297003
theorem B1531355 : Blo 1530462 1531355 := bstep (se 1 (by rfl) ⟨1148516, by rfl⟩ : syracuseStep 1531355 = 2297033) B2297033
theorem B7749107 : Blo 1530462 7749107 := bstep (se 1 (by rfl) ⟨5811830, by rfl⟩ : syracuseStep 7749107 = 11623661) B11623661
theorem B3104263 : Blo 1530462 3104263 := bstep (se 1 (by rfl) ⟨2328197, by rfl⟩ : syracuseStep 3104263 = 4656395) B4656395
theorem B1531431 : Blo 1530462 1531431 := bstep (se 1 (by rfl) ⟨1148573, by rfl⟩ : syracuseStep 1531431 = 2297147) B2297147
theorem B1531471 : Blo 1530462 1531471 := bstep (se 1 (by rfl) ⟨1148603, by rfl⟩ : syracuseStep 1531471 = 2297207) B2297207
theorem B1531487 : Blo 1530462 1531487 := bstep (se 1 (by rfl) ⟨1148615, by rfl⟩ : syracuseStep 1531487 = 2297231) B2297231
theorem B4423265 : Blo 1530462 4423265 := bstep (se 2 (by rfl) ⟨1658724, by rfl⟩ : syracuseStep 4423265 = 3317449) B3317449
theorem B1531515 : Blo 1530462 1531515 := bstep (se 1 (by rfl) ⟨1148636, by rfl⟩ : syracuseStep 1531515 = 2297273) B2297273
theorem B1531567 : Blo 1530462 1531567 := bstep (se 1 (by rfl) ⟨1148675, by rfl⟩ : syracuseStep 1531567 = 2297351) B2297351
theorem B5168825 : Blo 1530462 5168825 := bstep (se 2 (by rfl) ⟨1938309, by rfl⟩ : syracuseStep 5168825 = 3876619) B3876619
theorem B1531591 : Blo 1530462 1531591 := bstep (se 1 (by rfl) ⟨1148693, by rfl⟩ : syracuseStep 1531591 = 2297387) B2297387
theorem B1531611 : Blo 1530462 1531611 := bstep (se 1 (by rfl) ⟨1148708, by rfl⟩ : syracuseStep 1531611 = 2297417) B2297417
theorem B6209273 : Blo 1530462 6209273 := bstep (se 2 (by rfl) ⟨2328477, by rfl⟩ : syracuseStep 6209273 = 4656955) B4656955
theorem B1531687 : Blo 1530462 1531687 := bstep (se 1 (by rfl) ⟨1148765, by rfl⟩ : syracuseStep 1531687 = 2297531) B2297531
theorem B1531727 : Blo 1530462 1531727 := bstep (se 1 (by rfl) ⟨1148795, by rfl⟩ : syracuseStep 1531727 = 2297591) B2297591
theorem B3874655 : Blo 1530462 3874655 := bstep (se 1 (by rfl) ⟨2905991, by rfl⟩ : syracuseStep 3874655 = 5811983) B5811983
theorem B7855967 : Blo 1530462 7855967 := bstep (se 1 (by rfl) ⟨5891975, by rfl⟩ : syracuseStep 7855967 = 11783951) B11783951
theorem B1531743 : Blo 1530462 1531743 := bstep (se 1 (by rfl) ⟨1148807, by rfl⟩ : syracuseStep 1531743 = 2297615) B2297615
theorem B1531771 : Blo 1530462 1531771 := bstep (se 1 (by rfl) ⟨1148828, by rfl⟩ : syracuseStep 1531771 = 2297657) B2297657
theorem B1531823 : Blo 1530462 1531823 := bstep (se 1 (by rfl) ⟨1148867, by rfl⟩ : syracuseStep 1531823 = 2297735) B2297735
theorem B1531847 : Blo 1530462 1531847 := bstep (se 1 (by rfl) ⟨1148885, by rfl⟩ : syracuseStep 1531847 = 2297771) B2297771
theorem B1531867 : Blo 1530462 1531867 := bstep (se 1 (by rfl) ⟨1148900, by rfl⟩ : syracuseStep 1531867 = 2297801) B2297801
theorem B26165267 : Blo 1530462 26165267 := bstep (se 1 (by rfl) ⟨19623950, by rfl⟩ : syracuseStep 26165267 = 39247901) B39247901
theorem B13090835 : Blo 1530462 13090835 := bstep (se 1 (by rfl) ⟨9818126, by rfl⟩ : syracuseStep 13090835 = 19636253) B19636253
theorem B16556069 : Blo 1530462 16556069 := bstep (se 4 (by rfl) ⟨1552131, by rfl⟩ : syracuseStep 16556069 = 3104263) B3104263
theorem B5169257 : Blo 1530462 5169257 := bstep (se 2 (by rfl) ⟨1938471, by rfl⟩ : syracuseStep 5169257 = 3876943) B3876943
theorem B1532191 : Blo 1530462 1532191 := bstep (se 1 (by rfl) ⟨1149143, by rfl⟩ : syracuseStep 1532191 = 2298287) B2298287
theorem B1532251 : Blo 1530462 1532251 := bstep (se 1 (by rfl) ⟨1149188, by rfl⟩ : syracuseStep 1532251 = 2298377) B2298377
theorem B1532271 : Blo 1530462 1532271 := bstep (se 1 (by rfl) ⟨1149203, by rfl⟩ : syracuseStep 1532271 = 2298407) B2298407
theorem B1532327 : Blo 1530462 1532327 := bstep (se 1 (by rfl) ⟨1149245, by rfl⟩ : syracuseStep 1532327 = 2298491) B2298491
theorem B3875323 : Blo 1530462 3875323 := bstep (se 1 (by rfl) ⟨2906492, by rfl⟩ : syracuseStep 3875323 = 5812985) B5812985
theorem B1532411 : Blo 1530462 1532411 := bstep (se 1 (by rfl) ⟨1149308, by rfl⟩ : syracuseStep 1532411 = 2298617) B2298617
theorem B3727891 : Blo 1530462 3727891 := bstep (se 1 (by rfl) ⟨2795918, by rfl⟩ : syracuseStep 3727891 = 5591837) B5591837
theorem B7750241 : Blo 1530462 7750241 := bstep (se 2 (by rfl) ⟨2906340, by rfl⟩ : syracuseStep 7750241 = 5812681) B5812681
theorem B3875435 : Blo 1530462 3875435 := bstep (se 1 (by rfl) ⟨2906576, by rfl⟩ : syracuseStep 3875435 = 5813153) B5813153
theorem B2179705 : Blo 1530462 2179705 := bstep (se 2 (by rfl) ⟨817389, by rfl⟩ : syracuseStep 2179705 = 1634779) B1634779
theorem B2908847 : Blo 1530462 2908847 := bstep (se 1 (by rfl) ⟨2181635, by rfl⟩ : syracuseStep 2908847 = 4363271) B4363271
theorem B7455415 : Blo 1530462 7455415 := bstep (se 1 (by rfl) ⟨5591561, by rfl⟩ : syracuseStep 7455415 = 11183123) B11183123
theorem B5817055 : Blo 1530462 5817055 := bstep (se 1 (by rfl) ⟨4362791, by rfl⟩ : syracuseStep 5817055 = 8725583) B8725583
theorem B58852169 : Blo 1530462 58852169 := bstep (se 2 (by rfl) ⟨22069563, by rfl⟩ : syracuseStep 58852169 = 44139127) B44139127
theorem B8282989 : Blo 1530462 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B4137871 : Blo 1530462 4137871 := bstep (se 1 (by rfl) ⟨3103403, by rfl⟩ : syracuseStep 4137871 = 6206807) B6206807
theorem B33137561 : Blo 1530462 33137561 := bstep (se 2 (by rfl) ⟨12426585, by rfl⟩ : syracuseStep 33137561 = 24853171) B24853171
theorem B3269531 : Blo 1530462 3269531 := bstep (se 1 (by rfl) ⟨2452148, by rfl⟩ : syracuseStep 3269531 = 4904297) B4904297
theorem B3105707 : Blo 1530462 3105707 := bstep (se 1 (by rfl) ⟨2329280, by rfl⟩ : syracuseStep 3105707 = 4658561) B4658561
theorem B5170121 : Blo 1530462 5170121 := bstep (se 2 (by rfl) ⟨1938795, by rfl⟩ : syracuseStep 5170121 = 3877591) B3877591
theorem B4137959 : Blo 1530462 4137959 := bstep (se 1 (by rfl) ⟨3103469, by rfl⟩ : syracuseStep 4137959 = 6206939) B6206939
theorem B5170391 : Blo 1530462 5170391 := bstep (se 1 (by rfl) ⟨3877793, by rfl⟩ : syracuseStep 5170391 = 7755587) B7755587
theorem B7750889 : Blo 1530462 7750889 := bstep (se 2 (by rfl) ⟨2906583, by rfl⟩ : syracuseStep 7750889 = 5813167) B5813167
theorem B3876083 : Blo 1530462 3876083 := bstep (se 1 (by rfl) ⟨2907062, by rfl⟩ : syracuseStep 3876083 = 5814125) B5814125
theorem B6538583 : Blo 1530462 6538583 := bstep (se 1 (by rfl) ⟨4903937, by rfl⟩ : syracuseStep 6538583 = 9807875) B9807875
theorem B7751051 : Blo 1530462 7751051 := bstep (se 1 (by rfl) ⟨5813288, by rfl⟩ : syracuseStep 7751051 = 11626577) B11626577
theorem B3876295 : Blo 1530462 3876295 := bstep (se 1 (by rfl) ⟨2907221, by rfl⟩ : syracuseStep 3876295 = 5814443) B5814443
theorem B7357985 : Blo 1530462 7357985 := bstep (se 2 (by rfl) ⟨2759244, by rfl⟩ : syracuseStep 7357985 = 5518489) B5518489
theorem B33130133 : Blo 1530462 33130133 := bstep (se 6 (by rfl) ⟨776487, by rfl⟩ : syracuseStep 33130133 = 1552975) B1552975
theorem B5818013 : Blo 1530462 5818013 := bstep (se 3 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 5818013 = 2181755) B2181755
theorem B3106615 : Blo 1530462 3106615 := bstep (se 1 (by rfl) ⟨2329961, by rfl⟩ : syracuseStep 3106615 = 4659923) B4659923
theorem B1722343 : Blo 1530462 1722343 := bstep (se 1 (by rfl) ⟨1291757, by rfl⟩ : syracuseStep 1722343 = 2583515) B2583515
theorem B8726723 : Blo 1530462 8726723 := bstep (se 1 (by rfl) ⟨6545042, by rfl⟩ : syracuseStep 8726723 = 13090085) B13090085
theorem B2296073 : Blo 1530462 2296073 := bstep (se 2 (by rfl) ⟨861027, by rfl⟩ : syracuseStep 2296073 = 1722055) B1722055
theorem B2296175 : Blo 1530462 2296175 := bstep (se 1 (by rfl) ⟨1722131, by rfl⟩ : syracuseStep 2296175 = 3444263) B3444263
theorem B2181487 : Blo 1530462 2181487 := bstep (se 1 (by rfl) ⟨1636115, by rfl⟩ : syracuseStep 2181487 = 3272231) B3272231
theorem B4139515 : Blo 1530462 4139515 := bstep (se 1 (by rfl) ⟨3104636, by rfl⟩ : syracuseStep 4139515 = 6209273) B6209273
theorem B2583103 : Blo 1530462 2583103 := bstep (se 1 (by rfl) ⟨1937327, by rfl⟩ : syracuseStep 2583103 = 3874655) B3874655
theorem B5237311 : Blo 1530462 5237311 := bstep (se 1 (by rfl) ⟨3927983, by rfl⟩ : syracuseStep 5237311 = 7855967) B7855967
theorem B2296391 : Blo 1530462 2296391 := bstep (se 1 (by rfl) ⟨1722293, by rfl⟩ : syracuseStep 2296391 = 3444587) B3444587
theorem B6539849 : Blo 1530462 6539849 := bstep (se 2 (by rfl) ⟨2452443, by rfl⟩ : syracuseStep 6539849 = 4904887) B4904887
theorem B2296427 : Blo 1530462 2296427 := bstep (se 1 (by rfl) ⟨1722320, by rfl⟩ : syracuseStep 2296427 = 3444641) B3444641
theorem B5515951 : Blo 1530462 5515951 := bstep (se 1 (by rfl) ⟨4136963, by rfl⟩ : syracuseStep 5515951 = 8273927) B8273927
theorem B6212371 : Blo 1530462 6212371 := bstep (se 1 (by rfl) ⟨4659278, by rfl⟩ : syracuseStep 6212371 = 9318557) B9318557
theorem B2296655 : Blo 1530462 2296655 := bstep (se 1 (by rfl) ⟨1722491, by rfl⟩ : syracuseStep 2296655 = 3444983) B3444983
theorem B35367815 : Blo 1530462 35367815 := bstep (se 1 (by rfl) ⟨26525861, by rfl⟩ : syracuseStep 35367815 = 53051723) B53051723
theorem B88337303 : Blo 1530462 88337303 := bstep (se 1 (by rfl) ⟨66252977, by rfl⟩ : syracuseStep 88337303 = 132505955) B132505955
theorem B4139947 : Blo 1530462 4139947 := bstep (se 1 (by rfl) ⟨3104960, by rfl⟩ : syracuseStep 4139947 = 6209921) B6209921
theorem B3443687 : Blo 1530462 3443687 := bstep (se 1 (by rfl) ⟨2582765, by rfl⟩ : syracuseStep 3443687 = 5165531) B5165531
theorem B13085711 : Blo 1530462 13085711 := bstep (se 1 (by rfl) ⟨9814283, by rfl⟩ : syracuseStep 13085711 = 19628567) B19628567
theorem B3878027 : Blo 1530462 3878027 := bstep (se 1 (by rfl) ⟨2908520, by rfl⟩ : syracuseStep 3878027 = 5817041) B5817041
theorem B19623131 : Blo 1530462 19623131 := bstep (se 1 (by rfl) ⟨14717348, by rfl⟩ : syracuseStep 19623131 = 29434697) B29434697
theorem B2297051 : Blo 1530462 2297051 := bstep (se 1 (by rfl) ⟨1722788, by rfl⟩ : syracuseStep 2297051 = 3445577) B3445577
theorem B9817307 : Blo 1530462 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B2583785 : Blo 1530462 2583785 := bstep (se 2 (by rfl) ⟨968919, by rfl⟩ : syracuseStep 2583785 = 1937839) B1937839
theorem B2583839 : Blo 1530462 2583839 := bstep (se 1 (by rfl) ⟨1937879, by rfl⟩ : syracuseStep 2583839 = 3875759) B3875759
theorem B3878239 : Blo 1530462 3878239 := bstep (se 1 (by rfl) ⟨2908679, by rfl⟩ : syracuseStep 3878239 = 5817359) B5817359
theorem B3444065 : Blo 1530462 3444065 := bstep (se 2 (by rfl) ⟨1291524, by rfl⟩ : syracuseStep 3444065 = 2583049) B2583049
theorem B8277385 : Blo 1530462 8277385 := bstep (se 2 (by rfl) ⟨3104019, by rfl⟩ : syracuseStep 8277385 = 6208039) B6208039
theorem B2297225 : Blo 1530462 2297225 := bstep (se 2 (by rfl) ⟨861459, by rfl⟩ : syracuseStep 2297225 = 1722919) B1722919
theorem B3444155 : Blo 1530462 3444155 := bstep (se 1 (by rfl) ⟨2583116, by rfl⟩ : syracuseStep 3444155 = 5166233) B5166233
theorem B3444281 : Blo 1530462 3444281 := bstep (se 2 (by rfl) ⟨1291605, by rfl⟩ : syracuseStep 3444281 = 2583211) B2583211
theorem B5893715 : Blo 1530462 5893715 := bstep (se 1 (by rfl) ⟨4420286, by rfl⟩ : syracuseStep 5893715 = 8840573) B8840573
theorem B3681875 : Blo 1530462 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B1723999 : Blo 1530462 1723999 := bstep (se 1 (by rfl) ⟨1292999, by rfl⟩ : syracuseStep 1723999 = 2585999) B2585999
theorem B6631121 : Blo 1530462 6631121 := bstep (se 2 (by rfl) ⟨2486670, by rfl⟩ : syracuseStep 6631121 = 4973341) B4973341
theorem B2297579 : Blo 1530462 2297579 := bstep (se 1 (by rfl) ⟨1723184, by rfl⟩ : syracuseStep 2297579 = 3446369) B3446369
theorem B37261073 : Blo 1530462 37261073 := bstep (se 2 (by rfl) ⟨13972902, by rfl⟩ : syracuseStep 37261073 = 27945805) B27945805
theorem B4656943 : Blo 1530462 4656943 := bstep (se 1 (by rfl) ⟨3492707, by rfl⟩ : syracuseStep 4656943 = 6985415) B6985415
theorem B2297807 : Blo 1530462 2297807 := bstep (se 1 (by rfl) ⟨1723355, by rfl⟩ : syracuseStep 2297807 = 3446711) B3446711
theorem B15708113 : Blo 1530462 15708113 := bstep (se 2 (by rfl) ⟨5890542, by rfl⟩ : syracuseStep 15708113 = 11781085) B11781085
theorem B12414977 : Blo 1530462 12414977 := bstep (se 2 (by rfl) ⟨4655616, by rfl⟩ : syracuseStep 12414977 = 9311233) B9311233
theorem B2453609 : Blo 1530462 2453609 := bstep (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) B1840207
theorem B18632875 : Blo 1530462 18632875 := bstep (se 1 (by rfl) ⟨13974656, by rfl⟩ : syracuseStep 18632875 = 27949313) B27949313
theorem B3444947 : Blo 1530462 3444947 := bstep (se 1 (by rfl) ⟨2583710, by rfl⟩ : syracuseStep 3444947 = 5167421) B5167421
theorem B6541523 : Blo 1530462 6541523 := bstep (se 1 (by rfl) ⟨4906142, by rfl⟩ : syracuseStep 6541523 = 9812285) B9812285
theorem B3445001 : Blo 1530462 3445001 := bstep (se 2 (by rfl) ⟨1291875, by rfl⟩ : syracuseStep 3445001 = 2583751) B2583751
theorem B2298203 : Blo 1530462 2298203 := bstep (se 1 (by rfl) ⟨1723652, by rfl⟩ : syracuseStep 2298203 = 3447305) B3447305
theorem B3445217 : Blo 1530462 3445217 := bstep (se 2 (by rfl) ⟨1291956, by rfl⟩ : syracuseStep 3445217 = 2583913) B2583913
theorem B7754291 : Blo 1530462 7754291 := bstep (se 1 (by rfl) ⟨5815718, by rfl⟩ : syracuseStep 7754291 = 11631437) B11631437
theorem B2298431 : Blo 1530462 2298431 := bstep (se 1 (by rfl) ⟨1723823, by rfl⟩ : syracuseStep 2298431 = 3447647) B3447647
theorem B5165639 : Blo 1530462 5165639 := bstep (se 1 (by rfl) ⟨3874229, by rfl⟩ : syracuseStep 5165639 = 7748459) B7748459
theorem B2585209 : Blo 1530462 2585209 := bstep (se 2 (by rfl) ⟨969453, by rfl⟩ : syracuseStep 2585209 = 1938907) B1938907
theorem B2585263 : Blo 1530462 2585263 := bstep (se 1 (by rfl) ⟨1938947, by rfl⟩ : syracuseStep 2585263 = 3877895) B3877895
theorem B2298551 : Blo 1530462 2298551 := bstep (se 1 (by rfl) ⟨1723913, by rfl⟩ : syracuseStep 2298551 = 3447827) B3447827
theorem B3445523 : Blo 1530462 3445523 := bstep (se 1 (by rfl) ⟨2584142, by rfl⟩ : syracuseStep 3445523 = 5168285) B5168285
theorem B2069455 : Blo 1530462 2069455 := bstep (se 1 (by rfl) ⟨1552091, by rfl⟩ : syracuseStep 2069455 = 3104183) B3104183
theorem B5166071 : Blo 1530462 5166071 := bstep (se 1 (by rfl) ⟨3874553, by rfl⟩ : syracuseStep 5166071 = 7749107) B7749107
theorem B3445883 : Blo 1530462 3445883 := bstep (se 1 (by rfl) ⟨2584412, by rfl⟩ : syracuseStep 3445883 = 5168825) B5168825
theorem B9311377 : Blo 1530462 9311377 := bstep (se 2 (by rfl) ⟨3491766, by rfl⟩ : syracuseStep 9311377 = 6983533) B6983533
theorem B3446009 : Blo 1530462 3446009 := bstep (se 2 (by rfl) ⟨1292253, by rfl⟩ : syracuseStep 3446009 = 2584507) B2584507
theorem B5240159 : Blo 1530462 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B7361887 : Blo 1530462 7361887 := bstep (se 1 (by rfl) ⟨5521415, by rfl⟩ : syracuseStep 7361887 = 11042831) B11042831
theorem B1938811 : Blo 1530462 1938811 := bstep (se 1 (by rfl) ⟨1454108, by rfl⟩ : syracuseStep 1938811 = 2908217) B2908217
theorem B3446153 : Blo 1530462 3446153 := bstep (se 2 (by rfl) ⟨1292307, by rfl⟩ : syracuseStep 3446153 = 2584615) B2584615
theorem B9811361 : Blo 1530462 9811361 := bstep (se 2 (by rfl) ⟨3679260, by rfl⟩ : syracuseStep 9811361 = 7358521) B7358521
theorem B3446279 : Blo 1530462 3446279 := bstep (se 1 (by rfl) ⟨2584709, by rfl⟩ : syracuseStep 3446279 = 5169419) B5169419
theorem B31446593 : Blo 1530462 31446593 := bstep (se 2 (by rfl) ⟨11792472, by rfl⟩ : syracuseStep 31446593 = 23584945) B23584945
theorem B2905787 : Blo 1530462 2905787 := bstep (se 1 (by rfl) ⟨2179340, by rfl⟩ : syracuseStep 2905787 = 4358681) B4358681
theorem B3446459 : Blo 1530462 3446459 := bstep (se 1 (by rfl) ⟨2584844, by rfl⟩ : syracuseStep 3446459 = 5169689) B5169689
theorem B3446585 : Blo 1530462 3446585 := bstep (se 2 (by rfl) ⟨1292469, by rfl⟩ : syracuseStep 3446585 = 2584939) B2584939
theorem B5166935 : Blo 1530462 5166935 := bstep (se 1 (by rfl) ⟨3875201, by rfl⟩ : syracuseStep 5166935 = 7750403) B7750403
theorem B5109895 : Blo 1530462 5109895 := bstep (se 1 (by rfl) ⟨3832421, by rfl⟩ : syracuseStep 5109895 = 7664843) B7664843
theorem B15718535 : Blo 1530462 15718535 := bstep (se 1 (by rfl) ⟨11788901, by rfl⟩ : syracuseStep 15718535 = 23577803) B23577803
theorem B7755911 : Blo 1530462 7755911 := bstep (se 1 (by rfl) ⟨5816933, by rfl⟩ : syracuseStep 7755911 = 11633867) B11633867
theorem B11032823 : Blo 1530462 11032823 := bstep (se 1 (by rfl) ⟨8274617, by rfl⟩ : syracuseStep 11032823 = 16549235) B16549235
theorem B6543625 : Blo 1530462 6543625 := bstep (se 2 (by rfl) ⟨2453859, by rfl⟩ : syracuseStep 6543625 = 4907719) B4907719
theorem B6543641 : Blo 1530462 6543641 := bstep (se 2 (by rfl) ⟨2453865, by rfl⟩ : syracuseStep 6543641 = 4907731) B4907731
theorem B3447215 : Blo 1530462 3447215 := bstep (se 1 (by rfl) ⟨2585411, by rfl⟩ : syracuseStep 3447215 = 5170823) B5170823
theorem B3447251 : Blo 1530462 3447251 := bstep (se 1 (by rfl) ⟨2585438, by rfl⟩ : syracuseStep 3447251 = 5170877) B5170877
theorem B7748135 : Blo 1530462 7748135 := bstep (se 1 (by rfl) ⟨5811101, by rfl⟩ : syracuseStep 7748135 = 11622203) B11622203
theorem B3447359 : Blo 1530462 3447359 := bstep (se 1 (by rfl) ⟨2585519, by rfl⟩ : syracuseStep 3447359 = 5171039) B5171039
theorem B7854671 : Blo 1530462 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B3447467 : Blo 1530462 3447467 := bstep (se 1 (by rfl) ⟨2585600, by rfl⟩ : syracuseStep 3447467 = 5171201) B5171201
theorem B1530591 : Blo 1530462 1530591 := bstep (se 1 (by rfl) ⟨1147943, by rfl⟩ : syracuseStep 1530591 = 2295887) B2295887
theorem B1530671 : Blo 1530462 1530671 := bstep (se 1 (by rfl) ⟨1148003, by rfl⟩ : syracuseStep 1530671 = 2296007) B2296007
theorem B5168015 : Blo 1530462 5168015 := bstep (se 1 (by rfl) ⟨3876011, by rfl⟩ : syracuseStep 5168015 = 7752023) B7752023
theorem B7355291 : Blo 1530462 7355291 := bstep (se 1 (by rfl) ⟨5516468, by rfl⟩ : syracuseStep 7355291 = 11032937) B11032937
theorem B1530779 : Blo 1530462 1530779 := bstep (se 1 (by rfl) ⟨1148084, by rfl⟩ : syracuseStep 1530779 = 2296169) B2296169
theorem B1530831 : Blo 1530462 1530831 := bstep (se 1 (by rfl) ⟨1148123, by rfl⟩ : syracuseStep 1530831 = 2296247) B2296247
theorem B1530855 : Blo 1530462 1530855 := bstep (se 1 (by rfl) ⟨1148141, by rfl⟩ : syracuseStep 1530855 = 2296283) B2296283
theorem B4250747 : Blo 1530462 4250747 := bstep (se 1 (by rfl) ⟨3188060, by rfl⟩ : syracuseStep 4250747 = 6376121) B6376121
theorem B3448007 : Blo 1530462 3448007 := bstep (se 1 (by rfl) ⟨2586005, by rfl⟩ : syracuseStep 3448007 = 5172011) B5172011
theorem B3874007 : Blo 1530462 3874007 := bstep (se 1 (by rfl) ⟨2905505, by rfl⟩ : syracuseStep 3874007 = 5811011) B5811011
theorem B1531167 : Blo 1530462 1531167 := bstep (se 1 (by rfl) ⟨1148375, by rfl⟩ : syracuseStep 1531167 = 2296751) B2296751
theorem B5815583 : Blo 1530462 5815583 := bstep (se 1 (by rfl) ⟨4361687, by rfl⟩ : syracuseStep 5815583 = 8723375) B8723375
theorem B1531227 : Blo 1530462 1531227 := bstep (se 1 (by rfl) ⟨1148420, by rfl⟩ : syracuseStep 1531227 = 2296841) B2296841
theorem B5520737 : Blo 1530462 5520737 := bstep (se 2 (by rfl) ⟨2070276, by rfl⟩ : syracuseStep 5520737 = 4140553) B4140553
theorem B1531247 : Blo 1530462 1531247 := bstep (se 1 (by rfl) ⟨1148435, by rfl⟩ : syracuseStep 1531247 = 2296871) B2296871
theorem B1531303 : Blo 1530462 1531303 := bstep (se 1 (by rfl) ⟨1148477, by rfl⟩ : syracuseStep 1531303 = 2296955) B2296955
theorem B4193735 : Blo 1530462 4193735 := bstep (se 1 (by rfl) ⟨3145301, by rfl⟩ : syracuseStep 4193735 = 6290603) B6290603
theorem B4906489 : Blo 1530462 4906489 := bstep (se 2 (by rfl) ⟨1839933, by rfl⟩ : syracuseStep 4906489 = 3679867) B3679867
theorem B1531387 : Blo 1530462 1531387 := bstep (se 1 (by rfl) ⟨1148540, by rfl⟩ : syracuseStep 1531387 = 2297081) B2297081
theorem B1531455 : Blo 1530462 1531455 := bstep (se 1 (by rfl) ⟨1148591, by rfl⟩ : syracuseStep 1531455 = 2297183) B2297183
theorem B1531463 : Blo 1530462 1531463 := bstep (se 1 (by rfl) ⟨1148597, by rfl⟩ : syracuseStep 1531463 = 2297195) B2297195
theorem B2907731 : Blo 1530462 2907731 := bstep (se 1 (by rfl) ⟨2180798, by rfl⟩ : syracuseStep 2907731 = 4361597) B4361597
theorem B4849267 : Blo 1530462 4849267 := bstep (se 1 (by rfl) ⟨3636950, by rfl⟩ : syracuseStep 4849267 = 7273901) B7273901
theorem B1531615 : Blo 1530462 1531615 := bstep (se 1 (by rfl) ⟨1148711, by rfl⟩ : syracuseStep 1531615 = 2297423) B2297423
theorem B2948843 : Blo 1530462 2948843 := bstep (se 1 (by rfl) ⟨2211632, by rfl⟩ : syracuseStep 2948843 = 4423265) B4423265
theorem B1531695 : Blo 1530462 1531695 := bstep (se 1 (by rfl) ⟨1148771, by rfl⟩ : syracuseStep 1531695 = 2297543) B2297543
theorem B6545281 : Blo 1530462 6545281 := bstep (se 2 (by rfl) ⟨2454480, by rfl⟩ : syracuseStep 6545281 = 4908961) B4908961
theorem B1531803 : Blo 1530462 1531803 := bstep (se 1 (by rfl) ⟨1148852, by rfl⟩ : syracuseStep 1531803 = 2297705) B2297705
theorem B1531855 : Blo 1530462 1531855 := bstep (se 1 (by rfl) ⟨1148891, by rfl⟩ : syracuseStep 1531855 = 2297783) B2297783
theorem B1531879 : Blo 1530462 1531879 := bstep (se 1 (by rfl) ⟨1148909, by rfl⟩ : syracuseStep 1531879 = 2297819) B2297819
theorem B1532135 : Blo 1530462 1532135 := bstep (se 1 (by rfl) ⟨1149101, by rfl⟩ : syracuseStep 1532135 = 2298203) B2298203
theorem B8724833 : Blo 1530462 8724833 := bstep (se 2 (by rfl) ⟨3271812, by rfl⟩ : syracuseStep 8724833 = 6543625) B6543625
theorem B5169527 : Blo 1530462 5169527 := bstep (se 1 (by rfl) ⟨3877145, by rfl⟩ : syracuseStep 5169527 = 7754291) B7754291
theorem B1532287 : Blo 1530462 1532287 := bstep (se 1 (by rfl) ⟨1149215, by rfl⟩ : syracuseStep 1532287 = 2298431) B2298431
theorem B1532367 : Blo 1530462 1532367 := bstep (se 1 (by rfl) ⟨1149275, by rfl⟩ : syracuseStep 1532367 = 2298551) B2298551
theorem B2908649 : Blo 1530462 2908649 := bstep (se 2 (by rfl) ⟨1090743, by rfl⟩ : syracuseStep 2908649 = 2181487) B2181487
theorem B8283161 : Blo 1530462 8283161 := bstep (se 2 (by rfl) ⟨3106185, by rfl⟩ : syracuseStep 8283161 = 6212371) B6212371
theorem B20964395 : Blo 1530462 20964395 := bstep (se 1 (by rfl) ⟨15723296, by rfl⟩ : syracuseStep 20964395 = 31446593) B31446593
theorem B22086755 : Blo 1530462 22086755 := bstep (se 1 (by rfl) ⟨16565066, by rfl⟩ : syracuseStep 22086755 = 33130133) B33130133
theorem B11043985 : Blo 1530462 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B11183293 : Blo 1530462 11183293 := bstep (se 3 (by rfl) ⟨2096867, by rfl⟩ : syracuseStep 11183293 = 4193735) B4193735
theorem B10479023 : Blo 1530462 10479023 := bstep (se 1 (by rfl) ⟨7859267, by rfl⟩ : syracuseStep 10479023 = 15718535) B15718535
theorem B5170607 : Blo 1530462 5170607 := bstep (se 1 (by rfl) ⟨3877955, by rfl⟩ : syracuseStep 5170607 = 7755911) B7755911
theorem B5817815 : Blo 1530462 5817815 := bstep (se 1 (by rfl) ⟨4363361, by rfl⟩ : syracuseStep 5817815 = 8726723) B8726723
theorem B4359899 : Blo 1530462 4359899 := bstep (se 1 (by rfl) ⟨3269924, by rfl⟩ : syracuseStep 4359899 = 6539849) B6539849
theorem B9815849 : Blo 1530462 9815849 := bstep (se 2 (by rfl) ⟨3680943, by rfl⟩ : syracuseStep 9815849 = 7361887) B7361887
theorem B5170985 : Blo 1530462 5170985 := bstep (se 2 (by rfl) ⟨1939119, by rfl⟩ : syracuseStep 5170985 = 3878239) B3878239
theorem B11036513 : Blo 1530462 11036513 := bstep (se 2 (by rfl) ⟨4138692, by rfl⟩ : syracuseStep 11036513 = 8277385) B8277385
theorem B23578543 : Blo 1530462 23578543 := bstep (se 1 (by rfl) ⟨17683907, by rfl⟩ : syracuseStep 23578543 = 35367815) B35367815
theorem B2295791 : Blo 1530462 2295791 := bstep (se 1 (by rfl) ⟨1721843, by rfl⟩ : syracuseStep 2295791 = 3443687) B3443687
theorem B99362861 : Blo 1530462 99362861 := bstep (se 3 (by rfl) ⟨18630536, by rfl⟩ : syracuseStep 99362861 = 37261073) B37261073
theorem B2582671 : Blo 1530462 2582671 := bstep (se 1 (by rfl) ⟨1937003, by rfl⟩ : syracuseStep 2582671 = 3874007) B3874007
theorem B6465689 : Blo 1530462 6465689 := bstep (se 2 (by rfl) ⟨2424633, by rfl⟩ : syracuseStep 6465689 = 4849267) B4849267
theorem B1722523 : Blo 1530462 1722523 := bstep (se 1 (by rfl) ⟨1291892, by rfl⟩ : syracuseStep 1722523 = 2583785) B2583785
theorem B1722559 : Blo 1530462 1722559 := bstep (se 1 (by rfl) ⟨1291919, by rfl⟩ : syracuseStep 1722559 = 2583839) B2583839
theorem B3877055 : Blo 1530462 3877055 := bstep (se 1 (by rfl) ⟨2907791, by rfl⟩ : syracuseStep 3877055 = 5815583) B5815583
theorem B2296043 : Blo 1530462 2296043 := bstep (se 1 (by rfl) ⟨1722032, by rfl⟩ : syracuseStep 2296043 = 3444065) B3444065
theorem B3680491 : Blo 1530462 3680491 := bstep (se 1 (by rfl) ⟨2760368, by rfl⟩ : syracuseStep 3680491 = 5520737) B5520737
theorem B2296103 : Blo 1530462 2296103 := bstep (se 1 (by rfl) ⟨1722077, by rfl⟩ : syracuseStep 2296103 = 3444155) B3444155
theorem B2296187 : Blo 1530462 2296187 := bstep (se 1 (by rfl) ⟨1722140, by rfl⟩ : syracuseStep 2296187 = 3444281) B3444281
theorem B19614109 : Blo 1530462 19614109 := bstep (se 3 (by rfl) ⟨3677645, by rfl⟩ : syracuseStep 19614109 = 7355291) B7355291
theorem B8718749 : Blo 1530462 8718749 := bstep (se 3 (by rfl) ⟨1634765, by rfl⟩ : syracuseStep 8718749 = 3269531) B3269531
theorem B8727041 : Blo 1530462 8727041 := bstep (se 2 (by rfl) ⟨3272640, by rfl⟩ : syracuseStep 8727041 = 6545281) B6545281
theorem B2296457 : Blo 1530462 2296457 := bstep (se 2 (by rfl) ⟨861171, by rfl⟩ : syracuseStep 2296457 = 1722343) B1722343
theorem B10472075 : Blo 1530462 10472075 := bstep (se 1 (by rfl) ⟨7854056, by rfl⟩ : syracuseStep 10472075 = 15708113) B15708113
theorem B8276651 : Blo 1530462 8276651 := bstep (se 1 (by rfl) ⟨6207488, by rfl⟩ : syracuseStep 8276651 = 12414977) B12414977
theorem B17443511 : Blo 1530462 17443511 := bstep (se 1 (by rfl) ⟨13082633, by rfl⟩ : syracuseStep 17443511 = 26165267) B26165267
theorem B8727223 : Blo 1530462 8727223 := bstep (se 1 (by rfl) ⟨6545417, by rfl⟩ : syracuseStep 8727223 = 13090835) B13090835
theorem B11037379 : Blo 1530462 11037379 := bstep (se 1 (by rfl) ⟨8278034, by rfl⟩ : syracuseStep 11037379 = 16556069) B16556069
theorem B2296631 : Blo 1530462 2296631 := bstep (se 1 (by rfl) ⟨1722473, by rfl⟩ : syracuseStep 2296631 = 3444947) B3444947
theorem B4361015 : Blo 1530462 4361015 := bstep (se 1 (by rfl) ⟨3270761, by rfl⟩ : syracuseStep 4361015 = 6541523) B6541523
theorem B2296667 : Blo 1530462 2296667 := bstep (se 1 (by rfl) ⟨1722500, by rfl⟩ : syracuseStep 2296667 = 3445001) B3445001
theorem B2296811 : Blo 1530462 2296811 := bstep (se 1 (by rfl) ⟨1722608, by rfl⟩ : syracuseStep 2296811 = 3445217) B3445217
theorem B3443759 : Blo 1530462 3443759 := bstep (se 1 (by rfl) ⟨2582819, by rfl⟩ : syracuseStep 3443759 = 5165639) B5165639
theorem B2583623 : Blo 1530462 2583623 := bstep (se 1 (by rfl) ⟨1937717, by rfl⟩ : syracuseStep 2583623 = 3875435) B3875435
theorem B2297015 : Blo 1530462 2297015 := bstep (se 1 (by rfl) ⟨1722761, by rfl⟩ : syracuseStep 2297015 = 3445523) B3445523
theorem B39234779 : Blo 1530462 39234779 := bstep (se 1 (by rfl) ⟨29426084, by rfl⟩ : syracuseStep 39234779 = 58852169) B58852169
theorem B3444047 : Blo 1530462 3444047 := bstep (se 1 (by rfl) ⟨2583035, by rfl⟩ : syracuseStep 3444047 = 5166071) B5166071
theorem B2297255 : Blo 1530462 2297255 := bstep (se 1 (by rfl) ⟨1722941, by rfl⟩ : syracuseStep 2297255 = 3445883) B3445883
theorem B3444137 : Blo 1530462 3444137 := bstep (se 2 (by rfl) ⟨1291551, by rfl⟩ : syracuseStep 3444137 = 2583103) B2583103
theorem B6983081 : Blo 1530462 6983081 := bstep (se 2 (by rfl) ⟨2618655, by rfl⟩ : syracuseStep 6983081 = 5237311) B5237311
theorem B2584055 : Blo 1530462 2584055 := bstep (se 1 (by rfl) ⟨1938041, by rfl⟩ : syracuseStep 2584055 = 3876083) B3876083
theorem B2297339 : Blo 1530462 2297339 := bstep (se 1 (by rfl) ⟨1723004, by rfl⟩ : syracuseStep 2297339 = 3446009) B3446009
theorem B17436221 : Blo 1530462 17436221 := bstep (se 3 (by rfl) ⟨3269291, by rfl⟩ : syracuseStep 17436221 = 6538583) B6538583
theorem B3493439 : Blo 1530462 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B9940553 : Blo 1530462 9940553 := bstep (se 2 (by rfl) ⟨3727707, by rfl⟩ : syracuseStep 9940553 = 7455415) B7455415
theorem B2297435 : Blo 1530462 2297435 := bstep (se 1 (by rfl) ⟨1723076, by rfl⟩ : syracuseStep 2297435 = 3446153) B3446153
theorem B6540907 : Blo 1530462 6540907 := bstep (se 1 (by rfl) ⟨4905680, by rfl⟩ : syracuseStep 6540907 = 9811361) B9811361
theorem B2297519 : Blo 1530462 2297519 := bstep (se 1 (by rfl) ⟨1723139, by rfl⟩ : syracuseStep 2297519 = 3446279) B3446279
theorem B3878675 : Blo 1530462 3878675 := bstep (se 1 (by rfl) ⟨2909006, by rfl⟩ : syracuseStep 3878675 = 5818013) B5818013
theorem B1937191 : Blo 1530462 1937191 := bstep (se 1 (by rfl) ⟨1452893, by rfl⟩ : syracuseStep 1937191 = 2905787) B2905787
theorem B2297639 : Blo 1530462 2297639 := bstep (se 1 (by rfl) ⟨1723229, by rfl⟩ : syracuseStep 2297639 = 3446459) B3446459
theorem B5517161 : Blo 1530462 5517161 := bstep (se 2 (by rfl) ⟨2068935, by rfl⟩ : syracuseStep 5517161 = 4137871) B4137871
theorem B2297723 : Blo 1530462 2297723 := bstep (se 1 (by rfl) ⟨1723292, by rfl⟩ : syracuseStep 2297723 = 3446585) B3446585
theorem B3444623 : Blo 1530462 3444623 := bstep (se 1 (by rfl) ⟨2583467, by rfl⟩ : syracuseStep 3444623 = 5166935) B5166935
theorem B4362427 : Blo 1530462 4362427 := bstep (se 1 (by rfl) ⟨3271820, by rfl⟩ : syracuseStep 4362427 = 6543641) B6543641
theorem B12415169 : Blo 1530462 12415169 := bstep (se 2 (by rfl) ⟨4655688, by rfl⟩ : syracuseStep 12415169 = 9311377) B9311377
theorem B9818333 : Blo 1530462 9818333 := bstep (se 3 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 9818333 = 3681875) B3681875
theorem B2298143 : Blo 1530462 2298143 := bstep (se 1 (by rfl) ⟨1723607, by rfl⟩ : syracuseStep 2298143 = 3447215) B3447215
theorem B2298167 : Blo 1530462 2298167 := bstep (se 1 (by rfl) ⟨1723625, by rfl⟩ : syracuseStep 2298167 = 3447251) B3447251
theorem B5165423 : Blo 1530462 5165423 := bstep (se 1 (by rfl) ⟨3874067, by rfl⟩ : syracuseStep 5165423 = 7748135) B7748135
theorem B2298239 : Blo 1530462 2298239 := bstep (se 1 (by rfl) ⟨1723679, by rfl⟩ : syracuseStep 2298239 = 3447359) B3447359
theorem B2298311 : Blo 1530462 2298311 := bstep (se 1 (by rfl) ⟨1723733, by rfl⟩ : syracuseStep 2298311 = 3447467) B3447467
theorem B2585081 : Blo 1530462 2585081 := bstep (se 2 (by rfl) ⟨969405, by rfl⟩ : syracuseStep 2585081 = 1938811) B1938811
theorem B3445343 : Blo 1530462 3445343 := bstep (se 1 (by rfl) ⟨2584007, by rfl⟩ : syracuseStep 3445343 = 5168015) B5168015
theorem B6541985 : Blo 1530462 6541985 := bstep (se 2 (by rfl) ⟨2453244, by rfl⟩ : syracuseStep 6541985 = 4906489) B4906489
theorem B2585351 : Blo 1530462 2585351 := bstep (se 1 (by rfl) ⟨1939013, by rfl⟩ : syracuseStep 2585351 = 3878027) B3878027
theorem B2298665 : Blo 1530462 2298665 := bstep (se 2 (by rfl) ⟨861999, by rfl⟩ : syracuseStep 2298665 = 1723999) B1723999
theorem B2298671 : Blo 1530462 2298671 := bstep (se 1 (by rfl) ⟨1724003, by rfl⟩ : syracuseStep 2298671 = 3448007) B3448007
theorem B3929143 : Blo 1530462 3929143 := bstep (se 1 (by rfl) ⟨2946857, by rfl⟩ : syracuseStep 3929143 = 5893715) B5893715
theorem B1938487 : Blo 1530462 1938487 := bstep (se 1 (by rfl) ⟨1453865, by rfl⟩ : syracuseStep 1938487 = 2907731) B2907731
theorem B4142153 : Blo 1530462 4142153 := bstep (se 2 (by rfl) ⟨1553307, by rfl⟩ : syracuseStep 4142153 = 3106615) B3106615
theorem B4420747 : Blo 1530462 4420747 := bstep (se 1 (by rfl) ⟨3315560, by rfl⟩ : syracuseStep 4420747 = 6631121) B6631121
theorem B3446171 : Blo 1530462 3446171 := bstep (se 1 (by rfl) ⟨2584628, by rfl⟩ : syracuseStep 3446171 = 5169257) B5169257
theorem B6813193 : Blo 1530462 6813193 := bstep (se 2 (by rfl) ⟨2554947, by rfl⟩ : syracuseStep 6813193 = 5109895) B5109895
theorem B24843833 : Blo 1530462 24843833 := bstep (se 2 (by rfl) ⟨9316437, by rfl⟩ : syracuseStep 24843833 = 18632875) B18632875
theorem B6542957 : Blo 1530462 6542957 := bstep (se 3 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 6542957 = 2453609) B2453609
theorem B5166827 : Blo 1530462 5166827 := bstep (se 1 (by rfl) ⟨3875120, by rfl⟩ : syracuseStep 5166827 = 7750241) B7750241
theorem B1939231 : Blo 1530462 1939231 := bstep (se 1 (by rfl) ⟨1454423, by rfl⟩ : syracuseStep 1939231 = 2908847) B2908847
theorem B22091707 : Blo 1530462 22091707 := bstep (se 1 (by rfl) ⟨16568780, by rfl⟩ : syracuseStep 22091707 = 33137561) B33137561
theorem B3446747 : Blo 1530462 3446747 := bstep (se 1 (by rfl) ⟨2585060, by rfl⟩ : syracuseStep 3446747 = 5170121) B5170121
theorem B2758639 : Blo 1530462 2758639 := bstep (se 1 (by rfl) ⟨2068979, by rfl⟩ : syracuseStep 2758639 = 4137959) B4137959
theorem B5167097 : Blo 1530462 5167097 := bstep (se 2 (by rfl) ⟨1937661, by rfl⟩ : syracuseStep 5167097 = 3875323) B3875323
theorem B5519353 : Blo 1530462 5519353 := bstep (se 2 (by rfl) ⟨2069757, by rfl⟩ : syracuseStep 5519353 = 4139515) B4139515
theorem B4970521 : Blo 1530462 4970521 := bstep (se 2 (by rfl) ⟨1863945, by rfl⟩ : syracuseStep 4970521 = 3727891) B3727891
theorem B3446927 : Blo 1530462 3446927 := bstep (se 1 (by rfl) ⟨2585195, by rfl⟩ : syracuseStep 3446927 = 5170391) B5170391
theorem B5167259 : Blo 1530462 5167259 := bstep (se 1 (by rfl) ⟨3875444, by rfl⟩ : syracuseStep 5167259 = 7750889) B7750889
theorem B2906273 : Blo 1530462 2906273 := bstep (se 2 (by rfl) ⟨1089852, by rfl⟩ : syracuseStep 2906273 = 2179705) B2179705
theorem B3446945 : Blo 1530462 3446945 := bstep (se 2 (by rfl) ⟨1292604, by rfl⟩ : syracuseStep 3446945 = 2585209) B2585209
theorem B7354601 : Blo 1530462 7354601 := bstep (se 2 (by rfl) ⟨2757975, by rfl⟩ : syracuseStep 7354601 = 5515951) B5515951
theorem B3447017 : Blo 1530462 3447017 := bstep (se 2 (by rfl) ⟨1292631, by rfl⟩ : syracuseStep 3447017 = 2585263) B2585263
theorem B5167367 : Blo 1530462 5167367 := bstep (se 1 (by rfl) ⟨3875525, by rfl⟩ : syracuseStep 5167367 = 7751051) B7751051
theorem B7756073 : Blo 1530462 7756073 := bstep (se 2 (by rfl) ⟨2908527, by rfl⟩ : syracuseStep 7756073 = 5817055) B5817055
theorem B4905323 : Blo 1530462 4905323 := bstep (se 1 (by rfl) ⟨3678992, by rfl⟩ : syracuseStep 4905323 = 7357985) B7357985
theorem B5519929 : Blo 1530462 5519929 := bstep (se 2 (by rfl) ⟨2069973, by rfl⟩ : syracuseStep 5519929 = 4139947) B4139947
theorem B2759273 : Blo 1530462 2759273 := bstep (se 2 (by rfl) ⟨1034727, by rfl⟩ : syracuseStep 2759273 = 2069455) B2069455
theorem B7355215 : Blo 1530462 7355215 := bstep (se 1 (by rfl) ⟨5516411, by rfl⟩ : syracuseStep 7355215 = 11032823) B11032823
theorem B1530715 : Blo 1530462 1530715 := bstep (se 1 (by rfl) ⟨1148036, by rfl⟩ : syracuseStep 1530715 = 2296073) B2296073
theorem B20945789 : Blo 1530462 20945789 := bstep (se 3 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 20945789 = 7854671) B7854671
theorem B1530783 : Blo 1530462 1530783 := bstep (se 1 (by rfl) ⟨1148087, by rfl⟩ : syracuseStep 1530783 = 2296175) B2296175
theorem B24837029 : Blo 1530462 24837029 := bstep (se 4 (by rfl) ⟨2328471, by rfl⟩ : syracuseStep 24837029 = 4656943) B4656943
theorem B1530927 : Blo 1530462 1530927 := bstep (se 1 (by rfl) ⟨1148195, by rfl⟩ : syracuseStep 1530927 = 2296391) B2296391
theorem B1530951 : Blo 1530462 1530951 := bstep (se 1 (by rfl) ⟨1148213, by rfl⟩ : syracuseStep 1530951 = 2296427) B2296427
theorem B1531103 : Blo 1530462 1531103 := bstep (se 1 (by rfl) ⟨1148327, by rfl⟩ : syracuseStep 1531103 = 2296655) B2296655
theorem B5168393 : Blo 1530462 5168393 := bstep (se 2 (by rfl) ⟨1938147, by rfl⟩ : syracuseStep 5168393 = 3876295) B3876295
theorem B58891535 : Blo 1530462 58891535 := bstep (se 1 (by rfl) ⟨44168651, by rfl⟩ : syracuseStep 58891535 = 88337303) B88337303
theorem B7863581 : Blo 1530462 7863581 := bstep (se 3 (by rfl) ⟨1474421, by rfl⟩ : syracuseStep 7863581 = 2948843) B2948843
theorem B8723807 : Blo 1530462 8723807 := bstep (se 1 (by rfl) ⟨6542855, by rfl⟩ : syracuseStep 8723807 = 13085711) B13085711
theorem B2833831 : Blo 1530462 2833831 := bstep (se 1 (by rfl) ⟨2125373, by rfl⟩ : syracuseStep 2833831 = 4250747) B4250747
theorem B13082087 : Blo 1530462 13082087 := bstep (se 1 (by rfl) ⟨9811565, by rfl⟩ : syracuseStep 13082087 = 19623131) B19623131
theorem B1531367 : Blo 1530462 1531367 := bstep (se 1 (by rfl) ⟨1148525, by rfl⟩ : syracuseStep 1531367 = 2297051) B2297051
theorem B6544871 : Blo 1530462 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B1531483 : Blo 1530462 1531483 := bstep (se 1 (by rfl) ⟨1148612, by rfl⟩ : syracuseStep 1531483 = 2297225) B2297225
theorem B8281885 : Blo 1530462 8281885 := bstep (se 3 (by rfl) ⟨1552853, by rfl⟩ : syracuseStep 8281885 = 3105707) B3105707
theorem B1531719 : Blo 1530462 1531719 := bstep (se 1 (by rfl) ⟨1148789, by rfl⟩ : syracuseStep 1531719 = 2297579) B2297579
theorem B1531871 : Blo 1530462 1531871 := bstep (se 1 (by rfl) ⟨1148903, by rfl⟩ : syracuseStep 1531871 = 2297807) B2297807
theorem B6627361 : Blo 1530462 6627361 := bstep (se 2 (by rfl) ⟨2485260, by rfl⟩ : syracuseStep 6627361 = 4970521) B4970521
theorem B6545555 : Blo 1530462 6545555 := bstep (se 1 (by rfl) ⟨4909166, by rfl⟩ : syracuseStep 6545555 = 9818333) B9818333
theorem B1532095 : Blo 1530462 1532095 := bstep (se 1 (by rfl) ⟨1149071, by rfl⟩ : syracuseStep 1532095 = 2298143) B2298143
theorem B1532111 : Blo 1530462 1532111 := bstep (se 1 (by rfl) ⟨1149083, by rfl⟩ : syracuseStep 1532111 = 2298167) B2298167
theorem B5816555 : Blo 1530462 5816555 := bstep (se 1 (by rfl) ⟨4362416, by rfl⟩ : syracuseStep 5816555 = 8724833) B8724833
theorem B5816569 : Blo 1530462 5816569 := bstep (se 2 (by rfl) ⟨2181213, by rfl⟩ : syracuseStep 5816569 = 4362427) B4362427
theorem B1532159 : Blo 1530462 1532159 := bstep (se 1 (by rfl) ⟨1149119, by rfl⟩ : syracuseStep 1532159 = 2298239) B2298239
theorem B1532207 : Blo 1530462 1532207 := bstep (se 1 (by rfl) ⟨1149155, by rfl⟩ : syracuseStep 1532207 = 2298311) B2298311
theorem B4907321 : Blo 1530462 4907321 := bstep (se 2 (by rfl) ⟨1840245, by rfl⟩ : syracuseStep 4907321 = 3680491) B3680491
theorem B1532443 : Blo 1530462 1532443 := bstep (se 1 (by rfl) ⟨1149332, by rfl⟩ : syracuseStep 1532443 = 2298665) B2298665
theorem B1532447 : Blo 1530462 1532447 := bstep (se 1 (by rfl) ⟨1149335, by rfl⟩ : syracuseStep 1532447 = 2298671) B2298671
theorem B5522107 : Blo 1530462 5522107 := bstep (se 1 (by rfl) ⟨4141580, by rfl⟩ : syracuseStep 5522107 = 8283161) B8283161
theorem B13976263 : Blo 1530462 13976263 := bstep (se 1 (by rfl) ⟨10482197, by rfl⟩ : syracuseStep 13976263 = 20964395) B20964395
theorem B2761435 : Blo 1530462 2761435 := bstep (se 1 (by rfl) ⟨2071076, by rfl⟩ : syracuseStep 2761435 = 4142153) B4142153
theorem B9806953 : Blo 1530462 9806953 := bstep (se 2 (by rfl) ⟨3677607, by rfl⟩ : syracuseStep 9806953 = 7355215) B7355215
theorem B66241907 : Blo 1530462 66241907 := bstep (se 1 (by rfl) ⟨49681430, by rfl⟩ : syracuseStep 66241907 = 99362861) B99362861
theorem B4310459 : Blo 1530462 4310459 := bstep (se 1 (by rfl) ⟨3232844, by rfl⟩ : syracuseStep 4310459 = 6465689) B6465689
theorem B5170715 : Blo 1530462 5170715 := bstep (se 1 (by rfl) ⟨3878036, by rfl⟩ : syracuseStep 5170715 = 7756073) B7756073
theorem B3270215 : Blo 1530462 3270215 := bstep (se 1 (by rfl) ⟨2452661, by rfl⟩ : syracuseStep 3270215 = 4905323) B4905323
theorem B14911057 : Blo 1530462 14911057 := bstep (se 2 (by rfl) ⟨5591646, by rfl⟩ : syracuseStep 14911057 = 11183293) B11183293
theorem B5818027 : Blo 1530462 5818027 := bstep (se 1 (by rfl) ⟨4363520, by rfl⟩ : syracuseStep 5818027 = 8727041) B8727041
theorem B6981383 : Blo 1530462 6981383 := bstep (se 1 (by rfl) ⟨5236037, by rfl⟩ : syracuseStep 6981383 = 10472075) B10472075
theorem B16558019 : Blo 1530462 16558019 := bstep (se 1 (by rfl) ⟨12418514, by rfl⟩ : syracuseStep 16558019 = 24837029) B24837029
theorem B2295839 : Blo 1530462 2295839 := bstep (se 1 (by rfl) ⟨1721879, by rfl⟩ : syracuseStep 2295839 = 3443759) B3443759
theorem B1722415 : Blo 1530462 1722415 := bstep (se 1 (by rfl) ⟨1291811, by rfl⟩ : syracuseStep 1722415 = 2583623) B2583623
theorem B2296031 : Blo 1530462 2296031 := bstep (se 1 (by rfl) ⟨1722023, by rfl⟩ : syracuseStep 2296031 = 3444047) B3444047
theorem B2296091 : Blo 1530462 2296091 := bstep (se 1 (by rfl) ⟨1722068, by rfl⟩ : syracuseStep 2296091 = 3444137) B3444137
theorem B4655387 : Blo 1530462 4655387 := bstep (se 1 (by rfl) ⟨3491540, by rfl⟩ : syracuseStep 4655387 = 6983081) B6983081
theorem B1722703 : Blo 1530462 1722703 := bstep (se 1 (by rfl) ⟨1292027, by rfl⟩ : syracuseStep 1722703 = 2584055) B2584055
theorem B2328959 : Blo 1530462 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B2582921 : Blo 1530462 2582921 := bstep (se 2 (by rfl) ⟨968595, by rfl⟩ : syracuseStep 2582921 = 1937191) B1937191
theorem B2296415 : Blo 1530462 2296415 := bstep (se 1 (by rfl) ⟨1722311, by rfl⟩ : syracuseStep 2296415 = 3444623) B3444623
theorem B7359137 : Blo 1530462 7359137 := bstep (se 2 (by rfl) ⟨2759676, by rfl⟩ : syracuseStep 7359137 = 5519353) B5519353
theorem B8276779 : Blo 1530462 8276779 := bstep (se 1 (by rfl) ⟨6207584, by rfl⟩ : syracuseStep 8276779 = 12415169) B12415169
theorem B3443561 : Blo 1530462 3443561 := bstep (se 2 (by rfl) ⟨1291335, by rfl⟩ : syracuseStep 3443561 = 2582671) B2582671
theorem B2296697 : Blo 1530462 2296697 := bstep (se 2 (by rfl) ⟨861261, by rfl⟩ : syracuseStep 2296697 = 1722523) B1722523
theorem B3443615 : Blo 1530462 3443615 := bstep (se 1 (by rfl) ⟨2582711, by rfl⟩ : syracuseStep 3443615 = 5165423) B5165423
theorem B2296745 : Blo 1530462 2296745 := bstep (se 2 (by rfl) ⟨861279, by rfl⟩ : syracuseStep 2296745 = 1722559) B1722559
theorem B1723387 : Blo 1530462 1723387 := bstep (se 1 (by rfl) ⟨1292540, by rfl⟩ : syracuseStep 1723387 = 2585081) B2585081
theorem B2296895 : Blo 1530462 2296895 := bstep (se 1 (by rfl) ⟨1722671, by rfl⟩ : syracuseStep 2296895 = 3445343) B3445343
theorem B4361323 : Blo 1530462 4361323 := bstep (se 1 (by rfl) ⟨3270992, by rfl⟩ : syracuseStep 4361323 = 6541985) B6541985
theorem B1723567 : Blo 1530462 1723567 := bstep (se 1 (by rfl) ⟨1292675, by rfl⟩ : syracuseStep 1723567 = 2585351) B2585351
theorem B26152145 : Blo 1530462 26152145 := bstep (se 2 (by rfl) ⟨9807054, by rfl⟩ : syracuseStep 26152145 = 19614109) B19614109
theorem B14724503 : Blo 1530462 14724503 := bstep (se 1 (by rfl) ⟨11043377, by rfl⟩ : syracuseStep 14724503 = 22086755) B22086755
theorem B7359905 : Blo 1530462 7359905 := bstep (se 2 (by rfl) ⟨2759964, by rfl⟩ : syracuseStep 7359905 = 5519929) B5519929
theorem B11636297 : Blo 1530462 11636297 := bstep (se 2 (by rfl) ⟨4363611, by rfl⟩ : syracuseStep 11636297 = 8727223) B8727223
theorem B14716505 : Blo 1530462 14716505 := bstep (se 2 (by rfl) ⟨5518689, by rfl⟩ : syracuseStep 14716505 = 11037379) B11037379
theorem B2297447 : Blo 1530462 2297447 := bstep (se 1 (by rfl) ⟨1723085, by rfl⟩ : syracuseStep 2297447 = 3446171) B3446171
theorem B3878543 : Blo 1530462 3878543 := bstep (se 1 (by rfl) ⟨2908907, by rfl⟩ : syracuseStep 3878543 = 5817815) B5817815
theorem B3444551 : Blo 1530462 3444551 := bstep (se 1 (by rfl) ⟨2583413, by rfl⟩ : syracuseStep 3444551 = 5166827) B5166827
theorem B2297831 : Blo 1530462 2297831 := bstep (se 1 (by rfl) ⟨1723373, by rfl⟩ : syracuseStep 2297831 = 3446747) B3446747
theorem B3444731 : Blo 1530462 3444731 := bstep (se 1 (by rfl) ⟨2583548, by rfl⟩ : syracuseStep 3444731 = 5167097) B5167097
theorem B5238857 : Blo 1530462 5238857 := bstep (se 2 (by rfl) ⟨1964571, by rfl⟩ : syracuseStep 5238857 = 3929143) B3929143
theorem B2584649 : Blo 1530462 2584649 := bstep (se 2 (by rfl) ⟨969243, by rfl⟩ : syracuseStep 2584649 = 1938487) B1938487
theorem B2297951 : Blo 1530462 2297951 := bstep (se 1 (by rfl) ⟨1723463, by rfl⟩ : syracuseStep 2297951 = 3446927) B3446927
theorem B3444839 : Blo 1530462 3444839 := bstep (se 1 (by rfl) ⟨2583629, by rfl⟩ : syracuseStep 3444839 = 5167259) B5167259
theorem B1937515 : Blo 1530462 1937515 := bstep (se 1 (by rfl) ⟨1453136, by rfl⟩ : syracuseStep 1937515 = 2906273) B2906273
theorem B2297963 : Blo 1530462 2297963 := bstep (se 1 (by rfl) ⟨1723472, by rfl⟩ : syracuseStep 2297963 = 3446945) B3446945
theorem B2584703 : Blo 1530462 2584703 := bstep (se 1 (by rfl) ⟨1938527, by rfl⟩ : syracuseStep 2584703 = 3877055) B3877055
theorem B4903067 : Blo 1530462 4903067 := bstep (se 1 (by rfl) ⟨3677300, by rfl⟩ : syracuseStep 4903067 = 7354601) B7354601
theorem B2298011 : Blo 1530462 2298011 := bstep (se 1 (by rfl) ⟨1723508, by rfl⟩ : syracuseStep 2298011 = 3447017) B3447017
theorem B3444911 : Blo 1530462 3444911 := bstep (se 1 (by rfl) ⟨2583683, by rfl⟩ : syracuseStep 3444911 = 5167367) B5167367
theorem B5894329 : Blo 1530462 5894329 := bstep (se 2 (by rfl) ⟨2210373, by rfl⟩ : syracuseStep 5894329 = 4420747) B4420747
theorem B14725313 : Blo 1530462 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B5812499 : Blo 1530462 5812499 := bstep (se 1 (by rfl) ⟨4359374, by rfl⟩ : syracuseStep 5812499 = 8718749) B8718749
theorem B1839515 : Blo 1530462 1839515 := bstep (se 1 (by rfl) ⟨1379636, by rfl⟩ : syracuseStep 1839515 = 2759273) B2759273
theorem B5517767 : Blo 1530462 5517767 := bstep (se 1 (by rfl) ⟨4138325, by rfl⟩ : syracuseStep 5517767 = 8276651) B8276651
theorem B11629007 : Blo 1530462 11629007 := bstep (se 1 (by rfl) ⟨8721755, by rfl⟩ : syracuseStep 11629007 = 17443511) B17443511
theorem B13963859 : Blo 1530462 13963859 := bstep (se 1 (by rfl) ⟨10472894, by rfl⟩ : syracuseStep 13963859 = 20945789) B20945789
theorem B8721209 : Blo 1530462 8721209 := bstep (se 2 (by rfl) ⟨3270453, by rfl⟩ : syracuseStep 8721209 = 6540907) B6540907
theorem B3445595 : Blo 1530462 3445595 := bstep (se 1 (by rfl) ⟨2584196, by rfl⟩ : syracuseStep 3445595 = 5168393) B5168393
theorem B39261023 : Blo 1530462 39261023 := bstep (se 1 (by rfl) ⟨29445767, by rfl⟩ : syracuseStep 39261023 = 58891535) B58891535
theorem B29430701 : Blo 1530462 29430701 := bstep (se 3 (by rfl) ⟨5518256, by rfl⟩ : syracuseStep 29430701 = 11036513) B11036513
theorem B8721391 : Blo 1530462 8721391 := bstep (se 1 (by rfl) ⟨6541043, by rfl⟩ : syracuseStep 8721391 = 13082087) B13082087
theorem B4363247 : Blo 1530462 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B2585641 : Blo 1530462 2585641 := bstep (se 2 (by rfl) ⟨969615, by rfl⟩ : syracuseStep 2585641 = 1939231) B1939231
theorem B2585783 : Blo 1530462 2585783 := bstep (se 1 (by rfl) ⟨1939337, by rfl⟩ : syracuseStep 2585783 = 3878675) B3878675
theorem B31438057 : Blo 1530462 31438057 := bstep (se 2 (by rfl) ⟨11789271, by rfl⟩ : syracuseStep 31438057 = 23578543) B23578543
theorem B29455609 : Blo 1530462 29455609 := bstep (se 2 (by rfl) ⟨11045853, by rfl⟩ : syracuseStep 29455609 = 22091707) B22091707
theorem B3446351 : Blo 1530462 3446351 := bstep (se 1 (by rfl) ⟨2584763, by rfl⟩ : syracuseStep 3446351 = 5169527) B5169527
theorem B20969549 : Blo 1530462 20969549 := bstep (se 3 (by rfl) ⟨3931790, by rfl⟩ : syracuseStep 20969549 = 7863581) B7863581
theorem B6986015 : Blo 1530462 6986015 := bstep (se 1 (by rfl) ⟨5239511, by rfl⟩ : syracuseStep 6986015 = 10479023) B10479023
theorem B3447071 : Blo 1530462 3447071 := bstep (se 1 (by rfl) ⟨2585303, by rfl⟩ : syracuseStep 3447071 = 5170607) B5170607
theorem B16562555 : Blo 1530462 16562555 := bstep (se 1 (by rfl) ⟨12421916, by rfl⟩ : syracuseStep 16562555 = 24843833) B24843833
theorem B2906599 : Blo 1530462 2906599 := bstep (se 1 (by rfl) ⟨2179949, by rfl⟩ : syracuseStep 2906599 = 4359899) B4359899
theorem B6543899 : Blo 1530462 6543899 := bstep (se 1 (by rfl) ⟨4907924, by rfl⟩ : syracuseStep 6543899 = 9815849) B9815849
theorem B3447323 : Blo 1530462 3447323 := bstep (se 1 (by rfl) ⟨2585492, by rfl⟩ : syracuseStep 3447323 = 5170985) B5170985
theorem B7756397 : Blo 1530462 7756397 := bstep (se 3 (by rfl) ⟨1454324, by rfl⟩ : syracuseStep 7756397 = 2908649) B2908649
theorem B1530527 : Blo 1530462 1530527 := bstep (se 1 (by rfl) ⟨1147895, by rfl⟩ : syracuseStep 1530527 = 2295791) B2295791
theorem B1530695 : Blo 1530462 1530695 := bstep (se 1 (by rfl) ⟨1148021, by rfl⟩ : syracuseStep 1530695 = 2296043) B2296043
theorem B1530735 : Blo 1530462 1530735 := bstep (se 1 (by rfl) ⟨1148051, by rfl⟩ : syracuseStep 1530735 = 2296103) B2296103
theorem B1530791 : Blo 1530462 1530791 := bstep (se 1 (by rfl) ⟨1148093, by rfl⟩ : syracuseStep 1530791 = 2296187) B2296187
theorem B17447885 : Blo 1530462 17447885 := bstep (se 3 (by rfl) ⟨3271478, by rfl⟩ : syracuseStep 17447885 = 6542957) B6542957
theorem B1530971 : Blo 1530462 1530971 := bstep (se 1 (by rfl) ⟨1148228, by rfl⟩ : syracuseStep 1530971 = 2296457) B2296457
theorem B1531087 : Blo 1530462 1531087 := bstep (se 1 (by rfl) ⟨1148315, by rfl⟩ : syracuseStep 1531087 = 2296631) B2296631
theorem B2907343 : Blo 1530462 2907343 := bstep (se 1 (by rfl) ⟨2180507, by rfl⟩ : syracuseStep 2907343 = 4361015) B4361015
theorem B1531111 : Blo 1530462 1531111 := bstep (se 1 (by rfl) ⟨1148333, by rfl⟩ : syracuseStep 1531111 = 2296667) B2296667
theorem B1531207 : Blo 1530462 1531207 := bstep (se 1 (by rfl) ⟨1148405, by rfl⟩ : syracuseStep 1531207 = 2296811) B2296811
theorem B9084257 : Blo 1530462 9084257 := bstep (se 2 (by rfl) ⟨3406596, by rfl⟩ : syracuseStep 9084257 = 6813193) B6813193
theorem B1531343 : Blo 1530462 1531343 := bstep (se 1 (by rfl) ⟨1148507, by rfl⟩ : syracuseStep 1531343 = 2297015) B2297015
theorem B26156519 : Blo 1530462 26156519 := bstep (se 1 (by rfl) ⟨19617389, by rfl⟩ : syracuseStep 26156519 = 39234779) B39234779
theorem B15113765 : Blo 1530462 15113765 := bstep (se 4 (by rfl) ⟨1416915, by rfl⟩ : syracuseStep 15113765 = 2833831) B2833831
theorem B5815871 : Blo 1530462 5815871 := bstep (se 1 (by rfl) ⟨4361903, by rfl⟩ : syracuseStep 5815871 = 8723807) B8723807
theorem B1531503 : Blo 1530462 1531503 := bstep (se 1 (by rfl) ⟨1148627, by rfl⟩ : syracuseStep 1531503 = 2297255) B2297255
theorem B1531559 : Blo 1530462 1531559 := bstep (se 1 (by rfl) ⟨1148669, by rfl⟩ : syracuseStep 1531559 = 2297339) B2297339
theorem B11042513 : Blo 1530462 11042513 := bstep (se 2 (by rfl) ⟨4140942, by rfl⟩ : syracuseStep 11042513 = 8281885) B8281885
theorem B11624147 : Blo 1530462 11624147 := bstep (se 1 (by rfl) ⟨8718110, by rfl⟩ : syracuseStep 11624147 = 17436221) B17436221
theorem B6627035 : Blo 1530462 6627035 := bstep (se 1 (by rfl) ⟨4970276, by rfl⟩ : syracuseStep 6627035 = 9940553) B9940553
theorem B1531623 : Blo 1530462 1531623 := bstep (se 1 (by rfl) ⟨1148717, by rfl⟩ : syracuseStep 1531623 = 2297435) B2297435
theorem B1531679 : Blo 1530462 1531679 := bstep (se 1 (by rfl) ⟨1148759, by rfl⟩ : syracuseStep 1531679 = 2297519) B2297519
theorem B1531759 : Blo 1530462 1531759 := bstep (se 1 (by rfl) ⟨1148819, by rfl⟩ : syracuseStep 1531759 = 2297639) B2297639
theorem B3678107 : Blo 1530462 3678107 := bstep (se 1 (by rfl) ⟨2758580, by rfl⟩ : syracuseStep 3678107 = 5517161) B5517161
theorem B1531815 : Blo 1530462 1531815 := bstep (se 1 (by rfl) ⟨1148861, by rfl⟩ : syracuseStep 1531815 = 2297723) B2297723
theorem B3678185 : Blo 1530462 3678185 := bstep (se 2 (by rfl) ⟨1379319, by rfl⟩ : syracuseStep 3678185 = 2758639) B2758639
theorem B1531967 : Blo 1530462 1531967 := bstep (se 1 (by rfl) ⟨1148975, by rfl⟩ : syracuseStep 1531967 = 2297951) B2297951
theorem B1531975 : Blo 1530462 1531975 := bstep (se 1 (by rfl) ⟨1148981, by rfl⟩ : syracuseStep 1531975 = 2297963) B2297963
theorem B3268711 : Blo 1530462 3268711 := bstep (se 1 (by rfl) ⟨2451533, by rfl⟩ : syracuseStep 3268711 = 4903067) B4903067
theorem B1532007 : Blo 1530462 1532007 := bstep (se 1 (by rfl) ⟨1149005, by rfl⟩ : syracuseStep 1532007 = 2298011) B2298011
theorem B3874999 : Blo 1530462 3874999 := bstep (se 1 (by rfl) ⟨2906249, by rfl⟩ : syracuseStep 3874999 = 5812499) B5812499
theorem B26174015 : Blo 1530462 26174015 := bstep (se 1 (by rfl) ⟨19630511, by rfl⟩ : syracuseStep 26174015 = 39261023) B39261023
theorem B19620467 : Blo 1530462 19620467 := bstep (se 1 (by rfl) ⟨14715350, by rfl⟩ : syracuseStep 19620467 = 29430701) B29430701
theorem B3875465 : Blo 1530462 3875465 := bstep (se 2 (by rfl) ⟨1453299, by rfl⟩ : syracuseStep 3875465 = 2906599) B2906599
theorem B6210557 : Blo 1530462 6210557 := bstep (se 3 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 6210557 = 2328959) B2328959
theorem B2180143 : Blo 1530462 2180143 := bstep (se 1 (by rfl) ⟨1635107, by rfl⟩ : syracuseStep 2180143 = 3270215) B3270215
theorem B11035705 : Blo 1530462 11035705 := bstep (se 2 (by rfl) ⟨4138389, by rfl⟩ : syracuseStep 11035705 = 8276779) B8276779
theorem B4654255 : Blo 1530462 4654255 := bstep (se 1 (by rfl) ⟨3490691, by rfl⟩ : syracuseStep 4654255 = 6981383) B6981383
theorem B14714045 : Blo 1530462 14714045 := bstep (se 3 (by rfl) ⟨2758883, by rfl⟩ : syracuseStep 14714045 = 5517767) B5517767
theorem B13075937 : Blo 1530462 13075937 := bstep (se 2 (by rfl) ⟨4903476, by rfl⟩ : syracuseStep 13075937 = 9806953) B9806953
theorem B1721947 : Blo 1530462 1721947 := bstep (se 1 (by rfl) ⟨1291460, by rfl⟩ : syracuseStep 1721947 = 2582921) B2582921
theorem B3876457 : Blo 1530462 3876457 := bstep (se 2 (by rfl) ⟨1453671, by rfl⟩ : syracuseStep 3876457 = 2907343) B2907343
theorem B39274145 : Blo 1530462 39274145 := bstep (se 2 (by rfl) ⟨14727804, by rfl⟩ : syracuseStep 39274145 = 29455609) B29455609
theorem B5170931 : Blo 1530462 5170931 := bstep (se 1 (by rfl) ⟨3878198, by rfl⟩ : syracuseStep 5170931 = 7756397) B7756397
theorem B2295707 : Blo 1530462 2295707 := bstep (se 1 (by rfl) ⟨1721780, by rfl⟩ : syracuseStep 2295707 = 3443561) B3443561
theorem B2295743 : Blo 1530462 2295743 := bstep (se 1 (by rfl) ⟨1721807, by rfl⟩ : syracuseStep 2295743 = 3443615) B3443615
theorem B17434763 : Blo 1530462 17434763 := bstep (se 1 (by rfl) ⟨13076072, by rfl⟩ : syracuseStep 17434763 = 26152145) B26152145
theorem B6056171 : Blo 1530462 6056171 := bstep (se 1 (by rfl) ⟨4542128, by rfl⟩ : syracuseStep 6056171 = 9084257) B9084257
theorem B9816335 : Blo 1530462 9816335 := bstep (se 1 (by rfl) ⟨7362251, by rfl⟩ : syracuseStep 9816335 = 14724503) B14724503
theorem B3877247 : Blo 1530462 3877247 := bstep (se 1 (by rfl) ⟨2907935, by rfl⟩ : syracuseStep 3877247 = 5815871) B5815871
theorem B9808285 : Blo 1530462 9808285 := bstep (se 3 (by rfl) ⟨1839053, by rfl⟩ : syracuseStep 9808285 = 3678107) B3678107
theorem B4418023 : Blo 1530462 4418023 := bstep (se 1 (by rfl) ⟨3313517, by rfl⟩ : syracuseStep 4418023 = 6627035) B6627035
theorem B2296367 : Blo 1530462 2296367 := bstep (se 1 (by rfl) ⟨1722275, by rfl⟩ : syracuseStep 2296367 = 3444551) B3444551
theorem B11635325 : Blo 1530462 11635325 := bstep (se 3 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 11635325 = 4363247) B4363247
theorem B2452123 : Blo 1530462 2452123 := bstep (se 1 (by rfl) ⟨1839092, by rfl⟩ : syracuseStep 2452123 = 3678185) B3678185
theorem B2296487 : Blo 1530462 2296487 := bstep (se 1 (by rfl) ⟨1722365, by rfl⟩ : syracuseStep 2296487 = 3444731) B3444731
theorem B3492571 : Blo 1530462 3492571 := bstep (se 1 (by rfl) ⟨2619428, by rfl⟩ : syracuseStep 3492571 = 5238857) B5238857
theorem B1723099 : Blo 1530462 1723099 := bstep (se 1 (by rfl) ⟨1292324, by rfl⟩ : syracuseStep 1723099 = 2584649) B2584649
theorem B2296553 : Blo 1530462 2296553 := bstep (se 2 (by rfl) ⟨861207, by rfl⟩ : syracuseStep 2296553 = 1722415) B1722415
theorem B2296559 : Blo 1530462 2296559 := bstep (se 1 (by rfl) ⟨1722419, by rfl⟩ : syracuseStep 2296559 = 3444839) B3444839
theorem B1723135 : Blo 1530462 1723135 := bstep (se 1 (by rfl) ⟨1292351, by rfl⟩ : syracuseStep 1723135 = 2584703) B2584703
theorem B2296607 : Blo 1530462 2296607 := bstep (se 1 (by rfl) ⟨1722455, by rfl⟩ : syracuseStep 2296607 = 3444911) B3444911
theorem B9816875 : Blo 1530462 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B2583353 : Blo 1530462 2583353 := bstep (se 2 (by rfl) ⟨968757, by rfl⟩ : syracuseStep 2583353 = 1937515) B1937515
theorem B3877703 : Blo 1530462 3877703 := bstep (se 1 (by rfl) ⟨2908277, by rfl⟩ : syracuseStep 3877703 = 5816555) B5816555
theorem B3271547 : Blo 1530462 3271547 := bstep (se 1 (by rfl) ⟨2453660, by rfl⟩ : syracuseStep 3271547 = 4907321) B4907321
theorem B7859105 : Blo 1530462 7859105 := bstep (se 2 (by rfl) ⟨2947164, by rfl⟩ : syracuseStep 7859105 = 5894329) B5894329
theorem B7752671 : Blo 1530462 7752671 := bstep (se 1 (by rfl) ⟨5814503, by rfl⟩ : syracuseStep 7752671 = 11629007) B11629007
theorem B9309239 : Blo 1530462 9309239 := bstep (se 1 (by rfl) ⟨6981929, by rfl⟩ : syracuseStep 9309239 = 13963859) B13963859
theorem B2296937 : Blo 1530462 2296937 := bstep (se 2 (by rfl) ⟨861351, by rfl⟩ : syracuseStep 2296937 = 1722703) B1722703
theorem B2297063 : Blo 1530462 2297063 := bstep (se 1 (by rfl) ⟨1722797, by rfl⟩ : syracuseStep 2297063 = 3445595) B3445595
theorem B1723855 : Blo 1530462 1723855 := bstep (se 1 (by rfl) ⟨1292891, by rfl⟩ : syracuseStep 1723855 = 2585783) B2585783
theorem B2297567 : Blo 1530462 2297567 := bstep (se 1 (by rfl) ⟨1723175, by rfl⟩ : syracuseStep 2297567 = 3446351) B3446351
theorem B11038679 : Blo 1530462 11038679 := bstep (se 1 (by rfl) ⟨8279009, by rfl⟩ : syracuseStep 11038679 = 16558019) B16558019
theorem B11628521 : Blo 1530462 11628521 := bstep (se 2 (by rfl) ⟨4360695, by rfl⟩ : syracuseStep 11628521 = 8721391) B8721391
theorem B2297849 : Blo 1530462 2297849 := bstep (se 2 (by rfl) ⟨861693, by rfl⟩ : syracuseStep 2297849 = 1723387) B1723387
theorem B13979699 : Blo 1530462 13979699 := bstep (se 1 (by rfl) ⟨10484774, by rfl⟩ : syracuseStep 13979699 = 20969549) B20969549
theorem B4657343 : Blo 1530462 4657343 := bstep (se 1 (by rfl) ⟨3493007, by rfl⟩ : syracuseStep 4657343 = 6986015) B6986015
theorem B2298047 : Blo 1530462 2298047 := bstep (se 1 (by rfl) ⟨1723535, by rfl⟩ : syracuseStep 2298047 = 3447071) B3447071
theorem B2298089 : Blo 1530462 2298089 := bstep (se 2 (by rfl) ⟨861783, by rfl⟩ : syracuseStep 2298089 = 1723567) B1723567
theorem B4362599 : Blo 1530462 4362599 := bstep (se 1 (by rfl) ⟨3271949, by rfl⟩ : syracuseStep 4362599 = 6543899) B6543899
theorem B2298215 : Blo 1530462 2298215 := bstep (se 1 (by rfl) ⟨1723661, by rfl⟩ : syracuseStep 2298215 = 3447323) B3447323
theorem B17437679 : Blo 1530462 17437679 := bstep (se 1 (by rfl) ⟨13078259, by rfl⟩ : syracuseStep 17437679 = 26156519) B26156519
theorem B9811003 : Blo 1530462 9811003 := bstep (se 1 (by rfl) ⟨7358252, by rfl⟩ : syracuseStep 9811003 = 14716505) B14716505
theorem B2585695 : Blo 1530462 2585695 := bstep (se 1 (by rfl) ⟨1939271, by rfl⟩ : syracuseStep 2585695 = 3878543) B3878543
theorem B7361675 : Blo 1530462 7361675 := bstep (se 1 (by rfl) ⟨5521256, by rfl⟩ : syracuseStep 7361675 = 11042513) B11042513
theorem B8836481 : Blo 1530462 8836481 := bstep (se 2 (by rfl) ⟨3313680, by rfl⟩ : syracuseStep 8836481 = 6627361) B6627361
theorem B4363703 : Blo 1530462 4363703 := bstep (se 1 (by rfl) ⟨3272777, by rfl⟩ : syracuseStep 4363703 = 6545555) B6545555
theorem B7755425 : Blo 1530462 7755425 := bstep (se 2 (by rfl) ⟨2908284, by rfl⟩ : syracuseStep 7755425 = 5816569) B5816569
theorem B5814139 : Blo 1530462 5814139 := bstep (se 1 (by rfl) ⟨4360604, by rfl⟩ : syracuseStep 5814139 = 8721209) B8721209
theorem B44161271 : Blo 1530462 44161271 := bstep (se 1 (by rfl) ⟨33120953, by rfl⟩ : syracuseStep 44161271 = 66241907) B66241907
theorem B7362809 : Blo 1530462 7362809 := bstep (se 2 (by rfl) ⟨2761053, by rfl⟩ : syracuseStep 7362809 = 5522107) B5522107
theorem B18635017 : Blo 1530462 18635017 := bstep (se 2 (by rfl) ⟨6988131, by rfl⟩ : syracuseStep 18635017 = 13976263) B13976263
theorem B2873639 : Blo 1530462 2873639 := bstep (se 1 (by rfl) ⟨2155229, by rfl⟩ : syracuseStep 2873639 = 4310459) B4310459
theorem B3447143 : Blo 1530462 3447143 := bstep (se 1 (by rfl) ⟨2585357, by rfl⟩ : syracuseStep 3447143 = 5170715) B5170715
theorem B4905373 : Blo 1530462 4905373 := bstep (se 3 (by rfl) ⟨919757, by rfl⟩ : syracuseStep 4905373 = 1839515) B1839515
theorem B14727653 : Blo 1530462 14727653 := bstep (se 4 (by rfl) ⟨1380717, by rfl⟩ : syracuseStep 14727653 = 2761435) B2761435
theorem B1530559 : Blo 1530462 1530559 := bstep (se 1 (by rfl) ⟨1147919, by rfl⟩ : syracuseStep 1530559 = 2295839) B2295839
theorem B3447521 : Blo 1530462 3447521 := bstep (se 2 (by rfl) ⟨1292820, by rfl⟩ : syracuseStep 3447521 = 2585641) B2585641
theorem B5815097 : Blo 1530462 5815097 := bstep (se 2 (by rfl) ⟨2180661, by rfl⟩ : syracuseStep 5815097 = 4361323) B4361323
theorem B1530687 : Blo 1530462 1530687 := bstep (se 1 (by rfl) ⟨1148015, by rfl⟩ : syracuseStep 1530687 = 2296031) B2296031
theorem B1530727 : Blo 1530462 1530727 := bstep (se 1 (by rfl) ⟨1148045, by rfl⟩ : syracuseStep 1530727 = 2296091) B2296091
theorem B3103591 : Blo 1530462 3103591 := bstep (se 1 (by rfl) ⟨2327693, by rfl⟩ : syracuseStep 3103591 = 4655387) B4655387
theorem B11041703 : Blo 1530462 11041703 := bstep (se 1 (by rfl) ⟨8281277, by rfl⟩ : syracuseStep 11041703 = 16562555) B16562555
theorem B41917409 : Blo 1530462 41917409 := bstep (se 2 (by rfl) ⟨15719028, by rfl⟩ : syracuseStep 41917409 = 31438057) B31438057
theorem B1530943 : Blo 1530462 1530943 := bstep (se 1 (by rfl) ⟨1148207, by rfl⟩ : syracuseStep 1530943 = 2296415) B2296415
theorem B4906091 : Blo 1530462 4906091 := bstep (se 1 (by rfl) ⟨3679568, by rfl⟩ : syracuseStep 4906091 = 7359137) B7359137
theorem B1531131 : Blo 1530462 1531131 := bstep (se 1 (by rfl) ⟨1148348, by rfl⟩ : syracuseStep 1531131 = 2296697) B2296697
theorem B1531163 : Blo 1530462 1531163 := bstep (se 1 (by rfl) ⟨1148372, by rfl⟩ : syracuseStep 1531163 = 2296745) B2296745
theorem B11631923 : Blo 1530462 11631923 := bstep (se 1 (by rfl) ⟨8723942, by rfl⟩ : syracuseStep 11631923 = 17447885) B17447885
theorem B1531263 : Blo 1530462 1531263 := bstep (se 1 (by rfl) ⟨1148447, by rfl⟩ : syracuseStep 1531263 = 2296895) B2296895
theorem B19881409 : Blo 1530462 19881409 := bstep (se 2 (by rfl) ⟨7455528, by rfl⟩ : syracuseStep 19881409 = 14911057) B14911057
theorem B7757369 : Blo 1530462 7757369 := bstep (se 2 (by rfl) ⟨2909013, by rfl⟩ : syracuseStep 7757369 = 5818027) B5818027
theorem B4906603 : Blo 1530462 4906603 := bstep (se 1 (by rfl) ⟨3679952, by rfl⟩ : syracuseStep 4906603 = 7359905) B7359905
theorem B10075843 : Blo 1530462 10075843 := bstep (se 1 (by rfl) ⟨7556882, by rfl⟩ : syracuseStep 10075843 = 15113765) B15113765
theorem B7757531 : Blo 1530462 7757531 := bstep (se 1 (by rfl) ⟨5818148, by rfl⟩ : syracuseStep 7757531 = 11636297) B11636297
theorem B1531631 : Blo 1530462 1531631 := bstep (se 1 (by rfl) ⟨1148723, by rfl⟩ : syracuseStep 1531631 = 2297447) B2297447
theorem B7749431 : Blo 1530462 7749431 := bstep (se 1 (by rfl) ⟨5812073, by rfl⟩ : syracuseStep 7749431 = 11624147) B11624147
theorem B1531887 : Blo 1530462 1531887 := bstep (se 1 (by rfl) ⟨1148915, by rfl⟩ : syracuseStep 1531887 = 2297831) B2297831
theorem B1532031 : Blo 1530462 1532031 := bstep (se 1 (by rfl) ⟨1149023, by rfl⟩ : syracuseStep 1532031 = 2298047) B2298047
theorem B4358281 : Blo 1530462 4358281 := bstep (se 2 (by rfl) ⟨1634355, by rfl⟩ : syracuseStep 4358281 = 3268711) B3268711
theorem B1532059 : Blo 1530462 1532059 := bstep (se 1 (by rfl) ⟨1149044, by rfl⟩ : syracuseStep 1532059 = 2298089) B2298089
theorem B2908399 : Blo 1530462 2908399 := bstep (se 1 (by rfl) ⟨2181299, by rfl⟩ : syracuseStep 2908399 = 4362599) B4362599
theorem B1532143 : Blo 1530462 1532143 := bstep (se 1 (by rfl) ⟨1149107, by rfl⟩ : syracuseStep 1532143 = 2298215) B2298215
theorem B24846689 : Blo 1530462 24846689 := bstep (se 2 (by rfl) ⟨9317508, by rfl⟩ : syracuseStep 24846689 = 18635017) B18635017
theorem B17449343 : Blo 1530462 17449343 := bstep (se 1 (by rfl) ⟨13087007, by rfl⟩ : syracuseStep 17449343 = 26174015) B26174015
theorem B12419581 : Blo 1530462 12419581 := bstep (se 3 (by rfl) ⟨2328671, by rfl⟩ : syracuseStep 12419581 = 4657343) B4657343
theorem B5890697 : Blo 1530462 5890697 := bstep (se 2 (by rfl) ⟨2209011, by rfl⟩ : syracuseStep 5890697 = 4418023) B4418023
theorem B11625119 : Blo 1530462 11625119 := bstep (se 1 (by rfl) ⟨8718839, by rfl⟩ : syracuseStep 11625119 = 17437679) B17437679
theorem B4907783 : Blo 1530462 4907783 := bstep (se 1 (by rfl) ⟨3680837, by rfl⟩ : syracuseStep 4907783 = 7361675) B7361675
theorem B3269497 : Blo 1530462 3269497 := bstep (se 2 (by rfl) ⟨1226061, by rfl⟩ : syracuseStep 3269497 = 2452123) B2452123
theorem B5890987 : Blo 1530462 5890987 := bstep (se 1 (by rfl) ⟨4418240, by rfl⟩ : syracuseStep 5890987 = 8836481) B8836481
theorem B2909135 : Blo 1530462 2909135 := bstep (se 1 (by rfl) ⟨2181851, by rfl⟩ : syracuseStep 2909135 = 4363703) B4363703
theorem B8717291 : Blo 1530462 8717291 := bstep (se 1 (by rfl) ⟨6537968, by rfl⟩ : syracuseStep 8717291 = 13075937) B13075937
theorem B5170283 : Blo 1530462 5170283 := bstep (se 1 (by rfl) ⟨3877712, by rfl⟩ : syracuseStep 5170283 = 7755425) B7755425
theorem B26182763 : Blo 1530462 26182763 := bstep (se 1 (by rfl) ⟨19637072, by rfl⟩ : syracuseStep 26182763 = 39274145) B39274145
theorem B4138121 : Blo 1530462 4138121 := bstep (se 2 (by rfl) ⟨1551795, by rfl⟩ : syracuseStep 4138121 = 3103591) B3103591
theorem B14714273 : Blo 1530462 14714273 := bstep (se 2 (by rfl) ⟨5517852, by rfl⟩ : syracuseStep 14714273 = 11035705) B11035705
theorem B4908539 : Blo 1530462 4908539 := bstep (se 1 (by rfl) ⟨3681404, by rfl⟩ : syracuseStep 4908539 = 7362809) B7362809
theorem B1722235 : Blo 1530462 1722235 := bstep (se 1 (by rfl) ⟨1291676, by rfl⟩ : syracuseStep 1722235 = 2583353) B2583353
theorem B3876731 : Blo 1530462 3876731 := bstep (se 1 (by rfl) ⟨2907548, by rfl⟩ : syracuseStep 3876731 = 5815097) B5815097
theorem B27944939 : Blo 1530462 27944939 := bstep (se 1 (by rfl) ⟨20958704, by rfl⟩ : syracuseStep 27944939 = 41917409) B41917409
theorem B3270727 : Blo 1530462 3270727 := bstep (se 1 (by rfl) ⟨2453045, by rfl⟩ : syracuseStep 3270727 = 4906091) B4906091
theorem B2295929 : Blo 1530462 2295929 := bstep (se 2 (by rfl) ⟨860973, by rfl⟩ : syracuseStep 2295929 = 1721947) B1721947
theorem B5171579 : Blo 1530462 5171579 := bstep (se 1 (by rfl) ⟨3878684, by rfl⟩ : syracuseStep 5171579 = 7757369) B7757369
theorem B5171687 : Blo 1530462 5171687 := bstep (se 1 (by rfl) ⟨3878765, by rfl⟩ : syracuseStep 5171687 = 7757531) B7757531
theorem B7752185 : Blo 1530462 7752185 := bstep (se 2 (by rfl) ⟨2907069, by rfl⟩ : syracuseStep 7752185 = 5814139) B5814139
theorem B7359119 : Blo 1530462 7359119 := bstep (se 1 (by rfl) ⟨5519339, by rfl⟩ : syracuseStep 7359119 = 11038679) B11038679
theorem B7752347 : Blo 1530462 7752347 := bstep (se 1 (by rfl) ⟨5814260, by rfl⟩ : syracuseStep 7752347 = 11628521) B11628521
theorem B2583643 : Blo 1530462 2583643 := bstep (se 1 (by rfl) ⟨1937732, by rfl⟩ : syracuseStep 2583643 = 3875465) B3875465
theorem B13077713 : Blo 1530462 13077713 := bstep (se 2 (by rfl) ⟨4904142, by rfl⟩ : syracuseStep 13077713 = 9808285) B9808285
theorem B6540497 : Blo 1530462 6540497 := bstep (se 2 (by rfl) ⟨2452686, by rfl⟩ : syracuseStep 6540497 = 4905373) B4905373
theorem B4140371 : Blo 1530462 4140371 := bstep (se 1 (by rfl) ⟨3105278, by rfl⟩ : syracuseStep 4140371 = 6210557) B6210557
theorem B9809363 : Blo 1530462 9809363 := bstep (se 1 (by rfl) ⟨7357022, by rfl⟩ : syracuseStep 9809363 = 14714045) B14714045
theorem B4656761 : Blo 1530462 4656761 := bstep (se 2 (by rfl) ⟨1746285, by rfl⟩ : syracuseStep 4656761 = 3492571) B3492571
theorem B2297465 : Blo 1530462 2297465 := bstep (se 2 (by rfl) ⟨861549, by rfl⟩ : syracuseStep 2297465 = 1723099) B1723099
theorem B2297513 : Blo 1530462 2297513 := bstep (se 2 (by rfl) ⟨861567, by rfl⟩ : syracuseStep 2297513 = 1723135) B1723135
theorem B6205673 : Blo 1530462 6205673 := bstep (se 2 (by rfl) ⟨2327127, by rfl⟩ : syracuseStep 6205673 = 4654255) B4654255
theorem B2298095 : Blo 1530462 2298095 := bstep (se 1 (by rfl) ⟨1723571, by rfl⟩ : syracuseStep 2298095 = 3447143) B3447143
theorem B2584831 : Blo 1530462 2584831 := bstep (se 1 (by rfl) ⟨1938623, by rfl⟩ : syracuseStep 2584831 = 3877247) B3877247
theorem B9818435 : Blo 1530462 9818435 := bstep (se 1 (by rfl) ⟨7363826, by rfl⟩ : syracuseStep 9818435 = 14727653) B14727653
theorem B2298347 : Blo 1530462 2298347 := bstep (se 1 (by rfl) ⟨1723760, by rfl⟩ : syracuseStep 2298347 = 3447521) B3447521
theorem B2585135 : Blo 1530462 2585135 := bstep (se 1 (by rfl) ⟨1938851, by rfl⟩ : syracuseStep 2585135 = 3877703) B3877703
theorem B2298473 : Blo 1530462 2298473 := bstep (se 2 (by rfl) ⟨861927, by rfl⟩ : syracuseStep 2298473 = 1723855) B1723855
theorem B5239403 : Blo 1530462 5239403 := bstep (se 1 (by rfl) ⟨3929552, by rfl⟩ : syracuseStep 5239403 = 7859105) B7859105
theorem B7361135 : Blo 1530462 7361135 := bstep (se 1 (by rfl) ⟨5520851, by rfl⟩ : syracuseStep 7361135 = 11041703) B11041703
theorem B6206159 : Blo 1530462 6206159 := bstep (se 1 (by rfl) ⟨4654619, by rfl⟩ : syracuseStep 6206159 = 9309239) B9309239
theorem B6542137 : Blo 1530462 6542137 := bstep (se 2 (by rfl) ⟨2453301, by rfl⟩ : syracuseStep 6542137 = 4906603) B4906603
theorem B7754615 : Blo 1530462 7754615 := bstep (se 1 (by rfl) ⟨5815961, by rfl⟩ : syracuseStep 7754615 = 11631923) B11631923
theorem B5166287 : Blo 1530462 5166287 := bstep (se 1 (by rfl) ⟨3874715, by rfl⟩ : syracuseStep 5166287 = 7749431) B7749431
theorem B9319799 : Blo 1530462 9319799 := bstep (se 1 (by rfl) ⟨6989849, by rfl⟩ : syracuseStep 9319799 = 13979699) B13979699
theorem B5166665 : Blo 1530462 5166665 := bstep (se 2 (by rfl) ⟨1937499, by rfl⟩ : syracuseStep 5166665 = 3874999) B3874999
theorem B13080311 : Blo 1530462 13080311 := bstep (se 1 (by rfl) ⟨9810233, by rfl⟩ : syracuseStep 13080311 = 19620467) B19620467
theorem B3447287 : Blo 1530462 3447287 := bstep (se 1 (by rfl) ⟨2585465, by rfl⟩ : syracuseStep 3447287 = 5170931) B5170931
theorem B1530471 : Blo 1530462 1530471 := bstep (se 1 (by rfl) ⟨1147853, by rfl⟩ : syracuseStep 1530471 = 2295707) B2295707
theorem B1530495 : Blo 1530462 1530495 := bstep (se 1 (by rfl) ⟨1147871, by rfl⟩ : syracuseStep 1530495 = 2295743) B2295743
theorem B2906857 : Blo 1530462 2906857 := bstep (se 2 (by rfl) ⟨1090071, by rfl⟩ : syracuseStep 2906857 = 2180143) B2180143
theorem B13081337 : Blo 1530462 13081337 := bstep (se 2 (by rfl) ⟨4905501, by rfl⟩ : syracuseStep 13081337 = 9811003) B9811003
theorem B11623175 : Blo 1530462 11623175 := bstep (se 1 (by rfl) ⟨8717381, by rfl⟩ : syracuseStep 11623175 = 17434763) B17434763
theorem B3447593 : Blo 1530462 3447593 := bstep (se 2 (by rfl) ⟨1292847, by rfl⟩ : syracuseStep 3447593 = 2585695) B2585695
theorem B4037447 : Blo 1530462 4037447 := bstep (se 1 (by rfl) ⟨3028085, by rfl⟩ : syracuseStep 4037447 = 6056171) B6056171
theorem B29440847 : Blo 1530462 29440847 := bstep (se 1 (by rfl) ⟨22080635, by rfl⟩ : syracuseStep 29440847 = 44161271) B44161271
theorem B6544223 : Blo 1530462 6544223 := bstep (se 1 (by rfl) ⟨4908167, by rfl⟩ : syracuseStep 6544223 = 9816335) B9816335
theorem B1915759 : Blo 1530462 1915759 := bstep (se 1 (by rfl) ⟨1436819, by rfl⟩ : syracuseStep 1915759 = 2873639) B2873639
theorem B1530911 : Blo 1530462 1530911 := bstep (se 1 (by rfl) ⟨1148183, by rfl⟩ : syracuseStep 1530911 = 2296367) B2296367
theorem B7756883 : Blo 1530462 7756883 := bstep (se 1 (by rfl) ⟨5817662, by rfl⟩ : syracuseStep 7756883 = 11635325) B11635325
theorem B1530991 : Blo 1530462 1530991 := bstep (se 1 (by rfl) ⟨1148243, by rfl⟩ : syracuseStep 1530991 = 2296487) B2296487
theorem B1531035 : Blo 1530462 1531035 := bstep (se 1 (by rfl) ⟨1148276, by rfl⟩ : syracuseStep 1531035 = 2296553) B2296553
theorem B1531039 : Blo 1530462 1531039 := bstep (se 1 (by rfl) ⟨1148279, by rfl⟩ : syracuseStep 1531039 = 2296559) B2296559
theorem B1531071 : Blo 1530462 1531071 := bstep (se 1 (by rfl) ⟨1148303, by rfl⟩ : syracuseStep 1531071 = 2296607) B2296607
theorem B6544583 : Blo 1530462 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B26508545 : Blo 1530462 26508545 := bstep (se 2 (by rfl) ⟨9940704, by rfl⟩ : syracuseStep 26508545 = 19881409) B19881409
theorem B5168447 : Blo 1530462 5168447 := bstep (se 1 (by rfl) ⟨3876335, by rfl⟩ : syracuseStep 5168447 = 7752671) B7752671
theorem B1531291 : Blo 1530462 1531291 := bstep (se 1 (by rfl) ⟨1148468, by rfl⟩ : syracuseStep 1531291 = 2296937) B2296937
theorem B5168609 : Blo 1530462 5168609 := bstep (se 2 (by rfl) ⟨1938228, by rfl⟩ : syracuseStep 5168609 = 3876457) B3876457
theorem B1531375 : Blo 1530462 1531375 := bstep (se 1 (by rfl) ⟨1148531, by rfl⟩ : syracuseStep 1531375 = 2297063) B2297063
theorem B13434457 : Blo 1530462 13434457 := bstep (se 2 (by rfl) ⟨5037921, by rfl⟩ : syracuseStep 13434457 = 10075843) B10075843
theorem B8724125 : Blo 1530462 8724125 := bstep (se 3 (by rfl) ⟨1635773, by rfl⟩ : syracuseStep 8724125 = 3271547) B3271547
theorem B1531711 : Blo 1530462 1531711 := bstep (se 1 (by rfl) ⟨1148783, by rfl⟩ : syracuseStep 1531711 = 2297567) B2297567
theorem B1531899 : Blo 1530462 1531899 := bstep (se 1 (by rfl) ⟨1148924, by rfl⟩ : syracuseStep 1531899 = 2297849) B2297849
theorem B1532063 : Blo 1530462 1532063 := bstep (se 1 (by rfl) ⟨1149047, by rfl⟩ : syracuseStep 1532063 = 2298095) B2298095
theorem B6545623 : Blo 1530462 6545623 := bstep (se 1 (by rfl) ⟨4909217, by rfl⟩ : syracuseStep 6545623 = 9818435) B9818435
theorem B16564459 : Blo 1530462 16564459 := bstep (se 1 (by rfl) ⟨12423344, by rfl⟩ : syracuseStep 16564459 = 24846689) B24846689
theorem B11632895 : Blo 1530462 11632895 := bstep (se 1 (by rfl) ⟨8724671, by rfl⟩ : syracuseStep 11632895 = 17449343) B17449343
theorem B1532231 : Blo 1530462 1532231 := bstep (se 1 (by rfl) ⟨1149173, by rfl⟩ : syracuseStep 1532231 = 2298347) B2298347
theorem B1532315 : Blo 1530462 1532315 := bstep (se 1 (by rfl) ⟨1149236, by rfl⟩ : syracuseStep 1532315 = 2298473) B2298473
theorem B4907423 : Blo 1530462 4907423 := bstep (se 1 (by rfl) ⟨3680567, by rfl⟩ : syracuseStep 4907423 = 7361135) B7361135
theorem B7750079 : Blo 1530462 7750079 := bstep (se 1 (by rfl) ⟨5812559, by rfl⟩ : syracuseStep 7750079 = 11625119) B11625119
theorem B5169743 : Blo 1530462 5169743 := bstep (se 1 (by rfl) ⟨3877307, by rfl⟩ : syracuseStep 5169743 = 7754615) B7754615
theorem B16548461 : Blo 1530462 16548461 := bstep (se 3 (by rfl) ⟨3102836, by rfl⟩ : syracuseStep 16548461 = 6205673) B6205673
theorem B3875809 : Blo 1530462 3875809 := bstep (se 2 (by rfl) ⟨1453428, by rfl⟩ : syracuseStep 3875809 = 2906857) B2906857
theorem B4359329 : Blo 1530462 4359329 := bstep (se 2 (by rfl) ⟨1634748, by rfl⟩ : syracuseStep 4359329 = 3269497) B3269497
theorem B16549757 : Blo 1530462 16549757 := bstep (se 3 (by rfl) ⟨3103079, by rfl⟩ : syracuseStep 16549757 = 6206159) B6206159
theorem B5171255 : Blo 1530462 5171255 := bstep (se 1 (by rfl) ⟨3878441, by rfl⟩ : syracuseStep 5171255 = 7756883) B7756883
theorem B8718475 : Blo 1530462 8718475 := bstep (se 1 (by rfl) ⟨6538856, by rfl⟩ : syracuseStep 8718475 = 13077713) B13077713
theorem B4360331 : Blo 1530462 4360331 := bstep (se 1 (by rfl) ⟨3270248, by rfl⟩ : syracuseStep 4360331 = 6540497) B6540497
theorem B17672363 : Blo 1530462 17672363 := bstep (se 1 (by rfl) ⟨13254272, by rfl⟩ : syracuseStep 17672363 = 26508545) B26508545
theorem B31418597 : Blo 1530462 31418597 := bstep (se 4 (by rfl) ⟨2945493, by rfl⟩ : syracuseStep 31418597 = 5890987) B5890987
theorem B6539575 : Blo 1530462 6539575 := bstep (se 1 (by rfl) ⟨4904681, by rfl⟩ : syracuseStep 6539575 = 9809363) B9809363
theorem B2296313 : Blo 1530462 2296313 := bstep (se 2 (by rfl) ⟨861117, by rfl⟩ : syracuseStep 2296313 = 1722235) B1722235
theorem B4360969 : Blo 1530462 4360969 := bstep (se 2 (by rfl) ⟨1635363, by rfl⟩ : syracuseStep 4360969 = 3270727) B3270727
theorem B5811041 : Blo 1530462 5811041 := bstep (se 2 (by rfl) ⟨2179140, by rfl⟩ : syracuseStep 5811041 = 4358281) B4358281
theorem B3877865 : Blo 1530462 3877865 := bstep (se 2 (by rfl) ⟨1454199, by rfl⟩ : syracuseStep 3877865 = 2908399) B2908399
theorem B1723423 : Blo 1530462 1723423 := bstep (se 1 (by rfl) ⟨1292567, by rfl⟩ : syracuseStep 1723423 = 2585135) B2585135
theorem B3492935 : Blo 1530462 3492935 := bstep (se 1 (by rfl) ⟨2619701, by rfl⟩ : syracuseStep 3492935 = 5239403) B5239403
theorem B3927131 : Blo 1530462 3927131 := bstep (se 1 (by rfl) ⟨2945348, by rfl⟩ : syracuseStep 3927131 = 5890697) B5890697
theorem B3271855 : Blo 1530462 3271855 := bstep (se 1 (by rfl) ⟨2453891, by rfl⟩ : syracuseStep 3271855 = 4907783) B4907783
theorem B5811527 : Blo 1530462 5811527 := bstep (se 1 (by rfl) ⟨4358645, by rfl⟩ : syracuseStep 5811527 = 8717291) B8717291
theorem B16559441 : Blo 1530462 16559441 := bstep (se 2 (by rfl) ⟨6209790, by rfl⟩ : syracuseStep 16559441 = 12419581) B12419581
theorem B3444191 : Blo 1530462 3444191 := bstep (se 1 (by rfl) ⟨2583143, by rfl⟩ : syracuseStep 3444191 = 5166287) B5166287
theorem B6213199 : Blo 1530462 6213199 := bstep (se 1 (by rfl) ⟨4659899, by rfl⟩ : syracuseStep 6213199 = 9319799) B9319799
theorem B9809515 : Blo 1530462 9809515 := bstep (se 1 (by rfl) ⟨7357136, by rfl⟩ : syracuseStep 9809515 = 14714273) B14714273
theorem B3444443 : Blo 1530462 3444443 := bstep (se 1 (by rfl) ⟨2583332, by rfl⟩ : syracuseStep 3444443 = 5166665) B5166665
theorem B8720207 : Blo 1530462 8720207 := bstep (se 1 (by rfl) ⟨6540155, by rfl⟩ : syracuseStep 8720207 = 13080311) B13080311
theorem B2584487 : Blo 1530462 2584487 := bstep (se 1 (by rfl) ⟨1938365, by rfl⟩ : syracuseStep 2584487 = 3876731) B3876731
theorem B3444857 : Blo 1530462 3444857 := bstep (se 2 (by rfl) ⟨1291821, by rfl⟩ : syracuseStep 3444857 = 2583643) B2583643
theorem B2298191 : Blo 1530462 2298191 := bstep (se 1 (by rfl) ⟨1723643, by rfl⟩ : syracuseStep 2298191 = 3447287) B3447287
theorem B8720891 : Blo 1530462 8720891 := bstep (se 1 (by rfl) ⟨6540668, by rfl⟩ : syracuseStep 8720891 = 13081337) B13081337
theorem B2298395 : Blo 1530462 2298395 := bstep (se 1 (by rfl) ⟨1723796, by rfl⟩ : syracuseStep 2298395 = 3447593) B3447593
theorem B2691631 : Blo 1530462 2691631 := bstep (se 1 (by rfl) ⟨2018723, by rfl⟩ : syracuseStep 2691631 = 4037447) B4037447
theorem B4362815 : Blo 1530462 4362815 := bstep (se 1 (by rfl) ⟨3272111, by rfl⟩ : syracuseStep 4362815 = 6544223) B6544223
theorem B17912609 : Blo 1530462 17912609 := bstep (se 2 (by rfl) ⟨6717228, by rfl⟩ : syracuseStep 17912609 = 13434457) B13434457
theorem B4363055 : Blo 1530462 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B3445631 : Blo 1530462 3445631 := bstep (se 1 (by rfl) ⟨2584223, by rfl⟩ : syracuseStep 3445631 = 5168447) B5168447
theorem B3445739 : Blo 1530462 3445739 := bstep (se 1 (by rfl) ⟨2584304, by rfl⟩ : syracuseStep 3445739 = 5168609) B5168609
theorem B74519837 : Blo 1530462 74519837 := bstep (se 3 (by rfl) ⟨13972469, by rfl⟩ : syracuseStep 74519837 = 27944939) B27944939
theorem B3446441 : Blo 1530462 3446441 := bstep (se 2 (by rfl) ⟨1292415, by rfl⟩ : syracuseStep 3446441 = 2584831) B2584831
theorem B3446855 : Blo 1530462 3446855 := bstep (se 1 (by rfl) ⟨2585141, by rfl⟩ : syracuseStep 3446855 = 5170283) B5170283
theorem B17455175 : Blo 1530462 17455175 := bstep (se 1 (by rfl) ⟨13091381, by rfl⟩ : syracuseStep 17455175 = 26182763) B26182763
theorem B2758747 : Blo 1530462 2758747 := bstep (se 1 (by rfl) ⟨2069060, by rfl⟩ : syracuseStep 2758747 = 4138121) B4138121
theorem B8722849 : Blo 1530462 8722849 := bstep (se 2 (by rfl) ⟨3271068, by rfl⟩ : syracuseStep 8722849 = 6542137) B6542137
theorem B2554345 : Blo 1530462 2554345 := bstep (se 2 (by rfl) ⟨957879, by rfl⟩ : syracuseStep 2554345 = 1915759) B1915759
theorem B13089437 : Blo 1530462 13089437 := bstep (se 3 (by rfl) ⟨2454269, by rfl⟩ : syracuseStep 13089437 = 4908539) B4908539
theorem B1530619 : Blo 1530462 1530619 := bstep (se 1 (by rfl) ⟨1147964, by rfl⟩ : syracuseStep 1530619 = 2295929) B2295929
theorem B3447719 : Blo 1530462 3447719 := bstep (se 1 (by rfl) ⟨2585789, by rfl⟩ : syracuseStep 3447719 = 5171579) B5171579
theorem B3447791 : Blo 1530462 3447791 := bstep (se 1 (by rfl) ⟨2585843, by rfl⟩ : syracuseStep 3447791 = 5171687) B5171687
theorem B5168123 : Blo 1530462 5168123 := bstep (se 1 (by rfl) ⟨3876092, by rfl⟩ : syracuseStep 5168123 = 7752185) B7752185
theorem B4906079 : Blo 1530462 4906079 := bstep (se 1 (by rfl) ⟨3679559, by rfl⟩ : syracuseStep 4906079 = 7359119) B7359119
theorem B5168231 : Blo 1530462 5168231 := bstep (se 1 (by rfl) ⟨3876173, by rfl⟩ : syracuseStep 5168231 = 7752347) B7752347
theorem B7748783 : Blo 1530462 7748783 := bstep (se 1 (by rfl) ⟨5811587, by rfl⟩ : syracuseStep 7748783 = 11623175) B11623175
theorem B19627231 : Blo 1530462 19627231 := bstep (se 1 (by rfl) ⟨14720423, by rfl⟩ : syracuseStep 19627231 = 29440847) B29440847
theorem B2760247 : Blo 1530462 2760247 := bstep (se 1 (by rfl) ⟨2070185, by rfl⟩ : syracuseStep 2760247 = 4140371) B4140371
theorem B3104507 : Blo 1530462 3104507 := bstep (se 1 (by rfl) ⟨2328380, by rfl⟩ : syracuseStep 3104507 = 4656761) B4656761
theorem B1531643 : Blo 1530462 1531643 := bstep (se 1 (by rfl) ⟨1148732, by rfl⟩ : syracuseStep 1531643 = 2297465) B2297465
theorem B5816083 : Blo 1530462 5816083 := bstep (se 1 (by rfl) ⟨4362062, by rfl⟩ : syracuseStep 5816083 = 8724125) B8724125
theorem B1531675 : Blo 1530462 1531675 := bstep (se 1 (by rfl) ⟨1148756, by rfl⟩ : syracuseStep 1531675 = 2297513) B2297513
theorem B7757693 : Blo 1530462 7757693 := bstep (se 3 (by rfl) ⟨1454567, by rfl⟩ : syracuseStep 7757693 = 2909135) B2909135
theorem B3678329 : Blo 1530462 3678329 := bstep (se 2 (by rfl) ⟨1379373, by rfl⟩ : syracuseStep 3678329 = 2758747) B2758747
theorem B11624633 : Blo 1530462 11624633 := bstep (se 2 (by rfl) ⟨4359237, by rfl⟩ : syracuseStep 11624633 = 8718475) B8718475
theorem B1532127 : Blo 1530462 1532127 := bstep (se 1 (by rfl) ⟨1149095, by rfl⟩ : syracuseStep 1532127 = 2298191) B2298191
theorem B22085945 : Blo 1530462 22085945 := bstep (se 2 (by rfl) ⟨8282229, by rfl⟩ : syracuseStep 22085945 = 16564459) B16564459
theorem B1532263 : Blo 1530462 1532263 := bstep (se 1 (by rfl) ⟨1149197, by rfl⟩ : syracuseStep 1532263 = 2298395) B2298395
theorem B2908543 : Blo 1530462 2908543 := bstep (se 1 (by rfl) ⟨2181407, by rfl⟩ : syracuseStep 2908543 = 4362815) B4362815
theorem B2908703 : Blo 1530462 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B11781575 : Blo 1530462 11781575 := bstep (se 1 (by rfl) ⟨8836181, by rfl⟩ : syracuseStep 11781575 = 17672363) B17672363
theorem B8726291 : Blo 1530462 8726291 := bstep (se 1 (by rfl) ⟨6544718, by rfl⟩ : syracuseStep 8726291 = 13089437) B13089437
theorem B2328623 : Blo 1530462 2328623 := bstep (se 1 (by rfl) ⟨1746467, by rfl⟩ : syracuseStep 2328623 = 3492935) B3492935
theorem B3270719 : Blo 1530462 3270719 := bstep (se 1 (by rfl) ⟨2453039, by rfl⟩ : syracuseStep 3270719 = 4906079) B4906079
theorem B3680329 : Blo 1530462 3680329 := bstep (se 2 (by rfl) ⟨1380123, by rfl⟩ : syracuseStep 3680329 = 2760247) B2760247
theorem B8284265 : Blo 1530462 8284265 := bstep (se 2 (by rfl) ⟨3106599, by rfl⟩ : syracuseStep 8284265 = 6213199) B6213199
theorem B2296127 : Blo 1530462 2296127 := bstep (se 1 (by rfl) ⟨1722095, by rfl⟩ : syracuseStep 2296127 = 3444191) B3444191
theorem B2296295 : Blo 1530462 2296295 := bstep (se 1 (by rfl) ⟨1722221, by rfl⟩ : syracuseStep 2296295 = 3444443) B3444443
theorem B5171795 : Blo 1530462 5171795 := bstep (se 1 (by rfl) ⟨3878846, by rfl⟩ : syracuseStep 5171795 = 7757693) B7757693
theorem B1722991 : Blo 1530462 1722991 := bstep (se 1 (by rfl) ⟨1292243, by rfl⟩ : syracuseStep 1722991 = 2584487) B2584487
theorem B2296571 : Blo 1530462 2296571 := bstep (se 1 (by rfl) ⟨1722428, by rfl⟩ : syracuseStep 2296571 = 3444857) B3444857
theorem B14355365 : Blo 1530462 14355365 := bstep (se 4 (by rfl) ⟨1345815, by rfl⟩ : syracuseStep 14355365 = 2691631) B2691631
theorem B8727497 : Blo 1530462 8727497 := bstep (se 2 (by rfl) ⟨3272811, by rfl⟩ : syracuseStep 8727497 = 6545623) B6545623
theorem B11627549 : Blo 1530462 11627549 := bstep (se 3 (by rfl) ⟨2180165, by rfl⟩ : syracuseStep 11627549 = 4360331) B4360331
theorem B8719433 : Blo 1530462 8719433 := bstep (se 2 (by rfl) ⟨3269787, by rfl⟩ : syracuseStep 8719433 = 6539575) B6539575
theorem B2297087 : Blo 1530462 2297087 := bstep (se 1 (by rfl) ⟨1722815, by rfl⟩ : syracuseStep 2297087 = 3445631) B3445631
theorem B2297159 : Blo 1530462 2297159 := bstep (se 1 (by rfl) ⟨1722869, by rfl⟩ : syracuseStep 2297159 = 3445739) B3445739
theorem B49679891 : Blo 1530462 49679891 := bstep (se 1 (by rfl) ⟨37259918, by rfl⟩ : syracuseStep 49679891 = 74519837) B74519837
theorem B13086461 : Blo 1530462 13086461 := bstep (se 3 (by rfl) ⟨2453711, by rfl⟩ : syracuseStep 13086461 = 4907423) B4907423
theorem B2297627 : Blo 1530462 2297627 := bstep (se 1 (by rfl) ⟨1723220, by rfl⟩ : syracuseStep 2297627 = 3446441) B3446441
theorem B2297897 : Blo 1530462 2297897 := bstep (se 2 (by rfl) ⟨861711, by rfl⟩ : syracuseStep 2297897 = 1723423) B1723423
theorem B2297903 : Blo 1530462 2297903 := bstep (se 1 (by rfl) ⟨1723427, by rfl⟩ : syracuseStep 2297903 = 3446855) B3446855
theorem B11636783 : Blo 1530462 11636783 := bstep (se 1 (by rfl) ⟨8727587, by rfl⟩ : syracuseStep 11636783 = 17455175) B17455175
theorem B4362473 : Blo 1530462 4362473 := bstep (se 2 (by rfl) ⟨1635927, by rfl⟩ : syracuseStep 4362473 = 3271855) B3271855
theorem B26169641 : Blo 1530462 26169641 := bstep (se 2 (by rfl) ⟨9813615, by rfl⟩ : syracuseStep 26169641 = 19627231) B19627231
theorem B2298479 : Blo 1530462 2298479 := bstep (se 1 (by rfl) ⟨1723859, by rfl⟩ : syracuseStep 2298479 = 3447719) B3447719
theorem B2585243 : Blo 1530462 2585243 := bstep (se 1 (by rfl) ⟨1938932, by rfl⟩ : syracuseStep 2585243 = 3877865) B3877865
theorem B8278685 : Blo 1530462 8278685 := bstep (se 3 (by rfl) ⟨1552253, by rfl⟩ : syracuseStep 8278685 = 3104507) B3104507
theorem B2298527 : Blo 1530462 2298527 := bstep (se 1 (by rfl) ⟨1723895, by rfl⟩ : syracuseStep 2298527 = 3447791) B3447791
theorem B3445415 : Blo 1530462 3445415 := bstep (se 1 (by rfl) ⟨2584061, by rfl⟩ : syracuseStep 3445415 = 5168123) B5168123
theorem B2618087 : Blo 1530462 2618087 := bstep (se 1 (by rfl) ⟨1963565, by rfl⟩ : syracuseStep 2618087 = 3927131) B3927131
theorem B3445487 : Blo 1530462 3445487 := bstep (se 1 (by rfl) ⟨2584115, by rfl⟩ : syracuseStep 3445487 = 5168231) B5168231
theorem B5165855 : Blo 1530462 5165855 := bstep (se 1 (by rfl) ⟨3874391, by rfl⟩ : syracuseStep 5165855 = 7748783) B7748783
theorem B13079353 : Blo 1530462 13079353 := bstep (se 2 (by rfl) ⟨4904757, by rfl⟩ : syracuseStep 13079353 = 9809515) B9809515
theorem B11039627 : Blo 1530462 11039627 := bstep (se 1 (by rfl) ⟨8279720, by rfl⟩ : syracuseStep 11039627 = 16559441) B16559441
theorem B7754777 : Blo 1530462 7754777 := bstep (se 2 (by rfl) ⟨2908041, by rfl⟩ : syracuseStep 7754777 = 5816083) B5816083
theorem B5813471 : Blo 1530462 5813471 := bstep (se 1 (by rfl) ⟨4360103, by rfl⟩ : syracuseStep 5813471 = 8720207) B8720207
theorem B7755263 : Blo 1530462 7755263 := bstep (se 1 (by rfl) ⟨5816447, by rfl⟩ : syracuseStep 7755263 = 11632895) B11632895
theorem B5166719 : Blo 1530462 5166719 := bstep (se 1 (by rfl) ⟨3875039, by rfl⟩ : syracuseStep 5166719 = 7750079) B7750079
theorem B5813927 : Blo 1530462 5813927 := bstep (se 1 (by rfl) ⟨4360445, by rfl⟩ : syracuseStep 5813927 = 8720891) B8720891
theorem B3446495 : Blo 1530462 3446495 := bstep (se 1 (by rfl) ⟨2584871, by rfl⟩ : syracuseStep 3446495 = 5169743) B5169743
theorem B11032307 : Blo 1530462 11032307 := bstep (se 1 (by rfl) ⟨8274230, by rfl⟩ : syracuseStep 11032307 = 16548461) B16548461
theorem B11941739 : Blo 1530462 11941739 := bstep (se 1 (by rfl) ⟨8956304, by rfl⟩ : syracuseStep 11941739 = 17912609) B17912609
theorem B11630465 : Blo 1530462 11630465 := bstep (se 2 (by rfl) ⟨4361424, by rfl⟩ : syracuseStep 11630465 = 8722849) B8722849
theorem B2906219 : Blo 1530462 2906219 := bstep (se 1 (by rfl) ⟨2179664, by rfl⟩ : syracuseStep 2906219 = 4359329) B4359329
theorem B5814625 : Blo 1530462 5814625 := bstep (se 2 (by rfl) ⟨2180484, by rfl⟩ : syracuseStep 5814625 = 4360969) B4360969
theorem B11033171 : Blo 1530462 11033171 := bstep (se 1 (by rfl) ⟨8274878, by rfl⟩ : syracuseStep 11033171 = 16549757) B16549757
theorem B5167745 : Blo 1530462 5167745 := bstep (se 2 (by rfl) ⟨1937904, by rfl⟩ : syracuseStep 5167745 = 3875809) B3875809
theorem B3447503 : Blo 1530462 3447503 := bstep (se 1 (by rfl) ⟨2585627, by rfl⟩ : syracuseStep 3447503 = 5171255) B5171255
theorem B20945731 : Blo 1530462 20945731 := bstep (se 1 (by rfl) ⟨15709298, by rfl⟩ : syracuseStep 20945731 = 31418597) B31418597
theorem B1530875 : Blo 1530462 1530875 := bstep (se 1 (by rfl) ⟨1148156, by rfl⟩ : syracuseStep 1530875 = 2296313) B2296313
theorem B3874027 : Blo 1530462 3874027 := bstep (se 1 (by rfl) ⟨2905520, by rfl⟩ : syracuseStep 3874027 = 5811041) B5811041
theorem B3874351 : Blo 1530462 3874351 := bstep (se 1 (by rfl) ⟨2905763, by rfl⟩ : syracuseStep 3874351 = 5811527) B5811527
theorem B13623173 : Blo 1530462 13623173 := bstep (se 4 (by rfl) ⟨1277172, by rfl⟩ : syracuseStep 13623173 = 2554345) B2554345
theorem B1531931 : Blo 1530462 1531931 := bstep (se 1 (by rfl) ⟨1148948, by rfl⟩ : syracuseStep 1531931 = 2297897) B2297897
theorem B1531935 : Blo 1530462 1531935 := bstep (se 1 (by rfl) ⟨1148951, by rfl⟩ : syracuseStep 1531935 = 2297903) B2297903
theorem B7757855 : Blo 1530462 7757855 := bstep (se 1 (by rfl) ⟨5818391, by rfl⟩ : syracuseStep 7757855 = 11636783) B11636783
theorem B4907105 : Blo 1530462 4907105 := bstep (se 2 (by rfl) ⟨1840164, by rfl⟩ : syracuseStep 4907105 = 3680329) B3680329
theorem B7749755 : Blo 1530462 7749755 := bstep (se 1 (by rfl) ⟨5812316, by rfl⟩ : syracuseStep 7749755 = 11624633) B11624633
theorem B2908315 : Blo 1530462 2908315 := bstep (se 1 (by rfl) ⟨2181236, by rfl⟩ : syracuseStep 2908315 = 4362473) B4362473
theorem B7749917 : Blo 1530462 7749917 := bstep (se 3 (by rfl) ⟨1453109, by rfl⟩ : syracuseStep 7749917 = 2906219) B2906219
theorem B1532319 : Blo 1530462 1532319 := bstep (se 1 (by rfl) ⟨1149239, by rfl⟩ : syracuseStep 1532319 = 2298479) B2298479
theorem B1532351 : Blo 1530462 1532351 := bstep (se 1 (by rfl) ⟨1149263, by rfl⟩ : syracuseStep 1532351 = 2298527) B2298527
theorem B5169851 : Blo 1530462 5169851 := bstep (se 1 (by rfl) ⟨3877388, by rfl⟩ : syracuseStep 5169851 = 7754777) B7754777
theorem B3875647 : Blo 1530462 3875647 := bstep (se 1 (by rfl) ⟨2906735, by rfl⟩ : syracuseStep 3875647 = 5813471) B5813471
theorem B5170175 : Blo 1530462 5170175 := bstep (se 1 (by rfl) ⟨3877631, by rfl⟩ : syracuseStep 5170175 = 7755263) B7755263
theorem B27927641 : Blo 1530462 27927641 := bstep (se 2 (by rfl) ⟨10472865, by rfl⟩ : syracuseStep 27927641 = 20945731) B20945731
theorem B3875951 : Blo 1530462 3875951 := bstep (se 1 (by rfl) ⟨2906963, by rfl⟩ : syracuseStep 3875951 = 5813927) B5813927
theorem B5817527 : Blo 1530462 5817527 := bstep (se 1 (by rfl) ⟨4363145, by rfl⟩ : syracuseStep 5817527 = 8726291) B8726291
theorem B5522843 : Blo 1530462 5522843 := bstep (se 1 (by rfl) ⟨4142132, by rfl⟩ : syracuseStep 5522843 = 8284265) B8284265
theorem B6981565 : Blo 1530462 6981565 := bstep (se 3 (by rfl) ⟨1309043, by rfl⟩ : syracuseStep 6981565 = 2618087) B2618087
theorem B5818331 : Blo 1530462 5818331 := bstep (se 1 (by rfl) ⟨4363748, by rfl⟩ : syracuseStep 5818331 = 8727497) B8727497
theorem B7751699 : Blo 1530462 7751699 := bstep (se 1 (by rfl) ⟨5813774, by rfl⟩ : syracuseStep 7751699 = 11627549) B11627549
theorem B14723963 : Blo 1530462 14723963 := bstep (se 1 (by rfl) ⟨11042972, by rfl⟩ : syracuseStep 14723963 = 22085945) B22085945
theorem B9808877 : Blo 1530462 9808877 := bstep (se 3 (by rfl) ⟨1839164, by rfl⟩ : syracuseStep 9808877 = 3678329) B3678329
theorem B1723495 : Blo 1530462 1723495 := bstep (se 1 (by rfl) ⟨1292621, by rfl⟩ : syracuseStep 1723495 = 2585243) B2585243
theorem B2296943 : Blo 1530462 2296943 := bstep (se 1 (by rfl) ⟨1722707, by rfl⟩ : syracuseStep 2296943 = 3445415) B3445415
theorem B7752833 : Blo 1530462 7752833 := bstep (se 2 (by rfl) ⟨2907312, by rfl⟩ : syracuseStep 7752833 = 5814625) B5814625
theorem B2296991 : Blo 1530462 2296991 := bstep (se 1 (by rfl) ⟨1722743, by rfl⟩ : syracuseStep 2296991 = 3445487) B3445487
theorem B3878057 : Blo 1530462 3878057 := bstep (se 2 (by rfl) ⟨1454271, by rfl⟩ : syracuseStep 3878057 = 2908543) B2908543
theorem B3443903 : Blo 1530462 3443903 := bstep (se 1 (by rfl) ⟨2582927, by rfl⟩ : syracuseStep 3443903 = 5165855) B5165855
theorem B7359751 : Blo 1530462 7359751 := bstep (se 1 (by rfl) ⟨5519813, by rfl⟩ : syracuseStep 7359751 = 11039627) B11039627
theorem B2297321 : Blo 1530462 2297321 := bstep (se 2 (by rfl) ⟨861495, by rfl⟩ : syracuseStep 2297321 = 1722991) B1722991
theorem B3444479 : Blo 1530462 3444479 := bstep (se 1 (by rfl) ⟨2583359, by rfl⟩ : syracuseStep 3444479 = 5166719) B5166719
theorem B2297663 : Blo 1530462 2297663 := bstep (se 1 (by rfl) ⟨1723247, by rfl⟩ : syracuseStep 2297663 = 3446495) B3446495
theorem B7753643 : Blo 1530462 7753643 := bstep (se 1 (by rfl) ⟨5815232, by rfl⟩ : syracuseStep 7753643 = 11630465) B11630465
theorem B1552415 : Blo 1530462 1552415 := bstep (se 1 (by rfl) ⟨1164311, by rfl⟩ : syracuseStep 1552415 = 2328623) B2328623
theorem B5165369 : Blo 1530462 5165369 := bstep (se 2 (by rfl) ⟨1937013, by rfl⟩ : syracuseStep 5165369 = 3874027) B3874027
theorem B3445163 : Blo 1530462 3445163 := bstep (se 1 (by rfl) ⟨2583872, by rfl⟩ : syracuseStep 3445163 = 5167745) B5167745
theorem B2298335 : Blo 1530462 2298335 := bstep (se 1 (by rfl) ⟨1723751, by rfl⟩ : syracuseStep 2298335 = 3447503) B3447503
theorem B5812955 : Blo 1530462 5812955 := bstep (se 1 (by rfl) ⟨4359716, by rfl⟩ : syracuseStep 5812955 = 8719433) B8719433
theorem B5165801 : Blo 1530462 5165801 := bstep (se 2 (by rfl) ⟨1937175, by rfl⟩ : syracuseStep 5165801 = 3874351) B3874351
theorem B9082115 : Blo 1530462 9082115 := bstep (se 1 (by rfl) ⟨6811586, by rfl⟩ : syracuseStep 9082115 = 13623173) B13623173
theorem B8721917 : Blo 1530462 8721917 := bstep (se 3 (by rfl) ⟨1635359, by rfl⟩ : syracuseStep 8721917 = 3270719) B3270719
theorem B17446427 : Blo 1530462 17446427 := bstep (se 1 (by rfl) ⟨13084820, by rfl⟩ : syracuseStep 17446427 = 26169641) B26169641
theorem B1939135 : Blo 1530462 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B5519123 : Blo 1530462 5519123 := bstep (se 1 (by rfl) ⟨4139342, by rfl⟩ : syracuseStep 5519123 = 8278685) B8278685
theorem B7854383 : Blo 1530462 7854383 := bstep (se 1 (by rfl) ⟨5890787, by rfl⟩ : syracuseStep 7854383 = 11781575) B11781575
theorem B17439137 : Blo 1530462 17439137 := bstep (se 2 (by rfl) ⟨6539676, by rfl⟩ : syracuseStep 17439137 = 13079353) B13079353
theorem B7354871 : Blo 1530462 7354871 := bstep (se 1 (by rfl) ⟨5516153, by rfl⟩ : syracuseStep 7354871 = 11032307) B11032307
theorem B7961159 : Blo 1530462 7961159 := bstep (se 1 (by rfl) ⟨5970869, by rfl⟩ : syracuseStep 7961159 = 11941739) B11941739
theorem B1530751 : Blo 1530462 1530751 := bstep (se 1 (by rfl) ⟨1148063, by rfl⟩ : syracuseStep 1530751 = 2296127) B2296127
theorem B1530863 : Blo 1530462 1530863 := bstep (se 1 (by rfl) ⟨1148147, by rfl⟩ : syracuseStep 1530863 = 2296295) B2296295
theorem B7355447 : Blo 1530462 7355447 := bstep (se 1 (by rfl) ⟨5516585, by rfl⟩ : syracuseStep 7355447 = 11033171) B11033171
theorem B3447863 : Blo 1530462 3447863 := bstep (se 1 (by rfl) ⟨2585897, by rfl⟩ : syracuseStep 3447863 = 5171795) B5171795
theorem B1531047 : Blo 1530462 1531047 := bstep (se 1 (by rfl) ⟨1148285, by rfl⟩ : syracuseStep 1531047 = 2296571) B2296571
theorem B1531391 : Blo 1530462 1531391 := bstep (se 1 (by rfl) ⟨1148543, by rfl⟩ : syracuseStep 1531391 = 2297087) B2297087
theorem B1531439 : Blo 1530462 1531439 := bstep (se 1 (by rfl) ⟨1148579, by rfl⟩ : syracuseStep 1531439 = 2297159) B2297159
theorem B33119927 : Blo 1530462 33119927 := bstep (se 1 (by rfl) ⟨24839945, by rfl⟩ : syracuseStep 33119927 = 49679891) B49679891
theorem B38280973 : Blo 1530462 38280973 := bstep (se 3 (by rfl) ⟨7177682, by rfl⟩ : syracuseStep 38280973 = 14355365) B14355365
theorem B8724307 : Blo 1530462 8724307 := bstep (se 1 (by rfl) ⟨6543230, by rfl⟩ : syracuseStep 8724307 = 13086461) B13086461
theorem B1531751 : Blo 1530462 1531751 := bstep (se 1 (by rfl) ⟨1148813, by rfl⟩ : syracuseStep 1531751 = 2297627) B2297627
theorem B1532223 : Blo 1530462 1532223 := bstep (se 1 (by rfl) ⟨1149167, by rfl⟩ : syracuseStep 1532223 = 2298335) B2298335
theorem B3875303 : Blo 1530462 3875303 := bstep (se 1 (by rfl) ⟨2906477, by rfl⟩ : syracuseStep 3875303 = 5812955) B5812955
theorem B6054743 : Blo 1530462 6054743 := bstep (se 1 (by rfl) ⟨4541057, by rfl⟩ : syracuseStep 6054743 = 9082115) B9082115
theorem B3679415 : Blo 1530462 3679415 := bstep (se 1 (by rfl) ⟨2759561, by rfl⟩ : syracuseStep 3679415 = 5519123) B5519123
theorem B5236255 : Blo 1530462 5236255 := bstep (se 1 (by rfl) ⟨3927191, by rfl⟩ : syracuseStep 5236255 = 7854383) B7854383
theorem B11626091 : Blo 1530462 11626091 := bstep (se 1 (by rfl) ⟨8719568, by rfl⟩ : syracuseStep 11626091 = 17439137) B17439137
theorem B9815975 : Blo 1530462 9815975 := bstep (se 1 (by rfl) ⟨7361981, by rfl⟩ : syracuseStep 9815975 = 14723963) B14723963
theorem B6539251 : Blo 1530462 6539251 := bstep (se 1 (by rfl) ⟨4904438, by rfl⟩ : syracuseStep 6539251 = 9808877) B9808877
theorem B2295935 : Blo 1530462 2295935 := bstep (se 1 (by rfl) ⟨1721951, by rfl⟩ : syracuseStep 2295935 = 3443903) B3443903
theorem B22079951 : Blo 1530462 22079951 := bstep (se 1 (by rfl) ⟨16559963, by rfl⟩ : syracuseStep 22079951 = 33119927) B33119927
theorem B2296319 : Blo 1530462 2296319 := bstep (se 1 (by rfl) ⟨1722239, by rfl⟩ : syracuseStep 2296319 = 3444479) B3444479
theorem B9308753 : Blo 1530462 9308753 := bstep (se 2 (by rfl) ⟨3490782, by rfl⟩ : syracuseStep 9308753 = 6981565) B6981565
theorem B5171903 : Blo 1530462 5171903 := bstep (se 1 (by rfl) ⟨3878927, by rfl⟩ : syracuseStep 5171903 = 7757855) B7757855
theorem B3271403 : Blo 1530462 3271403 := bstep (se 1 (by rfl) ⟨2453552, by rfl⟩ : syracuseStep 3271403 = 4907105) B4907105
theorem B3877753 : Blo 1530462 3877753 := bstep (se 2 (by rfl) ⟨1454157, by rfl⟩ : syracuseStep 3877753 = 2908315) B2908315
theorem B3443579 : Blo 1530462 3443579 := bstep (se 1 (by rfl) ⟨2582684, by rfl⟩ : syracuseStep 3443579 = 5165369) B5165369
theorem B2296775 : Blo 1530462 2296775 := bstep (se 1 (by rfl) ⟨1722581, by rfl⟩ : syracuseStep 2296775 = 3445163) B3445163
theorem B16559093 : Blo 1530462 16559093 := bstep (se 5 (by rfl) ⟨776207, by rfl⟩ : syracuseStep 16559093 = 1552415) B1552415
theorem B3443867 : Blo 1530462 3443867 := bstep (se 1 (by rfl) ⟨2582900, by rfl⟩ : syracuseStep 3443867 = 5165801) B5165801
theorem B2583967 : Blo 1530462 2583967 := bstep (se 1 (by rfl) ⟨1937975, by rfl⟩ : syracuseStep 2583967 = 3875951) B3875951
theorem B3878351 : Blo 1530462 3878351 := bstep (se 1 (by rfl) ⟨2908763, by rfl⟩ : syracuseStep 3878351 = 5817527) B5817527
theorem B3681895 : Blo 1530462 3681895 := bstep (se 1 (by rfl) ⟨2761421, by rfl⟩ : syracuseStep 3681895 = 5522843) B5522843
theorem B3878887 : Blo 1530462 3878887 := bstep (se 1 (by rfl) ⟨2909165, by rfl⟩ : syracuseStep 3878887 = 5818331) B5818331
theorem B2297993 : Blo 1530462 2297993 := bstep (se 2 (by rfl) ⟨861747, by rfl⟩ : syracuseStep 2297993 = 1723495) B1723495
theorem B4903247 : Blo 1530462 4903247 := bstep (se 1 (by rfl) ⟨3677435, by rfl⟩ : syracuseStep 4903247 = 7354871) B7354871
theorem B4903631 : Blo 1530462 4903631 := bstep (se 1 (by rfl) ⟨3677723, by rfl⟩ : syracuseStep 4903631 = 7355447) B7355447
theorem B2298575 : Blo 1530462 2298575 := bstep (se 1 (by rfl) ⟨1723931, by rfl⟩ : syracuseStep 2298575 = 3447863) B3447863
theorem B2585371 : Blo 1530462 2585371 := bstep (se 1 (by rfl) ⟨1939028, by rfl⟩ : syracuseStep 2585371 = 3878057) B3878057
theorem B2585513 : Blo 1530462 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B51041297 : Blo 1530462 51041297 := bstep (se 2 (by rfl) ⟨19140486, by rfl⟩ : syracuseStep 51041297 = 38280973) B38280973
theorem B5166503 : Blo 1530462 5166503 := bstep (se 1 (by rfl) ⟨3874877, by rfl⟩ : syracuseStep 5166503 = 7749755) B7749755
theorem B5166611 : Blo 1530462 5166611 := bstep (se 1 (by rfl) ⟨3874958, by rfl⟩ : syracuseStep 5166611 = 7749917) B7749917
theorem B3446567 : Blo 1530462 3446567 := bstep (se 1 (by rfl) ⟨2584925, by rfl⟩ : syracuseStep 3446567 = 5169851) B5169851
theorem B3446783 : Blo 1530462 3446783 := bstep (se 1 (by rfl) ⟨2585087, by rfl⟩ : syracuseStep 3446783 = 5170175) B5170175
theorem B18618427 : Blo 1530462 18618427 := bstep (se 1 (by rfl) ⟨13963820, by rfl⟩ : syracuseStep 18618427 = 27927641) B27927641
theorem B5814611 : Blo 1530462 5814611 := bstep (se 1 (by rfl) ⟨4360958, by rfl⟩ : syracuseStep 5814611 = 8721917) B8721917
theorem B11630951 : Blo 1530462 11630951 := bstep (se 1 (by rfl) ⟨8723213, by rfl⟩ : syracuseStep 11630951 = 17446427) B17446427
theorem B5167529 : Blo 1530462 5167529 := bstep (se 2 (by rfl) ⟨1937823, by rfl⟩ : syracuseStep 5167529 = 3875647) B3875647
theorem B5167799 : Blo 1530462 5167799 := bstep (se 1 (by rfl) ⟨3875849, by rfl⟩ : syracuseStep 5167799 = 7751699) B7751699
theorem B9813001 : Blo 1530462 9813001 := bstep (se 2 (by rfl) ⟨3679875, by rfl⟩ : syracuseStep 9813001 = 7359751) B7359751
theorem B5307439 : Blo 1530462 5307439 := bstep (se 1 (by rfl) ⟨3980579, by rfl⟩ : syracuseStep 5307439 = 7961159) B7961159
theorem B1531295 : Blo 1530462 1531295 := bstep (se 1 (by rfl) ⟨1148471, by rfl⟩ : syracuseStep 1531295 = 2296943) B2296943
theorem B5168555 : Blo 1530462 5168555 := bstep (se 1 (by rfl) ⟨3876416, by rfl⟩ : syracuseStep 5168555 = 7752833) B7752833
theorem B1531327 : Blo 1530462 1531327 := bstep (se 1 (by rfl) ⟨1148495, by rfl⟩ : syracuseStep 1531327 = 2296991) B2296991
theorem B1531547 : Blo 1530462 1531547 := bstep (se 1 (by rfl) ⟨1148660, by rfl⟩ : syracuseStep 1531547 = 2297321) B2297321
theorem B11632409 : Blo 1530462 11632409 := bstep (se 2 (by rfl) ⟨4362153, by rfl⟩ : syracuseStep 11632409 = 8724307) B8724307
theorem B1531775 : Blo 1530462 1531775 := bstep (se 1 (by rfl) ⟨1148831, by rfl⟩ : syracuseStep 1531775 = 2297663) B2297663
theorem B5169095 : Blo 1530462 5169095 := bstep (se 1 (by rfl) ⟨3876821, by rfl⟩ : syracuseStep 5169095 = 7753643) B7753643
theorem B136110125 : Blo 1530462 136110125 := bstep (se 3 (by rfl) ⟨25520648, by rfl⟩ : syracuseStep 136110125 = 51041297) B51041297
theorem B1531995 : Blo 1530462 1531995 := bstep (se 1 (by rfl) ⟨1148996, by rfl⟩ : syracuseStep 1531995 = 2297993) B2297993
theorem B27926693 : Blo 1530462 27926693 := bstep (se 4 (by rfl) ⟨2618127, by rfl⟩ : syracuseStep 27926693 = 5236255) B5236255
theorem B3268831 : Blo 1530462 3268831 := bstep (se 1 (by rfl) ⟨2451623, by rfl⟩ : syracuseStep 3268831 = 4903247) B4903247
theorem B3269087 : Blo 1530462 3269087 := bstep (se 1 (by rfl) ⟨2451815, by rfl⟩ : syracuseStep 3269087 = 4903631) B4903631
theorem B1532383 : Blo 1530462 1532383 := bstep (se 1 (by rfl) ⟨1149287, by rfl⟩ : syracuseStep 1532383 = 2298575) B2298575
theorem B7750727 : Blo 1530462 7750727 := bstep (se 1 (by rfl) ⟨5813045, by rfl⟩ : syracuseStep 7750727 = 11626091) B11626091
theorem B5170337 : Blo 1530462 5170337 := bstep (se 2 (by rfl) ⟨1938876, by rfl⟩ : syracuseStep 5170337 = 3877753) B3877753
theorem B13084001 : Blo 1530462 13084001 := bstep (se 2 (by rfl) ⟨4906500, by rfl⟩ : syracuseStep 13084001 = 9813001) B9813001
theorem B3876407 : Blo 1530462 3876407 := bstep (se 1 (by rfl) ⟨2907305, by rfl⟩ : syracuseStep 3876407 = 5814611) B5814611
theorem B2180935 : Blo 1530462 2180935 := bstep (se 1 (by rfl) ⟨1635701, by rfl⟩ : syracuseStep 2180935 = 3271403) B3271403
theorem B2295719 : Blo 1530462 2295719 := bstep (se 1 (by rfl) ⟨1721789, by rfl⟩ : syracuseStep 2295719 = 3443579) B3443579
theorem B2295911 : Blo 1530462 2295911 := bstep (se 1 (by rfl) ⟨1721933, by rfl⟩ : syracuseStep 2295911 = 3443867) B3443867
theorem B4909193 : Blo 1530462 4909193 := bstep (se 2 (by rfl) ⟨1840947, by rfl⟩ : syracuseStep 4909193 = 3681895) B3681895
theorem B5171849 : Blo 1530462 5171849 := bstep (se 2 (by rfl) ⟨1939443, by rfl⟩ : syracuseStep 5171849 = 3878887) B3878887
theorem B44157581 : Blo 1530462 44157581 := bstep (se 3 (by rfl) ⟨8279546, by rfl⟩ : syracuseStep 44157581 = 16559093) B16559093
theorem B8719001 : Blo 1530462 8719001 := bstep (se 2 (by rfl) ⟨3269625, by rfl⟩ : syracuseStep 8719001 = 6539251) B6539251
theorem B24824569 : Blo 1530462 24824569 := bstep (se 2 (by rfl) ⟨9309213, by rfl⟩ : syracuseStep 24824569 = 18618427) B18618427
theorem B2583535 : Blo 1530462 2583535 := bstep (se 1 (by rfl) ⟨1937651, by rfl⟩ : syracuseStep 2583535 = 3875303) B3875303
theorem B1723675 : Blo 1530462 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B2452943 : Blo 1530462 2452943 := bstep (se 1 (by rfl) ⟨1839707, by rfl⟩ : syracuseStep 2452943 = 3679415) B3679415
theorem B3444335 : Blo 1530462 3444335 := bstep (se 1 (by rfl) ⟨2583251, by rfl⟩ : syracuseStep 3444335 = 5166503) B5166503
theorem B3444407 : Blo 1530462 3444407 := bstep (se 1 (by rfl) ⟨2583305, by rfl⟩ : syracuseStep 3444407 = 5166611) B5166611
theorem B2297711 : Blo 1530462 2297711 := bstep (se 1 (by rfl) ⟨1723283, by rfl⟩ : syracuseStep 2297711 = 3446567) B3446567
theorem B2297855 : Blo 1530462 2297855 := bstep (se 1 (by rfl) ⟨1723391, by rfl⟩ : syracuseStep 2297855 = 3446783) B3446783
theorem B7753967 : Blo 1530462 7753967 := bstep (se 1 (by rfl) ⟨5815475, by rfl⟩ : syracuseStep 7753967 = 11630951) B11630951
theorem B3445019 : Blo 1530462 3445019 := bstep (se 1 (by rfl) ⟨2583764, by rfl⟩ : syracuseStep 3445019 = 5167529) B5167529
theorem B6205835 : Blo 1530462 6205835 := bstep (se 1 (by rfl) ⟨4654376, by rfl⟩ : syracuseStep 6205835 = 9308753) B9308753
theorem B3445199 : Blo 1530462 3445199 := bstep (se 1 (by rfl) ⟨2583899, by rfl⟩ : syracuseStep 3445199 = 5167799) B5167799
theorem B3445289 : Blo 1530462 3445289 := bstep (se 2 (by rfl) ⟨1291983, by rfl⟩ : syracuseStep 3445289 = 2583967) B2583967
theorem B3445703 : Blo 1530462 3445703 := bstep (se 1 (by rfl) ⟨2584277, by rfl⟩ : syracuseStep 3445703 = 5168555) B5168555
theorem B2585567 : Blo 1530462 2585567 := bstep (se 1 (by rfl) ⟨1939175, by rfl⟩ : syracuseStep 2585567 = 3878351) B3878351
theorem B7754939 : Blo 1530462 7754939 := bstep (se 1 (by rfl) ⟨5816204, by rfl⟩ : syracuseStep 7754939 = 11632409) B11632409
theorem B3446063 : Blo 1530462 3446063 := bstep (se 1 (by rfl) ⟨2584547, by rfl⟩ : syracuseStep 3446063 = 5169095) B5169095
theorem B3447161 : Blo 1530462 3447161 := bstep (se 2 (by rfl) ⟨1292685, by rfl⟩ : syracuseStep 3447161 = 2585371) B2585371
theorem B6543983 : Blo 1530462 6543983 := bstep (se 1 (by rfl) ⟨4907987, by rfl⟩ : syracuseStep 6543983 = 9815975) B9815975
theorem B7076585 : Blo 1530462 7076585 := bstep (se 2 (by rfl) ⟨2653719, by rfl⟩ : syracuseStep 7076585 = 5307439) B5307439
theorem B1530623 : Blo 1530462 1530623 := bstep (se 1 (by rfl) ⟨1147967, by rfl⟩ : syracuseStep 1530623 = 2295935) B2295935
theorem B14719967 : Blo 1530462 14719967 := bstep (se 1 (by rfl) ⟨11039975, by rfl⟩ : syracuseStep 14719967 = 22079951) B22079951
theorem B1530879 : Blo 1530462 1530879 := bstep (se 1 (by rfl) ⟨1148159, by rfl⟩ : syracuseStep 1530879 = 2296319) B2296319
theorem B3447935 : Blo 1530462 3447935 := bstep (se 1 (by rfl) ⟨2585951, by rfl⟩ : syracuseStep 3447935 = 5171903) B5171903
theorem B1531183 : Blo 1530462 1531183 := bstep (se 1 (by rfl) ⟨1148387, by rfl⟩ : syracuseStep 1531183 = 2296775) B2296775
theorem B16145981 : Blo 1530462 16145981 := bstep (se 3 (by rfl) ⟨3027371, by rfl⟩ : syracuseStep 16145981 = 6054743) B6054743
theorem B5169311 : Blo 1530462 5169311 := bstep (se 1 (by rfl) ⟨3876983, by rfl⟩ : syracuseStep 5169311 = 7753967) B7753967
theorem B4358441 : Blo 1530462 4358441 := bstep (se 2 (by rfl) ⟨1634415, by rfl⟩ : syracuseStep 4358441 = 3268831) B3268831
theorem B2179391 : Blo 1530462 2179391 := bstep (se 1 (by rfl) ⟨1634543, by rfl⟩ : syracuseStep 2179391 = 3269087) B3269087
theorem B5169959 : Blo 1530462 5169959 := bstep (se 1 (by rfl) ⟨3877469, by rfl⟩ : syracuseStep 5169959 = 7754939) B7754939
theorem B16548893 : Blo 1530462 16548893 := bstep (se 3 (by rfl) ⟨3102917, by rfl⟩ : syracuseStep 16548893 = 6205835) B6205835
theorem B2296223 : Blo 1530462 2296223 := bstep (se 1 (by rfl) ⟨1722167, by rfl⟩ : syracuseStep 2296223 = 3444335) B3444335
theorem B2296271 : Blo 1530462 2296271 := bstep (se 1 (by rfl) ⟨1722203, by rfl⟩ : syracuseStep 2296271 = 3444407) B3444407
theorem B2296679 : Blo 1530462 2296679 := bstep (se 1 (by rfl) ⟨1722509, by rfl⟩ : syracuseStep 2296679 = 3445019) B3445019
theorem B2296799 : Blo 1530462 2296799 := bstep (se 1 (by rfl) ⟨1722599, by rfl⟩ : syracuseStep 2296799 = 3445199) B3445199
theorem B2296859 : Blo 1530462 2296859 := bstep (se 1 (by rfl) ⟨1722644, by rfl⟩ : syracuseStep 2296859 = 3445289) B3445289
theorem B2297135 : Blo 1530462 2297135 := bstep (se 1 (by rfl) ⟨1722851, by rfl⟩ : syracuseStep 2297135 = 3445703) B3445703
theorem B1723711 : Blo 1530462 1723711 := bstep (se 1 (by rfl) ⟨1292783, by rfl⟩ : syracuseStep 1723711 = 2585567) B2585567
theorem B2297375 : Blo 1530462 2297375 := bstep (se 1 (by rfl) ⟨1723031, by rfl⟩ : syracuseStep 2297375 = 3446063) B3446063
theorem B33099425 : Blo 1530462 33099425 := bstep (se 2 (by rfl) ⟨12412284, by rfl⟩ : syracuseStep 33099425 = 24824569) B24824569
theorem B2584271 : Blo 1530462 2584271 := bstep (se 1 (by rfl) ⟨1938203, by rfl⟩ : syracuseStep 2584271 = 3876407) B3876407
theorem B6541181 : Blo 1530462 6541181 := bstep (se 3 (by rfl) ⟨1226471, by rfl⟩ : syracuseStep 6541181 = 2452943) B2452943
theorem B3444713 : Blo 1530462 3444713 := bstep (se 2 (by rfl) ⟨1291767, by rfl⟩ : syracuseStep 3444713 = 2583535) B2583535
theorem B3272795 : Blo 1530462 3272795 := bstep (se 1 (by rfl) ⟨2454596, by rfl⟩ : syracuseStep 3272795 = 4909193) B4909193
theorem B2298107 : Blo 1530462 2298107 := bstep (se 1 (by rfl) ⟨1723580, by rfl⟩ : syracuseStep 2298107 = 3447161) B3447161
theorem B2298233 : Blo 1530462 2298233 := bstep (se 2 (by rfl) ⟨861837, by rfl⟩ : syracuseStep 2298233 = 1723675) B1723675
theorem B4362655 : Blo 1530462 4362655 := bstep (se 1 (by rfl) ⟨3271991, by rfl⟩ : syracuseStep 4362655 = 6543983) B6543983
theorem B29438387 : Blo 1530462 29438387 := bstep (se 1 (by rfl) ⟨22078790, by rfl⟩ : syracuseStep 29438387 = 44157581) B44157581
theorem B5812667 : Blo 1530462 5812667 := bstep (se 1 (by rfl) ⟨4359500, by rfl⟩ : syracuseStep 5812667 = 8719001) B8719001
theorem B18870893 : Blo 1530462 18870893 := bstep (se 3 (by rfl) ⟨3538292, by rfl⟩ : syracuseStep 18870893 = 7076585) B7076585
theorem B2298623 : Blo 1530462 2298623 := bstep (se 1 (by rfl) ⟨1723967, by rfl⟩ : syracuseStep 2298623 = 3447935) B3447935
theorem B90740083 : Blo 1530462 90740083 := bstep (se 1 (by rfl) ⟨68055062, by rfl⟩ : syracuseStep 90740083 = 136110125) B136110125
theorem B18617795 : Blo 1530462 18617795 := bstep (se 1 (by rfl) ⟨13963346, by rfl⟩ : syracuseStep 18617795 = 27926693) B27926693
theorem B5167151 : Blo 1530462 5167151 := bstep (se 1 (by rfl) ⟨3875363, by rfl⟩ : syracuseStep 5167151 = 7750727) B7750727
theorem B3446891 : Blo 1530462 3446891 := bstep (se 1 (by rfl) ⟨2585168, by rfl⟩ : syracuseStep 3446891 = 5170337) B5170337
theorem B8722667 : Blo 1530462 8722667 := bstep (se 1 (by rfl) ⟨6542000, by rfl⟩ : syracuseStep 8722667 = 13084001) B13084001
theorem B1530479 : Blo 1530462 1530479 := bstep (se 1 (by rfl) ⟨1147859, by rfl⟩ : syracuseStep 1530479 = 2295719) B2295719
theorem B1530607 : Blo 1530462 1530607 := bstep (se 1 (by rfl) ⟨1147955, by rfl⟩ : syracuseStep 1530607 = 2295911) B2295911
theorem B3447899 : Blo 1530462 3447899 := bstep (se 1 (by rfl) ⟨2585924, by rfl⟩ : syracuseStep 3447899 = 5171849) B5171849
theorem B9813311 : Blo 1530462 9813311 := bstep (se 1 (by rfl) ⟨7359983, by rfl⟩ : syracuseStep 9813311 = 14719967) B14719967
theorem B10763987 : Blo 1530462 10763987 := bstep (se 1 (by rfl) ⟨8072990, by rfl⟩ : syracuseStep 10763987 = 16145981) B16145981
theorem B2907913 : Blo 1530462 2907913 := bstep (se 2 (by rfl) ⟨1090467, by rfl⟩ : syracuseStep 2907913 = 2180935) B2180935
theorem B1531807 : Blo 1530462 1531807 := bstep (se 1 (by rfl) ⟨1148855, by rfl⟩ : syracuseStep 1531807 = 2297711) B2297711
theorem B1531903 : Blo 1530462 1531903 := bstep (se 1 (by rfl) ⟨1148927, by rfl⟩ : syracuseStep 1531903 = 2297855) B2297855
theorem B1532071 : Blo 1530462 1532071 := bstep (se 1 (by rfl) ⟨1149053, by rfl⟩ : syracuseStep 1532071 = 2298107) B2298107
theorem B1532155 : Blo 1530462 1532155 := bstep (se 1 (by rfl) ⟨1149116, by rfl⟩ : syracuseStep 1532155 = 2298233) B2298233
theorem B3875111 : Blo 1530462 3875111 := bstep (se 1 (by rfl) ⟨2906333, by rfl⟩ : syracuseStep 3875111 = 5812667) B5812667
theorem B1532415 : Blo 1530462 1532415 := bstep (se 1 (by rfl) ⟨1149311, by rfl⟩ : syracuseStep 1532415 = 2298623) B2298623
theorem B5816873 : Blo 1530462 5816873 := bstep (se 2 (by rfl) ⟨2181327, by rfl⟩ : syracuseStep 5816873 = 4362655) B4362655
theorem B12411863 : Blo 1530462 12411863 := bstep (se 1 (by rfl) ⟨9308897, by rfl⟩ : syracuseStep 12411863 = 18617795) B18617795
theorem B3877217 : Blo 1530462 3877217 := bstep (se 2 (by rfl) ⟨1453956, by rfl⟩ : syracuseStep 3877217 = 2907913) B2907913
theorem B1722847 : Blo 1530462 1722847 := bstep (se 1 (by rfl) ⟨1292135, by rfl⟩ : syracuseStep 1722847 = 2584271) B2584271
theorem B4360787 : Blo 1530462 4360787 := bstep (se 1 (by rfl) ⟨3270590, by rfl⟩ : syracuseStep 4360787 = 6541181) B6541181
theorem B2296475 : Blo 1530462 2296475 := bstep (se 1 (by rfl) ⟨1722356, by rfl⟩ : syracuseStep 2296475 = 3444713) B3444713
theorem B2181863 : Blo 1530462 2181863 := bstep (se 1 (by rfl) ⟨1636397, by rfl⟩ : syracuseStep 2181863 = 3272795) B3272795
theorem B5811709 : Blo 1530462 5811709 := bstep (se 3 (by rfl) ⟨1089695, by rfl⟩ : syracuseStep 5811709 = 2179391) B2179391
theorem B3444767 : Blo 1530462 3444767 := bstep (se 1 (by rfl) ⟨2583575, by rfl⟩ : syracuseStep 3444767 = 5167151) B5167151
theorem B2297927 : Blo 1530462 2297927 := bstep (se 1 (by rfl) ⟨1723445, by rfl⟩ : syracuseStep 2297927 = 3446891) B3446891
theorem B2298281 : Blo 1530462 2298281 := bstep (se 2 (by rfl) ⟨861855, by rfl⟩ : syracuseStep 2298281 = 1723711) B1723711
theorem B2298599 : Blo 1530462 2298599 := bstep (se 1 (by rfl) ⟨1723949, by rfl⟩ : syracuseStep 2298599 = 3447899) B3447899
theorem B6542207 : Blo 1530462 6542207 := bstep (se 1 (by rfl) ⟨4906655, by rfl⟩ : syracuseStep 6542207 = 9813311) B9813311
theorem B22066283 : Blo 1530462 22066283 := bstep (se 1 (by rfl) ⟨16549712, by rfl⟩ : syracuseStep 22066283 = 33099425) B33099425
theorem B3446207 : Blo 1530462 3446207 := bstep (se 1 (by rfl) ⟨2584655, by rfl⟩ : syracuseStep 3446207 = 5169311) B5169311
theorem B2905627 : Blo 1530462 2905627 := bstep (se 1 (by rfl) ⟨2179220, by rfl⟩ : syracuseStep 2905627 = 4358441) B4358441
theorem B19625591 : Blo 1530462 19625591 := bstep (se 1 (by rfl) ⟨14719193, by rfl⟩ : syracuseStep 19625591 = 29438387) B29438387
theorem B12580595 : Blo 1530462 12580595 := bstep (se 1 (by rfl) ⟨9435446, by rfl⟩ : syracuseStep 12580595 = 18870893) B18870893
theorem B3446639 : Blo 1530462 3446639 := bstep (se 1 (by rfl) ⟨2584979, by rfl⟩ : syracuseStep 3446639 = 5169959) B5169959
theorem B11032595 : Blo 1530462 11032595 := bstep (se 1 (by rfl) ⟨8274446, by rfl⟩ : syracuseStep 11032595 = 16548893) B16548893
theorem B5815111 : Blo 1530462 5815111 := bstep (se 1 (by rfl) ⟨4361333, by rfl⟩ : syracuseStep 5815111 = 8722667) B8722667
theorem B1530815 : Blo 1530462 1530815 := bstep (se 1 (by rfl) ⟨1148111, by rfl⟩ : syracuseStep 1530815 = 2296223) B2296223
theorem B1530847 : Blo 1530462 1530847 := bstep (se 1 (by rfl) ⟨1148135, by rfl⟩ : syracuseStep 1530847 = 2296271) B2296271
theorem B120986777 : Blo 1530462 120986777 := bstep (se 2 (by rfl) ⟨45370041, by rfl⟩ : syracuseStep 120986777 = 90740083) B90740083
theorem B28703965 : Blo 1530462 28703965 := bstep (se 3 (by rfl) ⟨5381993, by rfl⟩ : syracuseStep 28703965 = 10763987) B10763987
theorem B1531119 : Blo 1530462 1531119 := bstep (se 1 (by rfl) ⟨1148339, by rfl⟩ : syracuseStep 1531119 = 2296679) B2296679
theorem B1531199 : Blo 1530462 1531199 := bstep (se 1 (by rfl) ⟨1148399, by rfl⟩ : syracuseStep 1531199 = 2296799) B2296799
theorem B1531239 : Blo 1530462 1531239 := bstep (se 1 (by rfl) ⟨1148429, by rfl⟩ : syracuseStep 1531239 = 2296859) B2296859
theorem B1531423 : Blo 1530462 1531423 := bstep (se 1 (by rfl) ⟨1148567, by rfl⟩ : syracuseStep 1531423 = 2297135) B2297135
theorem B1531583 : Blo 1530462 1531583 := bstep (se 1 (by rfl) ⟨1148687, by rfl⟩ : syracuseStep 1531583 = 2297375) B2297375
theorem B1531951 : Blo 1530462 1531951 := bstep (se 1 (by rfl) ⟨1148963, by rfl⟩ : syracuseStep 1531951 = 2297927) B2297927
theorem B1532187 : Blo 1530462 1532187 := bstep (se 1 (by rfl) ⟨1149140, by rfl⟩ : syracuseStep 1532187 = 2298281) B2298281
theorem B1532399 : Blo 1530462 1532399 := bstep (se 1 (by rfl) ⟨1149299, by rfl⟩ : syracuseStep 1532399 = 2298599) B2298599
theorem B8274575 : Blo 1530462 8274575 := bstep (se 1 (by rfl) ⟨6205931, by rfl⟩ : syracuseStep 8274575 = 12411863) B12411863
theorem B13083727 : Blo 1530462 13083727 := bstep (se 1 (by rfl) ⟨9812795, by rfl⟩ : syracuseStep 13083727 = 19625591) B19625591
theorem B5818301 : Blo 1530462 5818301 := bstep (se 3 (by rfl) ⟨1090931, by rfl⟩ : syracuseStep 5818301 = 2181863) B2181863
theorem B2296511 : Blo 1530462 2296511 := bstep (se 1 (by rfl) ⟨1722383, by rfl⟩ : syracuseStep 2296511 = 3444767) B3444767
theorem B2583407 : Blo 1530462 2583407 := bstep (se 1 (by rfl) ⟨1937555, by rfl⟩ : syracuseStep 2583407 = 3875111) B3875111
theorem B3877915 : Blo 1530462 3877915 := bstep (se 1 (by rfl) ⟨2908436, by rfl⟩ : syracuseStep 3877915 = 5816873) B5816873
theorem B4361471 : Blo 1530462 4361471 := bstep (se 1 (by rfl) ⟨3271103, by rfl⟩ : syracuseStep 4361471 = 6542207) B6542207
theorem B2297129 : Blo 1530462 2297129 := bstep (se 2 (by rfl) ⟨861423, by rfl⟩ : syracuseStep 2297129 = 1722847) B1722847
theorem B2297471 : Blo 1530462 2297471 := bstep (se 1 (by rfl) ⟨1723103, by rfl⟩ : syracuseStep 2297471 = 3446207) B3446207
theorem B7753481 : Blo 1530462 7753481 := bstep (se 2 (by rfl) ⟨2907555, by rfl⟩ : syracuseStep 7753481 = 5815111) B5815111
theorem B2297759 : Blo 1530462 2297759 := bstep (se 1 (by rfl) ⟨1723319, by rfl⟩ : syracuseStep 2297759 = 3446639) B3446639
theorem B2584811 : Blo 1530462 2584811 := bstep (se 1 (by rfl) ⟨1938608, by rfl⟩ : syracuseStep 2584811 = 3877217) B3877217
theorem B14710855 : Blo 1530462 14710855 := bstep (se 1 (by rfl) ⟨11033141, by rfl⟩ : syracuseStep 14710855 = 22066283) B22066283
theorem B8387063 : Blo 1530462 8387063 := bstep (se 1 (by rfl) ⟨6290297, by rfl⟩ : syracuseStep 8387063 = 12580595) B12580595
theorem B7355063 : Blo 1530462 7355063 := bstep (se 1 (by rfl) ⟨5516297, by rfl⟩ : syracuseStep 7355063 = 11032595) B11032595
theorem B38271953 : Blo 1530462 38271953 := bstep (se 2 (by rfl) ⟨14351982, by rfl⟩ : syracuseStep 38271953 = 28703965) B28703965
theorem B2907191 : Blo 1530462 2907191 := bstep (se 1 (by rfl) ⟨2180393, by rfl⟩ : syracuseStep 2907191 = 4360787) B4360787
theorem B1530983 : Blo 1530462 1530983 := bstep (se 1 (by rfl) ⟨1148237, by rfl⟩ : syracuseStep 1530983 = 2296475) B2296475
theorem B7748945 : Blo 1530462 7748945 := bstep (se 2 (by rfl) ⟨2905854, by rfl⟩ : syracuseStep 7748945 = 5811709) B5811709
theorem B3874169 : Blo 1530462 3874169 := bstep (se 2 (by rfl) ⟨1452813, by rfl⟩ : syracuseStep 3874169 = 2905627) B2905627
theorem B80657851 : Blo 1530462 80657851 := bstep (se 1 (by rfl) ⟨60493388, by rfl⟩ : syracuseStep 80657851 = 120986777) B120986777
theorem B5170553 : Blo 1530462 5170553 := bstep (se 2 (by rfl) ⟨1938957, by rfl⟩ : syracuseStep 5170553 = 3877915) B3877915
theorem B1722271 : Blo 1530462 1722271 := bstep (se 1 (by rfl) ⟨1291703, by rfl⟩ : syracuseStep 1722271 = 2583407) B2583407
theorem B2582779 : Blo 1530462 2582779 := bstep (se 1 (by rfl) ⟨1937084, by rfl⟩ : syracuseStep 2582779 = 3874169) B3874169
theorem B102058541 : Blo 1530462 102058541 := bstep (se 3 (by rfl) ⟨19135976, by rfl⟩ : syracuseStep 102058541 = 38271953) B38271953
theorem B19614473 : Blo 1530462 19614473 := bstep (se 2 (by rfl) ⟨7355427, by rfl⟩ : syracuseStep 19614473 = 14710855) B14710855
theorem B7752509 : Blo 1530462 7752509 := bstep (se 3 (by rfl) ⟨1453595, by rfl⟩ : syracuseStep 7752509 = 2907191) B2907191
theorem B1723207 : Blo 1530462 1723207 := bstep (se 1 (by rfl) ⟨1292405, by rfl⟩ : syracuseStep 1723207 = 2584811) B2584811
theorem B3878867 : Blo 1530462 3878867 := bstep (se 1 (by rfl) ⟨2909150, by rfl⟩ : syracuseStep 3878867 = 5818301) B5818301
theorem B17444969 : Blo 1530462 17444969 := bstep (se 2 (by rfl) ⟨6541863, by rfl⟩ : syracuseStep 17444969 = 13083727) B13083727
theorem B5591375 : Blo 1530462 5591375 := bstep (se 1 (by rfl) ⟨4193531, by rfl⟩ : syracuseStep 5591375 = 8387063) B8387063
theorem B22065533 : Blo 1530462 22065533 := bstep (se 3 (by rfl) ⟨4137287, by rfl⟩ : syracuseStep 22065533 = 8274575) B8274575
theorem B4903375 : Blo 1530462 4903375 := bstep (se 1 (by rfl) ⟨3677531, by rfl⟩ : syracuseStep 4903375 = 7355063) B7355063
theorem B5165963 : Blo 1530462 5165963 := bstep (se 1 (by rfl) ⟨3874472, by rfl⟩ : syracuseStep 5165963 = 7748945) B7748945
theorem B1531007 : Blo 1530462 1531007 := bstep (se 1 (by rfl) ⟨1148255, by rfl⟩ : syracuseStep 1531007 = 2296511) B2296511
theorem B107543801 : Blo 1530462 107543801 := bstep (se 2 (by rfl) ⟨40328925, by rfl⟩ : syracuseStep 107543801 = 80657851) B80657851
theorem B2907647 : Blo 1530462 2907647 := bstep (se 1 (by rfl) ⟨2180735, by rfl⟩ : syracuseStep 2907647 = 4361471) B4361471
theorem B1531419 : Blo 1530462 1531419 := bstep (se 1 (by rfl) ⟨1148564, by rfl⟩ : syracuseStep 1531419 = 2297129) B2297129
theorem B1531647 : Blo 1530462 1531647 := bstep (se 1 (by rfl) ⟨1148735, by rfl⟩ : syracuseStep 1531647 = 2297471) B2297471
theorem B5168987 : Blo 1530462 5168987 := bstep (se 1 (by rfl) ⟨3876740, by rfl⟩ : syracuseStep 5168987 = 7753481) B7753481
theorem B1531839 : Blo 1530462 1531839 := bstep (se 1 (by rfl) ⟨1148879, by rfl⟩ : syracuseStep 1531839 = 2297759) B2297759
theorem B3727583 : Blo 1530462 3727583 := bstep (se 1 (by rfl) ⟨2795687, by rfl⟩ : syracuseStep 3727583 = 5591375) B5591375
theorem B6537833 : Blo 1530462 6537833 := bstep (se 2 (by rfl) ⟨2451687, by rfl⟩ : syracuseStep 6537833 = 4903375) B4903375
theorem B13076315 : Blo 1530462 13076315 := bstep (se 1 (by rfl) ⟨9807236, by rfl⟩ : syracuseStep 13076315 = 19614473) B19614473
theorem B2296361 : Blo 1530462 2296361 := bstep (se 2 (by rfl) ⟨861135, by rfl⟩ : syracuseStep 2296361 = 1722271) B1722271
theorem B3443705 : Blo 1530462 3443705 := bstep (se 2 (by rfl) ⟨1291389, by rfl⟩ : syracuseStep 3443705 = 2582779) B2582779
theorem B3443975 : Blo 1530462 3443975 := bstep (se 1 (by rfl) ⟨2582981, by rfl⟩ : syracuseStep 3443975 = 5165963) B5165963
theorem B2297609 : Blo 1530462 2297609 := bstep (se 2 (by rfl) ⟨861603, by rfl⟩ : syracuseStep 2297609 = 1723207) B1723207
theorem B68039027 : Blo 1530462 68039027 := bstep (se 1 (by rfl) ⟨51029270, by rfl⟩ : syracuseStep 68039027 = 102058541) B102058541
theorem B1938431 : Blo 1530462 1938431 := bstep (se 1 (by rfl) ⟨1453823, by rfl⟩ : syracuseStep 1938431 = 2907647) B2907647
theorem B3445991 : Blo 1530462 3445991 := bstep (se 1 (by rfl) ⟨2584493, by rfl⟩ : syracuseStep 3445991 = 5168987) B5168987
theorem B2585911 : Blo 1530462 2585911 := bstep (se 1 (by rfl) ⟨1939433, by rfl⟩ : syracuseStep 2585911 = 3878867) B3878867
theorem B11629979 : Blo 1530462 11629979 := bstep (se 1 (by rfl) ⟨8722484, by rfl⟩ : syracuseStep 11629979 = 17444969) B17444969
theorem B14710355 : Blo 1530462 14710355 := bstep (se 1 (by rfl) ⟨11032766, by rfl⟩ : syracuseStep 14710355 = 22065533) B22065533
theorem B3447035 : Blo 1530462 3447035 := bstep (se 1 (by rfl) ⟨2585276, by rfl⟩ : syracuseStep 3447035 = 5170553) B5170553
theorem B5168339 : Blo 1530462 5168339 := bstep (se 1 (by rfl) ⟨3876254, by rfl⟩ : syracuseStep 5168339 = 7752509) B7752509
theorem B71695867 : Blo 1530462 71695867 := bstep (se 1 (by rfl) ⟨53771900, by rfl⟩ : syracuseStep 71695867 = 107543801) B107543801
theorem B45359351 : Blo 1530462 45359351 := bstep (se 1 (by rfl) ⟨34019513, by rfl⟩ : syracuseStep 45359351 = 68039027) B68039027
theorem B4358555 : Blo 1530462 4358555 := bstep (se 1 (by rfl) ⟨3268916, by rfl⟩ : syracuseStep 4358555 = 6537833) B6537833
theorem B9806903 : Blo 1530462 9806903 := bstep (se 1 (by rfl) ⟨7355177, by rfl⟩ : syracuseStep 9806903 = 14710355) B14710355
theorem B8717543 : Blo 1530462 8717543 := bstep (se 1 (by rfl) ⟨6538157, by rfl⟩ : syracuseStep 8717543 = 13076315) B13076315
theorem B95594489 : Blo 1530462 95594489 := bstep (se 2 (by rfl) ⟨35847933, by rfl⟩ : syracuseStep 95594489 = 71695867) B71695867
theorem B2295803 : Blo 1530462 2295803 := bstep (se 1 (by rfl) ⟨1721852, by rfl⟩ : syracuseStep 2295803 = 3443705) B3443705
theorem B2295983 : Blo 1530462 2295983 := bstep (se 1 (by rfl) ⟨1721987, by rfl⟩ : syracuseStep 2295983 = 3443975) B3443975
theorem B2485055 : Blo 1530462 2485055 := bstep (se 1 (by rfl) ⟨1863791, by rfl⟩ : syracuseStep 2485055 = 3727583) B3727583
theorem B2297327 : Blo 1530462 2297327 := bstep (se 1 (by rfl) ⟨1722995, by rfl⟩ : syracuseStep 2297327 = 3445991) B3445991
theorem B7753319 : Blo 1530462 7753319 := bstep (se 1 (by rfl) ⟨5814989, by rfl⟩ : syracuseStep 7753319 = 11629979) B11629979
theorem B2298023 : Blo 1530462 2298023 := bstep (se 1 (by rfl) ⟨1723517, by rfl⟩ : syracuseStep 2298023 = 3447035) B3447035
theorem B3445559 : Blo 1530462 3445559 := bstep (se 1 (by rfl) ⟨2584169, by rfl⟩ : syracuseStep 3445559 = 5168339) B5168339
theorem B1530907 : Blo 1530462 1530907 := bstep (se 1 (by rfl) ⟨1148180, by rfl⟩ : syracuseStep 1530907 = 2296361) B2296361
theorem B3447881 : Blo 1530462 3447881 := bstep (se 2 (by rfl) ⟨1292955, by rfl⟩ : syracuseStep 3447881 = 2585911) B2585911
theorem B1531739 : Blo 1530462 1531739 := bstep (se 1 (by rfl) ⟨1148804, by rfl⟩ : syracuseStep 1531739 = 2297609) B2297609
theorem B5169149 : Blo 1530462 5169149 := bstep (se 3 (by rfl) ⟨969215, by rfl⟩ : syracuseStep 5169149 = 1938431) B1938431
theorem B1532015 : Blo 1530462 1532015 := bstep (se 1 (by rfl) ⟨1149011, by rfl⟩ : syracuseStep 1532015 = 2298023) B2298023
theorem B6537935 : Blo 1530462 6537935 := bstep (se 1 (by rfl) ⟨4903451, by rfl⟩ : syracuseStep 6537935 = 9806903) B9806903
theorem B1656703 : Blo 1530462 1656703 := bstep (se 1 (by rfl) ⟨1242527, by rfl⟩ : syracuseStep 1656703 = 2485055) B2485055
theorem B30239567 : Blo 1530462 30239567 := bstep (se 1 (by rfl) ⟨22679675, by rfl⟩ : syracuseStep 30239567 = 45359351) B45359351
theorem B2297039 : Blo 1530462 2297039 := bstep (se 1 (by rfl) ⟨1722779, by rfl⟩ : syracuseStep 2297039 = 3445559) B3445559
theorem B5811695 : Blo 1530462 5811695 := bstep (se 1 (by rfl) ⟨4358771, by rfl⟩ : syracuseStep 5811695 = 8717543) B8717543
theorem B63729659 : Blo 1530462 63729659 := bstep (se 1 (by rfl) ⟨47797244, by rfl⟩ : syracuseStep 63729659 = 95594489) B95594489
theorem B2298587 : Blo 1530462 2298587 := bstep (se 1 (by rfl) ⟨1723940, by rfl⟩ : syracuseStep 2298587 = 3447881) B3447881
theorem B3446099 : Blo 1530462 3446099 := bstep (se 1 (by rfl) ⟨2584574, by rfl⟩ : syracuseStep 3446099 = 5169149) B5169149
theorem B2905703 : Blo 1530462 2905703 := bstep (se 1 (by rfl) ⟨2179277, by rfl⟩ : syracuseStep 2905703 = 4358555) B4358555
theorem B1530535 : Blo 1530462 1530535 := bstep (se 1 (by rfl) ⟨1147901, by rfl⟩ : syracuseStep 1530535 = 2295803) B2295803
theorem B1530655 : Blo 1530462 1530655 := bstep (se 1 (by rfl) ⟨1147991, by rfl⟩ : syracuseStep 1530655 = 2295983) B2295983
theorem B1531551 : Blo 1530462 1531551 := bstep (se 1 (by rfl) ⟨1148663, by rfl⟩ : syracuseStep 1531551 = 2297327) B2297327
theorem B5168879 : Blo 1530462 5168879 := bstep (se 1 (by rfl) ⟨3876659, by rfl⟩ : syracuseStep 5168879 = 7753319) B7753319
theorem B4358623 : Blo 1530462 4358623 := bstep (se 1 (by rfl) ⟨3268967, by rfl⟩ : syracuseStep 4358623 = 6537935) B6537935
theorem B1532391 : Blo 1530462 1532391 := bstep (se 1 (by rfl) ⟨1149293, by rfl⟩ : syracuseStep 1532391 = 2298587) B2298587
theorem B42486439 : Blo 1530462 42486439 := bstep (se 1 (by rfl) ⟨31864829, by rfl⟩ : syracuseStep 42486439 = 63729659) B63729659
theorem B2297399 : Blo 1530462 2297399 := bstep (se 1 (by rfl) ⟨1723049, by rfl⟩ : syracuseStep 2297399 = 3446099) B3446099
theorem B1937135 : Blo 1530462 1937135 := bstep (se 1 (by rfl) ⟨1452851, by rfl⟩ : syracuseStep 1937135 = 2905703) B2905703
theorem B3445919 : Blo 1530462 3445919 := bstep (se 1 (by rfl) ⟨2584439, by rfl⟩ : syracuseStep 3445919 = 5168879) B5168879
theorem B2208937 : Blo 1530462 2208937 := bstep (se 2 (by rfl) ⟨828351, by rfl⟩ : syracuseStep 2208937 = 1656703) B1656703
theorem B20159711 : Blo 1530462 20159711 := bstep (se 1 (by rfl) ⟨15119783, by rfl⟩ : syracuseStep 20159711 = 30239567) B30239567
theorem B1531359 : Blo 1530462 1531359 := bstep (se 1 (by rfl) ⟨1148519, by rfl⟩ : syracuseStep 1531359 = 2297039) B2297039
theorem B3874463 : Blo 1530462 3874463 := bstep (se 1 (by rfl) ⟨2905847, by rfl⟩ : syracuseStep 3874463 = 5811695) B5811695
theorem B56648585 : Blo 1530462 56648585 := bstep (se 2 (by rfl) ⟨21243219, by rfl⟩ : syracuseStep 56648585 = 42486439) B42486439
theorem B2582975 : Blo 1530462 2582975 := bstep (se 1 (by rfl) ⟨1937231, by rfl⟩ : syracuseStep 2582975 = 3874463) B3874463
theorem B5811497 : Blo 1530462 5811497 := bstep (se 2 (by rfl) ⟨2179311, by rfl⟩ : syracuseStep 5811497 = 4358623) B4358623
theorem B2297279 : Blo 1530462 2297279 := bstep (se 1 (by rfl) ⟨1722959, by rfl⟩ : syracuseStep 2297279 = 3445919) B3445919
theorem B2945249 : Blo 1530462 2945249 := bstep (se 2 (by rfl) ⟨1104468, by rfl⟩ : syracuseStep 2945249 = 2208937) B2208937
theorem B5165693 : Blo 1530462 5165693 := bstep (se 3 (by rfl) ⟨968567, by rfl⟩ : syracuseStep 5165693 = 1937135) B1937135
theorem B13439807 : Blo 1530462 13439807 := bstep (se 1 (by rfl) ⟨10079855, by rfl⟩ : syracuseStep 13439807 = 20159711) B20159711
theorem B1531599 : Blo 1530462 1531599 := bstep (se 1 (by rfl) ⟨1148699, by rfl⟩ : syracuseStep 1531599 = 2297399) B2297399
theorem B1721983 : Blo 1530462 1721983 := bstep (se 1 (by rfl) ⟨1291487, by rfl⟩ : syracuseStep 1721983 = 2582975) B2582975
theorem B151062893 : Blo 1530462 151062893 := bstep (se 3 (by rfl) ⟨28324292, by rfl⟩ : syracuseStep 151062893 = 56648585) B56648585
theorem B3443795 : Blo 1530462 3443795 := bstep (se 1 (by rfl) ⟨2582846, by rfl⟩ : syracuseStep 3443795 = 5165693) B5165693
theorem B1963499 : Blo 1530462 1963499 := bstep (se 1 (by rfl) ⟨1472624, by rfl⟩ : syracuseStep 1963499 = 2945249) B2945249
theorem B8959871 : Blo 1530462 8959871 := bstep (se 1 (by rfl) ⟨6719903, by rfl⟩ : syracuseStep 8959871 = 13439807) B13439807
theorem B3874331 : Blo 1530462 3874331 := bstep (se 1 (by rfl) ⟨2905748, by rfl⟩ : syracuseStep 3874331 = 5811497) B5811497
theorem B1531519 : Blo 1530462 1531519 := bstep (se 1 (by rfl) ⟨1148639, by rfl⟩ : syracuseStep 1531519 = 2297279) B2297279
theorem B5973247 : Blo 1530462 5973247 := bstep (se 1 (by rfl) ⟨4479935, by rfl⟩ : syracuseStep 5973247 = 8959871) B8959871
theorem B5235997 : Blo 1530462 5235997 := bstep (se 3 (by rfl) ⟨981749, by rfl⟩ : syracuseStep 5235997 = 1963499) B1963499
theorem B2295863 : Blo 1530462 2295863 := bstep (se 1 (by rfl) ⟨1721897, by rfl⟩ : syracuseStep 2295863 = 3443795) B3443795
theorem B2295977 : Blo 1530462 2295977 := bstep (se 2 (by rfl) ⟨860991, by rfl⟩ : syracuseStep 2295977 = 1721983) B1721983
theorem B2582887 : Blo 1530462 2582887 := bstep (se 1 (by rfl) ⟨1937165, by rfl⟩ : syracuseStep 2582887 = 3874331) B3874331
theorem B100708595 : Blo 1530462 100708595 := bstep (se 1 (by rfl) ⟨75531446, by rfl⟩ : syracuseStep 100708595 = 151062893) B151062893
theorem B7964329 : Blo 1530462 7964329 := bstep (se 2 (by rfl) ⟨2986623, by rfl⟩ : syracuseStep 7964329 = 5973247) B5973247
theorem B6981329 : Blo 1530462 6981329 := bstep (se 2 (by rfl) ⟨2617998, by rfl⟩ : syracuseStep 6981329 = 5235997) B5235997
theorem B3443849 : Blo 1530462 3443849 := bstep (se 2 (by rfl) ⟨1291443, by rfl⟩ : syracuseStep 3443849 = 2582887) B2582887
theorem B67139063 : Blo 1530462 67139063 := bstep (se 1 (by rfl) ⟨50354297, by rfl⟩ : syracuseStep 67139063 = 100708595) B100708595
theorem B1530575 : Blo 1530462 1530575 := bstep (se 1 (by rfl) ⟨1147931, by rfl⟩ : syracuseStep 1530575 = 2295863) B2295863
theorem B1530651 : Blo 1530462 1530651 := bstep (se 1 (by rfl) ⟨1147988, by rfl⟩ : syracuseStep 1530651 = 2295977) B2295977
theorem B4654219 : Blo 1530462 4654219 := bstep (se 1 (by rfl) ⟨3490664, by rfl⟩ : syracuseStep 4654219 = 6981329) B6981329
theorem B2295899 : Blo 1530462 2295899 := bstep (se 1 (by rfl) ⟨1721924, by rfl⟩ : syracuseStep 2295899 = 3443849) B3443849
theorem B10619105 : Blo 1530462 10619105 := bstep (se 2 (by rfl) ⟨3982164, by rfl⟩ : syracuseStep 10619105 = 7964329) B7964329
theorem B44759375 : Blo 1530462 44759375 := bstep (se 1 (by rfl) ⟨33569531, by rfl⟩ : syracuseStep 44759375 = 67139063) B67139063
theorem B6205625 : Blo 1530462 6205625 := bstep (se 2 (by rfl) ⟨2327109, by rfl⟩ : syracuseStep 6205625 = 4654219) B4654219
theorem B29839583 : Blo 1530462 29839583 := bstep (se 1 (by rfl) ⟨22379687, by rfl⟩ : syracuseStep 29839583 = 44759375) B44759375
theorem B28317613 : Blo 1530462 28317613 := bstep (se 3 (by rfl) ⟨5309552, by rfl⟩ : syracuseStep 28317613 = 10619105) B10619105
theorem B1530599 : Blo 1530462 1530599 := bstep (se 1 (by rfl) ⟨1147949, by rfl⟩ : syracuseStep 1530599 = 2295899) B2295899
theorem B4137083 : Blo 1530462 4137083 := bstep (se 1 (by rfl) ⟨3102812, by rfl⟩ : syracuseStep 4137083 = 6205625) B6205625
theorem B19893055 : Blo 1530462 19893055 := bstep (se 1 (by rfl) ⟨14919791, by rfl⟩ : syracuseStep 19893055 = 29839583) B29839583
theorem B37756817 : Blo 1530462 37756817 := bstep (se 2 (by rfl) ⟨14158806, by rfl⟩ : syracuseStep 37756817 = 28317613) B28317613
theorem B25171211 : Blo 1530462 25171211 := bstep (se 1 (by rfl) ⟨18878408, by rfl⟩ : syracuseStep 25171211 = 37756817) B37756817
theorem B2758055 : Blo 1530462 2758055 := bstep (se 1 (by rfl) ⟨2068541, by rfl⟩ : syracuseStep 2758055 = 4137083) B4137083
theorem B26524073 : Blo 1530462 26524073 := bstep (se 2 (by rfl) ⟨9946527, by rfl⟩ : syracuseStep 26524073 = 19893055) B19893055
theorem B16780807 : Blo 1530462 16780807 := bstep (se 1 (by rfl) ⟨12585605, by rfl⟩ : syracuseStep 16780807 = 25171211) B25171211
theorem B17682715 : Blo 1530462 17682715 := bstep (se 1 (by rfl) ⟨13262036, by rfl⟩ : syracuseStep 17682715 = 26524073) B26524073
theorem B7354813 : Blo 1530462 7354813 := bstep (se 3 (by rfl) ⟨1379027, by rfl⟩ : syracuseStep 7354813 = 2758055) B2758055
theorem B23576953 : Blo 1530462 23576953 := bstep (se 2 (by rfl) ⟨8841357, by rfl⟩ : syracuseStep 23576953 = 17682715) B17682715
theorem B9806417 : Blo 1530462 9806417 := bstep (se 2 (by rfl) ⟨3677406, by rfl⟩ : syracuseStep 9806417 = 7354813) B7354813
theorem B22374409 : Blo 1530462 22374409 := bstep (se 2 (by rfl) ⟨8390403, by rfl⟩ : syracuseStep 22374409 = 16780807) B16780807
theorem B6537611 : Blo 1530462 6537611 := bstep (se 1 (by rfl) ⟨4903208, by rfl⟩ : syracuseStep 6537611 = 9806417) B9806417
theorem B31435937 : Blo 1530462 31435937 := bstep (se 2 (by rfl) ⟨11788476, by rfl⟩ : syracuseStep 31435937 = 23576953) B23576953
theorem B29832545 : Blo 1530462 29832545 := bstep (se 2 (by rfl) ⟨11187204, by rfl⟩ : syracuseStep 29832545 = 22374409) B22374409
theorem B4358407 : Blo 1530462 4358407 := bstep (se 1 (by rfl) ⟨3268805, by rfl⟩ : syracuseStep 4358407 = 6537611) B6537611
theorem B20957291 : Blo 1530462 20957291 := bstep (se 1 (by rfl) ⟨15717968, by rfl⟩ : syracuseStep 20957291 = 31435937) B31435937
theorem B19888363 : Blo 1530462 19888363 := bstep (se 1 (by rfl) ⟨14916272, by rfl⟩ : syracuseStep 19888363 = 29832545) B29832545
theorem B26517817 : Blo 1530462 26517817 := bstep (se 2 (by rfl) ⟨9944181, by rfl⟩ : syracuseStep 26517817 = 19888363) B19888363
theorem B5811209 : Blo 1530462 5811209 := bstep (se 2 (by rfl) ⟨2179203, by rfl⟩ : syracuseStep 5811209 = 4358407) B4358407
theorem B13971527 : Blo 1530462 13971527 := bstep (se 1 (by rfl) ⟨10478645, by rfl⟩ : syracuseStep 13971527 = 20957291) B20957291
theorem B9314351 : Blo 1530462 9314351 := bstep (se 1 (by rfl) ⟨6985763, by rfl⟩ : syracuseStep 9314351 = 13971527) B13971527
theorem B35357089 : Blo 1530462 35357089 := bstep (se 2 (by rfl) ⟨13258908, by rfl⟩ : syracuseStep 35357089 = 26517817) B26517817
theorem B3874139 : Blo 1530462 3874139 := bstep (se 1 (by rfl) ⟨2905604, by rfl⟩ : syracuseStep 3874139 = 5811209) B5811209
theorem B6209567 : Blo 1530462 6209567 := bstep (se 1 (by rfl) ⟨4657175, by rfl⟩ : syracuseStep 6209567 = 9314351) B9314351
theorem B2582759 : Blo 1530462 2582759 := bstep (se 1 (by rfl) ⟨1937069, by rfl⟩ : syracuseStep 2582759 = 3874139) B3874139
theorem B47142785 : Blo 1530462 47142785 := bstep (se 2 (by rfl) ⟨17678544, by rfl⟩ : syracuseStep 47142785 = 35357089) B35357089
theorem B1721839 : Blo 1530462 1721839 := bstep (se 1 (by rfl) ⟨1291379, by rfl⟩ : syracuseStep 1721839 = 2582759) B2582759
theorem B4139711 : Blo 1530462 4139711 := bstep (se 1 (by rfl) ⟨3104783, by rfl⟩ : syracuseStep 4139711 = 6209567) B6209567
theorem B31428523 : Blo 1530462 31428523 := bstep (se 1 (by rfl) ⟨23571392, by rfl⟩ : syracuseStep 31428523 = 47142785) B47142785
theorem B2295785 : Blo 1530462 2295785 := bstep (se 2 (by rfl) ⟨860919, by rfl⟩ : syracuseStep 2295785 = 1721839) B1721839
theorem B41904697 : Blo 1530462 41904697 := bstep (se 2 (by rfl) ⟨15714261, by rfl⟩ : syracuseStep 41904697 = 31428523) B31428523
theorem B2759807 : Blo 1530462 2759807 := bstep (se 1 (by rfl) ⟨2069855, by rfl⟩ : syracuseStep 2759807 = 4139711) B4139711
theorem B55872929 : Blo 1530462 55872929 := bstep (se 2 (by rfl) ⟨20952348, by rfl⟩ : syracuseStep 55872929 = 41904697) B41904697
theorem B1839871 : Blo 1530462 1839871 := bstep (se 1 (by rfl) ⟨1379903, by rfl⟩ : syracuseStep 1839871 = 2759807) B2759807
theorem B1530523 : Blo 1530462 1530523 := bstep (se 1 (by rfl) ⟨1147892, by rfl⟩ : syracuseStep 1530523 = 2295785) B2295785
theorem B2453161 : Blo 1530462 2453161 := bstep (se 2 (by rfl) ⟨919935, by rfl⟩ : syracuseStep 2453161 = 1839871) B1839871
theorem B37248619 : Blo 1530462 37248619 := bstep (se 1 (by rfl) ⟨27936464, by rfl⟩ : syracuseStep 37248619 = 55872929) B55872929
theorem B3270881 : Blo 1530462 3270881 := bstep (se 2 (by rfl) ⟨1226580, by rfl⟩ : syracuseStep 3270881 = 2453161) B2453161
theorem B49664825 : Blo 1530462 49664825 := bstep (se 2 (by rfl) ⟨18624309, by rfl⟩ : syracuseStep 49664825 = 37248619) B37248619
theorem B33109883 : Blo 1530462 33109883 := bstep (se 1 (by rfl) ⟨24832412, by rfl⟩ : syracuseStep 33109883 = 49664825) B49664825
theorem B8722349 : Blo 1530462 8722349 := bstep (se 3 (by rfl) ⟨1635440, by rfl⟩ : syracuseStep 8722349 = 3270881) B3270881
theorem B22073255 : Blo 1530462 22073255 := bstep (se 1 (by rfl) ⟨16554941, by rfl⟩ : syracuseStep 22073255 = 33109883) B33109883
theorem B5814899 : Blo 1530462 5814899 := bstep (se 1 (by rfl) ⟨4361174, by rfl⟩ : syracuseStep 5814899 = 8722349) B8722349
theorem B3876599 : Blo 1530462 3876599 := bstep (se 1 (by rfl) ⟨2907449, by rfl⟩ : syracuseStep 3876599 = 5814899) B5814899
theorem B14715503 : Blo 1530462 14715503 := bstep (se 1 (by rfl) ⟨11036627, by rfl⟩ : syracuseStep 14715503 = 22073255) B22073255
theorem B2584399 : Blo 1530462 2584399 := bstep (se 1 (by rfl) ⟨1938299, by rfl⟩ : syracuseStep 2584399 = 3876599) B3876599
theorem B9810335 : Blo 1530462 9810335 := bstep (se 1 (by rfl) ⟨7357751, by rfl⟩ : syracuseStep 9810335 = 14715503) B14715503
theorem B26160893 : Blo 1530462 26160893 := bstep (se 3 (by rfl) ⟨4905167, by rfl⟩ : syracuseStep 26160893 = 9810335) B9810335
theorem B3445865 : Blo 1530462 3445865 := bstep (se 2 (by rfl) ⟨1292199, by rfl⟩ : syracuseStep 3445865 = 2584399) B2584399
theorem B2297243 : Blo 1530462 2297243 := bstep (se 1 (by rfl) ⟨1722932, by rfl⟩ : syracuseStep 2297243 = 3445865) B3445865
theorem B17440595 : Blo 1530462 17440595 := bstep (se 1 (by rfl) ⟨13080446, by rfl⟩ : syracuseStep 17440595 = 26160893) B26160893
theorem B11627063 : Blo 1530462 11627063 := bstep (se 1 (by rfl) ⟨8720297, by rfl⟩ : syracuseStep 11627063 = 17440595) B17440595
theorem B1531495 : Blo 1530462 1531495 := bstep (se 1 (by rfl) ⟨1148621, by rfl⟩ : syracuseStep 1531495 = 2297243) B2297243
theorem B7751375 : Blo 1530462 7751375 := bstep (se 1 (by rfl) ⟨5813531, by rfl⟩ : syracuseStep 7751375 = 11627063) B11627063
theorem B5167583 : Blo 1530462 5167583 := bstep (se 1 (by rfl) ⟨3875687, by rfl⟩ : syracuseStep 5167583 = 7751375) B7751375
theorem B3445055 : Blo 1530462 3445055 := bstep (se 1 (by rfl) ⟨2583791, by rfl⟩ : syracuseStep 3445055 = 5167583) B5167583
theorem B2296703 : Blo 1530462 2296703 := bstep (se 1 (by rfl) ⟨1722527, by rfl⟩ : syracuseStep 2296703 = 3445055) B3445055
theorem B1531135 : Blo 1530462 1531135 := bstep (se 1 (by rfl) ⟨1148351, by rfl⟩ : syracuseStep 1531135 = 2296703) B2296703

theorem C0 (j : ℕ) (h1 : 382615 ≤ j) (h2 : j ≤ 383114) : Blo 1530462 (4 * j + 3) := by
  interval_cases j
  · exact B1530463
  · exact B1530467
  · exact B1530471
  · exact B1530475
  · exact B1530479
  · exact B1530483
  · exact B1530487
  · exact B1530491
  · exact B1530495
  · exact B1530499
  · exact B1530503
  · exact B1530507
  · exact B1530511
  · exact B1530515
  · exact B1530519
  · exact B1530523
  · exact B1530527
  · exact B1530531
  · exact B1530535
  · exact B1530539
  · exact B1530543
  · exact B1530547
  · exact B1530551
  · exact B1530555
  · exact B1530559
  · exact B1530563
  · exact B1530567
  · exact B1530571
  · exact B1530575
  · exact B1530579
  · exact B1530583
  · exact B1530587
  · exact B1530591
  · exact B1530595
  · exact B1530599
  · exact B1530603
  · exact B1530607
  · exact B1530611
  · exact B1530615
  · exact B1530619
  · exact B1530623
  · exact B1530627
  · exact B1530631
  · exact B1530635
  · exact B1530639
  · exact B1530643
  · exact B1530647
  · exact B1530651
  · exact B1530655
  · exact B1530659
  · exact B1530663
  · exact B1530667
  · exact B1530671
  · exact B1530675
  · exact B1530679
  · exact B1530683
  · exact B1530687
  · exact B1530691
  · exact B1530695
  · exact B1530699
  · exact B1530703
  · exact B1530707
  · exact B1530711
  · exact B1530715
  · exact B1530719
  · exact B1530723
  · exact B1530727
  · exact B1530731
  · exact B1530735
  · exact B1530739
  · exact B1530743
  · exact B1530747
  · exact B1530751
  · exact B1530755
  · exact B1530759
  · exact B1530763
  · exact B1530767
  · exact B1530771
  · exact B1530775
  · exact B1530779
  · exact B1530783
  · exact B1530787
  · exact B1530791
  · exact B1530795
  · exact B1530799
  · exact B1530803
  · exact B1530807
  · exact B1530811
  · exact B1530815
  · exact B1530819
  · exact B1530823
  · exact B1530827
  · exact B1530831
  · exact B1530835
  · exact B1530839
  · exact B1530843
  · exact B1530847
  · exact B1530851
  · exact B1530855
  · exact B1530859
  · exact B1530863
  · exact B1530867
  · exact B1530871
  · exact B1530875
  · exact B1530879
  · exact B1530883
  · exact B1530887
  · exact B1530891
  · exact B1530895
  · exact B1530899
  · exact B1530903
  · exact B1530907
  · exact B1530911
  · exact B1530915
  · exact B1530919
  · exact B1530923
  · exact B1530927
  · exact B1530931
  · exact B1530935
  · exact B1530939
  · exact B1530943
  · exact B1530947
  · exact B1530951
  · exact B1530955
  · exact B1530959
  · exact B1530963
  · exact B1530967
  · exact B1530971
  · exact B1530975
  · exact B1530979
  · exact B1530983
  · exact B1530987
  · exact B1530991
  · exact B1530995
  · exact B1530999
  · exact B1531003
  · exact B1531007
  · exact B1531011
  · exact B1531015
  · exact B1531019
  · exact B1531023
  · exact B1531027
  · exact B1531031
  · exact B1531035
  · exact B1531039
  · exact B1531043
  · exact B1531047
  · exact B1531051
  · exact B1531055
  · exact B1531059
  · exact B1531063
  · exact B1531067
  · exact B1531071
  · exact B1531075
  · exact B1531079
  · exact B1531083
  · exact B1531087
  · exact B1531091
  · exact B1531095
  · exact B1531099
  · exact B1531103
  · exact B1531107
  · exact B1531111
  · exact B1531115
  · exact B1531119
  · exact B1531123
  · exact B1531127
  · exact B1531131
  · exact B1531135
  · exact B1531139
  · exact B1531143
  · exact B1531147
  · exact B1531151
  · exact B1531155
  · exact B1531159
  · exact B1531163
  · exact B1531167
  · exact B1531171
  · exact B1531175
  · exact B1531179
  · exact B1531183
  · exact B1531187
  · exact B1531191
  · exact B1531195
  · exact B1531199
  · exact B1531203
  · exact B1531207
  · exact B1531211
  · exact B1531215
  · exact B1531219
  · exact B1531223
  · exact B1531227
  · exact B1531231
  · exact B1531235
  · exact B1531239
  · exact B1531243
  · exact B1531247
  · exact B1531251
  · exact B1531255
  · exact B1531259
  · exact B1531263
  · exact B1531267
  · exact B1531271
  · exact B1531275
  · exact B1531279
  · exact B1531283
  · exact B1531287
  · exact B1531291
  · exact B1531295
  · exact B1531299
  · exact B1531303
  · exact B1531307
  · exact B1531311
  · exact B1531315
  · exact B1531319
  · exact B1531323
  · exact B1531327
  · exact B1531331
  · exact B1531335
  · exact B1531339
  · exact B1531343
  · exact B1531347
  · exact B1531351
  · exact B1531355
  · exact B1531359
  · exact B1531363
  · exact B1531367
  · exact B1531371
  · exact B1531375
  · exact B1531379
  · exact B1531383
  · exact B1531387
  · exact B1531391
  · exact B1531395
  · exact B1531399
  · exact B1531403
  · exact B1531407
  · exact B1531411
  · exact B1531415
  · exact B1531419
  · exact B1531423
  · exact B1531427
  · exact B1531431
  · exact B1531435
  · exact B1531439
  · exact B1531443
  · exact B1531447
  · exact B1531451
  · exact B1531455
  · exact B1531459
  · exact B1531463
  · exact B1531467
  · exact B1531471
  · exact B1531475
  · exact B1531479
  · exact B1531483
  · exact B1531487
  · exact B1531491
  · exact B1531495
  · exact B1531499
  · exact B1531503
  · exact B1531507
  · exact B1531511
  · exact B1531515
  · exact B1531519
  · exact B1531523
  · exact B1531527
  · exact B1531531
  · exact B1531535
  · exact B1531539
  · exact B1531543
  · exact B1531547
  · exact B1531551
  · exact B1531555
  · exact B1531559
  · exact B1531563
  · exact B1531567
  · exact B1531571
  · exact B1531575
  · exact B1531579
  · exact B1531583
  · exact B1531587
  · exact B1531591
  · exact B1531595
  · exact B1531599
  · exact B1531603
  · exact B1531607
  · exact B1531611
  · exact B1531615
  · exact B1531619
  · exact B1531623
  · exact B1531627
  · exact B1531631
  · exact B1531635
  · exact B1531639
  · exact B1531643
  · exact B1531647
  · exact B1531651
  · exact B1531655
  · exact B1531659
  · exact B1531663
  · exact B1531667
  · exact B1531671
  · exact B1531675
  · exact B1531679
  · exact B1531683
  · exact B1531687
  · exact B1531691
  · exact B1531695
  · exact B1531699
  · exact B1531703
  · exact B1531707
  · exact B1531711
  · exact B1531715
  · exact B1531719
  · exact B1531723
  · exact B1531727
  · exact B1531731
  · exact B1531735
  · exact B1531739
  · exact B1531743
  · exact B1531747
  · exact B1531751
  · exact B1531755
  · exact B1531759
  · exact B1531763
  · exact B1531767
  · exact B1531771
  · exact B1531775
  · exact B1531779
  · exact B1531783
  · exact B1531787
  · exact B1531791
  · exact B1531795
  · exact B1531799
  · exact B1531803
  · exact B1531807
  · exact B1531811
  · exact B1531815
  · exact B1531819
  · exact B1531823
  · exact B1531827
  · exact B1531831
  · exact B1531835
  · exact B1531839
  · exact B1531843
  · exact B1531847
  · exact B1531851
  · exact B1531855
  · exact B1531859
  · exact B1531863
  · exact B1531867
  · exact B1531871
  · exact B1531875
  · exact B1531879
  · exact B1531883
  · exact B1531887
  · exact B1531891
  · exact B1531895
  · exact B1531899
  · exact B1531903
  · exact B1531907
  · exact B1531911
  · exact B1531915
  · exact B1531919
  · exact B1531923
  · exact B1531927
  · exact B1531931
  · exact B1531935
  · exact B1531939
  · exact B1531943
  · exact B1531947
  · exact B1531951
  · exact B1531955
  · exact B1531959
  · exact B1531963
  · exact B1531967
  · exact B1531971
  · exact B1531975
  · exact B1531979
  · exact B1531983
  · exact B1531987
  · exact B1531991
  · exact B1531995
  · exact B1531999
  · exact B1532003
  · exact B1532007
  · exact B1532011
  · exact B1532015
  · exact B1532019
  · exact B1532023
  · exact B1532027
  · exact B1532031
  · exact B1532035
  · exact B1532039
  · exact B1532043
  · exact B1532047
  · exact B1532051
  · exact B1532055
  · exact B1532059
  · exact B1532063
  · exact B1532067
  · exact B1532071
  · exact B1532075
  · exact B1532079
  · exact B1532083
  · exact B1532087
  · exact B1532091
  · exact B1532095
  · exact B1532099
  · exact B1532103
  · exact B1532107
  · exact B1532111
  · exact B1532115
  · exact B1532119
  · exact B1532123
  · exact B1532127
  · exact B1532131
  · exact B1532135
  · exact B1532139
  · exact B1532143
  · exact B1532147
  · exact B1532151
  · exact B1532155
  · exact B1532159
  · exact B1532163
  · exact B1532167
  · exact B1532171
  · exact B1532175
  · exact B1532179
  · exact B1532183
  · exact B1532187
  · exact B1532191
  · exact B1532195
  · exact B1532199
  · exact B1532203
  · exact B1532207
  · exact B1532211
  · exact B1532215
  · exact B1532219
  · exact B1532223
  · exact B1532227
  · exact B1532231
  · exact B1532235
  · exact B1532239
  · exact B1532243
  · exact B1532247
  · exact B1532251
  · exact B1532255
  · exact B1532259
  · exact B1532263
  · exact B1532267
  · exact B1532271
  · exact B1532275
  · exact B1532279
  · exact B1532283
  · exact B1532287
  · exact B1532291
  · exact B1532295
  · exact B1532299
  · exact B1532303
  · exact B1532307
  · exact B1532311
  · exact B1532315
  · exact B1532319
  · exact B1532323
  · exact B1532327
  · exact B1532331
  · exact B1532335
  · exact B1532339
  · exact B1532343
  · exact B1532347
  · exact B1532351
  · exact B1532355
  · exact B1532359
  · exact B1532363
  · exact B1532367
  · exact B1532371
  · exact B1532375
  · exact B1532379
  · exact B1532383
  · exact B1532387
  · exact B1532391
  · exact B1532395
  · exact B1532399
  · exact B1532403
  · exact B1532407
  · exact B1532411
  · exact B1532415
  · exact B1532419
  · exact B1532423
  · exact B1532427
  · exact B1532431
  · exact B1532435
  · exact B1532439
  · exact B1532443
  · exact B1532447
  · exact B1532451
  · exact B1532455
  · exact B1532459

theorem solution (m : ℕ) (hlo : 1530462 ≤ m) (hhi : m ≤ 1532462) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 382615 ≤ j := by omega
    have hj2 : j ≤ 383114 := by omega
    have hb : Blo 1530462 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
