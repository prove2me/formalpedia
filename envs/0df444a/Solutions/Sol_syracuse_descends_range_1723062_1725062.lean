-- Prove2me | solution 1 for syracuse_descends_range_1723062_1725062
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:30:06.904853+00:00
-- url     : https://prove2.me/submissions/22cec547-19b2-4220-bb28-2e4d022f0860

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


theorem B2908237 : Blo 1723062 2908237 := bbase (se 3 (by rfl) ⟨545294, by rfl⟩ : syracuseStep 2908237 = 1090589) (by norm_num)
theorem B83845205 : Blo 1723062 83845205 := bbase (se 8 (by rfl) ⟨491280, by rfl⟩ : syracuseStep 83845205 = 982561) (by norm_num)
theorem B2621525 : Blo 1723062 2621525 := bbase (se 8 (by rfl) ⟨15360, by rfl⟩ : syracuseStep 2621525 = 30721) (by norm_num)
theorem B15949973 : Blo 1723062 15949973 := bbase (se 6 (by rfl) ⟨373827, by rfl⟩ : syracuseStep 15949973 = 747655) (by norm_num)
theorem B13099157 : Blo 1723062 13099157 := bbase (se 6 (by rfl) ⟨307011, by rfl⟩ : syracuseStep 13099157 = 614023) (by norm_num)
theorem B2908325 : Blo 1723062 2908325 := bbase (se 4 (by rfl) ⟨272655, by rfl⟩ : syracuseStep 2908325 = 545311) (by norm_num)
theorem B5816501 : Blo 1723062 5816501 := bbase (se 5 (by rfl) ⟨272648, by rfl⟩ : syracuseStep 5816501 = 545297) (by norm_num)
theorem B5521621 : Blo 1723062 5521621 := bbase (se 7 (by rfl) ⟨64706, by rfl⟩ : syracuseStep 5521621 = 129413) (by norm_num)
theorem B2212057 : Blo 1723062 2212057 := bbase (se 2 (by rfl) ⟨829521, by rfl⟩ : syracuseStep 2212057 = 1659043) (by norm_num)
theorem B4423909 : Blo 1723062 4423909 := bbase (se 4 (by rfl) ⟨414741, by rfl⟩ : syracuseStep 4423909 = 829483) (by norm_num)
theorem B8732933 : Blo 1723062 8732933 := bbase (se 4 (by rfl) ⟨818712, by rfl⟩ : syracuseStep 8732933 = 1637425) (by norm_num)
theorem B2908453 : Blo 1723062 2908453 := bbase (se 4 (by rfl) ⟨272667, by rfl⟩ : syracuseStep 2908453 = 545335) (by norm_num)
theorem B2908541 : Blo 1723062 2908541 := bbase (se 3 (by rfl) ⟨545351, by rfl⟩ : syracuseStep 2908541 = 1090703) (by norm_num)
theorem B2908669 : Blo 1723062 2908669 := bbase (se 3 (by rfl) ⟨545375, by rfl⟩ : syracuseStep 2908669 = 1090751) (by norm_num)
theorem B13091381 : Blo 1723062 13091381 := bbase (se 5 (by rfl) ⟨613658, by rfl⟩ : syracuseStep 13091381 = 1227317) (by norm_num)
theorem B2761285 : Blo 1723062 2761285 := bbase (se 4 (by rfl) ⟨258870, by rfl⟩ : syracuseStep 2761285 = 517741) (by norm_num)
theorem B2908757 : Blo 1723062 2908757 := bbase (se 8 (by rfl) ⟨17043, by rfl⟩ : syracuseStep 2908757 = 34087) (by norm_num)
theorem B5816933 : Blo 1723062 5816933 := bbase (se 4 (by rfl) ⟨545337, by rfl⟩ : syracuseStep 5816933 = 1090675) (by norm_num)
theorem B7365269 : Blo 1723062 7365269 := bbase (se 6 (by rfl) ⟨172623, by rfl⟩ : syracuseStep 7365269 = 345247) (by norm_num)
theorem B8725157 : Blo 1723062 8725157 := bbase (se 4 (by rfl) ⟨817983, by rfl⟩ : syracuseStep 8725157 = 1635967) (by norm_num)
theorem B9814709 : Blo 1723062 9814709 := bbase (se 5 (by rfl) ⟨460064, by rfl⟩ : syracuseStep 9814709 = 920129) (by norm_num)
theorem B8282837 : Blo 1723062 8282837 := bbase (se 7 (by rfl) ⟨97064, by rfl⟩ : syracuseStep 8282837 = 194129) (by norm_num)
theorem B2908885 : Blo 1723062 2908885 := bbase (se 7 (by rfl) ⟨34088, by rfl⟩ : syracuseStep 2908885 = 68177) (by norm_num)
theorem B4907765 : Blo 1723062 4907765 := bbase (se 5 (by rfl) ⟨230051, by rfl⟩ : syracuseStep 4907765 = 460103) (by norm_num)
theorem B5899013 : Blo 1723062 5899013 := bbase (se 4 (by rfl) ⟨553032, by rfl⟩ : syracuseStep 5899013 = 1106065) (by norm_num)
theorem B2908973 : Blo 1723062 2908973 := bbase (se 3 (by rfl) ⟨545432, by rfl⟩ : syracuseStep 2908973 = 1090865) (by norm_num)
theorem B2761541 : Blo 1723062 2761541 := bbase (se 4 (by rfl) ⟨258894, by rfl⟩ : syracuseStep 2761541 = 517789) (by norm_num)
theorem B80700245 : Blo 1723062 80700245 := bbase (se 9 (by rfl) ⟨236426, by rfl⟩ : syracuseStep 80700245 = 472853) (by norm_num)
theorem B1966993 : Blo 1723062 1966993 := bbase (se 2 (by rfl) ⟨737622, by rfl⟩ : syracuseStep 1966993 = 1475245) (by norm_num)
theorem B2909101 : Blo 1723062 2909101 := bbase (se 3 (by rfl) ⟨545456, by rfl⟩ : syracuseStep 2909101 = 1090913) (by norm_num)
theorem B1967053 : Blo 1723062 1967053 := bbase (se 3 (by rfl) ⟨368822, by rfl⟩ : syracuseStep 1967053 = 737645) (by norm_num)
theorem B17523701 : Blo 1723062 17523701 := bbase (se 5 (by rfl) ⟨821423, by rfl⟩ : syracuseStep 17523701 = 1642847) (by norm_num)
theorem B1795061 : Blo 1723062 1795061 := bbase (se 5 (by rfl) ⟨84143, by rfl⟩ : syracuseStep 1795061 = 168287) (by norm_num)
theorem B2909189 : Blo 1723062 2909189 := bbase (se 4 (by rfl) ⟨272736, by rfl⟩ : syracuseStep 2909189 = 545473) (by norm_num)
theorem B2761733 : Blo 1723062 2761733 := bbase (se 4 (by rfl) ⟨258912, by rfl⟩ : syracuseStep 2761733 = 517825) (by norm_num)
theorem B5817365 : Blo 1723062 5817365 := bbase (se 6 (by rfl) ⟨136344, by rfl⟩ : syracuseStep 5817365 = 272689) (by norm_num)
theorem B2909317 : Blo 1723062 2909317 := bbase (se 4 (by rfl) ⟨272748, by rfl⟩ : syracuseStep 2909317 = 545497) (by norm_num)
theorem B22103189 : Blo 1723062 22103189 := bbase (se 6 (by rfl) ⟨518043, by rfl⟩ : syracuseStep 22103189 = 1036087) (by norm_num)
theorem B2909405 : Blo 1723062 2909405 := bbase (se 3 (by rfl) ⟨545513, by rfl⟩ : syracuseStep 2909405 = 1091027) (by norm_num)
theorem B2909533 : Blo 1723062 2909533 := bbase (se 3 (by rfl) ⟨545537, by rfl⟩ : syracuseStep 2909533 = 1091075) (by norm_num)
theorem B2909621 : Blo 1723062 2909621 := bbase (se 5 (by rfl) ⟨136388, by rfl⟩ : syracuseStep 2909621 = 272777) (by norm_num)
theorem B5817797 : Blo 1723062 5817797 := bbase (se 4 (by rfl) ⟨545418, by rfl⟩ : syracuseStep 5817797 = 1090837) (by norm_num)
theorem B7972357 : Blo 1723062 7972357 := bbase (se 4 (by rfl) ⟨747408, by rfl⟩ : syracuseStep 7972357 = 1494817) (by norm_num)
theorem B2909749 : Blo 1723062 2909749 := bbase (se 5 (by rfl) ⟨136394, by rfl⟩ : syracuseStep 2909749 = 272789) (by norm_num)
theorem B4974149 : Blo 1723062 4974149 := bbase (se 4 (by rfl) ⟨466326, by rfl⟩ : syracuseStep 4974149 = 932653) (by norm_num)
theorem B6547013 : Blo 1723062 6547013 := bbase (se 4 (by rfl) ⟨613782, by rfl⟩ : syracuseStep 6547013 = 1227565) (by norm_num)
theorem B7366261 : Blo 1723062 7366261 := bbase (se 5 (by rfl) ⟨345293, by rfl⟩ : syracuseStep 7366261 = 690587) (by norm_num)
theorem B2909837 : Blo 1723062 2909837 := bbase (se 3 (by rfl) ⟨545594, by rfl⟩ : syracuseStep 2909837 = 1091189) (by norm_num)
theorem B2180773 : Blo 1723062 2180773 := bbase (se 4 (by rfl) ⟨204447, by rfl⟩ : syracuseStep 2180773 = 408895) (by norm_num)
theorem B16574165 : Blo 1723062 16574165 := bbase (se 7 (by rfl) ⟨194228, by rfl⟩ : syracuseStep 16574165 = 388457) (by norm_num)
theorem B6211333 : Blo 1723062 6211333 := bbase (se 4 (by rfl) ⟨582312, by rfl⟩ : syracuseStep 6211333 = 1164625) (by norm_num)
theorem B2909965 : Blo 1723062 2909965 := bbase (se 3 (by rfl) ⟨545618, by rfl⟩ : syracuseStep 2909965 = 1091237) (by norm_num)
theorem B2180945 : Blo 1723062 2180945 := bbase (se 2 (by rfl) ⟨817854, by rfl⟩ : syracuseStep 2180945 = 1635709) (by norm_num)
theorem B13985621 : Blo 1723062 13985621 := bbase (se 9 (by rfl) ⟨40973, by rfl⟩ : syracuseStep 13985621 = 81947) (by norm_num)
theorem B6547301 : Blo 1723062 6547301 := bbase (se 4 (by rfl) ⟨613809, by rfl⟩ : syracuseStep 6547301 = 1227619) (by norm_num)
theorem B2910053 : Blo 1723062 2910053 := bbase (se 4 (by rfl) ⟨272817, by rfl⟩ : syracuseStep 2910053 = 545635) (by norm_num)
theorem B5818229 : Blo 1723062 5818229 := bbase (se 5 (by rfl) ⟨272729, by rfl⟩ : syracuseStep 5818229 = 545459) (by norm_num)
theorem B2181001 : Blo 1723062 2181001 := bbase (se 2 (by rfl) ⟨817875, by rfl⟩ : syracuseStep 2181001 = 1635751) (by norm_num)
theorem B2762669 : Blo 1723062 2762669 := bbase (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) (by norm_num)
theorem B8726453 : Blo 1723062 8726453 := bbase (se 5 (by rfl) ⟨409052, by rfl⟩ : syracuseStep 8726453 = 818105) (by norm_num)
theorem B1746889 : Blo 1723062 1746889 := bbase (se 2 (by rfl) ⟨655083, by rfl⟩ : syracuseStep 1746889 = 1310167) (by norm_num)
theorem B2910181 : Blo 1723062 2910181 := bbase (se 4 (by rfl) ⟨272829, by rfl⟩ : syracuseStep 2910181 = 545659) (by norm_num)
theorem B2181097 : Blo 1723062 2181097 := bbase (se 2 (by rfl) ⟨817911, by rfl⟩ : syracuseStep 2181097 = 1635823) (by norm_num)
theorem B6989813 : Blo 1723062 6989813 := bbase (se 5 (by rfl) ⟨327647, by rfl⟩ : syracuseStep 6989813 = 655295) (by norm_num)
theorem B2590733 : Blo 1723062 2590733 := bbase (se 3 (by rfl) ⟨485762, by rfl⟩ : syracuseStep 2590733 = 971525) (by norm_num)
theorem B9447445 : Blo 1723062 9447445 := bbase (se 6 (by rfl) ⟨221424, by rfl⟩ : syracuseStep 9447445 = 442849) (by norm_num)
theorem B3876893 : Blo 1723062 3876893 := bbase (se 3 (by rfl) ⟨726917, by rfl⟩ : syracuseStep 3876893 = 1453835) (by norm_num)
theorem B2910269 : Blo 1723062 2910269 := bbase (se 3 (by rfl) ⟨545675, by rfl⟩ : syracuseStep 2910269 = 1091351) (by norm_num)
theorem B19646549 : Blo 1723062 19646549 := bbase (se 8 (by rfl) ⟨115116, by rfl⟩ : syracuseStep 19646549 = 230233) (by norm_num)
theorem B3541085 : Blo 1723062 3541085 := bbase (se 3 (by rfl) ⟨663953, by rfl⟩ : syracuseStep 3541085 = 1327907) (by norm_num)
theorem B3876965 : Blo 1723062 3876965 := bbase (se 4 (by rfl) ⟨363465, by rfl⟩ : syracuseStep 3876965 = 726931) (by norm_num)
theorem B2181269 : Blo 1723062 2181269 := bbase (se 6 (by rfl) ⟨51123, by rfl⟩ : syracuseStep 2181269 = 102247) (by norm_num)
theorem B3877037 : Blo 1723062 3877037 := bbase (se 3 (by rfl) ⟨726944, by rfl⟩ : syracuseStep 3877037 = 1453889) (by norm_num)
theorem B1747117 : Blo 1723062 1747117 := bbase (se 3 (by rfl) ⟨327584, by rfl⟩ : syracuseStep 1747117 = 655169) (by norm_num)
theorem B2910397 : Blo 1723062 2910397 := bbase (se 3 (by rfl) ⟨545699, by rfl⟩ : syracuseStep 2910397 = 1091399) (by norm_num)
theorem B2181325 : Blo 1723062 2181325 := bbase (se 3 (by rfl) ⟨408998, by rfl⟩ : syracuseStep 2181325 = 817997) (by norm_num)
theorem B3877109 : Blo 1723062 3877109 := bbase (se 5 (by rfl) ⟨181739, by rfl⟩ : syracuseStep 3877109 = 363479) (by norm_num)
theorem B2910485 : Blo 1723062 2910485 := bbase (se 6 (by rfl) ⟨68214, by rfl⟩ : syracuseStep 2910485 = 136429) (by norm_num)
theorem B4909349 : Blo 1723062 4909349 := bbase (se 4 (by rfl) ⟨460251, by rfl⟩ : syracuseStep 4909349 = 920503) (by norm_num)
theorem B5818661 : Blo 1723062 5818661 := bbase (se 4 (by rfl) ⟨545499, by rfl⟩ : syracuseStep 5818661 = 1090999) (by norm_num)
theorem B2181421 : Blo 1723062 2181421 := bbase (se 3 (by rfl) ⟨409016, by rfl⟩ : syracuseStep 2181421 = 818033) (by norm_num)
theorem B2763053 : Blo 1723062 2763053 := bbase (se 3 (by rfl) ⟨518072, by rfl⟩ : syracuseStep 2763053 = 1036145) (by norm_num)
theorem B3877181 : Blo 1723062 3877181 := bbase (se 3 (by rfl) ⟨726971, by rfl⟩ : syracuseStep 3877181 = 1453943) (by norm_num)
theorem B9824597 : Blo 1723062 9824597 := bbase (se 10 (by rfl) ⟨14391, by rfl⟩ : syracuseStep 9824597 = 28783) (by norm_num)
theorem B3877253 : Blo 1723062 3877253 := bbase (se 4 (by rfl) ⟨363492, by rfl⟩ : syracuseStep 3877253 = 726985) (by norm_num)
theorem B3680653 : Blo 1723062 3680653 := bbase (se 3 (by rfl) ⟨690122, by rfl⟩ : syracuseStep 3680653 = 1380245) (by norm_num)
theorem B2910613 : Blo 1723062 2910613 := bbase (se 6 (by rfl) ⟨68217, by rfl⟩ : syracuseStep 2910613 = 136435) (by norm_num)
theorem B2763181 : Blo 1723062 2763181 := bbase (se 3 (by rfl) ⟨518096, by rfl⟩ : syracuseStep 2763181 = 1036193) (by norm_num)
theorem B2329013 : Blo 1723062 2329013 := bbase (se 5 (by rfl) ⟨109172, by rfl⟩ : syracuseStep 2329013 = 218345) (by norm_num)
theorem B3877325 : Blo 1723062 3877325 := bbase (se 3 (by rfl) ⟨726998, by rfl⟩ : syracuseStep 3877325 = 1453997) (by norm_num)
theorem B2181593 : Blo 1723062 2181593 := bbase (se 2 (by rfl) ⟨818097, by rfl⟩ : syracuseStep 2181593 = 1636195) (by norm_num)
theorem B2910701 : Blo 1723062 2910701 := bbase (se 3 (by rfl) ⟨545756, by rfl⟩ : syracuseStep 2910701 = 1091513) (by norm_num)
theorem B2181649 : Blo 1723062 2181649 := bbase (se 2 (by rfl) ⟨818118, by rfl⟩ : syracuseStep 2181649 = 1636237) (by norm_num)
theorem B3877397 : Blo 1723062 3877397 := bbase (se 6 (by rfl) ⟨90876, by rfl⟩ : syracuseStep 3877397 = 181753) (by norm_num)
theorem B3271205 : Blo 1723062 3271205 := bbase (se 4 (by rfl) ⟨306675, by rfl⟩ : syracuseStep 3271205 = 613351) (by norm_num)
theorem B3877469 : Blo 1723062 3877469 := bbase (se 3 (by rfl) ⟨727025, by rfl⟩ : syracuseStep 3877469 = 1454051) (by norm_num)
theorem B2910829 : Blo 1723062 2910829 := bbase (se 3 (by rfl) ⟨545780, by rfl⟩ : syracuseStep 2910829 = 1091561) (by norm_num)
theorem B2181745 : Blo 1723062 2181745 := bbase (se 2 (by rfl) ⟨818154, by rfl⟩ : syracuseStep 2181745 = 1636309) (by norm_num)
theorem B3877541 : Blo 1723062 3877541 := bbase (se 4 (by rfl) ⟨363519, by rfl⟩ : syracuseStep 3877541 = 727039) (by norm_num)
theorem B3271357 : Blo 1723062 3271357 := bbase (se 3 (by rfl) ⟨613379, by rfl⟩ : syracuseStep 3271357 = 1226759) (by norm_num)
theorem B2910917 : Blo 1723062 2910917 := bbase (se 4 (by rfl) ⟨272898, by rfl⟩ : syracuseStep 2910917 = 545797) (by norm_num)
theorem B5819093 : Blo 1723062 5819093 := bbase (se 7 (by rfl) ⟨68192, by rfl⟩ : syracuseStep 5819093 = 136385) (by norm_num)
theorem B3877613 : Blo 1723062 3877613 := bbase (se 3 (by rfl) ⟨727052, by rfl⟩ : syracuseStep 3877613 = 1454105) (by norm_num)
theorem B2181917 : Blo 1723062 2181917 := bbase (se 3 (by rfl) ⟨409109, by rfl⟩ : syracuseStep 2181917 = 818219) (by norm_num)
theorem B3107621 : Blo 1723062 3107621 := bbase (se 4 (by rfl) ⟨291339, by rfl⟩ : syracuseStep 3107621 = 582679) (by norm_num)
theorem B3877685 : Blo 1723062 3877685 := bbase (se 5 (by rfl) ⟨181766, by rfl⟩ : syracuseStep 3877685 = 363533) (by norm_num)
theorem B2362165 : Blo 1723062 2362165 := bbase (se 5 (by rfl) ⟨110726, by rfl⟩ : syracuseStep 2362165 = 221453) (by norm_num)
theorem B7867205 : Blo 1723062 7867205 := bbase (se 4 (by rfl) ⟨737550, by rfl⟩ : syracuseStep 7867205 = 1475101) (by norm_num)
theorem B12421973 : Blo 1723062 12421973 := bbase (se 9 (by rfl) ⟨36392, by rfl⟩ : syracuseStep 12421973 = 72785) (by norm_num)
theorem B2181973 : Blo 1723062 2181973 := bbase (se 9 (by rfl) ⟨6392, by rfl⟩ : syracuseStep 2181973 = 12785) (by norm_num)
theorem B3877757 : Blo 1723062 3877757 := bbase (se 3 (by rfl) ⟨727079, by rfl⟩ : syracuseStep 3877757 = 1454159) (by norm_num)
theorem B2182069 : Blo 1723062 2182069 := bbase (se 5 (by rfl) ⟨102284, by rfl⟩ : syracuseStep 2182069 = 204569) (by norm_num)
theorem B3877829 : Blo 1723062 3877829 := bbase (se 4 (by rfl) ⟨363546, by rfl⟩ : syracuseStep 3877829 = 727093) (by norm_num)
theorem B4910021 : Blo 1723062 4910021 := bbase (se 4 (by rfl) ⟨460314, by rfl⟩ : syracuseStep 4910021 = 920629) (by norm_num)
theorem B5524453 : Blo 1723062 5524453 := bbase (se 4 (by rfl) ⟨517917, by rfl⟩ : syracuseStep 5524453 = 1035835) (by norm_num)
theorem B3271661 : Blo 1723062 3271661 := bbase (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) (by norm_num)
theorem B6548485 : Blo 1723062 6548485 := bbase (se 4 (by rfl) ⟨613920, by rfl⟩ : syracuseStep 6548485 = 1227841) (by norm_num)
theorem B3877901 : Blo 1723062 3877901 := bbase (se 3 (by rfl) ⟨727106, by rfl⟩ : syracuseStep 3877901 = 1454213) (by norm_num)
theorem B5598229 : Blo 1723062 5598229 := bbase (se 6 (by rfl) ⟨131208, by rfl⟩ : syracuseStep 5598229 = 262417) (by norm_num)
theorem B5524517 : Blo 1723062 5524517 := bbase (se 4 (by rfl) ⟨517923, by rfl⟩ : syracuseStep 5524517 = 1035847) (by norm_num)
theorem B1748017 : Blo 1723062 1748017 := bbase (se 2 (by rfl) ⟨655506, by rfl⟩ : syracuseStep 1748017 = 1311013) (by norm_num)
theorem B8285237 : Blo 1723062 8285237 := bbase (se 5 (by rfl) ⟨388370, by rfl⟩ : syracuseStep 8285237 = 776741) (by norm_num)
theorem B3877973 : Blo 1723062 3877973 := bbase (se 8 (by rfl) ⟨22722, by rfl⟩ : syracuseStep 3877973 = 45445) (by norm_num)
theorem B2182241 : Blo 1723062 2182241 := bbase (se 2 (by rfl) ⟨818340, by rfl⟩ : syracuseStep 2182241 = 1636681) (by norm_num)
theorem B5819525 : Blo 1723062 5819525 := bbase (se 4 (by rfl) ⟨545580, by rfl⟩ : syracuseStep 5819525 = 1091161) (by norm_num)
theorem B1748105 : Blo 1723062 1748105 := bbase (se 2 (by rfl) ⟨655539, by rfl⟩ : syracuseStep 1748105 = 1311079) (by norm_num)
theorem B2182297 : Blo 1723062 2182297 := bbase (se 2 (by rfl) ⟨818361, by rfl⟩ : syracuseStep 2182297 = 1636723) (by norm_num)
theorem B3878045 : Blo 1723062 3878045 := bbase (se 3 (by rfl) ⟨727133, by rfl⟩ : syracuseStep 3878045 = 1454267) (by norm_num)
theorem B8727749 : Blo 1723062 8727749 := bbase (se 4 (by rfl) ⟨818226, by rfl⟩ : syracuseStep 8727749 = 1636453) (by norm_num)
theorem B3878117 : Blo 1723062 3878117 := bbase (se 4 (by rfl) ⟨363573, by rfl⟩ : syracuseStep 3878117 = 727147) (by norm_num)
theorem B2182393 : Blo 1723062 2182393 := bbase (se 2 (by rfl) ⟨818397, by rfl⟩ : syracuseStep 2182393 = 1636795) (by norm_num)
theorem B3681541 : Blo 1723062 3681541 := bbase (se 4 (by rfl) ⟨345144, by rfl⟩ : syracuseStep 3681541 = 690289) (by norm_num)
theorem B17689877 : Blo 1723062 17689877 := bbase (se 6 (by rfl) ⟨414606, by rfl⟩ : syracuseStep 17689877 = 829213) (by norm_num)
theorem B2100505 : Blo 1723062 2100505 := bbase (se 2 (by rfl) ⟨787689, by rfl⟩ : syracuseStep 2100505 = 1575379) (by norm_num)
theorem B3878189 : Blo 1723062 3878189 := bbase (se 3 (by rfl) ⟨727160, by rfl⟩ : syracuseStep 3878189 = 1454321) (by norm_num)
theorem B6548789 : Blo 1723062 6548789 := bbase (se 5 (by rfl) ⟨306974, by rfl⟩ : syracuseStep 6548789 = 613949) (by norm_num)
theorem B3878261 : Blo 1723062 3878261 := bbase (se 5 (by rfl) ⟨181793, by rfl⟩ : syracuseStep 3878261 = 363587) (by norm_num)
theorem B4910453 : Blo 1723062 4910453 := bbase (se 5 (by rfl) ⟨230177, by rfl⟩ : syracuseStep 4910453 = 460355) (by norm_num)
theorem B4361597 : Blo 1723062 4361597 := bbase (se 3 (by rfl) ⟨817799, by rfl⟩ : syracuseStep 4361597 = 1635599) (by norm_num)
theorem B2100637 : Blo 1723062 2100637 := bbase (se 3 (by rfl) ⟨393869, by rfl⟩ : syracuseStep 2100637 = 787739) (by norm_num)
theorem B2182565 : Blo 1723062 2182565 := bbase (se 4 (by rfl) ⟨204615, by rfl⟩ : syracuseStep 2182565 = 409231) (by norm_num)
theorem B14732725 : Blo 1723062 14732725 := bbase (se 5 (by rfl) ⟨690596, by rfl⟩ : syracuseStep 14732725 = 1381193) (by norm_num)
theorem B3878333 : Blo 1723062 3878333 := bbase (se 3 (by rfl) ⟨727187, by rfl⟩ : syracuseStep 3878333 = 1454375) (by norm_num)
theorem B2182621 : Blo 1723062 2182621 := bbase (se 3 (by rfl) ⟨409241, by rfl⟩ : syracuseStep 2182621 = 818483) (by norm_num)
theorem B3984869 : Blo 1723062 3984869 := bbase (se 4 (by rfl) ⟨373581, by rfl⟩ : syracuseStep 3984869 = 747163) (by norm_num)
theorem B3878405 : Blo 1723062 3878405 := bbase (se 4 (by rfl) ⟨363600, by rfl⟩ : syracuseStep 3878405 = 727201) (by norm_num)
theorem B22081045 : Blo 1723062 22081045 := bbase (se 6 (by rfl) ⟨517524, by rfl⟩ : syracuseStep 22081045 = 1035049) (by norm_num)
theorem B5819957 : Blo 1723062 5819957 := bbase (se 5 (by rfl) ⟨272810, by rfl⟩ : syracuseStep 5819957 = 545621) (by norm_num)
theorem B4361789 : Blo 1723062 4361789 := bbase (se 3 (by rfl) ⟨817835, by rfl⟩ : syracuseStep 4361789 = 1635671) (by norm_num)
theorem B2182717 : Blo 1723062 2182717 := bbase (se 3 (by rfl) ⟨409259, by rfl⟩ : syracuseStep 2182717 = 818519) (by norm_num)
theorem B3878477 : Blo 1723062 3878477 := bbase (se 3 (by rfl) ⟨727214, by rfl⟩ : syracuseStep 3878477 = 1454429) (by norm_num)
theorem B3878549 : Blo 1723062 3878549 := bbase (se 6 (by rfl) ⟨90903, by rfl⟩ : syracuseStep 3878549 = 181807) (by norm_num)
theorem B12431029 : Blo 1723062 12431029 := bbase (se 5 (by rfl) ⟨582704, by rfl⟩ : syracuseStep 12431029 = 1165409) (by norm_num)
theorem B3272413 : Blo 1723062 3272413 := bbase (se 3 (by rfl) ⟨613577, by rfl⟩ : syracuseStep 3272413 = 1227155) (by norm_num)
theorem B3878621 : Blo 1723062 3878621 := bbase (se 3 (by rfl) ⟨727241, by rfl⟩ : syracuseStep 3878621 = 1454483) (by norm_num)
theorem B2182889 : Blo 1723062 2182889 := bbase (se 2 (by rfl) ⟨818583, by rfl⟩ : syracuseStep 2182889 = 1637167) (by norm_num)
theorem B3682037 : Blo 1723062 3682037 := bbase (se 5 (by rfl) ⟨172595, by rfl⟩ : syracuseStep 3682037 = 345191) (by norm_num)
theorem B10481429 : Blo 1723062 10481429 := bbase (se 6 (by rfl) ⟨245658, by rfl⟩ : syracuseStep 10481429 = 491317) (by norm_num)
theorem B2182945 : Blo 1723062 2182945 := bbase (se 2 (by rfl) ⟨818604, by rfl⟩ : syracuseStep 2182945 = 1637209) (by norm_num)
theorem B3878693 : Blo 1723062 3878693 := bbase (se 4 (by rfl) ⟨363627, by rfl⟩ : syracuseStep 3878693 = 727255) (by norm_num)
theorem B2330461 : Blo 1723062 2330461 := bbase (se 3 (by rfl) ⟨436961, by rfl⟩ : syracuseStep 2330461 = 873923) (by norm_num)
theorem B3272557 : Blo 1723062 3272557 := bbase (se 3 (by rfl) ⟨613604, by rfl⟩ : syracuseStep 3272557 = 1227209) (by norm_num)
theorem B3878765 : Blo 1723062 3878765 := bbase (se 3 (by rfl) ⟨727268, by rfl⟩ : syracuseStep 3878765 = 1454537) (by norm_num)
theorem B2183041 : Blo 1723062 2183041 := bbase (se 2 (by rfl) ⟨818640, by rfl⟩ : syracuseStep 2183041 = 1637281) (by norm_num)
theorem B4362133 : Blo 1723062 4362133 := bbase (se 6 (by rfl) ⟨102237, by rfl⟩ : syracuseStep 4362133 = 204475) (by norm_num)
theorem B3878837 : Blo 1723062 3878837 := bbase (se 5 (by rfl) ⟨181820, by rfl⟩ : syracuseStep 3878837 = 363641) (by norm_num)
theorem B5820389 : Blo 1723062 5820389 := bbase (se 4 (by rfl) ⟨545661, by rfl⟩ : syracuseStep 5820389 = 1091323) (by norm_num)
theorem B11800565 : Blo 1723062 11800565 := bbase (se 5 (by rfl) ⟨553151, by rfl⟩ : syracuseStep 11800565 = 1106303) (by norm_num)
theorem B3878909 : Blo 1723062 3878909 := bbase (se 3 (by rfl) ⟨727295, by rfl⟩ : syracuseStep 3878909 = 1454591) (by norm_num)
theorem B4362245 : Blo 1723062 4362245 := bbase (se 4 (by rfl) ⟨408960, by rfl⟩ : syracuseStep 4362245 = 817921) (by norm_num)
theorem B3272717 : Blo 1723062 3272717 := bbase (se 3 (by rfl) ⟨613634, by rfl⟩ : syracuseStep 3272717 = 1227269) (by norm_num)
theorem B2584613 : Blo 1723062 2584613 := bbase (se 4 (by rfl) ⟨242307, by rfl⟩ : syracuseStep 2584613 = 484615) (by norm_num)
theorem B2183213 : Blo 1723062 2183213 := bbase (se 3 (by rfl) ⟨409352, by rfl⟩ : syracuseStep 2183213 = 818705) (by norm_num)
theorem B2584637 : Blo 1723062 2584637 := bbase (se 3 (by rfl) ⟨484619, by rfl⟩ : syracuseStep 2584637 = 969239) (by norm_num)
theorem B3878981 : Blo 1723062 3878981 := bbase (se 4 (by rfl) ⟨363654, by rfl⟩ : syracuseStep 3878981 = 727309) (by norm_num)
theorem B2453581 : Blo 1723062 2453581 := bbase (se 3 (by rfl) ⟨460046, by rfl⟩ : syracuseStep 2453581 = 920093) (by norm_num)
theorem B2584661 : Blo 1723062 2584661 := bbase (se 8 (by rfl) ⟨15144, by rfl⟩ : syracuseStep 2584661 = 30289) (by norm_num)
theorem B4911205 : Blo 1723062 4911205 := bbase (se 4 (by rfl) ⟨460425, by rfl⟩ : syracuseStep 4911205 = 920851) (by norm_num)
theorem B2183269 : Blo 1723062 2183269 := bbase (se 4 (by rfl) ⟨204681, by rfl⟩ : syracuseStep 2183269 = 409363) (by norm_num)
theorem B2584685 : Blo 1723062 2584685 := bbase (se 3 (by rfl) ⟨484628, by rfl⟩ : syracuseStep 2584685 = 969257) (by norm_num)
theorem B2584709 : Blo 1723062 2584709 := bbase (se 4 (by rfl) ⟨242316, by rfl⟩ : syracuseStep 2584709 = 484633) (by norm_num)
theorem B3494021 : Blo 1723062 3494021 := bbase (se 4 (by rfl) ⟨327564, by rfl⟩ : syracuseStep 3494021 = 655129) (by norm_num)
theorem B3879053 : Blo 1723062 3879053 := bbase (se 3 (by rfl) ⟨727322, by rfl⟩ : syracuseStep 3879053 = 1454645) (by norm_num)
theorem B8851589 : Blo 1723062 8851589 := bbase (se 4 (by rfl) ⟨829836, by rfl⟩ : syracuseStep 8851589 = 1659673) (by norm_num)
theorem B2584733 : Blo 1723062 2584733 := bbase (se 3 (by rfl) ⟨484637, by rfl⟩ : syracuseStep 2584733 = 969275) (by norm_num)
theorem B3272861 : Blo 1723062 3272861 := bbase (se 3 (by rfl) ⟨613661, by rfl⟩ : syracuseStep 3272861 = 1227323) (by norm_num)
theorem B2584757 : Blo 1723062 2584757 := bbase (se 5 (by rfl) ⟨121160, by rfl⟩ : syracuseStep 2584757 = 242321) (by norm_num)
theorem B4362437 : Blo 1723062 4362437 := bbase (se 4 (by rfl) ⟨408978, by rfl⟩ : syracuseStep 4362437 = 817957) (by norm_num)
theorem B2584781 : Blo 1723062 2584781 := bbase (se 3 (by rfl) ⟨484646, by rfl⟩ : syracuseStep 2584781 = 969293) (by norm_num)
theorem B3879125 : Blo 1723062 3879125 := bbase (se 7 (by rfl) ⟨45458, by rfl⟩ : syracuseStep 3879125 = 90917) (by norm_num)
theorem B2584805 : Blo 1723062 2584805 := bbase (se 4 (by rfl) ⟨242325, by rfl⟩ : syracuseStep 2584805 = 484651) (by norm_num)
theorem B4976885 : Blo 1723062 4976885 := bbase (se 5 (by rfl) ⟨233291, by rfl⟩ : syracuseStep 4976885 = 466583) (by norm_num)
theorem B2584829 : Blo 1723062 2584829 := bbase (se 3 (by rfl) ⟨484655, by rfl⟩ : syracuseStep 2584829 = 969311) (by norm_num)
theorem B2584853 : Blo 1723062 2584853 := bbase (se 6 (by rfl) ⟨60582, by rfl⟩ : syracuseStep 2584853 = 121165) (by norm_num)
theorem B3879197 : Blo 1723062 3879197 := bbase (se 3 (by rfl) ⟨727349, by rfl⟩ : syracuseStep 3879197 = 1454699) (by norm_num)
theorem B2584877 : Blo 1723062 2584877 := bbase (se 3 (by rfl) ⟨484664, by rfl⟩ : syracuseStep 2584877 = 969329) (by norm_num)
theorem B2584901 : Blo 1723062 2584901 := bbase (se 4 (by rfl) ⟨242334, by rfl⟩ : syracuseStep 2584901 = 484669) (by norm_num)
theorem B2584925 : Blo 1723062 2584925 := bbase (se 3 (by rfl) ⟨484673, by rfl⟩ : syracuseStep 2584925 = 969347) (by norm_num)
theorem B3879269 : Blo 1723062 3879269 := bbase (se 4 (by rfl) ⟨363681, by rfl⟩ : syracuseStep 3879269 = 727363) (by norm_num)
theorem B2584949 : Blo 1723062 2584949 := bbase (se 5 (by rfl) ⟨121169, by rfl⟩ : syracuseStep 2584949 = 242339) (by norm_num)
theorem B9318773 : Blo 1723062 9318773 := bbase (se 5 (by rfl) ⟨436817, by rfl⟩ : syracuseStep 9318773 = 873635) (by norm_num)
theorem B2584973 : Blo 1723062 2584973 := bbase (se 3 (by rfl) ⟨484682, by rfl⟩ : syracuseStep 2584973 = 969365) (by norm_num)
theorem B5820821 : Blo 1723062 5820821 := bbase (se 6 (by rfl) ⟨136425, by rfl⟩ : syracuseStep 5820821 = 272851) (by norm_num)
theorem B2453917 : Blo 1723062 2453917 := bbase (se 3 (by rfl) ⟨460109, by rfl⟩ : syracuseStep 2453917 = 920219) (by norm_num)
theorem B2584997 : Blo 1723062 2584997 := bbase (se 4 (by rfl) ⟨242343, by rfl⟩ : syracuseStep 2584997 = 484687) (by norm_num)
theorem B3879341 : Blo 1723062 3879341 := bbase (se 3 (by rfl) ⟨727376, by rfl⟩ : syracuseStep 3879341 = 1454753) (by norm_num)
theorem B2585021 : Blo 1723062 2585021 := bbase (se 3 (by rfl) ⟨484691, by rfl⟩ : syracuseStep 2585021 = 969383) (by norm_num)
theorem B3273149 : Blo 1723062 3273149 := bbase (se 3 (by rfl) ⟨613715, by rfl⟩ : syracuseStep 3273149 = 1227431) (by norm_num)
theorem B2585045 : Blo 1723062 2585045 := bbase (se 7 (by rfl) ⟨30293, by rfl⟩ : syracuseStep 2585045 = 60587) (by norm_num)
theorem B38302165 : Blo 1723062 38302165 := bbase (se 7 (by rfl) ⟨448853, by rfl⟩ : syracuseStep 38302165 = 897707) (by norm_num)
theorem B8729045 : Blo 1723062 8729045 := bbase (se 7 (by rfl) ⟨102293, by rfl⟩ : syracuseStep 8729045 = 204587) (by norm_num)
theorem B2585069 : Blo 1723062 2585069 := bbase (se 3 (by rfl) ⟨484700, by rfl⟩ : syracuseStep 2585069 = 969401) (by norm_num)
theorem B3879413 : Blo 1723062 3879413 := bbase (se 5 (by rfl) ⟨181847, by rfl⟩ : syracuseStep 3879413 = 363695) (by norm_num)
theorem B2585093 : Blo 1723062 2585093 := bbase (se 4 (by rfl) ⟨242352, by rfl⟩ : syracuseStep 2585093 = 484705) (by norm_num)
theorem B2585117 : Blo 1723062 2585117 := bbase (se 3 (by rfl) ⟨484709, by rfl⟩ : syracuseStep 2585117 = 969419) (by norm_num)
theorem B4362781 : Blo 1723062 4362781 := bbase (se 3 (by rfl) ⟨818021, by rfl⟩ : syracuseStep 4362781 = 1636043) (by norm_num)
theorem B2585141 : Blo 1723062 2585141 := bbase (se 5 (by rfl) ⟨121178, by rfl⟩ : syracuseStep 2585141 = 242357) (by norm_num)
theorem B3879485 : Blo 1723062 3879485 := bbase (se 3 (by rfl) ⟨727403, by rfl⟩ : syracuseStep 3879485 = 1454807) (by norm_num)
theorem B2585165 : Blo 1723062 2585165 := bbase (se 3 (by rfl) ⟨484718, by rfl⟩ : syracuseStep 2585165 = 969437) (by norm_num)
theorem B3494477 : Blo 1723062 3494477 := bbase (se 3 (by rfl) ⟨655214, by rfl⟩ : syracuseStep 3494477 = 1310429) (by norm_num)
theorem B3273301 : Blo 1723062 3273301 := bbase (se 8 (by rfl) ⟨19179, by rfl⟩ : syracuseStep 3273301 = 38359) (by norm_num)
theorem B3682901 : Blo 1723062 3682901 := bbase (se 8 (by rfl) ⟨21579, by rfl⟩ : syracuseStep 3682901 = 43159) (by norm_num)
theorem B2585189 : Blo 1723062 2585189 := bbase (se 4 (by rfl) ⟨242361, by rfl⟩ : syracuseStep 2585189 = 484723) (by norm_num)
theorem B2454133 : Blo 1723062 2454133 := bbase (se 5 (by rfl) ⟨115037, by rfl⟩ : syracuseStep 2454133 = 230075) (by norm_num)
theorem B2585213 : Blo 1723062 2585213 := bbase (se 3 (by rfl) ⟨484727, by rfl⟩ : syracuseStep 2585213 = 969455) (by norm_num)
theorem B3879557 : Blo 1723062 3879557 := bbase (se 4 (by rfl) ⟨363708, by rfl⟩ : syracuseStep 3879557 = 727417) (by norm_num)
theorem B4362893 : Blo 1723062 4362893 := bbase (se 3 (by rfl) ⟨818042, by rfl⟩ : syracuseStep 4362893 = 1636085) (by norm_num)
theorem B2585237 : Blo 1723062 2585237 := bbase (se 6 (by rfl) ⟨60591, by rfl⟩ : syracuseStep 2585237 = 121183) (by norm_num)
theorem B2585261 : Blo 1723062 2585261 := bbase (se 3 (by rfl) ⟨484736, by rfl⟩ : syracuseStep 2585261 = 969473) (by norm_num)
theorem B2486965 : Blo 1723062 2486965 := bbase (se 5 (by rfl) ⟨116576, by rfl⟩ : syracuseStep 2486965 = 233153) (by norm_num)
theorem B2585285 : Blo 1723062 2585285 := bbase (se 4 (by rfl) ⟨242370, by rfl⟩ : syracuseStep 2585285 = 484741) (by norm_num)
theorem B3879629 : Blo 1723062 3879629 := bbase (se 3 (by rfl) ⟨727430, by rfl⟩ : syracuseStep 3879629 = 1454861) (by norm_num)
theorem B2585309 : Blo 1723062 2585309 := bbase (se 3 (by rfl) ⟨484745, by rfl⟩ : syracuseStep 2585309 = 969491) (by norm_num)
theorem B3683045 : Blo 1723062 3683045 := bbase (se 4 (by rfl) ⟨345285, by rfl⟩ : syracuseStep 3683045 = 690571) (by norm_num)
theorem B2487029 : Blo 1723062 2487029 := bbase (se 5 (by rfl) ⟨116579, by rfl⟩ : syracuseStep 2487029 = 233159) (by norm_num)
theorem B2585333 : Blo 1723062 2585333 := bbase (se 5 (by rfl) ⟨121187, by rfl⟩ : syracuseStep 2585333 = 242375) (by norm_num)
theorem B2585357 : Blo 1723062 2585357 := bbase (se 3 (by rfl) ⟨484754, by rfl⟩ : syracuseStep 2585357 = 969509) (by norm_num)
theorem B3879701 : Blo 1723062 3879701 := bbase (se 6 (by rfl) ⟨90930, by rfl⟩ : syracuseStep 3879701 = 181861) (by norm_num)
theorem B2585381 : Blo 1723062 2585381 := bbase (se 4 (by rfl) ⟨242379, by rfl⟩ : syracuseStep 2585381 = 484759) (by norm_num)
theorem B2585405 : Blo 1723062 2585405 := bbase (se 3 (by rfl) ⟨484763, by rfl⟩ : syracuseStep 2585405 = 969527) (by norm_num)
theorem B5821253 : Blo 1723062 5821253 := bbase (se 4 (by rfl) ⟨545742, by rfl⟩ : syracuseStep 5821253 = 1091485) (by norm_num)
theorem B4363085 : Blo 1723062 4363085 := bbase (se 3 (by rfl) ⟨818078, by rfl⟩ : syracuseStep 4363085 = 1636157) (by norm_num)
theorem B2585429 : Blo 1723062 2585429 := bbase (se 9 (by rfl) ⟨7574, by rfl⟩ : syracuseStep 2585429 = 15149) (by norm_num)
theorem B3879773 : Blo 1723062 3879773 := bbase (se 3 (by rfl) ⟨727457, by rfl⟩ : syracuseStep 3879773 = 1454915) (by norm_num)
theorem B2585453 : Blo 1723062 2585453 := bbase (se 3 (by rfl) ⟨484772, by rfl⟩ : syracuseStep 2585453 = 969545) (by norm_num)
theorem B2585477 : Blo 1723062 2585477 := bbase (se 4 (by rfl) ⟨242388, by rfl⟩ : syracuseStep 2585477 = 484777) (by norm_num)
theorem B3273605 : Blo 1723062 3273605 := bbase (se 4 (by rfl) ⟨306900, by rfl⟩ : syracuseStep 3273605 = 613801) (by norm_num)
theorem B2585501 : Blo 1723062 2585501 := bbase (se 3 (by rfl) ⟨484781, by rfl⟩ : syracuseStep 2585501 = 969563) (by norm_num)
theorem B3879845 : Blo 1723062 3879845 := bbase (se 4 (by rfl) ⟨363735, by rfl⟩ : syracuseStep 3879845 = 727471) (by norm_num)
theorem B2585525 : Blo 1723062 2585525 := bbase (se 5 (by rfl) ⟨121196, by rfl⟩ : syracuseStep 2585525 = 242393) (by norm_num)
theorem B2585549 : Blo 1723062 2585549 := bbase (se 3 (by rfl) ⟨484790, by rfl⟩ : syracuseStep 2585549 = 969581) (by norm_num)
theorem B2585573 : Blo 1723062 2585573 := bbase (se 4 (by rfl) ⟨242397, by rfl⟩ : syracuseStep 2585573 = 484795) (by norm_num)
theorem B2454509 : Blo 1723062 2454509 := bbase (se 3 (by rfl) ⟨460220, by rfl⟩ : syracuseStep 2454509 = 920441) (by norm_num)
theorem B3879917 : Blo 1723062 3879917 := bbase (se 3 (by rfl) ⟨727484, by rfl⟩ : syracuseStep 3879917 = 1454969) (by norm_num)
theorem B2585597 : Blo 1723062 2585597 := bbase (se 3 (by rfl) ⟨484799, by rfl⟩ : syracuseStep 2585597 = 969599) (by norm_num)
theorem B2585621 : Blo 1723062 2585621 := bbase (se 6 (by rfl) ⟨60600, by rfl⟩ : syracuseStep 2585621 = 121201) (by norm_num)
theorem B1938469 : Blo 1723062 1938469 := bbase (se 4 (by rfl) ⟨181731, by rfl⟩ : syracuseStep 1938469 = 363463) (by norm_num)
theorem B2585645 : Blo 1723062 2585645 := bbase (se 3 (by rfl) ⟨484808, by rfl⟩ : syracuseStep 2585645 = 969617) (by norm_num)
theorem B3879989 : Blo 1723062 3879989 := bbase (se 5 (by rfl) ⟨181874, by rfl⟩ : syracuseStep 3879989 = 363749) (by norm_num)
theorem B2585669 : Blo 1723062 2585669 := bbase (se 4 (by rfl) ⟨242406, by rfl⟩ : syracuseStep 2585669 = 484813) (by norm_num)
theorem B1938505 : Blo 1723062 1938505 := bbase (se 2 (by rfl) ⟨726939, by rfl⟩ : syracuseStep 1938505 = 1453879) (by norm_num)
theorem B2585693 : Blo 1723062 2585693 := bbase (se 3 (by rfl) ⟨484817, by rfl⟩ : syracuseStep 2585693 = 969635) (by norm_num)
theorem B1938541 : Blo 1723062 1938541 := bbase (se 3 (by rfl) ⟨363476, by rfl⟩ : syracuseStep 1938541 = 726953) (by norm_num)
theorem B2585717 : Blo 1723062 2585717 := bbase (se 5 (by rfl) ⟨121205, by rfl⟩ : syracuseStep 2585717 = 242411) (by norm_num)
theorem B3880061 : Blo 1723062 3880061 := bbase (se 3 (by rfl) ⟨727511, by rfl⟩ : syracuseStep 3880061 = 1455023) (by norm_num)
theorem B2585741 : Blo 1723062 2585741 := bbase (se 3 (by rfl) ⟨484826, by rfl⟩ : syracuseStep 2585741 = 969653) (by norm_num)
theorem B1938577 : Blo 1723062 1938577 := bbase (se 2 (by rfl) ⟨726966, by rfl⟩ : syracuseStep 1938577 = 1453933) (by norm_num)
theorem B4363429 : Blo 1723062 4363429 := bbase (se 4 (by rfl) ⟨409071, by rfl⟩ : syracuseStep 4363429 = 818143) (by norm_num)
theorem B2585765 : Blo 1723062 2585765 := bbase (se 4 (by rfl) ⟨242415, by rfl⟩ : syracuseStep 2585765 = 484831) (by norm_num)
theorem B1938613 : Blo 1723062 1938613 := bbase (se 5 (by rfl) ⟨90872, by rfl⟩ : syracuseStep 1938613 = 181745) (by norm_num)
theorem B2585789 : Blo 1723062 2585789 := bbase (se 3 (by rfl) ⟨484835, by rfl⟩ : syracuseStep 2585789 = 969671) (by norm_num)
theorem B3880133 : Blo 1723062 3880133 := bbase (se 4 (by rfl) ⟨363762, by rfl⟩ : syracuseStep 3880133 = 727525) (by norm_num)
theorem B2585813 : Blo 1723062 2585813 := bbase (se 7 (by rfl) ⟨30302, by rfl⟩ : syracuseStep 2585813 = 60605) (by norm_num)
theorem B1938649 : Blo 1723062 1938649 := bbase (se 2 (by rfl) ⟨726993, by rfl⟩ : syracuseStep 1938649 = 1453987) (by norm_num)
theorem B1840357 : Blo 1723062 1840357 := bbase (se 4 (by rfl) ⟨172533, by rfl⟩ : syracuseStep 1840357 = 345067) (by norm_num)
theorem B2585837 : Blo 1723062 2585837 := bbase (se 3 (by rfl) ⟨484844, by rfl⟩ : syracuseStep 2585837 = 969689) (by norm_num)
theorem B5821685 : Blo 1723062 5821685 := bbase (se 5 (by rfl) ⟨272891, by rfl⟩ : syracuseStep 5821685 = 545783) (by norm_num)
theorem B1938685 : Blo 1723062 1938685 := bbase (se 3 (by rfl) ⟨363503, by rfl⟩ : syracuseStep 1938685 = 727007) (by norm_num)
theorem B2585861 : Blo 1723062 2585861 := bbase (se 4 (by rfl) ⟨242424, by rfl⟩ : syracuseStep 2585861 = 484849) (by norm_num)
theorem B3880205 : Blo 1723062 3880205 := bbase (se 3 (by rfl) ⟨727538, by rfl⟩ : syracuseStep 3880205 = 1455077) (by norm_num)
theorem B4363541 : Blo 1723062 4363541 := bbase (se 6 (by rfl) ⟨102270, by rfl⟩ : syracuseStep 4363541 = 204541) (by norm_num)
theorem B2585885 : Blo 1723062 2585885 := bbase (se 3 (by rfl) ⟨484853, by rfl⟩ : syracuseStep 2585885 = 969707) (by norm_num)
theorem B1938721 : Blo 1723062 1938721 := bbase (se 2 (by rfl) ⟨727020, by rfl⟩ : syracuseStep 1938721 = 1454041) (by norm_num)
theorem B1840429 : Blo 1723062 1840429 := bbase (se 3 (by rfl) ⟨345080, by rfl⟩ : syracuseStep 1840429 = 690161) (by norm_num)
theorem B2585909 : Blo 1723062 2585909 := bbase (se 5 (by rfl) ⟨121214, by rfl⟩ : syracuseStep 2585909 = 242429) (by norm_num)
theorem B1938757 : Blo 1723062 1938757 := bbase (se 4 (by rfl) ⟨181758, by rfl⟩ : syracuseStep 1938757 = 363517) (by norm_num)
theorem B2585933 : Blo 1723062 2585933 := bbase (se 3 (by rfl) ⟨484862, by rfl⟩ : syracuseStep 2585933 = 969725) (by norm_num)
theorem B3880277 : Blo 1723062 3880277 := bbase (se 13 (by rfl) ⟨710, by rfl⟩ : syracuseStep 3880277 = 1421) (by norm_num)
theorem B2585957 : Blo 1723062 2585957 := bbase (se 4 (by rfl) ⟨242433, by rfl⟩ : syracuseStep 2585957 = 484867) (by norm_num)
theorem B1938793 : Blo 1723062 1938793 := bbase (se 2 (by rfl) ⟨727047, by rfl⟩ : syracuseStep 1938793 = 1454095) (by norm_num)
theorem B14734709 : Blo 1723062 14734709 := bbase (se 5 (by rfl) ⟨690689, by rfl⟩ : syracuseStep 14734709 = 1381379) (by norm_num)
theorem B2585981 : Blo 1723062 2585981 := bbase (se 3 (by rfl) ⟨484871, by rfl⟩ : syracuseStep 2585981 = 969743) (by norm_num)
theorem B1938829 : Blo 1723062 1938829 := bbase (se 3 (by rfl) ⟨363530, by rfl⟩ : syracuseStep 1938829 = 727061) (by norm_num)
theorem B2586005 : Blo 1723062 2586005 := bbase (se 6 (by rfl) ⟨60609, by rfl⟩ : syracuseStep 2586005 = 121219) (by norm_num)
theorem B3880349 : Blo 1723062 3880349 := bbase (se 3 (by rfl) ⟨727565, by rfl⟩ : syracuseStep 3880349 = 1455131) (by norm_num)
theorem B2586029 : Blo 1723062 2586029 := bbase (se 3 (by rfl) ⟨484880, by rfl⟩ : syracuseStep 2586029 = 969761) (by norm_num)
theorem B1938865 : Blo 1723062 1938865 := bbase (se 2 (by rfl) ⟨727074, by rfl⟩ : syracuseStep 1938865 = 1454149) (by norm_num)
theorem B2586053 : Blo 1723062 2586053 := bbase (se 4 (by rfl) ⟨242442, by rfl⟩ : syracuseStep 2586053 = 484885) (by norm_num)
theorem B3683789 : Blo 1723062 3683789 := bbase (se 3 (by rfl) ⟨690710, by rfl⟩ : syracuseStep 3683789 = 1381421) (by norm_num)
theorem B1938901 : Blo 1723062 1938901 := bbase (se 7 (by rfl) ⟨22721, by rfl⟩ : syracuseStep 1938901 = 45443) (by norm_num)
theorem B4363733 : Blo 1723062 4363733 := bbase (se 7 (by rfl) ⟨51137, by rfl⟩ : syracuseStep 4363733 = 102275) (by norm_num)
theorem B2586077 : Blo 1723062 2586077 := bbase (se 3 (by rfl) ⟨484889, by rfl⟩ : syracuseStep 2586077 = 969779) (by norm_num)
theorem B3880421 : Blo 1723062 3880421 := bbase (se 4 (by rfl) ⟨363789, by rfl⟩ : syracuseStep 3880421 = 727579) (by norm_num)
theorem B2586101 : Blo 1723062 2586101 := bbase (se 5 (by rfl) ⟨121223, by rfl⟩ : syracuseStep 2586101 = 242447) (by norm_num)
theorem B1938937 : Blo 1723062 1938937 := bbase (se 2 (by rfl) ⟨727101, by rfl⟩ : syracuseStep 1938937 = 1454203) (by norm_num)
theorem B2586125 : Blo 1723062 2586125 := bbase (se 3 (by rfl) ⟨484898, by rfl⟩ : syracuseStep 2586125 = 969797) (by norm_num)
theorem B2070041 : Blo 1723062 2070041 := bbase (se 2 (by rfl) ⟨776265, by rfl⟩ : syracuseStep 2070041 = 1552531) (by norm_num)
theorem B1938973 : Blo 1723062 1938973 := bbase (se 3 (by rfl) ⟨363557, by rfl⟩ : syracuseStep 1938973 = 727115) (by norm_num)
theorem B2586149 : Blo 1723062 2586149 := bbase (se 4 (by rfl) ⟨242451, by rfl⟩ : syracuseStep 2586149 = 484903) (by norm_num)
theorem B3880493 : Blo 1723062 3880493 := bbase (se 3 (by rfl) ⟨727592, by rfl⟩ : syracuseStep 3880493 = 1455185) (by norm_num)
theorem B2586173 : Blo 1723062 2586173 := bbase (se 3 (by rfl) ⟨484907, by rfl⟩ : syracuseStep 2586173 = 969815) (by norm_num)
theorem B1939009 : Blo 1723062 1939009 := bbase (se 2 (by rfl) ⟨727128, by rfl⟩ : syracuseStep 1939009 = 1454257) (by norm_num)
theorem B4421189 : Blo 1723062 4421189 := bbase (se 4 (by rfl) ⟨414486, by rfl⟩ : syracuseStep 4421189 = 828973) (by norm_num)
theorem B2586197 : Blo 1723062 2586197 := bbase (se 8 (by rfl) ⟨15153, by rfl⟩ : syracuseStep 2586197 = 30307) (by norm_num)
theorem B1939045 : Blo 1723062 1939045 := bbase (se 4 (by rfl) ⟨181785, by rfl⟩ : syracuseStep 1939045 = 363571) (by norm_num)
theorem B2586221 : Blo 1723062 2586221 := bbase (se 3 (by rfl) ⟨484916, by rfl⟩ : syracuseStep 2586221 = 969833) (by norm_num)
theorem B3880565 : Blo 1723062 3880565 := bbase (se 5 (by rfl) ⟨181901, by rfl⟩ : syracuseStep 3880565 = 363803) (by norm_num)
theorem B3274357 : Blo 1723062 3274357 := bbase (se 5 (by rfl) ⟨153485, by rfl⟩ : syracuseStep 3274357 = 306971) (by norm_num)
theorem B2070137 : Blo 1723062 2070137 := bbase (se 2 (by rfl) ⟨776301, by rfl⟩ : syracuseStep 2070137 = 1552603) (by norm_num)
theorem B2586245 : Blo 1723062 2586245 := bbase (se 4 (by rfl) ⟨242460, by rfl⟩ : syracuseStep 2586245 = 484921) (by norm_num)
theorem B1939081 : Blo 1723062 1939081 := bbase (se 2 (by rfl) ⟨727155, by rfl⟩ : syracuseStep 1939081 = 1454311) (by norm_num)
theorem B2586269 : Blo 1723062 2586269 := bbase (se 3 (by rfl) ⟨484925, by rfl⟩ : syracuseStep 2586269 = 969851) (by norm_num)
theorem B1840801 : Blo 1723062 1840801 := bbase (se 2 (by rfl) ⟨690300, by rfl⟩ : syracuseStep 1840801 = 1380601) (by norm_num)
theorem B1939117 : Blo 1723062 1939117 := bbase (se 3 (by rfl) ⟨363584, by rfl⟩ : syracuseStep 1939117 = 727169) (by norm_num)
theorem B2586293 : Blo 1723062 2586293 := bbase (se 5 (by rfl) ⟨121232, by rfl⟩ : syracuseStep 2586293 = 242465) (by norm_num)
theorem B3880637 : Blo 1723062 3880637 := bbase (se 3 (by rfl) ⟨727619, by rfl⟩ : syracuseStep 3880637 = 1455239) (by norm_num)
theorem B2586317 : Blo 1723062 2586317 := bbase (se 3 (by rfl) ⟨484934, by rfl⟩ : syracuseStep 2586317 = 969869) (by norm_num)
theorem B1939153 : Blo 1723062 1939153 := bbase (se 2 (by rfl) ⟨727182, by rfl⟩ : syracuseStep 1939153 = 1454365) (by norm_num)
theorem B2586341 : Blo 1723062 2586341 := bbase (se 4 (by rfl) ⟨242469, by rfl⟩ : syracuseStep 2586341 = 484939) (by norm_num)
theorem B8730341 : Blo 1723062 8730341 := bbase (se 4 (by rfl) ⟨818469, by rfl⟩ : syracuseStep 8730341 = 1636939) (by norm_num)
theorem B4658933 : Blo 1723062 4658933 := bbase (se 5 (by rfl) ⟨218387, by rfl⟩ : syracuseStep 4658933 = 436775) (by norm_num)
theorem B1939189 : Blo 1723062 1939189 := bbase (se 5 (by rfl) ⟨90899, by rfl⟩ : syracuseStep 1939189 = 181799) (by norm_num)
theorem B2586365 : Blo 1723062 2586365 := bbase (se 3 (by rfl) ⟨484943, by rfl⟩ : syracuseStep 2586365 = 969887) (by norm_num)
theorem B3880709 : Blo 1723062 3880709 := bbase (se 4 (by rfl) ⟨363816, by rfl⟩ : syracuseStep 3880709 = 727633) (by norm_num)
theorem B3274501 : Blo 1723062 3274501 := bbase (se 4 (by rfl) ⟨306984, by rfl⟩ : syracuseStep 3274501 = 613969) (by norm_num)
theorem B6543125 : Blo 1723062 6543125 := bbase (se 6 (by rfl) ⟨153354, by rfl⟩ : syracuseStep 6543125 = 306709) (by norm_num)
theorem B2586389 : Blo 1723062 2586389 := bbase (se 6 (by rfl) ⟨60618, by rfl⟩ : syracuseStep 2586389 = 121237) (by norm_num)
theorem B1939225 : Blo 1723062 1939225 := bbase (se 2 (by rfl) ⟨727209, by rfl⟩ : syracuseStep 1939225 = 1454419) (by norm_num)
theorem B2070301 : Blo 1723062 2070301 := bbase (se 3 (by rfl) ⟨388181, by rfl⟩ : syracuseStep 2070301 = 776363) (by norm_num)
theorem B4364077 : Blo 1723062 4364077 := bbase (se 3 (by rfl) ⟨818264, by rfl⟩ : syracuseStep 4364077 = 1636529) (by norm_num)
theorem B2586413 : Blo 1723062 2586413 := bbase (se 3 (by rfl) ⟨484952, by rfl⟩ : syracuseStep 2586413 = 969905) (by norm_num)
theorem B1939261 : Blo 1723062 1939261 := bbase (se 3 (by rfl) ⟨363611, by rfl⟩ : syracuseStep 1939261 = 727223) (by norm_num)
theorem B2586437 : Blo 1723062 2586437 := bbase (se 4 (by rfl) ⟨242478, by rfl⟩ : syracuseStep 2586437 = 484957) (by norm_num)
theorem B3495757 : Blo 1723062 3495757 := bbase (se 3 (by rfl) ⟨655454, by rfl⟩ : syracuseStep 3495757 = 1310909) (by norm_num)
theorem B3880781 : Blo 1723062 3880781 := bbase (se 3 (by rfl) ⟨727646, by rfl⟩ : syracuseStep 3880781 = 1455293) (by norm_num)
theorem B2586461 : Blo 1723062 2586461 := bbase (se 3 (by rfl) ⟨484961, by rfl⟩ : syracuseStep 2586461 = 969923) (by norm_num)
theorem B1939297 : Blo 1723062 1939297 := bbase (se 2 (by rfl) ⟨727236, by rfl⟩ : syracuseStep 1939297 = 1454473) (by norm_num)
theorem B2586485 : Blo 1723062 2586485 := bbase (se 5 (by rfl) ⟨121241, by rfl⟩ : syracuseStep 2586485 = 242483) (by norm_num)
theorem B1939333 : Blo 1723062 1939333 := bbase (se 4 (by rfl) ⟨181812, by rfl⟩ : syracuseStep 1939333 = 363625) (by norm_num)
theorem B2586509 : Blo 1723062 2586509 := bbase (se 3 (by rfl) ⟨484970, by rfl⟩ : syracuseStep 2586509 = 969941) (by norm_num)
theorem B3880853 : Blo 1723062 3880853 := bbase (se 6 (by rfl) ⟨90957, by rfl⟩ : syracuseStep 3880853 = 181915) (by norm_num)
theorem B4364189 : Blo 1723062 4364189 := bbase (se 3 (by rfl) ⟨818285, by rfl⟩ : syracuseStep 4364189 = 1636571) (by norm_num)
theorem B2586533 : Blo 1723062 2586533 := bbase (se 4 (by rfl) ⟨242487, by rfl⟩ : syracuseStep 2586533 = 484975) (by norm_num)
theorem B3274661 : Blo 1723062 3274661 := bbase (se 4 (by rfl) ⟨306999, by rfl⟩ : syracuseStep 3274661 = 613999) (by norm_num)
theorem B1939369 : Blo 1723062 1939369 := bbase (se 2 (by rfl) ⟨727263, by rfl⟩ : syracuseStep 1939369 = 1454527) (by norm_num)
theorem B2586557 : Blo 1723062 2586557 := bbase (se 3 (by rfl) ⟨484979, by rfl⟩ : syracuseStep 2586557 = 969959) (by norm_num)
theorem B1939405 : Blo 1723062 1939405 := bbase (se 3 (by rfl) ⟨363638, by rfl⟩ : syracuseStep 1939405 = 727277) (by norm_num)
theorem B2586581 : Blo 1723062 2586581 := bbase (se 7 (by rfl) ⟨30311, by rfl⟩ : syracuseStep 2586581 = 60623) (by norm_num)
theorem B13277141 : Blo 1723062 13277141 := bbase (se 7 (by rfl) ⟨155591, by rfl⟩ : syracuseStep 13277141 = 311183) (by norm_num)
theorem B3880925 : Blo 1723062 3880925 := bbase (se 3 (by rfl) ⟨727673, by rfl⟩ : syracuseStep 3880925 = 1455347) (by norm_num)
theorem B2586605 : Blo 1723062 2586605 := bbase (se 3 (by rfl) ⟨484988, by rfl⟩ : syracuseStep 2586605 = 969977) (by norm_num)
theorem B1939441 : Blo 1723062 1939441 := bbase (se 2 (by rfl) ⟨727290, by rfl⟩ : syracuseStep 1939441 = 1454581) (by norm_num)
theorem B2070517 : Blo 1723062 2070517 := bbase (se 5 (by rfl) ⟨97055, by rfl⟩ : syracuseStep 2070517 = 194111) (by norm_num)
theorem B2586629 : Blo 1723062 2586629 := bbase (se 4 (by rfl) ⟨242496, by rfl⟩ : syracuseStep 2586629 = 484993) (by norm_num)
theorem B2488333 : Blo 1723062 2488333 := bbase (se 3 (by rfl) ⟨466562, by rfl⟩ : syracuseStep 2488333 = 933125) (by norm_num)
theorem B8280085 : Blo 1723062 8280085 := bbase (se 6 (by rfl) ⟨194064, by rfl⟩ : syracuseStep 8280085 = 388129) (by norm_num)
theorem B1939477 : Blo 1723062 1939477 := bbase (se 6 (by rfl) ⟨45456, by rfl⟩ : syracuseStep 1939477 = 90913) (by norm_num)
theorem B1841177 : Blo 1723062 1841177 := bbase (se 2 (by rfl) ⟨690441, by rfl⟩ : syracuseStep 1841177 = 1380883) (by norm_num)
theorem B2586653 : Blo 1723062 2586653 := bbase (se 3 (by rfl) ⟨484997, by rfl⟩ : syracuseStep 2586653 = 969995) (by norm_num)
theorem B6215717 : Blo 1723062 6215717 := bbase (se 4 (by rfl) ⟨582723, by rfl⟩ : syracuseStep 6215717 = 1165447) (by norm_num)
theorem B3880997 : Blo 1723062 3880997 := bbase (se 4 (by rfl) ⟨363843, by rfl⟩ : syracuseStep 3880997 = 727687) (by norm_num)
theorem B6543413 : Blo 1723062 6543413 := bbase (se 5 (by rfl) ⟨306722, by rfl⟩ : syracuseStep 6543413 = 613445) (by norm_num)
theorem B2586677 : Blo 1723062 2586677 := bbase (se 5 (by rfl) ⟨121250, by rfl⟩ : syracuseStep 2586677 = 242501) (by norm_num)
theorem B3274805 : Blo 1723062 3274805 := bbase (se 5 (by rfl) ⟨153506, by rfl⟩ : syracuseStep 3274805 = 307013) (by norm_num)
theorem B1939513 : Blo 1723062 1939513 := bbase (se 2 (by rfl) ⟨727317, by rfl⟩ : syracuseStep 1939513 = 1454635) (by norm_num)
theorem B2586701 : Blo 1723062 2586701 := bbase (se 3 (by rfl) ⟨485006, by rfl⟩ : syracuseStep 2586701 = 970013) (by norm_num)
theorem B1939549 : Blo 1723062 1939549 := bbase (se 3 (by rfl) ⟨363665, by rfl⟩ : syracuseStep 1939549 = 727331) (by norm_num)
theorem B4364381 : Blo 1723062 4364381 := bbase (se 3 (by rfl) ⟨818321, by rfl⟩ : syracuseStep 4364381 = 1636643) (by norm_num)
theorem B1841249 : Blo 1723062 1841249 := bbase (se 2 (by rfl) ⟨690468, by rfl⟩ : syracuseStep 1841249 = 1380937) (by norm_num)
theorem B2586725 : Blo 1723062 2586725 := bbase (se 4 (by rfl) ⟨242505, by rfl⟩ : syracuseStep 2586725 = 485011) (by norm_num)
theorem B3881069 : Blo 1723062 3881069 := bbase (se 3 (by rfl) ⟨727700, by rfl⟩ : syracuseStep 3881069 = 1455401) (by norm_num)
theorem B2586749 : Blo 1723062 2586749 := bbase (se 3 (by rfl) ⟨485015, by rfl⟩ : syracuseStep 2586749 = 970031) (by norm_num)
theorem B1939585 : Blo 1723062 1939585 := bbase (se 2 (by rfl) ⟨727344, by rfl⟩ : syracuseStep 1939585 = 1454689) (by norm_num)
theorem B3315853 : Blo 1723062 3315853 := bbase (se 3 (by rfl) ⟨621722, by rfl⟩ : syracuseStep 3315853 = 1243445) (by norm_num)
theorem B2586773 : Blo 1723062 2586773 := bbase (se 6 (by rfl) ⟨60627, by rfl⟩ : syracuseStep 2586773 = 121255) (by norm_num)
theorem B2070685 : Blo 1723062 2070685 := bbase (se 3 (by rfl) ⟨388253, by rfl⟩ : syracuseStep 2070685 = 776507) (by norm_num)
theorem B1939621 : Blo 1723062 1939621 := bbase (se 4 (by rfl) ⟨181839, by rfl⟩ : syracuseStep 1939621 = 363679) (by norm_num)
theorem B2586797 : Blo 1723062 2586797 := bbase (se 3 (by rfl) ⟨485024, by rfl⟩ : syracuseStep 2586797 = 970049) (by norm_num)
theorem B3881141 : Blo 1723062 3881141 := bbase (se 5 (by rfl) ⟨181928, by rfl⟩ : syracuseStep 3881141 = 363857) (by norm_num)
theorem B1865921 : Blo 1723062 1865921 := bbase (se 2 (by rfl) ⟨699720, by rfl⟩ : syracuseStep 1865921 = 1399441) (by norm_num)
theorem B2586821 : Blo 1723062 2586821 := bbase (se 4 (by rfl) ⟨242514, by rfl⟩ : syracuseStep 2586821 = 485029) (by norm_num)
theorem B1939657 : Blo 1723062 1939657 := bbase (se 2 (by rfl) ⟨727371, by rfl⟩ : syracuseStep 1939657 = 1454743) (by norm_num)
theorem B2586845 : Blo 1723062 2586845 := bbase (se 3 (by rfl) ⟨485033, by rfl⟩ : syracuseStep 2586845 = 970067) (by norm_num)
theorem B1939693 : Blo 1723062 1939693 := bbase (se 3 (by rfl) ⟨363692, by rfl⟩ : syracuseStep 1939693 = 727385) (by norm_num)
theorem B4143349 : Blo 1723062 4143349 := bbase (se 5 (by rfl) ⟨194219, by rfl⟩ : syracuseStep 4143349 = 388439) (by norm_num)
theorem B2586869 : Blo 1723062 2586869 := bbase (se 5 (by rfl) ⟨121259, by rfl⟩ : syracuseStep 2586869 = 242519) (by norm_num)
theorem B3881213 : Blo 1723062 3881213 := bbase (se 3 (by rfl) ⟨727727, by rfl⟩ : syracuseStep 3881213 = 1455455) (by norm_num)
theorem B2586893 : Blo 1723062 2586893 := bbase (se 3 (by rfl) ⟨485042, by rfl⟩ : syracuseStep 2586893 = 970085) (by norm_num)
theorem B1939729 : Blo 1723062 1939729 := bbase (se 2 (by rfl) ⟨727398, by rfl⟩ : syracuseStep 1939729 = 1454797) (by norm_num)
theorem B1841437 : Blo 1723062 1841437 := bbase (se 3 (by rfl) ⟨345269, by rfl⟩ : syracuseStep 1841437 = 690539) (by norm_num)
theorem B2586917 : Blo 1723062 2586917 := bbase (se 4 (by rfl) ⟨242523, by rfl⟩ : syracuseStep 2586917 = 485047) (by norm_num)
theorem B1939765 : Blo 1723062 1939765 := bbase (se 5 (by rfl) ⟨90926, by rfl⟩ : syracuseStep 1939765 = 181853) (by norm_num)
theorem B2586941 : Blo 1723062 2586941 := bbase (se 3 (by rfl) ⟨485051, by rfl⟩ : syracuseStep 2586941 = 970103) (by norm_num)
theorem B3881285 : Blo 1723062 3881285 := bbase (se 4 (by rfl) ⟨363870, by rfl⟩ : syracuseStep 3881285 = 727741) (by norm_num)
theorem B3496277 : Blo 1723062 3496277 := bbase (se 10 (by rfl) ⟨5121, by rfl⟩ : syracuseStep 3496277 = 10243) (by norm_num)
theorem B2586965 : Blo 1723062 2586965 := bbase (se 10 (by rfl) ⟨3789, by rfl⟩ : syracuseStep 2586965 = 7579) (by norm_num)
theorem B1939801 : Blo 1723062 1939801 := bbase (se 2 (by rfl) ⟨727425, by rfl⟩ : syracuseStep 1939801 = 1454851) (by norm_num)
theorem B2586989 : Blo 1723062 2586989 := bbase (se 3 (by rfl) ⟨485060, by rfl⟩ : syracuseStep 2586989 = 970121) (by norm_num)
theorem B1939837 : Blo 1723062 1939837 := bbase (se 3 (by rfl) ⟨363719, by rfl⟩ : syracuseStep 1939837 = 727439) (by norm_num)
theorem B2455933 : Blo 1723062 2455933 := bbase (se 3 (by rfl) ⟨460487, by rfl⟩ : syracuseStep 2455933 = 920975) (by norm_num)
theorem B2587013 : Blo 1723062 2587013 := bbase (se 4 (by rfl) ⟨242532, by rfl⟩ : syracuseStep 2587013 = 485065) (by norm_num)
theorem B3881357 : Blo 1723062 3881357 := bbase (se 3 (by rfl) ⟨727754, by rfl⟩ : syracuseStep 3881357 = 1455509) (by norm_num)
theorem B2587037 : Blo 1723062 2587037 := bbase (se 3 (by rfl) ⟨485069, by rfl⟩ : syracuseStep 2587037 = 970139) (by norm_num)
theorem B1939873 : Blo 1723062 1939873 := bbase (se 2 (by rfl) ⟨727452, by rfl⟩ : syracuseStep 1939873 = 1454905) (by norm_num)
theorem B4364725 : Blo 1723062 4364725 := bbase (se 5 (by rfl) ⟨204596, by rfl⟩ : syracuseStep 4364725 = 409193) (by norm_num)
theorem B3496373 : Blo 1723062 3496373 := bbase (se 5 (by rfl) ⟨163892, by rfl⟩ : syracuseStep 3496373 = 327785) (by norm_num)
theorem B2587061 : Blo 1723062 2587061 := bbase (se 5 (by rfl) ⟨121268, by rfl⟩ : syracuseStep 2587061 = 242537) (by norm_num)
theorem B1939909 : Blo 1723062 1939909 := bbase (se 4 (by rfl) ⟨181866, by rfl⟩ : syracuseStep 1939909 = 363733) (by norm_num)
theorem B2587085 : Blo 1723062 2587085 := bbase (se 3 (by rfl) ⟨485078, by rfl⟩ : syracuseStep 2587085 = 970157) (by norm_num)
theorem B1841621 : Blo 1723062 1841621 := bbase (se 7 (by rfl) ⟨21581, by rfl⟩ : syracuseStep 1841621 = 43163) (by norm_num)
theorem B2587109 : Blo 1723062 2587109 := bbase (se 4 (by rfl) ⟨242541, by rfl⟩ : syracuseStep 2587109 = 485083) (by norm_num)
theorem B1939945 : Blo 1723062 1939945 := bbase (se 2 (by rfl) ⟨727479, by rfl⟩ : syracuseStep 1939945 = 1454959) (by norm_num)
theorem B2587133 : Blo 1723062 2587133 := bbase (se 3 (by rfl) ⟨485087, by rfl⟩ : syracuseStep 2587133 = 970175) (by norm_num)
theorem B1939981 : Blo 1723062 1939981 := bbase (se 3 (by rfl) ⟨363746, by rfl⟩ : syracuseStep 1939981 = 727493) (by norm_num)
theorem B2587157 : Blo 1723062 2587157 := bbase (se 6 (by rfl) ⟨60636, by rfl⟩ : syracuseStep 2587157 = 121273) (by norm_num)
theorem B4364837 : Blo 1723062 4364837 := bbase (se 4 (by rfl) ⟨409203, by rfl⟩ : syracuseStep 4364837 = 818407) (by norm_num)
theorem B2587181 : Blo 1723062 2587181 := bbase (se 3 (by rfl) ⟨485096, by rfl⟩ : syracuseStep 2587181 = 970193) (by norm_num)
theorem B1940017 : Blo 1723062 1940017 := bbase (se 2 (by rfl) ⟨727506, by rfl⟩ : syracuseStep 1940017 = 1455013) (by norm_num)
theorem B2587205 : Blo 1723062 2587205 := bbase (se 4 (by rfl) ⟨242550, by rfl⟩ : syracuseStep 2587205 = 485101) (by norm_num)
theorem B4659797 : Blo 1723062 4659797 := bbase (se 8 (by rfl) ⟨27303, by rfl⟩ : syracuseStep 4659797 = 54607) (by norm_num)
theorem B1940053 : Blo 1723062 1940053 := bbase (se 8 (by rfl) ⟨11367, by rfl⟩ : syracuseStep 1940053 = 22735) (by norm_num)
theorem B2587229 : Blo 1723062 2587229 := bbase (se 3 (by rfl) ⟨485105, by rfl⟩ : syracuseStep 2587229 = 970211) (by norm_num)
theorem B2587253 : Blo 1723062 2587253 := bbase (se 5 (by rfl) ⟨121277, by rfl⟩ : syracuseStep 2587253 = 242555) (by norm_num)
theorem B1940089 : Blo 1723062 1940089 := bbase (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) (by norm_num)
theorem B2587277 : Blo 1723062 2587277 := bbase (se 3 (by rfl) ⟨485114, by rfl⟩ : syracuseStep 2587277 = 970229) (by norm_num)
theorem B5241493 : Blo 1723062 5241493 := bbase (se 6 (by rfl) ⟨122847, by rfl⟩ : syracuseStep 5241493 = 245695) (by norm_num)
theorem B1940125 : Blo 1723062 1940125 := bbase (se 3 (by rfl) ⟨363773, by rfl⟩ : syracuseStep 1940125 = 727547) (by norm_num)
theorem B4143773 : Blo 1723062 4143773 := bbase (se 3 (by rfl) ⟨776957, by rfl⟩ : syracuseStep 4143773 = 1553915) (by norm_num)
theorem B2587301 : Blo 1723062 2587301 := bbase (se 4 (by rfl) ⟨242559, by rfl⟩ : syracuseStep 2587301 = 485119) (by norm_num)
theorem B2071213 : Blo 1723062 2071213 := bbase (se 3 (by rfl) ⟨388352, by rfl⟩ : syracuseStep 2071213 = 776705) (by norm_num)
theorem B2587325 : Blo 1723062 2587325 := bbase (se 3 (by rfl) ⟨485123, by rfl⟩ : syracuseStep 2587325 = 970247) (by norm_num)
theorem B1940161 : Blo 1723062 1940161 := bbase (se 2 (by rfl) ⟨727560, by rfl⟩ : syracuseStep 1940161 = 1455121) (by norm_num)
theorem B5896901 : Blo 1723062 5896901 := bbase (se 4 (by rfl) ⟨552834, by rfl⟩ : syracuseStep 5896901 = 1105669) (by norm_num)
theorem B3234517 : Blo 1723062 3234517 := bbase (se 7 (by rfl) ⟨37904, by rfl⟩ : syracuseStep 3234517 = 75809) (by norm_num)
theorem B2587349 : Blo 1723062 2587349 := bbase (se 7 (by rfl) ⟨30320, by rfl⟩ : syracuseStep 2587349 = 60641) (by norm_num)
theorem B4365029 : Blo 1723062 4365029 := bbase (se 4 (by rfl) ⟨409221, by rfl⟩ : syracuseStep 4365029 = 818443) (by norm_num)
theorem B1940197 : Blo 1723062 1940197 := bbase (se 4 (by rfl) ⟨181893, by rfl⟩ : syracuseStep 1940197 = 363787) (by norm_num)
theorem B2587373 : Blo 1723062 2587373 := bbase (se 3 (by rfl) ⟨485132, by rfl⟩ : syracuseStep 2587373 = 970265) (by norm_num)
theorem B2587397 : Blo 1723062 2587397 := bbase (se 4 (by rfl) ⟨242568, by rfl⟩ : syracuseStep 2587397 = 485137) (by norm_num)
theorem B1940233 : Blo 1723062 1940233 := bbase (se 2 (by rfl) ⟨727587, by rfl⟩ : syracuseStep 1940233 = 1455175) (by norm_num)
theorem B2587421 : Blo 1723062 2587421 := bbase (se 3 (by rfl) ⟨485141, by rfl⟩ : syracuseStep 2587421 = 970283) (by norm_num)
theorem B1940269 : Blo 1723062 1940269 := bbase (se 3 (by rfl) ⟨363800, by rfl⟩ : syracuseStep 1940269 = 727601) (by norm_num)
theorem B2587445 : Blo 1723062 2587445 := bbase (se 5 (by rfl) ⟨121286, by rfl⟩ : syracuseStep 2587445 = 242573) (by norm_num)
theorem B2587469 : Blo 1723062 2587469 := bbase (se 3 (by rfl) ⟨485150, by rfl⟩ : syracuseStep 2587469 = 970301) (by norm_num)
theorem B1940305 : Blo 1723062 1940305 := bbase (se 2 (by rfl) ⟨727614, by rfl⟩ : syracuseStep 1940305 = 1455229) (by norm_num)
theorem B2587493 : Blo 1723062 2587493 := bbase (se 4 (by rfl) ⟨242577, by rfl⟩ : syracuseStep 2587493 = 485155) (by norm_num)
theorem B1940341 : Blo 1723062 1940341 := bbase (se 5 (by rfl) ⟨90953, by rfl⟩ : syracuseStep 1940341 = 181907) (by norm_num)
theorem B2587517 : Blo 1723062 2587517 := bbase (se 3 (by rfl) ⟨485159, by rfl⟩ : syracuseStep 2587517 = 970319) (by norm_num)
theorem B2587541 : Blo 1723062 2587541 := bbase (se 6 (by rfl) ⟨60645, by rfl⟩ : syracuseStep 2587541 = 121291) (by norm_num)
theorem B1940377 : Blo 1723062 1940377 := bbase (se 2 (by rfl) ⟨727641, by rfl⟩ : syracuseStep 1940377 = 1455283) (by norm_num)
theorem B7363493 : Blo 1723062 7363493 := bbase (se 4 (by rfl) ⟨690327, by rfl⟩ : syracuseStep 7363493 = 1380655) (by norm_num)
theorem B2587565 : Blo 1723062 2587565 := bbase (se 3 (by rfl) ⟨485168, by rfl⟩ : syracuseStep 2587565 = 970337) (by norm_num)
theorem B4144061 : Blo 1723062 4144061 := bbase (se 3 (by rfl) ⟨777011, by rfl⟩ : syracuseStep 4144061 = 1554023) (by norm_num)
theorem B1940413 : Blo 1723062 1940413 := bbase (se 3 (by rfl) ⟨363827, by rfl⟩ : syracuseStep 1940413 = 727655) (by norm_num)
theorem B2587589 : Blo 1723062 2587589 := bbase (se 4 (by rfl) ⟨242586, by rfl⟩ : syracuseStep 2587589 = 485173) (by norm_num)
theorem B1940449 : Blo 1723062 1940449 := bbase (se 2 (by rfl) ⟨727668, by rfl⟩ : syracuseStep 1940449 = 1455337) (by norm_num)
theorem B8731637 : Blo 1723062 8731637 := bbase (se 5 (by rfl) ⟨409295, by rfl⟩ : syracuseStep 8731637 = 818591) (by norm_num)
theorem B1940485 : Blo 1723062 1940485 := bbase (se 4 (by rfl) ⟨181920, by rfl⟩ : syracuseStep 1940485 = 363841) (by norm_num)
theorem B1940521 : Blo 1723062 1940521 := bbase (se 2 (by rfl) ⟨727695, by rfl⟩ : syracuseStep 1940521 = 1455391) (by norm_num)
theorem B4365373 : Blo 1723062 4365373 := bbase (se 3 (by rfl) ⟨818507, by rfl⟩ : syracuseStep 4365373 = 1637015) (by norm_num)
theorem B1940557 : Blo 1723062 1940557 := bbase (se 3 (by rfl) ⟨363854, by rfl⟩ : syracuseStep 1940557 = 727709) (by norm_num)
theorem B1940593 : Blo 1723062 1940593 := bbase (se 2 (by rfl) ⟨727722, by rfl⟩ : syracuseStep 1940593 = 1455445) (by norm_num)
theorem B1940629 : Blo 1723062 1940629 := bbase (se 6 (by rfl) ⟨45483, by rfl⟩ : syracuseStep 1940629 = 90967) (by norm_num)
theorem B4365485 : Blo 1723062 4365485 := bbase (se 3 (by rfl) ⟨818528, by rfl⟩ : syracuseStep 4365485 = 1637057) (by norm_num)
theorem B1940665 : Blo 1723062 1940665 := bbase (se 2 (by rfl) ⟨727749, by rfl⟩ : syracuseStep 1940665 = 1455499) (by norm_num)
theorem B6544597 : Blo 1723062 6544597 := bbase (se 7 (by rfl) ⟨76694, by rfl⟩ : syracuseStep 6544597 = 153389) (by norm_num)
theorem B55934165 : Blo 1723062 55934165 := bbase (se 7 (by rfl) ⟨655478, by rfl⟩ : syracuseStep 55934165 = 1310957) (by norm_num)
theorem B51092693 : Blo 1723062 51092693 := bbase (se 7 (by rfl) ⟨598742, by rfl⟩ : syracuseStep 51092693 = 1197485) (by norm_num)
theorem B8633573 : Blo 1723062 8633573 := bbase (se 4 (by rfl) ⟨809397, by rfl⟩ : syracuseStep 8633573 = 1618795) (by norm_num)
theorem B15719669 : Blo 1723062 15719669 := bbase (se 5 (by rfl) ⟨736859, by rfl⟩ : syracuseStep 15719669 = 1473719) (by norm_num)
theorem B5815637 : Blo 1723062 5815637 := bbase (se 11 (by rfl) ⟨4259, by rfl⟩ : syracuseStep 5815637 = 8519) (by norm_num)
theorem B1965397 : Blo 1723062 1965397 := bbase (se 11 (by rfl) ⟨1439, by rfl⟩ : syracuseStep 1965397 = 2879) (by norm_num)
theorem B4365677 : Blo 1723062 4365677 := bbase (se 3 (by rfl) ⟨818564, by rfl⟩ : syracuseStep 4365677 = 1637129) (by norm_num)
theorem B8723861 : Blo 1723062 8723861 := bbase (se 6 (by rfl) ⟨204465, by rfl⟩ : syracuseStep 8723861 = 408931) (by norm_num)
theorem B6544901 : Blo 1723062 6544901 := bbase (se 4 (by rfl) ⟨613584, by rfl⟩ : syracuseStep 6544901 = 1227169) (by norm_num)
theorem B1965593 : Blo 1723062 1965593 := bbase (se 2 (by rfl) ⟨737097, by rfl⟩ : syracuseStep 1965593 = 1474195) (by norm_num)
theorem B2907677 : Blo 1723062 2907677 := bbase (se 3 (by rfl) ⟨545189, by rfl⟩ : syracuseStep 2907677 = 1090379) (by norm_num)
theorem B2907805 : Blo 1723062 2907805 := bbase (se 3 (by rfl) ⟨545213, by rfl⟩ : syracuseStep 2907805 = 1090427) (by norm_num)
theorem B4366021 : Blo 1723062 4366021 := bbase (se 4 (by rfl) ⟨409314, by rfl⟩ : syracuseStep 4366021 = 818629) (by norm_num)
theorem B2907893 : Blo 1723062 2907893 := bbase (se 5 (by rfl) ⟨136307, by rfl⟩ : syracuseStep 2907893 = 272615) (by norm_num)
theorem B2072309 : Blo 1723062 2072309 := bbase (se 5 (by rfl) ⟨97139, by rfl⟩ : syracuseStep 2072309 = 194279) (by norm_num)
theorem B5816069 : Blo 1723062 5816069 := bbase (se 4 (by rfl) ⟨545256, by rfl⟩ : syracuseStep 5816069 = 1090513) (by norm_num)
theorem B4366133 : Blo 1723062 4366133 := bbase (se 5 (by rfl) ⟨204662, by rfl⟩ : syracuseStep 4366133 = 409325) (by norm_num)
theorem B1965889 : Blo 1723062 1965889 := bbase (se 2 (by rfl) ⟨737208, by rfl⟩ : syracuseStep 1965889 = 1474417) (by norm_num)
theorem B2908021 : Blo 1723062 2908021 := bbase (se 5 (by rfl) ⟨136313, by rfl⟩ : syracuseStep 2908021 = 272627) (by norm_num)
theorem B3317701 : Blo 1723062 3317701 := bbase (se 4 (by rfl) ⟨311034, by rfl⟩ : syracuseStep 3317701 = 622069) (by norm_num)
theorem B2908109 : Blo 1723062 2908109 := bbase (se 3 (by rfl) ⟨545270, by rfl⟩ : syracuseStep 2908109 = 1090541) (by norm_num)
theorem B4423661 : Blo 1723062 4423661 := bbase (se 3 (by rfl) ⟨829436, by rfl⟩ : syracuseStep 4423661 = 1658873) (by norm_num)
theorem B12427253 : Blo 1723062 12427253 := bbase (se 5 (by rfl) ⟨582527, by rfl⟩ : syracuseStep 12427253 = 1165055) (by norm_num)
theorem B4366325 : Blo 1723062 4366325 := bbase (se 5 (by rfl) ⟨204671, by rfl⟩ : syracuseStep 4366325 = 409343) (by norm_num)
theorem B2908163 : Blo 1723062 2908163 := bstep (se 1 (by rfl) ⟨2181122, by rfl⟩ : syracuseStep 2908163 = 4362245) B4362245
theorem B7364621 : Blo 1723062 7364621 := bstep (se 3 (by rfl) ⟨1380866, by rfl⟩ : syracuseStep 7364621 = 2761733) B2761733
theorem B3317777 : Blo 1723062 3317777 := bstep (se 2 (by rfl) ⟨1244166, by rfl⟩ : syracuseStep 3317777 = 2488333) B2488333
theorem B10633315 : Blo 1723062 10633315 := bstep (se 1 (by rfl) ⟨7974986, by rfl⟩ : syracuseStep 10633315 = 15949973) B15949973
theorem B8732771 : Blo 1723062 8732771 := bstep (se 1 (by rfl) ⟨6549578, by rfl⟩ : syracuseStep 8732771 = 13099157) B13099157
theorem B2908291 : Blo 1723062 2908291 := bstep (se 1 (by rfl) ⟨2181218, by rfl⟩ : syracuseStep 2908291 = 4362437) B4362437
theorem B3317923 : Blo 1723062 3317923 := bstep (se 1 (by rfl) ⟨2488442, by rfl⟩ : syracuseStep 3317923 = 4976885) B4976885
theorem B2760913 : Blo 1723062 2760913 := bstep (se 2 (by rfl) ⟨1035342, by rfl⟩ : syracuseStep 2760913 = 2070685) B2070685
theorem B2908433 : Blo 1723062 2908433 := bstep (se 2 (by rfl) ⟨1090662, by rfl⟩ : syracuseStep 2908433 = 2181325) B2181325
theorem B2949409 : Blo 1723062 2949409 := bstep (se 2 (by rfl) ⟨1106028, by rfl⟩ : syracuseStep 2949409 = 2212057) B2212057
theorem B5898545 : Blo 1723062 5898545 := bstep (se 2 (by rfl) ⟨2211954, by rfl⟩ : syracuseStep 5898545 = 4423909) B4423909
theorem B5816717 : Blo 1723062 5816717 := bstep (se 3 (by rfl) ⟨1090634, by rfl⟩ : syracuseStep 5816717 = 2181269) B2181269
theorem B2908561 : Blo 1723062 2908561 := bstep (se 2 (by rfl) ⟨1090710, by rfl⟩ : syracuseStep 2908561 = 2181421) B2181421
theorem B2908595 : Blo 1723062 2908595 := bstep (se 1 (by rfl) ⟨2181446, by rfl⟩ : syracuseStep 2908595 = 4362893) B4362893
theorem B5816771 : Blo 1723062 5816771 := bstep (se 1 (by rfl) ⟨4362578, by rfl⟩ : syracuseStep 5816771 = 8725157) B8725157
theorem B5521891 : Blo 1723062 5521891 := bstep (se 1 (by rfl) ⟨4141418, by rfl⟩ : syracuseStep 5521891 = 8282837) B8282837
theorem B3932675 : Blo 1723062 3932675 := bstep (se 1 (by rfl) ⟨2949506, by rfl⟩ : syracuseStep 3932675 = 5899013) B5899013
theorem B4907537 : Blo 1723062 4907537 := bstep (se 2 (by rfl) ⟨1840326, by rfl⟩ : syracuseStep 4907537 = 3680653) B3680653
theorem B2908723 : Blo 1723062 2908723 := bstep (se 1 (by rfl) ⟨2181542, by rfl⟩ : syracuseStep 2908723 = 4363085) B4363085
theorem B51069553 : Blo 1723062 51069553 := bstep (se 2 (by rfl) ⟨19151082, by rfl⟩ : syracuseStep 51069553 = 38302165) B38302165
theorem B11682467 : Blo 1723062 11682467 := bstep (se 1 (by rfl) ⟨8761850, by rfl⟩ : syracuseStep 11682467 = 17523701) B17523701
theorem B2908865 : Blo 1723062 2908865 := bstep (se 2 (by rfl) ⟨1090824, by rfl⟩ : syracuseStep 2908865 = 2181649) B2181649
theorem B5817041 : Blo 1723062 5817041 := bstep (se 2 (by rfl) ⟨2181390, by rfl⟩ : syracuseStep 5817041 = 4362781) B4362781
theorem B2908993 : Blo 1723062 2908993 := bstep (se 2 (by rfl) ⟨1090872, by rfl⟩ : syracuseStep 2908993 = 2181745) B2181745
theorem B2909027 : Blo 1723062 2909027 := bstep (se 1 (by rfl) ⟨2181770, by rfl⟩ : syracuseStep 2909027 = 4363541) B4363541
theorem B9823139 : Blo 1723062 9823139 := bstep (se 1 (by rfl) ⟨7367354, by rfl⟩ : syracuseStep 9823139 = 14734709) B14734709
theorem B2909155 : Blo 1723062 2909155 := bstep (se 1 (by rfl) ⟨2181866, by rfl⟩ : syracuseStep 2909155 = 4363733) B4363733
theorem B2909297 : Blo 1723062 2909297 := bstep (se 2 (by rfl) ⟨1090986, by rfl⟩ : syracuseStep 2909297 = 2181973) B2181973
theorem B6210701 : Blo 1723062 6210701 := bstep (se 3 (by rfl) ⟨1164506, by rfl⟩ : syracuseStep 6210701 = 2329013) B2329013
theorem B3105955 : Blo 1723062 3105955 := bstep (se 1 (by rfl) ⟨2329466, by rfl⟩ : syracuseStep 3105955 = 4658933) B4658933
theorem B9323747 : Blo 1723062 9323747 := bstep (se 1 (by rfl) ⟨6992810, by rfl⟩ : syracuseStep 9323747 = 13985621) B13985621
theorem B5817581 : Blo 1723062 5817581 := bstep (se 3 (by rfl) ⟨1090796, by rfl⟩ : syracuseStep 5817581 = 2181593) B2181593
theorem B2909425 : Blo 1723062 2909425 := bstep (se 2 (by rfl) ⟨1091034, by rfl⟩ : syracuseStep 2909425 = 2182069) B2182069
theorem B2622737 : Blo 1723062 2622737 := bstep (se 2 (by rfl) ⟨983526, by rfl⟩ : syracuseStep 2622737 = 1967053) B1967053
theorem B2909459 : Blo 1723062 2909459 := bstep (se 1 (by rfl) ⟨2182094, by rfl⟩ : syracuseStep 2909459 = 4364189) B4364189
theorem B5817635 : Blo 1723062 5817635 := bstep (se 1 (by rfl) ⟨4363226, by rfl⟩ : syracuseStep 5817635 = 8726453) B8726453
theorem B7365937 : Blo 1723062 7365937 := bstep (se 2 (by rfl) ⟨2762226, by rfl⟩ : syracuseStep 7365937 = 5524453) B5524453
theorem B7464305 : Blo 1723062 7464305 := bstep (se 2 (by rfl) ⟨2799114, by rfl⟩ : syracuseStep 7464305 = 5598229) B5598229
theorem B2360723 : Blo 1723062 2360723 := bstep (se 1 (by rfl) ⟨1770542, by rfl⟩ : syracuseStep 2360723 = 3541085) B3541085
theorem B2909587 : Blo 1723062 2909587 := bstep (se 1 (by rfl) ⟨2182190, by rfl⟩ : syracuseStep 2909587 = 4364381) B4364381
theorem B18646453 : Blo 1723062 18646453 := bstep (se 5 (by rfl) ⟨874052, by rfl⟩ : syracuseStep 18646453 = 1748105) B1748105
theorem B11789837 : Blo 1723062 11789837 := bstep (se 3 (by rfl) ⟨2210594, by rfl⟩ : syracuseStep 11789837 = 4421189) B4421189
theorem B13264397 : Blo 1723062 13264397 := bstep (se 3 (by rfl) ⟨2487074, by rfl⟩ : syracuseStep 13264397 = 4974149) B4974149
theorem B2909729 : Blo 1723062 2909729 := bstep (se 2 (by rfl) ⟨1091148, by rfl⟩ : syracuseStep 2909729 = 2182297) B2182297
theorem B5817905 : Blo 1723062 5817905 := bstep (se 2 (by rfl) ⟨2181714, by rfl⟩ : syracuseStep 5817905 = 4363429) B4363429
theorem B8726129 : Blo 1723062 8726129 := bstep (se 2 (by rfl) ⟨3272298, by rfl⟩ : syracuseStep 8726129 = 6544597) B6544597
theorem B2909857 : Blo 1723062 2909857 := bstep (se 2 (by rfl) ⟨1091196, by rfl⟩ : syracuseStep 2909857 = 2182393) B2182393
theorem B2909891 : Blo 1723062 2909891 := bstep (se 1 (by rfl) ⟨2182418, by rfl⟩ : syracuseStep 2909891 = 4364837) B4364837
theorem B3106531 : Blo 1723062 3106531 := bstep (se 1 (by rfl) ⟨2329898, by rfl⟩ : syracuseStep 3106531 = 4659797) B4659797
theorem B2762515 : Blo 1723062 2762515 := bstep (se 1 (by rfl) ⟨2071886, by rfl⟩ : syracuseStep 2762515 = 4143773) B4143773
theorem B2910019 : Blo 1723062 2910019 := bstep (se 1 (by rfl) ⟨2182514, by rfl⟩ : syracuseStep 2910019 = 4365029) B4365029
theorem B12429125 : Blo 1723062 12429125 := bstep (se 4 (by rfl) ⟨1165230, by rfl⟩ : syracuseStep 12429125 = 2330461) B2330461
theorem B5244803 : Blo 1723062 5244803 := bstep (se 1 (by rfl) ⟨3933602, by rfl⟩ : syracuseStep 5244803 = 7867205) B7867205
theorem B4908995 : Blo 1723062 4908995 := bstep (se 1 (by rfl) ⟨3681746, by rfl⟩ : syracuseStep 4908995 = 7363493) B7363493
theorem B2910161 : Blo 1723062 2910161 := bstep (se 2 (by rfl) ⟨1091310, by rfl⟩ : syracuseStep 2910161 = 2182621) B2182621
theorem B2181107 : Blo 1723062 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B5523491 : Blo 1723062 5523491 := bstep (se 1 (by rfl) ⟨4142618, by rfl⟩ : syracuseStep 5523491 = 8285237) B8285237
theorem B5818445 : Blo 1723062 5818445 := bstep (se 3 (by rfl) ⟨1090958, by rfl⟩ : syracuseStep 5818445 = 2181917) B2181917
theorem B2910289 : Blo 1723062 2910289 := bstep (se 2 (by rfl) ⟨1091358, by rfl⟩ : syracuseStep 2910289 = 2182717) B2182717
theorem B2910323 : Blo 1723062 2910323 := bstep (se 1 (by rfl) ⟨2182742, by rfl⟩ : syracuseStep 2910323 = 4365485) B4365485
theorem B5818499 : Blo 1723062 5818499 := bstep (se 1 (by rfl) ⟨4363874, by rfl⟩ : syracuseStep 5818499 = 8727749) B8727749
theorem B10479779 : Blo 1723062 10479779 := bstep (se 1 (by rfl) ⟨7859834, by rfl⟩ : syracuseStep 10479779 = 15719669) B15719669
theorem B3877073 : Blo 1723062 3877073 := bstep (se 2 (by rfl) ⟨1453902, by rfl⟩ : syracuseStep 3877073 = 2907805) B2907805
theorem B3877091 : Blo 1723062 3877091 := bstep (se 1 (by rfl) ⟨2907818, by rfl⟩ : syracuseStep 3877091 = 5815637) B5815637
theorem B16574705 : Blo 1723062 16574705 := bstep (se 2 (by rfl) ⟨6215514, by rfl⟩ : syracuseStep 16574705 = 12431029) B12431029
theorem B2910451 : Blo 1723062 2910451 := bstep (se 1 (by rfl) ⟨2182838, by rfl⟩ : syracuseStep 2910451 = 4365677) B4365677
theorem B2656579 : Blo 1723062 2656579 := bstep (se 1 (by rfl) ⟨1992434, by rfl⟩ : syracuseStep 2656579 = 3984869) B3984869
theorem B2910593 : Blo 1723062 2910593 := bstep (se 2 (by rfl) ⟨1091472, by rfl⟩ : syracuseStep 2910593 = 2182945) B2182945
theorem B9316741 : Blo 1723062 9316741 := bstep (se 4 (by rfl) ⟨873444, by rfl⟩ : syracuseStep 9316741 = 1746889) B1746889
theorem B5818769 : Blo 1723062 5818769 := bstep (se 2 (by rfl) ⟨2182038, by rfl⟩ : syracuseStep 5818769 = 4364077) B4364077
theorem B3877361 : Blo 1723062 3877361 := bstep (se 2 (by rfl) ⟨1454010, by rfl⟩ : syracuseStep 3877361 = 2908021) B2908021
theorem B2910721 : Blo 1723062 2910721 := bstep (se 2 (by rfl) ⟨1091520, by rfl⟩ : syracuseStep 2910721 = 2183041) B2183041
theorem B3877379 : Blo 1723062 3877379 := bstep (se 1 (by rfl) ⟨2908034, by rfl⟩ : syracuseStep 3877379 = 5816069) B5816069
theorem B2910755 : Blo 1723062 2910755 := bstep (se 1 (by rfl) ⟨2183066, by rfl⟩ : syracuseStep 2910755 = 4366133) B4366133
theorem B26528309 : Blo 1723062 26528309 := bstep (se 5 (by rfl) ⟨1243514, by rfl⟩ : syracuseStep 26528309 = 2487029) B2487029
theorem B4786829 : Blo 1723062 4786829 := bstep (se 3 (by rfl) ⟨897530, by rfl⟩ : syracuseStep 4786829 = 1795061) B1795061
theorem B8284835 : Blo 1723062 8284835 := bstep (se 1 (by rfl) ⟨6213626, by rfl⟩ : syracuseStep 8284835 = 12427253) B12427253
theorem B7867043 : Blo 1723062 7867043 := bstep (se 1 (by rfl) ⟨5900282, by rfl⟩ : syracuseStep 7867043 = 11800565) B11800565
theorem B2910883 : Blo 1723062 2910883 := bstep (se 1 (by rfl) ⟨2183162, by rfl⟩ : syracuseStep 2910883 = 4366325) B4366325
theorem B2181811 : Blo 1723062 2181811 := bstep (se 1 (by rfl) ⟨1636358, by rfl⟩ : syracuseStep 2181811 = 3272717) B3272717
theorem B1723075 : Blo 1723062 1723075 := bstep (se 1 (by rfl) ⟨1292306, by rfl⟩ : syracuseStep 1723075 = 2584613) B2584613
theorem B6908621 : Blo 1723062 6908621 := bstep (se 3 (by rfl) ⟨1295366, by rfl⟩ : syracuseStep 6908621 = 2590733) B2590733
theorem B1723091 : Blo 1723062 1723091 := bstep (se 1 (by rfl) ⟨1292318, by rfl⟩ : syracuseStep 1723091 = 2584637) B2584637
theorem B1723107 : Blo 1723062 1723107 := bstep (se 1 (by rfl) ⟨1292330, by rfl⟩ : syracuseStep 1723107 = 2584661) B2584661
theorem B55896803 : Blo 1723062 55896803 := bstep (se 1 (by rfl) ⟨41922602, by rfl⟩ : syracuseStep 55896803 = 83845205) B83845205
theorem B4909805 : Blo 1723062 4909805 := bstep (se 3 (by rfl) ⟨920588, by rfl⟩ : syracuseStep 4909805 = 1841177) B1841177
theorem B1723123 : Blo 1723062 1723123 := bstep (se 1 (by rfl) ⟨1292342, by rfl⟩ : syracuseStep 1723123 = 2584685) B2584685
theorem B1723139 : Blo 1723062 1723139 := bstep (se 1 (by rfl) ⟨1292354, by rfl⟩ : syracuseStep 1723139 = 2584709) B2584709
theorem B5901059 : Blo 1723062 5901059 := bstep (se 1 (by rfl) ⟨4425794, by rfl⟩ : syracuseStep 5901059 = 8851589) B8851589
theorem B3271441 : Blo 1723062 3271441 := bstep (se 2 (by rfl) ⟨1226790, by rfl⟩ : syracuseStep 3271441 = 2453581) B2453581
theorem B3877649 : Blo 1723062 3877649 := bstep (se 2 (by rfl) ⟨1454118, by rfl⟩ : syracuseStep 3877649 = 2908237) B2908237
theorem B1723155 : Blo 1723062 1723155 := bstep (se 1 (by rfl) ⟨1292366, by rfl⟩ : syracuseStep 1723155 = 2584733) B2584733
theorem B2181907 : Blo 1723062 2181907 := bstep (se 1 (by rfl) ⟨1636430, by rfl⟩ : syracuseStep 2181907 = 3272861) B3272861
theorem B1723171 : Blo 1723062 1723171 := bstep (se 1 (by rfl) ⟨1292378, by rfl⟩ : syracuseStep 1723171 = 2584757) B2584757
theorem B3877667 : Blo 1723062 3877667 := bstep (se 1 (by rfl) ⟨2908250, by rfl⟩ : syracuseStep 3877667 = 5816501) B5816501
theorem B6548273 : Blo 1723062 6548273 := bstep (se 2 (by rfl) ⟨2455602, by rfl⟩ : syracuseStep 6548273 = 4911205) B4911205
theorem B2911025 : Blo 1723062 2911025 := bstep (se 2 (by rfl) ⟨1091634, by rfl⟩ : syracuseStep 2911025 = 2183269) B2183269
theorem B1723187 : Blo 1723062 1723187 := bstep (se 1 (by rfl) ⟨1292390, by rfl⟩ : syracuseStep 1723187 = 2584781) B2584781
theorem B1723203 : Blo 1723062 1723203 := bstep (se 1 (by rfl) ⟨1292402, by rfl⟩ : syracuseStep 1723203 = 2584805) B2584805
theorem B1723219 : Blo 1723062 1723219 := bstep (se 1 (by rfl) ⟨1292414, by rfl⟩ : syracuseStep 1723219 = 2584829) B2584829
theorem B1723235 : Blo 1723062 1723235 := bstep (se 1 (by rfl) ⟨1292426, by rfl⟩ : syracuseStep 1723235 = 2584853) B2584853
theorem B1723251 : Blo 1723062 1723251 := bstep (se 1 (by rfl) ⟨1292438, by rfl⟩ : syracuseStep 1723251 = 2584877) B2584877
theorem B1723267 : Blo 1723062 1723267 := bstep (se 1 (by rfl) ⟨1292450, by rfl⟩ : syracuseStep 1723267 = 2584901) B2584901
theorem B6990733 : Blo 1723062 6990733 := bstep (se 3 (by rfl) ⟨1310762, by rfl⟩ : syracuseStep 6990733 = 2621525) B2621525
theorem B2329489 : Blo 1723062 2329489 := bstep (se 2 (by rfl) ⟨873558, by rfl⟩ : syracuseStep 2329489 = 1747117) B1747117
theorem B1723283 : Blo 1723062 1723283 := bstep (se 1 (by rfl) ⟨1292462, by rfl⟩ : syracuseStep 1723283 = 2584925) B2584925
theorem B1723299 : Blo 1723062 1723299 := bstep (se 1 (by rfl) ⟨1292474, by rfl⟩ : syracuseStep 1723299 = 2584949) B2584949
theorem B4909997 : Blo 1723062 4909997 := bstep (se 3 (by rfl) ⟨920624, by rfl⟩ : syracuseStep 4909997 = 1841249) B1841249
theorem B5819309 : Blo 1723062 5819309 := bstep (se 3 (by rfl) ⟨1091120, by rfl⟩ : syracuseStep 5819309 = 2182241) B2182241
theorem B1723315 : Blo 1723062 1723315 := bstep (se 1 (by rfl) ⟨1292486, by rfl⟩ : syracuseStep 1723315 = 2584973) B2584973
theorem B1723331 : Blo 1723062 1723331 := bstep (se 1 (by rfl) ⟨1292498, by rfl⟩ : syracuseStep 1723331 = 2584997) B2584997
theorem B1723347 : Blo 1723062 1723347 := bstep (se 1 (by rfl) ⟨1292510, by rfl⟩ : syracuseStep 1723347 = 2585021) B2585021
theorem B1723363 : Blo 1723062 1723363 := bstep (se 1 (by rfl) ⟨1292522, by rfl⟩ : syracuseStep 1723363 = 2585045) B2585045
theorem B5819363 : Blo 1723062 5819363 := bstep (se 1 (by rfl) ⟨4364522, by rfl⟩ : syracuseStep 5819363 = 8729045) B8729045
theorem B5524465 : Blo 1723062 5524465 := bstep (se 2 (by rfl) ⟨2071674, by rfl⟩ : syracuseStep 5524465 = 4143349) B4143349
theorem B1723379 : Blo 1723062 1723379 := bstep (se 1 (by rfl) ⟨1292534, by rfl⟩ : syracuseStep 1723379 = 2585069) B2585069
theorem B1723395 : Blo 1723062 1723395 := bstep (se 1 (by rfl) ⟨1292546, by rfl⟩ : syracuseStep 1723395 = 2585093) B2585093
theorem B1723411 : Blo 1723062 1723411 := bstep (se 1 (by rfl) ⟨1292558, by rfl⟩ : syracuseStep 1723411 = 2585117) B2585117
theorem B1723427 : Blo 1723062 1723427 := bstep (se 1 (by rfl) ⟨1292570, by rfl⟩ : syracuseStep 1723427 = 2585141) B2585141
theorem B8727587 : Blo 1723062 8727587 := bstep (se 1 (by rfl) ⟨6545690, by rfl⟩ : syracuseStep 8727587 = 13091381) B13091381
theorem B3877937 : Blo 1723062 3877937 := bstep (se 2 (by rfl) ⟨1454226, by rfl⟩ : syracuseStep 3877937 = 2908453) B2908453
theorem B1723443 : Blo 1723062 1723443 := bstep (se 1 (by rfl) ⟨1292582, by rfl⟩ : syracuseStep 1723443 = 2585165) B2585165
theorem B2329651 : Blo 1723062 2329651 := bstep (se 1 (by rfl) ⟨1747238, by rfl⟩ : syracuseStep 2329651 = 3494477) B3494477
theorem B1723459 : Blo 1723062 1723459 := bstep (se 1 (by rfl) ⟨1292594, by rfl⟩ : syracuseStep 1723459 = 2585189) B2585189
theorem B3877955 : Blo 1723062 3877955 := bstep (se 1 (by rfl) ⟨2908466, by rfl⟩ : syracuseStep 3877955 = 5816933) B5816933
theorem B1723475 : Blo 1723062 1723475 := bstep (se 1 (by rfl) ⟨1292606, by rfl⟩ : syracuseStep 1723475 = 2585213) B2585213
theorem B1723491 : Blo 1723062 1723491 := bstep (se 1 (by rfl) ⟨1292618, by rfl⟩ : syracuseStep 1723491 = 2585237) B2585237
theorem B1723507 : Blo 1723062 1723507 := bstep (se 1 (by rfl) ⟨1292630, by rfl⟩ : syracuseStep 1723507 = 2585261) B2585261
theorem B1723523 : Blo 1723062 1723523 := bstep (se 1 (by rfl) ⟨1292642, by rfl⟩ : syracuseStep 1723523 = 2585285) B2585285
theorem B1723539 : Blo 1723062 1723539 := bstep (se 1 (by rfl) ⟨1292654, by rfl⟩ : syracuseStep 1723539 = 2585309) B2585309
theorem B3271843 : Blo 1723062 3271843 := bstep (se 1 (by rfl) ⟨2453882, by rfl⟩ : syracuseStep 3271843 = 4907765) B4907765
theorem B1723555 : Blo 1723062 1723555 := bstep (se 1 (by rfl) ⟨1292666, by rfl⟩ : syracuseStep 1723555 = 2585333) B2585333
theorem B1723571 : Blo 1723062 1723571 := bstep (se 1 (by rfl) ⟨1292678, by rfl⟩ : syracuseStep 1723571 = 2585357) B2585357
theorem B1723587 : Blo 1723062 1723587 := bstep (se 1 (by rfl) ⟨1292690, by rfl⟩ : syracuseStep 1723587 = 2585381) B2585381
theorem B3271889 : Blo 1723062 3271889 := bstep (se 2 (by rfl) ⟨1226958, by rfl⟩ : syracuseStep 3271889 = 2453917) B2453917
theorem B1723603 : Blo 1723062 1723603 := bstep (se 1 (by rfl) ⟨1292702, by rfl⟩ : syracuseStep 1723603 = 2585405) B2585405
theorem B1723619 : Blo 1723062 1723619 := bstep (se 1 (by rfl) ⟨1292714, by rfl⟩ : syracuseStep 1723619 = 2585429) B2585429
theorem B53800163 : Blo 1723062 53800163 := bstep (se 1 (by rfl) ⟨40350122, by rfl⟩ : syracuseStep 53800163 = 80700245) B80700245
theorem B5819633 : Blo 1723062 5819633 := bstep (se 2 (by rfl) ⟨2182362, by rfl⟩ : syracuseStep 5819633 = 4364725) B4364725
theorem B1723635 : Blo 1723062 1723635 := bstep (se 1 (by rfl) ⟨1292726, by rfl⟩ : syracuseStep 1723635 = 2585453) B2585453
theorem B1723651 : Blo 1723062 1723651 := bstep (se 1 (by rfl) ⟨1292738, by rfl⟩ : syracuseStep 1723651 = 2585477) B2585477
theorem B2182403 : Blo 1723062 2182403 := bstep (se 1 (by rfl) ⟨1636802, by rfl⟩ : syracuseStep 2182403 = 3273605) B3273605
theorem B1723667 : Blo 1723062 1723667 := bstep (se 1 (by rfl) ⟨1292750, by rfl⟩ : syracuseStep 1723667 = 2585501) B2585501
theorem B1723683 : Blo 1723062 1723683 := bstep (se 1 (by rfl) ⟨1292762, by rfl⟩ : syracuseStep 1723683 = 2585525) B2585525
theorem B1723699 : Blo 1723062 1723699 := bstep (se 1 (by rfl) ⟨1292774, by rfl⟩ : syracuseStep 1723699 = 2585549) B2585549
theorem B1723715 : Blo 1723062 1723715 := bstep (se 1 (by rfl) ⟨1292786, by rfl⟩ : syracuseStep 1723715 = 2585573) B2585573
theorem B3878225 : Blo 1723062 3878225 := bstep (se 2 (by rfl) ⟨1454334, by rfl⟩ : syracuseStep 3878225 = 2908669) B2908669
theorem B1723731 : Blo 1723062 1723731 := bstep (se 1 (by rfl) ⟨1292798, by rfl⟩ : syracuseStep 1723731 = 2585597) B2585597
theorem B3878243 : Blo 1723062 3878243 := bstep (se 1 (by rfl) ⟨2908682, by rfl⟩ : syracuseStep 3878243 = 5817365) B5817365
theorem B1723747 : Blo 1723062 1723747 := bstep (se 1 (by rfl) ⟨1292810, by rfl⟩ : syracuseStep 1723747 = 2585621) B2585621
theorem B1723763 : Blo 1723062 1723763 := bstep (se 1 (by rfl) ⟨1292822, by rfl⟩ : syracuseStep 1723763 = 2585645) B2585645
theorem B1723779 : Blo 1723062 1723779 := bstep (se 1 (by rfl) ⟨1292834, by rfl⟩ : syracuseStep 1723779 = 2585669) B2585669
theorem B1723795 : Blo 1723062 1723795 := bstep (se 1 (by rfl) ⟨1292846, by rfl⟩ : syracuseStep 1723795 = 2585693) B2585693
theorem B1723811 : Blo 1723062 1723811 := bstep (se 1 (by rfl) ⟨1292858, by rfl⟩ : syracuseStep 1723811 = 2585717) B2585717
theorem B3681713 : Blo 1723062 3681713 := bstep (se 2 (by rfl) ⟨1380642, by rfl⟩ : syracuseStep 3681713 = 2761285) B2761285
theorem B1723827 : Blo 1723062 1723827 := bstep (se 1 (by rfl) ⟨1292870, by rfl⟩ : syracuseStep 1723827 = 2585741) B2585741
theorem B1723843 : Blo 1723062 1723843 := bstep (se 1 (by rfl) ⟨1292882, by rfl⟩ : syracuseStep 1723843 = 2585765) B2585765
theorem B27954629 : Blo 1723062 27954629 := bstep (se 4 (by rfl) ⟨2620746, by rfl⟩ : syracuseStep 27954629 = 5241493) B5241493
theorem B1723859 : Blo 1723062 1723859 := bstep (se 1 (by rfl) ⟨1292894, by rfl⟩ : syracuseStep 1723859 = 2585789) B2585789
theorem B1723875 : Blo 1723062 1723875 := bstep (se 1 (by rfl) ⟨1292906, by rfl⟩ : syracuseStep 1723875 = 2585813) B2585813
theorem B3272177 : Blo 1723062 3272177 := bstep (se 2 (by rfl) ⟨1227066, by rfl⟩ : syracuseStep 3272177 = 2454133) B2454133
theorem B1723891 : Blo 1723062 1723891 := bstep (se 1 (by rfl) ⟨1292918, by rfl⟩ : syracuseStep 1723891 = 2585837) B2585837
theorem B1723907 : Blo 1723062 1723907 := bstep (se 1 (by rfl) ⟨1292930, by rfl⟩ : syracuseStep 1723907 = 2585861) B2585861
theorem B1723923 : Blo 1723062 1723923 := bstep (se 1 (by rfl) ⟨1292942, by rfl⟩ : syracuseStep 1723923 = 2585885) B2585885
theorem B1723939 : Blo 1723062 1723939 := bstep (se 1 (by rfl) ⟨1292954, by rfl⟩ : syracuseStep 1723939 = 2585909) B2585909
theorem B1723955 : Blo 1723062 1723955 := bstep (se 1 (by rfl) ⟨1292966, by rfl⟩ : syracuseStep 1723955 = 2585933) B2585933
theorem B1723971 : Blo 1723062 1723971 := bstep (se 1 (by rfl) ⟨1292978, by rfl⟩ : syracuseStep 1723971 = 2585957) B2585957
theorem B11046469 : Blo 1723062 11046469 := bstep (se 4 (by rfl) ⟨1035606, by rfl⟩ : syracuseStep 11046469 = 2071213) B2071213
theorem B4361809 : Blo 1723062 4361809 := bstep (se 2 (by rfl) ⟨1635678, by rfl⟩ : syracuseStep 4361809 = 3271357) B3271357
theorem B1723987 : Blo 1723062 1723987 := bstep (se 1 (by rfl) ⟨1292990, by rfl⟩ : syracuseStep 1723987 = 2585981) B2585981
theorem B1724003 : Blo 1723062 1724003 := bstep (se 1 (by rfl) ⟨1293002, by rfl⟩ : syracuseStep 1724003 = 2586005) B2586005
theorem B3878513 : Blo 1723062 3878513 := bstep (se 2 (by rfl) ⟨1454442, by rfl⟩ : syracuseStep 3878513 = 2908885) B2908885
theorem B1724019 : Blo 1723062 1724019 := bstep (se 1 (by rfl) ⟨1293014, by rfl⟩ : syracuseStep 1724019 = 2586029) B2586029
theorem B3878531 : Blo 1723062 3878531 := bstep (se 1 (by rfl) ⟨2908898, by rfl⟩ : syracuseStep 3878531 = 5817797) B5817797
theorem B1724035 : Blo 1723062 1724035 := bstep (se 1 (by rfl) ⟨1293026, by rfl⟩ : syracuseStep 1724035 = 2586053) B2586053
theorem B24850061 : Blo 1723062 24850061 := bstep (se 3 (by rfl) ⟨4659386, by rfl⟩ : syracuseStep 24850061 = 9318773) B9318773
theorem B1724051 : Blo 1723062 1724051 := bstep (se 1 (by rfl) ⟨1293038, by rfl⟩ : syracuseStep 1724051 = 2586077) B2586077
theorem B1724067 : Blo 1723062 1724067 := bstep (se 1 (by rfl) ⟨1293050, by rfl⟩ : syracuseStep 1724067 = 2586101) B2586101
theorem B1724083 : Blo 1723062 1724083 := bstep (se 1 (by rfl) ⟨1293062, by rfl⟩ : syracuseStep 1724083 = 2586125) B2586125
theorem B1724099 : Blo 1723062 1724099 := bstep (se 1 (by rfl) ⟨1293074, by rfl⟩ : syracuseStep 1724099 = 2586149) B2586149
theorem B1724115 : Blo 1723062 1724115 := bstep (se 1 (by rfl) ⟨1293086, by rfl⟩ : syracuseStep 1724115 = 2586173) B2586173
theorem B1724131 : Blo 1723062 1724131 := bstep (se 1 (by rfl) ⟨1293098, by rfl⟩ : syracuseStep 1724131 = 2586197) B2586197
theorem B1724147 : Blo 1723062 1724147 := bstep (se 1 (by rfl) ⟨1293110, by rfl⟩ : syracuseStep 1724147 = 2586221) B2586221
theorem B1724163 : Blo 1723062 1724163 := bstep (se 1 (by rfl) ⟨1293122, by rfl⟩ : syracuseStep 1724163 = 2586245) B2586245
theorem B5820173 : Blo 1723062 5820173 := bstep (se 3 (by rfl) ⟨1091282, by rfl⟩ : syracuseStep 5820173 = 2182565) B2182565
theorem B1724179 : Blo 1723062 1724179 := bstep (se 1 (by rfl) ⟨1293134, by rfl⟩ : syracuseStep 1724179 = 2586269) B2586269
theorem B1724195 : Blo 1723062 1724195 := bstep (se 1 (by rfl) ⟨1293146, by rfl⟩ : syracuseStep 1724195 = 2586293) B2586293
theorem B1724211 : Blo 1723062 1724211 := bstep (se 1 (by rfl) ⟨1293158, by rfl⟩ : syracuseStep 1724211 = 2586317) B2586317
theorem B1724227 : Blo 1723062 1724227 := bstep (se 1 (by rfl) ⟨1293170, by rfl⟩ : syracuseStep 1724227 = 2586341) B2586341
theorem B5820227 : Blo 1723062 5820227 := bstep (se 1 (by rfl) ⟨4365170, by rfl⟩ : syracuseStep 5820227 = 8730341) B8730341
theorem B8728397 : Blo 1723062 8728397 := bstep (se 3 (by rfl) ⟨1636574, by rfl⟩ : syracuseStep 8728397 = 3273149) B3273149
theorem B1724243 : Blo 1723062 1724243 := bstep (se 1 (by rfl) ⟨1293182, by rfl⟩ : syracuseStep 1724243 = 2586365) B2586365
theorem B4362083 : Blo 1723062 4362083 := bstep (se 1 (by rfl) ⟨3271562, by rfl⟩ : syracuseStep 4362083 = 6543125) B6543125
theorem B1724259 : Blo 1723062 1724259 := bstep (se 1 (by rfl) ⟨1293194, by rfl⟩ : syracuseStep 1724259 = 2586389) B2586389
theorem B1724275 : Blo 1723062 1724275 := bstep (se 1 (by rfl) ⟨1293206, by rfl⟩ : syracuseStep 1724275 = 2586413) B2586413
theorem B1724291 : Blo 1723062 1724291 := bstep (se 1 (by rfl) ⟨1293218, by rfl⟩ : syracuseStep 1724291 = 2586437) B2586437
theorem B4910989 : Blo 1723062 4910989 := bstep (se 3 (by rfl) ⟨920810, by rfl⟩ : syracuseStep 4910989 = 1841621) B1841621
theorem B3878801 : Blo 1723062 3878801 := bstep (se 2 (by rfl) ⟨1454550, by rfl⟩ : syracuseStep 3878801 = 2909101) B2909101
theorem B1724307 : Blo 1723062 1724307 := bstep (se 1 (by rfl) ⟨1293230, by rfl⟩ : syracuseStep 1724307 = 2586461) B2586461
theorem B3878819 : Blo 1723062 3878819 := bstep (se 1 (by rfl) ⟨2909114, by rfl⟩ : syracuseStep 3878819 = 5818229) B5818229
theorem B1724323 : Blo 1723062 1724323 := bstep (se 1 (by rfl) ⟨1293242, by rfl⟩ : syracuseStep 1724323 = 2586485) B2586485
theorem B1724339 : Blo 1723062 1724339 := bstep (se 1 (by rfl) ⟨1293254, by rfl⟩ : syracuseStep 1724339 = 2586509) B2586509
theorem B1724355 : Blo 1723062 1724355 := bstep (se 1 (by rfl) ⟨1293266, by rfl⟩ : syracuseStep 1724355 = 2586533) B2586533
theorem B2183107 : Blo 1723062 2183107 := bstep (se 1 (by rfl) ⟨1637330, by rfl⟩ : syracuseStep 2183107 = 3274661) B3274661
theorem B1724371 : Blo 1723062 1724371 := bstep (se 1 (by rfl) ⟨1293278, by rfl⟩ : syracuseStep 1724371 = 2586557) B2586557
theorem B1724387 : Blo 1723062 1724387 := bstep (se 1 (by rfl) ⟨1293290, by rfl⟩ : syracuseStep 1724387 = 2586581) B2586581
theorem B8851427 : Blo 1723062 8851427 := bstep (se 1 (by rfl) ⟨6638570, by rfl⟩ : syracuseStep 8851427 = 13277141) B13277141
theorem B1724403 : Blo 1723062 1724403 := bstep (se 1 (by rfl) ⟨1293302, by rfl⟩ : syracuseStep 1724403 = 2586605) B2586605
theorem B1724419 : Blo 1723062 1724419 := bstep (se 1 (by rfl) ⟨1293314, by rfl⟩ : syracuseStep 1724419 = 2586629) B2586629
theorem B2584595 : Blo 1723062 2584595 := bstep (se 1 (by rfl) ⟨1938446, by rfl⟩ : syracuseStep 2584595 = 3876893) B3876893
theorem B1724435 : Blo 1723062 1724435 := bstep (se 1 (by rfl) ⟨1293326, by rfl⟩ : syracuseStep 1724435 = 2586653) B2586653
theorem B4362275 : Blo 1723062 4362275 := bstep (se 1 (by rfl) ⟨3271706, by rfl⟩ : syracuseStep 4362275 = 6543413) B6543413
theorem B1724451 : Blo 1723062 1724451 := bstep (se 1 (by rfl) ⟨1293338, by rfl⟩ : syracuseStep 1724451 = 2586677) B2586677
theorem B2183203 : Blo 1723062 2183203 := bstep (se 1 (by rfl) ⟨1637402, by rfl⟩ : syracuseStep 2183203 = 3274805) B3274805
theorem B2584625 : Blo 1723062 2584625 := bstep (se 2 (by rfl) ⟨969234, by rfl⟩ : syracuseStep 2584625 = 1938469) B1938469
theorem B1724467 : Blo 1723062 1724467 := bstep (se 1 (by rfl) ⟨1293350, by rfl⟩ : syracuseStep 1724467 = 2586701) B2586701
theorem B37269557 : Blo 1723062 37269557 := bstep (se 5 (by rfl) ⟨1747010, by rfl⟩ : syracuseStep 37269557 = 3494021) B3494021
theorem B2330689 : Blo 1723062 2330689 := bstep (se 2 (by rfl) ⟨874008, by rfl⟩ : syracuseStep 2330689 = 1748017) B1748017
theorem B2584643 : Blo 1723062 2584643 := bstep (se 1 (by rfl) ⟨1938482, by rfl⟩ : syracuseStep 2584643 = 3876965) B3876965
theorem B1724483 : Blo 1723062 1724483 := bstep (se 1 (by rfl) ⟨1293362, by rfl⟩ : syracuseStep 1724483 = 2586725) B2586725
theorem B5820497 : Blo 1723062 5820497 := bstep (se 2 (by rfl) ⟨2182686, by rfl⟩ : syracuseStep 5820497 = 4365373) B4365373
theorem B1724499 : Blo 1723062 1724499 := bstep (se 1 (by rfl) ⟨1293374, by rfl⟩ : syracuseStep 1724499 = 2586749) B2586749
theorem B2584673 : Blo 1723062 2584673 := bstep (se 2 (by rfl) ⟨969252, by rfl⟩ : syracuseStep 2584673 = 1938505) B1938505
theorem B1724515 : Blo 1723062 1724515 := bstep (se 1 (by rfl) ⟨1293386, by rfl⟩ : syracuseStep 1724515 = 2586773) B2586773
theorem B2584691 : Blo 1723062 2584691 := bstep (se 1 (by rfl) ⟨1938518, by rfl⟩ : syracuseStep 2584691 = 3877037) B3877037
theorem B1724531 : Blo 1723062 1724531 := bstep (se 1 (by rfl) ⟨1293398, by rfl⟩ : syracuseStep 1724531 = 2586797) B2586797
theorem B1724547 : Blo 1723062 1724547 := bstep (se 1 (by rfl) ⟨1293410, by rfl⟩ : syracuseStep 1724547 = 2586821) B2586821
theorem B2584721 : Blo 1723062 2584721 := bstep (se 2 (by rfl) ⟨969270, by rfl⟩ : syracuseStep 2584721 = 1938541) B1938541
theorem B1724563 : Blo 1723062 1724563 := bstep (se 1 (by rfl) ⟨1293422, by rfl⟩ : syracuseStep 1724563 = 2586845) B2586845
theorem B2584739 : Blo 1723062 2584739 := bstep (se 1 (by rfl) ⟨1938554, by rfl⟩ : syracuseStep 2584739 = 3877109) B3877109
theorem B1724579 : Blo 1723062 1724579 := bstep (se 1 (by rfl) ⟨1293434, by rfl⟩ : syracuseStep 1724579 = 2586869) B2586869
theorem B3879089 : Blo 1723062 3879089 := bstep (se 2 (by rfl) ⟨1454658, by rfl⟩ : syracuseStep 3879089 = 2909317) B2909317
theorem B1724595 : Blo 1723062 1724595 := bstep (se 1 (by rfl) ⟨1293446, by rfl⟩ : syracuseStep 1724595 = 2586893) B2586893
theorem B2584769 : Blo 1723062 2584769 := bstep (se 2 (by rfl) ⟨969288, by rfl⟩ : syracuseStep 2584769 = 1938577) B1938577
theorem B3272899 : Blo 1723062 3272899 := bstep (se 1 (by rfl) ⟨2454674, by rfl⟩ : syracuseStep 3272899 = 4909349) B4909349
theorem B3879107 : Blo 1723062 3879107 := bstep (se 1 (by rfl) ⟨2909330, by rfl⟩ : syracuseStep 3879107 = 5818661) B5818661
theorem B1724611 : Blo 1723062 1724611 := bstep (se 1 (by rfl) ⟨1293458, by rfl⟩ : syracuseStep 1724611 = 2586917) B2586917
theorem B2584787 : Blo 1723062 2584787 := bstep (se 1 (by rfl) ⟨1938590, by rfl⟩ : syracuseStep 2584787 = 3877181) B3877181
theorem B1724627 : Blo 1723062 1724627 := bstep (se 1 (by rfl) ⟨1293470, by rfl⟩ : syracuseStep 1724627 = 2586941) B2586941
theorem B2330851 : Blo 1723062 2330851 := bstep (se 1 (by rfl) ⟨1748138, by rfl⟩ : syracuseStep 2330851 = 3496277) B3496277
theorem B1724643 : Blo 1723062 1724643 := bstep (se 1 (by rfl) ⟨1293482, by rfl⟩ : syracuseStep 1724643 = 2586965) B2586965
theorem B6549731 : Blo 1723062 6549731 := bstep (se 1 (by rfl) ⟨4912298, by rfl⟩ : syracuseStep 6549731 = 9824597) B9824597
theorem B2584817 : Blo 1723062 2584817 := bstep (se 2 (by rfl) ⟨969306, by rfl⟩ : syracuseStep 2584817 = 1938613) B1938613
theorem B1724659 : Blo 1723062 1724659 := bstep (se 1 (by rfl) ⟨1293494, by rfl⟩ : syracuseStep 1724659 = 2586989) B2586989
theorem B2584835 : Blo 1723062 2584835 := bstep (se 1 (by rfl) ⟨1938626, by rfl⟩ : syracuseStep 2584835 = 3877253) B3877253
theorem B1724675 : Blo 1723062 1724675 := bstep (se 1 (by rfl) ⟨1293506, by rfl⟩ : syracuseStep 1724675 = 2587013) B2587013
theorem B1724691 : Blo 1723062 1724691 := bstep (se 1 (by rfl) ⟨1293518, by rfl⟩ : syracuseStep 1724691 = 2587037) B2587037
theorem B2584865 : Blo 1723062 2584865 := bstep (se 2 (by rfl) ⟨969324, by rfl⟩ : syracuseStep 2584865 = 1938649) B1938649
theorem B2330915 : Blo 1723062 2330915 := bstep (se 1 (by rfl) ⟨1748186, by rfl⟩ : syracuseStep 2330915 = 3496373) B3496373
theorem B1724707 : Blo 1723062 1724707 := bstep (se 1 (by rfl) ⟨1293530, by rfl⟩ : syracuseStep 1724707 = 2587061) B2587061
theorem B2453809 : Blo 1723062 2453809 := bstep (se 2 (by rfl) ⟨920178, by rfl⟩ : syracuseStep 2453809 = 1840357) B1840357
theorem B2584883 : Blo 1723062 2584883 := bstep (se 1 (by rfl) ⟨1938662, by rfl⟩ : syracuseStep 2584883 = 3877325) B3877325
theorem B1724723 : Blo 1723062 1724723 := bstep (se 1 (by rfl) ⟨1293542, by rfl⟩ : syracuseStep 1724723 = 2587085) B2587085
theorem B1724739 : Blo 1723062 1724739 := bstep (se 1 (by rfl) ⟨1293554, by rfl⟩ : syracuseStep 1724739 = 2587109) B2587109
theorem B2584913 : Blo 1723062 2584913 := bstep (se 2 (by rfl) ⟨969342, by rfl⟩ : syracuseStep 2584913 = 1938685) B1938685
theorem B1724755 : Blo 1723062 1724755 := bstep (se 1 (by rfl) ⟨1293566, by rfl⟩ : syracuseStep 1724755 = 2587133) B2587133
theorem B2584931 : Blo 1723062 2584931 := bstep (se 1 (by rfl) ⟨1938698, by rfl⟩ : syracuseStep 2584931 = 3877397) B3877397
theorem B1724771 : Blo 1723062 1724771 := bstep (se 1 (by rfl) ⟨1293578, by rfl⟩ : syracuseStep 1724771 = 2587157) B2587157
theorem B1724787 : Blo 1723062 1724787 := bstep (se 1 (by rfl) ⟨1293590, by rfl⟩ : syracuseStep 1724787 = 2587181) B2587181
theorem B2584961 : Blo 1723062 2584961 := bstep (se 2 (by rfl) ⟨969360, by rfl⟩ : syracuseStep 2584961 = 1938721) B1938721
theorem B1724803 : Blo 1723062 1724803 := bstep (se 1 (by rfl) ⟨1293602, by rfl⟩ : syracuseStep 1724803 = 2587205) B2587205
theorem B19640717 : Blo 1723062 19640717 := bstep (se 3 (by rfl) ⟨3682634, by rfl⟩ : syracuseStep 19640717 = 7365269) B7365269
theorem B2453905 : Blo 1723062 2453905 := bstep (se 2 (by rfl) ⟨920214, by rfl⟩ : syracuseStep 2453905 = 1840429) B1840429
theorem B2584979 : Blo 1723062 2584979 := bstep (se 1 (by rfl) ⟨1938734, by rfl⟩ : syracuseStep 2584979 = 3877469) B3877469
theorem B1724819 : Blo 1723062 1724819 := bstep (se 1 (by rfl) ⟨1293614, by rfl⟩ : syracuseStep 1724819 = 2587229) B2587229
theorem B1724835 : Blo 1723062 1724835 := bstep (se 1 (by rfl) ⟨1293626, by rfl⟩ : syracuseStep 1724835 = 2587253) B2587253
theorem B2585009 : Blo 1723062 2585009 := bstep (se 2 (by rfl) ⟨969378, by rfl⟩ : syracuseStep 2585009 = 1938757) B1938757
theorem B1724851 : Blo 1723062 1724851 := bstep (se 1 (by rfl) ⟨1293638, by rfl⟩ : syracuseStep 1724851 = 2587277) B2587277
theorem B2585027 : Blo 1723062 2585027 := bstep (se 1 (by rfl) ⟨1938770, by rfl⟩ : syracuseStep 2585027 = 3877541) B3877541
theorem B1724867 : Blo 1723062 1724867 := bstep (se 1 (by rfl) ⟨1293650, by rfl⟩ : syracuseStep 1724867 = 2587301) B2587301
theorem B3879377 : Blo 1723062 3879377 := bstep (se 2 (by rfl) ⟨1454766, by rfl⟩ : syracuseStep 3879377 = 2909533) B2909533
theorem B1724883 : Blo 1723062 1724883 := bstep (se 1 (by rfl) ⟨1293662, by rfl⟩ : syracuseStep 1724883 = 2587325) B2587325
theorem B2585057 : Blo 1723062 2585057 := bstep (se 2 (by rfl) ⟨969396, by rfl⟩ : syracuseStep 2585057 = 1938793) B1938793
theorem B3879395 : Blo 1723062 3879395 := bstep (se 1 (by rfl) ⟨2909546, by rfl⟩ : syracuseStep 3879395 = 5819093) B5819093
theorem B1724899 : Blo 1723062 1724899 := bstep (se 1 (by rfl) ⟨1293674, by rfl⟩ : syracuseStep 1724899 = 2587349) B2587349
theorem B2585075 : Blo 1723062 2585075 := bstep (se 1 (by rfl) ⟨1938806, by rfl⟩ : syracuseStep 2585075 = 3877613) B3877613
theorem B1724915 : Blo 1723062 1724915 := bstep (se 1 (by rfl) ⟨1293686, by rfl⟩ : syracuseStep 1724915 = 2587373) B2587373
theorem B1724931 : Blo 1723062 1724931 := bstep (se 1 (by rfl) ⟨1293698, by rfl⟩ : syracuseStep 1724931 = 2587397) B2587397
theorem B2585105 : Blo 1723062 2585105 := bstep (se 2 (by rfl) ⟨969414, by rfl⟩ : syracuseStep 2585105 = 1938829) B1938829
theorem B1724947 : Blo 1723062 1724947 := bstep (se 1 (by rfl) ⟨1293710, by rfl⟩ : syracuseStep 1724947 = 2587421) B2587421
theorem B2585123 : Blo 1723062 2585123 := bstep (se 1 (by rfl) ⟨1938842, by rfl⟩ : syracuseStep 2585123 = 3877685) B3877685
theorem B1724963 : Blo 1723062 1724963 := bstep (se 1 (by rfl) ⟨1293722, by rfl⟩ : syracuseStep 1724963 = 2587445) B2587445
theorem B1724979 : Blo 1723062 1724979 := bstep (se 1 (by rfl) ⟨1293734, by rfl⟩ : syracuseStep 1724979 = 2587469) B2587469
theorem B2585153 : Blo 1723062 2585153 := bstep (se 2 (by rfl) ⟨969432, by rfl⟩ : syracuseStep 2585153 = 1938865) B1938865
theorem B1724995 : Blo 1723062 1724995 := bstep (se 1 (by rfl) ⟨1293746, by rfl⟩ : syracuseStep 1724995 = 2587493) B2587493
theorem B2585171 : Blo 1723062 2585171 := bstep (se 1 (by rfl) ⟨1938878, by rfl⟩ : syracuseStep 2585171 = 3877757) B3877757
theorem B1725011 : Blo 1723062 1725011 := bstep (se 1 (by rfl) ⟨1293758, by rfl⟩ : syracuseStep 1725011 = 2587517) B2587517
theorem B1725027 : Blo 1723062 1725027 := bstep (se 1 (by rfl) ⟨1293770, by rfl⟩ : syracuseStep 1725027 = 2587541) B2587541
theorem B5821037 : Blo 1723062 5821037 := bstep (se 3 (by rfl) ⟨1091444, by rfl⟩ : syracuseStep 5821037 = 2182889) B2182889
theorem B2585201 : Blo 1723062 2585201 := bstep (se 2 (by rfl) ⟨969450, by rfl⟩ : syracuseStep 2585201 = 1938901) B1938901
theorem B1725043 : Blo 1723062 1725043 := bstep (se 1 (by rfl) ⟨1293782, by rfl⟩ : syracuseStep 1725043 = 2587565) B2587565
theorem B2585219 : Blo 1723062 2585219 := bstep (se 1 (by rfl) ⟨1938914, by rfl⟩ : syracuseStep 2585219 = 3877829) B3877829
theorem B3273347 : Blo 1723062 3273347 := bstep (se 1 (by rfl) ⟨2455010, by rfl⟩ : syracuseStep 3273347 = 4910021) B4910021
theorem B1725059 : Blo 1723062 1725059 := bstep (se 1 (by rfl) ⟨1293794, by rfl⟩ : syracuseStep 1725059 = 2587589) B2587589
theorem B9818765 : Blo 1723062 9818765 := bstep (se 3 (by rfl) ⟨1841018, by rfl⟩ : syracuseStep 9818765 = 3682037) B3682037
theorem B5526157 : Blo 1723062 5526157 := bstep (se 3 (by rfl) ⟨1036154, by rfl⟩ : syracuseStep 5526157 = 2072309) B2072309
theorem B2585249 : Blo 1723062 2585249 := bstep (se 2 (by rfl) ⟨969468, by rfl⟩ : syracuseStep 2585249 = 1938937) B1938937
theorem B5821091 : Blo 1723062 5821091 := bstep (se 1 (by rfl) ⟨4365818, by rfl⟩ : syracuseStep 5821091 = 8731637) B8731637
theorem B10629809 : Blo 1723062 10629809 := bstep (se 2 (by rfl) ⟨3986178, by rfl⟩ : syracuseStep 10629809 = 7972357) B7972357
theorem B2585267 : Blo 1723062 2585267 := bstep (se 1 (by rfl) ⟨1938950, by rfl⟩ : syracuseStep 2585267 = 3877901) B3877901
theorem B19903157 : Blo 1723062 19903157 := bstep (se 5 (by rfl) ⟨932960, by rfl⟩ : syracuseStep 19903157 = 1865921) B1865921
theorem B3683011 : Blo 1723062 3683011 := bstep (se 1 (by rfl) ⟨2762258, by rfl⟩ : syracuseStep 3683011 = 5524517) B5524517
theorem B2585297 : Blo 1723062 2585297 := bstep (se 2 (by rfl) ⟨969486, by rfl⟩ : syracuseStep 2585297 = 1938973) B1938973
theorem B2585315 : Blo 1723062 2585315 := bstep (se 1 (by rfl) ⟨1938986, by rfl⟩ : syracuseStep 2585315 = 3877973) B3877973
theorem B3879665 : Blo 1723062 3879665 := bstep (se 2 (by rfl) ⟨1454874, by rfl⟩ : syracuseStep 3879665 = 2909749) B2909749
theorem B2585345 : Blo 1723062 2585345 := bstep (se 2 (by rfl) ⟨969504, by rfl⟩ : syracuseStep 2585345 = 1939009) B1939009
theorem B3879683 : Blo 1723062 3879683 := bstep (se 1 (by rfl) ⟨2909762, by rfl⟩ : syracuseStep 3879683 = 5819525) B5819525
theorem B10490629 : Blo 1723062 10490629 := bstep (se 4 (by rfl) ⟨983496, by rfl⟩ : syracuseStep 10490629 = 1966993) B1966993
theorem B2585363 : Blo 1723062 2585363 := bstep (se 1 (by rfl) ⟨1939022, by rfl⟩ : syracuseStep 2585363 = 3878045) B3878045
theorem B2585393 : Blo 1723062 2585393 := bstep (se 2 (by rfl) ⟨969522, by rfl⟩ : syracuseStep 2585393 = 1939045) B1939045
theorem B2585411 : Blo 1723062 2585411 := bstep (se 1 (by rfl) ⟨1939058, by rfl⟩ : syracuseStep 2585411 = 3878117) B3878117
theorem B5755715 : Blo 1723062 5755715 := bstep (se 1 (by rfl) ⟨4316786, by rfl⟩ : syracuseStep 5755715 = 8633573) B8633573
theorem B2585441 : Blo 1723062 2585441 := bstep (se 2 (by rfl) ⟨969540, by rfl⟩ : syracuseStep 2585441 = 1939081) B1939081
theorem B11793251 : Blo 1723062 11793251 := bstep (se 1 (by rfl) ⟨8844938, by rfl⟩ : syracuseStep 11793251 = 17689877) B17689877
theorem B2585459 : Blo 1723062 2585459 := bstep (se 1 (by rfl) ⟨1939094, by rfl⟩ : syracuseStep 2585459 = 3878189) B3878189
theorem B2454401 : Blo 1723062 2454401 := bstep (se 2 (by rfl) ⟨920400, by rfl⟩ : syracuseStep 2454401 = 1840801) B1840801
theorem B2585489 : Blo 1723062 2585489 := bstep (se 2 (by rfl) ⟨969558, by rfl⟩ : syracuseStep 2585489 = 1939117) B1939117
theorem B2585507 : Blo 1723062 2585507 := bstep (se 1 (by rfl) ⟨1939130, by rfl⟩ : syracuseStep 2585507 = 3878261) B3878261
theorem B3273635 : Blo 1723062 3273635 := bstep (se 1 (by rfl) ⟨2455226, by rfl⟩ : syracuseStep 3273635 = 4910453) B4910453
theorem B5821361 : Blo 1723062 5821361 := bstep (se 2 (by rfl) ⟨2183010, by rfl⟩ : syracuseStep 5821361 = 4366021) B4366021
theorem B2585537 : Blo 1723062 2585537 := bstep (se 2 (by rfl) ⟨969576, by rfl⟩ : syracuseStep 2585537 = 1939153) B1939153
theorem B4363217 : Blo 1723062 4363217 := bstep (se 2 (by rfl) ⟨1636206, by rfl⟩ : syracuseStep 4363217 = 3272413) B3272413
theorem B2585555 : Blo 1723062 2585555 := bstep (se 1 (by rfl) ⟨1939166, by rfl⟩ : syracuseStep 2585555 = 3878333) B3878333
theorem B2585585 : Blo 1723062 2585585 := bstep (se 2 (by rfl) ⟨969594, by rfl⟩ : syracuseStep 2585585 = 1939189) B1939189
theorem B2585603 : Blo 1723062 2585603 := bstep (se 1 (by rfl) ⟨1939202, by rfl⟩ : syracuseStep 2585603 = 3878405) B3878405
theorem B4363267 : Blo 1723062 4363267 := bstep (se 1 (by rfl) ⟨3272450, by rfl⟩ : syracuseStep 4363267 = 6544901) B6544901
theorem B3879953 : Blo 1723062 3879953 := bstep (se 2 (by rfl) ⟨1454982, by rfl⟩ : syracuseStep 3879953 = 2909965) B2909965
theorem B1938451 : Blo 1723062 1938451 := bstep (se 1 (by rfl) ⟨1453838, by rfl⟩ : syracuseStep 1938451 = 2907677) B2907677
theorem B2585633 : Blo 1723062 2585633 := bstep (se 2 (by rfl) ⟨969612, by rfl⟩ : syracuseStep 2585633 = 1939225) B1939225
theorem B3879971 : Blo 1723062 3879971 := bstep (se 1 (by rfl) ⟨2909978, by rfl⟩ : syracuseStep 3879971 = 5819957) B5819957
theorem B2585651 : Blo 1723062 2585651 := bstep (se 1 (by rfl) ⟨1939238, by rfl⟩ : syracuseStep 2585651 = 3878477) B3878477
theorem B2585681 : Blo 1723062 2585681 := bstep (se 2 (by rfl) ⟨969630, by rfl⟩ : syracuseStep 2585681 = 1939261) B1939261
theorem B2585699 : Blo 1723062 2585699 := bstep (se 1 (by rfl) ⟨1939274, by rfl⟩ : syracuseStep 2585699 = 3878549) B3878549
theorem B2585729 : Blo 1723062 2585729 := bstep (se 2 (by rfl) ⟨969648, by rfl⟩ : syracuseStep 2585729 = 1939297) B1939297
theorem B4363409 : Blo 1723062 4363409 := bstep (se 2 (by rfl) ⟨1636278, by rfl⟩ : syracuseStep 4363409 = 3272557) B3272557
theorem B2585747 : Blo 1723062 2585747 := bstep (se 1 (by rfl) ⟨1939310, by rfl⟩ : syracuseStep 2585747 = 3878621) B3878621
theorem B1938595 : Blo 1723062 1938595 := bstep (se 1 (by rfl) ⟨1453946, by rfl⟩ : syracuseStep 1938595 = 2907893) B2907893
theorem B2585777 : Blo 1723062 2585777 := bstep (se 2 (by rfl) ⟨969666, by rfl⟩ : syracuseStep 2585777 = 1939333) B1939333
theorem B2585795 : Blo 1723062 2585795 := bstep (se 1 (by rfl) ⟨1939346, by rfl⟩ : syracuseStep 2585795 = 3878693) B3878693
theorem B2585825 : Blo 1723062 2585825 := bstep (se 2 (by rfl) ⟨969684, by rfl⟩ : syracuseStep 2585825 = 1939369) B1939369
theorem B2585843 : Blo 1723062 2585843 := bstep (se 1 (by rfl) ⟨1939382, by rfl⟩ : syracuseStep 2585843 = 3878765) B3878765
theorem B2585873 : Blo 1723062 2585873 := bstep (se 2 (by rfl) ⟨969702, by rfl⟩ : syracuseStep 2585873 = 1939405) B1939405
theorem B2585891 : Blo 1723062 2585891 := bstep (se 1 (by rfl) ⟨1939418, by rfl⟩ : syracuseStep 2585891 = 3878837) B3878837
theorem B3880241 : Blo 1723062 3880241 := bstep (se 2 (by rfl) ⟨1455090, by rfl⟩ : syracuseStep 3880241 = 2910181) B2910181
theorem B1938739 : Blo 1723062 1938739 := bstep (se 1 (by rfl) ⟨1454054, by rfl⟩ : syracuseStep 1938739 = 2908109) B2908109
theorem B2585921 : Blo 1723062 2585921 := bstep (se 2 (by rfl) ⟨969720, by rfl⟩ : syracuseStep 2585921 = 1939441) B1939441
theorem B3880259 : Blo 1723062 3880259 := bstep (se 1 (by rfl) ⟨2910194, by rfl⟩ : syracuseStep 3880259 = 5820389) B5820389
theorem B2585939 : Blo 1723062 2585939 := bstep (se 1 (by rfl) ⟨1939454, by rfl⟩ : syracuseStep 2585939 = 3878909) B3878909
theorem B11040113 : Blo 1723062 11040113 := bstep (se 2 (by rfl) ⟨4140042, by rfl⟩ : syracuseStep 11040113 = 8280085) B8280085
theorem B2585969 : Blo 1723062 2585969 := bstep (se 2 (by rfl) ⟨969738, by rfl⟩ : syracuseStep 2585969 = 1939477) B1939477
theorem B2585987 : Blo 1723062 2585987 := bstep (se 1 (by rfl) ⟨1939490, by rfl⟩ : syracuseStep 2585987 = 3878981) B3878981
theorem B2586017 : Blo 1723062 2586017 := bstep (se 2 (by rfl) ⟨969756, by rfl⟩ : syracuseStep 2586017 = 1939513) B1939513
theorem B2586035 : Blo 1723062 2586035 := bstep (se 1 (by rfl) ⟨1939526, by rfl⟩ : syracuseStep 2586035 = 3879053) B3879053
theorem B1938883 : Blo 1723062 1938883 := bstep (se 1 (by rfl) ⟨1454162, by rfl⟩ : syracuseStep 1938883 = 2908325) B2908325
theorem B50386373 : Blo 1723062 50386373 := bstep (se 4 (by rfl) ⟨4723722, by rfl⟩ : syracuseStep 50386373 = 9447445) B9447445
theorem B5821901 : Blo 1723062 5821901 := bstep (se 3 (by rfl) ⟨1091606, by rfl⟩ : syracuseStep 5821901 = 2183213) B2183213
theorem B2586065 : Blo 1723062 2586065 := bstep (se 2 (by rfl) ⟨969774, by rfl⟩ : syracuseStep 2586065 = 1939549) B1939549
theorem B2586083 : Blo 1723062 2586083 := bstep (se 1 (by rfl) ⟨1939562, by rfl⟩ : syracuseStep 2586083 = 3879125) B3879125
theorem B2586113 : Blo 1723062 2586113 := bstep (se 2 (by rfl) ⟨969792, by rfl⟩ : syracuseStep 2586113 = 1939585) B1939585
theorem B5821955 : Blo 1723062 5821955 := bstep (se 1 (by rfl) ⟨4366466, by rfl⟩ : syracuseStep 5821955 = 8732933) B8732933
theorem B4421137 : Blo 1723062 4421137 := bstep (se 2 (by rfl) ⟨1657926, by rfl⟩ : syracuseStep 4421137 = 3315853) B3315853
theorem B2586131 : Blo 1723062 2586131 := bstep (se 1 (by rfl) ⟨1939598, by rfl⟩ : syracuseStep 2586131 = 3879197) B3879197
theorem B2586161 : Blo 1723062 2586161 := bstep (se 2 (by rfl) ⟨969810, by rfl⟩ : syracuseStep 2586161 = 1939621) B1939621
theorem B2586179 : Blo 1723062 2586179 := bstep (se 1 (by rfl) ⟨1939634, by rfl⟩ : syracuseStep 2586179 = 3879269) B3879269
theorem B3880529 : Blo 1723062 3880529 := bstep (se 2 (by rfl) ⟨1455198, by rfl⟩ : syracuseStep 3880529 = 2910397) B2910397
theorem B1939027 : Blo 1723062 1939027 := bstep (se 1 (by rfl) ⟨1454270, by rfl⟩ : syracuseStep 1939027 = 2908541) B2908541
theorem B2586209 : Blo 1723062 2586209 := bstep (se 2 (by rfl) ⟨969828, by rfl⟩ : syracuseStep 2586209 = 1939657) B1939657
theorem B3880547 : Blo 1723062 3880547 := bstep (se 1 (by rfl) ⟨2910410, by rfl⟩ : syracuseStep 3880547 = 5820821) B5820821
theorem B7362161 : Blo 1723062 7362161 := bstep (se 2 (by rfl) ⟨2760810, by rfl⟩ : syracuseStep 7362161 = 5521621) B5521621
theorem B2586227 : Blo 1723062 2586227 := bstep (se 1 (by rfl) ⟨1939670, by rfl⟩ : syracuseStep 2586227 = 3879341) B3879341
theorem B2586257 : Blo 1723062 2586257 := bstep (se 2 (by rfl) ⟨969846, by rfl⟩ : syracuseStep 2586257 = 1939693) B1939693
theorem B2586275 : Blo 1723062 2586275 := bstep (se 1 (by rfl) ⟨1939706, by rfl⟩ : syracuseStep 2586275 = 3879413) B3879413
theorem B2586305 : Blo 1723062 2586305 := bstep (se 2 (by rfl) ⟨969864, by rfl⟩ : syracuseStep 2586305 = 1939729) B1939729
theorem B2586323 : Blo 1723062 2586323 := bstep (se 1 (by rfl) ⟨1939742, by rfl⟩ : syracuseStep 2586323 = 3879485) B3879485
theorem B1939171 : Blo 1723062 1939171 := bstep (se 1 (by rfl) ⟨1454378, by rfl⟩ : syracuseStep 1939171 = 2908757) B2908757
theorem B2455267 : Blo 1723062 2455267 := bstep (se 1 (by rfl) ⟨1841450, by rfl⟩ : syracuseStep 2455267 = 3682901) B3682901
theorem B2586353 : Blo 1723062 2586353 := bstep (se 2 (by rfl) ⟨969882, by rfl⟩ : syracuseStep 2586353 = 1939765) B1939765
theorem B2586371 : Blo 1723062 2586371 := bstep (se 1 (by rfl) ⟨1939778, by rfl⟩ : syracuseStep 2586371 = 3879557) B3879557
theorem B2586401 : Blo 1723062 2586401 := bstep (se 2 (by rfl) ⟨969900, by rfl⟩ : syracuseStep 2586401 = 1939801) B1939801
theorem B6543139 : Blo 1723062 6543139 := bstep (se 1 (by rfl) ⟨4907354, by rfl⟩ : syracuseStep 6543139 = 9814709) B9814709
theorem B2586419 : Blo 1723062 2586419 := bstep (se 1 (by rfl) ⟨1939814, by rfl⟩ : syracuseStep 2586419 = 3879629) B3879629
theorem B2455363 : Blo 1723062 2455363 := bstep (se 1 (by rfl) ⟨1841522, by rfl⟩ : syracuseStep 2455363 = 3683045) B3683045
theorem B2586449 : Blo 1723062 2586449 := bstep (se 2 (by rfl) ⟨969918, by rfl⟩ : syracuseStep 2586449 = 1939837) B1939837
theorem B3274577 : Blo 1723062 3274577 := bstep (se 2 (by rfl) ⟨1227966, by rfl⟩ : syracuseStep 3274577 = 2455933) B2455933
theorem B2586467 : Blo 1723062 2586467 := bstep (se 1 (by rfl) ⟨1939850, by rfl⟩ : syracuseStep 2586467 = 3879701) B3879701
theorem B3880817 : Blo 1723062 3880817 := bstep (se 2 (by rfl) ⟨1455306, by rfl⟩ : syracuseStep 3880817 = 2910613) B2910613
theorem B1939315 : Blo 1723062 1939315 := bstep (se 1 (by rfl) ⟨1454486, by rfl⟩ : syracuseStep 1939315 = 2908973) B2908973
theorem B2586497 : Blo 1723062 2586497 := bstep (se 2 (by rfl) ⟨969936, by rfl⟩ : syracuseStep 2586497 = 1939873) B1939873
theorem B1841027 : Blo 1723062 1841027 := bstep (se 1 (by rfl) ⟨1380770, by rfl⟩ : syracuseStep 1841027 = 2761541) B2761541
theorem B3880835 : Blo 1723062 3880835 := bstep (se 1 (by rfl) ⟨2910626, by rfl⟩ : syracuseStep 3880835 = 5821253) B5821253
theorem B149157773 : Blo 1723062 149157773 := bstep (se 3 (by rfl) ⟨27967082, by rfl⟩ : syracuseStep 149157773 = 55934165) B55934165
theorem B3684241 : Blo 1723062 3684241 := bstep (se 2 (by rfl) ⟨1381590, by rfl⟩ : syracuseStep 3684241 = 2763181) B2763181
theorem B2586515 : Blo 1723062 2586515 := bstep (se 1 (by rfl) ⟨1939886, by rfl⟩ : syracuseStep 2586515 = 3879773) B3879773
theorem B2586545 : Blo 1723062 2586545 := bstep (se 2 (by rfl) ⟨969954, by rfl⟩ : syracuseStep 2586545 = 1939909) B1939909
theorem B2586563 : Blo 1723062 2586563 := bstep (se 1 (by rfl) ⟨1939922, by rfl⟩ : syracuseStep 2586563 = 3879845) B3879845
theorem B2586593 : Blo 1723062 2586593 := bstep (se 2 (by rfl) ⟨969972, by rfl⟩ : syracuseStep 2586593 = 1939945) B1939945
theorem B2586611 : Blo 1723062 2586611 := bstep (se 1 (by rfl) ⟨1939958, by rfl⟩ : syracuseStep 2586611 = 3879917) B3879917
theorem B1939459 : Blo 1723062 1939459 := bstep (se 1 (by rfl) ⟨1454594, by rfl⟩ : syracuseStep 1939459 = 2909189) B2909189
theorem B2586641 : Blo 1723062 2586641 := bstep (se 2 (by rfl) ⟨969990, by rfl⟩ : syracuseStep 2586641 = 1939981) B1939981
theorem B2586659 : Blo 1723062 2586659 := bstep (se 1 (by rfl) ⟨1939994, by rfl⟩ : syracuseStep 2586659 = 3879989) B3879989
theorem B2586689 : Blo 1723062 2586689 := bstep (se 2 (by rfl) ⟨970008, by rfl⟩ : syracuseStep 2586689 = 1940017) B1940017
theorem B2586707 : Blo 1723062 2586707 := bstep (se 1 (by rfl) ⟨1940030, by rfl⟩ : syracuseStep 2586707 = 3880061) B3880061
theorem B14735459 : Blo 1723062 14735459 := bstep (se 1 (by rfl) ⟨11051594, by rfl⟩ : syracuseStep 14735459 = 22103189) B22103189
theorem B4364401 : Blo 1723062 4364401 := bstep (se 2 (by rfl) ⟨1636650, by rfl⟩ : syracuseStep 4364401 = 3273301) B3273301
theorem B2586737 : Blo 1723062 2586737 := bstep (se 2 (by rfl) ⟨970026, by rfl⟩ : syracuseStep 2586737 = 1940053) B1940053
theorem B2586755 : Blo 1723062 2586755 := bstep (se 1 (by rfl) ⟨1940066, by rfl⟩ : syracuseStep 2586755 = 3880133) B3880133
theorem B3881105 : Blo 1723062 3881105 := bstep (se 2 (by rfl) ⟨1455414, by rfl⟩ : syracuseStep 3881105 = 2910829) B2910829
theorem B1939603 : Blo 1723062 1939603 := bstep (se 1 (by rfl) ⟨1454702, by rfl⟩ : syracuseStep 1939603 = 2909405) B2909405
theorem B2586785 : Blo 1723062 2586785 := bstep (se 2 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 2586785 = 1940089) B1940089
theorem B3881123 : Blo 1723062 3881123 := bstep (se 1 (by rfl) ⟨2910842, by rfl⟩ : syracuseStep 3881123 = 5821685) B5821685
theorem B2586803 : Blo 1723062 2586803 := bstep (se 1 (by rfl) ⟨1940102, by rfl⟩ : syracuseStep 2586803 = 3880205) B3880205
theorem B2586833 : Blo 1723062 2586833 := bstep (se 2 (by rfl) ⟨970062, by rfl⟩ : syracuseStep 2586833 = 1940125) B1940125
theorem B2586851 : Blo 1723062 2586851 := bstep (se 1 (by rfl) ⟨1940138, by rfl⟩ : syracuseStep 2586851 = 3880277) B3880277
theorem B3315953 : Blo 1723062 3315953 := bstep (se 2 (by rfl) ⟨1243482, by rfl⟩ : syracuseStep 3315953 = 2486965) B2486965
theorem B2586881 : Blo 1723062 2586881 := bstep (se 2 (by rfl) ⟨970080, by rfl⟩ : syracuseStep 2586881 = 1940161) B1940161
theorem B2586899 : Blo 1723062 2586899 := bstep (se 1 (by rfl) ⟨1940174, by rfl⟩ : syracuseStep 2586899 = 3880349) B3880349
theorem B1939747 : Blo 1723062 1939747 := bstep (se 1 (by rfl) ⟨1454810, by rfl⟩ : syracuseStep 1939747 = 2909621) B2909621
theorem B2586929 : Blo 1723062 2586929 := bstep (se 2 (by rfl) ⟨970098, by rfl⟩ : syracuseStep 2586929 = 1940197) B1940197
theorem B2455859 : Blo 1723062 2455859 := bstep (se 1 (by rfl) ⟨1841894, by rfl⟩ : syracuseStep 2455859 = 3683789) B3683789
theorem B2586947 : Blo 1723062 2586947 := bstep (se 1 (by rfl) ⟨1940210, by rfl⟩ : syracuseStep 2586947 = 3880421) B3880421
theorem B2586977 : Blo 1723062 2586977 := bstep (se 2 (by rfl) ⟨970116, by rfl⟩ : syracuseStep 2586977 = 1940233) B1940233
theorem B2586995 : Blo 1723062 2586995 := bstep (se 1 (by rfl) ⟨1940246, by rfl⟩ : syracuseStep 2586995 = 3880493) B3880493
theorem B4364675 : Blo 1723062 4364675 := bstep (se 1 (by rfl) ⟨3273506, by rfl⟩ : syracuseStep 4364675 = 6547013) B6547013
theorem B2587025 : Blo 1723062 2587025 := bstep (se 2 (by rfl) ⟨970134, by rfl⟩ : syracuseStep 2587025 = 1940269) B1940269
theorem B2587043 : Blo 1723062 2587043 := bstep (se 1 (by rfl) ⟨1940282, by rfl⟩ : syracuseStep 2587043 = 3880565) B3880565
theorem B1939891 : Blo 1723062 1939891 := bstep (se 1 (by rfl) ⟨1454918, by rfl⟩ : syracuseStep 1939891 = 2909837) B2909837
theorem B2587073 : Blo 1723062 2587073 := bstep (se 2 (by rfl) ⟨970152, by rfl⟩ : syracuseStep 2587073 = 1940305) B1940305
theorem B17250757 : Blo 1723062 17250757 := bstep (se 4 (by rfl) ⟨1617258, by rfl⟩ : syracuseStep 17250757 = 3234517) B3234517
theorem B2587091 : Blo 1723062 2587091 := bstep (se 1 (by rfl) ⟨1940318, by rfl⟩ : syracuseStep 2587091 = 3880637) B3880637
theorem B11049443 : Blo 1723062 11049443 := bstep (se 1 (by rfl) ⟨8287082, by rfl⟩ : syracuseStep 11049443 = 16574165) B16574165
theorem B2587121 : Blo 1723062 2587121 := bstep (se 2 (by rfl) ⟨970170, by rfl⟩ : syracuseStep 2587121 = 1940341) B1940341
theorem B2587139 : Blo 1723062 2587139 := bstep (se 1 (by rfl) ⟨1940354, by rfl⟩ : syracuseStep 2587139 = 3880709) B3880709
theorem B2587169 : Blo 1723062 2587169 := bstep (se 2 (by rfl) ⟨970188, by rfl⟩ : syracuseStep 2587169 = 1940377) B1940377
theorem B2587187 : Blo 1723062 2587187 := bstep (se 1 (by rfl) ⟨1940390, by rfl⟩ : syracuseStep 2587187 = 3880781) B3880781
theorem B4364867 : Blo 1723062 4364867 := bstep (se 1 (by rfl) ⟨3273650, by rfl⟩ : syracuseStep 4364867 = 6547301) B6547301
theorem B1940035 : Blo 1723062 1940035 := bstep (se 1 (by rfl) ⟨1455026, by rfl⟩ : syracuseStep 1940035 = 2910053) B2910053
theorem B2587217 : Blo 1723062 2587217 := bstep (se 2 (by rfl) ⟨970206, by rfl⟩ : syracuseStep 2587217 = 1940413) B1940413
theorem B2587235 : Blo 1723062 2587235 := bstep (se 1 (by rfl) ⟨1940426, by rfl⟩ : syracuseStep 2587235 = 3880853) B3880853
theorem B1841779 : Blo 1723062 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B2587265 : Blo 1723062 2587265 := bstep (se 2 (by rfl) ⟨970224, by rfl⟩ : syracuseStep 2587265 = 1940449) B1940449
theorem B2587283 : Blo 1723062 2587283 := bstep (se 1 (by rfl) ⟨1940462, by rfl⟩ : syracuseStep 2587283 = 3880925) B3880925
theorem B4659875 : Blo 1723062 4659875 := bstep (se 1 (by rfl) ⟨3494906, by rfl⟩ : syracuseStep 4659875 = 6989813) B6989813
theorem B8731313 : Blo 1723062 8731313 := bstep (se 2 (by rfl) ⟨3274242, by rfl⟩ : syracuseStep 8731313 = 6548485) B6548485
theorem B2587313 : Blo 1723062 2587313 := bstep (se 2 (by rfl) ⟨970242, by rfl⟩ : syracuseStep 2587313 = 1940485) B1940485
theorem B4143811 : Blo 1723062 4143811 := bstep (se 1 (by rfl) ⟨3107858, by rfl⟩ : syracuseStep 4143811 = 6215717) B6215717
theorem B19634885 : Blo 1723062 19634885 := bstep (se 4 (by rfl) ⟨1840770, by rfl⟩ : syracuseStep 19634885 = 3681541) B3681541
theorem B2587331 : Blo 1723062 2587331 := bstep (se 1 (by rfl) ⟨1940498, by rfl⟩ : syracuseStep 2587331 = 3880997) B3880997
theorem B1940179 : Blo 1723062 1940179 := bstep (se 1 (by rfl) ⟨1455134, by rfl⟩ : syracuseStep 1940179 = 2910269) B2910269
theorem B2587361 : Blo 1723062 2587361 := bstep (se 2 (by rfl) ⟨970260, by rfl⟩ : syracuseStep 2587361 = 1940521) B1940521
theorem B13097699 : Blo 1723062 13097699 := bstep (se 1 (by rfl) ⟨9823274, by rfl⟩ : syracuseStep 13097699 = 19646549) B19646549
theorem B5520109 : Blo 1723062 5520109 := bstep (se 3 (by rfl) ⟨1035020, by rfl⟩ : syracuseStep 5520109 = 2070041) B2070041
theorem B5241581 : Blo 1723062 5241581 := bstep (se 3 (by rfl) ⟨982796, by rfl⟩ : syracuseStep 5241581 = 1965593) B1965593
theorem B2587379 : Blo 1723062 2587379 := bstep (se 1 (by rfl) ⟨1940534, by rfl⟩ : syracuseStep 2587379 = 3881069) B3881069
theorem B8723213 : Blo 1723062 8723213 := bstep (se 3 (by rfl) ⟨1635602, by rfl⟩ : syracuseStep 8723213 = 3271205) B3271205
theorem B2587409 : Blo 1723062 2587409 := bstep (se 2 (by rfl) ⟨970278, by rfl⟩ : syracuseStep 2587409 = 1940557) B1940557
theorem B2587427 : Blo 1723062 2587427 := bstep (se 1 (by rfl) ⟨1940570, by rfl⟩ : syracuseStep 2587427 = 3881141) B3881141
theorem B2587457 : Blo 1723062 2587457 := bstep (se 2 (by rfl) ⟨970296, by rfl⟩ : syracuseStep 2587457 = 1940593) B1940593
theorem B9820997 : Blo 1723062 9820997 := bstep (se 4 (by rfl) ⟨920718, by rfl⟩ : syracuseStep 9820997 = 1841437) B1841437
theorem B2587475 : Blo 1723062 2587475 := bstep (se 1 (by rfl) ⟨1940606, by rfl⟩ : syracuseStep 2587475 = 3881213) B3881213
theorem B1940323 : Blo 1723062 1940323 := bstep (se 1 (by rfl) ⟨1455242, by rfl⟩ : syracuseStep 1940323 = 2910485) B2910485
theorem B2587505 : Blo 1723062 2587505 := bstep (se 2 (by rfl) ⟨970314, by rfl⟩ : syracuseStep 2587505 = 1940629) B1940629
theorem B1842035 : Blo 1723062 1842035 := bstep (se 1 (by rfl) ⟨1381526, by rfl⟩ : syracuseStep 1842035 = 2763053) B2763053
theorem B2587523 : Blo 1723062 2587523 := bstep (se 1 (by rfl) ⟨1940642, by rfl⟩ : syracuseStep 2587523 = 3881285) B3881285
theorem B2587553 : Blo 1723062 2587553 := bstep (se 2 (by rfl) ⟨970332, by rfl⟩ : syracuseStep 2587553 = 1940665) B1940665
theorem B2587571 : Blo 1723062 2587571 := bstep (se 1 (by rfl) ⟨1940678, by rfl⟩ : syracuseStep 2587571 = 3881357) B3881357
theorem B12598213 : Blo 1723062 12598213 := bstep (se 4 (by rfl) ⟨1181082, by rfl⟩ : syracuseStep 12598213 = 2362165) B2362165
theorem B5520365 : Blo 1723062 5520365 := bstep (se 3 (by rfl) ⟨1035068, by rfl⟩ : syracuseStep 5520365 = 2070137) B2070137
theorem B1940467 : Blo 1723062 1940467 := bstep (se 1 (by rfl) ⟨1455350, by rfl⟩ : syracuseStep 1940467 = 2910701) B2910701
theorem B10484741 : Blo 1723062 10484741 := bstep (se 4 (by rfl) ⟨982944, by rfl⟩ : syracuseStep 10484741 = 1965889) B1965889
theorem B2800673 : Blo 1723062 2800673 := bstep (se 2 (by rfl) ⟨1050252, by rfl⟩ : syracuseStep 2800673 = 2100505) B2100505
theorem B2620529 : Blo 1723062 2620529 := bstep (se 2 (by rfl) ⟨982698, by rfl⟩ : syracuseStep 2620529 = 1965397) B1965397
theorem B3931267 : Blo 1723062 3931267 := bstep (se 1 (by rfl) ⟨2948450, by rfl⟩ : syracuseStep 3931267 = 5896901) B5896901
theorem B1940611 : Blo 1723062 1940611 := bstep (se 1 (by rfl) ⟨1455458, by rfl⟩ : syracuseStep 1940611 = 2910917) B2910917
theorem B2071747 : Blo 1723062 2071747 := bstep (se 1 (by rfl) ⟨1553810, by rfl⟩ : syracuseStep 2071747 = 3107621) B3107621
theorem B2800849 : Blo 1723062 2800849 := bstep (se 2 (by rfl) ⟨1050318, by rfl⟩ : syracuseStep 2800849 = 2100637) B2100637
theorem B8281315 : Blo 1723062 8281315 := bstep (se 1 (by rfl) ⟨6210986, by rfl⟩ : syracuseStep 8281315 = 12421973) B12421973
theorem B19643633 : Blo 1723062 19643633 := bstep (se 2 (by rfl) ⟨7366362, by rfl⟩ : syracuseStep 19643633 = 14732725) B14732725
theorem B29441393 : Blo 1723062 29441393 := bstep (se 2 (by rfl) ⟨11040522, by rfl⟩ : syracuseStep 29441393 = 22081045) B22081045
theorem B34061795 : Blo 1723062 34061795 := bstep (se 1 (by rfl) ⟨25546346, by rfl⟩ : syracuseStep 34061795 = 51092693) B51092693
theorem B9821681 : Blo 1723062 9821681 := bstep (se 2 (by rfl) ⟨3683130, by rfl⟩ : syracuseStep 9821681 = 7366261) B7366261
theorem B4365809 : Blo 1723062 4365809 := bstep (se 2 (by rfl) ⟨1637178, by rfl⟩ : syracuseStep 4365809 = 3274357) B3274357
theorem B4365859 : Blo 1723062 4365859 := bstep (se 1 (by rfl) ⟨3274394, by rfl⟩ : syracuseStep 4365859 = 6548789) B6548789
theorem B5815853 : Blo 1723062 5815853 := bstep (se 3 (by rfl) ⟨1090472, by rfl⟩ : syracuseStep 5815853 = 2180945) B2180945
theorem B2907697 : Blo 1723062 2907697 := bstep (se 2 (by rfl) ⟨1090386, by rfl⟩ : syracuseStep 2907697 = 2180773) B2180773
theorem B2907731 : Blo 1723062 2907731 := bstep (se 1 (by rfl) ⟨2180798, by rfl⟩ : syracuseStep 2907731 = 4361597) B4361597
theorem B5815907 : Blo 1723062 5815907 := bstep (se 1 (by rfl) ⟨4361930, by rfl⟩ : syracuseStep 5815907 = 8723861) B8723861
theorem B8281777 : Blo 1723062 8281777 := bstep (se 2 (by rfl) ⟨3105666, by rfl⟩ : syracuseStep 8281777 = 6211333) B6211333
theorem B4366001 : Blo 1723062 4366001 := bstep (se 2 (by rfl) ⟨1637250, by rfl⟩ : syracuseStep 4366001 = 3274501) B3274501
theorem B2760401 : Blo 1723062 2760401 := bstep (se 2 (by rfl) ⟨1035150, by rfl⟩ : syracuseStep 2760401 = 2070301) B2070301
theorem B2907859 : Blo 1723062 2907859 := bstep (se 1 (by rfl) ⟨2180894, by rfl⟩ : syracuseStep 2907859 = 4361789) B4361789
theorem B4661009 : Blo 1723062 4661009 := bstep (se 2 (by rfl) ⟨1747878, by rfl⟩ : syracuseStep 4661009 = 3495757) B3495757
theorem B11050829 : Blo 1723062 11050829 := bstep (se 3 (by rfl) ⟨2072030, by rfl⟩ : syracuseStep 11050829 = 4144061) B4144061
theorem B2908001 : Blo 1723062 2908001 := bstep (se 2 (by rfl) ⟨1090500, by rfl⟩ : syracuseStep 2908001 = 2181001) B2181001
theorem B6987619 : Blo 1723062 6987619 := bstep (se 1 (by rfl) ⟨5240714, by rfl⟩ : syracuseStep 6987619 = 10481429) B10481429
theorem B5816177 : Blo 1723062 5816177 := bstep (se 2 (by rfl) ⟨2181066, by rfl⟩ : syracuseStep 5816177 = 4362133) B4362133
theorem B4423601 : Blo 1723062 4423601 := bstep (se 2 (by rfl) ⟨1658850, by rfl⟩ : syracuseStep 4423601 = 3317701) B3317701
theorem B6545357 : Blo 1723062 6545357 := bstep (se 3 (by rfl) ⟨1227254, by rfl⟩ : syracuseStep 6545357 = 2454509) B2454509
theorem B2908129 : Blo 1723062 2908129 := bstep (se 2 (by rfl) ⟨1090548, by rfl⟩ : syracuseStep 2908129 = 2181097) B2181097
theorem B2760689 : Blo 1723062 2760689 := bstep (se 2 (by rfl) ⟨1035258, by rfl⟩ : syracuseStep 2760689 = 2070517) B2070517
theorem B2949107 : Blo 1723062 2949107 := bstep (se 1 (by rfl) ⟨2211830, by rfl⟩ : syracuseStep 2949107 = 4423661) B4423661
theorem B2211851 : Blo 1723062 2211851 := bstep (se 1 (by rfl) ⟨1658888, by rfl⟩ : syracuseStep 2211851 = 3317777) B3317777
theorem B2908183 : Blo 1723062 2908183 := bstep (se 1 (by rfl) ⟨2181137, by rfl⟩ : syracuseStep 2908183 = 4362275) B4362275
theorem B24846371 : Blo 1723062 24846371 := bstep (se 1 (by rfl) ⟨18634778, by rfl⟩ : syracuseStep 24846371 = 37269557) B37269557
theorem B14729309 : Blo 1723062 14729309 := bstep (se 3 (by rfl) ⟨2761745, by rfl⟩ : syracuseStep 14729309 = 5523491) B5523491
theorem B4366487 : Blo 1723062 4366487 := bstep (se 1 (by rfl) ⟨3274865, by rfl⟩ : syracuseStep 4366487 = 6549731) B6549731
theorem B3932363 : Blo 1723062 3932363 := bstep (se 1 (by rfl) ⟨2949272, by rfl⟩ : syracuseStep 3932363 = 5898545) B5898545
theorem B4423897 : Blo 1723062 4423897 := bstep (se 2 (by rfl) ⟨1658961, by rfl⟩ : syracuseStep 4423897 = 3317923) B3317923
theorem B2621783 : Blo 1723062 2621783 := bstep (se 1 (by rfl) ⟨1966337, by rfl⟩ : syracuseStep 2621783 = 3932675) B3932675
theorem B3932545 : Blo 1723062 3932545 := bstep (se 2 (by rfl) ⟨1474704, by rfl⟩ : syracuseStep 3932545 = 2949409) B2949409
theorem B6545843 : Blo 1723062 6545843 := bstep (se 1 (by rfl) ⟨4909382, by rfl⟩ : syracuseStep 6545843 = 9818765) B9818765
theorem B7086539 : Blo 1723062 7086539 := bstep (se 1 (by rfl) ⟨5314904, by rfl⟩ : syracuseStep 7086539 = 10629809) B10629809
theorem B2908811 : Blo 1723062 2908811 := bstep (se 1 (by rfl) ⟨2181608, by rfl⟩ : syracuseStep 2908811 = 4363217) B4363217
theorem B2908939 : Blo 1723062 2908939 := bstep (se 1 (by rfl) ⟨2181704, by rfl⟩ : syracuseStep 2908939 = 4363409) B4363409
theorem B2909081 : Blo 1723062 2909081 := bstep (se 2 (by rfl) ⟨1090905, by rfl⟩ : syracuseStep 2909081 = 2181811) B2181811
theorem B2909209 : Blo 1723062 2909209 := bstep (se 2 (by rfl) ⟨1090953, by rfl⟩ : syracuseStep 2909209 = 2181907) B2181907
theorem B4908107 : Blo 1723062 4908107 := bstep (se 1 (by rfl) ⟨3681080, by rfl⟩ : syracuseStep 4908107 = 7362161) B7362161
theorem B5817419 : Blo 1723062 5817419 := bstep (se 1 (by rfl) ⟨4363064, by rfl⟩ : syracuseStep 5817419 = 8726129) B8726129
theorem B3105985 : Blo 1723062 3105985 := bstep (se 2 (by rfl) ⟨1164744, by rfl⟩ : syracuseStep 3105985 = 2329489) B2329489
theorem B8725805 : Blo 1723062 8725805 := bstep (se 3 (by rfl) ⟨1636088, by rfl⟩ : syracuseStep 8725805 = 3272177) B3272177
theorem B7365953 : Blo 1723062 7365953 := bstep (se 2 (by rfl) ⟨2762232, by rfl⟩ : syracuseStep 7365953 = 5524465) B5524465
theorem B5817689 : Blo 1723062 5817689 := bstep (se 2 (by rfl) ⟨2181633, by rfl⟩ : syracuseStep 5817689 = 4363267) B4363267
theorem B9823639 : Blo 1723062 9823639 := bstep (se 1 (by rfl) ⟨7367729, by rfl⟩ : syracuseStep 9823639 = 14735459) B14735459
theorem B3106201 : Blo 1723062 3106201 := bstep (se 2 (by rfl) ⟨1164825, by rfl⟩ : syracuseStep 3106201 = 2329651) B2329651
theorem B2909783 : Blo 1723062 2909783 := bstep (se 1 (by rfl) ⟨2182337, by rfl⟩ : syracuseStep 2909783 = 4364675) B4364675
theorem B7366295 : Blo 1723062 7366295 := bstep (se 1 (by rfl) ⟨5524721, by rfl⟩ : syracuseStep 7366295 = 11049443) B11049443
theorem B2909911 : Blo 1723062 2909911 := bstep (se 1 (by rfl) ⟨2182433, by rfl⟩ : syracuseStep 2909911 = 4364867) B4364867
theorem B3106583 : Blo 1723062 3106583 := bstep (se 1 (by rfl) ⟨2329937, by rfl⟩ : syracuseStep 3106583 = 4659875) B4659875
theorem B5523223 : Blo 1723062 5523223 := bstep (se 1 (by rfl) ⟨4142417, by rfl⟩ : syracuseStep 5523223 = 8284835) B8284835
theorem B5244695 : Blo 1723062 5244695 := bstep (se 1 (by rfl) ⟨3933521, by rfl⟩ : syracuseStep 5244695 = 7867043) B7867043
theorem B6547331 : Blo 1723062 6547331 := bstep (se 1 (by rfl) ⟨4910498, by rfl⟩ : syracuseStep 6547331 = 9820997) B9820997
theorem B3680243 : Blo 1723062 3680243 := bstep (se 1 (by rfl) ⟨2760182, by rfl⟩ : syracuseStep 3680243 = 5520365) B5520365
theorem B6989827 : Blo 1723062 6989827 := bstep (se 1 (by rfl) ⟨5242370, by rfl⟩ : syracuseStep 6989827 = 10484741) B10484741
theorem B5818391 : Blo 1723062 5818391 := bstep (se 1 (by rfl) ⟨4363793, by rfl⟩ : syracuseStep 5818391 = 8727587) B8727587
theorem B3876929 : Blo 1723062 3876929 := bstep (se 2 (by rfl) ⟨1453848, by rfl⟩ : syracuseStep 3876929 = 2907697) B2907697
theorem B1747019 : Blo 1723062 1747019 := bstep (se 1 (by rfl) ⟨1310264, by rfl⟩ : syracuseStep 1747019 = 2620529) B2620529
theorem B2181259 : Blo 1723062 2181259 := bstep (se 1 (by rfl) ⟨1635944, by rfl⟩ : syracuseStep 2181259 = 3271889) B3271889
theorem B35866775 : Blo 1723062 35866775 := bstep (se 1 (by rfl) ⟨26900081, by rfl⟩ : syracuseStep 35866775 = 53800163) B53800163
theorem B3877145 : Blo 1723062 3877145 := bstep (se 2 (by rfl) ⟨1453929, by rfl⟩ : syracuseStep 3877145 = 2907859) B2907859
theorem B6547787 : Blo 1723062 6547787 := bstep (se 1 (by rfl) ⟨4910840, by rfl⟩ : syracuseStep 6547787 = 9821681) B9821681
theorem B2910539 : Blo 1723062 2910539 := bstep (se 1 (by rfl) ⟨2182904, by rfl⟩ : syracuseStep 2910539 = 4365809) B4365809
theorem B4909405 : Blo 1723062 4909405 := bstep (se 3 (by rfl) ⟨920513, by rfl⟩ : syracuseStep 4909405 = 1841027) B1841027
theorem B3877235 : Blo 1723062 3877235 := bstep (se 1 (by rfl) ⟨2907926, by rfl⟩ : syracuseStep 3877235 = 5815853) B5815853
theorem B3877271 : Blo 1723062 3877271 := bstep (se 1 (by rfl) ⟨2907953, by rfl⟩ : syracuseStep 3877271 = 5815907) B5815907
theorem B16566707 : Blo 1723062 16566707 := bstep (se 1 (by rfl) ⟨12425030, by rfl⟩ : syracuseStep 16566707 = 24850061) B24850061
theorem B2910667 : Blo 1723062 2910667 := bstep (se 1 (by rfl) ⟨2183000, by rfl⟩ : syracuseStep 2910667 = 4366001) B4366001
theorem B13093325 : Blo 1723062 13093325 := bstep (se 3 (by rfl) ⟨2454998, by rfl⟩ : syracuseStep 13093325 = 4909997) B4909997
theorem B9316825 : Blo 1723062 9316825 := bstep (se 2 (by rfl) ⟨3493809, by rfl⟩ : syracuseStep 9316825 = 6987619) B6987619
theorem B3107339 : Blo 1723062 3107339 := bstep (se 1 (by rfl) ⟨2330504, by rfl⟩ : syracuseStep 3107339 = 4661009) B4661009
theorem B6547985 : Blo 1723062 6547985 := bstep (se 2 (by rfl) ⟨2455494, by rfl⟩ : syracuseStep 6547985 = 4910989) B4910989
theorem B5818931 : Blo 1723062 5818931 := bstep (se 1 (by rfl) ⟨4364198, by rfl⟩ : syracuseStep 5818931 = 8728397) B8728397
theorem B7367219 : Blo 1723062 7367219 := bstep (se 1 (by rfl) ⟨5525414, by rfl⟩ : syracuseStep 7367219 = 11050829) B11050829
theorem B3877451 : Blo 1723062 3877451 := bstep (se 1 (by rfl) ⟨2908088, by rfl⟩ : syracuseStep 3877451 = 5816177) B5816177
theorem B2910809 : Blo 1723062 2910809 := bstep (se 2 (by rfl) ⟨1091553, by rfl⟩ : syracuseStep 2910809 = 2183107) B2183107
theorem B3877505 : Blo 1723062 3877505 := bstep (se 2 (by rfl) ⟨1454064, by rfl⟩ : syracuseStep 3877505 = 2908129) B2908129
theorem B5900951 : Blo 1723062 5900951 := bstep (se 1 (by rfl) ⟨4425713, by rfl⟩ : syracuseStep 5900951 = 8851427) B8851427
theorem B4909747 : Blo 1723062 4909747 := bstep (se 1 (by rfl) ⟨3682310, by rfl⟩ : syracuseStep 4909747 = 7364621) B7364621
theorem B1723063 : Blo 1723062 1723063 := bstep (se 1 (by rfl) ⟨1292297, by rfl⟩ : syracuseStep 1723063 = 2584595) B2584595
theorem B1723083 : Blo 1723062 1723083 := bstep (se 1 (by rfl) ⟨1292312, by rfl⟩ : syracuseStep 1723083 = 2584625) B2584625
theorem B1723095 : Blo 1723062 1723095 := bstep (se 1 (by rfl) ⟨1292321, by rfl⟩ : syracuseStep 1723095 = 2584643) B2584643
theorem B2910937 : Blo 1723062 2910937 := bstep (se 2 (by rfl) ⟨1091601, by rfl⟩ : syracuseStep 2910937 = 2183203) B2183203
theorem B1723115 : Blo 1723062 1723115 := bstep (se 1 (by rfl) ⟨1292336, by rfl⟩ : syracuseStep 1723115 = 2584673) B2584673
theorem B1723127 : Blo 1723062 1723127 := bstep (se 1 (by rfl) ⟨1292345, by rfl⟩ : syracuseStep 1723127 = 2584691) B2584691
theorem B3107585 : Blo 1723062 3107585 := bstep (se 2 (by rfl) ⟨1165344, by rfl⟩ : syracuseStep 3107585 = 2330689) B2330689
theorem B1723147 : Blo 1723062 1723147 := bstep (se 1 (by rfl) ⟨1292360, by rfl⟩ : syracuseStep 1723147 = 2584721) B2584721
theorem B1723159 : Blo 1723062 1723159 := bstep (se 1 (by rfl) ⟨1292369, by rfl⟩ : syracuseStep 1723159 = 2584739) B2584739
theorem B1723179 : Blo 1723062 1723179 := bstep (se 1 (by rfl) ⟨1292384, by rfl⟩ : syracuseStep 1723179 = 2584769) B2584769
theorem B1723191 : Blo 1723062 1723191 := bstep (se 1 (by rfl) ⟨1292393, by rfl⟩ : syracuseStep 1723191 = 2584787) B2584787
theorem B5819201 : Blo 1723062 5819201 := bstep (se 2 (by rfl) ⟨2182200, by rfl⟩ : syracuseStep 5819201 = 4364401) B4364401
theorem B1723211 : Blo 1723062 1723211 := bstep (se 1 (by rfl) ⟨1292408, by rfl⟩ : syracuseStep 1723211 = 2584817) B2584817
theorem B1723223 : Blo 1723062 1723223 := bstep (se 1 (by rfl) ⟨1292417, by rfl⟩ : syracuseStep 1723223 = 2584835) B2584835
theorem B3877721 : Blo 1723062 3877721 := bstep (se 2 (by rfl) ⟨1454145, by rfl⟩ : syracuseStep 3877721 = 2908291) B2908291
theorem B1723243 : Blo 1723062 1723243 := bstep (se 1 (by rfl) ⟨1292432, by rfl⟩ : syracuseStep 1723243 = 2584865) B2584865
theorem B1723255 : Blo 1723062 1723255 := bstep (se 1 (by rfl) ⟨1292441, by rfl⟩ : syracuseStep 1723255 = 2584883) B2584883
theorem B1723275 : Blo 1723062 1723275 := bstep (se 1 (by rfl) ⟨1292456, by rfl⟩ : syracuseStep 1723275 = 2584913) B2584913
theorem B1723287 : Blo 1723062 1723287 := bstep (se 1 (by rfl) ⟨1292465, by rfl⟩ : syracuseStep 1723287 = 2584931) B2584931
theorem B1723307 : Blo 1723062 1723307 := bstep (se 1 (by rfl) ⟨1292480, by rfl⟩ : syracuseStep 1723307 = 2584961) B2584961
theorem B3877811 : Blo 1723062 3877811 := bstep (se 1 (by rfl) ⟨2908358, by rfl⟩ : syracuseStep 3877811 = 5816717) B5816717
theorem B13093811 : Blo 1723062 13093811 := bstep (se 1 (by rfl) ⟨9820358, by rfl⟩ : syracuseStep 13093811 = 19640717) B19640717
theorem B1723319 : Blo 1723062 1723319 := bstep (se 1 (by rfl) ⟨1292489, by rfl⟩ : syracuseStep 1723319 = 2584979) B2584979
theorem B3681217 : Blo 1723062 3681217 := bstep (se 2 (by rfl) ⟨1380456, by rfl⟩ : syracuseStep 3681217 = 2760913) B2760913
theorem B1723339 : Blo 1723062 1723339 := bstep (se 1 (by rfl) ⟨1292504, by rfl⟩ : syracuseStep 1723339 = 2585009) B2585009
theorem B1723351 : Blo 1723062 1723351 := bstep (se 1 (by rfl) ⟨1292513, by rfl⟩ : syracuseStep 1723351 = 2585027) B2585027
theorem B3877847 : Blo 1723062 3877847 := bstep (se 1 (by rfl) ⟨2908385, by rfl⟩ : syracuseStep 3877847 = 5816771) B5816771
theorem B3107801 : Blo 1723062 3107801 := bstep (se 2 (by rfl) ⟨1165425, by rfl⟩ : syracuseStep 3107801 = 2330851) B2330851
theorem B1723371 : Blo 1723062 1723371 := bstep (se 1 (by rfl) ⟨1292528, by rfl⟩ : syracuseStep 1723371 = 2585057) B2585057
theorem B1723383 : Blo 1723062 1723383 := bstep (se 1 (by rfl) ⟨1292537, by rfl⟩ : syracuseStep 1723383 = 2585075) B2585075
theorem B3271691 : Blo 1723062 3271691 := bstep (se 1 (by rfl) ⟨2453768, by rfl⟩ : syracuseStep 3271691 = 4907537) B4907537
theorem B1723403 : Blo 1723062 1723403 := bstep (se 1 (by rfl) ⟨1292552, by rfl⟩ : syracuseStep 1723403 = 2585105) B2585105
theorem B1723415 : Blo 1723062 1723415 := bstep (se 1 (by rfl) ⟨1292561, by rfl⟩ : syracuseStep 1723415 = 2585123) B2585123
theorem B1723435 : Blo 1723062 1723435 := bstep (se 1 (by rfl) ⟨1292576, by rfl⟩ : syracuseStep 1723435 = 2585153) B2585153
theorem B1723447 : Blo 1723062 1723447 := bstep (se 1 (by rfl) ⟨1292585, by rfl⟩ : syracuseStep 1723447 = 2585171) B2585171
theorem B3271745 : Blo 1723062 3271745 := bstep (se 2 (by rfl) ⟨1226904, by rfl⟩ : syracuseStep 3271745 = 2453809) B2453809
theorem B1723467 : Blo 1723062 1723467 := bstep (se 1 (by rfl) ⟨1292600, by rfl⟩ : syracuseStep 1723467 = 2585201) B2585201
theorem B1723479 : Blo 1723062 1723479 := bstep (se 1 (by rfl) ⟨1292609, by rfl⟩ : syracuseStep 1723479 = 2585219) B2585219
theorem B2182231 : Blo 1723062 2182231 := bstep (se 1 (by rfl) ⟨1636673, by rfl⟩ : syracuseStep 2182231 = 3273347) B3273347
theorem B3542105 : Blo 1723062 3542105 := bstep (se 2 (by rfl) ⟨1328289, by rfl⟩ : syracuseStep 3542105 = 2656579) B2656579
theorem B1723499 : Blo 1723062 1723499 := bstep (se 1 (by rfl) ⟨1292624, by rfl⟩ : syracuseStep 1723499 = 2585249) B2585249
theorem B1723511 : Blo 1723062 1723511 := bstep (se 1 (by rfl) ⟨1292633, by rfl⟩ : syracuseStep 1723511 = 2585267) B2585267
theorem B1723531 : Blo 1723062 1723531 := bstep (se 1 (by rfl) ⟨1292648, by rfl⟩ : syracuseStep 1723531 = 2585297) B2585297
theorem B3878027 : Blo 1723062 3878027 := bstep (se 1 (by rfl) ⟨2908520, by rfl⟩ : syracuseStep 3878027 = 5817041) B5817041
theorem B1723543 : Blo 1723062 1723543 := bstep (se 1 (by rfl) ⟨1292657, by rfl⟩ : syracuseStep 1723543 = 2585315) B2585315
theorem B1723563 : Blo 1723062 1723563 := bstep (se 1 (by rfl) ⟨1292672, by rfl⟩ : syracuseStep 1723563 = 2585345) B2585345
theorem B12422321 : Blo 1723062 12422321 := bstep (se 2 (by rfl) ⟨4658370, by rfl⟩ : syracuseStep 12422321 = 9316741) B9316741
theorem B1723575 : Blo 1723062 1723575 := bstep (se 1 (by rfl) ⟨1292681, by rfl⟩ : syracuseStep 1723575 = 2585363) B2585363
theorem B3878081 : Blo 1723062 3878081 := bstep (se 2 (by rfl) ⟨1454280, by rfl⟩ : syracuseStep 3878081 = 2908561) B2908561
theorem B1723595 : Blo 1723062 1723595 := bstep (se 1 (by rfl) ⟨1292696, by rfl⟩ : syracuseStep 1723595 = 2585393) B2585393
theorem B204238037 : Blo 1723062 204238037 := bstep (se 7 (by rfl) ⟨2393414, by rfl⟩ : syracuseStep 204238037 = 4786829) B4786829
theorem B1723607 : Blo 1723062 1723607 := bstep (se 1 (by rfl) ⟨1292705, by rfl⟩ : syracuseStep 1723607 = 2585411) B2585411
theorem B3837143 : Blo 1723062 3837143 := bstep (se 1 (by rfl) ⟨2877857, by rfl⟩ : syracuseStep 3837143 = 5755715) B5755715
theorem B1723627 : Blo 1723062 1723627 := bstep (se 1 (by rfl) ⟨1292720, by rfl⟩ : syracuseStep 1723627 = 2585441) B2585441
theorem B1723639 : Blo 1723062 1723639 := bstep (se 1 (by rfl) ⟨1292729, by rfl⟩ : syracuseStep 1723639 = 2585459) B2585459
theorem B1723659 : Blo 1723062 1723659 := bstep (se 1 (by rfl) ⟨1292744, by rfl⟩ : syracuseStep 1723659 = 2585489) B2585489
theorem B1723671 : Blo 1723062 1723671 := bstep (se 1 (by rfl) ⟨1292753, by rfl⟩ : syracuseStep 1723671 = 2585507) B2585507
theorem B6548759 : Blo 1723062 6548759 := bstep (se 1 (by rfl) ⟨4911569, by rfl⟩ : syracuseStep 6548759 = 9823139) B9823139
theorem B1723691 : Blo 1723062 1723691 := bstep (se 1 (by rfl) ⟨1292768, by rfl⟩ : syracuseStep 1723691 = 2585537) B2585537
theorem B1723703 : Blo 1723062 1723703 := bstep (se 1 (by rfl) ⟨1292777, by rfl⟩ : syracuseStep 1723703 = 2585555) B2585555
theorem B1723723 : Blo 1723062 1723723 := bstep (se 1 (by rfl) ⟨1292792, by rfl⟩ : syracuseStep 1723723 = 2585585) B2585585
theorem B1723735 : Blo 1723062 1723735 := bstep (se 1 (by rfl) ⟨1292801, by rfl⟩ : syracuseStep 1723735 = 2585603) B2585603
theorem B5819741 : Blo 1723062 5819741 := bstep (se 3 (by rfl) ⟨1091201, by rfl⟩ : syracuseStep 5819741 = 2182403) B2182403
theorem B1723755 : Blo 1723062 1723755 := bstep (se 1 (by rfl) ⟨1292816, by rfl⟩ : syracuseStep 1723755 = 2585633) B2585633
theorem B1723767 : Blo 1723062 1723767 := bstep (se 1 (by rfl) ⟨1292825, by rfl⟩ : syracuseStep 1723767 = 2585651) B2585651
theorem B1723787 : Blo 1723062 1723787 := bstep (se 1 (by rfl) ⟨1292840, by rfl⟩ : syracuseStep 1723787 = 2585681) B2585681
theorem B1723799 : Blo 1723062 1723799 := bstep (se 1 (by rfl) ⟨1292849, by rfl⟩ : syracuseStep 1723799 = 2585699) B2585699
theorem B3878297 : Blo 1723062 3878297 := bstep (se 2 (by rfl) ⟨1454361, by rfl⟩ : syracuseStep 3878297 = 2908723) B2908723
theorem B1723819 : Blo 1723062 1723819 := bstep (se 1 (by rfl) ⟨1292864, by rfl⟩ : syracuseStep 1723819 = 2585729) B2585729
theorem B4140467 : Blo 1723062 4140467 := bstep (se 1 (by rfl) ⟨3105350, by rfl⟩ : syracuseStep 4140467 = 6210701) B6210701
theorem B1723831 : Blo 1723062 1723831 := bstep (se 1 (by rfl) ⟨1292873, by rfl⟩ : syracuseStep 1723831 = 2585747) B2585747
theorem B1723851 : Blo 1723062 1723851 := bstep (se 1 (by rfl) ⟨1292888, by rfl⟩ : syracuseStep 1723851 = 2585777) B2585777
theorem B1723863 : Blo 1723062 1723863 := bstep (se 1 (by rfl) ⟨1292897, by rfl⟩ : syracuseStep 1723863 = 2585795) B2585795
theorem B6548957 : Blo 1723062 6548957 := bstep (se 3 (by rfl) ⟨1227929, by rfl⟩ : syracuseStep 6548957 = 2455859) B2455859
theorem B1723883 : Blo 1723062 1723883 := bstep (se 1 (by rfl) ⟨1292912, by rfl⟩ : syracuseStep 1723883 = 2585825) B2585825
theorem B3878387 : Blo 1723062 3878387 := bstep (se 1 (by rfl) ⟨2908790, by rfl⟩ : syracuseStep 3878387 = 5817581) B5817581
theorem B1723895 : Blo 1723062 1723895 := bstep (se 1 (by rfl) ⟨1292921, by rfl⟩ : syracuseStep 1723895 = 2585843) B2585843
theorem B1723915 : Blo 1723062 1723915 := bstep (se 1 (by rfl) ⟨1292936, by rfl⟩ : syracuseStep 1723915 = 2585873) B2585873
theorem B7368209 : Blo 1723062 7368209 := bstep (se 2 (by rfl) ⟨2763078, by rfl⟩ : syracuseStep 7368209 = 5526157) B5526157
theorem B3878423 : Blo 1723062 3878423 := bstep (se 1 (by rfl) ⟨2908817, by rfl⟩ : syracuseStep 3878423 = 5817635) B5817635
theorem B1723927 : Blo 1723062 1723927 := bstep (se 1 (by rfl) ⟨1292945, by rfl⟩ : syracuseStep 1723927 = 2585891) B2585891
theorem B1723947 : Blo 1723062 1723947 := bstep (se 1 (by rfl) ⟨1292960, by rfl⟩ : syracuseStep 1723947 = 2585921) B2585921
theorem B1723959 : Blo 1723062 1723959 := bstep (se 1 (by rfl) ⟨1292969, by rfl⟩ : syracuseStep 1723959 = 2585939) B2585939
theorem B7360075 : Blo 1723062 7360075 := bstep (se 1 (by rfl) ⟨5520056, by rfl⟩ : syracuseStep 7360075 = 11040113) B11040113
theorem B4976203 : Blo 1723062 4976203 := bstep (se 1 (by rfl) ⟨3732152, by rfl⟩ : syracuseStep 4976203 = 7464305) B7464305
theorem B1723979 : Blo 1723062 1723979 := bstep (se 1 (by rfl) ⟨1292984, by rfl⟩ : syracuseStep 1723979 = 2585969) B2585969
theorem B1723991 : Blo 1723062 1723991 := bstep (se 1 (by rfl) ⟨1292993, by rfl⟩ : syracuseStep 1723991 = 2585987) B2585987
theorem B4910681 : Blo 1723062 4910681 := bstep (se 2 (by rfl) ⟨1841505, by rfl⟩ : syracuseStep 4910681 = 3683011) B3683011
theorem B5525081 : Blo 1723062 5525081 := bstep (se 2 (by rfl) ⟨2071905, by rfl⟩ : syracuseStep 5525081 = 4143811) B4143811
theorem B1724011 : Blo 1723062 1724011 := bstep (se 1 (by rfl) ⟨1293008, by rfl⟩ : syracuseStep 1724011 = 2586017) B2586017
theorem B1724023 : Blo 1723062 1724023 := bstep (se 1 (by rfl) ⟨1293017, by rfl⟩ : syracuseStep 1724023 = 2586035) B2586035
theorem B33590915 : Blo 1723062 33590915 := bstep (se 1 (by rfl) ⟨25193186, by rfl⟩ : syracuseStep 33590915 = 50386373) B50386373
theorem B1724043 : Blo 1723062 1724043 := bstep (se 1 (by rfl) ⟨1293032, by rfl⟩ : syracuseStep 1724043 = 2586065) B2586065
theorem B7360145 : Blo 1723062 7360145 := bstep (se 2 (by rfl) ⟨2760054, by rfl⟩ : syracuseStep 7360145 = 5520109) B5520109
theorem B1724055 : Blo 1723062 1724055 := bstep (se 1 (by rfl) ⟨1293041, by rfl⟩ : syracuseStep 1724055 = 2586083) B2586083
theorem B1724075 : Blo 1723062 1724075 := bstep (se 1 (by rfl) ⟨1293056, by rfl⟩ : syracuseStep 1724075 = 2586113) B2586113
theorem B13987505 : Blo 1723062 13987505 := bstep (se 2 (by rfl) ⟨5245314, by rfl⟩ : syracuseStep 13987505 = 10490629) B10490629
theorem B7859891 : Blo 1723062 7859891 := bstep (se 1 (by rfl) ⟨5894918, by rfl⟩ : syracuseStep 7859891 = 11789837) B11789837
theorem B8842931 : Blo 1723062 8842931 := bstep (se 1 (by rfl) ⟨6632198, by rfl⟩ : syracuseStep 8842931 = 13264397) B13264397
theorem B1724087 : Blo 1723062 1724087 := bstep (se 1 (by rfl) ⟨1293065, by rfl⟩ : syracuseStep 1724087 = 2586131) B2586131
theorem B4361921 : Blo 1723062 4361921 := bstep (se 2 (by rfl) ⟨1635720, by rfl⟩ : syracuseStep 4361921 = 3271441) B3271441
theorem B3878603 : Blo 1723062 3878603 := bstep (se 1 (by rfl) ⟨2908952, by rfl⟩ : syracuseStep 3878603 = 5817905) B5817905
theorem B1724107 : Blo 1723062 1724107 := bstep (se 1 (by rfl) ⟨1293080, by rfl⟩ : syracuseStep 1724107 = 2586161) B2586161
theorem B1724119 : Blo 1723062 1724119 := bstep (se 1 (by rfl) ⟨1293089, by rfl⟩ : syracuseStep 1724119 = 2586179) B2586179
theorem B6295261 : Blo 1723062 6295261 := bstep (se 3 (by rfl) ⟨1180361, by rfl⟩ : syracuseStep 6295261 = 2360723) B2360723
theorem B1724139 : Blo 1723062 1724139 := bstep (se 1 (by rfl) ⟨1293104, by rfl⟩ : syracuseStep 1724139 = 2586209) B2586209
theorem B1724151 : Blo 1723062 1724151 := bstep (se 1 (by rfl) ⟨1293113, by rfl⟩ : syracuseStep 1724151 = 2586227) B2586227
theorem B3878657 : Blo 1723062 3878657 := bstep (se 2 (by rfl) ⟨1454496, by rfl⟩ : syracuseStep 3878657 = 2908993) B2908993
theorem B1724171 : Blo 1723062 1724171 := bstep (se 1 (by rfl) ⟨1293128, by rfl⟩ : syracuseStep 1724171 = 2586257) B2586257
theorem B1724183 : Blo 1723062 1724183 := bstep (se 1 (by rfl) ⟨1293137, by rfl⟩ : syracuseStep 1724183 = 2586275) B2586275
theorem B1724203 : Blo 1723062 1724203 := bstep (se 1 (by rfl) ⟨1293152, by rfl⟩ : syracuseStep 1724203 = 2586305) B2586305
theorem B1724215 : Blo 1723062 1724215 := bstep (se 1 (by rfl) ⟨1293161, by rfl⟩ : syracuseStep 1724215 = 2586323) B2586323
theorem B1724235 : Blo 1723062 1724235 := bstep (se 1 (by rfl) ⟨1293176, by rfl⟩ : syracuseStep 1724235 = 2586353) B2586353
theorem B1724247 : Blo 1723062 1724247 := bstep (se 1 (by rfl) ⟨1293185, by rfl⟩ : syracuseStep 1724247 = 2586371) B2586371
theorem B16568165 : Blo 1723062 16568165 := bstep (se 4 (by rfl) ⟨1553265, by rfl⟩ : syracuseStep 16568165 = 3106531) B3106531
theorem B1724267 : Blo 1723062 1724267 := bstep (se 1 (by rfl) ⟨1293200, by rfl⟩ : syracuseStep 1724267 = 2586401) B2586401
theorem B1724279 : Blo 1723062 1724279 := bstep (se 1 (by rfl) ⟨1293209, by rfl⟩ : syracuseStep 1724279 = 2586419) B2586419
theorem B8286083 : Blo 1723062 8286083 := bstep (se 1 (by rfl) ⟨6214562, by rfl⟩ : syracuseStep 8286083 = 12429125) B12429125
theorem B1724299 : Blo 1723062 1724299 := bstep (se 1 (by rfl) ⟨1293224, by rfl⟩ : syracuseStep 1724299 = 2586449) B2586449
theorem B2183051 : Blo 1723062 2183051 := bstep (se 1 (by rfl) ⟨1637288, by rfl⟩ : syracuseStep 2183051 = 3274577) B3274577
theorem B1724311 : Blo 1723062 1724311 := bstep (se 1 (by rfl) ⟨1293233, by rfl⟩ : syracuseStep 1724311 = 2586467) B2586467
theorem B1724331 : Blo 1723062 1724331 := bstep (se 1 (by rfl) ⟨1293248, by rfl⟩ : syracuseStep 1724331 = 2586497) B2586497
theorem B16797617 : Blo 1723062 16797617 := bstep (se 2 (by rfl) ⟨6299106, by rfl⟩ : syracuseStep 16797617 = 12598213) B12598213
theorem B99438515 : Blo 1723062 99438515 := bstep (se 1 (by rfl) ⟨74578886, by rfl⟩ : syracuseStep 99438515 = 149157773) B149157773
theorem B1724343 : Blo 1723062 1724343 := bstep (se 1 (by rfl) ⟨1293257, by rfl⟩ : syracuseStep 1724343 = 2586515) B2586515
theorem B1724363 : Blo 1723062 1724363 := bstep (se 1 (by rfl) ⟨1293272, by rfl⟩ : syracuseStep 1724363 = 2586545) B2586545
theorem B3272663 : Blo 1723062 3272663 := bstep (se 1 (by rfl) ⟨2454497, by rfl⟩ : syracuseStep 3272663 = 4908995) B4908995
theorem B1724375 : Blo 1723062 1724375 := bstep (se 1 (by rfl) ⟨1293281, by rfl⟩ : syracuseStep 1724375 = 2586563) B2586563
theorem B3878873 : Blo 1723062 3878873 := bstep (se 2 (by rfl) ⟨1454577, by rfl⟩ : syracuseStep 3878873 = 2909155) B2909155
theorem B1724395 : Blo 1723062 1724395 := bstep (se 1 (by rfl) ⟨1293296, by rfl⟩ : syracuseStep 1724395 = 2586593) B2586593
theorem B1724407 : Blo 1723062 1724407 := bstep (se 1 (by rfl) ⟨1293305, by rfl⟩ : syracuseStep 1724407 = 2586611) B2586611
theorem B1724427 : Blo 1723062 1724427 := bstep (se 1 (by rfl) ⟨1293320, by rfl⟩ : syracuseStep 1724427 = 2586641) B2586641
theorem B1724439 : Blo 1723062 1724439 := bstep (se 1 (by rfl) ⟨1293329, by rfl⟩ : syracuseStep 1724439 = 2586659) B2586659
theorem B2584601 : Blo 1723062 2584601 := bstep (se 2 (by rfl) ⟨969225, by rfl⟩ : syracuseStep 2584601 = 1938451) B1938451
theorem B1724459 : Blo 1723062 1724459 := bstep (se 1 (by rfl) ⟨1293344, by rfl⟩ : syracuseStep 1724459 = 2586689) B2586689
theorem B3878963 : Blo 1723062 3878963 := bstep (se 1 (by rfl) ⟨2909222, by rfl⟩ : syracuseStep 3878963 = 5818445) B5818445
theorem B1724471 : Blo 1723062 1724471 := bstep (se 1 (by rfl) ⟨1293353, by rfl⟩ : syracuseStep 1724471 = 2586707) B2586707
theorem B1724491 : Blo 1723062 1724491 := bstep (se 1 (by rfl) ⟨1293368, by rfl⟩ : syracuseStep 1724491 = 2586737) B2586737
theorem B3878999 : Blo 1723062 3878999 := bstep (se 1 (by rfl) ⟨2909249, by rfl⟩ : syracuseStep 3878999 = 5818499) B5818499
theorem B1724503 : Blo 1723062 1724503 := bstep (se 1 (by rfl) ⟨1293377, by rfl⟩ : syracuseStep 1724503 = 2586755) B2586755
theorem B1724523 : Blo 1723062 1724523 := bstep (se 1 (by rfl) ⟨1293392, by rfl⟩ : syracuseStep 1724523 = 2586785) B2586785
theorem B1724535 : Blo 1723062 1724535 := bstep (se 1 (by rfl) ⟨1293401, by rfl⟩ : syracuseStep 1724535 = 2586803) B2586803
theorem B2584715 : Blo 1723062 2584715 := bstep (se 1 (by rfl) ⟨1938536, by rfl⟩ : syracuseStep 2584715 = 3877073) B3877073
theorem B1724555 : Blo 1723062 1724555 := bstep (se 1 (by rfl) ⟨1293416, by rfl⟩ : syracuseStep 1724555 = 2586833) B2586833
theorem B2584727 : Blo 1723062 2584727 := bstep (se 1 (by rfl) ⟨1938545, by rfl⟩ : syracuseStep 2584727 = 3877091) B3877091
theorem B1724567 : Blo 1723062 1724567 := bstep (se 1 (by rfl) ⟨1293425, by rfl⟩ : syracuseStep 1724567 = 2586851) B2586851
theorem B1724587 : Blo 1723062 1724587 := bstep (se 1 (by rfl) ⟨1293440, by rfl⟩ : syracuseStep 1724587 = 2586881) B2586881
theorem B1724599 : Blo 1723062 1724599 := bstep (se 1 (by rfl) ⟨1293449, by rfl⟩ : syracuseStep 1724599 = 2586899) B2586899
theorem B1724619 : Blo 1723062 1724619 := bstep (se 1 (by rfl) ⟨1293464, by rfl⟩ : syracuseStep 1724619 = 2586929) B2586929
theorem B1724631 : Blo 1723062 1724631 := bstep (se 1 (by rfl) ⟨1293473, by rfl⟩ : syracuseStep 1724631 = 2586947) B2586947
theorem B2584793 : Blo 1723062 2584793 := bstep (se 2 (by rfl) ⟨969297, by rfl⟩ : syracuseStep 2584793 = 1938595) B1938595
theorem B4362457 : Blo 1723062 4362457 := bstep (se 2 (by rfl) ⟨1635921, by rfl⟩ : syracuseStep 4362457 = 3271843) B3271843
theorem B4141273 : Blo 1723062 4141273 := bstep (se 2 (by rfl) ⟨1552977, by rfl⟩ : syracuseStep 4141273 = 3105955) B3105955
theorem B1724651 : Blo 1723062 1724651 := bstep (se 1 (by rfl) ⟨1293488, by rfl⟩ : syracuseStep 1724651 = 2586977) B2586977
theorem B1724663 : Blo 1723062 1724663 := bstep (se 1 (by rfl) ⟨1293497, by rfl⟩ : syracuseStep 1724663 = 2586995) B2586995
theorem B3879179 : Blo 1723062 3879179 := bstep (se 1 (by rfl) ⟨2909384, by rfl⟩ : syracuseStep 3879179 = 5818769) B5818769
theorem B1724683 : Blo 1723062 1724683 := bstep (se 1 (by rfl) ⟨1293512, by rfl⟩ : syracuseStep 1724683 = 2587025) B2587025
theorem B1724695 : Blo 1723062 1724695 := bstep (se 1 (by rfl) ⟨1293521, by rfl⟩ : syracuseStep 1724695 = 2587043) B2587043
theorem B1724715 : Blo 1723062 1724715 := bstep (se 1 (by rfl) ⟨1293536, by rfl⟩ : syracuseStep 1724715 = 2587073) B2587073
theorem B1724727 : Blo 1723062 1724727 := bstep (se 1 (by rfl) ⟨1293545, by rfl⟩ : syracuseStep 1724727 = 2587091) B2587091
theorem B3879233 : Blo 1723062 3879233 := bstep (se 2 (by rfl) ⟨1454712, by rfl⟩ : syracuseStep 3879233 = 2909425) B2909425
theorem B2584907 : Blo 1723062 2584907 := bstep (se 1 (by rfl) ⟨1938680, by rfl⟩ : syracuseStep 2584907 = 3877361) B3877361
theorem B1724747 : Blo 1723062 1724747 := bstep (se 1 (by rfl) ⟨1293560, by rfl⟩ : syracuseStep 1724747 = 2587121) B2587121
theorem B2584919 : Blo 1723062 2584919 := bstep (se 1 (by rfl) ⟨1938689, by rfl⟩ : syracuseStep 2584919 = 3877379) B3877379
theorem B1724759 : Blo 1723062 1724759 := bstep (se 1 (by rfl) ⟨1293569, by rfl⟩ : syracuseStep 1724759 = 2587139) B2587139
theorem B13095269 : Blo 1723062 13095269 := bstep (se 4 (by rfl) ⟨1227681, by rfl⟩ : syracuseStep 13095269 = 2455363) B2455363
theorem B1724779 : Blo 1723062 1724779 := bstep (se 1 (by rfl) ⟨1293584, by rfl⟩ : syracuseStep 1724779 = 2587169) B2587169
theorem B1724791 : Blo 1723062 1724791 := bstep (se 1 (by rfl) ⟨1293593, by rfl⟩ : syracuseStep 1724791 = 2587187) B2587187
theorem B1724811 : Blo 1723062 1724811 := bstep (se 1 (by rfl) ⟨1293608, by rfl⟩ : syracuseStep 1724811 = 2587217) B2587217
theorem B1724823 : Blo 1723062 1724823 := bstep (se 1 (by rfl) ⟨1293617, by rfl⟩ : syracuseStep 1724823 = 2587235) B2587235
theorem B2584985 : Blo 1723062 2584985 := bstep (se 2 (by rfl) ⟨969369, by rfl⟩ : syracuseStep 2584985 = 1938739) B1938739
theorem B1724843 : Blo 1723062 1724843 := bstep (se 1 (by rfl) ⟨1293632, by rfl⟩ : syracuseStep 1724843 = 2587265) B2587265
theorem B1724855 : Blo 1723062 1724855 := bstep (se 1 (by rfl) ⟨1293641, by rfl⟩ : syracuseStep 1724855 = 2587283) B2587283
theorem B5820875 : Blo 1723062 5820875 := bstep (se 1 (by rfl) ⟨4365656, by rfl⟩ : syracuseStep 5820875 = 8731313) B8731313
theorem B1724875 : Blo 1723062 1724875 := bstep (se 1 (by rfl) ⟨1293656, by rfl⟩ : syracuseStep 1724875 = 2587313) B2587313
theorem B1724887 : Blo 1723062 1724887 := bstep (se 1 (by rfl) ⟨1293665, by rfl⟩ : syracuseStep 1724887 = 2587331) B2587331
theorem B1724907 : Blo 1723062 1724907 := bstep (se 1 (by rfl) ⟨1293680, by rfl⟩ : syracuseStep 1724907 = 2587361) B2587361
theorem B3494387 : Blo 1723062 3494387 := bstep (se 1 (by rfl) ⟨2620790, by rfl⟩ : syracuseStep 3494387 = 5241581) B5241581
theorem B3273203 : Blo 1723062 3273203 := bstep (se 1 (by rfl) ⟨2454902, by rfl⟩ : syracuseStep 3273203 = 4909805) B4909805
theorem B1724919 : Blo 1723062 1724919 := bstep (se 1 (by rfl) ⟨1293689, by rfl⟩ : syracuseStep 1724919 = 2587379) B2587379
theorem B2585099 : Blo 1723062 2585099 := bstep (se 1 (by rfl) ⟨1938824, by rfl⟩ : syracuseStep 2585099 = 3877649) B3877649
theorem B1724939 : Blo 1723062 1724939 := bstep (se 1 (by rfl) ⟨1293704, by rfl⟩ : syracuseStep 1724939 = 2587409) B2587409
theorem B2585111 : Blo 1723062 2585111 := bstep (se 1 (by rfl) ⟨1938833, by rfl⟩ : syracuseStep 2585111 = 3877667) B3877667
theorem B1724951 : Blo 1723062 1724951 := bstep (se 1 (by rfl) ⟨1293713, by rfl⟩ : syracuseStep 1724951 = 2587427) B2587427
theorem B3879449 : Blo 1723062 3879449 := bstep (se 2 (by rfl) ⟨1454793, by rfl⟩ : syracuseStep 3879449 = 2909587) B2909587
theorem B1724971 : Blo 1723062 1724971 := bstep (se 1 (by rfl) ⟨1293728, by rfl⟩ : syracuseStep 1724971 = 2587457) B2587457
theorem B1724983 : Blo 1723062 1724983 := bstep (se 1 (by rfl) ⟨1293737, by rfl⟩ : syracuseStep 1724983 = 2587475) B2587475
theorem B1725003 : Blo 1723062 1725003 := bstep (se 1 (by rfl) ⟨1293752, by rfl⟩ : syracuseStep 1725003 = 2587505) B2587505
theorem B1725015 : Blo 1723062 1725015 := bstep (se 1 (by rfl) ⟨1293761, by rfl⟩ : syracuseStep 1725015 = 2587523) B2587523
theorem B2585177 : Blo 1723062 2585177 := bstep (se 2 (by rfl) ⟨969441, by rfl⟩ : syracuseStep 2585177 = 1938883) B1938883
theorem B1725035 : Blo 1723062 1725035 := bstep (se 1 (by rfl) ⟨1293776, by rfl⟩ : syracuseStep 1725035 = 2587553) B2587553
theorem B3879539 : Blo 1723062 3879539 := bstep (se 1 (by rfl) ⟨2909654, by rfl⟩ : syracuseStep 3879539 = 5819309) B5819309
theorem B1725047 : Blo 1723062 1725047 := bstep (se 1 (by rfl) ⟨1293785, by rfl⟩ : syracuseStep 1725047 = 2587571) B2587571
theorem B3879575 : Blo 1723062 3879575 := bstep (se 1 (by rfl) ⟨2909681, by rfl⟩ : syracuseStep 3879575 = 5819363) B5819363
theorem B5894849 : Blo 1723062 5894849 := bstep (se 2 (by rfl) ⟨2210568, by rfl⟩ : syracuseStep 5894849 = 4421137) B4421137
theorem B2585291 : Blo 1723062 2585291 := bstep (se 1 (by rfl) ⟨1938968, by rfl⟩ : syracuseStep 2585291 = 3877937) B3877937
theorem B2585303 : Blo 1723062 2585303 := bstep (se 1 (by rfl) ⟨1938977, by rfl⟩ : syracuseStep 2585303 = 3877955) B3877955
theorem B5821145 : Blo 1723062 5821145 := bstep (se 2 (by rfl) ⟨2182929, by rfl⟩ : syracuseStep 5821145 = 4365859) B4365859
theorem B13087493 : Blo 1723062 13087493 := bstep (se 4 (by rfl) ⟨1226952, by rfl⟩ : syracuseStep 13087493 = 2453905) B2453905
theorem B2585369 : Blo 1723062 2585369 := bstep (se 2 (by rfl) ⟨969513, by rfl⟩ : syracuseStep 2585369 = 1939027) B1939027
theorem B3879755 : Blo 1723062 3879755 := bstep (se 1 (by rfl) ⟨2909816, by rfl⟩ : syracuseStep 3879755 = 5819633) B5819633
theorem B13095755 : Blo 1723062 13095755 := bstep (se 1 (by rfl) ⟨9821816, by rfl⟩ : syracuseStep 13095755 = 19643633) B19643633
theorem B3879809 : Blo 1723062 3879809 := bstep (se 2 (by rfl) ⟨1454928, by rfl⟩ : syracuseStep 3879809 = 2909857) B2909857
theorem B2585483 : Blo 1723062 2585483 := bstep (se 1 (by rfl) ⟨1939112, by rfl⟩ : syracuseStep 2585483 = 3878225) B3878225
theorem B2585495 : Blo 1723062 2585495 := bstep (se 1 (by rfl) ⟨1939121, by rfl⟩ : syracuseStep 2585495 = 3878243) B3878243
theorem B2454475 : Blo 1723062 2454475 := bstep (se 1 (by rfl) ⟨1840856, by rfl⟩ : syracuseStep 2454475 = 3681713) B3681713
theorem B2585561 : Blo 1723062 2585561 := bstep (se 2 (by rfl) ⟨969585, by rfl⟩ : syracuseStep 2585561 = 1939171) B1939171
theorem B3273689 : Blo 1723062 3273689 := bstep (se 2 (by rfl) ⟨1227633, by rfl⟩ : syracuseStep 3273689 = 2455267) B2455267
theorem B4912093 : Blo 1723062 4912093 := bstep (se 3 (by rfl) ⟨921017, by rfl⟩ : syracuseStep 4912093 = 1842035) B1842035
theorem B1089483797 : Blo 1723062 1089483797 := bstep (se 6 (by rfl) ⟨25534776, by rfl⟩ : syracuseStep 1089483797 = 51069553) B51069553
theorem B3683353 : Blo 1723062 3683353 := bstep (se 2 (by rfl) ⟨1381257, by rfl⟩ : syracuseStep 3683353 = 2762515) B2762515
theorem B1938487 : Blo 1723062 1938487 := bstep (se 1 (by rfl) ⟨1453865, by rfl⟩ : syracuseStep 1938487 = 2907731) B2907731
theorem B2585675 : Blo 1723062 2585675 := bstep (se 1 (by rfl) ⟨1939256, by rfl⟩ : syracuseStep 2585675 = 3878513) B3878513
theorem B2585687 : Blo 1723062 2585687 := bstep (se 1 (by rfl) ⟨1939265, by rfl⟩ : syracuseStep 2585687 = 3878531) B3878531
theorem B3880025 : Blo 1723062 3880025 := bstep (se 2 (by rfl) ⟨1455009, by rfl⟩ : syracuseStep 3880025 = 2910019) B2910019
theorem B8729693 : Blo 1723062 8729693 := bstep (se 3 (by rfl) ⟨1636817, by rfl⟩ : syracuseStep 8729693 = 3273635) B3273635
theorem B1840267 : Blo 1723062 1840267 := bstep (se 1 (by rfl) ⟨1380200, by rfl⟩ : syracuseStep 1840267 = 2760401) B2760401
theorem B2585753 : Blo 1723062 2585753 := bstep (se 2 (by rfl) ⟨969657, by rfl⟩ : syracuseStep 2585753 = 1939315) B1939315
theorem B3880115 : Blo 1723062 3880115 := bstep (se 1 (by rfl) ⟨2910086, by rfl⟩ : syracuseStep 3880115 = 5820173) B5820173
theorem B4912321 : Blo 1723062 4912321 := bstep (se 2 (by rfl) ⟨1842120, by rfl⟩ : syracuseStep 4912321 = 3684241) B3684241
theorem B3880151 : Blo 1723062 3880151 := bstep (se 1 (by rfl) ⟨2910113, by rfl⟩ : syracuseStep 3880151 = 5820227) B5820227
theorem B1938667 : Blo 1723062 1938667 := bstep (se 1 (by rfl) ⟨1454000, by rfl⟩ : syracuseStep 1938667 = 2908001) B2908001
theorem B2585867 : Blo 1723062 2585867 := bstep (se 1 (by rfl) ⟨1939400, by rfl⟩ : syracuseStep 2585867 = 3878801) B3878801
theorem B2585879 : Blo 1723062 2585879 := bstep (se 1 (by rfl) ⟨1939409, by rfl⟩ : syracuseStep 2585879 = 3878819) B3878819
theorem B7361837 : Blo 1723062 7361837 := bstep (se 3 (by rfl) ⟨1380344, by rfl⟩ : syracuseStep 7361837 = 2760689) B2760689
theorem B4363571 : Blo 1723062 4363571 := bstep (se 1 (by rfl) ⟨3272678, by rfl⟩ : syracuseStep 4363571 = 6545357) B6545357
theorem B1938775 : Blo 1723062 1938775 := bstep (se 1 (by rfl) ⟨1454081, by rfl⟩ : syracuseStep 1938775 = 2908163) B2908163
theorem B2585945 : Blo 1723062 2585945 := bstep (se 2 (by rfl) ⟨969729, by rfl⟩ : syracuseStep 2585945 = 1939459) B1939459
theorem B3880331 : Blo 1723062 3880331 := bstep (se 1 (by rfl) ⟨2910248, by rfl⟩ : syracuseStep 3880331 = 5820497) B5820497
theorem B5821847 : Blo 1723062 5821847 := bstep (se 1 (by rfl) ⟨4366385, by rfl⟩ : syracuseStep 5821847 = 8732771) B8732771
theorem B3880385 : Blo 1723062 3880385 := bstep (se 2 (by rfl) ⟨1455144, by rfl⟩ : syracuseStep 3880385 = 2910289) B2910289
theorem B2586059 : Blo 1723062 2586059 := bstep (se 1 (by rfl) ⟨1939544, by rfl⟩ : syracuseStep 2586059 = 3879089) B3879089
theorem B2586071 : Blo 1723062 2586071 := bstep (se 1 (by rfl) ⟨1939553, by rfl⟩ : syracuseStep 2586071 = 3879107) B3879107
theorem B14177753 : Blo 1723062 14177753 := bstep (se 2 (by rfl) ⟨5316657, by rfl⟩ : syracuseStep 14177753 = 10633315) B10633315
theorem B1938955 : Blo 1723062 1938955 := bstep (se 1 (by rfl) ⟨1454216, by rfl⟩ : syracuseStep 1938955 = 2908433) B2908433
theorem B2586137 : Blo 1723062 2586137 := bstep (se 2 (by rfl) ⟨969801, by rfl⟩ : syracuseStep 2586137 = 1939603) B1939603
theorem B4363865 : Blo 1723062 4363865 := bstep (se 2 (by rfl) ⟨1636449, by rfl⟩ : syracuseStep 4363865 = 3272899) B3272899
theorem B1939063 : Blo 1723062 1939063 := bstep (se 1 (by rfl) ⟨1454297, by rfl⟩ : syracuseStep 1939063 = 2908595) B2908595
theorem B2586251 : Blo 1723062 2586251 := bstep (se 1 (by rfl) ⟨1939688, by rfl⟩ : syracuseStep 2586251 = 3879377) B3879377
theorem B2586263 : Blo 1723062 2586263 := bstep (se 1 (by rfl) ⟨1939697, by rfl⟩ : syracuseStep 2586263 = 3879395) B3879395
theorem B3880601 : Blo 1723062 3880601 := bstep (se 2 (by rfl) ⟨1455225, by rfl⟩ : syracuseStep 3880601 = 2910451) B2910451
theorem B2586329 : Blo 1723062 2586329 := bstep (se 2 (by rfl) ⟨969873, by rfl⟩ : syracuseStep 2586329 = 1939747) B1939747
theorem B3880691 : Blo 1723062 3880691 := bstep (se 1 (by rfl) ⟨2910518, by rfl⟩ : syracuseStep 3880691 = 5821037) B5821037
theorem B7788311 : Blo 1723062 7788311 := bstep (se 1 (by rfl) ⟨5841233, by rfl⟩ : syracuseStep 7788311 = 11682467) B11682467
theorem B3880727 : Blo 1723062 3880727 := bstep (se 1 (by rfl) ⟨2910545, by rfl⟩ : syracuseStep 3880727 = 5821091) B5821091
theorem B13268771 : Blo 1723062 13268771 := bstep (se 1 (by rfl) ⟨9951578, by rfl⟩ : syracuseStep 13268771 = 19903157) B19903157
theorem B1939243 : Blo 1723062 1939243 := bstep (se 1 (by rfl) ⟨1454432, by rfl⟩ : syracuseStep 1939243 = 2908865) B2908865
theorem B2586443 : Blo 1723062 2586443 := bstep (se 1 (by rfl) ⟨1939832, by rfl⟩ : syracuseStep 2586443 = 3879665) B3879665
theorem B2586455 : Blo 1723062 2586455 := bstep (se 1 (by rfl) ⟨1939841, by rfl⟩ : syracuseStep 2586455 = 3879683) B3879683
theorem B7862167 : Blo 1723062 7862167 := bstep (se 1 (by rfl) ⟨5896625, by rfl⟩ : syracuseStep 7862167 = 11793251) B11793251
theorem B1939351 : Blo 1723062 1939351 := bstep (se 1 (by rfl) ⟨1454513, by rfl⟩ : syracuseStep 1939351 = 2909027) B2909027
theorem B2586521 : Blo 1723062 2586521 := bstep (se 2 (by rfl) ⟨969945, by rfl⟩ : syracuseStep 2586521 = 1939891) B1939891
theorem B3880907 : Blo 1723062 3880907 := bstep (se 1 (by rfl) ⟨2910680, by rfl⟩ : syracuseStep 3880907 = 5821361) B5821361
theorem B7362521 : Blo 1723062 7362521 := bstep (se 2 (by rfl) ⟨2760945, by rfl⟩ : syracuseStep 7362521 = 5521891) B5521891
theorem B3880961 : Blo 1723062 3880961 := bstep (se 2 (by rfl) ⟨1455360, by rfl⟩ : syracuseStep 3880961 = 2910721) B2910721
theorem B2586635 : Blo 1723062 2586635 := bstep (se 1 (by rfl) ⟨1939976, by rfl⟩ : syracuseStep 2586635 = 3879953) B3879953
theorem B2586647 : Blo 1723062 2586647 := bstep (se 1 (by rfl) ⟨1939985, by rfl⟩ : syracuseStep 2586647 = 3879971) B3879971
theorem B6993965 : Blo 1723062 6993965 := bstep (se 3 (by rfl) ⟨1311368, by rfl⟩ : syracuseStep 6993965 = 2622737) B2622737
theorem B1939531 : Blo 1723062 1939531 := bstep (se 1 (by rfl) ⟨1454648, by rfl⟩ : syracuseStep 1939531 = 2909297) B2909297
theorem B2586713 : Blo 1723062 2586713 := bstep (se 2 (by rfl) ⟨970017, by rfl⟩ : syracuseStep 2586713 = 1940035) B1940035
theorem B6215773 : Blo 1723062 6215773 := bstep (se 3 (by rfl) ⟨1165457, by rfl⟩ : syracuseStep 6215773 = 2330915) B2330915
theorem B6215831 : Blo 1723062 6215831 := bstep (se 1 (by rfl) ⟨4661873, by rfl⟩ : syracuseStep 6215831 = 9323747) B9323747
theorem B2455705 : Blo 1723062 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B1939639 : Blo 1723062 1939639 := bstep (se 1 (by rfl) ⟨1454729, by rfl⟩ : syracuseStep 1939639 = 2909459) B2909459
theorem B2586827 : Blo 1723062 2586827 := bstep (se 1 (by rfl) ⟨1940120, by rfl⟩ : syracuseStep 2586827 = 3880241) B3880241
theorem B2586839 : Blo 1723062 2586839 := bstep (se 1 (by rfl) ⟨1940129, by rfl⟩ : syracuseStep 2586839 = 3880259) B3880259
theorem B3881177 : Blo 1723062 3881177 := bstep (se 2 (by rfl) ⟨1455441, by rfl⟩ : syracuseStep 3881177 = 2910883) B2910883
theorem B2586905 : Blo 1723062 2586905 := bstep (se 2 (by rfl) ⟨970089, by rfl⟩ : syracuseStep 2586905 = 1940179) B1940179
theorem B3881267 : Blo 1723062 3881267 := bstep (se 1 (by rfl) ⟨2910950, by rfl⟩ : syracuseStep 3881267 = 5821901) B5821901
theorem B3881303 : Blo 1723062 3881303 := bstep (se 1 (by rfl) ⟨2910977, by rfl⟩ : syracuseStep 3881303 = 5821955) B5821955
theorem B11049317 : Blo 1723062 11049317 := bstep (se 4 (by rfl) ⟨1035873, by rfl⟩ : syracuseStep 11049317 = 2071747) B2071747
theorem B1939819 : Blo 1723062 1939819 := bstep (se 1 (by rfl) ⟨1454864, by rfl⟩ : syracuseStep 1939819 = 2909729) B2909729
theorem B2587019 : Blo 1723062 2587019 := bstep (se 1 (by rfl) ⟨1940264, by rfl⟩ : syracuseStep 2587019 = 3880529) B3880529
theorem B2587031 : Blo 1723062 2587031 := bstep (se 1 (by rfl) ⟨1940273, by rfl⟩ : syracuseStep 2587031 = 3880547) B3880547
theorem B1939927 : Blo 1723062 1939927 := bstep (se 1 (by rfl) ⟨1454945, by rfl⟩ : syracuseStep 1939927 = 2909891) B2909891
theorem B2587097 : Blo 1723062 2587097 := bstep (se 2 (by rfl) ⟨970161, by rfl⟩ : syracuseStep 2587097 = 1940323) B1940323
theorem B9320977 : Blo 1723062 9320977 := bstep (se 2 (by rfl) ⟨3495366, by rfl⟩ : syracuseStep 9320977 = 6990733) B6990733
theorem B2587211 : Blo 1723062 2587211 := bstep (se 1 (by rfl) ⟨1940408, by rfl⟩ : syracuseStep 2587211 = 3880817) B3880817
theorem B3496535 : Blo 1723062 3496535 := bstep (se 1 (by rfl) ⟨2622401, by rfl⟩ : syracuseStep 3496535 = 5244803) B5244803
theorem B2587223 : Blo 1723062 2587223 := bstep (se 1 (by rfl) ⟨1940417, by rfl⟩ : syracuseStep 2587223 = 3880835) B3880835
theorem B1940107 : Blo 1723062 1940107 := bstep (se 1 (by rfl) ⟨1455080, by rfl⟩ : syracuseStep 1940107 = 2910161) B2910161
theorem B2587289 : Blo 1723062 2587289 := bstep (se 2 (by rfl) ⟨970233, by rfl⟩ : syracuseStep 2587289 = 1940467) B1940467
theorem B1940215 : Blo 1723062 1940215 := bstep (se 1 (by rfl) ⟨1455161, by rfl⟩ : syracuseStep 1940215 = 2910323) B2910323
theorem B2587403 : Blo 1723062 2587403 := bstep (se 1 (by rfl) ⟨1940552, by rfl⟩ : syracuseStep 2587403 = 3881105) B3881105
theorem B368016149 : Blo 1723062 368016149 := bstep (se 6 (by rfl) ⟨8625378, by rfl⟩ : syracuseStep 368016149 = 17250757) B17250757
theorem B6986519 : Blo 1723062 6986519 := bstep (se 1 (by rfl) ⟨5239889, by rfl⟩ : syracuseStep 6986519 = 10479779) B10479779
theorem B2587415 : Blo 1723062 2587415 := bstep (se 1 (by rfl) ⟨1940561, by rfl⟩ : syracuseStep 2587415 = 3881123) B3881123
theorem B2210635 : Blo 1723062 2210635 := bstep (se 1 (by rfl) ⟨1657976, by rfl⟩ : syracuseStep 2210635 = 3315953) B3315953
theorem B11049803 : Blo 1723062 11049803 := bstep (se 1 (by rfl) ⟨8287352, by rfl⟩ : syracuseStep 11049803 = 16574705) B16574705
theorem B5241689 : Blo 1723062 5241689 := bstep (se 2 (by rfl) ⟨1965633, by rfl⟩ : syracuseStep 5241689 = 3931267) B3931267
theorem B2587481 : Blo 1723062 2587481 := bstep (se 2 (by rfl) ⟨970305, by rfl⟩ : syracuseStep 2587481 = 1940611) B1940611
theorem B1940395 : Blo 1723062 1940395 := bstep (se 1 (by rfl) ⟨1455296, by rfl⟩ : syracuseStep 1940395 = 2910593) B2910593
theorem B3734465 : Blo 1723062 3734465 := bstep (se 2 (by rfl) ⟨1400424, by rfl⟩ : syracuseStep 3734465 = 2800849) B2800849
theorem B11041753 : Blo 1723062 11041753 := bstep (se 2 (by rfl) ⟨4140657, by rfl⟩ : syracuseStep 11041753 = 8281315) B8281315
theorem B1940503 : Blo 1723062 1940503 := bstep (se 1 (by rfl) ⟨1455377, by rfl⟩ : syracuseStep 1940503 = 2910755) B2910755
theorem B17685539 : Blo 1723062 17685539 := bstep (se 1 (by rfl) ⟨13264154, by rfl⟩ : syracuseStep 17685539 = 26528309) B26528309
theorem B9821249 : Blo 1723062 9821249 := bstep (se 2 (by rfl) ⟨3682968, by rfl⟩ : syracuseStep 9821249 = 7365937) B7365937
theorem B13089923 : Blo 1723062 13089923 := bstep (se 1 (by rfl) ⟨9817442, by rfl⟩ : syracuseStep 13089923 = 19634885) B19634885
theorem B37264535 : Blo 1723062 37264535 := bstep (se 1 (by rfl) ⟨27948401, by rfl⟩ : syracuseStep 37264535 = 55896803) B55896803
theorem B8731799 : Blo 1723062 8731799 := bstep (se 1 (by rfl) ⟨6548849, by rfl⟩ : syracuseStep 8731799 = 13097699) B13097699
theorem B5815475 : Blo 1723062 5815475 := bstep (se 1 (by rfl) ⟨4361606, by rfl⟩ : syracuseStep 5815475 = 8723213) B8723213
theorem B4365515 : Blo 1723062 4365515 := bstep (se 1 (by rfl) ⟨3274136, by rfl⟩ : syracuseStep 4365515 = 6548273) B6548273
theorem B1940683 : Blo 1723062 1940683 := bstep (se 1 (by rfl) ⟨1455512, by rfl⟩ : syracuseStep 1940683 = 2911025) B2911025
theorem B18422989 : Blo 1723062 18422989 := bstep (se 3 (by rfl) ⟨3454310, by rfl⟩ : syracuseStep 18422989 = 6908621) B6908621
theorem B24861937 : Blo 1723062 24861937 := bstep (se 2 (by rfl) ⟨9323226, by rfl⟩ : syracuseStep 24861937 = 18646453) B18646453
theorem B15736157 : Blo 1723062 15736157 := bstep (se 3 (by rfl) ⟨2950529, by rfl⟩ : syracuseStep 15736157 = 5901059) B5901059
theorem B1867115 : Blo 1723062 1867115 := bstep (se 1 (by rfl) ⟨1400336, by rfl⟩ : syracuseStep 1867115 = 2800673) B2800673
theorem B14728625 : Blo 1723062 14728625 := bstep (se 2 (by rfl) ⟨5523234, by rfl⟩ : syracuseStep 14728625 = 11046469) B11046469
theorem B5815745 : Blo 1723062 5815745 := bstep (se 2 (by rfl) ⟨2180904, by rfl⟩ : syracuseStep 5815745 = 4361809) B4361809
theorem B11042369 : Blo 1723062 11042369 := bstep (se 2 (by rfl) ⟨4140888, by rfl⟩ : syracuseStep 11042369 = 8281777) B8281777
theorem B19627595 : Blo 1723062 19627595 := bstep (se 1 (by rfl) ⟨14720696, by rfl⟩ : syracuseStep 19627595 = 29441393) B29441393
theorem B18636419 : Blo 1723062 18636419 := bstep (se 1 (by rfl) ⟨13977314, by rfl⟩ : syracuseStep 18636419 = 27954629) B27954629
theorem B22707863 : Blo 1723062 22707863 := bstep (se 1 (by rfl) ⟨17030897, by rfl⟩ : syracuseStep 22707863 = 34061795) B34061795
theorem B6545069 : Blo 1723062 6545069 := bstep (se 3 (by rfl) ⟨1227200, by rfl⟩ : syracuseStep 6545069 = 2454401) B2454401
theorem B8724185 : Blo 1723062 8724185 := bstep (se 2 (by rfl) ⟨3271569, by rfl⟩ : syracuseStep 8724185 = 6543139) B6543139
theorem B2908055 : Blo 1723062 2908055 := bstep (se 1 (by rfl) ⟨2181041, by rfl⟩ : syracuseStep 2908055 = 4362083) B4362083
theorem B2949067 : Blo 1723062 2949067 := bstep (se 1 (by rfl) ⟨2211800, by rfl⟩ : syracuseStep 2949067 = 4423601) B4423601
theorem B5816285 : Blo 1723062 5816285 := bstep (se 3 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 5816285 = 2181107) B2181107
theorem B7864285 : Blo 1723062 7864285 := bstep (se 3 (by rfl) ⟨1474553, by rfl⟩ : syracuseStep 7864285 = 2949107) B2949107
theorem B16564247 : Blo 1723062 16564247 := bstep (se 1 (by rfl) ⟨12423185, by rfl⟩ : syracuseStep 16564247 = 24846371) B24846371
theorem B8724509 : Blo 1723062 8724509 := bstep (se 3 (by rfl) ⟨1635845, by rfl⟩ : syracuseStep 8724509 = 3271691) B3271691
theorem B5898269 : Blo 1723062 5898269 := bstep (se 3 (by rfl) ⟨1105925, by rfl⟩ : syracuseStep 5898269 = 2211851) B2211851
theorem B2621575 : Blo 1723062 2621575 := bstep (se 1 (by rfl) ⟨1966181, by rfl⟩ : syracuseStep 2621575 = 3932363) B3932363
theorem B2908345 : Blo 1723062 2908345 := bstep (se 2 (by rfl) ⟨1090629, by rfl⟩ : syracuseStep 2908345 = 2181259) B2181259
theorem B5816609 : Blo 1723062 5816609 := bstep (se 2 (by rfl) ⟨2181228, by rfl⟩ : syracuseStep 5816609 = 4362457) B4362457
theorem B5521697 : Blo 1723062 5521697 := bstep (se 2 (by rfl) ⟨2070636, by rfl⟩ : syracuseStep 5521697 = 4141273) B4141273
theorem B5898529 : Blo 1723062 5898529 := bstep (se 2 (by rfl) ⟨2211948, by rfl⟩ : syracuseStep 5898529 = 4423897) B4423897
theorem B6545873 : Blo 1723062 6545873 := bstep (se 2 (by rfl) ⟨2454702, by rfl⟩ : syracuseStep 6545873 = 4909405) B4909405
theorem B5243393 : Blo 1723062 5243393 := bstep (se 2 (by rfl) ⟨1966272, by rfl⟩ : syracuseStep 5243393 = 3932545) B3932545
theorem B8724995 : Blo 1723062 8724995 := bstep (se 1 (by rfl) ⟨6543746, by rfl⟩ : syracuseStep 8724995 = 13087493) B13087493
theorem B10232381 : Blo 1723062 10232381 := bstep (se 3 (by rfl) ⟨1918571, by rfl⟩ : syracuseStep 10232381 = 3837143) B3837143
theorem B4907891 : Blo 1723062 4907891 := bstep (se 1 (by rfl) ⟨3680918, by rfl⟩ : syracuseStep 4907891 = 7361837) B7361837
theorem B5817203 : Blo 1723062 5817203 := bstep (se 1 (by rfl) ⟨4362902, by rfl⟩ : syracuseStep 5817203 = 8725805) B8725805
theorem B2909047 : Blo 1723062 2909047 := bstep (se 1 (by rfl) ⟨2181785, by rfl⟩ : syracuseStep 2909047 = 4363571) B4363571
theorem B6546329 : Blo 1723062 6546329 := bstep (se 2 (by rfl) ⟨2454873, by rfl⟩ : syracuseStep 6546329 = 4909747) B4909747
theorem B2909243 : Blo 1723062 2909243 := bstep (se 1 (by rfl) ⟨2181932, by rfl⟩ : syracuseStep 2909243 = 4363865) B4363865
theorem B4908289 : Blo 1723062 4908289 := bstep (se 2 (by rfl) ⟨1840608, by rfl⟩ : syracuseStep 4908289 = 3681217) B3681217
theorem B14722337 : Blo 1723062 14722337 := bstep (se 2 (by rfl) ⟨5520876, by rfl⟩ : syracuseStep 14722337 = 11041753) B11041753
theorem B4908347 : Blo 1723062 4908347 := bstep (se 1 (by rfl) ⟨3681260, by rfl⟩ : syracuseStep 4908347 = 7362521) B7362521
theorem B4662643 : Blo 1723062 4662643 := bstep (se 1 (by rfl) ⟨3496982, by rfl⟩ : syracuseStep 4662643 = 6993965) B6993965
theorem B2909641 : Blo 1723062 2909641 := bstep (se 2 (by rfl) ⟨1091115, by rfl⟩ : syracuseStep 2909641 = 2182231) B2182231
theorem B7366211 : Blo 1723062 7366211 := bstep (se 1 (by rfl) ⟨5524658, by rfl⟩ : syracuseStep 7366211 = 11049317) B11049317
theorem B11044471 : Blo 1723062 11044471 := bstep (se 1 (by rfl) ⟨8283353, by rfl⟩ : syracuseStep 11044471 = 16566707) B16566707
theorem B245344099 : Blo 1723062 245344099 := bstep (se 1 (by rfl) ⟨184008074, by rfl⟩ : syracuseStep 245344099 = 368016149) B368016149
theorem B7366535 : Blo 1723062 7366535 := bstep (se 1 (by rfl) ⟨5524901, by rfl⟩ : syracuseStep 7366535 = 11049803) B11049803
theorem B11790359 : Blo 1723062 11790359 := bstep (se 1 (by rfl) ⟨8842769, by rfl⟩ : syracuseStep 11790359 = 17685539) B17685539
theorem B2181163 : Blo 1723062 2181163 := bstep (se 1 (by rfl) ⟨1635872, by rfl⟩ : syracuseStep 2181163 = 3271745) B3271745
theorem B6547499 : Blo 1723062 6547499 := bstep (se 1 (by rfl) ⟨4910624, by rfl⟩ : syracuseStep 6547499 = 9821249) B9821249
theorem B2361403 : Blo 1723062 2361403 := bstep (se 1 (by rfl) ⟨1771052, by rfl⟩ : syracuseStep 2361403 = 3542105) B3542105
theorem B8726615 : Blo 1723062 8726615 := bstep (se 1 (by rfl) ⟨6544961, by rfl⟩ : syracuseStep 8726615 = 13089923) B13089923
theorem B3876983 : Blo 1723062 3876983 := bstep (se 1 (by rfl) ⟨2907737, by rfl⟩ : syracuseStep 3876983 = 5815475) B5815475
theorem B2910343 : Blo 1723062 2910343 := bstep (se 1 (by rfl) ⟨2182757, by rfl⟩ : syracuseStep 2910343 = 4365515) B4365515
theorem B44181773 : Blo 1723062 44181773 := bstep (se 3 (by rfl) ⟨8284082, by rfl⟩ : syracuseStep 44181773 = 16568165) B16568165
theorem B3877163 : Blo 1723062 3877163 := bstep (se 1 (by rfl) ⟨2907872, by rfl⟩ : syracuseStep 3877163 = 5815745) B5815745
theorem B13085063 : Blo 1723062 13085063 := bstep (se 1 (by rfl) ⟨9813797, by rfl⟩ : syracuseStep 13085063 = 19627595) B19627595
theorem B9325003 : Blo 1723062 9325003 := bstep (se 1 (by rfl) ⟨6993752, by rfl⟩ : syracuseStep 9325003 = 13987505) B13987505
theorem B8727101 : Blo 1723062 8727101 := bstep (se 3 (by rfl) ⟨1636331, by rfl⟩ : syracuseStep 8727101 = 3272663) B3272663
theorem B5524055 : Blo 1723062 5524055 := bstep (se 1 (by rfl) ⟨4143041, by rfl⟩ : syracuseStep 5524055 = 8286083) B8286083
theorem B66292343 : Blo 1723062 66292343 := bstep (se 1 (by rfl) ⟨49719257, by rfl⟩ : syracuseStep 66292343 = 99438515) B99438515
theorem B3877523 : Blo 1723062 3877523 := bstep (se 1 (by rfl) ⟨2908142, by rfl⟩ : syracuseStep 3877523 = 5816285) B5816285
theorem B1723067 : Blo 1723062 1723067 := bstep (se 1 (by rfl) ⟨1292300, by rfl⟩ : syracuseStep 1723067 = 2584601) B2584601
theorem B3877577 : Blo 1723062 3877577 := bstep (se 2 (by rfl) ⟨1454091, by rfl⟩ : syracuseStep 3877577 = 2908183) B2908183
theorem B49711877 : Blo 1723062 49711877 := bstep (se 4 (by rfl) ⟨4660488, by rfl⟩ : syracuseStep 49711877 = 9320977) B9320977
theorem B1723143 : Blo 1723062 1723143 := bstep (se 1 (by rfl) ⟨1292357, by rfl⟩ : syracuseStep 1723143 = 2584715) B2584715
theorem B1723151 : Blo 1723062 1723151 := bstep (se 1 (by rfl) ⟨1292363, by rfl⟩ : syracuseStep 1723151 = 2584727) B2584727
theorem B2910991 : Blo 1723062 2910991 := bstep (se 1 (by rfl) ⟨2183243, by rfl⟩ : syracuseStep 2910991 = 4366487) B4366487
theorem B1723195 : Blo 1723062 1723195 := bstep (se 1 (by rfl) ⟨1292396, by rfl⟩ : syracuseStep 1723195 = 2584793) B2584793
theorem B1723271 : Blo 1723062 1723271 := bstep (se 1 (by rfl) ⟨1292453, by rfl⟩ : syracuseStep 1723271 = 2584907) B2584907
theorem B1723279 : Blo 1723062 1723279 := bstep (se 1 (by rfl) ⟨1292459, by rfl⟩ : syracuseStep 1723279 = 2584919) B2584919
theorem B1747855 : Blo 1723062 1747855 := bstep (se 1 (by rfl) ⟨1310891, by rfl⟩ : syracuseStep 1747855 = 2621783) B2621783
theorem B1723323 : Blo 1723062 1723323 := bstep (se 1 (by rfl) ⟨1292492, by rfl⟩ : syracuseStep 1723323 = 2584985) B2584985
theorem B2329591 : Blo 1723062 2329591 := bstep (se 1 (by rfl) ⟨1747193, by rfl⟩ : syracuseStep 2329591 = 3494387) B3494387
theorem B2182135 : Blo 1723062 2182135 := bstep (se 1 (by rfl) ⟨1636601, by rfl⟩ : syracuseStep 2182135 = 3273203) B3273203
theorem B1723399 : Blo 1723062 1723399 := bstep (se 1 (by rfl) ⟨1292549, by rfl⟩ : syracuseStep 1723399 = 2585099) B2585099
theorem B1723407 : Blo 1723062 1723407 := bstep (se 1 (by rfl) ⟨1292555, by rfl⟩ : syracuseStep 1723407 = 2585111) B2585111
theorem B1723451 : Blo 1723062 1723451 := bstep (se 1 (by rfl) ⟨1292588, by rfl⟩ : syracuseStep 1723451 = 2585177) B2585177
theorem B1723527 : Blo 1723062 1723527 := bstep (se 1 (by rfl) ⟨1292645, by rfl⟩ : syracuseStep 1723527 = 2585291) B2585291
theorem B1723535 : Blo 1723062 1723535 := bstep (se 1 (by rfl) ⟨1292651, by rfl⟩ : syracuseStep 1723535 = 2585303) B2585303
theorem B1723579 : Blo 1723062 1723579 := bstep (se 1 (by rfl) ⟨1292684, by rfl⟩ : syracuseStep 1723579 = 2585369) B2585369
theorem B1723655 : Blo 1723062 1723655 := bstep (se 1 (by rfl) ⟨1292741, by rfl⟩ : syracuseStep 1723655 = 2585483) B2585483
theorem B1723663 : Blo 1723062 1723663 := bstep (se 1 (by rfl) ⟨1292747, by rfl⟩ : syracuseStep 1723663 = 2585495) B2585495
theorem B1723707 : Blo 1723062 1723707 := bstep (se 1 (by rfl) ⟨1292780, by rfl⟩ : syracuseStep 1723707 = 2585561) B2585561
theorem B2182459 : Blo 1723062 2182459 := bstep (se 1 (by rfl) ⟨1636844, by rfl⟩ : syracuseStep 2182459 = 3273689) B3273689
theorem B3272071 : Blo 1723062 3272071 := bstep (se 1 (by rfl) ⟨2454053, by rfl⟩ : syracuseStep 3272071 = 4908107) B4908107
theorem B3878279 : Blo 1723062 3878279 := bstep (se 1 (by rfl) ⟨2908709, by rfl⟩ : syracuseStep 3878279 = 5817419) B5817419
theorem B1723783 : Blo 1723062 1723783 := bstep (se 1 (by rfl) ⟨1292837, by rfl⟩ : syracuseStep 1723783 = 2585675) B2585675
theorem B1723791 : Blo 1723062 1723791 := bstep (se 1 (by rfl) ⟨1292843, by rfl⟩ : syracuseStep 1723791 = 2585687) B2585687
theorem B5819795 : Blo 1723062 5819795 := bstep (se 1 (by rfl) ⟨4364846, by rfl⟩ : syracuseStep 5819795 = 8729693) B8729693
theorem B1723835 : Blo 1723062 1723835 := bstep (se 1 (by rfl) ⟨1292876, by rfl⟩ : syracuseStep 1723835 = 2585753) B2585753
theorem B1723911 : Blo 1723062 1723911 := bstep (se 1 (by rfl) ⟨1292933, by rfl⟩ : syracuseStep 1723911 = 2585867) B2585867
theorem B1723919 : Blo 1723062 1723919 := bstep (se 1 (by rfl) ⟨1292939, by rfl⟩ : syracuseStep 1723919 = 2585879) B2585879
theorem B4910635 : Blo 1723062 4910635 := bstep (se 1 (by rfl) ⟨3682976, by rfl⟩ : syracuseStep 4910635 = 7365953) B7365953
theorem B3878459 : Blo 1723062 3878459 := bstep (se 1 (by rfl) ⟨2908844, by rfl⟩ : syracuseStep 3878459 = 5817689) B5817689
theorem B1723963 : Blo 1723062 1723963 := bstep (se 1 (by rfl) ⟨1292972, by rfl⟩ : syracuseStep 1723963 = 2585945) B2585945
theorem B1724039 : Blo 1723062 1724039 := bstep (se 1 (by rfl) ⟨1293029, by rfl⟩ : syracuseStep 1724039 = 2586059) B2586059
theorem B1724047 : Blo 1723062 1724047 := bstep (se 1 (by rfl) ⟨1293035, by rfl⟩ : syracuseStep 1724047 = 2586071) B2586071
theorem B3878585 : Blo 1723062 3878585 := bstep (se 2 (by rfl) ⟨1454469, by rfl⟩ : syracuseStep 3878585 = 2908939) B2908939
theorem B1724091 : Blo 1723062 1724091 := bstep (se 1 (by rfl) ⟨1293068, by rfl⟩ : syracuseStep 1724091 = 2586137) B2586137
theorem B1724167 : Blo 1723062 1724167 := bstep (se 1 (by rfl) ⟨1293125, by rfl⟩ : syracuseStep 1724167 = 2586251) B2586251
theorem B1724175 : Blo 1723062 1724175 := bstep (se 1 (by rfl) ⟨1293131, by rfl⟩ : syracuseStep 1724175 = 2586263) B2586263
theorem B4910863 : Blo 1723062 4910863 := bstep (se 1 (by rfl) ⟨3683147, by rfl⟩ : syracuseStep 4910863 = 7366295) B7366295
theorem B1724219 : Blo 1723062 1724219 := bstep (se 1 (by rfl) ⟨1293164, by rfl⟩ : syracuseStep 1724219 = 2586329) B2586329
theorem B1724295 : Blo 1723062 1724295 := bstep (se 1 (by rfl) ⟨1293221, by rfl⟩ : syracuseStep 1724295 = 2586443) B2586443
theorem B1724303 : Blo 1723062 1724303 := bstep (se 1 (by rfl) ⟨1293227, by rfl⟩ : syracuseStep 1724303 = 2586455) B2586455
theorem B3272633 : Blo 1723062 3272633 := bstep (se 2 (by rfl) ⟨1227237, by rfl⟩ : syracuseStep 3272633 = 2454475) B2454475
theorem B1724347 : Blo 1723062 1724347 := bstep (se 1 (by rfl) ⟨1293260, by rfl⟩ : syracuseStep 1724347 = 2586521) B2586521
theorem B6549457 : Blo 1723062 6549457 := bstep (se 2 (by rfl) ⟨2456046, by rfl⟩ : syracuseStep 6549457 = 4912093) B4912093
theorem B2453495 : Blo 1723062 2453495 := bstep (se 1 (by rfl) ⟨1840121, by rfl⟩ : syracuseStep 2453495 = 3680243) B3680243
theorem B1724423 : Blo 1723062 1724423 := bstep (se 1 (by rfl) ⟨1293317, by rfl⟩ : syracuseStep 1724423 = 2586635) B2586635
theorem B3878927 : Blo 1723062 3878927 := bstep (se 1 (by rfl) ⟨2909195, by rfl⟩ : syracuseStep 3878927 = 5818391) B5818391
theorem B1724431 : Blo 1723062 1724431 := bstep (se 1 (by rfl) ⟨1293323, by rfl⟩ : syracuseStep 1724431 = 2586647) B2586647
theorem B3878945 : Blo 1723062 3878945 := bstep (se 2 (by rfl) ⟨1454604, by rfl⟩ : syracuseStep 3878945 = 2909209) B2909209
theorem B4911137 : Blo 1723062 4911137 := bstep (se 2 (by rfl) ⟨1841676, by rfl⟩ : syracuseStep 4911137 = 3683353) B3683353
theorem B2584619 : Blo 1723062 2584619 := bstep (se 1 (by rfl) ⟨1938464, by rfl⟩ : syracuseStep 2584619 = 3876929) B3876929
theorem B1724475 : Blo 1723062 1724475 := bstep (se 1 (by rfl) ⟨1293356, by rfl⟩ : syracuseStep 1724475 = 2586713) B2586713
theorem B2584649 : Blo 1723062 2584649 := bstep (se 2 (by rfl) ⟨969243, by rfl⟩ : syracuseStep 2584649 = 1938487) B1938487
theorem B1724551 : Blo 1723062 1724551 := bstep (se 1 (by rfl) ⟨1293413, by rfl⟩ : syracuseStep 1724551 = 2586827) B2586827
theorem B1724559 : Blo 1723062 1724559 := bstep (se 1 (by rfl) ⟨1293419, by rfl⟩ : syracuseStep 1724559 = 2586839) B2586839
theorem B2453689 : Blo 1723062 2453689 := bstep (se 2 (by rfl) ⟨920133, by rfl⟩ : syracuseStep 2453689 = 1840267) B1840267
theorem B2584763 : Blo 1723062 2584763 := bstep (se 1 (by rfl) ⟨1938572, by rfl⟩ : syracuseStep 2584763 = 3877145) B3877145
theorem B1724603 : Blo 1723062 1724603 := bstep (se 1 (by rfl) ⟨1293452, by rfl⟩ : syracuseStep 1724603 = 2586905) B2586905
theorem B2584823 : Blo 1723062 2584823 := bstep (se 1 (by rfl) ⟨1938617, by rfl⟩ : syracuseStep 2584823 = 3877235) B3877235
theorem B4141313 : Blo 1723062 4141313 := bstep (se 2 (by rfl) ⟨1552992, by rfl⟩ : syracuseStep 4141313 = 3105985) B3105985
theorem B6549761 : Blo 1723062 6549761 := bstep (se 2 (by rfl) ⟨2456160, by rfl⟩ : syracuseStep 6549761 = 4912321) B4912321
theorem B1724679 : Blo 1723062 1724679 := bstep (se 1 (by rfl) ⟨1293509, by rfl⟩ : syracuseStep 1724679 = 2587019) B2587019
theorem B2584847 : Blo 1723062 2584847 := bstep (se 1 (by rfl) ⟨1938635, by rfl⟩ : syracuseStep 2584847 = 3877271) B3877271
theorem B1724687 : Blo 1723062 1724687 := bstep (se 1 (by rfl) ⟨1293515, by rfl⟩ : syracuseStep 1724687 = 2587031) B2587031
theorem B393023765 : Blo 1723062 393023765 := bstep (se 6 (by rfl) ⟨9211494, by rfl⟩ : syracuseStep 393023765 = 18422989) B18422989
theorem B8728883 : Blo 1723062 8728883 := bstep (se 1 (by rfl) ⟨6546662, by rfl⟩ : syracuseStep 8728883 = 13093325) B13093325
theorem B2584889 : Blo 1723062 2584889 := bstep (se 2 (by rfl) ⟨969333, by rfl⟩ : syracuseStep 2584889 = 1938667) B1938667
theorem B1724731 : Blo 1723062 1724731 := bstep (se 1 (by rfl) ⟨1293548, by rfl⟩ : syracuseStep 1724731 = 2587097) B2587097
theorem B33149249 : Blo 1723062 33149249 := bstep (se 2 (by rfl) ⟨12430968, by rfl⟩ : syracuseStep 33149249 = 24861937) B24861937
theorem B3879287 : Blo 1723062 3879287 := bstep (se 1 (by rfl) ⟨2909465, by rfl⟩ : syracuseStep 3879287 = 5818931) B5818931
theorem B4911479 : Blo 1723062 4911479 := bstep (se 1 (by rfl) ⟨3683609, by rfl⟩ : syracuseStep 4911479 = 7367219) B7367219
theorem B2584967 : Blo 1723062 2584967 := bstep (se 1 (by rfl) ⟨1938725, by rfl⟩ : syracuseStep 2584967 = 3877451) B3877451
theorem B1724807 : Blo 1723062 1724807 := bstep (se 1 (by rfl) ⟨1293605, by rfl⟩ : syracuseStep 1724807 = 2587211) B2587211
theorem B2331023 : Blo 1723062 2331023 := bstep (se 1 (by rfl) ⟨1748267, by rfl⟩ : syracuseStep 2331023 = 3496535) B3496535
theorem B1724815 : Blo 1723062 1724815 := bstep (se 1 (by rfl) ⟨1293611, by rfl⟩ : syracuseStep 1724815 = 2587223) B2587223
theorem B2585003 : Blo 1723062 2585003 := bstep (se 1 (by rfl) ⟨1938752, by rfl⟩ : syracuseStep 2585003 = 3877505) B3877505
theorem B1724859 : Blo 1723062 1724859 := bstep (se 1 (by rfl) ⟨1293644, by rfl⟩ : syracuseStep 1724859 = 2587289) B2587289
theorem B2585033 : Blo 1723062 2585033 := bstep (se 2 (by rfl) ⟨969387, by rfl⟩ : syracuseStep 2585033 = 1938775) B1938775
theorem B1724935 : Blo 1723062 1724935 := bstep (se 1 (by rfl) ⟨1293701, by rfl⟩ : syracuseStep 1724935 = 2587403) B2587403
theorem B4657679 : Blo 1723062 4657679 := bstep (se 1 (by rfl) ⟨3493259, by rfl⟩ : syracuseStep 4657679 = 6986519) B6986519
theorem B1724943 : Blo 1723062 1724943 := bstep (se 1 (by rfl) ⟨1293707, by rfl⟩ : syracuseStep 1724943 = 2587415) B2587415
theorem B4141601 : Blo 1723062 4141601 := bstep (se 2 (by rfl) ⟨1553100, by rfl⟩ : syracuseStep 4141601 = 3106201) B3106201
theorem B3879467 : Blo 1723062 3879467 := bstep (se 1 (by rfl) ⟨2909600, by rfl⟩ : syracuseStep 3879467 = 5819201) B5819201
theorem B2585147 : Blo 1723062 2585147 := bstep (se 1 (by rfl) ⟨1938860, by rfl⟩ : syracuseStep 2585147 = 3877721) B3877721
theorem B3494459 : Blo 1723062 3494459 := bstep (se 1 (by rfl) ⟨2620844, by rfl⟩ : syracuseStep 3494459 = 5241689) B5241689
theorem B1724987 : Blo 1723062 1724987 := bstep (se 1 (by rfl) ⟨1293740, by rfl⟩ : syracuseStep 1724987 = 2587481) B2587481
theorem B2585207 : Blo 1723062 2585207 := bstep (se 1 (by rfl) ⟨1938905, by rfl⟩ : syracuseStep 2585207 = 3877811) B3877811
theorem B8729207 : Blo 1723062 8729207 := bstep (se 1 (by rfl) ⟨6546905, by rfl⟩ : syracuseStep 8729207 = 13093811) B13093811
theorem B2585231 : Blo 1723062 2585231 := bstep (se 1 (by rfl) ⟨1938923, by rfl⟩ : syracuseStep 2585231 = 3877847) B3877847
theorem B8286893 : Blo 1723062 8286893 := bstep (se 3 (by rfl) ⟨1553792, by rfl⟩ : syracuseStep 8286893 = 3107585) B3107585
theorem B2585273 : Blo 1723062 2585273 := bstep (se 2 (by rfl) ⟨969477, by rfl⟩ : syracuseStep 2585273 = 1938955) B1938955
theorem B2585351 : Blo 1723062 2585351 := bstep (se 1 (by rfl) ⟨1939013, by rfl⟩ : syracuseStep 2585351 = 3878027) B3878027
theorem B24843023 : Blo 1723062 24843023 := bstep (se 1 (by rfl) ⟨18632267, by rfl⟩ : syracuseStep 24843023 = 37264535) B37264535
theorem B5821199 : Blo 1723062 5821199 := bstep (se 1 (by rfl) ⟨4365899, by rfl⟩ : syracuseStep 5821199 = 8731799) B8731799
theorem B41931557 : Blo 1723062 41931557 := bstep (se 4 (by rfl) ⟨3931083, by rfl⟩ : syracuseStep 41931557 = 7862167) B7862167
theorem B2585387 : Blo 1723062 2585387 := bstep (se 1 (by rfl) ⟨1939040, by rfl⟩ : syracuseStep 2585387 = 3878081) B3878081
theorem B2585417 : Blo 1723062 2585417 := bstep (se 2 (by rfl) ⟨969531, by rfl⟩ : syracuseStep 2585417 = 1939063) B1939063
theorem B3879827 : Blo 1723062 3879827 := bstep (se 1 (by rfl) ⟨2909870, by rfl⟩ : syracuseStep 3879827 = 5819741) B5819741
theorem B10490771 : Blo 1723062 10490771 := bstep (se 1 (by rfl) ⟨7868078, by rfl⟩ : syracuseStep 10490771 = 15736157) B15736157
theorem B2585531 : Blo 1723062 2585531 := bstep (se 1 (by rfl) ⟨1939148, by rfl⟩ : syracuseStep 2585531 = 3878297) B3878297
theorem B3879881 : Blo 1723062 3879881 := bstep (se 2 (by rfl) ⟨1454955, by rfl⟩ : syracuseStep 3879881 = 2909911) B2909911
theorem B9819083 : Blo 1723062 9819083 := bstep (se 1 (by rfl) ⟨7364312, by rfl⟩ : syracuseStep 9819083 = 14728625) B14728625
theorem B8393681 : Blo 1723062 8393681 := bstep (se 2 (by rfl) ⟨3147630, by rfl⟩ : syracuseStep 8393681 = 6295261) B6295261
theorem B2585591 : Blo 1723062 2585591 := bstep (se 1 (by rfl) ⟨1939193, by rfl⟩ : syracuseStep 2585591 = 3878387) B3878387
theorem B4912139 : Blo 1723062 4912139 := bstep (se 1 (by rfl) ⟨3684104, by rfl⟩ : syracuseStep 4912139 = 7368209) B7368209
theorem B2585615 : Blo 1723062 2585615 := bstep (se 1 (by rfl) ⟨1939211, by rfl⟩ : syracuseStep 2585615 = 3878423) B3878423
theorem B5821469 : Blo 1723062 5821469 := bstep (se 3 (by rfl) ⟨1091525, by rfl⟩ : syracuseStep 5821469 = 2183051) B2183051
theorem B7361579 : Blo 1723062 7361579 := bstep (se 1 (by rfl) ⟨5521184, by rfl⟩ : syracuseStep 7361579 = 11042369) B11042369
theorem B2585657 : Blo 1723062 2585657 := bstep (se 2 (by rfl) ⟨969621, by rfl⟩ : syracuseStep 2585657 = 1939243) B1939243
theorem B3273787 : Blo 1723062 3273787 := bstep (se 1 (by rfl) ⟨2455340, by rfl⟩ : syracuseStep 3273787 = 4910681) B4910681
theorem B3683387 : Blo 1723062 3683387 := bstep (se 1 (by rfl) ⟨2762540, by rfl⟩ : syracuseStep 3683387 = 5525081) B5525081
theorem B12424279 : Blo 1723062 12424279 := bstep (se 1 (by rfl) ⟨9318209, by rfl⟩ : syracuseStep 12424279 = 18636419) B18636419
theorem B22393943 : Blo 1723062 22393943 := bstep (se 1 (by rfl) ⟨16795457, by rfl⟩ : syracuseStep 22393943 = 33590915) B33590915
theorem B4363379 : Blo 1723062 4363379 := bstep (se 1 (by rfl) ⟨3272534, by rfl⟩ : syracuseStep 4363379 = 6545069) B6545069
theorem B5239927 : Blo 1723062 5239927 := bstep (se 1 (by rfl) ⟨3929945, by rfl⟩ : syracuseStep 5239927 = 7859891) B7859891
theorem B5895287 : Blo 1723062 5895287 := bstep (se 1 (by rfl) ⟨4421465, by rfl⟩ : syracuseStep 5895287 = 8842931) B8842931
theorem B49689733 : Blo 1723062 49689733 := bstep (se 4 (by rfl) ⟨4658412, by rfl⟩ : syracuseStep 49689733 = 9316825) B9316825
theorem B2585735 : Blo 1723062 2585735 := bstep (se 1 (by rfl) ⟨1939301, by rfl⟩ : syracuseStep 2585735 = 3878603) B3878603
theorem B2585771 : Blo 1723062 2585771 := bstep (se 1 (by rfl) ⟨1939328, by rfl⟩ : syracuseStep 2585771 = 3878657) B3878657
theorem B9958573 : Blo 1723062 9958573 := bstep (se 3 (by rfl) ⟨1867232, by rfl⟩ : syracuseStep 9958573 = 3734465) B3734465
theorem B2585801 : Blo 1723062 2585801 := bstep (se 2 (by rfl) ⟨969675, by rfl⟩ : syracuseStep 2585801 = 1939351) B1939351
theorem B1938703 : Blo 1723062 1938703 := bstep (se 1 (by rfl) ⟨1454027, by rfl⟩ : syracuseStep 1938703 = 2908055) B2908055
theorem B2585915 : Blo 1723062 2585915 := bstep (se 1 (by rfl) ⟨1939436, by rfl⟩ : syracuseStep 2585915 = 3878873) B3878873
theorem B9319769 : Blo 1723062 9319769 := bstep (se 2 (by rfl) ⟨3494913, by rfl⟩ : syracuseStep 9319769 = 6989827) B6989827
theorem B2585975 : Blo 1723062 2585975 := bstep (se 1 (by rfl) ⟨1939481, by rfl⟩ : syracuseStep 2585975 = 3878963) B3878963
theorem B2905290125 : Blo 1723062 2905290125 := bstep (se 3 (by rfl) ⟨544741898, by rfl⟩ : syracuseStep 2905290125 = 1089483797) B1089483797
theorem B2585999 : Blo 1723062 2585999 := bstep (se 1 (by rfl) ⟨1939499, by rfl⟩ : syracuseStep 2585999 = 3878999) B3878999
theorem B9819539 : Blo 1723062 9819539 := bstep (se 1 (by rfl) ⟨7364654, by rfl⟩ : syracuseStep 9819539 = 14729309) B14729309
theorem B2586041 : Blo 1723062 2586041 := bstep (se 2 (by rfl) ⟨969765, by rfl⟩ : syracuseStep 2586041 = 1939531) B1939531
theorem B8287697 : Blo 1723062 8287697 := bstep (se 2 (by rfl) ⟨3107886, by rfl⟩ : syracuseStep 8287697 = 6215773) B6215773
theorem B2586119 : Blo 1723062 2586119 := bstep (se 1 (by rfl) ⟨1939589, by rfl⟩ : syracuseStep 2586119 = 3879179) B3879179
theorem B4658717 : Blo 1723062 4658717 := bstep (se 3 (by rfl) ⟨873509, by rfl⟩ : syracuseStep 4658717 = 1747019) B1747019
theorem B3274273 : Blo 1723062 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B2586155 : Blo 1723062 2586155 := bstep (se 1 (by rfl) ⟨1939616, by rfl⟩ : syracuseStep 2586155 = 3879233) B3879233
theorem B8730179 : Blo 1723062 8730179 := bstep (se 1 (by rfl) ⟨6547634, by rfl⟩ : syracuseStep 8730179 = 13095269) B13095269
theorem B2586185 : Blo 1723062 2586185 := bstep (se 2 (by rfl) ⟨969819, by rfl⟩ : syracuseStep 2586185 = 1939639) B1939639
theorem B4363895 : Blo 1723062 4363895 := bstep (se 1 (by rfl) ⟨3272921, by rfl⟩ : syracuseStep 4363895 = 6545843) B6545843
theorem B3880583 : Blo 1723062 3880583 := bstep (se 1 (by rfl) ⟨2910437, by rfl⟩ : syracuseStep 3880583 = 5820875) B5820875
theorem B2586299 : Blo 1723062 2586299 := bstep (se 1 (by rfl) ⟨1939724, by rfl⟩ : syracuseStep 2586299 = 3879449) B3879449
theorem B2586359 : Blo 1723062 2586359 := bstep (se 1 (by rfl) ⟨1939769, by rfl⟩ : syracuseStep 2586359 = 3879539) B3879539
theorem B1939207 : Blo 1723062 1939207 := bstep (se 1 (by rfl) ⟨1454405, by rfl⟩ : syracuseStep 1939207 = 2908811) B2908811
theorem B2586383 : Blo 1723062 2586383 := bstep (se 1 (by rfl) ⟨1939787, by rfl⟩ : syracuseStep 2586383 = 3879575) B3879575
theorem B3929899 : Blo 1723062 3929899 := bstep (se 1 (by rfl) ⟨2947424, by rfl⟩ : syracuseStep 3929899 = 5894849) B5894849
theorem B2586425 : Blo 1723062 2586425 := bstep (se 2 (by rfl) ⟨969909, by rfl⟩ : syracuseStep 2586425 = 1939819) B1939819
theorem B3880763 : Blo 1723062 3880763 := bstep (se 1 (by rfl) ⟨2910572, by rfl⟩ : syracuseStep 3880763 = 5821145) B5821145
theorem B2586503 : Blo 1723062 2586503 := bstep (se 1 (by rfl) ⟨1939877, by rfl⟩ : syracuseStep 2586503 = 3879755) B3879755
theorem B8730503 : Blo 1723062 8730503 := bstep (se 1 (by rfl) ⟨6547877, by rfl⟩ : syracuseStep 8730503 = 13095755) B13095755
theorem B2586539 : Blo 1723062 2586539 := bstep (se 1 (by rfl) ⟨1939904, by rfl⟩ : syracuseStep 2586539 = 3879809) B3879809
theorem B3880889 : Blo 1723062 3880889 := bstep (se 2 (by rfl) ⟨1455333, by rfl⟩ : syracuseStep 3880889 = 2910667) B2910667
theorem B1939387 : Blo 1723062 1939387 := bstep (se 1 (by rfl) ⟨1454540, by rfl⟩ : syracuseStep 1939387 = 2909081) B2909081
theorem B2586569 : Blo 1723062 2586569 := bstep (se 2 (by rfl) ⟨969963, by rfl⟩ : syracuseStep 2586569 = 1939927) B1939927
theorem B2586683 : Blo 1723062 2586683 := bstep (se 1 (by rfl) ⟨1940012, by rfl⟩ : syracuseStep 2586683 = 3880025) B3880025
theorem B2586743 : Blo 1723062 2586743 := bstep (se 1 (by rfl) ⟨1940057, by rfl⟩ : syracuseStep 2586743 = 3880115) B3880115
theorem B2586767 : Blo 1723062 2586767 := bstep (se 1 (by rfl) ⟨1940075, by rfl⟩ : syracuseStep 2586767 = 3880151) B3880151
theorem B2586809 : Blo 1723062 2586809 := bstep (se 2 (by rfl) ⟨970053, by rfl⟩ : syracuseStep 2586809 = 1940107) B1940107
theorem B2586887 : Blo 1723062 2586887 := bstep (se 1 (by rfl) ⟨1940165, by rfl⟩ : syracuseStep 2586887 = 3880331) B3880331
theorem B3881231 : Blo 1723062 3881231 := bstep (se 1 (by rfl) ⟨2910923, by rfl⟩ : syracuseStep 3881231 = 5821847) B5821847
theorem B4978973 : Blo 1723062 4978973 := bstep (se 3 (by rfl) ⟨933557, by rfl⟩ : syracuseStep 4978973 = 1867115) B1867115
theorem B3881249 : Blo 1723062 3881249 := bstep (se 2 (by rfl) ⟨1455468, by rfl⟩ : syracuseStep 3881249 = 2910937) B2910937
theorem B2586923 : Blo 1723062 2586923 := bstep (se 1 (by rfl) ⟨1940192, by rfl⟩ : syracuseStep 2586923 = 3880385) B3880385
theorem B9451835 : Blo 1723062 9451835 := bstep (se 1 (by rfl) ⟨7088876, by rfl⟩ : syracuseStep 9451835 = 14177753) B14177753
theorem B2586953 : Blo 1723062 2586953 := bstep (se 2 (by rfl) ⟨970107, by rfl⟩ : syracuseStep 2586953 = 1940215) B1940215
theorem B1939855 : Blo 1723062 1939855 := bstep (se 1 (by rfl) ⟨1454891, by rfl⟩ : syracuseStep 1939855 = 2909783) B2909783
theorem B2947513 : Blo 1723062 2947513 := bstep (se 2 (by rfl) ⟨1105317, by rfl⟩ : syracuseStep 2947513 = 2210635) B2210635
theorem B2587067 : Blo 1723062 2587067 := bstep (se 1 (by rfl) ⟨1940300, by rfl⟩ : syracuseStep 2587067 = 3880601) B3880601
theorem B2587127 : Blo 1723062 2587127 := bstep (se 1 (by rfl) ⟨1940345, by rfl⟩ : syracuseStep 2587127 = 3880691) B3880691
theorem B5192207 : Blo 1723062 5192207 := bstep (se 1 (by rfl) ⟨3894155, by rfl⟩ : syracuseStep 5192207 = 7788311) B7788311
theorem B2071055 : Blo 1723062 2071055 := bstep (se 1 (by rfl) ⟨1553291, by rfl⟩ : syracuseStep 2071055 = 3106583) B3106583
theorem B3496463 : Blo 1723062 3496463 := bstep (se 1 (by rfl) ⟨2622347, by rfl⟩ : syracuseStep 3496463 = 5244695) B5244695
theorem B2587151 : Blo 1723062 2587151 := bstep (se 1 (by rfl) ⟨1940363, by rfl⟩ : syracuseStep 2587151 = 3880727) B3880727
theorem B8845847 : Blo 1723062 8845847 := bstep (se 1 (by rfl) ⟨6634385, by rfl⟩ : syracuseStep 8845847 = 13268771) B13268771
theorem B18897437 : Blo 1723062 18897437 := bstep (se 3 (by rfl) ⟨3543269, by rfl⟩ : syracuseStep 18897437 = 7086539) B7086539
theorem B2587193 : Blo 1723062 2587193 := bstep (se 2 (by rfl) ⟨970197, by rfl⟩ : syracuseStep 2587193 = 1940395) B1940395
theorem B4364887 : Blo 1723062 4364887 := bstep (se 1 (by rfl) ⟨3273665, by rfl⟩ : syracuseStep 4364887 = 6547331) B6547331
theorem B2587271 : Blo 1723062 2587271 := bstep (se 1 (by rfl) ⟨1940453, by rfl⟩ : syracuseStep 2587271 = 3880907) B3880907
theorem B2587307 : Blo 1723062 2587307 := bstep (se 1 (by rfl) ⟨1940480, by rfl⟩ : syracuseStep 2587307 = 3880961) B3880961
theorem B2587337 : Blo 1723062 2587337 := bstep (se 2 (by rfl) ⟨970251, by rfl⟩ : syracuseStep 2587337 = 1940503) B1940503
theorem B23911183 : Blo 1723062 23911183 := bstep (se 1 (by rfl) ⟨17933387, by rfl⟩ : syracuseStep 23911183 = 35866775) B35866775
theorem B4143887 : Blo 1723062 4143887 := bstep (se 1 (by rfl) ⟨3107915, by rfl⟩ : syracuseStep 4143887 = 6215831) B6215831
theorem B2587451 : Blo 1723062 2587451 := bstep (se 1 (by rfl) ⟨1940588, by rfl⟩ : syracuseStep 2587451 = 3881177) B3881177
theorem B2587511 : Blo 1723062 2587511 := bstep (se 1 (by rfl) ⟨1940633, by rfl⟩ : syracuseStep 2587511 = 3881267) B3881267
theorem B4365191 : Blo 1723062 4365191 := bstep (se 1 (by rfl) ⟨3273893, by rfl⟩ : syracuseStep 4365191 = 6547787) B6547787
theorem B1940359 : Blo 1723062 1940359 := bstep (se 1 (by rfl) ⟨1455269, by rfl⟩ : syracuseStep 1940359 = 2910539) B2910539
theorem B2587535 : Blo 1723062 2587535 := bstep (se 1 (by rfl) ⟨1940651, by rfl⟩ : syracuseStep 2587535 = 3881303) B3881303
theorem B2587577 : Blo 1723062 2587577 := bstep (se 2 (by rfl) ⟨970341, by rfl⟩ : syracuseStep 2587577 = 1940683) B1940683
theorem B2071559 : Blo 1723062 2071559 := bstep (se 1 (by rfl) ⟨1553669, by rfl⟩ : syracuseStep 2071559 = 3107339) B3107339
theorem B4365323 : Blo 1723062 4365323 := bstep (se 1 (by rfl) ⟨3273992, by rfl⟩ : syracuseStep 4365323 = 6547985) B6547985
theorem B1940539 : Blo 1723062 1940539 := bstep (se 1 (by rfl) ⟨1455404, by rfl⟩ : syracuseStep 1940539 = 2910809) B2910809
theorem B15735869 : Blo 1723062 15735869 := bstep (se 3 (by rfl) ⟨2950475, by rfl⟩ : syracuseStep 15735869 = 5900951) B5900951
theorem B13098185 : Blo 1723062 13098185 := bstep (se 2 (by rfl) ⟨4911819, by rfl⟩ : syracuseStep 13098185 = 9823639) B9823639
theorem B2071867 : Blo 1723062 2071867 := bstep (se 1 (by rfl) ⟨1553900, by rfl⟩ : syracuseStep 2071867 = 3107801) B3107801
theorem B9813433 : Blo 1723062 9813433 := bstep (se 2 (by rfl) ⟨3680037, by rfl⟩ : syracuseStep 9813433 = 7360075) B7360075
theorem B6634937 : Blo 1723062 6634937 := bstep (se 2 (by rfl) ⟨2488101, by rfl⟩ : syracuseStep 6634937 = 4976203) B4976203
theorem B8281547 : Blo 1723062 8281547 := bstep (se 1 (by rfl) ⟨6211160, by rfl⟩ : syracuseStep 8281547 = 12422321) B12422321
theorem B136158691 : Blo 1723062 136158691 := bstep (se 1 (by rfl) ⟨102119018, by rfl⟩ : syracuseStep 136158691 = 204238037) B204238037
theorem B4365839 : Blo 1723062 4365839 := bstep (se 1 (by rfl) ⟨3274379, by rfl⟩ : syracuseStep 4365839 = 6548759) B6548759
theorem B2760311 : Blo 1723062 2760311 := bstep (se 1 (by rfl) ⟨2070233, by rfl⟩ : syracuseStep 2760311 = 4140467) B4140467
theorem B4365971 : Blo 1723062 4365971 := bstep (se 1 (by rfl) ⟨3274478, by rfl⟩ : syracuseStep 4365971 = 6548957) B6548957
theorem B7364297 : Blo 1723062 7364297 := bstep (se 2 (by rfl) ⟨2761611, by rfl⟩ : syracuseStep 7364297 = 5523223) B5523223
theorem B15728357 : Blo 1723062 15728357 := bstep (se 4 (by rfl) ⟨1474533, by rfl⟩ : syracuseStep 15728357 = 2949067) B2949067
theorem B4906763 : Blo 1723062 4906763 := bstep (se 1 (by rfl) ⟨3680072, by rfl⟩ : syracuseStep 4906763 = 7360145) B7360145
theorem B15138575 : Blo 1723062 15138575 := bstep (se 1 (by rfl) ⟨11353931, by rfl⟩ : syracuseStep 15138575 = 22707863) B22707863
theorem B2907947 : Blo 1723062 2907947 := bstep (se 1 (by rfl) ⟨2180960, by rfl⟩ : syracuseStep 2907947 = 4361921) B4361921
theorem B5816123 : Blo 1723062 5816123 := bstep (se 1 (by rfl) ⟨4362092, by rfl⟩ : syracuseStep 5816123 = 8724185) B8724185
theorem B11198411 : Blo 1723062 11198411 := bstep (se 1 (by rfl) ⟨8398808, by rfl⟩ : syracuseStep 11198411 = 16797617) B16797617
theorem B10485713 : Blo 1723062 10485713 := bstep (se 2 (by rfl) ⟨3932142, by rfl⟩ : syracuseStep 10485713 = 7864285) B7864285
theorem B11042831 : Blo 1723062 11042831 := bstep (se 1 (by rfl) ⟨8282123, by rfl⟩ : syracuseStep 11042831 = 16564247) B16564247
theorem B5816339 : Blo 1723062 5816339 := bstep (se 1 (by rfl) ⟨4362254, by rfl⟩ : syracuseStep 5816339 = 8724509) B8724509
theorem B2908217 : Blo 1723062 2908217 := bstep (se 2 (by rfl) ⟨1090581, by rfl⟩ : syracuseStep 2908217 = 2181163) B2181163
theorem B15728717 : Blo 1723062 15728717 := bstep (se 3 (by rfl) ⟨2949134, by rfl⟩ : syracuseStep 15728717 = 5898269) B5898269
theorem B2760875 : Blo 1723062 2760875 := bstep (se 1 (by rfl) ⟨2070656, by rfl⟩ : syracuseStep 2760875 = 4141313) B4141313
theorem B4366507 : Blo 1723062 4366507 := bstep (se 1 (by rfl) ⟨3274880, by rfl⟩ : syracuseStep 4366507 = 6549761) B6549761
theorem B5816663 : Blo 1723062 5816663 := bstep (se 1 (by rfl) ⟨4362497, by rfl⟩ : syracuseStep 5816663 = 8724995) B8724995
theorem B3105119 : Blo 1723062 3105119 := bstep (se 1 (by rfl) ⟨2328839, by rfl⟩ : syracuseStep 3105119 = 4657679) B4657679
theorem B2761067 : Blo 1723062 2761067 := bstep (se 1 (by rfl) ⟨2070800, by rfl⟩ : syracuseStep 2761067 = 4141601) B4141601
theorem B7864705 : Blo 1723062 7864705 := bstep (se 2 (by rfl) ⟨2949264, by rfl⟩ : syracuseStep 7864705 = 5898529) B5898529
theorem B6546055 : Blo 1723062 6546055 := bstep (se 1 (by rfl) ⟨4909541, by rfl⟩ : syracuseStep 6546055 = 9819083) B9819083
theorem B5595787 : Blo 1723062 5595787 := bstep (se 1 (by rfl) ⟨4196840, by rfl⟩ : syracuseStep 5595787 = 8393681) B8393681
theorem B4907719 : Blo 1723062 4907719 := bstep (se 1 (by rfl) ⟨3680789, by rfl⟩ : syracuseStep 4907719 = 7361579) B7361579
theorem B2908919 : Blo 1723062 2908919 := bstep (se 1 (by rfl) ⟨2181689, by rfl⟩ : syracuseStep 2908919 = 4363379) B4363379
theorem B9814891 : Blo 1723062 9814891 := bstep (se 1 (by rfl) ⟨7361168, by rfl⟩ : syracuseStep 9814891 = 14722337) B14722337
theorem B1936860083 : Blo 1723062 1936860083 := bstep (se 1 (by rfl) ⟨1452645062, by rfl⟩ : syracuseStep 1936860083 = 2905290125) B2905290125
theorem B6546359 : Blo 1723062 6546359 := bstep (se 1 (by rfl) ⟨4909769, by rfl⟩ : syracuseStep 6546359 = 9819539) B9819539
theorem B3105811 : Blo 1723062 3105811 := bstep (se 1 (by rfl) ⟨2329358, by rfl⟩ : syracuseStep 3105811 = 4658717) B4658717
theorem B2909263 : Blo 1723062 2909263 := bstep (se 1 (by rfl) ⟨2181947, by rfl⟩ : syracuseStep 2909263 = 4363895) B4363895
theorem B3106121 : Blo 1723062 3106121 := bstep (se 2 (by rfl) ⟨1164795, by rfl⟩ : syracuseStep 3106121 = 2329591) B2329591
theorem B2909513 : Blo 1723062 2909513 := bstep (se 2 (by rfl) ⟨1091067, by rfl⟩ : syracuseStep 2909513 = 2182135) B2182135
theorem B5522813 : Blo 1723062 5522813 := bstep (se 3 (by rfl) ⟨1035527, by rfl⟩ : syracuseStep 5522813 = 2071055) B2071055
theorem B5817743 : Blo 1723062 5817743 := bstep (se 1 (by rfl) ⟨4363307, by rfl⟩ : syracuseStep 5817743 = 8726615) B8726615
theorem B127526309 : Blo 1723062 127526309 := bstep (se 4 (by rfl) ⟨11955591, by rfl⟩ : syracuseStep 127526309 = 23911183) B23911183
theorem B16565705 : Blo 1723062 16565705 := bstep (se 2 (by rfl) ⟨6212139, by rfl⟩ : syracuseStep 16565705 = 12424279) B12424279
theorem B24864245 : Blo 1723062 24864245 := bstep (se 5 (by rfl) ⟨1165511, by rfl⟩ : syracuseStep 24864245 = 2331023) B2331023
theorem B3319315 : Blo 1723062 3319315 := bstep (se 1 (by rfl) ⟨2489486, by rfl⟩ : syracuseStep 3319315 = 4978973) B4978973
theorem B6301223 : Blo 1723062 6301223 := bstep (se 1 (by rfl) ⟨4725917, by rfl⟩ : syracuseStep 6301223 = 9451835) B9451835
theorem B5818067 : Blo 1723062 5818067 := bstep (se 1 (by rfl) ⟨4363550, by rfl⟩ : syracuseStep 5818067 = 8727101) B8727101
theorem B2909945 : Blo 1723062 2909945 := bstep (se 2 (by rfl) ⟨1091229, by rfl⟩ : syracuseStep 2909945 = 2182459) B2182459
theorem B2762489 : Blo 1723062 2762489 := bstep (se 2 (by rfl) ⟨1035933, by rfl⟩ : syracuseStep 2762489 = 2071867) B2071867
theorem B2762591 : Blo 1723062 2762591 := bstep (se 1 (by rfl) ⟨2071943, by rfl⟩ : syracuseStep 2762591 = 4143887) B4143887
theorem B13084577 : Blo 1723062 13084577 := bstep (se 2 (by rfl) ⟨4906716, by rfl⟩ : syracuseStep 13084577 = 9813433) B9813433
theorem B2910127 : Blo 1723062 2910127 := bstep (se 1 (by rfl) ⟨2182595, by rfl⟩ : syracuseStep 2910127 = 4365191) B4365191
theorem B181544921 : Blo 1723062 181544921 := bstep (se 2 (by rfl) ⟨68079345, by rfl⟩ : syracuseStep 181544921 = 136158691) B136158691
theorem B2910215 : Blo 1723062 2910215 := bstep (se 1 (by rfl) ⟨2182661, by rfl⟩ : syracuseStep 2910215 = 4365323) B4365323
theorem B6547513 : Blo 1723062 6547513 := bstep (se 2 (by rfl) ⟨2455317, by rfl⟩ : syracuseStep 6547513 = 4910635) B4910635
theorem B2910559 : Blo 1723062 2910559 := bstep (se 1 (by rfl) ⟨2182919, by rfl⟩ : syracuseStep 2910559 = 4365839) B4365839
theorem B6547817 : Blo 1723062 6547817 := bstep (se 2 (by rfl) ⟨2455431, by rfl⟩ : syracuseStep 6547817 = 4910863) B4910863
theorem B2910647 : Blo 1723062 2910647 := bstep (se 1 (by rfl) ⟨2182985, by rfl⟩ : syracuseStep 2910647 = 4365971) B4365971
theorem B327125465 : Blo 1723062 327125465 := bstep (se 2 (by rfl) ⟨122672049, by rfl⟩ : syracuseStep 327125465 = 245344099) B245344099
theorem B4909531 : Blo 1723062 4909531 := bstep (se 1 (by rfl) ⟨3682148, by rfl⟩ : syracuseStep 4909531 = 7364297) B7364297
theorem B3271175 : Blo 1723062 3271175 := bstep (se 1 (by rfl) ⟨2453381, by rfl⟩ : syracuseStep 3271175 = 4906763) B4906763
theorem B3877415 : Blo 1723062 3877415 := bstep (se 1 (by rfl) ⟨2908061, by rfl⟩ : syracuseStep 3877415 = 5816123) B5816123
theorem B2181755 : Blo 1723062 2181755 := bstep (se 1 (by rfl) ⟨1636316, by rfl⟩ : syracuseStep 2181755 = 3272633) B3272633
theorem B7465607 : Blo 1723062 7465607 := bstep (se 1 (by rfl) ⟨5599205, by rfl⟩ : syracuseStep 7465607 = 11198411) B11198411
theorem B6990475 : Blo 1723062 6990475 := bstep (se 1 (by rfl) ⟨5242856, by rfl⟩ : syracuseStep 6990475 = 10485713) B10485713
theorem B5524157 : Blo 1723062 5524157 := bstep (se 3 (by rfl) ⟨1035779, by rfl⟩ : syracuseStep 5524157 = 2071559) B2071559
theorem B1723079 : Blo 1723062 1723079 := bstep (se 1 (by rfl) ⟨1292309, by rfl⟩ : syracuseStep 1723079 = 2584619) B2584619
theorem B1723099 : Blo 1723062 1723099 := bstep (se 1 (by rfl) ⟨1292324, by rfl⟩ : syracuseStep 1723099 = 2584649) B2584649
theorem B1723175 : Blo 1723062 1723175 := bstep (se 1 (by rfl) ⟨1292381, by rfl⟩ : syracuseStep 1723175 = 2584763) B2584763
theorem B1723215 : Blo 1723062 1723215 := bstep (se 1 (by rfl) ⟨1292411, by rfl⟩ : syracuseStep 1723215 = 2584823) B2584823
theorem B1723231 : Blo 1723062 1723231 := bstep (se 1 (by rfl) ⟨1292423, by rfl⟩ : syracuseStep 1723231 = 2584847) B2584847
theorem B262015843 : Blo 1723062 262015843 := bstep (se 1 (by rfl) ⟨196511882, by rfl⟩ : syracuseStep 262015843 = 393023765) B393023765
theorem B3877739 : Blo 1723062 3877739 := bstep (se 1 (by rfl) ⟨2908304, by rfl⟩ : syracuseStep 3877739 = 5816609) B5816609
theorem B3681131 : Blo 1723062 3681131 := bstep (se 1 (by rfl) ⟨2760848, by rfl⟩ : syracuseStep 3681131 = 5521697) B5521697
theorem B5819255 : Blo 1723062 5819255 := bstep (se 1 (by rfl) ⟨4364441, by rfl⟩ : syracuseStep 5819255 = 8728883) B8728883
theorem B1723259 : Blo 1723062 1723259 := bstep (se 1 (by rfl) ⟨1292444, by rfl⟩ : syracuseStep 1723259 = 2584889) B2584889
theorem B3271585 : Blo 1723062 3271585 := bstep (se 2 (by rfl) ⟨1226844, by rfl⟩ : syracuseStep 3271585 = 2453689) B2453689
theorem B3877793 : Blo 1723062 3877793 := bstep (se 2 (by rfl) ⟨1454172, by rfl⟩ : syracuseStep 3877793 = 2908345) B2908345
theorem B1723311 : Blo 1723062 1723311 := bstep (se 1 (by rfl) ⟨1292483, by rfl⟩ : syracuseStep 1723311 = 2584967) B2584967
theorem B1723335 : Blo 1723062 1723335 := bstep (se 1 (by rfl) ⟨1292501, by rfl⟩ : syracuseStep 1723335 = 2585003) B2585003
theorem B1723355 : Blo 1723062 1723355 := bstep (se 1 (by rfl) ⟨1292516, by rfl⟩ : syracuseStep 1723355 = 2585033) B2585033
theorem B12594149 : Blo 1723062 12594149 := bstep (se 4 (by rfl) ⟨1180701, by rfl⟩ : syracuseStep 12594149 = 2361403) B2361403
theorem B1723431 : Blo 1723062 1723431 := bstep (se 1 (by rfl) ⟨1292573, by rfl⟩ : syracuseStep 1723431 = 2585147) B2585147
theorem B1723471 : Blo 1723062 1723471 := bstep (se 1 (by rfl) ⟨1292603, by rfl⟩ : syracuseStep 1723471 = 2585207) B2585207
theorem B5819471 : Blo 1723062 5819471 := bstep (se 1 (by rfl) ⟨4364603, by rfl⟩ : syracuseStep 5819471 = 8729207) B8729207
theorem B1723487 : Blo 1723062 1723487 := bstep (se 1 (by rfl) ⟨1292615, by rfl⟩ : syracuseStep 1723487 = 2585231) B2585231
theorem B5524595 : Blo 1723062 5524595 := bstep (se 1 (by rfl) ⟨4143446, by rfl⟩ : syracuseStep 5524595 = 8286893) B8286893
theorem B1723515 : Blo 1723062 1723515 := bstep (se 1 (by rfl) ⟨1292636, by rfl⟩ : syracuseStep 1723515 = 2585273) B2585273
theorem B1723567 : Blo 1723062 1723567 := bstep (se 1 (by rfl) ⟨1292675, by rfl⟩ : syracuseStep 1723567 = 2585351) B2585351
theorem B27954371 : Blo 1723062 27954371 := bstep (se 1 (by rfl) ⟨20965778, by rfl⟩ : syracuseStep 27954371 = 41931557) B41931557
theorem B1723591 : Blo 1723062 1723591 := bstep (se 1 (by rfl) ⟨1292693, by rfl⟩ : syracuseStep 1723591 = 2585387) B2585387
theorem B1723611 : Blo 1723062 1723611 := bstep (se 1 (by rfl) ⟨1292708, by rfl⟩ : syracuseStep 1723611 = 2585417) B2585417
theorem B3271927 : Blo 1723062 3271927 := bstep (se 1 (by rfl) ⟨2453945, by rfl⟩ : syracuseStep 3271927 = 4907891) B4907891
theorem B3878135 : Blo 1723062 3878135 := bstep (se 1 (by rfl) ⟨2908601, by rfl⟩ : syracuseStep 3878135 = 5817203) B5817203
theorem B1723687 : Blo 1723062 1723687 := bstep (se 1 (by rfl) ⟨1292765, by rfl⟩ : syracuseStep 1723687 = 2585531) B2585531
theorem B1723727 : Blo 1723062 1723727 := bstep (se 1 (by rfl) ⟨1292795, by rfl⟩ : syracuseStep 1723727 = 2585591) B2585591
theorem B1723743 : Blo 1723062 1723743 := bstep (se 1 (by rfl) ⟨1292807, by rfl⟩ : syracuseStep 1723743 = 2585615) B2585615
theorem B1723771 : Blo 1723062 1723771 := bstep (se 1 (by rfl) ⟨1292828, by rfl⟩ : syracuseStep 1723771 = 2585657) B2585657
theorem B14929295 : Blo 1723062 14929295 := bstep (se 1 (by rfl) ⟨11196971, by rfl⟩ : syracuseStep 14929295 = 22393943) B22393943
theorem B1723823 : Blo 1723062 1723823 := bstep (se 1 (by rfl) ⟨1292867, by rfl⟩ : syracuseStep 1723823 = 2585735) B2585735
theorem B1723847 : Blo 1723062 1723847 := bstep (se 1 (by rfl) ⟨1292885, by rfl⟩ : syracuseStep 1723847 = 2585771) B2585771
theorem B5819849 : Blo 1723062 5819849 := bstep (se 2 (by rfl) ⟨2182443, by rfl⟩ : syracuseStep 5819849 = 4364887) B4364887
theorem B1723867 : Blo 1723062 1723867 := bstep (se 1 (by rfl) ⟨1292900, by rfl⟩ : syracuseStep 1723867 = 2585801) B2585801
theorem B3272231 : Blo 1723062 3272231 := bstep (se 1 (by rfl) ⟨2454173, by rfl⟩ : syracuseStep 3272231 = 4908347) B4908347
theorem B1723943 : Blo 1723062 1723943 := bstep (se 1 (by rfl) ⟨1292957, by rfl⟩ : syracuseStep 1723943 = 2585915) B2585915
theorem B6213179 : Blo 1723062 6213179 := bstep (se 1 (by rfl) ⟨4659884, by rfl⟩ : syracuseStep 6213179 = 9319769) B9319769
theorem B1723983 : Blo 1723062 1723983 := bstep (se 1 (by rfl) ⟨1292987, by rfl⟩ : syracuseStep 1723983 = 2585975) B2585975
theorem B1723999 : Blo 1723062 1723999 := bstep (se 1 (by rfl) ⟨1292999, by rfl⟩ : syracuseStep 1723999 = 2585999) B2585999
theorem B1724027 : Blo 1723062 1724027 := bstep (se 1 (by rfl) ⟨1293020, by rfl⟩ : syracuseStep 1724027 = 2586041) B2586041
theorem B1724079 : Blo 1723062 1724079 := bstep (se 1 (by rfl) ⟨1293059, by rfl⟩ : syracuseStep 1724079 = 2586119) B2586119
theorem B1724103 : Blo 1723062 1724103 := bstep (se 1 (by rfl) ⟨1293077, by rfl⟩ : syracuseStep 1724103 = 2586155) B2586155
theorem B5820119 : Blo 1723062 5820119 := bstep (se 1 (by rfl) ⟨4365089, by rfl⟩ : syracuseStep 5820119 = 8730179) B8730179
theorem B4910807 : Blo 1723062 4910807 := bstep (se 1 (by rfl) ⟨3683105, by rfl⟩ : syracuseStep 4910807 = 7366211) B7366211
theorem B1724123 : Blo 1723062 1724123 := bstep (se 1 (by rfl) ⟨1293092, by rfl⟩ : syracuseStep 1724123 = 2586185) B2586185
theorem B1724199 : Blo 1723062 1724199 := bstep (se 1 (by rfl) ⟨1293149, by rfl⟩ : syracuseStep 1724199 = 2586299) B2586299
theorem B3878729 : Blo 1723062 3878729 := bstep (se 2 (by rfl) ⟨1454523, by rfl⟩ : syracuseStep 3878729 = 2909047) B2909047
theorem B1724239 : Blo 1723062 1724239 := bstep (se 1 (by rfl) ⟨1293179, by rfl⟩ : syracuseStep 1724239 = 2586359) B2586359
theorem B1724255 : Blo 1723062 1724255 := bstep (se 1 (by rfl) ⟨1293191, by rfl⟩ : syracuseStep 1724255 = 2586383) B2586383
theorem B2330473 : Blo 1723062 2330473 := bstep (se 2 (by rfl) ⟨873927, by rfl⟩ : syracuseStep 2330473 = 1747855) B1747855
theorem B1724283 : Blo 1723062 1724283 := bstep (se 1 (by rfl) ⟨1293212, by rfl⟩ : syracuseStep 1724283 = 2586425) B2586425
theorem B1724335 : Blo 1723062 1724335 := bstep (se 1 (by rfl) ⟨1293251, by rfl⟩ : syracuseStep 1724335 = 2586503) B2586503
theorem B5820335 : Blo 1723062 5820335 := bstep (se 1 (by rfl) ⟨4365251, by rfl⟩ : syracuseStep 5820335 = 8730503) B8730503
theorem B4911023 : Blo 1723062 4911023 := bstep (se 1 (by rfl) ⟨3683267, by rfl⟩ : syracuseStep 4911023 = 7366535) B7366535
theorem B1724359 : Blo 1723062 1724359 := bstep (se 1 (by rfl) ⟨1293269, by rfl⟩ : syracuseStep 1724359 = 2586539) B2586539
theorem B1724379 : Blo 1723062 1724379 := bstep (se 1 (by rfl) ⟨1293284, by rfl⟩ : syracuseStep 1724379 = 2586569) B2586569
theorem B7860239 : Blo 1723062 7860239 := bstep (se 1 (by rfl) ⟨5895179, by rfl⟩ : syracuseStep 7860239 = 11790359) B11790359
theorem B1724455 : Blo 1723062 1724455 := bstep (se 1 (by rfl) ⟨1293341, by rfl⟩ : syracuseStep 1724455 = 2586683) B2586683
theorem B2584655 : Blo 1723062 2584655 := bstep (se 1 (by rfl) ⟨1938491, by rfl⟩ : syracuseStep 2584655 = 3876983) B3876983
theorem B1724495 : Blo 1723062 1724495 := bstep (se 1 (by rfl) ⟨1293371, by rfl⟩ : syracuseStep 1724495 = 2586743) B2586743
theorem B1724511 : Blo 1723062 1724511 := bstep (se 1 (by rfl) ⟨1293383, by rfl⟩ : syracuseStep 1724511 = 2586767) B2586767
theorem B1724539 : Blo 1723062 1724539 := bstep (se 1 (by rfl) ⟨1293404, by rfl⟩ : syracuseStep 1724539 = 2586809) B2586809
theorem B9318557 : Blo 1723062 9318557 := bstep (se 3 (by rfl) ⟨1747229, by rfl⟩ : syracuseStep 9318557 = 3494459) B3494459
theorem B1724591 : Blo 1723062 1724591 := bstep (se 1 (by rfl) ⟨1293443, by rfl⟩ : syracuseStep 1724591 = 2586887) B2586887
theorem B66252977 : Blo 1723062 66252977 := bstep (se 2 (by rfl) ⟨24844866, by rfl⟩ : syracuseStep 66252977 = 49689733) B49689733
theorem B29454515 : Blo 1723062 29454515 := bstep (se 1 (by rfl) ⟨22090886, by rfl⟩ : syracuseStep 29454515 = 44181773) B44181773
theorem B2584775 : Blo 1723062 2584775 := bstep (se 1 (by rfl) ⟨1938581, by rfl⟩ : syracuseStep 2584775 = 3877163) B3877163
theorem B1724615 : Blo 1723062 1724615 := bstep (se 1 (by rfl) ⟨1293461, by rfl⟩ : syracuseStep 1724615 = 2586923) B2586923
theorem B1724635 : Blo 1723062 1724635 := bstep (se 1 (by rfl) ⟨1293476, by rfl⟩ : syracuseStep 1724635 = 2586953) B2586953
theorem B1724711 : Blo 1723062 1724711 := bstep (se 1 (by rfl) ⟨1293533, by rfl⟩ : syracuseStep 1724711 = 2587067) B2587067
theorem B1724751 : Blo 1723062 1724751 := bstep (se 1 (by rfl) ⟨1293563, by rfl⟩ : syracuseStep 1724751 = 2587127) B2587127
theorem B3461471 : Blo 1723062 3461471 := bstep (se 1 (by rfl) ⟨2596103, by rfl⟩ : syracuseStep 3461471 = 5192207) B5192207
theorem B2330975 : Blo 1723062 2330975 := bstep (se 1 (by rfl) ⟨1748231, by rfl⟩ : syracuseStep 2330975 = 3496463) B3496463
theorem B1724767 : Blo 1723062 1724767 := bstep (se 1 (by rfl) ⟨1293575, by rfl⟩ : syracuseStep 1724767 = 2587151) B2587151
theorem B2584937 : Blo 1723062 2584937 := bstep (se 2 (by rfl) ⟨969351, by rfl⟩ : syracuseStep 2584937 = 1938703) B1938703
theorem B1724795 : Blo 1723062 1724795 := bstep (se 1 (by rfl) ⟨1293596, by rfl⟩ : syracuseStep 1724795 = 2587193) B2587193
theorem B3682703 : Blo 1723062 3682703 := bstep (se 1 (by rfl) ⟨2762027, by rfl⟩ : syracuseStep 3682703 = 5524055) B5524055
theorem B1724847 : Blo 1723062 1724847 := bstep (se 1 (by rfl) ⟨1293635, by rfl⟩ : syracuseStep 1724847 = 2587271) B2587271
theorem B2585015 : Blo 1723062 2585015 := bstep (se 1 (by rfl) ⟨1938761, by rfl⟩ : syracuseStep 2585015 = 3877523) B3877523
theorem B1724871 : Blo 1723062 1724871 := bstep (se 1 (by rfl) ⟨1293653, by rfl⟩ : syracuseStep 1724871 = 2587307) B2587307
theorem B2585051 : Blo 1723062 2585051 := bstep (se 1 (by rfl) ⟨1938788, by rfl⟩ : syracuseStep 2585051 = 3877577) B3877577
theorem B1724891 : Blo 1723062 1724891 := bstep (se 1 (by rfl) ⟨1293668, by rfl⟩ : syracuseStep 1724891 = 2587337) B2587337
theorem B33141251 : Blo 1723062 33141251 := bstep (se 1 (by rfl) ⟨24855938, by rfl⟩ : syracuseStep 33141251 = 49711877) B49711877
theorem B4362761 : Blo 1723062 4362761 := bstep (se 2 (by rfl) ⟨1636035, by rfl⟩ : syracuseStep 4362761 = 3272071) B3272071
theorem B1724967 : Blo 1723062 1724967 := bstep (se 1 (by rfl) ⟨1293725, by rfl⟩ : syracuseStep 1724967 = 2587451) B2587451
theorem B1725007 : Blo 1723062 1725007 := bstep (se 1 (by rfl) ⟨1293755, by rfl⟩ : syracuseStep 1725007 = 2587511) B2587511
theorem B3879521 : Blo 1723062 3879521 := bstep (se 2 (by rfl) ⟨1454820, by rfl⟩ : syracuseStep 3879521 = 2909641) B2909641
theorem B1725023 : Blo 1723062 1725023 := bstep (se 1 (by rfl) ⟨1293767, by rfl⟩ : syracuseStep 1725023 = 2587535) B2587535
theorem B1725051 : Blo 1723062 1725051 := bstep (se 1 (by rfl) ⟨1293788, by rfl⟩ : syracuseStep 1725051 = 2587577) B2587577
theorem B10490579 : Blo 1723062 10490579 := bstep (se 1 (by rfl) ⟨7867934, by rfl⟩ : syracuseStep 10490579 = 15735869) B15735869
theorem B14725961 : Blo 1723062 14725961 := bstep (se 2 (by rfl) ⟨5522235, by rfl⟩ : syracuseStep 14725961 = 11044471) B11044471
theorem B2585519 : Blo 1723062 2585519 := bstep (se 1 (by rfl) ⟨1939139, by rfl⟩ : syracuseStep 2585519 = 3878279) B3878279
theorem B3879863 : Blo 1723062 3879863 := bstep (se 1 (by rfl) ⟨2909897, by rfl⟩ : syracuseStep 3879863 = 5819795) B5819795
theorem B2585609 : Blo 1723062 2585609 := bstep (se 2 (by rfl) ⟨969603, by rfl⟩ : syracuseStep 2585609 = 1939207) B1939207
theorem B2585639 : Blo 1723062 2585639 := bstep (se 1 (by rfl) ⟨1939229, by rfl⟩ : syracuseStep 2585639 = 3878459) B3878459
theorem B5239865 : Blo 1723062 5239865 := bstep (se 2 (by rfl) ⟨1964949, by rfl⟩ : syracuseStep 5239865 = 3929899) B3929899
theorem B1840207 : Blo 1723062 1840207 := bstep (se 1 (by rfl) ⟨1380155, by rfl⟩ : syracuseStep 1840207 = 2760311) B2760311
theorem B2585723 : Blo 1723062 2585723 := bstep (se 1 (by rfl) ⟨1939292, by rfl⟩ : syracuseStep 2585723 = 3878585) B3878585
theorem B1938631 : Blo 1723062 1938631 := bstep (se 1 (by rfl) ⟨1453973, by rfl⟩ : syracuseStep 1938631 = 2907947) B2907947
theorem B2585849 : Blo 1723062 2585849 := bstep (se 2 (by rfl) ⟨969693, by rfl⟩ : syracuseStep 2585849 = 1939387) B1939387
theorem B6542653 : Blo 1723062 6542653 := bstep (se 3 (by rfl) ⟨1226747, by rfl⟩ : syracuseStep 6542653 = 2453495) B2453495
theorem B2585951 : Blo 1723062 2585951 := bstep (se 1 (by rfl) ⟨1939463, by rfl⟩ : syracuseStep 2585951 = 3878927) B3878927
theorem B2585963 : Blo 1723062 2585963 := bstep (se 1 (by rfl) ⟨1939472, by rfl⟩ : syracuseStep 2585963 = 3878945) B3878945
theorem B3274091 : Blo 1723062 3274091 := bstep (se 1 (by rfl) ⟨2455568, by rfl⟩ : syracuseStep 3274091 = 4911137) B4911137
theorem B3880457 : Blo 1723062 3880457 := bstep (se 2 (by rfl) ⟨1455171, by rfl⟩ : syracuseStep 3880457 = 2910343) B2910343
theorem B22099499 : Blo 1723062 22099499 := bstep (se 1 (by rfl) ⟨16574624, by rfl⟩ : syracuseStep 22099499 = 33149249) B33149249
theorem B2586191 : Blo 1723062 2586191 := bstep (se 1 (by rfl) ⟨1939643, by rfl⟩ : syracuseStep 2586191 = 3879287) B3879287
theorem B3274319 : Blo 1723062 3274319 := bstep (se 1 (by rfl) ⟨2455739, by rfl⟩ : syracuseStep 3274319 = 4911479) B4911479
theorem B4363915 : Blo 1723062 4363915 := bstep (se 1 (by rfl) ⟨3272936, by rfl⟩ : syracuseStep 4363915 = 6545873) B6545873
theorem B2586311 : Blo 1723062 2586311 := bstep (se 1 (by rfl) ⟨1939733, by rfl⟩ : syracuseStep 2586311 = 3879467) B3879467
theorem B6821587 : Blo 1723062 6821587 := bstep (se 1 (by rfl) ⟨5116190, by rfl⟩ : syracuseStep 6821587 = 10232381) B10232381
theorem B16562015 : Blo 1723062 16562015 := bstep (se 1 (by rfl) ⟨12421511, by rfl⟩ : syracuseStep 16562015 = 24843023) B24843023
theorem B3880799 : Blo 1723062 3880799 := bstep (se 1 (by rfl) ⟨2910599, by rfl⟩ : syracuseStep 3880799 = 5821199) B5821199
theorem B2586473 : Blo 1723062 2586473 := bstep (se 2 (by rfl) ⟨969927, by rfl⟩ : syracuseStep 2586473 = 1939855) B1939855
theorem B3930017 : Blo 1723062 3930017 := bstep (se 2 (by rfl) ⟨1473756, by rfl⟩ : syracuseStep 3930017 = 2947513) B2947513
theorem B2586551 : Blo 1723062 2586551 := bstep (se 1 (by rfl) ⟨1939913, by rfl⟩ : syracuseStep 2586551 = 3879827) B3879827
theorem B6993847 : Blo 1723062 6993847 := bstep (se 1 (by rfl) ⟨5245385, by rfl⟩ : syracuseStep 6993847 = 10490771) B10490771
theorem B12433337 : Blo 1723062 12433337 := bstep (se 2 (by rfl) ⟨4662501, by rfl⟩ : syracuseStep 12433337 = 9325003) B9325003
theorem B4364219 : Blo 1723062 4364219 := bstep (se 1 (by rfl) ⟨3273164, by rfl⟩ : syracuseStep 4364219 = 6546329) B6546329
theorem B2586587 : Blo 1723062 2586587 := bstep (se 1 (by rfl) ⟨1939940, by rfl⟩ : syracuseStep 2586587 = 3879881) B3879881
theorem B3274759 : Blo 1723062 3274759 := bstep (se 1 (by rfl) ⟨2456069, by rfl⟩ : syracuseStep 3274759 = 4912139) B4912139
theorem B3880979 : Blo 1723062 3880979 := bstep (se 1 (by rfl) ⟨2910734, by rfl⟩ : syracuseStep 3880979 = 5821469) B5821469
theorem B13981733 : Blo 1723062 13981733 := bstep (se 4 (by rfl) ⟨1310787, by rfl⟩ : syracuseStep 13981733 = 2621575) B2621575
theorem B1939495 : Blo 1723062 1939495 := bstep (se 1 (by rfl) ⟨1454621, by rfl⟩ : syracuseStep 1939495 = 2909243) B2909243
theorem B2455591 : Blo 1723062 2455591 := bstep (se 1 (by rfl) ⟨1841693, by rfl⟩ : syracuseStep 2455591 = 3683387) B3683387
theorem B3930191 : Blo 1723062 3930191 := bstep (se 1 (by rfl) ⟨2947643, by rfl⟩ : syracuseStep 3930191 = 5895287) B5895287
theorem B3881321 : Blo 1723062 3881321 := bstep (se 2 (by rfl) ⟨1455495, by rfl⟩ : syracuseStep 3881321 = 2910991) B2910991
theorem B2587055 : Blo 1723062 2587055 := bstep (se 1 (by rfl) ⟨1940291, by rfl⟩ : syracuseStep 2587055 = 3880583) B3880583
theorem B2587145 : Blo 1723062 2587145 := bstep (se 2 (by rfl) ⟨970179, by rfl⟩ : syracuseStep 2587145 = 1940359) B1940359
theorem B2587175 : Blo 1723062 2587175 := bstep (se 1 (by rfl) ⟨1940381, by rfl⟩ : syracuseStep 2587175 = 3880763) B3880763
theorem B22100525 : Blo 1723062 22100525 := bstep (se 3 (by rfl) ⟨4143848, by rfl⟩ : syracuseStep 22100525 = 8287697) B8287697
theorem B2587259 : Blo 1723062 2587259 := bstep (se 1 (by rfl) ⟨1940444, by rfl⟩ : syracuseStep 2587259 = 3880889) B3880889
theorem B13982381 : Blo 1723062 13982381 := bstep (se 3 (by rfl) ⟨2621696, by rfl⟩ : syracuseStep 13982381 = 5243393) B5243393
theorem B4364999 : Blo 1723062 4364999 := bstep (se 1 (by rfl) ⟨3273749, by rfl⟩ : syracuseStep 4364999 = 6547499) B6547499
theorem B4365049 : Blo 1723062 4365049 := bstep (se 2 (by rfl) ⟨1636893, by rfl⟩ : syracuseStep 4365049 = 3273787) B3273787
theorem B2587385 : Blo 1723062 2587385 := bstep (se 2 (by rfl) ⟨970269, by rfl⟩ : syracuseStep 2587385 = 1940539) B1940539
theorem B6986569 : Blo 1723062 6986569 := bstep (se 2 (by rfl) ⟨2619963, by rfl⟩ : syracuseStep 6986569 = 5239927) B5239927
theorem B2587487 : Blo 1723062 2587487 := bstep (se 1 (by rfl) ⟨1940615, by rfl⟩ : syracuseStep 2587487 = 3881231) B3881231
theorem B2587499 : Blo 1723062 2587499 := bstep (se 1 (by rfl) ⟨1940624, by rfl⟩ : syracuseStep 2587499 = 3881249) B3881249
theorem B13278097 : Blo 1723062 13278097 := bstep (se 2 (by rfl) ⟨4979286, by rfl⟩ : syracuseStep 13278097 = 9958573) B9958573
theorem B8723375 : Blo 1723062 8723375 := bstep (se 1 (by rfl) ⟨6542531, by rfl⟩ : syracuseStep 8723375 = 13085063) B13085063
theorem B6544385 : Blo 1723062 6544385 := bstep (se 2 (by rfl) ⟨2454144, by rfl⟩ : syracuseStep 6544385 = 4908289) B4908289
theorem B5897231 : Blo 1723062 5897231 := bstep (se 1 (by rfl) ⟨4422923, by rfl⟩ : syracuseStep 5897231 = 8845847) B8845847
theorem B12598291 : Blo 1723062 12598291 := bstep (se 1 (by rfl) ⟨9448718, by rfl⟩ : syracuseStep 12598291 = 18897437) B18897437
theorem B44194895 : Blo 1723062 44194895 := bstep (se 1 (by rfl) ⟨33146171, by rfl⟩ : syracuseStep 44194895 = 66292343) B66292343
theorem B6216857 : Blo 1723062 6216857 := bstep (se 2 (by rfl) ⟨2331321, by rfl⟩ : syracuseStep 6216857 = 4662643) B4662643
theorem B4365697 : Blo 1723062 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B8732123 : Blo 1723062 8732123 := bstep (se 1 (by rfl) ⟨6549092, by rfl⟩ : syracuseStep 8732123 = 13098185) B13098185
theorem B4423291 : Blo 1723062 4423291 := bstep (se 1 (by rfl) ⟨3317468, by rfl⟩ : syracuseStep 4423291 = 6634937) B6634937
theorem B5521031 : Blo 1723062 5521031 := bstep (se 1 (by rfl) ⟨4140773, by rfl⟩ : syracuseStep 5521031 = 8281547) B8281547
theorem B10485571 : Blo 1723062 10485571 := bstep (se 1 (by rfl) ⟨7864178, by rfl⟩ : syracuseStep 10485571 = 15728357) B15728357
theorem B10092383 : Blo 1723062 10092383 := bstep (se 1 (by rfl) ⟨7569287, by rfl⟩ : syracuseStep 10092383 = 15138575) B15138575
theorem B8732609 : Blo 1723062 8732609 := bstep (se 2 (by rfl) ⟨3274728, by rfl⟩ : syracuseStep 8732609 = 6549457) B6549457
theorem B4366345 : Blo 1723062 4366345 := bstep (se 2 (by rfl) ⟨1637379, by rfl⟩ : syracuseStep 4366345 = 3274759) B3274759
theorem B10485811 : Blo 1723062 10485811 := bstep (se 1 (by rfl) ⟨7864358, by rfl⟩ : syracuseStep 10485811 = 15728717) B15728717
theorem B19636343 : Blo 1723062 19636343 := bstep (se 1 (by rfl) ⟨14727257, by rfl⟩ : syracuseStep 19636343 = 29454515) B29454515
theorem B22094167 : Blo 1723062 22094167 := bstep (se 1 (by rfl) ⟨16570625, by rfl⟩ : syracuseStep 22094167 = 33141251) B33141251
theorem B2908507 : Blo 1723062 2908507 := bstep (se 1 (by rfl) ⟨2181380, by rfl⟩ : syracuseStep 2908507 = 4362761) B4362761
theorem B70812053 : Blo 1723062 70812053 := bstep (se 6 (by rfl) ⟨1659657, by rfl⟩ : syracuseStep 70812053 = 3319315) B3319315
theorem B10486273 : Blo 1723062 10486273 := bstep (se 2 (by rfl) ⟨3932352, by rfl⟩ : syracuseStep 10486273 = 7864705) B7864705
theorem B1291240055 : Blo 1723062 1291240055 := bstep (se 1 (by rfl) ⟨968430041, by rfl⟩ : syracuseStep 1291240055 = 1936860083) B1936860083
theorem B6546041 : Blo 1723062 6546041 := bstep (se 2 (by rfl) ⟨2454765, by rfl⟩ : syracuseStep 6546041 = 4909531) B4909531
theorem B29844197 : Blo 1723062 29844197 := bstep (se 4 (by rfl) ⟨2797893, by rfl⟩ : syracuseStep 29844197 = 5595787) B5595787
theorem B8282989 : Blo 1723062 8282989 := bstep (se 3 (by rfl) ⟨1553060, by rfl⟩ : syracuseStep 8282989 = 3106121) B3106121
theorem B85017539 : Blo 1723062 85017539 := bstep (se 1 (by rfl) ⟨63763154, by rfl⟩ : syracuseStep 85017539 = 127526309) B127526309
theorem B11043803 : Blo 1723062 11043803 := bstep (se 1 (by rfl) ⟨8282852, by rfl⟩ : syracuseStep 11043803 = 16565705) B16565705
theorem B29467637 : Blo 1723062 29467637 := bstep (se 5 (by rfl) ⟨1381295, by rfl⟩ : syracuseStep 29467637 = 2762591) B2762591
theorem B9315425 : Blo 1723062 9315425 := bstep (se 2 (by rfl) ⟨3493284, by rfl⟩ : syracuseStep 9315425 = 6986569) B6986569
theorem B2909479 : Blo 1723062 2909479 := bstep (se 1 (by rfl) ⟨2182109, by rfl⟩ : syracuseStep 2909479 = 4364219) B4364219
theorem B121029947 : Blo 1723062 121029947 := bstep (se 1 (by rfl) ⟨90772460, by rfl⟩ : syracuseStep 121029947 = 181544921) B181544921
theorem B159245813 : Blo 1723062 159245813 := bstep (se 5 (by rfl) ⟨7464647, by rfl⟩ : syracuseStep 159245813 = 14929295) B14929295
theorem B5818013 : Blo 1723062 5818013 := bstep (se 3 (by rfl) ⟨1090877, by rfl⟩ : syracuseStep 5818013 = 2181755) B2181755
theorem B2180783 : Blo 1723062 2180783 := bstep (se 1 (by rfl) ⟨1635587, by rfl⟩ : syracuseStep 2180783 = 3271175) B3271175
theorem B2909999 : Blo 1723062 2909999 := bstep (se 1 (by rfl) ⟨2182499, by rfl⟩ : syracuseStep 2909999 = 4364999) B4364999
theorem B14731085 : Blo 1723062 14731085 := bstep (se 3 (by rfl) ⟨2762078, by rfl⟩ : syracuseStep 14731085 = 5524157) B5524157
theorem B5818553 : Blo 1723062 5818553 := bstep (se 2 (by rfl) ⟨2181957, by rfl⟩ : syracuseStep 5818553 = 4363915) B4363915
theorem B9095449 : Blo 1723062 9095449 := bstep (se 2 (by rfl) ⟨3410793, by rfl⟩ : syracuseStep 9095449 = 6821587) B6821587
theorem B9816349 : Blo 1723062 9816349 := bstep (se 3 (by rfl) ⟨1840565, by rfl⟩ : syracuseStep 9816349 = 3681131) B3681131
theorem B2181487 : Blo 1723062 2181487 := bstep (se 1 (by rfl) ⟨1636115, by rfl⟩ : syracuseStep 2181487 = 3272231) B3272231
theorem B10480045 : Blo 1723062 10480045 := bstep (se 3 (by rfl) ⟨1965008, by rfl⟩ : syracuseStep 10480045 = 3930017) B3930017
theorem B3680687 : Blo 1723062 3680687 := bstep (se 1 (by rfl) ⟨2760515, by rfl⟩ : syracuseStep 3680687 = 5521031) B5521031
theorem B3107297 : Blo 1723062 3107297 := bstep (se 2 (by rfl) ⟨1165236, by rfl⟩ : syracuseStep 3107297 = 2330473) B2330473
theorem B6728255 : Blo 1723062 6728255 := bstep (se 1 (by rfl) ⟨5046191, by rfl⟩ : syracuseStep 6728255 = 10092383) B10092383
theorem B9325129 : Blo 1723062 9325129 := bstep (se 2 (by rfl) ⟨3496923, by rfl⟩ : syracuseStep 9325129 = 6993847) B6993847
theorem B3877559 : Blo 1723062 3877559 := bstep (se 1 (by rfl) ⟨2908169, by rfl⟩ : syracuseStep 3877559 = 5816339) B5816339
theorem B1723103 : Blo 1723062 1723103 := bstep (se 1 (by rfl) ⟨1292327, by rfl⟩ : syracuseStep 1723103 = 2584655) B2584655
theorem B6212371 : Blo 1723062 6212371 := bstep (se 1 (by rfl) ⟨4659278, by rfl⟩ : syracuseStep 6212371 = 9318557) B9318557
theorem B1723183 : Blo 1723062 1723183 := bstep (se 1 (by rfl) ⟨1292387, by rfl⟩ : syracuseStep 1723183 = 2584775) B2584775
theorem B3877775 : Blo 1723062 3877775 := bstep (se 1 (by rfl) ⟨2908331, by rfl⟩ : syracuseStep 3877775 = 5816663) B5816663
theorem B1723291 : Blo 1723062 1723291 := bstep (se 1 (by rfl) ⟨1292468, by rfl⟩ : syracuseStep 1723291 = 2584937) B2584937
theorem B1723343 : Blo 1723062 1723343 := bstep (se 1 (by rfl) ⟨1292507, by rfl⟩ : syracuseStep 1723343 = 2585015) B2585015
theorem B1723367 : Blo 1723062 1723367 := bstep (se 1 (by rfl) ⟨1292525, by rfl⟩ : syracuseStep 1723367 = 2585051) B2585051
theorem B9817307 : Blo 1723062 9817307 := bstep (se 1 (by rfl) ⟨7362980, by rfl⟩ : syracuseStep 9817307 = 14725961) B14725961
theorem B1723679 : Blo 1723062 1723679 := bstep (se 1 (by rfl) ⟨1292759, by rfl⟩ : syracuseStep 1723679 = 2585519) B2585519
theorem B1723739 : Blo 1723062 1723739 := bstep (se 1 (by rfl) ⟨1292804, by rfl⟩ : syracuseStep 1723739 = 2585609) B2585609
theorem B1723759 : Blo 1723062 1723759 := bstep (se 1 (by rfl) ⟨1292819, by rfl⟩ : syracuseStep 1723759 = 2585639) B2585639
theorem B3493243 : Blo 1723062 3493243 := bstep (se 1 (by rfl) ⟨2619932, by rfl⟩ : syracuseStep 3493243 = 5239865) B5239865
theorem B1723815 : Blo 1723062 1723815 := bstep (se 1 (by rfl) ⟨1292861, by rfl⟩ : syracuseStep 1723815 = 2585723) B2585723
theorem B1723899 : Blo 1723062 1723899 := bstep (se 1 (by rfl) ⟨1292924, by rfl⟩ : syracuseStep 1723899 = 2585849) B2585849
theorem B8728073 : Blo 1723062 8728073 := bstep (se 2 (by rfl) ⟨3273027, by rfl⟩ : syracuseStep 8728073 = 6546055) B6546055
theorem B1723967 : Blo 1723062 1723967 := bstep (se 1 (by rfl) ⟨1292975, by rfl⟩ : syracuseStep 1723967 = 2585951) B2585951
theorem B1723975 : Blo 1723062 1723975 := bstep (se 1 (by rfl) ⟨1292981, by rfl⟩ : syracuseStep 1723975 = 2585963) B2585963
theorem B2182727 : Blo 1723062 2182727 := bstep (se 1 (by rfl) ⟨1637045, by rfl⟩ : syracuseStep 2182727 = 3274091) B3274091
theorem B3681875 : Blo 1723062 3681875 := bstep (se 1 (by rfl) ⟨2761406, by rfl⟩ : syracuseStep 3681875 = 5522813) B5522813
theorem B3878495 : Blo 1723062 3878495 := bstep (se 1 (by rfl) ⟨2908871, by rfl⟩ : syracuseStep 3878495 = 5817743) B5817743
theorem B5820065 : Blo 1723062 5820065 := bstep (se 2 (by rfl) ⟨2182524, by rfl⟩ : syracuseStep 5820065 = 4365049) B4365049
theorem B16576163 : Blo 1723062 16576163 := bstep (se 1 (by rfl) ⟨12432122, by rfl⟩ : syracuseStep 16576163 = 24864245) B24864245
theorem B14732999 : Blo 1723062 14732999 := bstep (se 1 (by rfl) ⟨11049749, by rfl⟩ : syracuseStep 14732999 = 22099499) B22099499
theorem B1724127 : Blo 1723062 1724127 := bstep (se 1 (by rfl) ⟨1293095, by rfl⟩ : syracuseStep 1724127 = 2586191) B2586191
theorem B2182879 : Blo 1723062 2182879 := bstep (se 1 (by rfl) ⟨1637159, by rfl⟩ : syracuseStep 2182879 = 3274319) B3274319
theorem B1724207 : Blo 1723062 1724207 := bstep (se 1 (by rfl) ⟨1293155, by rfl⟩ : syracuseStep 1724207 = 2586311) B2586311
theorem B3878711 : Blo 1723062 3878711 := bstep (se 1 (by rfl) ⟨2909033, by rfl⟩ : syracuseStep 3878711 = 5818067) B5818067
theorem B13086521 : Blo 1723062 13086521 := bstep (se 2 (by rfl) ⟨4907445, by rfl⟩ : syracuseStep 13086521 = 9814891) B9814891
theorem B4362113 : Blo 1723062 4362113 := bstep (se 2 (by rfl) ⟨1635792, by rfl⟩ : syracuseStep 4362113 = 3271585) B3271585
theorem B1724315 : Blo 1723062 1724315 := bstep (se 1 (by rfl) ⟨1293236, by rfl⟩ : syracuseStep 1724315 = 2586473) B2586473
theorem B1724367 : Blo 1723062 1724367 := bstep (se 1 (by rfl) ⟨1293275, by rfl⟩ : syracuseStep 1724367 = 2586551) B2586551
theorem B1724391 : Blo 1723062 1724391 := bstep (se 1 (by rfl) ⟨1293293, by rfl⟩ : syracuseStep 1724391 = 2586587) B2586587
theorem B4141081 : Blo 1723062 4141081 := bstep (se 2 (by rfl) ⟨1552905, by rfl⟩ : syracuseStep 4141081 = 3105811) B3105811
theorem B16797721 : Blo 1723062 16797721 := bstep (se 2 (by rfl) ⟨6299145, by rfl⟩ : syracuseStep 16797721 = 12598291) B12598291
theorem B2453609 : Blo 1723062 2453609 := bstep (se 2 (by rfl) ⟨920103, by rfl⟩ : syracuseStep 2453609 = 1840207) B1840207
theorem B3879017 : Blo 1723062 3879017 := bstep (se 2 (by rfl) ⟨1454631, by rfl⟩ : syracuseStep 3879017 = 2909263) B2909263
theorem B2584841 : Blo 1723062 2584841 := bstep (se 2 (by rfl) ⟨969315, by rfl⟩ : syracuseStep 2584841 = 1938631) B1938631
theorem B1724703 : Blo 1723062 1724703 := bstep (se 1 (by rfl) ⟨1293527, by rfl⟩ : syracuseStep 1724703 = 2587055) B2587055
theorem B218083643 : Blo 1723062 218083643 := bstep (se 1 (by rfl) ⟨163562732, by rfl⟩ : syracuseStep 218083643 = 327125465) B327125465
theorem B4362569 : Blo 1723062 4362569 := bstep (se 2 (by rfl) ⟨1635963, by rfl⟩ : syracuseStep 4362569 = 3271927) B3271927
theorem B1724763 : Blo 1723062 1724763 := bstep (se 1 (by rfl) ⟨1293572, by rfl⟩ : syracuseStep 1724763 = 2587145) B2587145
theorem B2584943 : Blo 1723062 2584943 := bstep (se 1 (by rfl) ⟨1938707, by rfl⟩ : syracuseStep 2584943 = 3877415) B3877415
theorem B1724783 : Blo 1723062 1724783 := bstep (se 1 (by rfl) ⟨1293587, by rfl⟩ : syracuseStep 1724783 = 2587175) B2587175
theorem B14733683 : Blo 1723062 14733683 := bstep (se 1 (by rfl) ⟨11050262, by rfl⟩ : syracuseStep 14733683 = 22100525) B22100525
theorem B1724839 : Blo 1723062 1724839 := bstep (se 1 (by rfl) ⟨1293629, by rfl⟩ : syracuseStep 1724839 = 2587259) B2587259
theorem B4977071 : Blo 1723062 4977071 := bstep (se 1 (by rfl) ⟨3732803, by rfl⟩ : syracuseStep 4977071 = 7465607) B7465607
theorem B1724923 : Blo 1723062 1724923 := bstep (se 1 (by rfl) ⟨1293692, by rfl⟩ : syracuseStep 1724923 = 2587385) B2587385
theorem B5820929 : Blo 1723062 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B1724991 : Blo 1723062 1724991 := bstep (se 1 (by rfl) ⟨1293743, by rfl⟩ : syracuseStep 1724991 = 2587487) B2587487
theorem B2585159 : Blo 1723062 2585159 := bstep (se 1 (by rfl) ⟨1938869, by rfl⟩ : syracuseStep 2585159 = 3877739) B3877739
theorem B1724999 : Blo 1723062 1724999 := bstep (se 1 (by rfl) ⟨1293749, by rfl⟩ : syracuseStep 1724999 = 2587499) B2587499
theorem B3879503 : Blo 1723062 3879503 := bstep (se 1 (by rfl) ⟨2909627, by rfl⟩ : syracuseStep 3879503 = 5819255) B5819255
theorem B2585195 : Blo 1723062 2585195 := bstep (se 1 (by rfl) ⟨1938896, by rfl⟩ : syracuseStep 2585195 = 3877793) B3877793
theorem B4362923 : Blo 1723062 4362923 := bstep (se 1 (by rfl) ⟨3272192, by rfl⟩ : syracuseStep 4362923 = 6544385) B6544385
theorem B3879647 : Blo 1723062 3879647 := bstep (se 1 (by rfl) ⟨2909735, by rfl⟩ : syracuseStep 3879647 = 5819471) B5819471
theorem B29463263 : Blo 1723062 29463263 := bstep (se 1 (by rfl) ⟨22097447, by rfl⟩ : syracuseStep 29463263 = 44194895) B44194895
theorem B3683063 : Blo 1723062 3683063 := bstep (se 1 (by rfl) ⟨2762297, by rfl⟩ : syracuseStep 3683063 = 5524595) B5524595
theorem B70816517 : Blo 1723062 70816517 := bstep (se 4 (by rfl) ⟨6639048, by rfl⟩ : syracuseStep 70816517 = 13278097) B13278097
theorem B2585423 : Blo 1723062 2585423 := bstep (se 1 (by rfl) ⟨1939067, by rfl⟩ : syracuseStep 2585423 = 3878135) B3878135
theorem B3879899 : Blo 1723062 3879899 := bstep (se 1 (by rfl) ⟨2909924, by rfl⟩ : syracuseStep 3879899 = 5819849) B5819849
theorem B5821415 : Blo 1723062 5821415 := bstep (se 1 (by rfl) ⟨4366061, by rfl⟩ : syracuseStep 5821415 = 8732123) B8732123
theorem B4142119 : Blo 1723062 4142119 := bstep (se 1 (by rfl) ⟨3106589, by rfl⟩ : syracuseStep 4142119 = 6213179) B6213179
theorem B13980761 : Blo 1723062 13980761 := bstep (se 2 (by rfl) ⟨5242785, by rfl⟩ : syracuseStep 13980761 = 10485571) B10485571
theorem B3880079 : Blo 1723062 3880079 := bstep (se 1 (by rfl) ⟨2910059, by rfl⟩ : syracuseStep 3880079 = 5820119) B5820119
theorem B3273871 : Blo 1723062 3273871 := bstep (se 1 (by rfl) ⟨2455403, by rfl⟩ : syracuseStep 3273871 = 4910807) B4910807
theorem B2585819 : Blo 1723062 2585819 := bstep (se 1 (by rfl) ⟨1939364, by rfl⟩ : syracuseStep 2585819 = 3878729) B3878729
theorem B3880169 : Blo 1723062 3880169 := bstep (se 2 (by rfl) ⟨1455063, by rfl⟩ : syracuseStep 3880169 = 2910127) B2910127
theorem B3880223 : Blo 1723062 3880223 := bstep (se 1 (by rfl) ⟨2910167, by rfl⟩ : syracuseStep 3880223 = 5820335) B5820335
theorem B3274015 : Blo 1723062 3274015 := bstep (se 1 (by rfl) ⟨2455511, by rfl⟩ : syracuseStep 3274015 = 4911023) B4911023
theorem B5821739 : Blo 1723062 5821739 := bstep (se 1 (by rfl) ⟨4366304, by rfl⟩ : syracuseStep 5821739 = 8732609) B8732609
theorem B5240159 : Blo 1723062 5240159 := bstep (se 1 (by rfl) ⟨3930119, by rfl⟩ : syracuseStep 5240159 = 7860239) B7860239
theorem B7361887 : Blo 1723062 7361887 := bstep (se 1 (by rfl) ⟨5521415, by rfl⟩ : syracuseStep 7361887 = 11042831) B11042831
theorem B1938811 : Blo 1723062 1938811 := bstep (se 1 (by rfl) ⟨1454108, by rfl⟩ : syracuseStep 1938811 = 2908217) B2908217
theorem B2585993 : Blo 1723062 2585993 := bstep (se 2 (by rfl) ⟨969747, by rfl⟩ : syracuseStep 2585993 = 1939495) B1939495
theorem B3274121 : Blo 1723062 3274121 := bstep (se 2 (by rfl) ⟨1227795, by rfl⟩ : syracuseStep 3274121 = 2455591) B2455591
theorem B8730017 : Blo 1723062 8730017 := bstep (se 2 (by rfl) ⟨3273756, by rfl⟩ : syracuseStep 8730017 = 6547513) B6547513
theorem B1840583 : Blo 1723062 1840583 := bstep (se 1 (by rfl) ⟨1380437, by rfl⟩ : syracuseStep 1840583 = 2760875) B2760875
theorem B44168651 : Blo 1723062 44168651 := bstep (se 1 (by rfl) ⟨33126488, by rfl⟩ : syracuseStep 44168651 = 66252977) B66252977
theorem B5822009 : Blo 1723062 5822009 := bstep (se 2 (by rfl) ⟨2183253, by rfl⟩ : syracuseStep 5822009 = 4366507) B4366507
theorem B2070079 : Blo 1723062 2070079 := bstep (se 1 (by rfl) ⟨1552559, by rfl⟩ : syracuseStep 2070079 = 3105119) B3105119
theorem B2307647 : Blo 1723062 2307647 := bstep (se 1 (by rfl) ⟨1730735, by rfl⟩ : syracuseStep 2307647 = 3461471) B3461471
theorem B2586347 : Blo 1723062 2586347 := bstep (se 1 (by rfl) ⟨1939760, by rfl⟩ : syracuseStep 2586347 = 3879521) B3879521
theorem B3880745 : Blo 1723062 3880745 := bstep (se 2 (by rfl) ⟨1455279, by rfl⟩ : syracuseStep 3880745 = 2910559) B2910559
theorem B6993719 : Blo 1723062 6993719 := bstep (se 1 (by rfl) ⟨5245289, by rfl⟩ : syracuseStep 6993719 = 10490579) B10490579
theorem B1939279 : Blo 1723062 1939279 := bstep (se 1 (by rfl) ⟨1454459, by rfl⟩ : syracuseStep 1939279 = 2908919) B2908919
theorem B4364239 : Blo 1723062 4364239 := bstep (se 1 (by rfl) ⟨3273179, by rfl⟩ : syracuseStep 4364239 = 6546359) B6546359
theorem B2586575 : Blo 1723062 2586575 := bstep (se 1 (by rfl) ⟨1939931, by rfl⟩ : syracuseStep 2586575 = 3879863) B3879863
theorem B23590885 : Blo 1723062 23590885 := bstep (se 4 (by rfl) ⟨2211645, by rfl⟩ : syracuseStep 23590885 = 4423291) B4423291
theorem B9320633 : Blo 1723062 9320633 := bstep (se 2 (by rfl) ⟨3495237, by rfl⟩ : syracuseStep 9320633 = 6990475) B6990475
theorem B1939675 : Blo 1723062 1939675 := bstep (se 1 (by rfl) ⟨1454756, by rfl⟩ : syracuseStep 1939675 = 2909513) B2909513
theorem B6215933 : Blo 1723062 6215933 := bstep (se 3 (by rfl) ⟨1165487, by rfl⟩ : syracuseStep 6215933 = 2330975) B2330975
theorem B6543625 : Blo 1723062 6543625 := bstep (se 2 (by rfl) ⟨2453859, by rfl⟩ : syracuseStep 6543625 = 4907719) B4907719
theorem B7362845 : Blo 1723062 7362845 := bstep (se 3 (by rfl) ⟨1380533, by rfl⟩ : syracuseStep 7362845 = 2761067) B2761067
theorem B2586971 : Blo 1723062 2586971 := bstep (se 1 (by rfl) ⟨1940228, by rfl⟩ : syracuseStep 2586971 = 3880457) B3880457
theorem B4200815 : Blo 1723062 4200815 := bstep (se 1 (by rfl) ⟨3150611, by rfl⟩ : syracuseStep 4200815 = 6301223) B6301223
theorem B9820541 : Blo 1723062 9820541 := bstep (se 3 (by rfl) ⟨1841351, by rfl⟩ : syracuseStep 9820541 = 3682703) B3682703
theorem B349354457 : Blo 1723062 349354457 := bstep (se 2 (by rfl) ⟨131007921, by rfl⟩ : syracuseStep 349354457 = 262015843) B262015843
theorem B1939963 : Blo 1723062 1939963 := bstep (se 1 (by rfl) ⟨1454972, by rfl⟩ : syracuseStep 1939963 = 2909945) B2909945
theorem B1841659 : Blo 1723062 1841659 := bstep (se 1 (by rfl) ⟨1381244, by rfl⟩ : syracuseStep 1841659 = 2762489) B2762489
theorem B11041343 : Blo 1723062 11041343 := bstep (se 1 (by rfl) ⟨8281007, by rfl⟩ : syracuseStep 11041343 = 16562015) B16562015
theorem B2587199 : Blo 1723062 2587199 := bstep (se 1 (by rfl) ⟨1940399, by rfl⟩ : syracuseStep 2587199 = 3880799) B3880799
theorem B8723051 : Blo 1723062 8723051 := bstep (se 1 (by rfl) ⟨6542288, by rfl⟩ : syracuseStep 8723051 = 13084577) B13084577
theorem B8288891 : Blo 1723062 8288891 := bstep (se 1 (by rfl) ⟨6216668, by rfl⟩ : syracuseStep 8288891 = 12433337) B12433337
theorem B1940143 : Blo 1723062 1940143 := bstep (se 1 (by rfl) ⟨1455107, by rfl⟩ : syracuseStep 1940143 = 2910215) B2910215
theorem B2587319 : Blo 1723062 2587319 := bstep (se 1 (by rfl) ⟨1940489, by rfl⟩ : syracuseStep 2587319 = 3880979) B3880979
theorem B9321155 : Blo 1723062 9321155 := bstep (se 1 (by rfl) ⟨6990866, by rfl⟩ : syracuseStep 9321155 = 13981733) B13981733
theorem B2620127 : Blo 1723062 2620127 := bstep (se 1 (by rfl) ⟨1965095, by rfl⟩ : syracuseStep 2620127 = 3930191) B3930191
theorem B4365211 : Blo 1723062 4365211 := bstep (se 1 (by rfl) ⟨3273908, by rfl⟩ : syracuseStep 4365211 = 6547817) B6547817
theorem B2587547 : Blo 1723062 2587547 := bstep (se 1 (by rfl) ⟨1940660, by rfl⟩ : syracuseStep 2587547 = 3881321) B3881321
theorem B1940431 : Blo 1723062 1940431 := bstep (se 1 (by rfl) ⟨1455323, by rfl⟩ : syracuseStep 1940431 = 2910647) B2910647
theorem B8723537 : Blo 1723062 8723537 := bstep (se 2 (by rfl) ⟨3271326, by rfl⟩ : syracuseStep 8723537 = 6542653) B6542653
theorem B9321587 : Blo 1723062 9321587 := bstep (se 1 (by rfl) ⟨6991190, by rfl⟩ : syracuseStep 9321587 = 13982381) B13982381
theorem B5815583 : Blo 1723062 5815583 := bstep (se 1 (by rfl) ⟨4361687, by rfl⟩ : syracuseStep 5815583 = 8723375) B8723375
theorem B8396099 : Blo 1723062 8396099 := bstep (se 1 (by rfl) ⟨6297074, by rfl⟩ : syracuseStep 8396099 = 12594149) B12594149
theorem B3931487 : Blo 1723062 3931487 := bstep (se 1 (by rfl) ⟨2948615, by rfl⟩ : syracuseStep 3931487 = 5897231) B5897231
theorem B4144571 : Blo 1723062 4144571 := bstep (se 1 (by rfl) ⟨3108428, by rfl⟩ : syracuseStep 4144571 = 6216857) B6216857
theorem B18636247 : Blo 1723062 18636247 := bstep (se 1 (by rfl) ⟨13977185, by rfl⟩ : syracuseStep 18636247 = 27954371) B27954371
theorem B5521441 : Blo 1723062 5521441 := bstep (se 2 (by rfl) ⟨2070540, by rfl⟩ : syracuseStep 5521441 = 4141081) B4141081
theorem B22396961 : Blo 1723062 22396961 := bstep (se 2 (by rfl) ⟨8398860, by rfl⟩ : syracuseStep 22396961 = 16797721) B16797721
theorem B13090895 : Blo 1723062 13090895 := bstep (se 1 (by rfl) ⟨9818171, by rfl⟩ : syracuseStep 13090895 = 19636343) B19636343
theorem B2908379 : Blo 1723062 2908379 := bstep (se 1 (by rfl) ⟨2181284, by rfl⟩ : syracuseStep 2908379 = 4362569) B4362569
theorem B9822455 : Blo 1723062 9822455 := bstep (se 1 (by rfl) ⟨7366841, by rfl⟩ : syracuseStep 9822455 = 14733683) B14733683
theorem B3318047 : Blo 1723062 3318047 := bstep (se 1 (by rfl) ⟨2488535, by rfl⟩ : syracuseStep 3318047 = 4977071) B4977071
theorem B8724833 : Blo 1723062 8724833 := bstep (se 2 (by rfl) ⟨3271812, by rfl⟩ : syracuseStep 8724833 = 6543625) B6543625
theorem B2908615 : Blo 1723062 2908615 := bstep (se 1 (by rfl) ⟨2181461, by rfl⟩ : syracuseStep 2908615 = 4362923) B4362923
theorem B29458889 : Blo 1723062 29458889 := bstep (se 2 (by rfl) ⟨11047083, by rfl⟩ : syracuseStep 29458889 = 22094167) B22094167
theorem B2908649 : Blo 1723062 2908649 := bstep (se 2 (by rfl) ⟨1090743, by rfl⟩ : syracuseStep 2908649 = 2181487) B2181487
theorem B47211011 : Blo 1723062 47211011 := bstep (se 1 (by rfl) ⟨35408258, by rfl⟩ : syracuseStep 47211011 = 70816517) B70816517
theorem B19645091 : Blo 1723062 19645091 := bstep (se 1 (by rfl) ⟨14733818, by rfl⟩ : syracuseStep 19645091 = 29467637) B29467637
theorem B6210283 : Blo 1723062 6210283 := bstep (se 1 (by rfl) ⟨4657712, by rfl⟩ : syracuseStep 6210283 = 9315425) B9315425
theorem B8283161 : Blo 1723062 8283161 := bstep (se 2 (by rfl) ⟨3106185, by rfl⟩ : syracuseStep 8283161 = 6212371) B6212371
theorem B9815165 : Blo 1723062 9815165 := bstep (se 3 (by rfl) ⟨1840343, by rfl⟩ : syracuseStep 9815165 = 3680687) B3680687
theorem B11043985 : Blo 1723062 11043985 := bstep (se 2 (by rfl) ⟨4141494, by rfl⟩ : syracuseStep 11043985 = 8282989) B8282989
theorem B4908221 : Blo 1723062 4908221 := bstep (se 3 (by rfl) ⟨920291, by rfl⟩ : syracuseStep 4908221 = 1840583) B1840583
theorem B4662479 : Blo 1723062 4662479 := bstep (se 1 (by rfl) ⟨3496859, by rfl⟩ : syracuseStep 4662479 = 6993719) B6993719
theorem B5522825 : Blo 1723062 5522825 := bstep (se 2 (by rfl) ⟨2071059, by rfl⟩ : syracuseStep 5522825 = 4142119) B4142119
theorem B6153725 : Blo 1723062 6153725 := bstep (se 3 (by rfl) ⟨1153823, by rfl⟩ : syracuseStep 6153725 = 2307647) B2307647
theorem B4908563 : Blo 1723062 4908563 := bstep (se 1 (by rfl) ⟨3681422, by rfl⟩ : syracuseStep 4908563 = 7362845) B7362845
theorem B6547027 : Blo 1723062 6547027 := bstep (se 1 (by rfl) ⟨4910270, by rfl⟩ : syracuseStep 6547027 = 9820541) B9820541
theorem B9815849 : Blo 1723062 9815849 := bstep (se 2 (by rfl) ⟨3680943, by rfl⟩ : syracuseStep 9815849 = 7361887) B7361887
theorem B24848329 : Blo 1723062 24848329 := bstep (se 2 (by rfl) ⟨9318123, by rfl⟩ : syracuseStep 24848329 = 18636247) B18636247
theorem B3877055 : Blo 1723062 3877055 := bstep (se 1 (by rfl) ⟨2907791, by rfl⟩ : syracuseStep 3877055 = 5815583) B5815583
theorem B5597399 : Blo 1723062 5597399 := bstep (se 1 (by rfl) ⟨4198049, by rfl⟩ : syracuseStep 5597399 = 8396099) B8396099
theorem B2763047 : Blo 1723062 2763047 := bstep (se 1 (by rfl) ⟨2072285, by rfl⟩ : syracuseStep 2763047 = 4144571) B4144571
theorem B2910505 : Blo 1723062 2910505 := bstep (se 2 (by rfl) ⟨1091439, by rfl⟩ : syracuseStep 2910505 = 2182879) B2182879
theorem B5818715 : Blo 1723062 5818715 := bstep (se 1 (by rfl) ⟨4364036, by rfl⟩ : syracuseStep 5818715 = 8728073) B8728073
theorem B5818985 : Blo 1723062 5818985 := bstep (se 2 (by rfl) ⟨2182119, by rfl⟩ : syracuseStep 5818985 = 4364239) B4364239
theorem B1723227 : Blo 1723062 1723227 := bstep (se 1 (by rfl) ⟨1292420, by rfl⟩ : syracuseStep 1723227 = 2584841) B2584841
theorem B1723295 : Blo 1723062 1723295 := bstep (se 1 (by rfl) ⟨1292471, by rfl⟩ : syracuseStep 1723295 = 2584943) B2584943
theorem B12127265 : Blo 1723062 12127265 := bstep (se 2 (by rfl) ⟨4547724, by rfl⟩ : syracuseStep 12127265 = 9095449) B9095449
theorem B1723439 : Blo 1723062 1723439 := bstep (se 1 (by rfl) ⟨1292579, by rfl⟩ : syracuseStep 1723439 = 2585159) B2585159
theorem B1723463 : Blo 1723062 1723463 := bstep (se 1 (by rfl) ⟨1292597, by rfl⟩ : syracuseStep 1723463 = 2585195) B2585195
theorem B860826703 : Blo 1723062 860826703 := bstep (se 1 (by rfl) ⟨645620027, by rfl⟩ : syracuseStep 860826703 = 1291240055) B1291240055
theorem B3878009 : Blo 1723062 3878009 := bstep (se 2 (by rfl) ⟨1454253, by rfl⟩ : syracuseStep 3878009 = 2908507) B2908507
theorem B1723615 : Blo 1723062 1723615 := bstep (se 1 (by rfl) ⟨1292711, by rfl⟩ : syracuseStep 1723615 = 2585423) B2585423
theorem B1723879 : Blo 1723062 1723879 := bstep (se 1 (by rfl) ⟨1292909, by rfl⟩ : syracuseStep 1723879 = 2585819) B2585819
theorem B80686631 : Blo 1723062 80686631 := bstep (se 1 (by rfl) ⟨60514973, by rfl⟩ : syracuseStep 80686631 = 121029947) B121029947
theorem B3493439 : Blo 1723062 3493439 := bstep (se 1 (by rfl) ⟨2620079, by rfl⟩ : syracuseStep 3493439 = 5240159) B5240159
theorem B1723995 : Blo 1723062 1723995 := bstep (se 1 (by rfl) ⟨1292996, by rfl⟩ : syracuseStep 1723995 = 2585993) B2585993
theorem B5820011 : Blo 1723062 5820011 := bstep (se 1 (by rfl) ⟨4365008, by rfl⟩ : syracuseStep 5820011 = 8730017) B8730017
theorem B29445767 : Blo 1723062 29445767 := bstep (se 1 (by rfl) ⟨22084325, by rfl⟩ : syracuseStep 29445767 = 44168651) B44168651
theorem B106163875 : Blo 1723062 106163875 := bstep (se 1 (by rfl) ⟨79622906, by rfl⟩ : syracuseStep 106163875 = 159245813) B159245813
theorem B3878675 : Blo 1723062 3878675 := bstep (se 1 (by rfl) ⟨2909006, by rfl⟩ : syracuseStep 3878675 = 5818013) B5818013
theorem B1724231 : Blo 1723062 1724231 := bstep (se 1 (by rfl) ⟨1293173, by rfl⟩ : syracuseStep 1724231 = 2586347) B2586347
theorem B5820281 : Blo 1723062 5820281 := bstep (se 2 (by rfl) ⟨2182605, by rfl⟩ : syracuseStep 5820281 = 4365211) B4365211
theorem B1724383 : Blo 1723062 1724383 := bstep (se 1 (by rfl) ⟨1293287, by rfl⟩ : syracuseStep 1724383 = 2586575) B2586575
theorem B3879035 : Blo 1723062 3879035 := bstep (se 1 (by rfl) ⟨2909276, by rfl⟩ : syracuseStep 3879035 = 5818553) B5818553
theorem B6213755 : Blo 1723062 6213755 := bstep (se 1 (by rfl) ⟨4660316, by rfl⟩ : syracuseStep 6213755 = 9320633) B9320633
theorem B5820605 : Blo 1723062 5820605 := bstep (se 3 (by rfl) ⟨1091363, by rfl⟩ : syracuseStep 5820605 = 2182727) B2182727
theorem B9818333 : Blo 1723062 9818333 := bstep (se 3 (by rfl) ⟨1840937, by rfl⟩ : syracuseStep 9818333 = 3681875) B3681875
theorem B1724647 : Blo 1723062 1724647 := bstep (se 1 (by rfl) ⟨1293485, by rfl⟩ : syracuseStep 1724647 = 2586971) B2586971
theorem B232902971 : Blo 1723062 232902971 := bstep (se 1 (by rfl) ⟨174677228, by rfl⟩ : syracuseStep 232902971 = 349354457) B349354457
theorem B7360895 : Blo 1723062 7360895 := bstep (se 1 (by rfl) ⟨5520671, by rfl⟩ : syracuseStep 7360895 = 11041343) B11041343
theorem B4485503 : Blo 1723062 4485503 := bstep (se 1 (by rfl) ⟨3364127, by rfl⟩ : syracuseStep 4485503 = 6728255) B6728255
theorem B1724799 : Blo 1723062 1724799 := bstep (se 1 (by rfl) ⟨1293599, by rfl⟩ : syracuseStep 1724799 = 2587199) B2587199
theorem B3879305 : Blo 1723062 3879305 := bstep (se 2 (by rfl) ⟨1454739, by rfl⟩ : syracuseStep 3879305 = 2909479) B2909479
theorem B5525927 : Blo 1723062 5525927 := bstep (se 1 (by rfl) ⟨4144445, by rfl⟩ : syracuseStep 5525927 = 8288891) B8288891
theorem B2585039 : Blo 1723062 2585039 := bstep (se 1 (by rfl) ⟨1938779, by rfl⟩ : syracuseStep 2585039 = 3877559) B3877559
theorem B1724879 : Blo 1723062 1724879 := bstep (se 1 (by rfl) ⟨1293659, by rfl⟩ : syracuseStep 1724879 = 2587319) B2587319
theorem B6214103 : Blo 1723062 6214103 := bstep (se 1 (by rfl) ⟨4660577, by rfl⟩ : syracuseStep 6214103 = 9321155) B9321155
theorem B4657657 : Blo 1723062 4657657 := bstep (se 2 (by rfl) ⟨1746621, by rfl⟩ : syracuseStep 4657657 = 3493243) B3493243
theorem B2585081 : Blo 1723062 2585081 := bstep (se 2 (by rfl) ⟨969405, by rfl⟩ : syracuseStep 2585081 = 1938811) B1938811
theorem B2585183 : Blo 1723062 2585183 := bstep (se 1 (by rfl) ⟨1938887, by rfl⟩ : syracuseStep 2585183 = 3877775) B3877775
theorem B1725031 : Blo 1723062 1725031 := bstep (se 1 (by rfl) ⟨1293773, by rfl⟩ : syracuseStep 1725031 = 2587547) B2587547
theorem B6214391 : Blo 1723062 6214391 := bstep (se 1 (by rfl) ⟨4660793, by rfl⟩ : syracuseStep 6214391 = 9321587) B9321587
theorem B2585663 : Blo 1723062 2585663 := bstep (se 1 (by rfl) ⟨1939247, by rfl⟩ : syracuseStep 2585663 = 3878495) B3878495
theorem B2585705 : Blo 1723062 2585705 := bstep (se 2 (by rfl) ⟨969639, by rfl⟩ : syracuseStep 2585705 = 1939279) B1939279
theorem B3880043 : Blo 1723062 3880043 := bstep (se 1 (by rfl) ⟨2910032, by rfl⟩ : syracuseStep 3880043 = 5820065) B5820065
theorem B2585807 : Blo 1723062 2585807 := bstep (se 1 (by rfl) ⟨1939355, by rfl⟩ : syracuseStep 2585807 = 3878711) B3878711
theorem B31454513 : Blo 1723062 31454513 := bstep (se 2 (by rfl) ⟨11795442, by rfl⟩ : syracuseStep 31454513 = 23590885) B23590885
theorem B5821793 : Blo 1723062 5821793 := bstep (se 2 (by rfl) ⟨2183172, by rfl⟩ : syracuseStep 5821793 = 4366345) B4366345
theorem B13981081 : Blo 1723062 13981081 := bstep (se 2 (by rfl) ⟨5242905, by rfl⟩ : syracuseStep 13981081 = 10485811) B10485811
theorem B2586011 : Blo 1723062 2586011 := bstep (se 1 (by rfl) ⟨1939508, by rfl⟩ : syracuseStep 2586011 = 3879017) B3879017
theorem B145389095 : Blo 1723062 145389095 := bstep (se 1 (by rfl) ⟨109041821, by rfl⟩ : syracuseStep 145389095 = 218083643) B218083643
theorem B47208035 : Blo 1723062 47208035 := bstep (se 1 (by rfl) ⟨35406026, by rfl⟩ : syracuseStep 47208035 = 70812053) B70812053
theorem B6542957 : Blo 1723062 6542957 := bstep (se 3 (by rfl) ⟨1226804, by rfl⟩ : syracuseStep 6542957 = 2453609) B2453609
theorem B2586233 : Blo 1723062 2586233 := bstep (se 2 (by rfl) ⟨969837, by rfl⟩ : syracuseStep 2586233 = 1939675) B1939675
theorem B11040421 : Blo 1723062 11040421 := bstep (se 4 (by rfl) ⟨1035039, by rfl⟩ : syracuseStep 11040421 = 2070079) B2070079
theorem B3880619 : Blo 1723062 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B13088465 : Blo 1723062 13088465 := bstep (se 2 (by rfl) ⟨4908174, by rfl⟩ : syracuseStep 13088465 = 9816349) B9816349
theorem B2586335 : Blo 1723062 2586335 := bstep (se 1 (by rfl) ⟨1939751, by rfl⟩ : syracuseStep 2586335 = 3879503) B3879503
theorem B4364027 : Blo 1723062 4364027 := bstep (se 1 (by rfl) ⟨3273020, by rfl⟩ : syracuseStep 4364027 = 6546041) B6546041
theorem B2586431 : Blo 1723062 2586431 := bstep (se 1 (by rfl) ⟨1939823, by rfl⟩ : syracuseStep 2586431 = 3879647) B3879647
theorem B19642175 : Blo 1723062 19642175 := bstep (se 1 (by rfl) ⟨14731631, by rfl⟩ : syracuseStep 19642175 = 29463263) B29463263
theorem B19896131 : Blo 1723062 19896131 := bstep (se 1 (by rfl) ⟨14922098, by rfl⟩ : syracuseStep 19896131 = 29844197) B29844197
theorem B2455375 : Blo 1723062 2455375 := bstep (se 1 (by rfl) ⟨1841531, by rfl⟩ : syracuseStep 2455375 = 3683063) B3683063
theorem B13973393 : Blo 1723062 13973393 := bstep (se 2 (by rfl) ⟨5240022, by rfl⟩ : syracuseStep 13973393 = 10480045) B10480045
theorem B56678359 : Blo 1723062 56678359 := bstep (se 1 (by rfl) ⟨42508769, by rfl⟩ : syracuseStep 56678359 = 85017539) B85017539
theorem B2586599 : Blo 1723062 2586599 := bstep (se 1 (by rfl) ⟨1939949, by rfl⟩ : syracuseStep 2586599 = 3879899) B3879899
theorem B3880943 : Blo 1723062 3880943 := bstep (se 1 (by rfl) ⟨2910707, by rfl⟩ : syracuseStep 3880943 = 5821415) B5821415
theorem B2586617 : Blo 1723062 2586617 := bstep (se 2 (by rfl) ⟨969981, by rfl⟩ : syracuseStep 2586617 = 1939963) B1939963
theorem B13981697 : Blo 1723062 13981697 := bstep (se 2 (by rfl) ⟨5243136, by rfl⟩ : syracuseStep 13981697 = 10486273) B10486273
theorem B9320507 : Blo 1723062 9320507 := bstep (se 1 (by rfl) ⟨6990380, by rfl⟩ : syracuseStep 9320507 = 13980761) B13980761
theorem B2586719 : Blo 1723062 2586719 := bstep (se 1 (by rfl) ⟨1940039, by rfl⟩ : syracuseStep 2586719 = 3880079) B3880079
theorem B12433505 : Blo 1723062 12433505 := bstep (se 2 (by rfl) ⟨4662564, by rfl⟩ : syracuseStep 12433505 = 9325129) B9325129
theorem B2586779 : Blo 1723062 2586779 := bstep (se 1 (by rfl) ⟨1940084, by rfl⟩ : syracuseStep 2586779 = 3880169) B3880169
theorem B2586815 : Blo 1723062 2586815 := bstep (se 1 (by rfl) ⟨1940111, by rfl⟩ : syracuseStep 2586815 = 3880223) B3880223
theorem B3881159 : Blo 1723062 3881159 := bstep (se 1 (by rfl) ⟨2910869, by rfl⟩ : syracuseStep 3881159 = 5821739) B5821739
theorem B2586857 : Blo 1723062 2586857 := bstep (se 2 (by rfl) ⟨970071, by rfl⟩ : syracuseStep 2586857 = 1940143) B1940143
theorem B8730989 : Blo 1723062 8730989 := bstep (se 3 (by rfl) ⟨1637060, by rfl⟩ : syracuseStep 8730989 = 3274121) B3274121
theorem B3881339 : Blo 1723062 3881339 := bstep (se 1 (by rfl) ⟨2911004, by rfl⟩ : syracuseStep 3881339 = 5822009) B5822009
theorem B2587163 : Blo 1723062 2587163 := bstep (se 1 (by rfl) ⟨1940372, by rfl⟩ : syracuseStep 2587163 = 3880745) B3880745
theorem B1939999 : Blo 1723062 1939999 := bstep (se 1 (by rfl) ⟨1454999, by rfl⟩ : syracuseStep 1939999 = 2909999) B2909999
theorem B9820723 : Blo 1723062 9820723 := bstep (se 1 (by rfl) ⟨7365542, by rfl⟩ : syracuseStep 9820723 = 14731085) B14731085
theorem B2587241 : Blo 1723062 2587241 := bstep (se 2 (by rfl) ⟨970215, by rfl⟩ : syracuseStep 2587241 = 1940431) B1940431
theorem B4143955 : Blo 1723062 4143955 := bstep (se 1 (by rfl) ⟨3107966, by rfl⟩ : syracuseStep 4143955 = 6215933) B6215933
theorem B4365161 : Blo 1723062 4365161 := bstep (se 2 (by rfl) ⟨1636935, by rfl⟩ : syracuseStep 4365161 = 3273871) B3273871
theorem B2800543 : Blo 1723062 2800543 := bstep (se 1 (by rfl) ⟨2100407, by rfl⟩ : syracuseStep 2800543 = 4200815) B4200815
theorem B2071531 : Blo 1723062 2071531 := bstep (se 1 (by rfl) ⟨1553648, by rfl⟩ : syracuseStep 2071531 = 3107297) B3107297
theorem B4365353 : Blo 1723062 4365353 := bstep (se 2 (by rfl) ⟨1637007, by rfl⟩ : syracuseStep 4365353 = 3274015) B3274015
theorem B5815367 : Blo 1723062 5815367 := bstep (se 1 (by rfl) ⟨4361525, by rfl⟩ : syracuseStep 5815367 = 8723051) B8723051
theorem B5815421 : Blo 1723062 5815421 := bstep (se 3 (by rfl) ⟨1090391, by rfl⟩ : syracuseStep 5815421 = 2180783) B2180783
theorem B6987005 : Blo 1723062 6987005 := bstep (se 3 (by rfl) ⟨1310063, by rfl⟩ : syracuseStep 6987005 = 2620127) B2620127
theorem B5815691 : Blo 1723062 5815691 := bstep (se 1 (by rfl) ⟨4361768, by rfl⟩ : syracuseStep 5815691 = 8723537) B8723537
theorem B6544871 : Blo 1723062 6544871 := bstep (se 1 (by rfl) ⟨4908653, by rfl⟩ : syracuseStep 6544871 = 9817307) B9817307
theorem B2620991 : Blo 1723062 2620991 := bstep (se 1 (by rfl) ⟨1965743, by rfl⟩ : syracuseStep 2620991 = 3931487) B3931487
theorem B11050775 : Blo 1723062 11050775 := bstep (se 1 (by rfl) ⟨8288081, by rfl⟩ : syracuseStep 11050775 = 16576163) B16576163
theorem B9821999 : Blo 1723062 9821999 := bstep (se 1 (by rfl) ⟨7366499, by rfl⟩ : syracuseStep 9821999 = 14732999) B14732999
theorem B8724347 : Blo 1723062 8724347 := bstep (se 1 (by rfl) ⟨6543260, by rfl⟩ : syracuseStep 8724347 = 13086521) B13086521
theorem B29450141 : Blo 1723062 29450141 := bstep (se 3 (by rfl) ⟨5521901, by rfl⟩ : syracuseStep 29450141 = 11043803) B11043803
theorem B2908075 : Blo 1723062 2908075 := bstep (se 1 (by rfl) ⟨2181056, by rfl⟩ : syracuseStep 2908075 = 4362113) B4362113
theorem B9822181 : Blo 1723062 9822181 := bstep (se 4 (by rfl) ⟨920829, by rfl⟩ : syracuseStep 9822181 = 1841659) B1841659
theorem B6545555 : Blo 1723062 6545555 := bstep (se 1 (by rfl) ⟨4909166, by rfl⟩ : syracuseStep 6545555 = 9818333) B9818333
theorem B2212031 : Blo 1723062 2212031 := bstep (se 1 (by rfl) ⟨1659023, by rfl⟩ : syracuseStep 2212031 = 3318047) B3318047
theorem B5816555 : Blo 1723062 5816555 := bstep (se 1 (by rfl) ⟨4362416, by rfl⟩ : syracuseStep 5816555 = 8724833) B8724833
theorem B31474007 : Blo 1723062 31474007 := bstep (se 1 (by rfl) ⟨23605505, by rfl⟩ : syracuseStep 31474007 = 47211011) B47211011
theorem B6210209 : Blo 1723062 6210209 := bstep (se 2 (by rfl) ⟨2328828, by rfl⟩ : syracuseStep 6210209 = 4657657) B4657657
theorem B5522107 : Blo 1723062 5522107 := bstep (se 1 (by rfl) ⟨4141580, by rfl⟩ : syracuseStep 5522107 = 8283161) B8283161
theorem B19629053 : Blo 1723062 19629053 := bstep (se 3 (by rfl) ⟨3680447, by rfl⟩ : syracuseStep 19629053 = 7360895) B7360895
theorem B11961341 : Blo 1723062 11961341 := bstep (se 3 (by rfl) ⟨2242751, by rfl⟩ : syracuseStep 11961341 = 4485503) B4485503
theorem B8725643 : Blo 1723062 8725643 := bstep (se 1 (by rfl) ⟨6544232, by rfl⟩ : syracuseStep 8725643 = 13088465) B13088465
theorem B2909351 : Blo 1723062 2909351 := bstep (se 1 (by rfl) ⟨2182013, by rfl⟩ : syracuseStep 2909351 = 4364027) B4364027
theorem B13264087 : Blo 1723062 13264087 := bstep (se 1 (by rfl) ⟨9948065, by rfl⟩ : syracuseStep 13264087 = 19896131) B19896131
theorem B9315595 : Blo 1723062 9315595 := bstep (se 1 (by rfl) ⟨6986696, by rfl⟩ : syracuseStep 9315595 = 13973393) B13973393
theorem B2762041 : Blo 1723062 2762041 := bstep (se 2 (by rfl) ⟨1035765, by rfl⟩ : syracuseStep 2762041 = 2071531) B2071531
theorem B125888093 : Blo 1723062 125888093 := bstep (se 3 (by rfl) ⟨23604017, by rfl⟩ : syracuseStep 125888093 = 47208035) B47208035
theorem B2910107 : Blo 1723062 2910107 := bstep (se 1 (by rfl) ⟨2182580, by rfl⟩ : syracuseStep 2910107 = 4365161) B4365161
theorem B2910235 : Blo 1723062 2910235 := bstep (se 1 (by rfl) ⟨2182676, by rfl⟩ : syracuseStep 2910235 = 4365353) B4365353
theorem B3876911 : Blo 1723062 3876911 := bstep (se 1 (by rfl) ⟨2907683, by rfl⟩ : syracuseStep 3876911 = 5815367) B5815367
theorem B3876947 : Blo 1723062 3876947 := bstep (se 1 (by rfl) ⟨2907710, by rfl⟩ : syracuseStep 3876947 = 5815421) B5815421
theorem B141551833 : Blo 1723062 141551833 := bstep (se 2 (by rfl) ⟨53081937, by rfl⟩ : syracuseStep 141551833 = 106163875) B106163875
theorem B3877127 : Blo 1723062 3877127 := bstep (se 1 (by rfl) ⟨2907845, by rfl⟩ : syracuseStep 3877127 = 5815691) B5815691
theorem B53791087 : Blo 1723062 53791087 := bstep (se 1 (by rfl) ⟨40343315, by rfl⟩ : syracuseStep 53791087 = 80686631) B80686631
theorem B2328959 : Blo 1723062 2328959 := bstep (se 1 (by rfl) ⟨1746719, by rfl⟩ : syracuseStep 2328959 = 3493439) B3493439
theorem B1747327 : Blo 1723062 1747327 := bstep (se 1 (by rfl) ⟨1310495, by rfl⟩ : syracuseStep 1747327 = 2620991) B2620991
theorem B19630511 : Blo 1723062 19630511 := bstep (se 1 (by rfl) ⟨14722883, by rfl⟩ : syracuseStep 19630511 = 29445767) B29445767
theorem B7367183 : Blo 1723062 7367183 := bstep (se 1 (by rfl) ⟨5525387, by rfl⟩ : syracuseStep 7367183 = 11050775) B11050775
theorem B6547999 : Blo 1723062 6547999 := bstep (se 1 (by rfl) ⟨4910999, by rfl⟩ : syracuseStep 6547999 = 9821999) B9821999
theorem B3877433 : Blo 1723062 3877433 := bstep (se 2 (by rfl) ⟨1454037, by rfl⟩ : syracuseStep 3877433 = 2908075) B2908075
theorem B33131105 : Blo 1723062 33131105 := bstep (se 2 (by rfl) ⟨12424164, by rfl⟩ : syracuseStep 33131105 = 24848329) B24848329
theorem B8727263 : Blo 1723062 8727263 := bstep (se 1 (by rfl) ⟨6545447, by rfl⟩ : syracuseStep 8727263 = 13090895) B13090895
theorem B6548303 : Blo 1723062 6548303 := bstep (se 1 (by rfl) ⟨4911227, by rfl⟩ : syracuseStep 6548303 = 9822455) B9822455
theorem B33156013 : Blo 1723062 33156013 := bstep (se 3 (by rfl) ⟨6216752, by rfl⟩ : syracuseStep 33156013 = 12433505) B12433505
theorem B19639259 : Blo 1723062 19639259 := bstep (se 1 (by rfl) ⟨14729444, by rfl⟩ : syracuseStep 19639259 = 29458889) B29458889
theorem B1723359 : Blo 1723062 1723359 := bstep (se 1 (by rfl) ⟨1292519, by rfl⟩ : syracuseStep 1723359 = 2585039) B2585039
theorem B1723387 : Blo 1723062 1723387 := bstep (se 1 (by rfl) ⟨1292540, by rfl⟩ : syracuseStep 1723387 = 2585081) B2585081
theorem B1723455 : Blo 1723062 1723455 := bstep (se 1 (by rfl) ⟨1292591, by rfl⟩ : syracuseStep 1723455 = 2585183) B2585183
theorem B3878153 : Blo 1723062 3878153 := bstep (se 2 (by rfl) ⟨1454307, by rfl⟩ : syracuseStep 3878153 = 2908615) B2908615
theorem B1723775 : Blo 1723062 1723775 := bstep (se 1 (by rfl) ⟨1292831, by rfl⟩ : syracuseStep 1723775 = 2585663) B2585663
theorem B13094297 : Blo 1723062 13094297 := bstep (se 2 (by rfl) ⟨4910361, by rfl⟩ : syracuseStep 13094297 = 9820723) B9820723
theorem B1723803 : Blo 1723062 1723803 := bstep (se 1 (by rfl) ⟨1292852, by rfl⟩ : syracuseStep 1723803 = 2585705) B2585705
theorem B3272147 : Blo 1723062 3272147 := bstep (se 1 (by rfl) ⟨2454110, by rfl⟩ : syracuseStep 3272147 = 4908221) B4908221
theorem B1723871 : Blo 1723062 1723871 := bstep (se 1 (by rfl) ⟨1292903, by rfl⟩ : syracuseStep 1723871 = 2585807) B2585807
theorem B3681883 : Blo 1723062 3681883 := bstep (se 1 (by rfl) ⟨2761412, by rfl⟩ : syracuseStep 3681883 = 5522825) B5522825
theorem B1724007 : Blo 1723062 1724007 := bstep (se 1 (by rfl) ⟨1293005, by rfl⟩ : syracuseStep 1724007 = 2586011) B2586011
theorem B3272375 : Blo 1723062 3272375 := bstep (se 1 (by rfl) ⟨2454281, by rfl⟩ : syracuseStep 3272375 = 4908563) B4908563
theorem B4361971 : Blo 1723062 4361971 := bstep (se 1 (by rfl) ⟨3271478, by rfl⟩ : syracuseStep 4361971 = 6542957) B6542957
theorem B1724155 : Blo 1723062 1724155 := bstep (se 1 (by rfl) ⟨1293116, by rfl⟩ : syracuseStep 1724155 = 2586233) B2586233
theorem B5525273 : Blo 1723062 5525273 := bstep (se 2 (by rfl) ⟨2071977, by rfl⟩ : syracuseStep 5525273 = 4143955) B4143955
theorem B1724223 : Blo 1723062 1724223 := bstep (se 1 (by rfl) ⟨1293167, by rfl⟩ : syracuseStep 1724223 = 2586335) B2586335
theorem B1724287 : Blo 1723062 1724287 := bstep (se 1 (by rfl) ⟨1293215, by rfl⟩ : syracuseStep 1724287 = 2586431) B2586431
theorem B13094783 : Blo 1723062 13094783 := bstep (se 1 (by rfl) ⟨9821087, by rfl⟩ : syracuseStep 13094783 = 19642175) B19642175
theorem B1724399 : Blo 1723062 1724399 := bstep (se 1 (by rfl) ⟨1293299, by rfl⟩ : syracuseStep 1724399 = 2586599) B2586599
theorem B1724411 : Blo 1723062 1724411 := bstep (se 1 (by rfl) ⟨1293308, by rfl⟩ : syracuseStep 1724411 = 2586617) B2586617
theorem B6213671 : Blo 1723062 6213671 := bstep (se 1 (by rfl) ⟨4660253, by rfl⟩ : syracuseStep 6213671 = 9320507) B9320507
theorem B1724479 : Blo 1723062 1724479 := bstep (se 1 (by rfl) ⟨1293359, by rfl⟩ : syracuseStep 1724479 = 2586719) B2586719
theorem B1724519 : Blo 1723062 1724519 := bstep (se 1 (by rfl) ⟨1293389, by rfl⟩ : syracuseStep 1724519 = 2586779) B2586779
theorem B1147768937 : Blo 1723062 1147768937 := bstep (se 2 (by rfl) ⟨430413351, by rfl⟩ : syracuseStep 1147768937 = 860826703) B860826703
theorem B2584703 : Blo 1723062 2584703 := bstep (se 1 (by rfl) ⟨1938527, by rfl⟩ : syracuseStep 2584703 = 3877055) B3877055
theorem B1724543 : Blo 1723062 1724543 := bstep (se 1 (by rfl) ⟨1293407, by rfl⟩ : syracuseStep 1724543 = 2586815) B2586815
theorem B3731599 : Blo 1723062 3731599 := bstep (se 1 (by rfl) ⟨2798699, by rfl⟩ : syracuseStep 3731599 = 5597399) B5597399
theorem B1724571 : Blo 1723062 1724571 := bstep (se 1 (by rfl) ⟨1293428, by rfl⟩ : syracuseStep 1724571 = 2586857) B2586857
theorem B14725313 : Blo 1723062 14725313 := bstep (se 2 (by rfl) ⟨5521992, by rfl⟩ : syracuseStep 14725313 = 11043985) B11043985
theorem B3879143 : Blo 1723062 3879143 := bstep (se 1 (by rfl) ⟨2909357, by rfl⟩ : syracuseStep 3879143 = 5818715) B5818715
theorem B5820659 : Blo 1723062 5820659 := bstep (se 1 (by rfl) ⟨4365494, by rfl⟩ : syracuseStep 5820659 = 8730989) B8730989
theorem B1724775 : Blo 1723062 1724775 := bstep (se 1 (by rfl) ⟨1293581, by rfl⟩ : syracuseStep 1724775 = 2587163) B2587163
theorem B3879323 : Blo 1723062 3879323 := bstep (se 1 (by rfl) ⟨2909492, by rfl⟩ : syracuseStep 3879323 = 5818985) B5818985
theorem B1724827 : Blo 1723062 1724827 := bstep (se 1 (by rfl) ⟨1293620, by rfl⟩ : syracuseStep 1724827 = 2587241) B2587241
theorem B18641441 : Blo 1723062 18641441 := bstep (se 2 (by rfl) ⟨6990540, by rfl⟩ : syracuseStep 18641441 = 13981081) B13981081
theorem B2585339 : Blo 1723062 2585339 := bstep (se 1 (by rfl) ⟨1939004, by rfl⟩ : syracuseStep 2585339 = 3878009) B3878009
theorem B8729369 : Blo 1723062 8729369 := bstep (se 2 (by rfl) ⟨3273513, by rfl⟩ : syracuseStep 8729369 = 6547027) B6547027
theorem B4658003 : Blo 1723062 4658003 := bstep (se 1 (by rfl) ⟨3493502, by rfl⟩ : syracuseStep 4658003 = 6987005) B6987005
theorem B4363247 : Blo 1723062 4363247 := bstep (se 1 (by rfl) ⟨3272435, by rfl⟩ : syracuseStep 4363247 = 6544871) B6544871
theorem B3880007 : Blo 1723062 3880007 := bstep (se 1 (by rfl) ⟨2910005, by rfl⟩ : syracuseStep 3880007 = 5820011) B5820011
theorem B3273833 : Blo 1723062 3273833 := bstep (se 2 (by rfl) ⟨1227687, by rfl⟩ : syracuseStep 3273833 = 2455375) B2455375
theorem B2585783 : Blo 1723062 2585783 := bstep (se 1 (by rfl) ⟨1939337, by rfl⟩ : syracuseStep 2585783 = 3878675) B3878675
theorem B3880187 : Blo 1723062 3880187 := bstep (se 1 (by rfl) ⟨2910140, by rfl⟩ : syracuseStep 3880187 = 5820281) B5820281
theorem B19633427 : Blo 1723062 19633427 := bstep (se 1 (by rfl) ⟨14725070, by rfl⟩ : syracuseStep 19633427 = 29450141) B29450141
theorem B13096241 : Blo 1723062 13096241 := bstep (se 2 (by rfl) ⟨4911090, by rfl⟩ : syracuseStep 13096241 = 9822181) B9822181
theorem B14931307 : Blo 1723062 14931307 := bstep (se 1 (by rfl) ⟨11198480, by rfl⟩ : syracuseStep 14931307 = 22396961) B22396961
theorem B7361921 : Blo 1723062 7361921 := bstep (se 2 (by rfl) ⟨2760720, by rfl⟩ : syracuseStep 7361921 = 5521441) B5521441
theorem B2586023 : Blo 1723062 2586023 := bstep (se 1 (by rfl) ⟨1939517, by rfl⟩ : syracuseStep 2586023 = 3879035) B3879035
theorem B4142503 : Blo 1723062 4142503 := bstep (se 1 (by rfl) ⟨3106877, by rfl⟩ : syracuseStep 4142503 = 6213755) B6213755
theorem B3880403 : Blo 1723062 3880403 := bstep (se 1 (by rfl) ⟨2910302, by rfl⟩ : syracuseStep 3880403 = 5820605) B5820605
theorem B1938919 : Blo 1723062 1938919 := bstep (se 1 (by rfl) ⟨1454189, by rfl⟩ : syracuseStep 1938919 = 2908379) B2908379
theorem B155268647 : Blo 1723062 155268647 := bstep (se 1 (by rfl) ⟨116451485, by rfl⟩ : syracuseStep 155268647 = 232902971) B232902971
theorem B2586203 : Blo 1723062 2586203 := bstep (se 1 (by rfl) ⟨1939652, by rfl⟩ : syracuseStep 2586203 = 3879305) B3879305
theorem B3683951 : Blo 1723062 3683951 := bstep (se 1 (by rfl) ⟨2762963, by rfl⟩ : syracuseStep 3683951 = 5525927) B5525927
theorem B4142735 : Blo 1723062 4142735 := bstep (se 1 (by rfl) ⟨3107051, by rfl⟩ : syracuseStep 4142735 = 6214103) B6214103
theorem B1939099 : Blo 1723062 1939099 := bstep (se 1 (by rfl) ⟨1454324, by rfl⟩ : syracuseStep 1939099 = 2908649) B2908649
theorem B3880673 : Blo 1723062 3880673 := bstep (se 2 (by rfl) ⟨1455252, by rfl⟩ : syracuseStep 3880673 = 2910505) B2910505
theorem B13096727 : Blo 1723062 13096727 := bstep (se 1 (by rfl) ⟨9822545, by rfl⟩ : syracuseStep 13096727 = 19645091) B19645091
theorem B4142927 : Blo 1723062 4142927 := bstep (se 1 (by rfl) ⟨3107195, by rfl⟩ : syracuseStep 4142927 = 6214391) B6214391
theorem B12433277 : Blo 1723062 12433277 := bstep (se 3 (by rfl) ⟨2331239, by rfl⟩ : syracuseStep 12433277 = 4662479) B4662479
theorem B2586665 : Blo 1723062 2586665 := bstep (se 2 (by rfl) ⟨969999, by rfl⟩ : syracuseStep 2586665 = 1939999) B1939999
theorem B2586695 : Blo 1723062 2586695 := bstep (se 1 (by rfl) ⟨1940021, by rfl⟩ : syracuseStep 2586695 = 3880043) B3880043
theorem B6543443 : Blo 1723062 6543443 := bstep (se 1 (by rfl) ⟨4907582, by rfl⟩ : syracuseStep 6543443 = 9815165) B9815165
theorem B20969675 : Blo 1723062 20969675 := bstep (se 1 (by rfl) ⟨15727256, by rfl⟩ : syracuseStep 20969675 = 31454513) B31454513
theorem B3881195 : Blo 1723062 3881195 := bstep (se 1 (by rfl) ⟨2910896, by rfl⟩ : syracuseStep 3881195 = 5821793) B5821793
theorem B8280377 : Blo 1723062 8280377 := bstep (se 2 (by rfl) ⟨3105141, by rfl⟩ : syracuseStep 8280377 = 6210283) B6210283
theorem B4102483 : Blo 1723062 4102483 := bstep (se 1 (by rfl) ⟨3076862, by rfl⟩ : syracuseStep 4102483 = 6153725) B6153725
theorem B96926063 : Blo 1723062 96926063 := bstep (se 1 (by rfl) ⟨72694547, by rfl⟩ : syracuseStep 96926063 = 145389095) B145389095
theorem B2587079 : Blo 1723062 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B6543899 : Blo 1723062 6543899 := bstep (se 1 (by rfl) ⟨4907924, by rfl⟩ : syracuseStep 6543899 = 9815849) B9815849
theorem B3734057 : Blo 1723062 3734057 := bstep (se 2 (by rfl) ⟨1400271, by rfl⟩ : syracuseStep 3734057 = 2800543) B2800543
theorem B2587295 : Blo 1723062 2587295 := bstep (se 1 (by rfl) ⟨1940471, by rfl⟩ : syracuseStep 2587295 = 3880943) B3880943
theorem B9321131 : Blo 1723062 9321131 := bstep (se 1 (by rfl) ⟨6990848, by rfl⟩ : syracuseStep 9321131 = 13981697) B13981697
theorem B2587439 : Blo 1723062 2587439 := bstep (se 1 (by rfl) ⟨1940579, by rfl⟩ : syracuseStep 2587439 = 3881159) B3881159
theorem B1842031 : Blo 1723062 1842031 := bstep (se 1 (by rfl) ⟨1381523, by rfl⟩ : syracuseStep 1842031 = 2763047) B2763047
theorem B2587559 : Blo 1723062 2587559 := bstep (se 1 (by rfl) ⟨1940669, by rfl⟩ : syracuseStep 2587559 = 3881339) B3881339
theorem B8084843 : Blo 1723062 8084843 := bstep (se 1 (by rfl) ⟨6063632, by rfl⟩ : syracuseStep 8084843 = 12127265) B12127265
theorem B14720561 : Blo 1723062 14720561 := bstep (se 2 (by rfl) ⟨5520210, by rfl⟩ : syracuseStep 14720561 = 11040421) B11040421
theorem B5816231 : Blo 1723062 5816231 := bstep (se 1 (by rfl) ⟨4362173, by rfl⟩ : syracuseStep 5816231 = 8724347) B8724347
theorem B75571145 : Blo 1723062 75571145 := bstep (se 2 (by rfl) ⟨28339179, by rfl⟩ : syracuseStep 75571145 = 56678359) B56678359
theorem B188735777 : Blo 1723062 188735777 := bstep (se 2 (by rfl) ⟨70775916, by rfl⟩ : syracuseStep 188735777 = 141551833) B141551833
theorem B12427627 : Blo 1723062 12427627 := bstep (se 1 (by rfl) ⟨9320720, by rfl⟩ : syracuseStep 12427627 = 18641441) B18641441
theorem B71721449 : Blo 1723062 71721449 := bstep (se 2 (by rfl) ⟨26895543, by rfl⟩ : syracuseStep 71721449 = 53791087) B53791087
theorem B5898749 : Blo 1723062 5898749 := bstep (se 3 (by rfl) ⟨1106015, by rfl⟩ : syracuseStep 5898749 = 2212031) B2212031
theorem B3105335 : Blo 1723062 3105335 := bstep (se 1 (by rfl) ⟨2329001, by rfl⟩ : syracuseStep 3105335 = 4658003) B4658003
theorem B2908831 : Blo 1723062 2908831 := bstep (se 1 (by rfl) ⟨2181623, by rfl⟩ : syracuseStep 2908831 = 4363247) B4363247
theorem B5817095 : Blo 1723062 5817095 := bstep (se 1 (by rfl) ⟨4362821, by rfl⟩ : syracuseStep 5817095 = 8725643) B8725643
theorem B4907947 : Blo 1723062 4907947 := bstep (se 1 (by rfl) ⟨3680960, by rfl⟩ : syracuseStep 4907947 = 7361921) B7361921
theorem B6210557 : Blo 1723062 6210557 := bstep (se 3 (by rfl) ⟨1164479, by rfl⟩ : syracuseStep 6210557 = 2328959) B2328959
theorem B2761823 : Blo 1723062 2761823 := bstep (se 1 (by rfl) ⟨2071367, by rfl⟩ : syracuseStep 2761823 = 4142735) B4142735
theorem B2761951 : Blo 1723062 2761951 := bstep (se 1 (by rfl) ⟨2071463, by rfl⟩ : syracuseStep 2761951 = 4142927) B4142927
theorem B12420793 : Blo 1723062 12420793 := bstep (se 2 (by rfl) ⟨4657797, by rfl⟩ : syracuseStep 12420793 = 9315595) B9315595
theorem B22087403 : Blo 1723062 22087403 := bstep (se 1 (by rfl) ⟨16565552, by rfl⟩ : syracuseStep 22087403 = 33131105) B33131105
theorem B5818175 : Blo 1723062 5818175 := bstep (se 1 (by rfl) ⟨4363631, by rfl⟩ : syracuseStep 5818175 = 8727263) B8727263
theorem B5523337 : Blo 1723062 5523337 := bstep (se 2 (by rfl) ⟨2071251, by rfl⟩ : syracuseStep 5523337 = 4142503) B4142503
theorem B9824165 : Blo 1723062 9824165 := bstep (se 4 (by rfl) ⟨921015, by rfl⟩ : syracuseStep 9824165 = 1842031) B1842031
theorem B13092839 : Blo 1723062 13092839 := bstep (se 1 (by rfl) ⟨9819629, by rfl⟩ : syracuseStep 13092839 = 19639259) B19639259
theorem B4909177 : Blo 1723062 4909177 := bstep (se 2 (by rfl) ⟨1840941, by rfl⟩ : syracuseStep 4909177 = 3681883) B3681883
theorem B2181431 : Blo 1723062 2181431 := bstep (se 1 (by rfl) ⟨1636073, by rfl⟩ : syracuseStep 2181431 = 3272147) B3272147
theorem B2181583 : Blo 1723062 2181583 := bstep (se 1 (by rfl) ⟨1636187, by rfl⟩ : syracuseStep 2181583 = 3272375) B3272375
theorem B3877487 : Blo 1723062 3877487 := bstep (se 1 (by rfl) ⟨2908115, by rfl⟩ : syracuseStep 3877487 = 5816231) B5816231
theorem B1723135 : Blo 1723062 1723135 := bstep (se 1 (by rfl) ⟨1292351, by rfl⟩ : syracuseStep 1723135 = 2584703) B2584703
theorem B9816875 : Blo 1723062 9816875 := bstep (se 1 (by rfl) ⟨7362656, by rfl⟩ : syracuseStep 9816875 = 14725313) B14725313
theorem B3877703 : Blo 1723062 3877703 := bstep (se 1 (by rfl) ⟨2908277, by rfl⟩ : syracuseStep 3877703 = 5816555) B5816555
theorem B20982671 : Blo 1723062 20982671 := bstep (se 1 (by rfl) ⟨15737003, by rfl⟩ : syracuseStep 20982671 = 31474007) B31474007
theorem B1723559 : Blo 1723062 1723559 := bstep (se 1 (by rfl) ⟨1292669, by rfl⟩ : syracuseStep 1723559 = 2585339) B2585339
theorem B2329769 : Blo 1723062 2329769 := bstep (se 2 (by rfl) ⟨873663, by rfl⟩ : syracuseStep 2329769 = 1747327) B1747327
theorem B5819579 : Blo 1723062 5819579 := bstep (se 1 (by rfl) ⟨4364684, by rfl⟩ : syracuseStep 5819579 = 8729369) B8729369
theorem B13086035 : Blo 1723062 13086035 := bstep (se 1 (by rfl) ⟨9814526, by rfl⟩ : syracuseStep 13086035 = 19629053) B19629053
theorem B7974227 : Blo 1723062 7974227 := bstep (se 1 (by rfl) ⟨5980670, by rfl⟩ : syracuseStep 7974227 = 11961341) B11961341
theorem B2182555 : Blo 1723062 2182555 := bstep (se 1 (by rfl) ⟨1636916, by rfl⟩ : syracuseStep 2182555 = 3273833) B3273833
theorem B19901861 : Blo 1723062 19901861 := bstep (se 4 (by rfl) ⟨1865799, by rfl⟩ : syracuseStep 19901861 = 3731599) B3731599
theorem B1723855 : Blo 1723062 1723855 := bstep (se 1 (by rfl) ⟨1292891, by rfl⟩ : syracuseStep 1723855 = 2585783) B2585783
theorem B1724015 : Blo 1723062 1724015 := bstep (se 1 (by rfl) ⟨1293011, by rfl⟩ : syracuseStep 1724015 = 2586023) B2586023
theorem B258469501 : Blo 1723062 258469501 := bstep (se 3 (by rfl) ⟨48463031, by rfl⟩ : syracuseStep 258469501 = 96926063) B96926063
theorem B1724135 : Blo 1723062 1724135 := bstep (se 1 (by rfl) ⟨1293101, by rfl⟩ : syracuseStep 1724135 = 2586203) B2586203
theorem B44208017 : Blo 1723062 44208017 := bstep (se 2 (by rfl) ⟨16578006, by rfl⟩ : syracuseStep 44208017 = 33156013) B33156013
theorem B1724443 : Blo 1723062 1724443 := bstep (se 1 (by rfl) ⟨1293332, by rfl⟩ : syracuseStep 1724443 = 2586665) B2586665
theorem B2584607 : Blo 1723062 2584607 := bstep (se 1 (by rfl) ⟨1938455, by rfl⟩ : syracuseStep 2584607 = 3876911) B3876911
theorem B1724463 : Blo 1723062 1724463 := bstep (se 1 (by rfl) ⟨1293347, by rfl⟩ : syracuseStep 1724463 = 2586695) B2586695
theorem B2584631 : Blo 1723062 2584631 := bstep (se 1 (by rfl) ⟨1938473, by rfl⟩ : syracuseStep 2584631 = 3876947) B3876947
theorem B4362295 : Blo 1723062 4362295 := bstep (se 1 (by rfl) ⟨3271721, by rfl⟩ : syracuseStep 4362295 = 6543443) B6543443
theorem B9957485 : Blo 1723062 9957485 := bstep (se 3 (by rfl) ⟨1867028, by rfl⟩ : syracuseStep 9957485 = 3734057) B3734057
theorem B13979783 : Blo 1723062 13979783 := bstep (se 1 (by rfl) ⟨10484837, by rfl⟩ : syracuseStep 13979783 = 20969675) B20969675
theorem B2584751 : Blo 1723062 2584751 := bstep (se 1 (by rfl) ⟨1938563, by rfl⟩ : syracuseStep 2584751 = 3877127) B3877127
theorem B13087007 : Blo 1723062 13087007 := bstep (se 1 (by rfl) ⟨9815255, by rfl⟩ : syracuseStep 13087007 = 19630511) B19630511
theorem B1724719 : Blo 1723062 1724719 := bstep (se 1 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 1724719 = 2587079) B2587079
theorem B4911455 : Blo 1723062 4911455 := bstep (se 1 (by rfl) ⟨3683591, by rfl⟩ : syracuseStep 4911455 = 7367183) B7367183
theorem B4362599 : Blo 1723062 4362599 := bstep (se 1 (by rfl) ⟨3271949, by rfl⟩ : syracuseStep 4362599 = 6543899) B6543899
theorem B2584955 : Blo 1723062 2584955 := bstep (se 1 (by rfl) ⟨1938716, by rfl⟩ : syracuseStep 2584955 = 3877433) B3877433
theorem B3682721 : Blo 1723062 3682721 := bstep (se 2 (by rfl) ⟨1381020, by rfl⟩ : syracuseStep 3682721 = 2762041) B2762041
theorem B16560557 : Blo 1723062 16560557 := bstep (se 3 (by rfl) ⟨3105104, by rfl⟩ : syracuseStep 16560557 = 6210209) B6210209
theorem B1724863 : Blo 1723062 1724863 := bstep (se 1 (by rfl) ⟨1293647, by rfl⟩ : syracuseStep 1724863 = 2587295) B2587295
theorem B6214087 : Blo 1723062 6214087 := bstep (se 1 (by rfl) ⟨4660565, by rfl⟩ : syracuseStep 6214087 = 9321131) B9321131
theorem B1724959 : Blo 1723062 1724959 := bstep (se 1 (by rfl) ⟨1293719, by rfl⟩ : syracuseStep 1724959 = 2587439) B2587439
theorem B1725039 : Blo 1723062 1725039 := bstep (se 1 (by rfl) ⟨1293779, by rfl⟩ : syracuseStep 1725039 = 2587559) B2587559
theorem B2585225 : Blo 1723062 2585225 := bstep (se 2 (by rfl) ⟨969459, by rfl⟩ : syracuseStep 2585225 = 1938919) B1938919
theorem B14734061 : Blo 1723062 14734061 := bstep (se 3 (by rfl) ⟨2762636, by rfl⟩ : syracuseStep 14734061 = 5525273) B5525273
theorem B2585435 : Blo 1723062 2585435 := bstep (se 1 (by rfl) ⟨1939076, by rfl⟩ : syracuseStep 2585435 = 3878153) B3878153
theorem B2585465 : Blo 1723062 2585465 := bstep (se 2 (by rfl) ⟨969549, by rfl⟩ : syracuseStep 2585465 = 1939099) B1939099
theorem B8729531 : Blo 1723062 8729531 := bstep (se 1 (by rfl) ⟨6547148, by rfl⟩ : syracuseStep 8729531 = 13094297) B13094297
theorem B8729855 : Blo 1723062 8729855 := bstep (se 1 (by rfl) ⟨6547391, by rfl⟩ : syracuseStep 8729855 = 13094783) B13094783
theorem B4142447 : Blo 1723062 4142447 := bstep (se 1 (by rfl) ⟨3106835, by rfl⟩ : syracuseStep 4142447 = 6213671) B6213671
theorem B3880313 : Blo 1723062 3880313 := bstep (se 2 (by rfl) ⟨1455117, by rfl⟩ : syracuseStep 3880313 = 2910235) B2910235
theorem B765179291 : Blo 1723062 765179291 := bstep (se 1 (by rfl) ⟨573884468, by rfl⟩ : syracuseStep 765179291 = 1147768937) B1147768937
theorem B4363703 : Blo 1723062 4363703 := bstep (se 1 (by rfl) ⟨3272777, by rfl⟩ : syracuseStep 4363703 = 6545555) B6545555
theorem B2586095 : Blo 1723062 2586095 := bstep (se 1 (by rfl) ⟨1939571, by rfl⟩ : syracuseStep 2586095 = 3879143) B3879143
theorem B3880439 : Blo 1723062 3880439 := bstep (se 1 (by rfl) ⟨2910329, by rfl⟩ : syracuseStep 3880439 = 5820659) B5820659
theorem B2586215 : Blo 1723062 2586215 := bstep (se 1 (by rfl) ⟨1939661, by rfl⟩ : syracuseStep 2586215 = 3879323) B3879323
theorem B5469977 : Blo 1723062 5469977 := bstep (se 2 (by rfl) ⟨2051241, by rfl⟩ : syracuseStep 5469977 = 4102483) B4102483
theorem B8730665 : Blo 1723062 8730665 := bstep (se 2 (by rfl) ⟨3273999, by rfl⟩ : syracuseStep 8730665 = 6547999) B6547999
theorem B2586671 : Blo 1723062 2586671 := bstep (se 1 (by rfl) ⟨1940003, by rfl⟩ : syracuseStep 2586671 = 3880007) B3880007
theorem B1939567 : Blo 1723062 1939567 := bstep (se 1 (by rfl) ⟨1454675, by rfl⟩ : syracuseStep 1939567 = 2909351) B2909351
theorem B2586791 : Blo 1723062 2586791 := bstep (se 1 (by rfl) ⟨1940093, by rfl⟩ : syracuseStep 2586791 = 3880187) B3880187
theorem B13088951 : Blo 1723062 13088951 := bstep (se 1 (by rfl) ⟨9816713, by rfl⟩ : syracuseStep 13088951 = 19633427) B19633427
theorem B8730827 : Blo 1723062 8730827 := bstep (se 1 (by rfl) ⟨6548120, by rfl⟩ : syracuseStep 8730827 = 13096241) B13096241
theorem B7362809 : Blo 1723062 7362809 := bstep (se 2 (by rfl) ⟨2761053, by rfl⟩ : syracuseStep 7362809 = 5522107) B5522107
theorem B2586935 : Blo 1723062 2586935 := bstep (se 1 (by rfl) ⟨1940201, by rfl⟩ : syracuseStep 2586935 = 3880403) B3880403
theorem B103512431 : Blo 1723062 103512431 := bstep (se 1 (by rfl) ⟨77634323, by rfl⟩ : syracuseStep 103512431 = 155268647) B155268647
theorem B83925395 : Blo 1723062 83925395 := bstep (se 1 (by rfl) ⟨62944046, by rfl⟩ : syracuseStep 83925395 = 125888093) B125888093
theorem B2455967 : Blo 1723062 2455967 := bstep (se 1 (by rfl) ⟨1841975, by rfl⟩ : syracuseStep 2455967 = 3683951) B3683951
theorem B2587115 : Blo 1723062 2587115 := bstep (se 1 (by rfl) ⟨1940336, by rfl⟩ : syracuseStep 2587115 = 3880673) B3880673
theorem B8731151 : Blo 1723062 8731151 := bstep (se 1 (by rfl) ⟨6548363, by rfl⟩ : syracuseStep 8731151 = 13096727) B13096727
theorem B8288851 : Blo 1723062 8288851 := bstep (se 1 (by rfl) ⟨6216638, by rfl⟩ : syracuseStep 8288851 = 12433277) B12433277
theorem B1940071 : Blo 1723062 1940071 := bstep (se 1 (by rfl) ⟨1455053, by rfl⟩ : syracuseStep 1940071 = 2910107) B2910107
theorem B2587463 : Blo 1723062 2587463 := bstep (se 1 (by rfl) ⟨1940597, by rfl⟩ : syracuseStep 2587463 = 3881195) B3881195
theorem B5520251 : Blo 1723062 5520251 := bstep (se 1 (by rfl) ⟨4140188, by rfl⟩ : syracuseStep 5520251 = 8280377) B8280377
theorem B17685449 : Blo 1723062 17685449 := bstep (se 2 (by rfl) ⟨6632043, by rfl⟩ : syracuseStep 17685449 = 13264087) B13264087
theorem B4365535 : Blo 1723062 4365535 := bstep (se 1 (by rfl) ⟨3274151, by rfl⟩ : syracuseStep 4365535 = 6548303) B6548303
theorem B79633637 : Blo 1723062 79633637 := bstep (se 4 (by rfl) ⟨7465653, by rfl⟩ : syracuseStep 79633637 = 14931307) B14931307
theorem B5389895 : Blo 1723062 5389895 := bstep (se 1 (by rfl) ⟨4042421, by rfl⟩ : syracuseStep 5389895 = 8084843) B8084843
theorem B5815961 : Blo 1723062 5815961 := bstep (se 2 (by rfl) ⟨2180985, by rfl⟩ : syracuseStep 5815961 = 4361971) B4361971
theorem B9813707 : Blo 1723062 9813707 := bstep (se 1 (by rfl) ⟨7360280, by rfl⟩ : syracuseStep 9813707 = 14720561) B14720561
theorem B50380763 : Blo 1723062 50380763 := bstep (se 1 (by rfl) ⟨37785572, by rfl⟩ : syracuseStep 50380763 = 75571145) B75571145
theorem B5816393 : Blo 1723062 5816393 := bstep (se 2 (by rfl) ⟨2181147, by rfl⟩ : syracuseStep 5816393 = 4362295) B4362295
theorem B6545569 : Blo 1723062 6545569 := bstep (se 2 (by rfl) ⟨2454588, by rfl⟩ : syracuseStep 6545569 = 4909177) B4909177
theorem B8724671 : Blo 1723062 8724671 := bstep (se 1 (by rfl) ⟨6543503, by rfl⟩ : syracuseStep 8724671 = 13087007) B13087007
theorem B2908399 : Blo 1723062 2908399 := bstep (se 1 (by rfl) ⟨2181299, by rfl⟩ : syracuseStep 2908399 = 4362599) B4362599
theorem B9822707 : Blo 1723062 9822707 := bstep (se 1 (by rfl) ⟨7367030, by rfl⟩ : syracuseStep 9822707 = 14734061) B14734061
theorem B2908777 : Blo 1723062 2908777 := bstep (se 2 (by rfl) ⟨1090791, by rfl⟩ : syracuseStep 2908777 = 2181583) B2181583
theorem B11051801 : Blo 1723062 11051801 := bstep (se 2 (by rfl) ⟨4144425, by rfl⟩ : syracuseStep 11051801 = 8288851) B8288851
theorem B5817149 : Blo 1723062 5817149 := bstep (se 3 (by rfl) ⟨1090715, by rfl⟩ : syracuseStep 5817149 = 2181431) B2181431
theorem B2761631 : Blo 1723062 2761631 := bstep (se 1 (by rfl) ⟨2071223, by rfl⟩ : syracuseStep 2761631 = 4142447) B4142447
theorem B2909135 : Blo 1723062 2909135 := bstep (se 1 (by rfl) ⟨2181851, by rfl⟩ : syracuseStep 2909135 = 4363703) B4363703
theorem B3646651 : Blo 1723062 3646651 := bstep (se 1 (by rfl) ⟨2734988, by rfl⟩ : syracuseStep 3646651 = 5469977) B5469977
theorem B8725967 : Blo 1723062 8725967 := bstep (se 1 (by rfl) ⟨6544475, by rfl⟩ : syracuseStep 8725967 = 13088951) B13088951
theorem B4908539 : Blo 1723062 4908539 := bstep (se 1 (by rfl) ⟨3681404, by rfl⟩ : syracuseStep 4908539 = 7362809) B7362809
theorem B2910073 : Blo 1723062 2910073 := bstep (se 2 (by rfl) ⟨1091277, by rfl⟩ : syracuseStep 2910073 = 2182555) B2182555
theorem B3680167 : Blo 1723062 3680167 := bstep (se 1 (by rfl) ⟨2760125, by rfl⟩ : syracuseStep 3680167 = 5520251) B5520251
theorem B11790299 : Blo 1723062 11790299 := bstep (se 1 (by rfl) ⟨8842724, by rfl⟩ : syracuseStep 11790299 = 17685449) B17685449
theorem B3877307 : Blo 1723062 3877307 := bstep (se 1 (by rfl) ⟨2907980, by rfl⟩ : syracuseStep 3877307 = 5815961) B5815961
theorem B1723071 : Blo 1723062 1723071 := bstep (se 1 (by rfl) ⟨1292303, by rfl⟩ : syracuseStep 1723071 = 2584607) B2584607
theorem B1723087 : Blo 1723062 1723087 := bstep (se 1 (by rfl) ⟨1292315, by rfl⟩ : syracuseStep 1723087 = 2584631) B2584631
theorem B6638323 : Blo 1723062 6638323 := bstep (se 1 (by rfl) ⟨4978742, by rfl⟩ : syracuseStep 6638323 = 9957485) B9957485
theorem B1723167 : Blo 1723062 1723167 := bstep (se 1 (by rfl) ⟨1292375, by rfl⟩ : syracuseStep 1723167 = 2584751) B2584751
theorem B125823851 : Blo 1723062 125823851 := bstep (se 1 (by rfl) ⟨94367888, by rfl⟩ : syracuseStep 125823851 = 188735777) B188735777
theorem B1723303 : Blo 1723062 1723303 := bstep (se 1 (by rfl) ⟨1292477, by rfl⟩ : syracuseStep 1723303 = 2584955) B2584955
theorem B1723483 : Blo 1723062 1723483 := bstep (se 1 (by rfl) ⟨1292612, by rfl⟩ : syracuseStep 1723483 = 2585225) B2585225
theorem B6212717 : Blo 1723062 6212717 := bstep (se 3 (by rfl) ⟨1164884, by rfl⟩ : syracuseStep 6212717 = 2329769) B2329769
theorem B3878063 : Blo 1723062 3878063 := bstep (se 1 (by rfl) ⟨2908547, by rfl⟩ : syracuseStep 3878063 = 5817095) B5817095
theorem B1723623 : Blo 1723062 1723623 := bstep (se 1 (by rfl) ⟨1292717, by rfl⟩ : syracuseStep 1723623 = 2585435) B2585435
theorem B1723643 : Blo 1723062 1723643 := bstep (se 1 (by rfl) ⟨1292732, by rfl⟩ : syracuseStep 1723643 = 2585465) B2585465
theorem B5819687 : Blo 1723062 5819687 := bstep (se 1 (by rfl) ⟨4364765, by rfl⟩ : syracuseStep 5819687 = 8729531) B8729531
theorem B4140371 : Blo 1723062 4140371 := bstep (se 1 (by rfl) ⟨3105278, by rfl⟩ : syracuseStep 4140371 = 6210557) B6210557
theorem B5819903 : Blo 1723062 5819903 := bstep (se 1 (by rfl) ⟨4364927, by rfl⟩ : syracuseStep 5819903 = 8729855) B8729855
theorem B3878441 : Blo 1723062 3878441 := bstep (se 2 (by rfl) ⟨1454415, by rfl⟩ : syracuseStep 3878441 = 2908831) B2908831
theorem B510119527 : Blo 1723062 510119527 := bstep (se 1 (by rfl) ⟨382589645, by rfl⟩ : syracuseStep 510119527 = 765179291) B765179291
theorem B1724063 : Blo 1723062 1724063 := bstep (se 1 (by rfl) ⟨1293047, by rfl⟩ : syracuseStep 1724063 = 2586095) B2586095
theorem B1724143 : Blo 1723062 1724143 := bstep (se 1 (by rfl) ⟨1293107, by rfl⟩ : syracuseStep 1724143 = 2586215) B2586215
theorem B6549245 : Blo 1723062 6549245 := bstep (se 3 (by rfl) ⟨1227983, by rfl⟩ : syracuseStep 6549245 = 2455967) B2455967
theorem B14724935 : Blo 1723062 14724935 := bstep (se 1 (by rfl) ⟨11043701, by rfl⟩ : syracuseStep 14724935 = 22087403) B22087403
theorem B3878783 : Blo 1723062 3878783 := bstep (se 1 (by rfl) ⟨2909087, by rfl⟩ : syracuseStep 3878783 = 5818175) B5818175
theorem B6549443 : Blo 1723062 6549443 := bstep (se 1 (by rfl) ⟨4912082, by rfl⟩ : syracuseStep 6549443 = 9824165) B9824165
theorem B8728559 : Blo 1723062 8728559 := bstep (se 1 (by rfl) ⟨6546419, by rfl⟩ : syracuseStep 8728559 = 13092839) B13092839
theorem B5820443 : Blo 1723062 5820443 := bstep (se 1 (by rfl) ⟨4365332, by rfl⟩ : syracuseStep 5820443 = 8730665) B8730665
theorem B1724447 : Blo 1723062 1724447 := bstep (se 1 (by rfl) ⟨1293335, by rfl⟩ : syracuseStep 1724447 = 2586671) B2586671
theorem B1724527 : Blo 1723062 1724527 := bstep (se 1 (by rfl) ⟨1293395, by rfl⟩ : syracuseStep 1724527 = 2586791) B2586791
theorem B5820551 : Blo 1723062 5820551 := bstep (se 1 (by rfl) ⟨4365413, by rfl⟩ : syracuseStep 5820551 = 8730827) B8730827
theorem B1724623 : Blo 1723062 1724623 := bstep (se 1 (by rfl) ⟨1293467, by rfl⟩ : syracuseStep 1724623 = 2586935) B2586935
theorem B3682601 : Blo 1723062 3682601 := bstep (se 2 (by rfl) ⟨1380975, by rfl⟩ : syracuseStep 3682601 = 2761951) B2761951
theorem B5820713 : Blo 1723062 5820713 := bstep (se 2 (by rfl) ⟨2182767, by rfl⟩ : syracuseStep 5820713 = 4365535) B4365535
theorem B1724743 : Blo 1723062 1724743 := bstep (se 1 (by rfl) ⟨1293557, by rfl⟩ : syracuseStep 1724743 = 2587115) B2587115
theorem B5820767 : Blo 1723062 5820767 := bstep (se 1 (by rfl) ⟨4365575, by rfl⟩ : syracuseStep 5820767 = 8731151) B8731151
theorem B2584991 : Blo 1723062 2584991 := bstep (se 1 (by rfl) ⟨1938743, by rfl⟩ : syracuseStep 2584991 = 3877487) B3877487
theorem B2585135 : Blo 1723062 2585135 := bstep (se 1 (by rfl) ⟨1938851, by rfl⟩ : syracuseStep 2585135 = 3877703) B3877703
theorem B1724975 : Blo 1723062 1724975 := bstep (se 1 (by rfl) ⟨1293731, by rfl⟩ : syracuseStep 1724975 = 2587463) B2587463
theorem B13988447 : Blo 1723062 13988447 := bstep (se 1 (by rfl) ⟨10491335, by rfl⟩ : syracuseStep 13988447 = 20982671) B20982671
theorem B3879719 : Blo 1723062 3879719 := bstep (se 1 (by rfl) ⟨2909789, by rfl⟩ : syracuseStep 3879719 = 5819579) B5819579
theorem B53089091 : Blo 1723062 53089091 := bstep (se 1 (by rfl) ⟨39816818, by rfl⟩ : syracuseStep 53089091 = 79633637) B79633637
theorem B344626001 : Blo 1723062 344626001 := bstep (se 2 (by rfl) ⟨129234750, by rfl⟩ : syracuseStep 344626001 = 258469501) B258469501
theorem B16561057 : Blo 1723062 16561057 := bstep (se 2 (by rfl) ⟨6210396, by rfl⟩ : syracuseStep 16561057 = 12420793) B12420793
theorem B13267907 : Blo 1723062 13267907 := bstep (se 1 (by rfl) ⟨9950930, by rfl⟩ : syracuseStep 13267907 = 19901861) B19901861
theorem B33141797 : Blo 1723062 33141797 := bstep (se 4 (by rfl) ⟨3107043, by rfl⟩ : syracuseStep 33141797 = 6214087) B6214087
theorem B3593263 : Blo 1723062 3593263 := bstep (se 1 (by rfl) ⟨2694947, by rfl⟩ : syracuseStep 3593263 = 5389895) B5389895
theorem B6542471 : Blo 1723062 6542471 := bstep (se 1 (by rfl) ⟨4906853, by rfl⟩ : syracuseStep 6542471 = 9813707) B9813707
theorem B29472011 : Blo 1723062 29472011 := bstep (se 1 (by rfl) ⟨22104008, by rfl⟩ : syracuseStep 29472011 = 44208017) B44208017
theorem B62919989 : Blo 1723062 62919989 := bstep (se 5 (by rfl) ⟨2949374, by rfl⟩ : syracuseStep 62919989 = 5898749) B5898749
theorem B9319855 : Blo 1723062 9319855 := bstep (se 1 (by rfl) ⟨6989891, by rfl⟩ : syracuseStep 9319855 = 13979783) B13979783
theorem B2586089 : Blo 1723062 2586089 := bstep (se 2 (by rfl) ⟨969783, by rfl⟩ : syracuseStep 2586089 = 1939567) B1939567
theorem B2455147 : Blo 1723062 2455147 := bstep (se 1 (by rfl) ⟨1841360, by rfl⟩ : syracuseStep 2455147 = 3682721) B3682721
theorem B11040371 : Blo 1723062 11040371 := bstep (se 1 (by rfl) ⟨8280278, by rfl⟩ : syracuseStep 11040371 = 16560557) B16560557
theorem B47814299 : Blo 1723062 47814299 := bstep (se 1 (by rfl) ⟨35860724, by rfl⟩ : syracuseStep 47814299 = 71721449) B71721449
theorem B16570169 : Blo 1723062 16570169 := bstep (se 2 (by rfl) ⟨6213813, by rfl⟩ : syracuseStep 16570169 = 12427627) B12427627
theorem B1841215 : Blo 1723062 1841215 := bstep (se 1 (by rfl) ⟨1380911, by rfl⟩ : syracuseStep 1841215 = 2761823) B2761823
theorem B2586761 : Blo 1723062 2586761 := bstep (se 2 (by rfl) ⟨970035, by rfl⟩ : syracuseStep 2586761 = 1940071) B1940071
theorem B21264605 : Blo 1723062 21264605 := bstep (se 3 (by rfl) ⟨3987113, by rfl⟩ : syracuseStep 21264605 = 7974227) B7974227
theorem B2586875 : Blo 1723062 2586875 := bstep (se 1 (by rfl) ⟨1940156, by rfl⟩ : syracuseStep 2586875 = 3880313) B3880313
theorem B13097213 : Blo 1723062 13097213 := bstep (se 3 (by rfl) ⟨2455727, by rfl⟩ : syracuseStep 13097213 = 4911455) B4911455
theorem B2586959 : Blo 1723062 2586959 := bstep (se 1 (by rfl) ⟨1940219, by rfl⟩ : syracuseStep 2586959 = 3880439) B3880439
theorem B6543929 : Blo 1723062 6543929 := bstep (se 2 (by rfl) ⟨2453973, by rfl⟩ : syracuseStep 6543929 = 4907947) B4907947
theorem B8280893 : Blo 1723062 8280893 := bstep (se 3 (by rfl) ⟨1552667, by rfl⟩ : syracuseStep 8280893 = 3105335) B3105335
theorem B69008287 : Blo 1723062 69008287 := bstep (se 1 (by rfl) ⟨51756215, by rfl⟩ : syracuseStep 69008287 = 103512431) B103512431
theorem B55950263 : Blo 1723062 55950263 := bstep (se 1 (by rfl) ⟨41962697, by rfl⟩ : syracuseStep 55950263 = 83925395) B83925395
theorem B6544583 : Blo 1723062 6544583 := bstep (se 1 (by rfl) ⟨4908437, by rfl⟩ : syracuseStep 6544583 = 9816875) B9816875
theorem B8724023 : Blo 1723062 8724023 := bstep (se 1 (by rfl) ⟨6543017, by rfl⟩ : syracuseStep 8724023 = 13086035) B13086035
theorem B7364449 : Blo 1723062 7364449 := bstep (se 2 (by rfl) ⟨2761668, by rfl⟩ : syracuseStep 7364449 = 5523337) B5523337
theorem B134348701 : Blo 1723062 134348701 := bstep (se 3 (by rfl) ⟨25190381, by rfl⟩ : syracuseStep 134348701 = 50380763) B50380763
theorem B5816447 : Blo 1723062 5816447 := bstep (se 1 (by rfl) ⟨4362335, by rfl⟩ : syracuseStep 5816447 = 8724671) B8724671
theorem B22094531 : Blo 1723062 22094531 := bstep (se 1 (by rfl) ⟨16570898, by rfl⟩ : syracuseStep 22094531 = 33141797) B33141797
theorem B5817311 : Blo 1723062 5817311 := bstep (se 1 (by rfl) ⟨4362983, by rfl⟩ : syracuseStep 5817311 = 8725967) B8725967
theorem B31876199 : Blo 1723062 31876199 := bstep (se 1 (by rfl) ⟨23907149, by rfl⟩ : syracuseStep 31876199 = 47814299) B47814299
theorem B37300175 : Blo 1723062 37300175 := bstep (se 1 (by rfl) ⟨27975131, by rfl⟩ : syracuseStep 37300175 = 55950263) B55950263
theorem B680159369 : Blo 1723062 680159369 := bstep (se 2 (by rfl) ⟨255059763, by rfl⟩ : syracuseStep 680159369 = 510119527) B510119527
theorem B9816623 : Blo 1723062 9816623 := bstep (se 1 (by rfl) ⟨7362467, by rfl⟩ : syracuseStep 9816623 = 14724935) B14724935
theorem B5819039 : Blo 1723062 5819039 := bstep (se 1 (by rfl) ⟨4364279, by rfl⟩ : syracuseStep 5819039 = 8728559) B8728559
theorem B3877595 : Blo 1723062 3877595 := bstep (se 1 (by rfl) ⟨2908196, by rfl⟩ : syracuseStep 3877595 = 5816393) B5816393
theorem B8727425 : Blo 1723062 8727425 := bstep (se 2 (by rfl) ⟨3272784, by rfl⟩ : syracuseStep 8727425 = 6545569) B6545569
theorem B1723327 : Blo 1723062 1723327 := bstep (se 1 (by rfl) ⟨1292495, by rfl⟩ : syracuseStep 1723327 = 2584991) B2584991
theorem B3877865 : Blo 1723062 3877865 := bstep (se 2 (by rfl) ⟨1454199, by rfl⟩ : syracuseStep 3877865 = 2908399) B2908399
theorem B6548471 : Blo 1723062 6548471 := bstep (se 1 (by rfl) ⟨4911353, by rfl⟩ : syracuseStep 6548471 = 9822707) B9822707
theorem B1723423 : Blo 1723062 1723423 := bstep (se 1 (by rfl) ⟨1292567, by rfl⟩ : syracuseStep 1723423 = 2585135) B2585135
theorem B9325631 : Blo 1723062 9325631 := bstep (se 1 (by rfl) ⟨6994223, by rfl⟩ : syracuseStep 9325631 = 13988447) B13988447
theorem B7367867 : Blo 1723062 7367867 := bstep (se 1 (by rfl) ⟨5525900, by rfl⟩ : syracuseStep 7367867 = 11051801) B11051801
theorem B3878099 : Blo 1723062 3878099 := bstep (se 1 (by rfl) ⟨2908574, by rfl⟩ : syracuseStep 3878099 = 5817149) B5817149
theorem B35392727 : Blo 1723062 35392727 := bstep (se 1 (by rfl) ⟨26544545, by rfl⟩ : syracuseStep 35392727 = 53089091) B53089091
theorem B4361647 : Blo 1723062 4361647 := bstep (se 1 (by rfl) ⟨3271235, by rfl⟩ : syracuseStep 4361647 = 6542471) B6542471
theorem B3878369 : Blo 1723062 3878369 := bstep (se 2 (by rfl) ⟨1454388, by rfl⟩ : syracuseStep 3878369 = 2908777) B2908777
theorem B19648007 : Blo 1723062 19648007 := bstep (se 1 (by rfl) ⟨14736005, by rfl⟩ : syracuseStep 19648007 = 29472011) B29472011
theorem B41946659 : Blo 1723062 41946659 := bstep (se 1 (by rfl) ⟨31459994, by rfl⟩ : syracuseStep 41946659 = 62919989) B62919989
theorem B1724059 : Blo 1723062 1724059 := bstep (se 1 (by rfl) ⟨1293044, by rfl⟩ : syracuseStep 1724059 = 2586089) B2586089
theorem B8851097 : Blo 1723062 8851097 := bstep (se 2 (by rfl) ⟨3319161, by rfl⟩ : syracuseStep 8851097 = 6638323) B6638323
theorem B7360247 : Blo 1723062 7360247 := bstep (se 1 (by rfl) ⟨5520185, by rfl⟩ : syracuseStep 7360247 = 11040371) B11040371
theorem B11046779 : Blo 1723062 11046779 := bstep (se 1 (by rfl) ⟨8285084, by rfl⟩ : syracuseStep 11046779 = 16570169) B16570169
theorem B22081409 : Blo 1723062 22081409 := bstep (se 2 (by rfl) ⟨8280528, by rfl⟩ : syracuseStep 22081409 = 16561057) B16561057
theorem B7860199 : Blo 1723062 7860199 := bstep (se 1 (by rfl) ⟨5895149, by rfl⟩ : syracuseStep 7860199 = 11790299) B11790299
theorem B1724507 : Blo 1723062 1724507 := bstep (se 1 (by rfl) ⟨1293380, by rfl⟩ : syracuseStep 1724507 = 2586761) B2586761
theorem B14176403 : Blo 1723062 14176403 := bstep (se 1 (by rfl) ⟨10632302, by rfl⟩ : syracuseStep 14176403 = 21264605) B21264605
theorem B1724583 : Blo 1723062 1724583 := bstep (se 1 (by rfl) ⟨1293437, by rfl⟩ : syracuseStep 1724583 = 2586875) B2586875
theorem B1724639 : Blo 1723062 1724639 := bstep (se 1 (by rfl) ⟨1293479, by rfl⟩ : syracuseStep 1724639 = 2586959) B2586959
theorem B4862201 : Blo 1723062 4862201 := bstep (se 2 (by rfl) ⟨1823325, by rfl⟩ : syracuseStep 4862201 = 3646651) B3646651
theorem B2584871 : Blo 1723062 2584871 := bstep (se 1 (by rfl) ⟨1938653, by rfl⟩ : syracuseStep 2584871 = 3877307) B3877307
theorem B4362619 : Blo 1723062 4362619 := bstep (se 1 (by rfl) ⟨3271964, by rfl⟩ : syracuseStep 4362619 = 6543929) B6543929
theorem B83882567 : Blo 1723062 83882567 := bstep (se 1 (by rfl) ⟨62911925, by rfl⟩ : syracuseStep 83882567 = 125823851) B125823851
theorem B4141811 : Blo 1723062 4141811 := bstep (se 1 (by rfl) ⟨3106358, by rfl⟩ : syracuseStep 4141811 = 6212717) B6212717
theorem B2585375 : Blo 1723062 2585375 := bstep (se 1 (by rfl) ⟨1939031, by rfl⟩ : syracuseStep 2585375 = 3878063) B3878063
theorem B4363055 : Blo 1723062 4363055 := bstep (se 1 (by rfl) ⟨3272291, by rfl⟩ : syracuseStep 4363055 = 6544583) B6544583
theorem B3273529 : Blo 1723062 3273529 := bstep (se 2 (by rfl) ⟨1227573, by rfl⟩ : syracuseStep 3273529 = 2455147) B2455147
theorem B22082381 : Blo 1723062 22082381 := bstep (se 3 (by rfl) ⟨4140446, by rfl⟩ : syracuseStep 22082381 = 8280893) B8280893
theorem B3879791 : Blo 1723062 3879791 := bstep (se 1 (by rfl) ⟨2909843, by rfl⟩ : syracuseStep 3879791 = 5819687) B5819687
theorem B3879935 : Blo 1723062 3879935 := bstep (se 1 (by rfl) ⟨2909951, by rfl⟩ : syracuseStep 3879935 = 5819903) B5819903
theorem B2585627 : Blo 1723062 2585627 := bstep (se 1 (by rfl) ⟨1939220, by rfl⟩ : syracuseStep 2585627 = 3878441) B3878441
theorem B9819265 : Blo 1723062 9819265 := bstep (se 2 (by rfl) ⟨3682224, by rfl⟩ : syracuseStep 9819265 = 7364449) B7364449
theorem B3880097 : Blo 1723062 3880097 := bstep (se 2 (by rfl) ⟨1455036, by rfl⟩ : syracuseStep 3880097 = 2910073) B2910073
theorem B179131601 : Blo 1723062 179131601 := bstep (se 2 (by rfl) ⟨67174350, by rfl⟩ : syracuseStep 179131601 = 134348701) B134348701
theorem B2585855 : Blo 1723062 2585855 := bstep (se 1 (by rfl) ⟨1939391, by rfl⟩ : syracuseStep 2585855 = 3878783) B3878783
theorem B3880295 : Blo 1723062 3880295 := bstep (se 1 (by rfl) ⟨2910221, by rfl⟩ : syracuseStep 3880295 = 5820443) B5820443
theorem B2454953 : Blo 1723062 2454953 := bstep (se 2 (by rfl) ⟨920607, by rfl⟩ : syracuseStep 2454953 = 1841215) B1841215
theorem B3880367 : Blo 1723062 3880367 := bstep (se 1 (by rfl) ⟨2910275, by rfl⟩ : syracuseStep 3880367 = 5820551) B5820551
theorem B2455067 : Blo 1723062 2455067 := bstep (se 1 (by rfl) ⟨1841300, by rfl⟩ : syracuseStep 2455067 = 3682601) B3682601
theorem B3880475 : Blo 1723062 3880475 := bstep (se 1 (by rfl) ⟨2910356, by rfl⟩ : syracuseStep 3880475 = 5820713) B5820713
theorem B3880511 : Blo 1723062 3880511 := bstep (se 1 (by rfl) ⟨2910383, by rfl⟩ : syracuseStep 3880511 = 5820767) B5820767
theorem B2586479 : Blo 1723062 2586479 := bstep (se 1 (by rfl) ⟨1939859, by rfl⟩ : syracuseStep 2586479 = 3879719) B3879719
theorem B229750667 : Blo 1723062 229750667 := bstep (se 1 (by rfl) ⟨172313000, by rfl⟩ : syracuseStep 229750667 = 344626001) B344626001
theorem B1841087 : Blo 1723062 1841087 := bstep (se 1 (by rfl) ⟨1380815, by rfl⟩ : syracuseStep 1841087 = 2761631) B2761631
theorem B8845271 : Blo 1723062 8845271 := bstep (se 1 (by rfl) ⟨6633953, by rfl⟩ : syracuseStep 8845271 = 13267907) B13267907
theorem B1939423 : Blo 1723062 1939423 := bstep (se 1 (by rfl) ⟨1454567, by rfl⟩ : syracuseStep 1939423 = 2909135) B2909135
theorem B92011049 : Blo 1723062 92011049 := bstep (se 2 (by rfl) ⟨34504143, by rfl⟩ : syracuseStep 92011049 = 69008287) B69008287
theorem B13089437 : Blo 1723062 13089437 := bstep (se 3 (by rfl) ⟨2454269, by rfl⟩ : syracuseStep 13089437 = 4908539) B4908539
theorem B4791017 : Blo 1723062 4791017 := bstep (se 2 (by rfl) ⟨1796631, by rfl⟩ : syracuseStep 4791017 = 3593263) B3593263
theorem B8731475 : Blo 1723062 8731475 := bstep (se 1 (by rfl) ⟨6548606, by rfl⟩ : syracuseStep 8731475 = 13097213) B13097213
theorem B12426473 : Blo 1723062 12426473 := bstep (se 2 (by rfl) ⟨4659927, by rfl⟩ : syracuseStep 12426473 = 9319855) B9319855
theorem B2760247 : Blo 1723062 2760247 := bstep (se 1 (by rfl) ⟨2070185, by rfl⟩ : syracuseStep 2760247 = 4140371) B4140371
theorem B5816015 : Blo 1723062 5816015 := bstep (se 1 (by rfl) ⟨4362011, by rfl⟩ : syracuseStep 5816015 = 8724023) B8724023
theorem B4366163 : Blo 1723062 4366163 := bstep (se 1 (by rfl) ⟨3274622, by rfl⟩ : syracuseStep 4366163 = 6549245) B6549245
theorem B4906889 : Blo 1723062 4906889 := bstep (se 2 (by rfl) ⟨1840083, by rfl⟩ : syracuseStep 4906889 = 3680167) B3680167
theorem B4366295 : Blo 1723062 4366295 := bstep (se 1 (by rfl) ⟨3274721, by rfl⟩ : syracuseStep 4366295 = 6549443) B6549443
theorem B14729687 : Blo 1723062 14729687 := bstep (se 1 (by rfl) ⟨11047265, by rfl⟩ : syracuseStep 14729687 = 22094531) B22094531
theorem B5816825 : Blo 1723062 5816825 := bstep (se 2 (by rfl) ⟨2181309, by rfl⟩ : syracuseStep 5816825 = 4362619) B4362619
theorem B2908703 : Blo 1723062 2908703 := bstep (se 1 (by rfl) ⟨2181527, by rfl⟩ : syracuseStep 2908703 = 4363055) B4363055
theorem B14721587 : Blo 1723062 14721587 := bstep (se 1 (by rfl) ⟨11041190, by rfl⟩ : syracuseStep 14721587 = 22082381) B22082381
theorem B21250799 : Blo 1723062 21250799 := bstep (se 1 (by rfl) ⟨15938099, by rfl⟩ : syracuseStep 21250799 = 31876199) B31876199
theorem B6546541 : Blo 1723062 6546541 := bstep (se 3 (by rfl) ⟨1227476, by rfl⟩ : syracuseStep 6546541 = 2454953) B2454953
theorem B153167111 : Blo 1723062 153167111 := bstep (se 1 (by rfl) ⟨114875333, by rfl⟩ : syracuseStep 153167111 = 229750667) B229750667
theorem B6546845 : Blo 1723062 6546845 := bstep (se 3 (by rfl) ⟨1227533, by rfl⟩ : syracuseStep 6546845 = 2455067) B2455067
theorem B13092353 : Blo 1723062 13092353 := bstep (se 2 (by rfl) ⟨4909632, by rfl⟩ : syracuseStep 13092353 = 9819265) B9819265
theorem B8726291 : Blo 1723062 8726291 := bstep (se 1 (by rfl) ⟨6544718, by rfl⟩ : syracuseStep 8726291 = 13089437) B13089437
theorem B5818283 : Blo 1723062 5818283 := bstep (se 1 (by rfl) ⟨4363712, by rfl⟩ : syracuseStep 5818283 = 8727425) B8727425
theorem B11044829 : Blo 1723062 11044829 := bstep (se 3 (by rfl) ⟨2070905, by rfl⟩ : syracuseStep 11044829 = 4141811) B4141811
theorem B3680329 : Blo 1723062 3680329 := bstep (se 2 (by rfl) ⟨1380123, by rfl⟩ : syracuseStep 3680329 = 2760247) B2760247
theorem B23595151 : Blo 1723062 23595151 := bstep (se 1 (by rfl) ⟨17696363, by rfl⟩ : syracuseStep 23595151 = 35392727) B35392727
theorem B8284315 : Blo 1723062 8284315 := bstep (se 1 (by rfl) ⟨6213236, by rfl⟩ : syracuseStep 8284315 = 12426473) B12426473
theorem B5900731 : Blo 1723062 5900731 := bstep (se 1 (by rfl) ⟨4425548, by rfl⟩ : syracuseStep 5900731 = 8851097) B8851097
theorem B3877343 : Blo 1723062 3877343 := bstep (se 1 (by rfl) ⟨2908007, by rfl⟩ : syracuseStep 3877343 = 5816015) B5816015
theorem B4909565 : Blo 1723062 4909565 := bstep (se 3 (by rfl) ⟨920543, by rfl⟩ : syracuseStep 4909565 = 1841087) B1841087
theorem B2910775 : Blo 1723062 2910775 := bstep (se 1 (by rfl) ⟨2183081, by rfl⟩ : syracuseStep 2910775 = 4366163) B4366163
theorem B3271259 : Blo 1723062 3271259 := bstep (se 1 (by rfl) ⟨2453444, by rfl⟩ : syracuseStep 3271259 = 4906889) B4906889
theorem B10480265 : Blo 1723062 10480265 := bstep (se 2 (by rfl) ⟨3930099, by rfl⟩ : syracuseStep 10480265 = 7860199) B7860199
theorem B2910863 : Blo 1723062 2910863 := bstep (se 1 (by rfl) ⟨2183147, by rfl⟩ : syracuseStep 2910863 = 4366295) B4366295
theorem B3877631 : Blo 1723062 3877631 := bstep (se 1 (by rfl) ⟨2908223, by rfl⟩ : syracuseStep 3877631 = 5816447) B5816447
theorem B1723247 : Blo 1723062 1723247 := bstep (se 1 (by rfl) ⟨1292435, by rfl⟩ : syracuseStep 1723247 = 2584871) B2584871
theorem B55921711 : Blo 1723062 55921711 := bstep (se 1 (by rfl) ⟨41941283, by rfl⟩ : syracuseStep 55921711 = 83882567) B83882567
theorem B1723583 : Blo 1723062 1723583 := bstep (se 1 (by rfl) ⟨1292687, by rfl⟩ : syracuseStep 1723583 = 2585375) B2585375
theorem B3878207 : Blo 1723062 3878207 := bstep (se 1 (by rfl) ⟨2908655, by rfl⟩ : syracuseStep 3878207 = 5817311) B5817311
theorem B1723751 : Blo 1723062 1723751 := bstep (se 1 (by rfl) ⟨1292813, by rfl⟩ : syracuseStep 1723751 = 2585627) B2585627
theorem B1723903 : Blo 1723062 1723903 := bstep (se 1 (by rfl) ⟨1292927, by rfl⟩ : syracuseStep 1723903 = 2585855) B2585855
theorem B1724319 : Blo 1723062 1724319 := bstep (se 1 (by rfl) ⟨1293239, by rfl⟩ : syracuseStep 1724319 = 2586479) B2586479
theorem B24866783 : Blo 1723062 24866783 := bstep (se 1 (by rfl) ⟨18650087, by rfl⟩ : syracuseStep 24866783 = 37300175) B37300175
theorem B453439579 : Blo 1723062 453439579 := bstep (se 1 (by rfl) ⟨340079684, by rfl⟩ : syracuseStep 453439579 = 680159369) B680159369
theorem B3879359 : Blo 1723062 3879359 := bstep (se 1 (by rfl) ⟨2909519, by rfl⟩ : syracuseStep 3879359 = 5819039) B5819039
theorem B2585063 : Blo 1723062 2585063 := bstep (se 1 (by rfl) ⟨1938797, by rfl⟩ : syracuseStep 2585063 = 3877595) B3877595
theorem B5820983 : Blo 1723062 5820983 := bstep (se 1 (by rfl) ⟨4365737, by rfl⟩ : syracuseStep 5820983 = 8731475) B8731475
theorem B2585243 : Blo 1723062 2585243 := bstep (se 1 (by rfl) ⟨1938932, by rfl⟩ : syracuseStep 2585243 = 3877865) B3877865
theorem B4911911 : Blo 1723062 4911911 := bstep (se 1 (by rfl) ⟨3683933, by rfl⟩ : syracuseStep 4911911 = 7367867) B7367867
theorem B2585399 : Blo 1723062 2585399 := bstep (se 1 (by rfl) ⟨1939049, by rfl⟩ : syracuseStep 2585399 = 3878099) B3878099
theorem B2585579 : Blo 1723062 2585579 := bstep (se 1 (by rfl) ⟨1939184, by rfl⟩ : syracuseStep 2585579 = 3878369) B3878369
theorem B27964439 : Blo 1723062 27964439 := bstep (se 1 (by rfl) ⟨20973329, by rfl⟩ : syracuseStep 27964439 = 41946659) B41946659
theorem B2585897 : Blo 1723062 2585897 := bstep (se 2 (by rfl) ⟨969711, by rfl⟩ : syracuseStep 2585897 = 1939423) B1939423
theorem B9450935 : Blo 1723062 9450935 := bstep (se 1 (by rfl) ⟨7088201, by rfl⟩ : syracuseStep 9450935 = 14176403) B14176403
theorem B2586527 : Blo 1723062 2586527 := bstep (se 1 (by rfl) ⟨1939895, by rfl⟩ : syracuseStep 2586527 = 3879791) B3879791
theorem B12965869 : Blo 1723062 12965869 := bstep (se 3 (by rfl) ⟨2431100, by rfl⟩ : syracuseStep 12965869 = 4862201) B4862201
theorem B2586623 : Blo 1723062 2586623 := bstep (se 1 (by rfl) ⟨1939967, by rfl⟩ : syracuseStep 2586623 = 3879935) B3879935
theorem B2586731 : Blo 1723062 2586731 := bstep (se 1 (by rfl) ⟨1940048, by rfl⟩ : syracuseStep 2586731 = 3880097) B3880097
theorem B119421067 : Blo 1723062 119421067 := bstep (se 1 (by rfl) ⟨89565800, by rfl⟩ : syracuseStep 119421067 = 179131601) B179131601
theorem B2586863 : Blo 1723062 2586863 := bstep (se 1 (by rfl) ⟨1940147, by rfl⟩ : syracuseStep 2586863 = 3880295) B3880295
theorem B2586911 : Blo 1723062 2586911 := bstep (se 1 (by rfl) ⟨1940183, by rfl⟩ : syracuseStep 2586911 = 3880367) B3880367
theorem B2586983 : Blo 1723062 2586983 := bstep (se 1 (by rfl) ⟨1940237, by rfl⟩ : syracuseStep 2586983 = 3880475) B3880475
theorem B2587007 : Blo 1723062 2587007 := bstep (se 1 (by rfl) ⟨1940255, by rfl⟩ : syracuseStep 2587007 = 3880511) B3880511
theorem B4364705 : Blo 1723062 4364705 := bstep (se 2 (by rfl) ⟨1636764, by rfl⟩ : syracuseStep 4364705 = 3273529) B3273529
theorem B5896847 : Blo 1723062 5896847 := bstep (se 1 (by rfl) ⟨4422635, by rfl⟩ : syracuseStep 5896847 = 8845271) B8845271
theorem B61340699 : Blo 1723062 61340699 := bstep (se 1 (by rfl) ⟨46005524, by rfl⟩ : syracuseStep 61340699 = 92011049) B92011049
theorem B6544415 : Blo 1723062 6544415 := bstep (se 1 (by rfl) ⟨4908311, by rfl⟩ : syracuseStep 6544415 = 9816623) B9816623
theorem B3194011 : Blo 1723062 3194011 := bstep (se 1 (by rfl) ⟨2395508, by rfl⟩ : syracuseStep 3194011 = 4791017) B4791017
theorem B5815529 : Blo 1723062 5815529 := bstep (se 2 (by rfl) ⟨2180823, by rfl⟩ : syracuseStep 5815529 = 4361647) B4361647
theorem B4365647 : Blo 1723062 4365647 := bstep (se 1 (by rfl) ⟨3274235, by rfl⟩ : syracuseStep 4365647 = 6548471) B6548471
theorem B6217087 : Blo 1723062 6217087 := bstep (se 1 (by rfl) ⟨4662815, by rfl⟩ : syracuseStep 6217087 = 9325631) B9325631
theorem B13098671 : Blo 1723062 13098671 := bstep (se 1 (by rfl) ⟨9824003, by rfl⟩ : syracuseStep 13098671 = 19648007) B19648007
theorem B4906831 : Blo 1723062 4906831 := bstep (se 1 (by rfl) ⟨3680123, by rfl⟩ : syracuseStep 4906831 = 7360247) B7360247
theorem B7364519 : Blo 1723062 7364519 := bstep (se 1 (by rfl) ⟨5523389, by rfl⟩ : syracuseStep 7364519 = 11046779) B11046779
theorem B14720939 : Blo 1723062 14720939 := bstep (se 1 (by rfl) ⟨11040704, by rfl⟩ : syracuseStep 14720939 = 22081409) B22081409
theorem B4907105 : Blo 1723062 4907105 := bstep (se 2 (by rfl) ⟨1840164, by rfl⟩ : syracuseStep 4907105 = 3680329) B3680329
theorem B604586105 : Blo 1723062 604586105 := bstep (se 2 (by rfl) ⟨226719789, by rfl⟩ : syracuseStep 604586105 = 453439579) B453439579
theorem B159228089 : Blo 1723062 159228089 := bstep (se 2 (by rfl) ⟨59710533, by rfl⟩ : syracuseStep 159228089 = 119421067) B119421067
theorem B9814391 : Blo 1723062 9814391 := bstep (se 1 (by rfl) ⟨7360793, by rfl⟩ : syracuseStep 9814391 = 14721587) B14721587
theorem B6300623 : Blo 1723062 6300623 := bstep (se 1 (by rfl) ⟨4725467, by rfl⟩ : syracuseStep 6300623 = 9450935) B9450935
theorem B5817527 : Blo 1723062 5817527 := bstep (se 1 (by rfl) ⟨4363145, by rfl⟩ : syracuseStep 5817527 = 8726291) B8726291
theorem B2909803 : Blo 1723062 2909803 := bstep (se 1 (by rfl) ⟨2182352, by rfl⟩ : syracuseStep 2909803 = 4364705) B4364705
theorem B2180839 : Blo 1723062 2180839 := bstep (se 1 (by rfl) ⟨1635629, by rfl⟩ : syracuseStep 2180839 = 3271259) B3271259
theorem B3877019 : Blo 1723062 3877019 := bstep (se 1 (by rfl) ⟨2907764, by rfl⟩ : syracuseStep 3877019 = 5815529) B5815529
theorem B2910431 : Blo 1723062 2910431 := bstep (se 1 (by rfl) ⟨2182823, by rfl⟩ : syracuseStep 2910431 = 4365647) B4365647
theorem B4909679 : Blo 1723062 4909679 := bstep (se 1 (by rfl) ⟨3682259, by rfl⟩ : syracuseStep 4909679 = 7364519) B7364519
theorem B17287825 : Blo 1723062 17287825 := bstep (se 2 (by rfl) ⟨6482934, by rfl⟩ : syracuseStep 17287825 = 12965869) B12965869
theorem B31460201 : Blo 1723062 31460201 := bstep (se 2 (by rfl) ⟨11797575, by rfl⟩ : syracuseStep 31460201 = 23595151) B23595151
theorem B11045753 : Blo 1723062 11045753 := bstep (se 2 (by rfl) ⟨4142157, by rfl⟩ : syracuseStep 11045753 = 8284315) B8284315
theorem B1723375 : Blo 1723062 1723375 := bstep (se 1 (by rfl) ⟨1292531, by rfl⟩ : syracuseStep 1723375 = 2585063) B2585063
theorem B3877883 : Blo 1723062 3877883 := bstep (se 1 (by rfl) ⟨2908412, by rfl⟩ : syracuseStep 3877883 = 5816825) B5816825
theorem B1723495 : Blo 1723062 1723495 := bstep (se 1 (by rfl) ⟨1292621, by rfl⟩ : syracuseStep 1723495 = 2585243) B2585243
theorem B14167199 : Blo 1723062 14167199 := bstep (se 1 (by rfl) ⟨10625399, by rfl⟩ : syracuseStep 14167199 = 21250799) B21250799
theorem B1723599 : Blo 1723062 1723599 := bstep (se 1 (by rfl) ⟨1292699, by rfl⟩ : syracuseStep 1723599 = 2585399) B2585399
theorem B1723719 : Blo 1723062 1723719 := bstep (se 1 (by rfl) ⟨1292789, by rfl⟩ : syracuseStep 1723719 = 2585579) B2585579
theorem B17034725 : Blo 1723062 17034725 := bstep (se 4 (by rfl) ⟨1597005, by rfl⟩ : syracuseStep 17034725 = 3194011) B3194011
theorem B1723931 : Blo 1723062 1723931 := bstep (se 1 (by rfl) ⟨1292948, by rfl⟩ : syracuseStep 1723931 = 2585897) B2585897
theorem B8728235 : Blo 1723062 8728235 := bstep (se 1 (by rfl) ⟨6546176, by rfl⟩ : syracuseStep 8728235 = 13092353) B13092353
theorem B1724351 : Blo 1723062 1724351 := bstep (se 1 (by rfl) ⟨1293263, by rfl⟩ : syracuseStep 1724351 = 2586527) B2586527
theorem B3878855 : Blo 1723062 3878855 := bstep (se 1 (by rfl) ⟨2909141, by rfl⟩ : syracuseStep 3878855 = 5818283) B5818283
theorem B1724415 : Blo 1723062 1724415 := bstep (se 1 (by rfl) ⟨1293311, by rfl⟩ : syracuseStep 1724415 = 2586623) B2586623
theorem B1724487 : Blo 1723062 1724487 := bstep (se 1 (by rfl) ⟨1293365, by rfl⟩ : syracuseStep 1724487 = 2586731) B2586731
theorem B8728721 : Blo 1723062 8728721 := bstep (se 2 (by rfl) ⟨3273270, by rfl⟩ : syracuseStep 8728721 = 6546541) B6546541
theorem B1724575 : Blo 1723062 1724575 := bstep (se 1 (by rfl) ⟨1293431, by rfl⟩ : syracuseStep 1724575 = 2586863) B2586863
theorem B1724607 : Blo 1723062 1724607 := bstep (se 1 (by rfl) ⟨1293455, by rfl⟩ : syracuseStep 1724607 = 2586911) B2586911
theorem B1724655 : Blo 1723062 1724655 := bstep (se 1 (by rfl) ⟨1293491, by rfl⟩ : syracuseStep 1724655 = 2586983) B2586983
theorem B1724671 : Blo 1723062 1724671 := bstep (se 1 (by rfl) ⟨1293503, by rfl⟩ : syracuseStep 1724671 = 2587007) B2587007
theorem B2584895 : Blo 1723062 2584895 := bstep (se 1 (by rfl) ⟨1938671, by rfl⟩ : syracuseStep 2584895 = 3877343) B3877343
theorem B3273043 : Blo 1723062 3273043 := bstep (se 1 (by rfl) ⟨2454782, by rfl⟩ : syracuseStep 3273043 = 4909565) B4909565
theorem B15724925 : Blo 1723062 15724925 := bstep (se 3 (by rfl) ⟨2948423, by rfl⟩ : syracuseStep 15724925 = 5896847) B5896847
theorem B2585087 : Blo 1723062 2585087 := bstep (se 1 (by rfl) ⟨1938815, by rfl⟩ : syracuseStep 2585087 = 3877631) B3877631
theorem B4362943 : Blo 1723062 4362943 := bstep (se 1 (by rfl) ⟨3272207, by rfl⟩ : syracuseStep 4362943 = 6544415) B6544415
theorem B2585471 : Blo 1723062 2585471 := bstep (se 1 (by rfl) ⟨1939103, by rfl⟩ : syracuseStep 2585471 = 3878207) B3878207
theorem B31470565 : Blo 1723062 31470565 := bstep (se 4 (by rfl) ⟨2950365, by rfl⟩ : syracuseStep 31470565 = 5900731) B5900731
theorem B6542441 : Blo 1723062 6542441 := bstep (se 2 (by rfl) ⟨2453415, by rfl⟩ : syracuseStep 6542441 = 4906831) B4906831
theorem B16577855 : Blo 1723062 16577855 := bstep (se 1 (by rfl) ⟨12433391, by rfl⟩ : syracuseStep 16577855 = 24866783) B24866783
theorem B163575197 : Blo 1723062 163575197 := bstep (se 3 (by rfl) ⟨30670349, by rfl⟩ : syracuseStep 163575197 = 61340699) B61340699
theorem B2586239 : Blo 1723062 2586239 := bstep (se 1 (by rfl) ⟨1939679, by rfl⟩ : syracuseStep 2586239 = 3879359) B3879359
theorem B9819791 : Blo 1723062 9819791 := bstep (se 1 (by rfl) ⟨7364843, by rfl⟩ : syracuseStep 9819791 = 14729687) B14729687
theorem B1939135 : Blo 1723062 1939135 := bstep (se 1 (by rfl) ⟨1454351, by rfl⟩ : syracuseStep 1939135 = 2908703) B2908703
theorem B3880655 : Blo 1723062 3880655 := bstep (se 1 (by rfl) ⟨2910491, by rfl⟩ : syracuseStep 3880655 = 5820983) B5820983
theorem B3274607 : Blo 1723062 3274607 := bstep (se 1 (by rfl) ⟨2455955, by rfl⟩ : syracuseStep 3274607 = 4911911) B4911911
theorem B18642959 : Blo 1723062 18642959 := bstep (se 1 (by rfl) ⟨13982219, by rfl⟩ : syracuseStep 18642959 = 27964439) B27964439
theorem B3881033 : Blo 1723062 3881033 := bstep (se 2 (by rfl) ⟨1455387, by rfl⟩ : syracuseStep 3881033 = 2910775) B2910775
theorem B102111407 : Blo 1723062 102111407 := bstep (se 1 (by rfl) ⟨76583555, by rfl⟩ : syracuseStep 102111407 = 153167111) B153167111
theorem B4364563 : Blo 1723062 4364563 := bstep (se 1 (by rfl) ⟨3273422, by rfl⟩ : syracuseStep 4364563 = 6546845) B6546845
theorem B7363219 : Blo 1723062 7363219 := bstep (se 1 (by rfl) ⟨5522414, by rfl⟩ : syracuseStep 7363219 = 11044829) B11044829
theorem B74562281 : Blo 1723062 74562281 := bstep (se 2 (by rfl) ⟨27960855, by rfl⟩ : syracuseStep 74562281 = 55921711) B55921711
theorem B6986843 : Blo 1723062 6986843 := bstep (se 1 (by rfl) ⟨5240132, by rfl⟩ : syracuseStep 6986843 = 10480265) B10480265
theorem B1940575 : Blo 1723062 1940575 := bstep (se 1 (by rfl) ⟨1455431, by rfl⟩ : syracuseStep 1940575 = 2910863) B2910863
theorem B8289449 : Blo 1723062 8289449 := bstep (se 2 (by rfl) ⟨3108543, by rfl⟩ : syracuseStep 8289449 = 6217087) B6217087
theorem B8732447 : Blo 1723062 8732447 := bstep (se 1 (by rfl) ⟨6549335, by rfl⟩ : syracuseStep 8732447 = 13098671) B13098671
theorem B9813959 : Blo 1723062 9813959 := bstep (se 1 (by rfl) ⟨7360469, by rfl⟩ : syracuseStep 9813959 = 14720939) B14720939
theorem B106152059 : Blo 1723062 106152059 := bstep (se 1 (by rfl) ⟨79614044, by rfl⟩ : syracuseStep 106152059 = 159228089) B159228089
theorem B11051903 : Blo 1723062 11051903 := bstep (se 1 (by rfl) ⟨8288927, by rfl⟩ : syracuseStep 11051903 = 16577855) B16577855
theorem B5817257 : Blo 1723062 5817257 := bstep (se 2 (by rfl) ⟨2181471, by rfl⟩ : syracuseStep 5817257 = 4362943) B4362943
theorem B6546527 : Blo 1723062 6546527 := bstep (se 1 (by rfl) ⟨4909895, by rfl⟩ : syracuseStep 6546527 = 9819791) B9819791
theorem B41960753 : Blo 1723062 41960753 := bstep (se 2 (by rfl) ⟨15735282, by rfl⟩ : syracuseStep 41960753 = 31470565) B31470565
theorem B12428639 : Blo 1723062 12428639 := bstep (se 1 (by rfl) ⟨9321479, by rfl⟩ : syracuseStep 12428639 = 18642959) B18642959
theorem B20973467 : Blo 1723062 20973467 := bstep (se 1 (by rfl) ⟨15730100, by rfl⟩ : syracuseStep 20973467 = 31460201) B31460201
theorem B11356483 : Blo 1723062 11356483 := bstep (se 1 (by rfl) ⟨8517362, by rfl⟩ : syracuseStep 11356483 = 17034725) B17034725
theorem B5818823 : Blo 1723062 5818823 := bstep (se 1 (by rfl) ⟨4364117, by rfl⟩ : syracuseStep 5818823 = 8728235) B8728235
theorem B3271403 : Blo 1723062 3271403 := bstep (se 1 (by rfl) ⟨2453552, by rfl⟩ : syracuseStep 3271403 = 4907105) B4907105
theorem B403057403 : Blo 1723062 403057403 := bstep (se 1 (by rfl) ⟨302293052, by rfl⟩ : syracuseStep 403057403 = 604586105) B604586105
theorem B5819147 : Blo 1723062 5819147 := bstep (se 1 (by rfl) ⟨4364360, by rfl⟩ : syracuseStep 5819147 = 8728721) B8728721
theorem B1723263 : Blo 1723062 1723263 := bstep (se 1 (by rfl) ⟨1292447, by rfl⟩ : syracuseStep 1723263 = 2584895) B2584895
theorem B1723391 : Blo 1723062 1723391 := bstep (se 1 (by rfl) ⟨1292543, by rfl⟩ : syracuseStep 1723391 = 2585087) B2585087
theorem B5819417 : Blo 1723062 5819417 := bstep (se 2 (by rfl) ⟨2182281, by rfl⟩ : syracuseStep 5819417 = 4364563) B4364563
theorem B1723647 : Blo 1723062 1723647 := bstep (se 1 (by rfl) ⟨1292735, by rfl⟩ : syracuseStep 1723647 = 2585471) B2585471
theorem B4361627 : Blo 1723062 4361627 := bstep (se 1 (by rfl) ⟨3271220, by rfl⟩ : syracuseStep 4361627 = 6542441) B6542441
theorem B3878351 : Blo 1723062 3878351 := bstep (se 1 (by rfl) ⟨2908763, by rfl⟩ : syracuseStep 3878351 = 5817527) B5817527
theorem B9817625 : Blo 1723062 9817625 := bstep (se 2 (by rfl) ⟨3681609, by rfl⟩ : syracuseStep 9817625 = 7363219) B7363219
theorem B1724159 : Blo 1723062 1724159 := bstep (se 1 (by rfl) ⟨1293119, by rfl⟩ : syracuseStep 1724159 = 2586239) B2586239
theorem B2584679 : Blo 1723062 2584679 := bstep (se 1 (by rfl) ⟨1938509, by rfl⟩ : syracuseStep 2584679 = 3877019) B3877019
theorem B3273119 : Blo 1723062 3273119 := bstep (se 1 (by rfl) ⟨2454839, by rfl⟩ : syracuseStep 3273119 = 4909679) B4909679
theorem B2585255 : Blo 1723062 2585255 := bstep (se 1 (by rfl) ⟨1938941, by rfl⟩ : syracuseStep 2585255 = 3877883) B3877883
theorem B4657895 : Blo 1723062 4657895 := bstep (se 1 (by rfl) ⟨3493421, by rfl⟩ : syracuseStep 4657895 = 6986843) B6986843
theorem B5526299 : Blo 1723062 5526299 := bstep (se 1 (by rfl) ⟨4144724, by rfl⟩ : syracuseStep 5526299 = 8289449) B8289449
theorem B3879737 : Blo 1723062 3879737 := bstep (se 2 (by rfl) ⟨1454901, by rfl⟩ : syracuseStep 3879737 = 2909803) B2909803
theorem B2585513 : Blo 1723062 2585513 := bstep (se 2 (by rfl) ⟨969567, by rfl⟩ : syracuseStep 2585513 = 1939135) B1939135
theorem B5821631 : Blo 1723062 5821631 := bstep (se 1 (by rfl) ⟨4366223, by rfl⟩ : syracuseStep 5821631 = 8732447) B8732447
theorem B6542639 : Blo 1723062 6542639 := bstep (se 1 (by rfl) ⟨4906979, by rfl⟩ : syracuseStep 6542639 = 9813959) B9813959
theorem B2585903 : Blo 1723062 2585903 := bstep (se 1 (by rfl) ⟨1939427, by rfl⟩ : syracuseStep 2585903 = 3878855) B3878855
theorem B6542927 : Blo 1723062 6542927 := bstep (se 1 (by rfl) ⟨4907195, by rfl⟩ : syracuseStep 6542927 = 9814391) B9814391
theorem B10483283 : Blo 1723062 10483283 := bstep (se 1 (by rfl) ⟨7862462, by rfl⟩ : syracuseStep 10483283 = 15724925) B15724925
theorem B4364057 : Blo 1723062 4364057 := bstep (se 2 (by rfl) ⟨1636521, by rfl⟩ : syracuseStep 4364057 = 3273043) B3273043
theorem B23050433 : Blo 1723062 23050433 := bstep (se 2 (by rfl) ⟨8643912, by rfl⟩ : syracuseStep 23050433 = 17287825) B17287825
theorem B109050131 : Blo 1723062 109050131 := bstep (se 1 (by rfl) ⟨81787598, by rfl⟩ : syracuseStep 109050131 = 163575197) B163575197
theorem B2587103 : Blo 1723062 2587103 := bstep (se 1 (by rfl) ⟨1940327, by rfl⟩ : syracuseStep 2587103 = 3880655) B3880655
theorem B2587355 : Blo 1723062 2587355 := bstep (se 1 (by rfl) ⟨1940516, by rfl⟩ : syracuseStep 2587355 = 3881033) B3881033
theorem B68074271 : Blo 1723062 68074271 := bstep (se 1 (by rfl) ⟨51055703, by rfl⟩ : syracuseStep 68074271 = 102111407) B102111407
theorem B2587433 : Blo 1723062 2587433 := bstep (se 2 (by rfl) ⟨970287, by rfl⟩ : syracuseStep 2587433 = 1940575) B1940575
theorem B1940287 : Blo 1723062 1940287 := bstep (se 1 (by rfl) ⟨1455215, by rfl⟩ : syracuseStep 1940287 = 2910431) B2910431
theorem B49708187 : Blo 1723062 49708187 := bstep (se 1 (by rfl) ⟨37281140, by rfl⟩ : syracuseStep 49708187 = 74562281) B74562281
theorem B7363835 : Blo 1723062 7363835 := bstep (se 1 (by rfl) ⟨5522876, by rfl⟩ : syracuseStep 7363835 = 11045753) B11045753
theorem B9444799 : Blo 1723062 9444799 := bstep (se 1 (by rfl) ⟨7083599, by rfl⟩ : syracuseStep 9444799 = 14167199) B14167199
theorem B8732285 : Blo 1723062 8732285 := bstep (se 3 (by rfl) ⟨1637303, by rfl⟩ : syracuseStep 8732285 = 3274607) B3274607
theorem B2907785 : Blo 1723062 2907785 := bstep (se 2 (by rfl) ⟨1090419, by rfl⟩ : syracuseStep 2907785 = 2180839) B2180839
theorem B16801661 : Blo 1723062 16801661 := bstep (se 3 (by rfl) ⟨3150311, by rfl⟩ : syracuseStep 16801661 = 6300623) B6300623
theorem B3105263 : Blo 1723062 3105263 := bstep (se 1 (by rfl) ⟨2328947, by rfl⟩ : syracuseStep 3105263 = 4657895) B4657895
theorem B6988855 : Blo 1723062 6988855 := bstep (se 1 (by rfl) ⟨5241641, by rfl⟩ : syracuseStep 6988855 = 10483283) B10483283
theorem B2909371 : Blo 1723062 2909371 := bstep (se 1 (by rfl) ⟨2182028, by rfl⟩ : syracuseStep 2909371 = 4364057) B4364057
theorem B2180935 : Blo 1723062 2180935 := bstep (se 1 (by rfl) ⟨1635701, by rfl⟩ : syracuseStep 2180935 = 3271403) B3271403
theorem B12593065 : Blo 1723062 12593065 := bstep (se 2 (by rfl) ⟨4722399, by rfl⟩ : syracuseStep 12593065 = 9444799) B9444799
theorem B33138791 : Blo 1723062 33138791 := bstep (se 1 (by rfl) ⟨24854093, by rfl⟩ : syracuseStep 33138791 = 49708187) B49708187
theorem B4909223 : Blo 1723062 4909223 := bstep (se 1 (by rfl) ⟨3681917, by rfl⟩ : syracuseStep 4909223 = 7363835) B7363835
theorem B44804429 : Blo 1723062 44804429 := bstep (se 3 (by rfl) ⟨8400830, by rfl⟩ : syracuseStep 44804429 = 16801661) B16801661
theorem B1723119 : Blo 1723062 1723119 := bstep (se 1 (by rfl) ⟨1292339, by rfl⟩ : syracuseStep 1723119 = 2584679) B2584679
theorem B2182079 : Blo 1723062 2182079 := bstep (se 1 (by rfl) ⟨1636559, by rfl⟩ : syracuseStep 2182079 = 3273119) B3273119
theorem B15141977 : Blo 1723062 15141977 := bstep (se 2 (by rfl) ⟨5678241, by rfl⟩ : syracuseStep 15141977 = 11356483) B11356483
theorem B1723503 : Blo 1723062 1723503 := bstep (se 1 (by rfl) ⟨1292627, by rfl⟩ : syracuseStep 1723503 = 2585255) B2585255
theorem B7367935 : Blo 1723062 7367935 := bstep (se 1 (by rfl) ⟨5525951, by rfl⟩ : syracuseStep 7367935 = 11051903) B11051903
theorem B3878171 : Blo 1723062 3878171 := bstep (se 1 (by rfl) ⟨2908628, by rfl⟩ : syracuseStep 3878171 = 5817257) B5817257
theorem B1723675 : Blo 1723062 1723675 := bstep (se 1 (by rfl) ⟨1292756, by rfl⟩ : syracuseStep 1723675 = 2585513) B2585513
theorem B4361759 : Blo 1723062 4361759 := bstep (se 1 (by rfl) ⟨3271319, by rfl⟩ : syracuseStep 4361759 = 6542639) B6542639
theorem B1723935 : Blo 1723062 1723935 := bstep (se 1 (by rfl) ⟨1292951, by rfl⟩ : syracuseStep 1723935 = 2585903) B2585903
theorem B8285759 : Blo 1723062 8285759 := bstep (se 1 (by rfl) ⟨6214319, by rfl⟩ : syracuseStep 8285759 = 12428639) B12428639
theorem B4361951 : Blo 1723062 4361951 := bstep (se 1 (by rfl) ⟨3271463, by rfl⟩ : syracuseStep 4361951 = 6542927) B6542927
theorem B72700087 : Blo 1723062 72700087 := bstep (se 1 (by rfl) ⟨54525065, by rfl⟩ : syracuseStep 72700087 = 109050131) B109050131
theorem B3879215 : Blo 1723062 3879215 := bstep (se 1 (by rfl) ⟨2909411, by rfl⟩ : syracuseStep 3879215 = 5818823) B5818823
theorem B1724735 : Blo 1723062 1724735 := bstep (se 1 (by rfl) ⟨1293551, by rfl⟩ : syracuseStep 1724735 = 2587103) B2587103
theorem B1724903 : Blo 1723062 1724903 := bstep (se 1 (by rfl) ⟨1293677, by rfl⟩ : syracuseStep 1724903 = 2587355) B2587355
theorem B3879431 : Blo 1723062 3879431 := bstep (se 1 (by rfl) ⟨2909573, by rfl⟩ : syracuseStep 3879431 = 5819147) B5819147
theorem B1724955 : Blo 1723062 1724955 := bstep (se 1 (by rfl) ⟨1293716, by rfl⟩ : syracuseStep 1724955 = 2587433) B2587433
theorem B3879611 : Blo 1723062 3879611 := bstep (se 1 (by rfl) ⟨2909708, by rfl⟩ : syracuseStep 3879611 = 5819417) B5819417
theorem B2585567 : Blo 1723062 2585567 := bstep (se 1 (by rfl) ⟨1939175, by rfl⟩ : syracuseStep 2585567 = 3878351) B3878351
theorem B5821523 : Blo 1723062 5821523 := bstep (se 1 (by rfl) ⟨4366142, by rfl⟩ : syracuseStep 5821523 = 8732285) B8732285
theorem B1938523 : Blo 1723062 1938523 := bstep (se 1 (by rfl) ⟨1453892, by rfl⟩ : syracuseStep 1938523 = 2907785) B2907785
theorem B70768039 : Blo 1723062 70768039 := bstep (se 1 (by rfl) ⟨53076029, by rfl⟩ : syracuseStep 70768039 = 106152059) B106152059
theorem B3684199 : Blo 1723062 3684199 := bstep (se 1 (by rfl) ⟨2763149, by rfl⟩ : syracuseStep 3684199 = 5526299) B5526299
theorem B2586491 : Blo 1723062 2586491 := bstep (se 1 (by rfl) ⟨1939868, by rfl⟩ : syracuseStep 2586491 = 3879737) B3879737
theorem B4364351 : Blo 1723062 4364351 := bstep (se 1 (by rfl) ⟨3273263, by rfl⟩ : syracuseStep 4364351 = 6546527) B6546527
theorem B3881087 : Blo 1723062 3881087 := bstep (se 1 (by rfl) ⟨2910815, by rfl⟩ : syracuseStep 3881087 = 5821631) B5821631
theorem B27973835 : Blo 1723062 27973835 := bstep (se 1 (by rfl) ⟨20980376, by rfl⟩ : syracuseStep 27973835 = 41960753) B41960753
theorem B2587049 : Blo 1723062 2587049 := bstep (se 2 (by rfl) ⟨970143, by rfl⟩ : syracuseStep 2587049 = 1940287) B1940287
theorem B13982311 : Blo 1723062 13982311 := bstep (se 1 (by rfl) ⟨10486733, by rfl⟩ : syracuseStep 13982311 = 20973467) B20973467
theorem B15366955 : Blo 1723062 15366955 := bstep (se 1 (by rfl) ⟨11525216, by rfl⟩ : syracuseStep 15366955 = 23050433) B23050433
theorem B268704935 : Blo 1723062 268704935 := bstep (se 1 (by rfl) ⟨201528701, by rfl⟩ : syracuseStep 268704935 = 403057403) B403057403
theorem B45382847 : Blo 1723062 45382847 := bstep (se 1 (by rfl) ⟨34037135, by rfl⟩ : syracuseStep 45382847 = 68074271) B68074271
theorem B2907751 : Blo 1723062 2907751 := bstep (se 1 (by rfl) ⟨2180813, by rfl⟩ : syracuseStep 2907751 = 4361627) B4361627
theorem B6545083 : Blo 1723062 6545083 := bstep (se 1 (by rfl) ⟨4908812, by rfl⟩ : syracuseStep 6545083 = 9817625) B9817625
theorem B121020925 : Blo 1723062 121020925 := bstep (se 3 (by rfl) ⟨22691423, by rfl⟩ : syracuseStep 121020925 = 45382847) B45382847
theorem B74572325 : Blo 1723062 74572325 := bstep (se 4 (by rfl) ⟨6991155, by rfl⟩ : syracuseStep 74572325 = 13982311) B13982311
theorem B20489273 : Blo 1723062 20489273 := bstep (se 2 (by rfl) ⟨7683477, by rfl⟩ : syracuseStep 20489273 = 15366955) B15366955
theorem B2909567 : Blo 1723062 2909567 := bstep (se 1 (by rfl) ⟨2182175, by rfl⟩ : syracuseStep 2909567 = 4364351) B4364351
theorem B29869619 : Blo 1723062 29869619 := bstep (se 1 (by rfl) ⟨22402214, by rfl⟩ : syracuseStep 29869619 = 44804429) B44804429
theorem B9823913 : Blo 1723062 9823913 := bstep (se 2 (by rfl) ⟨3683967, by rfl⟩ : syracuseStep 9823913 = 7367935) B7367935
theorem B94357385 : Blo 1723062 94357385 := bstep (se 2 (by rfl) ⟨35384019, by rfl⟩ : syracuseStep 94357385 = 70768039) B70768039
theorem B10094651 : Blo 1723062 10094651 := bstep (se 1 (by rfl) ⟨7570988, by rfl⟩ : syracuseStep 10094651 = 15141977) B15141977
theorem B179136623 : Blo 1723062 179136623 := bstep (se 1 (by rfl) ⟨134352467, by rfl⟩ : syracuseStep 179136623 = 268704935) B268704935
theorem B3877001 : Blo 1723062 3877001 := bstep (se 2 (by rfl) ⟨1453875, by rfl⟩ : syracuseStep 3877001 = 2907751) B2907751
theorem B8726777 : Blo 1723062 8726777 := bstep (se 2 (by rfl) ⟨3272541, by rfl⟩ : syracuseStep 8726777 = 6545083) B6545083
theorem B5523839 : Blo 1723062 5523839 := bstep (se 1 (by rfl) ⟨4142879, by rfl⟩ : syracuseStep 5523839 = 8285759) B8285759
theorem B5818877 : Blo 1723062 5818877 := bstep (se 3 (by rfl) ⟨1091039, by rfl⟩ : syracuseStep 5818877 = 2182079) B2182079
theorem B1723711 : Blo 1723062 1723711 := bstep (se 1 (by rfl) ⟨1292783, by rfl⟩ : syracuseStep 1723711 = 2585567) B2585567
theorem B1724327 : Blo 1723062 1724327 := bstep (se 1 (by rfl) ⟨1293245, by rfl⟩ : syracuseStep 1724327 = 2586491) B2586491
theorem B9318473 : Blo 1723062 9318473 := bstep (se 2 (by rfl) ⟨3494427, by rfl⟩ : syracuseStep 9318473 = 6988855) B6988855
theorem B3272815 : Blo 1723062 3272815 := bstep (se 1 (by rfl) ⟨2454611, by rfl⟩ : syracuseStep 3272815 = 4909223) B4909223
theorem B2584697 : Blo 1723062 2584697 := bstep (se 2 (by rfl) ⟨969261, by rfl⟩ : syracuseStep 2584697 = 1938523) B1938523
theorem B18649223 : Blo 1723062 18649223 := bstep (se 1 (by rfl) ⟨13986917, by rfl⟩ : syracuseStep 18649223 = 27973835) B27973835
theorem B3879161 : Blo 1723062 3879161 := bstep (se 2 (by rfl) ⟨1454685, by rfl⟩ : syracuseStep 3879161 = 2909371) B2909371
theorem B1724699 : Blo 1723062 1724699 := bstep (se 1 (by rfl) ⟨1293524, by rfl⟩ : syracuseStep 1724699 = 2587049) B2587049
theorem B2585447 : Blo 1723062 2585447 := bstep (se 1 (by rfl) ⟨1939085, by rfl⟩ : syracuseStep 2585447 = 3878171) B3878171
theorem B4912265 : Blo 1723062 4912265 := bstep (se 2 (by rfl) ⟨1842099, by rfl⟩ : syracuseStep 4912265 = 3684199) B3684199
theorem B16790753 : Blo 1723062 16790753 := bstep (se 2 (by rfl) ⟨6296532, by rfl⟩ : syracuseStep 16790753 = 12593065) B12593065
theorem B2586143 : Blo 1723062 2586143 := bstep (se 1 (by rfl) ⟨1939607, by rfl⟩ : syracuseStep 2586143 = 3879215) B3879215
theorem B96933449 : Blo 1723062 96933449 := bstep (se 2 (by rfl) ⟨36350043, by rfl⟩ : syracuseStep 96933449 = 72700087) B72700087
theorem B2586287 : Blo 1723062 2586287 := bstep (se 1 (by rfl) ⟨1939715, by rfl⟩ : syracuseStep 2586287 = 3879431) B3879431
theorem B2586407 : Blo 1723062 2586407 := bstep (se 1 (by rfl) ⟨1939805, by rfl⟩ : syracuseStep 2586407 = 3879611) B3879611
theorem B3881015 : Blo 1723062 3881015 := bstep (se 1 (by rfl) ⟨2910761, by rfl⟩ : syracuseStep 3881015 = 5821523) B5821523
theorem B8280701 : Blo 1723062 8280701 := bstep (se 3 (by rfl) ⟨1552631, by rfl⟩ : syracuseStep 8280701 = 3105263) B3105263
theorem B22092527 : Blo 1723062 22092527 := bstep (se 1 (by rfl) ⟨16569395, by rfl⟩ : syracuseStep 22092527 = 33138791) B33138791
theorem B2587391 : Blo 1723062 2587391 := bstep (se 1 (by rfl) ⟨1940543, by rfl⟩ : syracuseStep 2587391 = 3881087) B3881087
theorem B2907839 : Blo 1723062 2907839 := bstep (se 1 (by rfl) ⟨2180879, by rfl⟩ : syracuseStep 2907839 = 4361759) B4361759
theorem B2907913 : Blo 1723062 2907913 := bstep (se 2 (by rfl) ⟨1090467, by rfl⟩ : syracuseStep 2907913 = 2180935) B2180935
theorem B2907967 : Blo 1723062 2907967 := bstep (se 1 (by rfl) ⟨2180975, by rfl⟩ : syracuseStep 2907967 = 4361951) B4361951
theorem B119424415 : Blo 1723062 119424415 := bstep (se 1 (by rfl) ⟨89568311, by rfl⟩ : syracuseStep 119424415 = 179136623) B179136623
theorem B79652317 : Blo 1723062 79652317 := bstep (se 3 (by rfl) ⟨14934809, by rfl⟩ : syracuseStep 79652317 = 29869619) B29869619
theorem B5817851 : Blo 1723062 5817851 := bstep (se 1 (by rfl) ⟨4363388, by rfl⟩ : syracuseStep 5817851 = 8726777) B8726777
theorem B3877217 : Blo 1723062 3877217 := bstep (se 2 (by rfl) ⟨1453956, by rfl⟩ : syracuseStep 3877217 = 2907913) B2907913
theorem B3877289 : Blo 1723062 3877289 := bstep (se 2 (by rfl) ⟨1453983, by rfl⟩ : syracuseStep 3877289 = 2907967) B2907967
theorem B6212315 : Blo 1723062 6212315 := bstep (se 1 (by rfl) ⟨4659236, by rfl⟩ : syracuseStep 6212315 = 9318473) B9318473
theorem B1723131 : Blo 1723062 1723131 := bstep (se 1 (by rfl) ⟨1292348, by rfl⟩ : syracuseStep 1723131 = 2584697) B2584697
theorem B1723631 : Blo 1723062 1723631 := bstep (se 1 (by rfl) ⟨1292723, by rfl⟩ : syracuseStep 1723631 = 2585447) B2585447
theorem B161361233 : Blo 1723062 161361233 := bstep (se 2 (by rfl) ⟨60510462, by rfl⟩ : syracuseStep 161361233 = 121020925) B121020925
theorem B13659515 : Blo 1723062 13659515 := bstep (se 1 (by rfl) ⟨10244636, by rfl⟩ : syracuseStep 13659515 = 20489273) B20489273
theorem B1724095 : Blo 1723062 1724095 := bstep (se 1 (by rfl) ⟨1293071, by rfl⟩ : syracuseStep 1724095 = 2586143) B2586143
theorem B64622299 : Blo 1723062 64622299 := bstep (se 1 (by rfl) ⟨48466724, by rfl⟩ : syracuseStep 64622299 = 96933449) B96933449
theorem B6549275 : Blo 1723062 6549275 := bstep (se 1 (by rfl) ⟨4911956, by rfl⟩ : syracuseStep 6549275 = 9823913) B9823913
theorem B1724191 : Blo 1723062 1724191 := bstep (se 1 (by rfl) ⟨1293143, by rfl⟩ : syracuseStep 1724191 = 2586287) B2586287
theorem B1724271 : Blo 1723062 1724271 := bstep (se 1 (by rfl) ⟨1293203, by rfl⟩ : syracuseStep 1724271 = 2586407) B2586407
theorem B6729767 : Blo 1723062 6729767 := bstep (se 1 (by rfl) ⟨5047325, by rfl⟩ : syracuseStep 6729767 = 10094651) B10094651
theorem B2584667 : Blo 1723062 2584667 := bstep (se 1 (by rfl) ⟨1938500, by rfl⟩ : syracuseStep 2584667 = 3877001) B3877001
theorem B3682559 : Blo 1723062 3682559 := bstep (se 1 (by rfl) ⟨2761919, by rfl⟩ : syracuseStep 3682559 = 5523839) B5523839
theorem B3879251 : Blo 1723062 3879251 := bstep (se 1 (by rfl) ⟨2909438, by rfl⟩ : syracuseStep 3879251 = 5818877) B5818877
theorem B1724927 : Blo 1723062 1724927 := bstep (se 1 (by rfl) ⟨1293695, by rfl⟩ : syracuseStep 1724927 = 2587391) B2587391
theorem B1938559 : Blo 1723062 1938559 := bstep (se 1 (by rfl) ⟨1453919, by rfl⟩ : syracuseStep 1938559 = 2907839) B2907839
theorem B12432815 : Blo 1723062 12432815 := bstep (se 1 (by rfl) ⟨9324611, by rfl⟩ : syracuseStep 12432815 = 18649223) B18649223
theorem B4363753 : Blo 1723062 4363753 := bstep (se 2 (by rfl) ⟨1636407, by rfl⟩ : syracuseStep 4363753 = 3272815) B3272815
theorem B2586107 : Blo 1723062 2586107 := bstep (se 1 (by rfl) ⟨1939580, by rfl⟩ : syracuseStep 2586107 = 3879161) B3879161
theorem B49714883 : Blo 1723062 49714883 := bstep (se 1 (by rfl) ⟨37286162, by rfl⟩ : syracuseStep 49714883 = 74572325) B74572325
theorem B44775341 : Blo 1723062 44775341 := bstep (se 3 (by rfl) ⟨8395376, by rfl⟩ : syracuseStep 44775341 = 16790753) B16790753
theorem B3274843 : Blo 1723062 3274843 := bstep (se 1 (by rfl) ⟨2456132, by rfl⟩ : syracuseStep 3274843 = 4912265) B4912265
theorem B1939711 : Blo 1723062 1939711 := bstep (se 1 (by rfl) ⟨1454783, by rfl⟩ : syracuseStep 1939711 = 2909567) B2909567
theorem B62904923 : Blo 1723062 62904923 := bstep (se 1 (by rfl) ⟨47178692, by rfl⟩ : syracuseStep 62904923 = 94357385) B94357385
theorem B2587343 : Blo 1723062 2587343 := bstep (se 1 (by rfl) ⟨1940507, by rfl⟩ : syracuseStep 2587343 = 3881015) B3881015
theorem B5520467 : Blo 1723062 5520467 := bstep (se 1 (by rfl) ⟨4140350, by rfl⟩ : syracuseStep 5520467 = 8280701) B8280701
theorem B14728351 : Blo 1723062 14728351 := bstep (se 1 (by rfl) ⟨11046263, by rfl⟩ : syracuseStep 14728351 = 22092527) B22092527
theorem B4366457 : Blo 1723062 4366457 := bstep (se 2 (by rfl) ⟨1637421, by rfl⟩ : syracuseStep 4366457 = 3274843) B3274843
theorem B19637801 : Blo 1723062 19637801 := bstep (se 2 (by rfl) ⟨7364175, by rfl⟩ : syracuseStep 19637801 = 14728351) B14728351
theorem B41936615 : Blo 1723062 41936615 := bstep (se 1 (by rfl) ⟨31452461, by rfl⟩ : syracuseStep 41936615 = 62904923) B62904923
theorem B106203089 : Blo 1723062 106203089 := bstep (se 2 (by rfl) ⟨39826158, by rfl⟩ : syracuseStep 106203089 = 79652317) B79652317
theorem B5818337 : Blo 1723062 5818337 := bstep (se 2 (by rfl) ⟨2181876, by rfl⟩ : syracuseStep 5818337 = 4363753) B4363753
theorem B3680311 : Blo 1723062 3680311 := bstep (se 1 (by rfl) ⟨2760233, by rfl⟩ : syracuseStep 3680311 = 5520467) B5520467
theorem B1723111 : Blo 1723062 1723111 := bstep (se 1 (by rfl) ⟨1292333, by rfl⟩ : syracuseStep 1723111 = 2584667) B2584667
theorem B3878567 : Blo 1723062 3878567 := bstep (se 1 (by rfl) ⟨2908925, by rfl⟩ : syracuseStep 3878567 = 5817851) B5817851
theorem B1724071 : Blo 1723062 1724071 := bstep (se 1 (by rfl) ⟨1293053, by rfl⟩ : syracuseStep 1724071 = 2586107) B2586107
theorem B2584745 : Blo 1723062 2584745 := bstep (se 2 (by rfl) ⟨969279, by rfl⟩ : syracuseStep 2584745 = 1938559) B1938559
theorem B2584811 : Blo 1723062 2584811 := bstep (se 1 (by rfl) ⟨1938608, by rfl⟩ : syracuseStep 2584811 = 3877217) B3877217
theorem B2584859 : Blo 1723062 2584859 := bstep (se 1 (by rfl) ⟨1938644, by rfl⟩ : syracuseStep 2584859 = 3877289) B3877289
theorem B1724895 : Blo 1723062 1724895 := bstep (se 1 (by rfl) ⟨1293671, by rfl⟩ : syracuseStep 1724895 = 2587343) B2587343
theorem B4141543 : Blo 1723062 4141543 := bstep (se 1 (by rfl) ⟨3106157, by rfl⟩ : syracuseStep 4141543 = 6212315) B6212315
theorem B159232553 : Blo 1723062 159232553 := bstep (se 2 (by rfl) ⟨59712207, by rfl⟩ : syracuseStep 159232553 = 119424415) B119424415
theorem B107574155 : Blo 1723062 107574155 := bstep (se 1 (by rfl) ⟨80680616, by rfl⟩ : syracuseStep 107574155 = 161361233) B161361233
theorem B9106343 : Blo 1723062 9106343 := bstep (se 1 (by rfl) ⟨6829757, by rfl⟩ : syracuseStep 9106343 = 13659515) B13659515
theorem B4486511 : Blo 1723062 4486511 := bstep (se 1 (by rfl) ⟨3364883, by rfl⟩ : syracuseStep 4486511 = 6729767) B6729767
theorem B2455039 : Blo 1723062 2455039 := bstep (se 1 (by rfl) ⟨1841279, by rfl⟩ : syracuseStep 2455039 = 3682559) B3682559
theorem B2586167 : Blo 1723062 2586167 := bstep (se 1 (by rfl) ⟨1939625, by rfl⟩ : syracuseStep 2586167 = 3879251) B3879251
theorem B2586281 : Blo 1723062 2586281 := bstep (se 2 (by rfl) ⟨969855, by rfl⟩ : syracuseStep 2586281 = 1939711) B1939711
theorem B8288543 : Blo 1723062 8288543 := bstep (se 1 (by rfl) ⟨6216407, by rfl⟩ : syracuseStep 8288543 = 12432815) B12432815
theorem B33143255 : Blo 1723062 33143255 := bstep (se 1 (by rfl) ⟨24857441, by rfl⟩ : syracuseStep 33143255 = 49714883) B49714883
theorem B29850227 : Blo 1723062 29850227 := bstep (se 1 (by rfl) ⟨22387670, by rfl⟩ : syracuseStep 29850227 = 44775341) B44775341
theorem B86163065 : Blo 1723062 86163065 := bstep (se 2 (by rfl) ⟨32311149, by rfl⟩ : syracuseStep 86163065 = 64622299) B64622299
theorem B4366183 : Blo 1723062 4366183 := bstep (se 1 (by rfl) ⟨3274637, by rfl⟩ : syracuseStep 4366183 = 6549275) B6549275
theorem B4907081 : Blo 1723062 4907081 := bstep (se 2 (by rfl) ⟨1840155, by rfl⟩ : syracuseStep 4907081 = 3680311) B3680311
theorem B6070895 : Blo 1723062 6070895 := bstep (se 1 (by rfl) ⟨4553171, by rfl⟩ : syracuseStep 6070895 = 9106343) B9106343
theorem B5522057 : Blo 1723062 5522057 := bstep (se 2 (by rfl) ⟨2070771, by rfl⟩ : syracuseStep 5522057 = 4141543) B4141543
theorem B2991007 : Blo 1723062 2991007 := bstep (se 1 (by rfl) ⟨2243255, by rfl⟩ : syracuseStep 2991007 = 4486511) B4486511
theorem B13091867 : Blo 1723062 13091867 := bstep (se 1 (by rfl) ⟨9818900, by rfl⟩ : syracuseStep 13091867 = 19637801) B19637801
theorem B22095503 : Blo 1723062 22095503 := bstep (se 1 (by rfl) ⟨16571627, by rfl⟩ : syracuseStep 22095503 = 33143255) B33143255
theorem B19900151 : Blo 1723062 19900151 := bstep (se 1 (by rfl) ⟨14925113, by rfl⟩ : syracuseStep 19900151 = 29850227) B29850227
theorem B2910971 : Blo 1723062 2910971 := bstep (se 1 (by rfl) ⟨2183228, by rfl⟩ : syracuseStep 2910971 = 4366457) B4366457
theorem B1723163 : Blo 1723062 1723163 := bstep (se 1 (by rfl) ⟨1292372, by rfl⟩ : syracuseStep 1723163 = 2584745) B2584745
theorem B1723207 : Blo 1723062 1723207 := bstep (se 1 (by rfl) ⟨1292405, by rfl⟩ : syracuseStep 1723207 = 2584811) B2584811
theorem B1723239 : Blo 1723062 1723239 := bstep (se 1 (by rfl) ⟨1292429, by rfl⟩ : syracuseStep 1723239 = 2584859) B2584859
theorem B106155035 : Blo 1723062 106155035 := bstep (se 1 (by rfl) ⟨79616276, by rfl⟩ : syracuseStep 106155035 = 159232553) B159232553
theorem B71716103 : Blo 1723062 71716103 := bstep (se 1 (by rfl) ⟨53787077, by rfl⟩ : syracuseStep 71716103 = 107574155) B107574155
theorem B1724111 : Blo 1723062 1724111 := bstep (se 1 (by rfl) ⟨1293083, by rfl⟩ : syracuseStep 1724111 = 2586167) B2586167
theorem B1724187 : Blo 1723062 1724187 := bstep (se 1 (by rfl) ⟨1293140, by rfl⟩ : syracuseStep 1724187 = 2586281) B2586281
theorem B3878891 : Blo 1723062 3878891 := bstep (se 1 (by rfl) ⟨2909168, by rfl⟩ : syracuseStep 3878891 = 5818337) B5818337
theorem B5525695 : Blo 1723062 5525695 := bstep (se 1 (by rfl) ⟨4144271, by rfl⟩ : syracuseStep 5525695 = 8288543) B8288543
theorem B3273385 : Blo 1723062 3273385 := bstep (se 2 (by rfl) ⟨1227519, by rfl⟩ : syracuseStep 3273385 = 2455039) B2455039
theorem B2585711 : Blo 1723062 2585711 := bstep (se 1 (by rfl) ⟨1939283, by rfl⟩ : syracuseStep 2585711 = 3878567) B3878567
theorem B5821577 : Blo 1723062 5821577 := bstep (se 2 (by rfl) ⟨2183091, by rfl⟩ : syracuseStep 5821577 = 4366183) B4366183
theorem B27957743 : Blo 1723062 27957743 := bstep (se 1 (by rfl) ⟨20968307, by rfl⟩ : syracuseStep 27957743 = 41936615) B41936615
theorem B70802059 : Blo 1723062 70802059 := bstep (se 1 (by rfl) ⟨53101544, by rfl⟩ : syracuseStep 70802059 = 106203089) B106203089
theorem B57442043 : Blo 1723062 57442043 := bstep (se 1 (by rfl) ⟨43081532, by rfl⟩ : syracuseStep 57442043 = 86163065) B86163065
theorem B4047263 : Blo 1723062 4047263 := bstep (se 1 (by rfl) ⟨3035447, by rfl⟩ : syracuseStep 4047263 = 6070895) B6070895
theorem B14730335 : Blo 1723062 14730335 := bstep (se 1 (by rfl) ⟨11047751, by rfl⟩ : syracuseStep 14730335 = 22095503) B22095503
theorem B18638495 : Blo 1723062 18638495 := bstep (se 1 (by rfl) ⟨13978871, by rfl⟩ : syracuseStep 18638495 = 27957743) B27957743
theorem B15952037 : Blo 1723062 15952037 := bstep (se 4 (by rfl) ⟨1495503, by rfl⟩ : syracuseStep 15952037 = 2991007) B2991007
theorem B47810735 : Blo 1723062 47810735 := bstep (se 1 (by rfl) ⟨35858051, by rfl⟩ : syracuseStep 47810735 = 71716103) B71716103
theorem B13085549 : Blo 1723062 13085549 := bstep (se 3 (by rfl) ⟨2453540, by rfl⟩ : syracuseStep 13085549 = 4907081) B4907081
theorem B7367593 : Blo 1723062 7367593 := bstep (se 2 (by rfl) ⟨2762847, by rfl⟩ : syracuseStep 7367593 = 5525695) B5525695
theorem B3681371 : Blo 1723062 3681371 := bstep (se 1 (by rfl) ⟨2761028, by rfl⟩ : syracuseStep 3681371 = 5522057) B5522057
theorem B8727911 : Blo 1723062 8727911 := bstep (se 1 (by rfl) ⟨6545933, by rfl⟩ : syracuseStep 8727911 = 13091867) B13091867
theorem B1723807 : Blo 1723062 1723807 := bstep (se 1 (by rfl) ⟨1292855, by rfl⟩ : syracuseStep 1723807 = 2585711) B2585711
theorem B13266767 : Blo 1723062 13266767 := bstep (se 1 (by rfl) ⟨9950075, by rfl⟩ : syracuseStep 13266767 = 19900151) B19900151
theorem B38294695 : Blo 1723062 38294695 := bstep (se 1 (by rfl) ⟨28721021, by rfl⟩ : syracuseStep 38294695 = 57442043) B57442043
theorem B2585927 : Blo 1723062 2585927 := bstep (se 1 (by rfl) ⟨1939445, by rfl⟩ : syracuseStep 2585927 = 3878891) B3878891
theorem B3881051 : Blo 1723062 3881051 := bstep (se 1 (by rfl) ⟨2910788, by rfl⟩ : syracuseStep 3881051 = 5821577) B5821577
theorem B94402745 : Blo 1723062 94402745 := bstep (se 2 (by rfl) ⟨35401029, by rfl⟩ : syracuseStep 94402745 = 70802059) B70802059
theorem B4364513 : Blo 1723062 4364513 := bstep (se 2 (by rfl) ⟨1636692, by rfl⟩ : syracuseStep 4364513 = 3273385) B3273385
theorem B1940647 : Blo 1723062 1940647 := bstep (se 1 (by rfl) ⟨1455485, by rfl⟩ : syracuseStep 1940647 = 2910971) B2910971
theorem B70770023 : Blo 1723062 70770023 := bstep (se 1 (by rfl) ⟨53077517, by rfl⟩ : syracuseStep 70770023 = 106155035) B106155035
theorem B9823457 : Blo 1723062 9823457 := bstep (se 2 (by rfl) ⟨3683796, by rfl⟩ : syracuseStep 9823457 = 7367593) B7367593
theorem B2909675 : Blo 1723062 2909675 := bstep (se 1 (by rfl) ⟨2182256, by rfl⟩ : syracuseStep 2909675 = 4364513) B4364513
theorem B47180015 : Blo 1723062 47180015 := bstep (se 1 (by rfl) ⟨35385011, by rfl⟩ : syracuseStep 47180015 = 70770023) B70770023
theorem B5818607 : Blo 1723062 5818607 := bstep (se 1 (by rfl) ⟨4363955, by rfl⟩ : syracuseStep 5818607 = 8727911) B8727911
theorem B2698175 : Blo 1723062 2698175 := bstep (se 1 (by rfl) ⟨2023631, by rfl⟩ : syracuseStep 2698175 = 4047263) B4047263
theorem B1723951 : Blo 1723062 1723951 := bstep (se 1 (by rfl) ⟨1292963, by rfl⟩ : syracuseStep 1723951 = 2585927) B2585927
theorem B62935163 : Blo 1723062 62935163 := bstep (se 1 (by rfl) ⟨47201372, by rfl⟩ : syracuseStep 62935163 = 94402745) B94402745
theorem B2454247 : Blo 1723062 2454247 := bstep (se 1 (by rfl) ⟨1840685, by rfl⟩ : syracuseStep 2454247 = 3681371) B3681371
theorem B8844511 : Blo 1723062 8844511 := bstep (se 1 (by rfl) ⟨6633383, by rfl⟩ : syracuseStep 8844511 = 13266767) B13266767
theorem B42538765 : Blo 1723062 42538765 := bstep (se 3 (by rfl) ⟨7976018, by rfl⟩ : syracuseStep 42538765 = 15952037) B15952037
theorem B9820223 : Blo 1723062 9820223 := bstep (se 1 (by rfl) ⟨7365167, by rfl⟩ : syracuseStep 9820223 = 14730335) B14730335
theorem B12425663 : Blo 1723062 12425663 := bstep (se 1 (by rfl) ⟨9319247, by rfl⟩ : syracuseStep 12425663 = 18638495) B18638495
theorem B2587367 : Blo 1723062 2587367 := bstep (se 1 (by rfl) ⟨1940525, by rfl⟩ : syracuseStep 2587367 = 3881051) B3881051
theorem B31873823 : Blo 1723062 31873823 := bstep (se 1 (by rfl) ⟨23905367, by rfl⟩ : syracuseStep 31873823 = 47810735) B47810735
theorem B51059593 : Blo 1723062 51059593 := bstep (se 2 (by rfl) ⟨19147347, by rfl⟩ : syracuseStep 51059593 = 38294695) B38294695
theorem B2587529 : Blo 1723062 2587529 := bstep (se 2 (by rfl) ⟨970323, by rfl⟩ : syracuseStep 2587529 = 1940647) B1940647
theorem B8723699 : Blo 1723062 8723699 := bstep (se 1 (by rfl) ⟨6542774, by rfl⟩ : syracuseStep 8723699 = 13085549) B13085549
theorem B6546815 : Blo 1723062 6546815 := bstep (se 1 (by rfl) ⟨4910111, by rfl⟩ : syracuseStep 6546815 = 9820223) B9820223
theorem B7195133 : Blo 1723062 7195133 := bstep (se 3 (by rfl) ⟨1349087, by rfl⟩ : syracuseStep 7195133 = 2698175) B2698175
theorem B6548971 : Blo 1723062 6548971 := bstep (se 1 (by rfl) ⟨4911728, by rfl⟩ : syracuseStep 6548971 = 9823457) B9823457
theorem B3272329 : Blo 1723062 3272329 := bstep (se 2 (by rfl) ⟨1227123, by rfl⟩ : syracuseStep 3272329 = 2454247) B2454247
theorem B68079457 : Blo 1723062 68079457 := bstep (se 2 (by rfl) ⟨25529796, by rfl⟩ : syracuseStep 68079457 = 51059593) B51059593
theorem B31453343 : Blo 1723062 31453343 := bstep (se 1 (by rfl) ⟨23590007, by rfl⟩ : syracuseStep 31453343 = 47180015) B47180015
theorem B3879071 : Blo 1723062 3879071 := bstep (se 1 (by rfl) ⟨2909303, by rfl⟩ : syracuseStep 3879071 = 5818607) B5818607
theorem B11792681 : Blo 1723062 11792681 := bstep (se 2 (by rfl) ⟨4422255, by rfl⟩ : syracuseStep 11792681 = 8844511) B8844511
theorem B1724911 : Blo 1723062 1724911 := bstep (se 1 (by rfl) ⟨1293683, by rfl⟩ : syracuseStep 1724911 = 2587367) B2587367
theorem B1725019 : Blo 1723062 1725019 := bstep (se 1 (by rfl) ⟨1293764, by rfl⟩ : syracuseStep 1725019 = 2587529) B2587529
theorem B56718353 : Blo 1723062 56718353 := bstep (se 2 (by rfl) ⟨21269382, by rfl⟩ : syracuseStep 56718353 = 42538765) B42538765
theorem B41956775 : Blo 1723062 41956775 := bstep (se 1 (by rfl) ⟨31467581, by rfl⟩ : syracuseStep 41956775 = 62935163) B62935163
theorem B1939783 : Blo 1723062 1939783 := bstep (se 1 (by rfl) ⟨1454837, by rfl⟩ : syracuseStep 1939783 = 2909675) B2909675
theorem B33135101 : Blo 1723062 33135101 := bstep (se 3 (by rfl) ⟨6212831, by rfl⟩ : syracuseStep 33135101 = 12425663) B12425663
theorem B21249215 : Blo 1723062 21249215 := bstep (se 1 (by rfl) ⟨15936911, by rfl⟩ : syracuseStep 21249215 = 31873823) B31873823
theorem B5815799 : Blo 1723062 5815799 := bstep (se 1 (by rfl) ⟨4361849, by rfl⟩ : syracuseStep 5815799 = 8723699) B8723699
theorem B151248941 : Blo 1723062 151248941 := bstep (se 3 (by rfl) ⟨28359176, by rfl⟩ : syracuseStep 151248941 = 56718353) B56718353
theorem B14166143 : Blo 1723062 14166143 := bstep (se 1 (by rfl) ⟨10624607, by rfl⟩ : syracuseStep 14166143 = 21249215) B21249215
theorem B3877199 : Blo 1723062 3877199 := bstep (se 1 (by rfl) ⟨2907899, by rfl⟩ : syracuseStep 3877199 = 5815799) B5815799
theorem B27971183 : Blo 1723062 27971183 := bstep (se 1 (by rfl) ⟨20978387, by rfl⟩ : syracuseStep 27971183 = 41956775) B41956775
theorem B4796755 : Blo 1723062 4796755 := bstep (se 1 (by rfl) ⟨3597566, by rfl⟩ : syracuseStep 4796755 = 7195133) B7195133
theorem B22090067 : Blo 1723062 22090067 := bstep (se 1 (by rfl) ⟨16567550, by rfl⟩ : syracuseStep 22090067 = 33135101) B33135101
theorem B4363105 : Blo 1723062 4363105 := bstep (se 2 (by rfl) ⟨1636164, by rfl⟩ : syracuseStep 4363105 = 3272329) B3272329
theorem B90772609 : Blo 1723062 90772609 := bstep (se 2 (by rfl) ⟨34039728, by rfl⟩ : syracuseStep 90772609 = 68079457) B68079457
theorem B20968895 : Blo 1723062 20968895 := bstep (se 1 (by rfl) ⟨15726671, by rfl⟩ : syracuseStep 20968895 = 31453343) B31453343
theorem B2586047 : Blo 1723062 2586047 := bstep (se 1 (by rfl) ⟨1939535, by rfl⟩ : syracuseStep 2586047 = 3879071) B3879071
theorem B7861787 : Blo 1723062 7861787 := bstep (se 1 (by rfl) ⟨5896340, by rfl⟩ : syracuseStep 7861787 = 11792681) B11792681
theorem B2586377 : Blo 1723062 2586377 := bstep (se 2 (by rfl) ⟨969891, by rfl⟩ : syracuseStep 2586377 = 1939783) B1939783
theorem B4364543 : Blo 1723062 4364543 := bstep (se 1 (by rfl) ⟨3273407, by rfl⟩ : syracuseStep 4364543 = 6546815) B6546815
theorem B8731961 : Blo 1723062 8731961 := bstep (se 2 (by rfl) ⟨3274485, by rfl⟩ : syracuseStep 8731961 = 6548971) B6548971
theorem B5817473 : Blo 1723062 5817473 := bstep (se 2 (by rfl) ⟨2181552, by rfl⟩ : syracuseStep 5817473 = 4363105) B4363105
theorem B2909695 : Blo 1723062 2909695 := bstep (se 1 (by rfl) ⟨2182271, by rfl⟩ : syracuseStep 2909695 = 4364543) B4364543
theorem B121030145 : Blo 1723062 121030145 := bstep (se 2 (by rfl) ⟨45386304, by rfl⟩ : syracuseStep 121030145 = 90772609) B90772609
theorem B18647455 : Blo 1723062 18647455 := bstep (se 1 (by rfl) ⟨13985591, by rfl⟩ : syracuseStep 18647455 = 27971183) B27971183
theorem B13979263 : Blo 1723062 13979263 := bstep (se 1 (by rfl) ⟨10484447, by rfl⟩ : syracuseStep 13979263 = 20968895) B20968895
theorem B1724031 : Blo 1723062 1724031 := bstep (se 1 (by rfl) ⟨1293023, by rfl⟩ : syracuseStep 1724031 = 2586047) B2586047
theorem B1724251 : Blo 1723062 1724251 := bstep (se 1 (by rfl) ⟨1293188, by rfl⟩ : syracuseStep 1724251 = 2586377) B2586377
theorem B2584799 : Blo 1723062 2584799 := bstep (se 1 (by rfl) ⟨1938599, by rfl⟩ : syracuseStep 2584799 = 3877199) B3877199
theorem B5821307 : Blo 1723062 5821307 := bstep (se 1 (by rfl) ⟨4365980, by rfl⟩ : syracuseStep 5821307 = 8731961) B8731961
theorem B100832627 : Blo 1723062 100832627 := bstep (se 1 (by rfl) ⟨75624470, by rfl⟩ : syracuseStep 100832627 = 151248941) B151248941
theorem B14726711 : Blo 1723062 14726711 := bstep (se 1 (by rfl) ⟨11045033, by rfl⟩ : syracuseStep 14726711 = 22090067) B22090067
theorem B1637292373 : Blo 1723062 1637292373 := bstep (se 10 (by rfl) ⟨2398377, by rfl⟩ : syracuseStep 1637292373 = 4796755) B4796755
theorem B5241191 : Blo 1723062 5241191 := bstep (se 1 (by rfl) ⟨3930893, by rfl⟩ : syracuseStep 5241191 = 7861787) B7861787
theorem B9444095 : Blo 1723062 9444095 := bstep (se 1 (by rfl) ⟨7083071, by rfl⟩ : syracuseStep 9444095 = 14166143) B14166143
theorem B24863273 : Blo 1723062 24863273 := bstep (se 2 (by rfl) ⟨9323727, by rfl⟩ : syracuseStep 24863273 = 18647455) B18647455
theorem B13976509 : Blo 1723062 13976509 := bstep (se 3 (by rfl) ⟨2620595, by rfl⟩ : syracuseStep 13976509 = 5241191) B5241191
theorem B18639017 : Blo 1723062 18639017 := bstep (se 2 (by rfl) ⟨6989631, by rfl⟩ : syracuseStep 18639017 = 13979263) B13979263
theorem B1723199 : Blo 1723062 1723199 := bstep (se 1 (by rfl) ⟨1292399, by rfl⟩ : syracuseStep 1723199 = 2584799) B2584799
theorem B3878315 : Blo 1723062 3878315 := bstep (se 1 (by rfl) ⟨2908736, by rfl⟩ : syracuseStep 3878315 = 5817473) B5817473
theorem B80686763 : Blo 1723062 80686763 := bstep (se 1 (by rfl) ⟨60515072, by rfl⟩ : syracuseStep 80686763 = 121030145) B121030145
theorem B9817807 : Blo 1723062 9817807 := bstep (se 1 (by rfl) ⟨7363355, by rfl⟩ : syracuseStep 9817807 = 14726711) B14726711
theorem B8732225989 : Blo 1723062 8732225989 := bstep (se 4 (by rfl) ⟨818646186, by rfl⟩ : syracuseStep 8732225989 = 1637292373) B1637292373
theorem B6296063 : Blo 1723062 6296063 := bstep (se 1 (by rfl) ⟨4722047, by rfl⟩ : syracuseStep 6296063 = 9444095) B9444095
theorem B3879593 : Blo 1723062 3879593 := bstep (se 2 (by rfl) ⟨1454847, by rfl⟩ : syracuseStep 3879593 = 2909695) B2909695
theorem B3880871 : Blo 1723062 3880871 := bstep (se 1 (by rfl) ⟨2910653, by rfl⟩ : syracuseStep 3880871 = 5821307) B5821307
theorem B67221751 : Blo 1723062 67221751 := bstep (se 1 (by rfl) ⟨50416313, by rfl⟩ : syracuseStep 67221751 = 100832627) B100832627
theorem B89629001 : Blo 1723062 89629001 := bstep (se 2 (by rfl) ⟨33610875, by rfl⟩ : syracuseStep 89629001 = 67221751) B67221751
theorem B53791175 : Blo 1723062 53791175 := bstep (se 1 (by rfl) ⟨40343381, by rfl⟩ : syracuseStep 53791175 = 80686763) B80686763
theorem B16575515 : Blo 1723062 16575515 := bstep (se 1 (by rfl) ⟨12431636, by rfl⟩ : syracuseStep 16575515 = 24863273) B24863273
theorem B16789501 : Blo 1723062 16789501 := bstep (se 3 (by rfl) ⟨3148031, by rfl⟩ : syracuseStep 16789501 = 6296063) B6296063
theorem B2585543 : Blo 1723062 2585543 := bstep (se 1 (by rfl) ⟨1939157, by rfl⟩ : syracuseStep 2585543 = 3878315) B3878315
theorem B2586395 : Blo 1723062 2586395 := bstep (se 1 (by rfl) ⟨1939796, by rfl⟩ : syracuseStep 2586395 = 3879593) B3879593
theorem B11642967985 : Blo 1723062 11642967985 := bstep (se 2 (by rfl) ⟨4366112994, by rfl⟩ : syracuseStep 11642967985 = 8732225989) B8732225989
theorem B18635345 : Blo 1723062 18635345 := bstep (se 2 (by rfl) ⟨6988254, by rfl⟩ : syracuseStep 18635345 = 13976509) B13976509
theorem B2587247 : Blo 1723062 2587247 := bstep (se 1 (by rfl) ⟨1940435, by rfl⟩ : syracuseStep 2587247 = 3880871) B3880871
theorem B12426011 : Blo 1723062 12426011 := bstep (se 1 (by rfl) ⟨9319508, by rfl⟩ : syracuseStep 12426011 = 18639017) B18639017
theorem B13090409 : Blo 1723062 13090409 := bstep (se 2 (by rfl) ⟨4908903, by rfl⟩ : syracuseStep 13090409 = 9817807) B9817807
theorem B59752667 : Blo 1723062 59752667 := bstep (se 1 (by rfl) ⟨44814500, by rfl⟩ : syracuseStep 59752667 = 89629001) B89629001
theorem B143443133 : Blo 1723062 143443133 := bstep (se 3 (by rfl) ⟨26895587, by rfl⟩ : syracuseStep 143443133 = 53791175) B53791175
theorem B8284007 : Blo 1723062 8284007 := bstep (se 1 (by rfl) ⟨6213005, by rfl⟩ : syracuseStep 8284007 = 12426011) B12426011
theorem B8726939 : Blo 1723062 8726939 := bstep (se 1 (by rfl) ⟨6545204, by rfl⟩ : syracuseStep 8726939 = 13090409) B13090409
theorem B15523957313 : Blo 1723062 15523957313 := bstep (se 2 (by rfl) ⟨5821483992, by rfl⟩ : syracuseStep 15523957313 = 11642967985) B11642967985
theorem B1723695 : Blo 1723062 1723695 := bstep (se 1 (by rfl) ⟨1292771, by rfl⟩ : syracuseStep 1723695 = 2585543) B2585543
theorem B1724263 : Blo 1723062 1724263 := bstep (se 1 (by rfl) ⟨1293197, by rfl⟩ : syracuseStep 1724263 = 2586395) B2586395
theorem B12423563 : Blo 1723062 12423563 := bstep (se 1 (by rfl) ⟨9317672, by rfl⟩ : syracuseStep 12423563 = 18635345) B18635345
theorem B1724831 : Blo 1723062 1724831 := bstep (se 1 (by rfl) ⟨1293623, by rfl⟩ : syracuseStep 1724831 = 2587247) B2587247
theorem B89544005 : Blo 1723062 89544005 := bstep (se 4 (by rfl) ⟨8394750, by rfl⟩ : syracuseStep 89544005 = 16789501) B16789501
theorem B11050343 : Blo 1723062 11050343 := bstep (se 1 (by rfl) ⟨8287757, by rfl⟩ : syracuseStep 11050343 = 16575515) B16575515
theorem B8282375 : Blo 1723062 8282375 := bstep (se 1 (by rfl) ⟨6211781, by rfl⟩ : syracuseStep 8282375 = 12423563) B12423563
theorem B59696003 : Blo 1723062 59696003 := bstep (se 1 (by rfl) ⟨44772002, by rfl⟩ : syracuseStep 59696003 = 89544005) B89544005
theorem B5522671 : Blo 1723062 5522671 := bstep (se 1 (by rfl) ⟨4142003, by rfl⟩ : syracuseStep 5522671 = 8284007) B8284007
theorem B5817959 : Blo 1723062 5817959 := bstep (se 1 (by rfl) ⟨4363469, by rfl⟩ : syracuseStep 5817959 = 8726939) B8726939
theorem B7366895 : Blo 1723062 7366895 := bstep (se 1 (by rfl) ⟨5525171, by rfl⟩ : syracuseStep 7366895 = 11050343) B11050343
theorem B95628755 : Blo 1723062 95628755 := bstep (se 1 (by rfl) ⟨71721566, by rfl⟩ : syracuseStep 95628755 = 143443133) B143443133
theorem B39835111 : Blo 1723062 39835111 := bstep (se 1 (by rfl) ⟨29876333, by rfl⟩ : syracuseStep 39835111 = 59752667) B59752667
theorem B10349304875 : Blo 1723062 10349304875 := bstep (se 1 (by rfl) ⟨7761978656, by rfl⟩ : syracuseStep 10349304875 = 15523957313) B15523957313
theorem B5521583 : Blo 1723062 5521583 := bstep (se 1 (by rfl) ⟨4141187, by rfl⟩ : syracuseStep 5521583 = 8282375) B8282375
theorem B39797335 : Blo 1723062 39797335 := bstep (se 1 (by rfl) ⟨29848001, by rfl⟩ : syracuseStep 39797335 = 59696003) B59696003
theorem B63752503 : Blo 1723062 63752503 := bstep (se 1 (by rfl) ⟨47814377, by rfl⟩ : syracuseStep 63752503 = 95628755) B95628755
theorem B3878639 : Blo 1723062 3878639 := bstep (se 1 (by rfl) ⟨2908979, by rfl⟩ : syracuseStep 3878639 = 5817959) B5817959
theorem B4911263 : Blo 1723062 4911263 := bstep (se 1 (by rfl) ⟨3683447, by rfl⟩ : syracuseStep 4911263 = 7366895) B7366895
theorem B53113481 : Blo 1723062 53113481 := bstep (se 2 (by rfl) ⟨19917555, by rfl⟩ : syracuseStep 53113481 = 39835111) B39835111
theorem B6899536583 : Blo 1723062 6899536583 := bstep (se 1 (by rfl) ⟨5174652437, by rfl⟩ : syracuseStep 6899536583 = 10349304875) B10349304875
theorem B7363561 : Blo 1723062 7363561 := bstep (se 2 (by rfl) ⟨2761335, by rfl⟩ : syracuseStep 7363561 = 5522671) B5522671
theorem B3681055 : Blo 1723062 3681055 := bstep (se 1 (by rfl) ⟨2760791, by rfl⟩ : syracuseStep 3681055 = 5521583) B5521583
theorem B85003337 : Blo 1723062 85003337 := bstep (se 2 (by rfl) ⟨31876251, by rfl⟩ : syracuseStep 85003337 = 63752503) B63752503
theorem B35408987 : Blo 1723062 35408987 := bstep (se 1 (by rfl) ⟨26556740, by rfl⟩ : syracuseStep 35408987 = 53113481) B53113481
theorem B53063113 : Blo 1723062 53063113 := bstep (se 2 (by rfl) ⟨19898667, by rfl⟩ : syracuseStep 53063113 = 39797335) B39797335
theorem B9818081 : Blo 1723062 9818081 := bstep (se 2 (by rfl) ⟨3681780, by rfl⟩ : syracuseStep 9818081 = 7363561) B7363561
theorem B2585759 : Blo 1723062 2585759 := bstep (se 1 (by rfl) ⟨1939319, by rfl⟩ : syracuseStep 2585759 = 3878639) B3878639
theorem B3274175 : Blo 1723062 3274175 := bstep (se 1 (by rfl) ⟨2455631, by rfl⟩ : syracuseStep 3274175 = 4911263) B4911263
theorem B4599691055 : Blo 1723062 4599691055 := bstep (se 1 (by rfl) ⟨3449768291, by rfl⟩ : syracuseStep 4599691055 = 6899536583) B6899536583
theorem B4908073 : Blo 1723062 4908073 := bstep (se 2 (by rfl) ⟨1840527, by rfl⟩ : syracuseStep 4908073 = 3681055) B3681055
theorem B1723839 : Blo 1723062 1723839 := bstep (se 1 (by rfl) ⟨1292879, by rfl⟩ : syracuseStep 1723839 = 2585759) B2585759
theorem B2182783 : Blo 1723062 2182783 := bstep (se 1 (by rfl) ⟨1637087, by rfl⟩ : syracuseStep 2182783 = 3274175) B3274175
theorem B70750817 : Blo 1723062 70750817 := bstep (se 2 (by rfl) ⟨26531556, by rfl⟩ : syracuseStep 70750817 = 53063113) B53063113
theorem B56668891 : Blo 1723062 56668891 := bstep (se 1 (by rfl) ⟨42501668, by rfl⟩ : syracuseStep 56668891 = 85003337) B85003337
theorem B23605991 : Blo 1723062 23605991 := bstep (se 1 (by rfl) ⟨17704493, by rfl⟩ : syracuseStep 23605991 = 35408987) B35408987
theorem B3066460703 : Blo 1723062 3066460703 := bstep (se 1 (by rfl) ⟨2299845527, by rfl⟩ : syracuseStep 3066460703 = 4599691055) B4599691055
theorem B6545387 : Blo 1723062 6545387 := bstep (se 1 (by rfl) ⟨4909040, by rfl⟩ : syracuseStep 6545387 = 9818081) B9818081
theorem B15737327 : Blo 1723062 15737327 := bstep (se 1 (by rfl) ⟨11802995, by rfl⟩ : syracuseStep 15737327 = 23605991) B23605991
theorem B2044307135 : Blo 1723062 2044307135 := bstep (se 1 (by rfl) ⟨1533230351, by rfl⟩ : syracuseStep 2044307135 = 3066460703) B3066460703
theorem B2910377 : Blo 1723062 2910377 := bstep (se 2 (by rfl) ⟨1091391, by rfl⟩ : syracuseStep 2910377 = 2182783) B2182783
theorem B75558521 : Blo 1723062 75558521 := bstep (se 2 (by rfl) ⟨28334445, by rfl⟩ : syracuseStep 75558521 = 56668891) B56668891
theorem B4363591 : Blo 1723062 4363591 := bstep (se 1 (by rfl) ⟨3272693, by rfl⟩ : syracuseStep 4363591 = 6545387) B6545387
theorem B47167211 : Blo 1723062 47167211 := bstep (se 1 (by rfl) ⟨35375408, by rfl⟩ : syracuseStep 47167211 = 70750817) B70750817
theorem B6544097 : Blo 1723062 6544097 := bstep (se 2 (by rfl) ⟨2454036, by rfl⟩ : syracuseStep 6544097 = 4908073) B4908073
theorem B1362871423 : Blo 1723062 1362871423 := bstep (se 1 (by rfl) ⟨1022153567, by rfl⟩ : syracuseStep 1362871423 = 2044307135) B2044307135
theorem B5818121 : Blo 1723062 5818121 := bstep (se 2 (by rfl) ⟨2181795, by rfl⟩ : syracuseStep 5818121 = 4363591) B4363591
theorem B31444807 : Blo 1723062 31444807 := bstep (se 1 (by rfl) ⟨23583605, by rfl⟩ : syracuseStep 31444807 = 47167211) B47167211
theorem B4362731 : Blo 1723062 4362731 := bstep (se 1 (by rfl) ⟨3272048, by rfl⟩ : syracuseStep 4362731 = 6544097) B6544097
theorem B10491551 : Blo 1723062 10491551 := bstep (se 1 (by rfl) ⟨7868663, by rfl⟩ : syracuseStep 10491551 = 15737327) B15737327
theorem B1940251 : Blo 1723062 1940251 := bstep (se 1 (by rfl) ⟨1455188, by rfl⟩ : syracuseStep 1940251 = 2910377) B2910377
theorem B201489389 : Blo 1723062 201489389 := bstep (se 3 (by rfl) ⟨37779260, by rfl⟩ : syracuseStep 201489389 = 75558521) B75558521
theorem B2908487 : Blo 1723062 2908487 := bstep (se 1 (by rfl) ⟨2181365, by rfl⟩ : syracuseStep 2908487 = 4362731) B4362731
theorem B134326259 : Blo 1723062 134326259 := bstep (se 1 (by rfl) ⟨100744694, by rfl⟩ : syracuseStep 134326259 = 201489389) B201489389
theorem B3878747 : Blo 1723062 3878747 := bstep (se 1 (by rfl) ⟨2909060, by rfl⟩ : syracuseStep 3878747 = 5818121) B5818121
theorem B1817161897 : Blo 1723062 1817161897 := bstep (se 2 (by rfl) ⟨681435711, by rfl⟩ : syracuseStep 1817161897 = 1362871423) B1362871423
theorem B2587001 : Blo 1723062 2587001 := bstep (se 2 (by rfl) ⟨970125, by rfl⟩ : syracuseStep 2587001 = 1940251) B1940251
theorem B6994367 : Blo 1723062 6994367 := bstep (se 1 (by rfl) ⟨5245775, by rfl⟩ : syracuseStep 6994367 = 10491551) B10491551
theorem B41926409 : Blo 1723062 41926409 := bstep (se 2 (by rfl) ⟨15722403, by rfl⟩ : syracuseStep 41926409 = 31444807) B31444807
theorem B2422882529 : Blo 1723062 2422882529 := bstep (se 2 (by rfl) ⟨908580948, by rfl⟩ : syracuseStep 2422882529 = 1817161897) B1817161897
theorem B4662911 : Blo 1723062 4662911 := bstep (se 1 (by rfl) ⟨3497183, by rfl⟩ : syracuseStep 4662911 = 6994367) B6994367
theorem B89550839 : Blo 1723062 89550839 := bstep (se 1 (by rfl) ⟨67163129, by rfl⟩ : syracuseStep 89550839 = 134326259) B134326259
theorem B1724667 : Blo 1723062 1724667 := bstep (se 1 (by rfl) ⟨1293500, by rfl⟩ : syracuseStep 1724667 = 2587001) B2587001
theorem B2585831 : Blo 1723062 2585831 := bstep (se 1 (by rfl) ⟨1939373, by rfl⟩ : syracuseStep 2585831 = 3878747) B3878747
theorem B1938991 : Blo 1723062 1938991 := bstep (se 1 (by rfl) ⟨1454243, by rfl⟩ : syracuseStep 1938991 = 2908487) B2908487
theorem B27950939 : Blo 1723062 27950939 := bstep (se 1 (by rfl) ⟨20963204, by rfl⟩ : syracuseStep 27950939 = 41926409) B41926409
theorem B1723887 : Blo 1723062 1723887 := bstep (se 1 (by rfl) ⟨1292915, by rfl⟩ : syracuseStep 1723887 = 2585831) B2585831
theorem B3108607 : Blo 1723062 3108607 := bstep (se 1 (by rfl) ⟨2331455, by rfl⟩ : syracuseStep 3108607 = 4662911) B4662911
theorem B2585321 : Blo 1723062 2585321 := bstep (se 2 (by rfl) ⟨969495, by rfl⟩ : syracuseStep 2585321 = 1938991) B1938991
theorem B18633959 : Blo 1723062 18633959 := bstep (se 1 (by rfl) ⟨13975469, by rfl⟩ : syracuseStep 18633959 = 27950939) B27950939
theorem B59700559 : Blo 1723062 59700559 := bstep (se 1 (by rfl) ⟨44775419, by rfl⟩ : syracuseStep 59700559 = 89550839) B89550839
theorem B1615255019 : Blo 1723062 1615255019 := bstep (se 1 (by rfl) ⟨1211441264, by rfl⟩ : syracuseStep 1615255019 = 2422882529) B2422882529
theorem B1723547 : Blo 1723062 1723547 := bstep (se 1 (by rfl) ⟨1292660, by rfl⟩ : syracuseStep 1723547 = 2585321) B2585321
theorem B12422639 : Blo 1723062 12422639 := bstep (se 1 (by rfl) ⟨9316979, by rfl⟩ : syracuseStep 12422639 = 18633959) B18633959
theorem B1076836679 : Blo 1723062 1076836679 := bstep (se 1 (by rfl) ⟨807627509, by rfl⟩ : syracuseStep 1076836679 = 1615255019) B1615255019
theorem B16579237 : Blo 1723062 16579237 := bstep (se 4 (by rfl) ⟨1554303, by rfl⟩ : syracuseStep 16579237 = 3108607) B3108607
theorem B79600745 : Blo 1723062 79600745 := bstep (se 2 (by rfl) ⟨29850279, by rfl⟩ : syracuseStep 79600745 = 59700559) B59700559
theorem B717891119 : Blo 1723062 717891119 := bstep (se 1 (by rfl) ⟨538418339, by rfl⟩ : syracuseStep 717891119 = 1076836679) B1076836679
theorem B22105649 : Blo 1723062 22105649 := bstep (se 2 (by rfl) ⟨8289618, by rfl⟩ : syracuseStep 22105649 = 16579237) B16579237
theorem B53067163 : Blo 1723062 53067163 := bstep (se 1 (by rfl) ⟨39800372, by rfl⟩ : syracuseStep 53067163 = 79600745) B79600745
theorem B8281759 : Blo 1723062 8281759 := bstep (se 1 (by rfl) ⟨6211319, by rfl⟩ : syracuseStep 8281759 = 12422639) B12422639
theorem B478594079 : Blo 1723062 478594079 := bstep (se 1 (by rfl) ⟨358945559, by rfl⟩ : syracuseStep 478594079 = 717891119) B717891119
theorem B70756217 : Blo 1723062 70756217 := bstep (se 2 (by rfl) ⟨26533581, by rfl⟩ : syracuseStep 70756217 = 53067163) B53067163
theorem B11042345 : Blo 1723062 11042345 := bstep (se 2 (by rfl) ⟨4140879, by rfl⟩ : syracuseStep 11042345 = 8281759) B8281759
theorem B14737099 : Blo 1723062 14737099 := bstep (se 1 (by rfl) ⟨11052824, by rfl⟩ : syracuseStep 14737099 = 22105649) B22105649
theorem B319062719 : Blo 1723062 319062719 := bstep (se 1 (by rfl) ⟨239297039, by rfl⟩ : syracuseStep 319062719 = 478594079) B478594079
theorem B47170811 : Blo 1723062 47170811 := bstep (se 1 (by rfl) ⟨35378108, by rfl⟩ : syracuseStep 47170811 = 70756217) B70756217
theorem B19649465 : Blo 1723062 19649465 := bstep (se 2 (by rfl) ⟨7368549, by rfl⟩ : syracuseStep 19649465 = 14737099) B14737099
theorem B7361563 : Blo 1723062 7361563 := bstep (se 1 (by rfl) ⟨5521172, by rfl⟩ : syracuseStep 7361563 = 11042345) B11042345
theorem B13099643 : Blo 1723062 13099643 := bstep (se 1 (by rfl) ⟨9824732, by rfl⟩ : syracuseStep 13099643 = 19649465) B19649465
theorem B9815417 : Blo 1723062 9815417 := bstep (se 2 (by rfl) ⟨3680781, by rfl⟩ : syracuseStep 9815417 = 7361563) B7361563
theorem B212708479 : Blo 1723062 212708479 := bstep (se 1 (by rfl) ⟨159531359, by rfl⟩ : syracuseStep 212708479 = 319062719) B319062719
theorem B31447207 : Blo 1723062 31447207 := bstep (se 1 (by rfl) ⟨23585405, by rfl⟩ : syracuseStep 31447207 = 47170811) B47170811
theorem B8733095 : Blo 1723062 8733095 := bstep (se 1 (by rfl) ⟨6549821, by rfl⟩ : syracuseStep 8733095 = 13099643) B13099643
theorem B41929609 : Blo 1723062 41929609 := bstep (se 2 (by rfl) ⟨15723603, by rfl⟩ : syracuseStep 41929609 = 31447207) B31447207
theorem B283611305 : Blo 1723062 283611305 := bstep (se 2 (by rfl) ⟨106354239, by rfl⟩ : syracuseStep 283611305 = 212708479) B212708479
theorem B6543611 : Blo 1723062 6543611 := bstep (se 1 (by rfl) ⟨4907708, by rfl⟩ : syracuseStep 6543611 = 9815417) B9815417
theorem B756296813 : Blo 1723062 756296813 := bstep (se 3 (by rfl) ⟨141805652, by rfl⟩ : syracuseStep 756296813 = 283611305) B283611305
theorem B55906145 : Blo 1723062 55906145 := bstep (se 2 (by rfl) ⟨20964804, by rfl⟩ : syracuseStep 55906145 = 41929609) B41929609
theorem B4362407 : Blo 1723062 4362407 := bstep (se 1 (by rfl) ⟨3271805, by rfl⟩ : syracuseStep 4362407 = 6543611) B6543611
theorem B5822063 : Blo 1723062 5822063 := bstep (se 1 (by rfl) ⟨4366547, by rfl⟩ : syracuseStep 5822063 = 8733095) B8733095
theorem B2908271 : Blo 1723062 2908271 := bstep (se 1 (by rfl) ⟨2181203, by rfl⟩ : syracuseStep 2908271 = 4362407) B4362407
theorem B504197875 : Blo 1723062 504197875 := bstep (se 1 (by rfl) ⟨378148406, by rfl⟩ : syracuseStep 504197875 = 756296813) B756296813
theorem B37270763 : Blo 1723062 37270763 := bstep (se 1 (by rfl) ⟨27953072, by rfl⟩ : syracuseStep 37270763 = 55906145) B55906145
theorem B3881375 : Blo 1723062 3881375 := bstep (se 1 (by rfl) ⟨2911031, by rfl⟩ : syracuseStep 3881375 = 5822063) B5822063
theorem B24847175 : Blo 1723062 24847175 := bstep (se 1 (by rfl) ⟨18635381, by rfl⟩ : syracuseStep 24847175 = 37270763) B37270763
theorem B672263833 : Blo 1723062 672263833 := bstep (se 2 (by rfl) ⟨252098937, by rfl⟩ : syracuseStep 672263833 = 504197875) B504197875
theorem B1938847 : Blo 1723062 1938847 := bstep (se 1 (by rfl) ⟨1454135, by rfl⟩ : syracuseStep 1938847 = 2908271) B2908271
theorem B2587583 : Blo 1723062 2587583 := bstep (se 1 (by rfl) ⟨1940687, by rfl⟩ : syracuseStep 2587583 = 3881375) B3881375
theorem B16564783 : Blo 1723062 16564783 := bstep (se 1 (by rfl) ⟨12423587, by rfl⟩ : syracuseStep 16564783 = 24847175) B24847175
theorem B2585129 : Blo 1723062 2585129 := bstep (se 2 (by rfl) ⟨969423, by rfl⟩ : syracuseStep 2585129 = 1938847) B1938847
theorem B1725055 : Blo 1723062 1725055 := bstep (se 1 (by rfl) ⟨1293791, by rfl⟩ : syracuseStep 1725055 = 2587583) B2587583
theorem B896351777 : Blo 1723062 896351777 := bstep (se 2 (by rfl) ⟨336131916, by rfl⟩ : syracuseStep 896351777 = 672263833) B672263833
theorem B22086377 : Blo 1723062 22086377 := bstep (se 2 (by rfl) ⟨8282391, by rfl⟩ : syracuseStep 22086377 = 16564783) B16564783
theorem B597567851 : Blo 1723062 597567851 := bstep (se 1 (by rfl) ⟨448175888, by rfl⟩ : syracuseStep 597567851 = 896351777) B896351777
theorem B1723419 : Blo 1723062 1723419 := bstep (se 1 (by rfl) ⟨1292564, by rfl⟩ : syracuseStep 1723419 = 2585129) B2585129
theorem B398378567 : Blo 1723062 398378567 := bstep (se 1 (by rfl) ⟨298783925, by rfl⟩ : syracuseStep 398378567 = 597567851) B597567851
theorem B14724251 : Blo 1723062 14724251 := bstep (se 1 (by rfl) ⟨11043188, by rfl⟩ : syracuseStep 14724251 = 22086377) B22086377
theorem B265585711 : Blo 1723062 265585711 := bstep (se 1 (by rfl) ⟨199189283, by rfl⟩ : syracuseStep 265585711 = 398378567) B398378567
theorem B9816167 : Blo 1723062 9816167 := bstep (se 1 (by rfl) ⟨7362125, by rfl⟩ : syracuseStep 9816167 = 14724251) B14724251
theorem B354114281 : Blo 1723062 354114281 := bstep (se 2 (by rfl) ⟨132792855, by rfl⟩ : syracuseStep 354114281 = 265585711) B265585711
theorem B6544111 : Blo 1723062 6544111 := bstep (se 1 (by rfl) ⟨4908083, by rfl⟩ : syracuseStep 6544111 = 9816167) B9816167
theorem B8725481 : Blo 1723062 8725481 := bstep (se 2 (by rfl) ⟨3272055, by rfl⟩ : syracuseStep 8725481 = 6544111) B6544111
theorem B944304749 : Blo 1723062 944304749 := bstep (se 3 (by rfl) ⟨177057140, by rfl⟩ : syracuseStep 944304749 = 354114281) B354114281
theorem B5816987 : Blo 1723062 5816987 := bstep (se 1 (by rfl) ⟨4362740, by rfl⟩ : syracuseStep 5816987 = 8725481) B8725481
theorem B629536499 : Blo 1723062 629536499 := bstep (se 1 (by rfl) ⟨472152374, by rfl⟩ : syracuseStep 629536499 = 944304749) B944304749
theorem B3877991 : Blo 1723062 3877991 := bstep (se 1 (by rfl) ⟨2908493, by rfl⟩ : syracuseStep 3877991 = 5816987) B5816987
theorem B419690999 : Blo 1723062 419690999 := bstep (se 1 (by rfl) ⟨314768249, by rfl⟩ : syracuseStep 419690999 = 629536499) B629536499
theorem B279793999 : Blo 1723062 279793999 := bstep (se 1 (by rfl) ⟨209845499, by rfl⟩ : syracuseStep 279793999 = 419690999) B419690999
theorem B2585327 : Blo 1723062 2585327 := bstep (se 1 (by rfl) ⟨1938995, by rfl⟩ : syracuseStep 2585327 = 3877991) B3877991
theorem B373058665 : Blo 1723062 373058665 := bstep (se 2 (by rfl) ⟨139896999, by rfl⟩ : syracuseStep 373058665 = 279793999) B279793999
theorem B1723551 : Blo 1723062 1723551 := bstep (se 1 (by rfl) ⟨1292663, by rfl⟩ : syracuseStep 1723551 = 2585327) B2585327
theorem B7958584853 : Blo 1723062 7958584853 := bstep (se 6 (by rfl) ⟨186529332, by rfl⟩ : syracuseStep 7958584853 = 373058665) B373058665
theorem B5305723235 : Blo 1723062 5305723235 := bstep (se 1 (by rfl) ⟨3979292426, by rfl⟩ : syracuseStep 5305723235 = 7958584853) B7958584853
theorem B3537148823 : Blo 1723062 3537148823 := bstep (se 1 (by rfl) ⟨2652861617, by rfl⟩ : syracuseStep 3537148823 = 5305723235) B5305723235
theorem B2358099215 : Blo 1723062 2358099215 := bstep (se 1 (by rfl) ⟨1768574411, by rfl⟩ : syracuseStep 2358099215 = 3537148823) B3537148823
theorem B1572066143 : Blo 1723062 1572066143 := bstep (se 1 (by rfl) ⟨1179049607, by rfl⟩ : syracuseStep 1572066143 = 2358099215) B2358099215
theorem B1048044095 : Blo 1723062 1048044095 := bstep (se 1 (by rfl) ⟨786033071, by rfl⟩ : syracuseStep 1048044095 = 1572066143) B1572066143
theorem B698696063 : Blo 1723062 698696063 := bstep (se 1 (by rfl) ⟨524022047, by rfl⟩ : syracuseStep 698696063 = 1048044095) B1048044095
theorem B465797375 : Blo 1723062 465797375 := bstep (se 1 (by rfl) ⟨349348031, by rfl⟩ : syracuseStep 465797375 = 698696063) B698696063
theorem B310531583 : Blo 1723062 310531583 := bstep (se 1 (by rfl) ⟨232898687, by rfl⟩ : syracuseStep 310531583 = 465797375) B465797375
theorem B207021055 : Blo 1723062 207021055 := bstep (se 1 (by rfl) ⟨155265791, by rfl⟩ : syracuseStep 207021055 = 310531583) B310531583
theorem B276028073 : Blo 1723062 276028073 := bstep (se 2 (by rfl) ⟨103510527, by rfl⟩ : syracuseStep 276028073 = 207021055) B207021055
theorem B184018715 : Blo 1723062 184018715 := bstep (se 1 (by rfl) ⟨138014036, by rfl⟩ : syracuseStep 184018715 = 276028073) B276028073
theorem B122679143 : Blo 1723062 122679143 := bstep (se 1 (by rfl) ⟨92009357, by rfl⟩ : syracuseStep 122679143 = 184018715) B184018715
theorem B81786095 : Blo 1723062 81786095 := bstep (se 1 (by rfl) ⟨61339571, by rfl⟩ : syracuseStep 81786095 = 122679143) B122679143
theorem B54524063 : Blo 1723062 54524063 := bstep (se 1 (by rfl) ⟨40893047, by rfl⟩ : syracuseStep 54524063 = 81786095) B81786095
theorem B145397501 : Blo 1723062 145397501 := bstep (se 3 (by rfl) ⟨27262031, by rfl⟩ : syracuseStep 145397501 = 54524063) B54524063
theorem B96931667 : Blo 1723062 96931667 := bstep (se 1 (by rfl) ⟨72698750, by rfl⟩ : syracuseStep 96931667 = 145397501) B145397501
theorem B64621111 : Blo 1723062 64621111 := bstep (se 1 (by rfl) ⟨48465833, by rfl⟩ : syracuseStep 64621111 = 96931667) B96931667
theorem B86161481 : Blo 1723062 86161481 := bstep (se 2 (by rfl) ⟨32310555, by rfl⟩ : syracuseStep 86161481 = 64621111) B64621111
theorem B57440987 : Blo 1723062 57440987 := bstep (se 1 (by rfl) ⟨43080740, by rfl⟩ : syracuseStep 57440987 = 86161481) B86161481
theorem B38293991 : Blo 1723062 38293991 := bstep (se 1 (by rfl) ⟨28720493, by rfl⟩ : syracuseStep 38293991 = 57440987) B57440987
theorem B25529327 : Blo 1723062 25529327 := bstep (se 1 (by rfl) ⟨19146995, by rfl⟩ : syracuseStep 25529327 = 38293991) B38293991
theorem B17019551 : Blo 1723062 17019551 := bstep (se 1 (by rfl) ⟨12764663, by rfl⟩ : syracuseStep 17019551 = 25529327) B25529327
theorem B11346367 : Blo 1723062 11346367 := bstep (se 1 (by rfl) ⟨8509775, by rfl⟩ : syracuseStep 11346367 = 17019551) B17019551
theorem B15128489 : Blo 1723062 15128489 := bstep (se 2 (by rfl) ⟨5673183, by rfl⟩ : syracuseStep 15128489 = 11346367) B11346367
theorem B40342637 : Blo 1723062 40342637 := bstep (se 3 (by rfl) ⟨7564244, by rfl⟩ : syracuseStep 40342637 = 15128489) B15128489
theorem B26895091 : Blo 1723062 26895091 := bstep (se 1 (by rfl) ⟨20171318, by rfl⟩ : syracuseStep 26895091 = 40342637) B40342637
theorem B35860121 : Blo 1723062 35860121 := bstep (se 2 (by rfl) ⟨13447545, by rfl⟩ : syracuseStep 35860121 = 26895091) B26895091
theorem B23906747 : Blo 1723062 23906747 := bstep (se 1 (by rfl) ⟨17930060, by rfl⟩ : syracuseStep 23906747 = 35860121) B35860121
theorem B15937831 : Blo 1723062 15937831 := bstep (se 1 (by rfl) ⟨11953373, by rfl⟩ : syracuseStep 15937831 = 23906747) B23906747
theorem B21250441 : Blo 1723062 21250441 := bstep (se 2 (by rfl) ⟨7968915, by rfl⟩ : syracuseStep 21250441 = 15937831) B15937831
theorem B28333921 : Blo 1723062 28333921 := bstep (se 2 (by rfl) ⟨10625220, by rfl⟩ : syracuseStep 28333921 = 21250441) B21250441
theorem B37778561 : Blo 1723062 37778561 := bstep (se 2 (by rfl) ⟨14166960, by rfl⟩ : syracuseStep 37778561 = 28333921) B28333921
theorem B25185707 : Blo 1723062 25185707 := bstep (se 1 (by rfl) ⟨18889280, by rfl⟩ : syracuseStep 25185707 = 37778561) B37778561
theorem B16790471 : Blo 1723062 16790471 := bstep (se 1 (by rfl) ⟨12592853, by rfl⟩ : syracuseStep 16790471 = 25185707) B25185707
theorem B11193647 : Blo 1723062 11193647 := bstep (se 1 (by rfl) ⟨8395235, by rfl⟩ : syracuseStep 11193647 = 16790471) B16790471
theorem B29849725 : Blo 1723062 29849725 := bstep (se 3 (by rfl) ⟨5596823, by rfl⟩ : syracuseStep 29849725 = 11193647) B11193647
theorem B159198533 : Blo 1723062 159198533 := bstep (se 4 (by rfl) ⟨14924862, by rfl⟩ : syracuseStep 159198533 = 29849725) B29849725
theorem B106132355 : Blo 1723062 106132355 := bstep (se 1 (by rfl) ⟨79599266, by rfl⟩ : syracuseStep 106132355 = 159198533) B159198533
theorem B70754903 : Blo 1723062 70754903 := bstep (se 1 (by rfl) ⟨53066177, by rfl⟩ : syracuseStep 70754903 = 106132355) B106132355
theorem B47169935 : Blo 1723062 47169935 := bstep (se 1 (by rfl) ⟨35377451, by rfl⟩ : syracuseStep 47169935 = 70754903) B70754903
theorem B31446623 : Blo 1723062 31446623 := bstep (se 1 (by rfl) ⟨23584967, by rfl⟩ : syracuseStep 31446623 = 47169935) B47169935
theorem B20964415 : Blo 1723062 20964415 := bstep (se 1 (by rfl) ⟨15723311, by rfl⟩ : syracuseStep 20964415 = 31446623) B31446623
theorem B27952553 : Blo 1723062 27952553 := bstep (se 2 (by rfl) ⟨10482207, by rfl⟩ : syracuseStep 27952553 = 20964415) B20964415
theorem B18635035 : Blo 1723062 18635035 := bstep (se 1 (by rfl) ⟨13976276, by rfl⟩ : syracuseStep 18635035 = 27952553) B27952553
theorem B24846713 : Blo 1723062 24846713 := bstep (se 2 (by rfl) ⟨9317517, by rfl⟩ : syracuseStep 24846713 = 18635035) B18635035
theorem B16564475 : Blo 1723062 16564475 := bstep (se 1 (by rfl) ⟨12423356, by rfl⟩ : syracuseStep 16564475 = 24846713) B24846713
theorem B11042983 : Blo 1723062 11042983 := bstep (se 1 (by rfl) ⟨8282237, by rfl⟩ : syracuseStep 11042983 = 16564475) B16564475
theorem B14723977 : Blo 1723062 14723977 := bstep (se 2 (by rfl) ⟨5521491, by rfl⟩ : syracuseStep 14723977 = 11042983) B11042983
theorem B19631969 : Blo 1723062 19631969 := bstep (se 2 (by rfl) ⟨7361988, by rfl⟩ : syracuseStep 19631969 = 14723977) B14723977
theorem B13087979 : Blo 1723062 13087979 := bstep (se 1 (by rfl) ⟨9815984, by rfl⟩ : syracuseStep 13087979 = 19631969) B19631969
theorem B8725319 : Blo 1723062 8725319 := bstep (se 1 (by rfl) ⟨6543989, by rfl⟩ : syracuseStep 8725319 = 13087979) B13087979
theorem B5816879 : Blo 1723062 5816879 := bstep (se 1 (by rfl) ⟨4362659, by rfl⟩ : syracuseStep 5816879 = 8725319) B8725319
theorem B3877919 : Blo 1723062 3877919 := bstep (se 1 (by rfl) ⟨2908439, by rfl⟩ : syracuseStep 3877919 = 5816879) B5816879
theorem B2585279 : Blo 1723062 2585279 := bstep (se 1 (by rfl) ⟨1938959, by rfl⟩ : syracuseStep 2585279 = 3877919) B3877919
theorem B1723519 : Blo 1723062 1723519 := bstep (se 1 (by rfl) ⟨1292639, by rfl⟩ : syracuseStep 1723519 = 2585279) B2585279

theorem C0 (j : ℕ) (h1 : 430765 ≤ j) (h2 : j ≤ 431264) : Blo 1723062 (4 * j + 3) := by
  interval_cases j
  · exact B1723063
  · exact B1723067
  · exact B1723071
  · exact B1723075
  · exact B1723079
  · exact B1723083
  · exact B1723087
  · exact B1723091
  · exact B1723095
  · exact B1723099
  · exact B1723103
  · exact B1723107
  · exact B1723111
  · exact B1723115
  · exact B1723119
  · exact B1723123
  · exact B1723127
  · exact B1723131
  · exact B1723135
  · exact B1723139
  · exact B1723143
  · exact B1723147
  · exact B1723151
  · exact B1723155
  · exact B1723159
  · exact B1723163
  · exact B1723167
  · exact B1723171
  · exact B1723175
  · exact B1723179
  · exact B1723183
  · exact B1723187
  · exact B1723191
  · exact B1723195
  · exact B1723199
  · exact B1723203
  · exact B1723207
  · exact B1723211
  · exact B1723215
  · exact B1723219
  · exact B1723223
  · exact B1723227
  · exact B1723231
  · exact B1723235
  · exact B1723239
  · exact B1723243
  · exact B1723247
  · exact B1723251
  · exact B1723255
  · exact B1723259
  · exact B1723263
  · exact B1723267
  · exact B1723271
  · exact B1723275
  · exact B1723279
  · exact B1723283
  · exact B1723287
  · exact B1723291
  · exact B1723295
  · exact B1723299
  · exact B1723303
  · exact B1723307
  · exact B1723311
  · exact B1723315
  · exact B1723319
  · exact B1723323
  · exact B1723327
  · exact B1723331
  · exact B1723335
  · exact B1723339
  · exact B1723343
  · exact B1723347
  · exact B1723351
  · exact B1723355
  · exact B1723359
  · exact B1723363
  · exact B1723367
  · exact B1723371
  · exact B1723375
  · exact B1723379
  · exact B1723383
  · exact B1723387
  · exact B1723391
  · exact B1723395
  · exact B1723399
  · exact B1723403
  · exact B1723407
  · exact B1723411
  · exact B1723415
  · exact B1723419
  · exact B1723423
  · exact B1723427
  · exact B1723431
  · exact B1723435
  · exact B1723439
  · exact B1723443
  · exact B1723447
  · exact B1723451
  · exact B1723455
  · exact B1723459
  · exact B1723463
  · exact B1723467
  · exact B1723471
  · exact B1723475
  · exact B1723479
  · exact B1723483
  · exact B1723487
  · exact B1723491
  · exact B1723495
  · exact B1723499
  · exact B1723503
  · exact B1723507
  · exact B1723511
  · exact B1723515
  · exact B1723519
  · exact B1723523
  · exact B1723527
  · exact B1723531
  · exact B1723535
  · exact B1723539
  · exact B1723543
  · exact B1723547
  · exact B1723551
  · exact B1723555
  · exact B1723559
  · exact B1723563
  · exact B1723567
  · exact B1723571
  · exact B1723575
  · exact B1723579
  · exact B1723583
  · exact B1723587
  · exact B1723591
  · exact B1723595
  · exact B1723599
  · exact B1723603
  · exact B1723607
  · exact B1723611
  · exact B1723615
  · exact B1723619
  · exact B1723623
  · exact B1723627
  · exact B1723631
  · exact B1723635
  · exact B1723639
  · exact B1723643
  · exact B1723647
  · exact B1723651
  · exact B1723655
  · exact B1723659
  · exact B1723663
  · exact B1723667
  · exact B1723671
  · exact B1723675
  · exact B1723679
  · exact B1723683
  · exact B1723687
  · exact B1723691
  · exact B1723695
  · exact B1723699
  · exact B1723703
  · exact B1723707
  · exact B1723711
  · exact B1723715
  · exact B1723719
  · exact B1723723
  · exact B1723727
  · exact B1723731
  · exact B1723735
  · exact B1723739
  · exact B1723743
  · exact B1723747
  · exact B1723751
  · exact B1723755
  · exact B1723759
  · exact B1723763
  · exact B1723767
  · exact B1723771
  · exact B1723775
  · exact B1723779
  · exact B1723783
  · exact B1723787
  · exact B1723791
  · exact B1723795
  · exact B1723799
  · exact B1723803
  · exact B1723807
  · exact B1723811
  · exact B1723815
  · exact B1723819
  · exact B1723823
  · exact B1723827
  · exact B1723831
  · exact B1723835
  · exact B1723839
  · exact B1723843
  · exact B1723847
  · exact B1723851
  · exact B1723855
  · exact B1723859
  · exact B1723863
  · exact B1723867
  · exact B1723871
  · exact B1723875
  · exact B1723879
  · exact B1723883
  · exact B1723887
  · exact B1723891
  · exact B1723895
  · exact B1723899
  · exact B1723903
  · exact B1723907
  · exact B1723911
  · exact B1723915
  · exact B1723919
  · exact B1723923
  · exact B1723927
  · exact B1723931
  · exact B1723935
  · exact B1723939
  · exact B1723943
  · exact B1723947
  · exact B1723951
  · exact B1723955
  · exact B1723959
  · exact B1723963
  · exact B1723967
  · exact B1723971
  · exact B1723975
  · exact B1723979
  · exact B1723983
  · exact B1723987
  · exact B1723991
  · exact B1723995
  · exact B1723999
  · exact B1724003
  · exact B1724007
  · exact B1724011
  · exact B1724015
  · exact B1724019
  · exact B1724023
  · exact B1724027
  · exact B1724031
  · exact B1724035
  · exact B1724039
  · exact B1724043
  · exact B1724047
  · exact B1724051
  · exact B1724055
  · exact B1724059
  · exact B1724063
  · exact B1724067
  · exact B1724071
  · exact B1724075
  · exact B1724079
  · exact B1724083
  · exact B1724087
  · exact B1724091
  · exact B1724095
  · exact B1724099
  · exact B1724103
  · exact B1724107
  · exact B1724111
  · exact B1724115
  · exact B1724119
  · exact B1724123
  · exact B1724127
  · exact B1724131
  · exact B1724135
  · exact B1724139
  · exact B1724143
  · exact B1724147
  · exact B1724151
  · exact B1724155
  · exact B1724159
  · exact B1724163
  · exact B1724167
  · exact B1724171
  · exact B1724175
  · exact B1724179
  · exact B1724183
  · exact B1724187
  · exact B1724191
  · exact B1724195
  · exact B1724199
  · exact B1724203
  · exact B1724207
  · exact B1724211
  · exact B1724215
  · exact B1724219
  · exact B1724223
  · exact B1724227
  · exact B1724231
  · exact B1724235
  · exact B1724239
  · exact B1724243
  · exact B1724247
  · exact B1724251
  · exact B1724255
  · exact B1724259
  · exact B1724263
  · exact B1724267
  · exact B1724271
  · exact B1724275
  · exact B1724279
  · exact B1724283
  · exact B1724287
  · exact B1724291
  · exact B1724295
  · exact B1724299
  · exact B1724303
  · exact B1724307
  · exact B1724311
  · exact B1724315
  · exact B1724319
  · exact B1724323
  · exact B1724327
  · exact B1724331
  · exact B1724335
  · exact B1724339
  · exact B1724343
  · exact B1724347
  · exact B1724351
  · exact B1724355
  · exact B1724359
  · exact B1724363
  · exact B1724367
  · exact B1724371
  · exact B1724375
  · exact B1724379
  · exact B1724383
  · exact B1724387
  · exact B1724391
  · exact B1724395
  · exact B1724399
  · exact B1724403
  · exact B1724407
  · exact B1724411
  · exact B1724415
  · exact B1724419
  · exact B1724423
  · exact B1724427
  · exact B1724431
  · exact B1724435
  · exact B1724439
  · exact B1724443
  · exact B1724447
  · exact B1724451
  · exact B1724455
  · exact B1724459
  · exact B1724463
  · exact B1724467
  · exact B1724471
  · exact B1724475
  · exact B1724479
  · exact B1724483
  · exact B1724487
  · exact B1724491
  · exact B1724495
  · exact B1724499
  · exact B1724503
  · exact B1724507
  · exact B1724511
  · exact B1724515
  · exact B1724519
  · exact B1724523
  · exact B1724527
  · exact B1724531
  · exact B1724535
  · exact B1724539
  · exact B1724543
  · exact B1724547
  · exact B1724551
  · exact B1724555
  · exact B1724559
  · exact B1724563
  · exact B1724567
  · exact B1724571
  · exact B1724575
  · exact B1724579
  · exact B1724583
  · exact B1724587
  · exact B1724591
  · exact B1724595
  · exact B1724599
  · exact B1724603
  · exact B1724607
  · exact B1724611
  · exact B1724615
  · exact B1724619
  · exact B1724623
  · exact B1724627
  · exact B1724631
  · exact B1724635
  · exact B1724639
  · exact B1724643
  · exact B1724647
  · exact B1724651
  · exact B1724655
  · exact B1724659
  · exact B1724663
  · exact B1724667
  · exact B1724671
  · exact B1724675
  · exact B1724679
  · exact B1724683
  · exact B1724687
  · exact B1724691
  · exact B1724695
  · exact B1724699
  · exact B1724703
  · exact B1724707
  · exact B1724711
  · exact B1724715
  · exact B1724719
  · exact B1724723
  · exact B1724727
  · exact B1724731
  · exact B1724735
  · exact B1724739
  · exact B1724743
  · exact B1724747
  · exact B1724751
  · exact B1724755
  · exact B1724759
  · exact B1724763
  · exact B1724767
  · exact B1724771
  · exact B1724775
  · exact B1724779
  · exact B1724783
  · exact B1724787
  · exact B1724791
  · exact B1724795
  · exact B1724799
  · exact B1724803
  · exact B1724807
  · exact B1724811
  · exact B1724815
  · exact B1724819
  · exact B1724823
  · exact B1724827
  · exact B1724831
  · exact B1724835
  · exact B1724839
  · exact B1724843
  · exact B1724847
  · exact B1724851
  · exact B1724855
  · exact B1724859
  · exact B1724863
  · exact B1724867
  · exact B1724871
  · exact B1724875
  · exact B1724879
  · exact B1724883
  · exact B1724887
  · exact B1724891
  · exact B1724895
  · exact B1724899
  · exact B1724903
  · exact B1724907
  · exact B1724911
  · exact B1724915
  · exact B1724919
  · exact B1724923
  · exact B1724927
  · exact B1724931
  · exact B1724935
  · exact B1724939
  · exact B1724943
  · exact B1724947
  · exact B1724951
  · exact B1724955
  · exact B1724959
  · exact B1724963
  · exact B1724967
  · exact B1724971
  · exact B1724975
  · exact B1724979
  · exact B1724983
  · exact B1724987
  · exact B1724991
  · exact B1724995
  · exact B1724999
  · exact B1725003
  · exact B1725007
  · exact B1725011
  · exact B1725015
  · exact B1725019
  · exact B1725023
  · exact B1725027
  · exact B1725031
  · exact B1725035
  · exact B1725039
  · exact B1725043
  · exact B1725047
  · exact B1725051
  · exact B1725055
  · exact B1725059

theorem solution (m : ℕ) (hlo : 1723062 ≤ m) (hhi : m ≤ 1725062) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 430765 ≤ j := by omega
    have hj2 : j ≤ 431264 := by omega
    have hb : Blo 1723062 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
