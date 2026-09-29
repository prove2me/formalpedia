-- Prove2me | solution 1 for syracuse_descends_range_1590994_1592994
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:08:53.891152+00:00
-- url     : https://prove2.me/submissions/dee0100e-ac9c-41bc-b7d6-70b31873e642

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


theorem B4030469 : Blo 1590994 4030469 := bbase (se 4 (by rfl) ⟨377856, by rfl⟩ : syracuseStep 4030469 = 755713) (by norm_num)
theorem B3227701 : Blo 1590994 3227701 := bbase (se 5 (by rfl) ⟨151298, by rfl⟩ : syracuseStep 3227701 = 302597) (by norm_num)
theorem B6045749 : Blo 1590994 6045749 := bbase (se 5 (by rfl) ⟨283394, by rfl⟩ : syracuseStep 6045749 = 566789) (by norm_num)
theorem B3579965 : Blo 1590994 3579965 := bbase (se 3 (by rfl) ⟨671243, by rfl⟩ : syracuseStep 3579965 = 1342487) (by norm_num)
theorem B2687053 : Blo 1590994 2687053 := bbase (se 3 (by rfl) ⟨503822, by rfl⟩ : syracuseStep 2687053 = 1007645) (by norm_num)
theorem B2867309 : Blo 1590994 2867309 := bbase (se 3 (by rfl) ⟨537620, by rfl⟩ : syracuseStep 2867309 = 1075241) (by norm_num)
theorem B1966189 : Blo 1590994 1966189 := bbase (se 3 (by rfl) ⟨368660, by rfl⟩ : syracuseStep 1966189 = 737321) (by norm_num)
theorem B15294581 : Blo 1590994 15294581 := bbase (se 5 (by rfl) ⟨716933, by rfl⟩ : syracuseStep 15294581 = 1433867) (by norm_num)
theorem B3580037 : Blo 1590994 3580037 := bbase (se 4 (by rfl) ⟨335628, by rfl⟩ : syracuseStep 3580037 = 671257) (by norm_num)
theorem B2015381 : Blo 1590994 2015381 := bbase (se 6 (by rfl) ⟨47235, by rfl⟩ : syracuseStep 2015381 = 94471) (by norm_num)
theorem B2687141 : Blo 1590994 2687141 := bbase (se 4 (by rfl) ⟨251919, by rfl⟩ : syracuseStep 2687141 = 503839) (by norm_num)
theorem B5374133 : Blo 1590994 5374133 := bbase (se 5 (by rfl) ⟨251912, by rfl⟩ : syracuseStep 5374133 = 503825) (by norm_num)
theorem B4030661 : Blo 1590994 4030661 := bbase (se 4 (by rfl) ⟨377874, by rfl⟩ : syracuseStep 4030661 = 755749) (by norm_num)
theorem B3580109 : Blo 1590994 3580109 := bbase (se 3 (by rfl) ⟨671270, by rfl⟩ : syracuseStep 3580109 = 1342541) (by norm_num)
theorem B2015437 : Blo 1590994 2015437 := bbase (se 3 (by rfl) ⟨377894, by rfl⟩ : syracuseStep 2015437 = 755789) (by norm_num)
theorem B10895573 : Blo 1590994 10895573 := bbase (se 7 (by rfl) ⟨127682, by rfl⟩ : syracuseStep 10895573 = 255365) (by norm_num)
theorem B6799589 : Blo 1590994 6799589 := bbase (se 4 (by rfl) ⟨637461, by rfl⟩ : syracuseStep 6799589 = 1274923) (by norm_num)
theorem B3580181 : Blo 1590994 3580181 := bbase (se 6 (by rfl) ⟨83910, by rfl⟩ : syracuseStep 3580181 = 167821) (by norm_num)
theorem B4301093 : Blo 1590994 4301093 := bbase (se 4 (by rfl) ⟨403227, by rfl⟩ : syracuseStep 4301093 = 806455) (by norm_num)
theorem B2687269 : Blo 1590994 2687269 := bbase (se 4 (by rfl) ⟨251931, by rfl⟩ : syracuseStep 2687269 = 503863) (by norm_num)
theorem B2015533 : Blo 1590994 2015533 := bbase (se 3 (by rfl) ⟨377912, by rfl⟩ : syracuseStep 2015533 = 755825) (by norm_num)
theorem B3580253 : Blo 1590994 3580253 := bbase (se 3 (by rfl) ⟨671297, by rfl⟩ : syracuseStep 3580253 = 1342595) (by norm_num)
theorem B2687357 : Blo 1590994 2687357 := bbase (se 3 (by rfl) ⟨503879, by rfl⟩ : syracuseStep 2687357 = 1007759) (by norm_num)
theorem B3580325 : Blo 1590994 3580325 := bbase (se 4 (by rfl) ⟨335655, by rfl⟩ : syracuseStep 3580325 = 671311) (by norm_num)
theorem B2015705 : Blo 1590994 2015705 := bbase (se 2 (by rfl) ⟨755889, by rfl⟩ : syracuseStep 2015705 = 1511779) (by norm_num)
theorem B3580397 : Blo 1590994 3580397 := bbase (se 3 (by rfl) ⟨671324, by rfl⟩ : syracuseStep 3580397 = 1342649) (by norm_num)
theorem B2687485 : Blo 1590994 2687485 := bbase (se 3 (by rfl) ⟨503903, by rfl⟩ : syracuseStep 2687485 = 1007807) (by norm_num)
theorem B2015761 : Blo 1590994 2015761 := bbase (se 2 (by rfl) ⟨755910, by rfl⟩ : syracuseStep 2015761 = 1511821) (by norm_num)
theorem B4031005 : Blo 1590994 4031005 := bbase (se 3 (by rfl) ⟨755813, by rfl⟩ : syracuseStep 4031005 = 1511627) (by norm_num)
theorem B4530725 : Blo 1590994 4530725 := bbase (se 4 (by rfl) ⟨424755, by rfl⟩ : syracuseStep 4530725 = 849511) (by norm_num)
theorem B3580469 : Blo 1590994 3580469 := bbase (se 5 (by rfl) ⟨167834, by rfl⟩ : syracuseStep 3580469 = 335669) (by norm_num)
theorem B2761277 : Blo 1590994 2761277 := bbase (se 3 (by rfl) ⟨517739, by rfl⟩ : syracuseStep 2761277 = 1035479) (by norm_num)
theorem B2687573 : Blo 1590994 2687573 := bbase (se 8 (by rfl) ⟨15747, by rfl⟩ : syracuseStep 2687573 = 31495) (by norm_num)
theorem B5374565 : Blo 1590994 5374565 := bbase (se 4 (by rfl) ⟨503865, by rfl⟩ : syracuseStep 5374565 = 1007731) (by norm_num)
theorem B2015857 : Blo 1590994 2015857 := bbase (se 2 (by rfl) ⟨755946, by rfl⟩ : syracuseStep 2015857 = 1511893) (by norm_num)
theorem B3580541 : Blo 1590994 3580541 := bbase (se 3 (by rfl) ⟨671351, by rfl⟩ : syracuseStep 3580541 = 1342703) (by norm_num)
theorem B4031117 : Blo 1590994 4031117 := bbase (se 3 (by rfl) ⟨755834, by rfl⟩ : syracuseStep 4031117 = 1511669) (by norm_num)
theorem B8061605 : Blo 1590994 8061605 := bbase (se 4 (by rfl) ⟨755775, by rfl⟩ : syracuseStep 8061605 = 1511551) (by norm_num)
theorem B3580613 : Blo 1590994 3580613 := bbase (se 4 (by rfl) ⟨335682, by rfl⟩ : syracuseStep 3580613 = 671365) (by norm_num)
theorem B4301525 : Blo 1590994 4301525 := bbase (se 7 (by rfl) ⟨50408, by rfl⟩ : syracuseStep 4301525 = 100817) (by norm_num)
theorem B2687701 : Blo 1590994 2687701 := bbase (se 7 (by rfl) ⟨31496, by rfl⟩ : syracuseStep 2687701 = 62993) (by norm_num)
theorem B3023581 : Blo 1590994 3023581 := bbase (se 3 (by rfl) ⟨566921, by rfl⟩ : syracuseStep 3023581 = 1133843) (by norm_num)
theorem B4530917 : Blo 1590994 4530917 := bbase (se 4 (by rfl) ⟨424773, by rfl⟩ : syracuseStep 4530917 = 849547) (by norm_num)
theorem B3982061 : Blo 1590994 3982061 := bbase (se 3 (by rfl) ⟨746636, by rfl⟩ : syracuseStep 3982061 = 1493273) (by norm_num)
theorem B1614593 : Blo 1590994 1614593 := bbase (se 2 (by rfl) ⟨605472, by rfl⟩ : syracuseStep 1614593 = 1210945) (by norm_num)
theorem B3580685 : Blo 1590994 3580685 := bbase (se 3 (by rfl) ⟨671378, by rfl⟩ : syracuseStep 3580685 = 1342757) (by norm_num)
theorem B2016029 : Blo 1590994 2016029 := bbase (se 3 (by rfl) ⟨378005, by rfl⟩ : syracuseStep 2016029 = 756011) (by norm_num)
theorem B2687789 : Blo 1590994 2687789 := bbase (se 3 (by rfl) ⟨503960, by rfl⟩ : syracuseStep 2687789 = 1007921) (by norm_num)
theorem B2868029 : Blo 1590994 2868029 := bbase (se 3 (by rfl) ⟨537755, by rfl⟩ : syracuseStep 2868029 = 1075511) (by norm_num)
theorem B6128453 : Blo 1590994 6128453 := bbase (se 4 (by rfl) ⟨574542, by rfl⟩ : syracuseStep 6128453 = 1149085) (by norm_num)
theorem B3269453 : Blo 1590994 3269453 := bbase (se 3 (by rfl) ⟨613022, by rfl⟩ : syracuseStep 3269453 = 1226045) (by norm_num)
theorem B4031309 : Blo 1590994 4031309 := bbase (se 3 (by rfl) ⟨755870, by rfl⟩ : syracuseStep 4031309 = 1511741) (by norm_num)
theorem B3580757 : Blo 1590994 3580757 := bbase (se 9 (by rfl) ⟨10490, by rfl⟩ : syracuseStep 3580757 = 20981) (by norm_num)
theorem B2016085 : Blo 1590994 2016085 := bbase (se 9 (by rfl) ⟨5906, by rfl⟩ : syracuseStep 2016085 = 11813) (by norm_num)
theorem B3023725 : Blo 1590994 3023725 := bbase (se 3 (by rfl) ⟨566948, by rfl⟩ : syracuseStep 3023725 = 1133897) (by norm_num)
theorem B3580829 : Blo 1590994 3580829 := bbase (se 3 (by rfl) ⟨671405, by rfl⟩ : syracuseStep 3580829 = 1342811) (by norm_num)
theorem B2687917 : Blo 1590994 2687917 := bbase (se 3 (by rfl) ⟨503984, by rfl⟩ : syracuseStep 2687917 = 1007969) (by norm_num)
theorem B3580901 : Blo 1590994 3580901 := bbase (se 4 (by rfl) ⟨335709, by rfl⟩ : syracuseStep 3580901 = 671419) (by norm_num)
theorem B2688005 : Blo 1590994 2688005 := bbase (se 4 (by rfl) ⟨252000, by rfl⟩ : syracuseStep 2688005 = 504001) (by norm_num)
theorem B3400717 : Blo 1590994 3400717 := bbase (se 3 (by rfl) ⟨637634, by rfl⟩ : syracuseStep 3400717 = 1275269) (by norm_num)
theorem B3023885 : Blo 1590994 3023885 := bbase (se 3 (by rfl) ⟨566978, by rfl⟩ : syracuseStep 3023885 = 1133957) (by norm_num)
theorem B5374997 : Blo 1590994 5374997 := bbase (se 6 (by rfl) ⟨125976, by rfl⟩ : syracuseStep 5374997 = 251953) (by norm_num)
theorem B3580973 : Blo 1590994 3580973 := bbase (se 3 (by rfl) ⟨671432, by rfl⟩ : syracuseStep 3580973 = 1342865) (by norm_num)
theorem B3581045 : Blo 1590994 3581045 := bbase (se 5 (by rfl) ⟨167861, by rfl⟩ : syracuseStep 3581045 = 335723) (by norm_num)
theorem B2688133 : Blo 1590994 2688133 := bbase (se 4 (by rfl) ⟨252012, by rfl⟩ : syracuseStep 2688133 = 504025) (by norm_num)
theorem B3024029 : Blo 1590994 3024029 := bbase (se 3 (by rfl) ⟨567005, by rfl⟩ : syracuseStep 3024029 = 1134011) (by norm_num)
theorem B4031653 : Blo 1590994 4031653 := bbase (se 4 (by rfl) ⟨377967, by rfl⟩ : syracuseStep 4031653 = 755935) (by norm_num)
theorem B3581117 : Blo 1590994 3581117 := bbase (se 3 (by rfl) ⟨671459, by rfl⟩ : syracuseStep 3581117 = 1342919) (by norm_num)
theorem B6046933 : Blo 1590994 6046933 := bbase (se 7 (by rfl) ⟨70862, by rfl⟩ : syracuseStep 6046933 = 141725) (by norm_num)
theorem B4359413 : Blo 1590994 4359413 := bbase (se 5 (by rfl) ⟨204347, by rfl⟩ : syracuseStep 4359413 = 408695) (by norm_num)
theorem B3581189 : Blo 1590994 3581189 := bbase (se 4 (by rfl) ⟨335736, by rfl⟩ : syracuseStep 3581189 = 671473) (by norm_num)
theorem B4031765 : Blo 1590994 4031765 := bbase (se 6 (by rfl) ⟨94494, by rfl⟩ : syracuseStep 4031765 = 188989) (by norm_num)
theorem B3065149 : Blo 1590994 3065149 := bbase (se 3 (by rfl) ⟨574715, by rfl⟩ : syracuseStep 3065149 = 1149431) (by norm_num)
theorem B3581261 : Blo 1590994 3581261 := bbase (se 3 (by rfl) ⟨671486, by rfl⟩ : syracuseStep 3581261 = 1342973) (by norm_num)
theorem B3581333 : Blo 1590994 3581333 := bbase (se 6 (by rfl) ⟨83937, by rfl⟩ : syracuseStep 3581333 = 167875) (by norm_num)
theorem B5375429 : Blo 1590994 5375429 := bbase (se 4 (by rfl) ⟨503946, by rfl⟩ : syracuseStep 5375429 = 1007893) (by norm_num)
theorem B4031957 : Blo 1590994 4031957 := bbase (se 7 (by rfl) ⟨47249, by rfl⟩ : syracuseStep 4031957 = 94499) (by norm_num)
theorem B3581405 : Blo 1590994 3581405 := bbase (se 3 (by rfl) ⟨671513, by rfl⟩ : syracuseStep 3581405 = 1343027) (by norm_num)
theorem B4302325 : Blo 1590994 4302325 := bbase (se 5 (by rfl) ⟨201671, by rfl⟩ : syracuseStep 4302325 = 403343) (by norm_num)
theorem B6047237 : Blo 1590994 6047237 := bbase (se 4 (by rfl) ⟨566928, by rfl⟩ : syracuseStep 6047237 = 1133857) (by norm_num)
theorem B3581477 : Blo 1590994 3581477 := bbase (se 4 (by rfl) ⟨335763, by rfl⟩ : syracuseStep 3581477 = 671527) (by norm_num)
theorem B4597285 : Blo 1590994 4597285 := bbase (se 4 (by rfl) ⟨430995, by rfl⟩ : syracuseStep 4597285 = 861991) (by norm_num)
theorem B4843061 : Blo 1590994 4843061 := bbase (se 5 (by rfl) ⟨227018, by rfl⟩ : syracuseStep 4843061 = 454037) (by norm_num)
theorem B3581549 : Blo 1590994 3581549 := bbase (se 3 (by rfl) ⟨671540, by rfl⟩ : syracuseStep 3581549 = 1343081) (by norm_num)
theorem B7652981 : Blo 1590994 7652981 := bbase (se 5 (by rfl) ⟨358733, by rfl⟩ : syracuseStep 7652981 = 717467) (by norm_num)
theorem B2393765 : Blo 1590994 2393765 := bbase (se 4 (by rfl) ⟨224415, by rfl⟩ : syracuseStep 2393765 = 448831) (by norm_num)
theorem B3581621 : Blo 1590994 3581621 := bbase (se 5 (by rfl) ⟨167888, by rfl⟩ : syracuseStep 3581621 = 335777) (by norm_num)
theorem B4531909 : Blo 1590994 4531909 := bbase (se 4 (by rfl) ⟨424866, by rfl⟩ : syracuseStep 4531909 = 849733) (by norm_num)
theorem B3581693 : Blo 1590994 3581693 := bbase (se 3 (by rfl) ⟨671567, by rfl⟩ : syracuseStep 3581693 = 1343135) (by norm_num)
theorem B3229445 : Blo 1590994 3229445 := bbase (se 4 (by rfl) ⟨302760, by rfl⟩ : syracuseStep 3229445 = 605521) (by norm_num)
theorem B3581765 : Blo 1590994 3581765 := bbase (se 4 (by rfl) ⟨335790, by rfl⟩ : syracuseStep 3581765 = 671581) (by norm_num)
theorem B5375861 : Blo 1590994 5375861 := bbase (se 5 (by rfl) ⟨251993, by rfl⟩ : syracuseStep 5375861 = 503987) (by norm_num)
theorem B3401605 : Blo 1590994 3401605 := bbase (se 4 (by rfl) ⟨318900, by rfl⟩ : syracuseStep 3401605 = 637801) (by norm_num)
theorem B3581837 : Blo 1590994 3581837 := bbase (se 3 (by rfl) ⟨671594, by rfl⟩ : syracuseStep 3581837 = 1343189) (by norm_num)
theorem B8062901 : Blo 1590994 8062901 := bbase (se 5 (by rfl) ⟨377948, by rfl⟩ : syracuseStep 8062901 = 755897) (by norm_num)
theorem B2549693 : Blo 1590994 2549693 := bbase (se 3 (by rfl) ⟨478067, by rfl⟩ : syracuseStep 2549693 = 956135) (by norm_num)
theorem B3581909 : Blo 1590994 3581909 := bbase (se 7 (by rfl) ⟨41975, by rfl⟩ : syracuseStep 3581909 = 83951) (by norm_num)
theorem B3581981 : Blo 1590994 3581981 := bbase (se 3 (by rfl) ⟨671621, by rfl⟩ : syracuseStep 3581981 = 1343243) (by norm_num)
theorem B5171285 : Blo 1590994 5171285 := bbase (se 8 (by rfl) ⟨30300, by rfl⟩ : syracuseStep 5171285 = 60601) (by norm_num)
theorem B3582053 : Blo 1590994 3582053 := bbase (se 4 (by rfl) ⟨335817, by rfl⟩ : syracuseStep 3582053 = 671635) (by norm_num)
theorem B6457477 : Blo 1590994 6457477 := bbase (se 4 (by rfl) ⟨605388, by rfl⟩ : syracuseStep 6457477 = 1210777) (by norm_num)
theorem B2549917 : Blo 1590994 2549917 := bbase (se 3 (by rfl) ⟨478109, by rfl⟩ : syracuseStep 2549917 = 956219) (by norm_num)
theorem B3582125 : Blo 1590994 3582125 := bbase (se 3 (by rfl) ⟨671648, by rfl⟩ : syracuseStep 3582125 = 1343297) (by norm_num)
theorem B3582197 : Blo 1590994 3582197 := bbase (se 5 (by rfl) ⟨167915, by rfl⟩ : syracuseStep 3582197 = 335831) (by norm_num)
theorem B5376293 : Blo 1590994 5376293 := bbase (se 4 (by rfl) ⟨504027, by rfl⟩ : syracuseStep 5376293 = 1008055) (by norm_num)
theorem B3582269 : Blo 1590994 3582269 := bbase (se 3 (by rfl) ⟨671675, by rfl⟩ : syracuseStep 3582269 = 1343351) (by norm_num)
theorem B3148093 : Blo 1590994 3148093 := bbase (se 3 (by rfl) ⟨590267, by rfl⟩ : syracuseStep 3148093 = 1180535) (by norm_num)
theorem B8055125 : Blo 1590994 8055125 := bbase (se 10 (by rfl) ⟨11799, by rfl⟩ : syracuseStep 8055125 = 23599) (by norm_num)
theorem B3402101 : Blo 1590994 3402101 := bbase (se 5 (by rfl) ⟨159473, by rfl⟩ : syracuseStep 3402101 = 318947) (by norm_num)
theorem B3582341 : Blo 1590994 3582341 := bbase (se 4 (by rfl) ⟨335844, by rfl⟩ : syracuseStep 3582341 = 671689) (by norm_num)
theorem B9062837 : Blo 1590994 9062837 := bbase (se 5 (by rfl) ⟨424820, by rfl⟩ : syracuseStep 9062837 = 849641) (by norm_num)
theorem B2722237 : Blo 1590994 2722237 := bbase (se 3 (by rfl) ⟨510419, by rfl⟩ : syracuseStep 2722237 = 1020839) (by norm_num)
theorem B3582413 : Blo 1590994 3582413 := bbase (se 3 (by rfl) ⟨671702, by rfl⟩ : syracuseStep 3582413 = 1343405) (by norm_num)
theorem B3631565 : Blo 1590994 3631565 := bbase (se 3 (by rfl) ⟨680918, by rfl⟩ : syracuseStep 3631565 = 1361837) (by norm_num)
theorem B3582485 : Blo 1590994 3582485 := bbase (se 6 (by rfl) ⟨83964, by rfl⟩ : syracuseStep 3582485 = 167929) (by norm_num)
theorem B2869789 : Blo 1590994 2869789 := bbase (se 3 (by rfl) ⟨538085, by rfl⟩ : syracuseStep 2869789 = 1076171) (by norm_num)
theorem B2722349 : Blo 1590994 2722349 := bbase (se 3 (by rfl) ⟨510440, by rfl⟩ : syracuseStep 2722349 = 1020881) (by norm_num)
theorem B2386493 : Blo 1590994 2386493 := bbase (se 3 (by rfl) ⟨447467, by rfl⟩ : syracuseStep 2386493 = 894935) (by norm_num)
theorem B2386517 : Blo 1590994 2386517 := bbase (se 8 (by rfl) ⟨13983, by rfl⟩ : syracuseStep 2386517 = 27967) (by norm_num)
theorem B1911385 : Blo 1590994 1911385 := bbase (se 2 (by rfl) ⟨716769, by rfl⟩ : syracuseStep 1911385 = 1433539) (by norm_num)
theorem B3582557 : Blo 1590994 3582557 := bbase (se 3 (by rfl) ⟨671729, by rfl⟩ : syracuseStep 3582557 = 1343459) (by norm_num)
theorem B2386541 : Blo 1590994 2386541 := bbase (se 3 (by rfl) ⟨447476, by rfl⟩ : syracuseStep 2386541 = 894953) (by norm_num)
theorem B2386565 : Blo 1590994 2386565 := bbase (se 4 (by rfl) ⟨223740, by rfl⟩ : syracuseStep 2386565 = 447481) (by norm_num)
theorem B2386589 : Blo 1590994 2386589 := bbase (se 3 (by rfl) ⟨447485, by rfl⟩ : syracuseStep 2386589 = 894971) (by norm_num)
theorem B3582629 : Blo 1590994 3582629 := bbase (se 4 (by rfl) ⟨335871, by rfl⟩ : syracuseStep 3582629 = 671743) (by norm_num)
theorem B2869925 : Blo 1590994 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B2386613 : Blo 1590994 2386613 := bbase (se 5 (by rfl) ⟨111872, by rfl⟩ : syracuseStep 2386613 = 223745) (by norm_num)
theorem B2386637 : Blo 1590994 2386637 := bbase (se 3 (by rfl) ⟨447494, by rfl⟩ : syracuseStep 2386637 = 894989) (by norm_num)
theorem B2386661 : Blo 1590994 2386661 := bbase (se 4 (by rfl) ⟨223749, by rfl⟩ : syracuseStep 2386661 = 447499) (by norm_num)
theorem B3582701 : Blo 1590994 3582701 := bbase (se 3 (by rfl) ⟨671756, by rfl⟩ : syracuseStep 3582701 = 1343513) (by norm_num)
theorem B2870005 : Blo 1590994 2870005 := bbase (se 5 (by rfl) ⟨134531, by rfl⟩ : syracuseStep 2870005 = 269063) (by norm_num)
theorem B2386685 : Blo 1590994 2386685 := bbase (se 3 (by rfl) ⟨447503, by rfl⟩ : syracuseStep 2386685 = 895007) (by norm_num)
theorem B2386709 : Blo 1590994 2386709 := bbase (se 6 (by rfl) ⟨55938, by rfl⟩ : syracuseStep 2386709 = 111877) (by norm_num)
theorem B6540053 : Blo 1590994 6540053 := bbase (se 6 (by rfl) ⟨153282, by rfl⟩ : syracuseStep 6540053 = 306565) (by norm_num)
theorem B4533013 : Blo 1590994 4533013 := bbase (se 6 (by rfl) ⟨106242, by rfl⟩ : syracuseStep 4533013 = 212485) (by norm_num)
theorem B1723177 : Blo 1590994 1723177 := bbase (se 2 (by rfl) ⟨646191, by rfl⟩ : syracuseStep 1723177 = 1292383) (by norm_num)
theorem B2386733 : Blo 1590994 2386733 := bbase (se 3 (by rfl) ⟨447512, by rfl⟩ : syracuseStep 2386733 = 895025) (by norm_num)
theorem B3582773 : Blo 1590994 3582773 := bbase (se 5 (by rfl) ⟨167942, by rfl⟩ : syracuseStep 3582773 = 335885) (by norm_num)
theorem B2386757 : Blo 1590994 2386757 := bbase (se 4 (by rfl) ⟨223758, by rfl⟩ : syracuseStep 2386757 = 447517) (by norm_num)
theorem B2386781 : Blo 1590994 2386781 := bbase (se 3 (by rfl) ⟨447521, by rfl⟩ : syracuseStep 2386781 = 895043) (by norm_num)
theorem B2386805 : Blo 1590994 2386805 := bbase (se 5 (by rfl) ⟨111881, by rfl⟩ : syracuseStep 2386805 = 223763) (by norm_num)
theorem B3582845 : Blo 1590994 3582845 := bbase (se 3 (by rfl) ⟨671783, by rfl⟩ : syracuseStep 3582845 = 1343567) (by norm_num)
theorem B2386829 : Blo 1590994 2386829 := bbase (se 3 (by rfl) ⟨447530, by rfl⟩ : syracuseStep 2386829 = 895061) (by norm_num)
theorem B2386853 : Blo 1590994 2386853 := bbase (se 4 (by rfl) ⟨223767, by rfl⟩ : syracuseStep 2386853 = 447535) (by norm_num)
theorem B2386877 : Blo 1590994 2386877 := bbase (se 3 (by rfl) ⟨447539, by rfl⟩ : syracuseStep 2386877 = 895079) (by norm_num)
theorem B3582917 : Blo 1590994 3582917 := bbase (se 4 (by rfl) ⟨335898, by rfl⟩ : syracuseStep 3582917 = 671797) (by norm_num)
theorem B2386901 : Blo 1590994 2386901 := bbase (se 7 (by rfl) ⟨27971, by rfl⟩ : syracuseStep 2386901 = 55943) (by norm_num)
theorem B2419669 : Blo 1590994 2419669 := bbase (se 7 (by rfl) ⟨28355, by rfl⟩ : syracuseStep 2419669 = 56711) (by norm_num)
theorem B2386925 : Blo 1590994 2386925 := bbase (se 3 (by rfl) ⟨447548, by rfl⟩ : syracuseStep 2386925 = 895097) (by norm_num)
theorem B2386949 : Blo 1590994 2386949 := bbase (se 4 (by rfl) ⟨223776, by rfl⟩ : syracuseStep 2386949 = 447553) (by norm_num)
theorem B3582989 : Blo 1590994 3582989 := bbase (se 3 (by rfl) ⟨671810, by rfl⟩ : syracuseStep 3582989 = 1343621) (by norm_num)
theorem B2386973 : Blo 1590994 2386973 := bbase (se 3 (by rfl) ⟨447557, by rfl⟩ : syracuseStep 2386973 = 895115) (by norm_num)
theorem B2386997 : Blo 1590994 2386997 := bbase (se 5 (by rfl) ⟨111890, by rfl⟩ : syracuseStep 2386997 = 223781) (by norm_num)
theorem B5098565 : Blo 1590994 5098565 := bbase (se 4 (by rfl) ⟨477990, by rfl⟩ : syracuseStep 5098565 = 955981) (by norm_num)
theorem B2387021 : Blo 1590994 2387021 := bbase (se 3 (by rfl) ⟨447566, by rfl⟩ : syracuseStep 2387021 = 895133) (by norm_num)
theorem B3583061 : Blo 1590994 3583061 := bbase (se 8 (by rfl) ⟨20994, by rfl⟩ : syracuseStep 3583061 = 41989) (by norm_num)
theorem B2387045 : Blo 1590994 2387045 := bbase (se 4 (by rfl) ⟨223785, by rfl⟩ : syracuseStep 2387045 = 447571) (by norm_num)
theorem B2387069 : Blo 1590994 2387069 := bbase (se 3 (by rfl) ⟨447575, by rfl⟩ : syracuseStep 2387069 = 895151) (by norm_num)
theorem B2387093 : Blo 1590994 2387093 := bbase (se 6 (by rfl) ⟨55947, by rfl⟩ : syracuseStep 2387093 = 111895) (by norm_num)
theorem B3583133 : Blo 1590994 3583133 := bbase (se 3 (by rfl) ⟨671837, by rfl⟩ : syracuseStep 3583133 = 1343675) (by norm_num)
theorem B5172389 : Blo 1590994 5172389 := bbase (se 4 (by rfl) ⟨484911, by rfl⟩ : syracuseStep 5172389 = 969823) (by norm_num)
theorem B2387117 : Blo 1590994 2387117 := bbase (se 3 (by rfl) ⟨447584, by rfl⟩ : syracuseStep 2387117 = 895169) (by norm_num)
theorem B2387141 : Blo 1590994 2387141 := bbase (se 4 (by rfl) ⟨223794, by rfl⟩ : syracuseStep 2387141 = 447589) (by norm_num)
theorem B8064197 : Blo 1590994 8064197 := bbase (se 4 (by rfl) ⟨756018, by rfl⟩ : syracuseStep 8064197 = 1512037) (by norm_num)
theorem B2387165 : Blo 1590994 2387165 := bbase (se 3 (by rfl) ⟨447593, by rfl⟩ : syracuseStep 2387165 = 895187) (by norm_num)
theorem B3583205 : Blo 1590994 3583205 := bbase (se 4 (by rfl) ⟨335925, by rfl⟩ : syracuseStep 3583205 = 671851) (by norm_num)
theorem B13593845 : Blo 1590994 13593845 := bbase (se 5 (by rfl) ⟨637211, by rfl⟩ : syracuseStep 13593845 = 1274423) (by norm_num)
theorem B2387189 : Blo 1590994 2387189 := bbase (se 5 (by rfl) ⟨111899, by rfl⟩ : syracuseStep 2387189 = 223799) (by norm_num)
theorem B2387213 : Blo 1590994 2387213 := bbase (se 3 (by rfl) ⟨447602, by rfl⟩ : syracuseStep 2387213 = 895205) (by norm_num)
theorem B20401429 : Blo 1590994 20401429 := bbase (se 6 (by rfl) ⟨478158, by rfl⟩ : syracuseStep 20401429 = 956317) (by norm_num)
theorem B2387237 : Blo 1590994 2387237 := bbase (se 4 (by rfl) ⟨223803, by rfl⟩ : syracuseStep 2387237 = 447607) (by norm_num)
theorem B3583277 : Blo 1590994 3583277 := bbase (se 3 (by rfl) ⟨671864, by rfl⟩ : syracuseStep 3583277 = 1343729) (by norm_num)
theorem B2387261 : Blo 1590994 2387261 := bbase (se 3 (by rfl) ⟨447611, by rfl⟩ : syracuseStep 2387261 = 895223) (by norm_num)
theorem B2387285 : Blo 1590994 2387285 := bbase (se 11 (by rfl) ⟨1748, by rfl⟩ : syracuseStep 2387285 = 3497) (by norm_num)
theorem B2387309 : Blo 1590994 2387309 := bbase (se 3 (by rfl) ⟨447620, by rfl⟩ : syracuseStep 2387309 = 895241) (by norm_num)
theorem B3583349 : Blo 1590994 3583349 := bbase (se 5 (by rfl) ⟨167969, by rfl⟩ : syracuseStep 3583349 = 335939) (by norm_num)
theorem B2387333 : Blo 1590994 2387333 := bbase (se 4 (by rfl) ⟨223812, by rfl⟩ : syracuseStep 2387333 = 447625) (by norm_num)
theorem B6991237 : Blo 1590994 6991237 := bbase (se 4 (by rfl) ⟨655428, by rfl⟩ : syracuseStep 6991237 = 1310857) (by norm_num)
theorem B2387357 : Blo 1590994 2387357 := bbase (se 3 (by rfl) ⟨447629, by rfl⟩ : syracuseStep 2387357 = 895259) (by norm_num)
theorem B2723237 : Blo 1590994 2723237 := bbase (se 4 (by rfl) ⟨255303, by rfl⟩ : syracuseStep 2723237 = 510607) (by norm_num)
theorem B2387381 : Blo 1590994 2387381 := bbase (se 5 (by rfl) ⟨111908, by rfl⟩ : syracuseStep 2387381 = 223817) (by norm_num)
theorem B3583421 : Blo 1590994 3583421 := bbase (se 3 (by rfl) ⟨671891, by rfl⟩ : syracuseStep 3583421 = 1343783) (by norm_num)
theorem B1699265 : Blo 1590994 1699265 := bbase (se 2 (by rfl) ⟨637224, by rfl⟩ : syracuseStep 1699265 = 1274449) (by norm_num)
theorem B2387405 : Blo 1590994 2387405 := bbase (se 3 (by rfl) ⟨447638, by rfl⟩ : syracuseStep 2387405 = 895277) (by norm_num)
theorem B2387429 : Blo 1590994 2387429 := bbase (se 4 (by rfl) ⟨223821, by rfl⟩ : syracuseStep 2387429 = 447643) (by norm_num)
theorem B2387453 : Blo 1590994 2387453 := bbase (se 3 (by rfl) ⟨447647, by rfl⟩ : syracuseStep 2387453 = 895295) (by norm_num)
theorem B3583493 : Blo 1590994 3583493 := bbase (se 4 (by rfl) ⟨335952, by rfl⟩ : syracuseStep 3583493 = 671905) (by norm_num)
theorem B2387477 : Blo 1590994 2387477 := bbase (se 6 (by rfl) ⟨55956, by rfl⟩ : syracuseStep 2387477 = 111913) (by norm_num)
theorem B2551333 : Blo 1590994 2551333 := bbase (se 4 (by rfl) ⟨239187, by rfl⟩ : syracuseStep 2551333 = 478375) (by norm_num)
theorem B2387501 : Blo 1590994 2387501 := bbase (se 3 (by rfl) ⟨447656, by rfl⟩ : syracuseStep 2387501 = 895313) (by norm_num)
theorem B2387525 : Blo 1590994 2387525 := bbase (se 4 (by rfl) ⟨223830, by rfl⟩ : syracuseStep 2387525 = 447661) (by norm_num)
theorem B3583565 : Blo 1590994 3583565 := bbase (se 3 (by rfl) ⟨671918, by rfl⟩ : syracuseStep 3583565 = 1343837) (by norm_num)
theorem B9064021 : Blo 1590994 9064021 := bbase (se 8 (by rfl) ⟨53109, by rfl⟩ : syracuseStep 9064021 = 106219) (by norm_num)
theorem B2387549 : Blo 1590994 2387549 := bbase (se 3 (by rfl) ⟨447665, by rfl⟩ : syracuseStep 2387549 = 895331) (by norm_num)
theorem B8056421 : Blo 1590994 8056421 := bbase (se 4 (by rfl) ⟨755289, by rfl⟩ : syracuseStep 8056421 = 1510579) (by norm_num)
theorem B2387573 : Blo 1590994 2387573 := bbase (se 5 (by rfl) ⟨111917, by rfl⟩ : syracuseStep 2387573 = 223835) (by norm_num)
theorem B2387597 : Blo 1590994 2387597 := bbase (se 3 (by rfl) ⟨447674, by rfl⟩ : syracuseStep 2387597 = 895349) (by norm_num)
theorem B3583637 : Blo 1590994 3583637 := bbase (se 6 (by rfl) ⟨83991, by rfl⟩ : syracuseStep 3583637 = 167983) (by norm_num)
theorem B2387621 : Blo 1590994 2387621 := bbase (se 4 (by rfl) ⟨223839, by rfl⟩ : syracuseStep 2387621 = 447679) (by norm_num)
theorem B5738165 : Blo 1590994 5738165 := bbase (se 5 (by rfl) ⟨268976, by rfl⟩ : syracuseStep 5738165 = 537953) (by norm_num)
theorem B2387645 : Blo 1590994 2387645 := bbase (se 3 (by rfl) ⟨447683, by rfl⟩ : syracuseStep 2387645 = 895367) (by norm_num)
theorem B1912529 : Blo 1590994 1912529 := bbase (se 2 (by rfl) ⟨717198, by rfl⟩ : syracuseStep 1912529 = 1434397) (by norm_num)
theorem B2387669 : Blo 1590994 2387669 := bbase (se 7 (by rfl) ⟨27980, by rfl⟩ : syracuseStep 2387669 = 55961) (by norm_num)
theorem B3583709 : Blo 1590994 3583709 := bbase (se 3 (by rfl) ⟨671945, by rfl⟩ : syracuseStep 3583709 = 1343891) (by norm_num)
theorem B2387693 : Blo 1590994 2387693 := bbase (se 3 (by rfl) ⟨447692, by rfl⟩ : syracuseStep 2387693 = 895385) (by norm_num)
theorem B1912577 : Blo 1590994 1912577 := bbase (se 2 (by rfl) ⟨717216, by rfl⟩ : syracuseStep 1912577 = 1434433) (by norm_num)
theorem B2387717 : Blo 1590994 2387717 := bbase (se 4 (by rfl) ⟨223848, by rfl⟩ : syracuseStep 2387717 = 447697) (by norm_num)
theorem B2387741 : Blo 1590994 2387741 := bbase (se 3 (by rfl) ⟨447701, by rfl⟩ : syracuseStep 2387741 = 895403) (by norm_num)
theorem B3583781 : Blo 1590994 3583781 := bbase (se 4 (by rfl) ⟨335979, by rfl⟩ : syracuseStep 3583781 = 671959) (by norm_num)
theorem B2551589 : Blo 1590994 2551589 := bbase (se 4 (by rfl) ⟨239211, by rfl⟩ : syracuseStep 2551589 = 478423) (by norm_num)
theorem B2387765 : Blo 1590994 2387765 := bbase (se 5 (by rfl) ⟨111926, by rfl⟩ : syracuseStep 2387765 = 223853) (by norm_num)
theorem B2420533 : Blo 1590994 2420533 := bbase (se 5 (by rfl) ⟨113462, by rfl⟩ : syracuseStep 2420533 = 226925) (by norm_num)
theorem B5738309 : Blo 1590994 5738309 := bbase (se 4 (by rfl) ⟨537966, by rfl⟩ : syracuseStep 5738309 = 1075933) (by norm_num)
theorem B2387789 : Blo 1590994 2387789 := bbase (se 3 (by rfl) ⟨447710, by rfl⟩ : syracuseStep 2387789 = 895421) (by norm_num)
theorem B1912673 : Blo 1590994 1912673 := bbase (se 2 (by rfl) ⟨717252, by rfl⟩ : syracuseStep 1912673 = 1434505) (by norm_num)
theorem B2387813 : Blo 1590994 2387813 := bbase (se 4 (by rfl) ⟨223857, by rfl⟩ : syracuseStep 2387813 = 447715) (by norm_num)
theorem B3583853 : Blo 1590994 3583853 := bbase (se 3 (by rfl) ⟨671972, by rfl⟩ : syracuseStep 3583853 = 1343945) (by norm_num)
theorem B2723701 : Blo 1590994 2723701 := bbase (se 5 (by rfl) ⟨127673, by rfl⟩ : syracuseStep 2723701 = 255347) (by norm_num)
theorem B1699709 : Blo 1590994 1699709 := bbase (se 3 (by rfl) ⟨318695, by rfl⟩ : syracuseStep 1699709 = 637391) (by norm_num)
theorem B2387837 : Blo 1590994 2387837 := bbase (se 3 (by rfl) ⟨447719, by rfl⟩ : syracuseStep 2387837 = 895439) (by norm_num)
theorem B2387861 : Blo 1590994 2387861 := bbase (se 6 (by rfl) ⟨55965, by rfl⟩ : syracuseStep 2387861 = 111931) (by norm_num)
theorem B2723749 : Blo 1590994 2723749 := bbase (se 4 (by rfl) ⟨255351, by rfl⟩ : syracuseStep 2723749 = 510703) (by norm_num)
theorem B2387885 : Blo 1590994 2387885 := bbase (se 3 (by rfl) ⟨447728, by rfl⟩ : syracuseStep 2387885 = 895457) (by norm_num)
theorem B3583925 : Blo 1590994 3583925 := bbase (se 5 (by rfl) ⟨167996, by rfl⟩ : syracuseStep 3583925 = 335993) (by norm_num)
theorem B2387909 : Blo 1590994 2387909 := bbase (se 4 (by rfl) ⟨223866, by rfl⟩ : syracuseStep 2387909 = 447733) (by norm_num)
theorem B1789897 : Blo 1590994 1789897 := bbase (se 2 (by rfl) ⟨671211, by rfl⟩ : syracuseStep 1789897 = 1342423) (by norm_num)
theorem B5369813 : Blo 1590994 5369813 := bbase (se 7 (by rfl) ⟨62927, by rfl⟩ : syracuseStep 5369813 = 125855) (by norm_num)
theorem B2387933 : Blo 1590994 2387933 := bbase (se 3 (by rfl) ⟨447737, by rfl⟩ : syracuseStep 2387933 = 895475) (by norm_num)
theorem B6041573 : Blo 1590994 6041573 := bbase (se 4 (by rfl) ⟨566397, by rfl⟩ : syracuseStep 6041573 = 1132795) (by norm_num)
theorem B1789933 : Blo 1590994 1789933 := bbase (se 3 (by rfl) ⟨335612, by rfl⟩ : syracuseStep 1789933 = 671225) (by norm_num)
theorem B2387957 : Blo 1590994 2387957 := bbase (se 5 (by rfl) ⟨111935, by rfl⟩ : syracuseStep 2387957 = 223871) (by norm_num)
theorem B3583997 : Blo 1590994 3583997 := bbase (se 3 (by rfl) ⟨671999, by rfl⟩ : syracuseStep 3583997 = 1343999) (by norm_num)
theorem B1912837 : Blo 1590994 1912837 := bbase (se 4 (by rfl) ⟨179328, by rfl⟩ : syracuseStep 1912837 = 358657) (by norm_num)
theorem B2387981 : Blo 1590994 2387981 := bbase (se 3 (by rfl) ⟨447746, by rfl⟩ : syracuseStep 2387981 = 895493) (by norm_num)
theorem B1789969 : Blo 1590994 1789969 := bbase (se 2 (by rfl) ⟨671238, by rfl⟩ : syracuseStep 1789969 = 1342477) (by norm_num)
theorem B2388005 : Blo 1590994 2388005 := bbase (se 4 (by rfl) ⟨223875, by rfl⟩ : syracuseStep 2388005 = 447751) (by norm_num)
theorem B1790005 : Blo 1590994 1790005 := bbase (se 5 (by rfl) ⟨83906, by rfl⟩ : syracuseStep 1790005 = 167813) (by norm_num)
theorem B2388029 : Blo 1590994 2388029 := bbase (se 3 (by rfl) ⟨447755, by rfl⟩ : syracuseStep 2388029 = 895511) (by norm_num)
theorem B3584069 : Blo 1590994 3584069 := bbase (se 4 (by rfl) ⟨336006, by rfl⟩ : syracuseStep 3584069 = 672013) (by norm_num)
theorem B2986069 : Blo 1590994 2986069 := bbase (se 8 (by rfl) ⟨17496, by rfl⟩ : syracuseStep 2986069 = 34993) (by norm_num)
theorem B6451285 : Blo 1590994 6451285 := bbase (se 8 (by rfl) ⟨37800, by rfl⟩ : syracuseStep 6451285 = 75601) (by norm_num)
theorem B2388053 : Blo 1590994 2388053 := bbase (se 8 (by rfl) ⟨13992, by rfl⟩ : syracuseStep 2388053 = 27985) (by norm_num)
theorem B1790041 : Blo 1590994 1790041 := bbase (se 2 (by rfl) ⟨671265, by rfl⟩ : syracuseStep 1790041 = 1342531) (by norm_num)
theorem B2420837 : Blo 1590994 2420837 := bbase (se 4 (by rfl) ⟨226953, by rfl⟩ : syracuseStep 2420837 = 453907) (by norm_num)
theorem B2388077 : Blo 1590994 2388077 := bbase (se 3 (by rfl) ⟨447764, by rfl⟩ : syracuseStep 2388077 = 895529) (by norm_num)
theorem B1699957 : Blo 1590994 1699957 := bbase (se 5 (by rfl) ⟨79685, by rfl⟩ : syracuseStep 1699957 = 159371) (by norm_num)
theorem B1790077 : Blo 1590994 1790077 := bbase (se 3 (by rfl) ⟨335639, by rfl⟩ : syracuseStep 1790077 = 671279) (by norm_num)
theorem B2388101 : Blo 1590994 2388101 := bbase (se 4 (by rfl) ⟨223884, by rfl⟩ : syracuseStep 2388101 = 447769) (by norm_num)
theorem B3584141 : Blo 1590994 3584141 := bbase (se 3 (by rfl) ⟨672026, by rfl⟩ : syracuseStep 3584141 = 1344053) (by norm_num)
theorem B2388125 : Blo 1590994 2388125 := bbase (se 3 (by rfl) ⟨447773, by rfl⟩ : syracuseStep 2388125 = 895547) (by norm_num)
theorem B1790113 : Blo 1590994 1790113 := bbase (se 2 (by rfl) ⟨671292, by rfl⟩ : syracuseStep 1790113 = 1342585) (by norm_num)
theorem B6803621 : Blo 1590994 6803621 := bbase (se 4 (by rfl) ⟨637839, by rfl⟩ : syracuseStep 6803621 = 1275679) (by norm_num)
theorem B2388149 : Blo 1590994 2388149 := bbase (se 5 (by rfl) ⟨111944, by rfl⟩ : syracuseStep 2388149 = 223889) (by norm_num)
theorem B1790149 : Blo 1590994 1790149 := bbase (se 4 (by rfl) ⟨167826, by rfl⟩ : syracuseStep 1790149 = 335653) (by norm_num)
theorem B2388173 : Blo 1590994 2388173 := bbase (se 3 (by rfl) ⟨447782, by rfl⟩ : syracuseStep 2388173 = 895565) (by norm_num)
theorem B3584213 : Blo 1590994 3584213 := bbase (se 7 (by rfl) ⟨42002, by rfl⟩ : syracuseStep 3584213 = 84005) (by norm_num)
theorem B1913053 : Blo 1590994 1913053 := bbase (se 3 (by rfl) ⟨358697, by rfl⟩ : syracuseStep 1913053 = 717395) (by norm_num)
theorem B7647461 : Blo 1590994 7647461 := bbase (se 4 (by rfl) ⟨716949, by rfl⟩ : syracuseStep 7647461 = 1433899) (by norm_num)
theorem B2388197 : Blo 1590994 2388197 := bbase (se 4 (by rfl) ⟨223893, by rfl⟩ : syracuseStep 2388197 = 447787) (by norm_num)
theorem B1790185 : Blo 1590994 1790185 := bbase (se 2 (by rfl) ⟨671319, by rfl⟩ : syracuseStep 1790185 = 1342639) (by norm_num)
theorem B1814761 : Blo 1590994 1814761 := bbase (se 2 (by rfl) ⟨680535, by rfl⟩ : syracuseStep 1814761 = 1361071) (by norm_num)
theorem B4534517 : Blo 1590994 4534517 := bbase (se 5 (by rfl) ⟨212555, by rfl⟩ : syracuseStep 4534517 = 425111) (by norm_num)
theorem B2388221 : Blo 1590994 2388221 := bbase (se 3 (by rfl) ⟨447791, by rfl⟩ : syracuseStep 2388221 = 895583) (by norm_num)
theorem B6041861 : Blo 1590994 6041861 := bbase (se 4 (by rfl) ⟨566424, by rfl⟩ : syracuseStep 6041861 = 1132849) (by norm_num)
theorem B1790221 : Blo 1590994 1790221 := bbase (se 3 (by rfl) ⟨335666, by rfl⟩ : syracuseStep 1790221 = 671333) (by norm_num)
theorem B2388245 : Blo 1590994 2388245 := bbase (se 6 (by rfl) ⟨55974, by rfl⟩ : syracuseStep 2388245 = 111949) (by norm_num)
theorem B2388269 : Blo 1590994 2388269 := bbase (se 3 (by rfl) ⟨447800, by rfl⟩ : syracuseStep 2388269 = 895601) (by norm_num)
theorem B1790257 : Blo 1590994 1790257 := bbase (se 2 (by rfl) ⟨671346, by rfl⟩ : syracuseStep 1790257 = 1342693) (by norm_num)
theorem B2265413 : Blo 1590994 2265413 := bbase (se 4 (by rfl) ⟨212382, by rfl⟩ : syracuseStep 2265413 = 424765) (by norm_num)
theorem B2388293 : Blo 1590994 2388293 := bbase (se 4 (by rfl) ⟨223902, by rfl⟩ : syracuseStep 2388293 = 447805) (by norm_num)
theorem B1790293 : Blo 1590994 1790293 := bbase (se 10 (by rfl) ⟨2622, by rfl⟩ : syracuseStep 1790293 = 5245) (by norm_num)
theorem B2388317 : Blo 1590994 2388317 := bbase (se 3 (by rfl) ⟨447809, by rfl⟩ : syracuseStep 2388317 = 895619) (by norm_num)
theorem B2388341 : Blo 1590994 2388341 := bbase (se 5 (by rfl) ⟨111953, by rfl⟩ : syracuseStep 2388341 = 223907) (by norm_num)
theorem B1790329 : Blo 1590994 1790329 := bbase (se 2 (by rfl) ⟨671373, by rfl⟩ : syracuseStep 1790329 = 1342747) (by norm_num)
theorem B5370245 : Blo 1590994 5370245 := bbase (se 4 (by rfl) ⟨503460, by rfl⟩ : syracuseStep 5370245 = 1006921) (by norm_num)
theorem B1913221 : Blo 1590994 1913221 := bbase (se 4 (by rfl) ⟨179364, by rfl⟩ : syracuseStep 1913221 = 358729) (by norm_num)
theorem B2388365 : Blo 1590994 2388365 := bbase (se 3 (by rfl) ⟨447818, by rfl⟩ : syracuseStep 2388365 = 895637) (by norm_num)
theorem B1790365 : Blo 1590994 1790365 := bbase (se 3 (by rfl) ⟨335693, by rfl⟩ : syracuseStep 1790365 = 671387) (by norm_num)
theorem B2388389 : Blo 1590994 2388389 := bbase (se 4 (by rfl) ⟨223911, by rfl⟩ : syracuseStep 2388389 = 447823) (by norm_num)
theorem B4084157 : Blo 1590994 4084157 := bbase (se 3 (by rfl) ⟨765779, by rfl⟩ : syracuseStep 4084157 = 1531559) (by norm_num)
theorem B2388413 : Blo 1590994 2388413 := bbase (se 3 (by rfl) ⟨447827, by rfl⟩ : syracuseStep 2388413 = 895655) (by norm_num)
theorem B1790401 : Blo 1590994 1790401 := bbase (se 2 (by rfl) ⟨671400, by rfl⟩ : syracuseStep 1790401 = 1342801) (by norm_num)
theorem B2388437 : Blo 1590994 2388437 := bbase (se 7 (by rfl) ⟨27989, by rfl⟩ : syracuseStep 2388437 = 55979) (by norm_num)
theorem B1790437 : Blo 1590994 1790437 := bbase (se 4 (by rfl) ⟨167853, by rfl⟩ : syracuseStep 1790437 = 335707) (by norm_num)
theorem B2388461 : Blo 1590994 2388461 := bbase (se 3 (by rfl) ⟨447836, by rfl⟩ : syracuseStep 2388461 = 895673) (by norm_num)
theorem B2388485 : Blo 1590994 2388485 := bbase (se 4 (by rfl) ⟨223920, by rfl⟩ : syracuseStep 2388485 = 447841) (by norm_num)
theorem B1790473 : Blo 1590994 1790473 := bbase (se 2 (by rfl) ⟨671427, by rfl⟩ : syracuseStep 1790473 = 1342855) (by norm_num)
theorem B2388509 : Blo 1590994 2388509 := bbase (se 3 (by rfl) ⟨447845, by rfl⟩ : syracuseStep 2388509 = 895691) (by norm_num)
theorem B1700389 : Blo 1590994 1700389 := bbase (se 4 (by rfl) ⟨159411, by rfl⟩ : syracuseStep 1700389 = 318823) (by norm_num)
theorem B1790509 : Blo 1590994 1790509 := bbase (se 3 (by rfl) ⟨335720, by rfl⟩ : syracuseStep 1790509 = 671441) (by norm_num)
theorem B2388533 : Blo 1590994 2388533 := bbase (se 5 (by rfl) ⟨111962, by rfl⟩ : syracuseStep 2388533 = 223925) (by norm_num)
theorem B12096053 : Blo 1590994 12096053 := bbase (se 5 (by rfl) ⟨567002, by rfl⟩ : syracuseStep 12096053 = 1134005) (by norm_num)
theorem B1937989 : Blo 1590994 1937989 := bbase (se 4 (by rfl) ⟨181686, by rfl⟩ : syracuseStep 1937989 = 363373) (by norm_num)
theorem B2388557 : Blo 1590994 2388557 := bbase (se 3 (by rfl) ⟨447854, by rfl⟩ : syracuseStep 2388557 = 895709) (by norm_num)
theorem B1790545 : Blo 1590994 1790545 := bbase (se 2 (by rfl) ⟨671454, by rfl⟩ : syracuseStep 1790545 = 1342909) (by norm_num)
theorem B2388581 : Blo 1590994 2388581 := bbase (se 4 (by rfl) ⟨223929, by rfl⟩ : syracuseStep 2388581 = 447859) (by norm_num)
theorem B1700461 : Blo 1590994 1700461 := bbase (se 3 (by rfl) ⟨318836, by rfl⟩ : syracuseStep 1700461 = 637673) (by norm_num)
theorem B1790581 : Blo 1590994 1790581 := bbase (se 5 (by rfl) ⟨83933, by rfl⟩ : syracuseStep 1790581 = 167867) (by norm_num)
theorem B2388605 : Blo 1590994 2388605 := bbase (se 3 (by rfl) ⟨447863, by rfl⟩ : syracuseStep 2388605 = 895727) (by norm_num)
theorem B2388629 : Blo 1590994 2388629 := bbase (se 6 (by rfl) ⟨55983, by rfl⟩ : syracuseStep 2388629 = 111967) (by norm_num)
theorem B1790617 : Blo 1590994 1790617 := bbase (se 2 (by rfl) ⟨671481, by rfl⟩ : syracuseStep 1790617 = 1342963) (by norm_num)
theorem B2388653 : Blo 1590994 2388653 := bbase (se 3 (by rfl) ⟨447872, by rfl⟩ : syracuseStep 2388653 = 895745) (by norm_num)
theorem B1790653 : Blo 1590994 1790653 := bbase (se 3 (by rfl) ⟨335747, by rfl⟩ : syracuseStep 1790653 = 671495) (by norm_num)
theorem B2388677 : Blo 1590994 2388677 := bbase (se 4 (by rfl) ⟨223938, by rfl⟩ : syracuseStep 2388677 = 447877) (by norm_num)
theorem B2388701 : Blo 1590994 2388701 := bbase (se 3 (by rfl) ⟨447881, by rfl⟩ : syracuseStep 2388701 = 895763) (by norm_num)
theorem B1790689 : Blo 1590994 1790689 := bbase (se 2 (by rfl) ⟨671508, by rfl⟩ : syracuseStep 1790689 = 1343017) (by norm_num)
theorem B2388725 : Blo 1590994 2388725 := bbase (se 5 (by rfl) ⟨111971, by rfl⟩ : syracuseStep 2388725 = 223943) (by norm_num)
theorem B1790725 : Blo 1590994 1790725 := bbase (se 4 (by rfl) ⟨167880, by rfl⟩ : syracuseStep 1790725 = 335761) (by norm_num)
theorem B3445517 : Blo 1590994 3445517 := bbase (se 3 (by rfl) ⟨646034, by rfl⟩ : syracuseStep 3445517 = 1292069) (by norm_num)
theorem B2388749 : Blo 1590994 2388749 := bbase (se 3 (by rfl) ⟨447890, by rfl⟩ : syracuseStep 2388749 = 895781) (by norm_num)
theorem B24507157 : Blo 1590994 24507157 := bbase (se 6 (by rfl) ⟨574386, by rfl⟩ : syracuseStep 24507157 = 1148773) (by norm_num)
theorem B2388773 : Blo 1590994 2388773 := bbase (se 4 (by rfl) ⟨223947, by rfl⟩ : syracuseStep 2388773 = 447895) (by norm_num)
theorem B1790761 : Blo 1590994 1790761 := bbase (se 2 (by rfl) ⟨671535, by rfl⟩ : syracuseStep 1790761 = 1343071) (by norm_num)
theorem B5370677 : Blo 1590994 5370677 := bbase (se 5 (by rfl) ⟨251750, by rfl⟩ : syracuseStep 5370677 = 503501) (by norm_num)
theorem B2388797 : Blo 1590994 2388797 := bbase (se 3 (by rfl) ⟨447899, by rfl⟩ : syracuseStep 2388797 = 895799) (by norm_num)
theorem B1790797 : Blo 1590994 1790797 := bbase (se 3 (by rfl) ⟨335774, by rfl⟩ : syracuseStep 1790797 = 671549) (by norm_num)
theorem B2388821 : Blo 1590994 2388821 := bbase (se 9 (by rfl) ⟨6998, by rfl⟩ : syracuseStep 2388821 = 13997) (by norm_num)
theorem B4027229 : Blo 1590994 4027229 := bbase (se 3 (by rfl) ⟨755105, by rfl⟩ : syracuseStep 4027229 = 1510211) (by norm_num)
theorem B2388845 : Blo 1590994 2388845 := bbase (se 3 (by rfl) ⟨447908, by rfl⟩ : syracuseStep 2388845 = 895817) (by norm_num)
theorem B1790833 : Blo 1590994 1790833 := bbase (se 2 (by rfl) ⟨671562, by rfl⟩ : syracuseStep 1790833 = 1343125) (by norm_num)
theorem B8057717 : Blo 1590994 8057717 := bbase (se 5 (by rfl) ⟨377705, by rfl⟩ : syracuseStep 8057717 = 755411) (by norm_num)
theorem B2388869 : Blo 1590994 2388869 := bbase (se 4 (by rfl) ⟨223956, by rfl⟩ : syracuseStep 2388869 = 447913) (by norm_num)
theorem B1790869 : Blo 1590994 1790869 := bbase (se 6 (by rfl) ⟨41973, by rfl⟩ : syracuseStep 1790869 = 83947) (by norm_num)
theorem B21795733 : Blo 1590994 21795733 := bbase (se 6 (by rfl) ⟨510837, by rfl⟩ : syracuseStep 21795733 = 1021675) (by norm_num)
theorem B1913749 : Blo 1590994 1913749 := bbase (se 6 (by rfl) ⟨44853, by rfl⟩ : syracuseStep 1913749 = 89707) (by norm_num)
theorem B2388893 : Blo 1590994 2388893 := bbase (se 3 (by rfl) ⟨447917, by rfl⟩ : syracuseStep 2388893 = 895835) (by norm_num)
theorem B2388917 : Blo 1590994 2388917 := bbase (se 5 (by rfl) ⟨111980, by rfl⟩ : syracuseStep 2388917 = 223961) (by norm_num)
theorem B1790905 : Blo 1590994 1790905 := bbase (se 2 (by rfl) ⟨671589, by rfl⟩ : syracuseStep 1790905 = 1343179) (by norm_num)
theorem B2388941 : Blo 1590994 2388941 := bbase (se 3 (by rfl) ⟨447926, by rfl⟩ : syracuseStep 2388941 = 895853) (by norm_num)
theorem B12088277 : Blo 1590994 12088277 := bbase (se 7 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 12088277 = 283319) (by norm_num)
theorem B1790941 : Blo 1590994 1790941 := bbase (se 3 (by rfl) ⟨335801, by rfl⟩ : syracuseStep 1790941 = 671603) (by norm_num)
theorem B1700833 : Blo 1590994 1700833 := bbase (se 2 (by rfl) ⟨637812, by rfl⟩ : syracuseStep 1700833 = 1275625) (by norm_num)
theorem B2388965 : Blo 1590994 2388965 := bbase (se 4 (by rfl) ⟨223965, by rfl⟩ : syracuseStep 2388965 = 447931) (by norm_num)
theorem B2388989 : Blo 1590994 2388989 := bbase (se 3 (by rfl) ⟨447935, by rfl⟩ : syracuseStep 2388989 = 895871) (by norm_num)
theorem B1790977 : Blo 1590994 1790977 := bbase (se 2 (by rfl) ⟨671616, by rfl⟩ : syracuseStep 1790977 = 1343233) (by norm_num)
theorem B2389013 : Blo 1590994 2389013 := bbase (se 6 (by rfl) ⟨55992, by rfl⟩ : syracuseStep 2389013 = 111985) (by norm_num)
theorem B4027421 : Blo 1590994 4027421 := bbase (se 3 (by rfl) ⟨755141, by rfl⟩ : syracuseStep 4027421 = 1510283) (by norm_num)
theorem B1791013 : Blo 1590994 1791013 := bbase (se 4 (by rfl) ⟨167907, by rfl⟩ : syracuseStep 1791013 = 335815) (by norm_num)
theorem B2389037 : Blo 1590994 2389037 := bbase (se 3 (by rfl) ⟨447944, by rfl⟩ : syracuseStep 2389037 = 895889) (by norm_num)
theorem B2266165 : Blo 1590994 2266165 := bbase (se 5 (by rfl) ⟨106226, by rfl⟩ : syracuseStep 2266165 = 212453) (by norm_num)
theorem B2389061 : Blo 1590994 2389061 := bbase (se 4 (by rfl) ⟨223974, by rfl⟩ : syracuseStep 2389061 = 447949) (by norm_num)
theorem B1791049 : Blo 1590994 1791049 := bbase (se 2 (by rfl) ⟨671643, by rfl⟩ : syracuseStep 1791049 = 1343287) (by norm_num)
theorem B2389085 : Blo 1590994 2389085 := bbase (se 3 (by rfl) ⟨447953, by rfl⟩ : syracuseStep 2389085 = 895907) (by norm_num)
theorem B1791085 : Blo 1590994 1791085 := bbase (se 3 (by rfl) ⟨335828, by rfl⟩ : syracuseStep 1791085 = 671657) (by norm_num)
theorem B8606837 : Blo 1590994 8606837 := bbase (se 5 (by rfl) ⟨403445, by rfl⟩ : syracuseStep 8606837 = 806891) (by norm_num)
theorem B2389109 : Blo 1590994 2389109 := bbase (se 5 (by rfl) ⟨111989, by rfl⟩ : syracuseStep 2389109 = 223979) (by norm_num)
theorem B2389133 : Blo 1590994 2389133 := bbase (se 3 (by rfl) ⟨447962, by rfl⟩ : syracuseStep 2389133 = 895925) (by norm_num)
theorem B1791121 : Blo 1590994 1791121 := bbase (se 2 (by rfl) ⟨671670, by rfl⟩ : syracuseStep 1791121 = 1343341) (by norm_num)
theorem B2389157 : Blo 1590994 2389157 := bbase (se 4 (by rfl) ⟨223983, by rfl⟩ : syracuseStep 2389157 = 447967) (by norm_num)
theorem B4592821 : Blo 1590994 4592821 := bbase (se 5 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 4592821 = 430577) (by norm_num)
theorem B1791157 : Blo 1590994 1791157 := bbase (se 5 (by rfl) ⟨83960, by rfl⟩ : syracuseStep 1791157 = 167921) (by norm_num)
theorem B2389181 : Blo 1590994 2389181 := bbase (se 3 (by rfl) ⟨447971, by rfl⟩ : syracuseStep 2389181 = 895943) (by norm_num)
theorem B2389205 : Blo 1590994 2389205 := bbase (se 7 (by rfl) ⟨27998, by rfl⟩ : syracuseStep 2389205 = 55997) (by norm_num)
theorem B1791193 : Blo 1590994 1791193 := bbase (se 2 (by rfl) ⟨671697, by rfl⟩ : syracuseStep 1791193 = 1343395) (by norm_num)
theorem B5371109 : Blo 1590994 5371109 := bbase (se 4 (by rfl) ⟨503541, by rfl⟩ : syracuseStep 5371109 = 1007083) (by norm_num)
theorem B6894821 : Blo 1590994 6894821 := bbase (se 4 (by rfl) ⟨646389, by rfl⟩ : syracuseStep 6894821 = 1292779) (by norm_num)
theorem B2389229 : Blo 1590994 2389229 := bbase (se 3 (by rfl) ⟨447980, by rfl⟩ : syracuseStep 2389229 = 895961) (by norm_num)
theorem B14521589 : Blo 1590994 14521589 := bbase (se 5 (by rfl) ⟨680699, by rfl⟩ : syracuseStep 14521589 = 1361399) (by norm_num)
theorem B1791229 : Blo 1590994 1791229 := bbase (se 3 (by rfl) ⟨335855, by rfl⟩ : syracuseStep 1791229 = 671711) (by norm_num)
theorem B2389253 : Blo 1590994 2389253 := bbase (se 4 (by rfl) ⟨223992, by rfl⟩ : syracuseStep 2389253 = 447985) (by norm_num)
theorem B2389277 : Blo 1590994 2389277 := bbase (se 3 (by rfl) ⟨447989, by rfl⟩ : syracuseStep 2389277 = 895979) (by norm_num)
theorem B1791265 : Blo 1590994 1791265 := bbase (se 2 (by rfl) ⟨671724, by rfl⟩ : syracuseStep 1791265 = 1343449) (by norm_num)
theorem B2389301 : Blo 1590994 2389301 := bbase (se 5 (by rfl) ⟨111998, by rfl⟩ : syracuseStep 2389301 = 223997) (by norm_num)
theorem B1791301 : Blo 1590994 1791301 := bbase (se 4 (by rfl) ⟨167934, by rfl⟩ : syracuseStep 1791301 = 335869) (by norm_num)
theorem B2389325 : Blo 1590994 2389325 := bbase (se 3 (by rfl) ⟨447998, by rfl⟩ : syracuseStep 2389325 = 895997) (by norm_num)
theorem B2389349 : Blo 1590994 2389349 := bbase (se 4 (by rfl) ⟨224001, by rfl⟩ : syracuseStep 2389349 = 448003) (by norm_num)
theorem B1791337 : Blo 1590994 1791337 := bbase (se 2 (by rfl) ⟨671751, by rfl⟩ : syracuseStep 1791337 = 1343503) (by norm_num)
theorem B4027765 : Blo 1590994 4027765 := bbase (se 5 (by rfl) ⟨188801, by rfl⟩ : syracuseStep 4027765 = 377603) (by norm_num)
theorem B2389373 : Blo 1590994 2389373 := bbase (se 3 (by rfl) ⟨448007, by rfl⟩ : syracuseStep 2389373 = 896015) (by norm_num)
theorem B1791373 : Blo 1590994 1791373 := bbase (se 3 (by rfl) ⟨335882, by rfl⟩ : syracuseStep 1791373 = 671765) (by norm_num)
theorem B2389397 : Blo 1590994 2389397 := bbase (se 6 (by rfl) ⟨56001, by rfl⟩ : syracuseStep 2389397 = 112003) (by norm_num)
theorem B6043045 : Blo 1590994 6043045 := bbase (se 4 (by rfl) ⟨566535, by rfl⟩ : syracuseStep 6043045 = 1133071) (by norm_num)
theorem B2389421 : Blo 1590994 2389421 := bbase (se 3 (by rfl) ⟨448016, by rfl⟩ : syracuseStep 2389421 = 896033) (by norm_num)
theorem B1791409 : Blo 1590994 1791409 := bbase (se 2 (by rfl) ⟨671778, by rfl⟩ : syracuseStep 1791409 = 1343557) (by norm_num)
theorem B2389445 : Blo 1590994 2389445 := bbase (se 4 (by rfl) ⟨224010, by rfl⟩ : syracuseStep 2389445 = 448021) (by norm_num)
theorem B1791445 : Blo 1590994 1791445 := bbase (se 7 (by rfl) ⟨20993, by rfl⟩ : syracuseStep 1791445 = 41987) (by norm_num)
theorem B58111445 : Blo 1590994 58111445 := bbase (se 7 (by rfl) ⟨680993, by rfl⟩ : syracuseStep 58111445 = 1361987) (by norm_num)
theorem B2389469 : Blo 1590994 2389469 := bbase (se 3 (by rfl) ⟨448025, by rfl⟩ : syracuseStep 2389469 = 896051) (by norm_num)
theorem B4027877 : Blo 1590994 4027877 := bbase (se 4 (by rfl) ⟨377613, by rfl⟩ : syracuseStep 4027877 = 755227) (by norm_num)
theorem B1791481 : Blo 1590994 1791481 := bbase (se 2 (by rfl) ⟨671805, by rfl⟩ : syracuseStep 1791481 = 1343611) (by norm_num)
theorem B9066005 : Blo 1590994 9066005 := bbase (se 6 (by rfl) ⟨212484, by rfl⟩ : syracuseStep 9066005 = 424969) (by norm_num)
theorem B1791517 : Blo 1590994 1791517 := bbase (se 3 (by rfl) ⟨335909, by rfl⟩ : syracuseStep 1791517 = 671819) (by norm_num)
theorem B2151973 : Blo 1590994 2151973 := bbase (se 4 (by rfl) ⟨201747, by rfl⟩ : syracuseStep 2151973 = 403495) (by norm_num)
theorem B1791553 : Blo 1590994 1791553 := bbase (se 2 (by rfl) ⟨671832, by rfl⟩ : syracuseStep 1791553 = 1343665) (by norm_num)
theorem B1791589 : Blo 1590994 1791589 := bbase (se 4 (by rfl) ⟨167961, by rfl⟩ : syracuseStep 1791589 = 335923) (by norm_num)
theorem B3823213 : Blo 1590994 3823213 := bbase (se 3 (by rfl) ⟨716852, by rfl⟩ : syracuseStep 3823213 = 1433705) (by norm_num)
theorem B1791625 : Blo 1590994 1791625 := bbase (se 2 (by rfl) ⟨671859, by rfl⟩ : syracuseStep 1791625 = 1343719) (by norm_num)
theorem B3020429 : Blo 1590994 3020429 := bbase (se 3 (by rfl) ⟨566330, by rfl⟩ : syracuseStep 3020429 = 1132661) (by norm_num)
theorem B5371541 : Blo 1590994 5371541 := bbase (se 6 (by rfl) ⟨125895, by rfl⟩ : syracuseStep 5371541 = 251791) (by norm_num)
theorem B4028069 : Blo 1590994 4028069 := bbase (se 4 (by rfl) ⟨377631, by rfl⟩ : syracuseStep 4028069 = 755263) (by norm_num)
theorem B6985381 : Blo 1590994 6985381 := bbase (se 4 (by rfl) ⟨654879, by rfl⟩ : syracuseStep 6985381 = 1309759) (by norm_num)
theorem B1791661 : Blo 1590994 1791661 := bbase (se 3 (by rfl) ⟨335936, by rfl⟩ : syracuseStep 1791661 = 671873) (by norm_num)
theorem B1791697 : Blo 1590994 1791697 := bbase (se 2 (by rfl) ⟨671886, by rfl⟩ : syracuseStep 1791697 = 1343773) (by norm_num)
theorem B6043349 : Blo 1590994 6043349 := bbase (se 7 (by rfl) ⟨70820, by rfl⟩ : syracuseStep 6043349 = 141641) (by norm_num)
theorem B1791733 : Blo 1590994 1791733 := bbase (se 5 (by rfl) ⟨83987, by rfl⟩ : syracuseStep 1791733 = 167975) (by norm_num)
theorem B1791769 : Blo 1590994 1791769 := bbase (se 2 (by rfl) ⟨671913, by rfl⟩ : syracuseStep 1791769 = 1343827) (by norm_num)
theorem B3020581 : Blo 1590994 3020581 := bbase (se 4 (by rfl) ⟨283179, by rfl⟩ : syracuseStep 3020581 = 566359) (by norm_num)
theorem B5740325 : Blo 1590994 5740325 := bbase (se 4 (by rfl) ⟨538155, by rfl⟩ : syracuseStep 5740325 = 1076311) (by norm_num)
theorem B4536101 : Blo 1590994 4536101 := bbase (se 4 (by rfl) ⟨425259, by rfl⟩ : syracuseStep 4536101 = 850519) (by norm_num)
theorem B1791805 : Blo 1590994 1791805 := bbase (se 3 (by rfl) ⟨335963, by rfl⟩ : syracuseStep 1791805 = 671927) (by norm_num)
theorem B2266957 : Blo 1590994 2266957 := bbase (se 3 (by rfl) ⟨425054, by rfl⟩ : syracuseStep 2266957 = 850109) (by norm_num)
theorem B1791841 : Blo 1590994 1791841 := bbase (se 2 (by rfl) ⟨671940, by rfl⟩ : syracuseStep 1791841 = 1343881) (by norm_num)
theorem B1791877 : Blo 1590994 1791877 := bbase (se 4 (by rfl) ⟨167988, by rfl⟩ : syracuseStep 1791877 = 335977) (by norm_num)
theorem B1791913 : Blo 1590994 1791913 := bbase (se 2 (by rfl) ⟨671967, by rfl⟩ : syracuseStep 1791913 = 1343935) (by norm_num)
theorem B1791949 : Blo 1590994 1791949 := bbase (se 3 (by rfl) ⟨335990, by rfl⟩ : syracuseStep 1791949 = 671981) (by norm_num)
theorem B2684893 : Blo 1590994 2684893 := bbase (se 3 (by rfl) ⟨503417, by rfl⟩ : syracuseStep 2684893 = 1006835) (by norm_num)
theorem B1791985 : Blo 1590994 1791985 := bbase (se 2 (by rfl) ⟨671994, by rfl⟩ : syracuseStep 1791985 = 1343989) (by norm_num)
theorem B4028413 : Blo 1590994 4028413 := bbase (se 3 (by rfl) ⟨755327, by rfl⟩ : syracuseStep 4028413 = 1510655) (by norm_num)
theorem B6797317 : Blo 1590994 6797317 := bbase (se 4 (by rfl) ⟨637248, by rfl⟩ : syracuseStep 6797317 = 1274497) (by norm_num)
theorem B6797333 : Blo 1590994 6797333 := bbase (se 6 (by rfl) ⟨159312, by rfl⟩ : syracuseStep 6797333 = 318625) (by norm_num)
theorem B1792021 : Blo 1590994 1792021 := bbase (se 6 (by rfl) ⟨42000, by rfl⟩ : syracuseStep 1792021 = 84001) (by norm_num)
theorem B2684981 : Blo 1590994 2684981 := bbase (se 5 (by rfl) ⟨125858, by rfl⟩ : syracuseStep 2684981 = 251717) (by norm_num)
theorem B1792057 : Blo 1590994 1792057 := bbase (se 2 (by rfl) ⟨672021, by rfl⟩ : syracuseStep 1792057 = 1344043) (by norm_num)
theorem B5371973 : Blo 1590994 5371973 := bbase (se 4 (by rfl) ⟨503622, by rfl⟩ : syracuseStep 5371973 = 1007245) (by norm_num)
theorem B3020885 : Blo 1590994 3020885 := bbase (se 8 (by rfl) ⟨17700, by rfl⟩ : syracuseStep 3020885 = 35401) (by norm_num)
theorem B1792093 : Blo 1590994 1792093 := bbase (se 3 (by rfl) ⟨336017, by rfl⟩ : syracuseStep 1792093 = 672035) (by norm_num)
theorem B4028525 : Blo 1590994 4028525 := bbase (se 3 (by rfl) ⟨755348, by rfl⟩ : syracuseStep 4028525 = 1510697) (by norm_num)
theorem B8059013 : Blo 1590994 8059013 := bbase (se 4 (by rfl) ⟨755532, by rfl⟩ : syracuseStep 8059013 = 1511065) (by norm_num)
theorem B3061901 : Blo 1590994 3061901 := bbase (se 3 (by rfl) ⟨574106, by rfl⟩ : syracuseStep 3061901 = 1148213) (by norm_num)
theorem B13596821 : Blo 1590994 13596821 := bbase (se 6 (by rfl) ⟨318675, by rfl⟩ : syracuseStep 13596821 = 637351) (by norm_num)
theorem B5101717 : Blo 1590994 5101717 := bbase (se 6 (by rfl) ⟨119571, by rfl⟩ : syracuseStep 5101717 = 239143) (by norm_num)
theorem B2267293 : Blo 1590994 2267293 := bbase (se 3 (by rfl) ⟨425117, by rfl⟩ : syracuseStep 2267293 = 850235) (by norm_num)
theorem B2685109 : Blo 1590994 2685109 := bbase (se 5 (by rfl) ⟨125864, by rfl⟩ : syracuseStep 2685109 = 251729) (by norm_num)
theorem B2685197 : Blo 1590994 2685197 := bbase (se 3 (by rfl) ⟨503474, by rfl⟩ : syracuseStep 2685197 = 1006949) (by norm_num)
theorem B4028717 : Blo 1590994 4028717 := bbase (se 3 (by rfl) ⟨755384, by rfl⟩ : syracuseStep 4028717 = 1510769) (by norm_num)
theorem B2267509 : Blo 1590994 2267509 := bbase (se 5 (by rfl) ⟨106289, by rfl⟩ : syracuseStep 2267509 = 212579) (by norm_num)
theorem B2685325 : Blo 1590994 2685325 := bbase (se 3 (by rfl) ⟨503498, by rfl⟩ : syracuseStep 2685325 = 1006997) (by norm_num)
theorem B6125989 : Blo 1590994 6125989 := bbase (se 4 (by rfl) ⟨574311, by rfl⟩ : syracuseStep 6125989 = 1148623) (by norm_num)
theorem B6453701 : Blo 1590994 6453701 := bbase (se 4 (by rfl) ⟨605034, by rfl⟩ : syracuseStep 6453701 = 1210069) (by norm_num)
theorem B2685413 : Blo 1590994 2685413 := bbase (se 4 (by rfl) ⟨251757, by rfl⟩ : syracuseStep 2685413 = 503515) (by norm_num)
theorem B5372405 : Blo 1590994 5372405 := bbase (se 5 (by rfl) ⟨251831, by rfl⟩ : syracuseStep 5372405 = 503663) (by norm_num)
theorem B2013761 : Blo 1590994 2013761 := bbase (se 2 (by rfl) ⟨755160, by rfl⟩ : syracuseStep 2013761 = 1510321) (by norm_num)
theorem B2685541 : Blo 1590994 2685541 := bbase (se 4 (by rfl) ⟨251769, by rfl⟩ : syracuseStep 2685541 = 503539) (by norm_num)
theorem B2013817 : Blo 1590994 2013817 := bbase (se 2 (by rfl) ⟨755181, by rfl⟩ : syracuseStep 2013817 = 1510363) (by norm_num)
theorem B4029061 : Blo 1590994 4029061 := bbase (se 4 (by rfl) ⟨377724, by rfl⟩ : syracuseStep 4029061 = 755449) (by norm_num)
theorem B2685629 : Blo 1590994 2685629 := bbase (se 3 (by rfl) ⟨503555, by rfl⟩ : syracuseStep 2685629 = 1007111) (by norm_num)
theorem B2013913 : Blo 1590994 2013913 := bbase (se 2 (by rfl) ⟨755217, by rfl⟩ : syracuseStep 2013913 = 1510435) (by norm_num)
theorem B2267885 : Blo 1590994 2267885 := bbase (se 3 (by rfl) ⟨425228, by rfl⟩ : syracuseStep 2267885 = 850457) (by norm_num)
theorem B4029173 : Blo 1590994 4029173 := bbase (se 5 (by rfl) ⟨188867, by rfl⟩ : syracuseStep 4029173 = 377735) (by norm_num)
theorem B2685757 : Blo 1590994 2685757 := bbase (se 3 (by rfl) ⟨503579, by rfl⟩ : syracuseStep 2685757 = 1007159) (by norm_num)
theorem B3021637 : Blo 1590994 3021637 := bbase (se 4 (by rfl) ⟨283278, by rfl⟩ : syracuseStep 3021637 = 566557) (by norm_num)
theorem B10197845 : Blo 1590994 10197845 := bbase (se 9 (by rfl) ⟨29876, by rfl⟩ : syracuseStep 10197845 = 59753) (by norm_num)
theorem B2014085 : Blo 1590994 2014085 := bbase (se 4 (by rfl) ⟨188820, by rfl⟩ : syracuseStep 2014085 = 377641) (by norm_num)
theorem B2685845 : Blo 1590994 2685845 := bbase (se 6 (by rfl) ⟨62949, by rfl⟩ : syracuseStep 2685845 = 125899) (by norm_num)
theorem B5372837 : Blo 1590994 5372837 := bbase (se 4 (by rfl) ⟨503703, by rfl⟩ : syracuseStep 5372837 = 1007407) (by norm_num)
theorem B4029365 : Blo 1590994 4029365 := bbase (se 5 (by rfl) ⟨188876, by rfl⟩ : syracuseStep 4029365 = 377753) (by norm_num)
theorem B7650229 : Blo 1590994 7650229 := bbase (se 5 (by rfl) ⟨358604, by rfl⟩ : syracuseStep 7650229 = 717209) (by norm_num)
theorem B2014141 : Blo 1590994 2014141 := bbase (se 3 (by rfl) ⟨377651, by rfl⟩ : syracuseStep 2014141 = 755303) (by norm_num)
theorem B3021781 : Blo 1590994 3021781 := bbase (se 7 (by rfl) ⟨35411, by rfl⟩ : syracuseStep 3021781 = 70823) (by norm_num)
theorem B3824597 : Blo 1590994 3824597 := bbase (se 7 (by rfl) ⟨44819, by rfl⟩ : syracuseStep 3824597 = 89639) (by norm_num)
theorem B5815253 : Blo 1590994 5815253 := bbase (se 7 (by rfl) ⟨68147, by rfl⟩ : syracuseStep 5815253 = 136295) (by norm_num)
theorem B2685973 : Blo 1590994 2685973 := bbase (se 6 (by rfl) ⟨62952, by rfl⟩ : syracuseStep 2685973 = 125905) (by norm_num)
theorem B2014237 : Blo 1590994 2014237 := bbase (se 3 (by rfl) ⟨377669, by rfl⟩ : syracuseStep 2014237 = 755339) (by norm_num)
theorem B3398701 : Blo 1590994 3398701 := bbase (se 3 (by rfl) ⟨637256, by rfl⟩ : syracuseStep 3398701 = 1274513) (by norm_num)
theorem B4422725 : Blo 1590994 4422725 := bbase (se 4 (by rfl) ⟨414630, by rfl⟩ : syracuseStep 4422725 = 829261) (by norm_num)
theorem B1612877 : Blo 1590994 1612877 := bbase (se 3 (by rfl) ⟨302414, by rfl⟩ : syracuseStep 1612877 = 604829) (by norm_num)
theorem B2686061 : Blo 1590994 2686061 := bbase (se 3 (by rfl) ⟨503636, by rfl⟩ : syracuseStep 2686061 = 1007273) (by norm_num)
theorem B3021941 : Blo 1590994 3021941 := bbase (se 5 (by rfl) ⟨141653, by rfl⟩ : syracuseStep 3021941 = 283307) (by norm_num)
theorem B4086949 : Blo 1590994 4086949 := bbase (se 4 (by rfl) ⟨383151, by rfl⟩ : syracuseStep 4086949 = 766303) (by norm_num)
theorem B2014409 : Blo 1590994 2014409 := bbase (se 2 (by rfl) ⟨755403, by rfl⟩ : syracuseStep 2014409 = 1510807) (by norm_num)
theorem B2686189 : Blo 1590994 2686189 := bbase (se 3 (by rfl) ⟨503660, by rfl⟩ : syracuseStep 2686189 = 1007321) (by norm_num)
theorem B2014465 : Blo 1590994 2014465 := bbase (se 2 (by rfl) ⟨755424, by rfl⟩ : syracuseStep 2014465 = 1510849) (by norm_num)
theorem B3022085 : Blo 1590994 3022085 := bbase (se 4 (by rfl) ⟨283320, by rfl⟩ : syracuseStep 3022085 = 566641) (by norm_num)
theorem B4029709 : Blo 1590994 4029709 := bbase (se 3 (by rfl) ⟨755570, by rfl⟩ : syracuseStep 4029709 = 1511141) (by norm_num)
theorem B1613081 : Blo 1590994 1613081 := bbase (se 2 (by rfl) ⟨604905, by rfl⟩ : syracuseStep 1613081 = 1209811) (by norm_num)
theorem B5242165 : Blo 1590994 5242165 := bbase (se 5 (by rfl) ⟨245726, by rfl⟩ : syracuseStep 5242165 = 491453) (by norm_num)
theorem B2686277 : Blo 1590994 2686277 := bbase (se 4 (by rfl) ⟨251838, by rfl⟩ : syracuseStep 2686277 = 503677) (by norm_num)
theorem B5373269 : Blo 1590994 5373269 := bbase (se 11 (by rfl) ⟨3935, by rfl⟩ : syracuseStep 5373269 = 7871) (by norm_num)
theorem B2014561 : Blo 1590994 2014561 := bbase (se 2 (by rfl) ⟨755460, by rfl⟩ : syracuseStep 2014561 = 1510921) (by norm_num)
theorem B4029821 : Blo 1590994 4029821 := bbase (se 3 (by rfl) ⟨755591, by rfl⟩ : syracuseStep 4029821 = 1511183) (by norm_num)
theorem B3825029 : Blo 1590994 3825029 := bbase (se 4 (by rfl) ⟨358596, by rfl⟩ : syracuseStep 3825029 = 717193) (by norm_num)
theorem B8060309 : Blo 1590994 8060309 := bbase (se 6 (by rfl) ⟨188913, by rfl⟩ : syracuseStep 8060309 = 377827) (by norm_num)
theorem B3399077 : Blo 1590994 3399077 := bbase (se 4 (by rfl) ⟨318663, by rfl⟩ : syracuseStep 3399077 = 637327) (by norm_num)
theorem B2686405 : Blo 1590994 2686405 := bbase (se 4 (by rfl) ⟨251850, by rfl⟩ : syracuseStep 2686405 = 503701) (by norm_num)
theorem B2014733 : Blo 1590994 2014733 := bbase (se 3 (by rfl) ⟨377762, by rfl⟩ : syracuseStep 2014733 = 755525) (by norm_num)
theorem B2686493 : Blo 1590994 2686493 := bbase (se 3 (by rfl) ⟨503717, by rfl⟩ : syracuseStep 2686493 = 1007435) (by norm_num)
theorem B3022373 : Blo 1590994 3022373 := bbase (se 4 (by rfl) ⟨283347, by rfl⟩ : syracuseStep 3022373 = 566695) (by norm_num)
theorem B4030013 : Blo 1590994 4030013 := bbase (se 3 (by rfl) ⟨755627, by rfl⟩ : syracuseStep 4030013 = 1511255) (by norm_num)
theorem B2014789 : Blo 1590994 2014789 := bbase (se 4 (by rfl) ⟨188886, by rfl⟩ : syracuseStep 2014789 = 377773) (by norm_num)
theorem B1613461 : Blo 1590994 1613461 := bbase (se 6 (by rfl) ⟨37815, by rfl⟩ : syracuseStep 1613461 = 75631) (by norm_num)
theorem B2686621 : Blo 1590994 2686621 := bbase (se 3 (by rfl) ⟨503741, by rfl⟩ : syracuseStep 2686621 = 1007483) (by norm_num)
theorem B2014885 : Blo 1590994 2014885 := bbase (se 4 (by rfl) ⟨188895, by rfl⟩ : syracuseStep 2014885 = 377791) (by norm_num)
theorem B9068213 : Blo 1590994 9068213 := bbase (se 5 (by rfl) ⟨425072, by rfl⟩ : syracuseStep 9068213 = 850145) (by norm_num)
theorem B3022525 : Blo 1590994 3022525 := bbase (se 3 (by rfl) ⟨566723, by rfl⟩ : syracuseStep 3022525 = 1133447) (by norm_num)
theorem B2686709 : Blo 1590994 2686709 := bbase (se 5 (by rfl) ⟨125939, by rfl⟩ : syracuseStep 2686709 = 251879) (by norm_num)
theorem B6455045 : Blo 1590994 6455045 := bbase (se 4 (by rfl) ⟨605160, by rfl⟩ : syracuseStep 6455045 = 1210321) (by norm_num)
theorem B5373701 : Blo 1590994 5373701 := bbase (se 4 (by rfl) ⟨503784, by rfl⟩ : syracuseStep 5373701 = 1007569) (by norm_num)
theorem B6045461 : Blo 1590994 6045461 := bbase (se 6 (by rfl) ⟨141690, by rfl⟩ : syracuseStep 6045461 = 283381) (by norm_num)
theorem B2015057 : Blo 1590994 2015057 := bbase (se 2 (by rfl) ⟨755646, by rfl⟩ : syracuseStep 2015057 = 1511293) (by norm_num)
theorem B20954965 : Blo 1590994 20954965 := bbase (se 9 (by rfl) ⟨61391, by rfl⟩ : syracuseStep 20954965 = 122783) (by norm_num)
theorem B3579749 : Blo 1590994 3579749 := bbase (se 4 (by rfl) ⟨335601, by rfl⟩ : syracuseStep 3579749 = 671203) (by norm_num)
theorem B2686837 : Blo 1590994 2686837 := bbase (se 5 (by rfl) ⟨125945, by rfl⟩ : syracuseStep 2686837 = 251891) (by norm_num)
theorem B2015113 : Blo 1590994 2015113 := bbase (se 2 (by rfl) ⟨755667, by rfl⟩ : syracuseStep 2015113 = 1511335) (by norm_num)
theorem B4030357 : Blo 1590994 4030357 := bbase (se 6 (by rfl) ⟨94461, by rfl⟩ : syracuseStep 4030357 = 188923) (by norm_num)
theorem B3579821 : Blo 1590994 3579821 := bbase (se 3 (by rfl) ⟨671216, by rfl⟩ : syracuseStep 3579821 = 1342433) (by norm_num)
theorem B3063725 : Blo 1590994 3063725 := bbase (se 3 (by rfl) ⟨574448, by rfl⟩ : syracuseStep 3063725 = 1148897) (by norm_num)
theorem B2686925 : Blo 1590994 2686925 := bbase (se 3 (by rfl) ⟨503798, by rfl⟩ : syracuseStep 2686925 = 1007597) (by norm_num)
theorem B2015209 : Blo 1590994 2015209 := bbase (se 2 (by rfl) ⟨755703, by rfl⟩ : syracuseStep 2015209 = 1511407) (by norm_num)
theorem B3022829 : Blo 1590994 3022829 := bbase (se 3 (by rfl) ⟨566780, by rfl⟩ : syracuseStep 3022829 = 1133561) (by norm_num)
theorem B3579893 : Blo 1590994 3579893 := bbase (se 5 (by rfl) ⟨167807, by rfl⟩ : syracuseStep 3579893 = 335615) (by norm_num)
theorem B2686979 : Blo 1590994 2686979 := bstep (se 1 (by rfl) ⟨2015234, by rfl⟩ : syracuseStep 2686979 = 4030469) B4030469
theorem B4030499 : Blo 1590994 4030499 := bstep (se 1 (by rfl) ⟨3022874, by rfl⟩ : syracuseStep 4030499 = 6045749) B6045749
theorem B1613891 : Blo 1590994 1613891 := bstep (se 1 (by rfl) ⟨1210418, by rfl⟩ : syracuseStep 1613891 = 2420837) B2420837
theorem B3981425 : Blo 1590994 3981425 := bstep (se 2 (by rfl) ⟨1493034, by rfl⟩ : syracuseStep 3981425 = 2986069) B2986069
theorem B8601713 : Blo 1590994 8601713 := bstep (se 2 (by rfl) ⟨3225642, by rfl⟩ : syracuseStep 8601713 = 6451285) B6451285
theorem B2687107 : Blo 1590994 2687107 := bstep (se 1 (by rfl) ⟨2015330, by rfl⟩ : syracuseStep 2687107 = 4030661) B4030661
theorem B2621585 : Blo 1590994 2621585 := bstep (se 2 (by rfl) ⟨983094, by rfl⟩ : syracuseStep 2621585 = 1966189) B1966189
theorem B3023011 : Blo 1590994 3023011 := bstep (se 1 (by rfl) ⟨2267258, by rfl⟩ : syracuseStep 3023011 = 4534517) B4534517
theorem B8609969 : Blo 1590994 8609969 := bstep (se 2 (by rfl) ⟨3228738, by rfl⟩ : syracuseStep 8609969 = 6457477) B6457477
theorem B2867395 : Blo 1590994 2867395 := bstep (se 1 (by rfl) ⟨2150546, by rfl⟩ : syracuseStep 2867395 = 4301093) B4301093
theorem B11477189 : Blo 1590994 11477189 := bstep (se 4 (by rfl) ⟨1075986, by rfl⟩ : syracuseStep 11477189 = 2151973) B2151973
theorem B3399889 : Blo 1590994 3399889 := bstep (se 2 (by rfl) ⟨1274958, by rfl⟩ : syracuseStep 3399889 = 2549917) B2549917
theorem B3023057 : Blo 1590994 3023057 := bstep (se 2 (by rfl) ⟨1133646, by rfl⟩ : syracuseStep 3023057 = 2267293) B2267293
theorem B3580145 : Blo 1590994 3580145 := bstep (se 2 (by rfl) ⟨1342554, by rfl⟩ : syracuseStep 3580145 = 2685109) B2685109
theorem B3580163 : Blo 1590994 3580163 := bstep (se 1 (by rfl) ⟨2685122, by rfl⟩ : syracuseStep 3580163 = 5370245) B5370245
theorem B2687249 : Blo 1590994 2687249 := bstep (se 2 (by rfl) ⟨1007718, by rfl⟩ : syracuseStep 2687249 = 2015437) B2015437
theorem B5374349 : Blo 1590994 5374349 := bstep (se 3 (by rfl) ⟨1007690, by rfl⟩ : syracuseStep 5374349 = 2015381) B2015381
theorem B2687377 : Blo 1590994 2687377 := bstep (se 2 (by rfl) ⟨1007766, by rfl⟩ : syracuseStep 2687377 = 2015533) B2015533
theorem B2687411 : Blo 1590994 2687411 := bstep (se 1 (by rfl) ⟨2015558, by rfl⟩ : syracuseStep 2687411 = 4031117) B4031117
theorem B5374403 : Blo 1590994 5374403 := bstep (se 1 (by rfl) ⟨4030802, by rfl⟩ : syracuseStep 5374403 = 8061605) B8061605
theorem B3023345 : Blo 1590994 3023345 := bstep (se 2 (by rfl) ⟨1133754, by rfl⟩ : syracuseStep 3023345 = 2267509) B2267509
theorem B2654707 : Blo 1590994 2654707 := bstep (se 1 (by rfl) ⟨1991030, by rfl⟩ : syracuseStep 2654707 = 3982061) B3982061
theorem B3580433 : Blo 1590994 3580433 := bstep (se 2 (by rfl) ⟨1342662, by rfl⟩ : syracuseStep 3580433 = 2685325) B2685325
theorem B3580451 : Blo 1590994 3580451 := bstep (se 1 (by rfl) ⟨2685338, by rfl⟩ : syracuseStep 3580451 = 5370677) B5370677
theorem B8167985 : Blo 1590994 8167985 := bstep (se 2 (by rfl) ⟨3062994, by rfl⟩ : syracuseStep 8167985 = 6125989) B6125989
theorem B2687539 : Blo 1590994 2687539 := bstep (se 1 (by rfl) ⟨2015654, by rfl⟩ : syracuseStep 2687539 = 4031309) B4031309
theorem B2015923 : Blo 1590994 2015923 := bstep (se 1 (by rfl) ⟨1511942, by rfl⟩ : syracuseStep 2015923 = 3023885) B3023885
theorem B2687681 : Blo 1590994 2687681 := bstep (se 2 (by rfl) ⟨1007880, by rfl⟩ : syracuseStep 2687681 = 2015761) B2015761
theorem B5374673 : Blo 1590994 5374673 := bstep (se 2 (by rfl) ⟨2015502, by rfl⟩ : syracuseStep 5374673 = 4031005) B4031005
theorem B3826385 : Blo 1590994 3826385 := bstep (se 2 (by rfl) ⟨1434894, by rfl⟩ : syracuseStep 3826385 = 2869789) B2869789
theorem B4301549 : Blo 1590994 4301549 := bstep (se 3 (by rfl) ⟨806540, by rfl⟩ : syracuseStep 4301549 = 1613081) B1613081
theorem B58106645 : Blo 1590994 58106645 := bstep (se 6 (by rfl) ⟨1361874, by rfl⟩ : syracuseStep 58106645 = 2723749) B2723749
theorem B2016019 : Blo 1590994 2016019 := bstep (se 1 (by rfl) ⟨1512014, by rfl⟩ : syracuseStep 2016019 = 3024029) B3024029
theorem B2548513 : Blo 1590994 2548513 := bstep (se 2 (by rfl) ⟨955692, by rfl⟩ : syracuseStep 2548513 = 1911385) B1911385
theorem B3580721 : Blo 1590994 3580721 := bstep (se 2 (by rfl) ⟨1342770, by rfl⟩ : syracuseStep 3580721 = 2685541) B2685541
theorem B17204021 : Blo 1590994 17204021 := bstep (se 5 (by rfl) ⟨806438, by rfl⟩ : syracuseStep 17204021 = 1612877) B1612877
theorem B34874165 : Blo 1590994 34874165 := bstep (se 5 (by rfl) ⟨1634726, by rfl⟩ : syracuseStep 34874165 = 3269453) B3269453
theorem B2687809 : Blo 1590994 2687809 := bstep (se 2 (by rfl) ⟨1007928, by rfl⟩ : syracuseStep 2687809 = 2015857) B2015857
theorem B3580739 : Blo 1590994 3580739 := bstep (se 1 (by rfl) ⟨2685554, by rfl⟩ : syracuseStep 3580739 = 5371109) B5371109
theorem B4596547 : Blo 1590994 4596547 := bstep (se 1 (by rfl) ⟨3447410, by rfl⟩ : syracuseStep 4596547 = 6894821) B6894821
theorem B2687843 : Blo 1590994 2687843 := bstep (se 1 (by rfl) ⟨2015882, by rfl⟩ : syracuseStep 2687843 = 4031765) B4031765
theorem B4031441 : Blo 1590994 4031441 := bstep (se 2 (by rfl) ⟨1511790, by rfl⟩ : syracuseStep 4031441 = 3023581) B3023581
theorem B38740963 : Blo 1590994 38740963 := bstep (se 1 (by rfl) ⟨29055722, by rfl⟩ : syracuseStep 38740963 = 58111445) B58111445
theorem B2687971 : Blo 1590994 2687971 := bstep (se 1 (by rfl) ⟨2015978, by rfl⟩ : syracuseStep 2687971 = 4031957) B4031957
theorem B3826673 : Blo 1590994 3826673 := bstep (se 2 (by rfl) ⟨1435002, by rfl⟩ : syracuseStep 3826673 = 2870005) B2870005
theorem B4031491 : Blo 1590994 4031491 := bstep (se 1 (by rfl) ⟨3023618, by rfl⟩ : syracuseStep 4031491 = 6047237) B6047237
theorem B10200077 : Blo 1590994 10200077 := bstep (se 3 (by rfl) ⟨1912514, by rfl⟩ : syracuseStep 10200077 = 3825029) B3825029
theorem B3228707 : Blo 1590994 3228707 := bstep (se 1 (by rfl) ⟨2421530, by rfl⟩ : syracuseStep 3228707 = 4843061) B4843061
theorem B3581009 : Blo 1590994 3581009 := bstep (se 2 (by rfl) ⟨1342878, by rfl⟩ : syracuseStep 3581009 = 2685757) B2685757
theorem B3581027 : Blo 1590994 3581027 := bstep (se 1 (by rfl) ⟨2685770, by rfl⟩ : syracuseStep 3581027 = 5371541) B5371541
theorem B2688113 : Blo 1590994 2688113 := bstep (se 2 (by rfl) ⟨1008042, by rfl⟩ : syracuseStep 2688113 = 2016085) B2016085
theorem B4031633 : Blo 1590994 4031633 := bstep (se 2 (by rfl) ⟨1511862, by rfl⟩ : syracuseStep 4031633 = 3023725) B3023725
theorem B4531373 : Blo 1590994 4531373 := bstep (se 3 (by rfl) ⟨849632, by rfl⟩ : syracuseStep 4531373 = 1699265) B1699265
theorem B3826883 : Blo 1590994 3826883 := bstep (se 1 (by rfl) ⟨2870162, by rfl⟩ : syracuseStep 3826883 = 5740325) B5740325
theorem B3024067 : Blo 1590994 3024067 := bstep (se 1 (by rfl) ⟨2268050, by rfl⟩ : syracuseStep 3024067 = 4536101) B4536101
theorem B9684173 : Blo 1590994 9684173 := bstep (se 3 (by rfl) ⟨1815782, by rfl⟩ : syracuseStep 9684173 = 3631565) B3631565
theorem B5375213 : Blo 1590994 5375213 := bstep (se 3 (by rfl) ⟨1007852, by rfl⟩ : syracuseStep 5375213 = 2015705) B2015705
theorem B10200305 : Blo 1590994 10200305 := bstep (se 2 (by rfl) ⟨3825114, by rfl⟩ : syracuseStep 10200305 = 7650229) B7650229
theorem B5375267 : Blo 1590994 5375267 := bstep (se 1 (by rfl) ⟨4031450, by rfl⟩ : syracuseStep 5375267 = 8062901) B8062901
theorem B18130229 : Blo 1590994 18130229 := bstep (se 5 (by rfl) ⟨849854, by rfl⟩ : syracuseStep 18130229 = 1699709) B1699709
theorem B4531555 : Blo 1590994 4531555 := bstep (se 1 (by rfl) ⟨3398666, by rfl⟩ : syracuseStep 4531555 = 6797333) B6797333
theorem B3581297 : Blo 1590994 3581297 := bstep (se 2 (by rfl) ⟨1342986, by rfl⟩ : syracuseStep 3581297 = 2685973) B2685973
theorem B3581315 : Blo 1590994 3581315 := bstep (se 1 (by rfl) ⟨2685986, by rfl⟩ : syracuseStep 3581315 = 5371973) B5371973
theorem B4531601 : Blo 1590994 4531601 := bstep (se 2 (by rfl) ⟨1699350, by rfl⟩ : syracuseStep 4531601 = 3398701) B3398701
theorem B5375537 : Blo 1590994 5375537 := bstep (se 2 (by rfl) ⟨2015826, by rfl⟩ : syracuseStep 5375537 = 4031653) B4031653
theorem B5449265 : Blo 1590994 5449265 := bstep (se 2 (by rfl) ⟨2043474, by rfl⟩ : syracuseStep 5449265 = 4086949) B4086949
theorem B8062577 : Blo 1590994 8062577 := bstep (se 2 (by rfl) ⟨3023466, by rfl⟩ : syracuseStep 8062577 = 6046933) B6046933
theorem B4302467 : Blo 1590994 4302467 := bstep (se 1 (by rfl) ⟨3226850, by rfl⟩ : syracuseStep 4302467 = 6453701) B6453701
theorem B3581585 : Blo 1590994 3581585 := bstep (se 2 (by rfl) ⟨1343094, by rfl⟩ : syracuseStep 3581585 = 2686189) B2686189
theorem B3581603 : Blo 1590994 3581603 := bstep (se 1 (by rfl) ⟨2686202, by rfl⟩ : syracuseStep 3581603 = 5372405) B5372405
theorem B8054477 : Blo 1590994 8054477 := bstep (se 3 (by rfl) ⟨1510214, by rfl⟩ : syracuseStep 8054477 = 3020429) B3020429
theorem B1590995 : Blo 1590994 1590995 := bstep (se 1 (by rfl) ⟨1193246, by rfl⟩ : syracuseStep 1590995 = 2386493) B2386493
theorem B1591011 : Blo 1590994 1591011 := bstep (se 1 (by rfl) ⟨1193258, by rfl⟩ : syracuseStep 1591011 = 2386517) B2386517
theorem B1591027 : Blo 1590994 1591027 := bstep (se 1 (by rfl) ⟨1193270, by rfl⟩ : syracuseStep 1591027 = 2386541) B2386541
theorem B1591043 : Blo 1590994 1591043 := bstep (se 1 (by rfl) ⟨1193282, by rfl⟩ : syracuseStep 1591043 = 2386565) B2386565
theorem B7653133 : Blo 1590994 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B1591059 : Blo 1590994 1591059 := bstep (se 1 (by rfl) ⟨1193294, by rfl⟩ : syracuseStep 1591059 = 2386589) B2386589
theorem B1591075 : Blo 1590994 1591075 := bstep (se 1 (by rfl) ⟨1193306, by rfl⟩ : syracuseStep 1591075 = 2386613) B2386613
theorem B1591091 : Blo 1590994 1591091 := bstep (se 1 (by rfl) ⟨1193318, by rfl⟩ : syracuseStep 1591091 = 2386637) B2386637
theorem B32679733 : Blo 1590994 32679733 := bstep (se 5 (by rfl) ⟨1531862, by rfl⟩ : syracuseStep 32679733 = 3063725) B3063725
theorem B1591107 : Blo 1590994 1591107 := bstep (se 1 (by rfl) ⟨1193330, by rfl⟩ : syracuseStep 1591107 = 2386661) B2386661
theorem B1591123 : Blo 1590994 1591123 := bstep (se 1 (by rfl) ⟨1193342, by rfl⟩ : syracuseStep 1591123 = 2386685) B2386685
theorem B1591139 : Blo 1590994 1591139 := bstep (se 1 (by rfl) ⟨1193354, by rfl⟩ : syracuseStep 1591139 = 2386709) B2386709
theorem B1591155 : Blo 1590994 1591155 := bstep (se 1 (by rfl) ⟨1193366, by rfl⟩ : syracuseStep 1591155 = 2386733) B2386733
theorem B1591171 : Blo 1590994 1591171 := bstep (se 1 (by rfl) ⟨1193378, by rfl⟩ : syracuseStep 1591171 = 2386757) B2386757
theorem B11470733 : Blo 1590994 11470733 := bstep (se 3 (by rfl) ⟨2150762, by rfl⟩ : syracuseStep 11470733 = 4301525) B4301525
theorem B1591187 : Blo 1590994 1591187 := bstep (se 1 (by rfl) ⟨1193390, by rfl⟩ : syracuseStep 1591187 = 2386781) B2386781
theorem B1591203 : Blo 1590994 1591203 := bstep (se 1 (by rfl) ⟨1193402, by rfl⟩ : syracuseStep 1591203 = 2386805) B2386805
theorem B3581873 : Blo 1590994 3581873 := bstep (se 2 (by rfl) ⟨1343202, by rfl⟩ : syracuseStep 3581873 = 2686405) B2686405
theorem B1591219 : Blo 1590994 1591219 := bstep (se 1 (by rfl) ⟨1193414, by rfl⟩ : syracuseStep 1591219 = 2386829) B2386829
theorem B1591235 : Blo 1590994 1591235 := bstep (se 1 (by rfl) ⟨1193426, by rfl⟩ : syracuseStep 1591235 = 2386853) B2386853
theorem B3581891 : Blo 1590994 3581891 := bstep (se 1 (by rfl) ⟨2686418, by rfl⟩ : syracuseStep 3581891 = 5372837) B5372837
theorem B6047693 : Blo 1590994 6047693 := bstep (se 3 (by rfl) ⟨1133942, by rfl⟩ : syracuseStep 6047693 = 2267885) B2267885
theorem B1591251 : Blo 1590994 1591251 := bstep (se 1 (by rfl) ⟨1193438, by rfl⟩ : syracuseStep 1591251 = 2386877) B2386877
theorem B1591267 : Blo 1590994 1591267 := bstep (se 1 (by rfl) ⟨1193450, by rfl⟩ : syracuseStep 1591267 = 2386901) B2386901
theorem B2549731 : Blo 1590994 2549731 := bstep (se 1 (by rfl) ⟨1912298, by rfl⟩ : syracuseStep 2549731 = 3824597) B3824597
theorem B3876835 : Blo 1590994 3876835 := bstep (se 1 (by rfl) ⟨2907626, by rfl⟩ : syracuseStep 3876835 = 5815253) B5815253
theorem B5736433 : Blo 1590994 5736433 := bstep (se 2 (by rfl) ⟨2151162, by rfl⟩ : syracuseStep 5736433 = 4302325) B4302325
theorem B1591283 : Blo 1590994 1591283 := bstep (se 1 (by rfl) ⟨1193462, by rfl⟩ : syracuseStep 1591283 = 2386925) B2386925
theorem B1591299 : Blo 1590994 1591299 := bstep (se 1 (by rfl) ⟨1193474, by rfl⟩ : syracuseStep 1591299 = 2386949) B2386949
theorem B1591315 : Blo 1590994 1591315 := bstep (se 1 (by rfl) ⟨1193486, by rfl⟩ : syracuseStep 1591315 = 2386973) B2386973
theorem B1591331 : Blo 1590994 1591331 := bstep (se 1 (by rfl) ⟨1193498, by rfl⟩ : syracuseStep 1591331 = 2386997) B2386997
theorem B1591347 : Blo 1590994 1591347 := bstep (se 1 (by rfl) ⟨1193510, by rfl⟩ : syracuseStep 1591347 = 2387021) B2387021
theorem B6129713 : Blo 1590994 6129713 := bstep (se 2 (by rfl) ⟨2298642, by rfl⟩ : syracuseStep 6129713 = 4597285) B4597285
theorem B3401777 : Blo 1590994 3401777 := bstep (se 2 (by rfl) ⟨1275666, by rfl⟩ : syracuseStep 3401777 = 2551333) B2551333
theorem B1591363 : Blo 1590994 1591363 := bstep (se 1 (by rfl) ⟨1193522, by rfl⟩ : syracuseStep 1591363 = 2387045) B2387045
theorem B5376077 : Blo 1590994 5376077 := bstep (se 3 (by rfl) ⟨1008014, by rfl⟩ : syracuseStep 5376077 = 2016029) B2016029
theorem B1591379 : Blo 1590994 1591379 := bstep (se 1 (by rfl) ⟨1193534, by rfl⟩ : syracuseStep 1591379 = 2387069) B2387069
theorem B1591395 : Blo 1590994 1591395 := bstep (se 1 (by rfl) ⟨1193546, by rfl⟩ : syracuseStep 1591395 = 2387093) B2387093
theorem B12085361 : Blo 1590994 12085361 := bstep (se 2 (by rfl) ⟨4532010, by rfl⟩ : syracuseStep 12085361 = 9064021) B9064021
theorem B1591411 : Blo 1590994 1591411 := bstep (se 1 (by rfl) ⟨1193558, by rfl⟩ : syracuseStep 1591411 = 2387117) B2387117
theorem B1591427 : Blo 1590994 1591427 := bstep (se 1 (by rfl) ⟨1193570, by rfl⟩ : syracuseStep 1591427 = 2387141) B2387141
theorem B5376131 : Blo 1590994 5376131 := bstep (se 1 (by rfl) ⟨4032098, by rfl⟩ : syracuseStep 5376131 = 8064197) B8064197
theorem B5097617 : Blo 1590994 5097617 := bstep (se 2 (by rfl) ⟨1911606, by rfl⟩ : syracuseStep 5097617 = 3823213) B3823213
theorem B1591443 : Blo 1590994 1591443 := bstep (se 1 (by rfl) ⟨1193582, by rfl⟩ : syracuseStep 1591443 = 2387165) B2387165
theorem B9062563 : Blo 1590994 9062563 := bstep (se 1 (by rfl) ⟨6796922, by rfl⟩ : syracuseStep 9062563 = 13593845) B13593845
theorem B1591459 : Blo 1590994 1591459 := bstep (se 1 (by rfl) ⟨1193594, by rfl⟩ : syracuseStep 1591459 = 2387189) B2387189
theorem B1591475 : Blo 1590994 1591475 := bstep (se 1 (by rfl) ⟨1193606, by rfl⟩ : syracuseStep 1591475 = 2387213) B2387213
theorem B1591491 : Blo 1590994 1591491 := bstep (se 1 (by rfl) ⟨1193618, by rfl⟩ : syracuseStep 1591491 = 2387237) B2387237
theorem B3582161 : Blo 1590994 3582161 := bstep (se 2 (by rfl) ⟨1343310, by rfl⟩ : syracuseStep 3582161 = 2686621) B2686621
theorem B1591507 : Blo 1590994 1591507 := bstep (se 1 (by rfl) ⟨1193630, by rfl⟩ : syracuseStep 1591507 = 2387261) B2387261
theorem B1591523 : Blo 1590994 1591523 := bstep (se 1 (by rfl) ⟨1193642, by rfl⟩ : syracuseStep 1591523 = 2387285) B2387285
theorem B3582179 : Blo 1590994 3582179 := bstep (se 1 (by rfl) ⟨2686634, by rfl⟩ : syracuseStep 3582179 = 5373269) B5373269
theorem B1591539 : Blo 1590994 1591539 := bstep (se 1 (by rfl) ⟨1193654, by rfl⟩ : syracuseStep 1591539 = 2387309) B2387309
theorem B1591555 : Blo 1590994 1591555 := bstep (se 1 (by rfl) ⟨1193666, by rfl⟩ : syracuseStep 1591555 = 2387333) B2387333
theorem B1591571 : Blo 1590994 1591571 := bstep (se 1 (by rfl) ⟨1193678, by rfl⟩ : syracuseStep 1591571 = 2387357) B2387357
theorem B1591587 : Blo 1590994 1591587 := bstep (se 1 (by rfl) ⟨1193690, by rfl⟩ : syracuseStep 1591587 = 2387381) B2387381
theorem B1591603 : Blo 1590994 1591603 := bstep (se 1 (by rfl) ⟨1193702, by rfl⟩ : syracuseStep 1591603 = 2387405) B2387405
theorem B1591619 : Blo 1590994 1591619 := bstep (se 1 (by rfl) ⟨1193714, by rfl⟩ : syracuseStep 1591619 = 2387429) B2387429
theorem B14518597 : Blo 1590994 14518597 := bstep (se 4 (by rfl) ⟨1361118, by rfl⟩ : syracuseStep 14518597 = 2722237) B2722237
theorem B1591635 : Blo 1590994 1591635 := bstep (se 1 (by rfl) ⟨1193726, by rfl⟩ : syracuseStep 1591635 = 2387453) B2387453
theorem B1591651 : Blo 1590994 1591651 := bstep (se 1 (by rfl) ⟨1193738, by rfl⟩ : syracuseStep 1591651 = 2387477) B2387477
theorem B1591667 : Blo 1590994 1591667 := bstep (se 1 (by rfl) ⟨1193750, by rfl⟩ : syracuseStep 1591667 = 2387501) B2387501
theorem B1591683 : Blo 1590994 1591683 := bstep (se 1 (by rfl) ⟨1193762, by rfl⟩ : syracuseStep 1591683 = 2387525) B2387525
theorem B1591699 : Blo 1590994 1591699 := bstep (se 1 (by rfl) ⟨1193774, by rfl⟩ : syracuseStep 1591699 = 2387549) B2387549
theorem B1591715 : Blo 1590994 1591715 := bstep (se 1 (by rfl) ⟨1193786, by rfl⟩ : syracuseStep 1591715 = 2387573) B2387573
theorem B1591731 : Blo 1590994 1591731 := bstep (se 1 (by rfl) ⟨1193798, by rfl⟩ : syracuseStep 1591731 = 2387597) B2387597
theorem B1591747 : Blo 1590994 1591747 := bstep (se 1 (by rfl) ⟨1193810, by rfl⟩ : syracuseStep 1591747 = 2387621) B2387621
theorem B1591763 : Blo 1590994 1591763 := bstep (se 1 (by rfl) ⟨1193822, by rfl⟩ : syracuseStep 1591763 = 2387645) B2387645
theorem B1591779 : Blo 1590994 1591779 := bstep (se 1 (by rfl) ⟨1193834, by rfl⟩ : syracuseStep 1591779 = 2387669) B2387669
theorem B3582449 : Blo 1590994 3582449 := bstep (se 2 (by rfl) ⟨1343418, by rfl⟩ : syracuseStep 3582449 = 2686837) B2686837
theorem B3631601 : Blo 1590994 3631601 := bstep (se 2 (by rfl) ⟨1361850, by rfl⟩ : syracuseStep 3631601 = 2723701) B2723701
theorem B1591795 : Blo 1590994 1591795 := bstep (se 1 (by rfl) ⟨1193846, by rfl⟩ : syracuseStep 1591795 = 2387693) B2387693
theorem B1591811 : Blo 1590994 1591811 := bstep (se 1 (by rfl) ⟨1193858, by rfl⟩ : syracuseStep 1591811 = 2387717) B2387717
theorem B4303363 : Blo 1590994 4303363 := bstep (se 1 (by rfl) ⟨3227522, by rfl⟩ : syracuseStep 4303363 = 6455045) B6455045
theorem B3582467 : Blo 1590994 3582467 := bstep (se 1 (by rfl) ⟨2686850, by rfl⟩ : syracuseStep 3582467 = 5373701) B5373701
theorem B1591827 : Blo 1590994 1591827 := bstep (se 1 (by rfl) ⟨1193870, by rfl⟩ : syracuseStep 1591827 = 2387741) B2387741
theorem B1591843 : Blo 1590994 1591843 := bstep (se 1 (by rfl) ⟨1193882, by rfl⟩ : syracuseStep 1591843 = 2387765) B2387765
theorem B1591859 : Blo 1590994 1591859 := bstep (se 1 (by rfl) ⟨1193894, by rfl⟩ : syracuseStep 1591859 = 2387789) B2387789
theorem B2386499 : Blo 1590994 2386499 := bstep (se 1 (by rfl) ⟨1789874, by rfl⟩ : syracuseStep 2386499 = 3579749) B3579749
theorem B1591875 : Blo 1590994 1591875 := bstep (se 1 (by rfl) ⟨1193906, by rfl⟩ : syracuseStep 1591875 = 2387813) B2387813
theorem B1591891 : Blo 1590994 1591891 := bstep (se 1 (by rfl) ⟨1193918, by rfl⟩ : syracuseStep 1591891 = 2387837) B2387837
theorem B2386529 : Blo 1590994 2386529 := bstep (se 2 (by rfl) ⟨894948, by rfl⟩ : syracuseStep 2386529 = 1789897) B1789897
theorem B1591907 : Blo 1590994 1591907 := bstep (se 1 (by rfl) ⟨1193930, by rfl⟩ : syracuseStep 1591907 = 2387861) B2387861
theorem B2386547 : Blo 1590994 2386547 := bstep (se 1 (by rfl) ⟨1789910, by rfl⟩ : syracuseStep 2386547 = 3579821) B3579821
theorem B1591923 : Blo 1590994 1591923 := bstep (se 1 (by rfl) ⟨1193942, by rfl⟩ : syracuseStep 1591923 = 2387885) B2387885
theorem B1591939 : Blo 1590994 1591939 := bstep (se 1 (by rfl) ⟨1193954, by rfl⟩ : syracuseStep 1591939 = 2387909) B2387909
theorem B2386577 : Blo 1590994 2386577 := bstep (se 2 (by rfl) ⟨894966, by rfl⟩ : syracuseStep 2386577 = 1789933) B1789933
theorem B1591955 : Blo 1590994 1591955 := bstep (se 1 (by rfl) ⟨1193966, by rfl⟩ : syracuseStep 1591955 = 2387933) B2387933
theorem B2386595 : Blo 1590994 2386595 := bstep (se 1 (by rfl) ⟨1789946, by rfl⟩ : syracuseStep 2386595 = 3579893) B3579893
theorem B1591971 : Blo 1590994 1591971 := bstep (se 1 (by rfl) ⟨1193978, by rfl⟩ : syracuseStep 1591971 = 2387957) B2387957
theorem B9063089 : Blo 1590994 9063089 := bstep (se 2 (by rfl) ⟨3398658, by rfl⟩ : syracuseStep 9063089 = 6797317) B6797317
theorem B2550449 : Blo 1590994 2550449 := bstep (se 2 (by rfl) ⟨956418, by rfl⟩ : syracuseStep 2550449 = 1912837) B1912837
theorem B1591987 : Blo 1590994 1591987 := bstep (se 1 (by rfl) ⟨1193990, by rfl⟩ : syracuseStep 1591987 = 2387981) B2387981
theorem B2386625 : Blo 1590994 2386625 := bstep (se 2 (by rfl) ⟨894984, by rfl⟩ : syracuseStep 2386625 = 1789969) B1789969
theorem B1592003 : Blo 1590994 1592003 := bstep (se 1 (by rfl) ⟨1194002, by rfl⟩ : syracuseStep 1592003 = 2388005) B2388005
theorem B2386643 : Blo 1590994 2386643 := bstep (se 1 (by rfl) ⟨1789982, by rfl⟩ : syracuseStep 2386643 = 3579965) B3579965
theorem B1592019 : Blo 1590994 1592019 := bstep (se 1 (by rfl) ⟨1194014, by rfl⟩ : syracuseStep 1592019 = 2388029) B2388029
theorem B1592035 : Blo 1590994 1592035 := bstep (se 1 (by rfl) ⟨1194026, by rfl⟩ : syracuseStep 1592035 = 2388053) B2388053
theorem B2386673 : Blo 1590994 2386673 := bstep (se 2 (by rfl) ⟨895002, by rfl⟩ : syracuseStep 2386673 = 1790005) B1790005
theorem B4303601 : Blo 1590994 4303601 := bstep (se 2 (by rfl) ⟨1613850, by rfl⟩ : syracuseStep 4303601 = 3227701) B3227701
theorem B1911539 : Blo 1590994 1911539 := bstep (se 1 (by rfl) ⟨1433654, by rfl⟩ : syracuseStep 1911539 = 2867309) B2867309
theorem B1592051 : Blo 1590994 1592051 := bstep (se 1 (by rfl) ⟨1194038, by rfl⟩ : syracuseStep 1592051 = 2388077) B2388077
theorem B2386691 : Blo 1590994 2386691 := bstep (se 1 (by rfl) ⟨1790018, by rfl⟩ : syracuseStep 2386691 = 3580037) B3580037
theorem B1592067 : Blo 1590994 1592067 := bstep (se 1 (by rfl) ⟨1194050, by rfl⟩ : syracuseStep 1592067 = 2388101) B2388101
theorem B3582737 : Blo 1590994 3582737 := bstep (se 2 (by rfl) ⟨1343526, by rfl⟩ : syracuseStep 3582737 = 2687053) B2687053
theorem B1592083 : Blo 1590994 1592083 := bstep (se 1 (by rfl) ⟨1194062, by rfl⟩ : syracuseStep 1592083 = 2388125) B2388125
theorem B2386721 : Blo 1590994 2386721 := bstep (se 2 (by rfl) ⟨895020, by rfl⟩ : syracuseStep 2386721 = 1790041) B1790041
theorem B1592099 : Blo 1590994 1592099 := bstep (se 1 (by rfl) ⟨1194074, by rfl⟩ : syracuseStep 1592099 = 2388149) B2388149
theorem B3582755 : Blo 1590994 3582755 := bstep (se 1 (by rfl) ⟨2687066, by rfl⟩ : syracuseStep 3582755 = 5374133) B5374133
theorem B2386739 : Blo 1590994 2386739 := bstep (se 1 (by rfl) ⟨1790054, by rfl⟩ : syracuseStep 2386739 = 3580109) B3580109
theorem B1592115 : Blo 1590994 1592115 := bstep (se 1 (by rfl) ⟨1194086, by rfl⟩ : syracuseStep 1592115 = 2388173) B2388173
theorem B5098307 : Blo 1590994 5098307 := bstep (se 1 (by rfl) ⟨3823730, by rfl⟩ : syracuseStep 5098307 = 7647461) B7647461
theorem B4533059 : Blo 1590994 4533059 := bstep (se 1 (by rfl) ⟨3399794, by rfl⟩ : syracuseStep 4533059 = 6799589) B6799589
theorem B1592131 : Blo 1590994 1592131 := bstep (se 1 (by rfl) ⟨1194098, by rfl⟩ : syracuseStep 1592131 = 2388197) B2388197
theorem B2386769 : Blo 1590994 2386769 := bstep (se 2 (by rfl) ⟨895038, by rfl⟩ : syracuseStep 2386769 = 1790077) B1790077
theorem B1592147 : Blo 1590994 1592147 := bstep (se 1 (by rfl) ⟨1194110, by rfl⟩ : syracuseStep 1592147 = 2388221) B2388221
theorem B2386787 : Blo 1590994 2386787 := bstep (se 1 (by rfl) ⟨1790090, by rfl⟩ : syracuseStep 2386787 = 3580181) B3580181
theorem B1592163 : Blo 1590994 1592163 := bstep (se 1 (by rfl) ⟨1194122, by rfl⟩ : syracuseStep 1592163 = 2388245) B2388245
theorem B6802289 : Blo 1590994 6802289 := bstep (se 2 (by rfl) ⟨2550858, by rfl⟩ : syracuseStep 6802289 = 5101717) B5101717
theorem B1592179 : Blo 1590994 1592179 := bstep (se 1 (by rfl) ⟨1194134, by rfl⟩ : syracuseStep 1592179 = 2388269) B2388269
theorem B2386817 : Blo 1590994 2386817 := bstep (se 2 (by rfl) ⟨895056, by rfl⟩ : syracuseStep 2386817 = 1790113) B1790113
theorem B1592195 : Blo 1590994 1592195 := bstep (se 1 (by rfl) ⟨1194146, by rfl⟩ : syracuseStep 1592195 = 2388293) B2388293
theorem B2386835 : Blo 1590994 2386835 := bstep (se 1 (by rfl) ⟨1790126, by rfl⟩ : syracuseStep 2386835 = 3580253) B3580253
theorem B1592211 : Blo 1590994 1592211 := bstep (se 1 (by rfl) ⟨1194158, by rfl⟩ : syracuseStep 1592211 = 2388317) B2388317
theorem B1592227 : Blo 1590994 1592227 := bstep (se 1 (by rfl) ⟨1194170, by rfl⟩ : syracuseStep 1592227 = 2388341) B2388341
theorem B2386865 : Blo 1590994 2386865 := bstep (se 2 (by rfl) ⟨895074, by rfl⟩ : syracuseStep 2386865 = 1790149) B1790149
theorem B1592243 : Blo 1590994 1592243 := bstep (se 1 (by rfl) ⟨1194182, by rfl⟩ : syracuseStep 1592243 = 2388365) B2388365
theorem B2386883 : Blo 1590994 2386883 := bstep (se 1 (by rfl) ⟨1790162, by rfl⟩ : syracuseStep 2386883 = 3580325) B3580325
theorem B1592259 : Blo 1590994 1592259 := bstep (se 1 (by rfl) ⟨1194194, by rfl⟩ : syracuseStep 1592259 = 2388389) B2388389
theorem B2550737 : Blo 1590994 2550737 := bstep (se 2 (by rfl) ⟨956526, by rfl⟩ : syracuseStep 2550737 = 1913053) B1913053
theorem B2722771 : Blo 1590994 2722771 := bstep (se 1 (by rfl) ⟨2042078, by rfl⟩ : syracuseStep 2722771 = 4084157) B4084157
theorem B1592275 : Blo 1590994 1592275 := bstep (se 1 (by rfl) ⟨1194206, by rfl⟩ : syracuseStep 1592275 = 2388413) B2388413
theorem B2386913 : Blo 1590994 2386913 := bstep (se 2 (by rfl) ⟨895092, by rfl⟩ : syracuseStep 2386913 = 1790185) B1790185
theorem B2419681 : Blo 1590994 2419681 := bstep (se 2 (by rfl) ⟨907380, by rfl⟩ : syracuseStep 2419681 = 1814761) B1814761
theorem B1592291 : Blo 1590994 1592291 := bstep (se 1 (by rfl) ⟨1194218, by rfl⟩ : syracuseStep 1592291 = 2388437) B2388437
theorem B2386931 : Blo 1590994 2386931 := bstep (se 1 (by rfl) ⟨1790198, by rfl⟩ : syracuseStep 2386931 = 3580397) B3580397
theorem B1592307 : Blo 1590994 1592307 := bstep (se 1 (by rfl) ⟨1194230, by rfl⟩ : syracuseStep 1592307 = 2388461) B2388461
theorem B1592323 : Blo 1590994 1592323 := bstep (se 1 (by rfl) ⟨1194242, by rfl⟩ : syracuseStep 1592323 = 2388485) B2388485
theorem B2386961 : Blo 1590994 2386961 := bstep (se 2 (by rfl) ⟨895110, by rfl⟩ : syracuseStep 2386961 = 1790221) B1790221
theorem B1592339 : Blo 1590994 1592339 := bstep (se 1 (by rfl) ⟨1194254, by rfl⟩ : syracuseStep 1592339 = 2388509) B2388509
theorem B2386979 : Blo 1590994 2386979 := bstep (se 1 (by rfl) ⟨1790234, by rfl⟩ : syracuseStep 2386979 = 3580469) B3580469
theorem B1592355 : Blo 1590994 1592355 := bstep (se 1 (by rfl) ⟨1194266, by rfl⟩ : syracuseStep 1592355 = 2388533) B2388533
theorem B8064035 : Blo 1590994 8064035 := bstep (se 1 (by rfl) ⟨6048026, by rfl⟩ : syracuseStep 8064035 = 12096053) B12096053
theorem B3583025 : Blo 1590994 3583025 := bstep (se 2 (by rfl) ⟨1343634, by rfl⟩ : syracuseStep 3583025 = 2687269) B2687269
theorem B1592371 : Blo 1590994 1592371 := bstep (se 1 (by rfl) ⟨1194278, by rfl⟩ : syracuseStep 1592371 = 2388557) B2388557
theorem B2387009 : Blo 1590994 2387009 := bstep (se 2 (by rfl) ⟨895128, by rfl⟩ : syracuseStep 2387009 = 1790257) B1790257
theorem B1592387 : Blo 1590994 1592387 := bstep (se 1 (by rfl) ⟨1194290, by rfl⟩ : syracuseStep 1592387 = 2388581) B2388581
theorem B3583043 : Blo 1590994 3583043 := bstep (se 1 (by rfl) ⟨2687282, by rfl⟩ : syracuseStep 3583043 = 5374565) B5374565
theorem B4197457 : Blo 1590994 4197457 := bstep (se 2 (by rfl) ⟨1574046, by rfl⟩ : syracuseStep 4197457 = 3148093) B3148093
theorem B2387027 : Blo 1590994 2387027 := bstep (se 1 (by rfl) ⟨1790270, by rfl⟩ : syracuseStep 2387027 = 3580541) B3580541
theorem B1592403 : Blo 1590994 1592403 := bstep (se 1 (by rfl) ⟨1194302, by rfl⟩ : syracuseStep 1592403 = 2388605) B2388605
theorem B1592419 : Blo 1590994 1592419 := bstep (se 1 (by rfl) ⟨1194314, by rfl⟩ : syracuseStep 1592419 = 2388629) B2388629
theorem B2387057 : Blo 1590994 2387057 := bstep (se 2 (by rfl) ⟨895146, by rfl⟩ : syracuseStep 2387057 = 1790293) B1790293
theorem B1592435 : Blo 1590994 1592435 := bstep (se 1 (by rfl) ⟨1194326, by rfl⟩ : syracuseStep 1592435 = 2388653) B2388653
theorem B2387075 : Blo 1590994 2387075 := bstep (se 1 (by rfl) ⟨1790306, by rfl⟩ : syracuseStep 2387075 = 3580613) B3580613
theorem B1592451 : Blo 1590994 1592451 := bstep (se 1 (by rfl) ⟨1194338, by rfl⟩ : syracuseStep 1592451 = 2388677) B2388677
theorem B1592467 : Blo 1590994 1592467 := bstep (se 1 (by rfl) ⟨1194350, by rfl⟩ : syracuseStep 1592467 = 2388701) B2388701
theorem B2387105 : Blo 1590994 2387105 := bstep (se 2 (by rfl) ⟨895164, by rfl⟩ : syracuseStep 2387105 = 1790329) B1790329
theorem B1592483 : Blo 1590994 1592483 := bstep (se 1 (by rfl) ⟨1194362, by rfl⟩ : syracuseStep 1592483 = 2388725) B2388725
theorem B2550961 : Blo 1590994 2550961 := bstep (se 2 (by rfl) ⟨956610, by rfl⟩ : syracuseStep 2550961 = 1913221) B1913221
theorem B2387123 : Blo 1590994 2387123 := bstep (se 1 (by rfl) ⟨1790342, by rfl⟩ : syracuseStep 2387123 = 3580685) B3580685
theorem B2297011 : Blo 1590994 2297011 := bstep (se 1 (by rfl) ⟨1722758, by rfl⟩ : syracuseStep 2297011 = 3445517) B3445517
theorem B1592499 : Blo 1590994 1592499 := bstep (se 1 (by rfl) ⟨1194374, by rfl⟩ : syracuseStep 1592499 = 2388749) B2388749
theorem B1592515 : Blo 1590994 1592515 := bstep (se 1 (by rfl) ⟨1194386, by rfl⟩ : syracuseStep 1592515 = 2388773) B2388773
theorem B2387153 : Blo 1590994 2387153 := bstep (se 2 (by rfl) ⟨895182, by rfl⟩ : syracuseStep 2387153 = 1790365) B1790365
theorem B1912019 : Blo 1590994 1912019 := bstep (se 1 (by rfl) ⟨1434014, by rfl⟩ : syracuseStep 1912019 = 2868029) B2868029
theorem B1592531 : Blo 1590994 1592531 := bstep (se 1 (by rfl) ⟨1194398, by rfl⟩ : syracuseStep 1592531 = 2388797) B2388797
theorem B2387171 : Blo 1590994 2387171 := bstep (se 1 (by rfl) ⟨1790378, by rfl⟩ : syracuseStep 2387171 = 3580757) B3580757
theorem B1592547 : Blo 1590994 1592547 := bstep (se 1 (by rfl) ⟨1194410, by rfl⟩ : syracuseStep 1592547 = 2388821) B2388821
theorem B1592563 : Blo 1590994 1592563 := bstep (se 1 (by rfl) ⟨1194422, by rfl⟩ : syracuseStep 1592563 = 2388845) B2388845
theorem B2387201 : Blo 1590994 2387201 := bstep (se 2 (by rfl) ⟨895200, by rfl⟩ : syracuseStep 2387201 = 1790401) B1790401
theorem B1592579 : Blo 1590994 1592579 := bstep (se 1 (by rfl) ⟨1194434, by rfl⟩ : syracuseStep 1592579 = 2388869) B2388869
theorem B2387219 : Blo 1590994 2387219 := bstep (se 1 (by rfl) ⟨1790414, by rfl⟩ : syracuseStep 2387219 = 3580829) B3580829
theorem B1592595 : Blo 1590994 1592595 := bstep (se 1 (by rfl) ⟨1194446, by rfl⟩ : syracuseStep 1592595 = 2388893) B2388893
theorem B1592611 : Blo 1590994 1592611 := bstep (se 1 (by rfl) ⟨1194458, by rfl⟩ : syracuseStep 1592611 = 2388917) B2388917
theorem B2387249 : Blo 1590994 2387249 := bstep (se 2 (by rfl) ⟨895218, by rfl⟩ : syracuseStep 2387249 = 1790437) B1790437
theorem B1592627 : Blo 1590994 1592627 := bstep (se 1 (by rfl) ⟨1194470, by rfl⟩ : syracuseStep 1592627 = 2388941) B2388941
theorem B2387267 : Blo 1590994 2387267 := bstep (se 1 (by rfl) ⟨1790450, by rfl⟩ : syracuseStep 2387267 = 3580901) B3580901
theorem B1592643 : Blo 1590994 1592643 := bstep (se 1 (by rfl) ⟨1194482, by rfl⟩ : syracuseStep 1592643 = 2388965) B2388965
theorem B3583313 : Blo 1590994 3583313 := bstep (se 2 (by rfl) ⟨1343742, by rfl⟩ : syracuseStep 3583313 = 2687485) B2687485
theorem B1592659 : Blo 1590994 1592659 := bstep (se 1 (by rfl) ⟨1194494, by rfl⟩ : syracuseStep 1592659 = 2388989) B2388989
theorem B2387297 : Blo 1590994 2387297 := bstep (se 2 (by rfl) ⟨895236, by rfl⟩ : syracuseStep 2387297 = 1790473) B1790473
theorem B3583331 : Blo 1590994 3583331 := bstep (se 1 (by rfl) ⟨2687498, by rfl⟩ : syracuseStep 3583331 = 5374997) B5374997
theorem B1592675 : Blo 1590994 1592675 := bstep (se 1 (by rfl) ⟨1194506, by rfl⟩ : syracuseStep 1592675 = 2389013) B2389013
theorem B2387315 : Blo 1590994 2387315 := bstep (se 1 (by rfl) ⟨1790486, by rfl⟩ : syracuseStep 2387315 = 3580973) B3580973
theorem B1592691 : Blo 1590994 1592691 := bstep (se 1 (by rfl) ⟨1194518, by rfl⟩ : syracuseStep 1592691 = 2389037) B2389037
theorem B1592707 : Blo 1590994 1592707 := bstep (se 1 (by rfl) ⟨1194530, by rfl⟩ : syracuseStep 1592707 = 2389061) B2389061
theorem B2387345 : Blo 1590994 2387345 := bstep (se 2 (by rfl) ⟨895254, by rfl⟩ : syracuseStep 2387345 = 1790509) B1790509
theorem B1592723 : Blo 1590994 1592723 := bstep (se 1 (by rfl) ⟨1194542, by rfl⟩ : syracuseStep 1592723 = 2389085) B2389085
theorem B2387363 : Blo 1590994 2387363 := bstep (se 1 (by rfl) ⟨1790522, by rfl⟩ : syracuseStep 2387363 = 3581045) B3581045
theorem B5737891 : Blo 1590994 5737891 := bstep (se 1 (by rfl) ⟨4303418, by rfl⟩ : syracuseStep 5737891 = 8606837) B8606837
theorem B1592739 : Blo 1590994 1592739 := bstep (se 1 (by rfl) ⟨1194554, by rfl⟩ : syracuseStep 1592739 = 2389109) B2389109
theorem B2583985 : Blo 1590994 2583985 := bstep (se 2 (by rfl) ⟨968994, by rfl⟩ : syracuseStep 2583985 = 1937989) B1937989
theorem B1592755 : Blo 1590994 1592755 := bstep (se 1 (by rfl) ⟨1194566, by rfl⟩ : syracuseStep 1592755 = 2389133) B2389133
theorem B2387393 : Blo 1590994 2387393 := bstep (se 2 (by rfl) ⟨895272, by rfl⟩ : syracuseStep 2387393 = 1790545) B1790545
theorem B1592771 : Blo 1590994 1592771 := bstep (se 1 (by rfl) ⟨1194578, by rfl⟩ : syracuseStep 1592771 = 2389157) B2389157
theorem B2387411 : Blo 1590994 2387411 := bstep (se 1 (by rfl) ⟨1790558, by rfl⟩ : syracuseStep 2387411 = 3581117) B3581117
theorem B1592787 : Blo 1590994 1592787 := bstep (se 1 (by rfl) ⟨1194590, by rfl⟩ : syracuseStep 1592787 = 2389181) B2389181
theorem B1592803 : Blo 1590994 1592803 := bstep (se 1 (by rfl) ⟨1194602, by rfl⟩ : syracuseStep 1592803 = 2389205) B2389205
theorem B2387441 : Blo 1590994 2387441 := bstep (se 2 (by rfl) ⟨895290, by rfl⟩ : syracuseStep 2387441 = 1790581) B1790581
theorem B1592819 : Blo 1590994 1592819 := bstep (se 1 (by rfl) ⟨1194614, by rfl⟩ : syracuseStep 1592819 = 2389229) B2389229
theorem B2387459 : Blo 1590994 2387459 := bstep (se 1 (by rfl) ⟨1790594, by rfl⟩ : syracuseStep 2387459 = 3581189) B3581189
theorem B1592835 : Blo 1590994 1592835 := bstep (se 1 (by rfl) ⟨1194626, by rfl⟩ : syracuseStep 1592835 = 2389253) B2389253
theorem B6041101 : Blo 1590994 6041101 := bstep (se 3 (by rfl) ⟨1132706, by rfl⟩ : syracuseStep 6041101 = 2265413) B2265413
theorem B1592851 : Blo 1590994 1592851 := bstep (se 1 (by rfl) ⟨1194638, by rfl⟩ : syracuseStep 1592851 = 2389277) B2389277
theorem B2387489 : Blo 1590994 2387489 := bstep (se 2 (by rfl) ⟨895308, by rfl⟩ : syracuseStep 2387489 = 1790617) B1790617
theorem B1592867 : Blo 1590994 1592867 := bstep (se 1 (by rfl) ⟨1194650, by rfl⟩ : syracuseStep 1592867 = 2389301) B2389301
theorem B2387507 : Blo 1590994 2387507 := bstep (se 1 (by rfl) ⟨1790630, by rfl⟩ : syracuseStep 2387507 = 3581261) B3581261
theorem B1592883 : Blo 1590994 1592883 := bstep (se 1 (by rfl) ⟨1194662, by rfl⟩ : syracuseStep 1592883 = 2389325) B2389325
theorem B1592899 : Blo 1590994 1592899 := bstep (se 1 (by rfl) ⟨1194674, by rfl⟩ : syracuseStep 1592899 = 2389349) B2389349
theorem B2387537 : Blo 1590994 2387537 := bstep (se 2 (by rfl) ⟨895326, by rfl⟩ : syracuseStep 2387537 = 1790653) B1790653
theorem B1592915 : Blo 1590994 1592915 := bstep (se 1 (by rfl) ⟨1194686, by rfl⟩ : syracuseStep 1592915 = 2389373) B2389373
theorem B2387555 : Blo 1590994 2387555 := bstep (se 1 (by rfl) ⟨1790666, by rfl⟩ : syracuseStep 2387555 = 3581333) B3581333
theorem B1592931 : Blo 1590994 1592931 := bstep (se 1 (by rfl) ⟨1194698, by rfl⟩ : syracuseStep 1592931 = 2389397) B2389397
theorem B3583601 : Blo 1590994 3583601 := bstep (se 2 (by rfl) ⟨1343850, by rfl⟩ : syracuseStep 3583601 = 2687701) B2687701
theorem B1592947 : Blo 1590994 1592947 := bstep (se 1 (by rfl) ⟨1194710, by rfl⟩ : syracuseStep 1592947 = 2389421) B2389421
theorem B2387585 : Blo 1590994 2387585 := bstep (se 2 (by rfl) ⟨895344, by rfl⟩ : syracuseStep 2387585 = 1790689) B1790689
theorem B3583619 : Blo 1590994 3583619 := bstep (se 1 (by rfl) ⟨2687714, by rfl⟩ : syracuseStep 3583619 = 5375429) B5375429
theorem B1592963 : Blo 1590994 1592963 := bstep (se 1 (by rfl) ⟨1194722, by rfl⟩ : syracuseStep 1592963 = 2389445) B2389445
theorem B9072269 : Blo 1590994 9072269 := bstep (se 3 (by rfl) ⟨1701050, by rfl⟩ : syracuseStep 9072269 = 3402101) B3402101
theorem B2387603 : Blo 1590994 2387603 := bstep (se 1 (by rfl) ⟨1790702, by rfl⟩ : syracuseStep 2387603 = 3581405) B3581405
theorem B1592979 : Blo 1590994 1592979 := bstep (se 1 (by rfl) ⟨1194734, by rfl⟩ : syracuseStep 1592979 = 2389469) B2389469
theorem B2387633 : Blo 1590994 2387633 := bstep (se 2 (by rfl) ⟨895362, by rfl⟩ : syracuseStep 2387633 = 1790725) B1790725
theorem B2387651 : Blo 1590994 2387651 := bstep (se 1 (by rfl) ⟨1790738, by rfl⟩ : syracuseStep 2387651 = 3581477) B3581477
theorem B2387681 : Blo 1590994 2387681 := bstep (se 2 (by rfl) ⟨895380, by rfl⟩ : syracuseStep 2387681 = 1790761) B1790761
theorem B2297569 : Blo 1590994 2297569 := bstep (se 2 (by rfl) ⟨861588, by rfl⟩ : syracuseStep 2297569 = 1723177) B1723177
theorem B2387699 : Blo 1590994 2387699 := bstep (se 1 (by rfl) ⟨1790774, by rfl⟩ : syracuseStep 2387699 = 3581549) B3581549
theorem B2387729 : Blo 1590994 2387729 := bstep (se 2 (by rfl) ⟨895398, by rfl⟩ : syracuseStep 2387729 = 1790797) B1790797
theorem B2387747 : Blo 1590994 2387747 := bstep (se 1 (by rfl) ⟨1790810, by rfl⟩ : syracuseStep 2387747 = 3581621) B3581621
theorem B2387777 : Blo 1590994 2387777 := bstep (se 2 (by rfl) ⟨895416, by rfl⟩ : syracuseStep 2387777 = 1790833) B1790833
theorem B2387795 : Blo 1590994 2387795 := bstep (se 1 (by rfl) ⟨1790846, by rfl⟩ : syracuseStep 2387795 = 3581693) B3581693
theorem B2387825 : Blo 1590994 2387825 := bstep (se 2 (by rfl) ⟨895434, by rfl⟩ : syracuseStep 2387825 = 1790869) B1790869
theorem B29060977 : Blo 1590994 29060977 := bstep (se 2 (by rfl) ⟨10897866, by rfl⟩ : syracuseStep 29060977 = 21795733) B21795733
theorem B2387843 : Blo 1590994 2387843 := bstep (se 1 (by rfl) ⟨1790882, by rfl⟩ : syracuseStep 2387843 = 3581765) B3581765
theorem B3583889 : Blo 1590994 3583889 := bstep (se 2 (by rfl) ⟨1343958, by rfl⟩ : syracuseStep 3583889 = 2687917) B2687917
theorem B2387873 : Blo 1590994 2387873 := bstep (se 2 (by rfl) ⟨895452, by rfl⟩ : syracuseStep 2387873 = 1790905) B1790905
theorem B3583907 : Blo 1590994 3583907 := bstep (se 1 (by rfl) ⟨2687930, by rfl⟩ : syracuseStep 3583907 = 5375861) B5375861
theorem B2387891 : Blo 1590994 2387891 := bstep (se 1 (by rfl) ⟨1790918, by rfl⟩ : syracuseStep 2387891 = 3581837) B3581837
theorem B2387921 : Blo 1590994 2387921 := bstep (se 2 (by rfl) ⟨895470, by rfl⟩ : syracuseStep 2387921 = 1790941) B1790941
theorem B1699795 : Blo 1590994 1699795 := bstep (se 1 (by rfl) ⟨1274846, by rfl⟩ : syracuseStep 1699795 = 2549693) B2549693
theorem B2387939 : Blo 1590994 2387939 := bstep (se 1 (by rfl) ⟨1790954, by rfl⟩ : syracuseStep 2387939 = 3581909) B3581909
theorem B2387969 : Blo 1590994 2387969 := bstep (se 2 (by rfl) ⟨895488, by rfl⟩ : syracuseStep 2387969 = 1790977) B1790977
theorem B4534289 : Blo 1590994 4534289 := bstep (se 2 (by rfl) ⟨1700358, by rfl⟩ : syracuseStep 4534289 = 3400717) B3400717
theorem B2387987 : Blo 1590994 2387987 := bstep (se 1 (by rfl) ⟨1790990, by rfl⟩ : syracuseStep 2387987 = 3581981) B3581981
theorem B1789987 : Blo 1590994 1789987 := bstep (se 1 (by rfl) ⟨1342490, by rfl⟩ : syracuseStep 1789987 = 2684981) B2684981
theorem B2388017 : Blo 1590994 2388017 := bstep (se 2 (by rfl) ⟨895506, by rfl⟩ : syracuseStep 2388017 = 1791013) B1791013
theorem B2388035 : Blo 1590994 2388035 := bstep (se 1 (by rfl) ⟨1791026, by rfl⟩ : syracuseStep 2388035 = 3582053) B3582053
theorem B2388065 : Blo 1590994 2388065 := bstep (se 2 (by rfl) ⟨895524, by rfl⟩ : syracuseStep 2388065 = 1791049) B1791049
theorem B9064547 : Blo 1590994 9064547 := bstep (se 1 (by rfl) ⟨6798410, by rfl⟩ : syracuseStep 9064547 = 13596821) B13596821
theorem B2388083 : Blo 1590994 2388083 := bstep (se 1 (by rfl) ⟨1791062, by rfl⟩ : syracuseStep 2388083 = 3582125) B3582125
theorem B2388113 : Blo 1590994 2388113 := bstep (se 2 (by rfl) ⟨895542, by rfl⟩ : syracuseStep 2388113 = 1791085) B1791085
theorem B2388131 : Blo 1590994 2388131 := bstep (se 1 (by rfl) ⟨1791098, by rfl⟩ : syracuseStep 2388131 = 3582197) B3582197
theorem B5370029 : Blo 1590994 5370029 := bstep (se 3 (by rfl) ⟨1006880, by rfl⟩ : syracuseStep 5370029 = 2013761) B2013761
theorem B3584177 : Blo 1590994 3584177 := bstep (se 2 (by rfl) ⟨1344066, by rfl⟩ : syracuseStep 3584177 = 2688133) B2688133
theorem B1790131 : Blo 1590994 1790131 := bstep (se 1 (by rfl) ⟨1342598, by rfl⟩ : syracuseStep 1790131 = 2685197) B2685197
theorem B2388161 : Blo 1590994 2388161 := bstep (se 2 (by rfl) ⟨895560, by rfl⟩ : syracuseStep 2388161 = 1791121) B1791121
theorem B3584195 : Blo 1590994 3584195 := bstep (se 1 (by rfl) ⟨2688146, by rfl⟩ : syracuseStep 3584195 = 5376293) B5376293
theorem B2388179 : Blo 1590994 2388179 := bstep (se 1 (by rfl) ⟨1791134, by rfl⟩ : syracuseStep 2388179 = 3582269) B3582269
theorem B102133973 : Blo 1590994 102133973 := bstep (se 7 (by rfl) ⟨1196882, by rfl⟩ : syracuseStep 102133973 = 2393765) B2393765
theorem B5370083 : Blo 1590994 5370083 := bstep (se 1 (by rfl) ⟨4027562, by rfl⟩ : syracuseStep 5370083 = 8055125) B8055125
theorem B6123761 : Blo 1590994 6123761 := bstep (se 2 (by rfl) ⟨2296410, by rfl⟩ : syracuseStep 6123761 = 4592821) B4592821
theorem B2388209 : Blo 1590994 2388209 := bstep (se 2 (by rfl) ⟨895578, by rfl⟩ : syracuseStep 2388209 = 1791157) B1791157
theorem B2388227 : Blo 1590994 2388227 := bstep (se 1 (by rfl) ⟨1791170, by rfl⟩ : syracuseStep 2388227 = 3582341) B3582341
theorem B2388257 : Blo 1590994 2388257 := bstep (se 2 (by rfl) ⟨895596, by rfl⟩ : syracuseStep 2388257 = 1791193) B1791193
theorem B6041891 : Blo 1590994 6041891 := bstep (se 1 (by rfl) ⟨4531418, by rfl⟩ : syracuseStep 6041891 = 9062837) B9062837
theorem B2388275 : Blo 1590994 2388275 := bstep (se 1 (by rfl) ⟨1791206, by rfl⟩ : syracuseStep 2388275 = 3582413) B3582413
theorem B1790275 : Blo 1590994 1790275 := bstep (se 1 (by rfl) ⟨1342706, by rfl⟩ : syracuseStep 1790275 = 2685413) B2685413
theorem B2388305 : Blo 1590994 2388305 := bstep (se 2 (by rfl) ⟨895614, by rfl⟩ : syracuseStep 2388305 = 1791229) B1791229
theorem B2388323 : Blo 1590994 2388323 := bstep (se 1 (by rfl) ⟨1791242, by rfl⟩ : syracuseStep 2388323 = 3582485) B3582485
theorem B27201905 : Blo 1590994 27201905 := bstep (se 2 (by rfl) ⟨10200714, by rfl⟩ : syracuseStep 27201905 = 20401429) B20401429
theorem B1814899 : Blo 1590994 1814899 := bstep (se 1 (by rfl) ⟨1361174, by rfl⟩ : syracuseStep 1814899 = 2722349) B2722349
theorem B2388353 : Blo 1590994 2388353 := bstep (se 2 (by rfl) ⟨895632, by rfl⟩ : syracuseStep 2388353 = 1791265) B1791265
theorem B2388371 : Blo 1590994 2388371 := bstep (se 1 (by rfl) ⟨1791278, by rfl⟩ : syracuseStep 2388371 = 3582557) B3582557
theorem B2388401 : Blo 1590994 2388401 := bstep (se 2 (by rfl) ⟨895650, by rfl⟩ : syracuseStep 2388401 = 1791301) B1791301
theorem B2388419 : Blo 1590994 2388419 := bstep (se 1 (by rfl) ⟨1791314, by rfl⟩ : syracuseStep 2388419 = 3582629) B3582629
theorem B1790419 : Blo 1590994 1790419 := bstep (se 1 (by rfl) ⟨1342814, by rfl⟩ : syracuseStep 1790419 = 2685629) B2685629
theorem B2388449 : Blo 1590994 2388449 := bstep (se 2 (by rfl) ⟨895668, by rfl⟩ : syracuseStep 2388449 = 1791337) B1791337
theorem B5370353 : Blo 1590994 5370353 := bstep (se 2 (by rfl) ⟨2013882, by rfl⟩ : syracuseStep 5370353 = 4027765) B4027765
theorem B2388467 : Blo 1590994 2388467 := bstep (se 1 (by rfl) ⟨1791350, by rfl⟩ : syracuseStep 2388467 = 3582701) B3582701
theorem B2388497 : Blo 1590994 2388497 := bstep (se 2 (by rfl) ⟨895686, by rfl⟩ : syracuseStep 2388497 = 1791373) B1791373
theorem B2388515 : Blo 1590994 2388515 := bstep (se 1 (by rfl) ⟨1791386, by rfl⟩ : syracuseStep 2388515 = 3582773) B3582773
theorem B5100077 : Blo 1590994 5100077 := bstep (se 3 (by rfl) ⟨956264, by rfl⟩ : syracuseStep 5100077 = 1912529) B1912529
theorem B8057393 : Blo 1590994 8057393 := bstep (se 2 (by rfl) ⟨3021522, by rfl⟩ : syracuseStep 8057393 = 6043045) B6043045
theorem B2388545 : Blo 1590994 2388545 := bstep (se 2 (by rfl) ⟨895704, by rfl⟩ : syracuseStep 2388545 = 1791409) B1791409
theorem B2388563 : Blo 1590994 2388563 := bstep (se 1 (by rfl) ⟨1791422, by rfl⟩ : syracuseStep 2388563 = 3582845) B3582845
theorem B1790563 : Blo 1590994 1790563 := bstep (se 1 (by rfl) ⟨1342922, by rfl⟩ : syracuseStep 1790563 = 2685845) B2685845
theorem B2388593 : Blo 1590994 2388593 := bstep (se 2 (by rfl) ⟨895722, by rfl⟩ : syracuseStep 2388593 = 1791445) B1791445
theorem B2388611 : Blo 1590994 2388611 := bstep (se 1 (by rfl) ⟨1791458, by rfl⟩ : syracuseStep 2388611 = 3582917) B3582917
theorem B2388641 : Blo 1590994 2388641 := bstep (se 2 (by rfl) ⟨895740, by rfl⟩ : syracuseStep 2388641 = 1791481) B1791481
theorem B5100205 : Blo 1590994 5100205 := bstep (se 3 (by rfl) ⟨956288, by rfl⟩ : syracuseStep 5100205 = 1912577) B1912577
theorem B4305581 : Blo 1590994 4305581 := bstep (se 3 (by rfl) ⟨807296, by rfl⟩ : syracuseStep 4305581 = 1614593) B1614593
theorem B2388659 : Blo 1590994 2388659 := bstep (se 1 (by rfl) ⟨1791494, by rfl⟩ : syracuseStep 2388659 = 3582989) B3582989
theorem B18141893 : Blo 1590994 18141893 := bstep (se 4 (by rfl) ⟨1700802, by rfl⟩ : syracuseStep 18141893 = 3401605) B3401605
theorem B2388689 : Blo 1590994 2388689 := bstep (se 2 (by rfl) ⟨895758, by rfl⟩ : syracuseStep 2388689 = 1791517) B1791517
theorem B2388707 : Blo 1590994 2388707 := bstep (se 1 (by rfl) ⟨1791530, by rfl⟩ : syracuseStep 2388707 = 3583061) B3583061
theorem B1790707 : Blo 1590994 1790707 := bstep (se 1 (by rfl) ⟨1343030, by rfl⟩ : syracuseStep 1790707 = 2686061) B2686061
theorem B2388737 : Blo 1590994 2388737 := bstep (se 2 (by rfl) ⟨895776, by rfl⟩ : syracuseStep 2388737 = 1791553) B1791553
theorem B2388755 : Blo 1590994 2388755 := bstep (se 1 (by rfl) ⟨1791566, by rfl⟩ : syracuseStep 2388755 = 3583133) B3583133
theorem B2388785 : Blo 1590994 2388785 := bstep (se 2 (by rfl) ⟨895794, by rfl⟩ : syracuseStep 2388785 = 1791589) B1791589
theorem B2388803 : Blo 1590994 2388803 := bstep (se 1 (by rfl) ⟨1791602, by rfl⟩ : syracuseStep 2388803 = 3583205) B3583205
theorem B2388833 : Blo 1590994 2388833 := bstep (se 2 (by rfl) ⟨895812, by rfl⟩ : syracuseStep 2388833 = 1791625) B1791625
theorem B2151281 : Blo 1590994 2151281 := bstep (se 2 (by rfl) ⟨806730, by rfl⟩ : syracuseStep 2151281 = 1613461) B1613461
theorem B2388851 : Blo 1590994 2388851 := bstep (se 1 (by rfl) ⟨1791638, by rfl⟩ : syracuseStep 2388851 = 3583277) B3583277
theorem B1790851 : Blo 1590994 1790851 := bstep (se 1 (by rfl) ⟨1343138, by rfl⟩ : syracuseStep 1790851 = 2686277) B2686277
theorem B2388881 : Blo 1590994 2388881 := bstep (se 2 (by rfl) ⟨895830, by rfl⟩ : syracuseStep 2388881 = 1791661) B1791661
theorem B2388899 : Blo 1590994 2388899 := bstep (se 1 (by rfl) ⟨1791674, by rfl⟩ : syracuseStep 2388899 = 3583349) B3583349
theorem B5100461 : Blo 1590994 5100461 := bstep (se 3 (by rfl) ⟨956336, by rfl⟩ : syracuseStep 5100461 = 1912673) B1912673
theorem B6042545 : Blo 1590994 6042545 := bstep (se 2 (by rfl) ⟨2265954, by rfl⟩ : syracuseStep 6042545 = 4531909) B4531909
theorem B2388929 : Blo 1590994 2388929 := bstep (se 2 (by rfl) ⟨895848, by rfl⟩ : syracuseStep 2388929 = 1791697) B1791697
theorem B2266051 : Blo 1590994 2266051 := bstep (se 1 (by rfl) ⟨1699538, by rfl⟩ : syracuseStep 2266051 = 3399077) B3399077
theorem B1815491 : Blo 1590994 1815491 := bstep (se 1 (by rfl) ⟨1361618, by rfl⟩ : syracuseStep 1815491 = 2723237) B2723237
theorem B2388947 : Blo 1590994 2388947 := bstep (se 1 (by rfl) ⟨1791710, by rfl⟩ : syracuseStep 2388947 = 3583421) B3583421
theorem B2388977 : Blo 1590994 2388977 := bstep (se 2 (by rfl) ⟨895866, by rfl⟩ : syracuseStep 2388977 = 1791733) B1791733
theorem B2388995 : Blo 1590994 2388995 := bstep (se 1 (by rfl) ⟨1791746, by rfl⟩ : syracuseStep 2388995 = 3583493) B3583493
theorem B5370893 : Blo 1590994 5370893 := bstep (se 3 (by rfl) ⟨1007042, by rfl⟩ : syracuseStep 5370893 = 2014085) B2014085
theorem B1790995 : Blo 1590994 1790995 := bstep (se 1 (by rfl) ⟨1343246, by rfl⟩ : syracuseStep 1790995 = 2686493) B2686493
theorem B2389025 : Blo 1590994 2389025 := bstep (se 2 (by rfl) ⟨895884, by rfl⟩ : syracuseStep 2389025 = 1791769) B1791769
theorem B4027441 : Blo 1590994 4027441 := bstep (se 2 (by rfl) ⟨1510290, by rfl⟩ : syracuseStep 4027441 = 3020581) B3020581
theorem B2389043 : Blo 1590994 2389043 := bstep (se 1 (by rfl) ⟨1791782, by rfl⟩ : syracuseStep 2389043 = 3583565) B3583565
theorem B5370947 : Blo 1590994 5370947 := bstep (se 1 (by rfl) ⟨4028210, by rfl⟩ : syracuseStep 5370947 = 8056421) B8056421
theorem B2389073 : Blo 1590994 2389073 := bstep (se 2 (by rfl) ⟨895902, by rfl⟩ : syracuseStep 2389073 = 1791805) B1791805
theorem B2389091 : Blo 1590994 2389091 := bstep (se 1 (by rfl) ⟨1791818, by rfl⟩ : syracuseStep 2389091 = 3583637) B3583637
theorem B27939953 : Blo 1590994 27939953 := bstep (se 2 (by rfl) ⟨10477482, by rfl⟩ : syracuseStep 27939953 = 20954965) B20954965
theorem B2389121 : Blo 1590994 2389121 := bstep (se 2 (by rfl) ⟨895920, by rfl⟩ : syracuseStep 2389121 = 1791841) B1791841
theorem B2389139 : Blo 1590994 2389139 := bstep (se 1 (by rfl) ⟨1791854, by rfl⟩ : syracuseStep 2389139 = 3583709) B3583709
theorem B1791139 : Blo 1590994 1791139 := bstep (se 1 (by rfl) ⟨1343354, by rfl⟩ : syracuseStep 1791139 = 2686709) B2686709
theorem B2389169 : Blo 1590994 2389169 := bstep (se 2 (by rfl) ⟨895938, by rfl⟩ : syracuseStep 2389169 = 1791877) B1791877
theorem B2389187 : Blo 1590994 2389187 := bstep (se 1 (by rfl) ⟨1791890, by rfl⟩ : syracuseStep 2389187 = 3583781) B3583781
theorem B1701059 : Blo 1590994 1701059 := bstep (se 1 (by rfl) ⟨1275794, by rfl⟩ : syracuseStep 1701059 = 2551589) B2551589
theorem B2389217 : Blo 1590994 2389217 := bstep (se 2 (by rfl) ⟨895956, by rfl⟩ : syracuseStep 2389217 = 1791913) B1791913
theorem B2389235 : Blo 1590994 2389235 := bstep (se 1 (by rfl) ⟨1791926, by rfl⟩ : syracuseStep 2389235 = 3583853) B3583853
theorem B2389265 : Blo 1590994 2389265 := bstep (se 2 (by rfl) ⟨895974, by rfl⟩ : syracuseStep 2389265 = 1791949) B1791949
theorem B2389283 : Blo 1590994 2389283 := bstep (se 1 (by rfl) ⟨1791962, by rfl⟩ : syracuseStep 2389283 = 3583925) B3583925
theorem B1791283 : Blo 1590994 1791283 := bstep (se 1 (by rfl) ⟨1343462, by rfl⟩ : syracuseStep 1791283 = 2686925) B2686925
theorem B2389313 : Blo 1590994 2389313 := bstep (se 2 (by rfl) ⟨895992, by rfl⟩ : syracuseStep 2389313 = 1791985) B1791985
theorem B4027715 : Blo 1590994 4027715 := bstep (se 1 (by rfl) ⟨3020786, by rfl⟩ : syracuseStep 4027715 = 6041573) B6041573
theorem B5371217 : Blo 1590994 5371217 := bstep (se 2 (by rfl) ⟨2014206, by rfl⟩ : syracuseStep 5371217 = 4028413) B4028413
theorem B2389331 : Blo 1590994 2389331 := bstep (se 1 (by rfl) ⟨1791998, by rfl⟩ : syracuseStep 2389331 = 3583997) B3583997
theorem B2389361 : Blo 1590994 2389361 := bstep (se 2 (by rfl) ⟨896010, by rfl⟩ : syracuseStep 2389361 = 1792021) B1792021
theorem B2389379 : Blo 1590994 2389379 := bstep (se 1 (by rfl) ⟨1792034, by rfl⟩ : syracuseStep 2389379 = 3584069) B3584069
theorem B2389409 : Blo 1590994 2389409 := bstep (se 2 (by rfl) ⟨896028, by rfl⟩ : syracuseStep 2389409 = 1792057) B1792057
theorem B10196387 : Blo 1590994 10196387 := bstep (se 1 (by rfl) ⟨7647290, by rfl⟩ : syracuseStep 10196387 = 15294581) B15294581
theorem B2389427 : Blo 1590994 2389427 := bstep (se 1 (by rfl) ⟨1792070, by rfl⟩ : syracuseStep 2389427 = 3584141) B3584141
theorem B1791427 : Blo 1590994 1791427 := bstep (se 1 (by rfl) ⟨1343570, by rfl⟩ : syracuseStep 1791427 = 2687141) B2687141
theorem B4535747 : Blo 1590994 4535747 := bstep (se 1 (by rfl) ⟨3401810, by rfl⟩ : syracuseStep 4535747 = 6803621) B6803621
theorem B2389457 : Blo 1590994 2389457 := bstep (se 2 (by rfl) ⟨896046, by rfl⟩ : syracuseStep 2389457 = 1792093) B1792093
theorem B7263715 : Blo 1590994 7263715 := bstep (se 1 (by rfl) ⟨5447786, by rfl⟩ : syracuseStep 7263715 = 10895573) B10895573
theorem B2389475 : Blo 1590994 2389475 := bstep (se 1 (by rfl) ⟨1792106, by rfl⟩ : syracuseStep 2389475 = 3584213) B3584213
theorem B4027907 : Blo 1590994 4027907 := bstep (se 1 (by rfl) ⟨3020930, by rfl⟩ : syracuseStep 4027907 = 6041861) B6041861
theorem B69760565 : Blo 1590994 69760565 := bstep (se 5 (by rfl) ⟨3270026, by rfl⟩ : syracuseStep 69760565 = 6540053) B6540053
theorem B1791571 : Blo 1590994 1791571 := bstep (se 1 (by rfl) ⟨1343678, by rfl⟩ : syracuseStep 1791571 = 2687357) B2687357
theorem B3020483 : Blo 1590994 3020483 := bstep (se 1 (by rfl) ⟨2265362, by rfl⟩ : syracuseStep 3020483 = 4530725) B4530725
theorem B8165069 : Blo 1590994 8165069 := bstep (se 3 (by rfl) ⟨1530950, by rfl⟩ : syracuseStep 8165069 = 3061901) B3061901
theorem B1791715 : Blo 1590994 1791715 := bstep (se 1 (by rfl) ⟨1343786, by rfl⟩ : syracuseStep 1791715 = 2687573) B2687573
theorem B5371757 : Blo 1590994 5371757 := bstep (se 3 (by rfl) ⟨1007204, by rfl⟩ : syracuseStep 5371757 = 2014409) B2014409
theorem B1791859 : Blo 1590994 1791859 := bstep (se 1 (by rfl) ⟨1343894, by rfl⟩ : syracuseStep 1791859 = 2687789) B2687789
theorem B4085635 : Blo 1590994 4085635 := bstep (se 1 (by rfl) ⟨3064226, by rfl⟩ : syracuseStep 4085635 = 6128453) B6128453
theorem B2684819 : Blo 1590994 2684819 := bstep (se 1 (by rfl) ⟨2013614, by rfl⟩ : syracuseStep 2684819 = 4027229) B4027229
theorem B5371811 : Blo 1590994 5371811 := bstep (se 1 (by rfl) ⟨4028858, by rfl⟩ : syracuseStep 5371811 = 8057717) B8057717
theorem B9066437 : Blo 1590994 9066437 := bstep (se 4 (by rfl) ⟨849978, by rfl⟩ : syracuseStep 9066437 = 1699957) B1699957
theorem B8058851 : Blo 1590994 8058851 := bstep (se 1 (by rfl) ⟨6044138, by rfl⟩ : syracuseStep 8058851 = 12088277) B12088277
theorem B1792003 : Blo 1590994 1792003 := bstep (se 1 (by rfl) ⟨1344002, by rfl⟩ : syracuseStep 1792003 = 2688005) B2688005
theorem B2684947 : Blo 1590994 2684947 := bstep (se 1 (by rfl) ⟨2013710, by rfl⟩ : syracuseStep 2684947 = 4027421) B4027421
theorem B2267185 : Blo 1590994 2267185 := bstep (se 2 (by rfl) ⟨850194, by rfl⟩ : syracuseStep 2267185 = 1700389) B1700389
theorem B2267281 : Blo 1590994 2267281 := bstep (se 2 (by rfl) ⟨850230, by rfl⟩ : syracuseStep 2267281 = 1700461) B1700461
theorem B2685089 : Blo 1590994 2685089 := bstep (se 2 (by rfl) ⟨1006908, by rfl⟩ : syracuseStep 2685089 = 2013817) B2013817
theorem B2906275 : Blo 1590994 2906275 := bstep (se 1 (by rfl) ⟨2179706, by rfl⟩ : syracuseStep 2906275 = 4359413) B4359413
theorem B9681059 : Blo 1590994 9681059 := bstep (se 1 (by rfl) ⟨7260794, by rfl⟩ : syracuseStep 9681059 = 14521589) B14521589
theorem B5372081 : Blo 1590994 5372081 := bstep (se 2 (by rfl) ⟨2014530, by rfl⟩ : syracuseStep 5372081 = 4029061) B4029061
theorem B2685217 : Blo 1590994 2685217 := bstep (se 2 (by rfl) ⟨1006956, by rfl⟩ : syracuseStep 2685217 = 2013913) B2013913
theorem B2685251 : Blo 1590994 2685251 := bstep (se 1 (by rfl) ⟨2013938, by rfl⟩ : syracuseStep 2685251 = 4027877) B4027877
theorem B6044003 : Blo 1590994 6044003 := bstep (se 1 (by rfl) ⟨4533002, by rfl⟩ : syracuseStep 6044003 = 9066005) B9066005
theorem B6044017 : Blo 1590994 6044017 := bstep (se 2 (by rfl) ⟨2266506, by rfl⟩ : syracuseStep 6044017 = 4533013) B4533013
theorem B32676209 : Blo 1590994 32676209 := bstep (se 2 (by rfl) ⟨12253578, by rfl⟩ : syracuseStep 32676209 = 24507157) B24507157
theorem B5101987 : Blo 1590994 5101987 := bstep (se 1 (by rfl) ⟨3826490, by rfl⟩ : syracuseStep 5101987 = 7652981) B7652981
theorem B4028849 : Blo 1590994 4028849 := bstep (se 2 (by rfl) ⟨1510818, by rfl⟩ : syracuseStep 4028849 = 3021637) B3021637
theorem B2685379 : Blo 1590994 2685379 := bstep (se 1 (by rfl) ⟨2014034, by rfl⟩ : syracuseStep 2685379 = 4028069) B4028069
theorem B4028899 : Blo 1590994 4028899 := bstep (se 1 (by rfl) ⟨3021674, by rfl⟩ : syracuseStep 4028899 = 6043349) B6043349
theorem B2152963 : Blo 1590994 2152963 := bstep (se 1 (by rfl) ⟨1614722, by rfl⟩ : syracuseStep 2152963 = 3229445) B3229445
theorem B2685521 : Blo 1590994 2685521 := bstep (se 2 (by rfl) ⟨1007070, by rfl⟩ : syracuseStep 2685521 = 2014141) B2014141
theorem B3226225 : Blo 1590994 3226225 := bstep (se 2 (by rfl) ⟨1209834, by rfl⟩ : syracuseStep 3226225 = 2419669) B2419669
theorem B4029041 : Blo 1590994 4029041 := bstep (se 2 (by rfl) ⟨1510890, by rfl⟩ : syracuseStep 4029041 = 3021781) B3021781
theorem B2267777 : Blo 1590994 2267777 := bstep (se 2 (by rfl) ⟨850416, by rfl⟩ : syracuseStep 2267777 = 1700833) B1700833
theorem B5372621 : Blo 1590994 5372621 := bstep (se 3 (by rfl) ⟨1007366, by rfl⟩ : syracuseStep 5372621 = 2014733) B2014733
theorem B2685649 : Blo 1590994 2685649 := bstep (se 2 (by rfl) ⟨1007118, by rfl⟩ : syracuseStep 2685649 = 2014237) B2014237
theorem B2013923 : Blo 1590994 2013923 := bstep (se 1 (by rfl) ⟨1510442, by rfl⟩ : syracuseStep 2013923 = 3020885) B3020885
theorem B3447523 : Blo 1590994 3447523 := bstep (se 1 (by rfl) ⟨2585642, by rfl⟩ : syracuseStep 3447523 = 5171285) B5171285
theorem B3021553 : Blo 1590994 3021553 := bstep (se 2 (by rfl) ⟨1133082, by rfl⟩ : syracuseStep 3021553 = 2266165) B2266165
theorem B2685683 : Blo 1590994 2685683 := bstep (se 1 (by rfl) ⟨2014262, by rfl⟩ : syracuseStep 2685683 = 4028525) B4028525
theorem B5372675 : Blo 1590994 5372675 := bstep (se 1 (by rfl) ⟨4029506, by rfl⟩ : syracuseStep 5372675 = 8059013) B8059013
theorem B8059661 : Blo 1590994 8059661 := bstep (se 3 (by rfl) ⟨1511186, by rfl⟩ : syracuseStep 8059661 = 3022373) B3022373
theorem B7363405 : Blo 1590994 7363405 := bstep (se 3 (by rfl) ⟨1380638, by rfl⟩ : syracuseStep 7363405 = 2761277) B2761277
theorem B2685811 : Blo 1590994 2685811 := bstep (se 1 (by rfl) ⟨2014358, by rfl⟩ : syracuseStep 2685811 = 4028717) B4028717
theorem B27958213 : Blo 1590994 27958213 := bstep (se 4 (by rfl) ⟨2621082, by rfl⟩ : syracuseStep 27958213 = 5242165) B5242165
theorem B2685953 : Blo 1590994 2685953 := bstep (se 2 (by rfl) ⟨1007232, by rfl⟩ : syracuseStep 2685953 = 2014465) B2014465
theorem B5372945 : Blo 1590994 5372945 := bstep (se 2 (by rfl) ⟨2014854, by rfl⟩ : syracuseStep 5372945 = 4029709) B4029709
theorem B4086865 : Blo 1590994 4086865 := bstep (se 2 (by rfl) ⟨1532574, by rfl⟩ : syracuseStep 4086865 = 3065149) B3065149
theorem B2686081 : Blo 1590994 2686081 := bstep (se 2 (by rfl) ⟨1007280, by rfl⟩ : syracuseStep 2686081 = 2014561) B2014561
theorem B2686115 : Blo 1590994 2686115 := bstep (se 1 (by rfl) ⟨2014586, by rfl⟩ : syracuseStep 2686115 = 4029173) B4029173
theorem B9321649 : Blo 1590994 9321649 := bstep (se 2 (by rfl) ⟨3495618, by rfl⟩ : syracuseStep 9321649 = 6991237) B6991237
theorem B6798563 : Blo 1590994 6798563 := bstep (se 1 (by rfl) ⟨5098922, by rfl⟩ : syracuseStep 6798563 = 10197845) B10197845
theorem B12082445 : Blo 1590994 12082445 := bstep (se 3 (by rfl) ⟨2265458, by rfl⟩ : syracuseStep 12082445 = 4530917) B4530917
theorem B2686243 : Blo 1590994 2686243 := bstep (se 1 (by rfl) ⟨2014682, by rfl⟩ : syracuseStep 2686243 = 4029365) B4029365
theorem B3399043 : Blo 1590994 3399043 := bstep (se 1 (by rfl) ⟨2549282, by rfl⟩ : syracuseStep 3399043 = 5098565) B5098565
theorem B2948483 : Blo 1590994 2948483 := bstep (se 1 (by rfl) ⟨2211362, by rfl⟩ : syracuseStep 2948483 = 4422725) B4422725
theorem B2014627 : Blo 1590994 2014627 := bstep (se 1 (by rfl) ⟨1510970, by rfl⟩ : syracuseStep 2014627 = 3021941) B3021941
theorem B2686385 : Blo 1590994 2686385 := bstep (se 2 (by rfl) ⟨1007394, by rfl⟩ : syracuseStep 2686385 = 2014789) B2014789
theorem B3448259 : Blo 1590994 3448259 := bstep (se 1 (by rfl) ⟨2586194, by rfl⟩ : syracuseStep 3448259 = 5172389) B5172389
theorem B10206661 : Blo 1590994 10206661 := bstep (se 4 (by rfl) ⟨956874, by rfl⟩ : syracuseStep 10206661 = 1913749) B1913749
theorem B2014723 : Blo 1590994 2014723 := bstep (se 1 (by rfl) ⟨1511042, by rfl⟩ : syracuseStep 2014723 = 3022085) B3022085
theorem B5373485 : Blo 1590994 5373485 := bstep (se 3 (by rfl) ⟨1007528, by rfl⟩ : syracuseStep 5373485 = 2015057) B2015057
theorem B9313841 : Blo 1590994 9313841 := bstep (se 2 (by rfl) ⟨3492690, by rfl⟩ : syracuseStep 9313841 = 6985381) B6985381
theorem B2686513 : Blo 1590994 2686513 := bstep (se 2 (by rfl) ⟨1007442, by rfl⟩ : syracuseStep 2686513 = 2014885) B2014885
theorem B4030033 : Blo 1590994 4030033 := bstep (se 2 (by rfl) ⟨1511262, by rfl⟩ : syracuseStep 4030033 = 3022525) B3022525
theorem B2686547 : Blo 1590994 2686547 := bstep (se 1 (by rfl) ⟨2014910, by rfl⟩ : syracuseStep 2686547 = 4029821) B4029821
theorem B5373539 : Blo 1590994 5373539 := bstep (se 1 (by rfl) ⟨4030154, by rfl⟩ : syracuseStep 5373539 = 8060309) B8060309
theorem B2686675 : Blo 1590994 2686675 := bstep (se 1 (by rfl) ⟨2015006, by rfl⟩ : syracuseStep 2686675 = 4030013) B4030013
theorem B3227377 : Blo 1590994 3227377 := bstep (se 2 (by rfl) ⟨1210266, by rfl⟩ : syracuseStep 3227377 = 2420533) B2420533
theorem B3022609 : Blo 1590994 3022609 := bstep (se 2 (by rfl) ⟨1133478, by rfl⟩ : syracuseStep 3022609 = 2266957) B2266957
theorem B3825443 : Blo 1590994 3825443 := bstep (se 1 (by rfl) ⟨2869082, by rfl⟩ : syracuseStep 3825443 = 5738165) B5738165
theorem B6045475 : Blo 1590994 6045475 := bstep (se 1 (by rfl) ⟨4534106, by rfl⟩ : syracuseStep 6045475 = 9068213) B9068213
theorem B2686817 : Blo 1590994 2686817 := bstep (se 2 (by rfl) ⟨1007556, by rfl⟩ : syracuseStep 2686817 = 2015113) B2015113
theorem B4030307 : Blo 1590994 4030307 := bstep (se 1 (by rfl) ⟨3022730, by rfl⟩ : syracuseStep 4030307 = 6045461) B6045461
theorem B5373809 : Blo 1590994 5373809 := bstep (se 2 (by rfl) ⟨2015178, by rfl⟩ : syracuseStep 5373809 = 4030357) B4030357
theorem B3825539 : Blo 1590994 3825539 := bstep (se 1 (by rfl) ⟨2869154, by rfl⟩ : syracuseStep 3825539 = 5738309) B5738309
theorem B3579857 : Blo 1590994 3579857 := bstep (se 2 (by rfl) ⟨1342446, by rfl⟩ : syracuseStep 3579857 = 2684893) B2684893
theorem B2686945 : Blo 1590994 2686945 := bstep (se 2 (by rfl) ⟨1007604, by rfl⟩ : syracuseStep 2686945 = 2015209) B2015209
theorem B3579875 : Blo 1590994 3579875 := bstep (se 1 (by rfl) ⟨2684906, by rfl⟩ : syracuseStep 3579875 = 5369813) B5369813
theorem B2015219 : Blo 1590994 2015219 := bstep (se 1 (by rfl) ⟨1511414, by rfl⟩ : syracuseStep 2015219 = 3022829) B3022829
theorem B3022859 : Blo 1590994 3022859 := bstep (se 1 (by rfl) ⟨2267144, by rfl⟩ : syracuseStep 3022859 = 4534289) B4534289
theorem B2686999 : Blo 1590994 2686999 := bstep (se 1 (by rfl) ⟨2015249, by rfl⟩ : syracuseStep 2686999 = 4030499) B4030499
theorem B3579929 : Blo 1590994 3579929 := bstep (se 2 (by rfl) ⟨1342473, by rfl⟩ : syracuseStep 3579929 = 2684947) B2684947
theorem B3022913 : Blo 1590994 3022913 := bstep (se 2 (by rfl) ⟨1133592, by rfl⟩ : syracuseStep 3022913 = 2267185) B2267185
theorem B5734475 : Blo 1590994 5734475 := bstep (se 1 (by rfl) ⟨4300856, by rfl⟩ : syracuseStep 5734475 = 8601713) B8601713
theorem B8609885 : Blo 1590994 8609885 := bstep (se 3 (by rfl) ⟨1614353, by rfl⟩ : syracuseStep 8609885 = 3228707) B3228707
theorem B3580019 : Blo 1590994 3580019 := bstep (se 1 (by rfl) ⟨2685014, by rfl⟩ : syracuseStep 3580019 = 5370029) B5370029
theorem B7651459 : Blo 1590994 7651459 := bstep (se 1 (by rfl) ⟨5738594, by rfl⟩ : syracuseStep 7651459 = 11477189) B11477189
theorem B2015371 : Blo 1590994 2015371 := bstep (se 1 (by rfl) ⟨1511528, by rfl⟩ : syracuseStep 2015371 = 3023057) B3023057
theorem B3580055 : Blo 1590994 3580055 := bstep (se 1 (by rfl) ⟨2685041, by rfl⟩ : syracuseStep 3580055 = 5370083) B5370083
theorem B3875033 : Blo 1590994 3875033 := bstep (se 2 (by rfl) ⟨1453137, by rfl⟩ : syracuseStep 3875033 = 2906275) B2906275
theorem B12083417 : Blo 1590994 12083417 := bstep (se 2 (by rfl) ⟨4531281, by rfl⟩ : syracuseStep 12083417 = 9062563) B9062563
theorem B4030681 : Blo 1590994 4030681 := bstep (se 2 (by rfl) ⟨1511505, by rfl⟩ : syracuseStep 4030681 = 3023011) B3023011
theorem B3580235 : Blo 1590994 3580235 := bstep (se 1 (by rfl) ⟨2685176, by rfl⟩ : syracuseStep 3580235 = 5370353) B5370353
theorem B3400051 : Blo 1590994 3400051 := bstep (se 1 (by rfl) ⟨2550038, by rfl⟩ : syracuseStep 3400051 = 5100077) B5100077
theorem B3580289 : Blo 1590994 3580289 := bstep (se 2 (by rfl) ⟨1342608, by rfl⟩ : syracuseStep 3580289 = 2685217) B2685217
theorem B19358129 : Blo 1590994 19358129 := bstep (se 2 (by rfl) ⟨7259298, by rfl⟩ : syracuseStep 19358129 = 14518597) B14518597
theorem B2867699 : Blo 1590994 2867699 := bstep (se 1 (by rfl) ⟨2150774, by rfl⟩ : syracuseStep 2867699 = 4301549) B4301549
theorem B23249443 : Blo 1590994 23249443 := bstep (se 1 (by rfl) ⟨17437082, by rfl⟩ : syracuseStep 23249443 = 34874165) B34874165
theorem B11469347 : Blo 1590994 11469347 := bstep (se 1 (by rfl) ⟨8602010, by rfl⟩ : syracuseStep 11469347 = 17204021) B17204021
theorem B3580505 : Blo 1590994 3580505 := bstep (se 2 (by rfl) ⟨1342689, by rfl⟩ : syracuseStep 3580505 = 2685379) B2685379
theorem B3400307 : Blo 1590994 3400307 := bstep (se 1 (by rfl) ⟨2550230, by rfl⟩ : syracuseStep 3400307 = 5100461) B5100461
theorem B2687627 : Blo 1590994 2687627 := bstep (se 1 (by rfl) ⟨2015720, by rfl⟩ : syracuseStep 2687627 = 4031441) B4031441
theorem B3539609 : Blo 1590994 3539609 := bstep (se 2 (by rfl) ⟨1327353, by rfl⟩ : syracuseStep 3539609 = 2654707) B2654707
theorem B3580595 : Blo 1590994 3580595 := bstep (se 1 (by rfl) ⟨2685446, by rfl⟩ : syracuseStep 3580595 = 5370893) B5370893
theorem B6800051 : Blo 1590994 6800051 := bstep (se 1 (by rfl) ⟨5100038, by rfl⟩ : syracuseStep 6800051 = 10200077) B10200077
theorem B3580631 : Blo 1590994 3580631 := bstep (se 1 (by rfl) ⟨2685473, by rfl⟩ : syracuseStep 3580631 = 5370947) B5370947
theorem B12092165 : Blo 1590994 12092165 := bstep (se 4 (by rfl) ⟨1133640, by rfl⟩ : syracuseStep 12092165 = 2267281) B2267281
theorem B2687755 : Blo 1590994 2687755 := bstep (se 1 (by rfl) ⟨2015816, by rfl⟩ : syracuseStep 2687755 = 4031633) B4031633
theorem B6456115 : Blo 1590994 6456115 := bstep (se 1 (by rfl) ⟨4842086, by rfl⟩ : syracuseStep 6456115 = 9684173) B9684173
theorem B4301633 : Blo 1590994 4301633 := bstep (se 2 (by rfl) ⟨1613112, by rfl⟩ : syracuseStep 4301633 = 3226225) B3226225
theorem B6800203 : Blo 1590994 6800203 := bstep (se 1 (by rfl) ⟨5100152, by rfl⟩ : syracuseStep 6800203 = 10200305) B10200305
theorem B3580811 : Blo 1590994 3580811 := bstep (se 1 (by rfl) ⟨2685608, by rfl⟩ : syracuseStep 3580811 = 5371217) B5371217
theorem B6800273 : Blo 1590994 6800273 := bstep (se 2 (by rfl) ⟨2550102, by rfl⟩ : syracuseStep 6800273 = 5100205) B5100205
theorem B2687897 : Blo 1590994 2687897 := bstep (se 2 (by rfl) ⟨1007961, by rfl⟩ : syracuseStep 2687897 = 2015923) B2015923
theorem B3580865 : Blo 1590994 3580865 := bstep (se 2 (by rfl) ⟨1342824, by rfl⟩ : syracuseStep 3580865 = 2685649) B2685649
theorem B3023831 : Blo 1590994 3023831 := bstep (se 1 (by rfl) ⟨2267873, by rfl⟩ : syracuseStep 3023831 = 4535747) B4535747
theorem B4596697 : Blo 1590994 4596697 := bstep (se 2 (by rfl) ⟨1723761, by rfl⟩ : syracuseStep 4596697 = 3447523) B3447523
theorem B2688025 : Blo 1590994 2688025 := bstep (se 2 (by rfl) ⟨1008009, by rfl⟩ : syracuseStep 2688025 = 2016019) B2016019
theorem B46507043 : Blo 1590994 46507043 := bstep (se 1 (by rfl) ⟨34880282, by rfl⟩ : syracuseStep 46507043 = 69760565) B69760565
theorem B5375051 : Blo 1590994 5375051 := bstep (se 1 (by rfl) ⟨4031288, by rfl⟩ : syracuseStep 5375051 = 8062577) B8062577
theorem B2868311 : Blo 1590994 2868311 := bstep (se 1 (by rfl) ⟨2151233, by rfl⟩ : syracuseStep 2868311 = 4302467) B4302467
theorem B6128729 : Blo 1590994 6128729 := bstep (se 2 (by rfl) ⟨2298273, by rfl⟩ : syracuseStep 6128729 = 4596547) B4596547
theorem B3581081 : Blo 1590994 3581081 := bstep (se 2 (by rfl) ⟨1342905, by rfl⟩ : syracuseStep 3581081 = 2685811) B2685811
theorem B42468533 : Blo 1590994 42468533 := bstep (se 5 (by rfl) ⟨1990712, by rfl⟩ : syracuseStep 42468533 = 3981425) B3981425
theorem B3581171 : Blo 1590994 3581171 := bstep (se 1 (by rfl) ⟨2685878, by rfl⟩ : syracuseStep 3581171 = 5371757) B5371757
theorem B3581207 : Blo 1590994 3581207 := bstep (se 1 (by rfl) ⟨2685905, by rfl⟩ : syracuseStep 3581207 = 5371811) B5371811
theorem B3630361 : Blo 1590994 3630361 := bstep (se 2 (by rfl) ⟨1361385, by rfl⟩ : syracuseStep 3630361 = 2722771) B2722771
theorem B8062253 : Blo 1590994 8062253 := bstep (se 3 (by rfl) ⟨1511672, by rfl⟩ : syracuseStep 8062253 = 3023345) B3023345
theorem B4031795 : Blo 1590994 4031795 := bstep (se 1 (by rfl) ⟨3023846, by rfl⟩ : syracuseStep 4031795 = 6047693) B6047693
theorem B5375321 : Blo 1590994 5375321 := bstep (se 2 (by rfl) ⟨2015745, by rfl⟩ : syracuseStep 5375321 = 4031491) B4031491
theorem B5596609 : Blo 1590994 5596609 := bstep (se 2 (by rfl) ⟨2098728, by rfl⟩ : syracuseStep 5596609 = 4197457) B4197457
theorem B3581387 : Blo 1590994 3581387 := bstep (se 1 (by rfl) ⟨2686040, by rfl⟩ : syracuseStep 3581387 = 5372081) B5372081
theorem B3581441 : Blo 1590994 3581441 := bstep (se 2 (by rfl) ⟨1343040, by rfl⟩ : syracuseStep 3581441 = 2686081) B2686081
theorem B13592069 : Blo 1590994 13592069 := bstep (se 4 (by rfl) ⟨1274256, by rfl⟩ : syracuseStep 13592069 = 2548513) B2548513
theorem B3401281 : Blo 1590994 3401281 := bstep (se 2 (by rfl) ⟨1275480, by rfl⟩ : syracuseStep 3401281 = 2550961) B2550961
theorem B21784139 : Blo 1590994 21784139 := bstep (se 1 (by rfl) ⟨16338104, by rfl⟩ : syracuseStep 21784139 = 32676209) B32676209
theorem B4032089 : Blo 1590994 4032089 := bstep (se 2 (by rfl) ⟨1512033, by rfl⟩ : syracuseStep 4032089 = 3024067) B3024067
theorem B6047405 : Blo 1590994 6047405 := bstep (se 3 (by rfl) ⟨1133888, by rfl⟩ : syracuseStep 6047405 = 2267777) B2267777
theorem B1590999 : Blo 1590994 1590999 := bstep (se 1 (by rfl) ⟨1193249, by rfl⟩ : syracuseStep 1590999 = 2386499) B2386499
theorem B3581657 : Blo 1590994 3581657 := bstep (se 2 (by rfl) ⟨1343121, by rfl⟩ : syracuseStep 3581657 = 2686243) B2686243
theorem B1591019 : Blo 1590994 1591019 := bstep (se 1 (by rfl) ⟨1193264, by rfl⟩ : syracuseStep 1591019 = 2386529) B2386529
theorem B1591031 : Blo 1590994 1591031 := bstep (se 1 (by rfl) ⟨1193273, by rfl⟩ : syracuseStep 1591031 = 2386547) B2386547
theorem B1591051 : Blo 1590994 1591051 := bstep (se 1 (by rfl) ⟨1193288, by rfl⟩ : syracuseStep 1591051 = 2386577) B2386577
theorem B1591063 : Blo 1590994 1591063 := bstep (se 1 (by rfl) ⟨1193297, by rfl⟩ : syracuseStep 1591063 = 2386595) B2386595
theorem B1591083 : Blo 1590994 1591083 := bstep (se 1 (by rfl) ⟨1193312, by rfl⟩ : syracuseStep 1591083 = 2386625) B2386625
theorem B3581747 : Blo 1590994 3581747 := bstep (se 1 (by rfl) ⟨2686310, by rfl⟩ : syracuseStep 3581747 = 5372621) B5372621
theorem B1591095 : Blo 1590994 1591095 := bstep (se 1 (by rfl) ⟨1193321, by rfl⟩ : syracuseStep 1591095 = 2386643) B2386643
theorem B1591115 : Blo 1590994 1591115 := bstep (se 1 (by rfl) ⟨1193336, by rfl⟩ : syracuseStep 1591115 = 2386673) B2386673
theorem B2869067 : Blo 1590994 2869067 := bstep (se 1 (by rfl) ⟨2151800, by rfl⟩ : syracuseStep 2869067 = 4303601) B4303601
theorem B1591127 : Blo 1590994 1591127 := bstep (se 1 (by rfl) ⟨1193345, by rfl⟩ : syracuseStep 1591127 = 2386691) B2386691
theorem B3581783 : Blo 1590994 3581783 := bstep (se 1 (by rfl) ⟨2686337, by rfl⟩ : syracuseStep 3581783 = 5372675) B5372675
theorem B4532057 : Blo 1590994 4532057 := bstep (se 2 (by rfl) ⟨1699521, by rfl⟩ : syracuseStep 4532057 = 3399043) B3399043
theorem B1591147 : Blo 1590994 1591147 := bstep (se 1 (by rfl) ⟨1193360, by rfl⟩ : syracuseStep 1591147 = 2386721) B2386721
theorem B1591159 : Blo 1590994 1591159 := bstep (se 1 (by rfl) ⟨1193369, by rfl⟩ : syracuseStep 1591159 = 2386739) B2386739
theorem B1591179 : Blo 1590994 1591179 := bstep (se 1 (by rfl) ⟨1193384, by rfl⟩ : syracuseStep 1591179 = 2386769) B2386769
theorem B1591191 : Blo 1590994 1591191 := bstep (se 1 (by rfl) ⟨1193393, by rfl⟩ : syracuseStep 1591191 = 2386787) B2386787
theorem B1591211 : Blo 1590994 1591211 := bstep (se 1 (by rfl) ⟨1193408, by rfl⟩ : syracuseStep 1591211 = 2386817) B2386817
theorem B13608881 : Blo 1590994 13608881 := bstep (se 2 (by rfl) ⟨5103330, by rfl⟩ : syracuseStep 13608881 = 10206661) B10206661
theorem B1591223 : Blo 1590994 1591223 := bstep (se 1 (by rfl) ⟨1193417, by rfl⟩ : syracuseStep 1591223 = 2386835) B2386835
theorem B1591243 : Blo 1590994 1591243 := bstep (se 1 (by rfl) ⟨1193432, by rfl⟩ : syracuseStep 1591243 = 2386865) B2386865
theorem B1591255 : Blo 1590994 1591255 := bstep (se 1 (by rfl) ⟨1193441, by rfl⟩ : syracuseStep 1591255 = 2386883) B2386883
theorem B9684953 : Blo 1590994 9684953 := bstep (se 2 (by rfl) ⟨3631857, by rfl⟩ : syracuseStep 9684953 = 7263715) B7263715
theorem B5097437 : Blo 1590994 5097437 := bstep (se 3 (by rfl) ⟨955769, by rfl⟩ : syracuseStep 5097437 = 1911539) B1911539
theorem B1591275 : Blo 1590994 1591275 := bstep (se 1 (by rfl) ⟨1193456, by rfl⟩ : syracuseStep 1591275 = 2386913) B2386913
theorem B1591287 : Blo 1590994 1591287 := bstep (se 1 (by rfl) ⟨1193465, by rfl⟩ : syracuseStep 1591287 = 2386931) B2386931
theorem B1591307 : Blo 1590994 1591307 := bstep (se 1 (by rfl) ⟨1193480, by rfl⟩ : syracuseStep 1591307 = 2386961) B2386961
theorem B3581963 : Blo 1590994 3581963 := bstep (se 1 (by rfl) ⟨2686472, by rfl⟩ : syracuseStep 3581963 = 5372945) B5372945
theorem B8054801 : Blo 1590994 8054801 := bstep (se 2 (by rfl) ⟨3020550, by rfl⟩ : syracuseStep 8054801 = 6041101) B6041101
theorem B1591319 : Blo 1590994 1591319 := bstep (se 1 (by rfl) ⟨1193489, by rfl⟩ : syracuseStep 1591319 = 2386979) B2386979
theorem B5376023 : Blo 1590994 5376023 := bstep (se 1 (by rfl) ⟨4032017, by rfl⟩ : syracuseStep 5376023 = 8064035) B8064035
theorem B1591339 : Blo 1590994 1591339 := bstep (se 1 (by rfl) ⟨1193504, by rfl⟩ : syracuseStep 1591339 = 2387009) B2387009
theorem B1591351 : Blo 1590994 1591351 := bstep (se 1 (by rfl) ⟨1193513, by rfl⟩ : syracuseStep 1591351 = 2387027) B2387027
theorem B3582017 : Blo 1590994 3582017 := bstep (se 2 (by rfl) ⟨1343256, by rfl⟩ : syracuseStep 3582017 = 2686513) B2686513
theorem B1591371 : Blo 1590994 1591371 := bstep (se 1 (by rfl) ⟨1193528, by rfl⟩ : syracuseStep 1591371 = 2387057) B2387057
theorem B1591383 : Blo 1590994 1591383 := bstep (se 1 (by rfl) ⟨1193537, by rfl⟩ : syracuseStep 1591383 = 2387075) B2387075
theorem B1591403 : Blo 1590994 1591403 := bstep (se 1 (by rfl) ⟨1193552, by rfl⟩ : syracuseStep 1591403 = 2387105) B2387105
theorem B1591415 : Blo 1590994 1591415 := bstep (se 1 (by rfl) ⟨1193561, by rfl⟩ : syracuseStep 1591415 = 2387123) B2387123
theorem B1591435 : Blo 1590994 1591435 := bstep (se 1 (by rfl) ⟨1193576, by rfl⟩ : syracuseStep 1591435 = 2387153) B2387153
theorem B1591447 : Blo 1590994 1591447 := bstep (se 1 (by rfl) ⟨1193585, by rfl⟩ : syracuseStep 1591447 = 2387171) B2387171
theorem B4532375 : Blo 1590994 4532375 := bstep (se 1 (by rfl) ⟨3399281, by rfl⟩ : syracuseStep 4532375 = 6798563) B6798563
theorem B1591467 : Blo 1590994 1591467 := bstep (se 1 (by rfl) ⟨1193600, by rfl⟩ : syracuseStep 1591467 = 2387201) B2387201
theorem B8054963 : Blo 1590994 8054963 := bstep (se 1 (by rfl) ⟨6041222, by rfl⟩ : syracuseStep 8054963 = 12082445) B12082445
theorem B1591479 : Blo 1590994 1591479 := bstep (se 1 (by rfl) ⟨1193609, by rfl⟩ : syracuseStep 1591479 = 2387219) B2387219
theorem B1591499 : Blo 1590994 1591499 := bstep (se 1 (by rfl) ⟨1193624, by rfl⟩ : syracuseStep 1591499 = 2387249) B2387249
theorem B1591511 : Blo 1590994 1591511 := bstep (se 1 (by rfl) ⟨1193633, by rfl⟩ : syracuseStep 1591511 = 2387267) B2387267
theorem B1591531 : Blo 1590994 1591531 := bstep (se 1 (by rfl) ⟨1193648, by rfl⟩ : syracuseStep 1591531 = 2387297) B2387297
theorem B1591543 : Blo 1590994 1591543 := bstep (se 1 (by rfl) ⟨1193657, by rfl⟩ : syracuseStep 1591543 = 2387315) B2387315
theorem B1591563 : Blo 1590994 1591563 := bstep (se 1 (by rfl) ⟨1193672, by rfl⟩ : syracuseStep 1591563 = 2387345) B2387345
theorem B1591575 : Blo 1590994 1591575 := bstep (se 1 (by rfl) ⟨1193681, by rfl⟩ : syracuseStep 1591575 = 2387363) B2387363
theorem B3582233 : Blo 1590994 3582233 := bstep (se 2 (by rfl) ⟨1343337, by rfl⟩ : syracuseStep 3582233 = 2686675) B2686675
theorem B1591595 : Blo 1590994 1591595 := bstep (se 1 (by rfl) ⟨1193696, by rfl⟩ : syracuseStep 1591595 = 2387393) B2387393
theorem B5736749 : Blo 1590994 5736749 := bstep (se 3 (by rfl) ⟨1075640, by rfl⟩ : syracuseStep 5736749 = 2151281) B2151281
theorem B1591607 : Blo 1590994 1591607 := bstep (se 1 (by rfl) ⟨1193705, by rfl⟩ : syracuseStep 1591607 = 2387411) B2387411
theorem B4303169 : Blo 1590994 4303169 := bstep (se 2 (by rfl) ⟨1613688, by rfl⟩ : syracuseStep 4303169 = 3227377) B3227377
theorem B1591627 : Blo 1590994 1591627 := bstep (se 1 (by rfl) ⟨1193720, by rfl⟩ : syracuseStep 1591627 = 2387441) B2387441
theorem B1591639 : Blo 1590994 1591639 := bstep (se 1 (by rfl) ⟨1193729, by rfl⟩ : syracuseStep 1591639 = 2387459) B2387459
theorem B1591659 : Blo 1590994 1591659 := bstep (se 1 (by rfl) ⟨1193744, by rfl⟩ : syracuseStep 1591659 = 2387489) B2387489
theorem B3582323 : Blo 1590994 3582323 := bstep (se 1 (by rfl) ⟨2686742, by rfl⟩ : syracuseStep 3582323 = 5373485) B5373485
theorem B1591671 : Blo 1590994 1591671 := bstep (se 1 (by rfl) ⟨1193753, by rfl⟩ : syracuseStep 1591671 = 2387507) B2387507
theorem B1591691 : Blo 1590994 1591691 := bstep (se 1 (by rfl) ⟨1193768, by rfl⟩ : syracuseStep 1591691 = 2387537) B2387537
theorem B1591703 : Blo 1590994 1591703 := bstep (se 1 (by rfl) ⟨1193777, by rfl⟩ : syracuseStep 1591703 = 2387555) B2387555
theorem B3582359 : Blo 1590994 3582359 := bstep (se 1 (by rfl) ⟨2686769, by rfl⟩ : syracuseStep 3582359 = 5373539) B5373539
theorem B1591723 : Blo 1590994 1591723 := bstep (se 1 (by rfl) ⟨1193792, by rfl⟩ : syracuseStep 1591723 = 2387585) B2387585
theorem B6048179 : Blo 1590994 6048179 := bstep (se 1 (by rfl) ⟨4536134, by rfl⟩ : syracuseStep 6048179 = 9072269) B9072269
theorem B1591735 : Blo 1590994 1591735 := bstep (se 1 (by rfl) ⟨1193801, by rfl⟩ : syracuseStep 1591735 = 2387603) B2387603
theorem B1591755 : Blo 1590994 1591755 := bstep (se 1 (by rfl) ⟨1193816, by rfl⟩ : syracuseStep 1591755 = 2387633) B2387633
theorem B1591767 : Blo 1590994 1591767 := bstep (se 1 (by rfl) ⟨1193825, by rfl⟩ : syracuseStep 1591767 = 2387651) B2387651
theorem B1591787 : Blo 1590994 1591787 := bstep (se 1 (by rfl) ⟨1193840, by rfl⟩ : syracuseStep 1591787 = 2387681) B2387681
theorem B1591799 : Blo 1590994 1591799 := bstep (se 1 (by rfl) ⟨1193849, by rfl⟩ : syracuseStep 1591799 = 2387699) B2387699
theorem B1591819 : Blo 1590994 1591819 := bstep (se 1 (by rfl) ⟨1193864, by rfl⟩ : syracuseStep 1591819 = 2387729) B2387729
theorem B1591831 : Blo 1590994 1591831 := bstep (se 1 (by rfl) ⟨1193873, by rfl⟩ : syracuseStep 1591831 = 2387747) B2387747
theorem B2550295 : Blo 1590994 2550295 := bstep (se 1 (by rfl) ⟨1912721, by rfl⟩ : syracuseStep 2550295 = 3825443) B3825443
theorem B1591851 : Blo 1590994 1591851 := bstep (se 1 (by rfl) ⟨1193888, by rfl⟩ : syracuseStep 1591851 = 2387777) B2387777
theorem B6801965 : Blo 1590994 6801965 := bstep (se 3 (by rfl) ⟨1275368, by rfl⟩ : syracuseStep 6801965 = 2550737) B2550737
theorem B1591863 : Blo 1590994 1591863 := bstep (se 1 (by rfl) ⟨1193897, by rfl⟩ : syracuseStep 1591863 = 2387795) B2387795
theorem B1591883 : Blo 1590994 1591883 := bstep (se 1 (by rfl) ⟨1193912, by rfl⟩ : syracuseStep 1591883 = 2387825) B2387825
theorem B3582539 : Blo 1590994 3582539 := bstep (se 1 (by rfl) ⟨2686904, by rfl⟩ : syracuseStep 3582539 = 5373809) B5373809
theorem B1591895 : Blo 1590994 1591895 := bstep (se 1 (by rfl) ⟨1193921, by rfl⟩ : syracuseStep 1591895 = 2387843) B2387843
theorem B2550359 : Blo 1590994 2550359 := bstep (se 1 (by rfl) ⟨1912769, by rfl⟩ : syracuseStep 2550359 = 3825539) B3825539
theorem B1591915 : Blo 1590994 1591915 := bstep (se 1 (by rfl) ⟨1193936, by rfl⟩ : syracuseStep 1591915 = 2387873) B2387873
theorem B1591927 : Blo 1590994 1591927 := bstep (se 1 (by rfl) ⟨1193945, by rfl⟩ : syracuseStep 1591927 = 2387891) B2387891
theorem B3582593 : Blo 1590994 3582593 := bstep (se 2 (by rfl) ⟨1343472, by rfl⟩ : syracuseStep 3582593 = 2686945) B2686945
theorem B2386571 : Blo 1590994 2386571 := bstep (se 1 (by rfl) ⟨1789928, by rfl⟩ : syracuseStep 2386571 = 3579857) B3579857
theorem B1591947 : Blo 1590994 1591947 := bstep (se 1 (by rfl) ⟨1193960, by rfl⟩ : syracuseStep 1591947 = 2387921) B2387921
theorem B2386583 : Blo 1590994 2386583 := bstep (se 1 (by rfl) ⟨1789937, by rfl⟩ : syracuseStep 2386583 = 3579875) B3579875
theorem B1591959 : Blo 1590994 1591959 := bstep (se 1 (by rfl) ⟨1193969, by rfl⟩ : syracuseStep 1591959 = 2387939) B2387939
theorem B1591979 : Blo 1590994 1591979 := bstep (se 1 (by rfl) ⟨1193984, by rfl⟩ : syracuseStep 1591979 = 2387969) B2387969
theorem B1591991 : Blo 1590994 1591991 := bstep (se 1 (by rfl) ⟨1193993, by rfl⟩ : syracuseStep 1591991 = 2387987) B2387987
theorem B1592011 : Blo 1590994 1592011 := bstep (se 1 (by rfl) ⟨1194008, by rfl⟩ : syracuseStep 1592011 = 2388017) B2388017
theorem B1592023 : Blo 1590994 1592023 := bstep (se 1 (by rfl) ⟨1194017, by rfl⟩ : syracuseStep 1592023 = 2388035) B2388035
theorem B2386649 : Blo 1590994 2386649 := bstep (se 2 (by rfl) ⟨894993, by rfl⟩ : syracuseStep 2386649 = 1789987) B1789987
theorem B1592043 : Blo 1590994 1592043 := bstep (se 1 (by rfl) ⟨1194032, by rfl⟩ : syracuseStep 1592043 = 2388065) B2388065
theorem B1592055 : Blo 1590994 1592055 := bstep (se 1 (by rfl) ⟨1194041, by rfl⟩ : syracuseStep 1592055 = 2388083) B2388083
theorem B1592075 : Blo 1590994 1592075 := bstep (se 1 (by rfl) ⟨1194056, by rfl⟩ : syracuseStep 1592075 = 2388113) B2388113
theorem B1592087 : Blo 1590994 1592087 := bstep (se 1 (by rfl) ⟨1194065, by rfl⟩ : syracuseStep 1592087 = 2388131) B2388131
theorem B1592107 : Blo 1590994 1592107 := bstep (se 1 (by rfl) ⟨1194080, by rfl⟩ : syracuseStep 1592107 = 2388161) B2388161
theorem B16345901 : Blo 1590994 16345901 := bstep (se 3 (by rfl) ⟨3064856, by rfl⟩ : syracuseStep 16345901 = 6129713) B6129713
theorem B1592119 : Blo 1590994 1592119 := bstep (se 1 (by rfl) ⟨1194089, by rfl⟩ : syracuseStep 1592119 = 2388179) B2388179
theorem B4082507 : Blo 1590994 4082507 := bstep (se 1 (by rfl) ⟨3061880, by rfl⟩ : syracuseStep 4082507 = 6123761) B6123761
theorem B2386763 : Blo 1590994 2386763 := bstep (se 1 (by rfl) ⟨1790072, by rfl⟩ : syracuseStep 2386763 = 3580145) B3580145
theorem B1592139 : Blo 1590994 1592139 := bstep (se 1 (by rfl) ⟨1194104, by rfl⟩ : syracuseStep 1592139 = 2388209) B2388209
theorem B2386775 : Blo 1590994 2386775 := bstep (se 1 (by rfl) ⟨1790081, by rfl⟩ : syracuseStep 2386775 = 3580163) B3580163
theorem B1592151 : Blo 1590994 1592151 := bstep (se 1 (by rfl) ⟨1194113, by rfl⟩ : syracuseStep 1592151 = 2388227) B2388227
theorem B3582809 : Blo 1590994 3582809 := bstep (se 2 (by rfl) ⟨1343553, by rfl⟩ : syracuseStep 3582809 = 2687107) B2687107
theorem B4303709 : Blo 1590994 4303709 := bstep (se 3 (by rfl) ⟨806945, by rfl⟩ : syracuseStep 4303709 = 1613891) B1613891
theorem B1592171 : Blo 1590994 1592171 := bstep (se 1 (by rfl) ⟨1194128, by rfl⟩ : syracuseStep 1592171 = 2388257) B2388257
theorem B1592183 : Blo 1590994 1592183 := bstep (se 1 (by rfl) ⟨1194137, by rfl⟩ : syracuseStep 1592183 = 2388275) B2388275
theorem B1592203 : Blo 1590994 1592203 := bstep (se 1 (by rfl) ⟨1194152, by rfl⟩ : syracuseStep 1592203 = 2388305) B2388305
theorem B1592215 : Blo 1590994 1592215 := bstep (se 1 (by rfl) ⟨1194161, by rfl⟩ : syracuseStep 1592215 = 2388323) B2388323
theorem B2386841 : Blo 1590994 2386841 := bstep (se 2 (by rfl) ⟨895065, by rfl⟩ : syracuseStep 2386841 = 1790131) B1790131
theorem B1592235 : Blo 1590994 1592235 := bstep (se 1 (by rfl) ⟨1194176, by rfl⟩ : syracuseStep 1592235 = 2388353) B2388353
theorem B3582899 : Blo 1590994 3582899 := bstep (se 1 (by rfl) ⟨2687174, by rfl⟩ : syracuseStep 3582899 = 5374349) B5374349
theorem B1592247 : Blo 1590994 1592247 := bstep (se 1 (by rfl) ⟨1194185, by rfl⟩ : syracuseStep 1592247 = 2388371) B2388371
theorem B4533185 : Blo 1590994 4533185 := bstep (se 2 (by rfl) ⟨1699944, by rfl⟩ : syracuseStep 4533185 = 3399889) B3399889
theorem B1592267 : Blo 1590994 1592267 := bstep (se 1 (by rfl) ⟨1194200, by rfl⟩ : syracuseStep 1592267 = 2388401) B2388401
theorem B1592279 : Blo 1590994 1592279 := bstep (se 1 (by rfl) ⟨1194209, by rfl⟩ : syracuseStep 1592279 = 2388419) B2388419
theorem B3582935 : Blo 1590994 3582935 := bstep (se 1 (by rfl) ⟨2687201, by rfl⟩ : syracuseStep 3582935 = 5374403) B5374403
theorem B1592299 : Blo 1590994 1592299 := bstep (se 1 (by rfl) ⟨1194224, by rfl⟩ : syracuseStep 1592299 = 2388449) B2388449
theorem B1592311 : Blo 1590994 1592311 := bstep (se 1 (by rfl) ⟨1194233, by rfl⟩ : syracuseStep 1592311 = 2388467) B2388467
theorem B2386955 : Blo 1590994 2386955 := bstep (se 1 (by rfl) ⟨1790216, by rfl⟩ : syracuseStep 2386955 = 3580433) B3580433
theorem B1592331 : Blo 1590994 1592331 := bstep (se 1 (by rfl) ⟨1194248, by rfl⟩ : syracuseStep 1592331 = 2388497) B2388497
theorem B2386967 : Blo 1590994 2386967 := bstep (se 1 (by rfl) ⟨1790225, by rfl⟩ : syracuseStep 2386967 = 3580451) B3580451
theorem B1592343 : Blo 1590994 1592343 := bstep (se 1 (by rfl) ⟨1194257, by rfl⟩ : syracuseStep 1592343 = 2388515) B2388515
theorem B1592363 : Blo 1590994 1592363 := bstep (se 1 (by rfl) ⟨1194272, by rfl⟩ : syracuseStep 1592363 = 2388545) B2388545
theorem B6990893 : Blo 1590994 6990893 := bstep (se 3 (by rfl) ⟨1310792, by rfl⟩ : syracuseStep 6990893 = 2621585) B2621585
theorem B1592375 : Blo 1590994 1592375 := bstep (se 1 (by rfl) ⟨1194281, by rfl⟩ : syracuseStep 1592375 = 2388563) B2388563
theorem B1592395 : Blo 1590994 1592395 := bstep (se 1 (by rfl) ⟨1194296, by rfl⟩ : syracuseStep 1592395 = 2388593) B2388593
theorem B1592407 : Blo 1590994 1592407 := bstep (se 1 (by rfl) ⟨1194305, by rfl⟩ : syracuseStep 1592407 = 2388611) B2388611
theorem B2387033 : Blo 1590994 2387033 := bstep (se 2 (by rfl) ⟨895137, by rfl⟩ : syracuseStep 2387033 = 1790275) B1790275
theorem B1592427 : Blo 1590994 1592427 := bstep (se 1 (by rfl) ⟨1194320, by rfl⟩ : syracuseStep 1592427 = 2388641) B2388641
theorem B2870387 : Blo 1590994 2870387 := bstep (se 1 (by rfl) ⟨2152790, by rfl⟩ : syracuseStep 2870387 = 4305581) B4305581
theorem B1592439 : Blo 1590994 1592439 := bstep (se 1 (by rfl) ⟨1194329, by rfl⟩ : syracuseStep 1592439 = 2388659) B2388659
theorem B12094595 : Blo 1590994 12094595 := bstep (se 1 (by rfl) ⟨9070946, by rfl⟩ : syracuseStep 12094595 = 18141893) B18141893
theorem B1592459 : Blo 1590994 1592459 := bstep (se 1 (by rfl) ⟨1194344, by rfl⟩ : syracuseStep 1592459 = 2388689) B2388689
theorem B3583115 : Blo 1590994 3583115 := bstep (se 1 (by rfl) ⟨2687336, by rfl⟩ : syracuseStep 3583115 = 5374673) B5374673
theorem B2550923 : Blo 1590994 2550923 := bstep (se 1 (by rfl) ⟨1913192, by rfl⟩ : syracuseStep 2550923 = 3826385) B3826385
theorem B1592471 : Blo 1590994 1592471 := bstep (se 1 (by rfl) ⟨1194353, by rfl⟩ : syracuseStep 1592471 = 2388707) B2388707
theorem B2419865 : Blo 1590994 2419865 := bstep (se 2 (by rfl) ⟨907449, by rfl⟩ : syracuseStep 2419865 = 1814899) B1814899
theorem B1592491 : Blo 1590994 1592491 := bstep (se 1 (by rfl) ⟨1194368, by rfl⟩ : syracuseStep 1592491 = 2388737) B2388737
theorem B1592503 : Blo 1590994 1592503 := bstep (se 1 (by rfl) ⟨1194377, by rfl⟩ : syracuseStep 1592503 = 2388755) B2388755
theorem B3583169 : Blo 1590994 3583169 := bstep (se 2 (by rfl) ⟨1343688, by rfl⟩ : syracuseStep 3583169 = 2687377) B2687377
theorem B2387147 : Blo 1590994 2387147 := bstep (se 1 (by rfl) ⟨1790360, by rfl⟩ : syracuseStep 2387147 = 3580721) B3580721
theorem B1592523 : Blo 1590994 1592523 := bstep (se 1 (by rfl) ⟨1194392, by rfl⟩ : syracuseStep 1592523 = 2388785) B2388785
theorem B2387159 : Blo 1590994 2387159 := bstep (se 1 (by rfl) ⟨1790369, by rfl⟩ : syracuseStep 2387159 = 3580739) B3580739
theorem B1592535 : Blo 1590994 1592535 := bstep (se 1 (by rfl) ⟨1194401, by rfl⟩ : syracuseStep 1592535 = 2388803) B2388803
theorem B6802649 : Blo 1590994 6802649 := bstep (se 2 (by rfl) ⟨2550993, by rfl⟩ : syracuseStep 6802649 = 5101987) B5101987
theorem B5098717 : Blo 1590994 5098717 := bstep (se 3 (by rfl) ⟨956009, by rfl⟩ : syracuseStep 5098717 = 1912019) B1912019
theorem B1592555 : Blo 1590994 1592555 := bstep (se 1 (by rfl) ⟨1194416, by rfl⟩ : syracuseStep 1592555 = 2388833) B2388833
theorem B1592567 : Blo 1590994 1592567 := bstep (se 1 (by rfl) ⟨1194425, by rfl⟩ : syracuseStep 1592567 = 2388851) B2388851
theorem B1592587 : Blo 1590994 1592587 := bstep (se 1 (by rfl) ⟨1194440, by rfl⟩ : syracuseStep 1592587 = 2388881) B2388881
theorem B1592599 : Blo 1590994 1592599 := bstep (se 1 (by rfl) ⟨1194449, by rfl⟩ : syracuseStep 1592599 = 2388899) B2388899
theorem B2387225 : Blo 1590994 2387225 := bstep (se 2 (by rfl) ⟨895209, by rfl⟩ : syracuseStep 2387225 = 1790419) B1790419
theorem B1592619 : Blo 1590994 1592619 := bstep (se 1 (by rfl) ⟨1194464, by rfl⟩ : syracuseStep 1592619 = 2388929) B2388929
theorem B1592631 : Blo 1590994 1592631 := bstep (se 1 (by rfl) ⟨1194473, by rfl⟩ : syracuseStep 1592631 = 2388947) B2388947
theorem B2551115 : Blo 1590994 2551115 := bstep (se 1 (by rfl) ⟨1913336, by rfl⟩ : syracuseStep 2551115 = 3826673) B3826673
theorem B1592651 : Blo 1590994 1592651 := bstep (se 1 (by rfl) ⟨1194488, by rfl⟩ : syracuseStep 1592651 = 2388977) B2388977
theorem B5737817 : Blo 1590994 5737817 := bstep (se 2 (by rfl) ⟨2151681, by rfl⟩ : syracuseStep 5737817 = 4303363) B4303363
theorem B1592663 : Blo 1590994 1592663 := bstep (se 1 (by rfl) ⟨1194497, by rfl⟩ : syracuseStep 1592663 = 2388995) B2388995
theorem B1592683 : Blo 1590994 1592683 := bstep (se 1 (by rfl) ⟨1194512, by rfl⟩ : syracuseStep 1592683 = 2389025) B2389025
theorem B1592695 : Blo 1590994 1592695 := bstep (se 1 (by rfl) ⟨1194521, by rfl⟩ : syracuseStep 1592695 = 2389043) B2389043
theorem B2387339 : Blo 1590994 2387339 := bstep (se 1 (by rfl) ⟨1790504, by rfl⟩ : syracuseStep 2387339 = 3581009) B3581009
theorem B1592715 : Blo 1590994 1592715 := bstep (se 1 (by rfl) ⟨1194536, by rfl⟩ : syracuseStep 1592715 = 2389073) B2389073
theorem B2387351 : Blo 1590994 2387351 := bstep (se 1 (by rfl) ⟨1790513, by rfl⟩ : syracuseStep 2387351 = 3581027) B3581027
theorem B1592727 : Blo 1590994 1592727 := bstep (se 1 (by rfl) ⟨1194545, by rfl⟩ : syracuseStep 1592727 = 2389091) B2389091
theorem B3583385 : Blo 1590994 3583385 := bstep (se 2 (by rfl) ⟨1343769, by rfl⟩ : syracuseStep 3583385 = 2687539) B2687539
theorem B1592747 : Blo 1590994 1592747 := bstep (se 1 (by rfl) ⟨1194560, by rfl⟩ : syracuseStep 1592747 = 2389121) B2389121
theorem B1592759 : Blo 1590994 1592759 := bstep (se 1 (by rfl) ⟨1194569, by rfl⟩ : syracuseStep 1592759 = 2389139) B2389139
theorem B1592779 : Blo 1590994 1592779 := bstep (se 1 (by rfl) ⟨1194584, by rfl⟩ : syracuseStep 1592779 = 2389169) B2389169
theorem B1592791 : Blo 1590994 1592791 := bstep (se 1 (by rfl) ⟨1194593, by rfl⟩ : syracuseStep 1592791 = 2389187) B2389187
theorem B2387417 : Blo 1590994 2387417 := bstep (se 2 (by rfl) ⟨895281, by rfl⟩ : syracuseStep 2387417 = 1790563) B1790563
theorem B1592811 : Blo 1590994 1592811 := bstep (se 1 (by rfl) ⟨1194608, by rfl⟩ : syracuseStep 1592811 = 2389217) B2389217
theorem B3583475 : Blo 1590994 3583475 := bstep (se 1 (by rfl) ⟨2687606, by rfl⟩ : syracuseStep 3583475 = 5375213) B5375213
theorem B1592823 : Blo 1590994 1592823 := bstep (se 1 (by rfl) ⟨1194617, by rfl⟩ : syracuseStep 1592823 = 2389235) B2389235
theorem B1592843 : Blo 1590994 1592843 := bstep (se 1 (by rfl) ⟨1194632, by rfl⟩ : syracuseStep 1592843 = 2389265) B2389265
theorem B3583511 : Blo 1590994 3583511 := bstep (se 1 (by rfl) ⟨2687633, by rfl⟩ : syracuseStep 3583511 = 5375267) B5375267
theorem B1592855 : Blo 1590994 1592855 := bstep (se 1 (by rfl) ⟨1194641, by rfl⟩ : syracuseStep 1592855 = 2389283) B2389283
theorem B12086819 : Blo 1590994 12086819 := bstep (se 1 (by rfl) ⟨9065114, by rfl⟩ : syracuseStep 12086819 = 18130229) B18130229
theorem B1592875 : Blo 1590994 1592875 := bstep (se 1 (by rfl) ⟨1194656, by rfl⟩ : syracuseStep 1592875 = 2389313) B2389313
theorem B1592887 : Blo 1590994 1592887 := bstep (se 1 (by rfl) ⟨1194665, by rfl⟩ : syracuseStep 1592887 = 2389331) B2389331
theorem B2387531 : Blo 1590994 2387531 := bstep (se 1 (by rfl) ⟨1790648, by rfl⟩ : syracuseStep 2387531 = 3581297) B3581297
theorem B1592907 : Blo 1590994 1592907 := bstep (se 1 (by rfl) ⟨1194680, by rfl⟩ : syracuseStep 1592907 = 2389361) B2389361
theorem B2387543 : Blo 1590994 2387543 := bstep (se 1 (by rfl) ⟨1790657, by rfl⟩ : syracuseStep 2387543 = 3581315) B3581315
theorem B1592919 : Blo 1590994 1592919 := bstep (se 1 (by rfl) ⟨1194689, by rfl⟩ : syracuseStep 1592919 = 2389379) B2389379
theorem B1592939 : Blo 1590994 1592939 := bstep (se 1 (by rfl) ⟨1194704, by rfl⟩ : syracuseStep 1592939 = 2389409) B2389409
theorem B1592951 : Blo 1590994 1592951 := bstep (se 1 (by rfl) ⟨1194713, by rfl⟩ : syracuseStep 1592951 = 2389427) B2389427
theorem B1592971 : Blo 1590994 1592971 := bstep (se 1 (by rfl) ⟨1194728, by rfl⟩ : syracuseStep 1592971 = 2389457) B2389457
theorem B1592983 : Blo 1590994 1592983 := bstep (se 1 (by rfl) ⟨1194737, by rfl⟩ : syracuseStep 1592983 = 2389475) B2389475
theorem B2387609 : Blo 1590994 2387609 := bstep (se 2 (by rfl) ⟨895353, by rfl⟩ : syracuseStep 2387609 = 1790707) B1790707
theorem B3583691 : Blo 1590994 3583691 := bstep (se 1 (by rfl) ⟨2687768, by rfl⟩ : syracuseStep 3583691 = 5375537) B5375537
theorem B3632843 : Blo 1590994 3632843 := bstep (se 1 (by rfl) ⟨2724632, by rfl⟩ : syracuseStep 3632843 = 5449265) B5449265
theorem B3583745 : Blo 1590994 3583745 := bstep (se 2 (by rfl) ⟨1343904, by rfl⟩ : syracuseStep 3583745 = 2687809) B2687809
theorem B2387723 : Blo 1590994 2387723 := bstep (se 1 (by rfl) ⟨1790792, by rfl⟩ : syracuseStep 2387723 = 3581585) B3581585
theorem B9817873 : Blo 1590994 9817873 := bstep (se 2 (by rfl) ⟨3681702, by rfl⟩ : syracuseStep 9817873 = 7363405) B7363405
theorem B2387735 : Blo 1590994 2387735 := bstep (se 1 (by rfl) ⟨1790801, by rfl⟩ : syracuseStep 2387735 = 3581603) B3581603
theorem B5369651 : Blo 1590994 5369651 := bstep (se 1 (by rfl) ⟨4027238, by rfl⟩ : syracuseStep 5369651 = 8054477) B8054477
theorem B5443379 : Blo 1590994 5443379 := bstep (se 1 (by rfl) ⟨4082534, by rfl⟩ : syracuseStep 5443379 = 8165069) B8165069
theorem B2387801 : Blo 1590994 2387801 := bstep (se 2 (by rfl) ⟨895425, by rfl⟩ : syracuseStep 2387801 = 1790851) B1790851
theorem B37277617 : Blo 1590994 37277617 := bstep (se 2 (by rfl) ⟨13979106, by rfl⟩ : syracuseStep 37277617 = 27958213) B27958213
theorem B7647155 : Blo 1590994 7647155 := bstep (se 1 (by rfl) ⟨5735366, by rfl⟩ : syracuseStep 7647155 = 11470733) B11470733
theorem B1789879 : Blo 1590994 1789879 := bstep (se 1 (by rfl) ⟨1342409, by rfl⟩ : syracuseStep 1789879 = 2684819) B2684819
theorem B2387915 : Blo 1590994 2387915 := bstep (se 1 (by rfl) ⟨1790936, by rfl⟩ : syracuseStep 2387915 = 3581873) B3581873
theorem B2387927 : Blo 1590994 2387927 := bstep (se 1 (by rfl) ⟨1790945, by rfl⟩ : syracuseStep 2387927 = 3581891) B3581891
theorem B51654617 : Blo 1590994 51654617 := bstep (se 2 (by rfl) ⟨19370481, by rfl⟩ : syracuseStep 51654617 = 38740963) B38740963
theorem B3583961 : Blo 1590994 3583961 := bstep (se 2 (by rfl) ⟨1343985, by rfl⟩ : syracuseStep 3583961 = 2687971) B2687971
theorem B2387993 : Blo 1590994 2387993 := bstep (se 2 (by rfl) ⟨895497, by rfl⟩ : syracuseStep 2387993 = 1790995) B1790995
theorem B3584051 : Blo 1590994 3584051 := bstep (se 1 (by rfl) ⟨2688038, by rfl⟩ : syracuseStep 3584051 = 5376077) B5376077
theorem B5369921 : Blo 1590994 5369921 := bstep (se 2 (by rfl) ⟨2013720, by rfl⟩ : syracuseStep 5369921 = 4027441) B4027441
theorem B8056907 : Blo 1590994 8056907 := bstep (se 1 (by rfl) ⟨6042680, by rfl⟩ : syracuseStep 8056907 = 12085361) B12085361
theorem B3584087 : Blo 1590994 3584087 := bstep (se 1 (by rfl) ⟨2688065, by rfl⟩ : syracuseStep 3584087 = 5376131) B5376131
theorem B1790059 : Blo 1590994 1790059 := bstep (se 1 (by rfl) ⟨1342544, by rfl⟩ : syracuseStep 1790059 = 2685089) B2685089
theorem B2388107 : Blo 1590994 2388107 := bstep (se 1 (by rfl) ⟨1791080, by rfl⟩ : syracuseStep 2388107 = 3582161) B3582161
theorem B2388119 : Blo 1590994 2388119 := bstep (se 1 (by rfl) ⟨1791089, by rfl⟩ : syracuseStep 2388119 = 3582179) B3582179
theorem B1790167 : Blo 1590994 1790167 := bstep (se 1 (by rfl) ⟨1342625, by rfl⟩ : syracuseStep 1790167 = 2685251) B2685251
theorem B2388185 : Blo 1590994 2388185 := bstep (se 2 (by rfl) ⟨895569, by rfl⟩ : syracuseStep 2388185 = 1791139) B1791139
theorem B2388299 : Blo 1590994 2388299 := bstep (se 1 (by rfl) ⟨1791224, by rfl⟩ : syracuseStep 2388299 = 3582449) B3582449
theorem B2421067 : Blo 1590994 2421067 := bstep (se 1 (by rfl) ⟨1815800, by rfl⟩ : syracuseStep 2421067 = 3631601) B3631601
theorem B2388311 : Blo 1590994 2388311 := bstep (se 1 (by rfl) ⟨1791233, by rfl⟩ : syracuseStep 2388311 = 3582467) B3582467
theorem B1790347 : Blo 1590994 1790347 := bstep (se 1 (by rfl) ⟨1342760, by rfl⟩ : syracuseStep 1790347 = 2685521) B2685521
theorem B2388377 : Blo 1590994 2388377 := bstep (se 2 (by rfl) ⟨895641, by rfl⟩ : syracuseStep 2388377 = 1791283) B1791283
theorem B6042059 : Blo 1590994 6042059 := bstep (se 1 (by rfl) ⟨4531544, by rfl⟩ : syracuseStep 6042059 = 9063089) B9063089
theorem B1700299 : Blo 1590994 1700299 := bstep (se 1 (by rfl) ⟨1275224, by rfl⟩ : syracuseStep 1700299 = 2550449) B2550449
theorem B6042073 : Blo 1590994 6042073 := bstep (se 2 (by rfl) ⟨2265777, by rfl⟩ : syracuseStep 6042073 = 4531555) B4531555
theorem B1790455 : Blo 1590994 1790455 := bstep (se 1 (by rfl) ⟨1342841, by rfl⟩ : syracuseStep 1790455 = 2685683) B2685683
theorem B2388491 : Blo 1590994 2388491 := bstep (se 1 (by rfl) ⟨1791368, by rfl⟩ : syracuseStep 2388491 = 3582737) B3582737
theorem B2388503 : Blo 1590994 2388503 := bstep (se 1 (by rfl) ⟨1791377, by rfl⟩ : syracuseStep 2388503 = 3582755) B3582755
theorem B3445313 : Blo 1590994 3445313 := bstep (se 2 (by rfl) ⟨1291992, by rfl⟩ : syracuseStep 3445313 = 2583985) B2583985
theorem B4534859 : Blo 1590994 4534859 := bstep (se 1 (by rfl) ⟨3401144, by rfl⟩ : syracuseStep 4534859 = 6802289) B6802289
theorem B2388569 : Blo 1590994 2388569 := bstep (se 2 (by rfl) ⟨895713, by rfl⟩ : syracuseStep 2388569 = 1791427) B1791427
theorem B5370461 : Blo 1590994 5370461 := bstep (se 3 (by rfl) ⟨1006961, by rfl⟩ : syracuseStep 5370461 = 2013923) B2013923
theorem B1790635 : Blo 1590994 1790635 := bstep (se 1 (by rfl) ⟨1342976, by rfl⟩ : syracuseStep 1790635 = 2685953) B2685953
theorem B2388683 : Blo 1590994 2388683 := bstep (se 1 (by rfl) ⟨1791512, by rfl⟩ : syracuseStep 2388683 = 3583025) B3583025
theorem B2388695 : Blo 1590994 2388695 := bstep (se 1 (by rfl) ⟨1791521, by rfl⟩ : syracuseStep 2388695 = 3583043) B3583043
theorem B1790743 : Blo 1590994 1790743 := bstep (se 1 (by rfl) ⟨1343057, by rfl⟩ : syracuseStep 1790743 = 2686115) B2686115
theorem B2388761 : Blo 1590994 2388761 := bstep (se 2 (by rfl) ⟨895785, by rfl⟩ : syracuseStep 2388761 = 1791571) B1791571
theorem B13595485 : Blo 1590994 13595485 := bstep (se 3 (by rfl) ⟨2549153, by rfl⟩ : syracuseStep 13595485 = 5098307) B5098307
theorem B2388875 : Blo 1590994 2388875 := bstep (se 1 (by rfl) ⟨1791656, by rfl⟩ : syracuseStep 2388875 = 3583313) B3583313
theorem B2388887 : Blo 1590994 2388887 := bstep (se 1 (by rfl) ⟨1791665, by rfl⟩ : syracuseStep 2388887 = 3583331) B3583331
theorem B1790923 : Blo 1590994 1790923 := bstep (se 1 (by rfl) ⟨1343192, by rfl⟩ : syracuseStep 1790923 = 2686385) B2686385
theorem B2388953 : Blo 1590994 2388953 := bstep (se 2 (by rfl) ⟨895857, by rfl⟩ : syracuseStep 2388953 = 1791715) B1791715
theorem B2298839 : Blo 1590994 2298839 := bstep (se 1 (by rfl) ⟨1724129, by rfl⟩ : syracuseStep 2298839 = 3448259) B3448259
theorem B10204177 : Blo 1590994 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B1791031 : Blo 1590994 1791031 := bstep (se 1 (by rfl) ⟨1343273, by rfl⟩ : syracuseStep 1791031 = 2686547) B2686547
theorem B2389067 : Blo 1590994 2389067 := bstep (se 1 (by rfl) ⟨1791800, by rfl⟩ : syracuseStep 2389067 = 3583601) B3583601
theorem B2389079 : Blo 1590994 2389079 := bstep (se 1 (by rfl) ⟨1791809, by rfl⟩ : syracuseStep 2389079 = 3583619) B3583619
theorem B2389145 : Blo 1590994 2389145 := bstep (se 2 (by rfl) ⟨895929, by rfl⟩ : syracuseStep 2389145 = 1791859) B1791859
theorem B1791211 : Blo 1590994 1791211 := bstep (se 1 (by rfl) ⟨1343408, by rfl⟩ : syracuseStep 1791211 = 2686817) B2686817
theorem B2389259 : Blo 1590994 2389259 := bstep (se 1 (by rfl) ⟨1791944, by rfl⟩ : syracuseStep 2389259 = 3583889) B3583889
theorem B2389271 : Blo 1590994 2389271 := bstep (se 1 (by rfl) ⟨1791953, by rfl⟩ : syracuseStep 2389271 = 3583907) B3583907
theorem B2266393 : Blo 1590994 2266393 := bstep (se 2 (by rfl) ⟨849897, by rfl⟩ : syracuseStep 2266393 = 1699795) B1699795
theorem B7648577 : Blo 1590994 7648577 := bstep (se 2 (by rfl) ⟨2868216, by rfl⟩ : syracuseStep 7648577 = 5736433) B5736433
theorem B1791319 : Blo 1590994 1791319 := bstep (se 1 (by rfl) ⟨1343489, by rfl⟩ : syracuseStep 1791319 = 2686979) B2686979
theorem B2389337 : Blo 1590994 2389337 := bstep (se 2 (by rfl) ⟨896001, by rfl⟩ : syracuseStep 2389337 = 1792003) B1792003
theorem B11482469 : Blo 1590994 11482469 := bstep (se 4 (by rfl) ⟨1076481, by rfl⟩ : syracuseStep 11482469 = 2152963) B2152963
theorem B6043031 : Blo 1590994 6043031 := bstep (se 1 (by rfl) ⟨4532273, by rfl⟩ : syracuseStep 6043031 = 9064547) B9064547
theorem B5739979 : Blo 1590994 5739979 := bstep (se 1 (by rfl) ⟨4304984, by rfl⟩ : syracuseStep 5739979 = 8609969) B8609969
theorem B2389451 : Blo 1590994 2389451 := bstep (se 1 (by rfl) ⟨1792088, by rfl⟩ : syracuseStep 2389451 = 3584177) B3584177
theorem B2389463 : Blo 1590994 2389463 := bstep (se 1 (by rfl) ⟨1792097, by rfl⟩ : syracuseStep 2389463 = 3584195) B3584195
theorem B1791499 : Blo 1590994 1791499 := bstep (se 1 (by rfl) ⟨1343624, by rfl⟩ : syracuseStep 1791499 = 2687249) B2687249
theorem B4027927 : Blo 1590994 4027927 := bstep (se 1 (by rfl) ⟨3020945, by rfl⟩ : syracuseStep 4027927 = 6041891) B6041891
theorem B18134603 : Blo 1590994 18134603 := bstep (se 1 (by rfl) ⟨13600952, by rfl⟩ : syracuseStep 18134603 = 27201905) B27201905
theorem B3823193 : Blo 1590994 3823193 := bstep (se 2 (by rfl) ⟨1433697, by rfl⟩ : syracuseStep 3823193 = 2867395) B2867395
theorem B1791607 : Blo 1590994 1791607 := bstep (se 1 (by rfl) ⟨1343705, by rfl⟩ : syracuseStep 1791607 = 2687411) B2687411
theorem B5371595 : Blo 1590994 5371595 := bstep (se 1 (by rfl) ⟨4028696, by rfl⟩ : syracuseStep 5371595 = 8057393) B8057393
theorem B5445323 : Blo 1590994 5445323 := bstep (se 1 (by rfl) ⟨4083992, by rfl⟩ : syracuseStep 5445323 = 8167985) B8167985
theorem B21796613 : Blo 1590994 21796613 := bstep (se 4 (by rfl) ⟨2043432, by rfl⟩ : syracuseStep 21796613 = 4086865) B4086865
theorem B1791787 : Blo 1590994 1791787 := bstep (se 1 (by rfl) ⟨1343840, by rfl⟩ : syracuseStep 1791787 = 2687681) B2687681
theorem B8058689 : Blo 1590994 8058689 := bstep (se 2 (by rfl) ⟨3022008, by rfl⟩ : syracuseStep 8058689 = 6044017) B6044017
theorem B10205021 : Blo 1590994 10205021 := bstep (se 3 (by rfl) ⟨1913441, by rfl⟩ : syracuseStep 10205021 = 3826883) B3826883
theorem B4536157 : Blo 1590994 4536157 := bstep (se 3 (by rfl) ⟨850529, by rfl⟩ : syracuseStep 4536157 = 1701059) B1701059
theorem B38737763 : Blo 1590994 38737763 := bstep (se 1 (by rfl) ⟨29053322, by rfl⟩ : syracuseStep 38737763 = 58106645) B58106645
theorem B272357261 : Blo 1590994 272357261 := bstep (se 3 (by rfl) ⟨51066986, by rfl⟩ : syracuseStep 272357261 = 102133973) B102133973
theorem B1791895 : Blo 1590994 1791895 := bstep (se 1 (by rfl) ⟨1343921, by rfl⟩ : syracuseStep 1791895 = 2687843) B2687843
theorem B4028363 : Blo 1590994 4028363 := bstep (se 1 (by rfl) ⟨3021272, by rfl⟩ : syracuseStep 4028363 = 6042545) B6042545
theorem B5371865 : Blo 1590994 5371865 := bstep (se 2 (by rfl) ⟨2014449, by rfl⟩ : syracuseStep 5371865 = 4028899) B4028899
theorem B18626635 : Blo 1590994 18626635 := bstep (se 1 (by rfl) ⟨13969976, by rfl⟩ : syracuseStep 18626635 = 27939953) B27939953
theorem B1792075 : Blo 1590994 1792075 := bstep (se 1 (by rfl) ⟨1344056, by rfl⟩ : syracuseStep 1792075 = 2688113) B2688113
theorem B3020915 : Blo 1590994 3020915 := bstep (se 1 (by rfl) ⟨2265686, by rfl⟩ : syracuseStep 3020915 = 4531373) B4531373
theorem B2685143 : Blo 1590994 2685143 := bstep (se 1 (by rfl) ⟨2013857, by rfl⟩ : syracuseStep 2685143 = 4027715) B4027715
theorem B49715461 : Blo 1590994 49715461 := bstep (se 4 (by rfl) ⟨4660824, by rfl⟩ : syracuseStep 49715461 = 9321649) B9321649
theorem B3021067 : Blo 1590994 3021067 := bstep (se 1 (by rfl) ⟨2265800, by rfl⟩ : syracuseStep 3021067 = 4531601) B4531601
theorem B6797591 : Blo 1590994 6797591 := bstep (se 1 (by rfl) ⟨5098193, by rfl⟩ : syracuseStep 6797591 = 10196387) B10196387
theorem B4028737 : Blo 1590994 4028737 := bstep (se 2 (by rfl) ⟨1510776, by rfl⟩ : syracuseStep 4028737 = 3021553) B3021553
theorem B2685271 : Blo 1590994 2685271 := bstep (se 1 (by rfl) ⟨2013953, by rfl⟩ : syracuseStep 2685271 = 4027907) B4027907
theorem B2013655 : Blo 1590994 2013655 := bstep (se 1 (by rfl) ⟨1510241, by rfl⟩ : syracuseStep 2013655 = 3020483) B3020483
theorem B3021401 : Blo 1590994 3021401 := bstep (se 2 (by rfl) ⟨1133025, by rfl⟩ : syracuseStep 3021401 = 2266051) B2266051
theorem B3226241 : Blo 1590994 3226241 := bstep (se 2 (by rfl) ⟨1209840, by rfl⟩ : syracuseStep 3226241 = 2419681) B2419681
theorem B6044291 : Blo 1590994 6044291 := bstep (se 1 (by rfl) ⟨4533218, by rfl⟩ : syracuseStep 6044291 = 9066437) B9066437
theorem B5372567 : Blo 1590994 5372567 := bstep (se 1 (by rfl) ⟨4029425, by rfl⟩ : syracuseStep 5372567 = 8058851) B8058851
theorem B2267851 : Blo 1590994 2267851 := bstep (se 1 (by rfl) ⟨1700888, by rfl⟩ : syracuseStep 2267851 = 3401777) B3401777
theorem B3398411 : Blo 1590994 3398411 := bstep (se 1 (by rfl) ⟨2548808, by rfl⟩ : syracuseStep 3398411 = 5097617) B5097617
theorem B6454039 : Blo 1590994 6454039 := bstep (se 1 (by rfl) ⟨4840529, by rfl⟩ : syracuseStep 6454039 = 9681059) B9681059
theorem B4029335 : Blo 1590994 4029335 := bstep (se 1 (by rfl) ⟨3022001, by rfl⟩ : syracuseStep 4029335 = 6044003) B6044003
theorem B3062681 : Blo 1590994 3062681 := bstep (se 2 (by rfl) ⟨1148505, by rfl⟩ : syracuseStep 3062681 = 2297011) B2297011
theorem B2685899 : Blo 1590994 2685899 := bstep (se 1 (by rfl) ⟨2014424, by rfl⟩ : syracuseStep 2685899 = 4028849) B4028849
theorem B2686027 : Blo 1590994 2686027 := bstep (se 1 (by rfl) ⟨2014520, by rfl⟩ : syracuseStep 2686027 = 4029041) B4029041
theorem B5373107 : Blo 1590994 5373107 := bstep (se 1 (by rfl) ⟨4029830, by rfl⟩ : syracuseStep 5373107 = 8059661) B8059661
theorem B3022039 : Blo 1590994 3022039 := bstep (se 1 (by rfl) ⟨2266529, by rfl⟩ : syracuseStep 3022039 = 4533059) B4533059
theorem B2686169 : Blo 1590994 2686169 := bstep (se 2 (by rfl) ⟨1007313, by rfl⟩ : syracuseStep 2686169 = 2014627) B2014627
theorem B7650521 : Blo 1590994 7650521 := bstep (se 2 (by rfl) ⟨2868945, by rfl⟩ : syracuseStep 7650521 = 5737891) B5737891
theorem B2686297 : Blo 1590994 2686297 := bstep (se 2 (by rfl) ⟨1007361, by rfl⟩ : syracuseStep 2686297 = 2014723) B2014723
theorem B5373377 : Blo 1590994 5373377 := bstep (se 2 (by rfl) ⟨2015016, by rfl⟩ : syracuseStep 5373377 = 4030033) B4030033
theorem B1965655 : Blo 1590994 1965655 := bstep (se 1 (by rfl) ⟨1474241, by rfl⟩ : syracuseStep 1965655 = 2948483) B2948483
theorem B3063425 : Blo 1590994 3063425 := bstep (se 2 (by rfl) ⟨1148784, by rfl⟩ : syracuseStep 3063425 = 2297569) B2297569
theorem B4030145 : Blo 1590994 4030145 := bstep (se 2 (by rfl) ⟨1511304, by rfl⟩ : syracuseStep 4030145 = 3022609) B3022609
theorem B6209227 : Blo 1590994 6209227 := bstep (se 1 (by rfl) ⟨4656920, by rfl⟩ : syracuseStep 6209227 = 9313841) B9313841
theorem B8060633 : Blo 1590994 8060633 := bstep (se 2 (by rfl) ⟨3022737, by rfl⟩ : syracuseStep 8060633 = 6045475) B6045475
theorem B43572977 : Blo 1590994 43572977 := bstep (se 2 (by rfl) ⟨16339866, by rfl⟩ : syracuseStep 43572977 = 32679733) B32679733
theorem B38747969 : Blo 1590994 38747969 := bstep (se 2 (by rfl) ⟨14530488, by rfl⟩ : syracuseStep 38747969 = 29060977) B29060977
theorem B5447513 : Blo 1590994 5447513 := bstep (se 2 (by rfl) ⟨2042817, by rfl⟩ : syracuseStep 5447513 = 4085635) B4085635
theorem B4841309 : Blo 1590994 4841309 := bstep (se 3 (by rfl) ⟨907745, by rfl⟩ : syracuseStep 4841309 = 1815491) B1815491
theorem B2686871 : Blo 1590994 2686871 := bstep (se 1 (by rfl) ⟨2015153, by rfl⟩ : syracuseStep 2686871 = 4030307) B4030307
theorem B3399641 : Blo 1590994 3399641 := bstep (se 2 (by rfl) ⟨1274865, by rfl⟩ : syracuseStep 3399641 = 2549731) B2549731
theorem B5169113 : Blo 1590994 5169113 := bstep (se 2 (by rfl) ⟨1938417, by rfl⟩ : syracuseStep 5169113 = 3876835) B3876835
theorem B5373917 : Blo 1590994 5373917 := bstep (se 3 (by rfl) ⟨1007609, by rfl⟩ : syracuseStep 5373917 = 2015219) B2015219
theorem B8060957 : Blo 1590994 8060957 := bstep (se 3 (by rfl) ⟨1511429, by rfl⟩ : syracuseStep 8060957 = 3022859) B3022859
theorem B3579947 : Blo 1590994 3579947 := bstep (se 1 (by rfl) ⟨2684960, by rfl⟩ : syracuseStep 3579947 = 5369921) B5369921
theorem B2015275 : Blo 1590994 2015275 := bstep (se 1 (by rfl) ⟨1511456, by rfl⟩ : syracuseStep 2015275 = 3022913) B3022913
theorem B2687161 : Blo 1590994 2687161 := bstep (se 2 (by rfl) ⟨1007685, by rfl⟩ : syracuseStep 2687161 = 2015371) B2015371
theorem B5374241 : Blo 1590994 5374241 := bstep (se 2 (by rfl) ⟨2015340, by rfl⟩ : syracuseStep 5374241 = 4030681) B4030681
theorem B3023239 : Blo 1590994 3023239 := bstep (se 1 (by rfl) ⟨2267429, by rfl⟩ : syracuseStep 3023239 = 4534859) B4534859
theorem B3580307 : Blo 1590994 3580307 := bstep (se 1 (by rfl) ⟨2685230, by rfl⟩ : syracuseStep 3580307 = 5370461) B5370461
theorem B3228089 : Blo 1590994 3228089 := bstep (se 2 (by rfl) ⟨1210533, by rfl⟩ : syracuseStep 3228089 = 2421067) B2421067
theorem B2359739 : Blo 1590994 2359739 := bstep (se 1 (by rfl) ⟨1769804, by rfl⟩ : syracuseStep 2359739 = 3539609) B3539609
theorem B3580361 : Blo 1590994 3580361 := bstep (se 2 (by rfl) ⟨1342635, by rfl⟩ : syracuseStep 3580361 = 2685271) B2685271
theorem B8061443 : Blo 1590994 8061443 := bstep (se 1 (by rfl) ⟨6046082, by rfl⟩ : syracuseStep 8061443 = 12092165) B12092165
theorem B3400393 : Blo 1590994 3400393 := bstep (se 2 (by rfl) ⟨1275147, by rfl⟩ : syracuseStep 3400393 = 2550295) B2550295
theorem B30999257 : Blo 1590994 30999257 := bstep (se 2 (by rfl) ⟨11624721, by rfl⟩ : syracuseStep 30999257 = 23249443) B23249443
theorem B28312355 : Blo 1590994 28312355 := bstep (se 1 (by rfl) ⟨21234266, by rfl⟩ : syracuseStep 28312355 = 42468533) B42468533
theorem B5374835 : Blo 1590994 5374835 := bstep (se 1 (by rfl) ⟨4031126, by rfl⟩ : syracuseStep 5374835 = 8062253) B8062253
theorem B2687863 : Blo 1590994 2687863 := bstep (se 1 (by rfl) ⟨2015897, by rfl⟩ : syracuseStep 2687863 = 4031795) B4031795
theorem B3023801 : Blo 1590994 3023801 := bstep (se 2 (by rfl) ⟨1133925, by rfl⟩ : syracuseStep 3023801 = 2267851) B2267851
theorem B9061379 : Blo 1590994 9061379 := bstep (se 1 (by rfl) ⟨6796034, by rfl⟩ : syracuseStep 9061379 = 13592069) B13592069
theorem B2548795 : Blo 1590994 2548795 := bstep (se 1 (by rfl) ⟨1911596, by rfl⟩ : syracuseStep 2548795 = 3823193) B3823193
theorem B2688059 : Blo 1590994 2688059 := bstep (se 1 (by rfl) ⟨2016044, by rfl⟩ : syracuseStep 2688059 = 4032089) B4032089
theorem B4031603 : Blo 1590994 4031603 := bstep (se 1 (by rfl) ⟨3023702, by rfl⟩ : syracuseStep 4031603 = 6047405) B6047405
theorem B3581063 : Blo 1590994 3581063 := bstep (se 1 (by rfl) ⟨2685797, by rfl⟩ : syracuseStep 3581063 = 5371595) B5371595
theorem B3630215 : Blo 1590994 3630215 := bstep (se 1 (by rfl) ⟨2722661, by rfl⟩ : syracuseStep 3630215 = 5445323) B5445323
theorem B6128929 : Blo 1590994 6128929 := bstep (se 2 (by rfl) ⟨2298348, by rfl⟩ : syracuseStep 6128929 = 4596697) B4596697
theorem B3581243 : Blo 1590994 3581243 := bstep (se 1 (by rfl) ⟨2685932, by rfl⟩ : syracuseStep 3581243 = 5371865) B5371865
theorem B6456635 : Blo 1590994 6456635 := bstep (se 1 (by rfl) ⟨4842476, by rfl⟩ : syracuseStep 6456635 = 9684953) B9684953
theorem B3581369 : Blo 1590994 3581369 := bstep (se 2 (by rfl) ⟨1343013, by rfl⟩ : syracuseStep 3581369 = 2686027) B2686027
theorem B4531727 : Blo 1590994 4531727 := bstep (se 1 (by rfl) ⟨3398795, by rfl⟩ : syracuseStep 4531727 = 6797591) B6797591
theorem B2868779 : Blo 1590994 2868779 := bstep (se 1 (by rfl) ⟨2151584, by rfl⟩ : syracuseStep 2868779 = 4303169) B4303169
theorem B4032119 : Blo 1590994 4032119 := bstep (se 1 (by rfl) ⟨3024089, by rfl⟩ : syracuseStep 4032119 = 6048179) B6048179
theorem B8603309 : Blo 1590994 8603309 := bstep (se 3 (by rfl) ⟨1613120, by rfl⟩ : syracuseStep 8603309 = 3226241) B3226241
theorem B8169133 : Blo 1590994 8169133 := bstep (se 3 (by rfl) ⟨1531712, by rfl⟩ : syracuseStep 8169133 = 3063425) B3063425
theorem B1591047 : Blo 1590994 1591047 := bstep (se 1 (by rfl) ⟨1193285, by rfl⟩ : syracuseStep 1591047 = 2386571) B2386571
theorem B1591055 : Blo 1590994 1591055 := bstep (se 1 (by rfl) ⟨1193291, by rfl⟩ : syracuseStep 1591055 = 2386583) B2386583
theorem B3581711 : Blo 1590994 3581711 := bstep (se 1 (by rfl) ⟨2686283, by rfl⟩ : syracuseStep 3581711 = 5372567) B5372567
theorem B3581729 : Blo 1590994 3581729 := bstep (se 2 (by rfl) ⟨1343148, by rfl⟩ : syracuseStep 3581729 = 2686297) B2686297
theorem B1591099 : Blo 1590994 1591099 := bstep (se 1 (by rfl) ⟨1193324, by rfl⟩ : syracuseStep 1591099 = 2386649) B2386649
theorem B10897267 : Blo 1590994 10897267 := bstep (se 1 (by rfl) ⟨8172950, by rfl⟩ : syracuseStep 10897267 = 16345901) B16345901
theorem B2721671 : Blo 1590994 2721671 := bstep (se 1 (by rfl) ⟨2041253, by rfl⟩ : syracuseStep 2721671 = 4082507) B4082507
theorem B1591175 : Blo 1590994 1591175 := bstep (se 1 (by rfl) ⟨1193381, by rfl⟩ : syracuseStep 1591175 = 2386763) B2386763
theorem B1591183 : Blo 1590994 1591183 := bstep (se 1 (by rfl) ⟨1193387, by rfl⟩ : syracuseStep 1591183 = 2386775) B2386775
theorem B2869139 : Blo 1590994 2869139 := bstep (se 1 (by rfl) ⟨2151854, by rfl⟩ : syracuseStep 2869139 = 4303709) B4303709
theorem B7653305 : Blo 1590994 7653305 := bstep (se 2 (by rfl) ⟨2869989, by rfl⟩ : syracuseStep 7653305 = 5739979) B5739979
theorem B1591227 : Blo 1590994 1591227 := bstep (se 1 (by rfl) ⟨1193420, by rfl⟩ : syracuseStep 1591227 = 2386841) B2386841
theorem B2041787 : Blo 1590994 2041787 := bstep (se 1 (by rfl) ⟨1531340, by rfl⟩ : syracuseStep 2041787 = 3062681) B3062681
theorem B1591303 : Blo 1590994 1591303 := bstep (se 1 (by rfl) ⟨1193477, by rfl⟩ : syracuseStep 1591303 = 2386955) B2386955
theorem B1591311 : Blo 1590994 1591311 := bstep (se 1 (by rfl) ⟨1193483, by rfl⟩ : syracuseStep 1591311 = 2386967) B2386967
theorem B1591355 : Blo 1590994 1591355 := bstep (se 1 (by rfl) ⟨1193516, by rfl⟩ : syracuseStep 1591355 = 2387033) B2387033
theorem B8063063 : Blo 1590994 8063063 := bstep (se 1 (by rfl) ⟨6047297, by rfl⟩ : syracuseStep 8063063 = 12094595) B12094595
theorem B3582071 : Blo 1590994 3582071 := bstep (se 1 (by rfl) ⟨2686553, by rfl⟩ : syracuseStep 3582071 = 5373107) B5373107
theorem B1591431 : Blo 1590994 1591431 := bstep (se 1 (by rfl) ⟨1193573, by rfl⟩ : syracuseStep 1591431 = 2387147) B2387147
theorem B1591439 : Blo 1590994 1591439 := bstep (se 1 (by rfl) ⟨1193579, by rfl⟩ : syracuseStep 1591439 = 2387159) B2387159
theorem B11471021 : Blo 1590994 11471021 := bstep (se 3 (by rfl) ⟨2150816, by rfl⟩ : syracuseStep 11471021 = 4301633) B4301633
theorem B1591483 : Blo 1590994 1591483 := bstep (se 1 (by rfl) ⟨1193612, by rfl⟩ : syracuseStep 1591483 = 2387225) B2387225
theorem B1591559 : Blo 1590994 1591559 := bstep (se 1 (by rfl) ⟨1193669, by rfl⟩ : syracuseStep 1591559 = 2387339) B2387339
theorem B1591567 : Blo 1590994 1591567 := bstep (se 1 (by rfl) ⟨1193675, by rfl⟩ : syracuseStep 1591567 = 2387351) B2387351
theorem B3582251 : Blo 1590994 3582251 := bstep (se 1 (by rfl) ⟨2686688, by rfl⟩ : syracuseStep 3582251 = 5373377) B5373377
theorem B1591611 : Blo 1590994 1591611 := bstep (se 1 (by rfl) ⟨1193708, by rfl⟩ : syracuseStep 1591611 = 2387417) B2387417
theorem B1591687 : Blo 1590994 1591687 := bstep (se 1 (by rfl) ⟨1193765, by rfl⟩ : syracuseStep 1591687 = 2387531) B2387531
theorem B1591695 : Blo 1590994 1591695 := bstep (se 1 (by rfl) ⟨1193771, by rfl⟩ : syracuseStep 1591695 = 2387543) B2387543
theorem B1591739 : Blo 1590994 1591739 := bstep (se 1 (by rfl) ⟨1193804, by rfl⟩ : syracuseStep 1591739 = 2387609) B2387609
theorem B6048209 : Blo 1590994 6048209 := bstep (se 2 (by rfl) ⟨2268078, by rfl⟩ : syracuseStep 6048209 = 4536157) B4536157
theorem B1591815 : Blo 1590994 1591815 := bstep (se 1 (by rfl) ⟨1193861, by rfl⟩ : syracuseStep 1591815 = 2387723) B2387723
theorem B1591823 : Blo 1590994 1591823 := bstep (se 1 (by rfl) ⟨1193867, by rfl⟩ : syracuseStep 1591823 = 2387735) B2387735
theorem B25831979 : Blo 1590994 25831979 := bstep (se 1 (by rfl) ⟨19373984, by rfl⟩ : syracuseStep 25831979 = 38747969) B38747969
theorem B1591867 : Blo 1590994 1591867 := bstep (se 1 (by rfl) ⟨1193900, by rfl⟩ : syracuseStep 1591867 = 2387801) B2387801
theorem B3631675 : Blo 1590994 3631675 := bstep (se 1 (by rfl) ⟨2723756, by rfl⟩ : syracuseStep 3631675 = 5447513) B5447513
theorem B8063549 : Blo 1590994 8063549 := bstep (se 3 (by rfl) ⟨1511915, by rfl⟩ : syracuseStep 8063549 = 3023831) B3023831
theorem B6130237 : Blo 1590994 6130237 := bstep (se 3 (by rfl) ⟨1149419, by rfl⟩ : syracuseStep 6130237 = 2298839) B2298839
theorem B49703489 : Blo 1590994 49703489 := bstep (se 2 (by rfl) ⟨18638808, by rfl⟩ : syracuseStep 49703489 = 37277617) B37277617
theorem B2386505 : Blo 1590994 2386505 := bstep (se 2 (by rfl) ⟨894939, by rfl⟩ : syracuseStep 2386505 = 1789879) B1789879
theorem B5098103 : Blo 1590994 5098103 := bstep (se 1 (by rfl) ⟨3823577, by rfl⟩ : syracuseStep 5098103 = 7647155) B7647155
theorem B1591943 : Blo 1590994 1591943 := bstep (se 1 (by rfl) ⟨1193957, by rfl⟩ : syracuseStep 1591943 = 2387915) B2387915
theorem B1591951 : Blo 1590994 1591951 := bstep (se 1 (by rfl) ⟨1193963, by rfl⟩ : syracuseStep 1591951 = 2387927) B2387927
theorem B3582611 : Blo 1590994 3582611 := bstep (se 1 (by rfl) ⟨2686958, by rfl⟩ : syracuseStep 3582611 = 5373917) B5373917
theorem B2386619 : Blo 1590994 2386619 := bstep (se 1 (by rfl) ⟨1789964, by rfl⟩ : syracuseStep 2386619 = 3579929) B3579929
theorem B1591995 : Blo 1590994 1591995 := bstep (se 1 (by rfl) ⟨1193996, by rfl⟩ : syracuseStep 1591995 = 2387993) B2387993
theorem B3582665 : Blo 1590994 3582665 := bstep (se 2 (by rfl) ⟨1343499, by rfl⟩ : syracuseStep 3582665 = 2686999) B2686999
theorem B2386679 : Blo 1590994 2386679 := bstep (se 1 (by rfl) ⟨1790009, by rfl⟩ : syracuseStep 2386679 = 3580019) B3580019
theorem B1592071 : Blo 1590994 1592071 := bstep (se 1 (by rfl) ⟨1194053, by rfl⟩ : syracuseStep 1592071 = 2388107) B2388107
theorem B2386703 : Blo 1590994 2386703 := bstep (se 1 (by rfl) ⟨1790027, by rfl⟩ : syracuseStep 2386703 = 3580055) B3580055
theorem B1592079 : Blo 1590994 1592079 := bstep (se 1 (by rfl) ⟨1194059, by rfl⟩ : syracuseStep 1592079 = 2388119) B2388119
theorem B2386745 : Blo 1590994 2386745 := bstep (se 2 (by rfl) ⟨895029, by rfl⟩ : syracuseStep 2386745 = 1790059) B1790059
theorem B8055611 : Blo 1590994 8055611 := bstep (se 1 (by rfl) ⟨6041708, by rfl⟩ : syracuseStep 8055611 = 12083417) B12083417
theorem B1592123 : Blo 1590994 1592123 := bstep (se 1 (by rfl) ⟨1194092, by rfl⟩ : syracuseStep 1592123 = 2388185) B2388185
theorem B10201945 : Blo 1590994 10201945 := bstep (se 2 (by rfl) ⟨3825729, by rfl⟩ : syracuseStep 10201945 = 7651459) B7651459
theorem B2386823 : Blo 1590994 2386823 := bstep (se 1 (by rfl) ⟨1790117, by rfl⟩ : syracuseStep 2386823 = 3580235) B3580235
theorem B1592199 : Blo 1590994 1592199 := bstep (se 1 (by rfl) ⟨1194149, by rfl⟩ : syracuseStep 1592199 = 2388299) B2388299
theorem B1592207 : Blo 1590994 1592207 := bstep (se 1 (by rfl) ⟨1194155, by rfl⟩ : syracuseStep 1592207 = 2388311) B2388311
theorem B2386859 : Blo 1590994 2386859 := bstep (se 1 (by rfl) ⟨1790144, by rfl⟩ : syracuseStep 2386859 = 3580289) B3580289
theorem B1592251 : Blo 1590994 1592251 := bstep (se 1 (by rfl) ⟨1194188, by rfl⟩ : syracuseStep 1592251 = 2388377) B2388377
theorem B2386889 : Blo 1590994 2386889 := bstep (se 2 (by rfl) ⟨895083, by rfl⟩ : syracuseStep 2386889 = 1790167) B1790167
theorem B12905419 : Blo 1590994 12905419 := bstep (se 1 (by rfl) ⟨9679064, by rfl⟩ : syracuseStep 12905419 = 19358129) B19358129
theorem B8055773 : Blo 1590994 8055773 := bstep (se 3 (by rfl) ⟨1510457, by rfl⟩ : syracuseStep 8055773 = 3020915) B3020915
theorem B1911799 : Blo 1590994 1911799 := bstep (se 1 (by rfl) ⟨1433849, by rfl⟩ : syracuseStep 1911799 = 2867699) B2867699
theorem B1592327 : Blo 1590994 1592327 := bstep (se 1 (by rfl) ⟨1194245, by rfl⟩ : syracuseStep 1592327 = 2388491) B2388491
theorem B1592335 : Blo 1590994 1592335 := bstep (se 1 (by rfl) ⟨1194251, by rfl⟩ : syracuseStep 1592335 = 2388503) B2388503
theorem B209447957 : Blo 1590994 209447957 := bstep (se 6 (by rfl) ⟨4908936, by rfl⟩ : syracuseStep 209447957 = 9817873) B9817873
theorem B7646231 : Blo 1590994 7646231 := bstep (se 1 (by rfl) ⟨5734673, by rfl⟩ : syracuseStep 7646231 = 11469347) B11469347
theorem B2387003 : Blo 1590994 2387003 := bstep (se 1 (by rfl) ⟨1790252, by rfl⟩ : syracuseStep 2387003 = 3580505) B3580505
theorem B1592379 : Blo 1590994 1592379 := bstep (se 1 (by rfl) ⟨1194284, by rfl⟩ : syracuseStep 1592379 = 2388569) B2388569
theorem B12086333 : Blo 1590994 12086333 := bstep (se 3 (by rfl) ⟨2266187, by rfl⟩ : syracuseStep 12086333 = 4532375) B4532375
theorem B2387063 : Blo 1590994 2387063 := bstep (se 1 (by rfl) ⟨1790297, by rfl⟩ : syracuseStep 2387063 = 3580595) B3580595
theorem B4533367 : Blo 1590994 4533367 := bstep (se 1 (by rfl) ⟨3400025, by rfl⟩ : syracuseStep 4533367 = 6800051) B6800051
theorem B1592455 : Blo 1590994 1592455 := bstep (se 1 (by rfl) ⟨1194341, by rfl⟩ : syracuseStep 1592455 = 2388683) B2388683
theorem B2387087 : Blo 1590994 2387087 := bstep (se 1 (by rfl) ⟨1790315, by rfl⟩ : syracuseStep 2387087 = 3580631) B3580631
theorem B1592463 : Blo 1590994 1592463 := bstep (se 1 (by rfl) ⟨1194347, by rfl⟩ : syracuseStep 1592463 = 2388695) B2388695
theorem B4533401 : Blo 1590994 4533401 := bstep (se 2 (by rfl) ⟨1700025, by rfl⟩ : syracuseStep 4533401 = 3400051) B3400051
theorem B2387129 : Blo 1590994 2387129 := bstep (se 2 (by rfl) ⟨895173, by rfl⟩ : syracuseStep 2387129 = 1790347) B1790347
theorem B1592507 : Blo 1590994 1592507 := bstep (se 1 (by rfl) ⟨1194380, by rfl⟩ : syracuseStep 1592507 = 2388761) B2388761
theorem B10333421 : Blo 1590994 10333421 := bstep (se 3 (by rfl) ⟨1937516, by rfl⟩ : syracuseStep 10333421 = 3875033) B3875033
theorem B2387207 : Blo 1590994 2387207 := bstep (se 1 (by rfl) ⟨1790405, by rfl⟩ : syracuseStep 2387207 = 3580811) B3580811
theorem B1592583 : Blo 1590994 1592583 := bstep (se 1 (by rfl) ⟨1194437, by rfl⟩ : syracuseStep 1592583 = 2388875) B2388875
theorem B4533515 : Blo 1590994 4533515 := bstep (se 1 (by rfl) ⟨3400136, by rfl⟩ : syracuseStep 4533515 = 6800273) B6800273
theorem B1592591 : Blo 1590994 1592591 := bstep (se 1 (by rfl) ⟨1194443, by rfl⟩ : syracuseStep 1592591 = 2388887) B2388887
theorem B8056097 : Blo 1590994 8056097 := bstep (se 2 (by rfl) ⟨3021036, by rfl⟩ : syracuseStep 8056097 = 6042073) B6042073
theorem B2387243 : Blo 1590994 2387243 := bstep (se 1 (by rfl) ⟨1790432, by rfl⟩ : syracuseStep 2387243 = 3580865) B3580865
theorem B1592635 : Blo 1590994 1592635 := bstep (se 1 (by rfl) ⟨1194476, by rfl⟩ : syracuseStep 1592635 = 2388953) B2388953
theorem B2387273 : Blo 1590994 2387273 := bstep (se 2 (by rfl) ⟨895227, by rfl⟩ : syracuseStep 2387273 = 1790455) B1790455
theorem B3583367 : Blo 1590994 3583367 := bstep (se 1 (by rfl) ⟨2687525, by rfl⟩ : syracuseStep 3583367 = 5375051) B5375051
theorem B1592711 : Blo 1590994 1592711 := bstep (se 1 (by rfl) ⟨1194533, by rfl⟩ : syracuseStep 1592711 = 2389067) B2389067
theorem B1592719 : Blo 1590994 1592719 := bstep (se 1 (by rfl) ⟨1194539, by rfl⟩ : syracuseStep 1592719 = 2389079) B2389079
theorem B2387387 : Blo 1590994 2387387 := bstep (se 1 (by rfl) ⟨1790540, by rfl⟩ : syracuseStep 2387387 = 3581081) B3581081
theorem B1592763 : Blo 1590994 1592763 := bstep (se 1 (by rfl) ⟨1194572, by rfl⟩ : syracuseStep 1592763 = 2389145) B2389145
theorem B15297997 : Blo 1590994 15297997 := bstep (se 3 (by rfl) ⟨2868374, by rfl⟩ : syracuseStep 15297997 = 5736749) B5736749
theorem B2387447 : Blo 1590994 2387447 := bstep (se 1 (by rfl) ⟨1790585, by rfl⟩ : syracuseStep 2387447 = 3581171) B3581171
theorem B1592839 : Blo 1590994 1592839 := bstep (se 1 (by rfl) ⟨1194629, by rfl⟩ : syracuseStep 1592839 = 2389259) B2389259
theorem B2387471 : Blo 1590994 2387471 := bstep (se 1 (by rfl) ⟨1790603, by rfl⟩ : syracuseStep 2387471 = 3581207) B3581207
theorem B1592847 : Blo 1590994 1592847 := bstep (se 1 (by rfl) ⟨1194635, by rfl⟩ : syracuseStep 1592847 = 2389271) B2389271
theorem B6802973 : Blo 1590994 6802973 := bstep (se 3 (by rfl) ⟨1275557, by rfl⟩ : syracuseStep 6802973 = 2551115) B2551115
theorem B5099051 : Blo 1590994 5099051 := bstep (se 1 (by rfl) ⟨3824288, by rfl⟩ : syracuseStep 5099051 = 7648577) B7648577
theorem B2387513 : Blo 1590994 2387513 := bstep (se 2 (by rfl) ⟨895317, by rfl⟩ : syracuseStep 2387513 = 1790635) B1790635
theorem B3583547 : Blo 1590994 3583547 := bstep (se 1 (by rfl) ⟨2687660, by rfl⟩ : syracuseStep 3583547 = 5375321) B5375321
theorem B1592891 : Blo 1590994 1592891 := bstep (se 1 (by rfl) ⟨1194668, by rfl⟩ : syracuseStep 1592891 = 2389337) B2389337
theorem B7654979 : Blo 1590994 7654979 := bstep (se 1 (by rfl) ⟨5741234, by rfl⟩ : syracuseStep 7654979 = 11482469) B11482469
theorem B2387591 : Blo 1590994 2387591 := bstep (se 1 (by rfl) ⟨1790693, by rfl⟩ : syracuseStep 2387591 = 3581387) B3581387
theorem B1592967 : Blo 1590994 1592967 := bstep (se 1 (by rfl) ⟨1194725, by rfl⟩ : syracuseStep 1592967 = 2389451) B2389451
theorem B1592975 : Blo 1590994 1592975 := bstep (se 1 (by rfl) ⟨1194731, by rfl⟩ : syracuseStep 1592975 = 2389463) B2389463
theorem B2387627 : Blo 1590994 2387627 := bstep (se 1 (by rfl) ⟨1790720, by rfl⟩ : syracuseStep 2387627 = 3581441) B3581441
theorem B3583673 : Blo 1590994 3583673 := bstep (se 2 (by rfl) ⟨1343877, by rfl⟩ : syracuseStep 3583673 = 2687755) B2687755
theorem B2387657 : Blo 1590994 2387657 := bstep (se 2 (by rfl) ⟨895371, by rfl⟩ : syracuseStep 2387657 = 1790743) B1790743
theorem B8605385 : Blo 1590994 8605385 := bstep (se 2 (by rfl) ⟨3227019, by rfl⟩ : syracuseStep 8605385 = 6454039) B6454039
theorem B2387771 : Blo 1590994 2387771 := bstep (se 1 (by rfl) ⟨1790828, by rfl⟩ : syracuseStep 2387771 = 3581657) B3581657
theorem B27193157 : Blo 1590994 27193157 := bstep (se 4 (by rfl) ⟨2549358, by rfl⟩ : syracuseStep 27193157 = 5098717) B5098717
theorem B2387831 : Blo 1590994 2387831 := bstep (se 1 (by rfl) ⟨1790873, by rfl⟩ : syracuseStep 2387831 = 3581747) B3581747
theorem B2387855 : Blo 1590994 2387855 := bstep (se 1 (by rfl) ⟨1790891, by rfl⟩ : syracuseStep 2387855 = 3581783) B3581783
theorem B6803347 : Blo 1590994 6803347 := bstep (se 1 (by rfl) ⟨5102510, by rfl⟩ : syracuseStep 6803347 = 10205021) B10205021
theorem B25825175 : Blo 1590994 25825175 := bstep (se 1 (by rfl) ⟨19368881, by rfl⟩ : syracuseStep 25825175 = 38737763) B38737763
theorem B181571507 : Blo 1590994 181571507 := bstep (se 1 (by rfl) ⟨136178630, by rfl⟩ : syracuseStep 181571507 = 272357261) B272357261
theorem B2387897 : Blo 1590994 2387897 := bstep (se 2 (by rfl) ⟨895461, by rfl⟩ : syracuseStep 2387897 = 1790923) B1790923
theorem B9072587 : Blo 1590994 9072587 := bstep (se 1 (by rfl) ⟨6804440, by rfl⟩ : syracuseStep 9072587 = 13608881) B13608881
theorem B2387975 : Blo 1590994 2387975 := bstep (se 1 (by rfl) ⟨1790981, by rfl⟩ : syracuseStep 2387975 = 3581963) B3581963
theorem B5369867 : Blo 1590994 5369867 := bstep (se 1 (by rfl) ⟨4027400, by rfl⟩ : syracuseStep 5369867 = 8054801) B8054801
theorem B3584015 : Blo 1590994 3584015 := bstep (se 1 (by rfl) ⟨2688011, by rfl⟩ : syracuseStep 3584015 = 5376023) B5376023
theorem B3584033 : Blo 1590994 3584033 := bstep (se 2 (by rfl) ⟨1344012, by rfl⟩ : syracuseStep 3584033 = 2688025) B2688025
theorem B2388011 : Blo 1590994 2388011 := bstep (se 1 (by rfl) ⟨1791008, by rfl⟩ : syracuseStep 2388011 = 3582017) B3582017
theorem B2388041 : Blo 1590994 2388041 := bstep (se 2 (by rfl) ⟨895515, by rfl⟩ : syracuseStep 2388041 = 1791031) B1791031
theorem B5369975 : Blo 1590994 5369975 := bstep (se 1 (by rfl) ⟨4027481, by rfl⟩ : syracuseStep 5369975 = 8054963) B8054963
theorem B1790095 : Blo 1590994 1790095 := bstep (se 1 (by rfl) ⟨1342571, by rfl⟩ : syracuseStep 1790095 = 2685143) B2685143
theorem B9187501 : Blo 1590994 9187501 := bstep (se 3 (by rfl) ⟨1722656, by rfl⟩ : syracuseStep 9187501 = 3445313) B3445313
theorem B2388155 : Blo 1590994 2388155 := bstep (se 1 (by rfl) ⟨1791116, by rfl⟩ : syracuseStep 2388155 = 3582233) B3582233
theorem B8057069 : Blo 1590994 8057069 := bstep (se 3 (by rfl) ⟨1510700, by rfl⟩ : syracuseStep 8057069 = 3021401) B3021401
theorem B2388215 : Blo 1590994 2388215 := bstep (se 1 (by rfl) ⟨1791161, by rfl⟩ : syracuseStep 2388215 = 3582323) B3582323
theorem B2388239 : Blo 1590994 2388239 := bstep (se 1 (by rfl) ⟨1791179, by rfl⟩ : syracuseStep 2388239 = 3582359) B3582359
theorem B2388281 : Blo 1590994 2388281 := bstep (se 2 (by rfl) ⟨895605, by rfl⟩ : syracuseStep 2388281 = 1791211) B1791211
theorem B4534643 : Blo 1590994 4534643 := bstep (se 1 (by rfl) ⟨3400982, by rfl⟩ : syracuseStep 4534643 = 6801965) B6801965
theorem B2388359 : Blo 1590994 2388359 := bstep (se 1 (by rfl) ⟨1791269, by rfl⟩ : syracuseStep 2388359 = 3582539) B3582539
theorem B1700239 : Blo 1590994 1700239 := bstep (se 1 (by rfl) ⟨1275179, by rfl⟩ : syracuseStep 1700239 = 2550359) B2550359
theorem B2388395 : Blo 1590994 2388395 := bstep (se 1 (by rfl) ⟨1791296, by rfl⟩ : syracuseStep 2388395 = 3582593) B3582593
theorem B2388425 : Blo 1590994 2388425 := bstep (se 2 (by rfl) ⟨895659, by rfl⟩ : syracuseStep 2388425 = 1791319) B1791319
theorem B2265607 : Blo 1590994 2265607 := bstep (se 1 (by rfl) ⟨1699205, by rfl⟩ : syracuseStep 2265607 = 3398411) B3398411
theorem B2388539 : Blo 1590994 2388539 := bstep (se 1 (by rfl) ⟨1791404, by rfl⟩ : syracuseStep 2388539 = 3582809) B3582809
theorem B2388599 : Blo 1590994 2388599 := bstep (se 1 (by rfl) ⟨1791449, by rfl⟩ : syracuseStep 2388599 = 3582899) B3582899
theorem B1790599 : Blo 1590994 1790599 := bstep (se 1 (by rfl) ⟨1342949, by rfl⟩ : syracuseStep 1790599 = 2685899) B2685899
theorem B2388623 : Blo 1590994 2388623 := bstep (se 1 (by rfl) ⟨1791467, by rfl⟩ : syracuseStep 2388623 = 3582935) B3582935
theorem B2388665 : Blo 1590994 2388665 := bstep (se 2 (by rfl) ⟨895749, by rfl⟩ : syracuseStep 2388665 = 1791499) B1791499
theorem B5370569 : Blo 1590994 5370569 := bstep (se 2 (by rfl) ⟨2013963, by rfl⟩ : syracuseStep 5370569 = 4027927) B4027927
theorem B1913591 : Blo 1590994 1913591 := bstep (se 1 (by rfl) ⟨1435193, by rfl⟩ : syracuseStep 1913591 = 2870387) B2870387
theorem B4535041 : Blo 1590994 4535041 := bstep (se 2 (by rfl) ⟨1700640, by rfl⟩ : syracuseStep 4535041 = 3401281) B3401281
theorem B2388743 : Blo 1590994 2388743 := bstep (se 1 (by rfl) ⟨1791557, by rfl⟩ : syracuseStep 2388743 = 3583115) B3583115
theorem B1700615 : Blo 1590994 1700615 := bstep (se 1 (by rfl) ⟨1275461, by rfl⟩ : syracuseStep 1700615 = 2550923) B2550923
theorem B2388779 : Blo 1590994 2388779 := bstep (se 1 (by rfl) ⟨1791584, by rfl⟩ : syracuseStep 2388779 = 3583169) B3583169
theorem B1790779 : Blo 1590994 1790779 := bstep (se 1 (by rfl) ⟨1343084, by rfl⟩ : syracuseStep 1790779 = 2686169) B2686169
theorem B5100347 : Blo 1590994 5100347 := bstep (se 1 (by rfl) ⟨3825260, by rfl⟩ : syracuseStep 5100347 = 7650521) B7650521
theorem B4535099 : Blo 1590994 4535099 := bstep (se 1 (by rfl) ⟨3401324, by rfl⟩ : syracuseStep 4535099 = 6802649) B6802649
theorem B2388809 : Blo 1590994 2388809 := bstep (se 2 (by rfl) ⟨895803, by rfl⟩ : syracuseStep 2388809 = 1791607) B1791607
theorem B8278969 : Blo 1590994 8278969 := bstep (se 2 (by rfl) ⟨3104613, by rfl⟩ : syracuseStep 8278969 = 6209227) B6209227
theorem B2388923 : Blo 1590994 2388923 := bstep (se 1 (by rfl) ⟨1791692, by rfl⟩ : syracuseStep 2388923 = 3583385) B3583385
theorem B2388983 : Blo 1590994 2388983 := bstep (se 1 (by rfl) ⟨1791737, by rfl⟩ : syracuseStep 2388983 = 3583475) B3583475
theorem B2389007 : Blo 1590994 2389007 := bstep (se 1 (by rfl) ⟨1791755, by rfl⟩ : syracuseStep 2389007 = 3583511) B3583511
theorem B8057879 : Blo 1590994 8057879 := bstep (se 1 (by rfl) ⟨6043409, by rfl⟩ : syracuseStep 8057879 = 12086819) B12086819
theorem B2389049 : Blo 1590994 2389049 := bstep (se 2 (by rfl) ⟨895893, by rfl⟩ : syracuseStep 2389049 = 1791787) B1791787
theorem B2389127 : Blo 1590994 2389127 := bstep (se 1 (by rfl) ⟨1791845, by rfl⟩ : syracuseStep 2389127 = 3583691) B3583691
theorem B2421895 : Blo 1590994 2421895 := bstep (se 1 (by rfl) ⟨1816421, by rfl⟩ : syracuseStep 2421895 = 3632843) B3632843
theorem B2389163 : Blo 1590994 2389163 := bstep (se 1 (by rfl) ⟨1791872, by rfl⟩ : syracuseStep 2389163 = 3583745) B3583745
theorem B2389193 : Blo 1590994 2389193 := bstep (se 2 (by rfl) ⟨895947, by rfl⟩ : syracuseStep 2389193 = 1791895) B1791895
theorem B1791247 : Blo 1590994 1791247 := bstep (se 1 (by rfl) ⟨1343435, by rfl⟩ : syracuseStep 1791247 = 2686871) B2686871
theorem B2266427 : Blo 1590994 2266427 := bstep (se 1 (by rfl) ⟨1699820, by rfl⟩ : syracuseStep 2266427 = 3399641) B3399641
theorem B3446075 : Blo 1590994 3446075 := bstep (se 1 (by rfl) ⟨2584556, by rfl⟩ : syracuseStep 3446075 = 5169113) B5169113
theorem B34436411 : Blo 1590994 34436411 := bstep (se 1 (by rfl) ⟨25827308, by rfl⟩ : syracuseStep 34436411 = 51654617) B51654617
theorem B2389307 : Blo 1590994 2389307 := bstep (se 1 (by rfl) ⟨1791980, by rfl⟩ : syracuseStep 2389307 = 3583961) B3583961
theorem B2389367 : Blo 1590994 2389367 := bstep (se 1 (by rfl) ⟨1792025, by rfl⟩ : syracuseStep 2389367 = 3584051) B3584051
theorem B3822983 : Blo 1590994 3822983 := bstep (se 1 (by rfl) ⟨2867237, by rfl⟩ : syracuseStep 3822983 = 5734475) B5734475
theorem B5371271 : Blo 1590994 5371271 := bstep (se 1 (by rfl) ⟨4028453, by rfl⟩ : syracuseStep 5371271 = 8056907) B8056907
theorem B2389391 : Blo 1590994 2389391 := bstep (se 1 (by rfl) ⟨1792043, by rfl⟩ : syracuseStep 2389391 = 3584087) B3584087
theorem B5739923 : Blo 1590994 5739923 := bstep (se 1 (by rfl) ⟨4304942, by rfl⟩ : syracuseStep 5739923 = 8609885) B8609885
theorem B24835513 : Blo 1590994 24835513 := bstep (se 2 (by rfl) ⟨9313317, by rfl⟩ : syracuseStep 24835513 = 18626635) B18626635
theorem B2389433 : Blo 1590994 2389433 := bstep (se 2 (by rfl) ⟨896037, by rfl⟩ : syracuseStep 2389433 = 1792075) B1792075
theorem B7648829 : Blo 1590994 7648829 := bstep (se 3 (by rfl) ⟨1434155, by rfl⟩ : syracuseStep 7648829 = 2868311) B2868311
theorem B4028039 : Blo 1590994 4028039 := bstep (se 1 (by rfl) ⟨3021029, by rfl⟩ : syracuseStep 4028039 = 6042059) B6042059
theorem B4028089 : Blo 1590994 4028089 := bstep (se 2 (by rfl) ⟨1510533, by rfl⟩ : syracuseStep 4028089 = 3021067) B3021067
theorem B2266871 : Blo 1590994 2266871 := bstep (se 1 (by rfl) ⟨1700153, by rfl⟩ : syracuseStep 2266871 = 3400307) B3400307
theorem B5371649 : Blo 1590994 5371649 := bstep (se 2 (by rfl) ⟨2014368, by rfl⟩ : syracuseStep 5371649 = 4028737) B4028737
theorem B1791751 : Blo 1590994 1791751 := bstep (se 1 (by rfl) ⟨1343813, by rfl⟩ : syracuseStep 1791751 = 2687627) B2687627
theorem B2267065 : Blo 1590994 2267065 := bstep (se 2 (by rfl) ⟨850149, by rfl⟩ : syracuseStep 2267065 = 1700299) B1700299
theorem B1791931 : Blo 1590994 1791931 := bstep (se 1 (by rfl) ⟨1343948, by rfl⟩ : syracuseStep 1791931 = 2687897) B2687897
theorem B2684873 : Blo 1590994 2684873 := bstep (se 2 (by rfl) ⟨1006827, by rfl⟩ : syracuseStep 2684873 = 2013655) B2013655
theorem B31004695 : Blo 1590994 31004695 := bstep (se 1 (by rfl) ⟨23253521, by rfl⟩ : syracuseStep 31004695 = 46507043) B46507043
theorem B4085819 : Blo 1590994 4085819 := bstep (se 1 (by rfl) ⟨3064364, by rfl⟩ : syracuseStep 4085819 = 6128729) B6128729
theorem B15300845 : Blo 1590994 15300845 := bstep (se 3 (by rfl) ⟨2868908, by rfl⟩ : syracuseStep 15300845 = 5737817) B5737817
theorem B4028687 : Blo 1590994 4028687 := bstep (se 1 (by rfl) ⟨3021515, by rfl⟩ : syracuseStep 4028687 = 6043031) B6043031
theorem B14522759 : Blo 1590994 14522759 := bstep (se 1 (by rfl) ⟨10892069, by rfl⟩ : syracuseStep 14522759 = 21784139) B21784139
theorem B12089735 : Blo 1590994 12089735 := bstep (se 1 (by rfl) ⟨9067301, by rfl⟩ : syracuseStep 12089735 = 18134603) B18134603
theorem B8608153 : Blo 1590994 8608153 := bstep (se 2 (by rfl) ⟨3228057, by rfl⟩ : syracuseStep 8608153 = 6456115) B6456115
theorem B9066937 : Blo 1590994 9066937 := bstep (se 2 (by rfl) ⟨3400101, by rfl⟩ : syracuseStep 9066937 = 6800203) B6800203
theorem B18127313 : Blo 1590994 18127313 := bstep (se 2 (by rfl) ⟨6797742, by rfl⟩ : syracuseStep 18127313 = 13595485) B13595485
theorem B14531075 : Blo 1590994 14531075 := bstep (se 1 (by rfl) ⟨10898306, by rfl⟩ : syracuseStep 14531075 = 21796613) B21796613
theorem B5372459 : Blo 1590994 5372459 := bstep (se 1 (by rfl) ⟨4029344, by rfl⟩ : syracuseStep 5372459 = 8058689) B8058689
theorem B3021371 : Blo 1590994 3021371 := bstep (se 1 (by rfl) ⟨2266028, by rfl⟩ : syracuseStep 3021371 = 4532057) B4532057
theorem B2685575 : Blo 1590994 2685575 := bstep (se 1 (by rfl) ⟨2014181, by rfl⟩ : syracuseStep 2685575 = 4028363) B4028363
theorem B3398291 : Blo 1590994 3398291 := bstep (se 1 (by rfl) ⟨2548718, by rfl⟩ : syracuseStep 3398291 = 5097437) B5097437
theorem B13605569 : Blo 1590994 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B265149125 : Blo 1590994 265149125 := bstep (se 4 (by rfl) ⟨24857730, by rfl⟩ : syracuseStep 265149125 = 49715461) B49715461
theorem B4029385 : Blo 1590994 4029385 := bstep (se 2 (by rfl) ⟨1511019, by rfl⟩ : syracuseStep 4029385 = 3022039) B3022039
theorem B3021857 : Blo 1590994 3021857 := bstep (se 2 (by rfl) ⟨1133196, by rfl⟩ : syracuseStep 3021857 = 2266393) B2266393
theorem B4840481 : Blo 1590994 4840481 := bstep (se 2 (by rfl) ⟨1815180, by rfl⟩ : syracuseStep 4840481 = 3630361) B3630361
theorem B4029527 : Blo 1590994 4029527 := bstep (se 1 (by rfl) ⟨3022145, by rfl⟩ : syracuseStep 4029527 = 6044291) B6044291
theorem B7462145 : Blo 1590994 7462145 := bstep (se 2 (by rfl) ⟨2798304, by rfl⟩ : syracuseStep 7462145 = 5596609) B5596609
theorem B2686223 : Blo 1590994 2686223 := bstep (se 1 (by rfl) ⟨2014667, by rfl⟩ : syracuseStep 2686223 = 4029335) B4029335
theorem B3022123 : Blo 1590994 3022123 := bstep (se 1 (by rfl) ⟨2266592, by rfl⟩ : syracuseStep 3022123 = 4533185) B4533185
theorem B4660595 : Blo 1590994 4660595 := bstep (se 1 (by rfl) ⟨3495446, by rfl⟩ : syracuseStep 4660595 = 6990893) B6990893
theorem B1613243 : Blo 1590994 1613243 := bstep (se 1 (by rfl) ⟨1209932, by rfl⟩ : syracuseStep 1613243 = 2419865) B2419865
theorem B2620873 : Blo 1590994 2620873 := bstep (se 2 (by rfl) ⟨982827, by rfl⟩ : syracuseStep 2620873 = 1965655) B1965655
theorem B7650845 : Blo 1590994 7650845 := bstep (se 3 (by rfl) ⟨1434533, by rfl⟩ : syracuseStep 7650845 = 2869067) B2869067
theorem B2686763 : Blo 1590994 2686763 := bstep (se 1 (by rfl) ⟨2015072, by rfl⟩ : syracuseStep 2686763 = 4030145) B4030145
theorem B5373755 : Blo 1590994 5373755 := bstep (se 1 (by rfl) ⟨4030316, by rfl⟩ : syracuseStep 5373755 = 8060633) B8060633
theorem B29048651 : Blo 1590994 29048651 := bstep (se 1 (by rfl) ⟨21786488, by rfl⟩ : syracuseStep 29048651 = 43572977) B43572977
theorem B3579767 : Blo 1590994 3579767 := bstep (se 1 (by rfl) ⟨2684825, by rfl⟩ : syracuseStep 3579767 = 5369651) B5369651
theorem B3628919 : Blo 1590994 3628919 := bstep (se 1 (by rfl) ⟨2721689, by rfl⟩ : syracuseStep 3628919 = 5443379) B5443379
theorem B3227539 : Blo 1590994 3227539 := bstep (se 1 (by rfl) ⟨2420654, by rfl⟩ : syracuseStep 3227539 = 4841309) B4841309
theorem B3579911 : Blo 1590994 3579911 := bstep (se 1 (by rfl) ⟨2684933, by rfl⟩ : syracuseStep 3579911 = 5369867) B5369867
theorem B5373971 : Blo 1590994 5373971 := bstep (se 1 (by rfl) ⟨4030478, by rfl⟩ : syracuseStep 5373971 = 8060957) B8060957
theorem B2687033 : Blo 1590994 2687033 := bstep (se 2 (by rfl) ⟨1007637, by rfl⟩ : syracuseStep 2687033 = 2015275) B2015275
theorem B3579983 : Blo 1590994 3579983 := bstep (se 1 (by rfl) ⟨2684987, by rfl⟩ : syracuseStep 3579983 = 5369975) B5369975
theorem B3023095 : Blo 1590994 3023095 := bstep (se 1 (by rfl) ⟨2267321, by rfl⟩ : syracuseStep 3023095 = 4534643) B4534643
theorem B5374295 : Blo 1590994 5374295 := bstep (se 1 (by rfl) ⟨4030721, by rfl⟩ : syracuseStep 5374295 = 8061443) B8061443
theorem B3580379 : Blo 1590994 3580379 := bstep (se 1 (by rfl) ⟨2685284, by rfl⟩ : syracuseStep 3580379 = 5370569) B5370569
theorem B4030985 : Blo 1590994 4030985 := bstep (se 2 (by rfl) ⟨1511619, by rfl⟩ : syracuseStep 4030985 = 3023239) B3023239
theorem B11477537 : Blo 1590994 11477537 := bstep (se 2 (by rfl) ⟨4304076, by rfl⟩ : syracuseStep 11477537 = 8608153) B8608153
theorem B3400231 : Blo 1590994 3400231 := bstep (se 1 (by rfl) ⟨2550173, by rfl⟩ : syracuseStep 3400231 = 5100347) B5100347
theorem B3023399 : Blo 1590994 3023399 := bstep (se 1 (by rfl) ⟨2267549, by rfl⟩ : syracuseStep 3023399 = 4535099) B4535099
theorem B2015867 : Blo 1590994 2015867 := bstep (se 1 (by rfl) ⟨1511900, by rfl⟩ : syracuseStep 2015867 = 3023801) B3023801
theorem B19899053 : Blo 1590994 19899053 := bstep (se 3 (by rfl) ⟨3731072, by rfl⟩ : syracuseStep 19899053 = 7462145) B7462145
theorem B2687735 : Blo 1590994 2687735 := bstep (se 1 (by rfl) ⟨2015801, by rfl⟩ : syracuseStep 2687735 = 4031603) B4031603
theorem B4842233 : Blo 1590994 4842233 := bstep (se 2 (by rfl) ⟨1815837, by rfl⟩ : syracuseStep 4842233 = 3631675) B3631675
theorem B2548655 : Blo 1590994 2548655 := bstep (se 1 (by rfl) ⟨1911491, by rfl⟩ : syracuseStep 2548655 = 3822983) B3822983
theorem B3580847 : Blo 1590994 3580847 := bstep (se 1 (by rfl) ⟨2685635, by rfl⟩ : syracuseStep 3580847 = 5371271) B5371271
theorem B3826615 : Blo 1590994 3826615 := bstep (se 1 (by rfl) ⟨2869961, by rfl⟩ : syracuseStep 3826615 = 5739923) B5739923
theorem B6046721 : Blo 1590994 6046721 := bstep (se 2 (by rfl) ⟨2267520, by rfl⟩ : syracuseStep 6046721 = 4535041) B4535041
theorem B2688079 : Blo 1590994 2688079 := bstep (se 1 (by rfl) ⟨2016059, by rfl⟩ : syracuseStep 2688079 = 4032119) B4032119
theorem B5735539 : Blo 1590994 5735539 := bstep (se 1 (by rfl) ⟨4301654, by rfl⟩ : syracuseStep 5735539 = 8603309) B8603309
theorem B6292637 : Blo 1590994 6292637 := bstep (se 3 (by rfl) ⟨1179869, by rfl⟩ : syracuseStep 6292637 = 2359739) B2359739
theorem B4301981 : Blo 1590994 4301981 := bstep (se 3 (by rfl) ⟨806621, by rfl⟩ : syracuseStep 4301981 = 1613243) B1613243
theorem B3581099 : Blo 1590994 3581099 := bstep (se 1 (by rfl) ⟨2685824, by rfl⟩ : syracuseStep 3581099 = 5371649) B5371649
theorem B2549065 : Blo 1590994 2549065 := bstep (se 2 (by rfl) ⟨955899, by rfl⟩ : syracuseStep 2549065 = 1911799) B1911799
theorem B5375375 : Blo 1590994 5375375 := bstep (se 1 (by rfl) ⟨4031531, by rfl⟩ : syracuseStep 5375375 = 8063063) B8063063
theorem B10200563 : Blo 1590994 10200563 := bstep (se 1 (by rfl) ⟨7650422, by rfl⟩ : syracuseStep 10200563 = 15300845) B15300845
theorem B32687621 : Blo 1590994 32687621 := bstep (se 4 (by rfl) ⟨3064464, by rfl⟩ : syracuseStep 32687621 = 6128929) B6128929
theorem B3229193 : Blo 1590994 3229193 := bstep (se 2 (by rfl) ⟨1210947, by rfl⟩ : syracuseStep 3229193 = 2421895) B2421895
theorem B12084875 : Blo 1590994 12084875 := bstep (se 1 (by rfl) ⟨9063656, by rfl⟩ : syracuseStep 12084875 = 18127313) B18127313
theorem B4032139 : Blo 1590994 4032139 := bstep (se 1 (by rfl) ⟨3024104, by rfl⟩ : syracuseStep 4032139 = 6048209) B6048209
theorem B3581639 : Blo 1590994 3581639 := bstep (se 1 (by rfl) ⟨2686229, by rfl⟩ : syracuseStep 3581639 = 5372459) B5372459
theorem B17221319 : Blo 1590994 17221319 := bstep (se 1 (by rfl) ⟨12915989, by rfl⟩ : syracuseStep 17221319 = 25831979) B25831979
theorem B5375699 : Blo 1590994 5375699 := bstep (se 1 (by rfl) ⟨4031774, by rfl⟩ : syracuseStep 5375699 = 8063549) B8063549
theorem B1591003 : Blo 1590994 1591003 := bstep (se 1 (by rfl) ⟨1193252, by rfl⟩ : syracuseStep 1591003 = 2386505) B2386505
theorem B1591079 : Blo 1590994 1591079 := bstep (se 1 (by rfl) ⟨1193309, by rfl⟩ : syracuseStep 1591079 = 2386619) B2386619
theorem B9070379 : Blo 1590994 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B1591119 : Blo 1590994 1591119 := bstep (se 1 (by rfl) ⟨1193339, by rfl⟩ : syracuseStep 1591119 = 2386679) B2386679
theorem B1591135 : Blo 1590994 1591135 := bstep (se 1 (by rfl) ⟨1193351, by rfl⟩ : syracuseStep 1591135 = 2386703) B2386703
theorem B1591163 : Blo 1590994 1591163 := bstep (se 1 (by rfl) ⟨1193372, by rfl⟩ : syracuseStep 1591163 = 2386745) B2386745
theorem B33114017 : Blo 1590994 33114017 := bstep (se 2 (by rfl) ⟨12417756, by rfl⟩ : syracuseStep 33114017 = 24835513) B24835513
theorem B1591215 : Blo 1590994 1591215 := bstep (se 1 (by rfl) ⟨1193411, by rfl⟩ : syracuseStep 1591215 = 2386823) B2386823
theorem B1591239 : Blo 1590994 1591239 := bstep (se 1 (by rfl) ⟨1193429, by rfl⟩ : syracuseStep 1591239 = 2386859) B2386859
theorem B1591259 : Blo 1590994 1591259 := bstep (se 1 (by rfl) ⟨1193444, by rfl⟩ : syracuseStep 1591259 = 2386889) B2386889
theorem B5097487 : Blo 1590994 5097487 := bstep (se 1 (by rfl) ⟨3823115, by rfl⟩ : syracuseStep 5097487 = 7646231) B7646231
theorem B1591335 : Blo 1590994 1591335 := bstep (se 1 (by rfl) ⟨1193501, by rfl⟩ : syracuseStep 1591335 = 2387003) B2387003
theorem B1591375 : Blo 1590994 1591375 := bstep (se 1 (by rfl) ⟨1193531, by rfl⟩ : syracuseStep 1591375 = 2387063) B2387063
theorem B75499613 : Blo 1590994 75499613 := bstep (se 3 (by rfl) ⟨14156177, by rfl⟩ : syracuseStep 75499613 = 28312355) B28312355
theorem B1591391 : Blo 1590994 1591391 := bstep (se 1 (by rfl) ⟨1193543, by rfl⟩ : syracuseStep 1591391 = 2387087) B2387087
theorem B1591419 : Blo 1590994 1591419 := bstep (se 1 (by rfl) ⟨1193564, by rfl⟩ : syracuseStep 1591419 = 2387129) B2387129
theorem B1591471 : Blo 1590994 1591471 := bstep (se 1 (by rfl) ⟨1193603, by rfl⟩ : syracuseStep 1591471 = 2387207) B2387207
theorem B1591495 : Blo 1590994 1591495 := bstep (se 1 (by rfl) ⟨1193621, by rfl⟩ : syracuseStep 1591495 = 2387243) B2387243
theorem B1591515 : Blo 1590994 1591515 := bstep (se 1 (by rfl) ⟨1193636, by rfl⟩ : syracuseStep 1591515 = 2387273) B2387273
theorem B3107063 : Blo 1590994 3107063 := bstep (se 1 (by rfl) ⟨2330297, by rfl⟩ : syracuseStep 3107063 = 4660595) B4660595
theorem B1591591 : Blo 1590994 1591591 := bstep (se 1 (by rfl) ⟨1193693, by rfl⟩ : syracuseStep 1591591 = 2387387) B2387387
theorem B9677117 : Blo 1590994 9677117 := bstep (se 3 (by rfl) ⟨1814459, by rfl⟩ : syracuseStep 9677117 = 3628919) B3628919
theorem B1591631 : Blo 1590994 1591631 := bstep (se 1 (by rfl) ⟨1193723, by rfl⟩ : syracuseStep 1591631 = 2387447) B2387447
theorem B1591647 : Blo 1590994 1591647 := bstep (se 1 (by rfl) ⟨1193735, by rfl⟩ : syracuseStep 1591647 = 2387471) B2387471
theorem B1591675 : Blo 1590994 1591675 := bstep (se 1 (by rfl) ⟨1193756, by rfl⟩ : syracuseStep 1591675 = 2387513) B2387513
theorem B1591727 : Blo 1590994 1591727 := bstep (se 1 (by rfl) ⟨1193795, by rfl⟩ : syracuseStep 1591727 = 2387591) B2387591
theorem B1591751 : Blo 1590994 1591751 := bstep (se 1 (by rfl) ⟨1193813, by rfl⟩ : syracuseStep 1591751 = 2387627) B2387627
theorem B1591771 : Blo 1590994 1591771 := bstep (se 1 (by rfl) ⟨1193828, by rfl⟩ : syracuseStep 1591771 = 2387657) B2387657
theorem B5736923 : Blo 1590994 5736923 := bstep (se 1 (by rfl) ⟨4302692, by rfl⟩ : syracuseStep 5736923 = 8605385) B8605385
theorem B4303385 : Blo 1590994 4303385 := bstep (se 2 (by rfl) ⟨1613769, by rfl⟩ : syracuseStep 4303385 = 3227539) B3227539
theorem B9071129 : Blo 1590994 9071129 := bstep (se 2 (by rfl) ⟨3401673, by rfl⟩ : syracuseStep 9071129 = 6803347) B6803347
theorem B1591847 : Blo 1590994 1591847 := bstep (se 1 (by rfl) ⟨1193885, by rfl⟩ : syracuseStep 1591847 = 2387771) B2387771
theorem B3582503 : Blo 1590994 3582503 := bstep (se 1 (by rfl) ⟨2686877, by rfl⟩ : syracuseStep 3582503 = 5373755) B5373755
theorem B2386511 : Blo 1590994 2386511 := bstep (se 1 (by rfl) ⟨1789883, by rfl⟩ : syracuseStep 2386511 = 3579767) B3579767
theorem B1591887 : Blo 1590994 1591887 := bstep (se 1 (by rfl) ⟨1193915, by rfl⟩ : syracuseStep 1591887 = 2387831) B2387831
theorem B1591903 : Blo 1590994 1591903 := bstep (se 1 (by rfl) ⟨1193927, by rfl⟩ : syracuseStep 1591903 = 2387855) B2387855
theorem B121047671 : Blo 1590994 121047671 := bstep (se 1 (by rfl) ⟨90785753, by rfl⟩ : syracuseStep 121047671 = 181571507) B181571507
theorem B1591931 : Blo 1590994 1591931 := bstep (se 1 (by rfl) ⟨1193948, by rfl⟩ : syracuseStep 1591931 = 2387897) B2387897
theorem B6048391 : Blo 1590994 6048391 := bstep (se 1 (by rfl) ⟨4536293, by rfl⟩ : syracuseStep 6048391 = 9072587) B9072587
theorem B1591983 : Blo 1590994 1591983 := bstep (se 1 (by rfl) ⟨1193987, by rfl⟩ : syracuseStep 1591983 = 2387975) B2387975
theorem B2386631 : Blo 1590994 2386631 := bstep (se 1 (by rfl) ⟨1789973, by rfl⟩ : syracuseStep 2386631 = 3579947) B3579947
theorem B1592007 : Blo 1590994 1592007 := bstep (se 1 (by rfl) ⟨1194005, by rfl⟩ : syracuseStep 1592007 = 2388011) B2388011
theorem B41339593 : Blo 1590994 41339593 := bstep (se 2 (by rfl) ⟨15502347, by rfl⟩ : syracuseStep 41339593 = 31004695) B31004695
theorem B1592027 : Blo 1590994 1592027 := bstep (se 1 (by rfl) ⟨1194020, by rfl⟩ : syracuseStep 1592027 = 2388041) B2388041
theorem B1592103 : Blo 1590994 1592103 := bstep (se 1 (by rfl) ⟨1194077, by rfl⟩ : syracuseStep 1592103 = 2388155) B2388155
theorem B1592143 : Blo 1590994 1592143 := bstep (se 1 (by rfl) ⟨1194107, by rfl⟩ : syracuseStep 1592143 = 2388215) B2388215
theorem B1592159 : Blo 1590994 1592159 := bstep (se 1 (by rfl) ⟨1194119, by rfl⟩ : syracuseStep 1592159 = 2388239) B2388239
theorem B2386793 : Blo 1590994 2386793 := bstep (se 2 (by rfl) ⟨895047, by rfl⟩ : syracuseStep 2386793 = 1790095) B1790095
theorem B3582827 : Blo 1590994 3582827 := bstep (se 1 (by rfl) ⟨2687120, by rfl⟩ : syracuseStep 3582827 = 5374241) B5374241
theorem B1592187 : Blo 1590994 1592187 := bstep (se 1 (by rfl) ⟨1194140, by rfl⟩ : syracuseStep 1592187 = 2388281) B2388281
theorem B12250001 : Blo 1590994 12250001 := bstep (se 2 (by rfl) ⟨4593750, by rfl⟩ : syracuseStep 12250001 = 9187501) B9187501
theorem B3582881 : Blo 1590994 3582881 := bstep (se 2 (by rfl) ⟨1343580, by rfl⟩ : syracuseStep 3582881 = 2687161) B2687161
theorem B1592239 : Blo 1590994 1592239 := bstep (se 1 (by rfl) ⟨1194179, by rfl⟩ : syracuseStep 1592239 = 2388359) B2388359
theorem B2386871 : Blo 1590994 2386871 := bstep (se 1 (by rfl) ⟨1790153, by rfl⟩ : syracuseStep 2386871 = 3580307) B3580307
theorem B1592263 : Blo 1590994 1592263 := bstep (se 1 (by rfl) ⟨1194197, by rfl⟩ : syracuseStep 1592263 = 2388395) B2388395
theorem B2386907 : Blo 1590994 2386907 := bstep (se 1 (by rfl) ⟨1790180, by rfl⟩ : syracuseStep 2386907 = 3580361) B3580361
theorem B1592283 : Blo 1590994 1592283 := bstep (se 1 (by rfl) ⟨1194212, by rfl⟩ : syracuseStep 1592283 = 2388425) B2388425
theorem B1592359 : Blo 1590994 1592359 := bstep (se 1 (by rfl) ⟨1194269, by rfl⟩ : syracuseStep 1592359 = 2388539) B2388539
theorem B1592399 : Blo 1590994 1592399 := bstep (se 1 (by rfl) ⟨1194299, by rfl⟩ : syracuseStep 1592399 = 2388599) B2388599
theorem B1592415 : Blo 1590994 1592415 := bstep (se 1 (by rfl) ⟨1194311, by rfl⟩ : syracuseStep 1592415 = 2388623) B2388623
theorem B1592443 : Blo 1590994 1592443 := bstep (se 1 (by rfl) ⟨1194332, by rfl⟩ : syracuseStep 1592443 = 2388665) B2388665
theorem B1592495 : Blo 1590994 1592495 := bstep (se 1 (by rfl) ⟨1194371, by rfl⟩ : syracuseStep 1592495 = 2388743) B2388743
theorem B1592519 : Blo 1590994 1592519 := bstep (se 1 (by rfl) ⟨1194389, by rfl⟩ : syracuseStep 1592519 = 2388779) B2388779
theorem B1592539 : Blo 1590994 1592539 := bstep (se 1 (by rfl) ⟨1194404, by rfl⟩ : syracuseStep 1592539 = 2388809) B2388809
theorem B3583223 : Blo 1590994 3583223 := bstep (se 1 (by rfl) ⟨2687417, by rfl⟩ : syracuseStep 3583223 = 5374835) B5374835
theorem B1592615 : Blo 1590994 1592615 := bstep (se 1 (by rfl) ⟨1194461, by rfl⟩ : syracuseStep 1592615 = 2388923) B2388923
theorem B1592655 : Blo 1590994 1592655 := bstep (se 1 (by rfl) ⟨1194491, by rfl⟩ : syracuseStep 1592655 = 2388983) B2388983
theorem B6040919 : Blo 1590994 6040919 := bstep (se 1 (by rfl) ⟨4530689, by rfl⟩ : syracuseStep 6040919 = 9061379) B9061379
theorem B1592671 : Blo 1590994 1592671 := bstep (se 1 (by rfl) ⟨1194503, by rfl⟩ : syracuseStep 1592671 = 2389007) B2389007
theorem B1592699 : Blo 1590994 1592699 := bstep (se 1 (by rfl) ⟨1194524, by rfl⟩ : syracuseStep 1592699 = 2389049) B2389049
theorem B2387375 : Blo 1590994 2387375 := bstep (se 1 (by rfl) ⟨1790531, by rfl⟩ : syracuseStep 2387375 = 3581063) B3581063
theorem B1592751 : Blo 1590994 1592751 := bstep (se 1 (by rfl) ⟨1194563, by rfl⟩ : syracuseStep 1592751 = 2389127) B2389127
theorem B1592775 : Blo 1590994 1592775 := bstep (se 1 (by rfl) ⟨1194581, by rfl⟩ : syracuseStep 1592775 = 2389163) B2389163
theorem B1592795 : Blo 1590994 1592795 := bstep (se 1 (by rfl) ⟨1194596, by rfl⟩ : syracuseStep 1592795 = 2389193) B2389193
theorem B2387465 : Blo 1590994 2387465 := bstep (se 2 (by rfl) ⟨895299, by rfl⟩ : syracuseStep 2387465 = 1790599) B1790599
theorem B2387495 : Blo 1590994 2387495 := bstep (se 1 (by rfl) ⟨1790621, by rfl⟩ : syracuseStep 2387495 = 3581243) B3581243
theorem B2297383 : Blo 1590994 2297383 := bstep (se 1 (by rfl) ⟨1723037, by rfl⟩ : syracuseStep 2297383 = 3446075) B3446075
theorem B4304423 : Blo 1590994 4304423 := bstep (se 1 (by rfl) ⟨3228317, by rfl⟩ : syracuseStep 4304423 = 6456635) B6456635
theorem B22957607 : Blo 1590994 22957607 := bstep (se 1 (by rfl) ⟨17218205, by rfl⟩ : syracuseStep 22957607 = 34436411) B34436411
theorem B1592871 : Blo 1590994 1592871 := bstep (se 1 (by rfl) ⟨1194653, by rfl⟩ : syracuseStep 1592871 = 2389307) B2389307
theorem B1592911 : Blo 1590994 1592911 := bstep (se 1 (by rfl) ⟨1194683, by rfl⟩ : syracuseStep 1592911 = 2389367) B2389367
theorem B1592927 : Blo 1590994 1592927 := bstep (se 1 (by rfl) ⟨1194695, by rfl⟩ : syracuseStep 1592927 = 2389391) B2389391
theorem B4533857 : Blo 1590994 4533857 := bstep (se 2 (by rfl) ⟨1700196, by rfl⟩ : syracuseStep 4533857 = 3400393) B3400393
theorem B2387579 : Blo 1590994 2387579 := bstep (se 1 (by rfl) ⟨1790684, by rfl⟩ : syracuseStep 2387579 = 3581369) B3581369
theorem B1592955 : Blo 1590994 1592955 := bstep (se 1 (by rfl) ⟨1194716, by rfl⟩ : syracuseStep 1592955 = 2389433) B2389433
theorem B1912519 : Blo 1590994 1912519 := bstep (se 1 (by rfl) ⟨1434389, by rfl⟩ : syracuseStep 1912519 = 2868779) B2868779
theorem B5099219 : Blo 1590994 5099219 := bstep (se 1 (by rfl) ⟨3824414, by rfl⟩ : syracuseStep 5099219 = 7648829) B7648829
theorem B2387705 : Blo 1590994 2387705 := bstep (se 2 (by rfl) ⟨895389, by rfl⟩ : syracuseStep 2387705 = 1790779) B1790779
theorem B13602593 : Blo 1590994 13602593 := bstep (se 2 (by rfl) ⟨5100972, by rfl⟩ : syracuseStep 13602593 = 10201945) B10201945
theorem B3583817 : Blo 1590994 3583817 := bstep (se 2 (by rfl) ⟨1343931, by rfl⟩ : syracuseStep 3583817 = 2687863) B2687863
theorem B2387807 : Blo 1590994 2387807 := bstep (se 1 (by rfl) ⟨1790855, by rfl⟩ : syracuseStep 2387807 = 3581711) B3581711
theorem B2387819 : Blo 1590994 2387819 := bstep (se 1 (by rfl) ⟨1790864, by rfl⟩ : syracuseStep 2387819 = 3581729) B3581729
theorem B11038625 : Blo 1590994 11038625 := bstep (se 2 (by rfl) ⟨4139484, by rfl⟩ : syracuseStep 11038625 = 8278969) B8278969
theorem B1814447 : Blo 1590994 1814447 := bstep (se 1 (by rfl) ⟨1360835, by rfl⟩ : syracuseStep 1814447 = 2721671) B2721671
theorem B17207225 : Blo 1590994 17207225 := bstep (se 2 (by rfl) ⟨6452709, by rfl⟩ : syracuseStep 17207225 = 12905419) B12905419
theorem B1789915 : Blo 1590994 1789915 := bstep (se 1 (by rfl) ⟨1342436, by rfl⟩ : syracuseStep 1789915 = 2684873) B2684873
theorem B2723879 : Blo 1590994 2723879 := bstep (se 1 (by rfl) ⟨2042909, by rfl⟩ : syracuseStep 2723879 = 4085819) B4085819
theorem B2388047 : Blo 1590994 2388047 := bstep (se 1 (by rfl) ⟨1791035, by rfl⟩ : syracuseStep 2388047 = 3582071) B3582071
theorem B7647347 : Blo 1590994 7647347 := bstep (se 1 (by rfl) ⟨5735510, by rfl⟩ : syracuseStep 7647347 = 11471021) B11471021
theorem B2388167 : Blo 1590994 2388167 := bstep (se 1 (by rfl) ⟨1791125, by rfl⟩ : syracuseStep 2388167 = 3582251) B3582251
theorem B9687383 : Blo 1590994 9687383 := bstep (se 1 (by rfl) ⟨7265537, by rfl⟩ : syracuseStep 9687383 = 14531075) B14531075
theorem B2388329 : Blo 1590994 2388329 := bstep (se 2 (by rfl) ⟨895623, by rfl⟩ : syracuseStep 2388329 = 1791247) B1791247
theorem B1790383 : Blo 1590994 1790383 := bstep (se 1 (by rfl) ⟨1342787, by rfl⟩ : syracuseStep 1790383 = 2685575) B2685575
theorem B2265527 : Blo 1590994 2265527 := bstep (se 1 (by rfl) ⟨1699145, by rfl⟩ : syracuseStep 2265527 = 3398291) B3398291
theorem B2388407 : Blo 1590994 2388407 := bstep (se 1 (by rfl) ⟨1791305, by rfl⟩ : syracuseStep 2388407 = 3582611) B3582611
theorem B2388443 : Blo 1590994 2388443 := bstep (se 1 (by rfl) ⟨1791332, by rfl⟩ : syracuseStep 2388443 = 3582665) B3582665
theorem B5370407 : Blo 1590994 5370407 := bstep (se 1 (by rfl) ⟨4027805, by rfl⟩ : syracuseStep 5370407 = 8055611) B8055611
theorem B3494497 : Blo 1590994 3494497 := bstep (se 2 (by rfl) ⟨1310436, by rfl⟩ : syracuseStep 3494497 = 2620873) B2620873
theorem B5370515 : Blo 1590994 5370515 := bstep (se 1 (by rfl) ⟨4027886, by rfl⟩ : syracuseStep 5370515 = 8055773) B8055773
theorem B4534973 : Blo 1590994 4534973 := bstep (se 3 (by rfl) ⟨850307, by rfl⟩ : syracuseStep 4534973 = 1700615) B1700615
theorem B8057555 : Blo 1590994 8057555 := bstep (se 1 (by rfl) ⟨6043166, by rfl⟩ : syracuseStep 8057555 = 12086333) B12086333
theorem B1790815 : Blo 1590994 1790815 := bstep (se 1 (by rfl) ⟨1343111, by rfl⟩ : syracuseStep 1790815 = 2686223) B2686223
theorem B5370731 : Blo 1590994 5370731 := bstep (se 1 (by rfl) ⟨4028048, by rfl⟩ : syracuseStep 5370731 = 8056097) B8056097
theorem B10892177 : Blo 1590994 10892177 := bstep (se 2 (by rfl) ⟨4084566, by rfl⟩ : syracuseStep 10892177 = 8169133) B8169133
theorem B5370785 : Blo 1590994 5370785 := bstep (se 2 (by rfl) ⟨2014044, by rfl⟩ : syracuseStep 5370785 = 4028089) B4028089
theorem B2388911 : Blo 1590994 2388911 := bstep (se 1 (by rfl) ⟨1791683, by rfl⟩ : syracuseStep 2388911 = 3583367) B3583367
theorem B2389001 : Blo 1590994 2389001 := bstep (se 2 (by rfl) ⟨895875, by rfl⟩ : syracuseStep 2389001 = 1791751) B1791751
theorem B5100563 : Blo 1590994 5100563 := bstep (se 1 (by rfl) ⟨3825422, by rfl⟩ : syracuseStep 5100563 = 7650845) B7650845
theorem B4535315 : Blo 1590994 4535315 := bstep (se 1 (by rfl) ⟨3401486, by rfl⟩ : syracuseStep 4535315 = 6802973) B6802973
theorem B2389031 : Blo 1590994 2389031 := bstep (se 1 (by rfl) ⟨1791773, by rfl⟩ : syracuseStep 2389031 = 3583547) B3583547
theorem B2389115 : Blo 1590994 2389115 := bstep (se 1 (by rfl) ⟨1791836, by rfl⟩ : syracuseStep 2389115 = 3583673) B3583673
theorem B14529689 : Blo 1590994 14529689 := bstep (se 2 (by rfl) ⟨5448633, by rfl⟩ : syracuseStep 14529689 = 10897267) B10897267
theorem B5444765 : Blo 1590994 5444765 := bstep (se 3 (by rfl) ⟨1020893, by rfl⟩ : syracuseStep 5444765 = 2041787) B2041787
theorem B1791175 : Blo 1590994 1791175 := bstep (se 1 (by rfl) ⟨1343381, by rfl⟩ : syracuseStep 1791175 = 2686763) B2686763
theorem B2389241 : Blo 1590994 2389241 := bstep (se 2 (by rfl) ⟨895965, by rfl⟩ : syracuseStep 2389241 = 1791931) B1791931
theorem B17216783 : Blo 1590994 17216783 := bstep (se 1 (by rfl) ⟨12912587, by rfl⟩ : syracuseStep 17216783 = 25825175) B25825175
theorem B2389343 : Blo 1590994 2389343 := bstep (se 1 (by rfl) ⟨1792007, by rfl⟩ : syracuseStep 2389343 = 3584015) B3584015
theorem B2389355 : Blo 1590994 2389355 := bstep (se 1 (by rfl) ⟨1792016, by rfl⟩ : syracuseStep 2389355 = 3584033) B3584033
theorem B558527885 : Blo 1590994 558527885 := bstep (se 3 (by rfl) ⟨104723978, by rfl⟩ : syracuseStep 558527885 = 209447957) B209447957
theorem B5371379 : Blo 1590994 5371379 := bstep (se 1 (by rfl) ⟨4028534, by rfl⟩ : syracuseStep 5371379 = 8057069) B8057069
theorem B9680573 : Blo 1590994 9680573 := bstep (se 3 (by rfl) ⟨1815107, by rfl⟩ : syracuseStep 9680573 = 3630215) B3630215
theorem B20666171 : Blo 1590994 20666171 := bstep (se 1 (by rfl) ⟨15499628, by rfl⟩ : syracuseStep 20666171 = 30999257) B30999257
theorem B2266985 : Blo 1590994 2266985 := bstep (se 2 (by rfl) ⟨850119, by rfl⟩ : syracuseStep 2266985 = 1700239) B1700239
theorem B12089249 : Blo 1590994 12089249 := bstep (se 2 (by rfl) ⟨4533468, by rfl⟩ : syracuseStep 12089249 = 9066937) B9066937
theorem B3020809 : Blo 1590994 3020809 := bstep (se 2 (by rfl) ⟨1132803, by rfl⟩ : syracuseStep 3020809 = 2265607) B2265607
theorem B5371919 : Blo 1590994 5371919 := bstep (se 1 (by rfl) ⟨4028939, by rfl⟩ : syracuseStep 5371919 = 8057879) B8057879
theorem B1792039 : Blo 1590994 1792039 := bstep (se 1 (by rfl) ⟨1344029, by rfl⟩ : syracuseStep 1792039 = 2688059) B2688059
theorem B8173649 : Blo 1590994 8173649 := bstep (se 2 (by rfl) ⟨3065118, by rfl⟩ : syracuseStep 8173649 = 6130237) B6130237
theorem B6043805 : Blo 1590994 6043805 := bstep (se 3 (by rfl) ⟨1133213, by rfl⟩ : syracuseStep 6043805 = 2266427) B2266427
theorem B3021151 : Blo 1590994 3021151 := bstep (se 1 (by rfl) ⟨2265863, by rfl⟩ : syracuseStep 3021151 = 4531727) B4531727
theorem B2685359 : Blo 1590994 2685359 := bstep (se 1 (by rfl) ⟨2014019, by rfl⟩ : syracuseStep 2685359 = 4028039) B4028039
theorem B8608237 : Blo 1590994 8608237 := bstep (se 3 (by rfl) ⟨1614044, by rfl⟩ : syracuseStep 8608237 = 3228089) B3228089
theorem B5372513 : Blo 1590994 5372513 := bstep (se 2 (by rfl) ⟨2014692, by rfl⟩ : syracuseStep 5372513 = 4029385) B4029385
theorem B5102203 : Blo 1590994 5102203 := bstep (se 1 (by rfl) ⟨3826652, by rfl⟩ : syracuseStep 5102203 = 7653305) B7653305
theorem B3398393 : Blo 1590994 3398393 := bstep (se 2 (by rfl) ⟨1274397, by rfl⟩ : syracuseStep 3398393 = 2548795) B2548795
theorem B13597469 : Blo 1590994 13597469 := bstep (se 3 (by rfl) ⟨2549525, by rfl⟩ : syracuseStep 13597469 = 5099051) B5099051
theorem B6044489 : Blo 1590994 6044489 := bstep (se 2 (by rfl) ⟨2266683, by rfl⟩ : syracuseStep 6044489 = 4533367) B4533367
theorem B2685791 : Blo 1590994 2685791 := bstep (se 1 (by rfl) ⟨2014343, by rfl⟩ : syracuseStep 2685791 = 4028687) B4028687
theorem B9681839 : Blo 1590994 9681839 := bstep (se 1 (by rfl) ⟨7261379, by rfl⟩ : syracuseStep 9681839 = 14522759) B14522759
theorem B8059823 : Blo 1590994 8059823 := bstep (se 1 (by rfl) ⟨6044867, by rfl⟩ : syracuseStep 8059823 = 12089735) B12089735
theorem B2014247 : Blo 1590994 2014247 := bstep (se 1 (by rfl) ⟨1510685, by rfl⟩ : syracuseStep 2014247 = 3021371) B3021371
theorem B33135659 : Blo 1590994 33135659 := bstep (se 1 (by rfl) ⟨24851744, by rfl⟩ : syracuseStep 33135659 = 49703489) B49703489
theorem B4029497 : Blo 1590994 4029497 := bstep (se 2 (by rfl) ⟨1511061, by rfl⟩ : syracuseStep 4029497 = 3022123) B3022123
theorem B3398735 : Blo 1590994 3398735 := bstep (se 1 (by rfl) ⟨2549051, by rfl⟩ : syracuseStep 3398735 = 5098103) B5098103
theorem B176766083 : Blo 1590994 176766083 := bstep (se 1 (by rfl) ⟨132574562, by rfl⟩ : syracuseStep 176766083 = 265149125) B265149125
theorem B20397329 : Blo 1590994 20397329 := bstep (se 2 (by rfl) ⟨7648998, by rfl⟩ : syracuseStep 20397329 = 15297997) B15297997
theorem B6044989 : Blo 1590994 6044989 := bstep (se 3 (by rfl) ⟨1133435, by rfl⟩ : syracuseStep 6044989 = 2266871) B2266871
theorem B5102909 : Blo 1590994 5102909 := bstep (se 3 (by rfl) ⟨956795, by rfl⟩ : syracuseStep 5102909 = 1913591) B1913591
theorem B2014571 : Blo 1590994 2014571 := bstep (se 1 (by rfl) ⟨1510928, by rfl⟩ : syracuseStep 2014571 = 3021857) B3021857
theorem B3226987 : Blo 1590994 3226987 := bstep (se 1 (by rfl) ⟨2420240, by rfl⟩ : syracuseStep 3226987 = 4840481) B4840481
theorem B2686351 : Blo 1590994 2686351 := bstep (se 1 (by rfl) ⟨2014763, by rfl⟩ : syracuseStep 2686351 = 4029527) B4029527
theorem B3022267 : Blo 1590994 3022267 := bstep (se 1 (by rfl) ⟨2266700, by rfl⟩ : syracuseStep 3022267 = 4533401) B4533401
theorem B6888947 : Blo 1590994 6888947 := bstep (se 1 (by rfl) ⟨5166710, by rfl⟩ : syracuseStep 6888947 = 10333421) B10333421
theorem B3022343 : Blo 1590994 3022343 := bstep (se 1 (by rfl) ⟨2266757, by rfl⟩ : syracuseStep 3022343 = 4533515) B4533515
theorem B5103319 : Blo 1590994 5103319 := bstep (se 1 (by rfl) ⟨3827489, by rfl⟩ : syracuseStep 5103319 = 7654979) B7654979
theorem B7651037 : Blo 1590994 7651037 := bstep (se 3 (by rfl) ⟨1434569, by rfl⟩ : syracuseStep 7651037 = 2869139) B2869139
theorem B18128771 : Blo 1590994 18128771 := bstep (se 1 (by rfl) ⟨13596578, by rfl⟩ : syracuseStep 18128771 = 27193157) B27193157
theorem B19365767 : Blo 1590994 19365767 := bstep (se 1 (by rfl) ⟨14524325, by rfl⟩ : syracuseStep 19365767 = 29048651) B29048651
theorem B3022753 : Blo 1590994 3022753 := bstep (se 2 (by rfl) ⟨1133532, by rfl⟩ : syracuseStep 3022753 = 2267065) B2267065
theorem B4030793 : Blo 1590994 4030793 := bstep (se 2 (by rfl) ⟨1511547, by rfl⟩ : syracuseStep 4030793 = 3023095) B3023095
theorem B2687323 : Blo 1590994 2687323 := bstep (se 1 (by rfl) ⟨2015492, by rfl⟩ : syracuseStep 2687323 = 4030985) B4030985
theorem B7651691 : Blo 1590994 7651691 := bstep (se 1 (by rfl) ⟨5738768, by rfl⟩ : syracuseStep 7651691 = 11477537) B11477537
theorem B3580271 : Blo 1590994 3580271 := bstep (se 1 (by rfl) ⟨2685203, by rfl⟩ : syracuseStep 3580271 = 5370407) B5370407
theorem B2015599 : Blo 1590994 2015599 := bstep (se 1 (by rfl) ⟨1511699, by rfl⟩ : syracuseStep 2015599 = 3023399) B3023399
theorem B3580343 : Blo 1590994 3580343 := bstep (se 1 (by rfl) ⟨2685257, by rfl⟩ : syracuseStep 3580343 = 5370515) B5370515
theorem B3023315 : Blo 1590994 3023315 := bstep (se 1 (by rfl) ⟨2267486, by rfl⟩ : syracuseStep 3023315 = 4534973) B4534973
theorem B3228155 : Blo 1590994 3228155 := bstep (se 1 (by rfl) ⟨2421116, by rfl⟩ : syracuseStep 3228155 = 4842233) B4842233
theorem B3580487 : Blo 1590994 3580487 := bstep (se 1 (by rfl) ⟨2685365, by rfl⟩ : syracuseStep 3580487 = 5370731) B5370731
theorem B3580523 : Blo 1590994 3580523 := bstep (se 1 (by rfl) ⟨2685392, by rfl⟩ : syracuseStep 3580523 = 5370785) B5370785
theorem B4031147 : Blo 1590994 4031147 := bstep (se 1 (by rfl) ⟨3023360, by rfl⟩ : syracuseStep 4031147 = 6046721) B6046721
theorem B3400375 : Blo 1590994 3400375 := bstep (se 1 (by rfl) ⟨2550281, by rfl⟩ : syracuseStep 3400375 = 5100563) B5100563
theorem B3023543 : Blo 1590994 3023543 := bstep (se 1 (by rfl) ⟨2267657, by rfl⟩ : syracuseStep 3023543 = 4535315) B4535315
theorem B4195091 : Blo 1590994 4195091 := bstep (se 1 (by rfl) ⟨3146318, by rfl⟩ : syracuseStep 4195091 = 6292637) B6292637
theorem B2867987 : Blo 1590994 2867987 := bstep (se 1 (by rfl) ⟨2150990, by rfl⟩ : syracuseStep 2867987 = 4301981) B4301981
theorem B3629843 : Blo 1590994 3629843 := bstep (se 1 (by rfl) ⟨2722382, by rfl⟩ : syracuseStep 3629843 = 5444765) B5444765
theorem B11477855 : Blo 1590994 11477855 := bstep (se 1 (by rfl) ⟨8608391, by rfl⟩ : syracuseStep 11477855 = 17216783) B17216783
theorem B372351923 : Blo 1590994 372351923 := bstep (se 1 (by rfl) ⟨279263942, by rfl⟩ : syracuseStep 372351923 = 558527885) B558527885
theorem B3580919 : Blo 1590994 3580919 := bstep (se 1 (by rfl) ⟨2685689, by rfl⟩ : syracuseStep 3580919 = 5371379) B5371379
theorem B6800375 : Blo 1590994 6800375 := bstep (se 1 (by rfl) ⟨5100281, by rfl⟩ : syracuseStep 6800375 = 10200563) B10200563
theorem B21791747 : Blo 1590994 21791747 := bstep (se 1 (by rfl) ⟨16343810, by rfl⟩ : syracuseStep 21791747 = 32687621) B32687621
theorem B6046919 : Blo 1590994 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B3581279 : Blo 1590994 3581279 := bstep (se 1 (by rfl) ⟨2685959, by rfl⟩ : syracuseStep 3581279 = 5371919) B5371919
theorem B8611181 : Blo 1590994 8611181 := bstep (se 3 (by rfl) ⟨1614596, by rfl⟩ : syracuseStep 8611181 = 3229193) B3229193
theorem B5449099 : Blo 1590994 5449099 := bstep (se 1 (by rfl) ⟨4086824, by rfl⟩ : syracuseStep 5449099 = 8173649) B8173649
theorem B50333075 : Blo 1590994 50333075 := bstep (se 1 (by rfl) ⟨37749806, by rfl⟩ : syracuseStep 50333075 = 75499613) B75499613
theorem B5375645 : Blo 1590994 5375645 := bstep (se 3 (by rfl) ⟨1007933, by rfl⟩ : syracuseStep 5375645 = 2015867) B2015867
theorem B2868923 : Blo 1590994 2868923 := bstep (se 1 (by rfl) ⟨2151692, by rfl⟩ : syracuseStep 2868923 = 4303385) B4303385
theorem B6047419 : Blo 1590994 6047419 := bstep (se 1 (by rfl) ⟨4535564, by rfl⟩ : syracuseStep 6047419 = 9071129) B9071129
theorem B1591007 : Blo 1590994 1591007 := bstep (se 1 (by rfl) ⟨1193255, by rfl⟩ : syracuseStep 1591007 = 2386511) B2386511
theorem B3581675 : Blo 1590994 3581675 := bstep (se 1 (by rfl) ⟨2686256, by rfl⟩ : syracuseStep 3581675 = 5372513) B5372513
theorem B1591087 : Blo 1590994 1591087 := bstep (se 1 (by rfl) ⟨1193315, by rfl⟩ : syracuseStep 1591087 = 2386631) B2386631
theorem B4302649 : Blo 1590994 4302649 := bstep (se 2 (by rfl) ⟨1613493, by rfl⟩ : syracuseStep 4302649 = 3226987) B3226987
theorem B3581801 : Blo 1590994 3581801 := bstep (se 2 (by rfl) ⟨1343175, by rfl⟩ : syracuseStep 3581801 = 2686351) B2686351
theorem B1591195 : Blo 1590994 1591195 := bstep (se 1 (by rfl) ⟨1193396, by rfl⟩ : syracuseStep 1591195 = 2386793) B2386793
theorem B1591247 : Blo 1590994 1591247 := bstep (se 1 (by rfl) ⟨1193435, by rfl⟩ : syracuseStep 1591247 = 2386871) B2386871
theorem B1591271 : Blo 1590994 1591271 := bstep (se 1 (by rfl) ⟨1193453, by rfl⟩ : syracuseStep 1591271 = 2386907) B2386907
theorem B9062381 : Blo 1590994 9062381 := bstep (se 3 (by rfl) ⟨1699196, by rfl⟩ : syracuseStep 9062381 = 3398393) B3398393
theorem B117844055 : Blo 1590994 117844055 := bstep (se 1 (by rfl) ⟨88383041, by rfl⟩ : syracuseStep 117844055 = 176766083) B176766083
theorem B5376185 : Blo 1590994 5376185 := bstep (se 2 (by rfl) ⟨2016069, by rfl⟩ : syracuseStep 5376185 = 4032139) B4032139
theorem B3401939 : Blo 1590994 3401939 := bstep (se 1 (by rfl) ⟨2551454, by rfl⟩ : syracuseStep 3401939 = 5102909) B5102909
theorem B2550025 : Blo 1590994 2550025 := bstep (se 2 (by rfl) ⟨956259, by rfl⟩ : syracuseStep 2550025 = 1912519) B1912519
theorem B1591583 : Blo 1590994 1591583 := bstep (se 1 (by rfl) ⟨1193687, by rfl⟩ : syracuseStep 1591583 = 2387375) B2387375
theorem B1591643 : Blo 1590994 1591643 := bstep (se 1 (by rfl) ⟨1193732, by rfl⟩ : syracuseStep 1591643 = 2387465) B2387465
theorem B1591663 : Blo 1590994 1591663 := bstep (se 1 (by rfl) ⟨1193747, by rfl⟩ : syracuseStep 1591663 = 2387495) B2387495
theorem B2869615 : Blo 1590994 2869615 := bstep (se 1 (by rfl) ⟨2152211, by rfl⟩ : syracuseStep 2869615 = 4304423) B4304423
theorem B15305071 : Blo 1590994 15305071 := bstep (se 1 (by rfl) ⟨11478803, by rfl⟩ : syracuseStep 15305071 = 22957607) B22957607
theorem B1591719 : Blo 1590994 1591719 := bstep (se 1 (by rfl) ⟨1193789, by rfl⟩ : syracuseStep 1591719 = 2387579) B2387579
theorem B1591803 : Blo 1590994 1591803 := bstep (se 1 (by rfl) ⟨1193852, by rfl⟩ : syracuseStep 1591803 = 2387705) B2387705
theorem B1591871 : Blo 1590994 1591871 := bstep (se 1 (by rfl) ⟨1193903, by rfl⟩ : syracuseStep 1591871 = 2387807) B2387807
theorem B45910597 : Blo 1590994 45910597 := bstep (se 4 (by rfl) ⟨4304118, by rfl⟩ : syracuseStep 45910597 = 8608237) B8608237
theorem B1591879 : Blo 1590994 1591879 := bstep (se 1 (by rfl) ⟨1193909, by rfl⟩ : syracuseStep 1591879 = 2387819) B2387819
theorem B12085847 : Blo 1590994 12085847 := bstep (se 1 (by rfl) ⟨9064385, by rfl⟩ : syracuseStep 12085847 = 18128771) B18128771
theorem B7359083 : Blo 1590994 7359083 := bstep (se 1 (by rfl) ⟨5519312, by rfl⟩ : syracuseStep 7359083 = 11038625) B11038625
theorem B2386553 : Blo 1590994 2386553 := bstep (se 2 (by rfl) ⟨894957, by rfl⟩ : syracuseStep 2386553 = 1789915) B1789915
theorem B11471483 : Blo 1590994 11471483 := bstep (se 1 (by rfl) ⟨8603612, by rfl⟩ : syracuseStep 11471483 = 17207225) B17207225
theorem B2386607 : Blo 1590994 2386607 := bstep (se 1 (by rfl) ⟨1789955, by rfl⟩ : syracuseStep 2386607 = 3579911) B3579911
theorem B3582647 : Blo 1590994 3582647 := bstep (se 1 (by rfl) ⟨2686985, by rfl⟩ : syracuseStep 3582647 = 5373971) B5373971
theorem B2386655 : Blo 1590994 2386655 := bstep (se 1 (by rfl) ⟨1789991, by rfl⟩ : syracuseStep 2386655 = 3579983) B3579983
theorem B1592031 : Blo 1590994 1592031 := bstep (se 1 (by rfl) ⟨1194023, by rfl⟩ : syracuseStep 1592031 = 2388047) B2388047
theorem B5098231 : Blo 1590994 5098231 := bstep (se 1 (by rfl) ⟨3823673, by rfl⟩ : syracuseStep 5098231 = 7647347) B7647347
theorem B1592111 : Blo 1590994 1592111 := bstep (se 1 (by rfl) ⟨1194083, by rfl⟩ : syracuseStep 1592111 = 2388167) B2388167
theorem B3582863 : Blo 1590994 3582863 := bstep (se 1 (by rfl) ⟨2687147, by rfl⟩ : syracuseStep 3582863 = 5374295) B5374295
theorem B6458255 : Blo 1590994 6458255 := bstep (se 1 (by rfl) ⟨4843691, by rfl⟩ : syracuseStep 6458255 = 9687383) B9687383
theorem B1592219 : Blo 1590994 1592219 := bstep (se 1 (by rfl) ⟨1194164, by rfl⟩ : syracuseStep 1592219 = 2388329) B2388329
theorem B1592271 : Blo 1590994 1592271 := bstep (se 1 (by rfl) ⟨1194203, by rfl⟩ : syracuseStep 1592271 = 2388407) B2388407
theorem B2386919 : Blo 1590994 2386919 := bstep (se 1 (by rfl) ⟨1790189, by rfl⟩ : syracuseStep 2386919 = 3580379) B3580379
theorem B1592295 : Blo 1590994 1592295 := bstep (se 1 (by rfl) ⟨1194221, by rfl⟩ : syracuseStep 1592295 = 2388443) B2388443
theorem B13266035 : Blo 1590994 13266035 := bstep (se 1 (by rfl) ⟨9949526, by rfl⟩ : syracuseStep 13266035 = 19899053) B19899053
theorem B2387177 : Blo 1590994 2387177 := bstep (se 2 (by rfl) ⟨895191, by rfl⟩ : syracuseStep 2387177 = 1790383) B1790383
theorem B7261451 : Blo 1590994 7261451 := bstep (se 1 (by rfl) ⟨5446088, by rfl⟩ : syracuseStep 7261451 = 10892177) B10892177
theorem B1699103 : Blo 1590994 1699103 := bstep (se 1 (by rfl) ⟨1274327, by rfl⟩ : syracuseStep 1699103 = 2548655) B2548655
theorem B2387231 : Blo 1590994 2387231 := bstep (se 1 (by rfl) ⟨1790423, by rfl⟩ : syracuseStep 2387231 = 3580847) B3580847
theorem B1592607 : Blo 1590994 1592607 := bstep (se 1 (by rfl) ⟨1194455, by rfl⟩ : syracuseStep 1592607 = 2388911) B2388911
theorem B8285501 : Blo 1590994 8285501 := bstep (se 3 (by rfl) ⟨1553531, by rfl⟩ : syracuseStep 8285501 = 3107063) B3107063
theorem B1592667 : Blo 1590994 1592667 := bstep (se 1 (by rfl) ⟨1194500, by rfl⟩ : syracuseStep 1592667 = 2389001) B2389001
theorem B1592687 : Blo 1590994 1592687 := bstep (se 1 (by rfl) ⟨1194515, by rfl⟩ : syracuseStep 1592687 = 2389031) B2389031
theorem B4533641 : Blo 1590994 4533641 := bstep (se 2 (by rfl) ⟨1700115, by rfl⟩ : syracuseStep 4533641 = 3400231) B3400231
theorem B1592743 : Blo 1590994 1592743 := bstep (se 1 (by rfl) ⟨1194557, by rfl⟩ : syracuseStep 1592743 = 2389115) B2389115
theorem B9686459 : Blo 1590994 9686459 := bstep (se 1 (by rfl) ⟨7264844, by rfl⟩ : syracuseStep 9686459 = 14529689) B14529689
theorem B2387399 : Blo 1590994 2387399 := bstep (se 1 (by rfl) ⟨1790549, by rfl⟩ : syracuseStep 2387399 = 3581099) B3581099
theorem B6802937 : Blo 1590994 6802937 := bstep (se 2 (by rfl) ⟨2551101, by rfl⟩ : syracuseStep 6802937 = 5102203) B5102203
theorem B1592827 : Blo 1590994 1592827 := bstep (se 1 (by rfl) ⟨1194620, by rfl⟩ : syracuseStep 1592827 = 2389241) B2389241
theorem B8064521 : Blo 1590994 8064521 := bstep (se 2 (by rfl) ⟨3024195, by rfl⟩ : syracuseStep 8064521 = 6048391) B6048391
theorem B1592895 : Blo 1590994 1592895 := bstep (se 1 (by rfl) ⟨1194671, by rfl⟩ : syracuseStep 1592895 = 2389343) B2389343
theorem B1592903 : Blo 1590994 1592903 := bstep (se 1 (by rfl) ⟨1194677, by rfl⟩ : syracuseStep 1592903 = 2389355) B2389355
theorem B3583583 : Blo 1590994 3583583 := bstep (se 1 (by rfl) ⟨2687687, by rfl⟩ : syracuseStep 3583583 = 5375375) B5375375
theorem B55119457 : Blo 1590994 55119457 := bstep (se 2 (by rfl) ⟨20669796, by rfl⟩ : syracuseStep 55119457 = 41339593) B41339593
theorem B8056583 : Blo 1590994 8056583 := bstep (se 1 (by rfl) ⟨6042437, by rfl⟩ : syracuseStep 8056583 = 12084875) B12084875
theorem B2387753 : Blo 1590994 2387753 := bstep (se 2 (by rfl) ⟨895407, by rfl⟩ : syracuseStep 2387753 = 1790815) B1790815
theorem B2387759 : Blo 1590994 2387759 := bstep (se 1 (by rfl) ⟨1790819, by rfl⟩ : syracuseStep 2387759 = 3581639) B3581639
theorem B11480879 : Blo 1590994 11480879 := bstep (se 1 (by rfl) ⟨8610659, by rfl⟩ : syracuseStep 11480879 = 17221319) B17221319
theorem B3583799 : Blo 1590994 3583799 := bstep (se 1 (by rfl) ⟨2687849, by rfl⟩ : syracuseStep 3583799 = 5375699) B5375699
theorem B6041405 : Blo 1590994 6041405 := bstep (se 3 (by rfl) ⟨1132763, by rfl⟩ : syracuseStep 6041405 = 2265527) B2265527
theorem B18370525 : Blo 1590994 18370525 := bstep (se 3 (by rfl) ⟨3444473, by rfl⟩ : syracuseStep 18370525 = 6888947) B6888947
theorem B3584105 : Blo 1590994 3584105 := bstep (se 2 (by rfl) ⟨1344039, by rfl⟩ : syracuseStep 3584105 = 2688079) B2688079
theorem B7647385 : Blo 1590994 7647385 := bstep (se 2 (by rfl) ⟨2867769, by rfl⟩ : syracuseStep 7647385 = 5735539) B5735539
theorem B6451411 : Blo 1590994 6451411 := bstep (se 1 (by rfl) ⟨4838558, by rfl⟩ : syracuseStep 6451411 = 9677117) B9677117
theorem B2388233 : Blo 1590994 2388233 := bstep (se 2 (by rfl) ⟨895587, by rfl⟩ : syracuseStep 2388233 = 1791175) B1791175
theorem B1790239 : Blo 1590994 1790239 := bstep (se 1 (by rfl) ⟨1342679, by rfl⟩ : syracuseStep 1790239 = 2685359) B2685359
theorem B2388335 : Blo 1590994 2388335 := bstep (se 1 (by rfl) ⟨1791251, by rfl⟩ : syracuseStep 2388335 = 3582503) B3582503
theorem B9064979 : Blo 1590994 9064979 := bstep (se 1 (by rfl) ⟨6798734, by rfl⟩ : syracuseStep 9064979 = 13597469) B13597469
theorem B1790527 : Blo 1590994 1790527 := bstep (se 1 (by rfl) ⟨1342895, by rfl⟩ : syracuseStep 1790527 = 2685791) B2685791
theorem B2388551 : Blo 1590994 2388551 := bstep (se 1 (by rfl) ⟨1791413, by rfl⟩ : syracuseStep 2388551 = 3582827) B3582827
theorem B20402765 : Blo 1590994 20402765 := bstep (se 3 (by rfl) ⟨3825518, by rfl⟩ : syracuseStep 20402765 = 7651037) B7651037
theorem B2388587 : Blo 1590994 2388587 := bstep (se 1 (by rfl) ⟨1791440, by rfl⟩ : syracuseStep 2388587 = 3582881) B3582881
theorem B22090439 : Blo 1590994 22090439 := bstep (se 1 (by rfl) ⟨16567829, by rfl⟩ : syracuseStep 22090439 = 33135659) B33135659
theorem B2265823 : Blo 1590994 2265823 := bstep (se 1 (by rfl) ⟨1699367, by rfl⟩ : syracuseStep 2265823 = 3398735) B3398735
theorem B2388815 : Blo 1590994 2388815 := bstep (se 1 (by rfl) ⟨1791611, by rfl⟩ : syracuseStep 2388815 = 3583223) B3583223
theorem B4027279 : Blo 1590994 4027279 := bstep (se 1 (by rfl) ⟨3020459, by rfl⟩ : syracuseStep 4027279 = 6040919) B6040919
theorem B6804425 : Blo 1590994 6804425 := bstep (se 2 (by rfl) ⟨2551659, by rfl⟩ : syracuseStep 6804425 = 5103319) B5103319
theorem B32666669 : Blo 1590994 32666669 := bstep (se 3 (by rfl) ⟨6125000, by rfl⟩ : syracuseStep 32666669 = 12250001) B12250001
theorem B4838525 : Blo 1590994 4838525 := bstep (se 3 (by rfl) ⟨907223, by rfl⟩ : syracuseStep 4838525 = 1814447) B1814447
theorem B2389211 : Blo 1590994 2389211 := bstep (se 1 (by rfl) ⟨1791908, by rfl⟩ : syracuseStep 2389211 = 3583817) B3583817
theorem B4027745 : Blo 1590994 4027745 := bstep (se 2 (by rfl) ⟨1510404, by rfl⟩ : syracuseStep 4027745 = 3020809) B3020809
theorem B6796649 : Blo 1590994 6796649 := bstep (se 2 (by rfl) ⟨2548743, by rfl⟩ : syracuseStep 6796649 = 5097487) B5097487
theorem B1791355 : Blo 1590994 1791355 := bstep (se 1 (by rfl) ⟨1343516, by rfl⟩ : syracuseStep 1791355 = 2687033) B2687033
theorem B2389385 : Blo 1590994 2389385 := bstep (se 2 (by rfl) ⟨896019, by rfl⟩ : syracuseStep 2389385 = 1792039) B1792039
theorem B5371325 : Blo 1590994 5371325 := bstep (se 3 (by rfl) ⟨1007123, by rfl⟩ : syracuseStep 5371325 = 2014247) B2014247
theorem B7263677 : Blo 1590994 7263677 := bstep (se 3 (by rfl) ⟨1361939, by rfl⟩ : syracuseStep 7263677 = 2723879) B2723879
theorem B4028201 : Blo 1590994 4028201 := bstep (se 2 (by rfl) ⟨1510575, by rfl⟩ : syracuseStep 4028201 = 3021151) B3021151
theorem B5371703 : Blo 1590994 5371703 := bstep (se 1 (by rfl) ⟨4028777, by rfl⟩ : syracuseStep 5371703 = 8057555) B8057555
theorem B1791823 : Blo 1590994 1791823 := bstep (se 1 (by rfl) ⟨1343867, by rfl⟩ : syracuseStep 1791823 = 2687735) B2687735
theorem B4659329 : Blo 1590994 4659329 := bstep (se 2 (by rfl) ⟨1747248, by rfl⟩ : syracuseStep 4659329 = 3494497) B3494497
theorem B49010837 : Blo 1590994 49010837 := bstep (se 6 (by rfl) ⟨1148691, by rfl⟩ : syracuseStep 49010837 = 2297383) B2297383
theorem B5372189 : Blo 1590994 5372189 := bstep (se 3 (by rfl) ⟨1007285, by rfl⟩ : syracuseStep 5372189 = 2014571) B2014571
theorem B6453715 : Blo 1590994 6453715 := bstep (se 1 (by rfl) ⟨4840286, by rfl⟩ : syracuseStep 6453715 = 9680573) B9680573
theorem B13777447 : Blo 1590994 13777447 := bstep (se 1 (by rfl) ⟨10333085, by rfl⟩ : syracuseStep 13777447 = 20666171) B20666171
theorem B5102153 : Blo 1590994 5102153 := bstep (se 2 (by rfl) ⟨1913307, by rfl⟩ : syracuseStep 5102153 = 3826615) B3826615
theorem B22076011 : Blo 1590994 22076011 := bstep (se 1 (by rfl) ⟨16557008, by rfl⟩ : syracuseStep 22076011 = 33114017) B33114017
theorem B8059499 : Blo 1590994 8059499 := bstep (se 1 (by rfl) ⟨6044624, by rfl⟩ : syracuseStep 8059499 = 12089249) B12089249
theorem B4029203 : Blo 1590994 4029203 := bstep (se 1 (by rfl) ⟨3021902, by rfl⟩ : syracuseStep 4029203 = 6043805) B6043805
theorem B3824615 : Blo 1590994 3824615 := bstep (se 1 (by rfl) ⟨2868461, by rfl⟩ : syracuseStep 3824615 = 5736923) B5736923
theorem B80698447 : Blo 1590994 80698447 := bstep (se 1 (by rfl) ⟨60523835, by rfl⟩ : syracuseStep 80698447 = 121047671) B121047671
theorem B8059985 : Blo 1590994 8059985 := bstep (se 2 (by rfl) ⟨3022494, by rfl⟩ : syracuseStep 8059985 = 6044989) B6044989
theorem B3398753 : Blo 1590994 3398753 := bstep (se 2 (by rfl) ⟨1274532, by rfl⟩ : syracuseStep 3398753 = 2549065) B2549065
theorem B4029659 : Blo 1590994 4029659 := bstep (se 1 (by rfl) ⟨3022244, by rfl⟩ : syracuseStep 4029659 = 6044489) B6044489
theorem B4029689 : Blo 1590994 4029689 := bstep (se 2 (by rfl) ⟨1511133, by rfl⟩ : syracuseStep 4029689 = 3022267) B3022267
theorem B6454559 : Blo 1590994 6454559 := bstep (se 1 (by rfl) ⟨4840919, by rfl⟩ : syracuseStep 6454559 = 9681839) B9681839
theorem B5373215 : Blo 1590994 5373215 := bstep (se 1 (by rfl) ⟨4029911, by rfl⟩ : syracuseStep 5373215 = 8059823) B8059823
theorem B2686331 : Blo 1590994 2686331 := bstep (se 1 (by rfl) ⟨2014748, by rfl⟩ : syracuseStep 2686331 = 4029497) B4029497
theorem B13598219 : Blo 1590994 13598219 := bstep (se 1 (by rfl) ⟨10198664, by rfl⟩ : syracuseStep 13598219 = 20397329) B20397329
theorem B6045293 : Blo 1590994 6045293 := bstep (se 3 (by rfl) ⟨1133492, by rfl⟩ : syracuseStep 6045293 = 2266985) B2266985
theorem B2014895 : Blo 1590994 2014895 := bstep (se 1 (by rfl) ⟨1511171, by rfl⟩ : syracuseStep 2014895 = 3022343) B3022343
theorem B3022571 : Blo 1590994 3022571 := bstep (se 1 (by rfl) ⟨2266928, by rfl⟩ : syracuseStep 3022571 = 4533857) B4533857
theorem B3399479 : Blo 1590994 3399479 := bstep (se 1 (by rfl) ⟨2549609, by rfl⟩ : syracuseStep 3399479 = 5099219) B5099219
theorem B9068395 : Blo 1590994 9068395 := bstep (se 1 (by rfl) ⟨6801296, by rfl⟩ : syracuseStep 9068395 = 13602593) B13602593
theorem B4030337 : Blo 1590994 4030337 := bstep (se 2 (by rfl) ⟨1511376, by rfl⟩ : syracuseStep 4030337 = 3022753) B3022753
theorem B12910511 : Blo 1590994 12910511 := bstep (se 1 (by rfl) ⟨9682883, by rfl⟩ : syracuseStep 12910511 = 19365767) B19365767
theorem B2687195 : Blo 1590994 2687195 := bstep (se 1 (by rfl) ⟨2015396, by rfl⟩ : syracuseStep 2687195 = 4030793) B4030793
theorem B8601881 : Blo 1590994 8601881 := bstep (se 2 (by rfl) ⟨3225705, by rfl⟩ : syracuseStep 8601881 = 6451411) B6451411
theorem B2015543 : Blo 1590994 2015543 := bstep (se 1 (by rfl) ⟨1511657, by rfl⟩ : syracuseStep 2015543 = 3023315) B3023315
theorem B130695565 : Blo 1590994 130695565 := bstep (se 3 (by rfl) ⟨24505418, by rfl⟩ : syracuseStep 130695565 = 49010837) B49010837
theorem B2687431 : Blo 1590994 2687431 := bstep (se 1 (by rfl) ⟨2015573, by rfl⟩ : syracuseStep 2687431 = 4031147) B4031147
theorem B2015695 : Blo 1590994 2015695 := bstep (se 1 (by rfl) ⟨1511771, by rfl⟩ : syracuseStep 2015695 = 3023543) B3023543
theorem B3826153 : Blo 1590994 3826153 := bstep (se 2 (by rfl) ⟨1434807, by rfl⟩ : syracuseStep 3826153 = 2869615) B2869615
theorem B20406761 : Blo 1590994 20406761 := bstep (se 2 (by rfl) ⟨7652535, by rfl⟩ : syracuseStep 20406761 = 15305071) B15305071
theorem B2687465 : Blo 1590994 2687465 := bstep (se 2 (by rfl) ⟨1007799, by rfl⟩ : syracuseStep 2687465 = 2015599) B2015599
theorem B7651903 : Blo 1590994 7651903 := bstep (se 1 (by rfl) ⟨5738927, by rfl⟩ : syracuseStep 7651903 = 11477855) B11477855
theorem B248234615 : Blo 1590994 248234615 := bstep (se 1 (by rfl) ⟨186175961, by rfl⟩ : syracuseStep 248234615 = 372351923) B372351923
theorem B4530941 : Blo 1590994 4530941 := bstep (se 3 (by rfl) ⟨849551, by rfl⟩ : syracuseStep 4530941 = 1699103) B1699103
theorem B4031279 : Blo 1590994 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B29434681 : Blo 1590994 29434681 := bstep (se 2 (by rfl) ⟨11038005, by rfl⟩ : syracuseStep 29434681 = 22076011) B22076011
theorem B22094669 : Blo 1590994 22094669 := bstep (se 3 (by rfl) ⟨4142750, by rfl⟩ : syracuseStep 22094669 = 8285501) B8285501
theorem B33555383 : Blo 1590994 33555383 := bstep (se 1 (by rfl) ⟨25166537, by rfl⟩ : syracuseStep 33555383 = 50333075) B50333075
theorem B3580883 : Blo 1590994 3580883 := bstep (se 1 (by rfl) ⟨2685662, by rfl⟩ : syracuseStep 3580883 = 5371325) B5371325
theorem B4842451 : Blo 1590994 4842451 := bstep (se 1 (by rfl) ⟨3631838, by rfl⟩ : syracuseStep 4842451 = 7263677) B7263677
theorem B12084389 : Blo 1590994 12084389 := bstep (se 4 (by rfl) ⟨1132911, by rfl⟩ : syracuseStep 12084389 = 2265823) B2265823
theorem B3581135 : Blo 1590994 3581135 := bstep (se 1 (by rfl) ⟨2685851, by rfl⟩ : syracuseStep 3581135 = 5371703) B5371703
theorem B13600133 : Blo 1590994 13600133 := bstep (se 4 (by rfl) ⟨1275012, by rfl⟩ : syracuseStep 13600133 = 2550025) B2550025
theorem B78562703 : Blo 1590994 78562703 := bstep (se 1 (by rfl) ⟨58922027, by rfl⟩ : syracuseStep 78562703 = 117844055) B117844055
theorem B3106219 : Blo 1590994 3106219 := bstep (se 1 (by rfl) ⟨2329664, by rfl⟩ : syracuseStep 3106219 = 4659329) B4659329
theorem B3581459 : Blo 1590994 3581459 := bstep (se 1 (by rfl) ⟨2686094, by rfl⟩ : syracuseStep 3581459 = 5372189) B5372189
theorem B22947461 : Blo 1590994 22947461 := bstep (se 4 (by rfl) ⟨2151324, by rfl⟩ : syracuseStep 22947461 = 4302649) B4302649
theorem B3401435 : Blo 1590994 3401435 := bstep (se 1 (by rfl) ⟨2551076, by rfl⟩ : syracuseStep 3401435 = 5102153) B5102153
theorem B1591035 : Blo 1590994 1591035 := bstep (se 1 (by rfl) ⟨1193276, by rfl⟩ : syracuseStep 1591035 = 2386553) B2386553
theorem B1591071 : Blo 1590994 1591071 := bstep (se 1 (by rfl) ⟨1193303, by rfl⟩ : syracuseStep 1591071 = 2386607) B2386607
theorem B1591103 : Blo 1590994 1591103 := bstep (se 1 (by rfl) ⟨1193327, by rfl⟩ : syracuseStep 1591103 = 2386655) B2386655
theorem B1591279 : Blo 1590994 1591279 := bstep (se 1 (by rfl) ⟨1193459, by rfl⟩ : syracuseStep 1591279 = 2386919) B2386919
theorem B30615677 : Blo 1590994 30615677 := bstep (se 3 (by rfl) ⟨5740439, by rfl⟩ : syracuseStep 30615677 = 11480879) B11480879
theorem B73492609 : Blo 1590994 73492609 := bstep (se 2 (by rfl) ⟨27559728, by rfl⟩ : syracuseStep 73492609 = 55119457) B55119457
theorem B1591451 : Blo 1590994 1591451 := bstep (se 1 (by rfl) ⟨1193588, by rfl⟩ : syracuseStep 1591451 = 2387177) B2387177
theorem B1591487 : Blo 1590994 1591487 := bstep (se 1 (by rfl) ⟨1193615, by rfl⟩ : syracuseStep 1591487 = 2387231) B2387231
theorem B4303039 : Blo 1590994 4303039 := bstep (se 1 (by rfl) ⟨3227279, by rfl⟩ : syracuseStep 4303039 = 6454559) B6454559
theorem B3582143 : Blo 1590994 3582143 := bstep (se 1 (by rfl) ⟨2686607, by rfl⟩ : syracuseStep 3582143 = 5373215) B5373215
theorem B8063225 : Blo 1590994 8063225 := bstep (se 2 (by rfl) ⟨3023709, by rfl⟩ : syracuseStep 8063225 = 6047419) B6047419
theorem B6457639 : Blo 1590994 6457639 := bstep (se 1 (by rfl) ⟨4843229, by rfl⟩ : syracuseStep 6457639 = 9686459) B9686459
theorem B1591599 : Blo 1590994 1591599 := bstep (se 1 (by rfl) ⟨1193699, by rfl⟩ : syracuseStep 1591599 = 2387399) B2387399
theorem B5376347 : Blo 1590994 5376347 := bstep (se 1 (by rfl) ⟨4032260, by rfl⟩ : syracuseStep 5376347 = 8064521) B8064521
theorem B1591835 : Blo 1590994 1591835 := bstep (se 1 (by rfl) ⟨1193876, by rfl⟩ : syracuseStep 1591835 = 2387753) B2387753
theorem B1591839 : Blo 1590994 1591839 := bstep (se 1 (by rfl) ⟨1193879, by rfl⟩ : syracuseStep 1591839 = 2387759) B2387759
theorem B1592155 : Blo 1590994 1592155 := bstep (se 1 (by rfl) ⟨1194116, by rfl⟩ : syracuseStep 1592155 = 2388233) B2388233
theorem B2386847 : Blo 1590994 2386847 := bstep (se 1 (by rfl) ⟨1790135, by rfl⟩ : syracuseStep 2386847 = 3580271) B3580271
theorem B1592223 : Blo 1590994 1592223 := bstep (se 1 (by rfl) ⟨1194167, by rfl⟩ : syracuseStep 1592223 = 2388335) B2388335
theorem B2386895 : Blo 1590994 2386895 := bstep (se 1 (by rfl) ⟨1790171, by rfl⟩ : syracuseStep 2386895 = 3580343) B3580343
theorem B2386985 : Blo 1590994 2386985 := bstep (se 2 (by rfl) ⟨895119, by rfl⟩ : syracuseStep 2386985 = 1790239) B1790239
theorem B2386991 : Blo 1590994 2386991 := bstep (se 1 (by rfl) ⟨1790243, by rfl⟩ : syracuseStep 2386991 = 3580487) B3580487
theorem B1592367 : Blo 1590994 1592367 := bstep (se 1 (by rfl) ⟨1194275, by rfl⟩ : syracuseStep 1592367 = 2388551) B2388551
theorem B13601843 : Blo 1590994 13601843 := bstep (se 1 (by rfl) ⟨10201382, by rfl⟩ : syracuseStep 13601843 = 20402765) B20402765
theorem B2387015 : Blo 1590994 2387015 := bstep (se 1 (by rfl) ⟨1790261, by rfl⟩ : syracuseStep 2387015 = 3580523) B3580523
theorem B1592391 : Blo 1590994 1592391 := bstep (se 1 (by rfl) ⟨1194293, by rfl⟩ : syracuseStep 1592391 = 2388587) B2388587
theorem B3583097 : Blo 1590994 3583097 := bstep (se 2 (by rfl) ⟨1343661, by rfl⟩ : syracuseStep 3583097 = 2687323) B2687323
theorem B2796727 : Blo 1590994 2796727 := bstep (se 1 (by rfl) ⟨2097545, by rfl⟩ : syracuseStep 2796727 = 4195091) B4195091
theorem B1911991 : Blo 1590994 1911991 := bstep (se 1 (by rfl) ⟨1433993, by rfl⟩ : syracuseStep 1911991 = 2867987) B2867987
theorem B2419895 : Blo 1590994 2419895 := bstep (se 1 (by rfl) ⟨1814921, by rfl⟩ : syracuseStep 2419895 = 3629843) B3629843
theorem B1592543 : Blo 1590994 1592543 := bstep (se 1 (by rfl) ⟨1194407, by rfl⟩ : syracuseStep 1592543 = 2388815) B2388815
theorem B9071837 : Blo 1590994 9071837 := bstep (se 3 (by rfl) ⟨1700969, by rfl⟩ : syracuseStep 9071837 = 3401939) B3401939
theorem B8604953 : Blo 1590994 8604953 := bstep (se 2 (by rfl) ⟨3226857, by rfl⟩ : syracuseStep 8604953 = 6453715) B6453715
theorem B2387279 : Blo 1590994 2387279 := bstep (se 1 (by rfl) ⟨1790459, by rfl⟩ : syracuseStep 2387279 = 3580919) B3580919
theorem B4533583 : Blo 1590994 4533583 := bstep (se 1 (by rfl) ⟨3400187, by rfl⟩ : syracuseStep 4533583 = 6800375) B6800375
theorem B14527831 : Blo 1590994 14527831 := bstep (se 1 (by rfl) ⟨10895873, by rfl⟩ : syracuseStep 14527831 = 21791747) B21791747
theorem B21777779 : Blo 1590994 21777779 := bstep (se 1 (by rfl) ⟨16333334, by rfl⟩ : syracuseStep 21777779 = 32666669) B32666669
theorem B18369929 : Blo 1590994 18369929 := bstep (se 2 (by rfl) ⟨6888723, by rfl⟩ : syracuseStep 18369929 = 13777447) B13777447
theorem B2387369 : Blo 1590994 2387369 := bstep (se 2 (by rfl) ⟨895263, by rfl⟩ : syracuseStep 2387369 = 1790527) B1790527
theorem B61214129 : Blo 1590994 61214129 := bstep (se 2 (by rfl) ⟨22955298, by rfl⟩ : syracuseStep 61214129 = 45910597) B45910597
theorem B1592807 : Blo 1590994 1592807 := bstep (se 1 (by rfl) ⟨1194605, by rfl⟩ : syracuseStep 1592807 = 2389211) B2389211
theorem B2387519 : Blo 1590994 2387519 := bstep (se 1 (by rfl) ⟨1790639, by rfl⟩ : syracuseStep 2387519 = 3581279) B3581279
theorem B4533833 : Blo 1590994 4533833 := bstep (se 2 (by rfl) ⟨1700187, by rfl⟩ : syracuseStep 4533833 = 3400375) B3400375
theorem B1592923 : Blo 1590994 1592923 := bstep (se 1 (by rfl) ⟨1194692, by rfl⟩ : syracuseStep 1592923 = 2389385) B2389385
theorem B18124397 : Blo 1590994 18124397 := bstep (se 3 (by rfl) ⟨3398324, by rfl⟩ : syracuseStep 18124397 = 6796649) B6796649
theorem B3583763 : Blo 1590994 3583763 := bstep (se 1 (by rfl) ⟨2687822, by rfl⟩ : syracuseStep 3583763 = 5375645) B5375645
theorem B1912615 : Blo 1590994 1912615 := bstep (se 1 (by rfl) ⟨1434461, by rfl⟩ : syracuseStep 1912615 = 2868923) B2868923
theorem B2387783 : Blo 1590994 2387783 := bstep (se 1 (by rfl) ⟨1790837, by rfl⟩ : syracuseStep 2387783 = 3581675) B3581675
theorem B5369705 : Blo 1590994 5369705 := bstep (se 2 (by rfl) ⟨2013639, by rfl⟩ : syracuseStep 5369705 = 4027279) B4027279
theorem B2387867 : Blo 1590994 2387867 := bstep (se 1 (by rfl) ⟨1790900, by rfl⟩ : syracuseStep 2387867 = 3581801) B3581801
theorem B6041587 : Blo 1590994 6041587 := bstep (se 1 (by rfl) ⟨4531190, by rfl⟩ : syracuseStep 6041587 = 9062381) B9062381
theorem B107597929 : Blo 1590994 107597929 := bstep (se 2 (by rfl) ⟨40349223, by rfl⟩ : syracuseStep 107597929 = 80698447) B80698447
theorem B3584123 : Blo 1590994 3584123 := bstep (se 1 (by rfl) ⟨2688092, by rfl⟩ : syracuseStep 3584123 = 5376185) B5376185
theorem B8057231 : Blo 1590994 8057231 := bstep (se 1 (by rfl) ⟨6042923, by rfl⟩ : syracuseStep 8057231 = 12085847) B12085847
theorem B7647655 : Blo 1590994 7647655 := bstep (se 1 (by rfl) ⟨5735741, by rfl⟩ : syracuseStep 7647655 = 11471483) B11471483
theorem B2388431 : Blo 1590994 2388431 := bstep (se 1 (by rfl) ⟨1791323, by rfl⟩ : syracuseStep 2388431 = 3582647) B3582647
theorem B2388473 : Blo 1590994 2388473 := bstep (se 2 (by rfl) ⟨895677, by rfl⟩ : syracuseStep 2388473 = 1791355) B1791355
theorem B2388575 : Blo 1590994 2388575 := bstep (se 1 (by rfl) ⟨1791431, by rfl⟩ : syracuseStep 2388575 = 3582863) B3582863
theorem B4305503 : Blo 1590994 4305503 := bstep (se 1 (by rfl) ⟨3229127, by rfl⟩ : syracuseStep 4305503 = 6458255) B6458255
theorem B2265835 : Blo 1590994 2265835 := bstep (se 1 (by rfl) ⟨1699376, by rfl⟩ : syracuseStep 2265835 = 3398753) B3398753
theorem B8844023 : Blo 1590994 8844023 := bstep (se 1 (by rfl) ⟨6633017, by rfl⟩ : syracuseStep 8844023 = 13266035) B13266035
theorem B1790887 : Blo 1590994 1790887 := bstep (se 1 (by rfl) ⟨1343165, by rfl⟩ : syracuseStep 1790887 = 2686331) B2686331
theorem B4535291 : Blo 1590994 4535291 := bstep (se 1 (by rfl) ⟨3401468, by rfl⟩ : syracuseStep 4535291 = 6802937) B6802937
theorem B9065479 : Blo 1590994 9065479 := bstep (se 1 (by rfl) ⟨6799109, by rfl⟩ : syracuseStep 9065479 = 13598219) B13598219
theorem B2389055 : Blo 1590994 2389055 := bstep (se 1 (by rfl) ⟨1791791, by rfl⟩ : syracuseStep 2389055 = 3583583) B3583583
theorem B2389097 : Blo 1590994 2389097 := bstep (se 2 (by rfl) ⟨895911, by rfl⟩ : syracuseStep 2389097 = 1791823) B1791823
theorem B5371055 : Blo 1590994 5371055 := bstep (se 1 (by rfl) ⟨4028291, by rfl⟩ : syracuseStep 5371055 = 8056583) B8056583
theorem B2266319 : Blo 1590994 2266319 := bstep (se 1 (by rfl) ⟨1699739, by rfl⟩ : syracuseStep 2266319 = 3399479) B3399479
theorem B2389199 : Blo 1590994 2389199 := bstep (se 1 (by rfl) ⟨1791899, by rfl⟩ : syracuseStep 2389199 = 3583799) B3583799
theorem B4027603 : Blo 1590994 4027603 := bstep (se 1 (by rfl) ⟨3020702, by rfl⟩ : syracuseStep 4027603 = 6041405) B6041405
theorem B8607007 : Blo 1590994 8607007 := bstep (se 1 (by rfl) ⟨6455255, by rfl⟩ : syracuseStep 8607007 = 12910511) B12910511
theorem B2389403 : Blo 1590994 2389403 := bstep (se 1 (by rfl) ⟨1792052, by rfl⟩ : syracuseStep 2389403 = 3584105) B3584105
theorem B10196513 : Blo 1590994 10196513 := bstep (se 2 (by rfl) ⟨3823692, by rfl⟩ : syracuseStep 10196513 = 7647385) B7647385
theorem B5101127 : Blo 1590994 5101127 := bstep (se 1 (by rfl) ⟨3825845, by rfl⟩ : syracuseStep 5101127 = 7651691) B7651691
theorem B2152103 : Blo 1590994 2152103 := bstep (se 1 (by rfl) ⟨1614077, by rfl⟩ : syracuseStep 2152103 = 3228155) B3228155
theorem B6043319 : Blo 1590994 6043319 := bstep (se 1 (by rfl) ⟨4532489, by rfl⟩ : syracuseStep 6043319 = 9064979) B9064979
theorem B4536283 : Blo 1590994 4536283 := bstep (se 1 (by rfl) ⟨3402212, by rfl⟩ : syracuseStep 4536283 = 6804425) B6804425
theorem B3225683 : Blo 1590994 3225683 := bstep (se 1 (by rfl) ⟨2419262, by rfl⟩ : syracuseStep 3225683 = 4838525) B4838525
theorem B2685163 : Blo 1590994 2685163 := bstep (se 1 (by rfl) ⟨2013872, by rfl⟩ : syracuseStep 2685163 = 4027745) B4027745
theorem B5740787 : Blo 1590994 5740787 := bstep (se 1 (by rfl) ⟨4305590, by rfl⟩ : syracuseStep 5740787 = 8611181) B8611181
theorem B6797641 : Blo 1590994 6797641 := bstep (se 2 (by rfl) ⟨2549115, by rfl⟩ : syracuseStep 6797641 = 5098231) B5098231
theorem B2685467 : Blo 1590994 2685467 := bstep (se 1 (by rfl) ⟨2014100, by rfl⟩ : syracuseStep 2685467 = 4028201) B4028201
theorem B4906055 : Blo 1590994 4906055 := bstep (se 1 (by rfl) ⟨3679541, by rfl⟩ : syracuseStep 4906055 = 7359083) B7359083
theorem B5372999 : Blo 1590994 5372999 := bstep (se 1 (by rfl) ⟨4029749, by rfl⟩ : syracuseStep 5372999 = 8059499) B8059499
theorem B5373053 : Blo 1590994 5373053 := bstep (se 3 (by rfl) ⟨1007447, by rfl⟩ : syracuseStep 5373053 = 2014895) B2014895
theorem B2686135 : Blo 1590994 2686135 := bstep (se 1 (by rfl) ⟨2014601, by rfl⟩ : syracuseStep 2686135 = 4029203) B4029203
theorem B7265465 : Blo 1590994 7265465 := bstep (se 2 (by rfl) ⟨2724549, by rfl⟩ : syracuseStep 7265465 = 5449099) B5449099
theorem B58907837 : Blo 1590994 58907837 := bstep (se 3 (by rfl) ⟨11045219, by rfl⟩ : syracuseStep 58907837 = 22090439) B22090439
theorem B5373323 : Blo 1590994 5373323 := bstep (se 1 (by rfl) ⟨4029992, by rfl⟩ : syracuseStep 5373323 = 8059985) B8059985
theorem B2686439 : Blo 1590994 2686439 := bstep (se 1 (by rfl) ⟨2014829, by rfl⟩ : syracuseStep 2686439 = 4029659) B4029659
theorem B2686459 : Blo 1590994 2686459 := bstep (se 1 (by rfl) ⟨2014844, by rfl⟩ : syracuseStep 2686459 = 4029689) B4029689
theorem B4840967 : Blo 1590994 4840967 := bstep (se 1 (by rfl) ⟨3630725, by rfl⟩ : syracuseStep 4840967 = 7261451) B7261451
theorem B3022427 : Blo 1590994 3022427 := bstep (se 1 (by rfl) ⟨2266820, by rfl⟩ : syracuseStep 3022427 = 4533641) B4533641
theorem B4030195 : Blo 1590994 4030195 := bstep (se 1 (by rfl) ⟨3022646, by rfl⟩ : syracuseStep 4030195 = 6045293) B6045293
theorem B12091193 : Blo 1590994 12091193 := bstep (se 2 (by rfl) ⟨4534197, by rfl⟩ : syracuseStep 12091193 = 9068395) B9068395
theorem B2015047 : Blo 1590994 2015047 := bstep (se 1 (by rfl) ⟨1511285, by rfl⟩ : syracuseStep 2015047 = 3022571) B3022571
theorem B2686891 : Blo 1590994 2686891 := bstep (se 1 (by rfl) ⟨2015168, by rfl⟩ : syracuseStep 2686891 = 4030337) B4030337
theorem B10198973 : Blo 1590994 10198973 := bstep (se 3 (by rfl) ⟨1912307, by rfl⟩ : syracuseStep 10198973 = 3824615) B3824615
theorem B24494033 : Blo 1590994 24494033 := bstep (se 2 (by rfl) ⟨9185262, by rfl⟩ : syracuseStep 24494033 = 18370525) B18370525
theorem B8601821 : Blo 1590994 8601821 := bstep (se 3 (by rfl) ⟨1612841, by rfl⟩ : syracuseStep 8601821 = 3225683) B3225683
theorem B3580217 : Blo 1590994 3580217 := bstep (se 2 (by rfl) ⟨1342581, by rfl⟩ : syracuseStep 3580217 = 2685163) B2685163
theorem B8610185 : Blo 1590994 8610185 := bstep (se 2 (by rfl) ⟨3228819, by rfl⟩ : syracuseStep 8610185 = 6457639) B6457639
theorem B174260753 : Blo 1590994 174260753 := bstep (se 2 (by rfl) ⟨65347782, by rfl⟩ : syracuseStep 174260753 = 130695565) B130695565
theorem B2687519 : Blo 1590994 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B14729779 : Blo 1590994 14729779 := bstep (se 1 (by rfl) ⟨11047334, by rfl⟩ : syracuseStep 14729779 = 22094669) B22094669
theorem B2687593 : Blo 1590994 2687593 := bstep (se 2 (by rfl) ⟨1007847, by rfl⟩ : syracuseStep 2687593 = 2015695) B2015695
theorem B22938349 : Blo 1590994 22938349 := bstep (se 3 (by rfl) ⟨4300940, by rfl⟩ : syracuseStep 22938349 = 8601881) B8601881
theorem B3580703 : Blo 1590994 3580703 := bstep (se 1 (by rfl) ⟨2685527, by rfl⟩ : syracuseStep 3580703 = 5371055) B5371055
theorem B5374781 : Blo 1590994 5374781 := bstep (se 3 (by rfl) ⟨1007771, by rfl⟩ : syracuseStep 5374781 = 2015543) B2015543
theorem B58074077 : Blo 1590994 58074077 := bstep (se 3 (by rfl) ⟨10888889, by rfl⟩ : syracuseStep 58074077 = 21777779) B21777779
theorem B3400751 : Blo 1590994 3400751 := bstep (se 1 (by rfl) ⟨2550563, by rfl⟩ : syracuseStep 3400751 = 5101127) B5101127
theorem B6456601 : Blo 1590994 6456601 := bstep (se 2 (by rfl) ⟨2421225, by rfl⟩ : syracuseStep 6456601 = 4842451) B4842451
theorem B3827191 : Blo 1590994 3827191 := bstep (se 1 (by rfl) ⟨2870393, by rfl⟩ : syracuseStep 3827191 = 5740787) B5740787
theorem B5375483 : Blo 1590994 5375483 := bstep (se 1 (by rfl) ⟨4031612, by rfl⟩ : syracuseStep 5375483 = 8063225) B8063225
theorem B10200613 : Blo 1590994 10200613 := bstep (se 4 (by rfl) ⟨956307, by rfl⟩ : syracuseStep 10200613 = 1912615) B1912615
theorem B3728969 : Blo 1590994 3728969 := bstep (se 2 (by rfl) ⟨1398363, by rfl⟩ : syracuseStep 3728969 = 2796727) B2796727
theorem B2549321 : Blo 1590994 2549321 := bstep (se 2 (by rfl) ⟨955995, by rfl⟩ : syracuseStep 2549321 = 1911991) B1911991
theorem B3581513 : Blo 1590994 3581513 := bstep (se 2 (by rfl) ⟨1343067, by rfl⟩ : syracuseStep 3581513 = 2686135) B2686135
theorem B156984965 : Blo 1590994 156984965 := bstep (se 4 (by rfl) ⟨14717340, by rfl⟩ : syracuseStep 156984965 = 29434681) B29434681
theorem B1591231 : Blo 1590994 1591231 := bstep (se 1 (by rfl) ⟨1193423, by rfl⟩ : syracuseStep 1591231 = 2386847) B2386847
theorem B1591263 : Blo 1590994 1591263 := bstep (se 1 (by rfl) ⟨1193447, by rfl⟩ : syracuseStep 1591263 = 2386895) B2386895
theorem B3581945 : Blo 1590994 3581945 := bstep (se 2 (by rfl) ⟨1343229, by rfl⟩ : syracuseStep 3581945 = 2686459) B2686459
theorem B1591323 : Blo 1590994 1591323 := bstep (se 1 (by rfl) ⟨1193492, by rfl⟩ : syracuseStep 1591323 = 2386985) B2386985
theorem B1591327 : Blo 1590994 1591327 := bstep (se 1 (by rfl) ⟨1193495, by rfl⟩ : syracuseStep 1591327 = 2386991) B2386991
theorem B1591343 : Blo 1590994 1591343 := bstep (se 1 (by rfl) ⟨1193507, by rfl⟩ : syracuseStep 1591343 = 2387015) B2387015
theorem B3270703 : Blo 1590994 3270703 := bstep (se 1 (by rfl) ⟨2453027, by rfl⟩ : syracuseStep 3270703 = 4906055) B4906055
theorem B3581999 : Blo 1590994 3581999 := bstep (se 1 (by rfl) ⟨2686499, by rfl⟩ : syracuseStep 3581999 = 5372999) B5372999
theorem B3582035 : Blo 1590994 3582035 := bstep (se 1 (by rfl) ⟨2686526, by rfl⟩ : syracuseStep 3582035 = 5373053) B5373053
theorem B4843643 : Blo 1590994 4843643 := bstep (se 1 (by rfl) ⟨3632732, by rfl⟩ : syracuseStep 4843643 = 7265465) B7265465
theorem B6047891 : Blo 1590994 6047891 := bstep (se 1 (by rfl) ⟨4535918, by rfl⟩ : syracuseStep 6047891 = 9071837) B9071837
theorem B5736635 : Blo 1590994 5736635 := bstep (se 1 (by rfl) ⟨4302476, by rfl⟩ : syracuseStep 5736635 = 8604953) B8604953
theorem B1591519 : Blo 1590994 1591519 := bstep (se 1 (by rfl) ⟨1193639, by rfl⟩ : syracuseStep 1591519 = 2387279) B2387279
theorem B3582215 : Blo 1590994 3582215 := bstep (se 1 (by rfl) ⟨2686661, by rfl⟩ : syracuseStep 3582215 = 5373323) B5373323
theorem B1591579 : Blo 1590994 1591579 := bstep (se 1 (by rfl) ⟨1193684, by rfl⟩ : syracuseStep 1591579 = 2387369) B2387369
theorem B1591679 : Blo 1590994 1591679 := bstep (se 1 (by rfl) ⟨1193759, by rfl⟩ : syracuseStep 1591679 = 2387519) B2387519
theorem B65317421 : Blo 1590994 65317421 := bstep (se 3 (by rfl) ⟨12247016, by rfl⟩ : syracuseStep 65317421 = 24494033) B24494033
theorem B1591855 : Blo 1590994 1591855 := bstep (se 1 (by rfl) ⟨1193891, by rfl⟩ : syracuseStep 1591855 = 2387783) B2387783
theorem B3582521 : Blo 1590994 3582521 := bstep (se 2 (by rfl) ⟨1343445, by rfl⟩ : syracuseStep 3582521 = 2686891) B2686891
theorem B1591911 : Blo 1590994 1591911 := bstep (se 1 (by rfl) ⟨1193933, by rfl⟩ : syracuseStep 1591911 = 2387867) B2387867
theorem B6048377 : Blo 1590994 6048377 := bstep (se 2 (by rfl) ⟨2268141, by rfl⟩ : syracuseStep 6048377 = 4536283) B4536283
theorem B8055449 : Blo 1590994 8055449 := bstep (se 2 (by rfl) ⟨3020793, by rfl⟩ : syracuseStep 8055449 = 6041587) B6041587
theorem B12094109 : Blo 1590994 12094109 := bstep (se 3 (by rfl) ⟨2267645, by rfl⟩ : syracuseStep 12094109 = 4535291) B4535291
theorem B5737385 : Blo 1590994 5737385 := bstep (se 2 (by rfl) ⟨2151519, by rfl⟩ : syracuseStep 5737385 = 4303039) B4303039
theorem B1592287 : Blo 1590994 1592287 := bstep (se 1 (by rfl) ⟨1194215, by rfl⟩ : syracuseStep 1592287 = 2388431) B2388431
theorem B1592315 : Blo 1590994 1592315 := bstep (se 1 (by rfl) ⟨1194236, by rfl⟩ : syracuseStep 1592315 = 2388473) B2388473
theorem B1592383 : Blo 1590994 1592383 := bstep (se 1 (by rfl) ⟨1194287, by rfl⟩ : syracuseStep 1592383 = 2388575) B2388575
theorem B2870335 : Blo 1590994 2870335 := bstep (se 1 (by rfl) ⟨2152751, by rfl⟩ : syracuseStep 2870335 = 4305503) B4305503
theorem B165489743 : Blo 1590994 165489743 := bstep (se 1 (by rfl) ⟨124117307, by rfl⟩ : syracuseStep 165489743 = 248234615) B248234615
theorem B9063521 : Blo 1590994 9063521 := bstep (se 2 (by rfl) ⟨3398820, by rfl⟩ : syracuseStep 9063521 = 6797641) B6797641
theorem B3583241 : Blo 1590994 3583241 := bstep (se 2 (by rfl) ⟨1343715, by rfl⟩ : syracuseStep 3583241 = 2687431) B2687431
theorem B2387255 : Blo 1590994 2387255 := bstep (se 1 (by rfl) ⟨1790441, by rfl⟩ : syracuseStep 2387255 = 3580883) B3580883
theorem B1592703 : Blo 1590994 1592703 := bstep (se 1 (by rfl) ⟨1194527, by rfl⟩ : syracuseStep 1592703 = 2389055) B2389055
theorem B1592731 : Blo 1590994 1592731 := bstep (se 1 (by rfl) ⟨1194548, by rfl⟩ : syracuseStep 1592731 = 2389097) B2389097
theorem B10202537 : Blo 1590994 10202537 := bstep (se 2 (by rfl) ⟨3825951, by rfl⟩ : syracuseStep 10202537 = 7651903) B7651903
theorem B8056259 : Blo 1590994 8056259 := bstep (se 1 (by rfl) ⟨6042194, by rfl⟩ : syracuseStep 8056259 = 12084389) B12084389
theorem B2387423 : Blo 1590994 2387423 := bstep (se 1 (by rfl) ⟨1790567, by rfl⟩ : syracuseStep 2387423 = 3581135) B3581135
theorem B1592799 : Blo 1590994 1592799 := bstep (se 1 (by rfl) ⟨1194599, by rfl⟩ : syracuseStep 1592799 = 2389199) B2389199
theorem B52375135 : Blo 1590994 52375135 := bstep (se 1 (by rfl) ⟨39281351, by rfl⟩ : syracuseStep 52375135 = 78562703) B78562703
theorem B1592935 : Blo 1590994 1592935 := bstep (se 1 (by rfl) ⟨1194701, by rfl⟩ : syracuseStep 1592935 = 2389403) B2389403
theorem B2387639 : Blo 1590994 2387639 := bstep (se 1 (by rfl) ⟨1790729, by rfl⟩ : syracuseStep 2387639 = 3581459) B3581459
theorem B15298307 : Blo 1590994 15298307 := bstep (se 1 (by rfl) ⟨11473730, by rfl⟩ : syracuseStep 15298307 = 22947461) B22947461
theorem B2387849 : Blo 1590994 2387849 := bstep (se 2 (by rfl) ⟨895443, by rfl⟩ : syracuseStep 2387849 = 1790887) B1790887
theorem B12087305 : Blo 1590994 12087305 := bstep (se 2 (by rfl) ⟨4532739, by rfl⟩ : syracuseStep 12087305 = 9065479) B9065479
theorem B20410451 : Blo 1590994 20410451 := bstep (se 1 (by rfl) ⟨15307838, by rfl⟩ : syracuseStep 20410451 = 30615677) B30615677
theorem B2388095 : Blo 1590994 2388095 := bstep (se 1 (by rfl) ⟨1791071, by rfl⟩ : syracuseStep 2388095 = 3582143) B3582143
theorem B3584231 : Blo 1590994 3584231 := bstep (se 1 (by rfl) ⟨2688173, by rfl⟩ : syracuseStep 3584231 = 5376347) B5376347
theorem B5370137 : Blo 1590994 5370137 := bstep (se 2 (by rfl) ⟨2013801, by rfl⟩ : syracuseStep 5370137 = 4027603) B4027603
theorem B1790311 : Blo 1590994 1790311 := bstep (se 1 (by rfl) ⟨1342733, by rfl⟩ : syracuseStep 1790311 = 2685467) B2685467
theorem B5738941 : Blo 1590994 5738941 := bstep (se 3 (by rfl) ⟨1076051, by rfl⟩ : syracuseStep 5738941 = 2152103) B2152103
theorem B19370441 : Blo 1590994 19370441 := bstep (se 2 (by rfl) ⟨7263915, by rfl⟩ : syracuseStep 19370441 = 14527831) B14527831
theorem B4141625 : Blo 1590994 4141625 := bstep (se 2 (by rfl) ⟨1553109, by rfl⟩ : syracuseStep 4141625 = 3106219) B3106219
theorem B2388731 : Blo 1590994 2388731 := bstep (se 1 (by rfl) ⟨1791548, by rfl⟩ : syracuseStep 2388731 = 3583097) B3583097
theorem B40809419 : Blo 1590994 40809419 := bstep (se 1 (by rfl) ⟨30607064, by rfl⟩ : syracuseStep 40809419 = 61214129) B61214129
theorem B1790959 : Blo 1590994 1790959 := bstep (se 1 (by rfl) ⟨1343219, by rfl⟩ : syracuseStep 1790959 = 2686439) B2686439
theorem B2389175 : Blo 1590994 2389175 := bstep (se 1 (by rfl) ⟨1791881, by rfl⟩ : syracuseStep 2389175 = 3583763) B3583763
theorem B2389415 : Blo 1590994 2389415 := bstep (se 1 (by rfl) ⟨1792061, by rfl⟩ : syracuseStep 2389415 = 3584123) B3584123
theorem B143463905 : Blo 1590994 143463905 := bstep (se 2 (by rfl) ⟨53798964, by rfl⟩ : syracuseStep 143463905 = 107597929) B107597929
theorem B1791463 : Blo 1590994 1791463 := bstep (se 1 (by rfl) ⟨1343597, by rfl⟩ : syracuseStep 1791463 = 2687195) B2687195
theorem B97990145 : Blo 1590994 97990145 := bstep (se 2 (by rfl) ⟨36746304, by rfl⟩ : syracuseStep 97990145 = 73492609) B73492609
theorem B5371487 : Blo 1590994 5371487 := bstep (se 1 (by rfl) ⟨4028615, by rfl⟩ : syracuseStep 5371487 = 8057231) B8057231
theorem B13604507 : Blo 1590994 13604507 := bstep (se 1 (by rfl) ⟨10203380, by rfl⟩ : syracuseStep 13604507 = 20406761) B20406761
theorem B1791643 : Blo 1590994 1791643 := bstep (se 1 (by rfl) ⟨1343732, by rfl⟩ : syracuseStep 1791643 = 2687465) B2687465
theorem B6453053 : Blo 1590994 6453053 := bstep (se 3 (by rfl) ⟨1209947, by rfl⟩ : syracuseStep 6453053 = 2419895) B2419895
theorem B3020627 : Blo 1590994 3020627 := bstep (se 1 (by rfl) ⟨2265470, by rfl⟩ : syracuseStep 3020627 = 4530941) B4530941
theorem B6043517 : Blo 1590994 6043517 := bstep (se 3 (by rfl) ⟨1133159, by rfl⟩ : syracuseStep 6043517 = 2266319) B2266319
theorem B10196873 : Blo 1590994 10196873 := bstep (se 2 (by rfl) ⟨3823827, by rfl⟩ : syracuseStep 10196873 = 7647655) B7647655
theorem B22370255 : Blo 1590994 22370255 := bstep (se 1 (by rfl) ⟨16777691, by rfl⟩ : syracuseStep 22370255 = 33555383) B33555383
theorem B5101537 : Blo 1590994 5101537 := bstep (se 2 (by rfl) ⟨1913076, by rfl⟩ : syracuseStep 5101537 = 3826153) B3826153
theorem B9066755 : Blo 1590994 9066755 := bstep (se 1 (by rfl) ⟨6800066, by rfl⟩ : syracuseStep 9066755 = 13600133) B13600133
theorem B3021113 : Blo 1590994 3021113 := bstep (se 2 (by rfl) ⟨1132917, by rfl⟩ : syracuseStep 3021113 = 2265835) B2265835
theorem B6797675 : Blo 1590994 6797675 := bstep (se 1 (by rfl) ⟨5098256, by rfl⟩ : syracuseStep 6797675 = 10196513) B10196513
theorem B48986477 : Blo 1590994 48986477 := bstep (se 3 (by rfl) ⟨9184964, by rfl⟩ : syracuseStep 48986477 = 18369929) B18369929
theorem B4028879 : Blo 1590994 4028879 := bstep (se 1 (by rfl) ⟨3021659, by rfl⟩ : syracuseStep 4028879 = 6043319) B6043319
theorem B2267623 : Blo 1590994 2267623 := bstep (se 1 (by rfl) ⟨1700717, by rfl⟩ : syracuseStep 2267623 = 3401435) B3401435
theorem B12090221 : Blo 1590994 12090221 := bstep (se 3 (by rfl) ⟨2266916, by rfl⟩ : syracuseStep 12090221 = 4533833) B4533833
theorem B11476009 : Blo 1590994 11476009 := bstep (se 2 (by rfl) ⟨4303503, by rfl⟩ : syracuseStep 11476009 = 8607007) B8607007
theorem B6044777 : Blo 1590994 6044777 := bstep (se 2 (by rfl) ⟨2266791, by rfl⟩ : syracuseStep 6044777 = 4533583) B4533583
theorem B23584061 : Blo 1590994 23584061 := bstep (se 3 (by rfl) ⟨4422011, by rfl⟩ : syracuseStep 23584061 = 8844023) B8844023
theorem B9067895 : Blo 1590994 9067895 := bstep (se 1 (by rfl) ⟨6800921, by rfl⟩ : syracuseStep 9067895 = 13601843) B13601843
theorem B39271891 : Blo 1590994 39271891 := bstep (se 1 (by rfl) ⟨29453918, by rfl⟩ : syracuseStep 39271891 = 58907837) B58907837
theorem B5373593 : Blo 1590994 5373593 := bstep (se 2 (by rfl) ⟨2015097, by rfl⟩ : syracuseStep 5373593 = 4030195) B4030195
theorem B3227311 : Blo 1590994 3227311 := bstep (se 1 (by rfl) ⟨2420483, by rfl⟩ : syracuseStep 3227311 = 4840967) B4840967
theorem B2014951 : Blo 1590994 2014951 := bstep (se 1 (by rfl) ⟨1511213, by rfl⟩ : syracuseStep 2014951 = 3022427) B3022427
theorem B12082931 : Blo 1590994 12082931 := bstep (se 1 (by rfl) ⟨9062198, by rfl⟩ : syracuseStep 12082931 = 18124397) B18124397
theorem B2686729 : Blo 1590994 2686729 := bstep (se 2 (by rfl) ⟨1007523, by rfl⟩ : syracuseStep 2686729 = 2015047) B2015047
theorem B8060795 : Blo 1590994 8060795 := bstep (se 1 (by rfl) ⟨6045596, by rfl⟩ : syracuseStep 8060795 = 12091193) B12091193
theorem B3579803 : Blo 1590994 3579803 := bstep (se 1 (by rfl) ⟨2684852, by rfl⟩ : syracuseStep 3579803 = 5369705) B5369705
theorem B6799315 : Blo 1590994 6799315 := bstep (se 1 (by rfl) ⟨5099486, by rfl⟩ : syracuseStep 6799315 = 10198973) B10198973
theorem B13606967 : Blo 1590994 13606967 := bstep (se 1 (by rfl) ⟨10205225, by rfl⟩ : syracuseStep 13606967 = 20410451) B20410451
theorem B9068669 : Blo 1590994 9068669 := bstep (se 3 (by rfl) ⟨1700375, by rfl⟩ : syracuseStep 9068669 = 3400751) B3400751
theorem B5734547 : Blo 1590994 5734547 := bstep (se 1 (by rfl) ⟨4300910, by rfl⟩ : syracuseStep 5734547 = 8601821) B8601821
theorem B3580091 : Blo 1590994 3580091 := bstep (se 1 (by rfl) ⟨2685068, by rfl⟩ : syracuseStep 3580091 = 5370137) B5370137
theorem B7651921 : Blo 1590994 7651921 := bstep (se 2 (by rfl) ⟨2869470, by rfl⟩ : syracuseStep 7651921 = 5738941) B5738941
theorem B27206279 : Blo 1590994 27206279 := bstep (se 1 (by rfl) ⟨20404709, by rfl⟩ : syracuseStep 27206279 = 40809419) B40809419
theorem B3023497 : Blo 1590994 3023497 := bstep (se 2 (by rfl) ⟨1133811, by rfl⟩ : syracuseStep 3023497 = 2267623) B2267623
theorem B38716051 : Blo 1590994 38716051 := bstep (se 1 (by rfl) ⟨29037038, by rfl⟩ : syracuseStep 38716051 = 58074077) B58074077
theorem B62890829 : Blo 1590994 62890829 := bstep (se 3 (by rfl) ⟨11792030, by rfl⟩ : syracuseStep 62890829 = 23584061) B23584061
theorem B95642603 : Blo 1590994 95642603 := bstep (se 1 (by rfl) ⟨71731952, by rfl⟩ : syracuseStep 95642603 = 143463905) B143463905
theorem B3580991 : Blo 1590994 3580991 := bstep (se 1 (by rfl) ⟨2685743, by rfl⟩ : syracuseStep 3580991 = 5371487) B5371487
theorem B9069671 : Blo 1590994 9069671 := bstep (se 1 (by rfl) ⟨6802253, by rfl⟩ : syracuseStep 9069671 = 13604507) B13604507
theorem B4302035 : Blo 1590994 4302035 := bstep (se 1 (by rfl) ⟨3226526, by rfl⟩ : syracuseStep 4302035 = 6453053) B6453053
theorem B4031927 : Blo 1590994 4031927 := bstep (se 1 (by rfl) ⟨3023945, by rfl⟩ : syracuseStep 4031927 = 6047891) B6047891
theorem B11044333 : Blo 1590994 11044333 := bstep (se 3 (by rfl) ⟨2070812, by rfl⟩ : syracuseStep 11044333 = 4141625) B4141625
theorem B4531783 : Blo 1590994 4531783 := bstep (se 1 (by rfl) ⟨3398837, by rfl⟩ : syracuseStep 4531783 = 6797675) B6797675
theorem B4032251 : Blo 1590994 4032251 := bstep (se 1 (by rfl) ⟨3024188, by rfl⟩ : syracuseStep 4032251 = 6048377) B6048377
theorem B8062739 : Blo 1590994 8062739 := bstep (se 1 (by rfl) ⟨6047054, by rfl⟩ : syracuseStep 8062739 = 12094109) B12094109
theorem B13600817 : Blo 1590994 13600817 := bstep (se 2 (by rfl) ⟨5100306, by rfl⟩ : syracuseStep 13600817 = 10200613) B10200613
theorem B1591503 : Blo 1590994 1591503 := bstep (se 1 (by rfl) ⟨1193627, by rfl⟩ : syracuseStep 1591503 = 2387255) B2387255
theorem B4303081 : Blo 1590994 4303081 := bstep (se 2 (by rfl) ⟨1613655, by rfl⟩ : syracuseStep 4303081 = 3227311) B3227311
theorem B6801691 : Blo 1590994 6801691 := bstep (se 1 (by rfl) ⟨5101268, by rfl⟩ : syracuseStep 6801691 = 10202537) B10202537
theorem B1591615 : Blo 1590994 1591615 := bstep (se 1 (by rfl) ⟨1193711, by rfl⟩ : syracuseStep 1591615 = 2387423) B2387423
theorem B3582305 : Blo 1590994 3582305 := bstep (se 2 (by rfl) ⟨1343364, by rfl⟩ : syracuseStep 3582305 = 2686729) B2686729
theorem B3582395 : Blo 1590994 3582395 := bstep (se 1 (by rfl) ⟨2686796, by rfl⟩ : syracuseStep 3582395 = 5373593) B5373593
theorem B1591759 : Blo 1590994 1591759 := bstep (se 1 (by rfl) ⟨1193819, by rfl⟩ : syracuseStep 1591759 = 2387639) B2387639
theorem B8055287 : Blo 1590994 8055287 := bstep (se 1 (by rfl) ⟨6041465, by rfl⟩ : syracuseStep 8055287 = 12082931) B12082931
theorem B1591899 : Blo 1590994 1591899 := bstep (se 1 (by rfl) ⟨1193924, by rfl⟩ : syracuseStep 1591899 = 2387849) B2387849
theorem B2386535 : Blo 1590994 2386535 := bstep (se 1 (by rfl) ⟨1789901, by rfl⟩ : syracuseStep 2386535 = 3579803) B3579803
theorem B6802049 : Blo 1590994 6802049 := bstep (se 2 (by rfl) ⟨2550768, by rfl⟩ : syracuseStep 6802049 = 5101537) B5101537
theorem B4360937 : Blo 1590994 4360937 := bstep (se 2 (by rfl) ⟨1635351, by rfl⟩ : syracuseStep 4360937 = 3270703) B3270703
theorem B1592063 : Blo 1590994 1592063 := bstep (se 1 (by rfl) ⟨1194047, by rfl⟩ : syracuseStep 1592063 = 2388095) B2388095
theorem B2386811 : Blo 1590994 2386811 := bstep (se 1 (by rfl) ⟨1790108, by rfl⟩ : syracuseStep 2386811 = 3580217) B3580217
theorem B441305981 : Blo 1590994 441305981 := bstep (se 3 (by rfl) ⟨82744871, by rfl⟩ : syracuseStep 441305981 = 165489743) B165489743
theorem B12913627 : Blo 1590994 12913627 := bstep (se 1 (by rfl) ⟨9685220, by rfl⟩ : syracuseStep 12913627 = 19370441) B19370441
theorem B116173835 : Blo 1590994 116173835 := bstep (se 1 (by rfl) ⟨87130376, by rfl⟩ : syracuseStep 116173835 = 174260753) B174260753
theorem B2387081 : Blo 1590994 2387081 := bstep (se 2 (by rfl) ⟨895155, by rfl⟩ : syracuseStep 2387081 = 1790311) B1790311
theorem B1592487 : Blo 1590994 1592487 := bstep (se 1 (by rfl) ⟨1194365, by rfl⟩ : syracuseStep 1592487 = 2388731) B2388731
theorem B2387135 : Blo 1590994 2387135 := bstep (se 1 (by rfl) ⟨1790351, by rfl⟩ : syracuseStep 2387135 = 3580703) B3580703
theorem B3583187 : Blo 1590994 3583187 := bstep (se 1 (by rfl) ⟨2687390, by rfl⟩ : syracuseStep 3583187 = 5374781) B5374781
theorem B19639705 : Blo 1590994 19639705 := bstep (se 2 (by rfl) ⟨7364889, by rfl⟩ : syracuseStep 19639705 = 14729779) B14729779
theorem B1592783 : Blo 1590994 1592783 := bstep (se 1 (by rfl) ⟨1194587, by rfl⟩ : syracuseStep 1592783 = 2389175) B2389175
theorem B3583457 : Blo 1590994 3583457 := bstep (se 2 (by rfl) ⟨1343796, by rfl⟩ : syracuseStep 3583457 = 2687593) B2687593
theorem B1592943 : Blo 1590994 1592943 := bstep (se 1 (by rfl) ⟨1194707, by rfl⟩ : syracuseStep 1592943 = 2389415) B2389415
theorem B30584465 : Blo 1590994 30584465 := bstep (se 2 (by rfl) ⟨11469174, by rfl⟩ : syracuseStep 30584465 = 22938349) B22938349
theorem B3583655 : Blo 1590994 3583655 := bstep (se 1 (by rfl) ⟨2687741, by rfl⟩ : syracuseStep 3583655 = 5375483) B5375483
theorem B65326763 : Blo 1590994 65326763 := bstep (se 1 (by rfl) ⟨48995072, by rfl⟩ : syracuseStep 65326763 = 97990145) B97990145
theorem B2485979 : Blo 1590994 2485979 := bstep (se 1 (by rfl) ⟨1864484, by rfl⟩ : syracuseStep 2485979 = 3728969) B3728969
theorem B1699547 : Blo 1590994 1699547 := bstep (se 1 (by rfl) ⟨1274660, by rfl⟩ : syracuseStep 1699547 = 2549321) B2549321
theorem B2387675 : Blo 1590994 2387675 := bstep (se 1 (by rfl) ⟨1790756, by rfl⟩ : syracuseStep 2387675 = 3581513) B3581513
theorem B104656643 : Blo 1590994 104656643 := bstep (se 1 (by rfl) ⟨78492482, by rfl⟩ : syracuseStep 104656643 = 156984965) B156984965
theorem B14913503 : Blo 1590994 14913503 := bstep (se 1 (by rfl) ⟨11185127, by rfl⟩ : syracuseStep 14913503 = 22370255) B22370255
theorem B2387945 : Blo 1590994 2387945 := bstep (se 2 (by rfl) ⟨895479, by rfl⟩ : syracuseStep 2387945 = 1790959) B1790959
theorem B2387963 : Blo 1590994 2387963 := bstep (se 1 (by rfl) ⟨1790972, by rfl⟩ : syracuseStep 2387963 = 3581945) B3581945
theorem B2387999 : Blo 1590994 2387999 := bstep (se 1 (by rfl) ⟨1790999, by rfl⟩ : syracuseStep 2387999 = 3581999) B3581999
theorem B2388023 : Blo 1590994 2388023 := bstep (se 1 (by rfl) ⟨1791017, by rfl⟩ : syracuseStep 2388023 = 3582035) B3582035
theorem B34435205 : Blo 1590994 34435205 := bstep (se 4 (by rfl) ⟨3228300, by rfl⟩ : syracuseStep 34435205 = 6456601) B6456601
theorem B2388143 : Blo 1590994 2388143 := bstep (se 1 (by rfl) ⟨1791107, by rfl⟩ : syracuseStep 2388143 = 3582215) B3582215
theorem B32657651 : Blo 1590994 32657651 := bstep (se 1 (by rfl) ⟨24493238, by rfl⟩ : syracuseStep 32657651 = 48986477) B48986477
theorem B43544947 : Blo 1590994 43544947 := bstep (se 1 (by rfl) ⟨32658710, by rfl⟩ : syracuseStep 43544947 = 65317421) B65317421
theorem B2388347 : Blo 1590994 2388347 := bstep (se 1 (by rfl) ⟨1791260, by rfl⟩ : syracuseStep 2388347 = 3582521) B3582521
theorem B5370299 : Blo 1590994 5370299 := bstep (se 1 (by rfl) ⟨4027724, by rfl⟩ : syracuseStep 5370299 = 8055449) B8055449
theorem B2388617 : Blo 1590994 2388617 := bstep (se 2 (by rfl) ⟨895731, by rfl⟩ : syracuseStep 2388617 = 1791463) B1791463
theorem B6042347 : Blo 1590994 6042347 := bstep (se 1 (by rfl) ⟨4531760, by rfl⟩ : syracuseStep 6042347 = 9063521) B9063521
theorem B69833513 : Blo 1590994 69833513 := bstep (se 2 (by rfl) ⟨26187567, by rfl⟩ : syracuseStep 69833513 = 52375135) B52375135
theorem B2388827 : Blo 1590994 2388827 := bstep (se 1 (by rfl) ⟨1791620, by rfl⟩ : syracuseStep 2388827 = 3583241) B3583241
theorem B2388857 : Blo 1590994 2388857 := bstep (se 2 (by rfl) ⟨895821, by rfl⟩ : syracuseStep 2388857 = 1791643) B1791643
theorem B5370839 : Blo 1590994 5370839 := bstep (se 1 (by rfl) ⟨4028129, by rfl⟩ : syracuseStep 5370839 = 8056259) B8056259
theorem B9065753 : Blo 1590994 9065753 := bstep (se 2 (by rfl) ⟨3399657, by rfl⟩ : syracuseStep 9065753 = 6799315) B6799315
theorem B8058203 : Blo 1590994 8058203 := bstep (se 1 (by rfl) ⟨6043652, by rfl⟩ : syracuseStep 8058203 = 12087305) B12087305
theorem B2389487 : Blo 1590994 2389487 := bstep (se 1 (by rfl) ⟨1792115, by rfl⟩ : syracuseStep 2389487 = 3584231) B3584231
theorem B12916381 : Blo 1590994 12916381 := bstep (se 3 (by rfl) ⟨2421821, by rfl⟩ : syracuseStep 12916381 = 4843643) B4843643
theorem B15308453 : Blo 1590994 15308453 := bstep (se 4 (by rfl) ⟨1435167, by rfl⟩ : syracuseStep 15308453 = 2870335) B2870335
theorem B1791679 : Blo 1590994 1791679 := bstep (se 1 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 1791679 = 2687519) B2687519
theorem B22960493 : Blo 1590994 22960493 := bstep (se 3 (by rfl) ⟨4305092, by rfl⟩ : syracuseStep 22960493 = 8610185) B8610185
theorem B2013751 : Blo 1590994 2013751 := bstep (se 1 (by rfl) ⟨1510313, by rfl⟩ : syracuseStep 2013751 = 3020627) B3020627
theorem B4029011 : Blo 1590994 4029011 := bstep (se 1 (by rfl) ⟨3021758, by rfl⟩ : syracuseStep 4029011 = 6043517) B6043517
theorem B6797915 : Blo 1590994 6797915 := bstep (se 1 (by rfl) ⟨5098436, by rfl⟩ : syracuseStep 6797915 = 10196873) B10196873
theorem B15301345 : Blo 1590994 15301345 := bstep (se 2 (by rfl) ⟨5738004, by rfl⟩ : syracuseStep 15301345 = 11476009) B11476009
theorem B3824423 : Blo 1590994 3824423 := bstep (se 1 (by rfl) ⟨2868317, by rfl⟩ : syracuseStep 3824423 = 5736635) B5736635
theorem B6044503 : Blo 1590994 6044503 := bstep (se 1 (by rfl) ⟨4533377, by rfl⟩ : syracuseStep 6044503 = 9066755) B9066755
theorem B2014075 : Blo 1590994 2014075 := bstep (se 1 (by rfl) ⟨1510556, by rfl⟩ : syracuseStep 2014075 = 3021113) B3021113
theorem B2685919 : Blo 1590994 2685919 := bstep (se 1 (by rfl) ⟨2014439, by rfl⟩ : syracuseStep 2685919 = 4028879) B4028879
theorem B8060147 : Blo 1590994 8060147 := bstep (se 1 (by rfl) ⟨6045110, by rfl⟩ : syracuseStep 8060147 = 12090221) B12090221
theorem B52362521 : Blo 1590994 52362521 := bstep (se 2 (by rfl) ⟨19635945, by rfl⟩ : syracuseStep 52362521 = 39271891) B39271891
theorem B3824923 : Blo 1590994 3824923 := bstep (se 1 (by rfl) ⟨2868692, by rfl⟩ : syracuseStep 3824923 = 5737385) B5737385
theorem B5102921 : Blo 1590994 5102921 := bstep (se 2 (by rfl) ⟨1913595, by rfl⟩ : syracuseStep 5102921 = 3827191) B3827191
theorem B4029851 : Blo 1590994 4029851 := bstep (se 1 (by rfl) ⟨3022388, by rfl⟩ : syracuseStep 4029851 = 6044777) B6044777
theorem B6045263 : Blo 1590994 6045263 := bstep (se 1 (by rfl) ⟨4533947, by rfl⟩ : syracuseStep 6045263 = 9067895) B9067895
theorem B2686601 : Blo 1590994 2686601 := bstep (se 2 (by rfl) ⟨1007475, by rfl⟩ : syracuseStep 2686601 = 2014951) B2014951
theorem B10198871 : Blo 1590994 10198871 := bstep (se 1 (by rfl) ⟨7649153, by rfl⟩ : syracuseStep 10198871 = 15298307) B15298307
theorem B5373863 : Blo 1590994 5373863 := bstep (se 1 (by rfl) ⟨4030397, by rfl⟩ : syracuseStep 5373863 = 8060795) B8060795
theorem B6045779 : Blo 1590994 6045779 := bstep (se 1 (by rfl) ⟨4534334, by rfl⟩ : syracuseStep 6045779 = 9068669) B9068669
theorem B3580199 : Blo 1590994 3580199 := bstep (se 1 (by rfl) ⟨2685149, by rfl⟩ : syracuseStep 3580199 = 5370299) B5370299
theorem B9068921 : Blo 1590994 9068921 := bstep (se 2 (by rfl) ⟨3400845, by rfl⟩ : syracuseStep 9068921 = 6801691) B6801691
theorem B18137519 : Blo 1590994 18137519 := bstep (se 1 (by rfl) ⟨13603139, by rfl⟩ : syracuseStep 18137519 = 27206279) B27206279
theorem B41927219 : Blo 1590994 41927219 := bstep (se 1 (by rfl) ⟨31445414, by rfl⟩ : syracuseStep 41927219 = 62890829) B62890829
theorem B3580559 : Blo 1590994 3580559 := bstep (se 1 (by rfl) ⟨2685419, by rfl⟩ : syracuseStep 3580559 = 5370839) B5370839
theorem B6046447 : Blo 1590994 6046447 := bstep (se 1 (by rfl) ⟨4534835, by rfl⟩ : syracuseStep 6046447 = 9069671) B9069671
theorem B2868023 : Blo 1590994 2868023 := bstep (se 1 (by rfl) ⟨2151017, by rfl⟩ : syracuseStep 2868023 = 4302035) B4302035
theorem B4031329 : Blo 1590994 4031329 := bstep (se 2 (by rfl) ⟨1511748, by rfl⟩ : syracuseStep 4031329 = 3023497) B3023497
theorem B2687951 : Blo 1590994 2687951 := bstep (se 1 (by rfl) ⟨2015963, by rfl⟩ : syracuseStep 2687951 = 4031927) B4031927
theorem B2688167 : Blo 1590994 2688167 := bstep (se 1 (by rfl) ⟨2016125, by rfl⟩ : syracuseStep 2688167 = 4032251) B4032251
theorem B5375159 : Blo 1590994 5375159 := bstep (se 1 (by rfl) ⟨4031369, by rfl⟩ : syracuseStep 5375159 = 8062739) B8062739
theorem B3581225 : Blo 1590994 3581225 := bstep (se 2 (by rfl) ⟨1342959, by rfl⟩ : syracuseStep 3581225 = 2685919) B2685919
theorem B4531943 : Blo 1590994 4531943 := bstep (se 1 (by rfl) ⟨3398957, by rfl⟩ : syracuseStep 4531943 = 6797915) B6797915
theorem B1591023 : Blo 1590994 1591023 := bstep (se 1 (by rfl) ⟨1193267, by rfl⟩ : syracuseStep 1591023 = 2386535) B2386535
theorem B40822541 : Blo 1590994 40822541 := bstep (se 3 (by rfl) ⟨7654226, by rfl⟩ : syracuseStep 40822541 = 15308453) B15308453
theorem B174204701 : Blo 1590994 174204701 := bstep (se 3 (by rfl) ⟨32663381, by rfl⟩ : syracuseStep 174204701 = 65326763) B65326763
theorem B2549615 : Blo 1590994 2549615 := bstep (se 1 (by rfl) ⟨1912211, by rfl⟩ : syracuseStep 2549615 = 3824423) B3824423
theorem B4532125 : Blo 1590994 4532125 := bstep (se 3 (by rfl) ⟨849773, by rfl⟩ : syracuseStep 4532125 = 1699547) B1699547
theorem B1591207 : Blo 1590994 1591207 := bstep (se 1 (by rfl) ⟨1193405, by rfl⟩ : syracuseStep 1591207 = 2386811) B2386811
theorem B77449223 : Blo 1590994 77449223 := bstep (se 1 (by rfl) ⟨58086917, by rfl⟩ : syracuseStep 77449223 = 116173835) B116173835
theorem B1591387 : Blo 1590994 1591387 := bstep (se 1 (by rfl) ⟨1193540, by rfl⟩ : syracuseStep 1591387 = 2387081) B2387081
theorem B186222701 : Blo 1590994 186222701 := bstep (se 3 (by rfl) ⟨34916756, by rfl⟩ : syracuseStep 186222701 = 69833513) B69833513
theorem B1591423 : Blo 1590994 1591423 := bstep (se 1 (by rfl) ⟨1193567, by rfl⟩ : syracuseStep 1591423 = 2387135) B2387135
theorem B34908347 : Blo 1590994 34908347 := bstep (se 1 (by rfl) ⟨26181260, by rfl⟩ : syracuseStep 34908347 = 52362521) B52362521
theorem B17221841 : Blo 1590994 17221841 := bstep (se 2 (by rfl) ⟨6458190, by rfl⟩ : syracuseStep 17221841 = 12916381) B12916381
theorem B3401947 : Blo 1590994 3401947 := bstep (se 1 (by rfl) ⟨2551460, by rfl⟩ : syracuseStep 3401947 = 5102921) B5102921
theorem B1657319 : Blo 1590994 1657319 := bstep (se 1 (by rfl) ⟨1242989, by rfl⟩ : syracuseStep 1657319 = 2485979) B2485979
theorem B1591783 : Blo 1590994 1591783 := bstep (se 1 (by rfl) ⟨1193837, by rfl⟩ : syracuseStep 1591783 = 2387675) B2387675
theorem B58903109 : Blo 1590994 58903109 := bstep (se 4 (by rfl) ⟨5522166, by rfl⟩ : syracuseStep 58903109 = 11044333) B11044333
theorem B3582575 : Blo 1590994 3582575 := bstep (se 1 (by rfl) ⟨2686931, by rfl⟩ : syracuseStep 3582575 = 5373863) B5373863
theorem B1591963 : Blo 1590994 1591963 := bstep (se 1 (by rfl) ⟨1193972, by rfl⟩ : syracuseStep 1591963 = 2387945) B2387945
theorem B1591975 : Blo 1590994 1591975 := bstep (se 1 (by rfl) ⟨1193981, by rfl⟩ : syracuseStep 1591975 = 2387963) B2387963
theorem B1591999 : Blo 1590994 1591999 := bstep (se 1 (by rfl) ⟨1193999, by rfl⟩ : syracuseStep 1591999 = 2387999) B2387999
theorem B1592015 : Blo 1590994 1592015 := bstep (se 1 (by rfl) ⟨1194011, by rfl⟩ : syracuseStep 1592015 = 2388023) B2388023
theorem B9071311 : Blo 1590994 9071311 := bstep (se 1 (by rfl) ⟨6803483, by rfl⟩ : syracuseStep 9071311 = 13606967) B13606967
theorem B22956803 : Blo 1590994 22956803 := bstep (se 1 (by rfl) ⟨17217602, by rfl⟩ : syracuseStep 22956803 = 34435205) B34435205
theorem B1592095 : Blo 1590994 1592095 := bstep (se 1 (by rfl) ⟨1194071, by rfl⟩ : syracuseStep 1592095 = 2388143) B2388143
theorem B2386727 : Blo 1590994 2386727 := bstep (se 1 (by rfl) ⟨1790045, by rfl⟩ : syracuseStep 2386727 = 3580091) B3580091
theorem B1592231 : Blo 1590994 1592231 := bstep (se 1 (by rfl) ⟨1194173, by rfl⟩ : syracuseStep 1592231 = 2388347) B2388347
theorem B5737441 : Blo 1590994 5737441 := bstep (se 2 (by rfl) ⟨2151540, by rfl⟩ : syracuseStep 5737441 = 4303081) B4303081
theorem B1592411 : Blo 1590994 1592411 := bstep (se 1 (by rfl) ⟨1194308, by rfl⟩ : syracuseStep 1592411 = 2388617) B2388617
theorem B58059929 : Blo 1590994 58059929 := bstep (se 2 (by rfl) ⟨21772473, by rfl⟩ : syracuseStep 58059929 = 43544947) B43544947
theorem B1592551 : Blo 1590994 1592551 := bstep (se 1 (by rfl) ⟨1194413, by rfl⟩ : syracuseStep 1592551 = 2388827) B2388827
theorem B1592571 : Blo 1590994 1592571 := bstep (se 1 (by rfl) ⟨1194428, by rfl⟩ : syracuseStep 1592571 = 2388857) B2388857
theorem B63761735 : Blo 1590994 63761735 := bstep (se 1 (by rfl) ⟨47821301, by rfl⟩ : syracuseStep 63761735 = 95642603) B95642603
theorem B2387327 : Blo 1590994 2387327 := bstep (se 1 (by rfl) ⟨1790495, by rfl⟩ : syracuseStep 2387327 = 3580991) B3580991
theorem B10202561 : Blo 1590994 10202561 := bstep (se 2 (by rfl) ⟨3825960, by rfl⟩ : syracuseStep 10202561 = 7651921) B7651921
theorem B51621401 : Blo 1590994 51621401 := bstep (se 2 (by rfl) ⟨19358025, by rfl⟩ : syracuseStep 51621401 = 38716051) B38716051
theorem B20401793 : Blo 1590994 20401793 := bstep (se 2 (by rfl) ⟨7650672, by rfl⟩ : syracuseStep 20401793 = 15301345) B15301345
theorem B1592991 : Blo 1590994 1592991 := bstep (se 1 (by rfl) ⟨1194743, by rfl⟩ : syracuseStep 1592991 = 2389487) B2389487
theorem B2388203 : Blo 1590994 2388203 := bstep (se 1 (by rfl) ⟨1791152, by rfl⟩ : syracuseStep 2388203 = 3582305) B3582305
theorem B15306995 : Blo 1590994 15306995 := bstep (se 1 (by rfl) ⟨11480246, by rfl⟩ : syracuseStep 15306995 = 22960493) B22960493
theorem B2388263 : Blo 1590994 2388263 := bstep (se 1 (by rfl) ⟨1791197, by rfl⟩ : syracuseStep 2388263 = 3582395) B3582395
theorem B5370191 : Blo 1590994 5370191 := bstep (se 1 (by rfl) ⟨4027643, by rfl⟩ : syracuseStep 5370191 = 8055287) B8055287
theorem B5099897 : Blo 1590994 5099897 := bstep (se 2 (by rfl) ⟨1912461, by rfl⟩ : syracuseStep 5099897 = 3824923) B3824923
theorem B4534699 : Blo 1590994 4534699 := bstep (se 1 (by rfl) ⟨3401024, by rfl⟩ : syracuseStep 4534699 = 6802049) B6802049
theorem B26186273 : Blo 1590994 26186273 := bstep (se 2 (by rfl) ⟨9819852, by rfl⟩ : syracuseStep 26186273 = 19639705) B19639705
theorem B294203987 : Blo 1590994 294203987 := bstep (se 1 (by rfl) ⟨220652990, by rfl⟩ : syracuseStep 294203987 = 441305981) B441305981
theorem B11629165 : Blo 1590994 11629165 := bstep (se 3 (by rfl) ⟨2180468, by rfl⟩ : syracuseStep 11629165 = 4360937) B4360937
theorem B6042377 : Blo 1590994 6042377 := bstep (se 2 (by rfl) ⟨2265891, by rfl⟩ : syracuseStep 6042377 = 4531783) B4531783
theorem B2388791 : Blo 1590994 2388791 := bstep (se 1 (by rfl) ⟨1791593, by rfl⟩ : syracuseStep 2388791 = 3583187) B3583187
theorem B2388905 : Blo 1590994 2388905 := bstep (se 2 (by rfl) ⟨895839, by rfl⟩ : syracuseStep 2388905 = 1791679) B1791679
theorem B2388971 : Blo 1590994 2388971 := bstep (se 1 (by rfl) ⟨1791728, by rfl⟩ : syracuseStep 2388971 = 3583457) B3583457
theorem B1791067 : Blo 1590994 1791067 := bstep (se 1 (by rfl) ⟨1343300, by rfl⟩ : syracuseStep 1791067 = 2686601) B2686601
theorem B2389103 : Blo 1590994 2389103 := bstep (se 1 (by rfl) ⟨1791827, by rfl⟩ : syracuseStep 2389103 = 3583655) B3583655
theorem B9942335 : Blo 1590994 9942335 := bstep (se 1 (by rfl) ⟨7456751, by rfl⟩ : syracuseStep 9942335 = 14913503) B14913503
theorem B3823031 : Blo 1590994 3823031 := bstep (se 1 (by rfl) ⟨2867273, by rfl⟩ : syracuseStep 3823031 = 5734547) B5734547
theorem B21771767 : Blo 1590994 21771767 := bstep (se 1 (by rfl) ⟨16328825, by rfl⟩ : syracuseStep 21771767 = 32657651) B32657651
theorem B4028231 : Blo 1590994 4028231 := bstep (se 1 (by rfl) ⟨3021173, by rfl⟩ : syracuseStep 4028231 = 6042347) B6042347
theorem B2685001 : Blo 1590994 2685001 := bstep (se 2 (by rfl) ⟨1006875, by rfl⟩ : syracuseStep 2685001 = 2013751) B2013751
theorem B6043835 : Blo 1590994 6043835 := bstep (se 1 (by rfl) ⟨4532876, by rfl⟩ : syracuseStep 6043835 = 9065753) B9065753
theorem B5372135 : Blo 1590994 5372135 := bstep (se 1 (by rfl) ⟨4029101, by rfl⟩ : syracuseStep 5372135 = 8058203) B8058203
theorem B8059337 : Blo 1590994 8059337 := bstep (se 2 (by rfl) ⟨3022251, by rfl⟩ : syracuseStep 8059337 = 6044503) B6044503
theorem B2685433 : Blo 1590994 2685433 := bstep (se 2 (by rfl) ⟨1007037, by rfl⟩ : syracuseStep 2685433 = 2014075) B2014075
theorem B17218169 : Blo 1590994 17218169 := bstep (se 2 (by rfl) ⟨6456813, by rfl⟩ : syracuseStep 17218169 = 12913627) B12913627
theorem B9067211 : Blo 1590994 9067211 := bstep (se 1 (by rfl) ⟨6800408, by rfl⟩ : syracuseStep 9067211 = 13600817) B13600817
theorem B2686007 : Blo 1590994 2686007 := bstep (se 1 (by rfl) ⟨2014505, by rfl⟩ : syracuseStep 2686007 = 4029011) B4029011
theorem B5373431 : Blo 1590994 5373431 := bstep (se 1 (by rfl) ⟨4030073, by rfl⟩ : syracuseStep 5373431 = 8060147) B8060147
theorem B2686567 : Blo 1590994 2686567 := bstep (se 1 (by rfl) ⟨2014925, by rfl⟩ : syracuseStep 2686567 = 4029851) B4029851
theorem B4030175 : Blo 1590994 4030175 := bstep (se 1 (by rfl) ⟨3022631, by rfl⟩ : syracuseStep 4030175 = 6045263) B6045263
theorem B20389643 : Blo 1590994 20389643 := bstep (se 1 (by rfl) ⟨15292232, by rfl⟩ : syracuseStep 20389643 = 30584465) B30584465
theorem B69771095 : Blo 1590994 69771095 := bstep (se 1 (by rfl) ⟨52328321, by rfl⟩ : syracuseStep 69771095 = 104656643) B104656643
theorem B6799247 : Blo 1590994 6799247 := bstep (se 1 (by rfl) ⟨5099435, by rfl⟩ : syracuseStep 6799247 = 10198871) B10198871
theorem B4030519 : Blo 1590994 4030519 := bstep (se 1 (by rfl) ⟨3022889, by rfl⟩ : syracuseStep 4030519 = 6045779) B6045779
theorem B3580001 : Blo 1590994 3580001 := bstep (se 2 (by rfl) ⟨1342500, by rfl⟩ : syracuseStep 3580001 = 2685001) B2685001
theorem B3580127 : Blo 1590994 3580127 := bstep (se 1 (by rfl) ⟨2685095, by rfl⟩ : syracuseStep 3580127 = 5370191) B5370191
theorem B3399931 : Blo 1590994 3399931 := bstep (se 1 (by rfl) ⟨2549948, by rfl⟩ : syracuseStep 3399931 = 5099897) B5099897
theorem B6045947 : Blo 1590994 6045947 := bstep (se 1 (by rfl) ⟨4534460, by rfl⟩ : syracuseStep 6045947 = 9068921) B9068921
theorem B12091679 : Blo 1590994 12091679 := bstep (se 1 (by rfl) ⟨9068759, by rfl⟩ : syracuseStep 12091679 = 18137519) B18137519
theorem B17457515 : Blo 1590994 17457515 := bstep (se 1 (by rfl) ⟨13093136, by rfl⟩ : syracuseStep 17457515 = 26186273) B26186273
theorem B27951479 : Blo 1590994 27951479 := bstep (se 1 (by rfl) ⟨20963609, by rfl⟩ : syracuseStep 27951479 = 41927219) B41927219
theorem B6046265 : Blo 1590994 6046265 := bstep (se 2 (by rfl) ⟨2267349, by rfl⟩ : syracuseStep 6046265 = 4534699) B4534699
theorem B3580577 : Blo 1590994 3580577 := bstep (se 2 (by rfl) ⟨1342716, by rfl⟩ : syracuseStep 3580577 = 2685433) B2685433
theorem B6628223 : Blo 1590994 6628223 := bstep (se 1 (by rfl) ⟨4971167, by rfl⟩ : syracuseStep 6628223 = 9942335) B9942335
theorem B2548687 : Blo 1590994 2548687 := bstep (se 1 (by rfl) ⟨1911515, by rfl⟩ : syracuseStep 2548687 = 3823031) B3823031
theorem B8061929 : Blo 1590994 8061929 := bstep (se 2 (by rfl) ⟨3023223, by rfl⟩ : syracuseStep 8061929 = 6046447) B6046447
theorem B5375105 : Blo 1590994 5375105 := bstep (se 2 (by rfl) ⟨2015664, by rfl⟩ : syracuseStep 5375105 = 4031329) B4031329
theorem B27215027 : Blo 1590994 27215027 := bstep (se 1 (by rfl) ⟨20411270, by rfl⟩ : syracuseStep 27215027 = 40822541) B40822541
theorem B3581423 : Blo 1590994 3581423 := bstep (se 1 (by rfl) ⟨2686067, by rfl⟩ : syracuseStep 3581423 = 5372135) B5372135
theorem B11478779 : Blo 1590994 11478779 := bstep (se 1 (by rfl) ⟨8609084, by rfl⟩ : syracuseStep 11478779 = 17218169) B17218169
theorem B15304535 : Blo 1590994 15304535 := bstep (se 1 (by rfl) ⟨11478401, by rfl⟩ : syracuseStep 15304535 = 22956803) B22956803
theorem B1591151 : Blo 1590994 1591151 := bstep (se 1 (by rfl) ⟨1193363, by rfl⟩ : syracuseStep 1591151 = 2386727) B2386727
theorem B3582089 : Blo 1590994 3582089 := bstep (se 2 (by rfl) ⟨1343283, by rfl⟩ : syracuseStep 3582089 = 2686567) B2686567
theorem B1591551 : Blo 1590994 1591551 := bstep (se 1 (by rfl) ⟨1193663, by rfl⟩ : syracuseStep 1591551 = 2387327) B2387327
theorem B6801707 : Blo 1590994 6801707 := bstep (se 1 (by rfl) ⟨5101280, by rfl⟩ : syracuseStep 6801707 = 10202561) B10202561
theorem B3582287 : Blo 1590994 3582287 := bstep (se 1 (by rfl) ⟨2686715, by rfl⟩ : syracuseStep 3582287 = 5373431) B5373431
theorem B13601195 : Blo 1590994 13601195 := bstep (se 1 (by rfl) ⟨10200896, by rfl⟩ : syracuseStep 13601195 = 20401793) B20401793
theorem B13593095 : Blo 1590994 13593095 := bstep (se 1 (by rfl) ⟨10194821, by rfl⟩ : syracuseStep 13593095 = 20389643) B20389643
theorem B4532831 : Blo 1590994 4532831 := bstep (se 1 (by rfl) ⟨3399623, by rfl⟩ : syracuseStep 4532831 = 6799247) B6799247
theorem B1592135 : Blo 1590994 1592135 := bstep (se 1 (by rfl) ⟨1194101, by rfl⟩ : syracuseStep 1592135 = 2388203) B2388203
theorem B2386799 : Blo 1590994 2386799 := bstep (se 1 (by rfl) ⟨1790099, by rfl⟩ : syracuseStep 2386799 = 3580199) B3580199
theorem B1592175 : Blo 1590994 1592175 := bstep (se 1 (by rfl) ⟨1194131, by rfl⟩ : syracuseStep 1592175 = 2388263) B2388263
theorem B196135991 : Blo 1590994 196135991 := bstep (se 1 (by rfl) ⟨147101993, by rfl⟩ : syracuseStep 196135991 = 294203987) B294203987
theorem B2387039 : Blo 1590994 2387039 := bstep (se 1 (by rfl) ⟨1790279, by rfl⟩ : syracuseStep 2387039 = 3580559) B3580559
theorem B93088925 : Blo 1590994 93088925 := bstep (se 3 (by rfl) ⟨17454173, by rfl⟩ : syracuseStep 93088925 = 34908347) B34908347
theorem B1912015 : Blo 1590994 1912015 := bstep (se 1 (by rfl) ⟨1434011, by rfl⟩ : syracuseStep 1912015 = 2868023) B2868023
theorem B1592527 : Blo 1590994 1592527 := bstep (se 1 (by rfl) ⟨1194395, by rfl⟩ : syracuseStep 1592527 = 2388791) B2388791
theorem B1592603 : Blo 1590994 1592603 := bstep (se 1 (by rfl) ⟨1194452, by rfl⟩ : syracuseStep 1592603 = 2388905) B2388905
theorem B1592647 : Blo 1590994 1592647 := bstep (se 1 (by rfl) ⟨1194485, by rfl⟩ : syracuseStep 1592647 = 2388971) B2388971
theorem B1592735 : Blo 1590994 1592735 := bstep (se 1 (by rfl) ⟨1194551, by rfl⟩ : syracuseStep 1592735 = 2389103) B2389103
theorem B3583439 : Blo 1590994 3583439 := bstep (se 1 (by rfl) ⟨2687579, by rfl⟩ : syracuseStep 3583439 = 5375159) B5375159
theorem B2387483 : Blo 1590994 2387483 := bstep (se 1 (by rfl) ⟨1790612, by rfl⟩ : syracuseStep 2387483 = 3581225) B3581225
theorem B12095081 : Blo 1590994 12095081 := bstep (se 2 (by rfl) ⟨4535655, by rfl⟩ : syracuseStep 12095081 = 9071311) B9071311
theorem B4419517 : Blo 1590994 4419517 := bstep (se 3 (by rfl) ⟨828659, by rfl⟩ : syracuseStep 4419517 = 1657319) B1657319
theorem B2388089 : Blo 1590994 2388089 := bstep (se 2 (by rfl) ⟨895533, by rfl⟩ : syracuseStep 2388089 = 1791067) B1791067
theorem B11481227 : Blo 1590994 11481227 := bstep (se 1 (by rfl) ⟨8610920, by rfl⟩ : syracuseStep 11481227 = 17221841) B17221841
theorem B39268739 : Blo 1590994 39268739 := bstep (se 1 (by rfl) ⟨29451554, by rfl⟩ : syracuseStep 39268739 = 58903109) B58903109
theorem B2388383 : Blo 1590994 2388383 := bstep (se 1 (by rfl) ⟨1791287, by rfl⟩ : syracuseStep 2388383 = 3582575) B3582575
theorem B1790671 : Blo 1590994 1790671 := bstep (se 1 (by rfl) ⟨1343003, by rfl⟩ : syracuseStep 1790671 = 2686007) B2686007
theorem B6042833 : Blo 1590994 6042833 := bstep (se 2 (by rfl) ⟨2266062, by rfl⟩ : syracuseStep 6042833 = 4532125) B4532125
theorem B10204663 : Blo 1590994 10204663 := bstep (se 1 (by rfl) ⟨7653497, by rfl⟩ : syracuseStep 10204663 = 15306995) B15306995
theorem B4535929 : Blo 1590994 4535929 := bstep (se 2 (by rfl) ⟨1700973, by rfl⟩ : syracuseStep 4535929 = 3401947) B3401947
theorem B154826477 : Blo 1590994 154826477 := bstep (se 3 (by rfl) ⟨29029964, by rfl⟩ : syracuseStep 154826477 = 58059929) B58059929
theorem B4028251 : Blo 1590994 4028251 := bstep (se 1 (by rfl) ⟨3021188, by rfl⟩ : syracuseStep 4028251 = 6042377) B6042377
theorem B1791967 : Blo 1590994 1791967 := bstep (se 1 (by rfl) ⟨1343975, by rfl⟩ : syracuseStep 1791967 = 2687951) B2687951
theorem B1792111 : Blo 1590994 1792111 := bstep (se 1 (by rfl) ⟨1344083, by rfl⟩ : syracuseStep 1792111 = 2688167) B2688167
theorem B15505553 : Blo 1590994 15505553 := bstep (se 2 (by rfl) ⟨5814582, by rfl⟩ : syracuseStep 15505553 = 11629165) B11629165
theorem B14514511 : Blo 1590994 14514511 := bstep (se 1 (by rfl) ⟨10885883, by rfl⟩ : syracuseStep 14514511 = 21771767) B21771767
theorem B3021295 : Blo 1590994 3021295 := bstep (se 1 (by rfl) ⟨2265971, by rfl⟩ : syracuseStep 3021295 = 4531943) B4531943
theorem B116136467 : Blo 1590994 116136467 := bstep (se 1 (by rfl) ⟨87102350, by rfl⟩ : syracuseStep 116136467 = 174204701) B174204701
theorem B2685487 : Blo 1590994 2685487 := bstep (se 1 (by rfl) ⟨2014115, by rfl⟩ : syracuseStep 2685487 = 4028231) B4028231
theorem B7649921 : Blo 1590994 7649921 := bstep (se 2 (by rfl) ⟨2868720, by rfl⟩ : syracuseStep 7649921 = 5737441) B5737441
theorem B51632815 : Blo 1590994 51632815 := bstep (se 1 (by rfl) ⟨38724611, by rfl⟩ : syracuseStep 51632815 = 77449223) B77449223
theorem B124148467 : Blo 1590994 124148467 := bstep (se 1 (by rfl) ⟨93111350, by rfl⟩ : syracuseStep 124148467 = 186222701) B186222701
theorem B4029223 : Blo 1590994 4029223 := bstep (se 1 (by rfl) ⟨3021917, by rfl⟩ : syracuseStep 4029223 = 6043835) B6043835
theorem B5372891 : Blo 1590994 5372891 := bstep (se 1 (by rfl) ⟨4029668, by rfl⟩ : syracuseStep 5372891 = 8059337) B8059337
theorem B6044807 : Blo 1590994 6044807 := bstep (se 1 (by rfl) ⟨4533605, by rfl⟩ : syracuseStep 6044807 = 9067211) B9067211
theorem B42507823 : Blo 1590994 42507823 := bstep (se 1 (by rfl) ⟨31880867, by rfl⟩ : syracuseStep 42507823 = 63761735) B63761735
theorem B6798973 : Blo 1590994 6798973 := bstep (se 3 (by rfl) ⟨1274807, by rfl⟩ : syracuseStep 6798973 = 2549615) B2549615
theorem B34414267 : Blo 1590994 34414267 := bstep (se 1 (by rfl) ⟨25810700, by rfl⟩ : syracuseStep 34414267 = 51621401) B51621401
theorem B2686783 : Blo 1590994 2686783 := bstep (se 1 (by rfl) ⟨2015087, by rfl⟩ : syracuseStep 2686783 = 4030175) B4030175
theorem B46514063 : Blo 1590994 46514063 := bstep (se 1 (by rfl) ⟨34885547, by rfl⟩ : syracuseStep 46514063 = 69771095) B69771095
theorem B5374025 : Blo 1590994 5374025 := bstep (se 2 (by rfl) ⟨2015259, by rfl⟩ : syracuseStep 5374025 = 4030519) B4030519
theorem B4030631 : Blo 1590994 4030631 := bstep (se 1 (by rfl) ⟨3022973, by rfl⟩ : syracuseStep 4030631 = 6045947) B6045947
theorem B8061119 : Blo 1590994 8061119 := bstep (se 1 (by rfl) ⟨6045839, by rfl⟩ : syracuseStep 8061119 = 12091679) B12091679
theorem B4030843 : Blo 1590994 4030843 := bstep (se 1 (by rfl) ⟨3023132, by rfl⟩ : syracuseStep 4030843 = 6046265) B6046265
theorem B5374619 : Blo 1590994 5374619 := bstep (se 1 (by rfl) ⟨4030964, by rfl⟩ : syracuseStep 5374619 = 8061929) B8061929
theorem B3580649 : Blo 1590994 3580649 := bstep (se 2 (by rfl) ⟨1342743, by rfl⟩ : syracuseStep 3580649 = 2685487) B2685487
theorem B7652519 : Blo 1590994 7652519 := bstep (se 1 (by rfl) ⟨5739389, by rfl⟩ : syracuseStep 7652519 = 11478779) B11478779
theorem B20399789 : Blo 1590994 20399789 := bstep (se 3 (by rfl) ⟨3824960, by rfl⟩ : syracuseStep 20399789 = 7649921) B7649921
theorem B9062063 : Blo 1590994 9062063 := bstep (se 1 (by rfl) ⟨6796547, by rfl⟩ : syracuseStep 9062063 = 13593095) B13593095
theorem B77424311 : Blo 1590994 77424311 := bstep (se 1 (by rfl) ⟨58068233, by rfl⟩ : syracuseStep 77424311 = 116136467) B116136467
theorem B1591199 : Blo 1590994 1591199 := bstep (se 1 (by rfl) ⟨1193399, by rfl⟩ : syracuseStep 1591199 = 2386799) B2386799
theorem B3581927 : Blo 1590994 3581927 := bstep (se 1 (by rfl) ⟨2686445, by rfl⟩ : syracuseStep 3581927 = 5372891) B5372891
theorem B1591359 : Blo 1590994 1591359 := bstep (se 1 (by rfl) ⟨1193519, by rfl⟩ : syracuseStep 1591359 = 2387039) B2387039
theorem B6047905 : Blo 1590994 6047905 := bstep (se 2 (by rfl) ⟨2267964, by rfl⟩ : syracuseStep 6047905 = 4535929) B4535929
theorem B45885689 : Blo 1590994 45885689 := bstep (se 2 (by rfl) ⟨17207133, by rfl⟩ : syracuseStep 45885689 = 34414267) B34414267
theorem B1591655 : Blo 1590994 1591655 := bstep (se 1 (by rfl) ⟨1193741, by rfl⟩ : syracuseStep 1591655 = 2387483) B2387483
theorem B8063387 : Blo 1590994 8063387 := bstep (se 1 (by rfl) ⟨6047540, by rfl⟩ : syracuseStep 8063387 = 12095081) B12095081
theorem B3582377 : Blo 1590994 3582377 := bstep (se 2 (by rfl) ⟨1343391, by rfl⟩ : syracuseStep 3582377 = 2686783) B2686783
theorem B5892689 : Blo 1590994 5892689 := bstep (se 2 (by rfl) ⟨2209758, by rfl⟩ : syracuseStep 5892689 = 4419517) B4419517
theorem B31009375 : Blo 1590994 31009375 := bstep (se 1 (by rfl) ⟨23257031, by rfl⟩ : syracuseStep 31009375 = 46514063) B46514063
theorem B2386667 : Blo 1590994 2386667 := bstep (se 1 (by rfl) ⟨1790000, by rfl⟩ : syracuseStep 2386667 = 3580001) B3580001
theorem B1592059 : Blo 1590994 1592059 := bstep (se 1 (by rfl) ⟨1194044, by rfl⟩ : syracuseStep 1592059 = 2388089) B2388089
theorem B7654151 : Blo 1590994 7654151 := bstep (se 1 (by rfl) ⟨5740613, by rfl⟩ : syracuseStep 7654151 = 11481227) B11481227
theorem B2386751 : Blo 1590994 2386751 := bstep (se 1 (by rfl) ⟨1790063, by rfl⟩ : syracuseStep 2386751 = 3580127) B3580127
theorem B1592255 : Blo 1590994 1592255 := bstep (se 1 (by rfl) ⟨1194191, by rfl⟩ : syracuseStep 1592255 = 2388383) B2388383
theorem B4533241 : Blo 1590994 4533241 := bstep (se 2 (by rfl) ⟨1699965, by rfl⟩ : syracuseStep 4533241 = 3399931) B3399931
theorem B41348141 : Blo 1590994 41348141 := bstep (se 3 (by rfl) ⟨7752776, by rfl⟩ : syracuseStep 41348141 = 15505553) B15505553
theorem B19352681 : Blo 1590994 19352681 := bstep (se 2 (by rfl) ⟨7257255, by rfl⟩ : syracuseStep 19352681 = 14514511) B14514511
theorem B2387051 : Blo 1590994 2387051 := bstep (se 1 (by rfl) ⟨1790288, by rfl⟩ : syracuseStep 2387051 = 3580577) B3580577
theorem B4418815 : Blo 1590994 4418815 := bstep (se 1 (by rfl) ⟨3314111, by rfl⟩ : syracuseStep 4418815 = 6628223) B6628223
theorem B3583403 : Blo 1590994 3583403 := bstep (se 1 (by rfl) ⟨2687552, by rfl⟩ : syracuseStep 3583403 = 5375105) B5375105
theorem B2387561 : Blo 1590994 2387561 := bstep (se 2 (by rfl) ⟨895335, by rfl⟩ : syracuseStep 2387561 = 1790671) B1790671
theorem B165531289 : Blo 1590994 165531289 := bstep (se 2 (by rfl) ⟨62074233, by rfl⟩ : syracuseStep 165531289 = 124148467) B124148467
theorem B2387615 : Blo 1590994 2387615 := bstep (se 1 (by rfl) ⟨1790711, by rfl⟩ : syracuseStep 2387615 = 3581423) B3581423
theorem B10203023 : Blo 1590994 10203023 := bstep (se 1 (by rfl) ⟨7652267, by rfl⟩ : syracuseStep 10203023 = 15304535) B15304535
theorem B2388059 : Blo 1590994 2388059 := bstep (se 1 (by rfl) ⟨1791044, by rfl⟩ : syracuseStep 2388059 = 3582089) B3582089
theorem B4534471 : Blo 1590994 4534471 := bstep (se 1 (by rfl) ⟨3400853, by rfl⟩ : syracuseStep 4534471 = 6801707) B6801707
theorem B2388191 : Blo 1590994 2388191 := bstep (se 1 (by rfl) ⟨1791143, by rfl⟩ : syracuseStep 2388191 = 3582287) B3582287
theorem B130757327 : Blo 1590994 130757327 := bstep (se 1 (by rfl) ⟨98067995, by rfl⟩ : syracuseStep 130757327 = 196135991) B196135991
theorem B56677097 : Blo 1590994 56677097 := bstep (se 2 (by rfl) ⟨21253911, by rfl⟩ : syracuseStep 56677097 = 42507823) B42507823
theorem B62059283 : Blo 1590994 62059283 := bstep (se 1 (by rfl) ⟨46544462, by rfl⟩ : syracuseStep 62059283 = 93088925) B93088925
theorem B9065297 : Blo 1590994 9065297 := bstep (se 2 (by rfl) ⟨3399486, by rfl⟩ : syracuseStep 9065297 = 6798973) B6798973
theorem B2388959 : Blo 1590994 2388959 := bstep (se 1 (by rfl) ⟨1791719, by rfl⟩ : syracuseStep 2388959 = 3583439) B3583439
theorem B5371001 : Blo 1590994 5371001 := bstep (se 2 (by rfl) ⟨2014125, by rfl⟩ : syracuseStep 5371001 = 4028251) B4028251
theorem B2389289 : Blo 1590994 2389289 := bstep (se 2 (by rfl) ⟨895983, by rfl⟩ : syracuseStep 2389289 = 1791967) B1791967
theorem B2389481 : Blo 1590994 2389481 := bstep (se 2 (by rfl) ⟨896055, by rfl⟩ : syracuseStep 2389481 = 1792111) B1792111
theorem B11638343 : Blo 1590994 11638343 := bstep (se 1 (by rfl) ⟨8728757, by rfl⟩ : syracuseStep 11638343 = 17457515) B17457515
theorem B18634319 : Blo 1590994 18634319 := bstep (se 1 (by rfl) ⟨13975739, by rfl⟩ : syracuseStep 18634319 = 27951479) B27951479
theorem B4028393 : Blo 1590994 4028393 := bstep (se 2 (by rfl) ⟨1510647, by rfl⟩ : syracuseStep 4028393 = 3021295) B3021295
theorem B18143351 : Blo 1590994 18143351 := bstep (se 1 (by rfl) ⟨13607513, by rfl⟩ : syracuseStep 18143351 = 27215027) B27215027
theorem B4028555 : Blo 1590994 4028555 := bstep (se 1 (by rfl) ⟨3021416, by rfl⟩ : syracuseStep 4028555 = 6042833) B6042833
theorem B68843753 : Blo 1590994 68843753 := bstep (se 2 (by rfl) ⟨25816407, by rfl⟩ : syracuseStep 68843753 = 51632815) B51632815
theorem B104716637 : Blo 1590994 104716637 := bstep (se 3 (by rfl) ⟨19634369, by rfl⟩ : syracuseStep 104716637 = 39268739) B39268739
theorem B5372297 : Blo 1590994 5372297 := bstep (se 2 (by rfl) ⟨2014611, by rfl⟩ : syracuseStep 5372297 = 4029223) B4029223
theorem B10197413 : Blo 1590994 10197413 := bstep (se 4 (by rfl) ⟨956007, by rfl⟩ : syracuseStep 10197413 = 1912015) B1912015
theorem B103217651 : Blo 1590994 103217651 := bstep (se 1 (by rfl) ⟨77413238, by rfl⟩ : syracuseStep 103217651 = 154826477) B154826477
theorem B3398249 : Blo 1590994 3398249 := bstep (se 2 (by rfl) ⟨1274343, by rfl⟩ : syracuseStep 3398249 = 2548687) B2548687
theorem B9067463 : Blo 1590994 9067463 := bstep (se 1 (by rfl) ⟨6800597, by rfl⟩ : syracuseStep 9067463 = 13601195) B13601195
theorem B3021887 : Blo 1590994 3021887 := bstep (se 1 (by rfl) ⟨2266415, by rfl⟩ : syracuseStep 3021887 = 4532831) B4532831
theorem B13606217 : Blo 1590994 13606217 := bstep (se 2 (by rfl) ⟨5102331, by rfl⟩ : syracuseStep 13606217 = 10204663) B10204663
theorem B4029871 : Blo 1590994 4029871 := bstep (se 1 (by rfl) ⟨3022403, by rfl⟩ : syracuseStep 4029871 = 6044807) B6044807
theorem B2687087 : Blo 1590994 2687087 := bstep (se 1 (by rfl) ⟨2015315, by rfl⟩ : syracuseStep 2687087 = 4030631) B4030631
theorem B5374079 : Blo 1590994 5374079 := bstep (se 1 (by rfl) ⟨4030559, by rfl⟩ : syracuseStep 5374079 = 8061119) B8061119
theorem B6045961 : Blo 1590994 6045961 := bstep (se 2 (by rfl) ⟨2267235, by rfl⟩ : syracuseStep 6045961 = 4534471) B4534471
theorem B87171551 : Blo 1590994 87171551 := bstep (se 1 (by rfl) ⟨65378663, by rfl⟩ : syracuseStep 87171551 = 130757327) B130757327
theorem B5374457 : Blo 1590994 5374457 := bstep (se 2 (by rfl) ⟨2015421, by rfl⟩ : syracuseStep 5374457 = 4030843) B4030843
theorem B3580667 : Blo 1590994 3580667 := bstep (se 1 (by rfl) ⟨2685500, by rfl⟩ : syracuseStep 3580667 = 5371001) B5371001
theorem B13599859 : Blo 1590994 13599859 := bstep (se 1 (by rfl) ⟨10199894, by rfl⟩ : syracuseStep 13599859 = 20399789) B20399789
theorem B30590459 : Blo 1590994 30590459 := bstep (se 1 (by rfl) ⟨22942844, by rfl⟩ : syracuseStep 30590459 = 45885689) B45885689
theorem B15713837 : Blo 1590994 15713837 := bstep (se 3 (by rfl) ⟨2946344, by rfl⟩ : syracuseStep 15713837 = 5892689) B5892689
theorem B3581531 : Blo 1590994 3581531 := bstep (se 1 (by rfl) ⟨2686148, by rfl⟩ : syracuseStep 3581531 = 5372297) B5372297
theorem B5375591 : Blo 1590994 5375591 := bstep (se 1 (by rfl) ⟨4031693, by rfl⟩ : syracuseStep 5375591 = 8063387) B8063387
theorem B5891753 : Blo 1590994 5891753 := bstep (se 2 (by rfl) ⟨2209407, by rfl⟩ : syracuseStep 5891753 = 4418815) B4418815
theorem B1591111 : Blo 1590994 1591111 := bstep (se 1 (by rfl) ⟨1193333, by rfl⟩ : syracuseStep 1591111 = 2386667) B2386667
theorem B1591167 : Blo 1590994 1591167 := bstep (se 1 (by rfl) ⟨1193375, by rfl⟩ : syracuseStep 1591167 = 2386751) B2386751
theorem B1591367 : Blo 1590994 1591367 := bstep (se 1 (by rfl) ⟨1193525, by rfl⟩ : syracuseStep 1591367 = 2387051) B2387051
theorem B9070811 : Blo 1590994 9070811 := bstep (se 1 (by rfl) ⟨6803108, by rfl⟩ : syracuseStep 9070811 = 13606217) B13606217
theorem B1591707 : Blo 1590994 1591707 := bstep (se 1 (by rfl) ⟨1193780, by rfl⟩ : syracuseStep 1591707 = 2387561) B2387561
theorem B1591743 : Blo 1590994 1591743 := bstep (se 1 (by rfl) ⟨1193807, by rfl⟩ : syracuseStep 1591743 = 2387615) B2387615
theorem B6802015 : Blo 1590994 6802015 := bstep (se 1 (by rfl) ⟨5101511, by rfl⟩ : syracuseStep 6802015 = 10203023) B10203023
theorem B3582683 : Blo 1590994 3582683 := bstep (se 1 (by rfl) ⟨2687012, by rfl⟩ : syracuseStep 3582683 = 5374025) B5374025
theorem B1592039 : Blo 1590994 1592039 := bstep (se 1 (by rfl) ⟨1194029, by rfl⟩ : syracuseStep 1592039 = 2388059) B2388059
theorem B1592127 : Blo 1590994 1592127 := bstep (se 1 (by rfl) ⟨1194095, by rfl⟩ : syracuseStep 1592127 = 2388191) B2388191
theorem B8063873 : Blo 1590994 8063873 := bstep (se 2 (by rfl) ⟨3023952, by rfl⟩ : syracuseStep 8063873 = 6047905) B6047905
theorem B3583079 : Blo 1590994 3583079 := bstep (se 1 (by rfl) ⟨2687309, by rfl⟩ : syracuseStep 3583079 = 5374619) B5374619
theorem B2387099 : Blo 1590994 2387099 := bstep (se 1 (by rfl) ⟨1790324, by rfl⟩ : syracuseStep 2387099 = 3580649) B3580649
theorem B37784731 : Blo 1590994 37784731 := bstep (se 1 (by rfl) ⟨28338548, by rfl⟩ : syracuseStep 37784731 = 56677097) B56677097
theorem B165383333 : Blo 1590994 165383333 := bstep (se 4 (by rfl) ⟨15504687, by rfl⟩ : syracuseStep 165383333 = 31009375) B31009375
theorem B41372855 : Blo 1590994 41372855 := bstep (se 1 (by rfl) ⟨31029641, by rfl⟩ : syracuseStep 41372855 = 62059283) B62059283
theorem B1592639 : Blo 1590994 1592639 := bstep (se 1 (by rfl) ⟨1194479, by rfl⟩ : syracuseStep 1592639 = 2388959) B2388959
theorem B1592859 : Blo 1590994 1592859 := bstep (se 1 (by rfl) ⟨1194644, by rfl⟩ : syracuseStep 1592859 = 2389289) B2389289
theorem B1592987 : Blo 1590994 1592987 := bstep (se 1 (by rfl) ⟨1194740, by rfl⟩ : syracuseStep 1592987 = 2389481) B2389481
theorem B12422879 : Blo 1590994 12422879 := bstep (se 1 (by rfl) ⟨9317159, by rfl⟩ : syracuseStep 12422879 = 18634319) B18634319
theorem B6041375 : Blo 1590994 6041375 := bstep (se 1 (by rfl) ⟨4531031, by rfl⟩ : syracuseStep 6041375 = 9062063) B9062063
theorem B2387951 : Blo 1590994 2387951 := bstep (se 1 (by rfl) ⟨1790963, by rfl⟩ : syracuseStep 2387951 = 3581927) B3581927
theorem B12095567 : Blo 1590994 12095567 := bstep (se 1 (by rfl) ⟨9071675, by rfl⟩ : syracuseStep 12095567 = 18143351) B18143351
theorem B45895835 : Blo 1590994 45895835 := bstep (se 1 (by rfl) ⟨34421876, by rfl⟩ : syracuseStep 45895835 = 68843753) B68843753
theorem B31035581 : Blo 1590994 31035581 := bstep (se 3 (by rfl) ⟨5819171, by rfl⟩ : syracuseStep 31035581 = 11638343) B11638343
theorem B2388251 : Blo 1590994 2388251 := bstep (se 1 (by rfl) ⟨1791188, by rfl⟩ : syracuseStep 2388251 = 3582377) B3582377
theorem B2265499 : Blo 1590994 2265499 := bstep (se 1 (by rfl) ⟨1699124, by rfl⟩ : syracuseStep 2265499 = 3398249) B3398249
theorem B2388935 : Blo 1590994 2388935 := bstep (se 1 (by rfl) ⟨1791701, by rfl⟩ : syracuseStep 2388935 = 3583403) B3583403
theorem B8058365 : Blo 1590994 8058365 := bstep (se 3 (by rfl) ⟨1510943, by rfl⟩ : syracuseStep 8058365 = 3021887) B3021887
theorem B6043531 : Blo 1590994 6043531 := bstep (se 1 (by rfl) ⟨4532648, by rfl⟩ : syracuseStep 6043531 = 9065297) B9065297
theorem B5101679 : Blo 1590994 5101679 := bstep (se 1 (by rfl) ⟨3826259, by rfl⟩ : syracuseStep 5101679 = 7652519) B7652519
theorem B51616207 : Blo 1590994 51616207 := bstep (se 1 (by rfl) ⟨38712155, by rfl⟩ : syracuseStep 51616207 = 77424311) B77424311
theorem B2685595 : Blo 1590994 2685595 := bstep (se 1 (by rfl) ⟨2014196, by rfl⟩ : syracuseStep 2685595 = 4028393) B4028393
theorem B6044321 : Blo 1590994 6044321 := bstep (se 2 (by rfl) ⟨2266620, by rfl⟩ : syracuseStep 6044321 = 4533241) B4533241
theorem B2685703 : Blo 1590994 2685703 := bstep (se 1 (by rfl) ⟨2014277, by rfl⟩ : syracuseStep 2685703 = 4028555) B4028555
theorem B69811091 : Blo 1590994 69811091 := bstep (se 1 (by rfl) ⟨52358318, by rfl⟩ : syracuseStep 69811091 = 104716637) B104716637
theorem B6798275 : Blo 1590994 6798275 := bstep (se 1 (by rfl) ⟨5098706, by rfl⟩ : syracuseStep 6798275 = 10197413) B10197413
theorem B68811767 : Blo 1590994 68811767 := bstep (se 1 (by rfl) ⟨51608825, by rfl⟩ : syracuseStep 68811767 = 103217651) B103217651
theorem B5102767 : Blo 1590994 5102767 := bstep (se 1 (by rfl) ⟨3827075, by rfl⟩ : syracuseStep 5102767 = 7654151) B7654151
theorem B5373161 : Blo 1590994 5373161 := bstep (se 2 (by rfl) ⟨2014935, by rfl⟩ : syracuseStep 5373161 = 4029871) B4029871
theorem B6044975 : Blo 1590994 6044975 := bstep (se 1 (by rfl) ⟨4533731, by rfl⟩ : syracuseStep 6044975 = 9067463) B9067463
theorem B27565427 : Blo 1590994 27565427 := bstep (se 1 (by rfl) ⟨20674070, by rfl⟩ : syracuseStep 27565427 = 41348141) B41348141
theorem B12901787 : Blo 1590994 12901787 := bstep (se 1 (by rfl) ⟨9676340, by rfl⟩ : syracuseStep 12901787 = 19352681) B19352681
theorem B220708385 : Blo 1590994 220708385 := bstep (se 2 (by rfl) ⟨82765644, by rfl⟩ : syracuseStep 220708385 = 165531289) B165531289
theorem B30597223 : Blo 1590994 30597223 := bstep (se 1 (by rfl) ⟨22947917, by rfl⟩ : syracuseStep 30597223 = 45895835) B45895835
theorem B58114367 : Blo 1590994 58114367 := bstep (se 1 (by rfl) ⟨43585775, by rfl⟩ : syracuseStep 58114367 = 87171551) B87171551
theorem B8061281 : Blo 1590994 8061281 := bstep (se 2 (by rfl) ⟨3022980, by rfl⟩ : syracuseStep 8061281 = 6045961) B6045961
theorem B68821609 : Blo 1590994 68821609 := bstep (se 2 (by rfl) ⟨25808103, by rfl⟩ : syracuseStep 68821609 = 51616207) B51616207
theorem B9069353 : Blo 1590994 9069353 := bstep (se 2 (by rfl) ⟨3401007, by rfl⟩ : syracuseStep 9069353 = 6802015) B6802015
theorem B3580793 : Blo 1590994 3580793 := bstep (se 2 (by rfl) ⟨1342797, by rfl⟩ : syracuseStep 3580793 = 2685595) B2685595
theorem B3580937 : Blo 1590994 3580937 := bstep (se 2 (by rfl) ⟨1342851, by rfl⟩ : syracuseStep 3580937 = 2685703) B2685703
theorem B3401119 : Blo 1590994 3401119 := bstep (se 1 (by rfl) ⟨2550839, by rfl⟩ : syracuseStep 3401119 = 5101679) B5101679
theorem B6047207 : Blo 1590994 6047207 := bstep (se 1 (by rfl) ⟨4535405, by rfl⟩ : syracuseStep 6047207 = 9070811) B9070811
theorem B5375915 : Blo 1590994 5375915 := bstep (se 1 (by rfl) ⟨4031936, by rfl⟩ : syracuseStep 5375915 = 8063873) B8063873
theorem B46540727 : Blo 1590994 46540727 := bstep (se 1 (by rfl) ⟨34905545, by rfl⟩ : syracuseStep 46540727 = 69811091) B69811091
theorem B4532183 : Blo 1590994 4532183 := bstep (se 1 (by rfl) ⟨3399137, by rfl⟩ : syracuseStep 4532183 = 6798275) B6798275
theorem B1591399 : Blo 1590994 1591399 := bstep (se 1 (by rfl) ⟨1193549, by rfl⟩ : syracuseStep 1591399 = 2387099) B2387099
theorem B3582107 : Blo 1590994 3582107 := bstep (se 1 (by rfl) ⟨2686580, by rfl⟩ : syracuseStep 3582107 = 5373161) B5373161
theorem B18376951 : Blo 1590994 18376951 := bstep (se 1 (by rfl) ⟨13782713, by rfl⟩ : syracuseStep 18376951 = 27565427) B27565427
theorem B147138923 : Blo 1590994 147138923 := bstep (se 1 (by rfl) ⟨110354192, by rfl⟩ : syracuseStep 147138923 = 220708385) B220708385
theorem B1591967 : Blo 1590994 1591967 := bstep (se 1 (by rfl) ⟨1193975, by rfl⟩ : syracuseStep 1591967 = 2387951) B2387951
theorem B8063711 : Blo 1590994 8063711 := bstep (se 1 (by rfl) ⟨6047783, by rfl⟩ : syracuseStep 8063711 = 12095567) B12095567
theorem B3582719 : Blo 1590994 3582719 := bstep (se 1 (by rfl) ⟨2687039, by rfl⟩ : syracuseStep 3582719 = 5374079) B5374079
theorem B1592167 : Blo 1590994 1592167 := bstep (se 1 (by rfl) ⟨1194125, by rfl⟩ : syracuseStep 1592167 = 2388251) B2388251
theorem B3582971 : Blo 1590994 3582971 := bstep (se 1 (by rfl) ⟨2687228, by rfl⟩ : syracuseStep 3582971 = 5374457) B5374457
theorem B2387111 : Blo 1590994 2387111 := bstep (se 1 (by rfl) ⟨1790333, by rfl⟩ : syracuseStep 2387111 = 3580667) B3580667
theorem B1592623 : Blo 1590994 1592623 := bstep (se 1 (by rfl) ⟨1194467, by rfl⟩ : syracuseStep 1592623 = 2388935) B2388935
theorem B20393639 : Blo 1590994 20393639 := bstep (se 1 (by rfl) ⟨15295229, by rfl⟩ : syracuseStep 20393639 = 30590459) B30590459
theorem B2387687 : Blo 1590994 2387687 := bstep (se 1 (by rfl) ⟨1790765, by rfl⟩ : syracuseStep 2387687 = 3581531) B3581531
theorem B3583727 : Blo 1590994 3583727 := bstep (se 1 (by rfl) ⟨2687795, by rfl⟩ : syracuseStep 3583727 = 5375591) B5375591
theorem B3927835 : Blo 1590994 3927835 := bstep (se 1 (by rfl) ⟨2945876, by rfl⟩ : syracuseStep 3927835 = 5891753) B5891753
theorem B18133145 : Blo 1590994 18133145 := bstep (se 2 (by rfl) ⟨6799929, by rfl⟩ : syracuseStep 18133145 = 13599859) B13599859
theorem B6803689 : Blo 1590994 6803689 := bstep (se 2 (by rfl) ⟨2551383, by rfl⟩ : syracuseStep 6803689 = 5102767) B5102767
theorem B2388455 : Blo 1590994 2388455 := bstep (se 1 (by rfl) ⟨1791341, by rfl⟩ : syracuseStep 2388455 = 3582683) B3582683
theorem B2388719 : Blo 1590994 2388719 := bstep (se 1 (by rfl) ⟨1791539, by rfl⟩ : syracuseStep 2388719 = 3583079) B3583079
theorem B8058041 : Blo 1590994 8058041 := bstep (se 2 (by rfl) ⟨3021765, by rfl⟩ : syracuseStep 8058041 = 6043531) B6043531
theorem B4027583 : Blo 1590994 4027583 := bstep (se 1 (by rfl) ⟨3020687, by rfl⟩ : syracuseStep 4027583 = 6041375) B6041375
theorem B1791391 : Blo 1590994 1791391 := bstep (se 1 (by rfl) ⟨1343543, by rfl⟩ : syracuseStep 1791391 = 2687087) B2687087
theorem B20690387 : Blo 1590994 20690387 := bstep (se 1 (by rfl) ⟨15517790, by rfl⟩ : syracuseStep 20690387 = 31035581) B31035581
theorem B3020665 : Blo 1590994 3020665 := bstep (se 2 (by rfl) ⟨1132749, by rfl⟩ : syracuseStep 3020665 = 2265499) B2265499
theorem B5372243 : Blo 1590994 5372243 := bstep (se 1 (by rfl) ⟨4029182, by rfl⟩ : syracuseStep 5372243 = 8058365) B8058365
theorem B10475891 : Blo 1590994 10475891 := bstep (se 1 (by rfl) ⟨7856918, by rfl⟩ : syracuseStep 10475891 = 15713837) B15713837
theorem B50379641 : Blo 1590994 50379641 := bstep (se 2 (by rfl) ⟨18892365, by rfl⟩ : syracuseStep 50379641 = 37784731) B37784731
theorem B4029547 : Blo 1590994 4029547 := bstep (se 1 (by rfl) ⟨3022160, by rfl⟩ : syracuseStep 4029547 = 6044321) B6044321
theorem B45874511 : Blo 1590994 45874511 := bstep (se 1 (by rfl) ⟨34405883, by rfl⟩ : syracuseStep 45874511 = 68811767) B68811767
theorem B110255555 : Blo 1590994 110255555 := bstep (se 1 (by rfl) ⟨82691666, by rfl⟩ : syracuseStep 110255555 = 165383333) B165383333
theorem B27581903 : Blo 1590994 27581903 := bstep (se 1 (by rfl) ⟨20686427, by rfl⟩ : syracuseStep 27581903 = 41372855) B41372855
theorem B4029983 : Blo 1590994 4029983 := bstep (se 1 (by rfl) ⟨3022487, by rfl⟩ : syracuseStep 4029983 = 6044975) B6044975
theorem B8601191 : Blo 1590994 8601191 := bstep (se 1 (by rfl) ⟨6450893, by rfl⟩ : syracuseStep 8601191 = 12901787) B12901787
theorem B8281919 : Blo 1590994 8281919 := bstep (se 1 (by rfl) ⟨6211439, by rfl⟩ : syracuseStep 8281919 = 12422879) B12422879
theorem B40796297 : Blo 1590994 40796297 := bstep (se 2 (by rfl) ⟨15298611, by rfl⟩ : syracuseStep 40796297 = 30597223) B30597223
theorem B5374187 : Blo 1590994 5374187 := bstep (se 1 (by rfl) ⟨4030640, by rfl⟩ : syracuseStep 5374187 = 8061281) B8061281
theorem B24502601 : Blo 1590994 24502601 := bstep (se 2 (by rfl) ⟨9188475, by rfl⟩ : syracuseStep 24502601 = 18376951) B18376951
theorem B6046235 : Blo 1590994 6046235 := bstep (se 1 (by rfl) ⟨4534676, by rfl⟩ : syracuseStep 6046235 = 9069353) B9069353
theorem B4031471 : Blo 1590994 4031471 := bstep (se 1 (by rfl) ⟨3023603, by rfl⟩ : syracuseStep 4031471 = 6047207) B6047207
theorem B20948453 : Blo 1590994 20948453 := bstep (se 4 (by rfl) ⟨1963917, by rfl⟩ : syracuseStep 20948453 = 3927835) B3927835
theorem B3581495 : Blo 1590994 3581495 := bstep (se 1 (by rfl) ⟨2686121, by rfl⟩ : syracuseStep 3581495 = 5372243) B5372243
theorem B98092615 : Blo 1590994 98092615 := bstep (se 1 (by rfl) ⟨73569461, by rfl⟩ : syracuseStep 98092615 = 147138923) B147138923
theorem B5375807 : Blo 1590994 5375807 := bstep (se 1 (by rfl) ⟨4031855, by rfl⟩ : syracuseStep 5375807 = 8063711) B8063711
theorem B1591407 : Blo 1590994 1591407 := bstep (se 1 (by rfl) ⟨1193555, by rfl⟩ : syracuseStep 1591407 = 2387111) B2387111
theorem B30583007 : Blo 1590994 30583007 := bstep (se 1 (by rfl) ⟨22937255, by rfl⟩ : syracuseStep 30583007 = 45874511) B45874511
theorem B1591791 : Blo 1590994 1591791 := bstep (se 1 (by rfl) ⟨1193843, by rfl⟩ : syracuseStep 1591791 = 2387687) B2387687
theorem B38742911 : Blo 1590994 38742911 := bstep (se 1 (by rfl) ⟨29057183, by rfl⟩ : syracuseStep 38742911 = 58114367) B58114367
theorem B9071585 : Blo 1590994 9071585 := bstep (se 2 (by rfl) ⟨3401844, by rfl⟩ : syracuseStep 9071585 = 6803689) B6803689
theorem B1592303 : Blo 1590994 1592303 := bstep (se 1 (by rfl) ⟨1194227, by rfl⟩ : syracuseStep 1592303 = 2388455) B2388455
theorem B1592479 : Blo 1590994 1592479 := bstep (se 1 (by rfl) ⟨1194359, by rfl⟩ : syracuseStep 1592479 = 2388719) B2388719
theorem B2387195 : Blo 1590994 2387195 := bstep (se 1 (by rfl) ⟨1790396, by rfl⟩ : syracuseStep 2387195 = 3580793) B3580793
theorem B2387291 : Blo 1590994 2387291 := bstep (se 1 (by rfl) ⟨1790468, by rfl⟩ : syracuseStep 2387291 = 3580937) B3580937
theorem B91762145 : Blo 1590994 91762145 := bstep (se 2 (by rfl) ⟨34410804, by rfl⟩ : syracuseStep 91762145 = 68821609) B68821609
theorem B3583943 : Blo 1590994 3583943 := bstep (se 1 (by rfl) ⟨2687957, by rfl⟩ : syracuseStep 3583943 = 5375915) B5375915
theorem B31027151 : Blo 1590994 31027151 := bstep (se 1 (by rfl) ⟨23270363, by rfl⟩ : syracuseStep 31027151 = 46540727) B46540727
theorem B2388071 : Blo 1590994 2388071 := bstep (se 1 (by rfl) ⟨1791053, by rfl⟩ : syracuseStep 2388071 = 3582107) B3582107
theorem B6983927 : Blo 1590994 6983927 := bstep (se 1 (by rfl) ⟨5237945, by rfl⟩ : syracuseStep 6983927 = 10475891) B10475891
theorem B2388479 : Blo 1590994 2388479 := bstep (se 1 (by rfl) ⟨1791359, by rfl⟩ : syracuseStep 2388479 = 3582719) B3582719
theorem B2388521 : Blo 1590994 2388521 := bstep (se 2 (by rfl) ⟨895695, by rfl⟩ : syracuseStep 2388521 = 1791391) B1791391
theorem B4534825 : Blo 1590994 4534825 := bstep (se 2 (by rfl) ⟨1700559, by rfl⟩ : syracuseStep 4534825 = 3401119) B3401119
theorem B2388647 : Blo 1590994 2388647 := bstep (se 1 (by rfl) ⟨1791485, by rfl⟩ : syracuseStep 2388647 = 3582971) B3582971
theorem B73503703 : Blo 1590994 73503703 := bstep (se 1 (by rfl) ⟨55127777, by rfl⟩ : syracuseStep 73503703 = 110255555) B110255555
theorem B18387935 : Blo 1590994 18387935 := bstep (se 1 (by rfl) ⟨13790951, by rfl⟩ : syracuseStep 18387935 = 27581903) B27581903
theorem B13595759 : Blo 1590994 13595759 := bstep (se 1 (by rfl) ⟨10196819, by rfl⟩ : syracuseStep 13595759 = 20393639) B20393639
theorem B2389151 : Blo 1590994 2389151 := bstep (se 1 (by rfl) ⟨1791863, by rfl⟩ : syracuseStep 2389151 = 3583727) B3583727
theorem B4027553 : Blo 1590994 4027553 := bstep (se 2 (by rfl) ⟨1510332, by rfl⟩ : syracuseStep 4027553 = 3020665) B3020665
theorem B12088763 : Blo 1590994 12088763 := bstep (se 1 (by rfl) ⟨9066572, by rfl⟩ : syracuseStep 12088763 = 18133145) B18133145
theorem B5372027 : Blo 1590994 5372027 := bstep (se 1 (by rfl) ⟨4029020, by rfl⟩ : syracuseStep 5372027 = 8058041) B8058041
theorem B2685055 : Blo 1590994 2685055 := bstep (se 1 (by rfl) ⟨2013791, by rfl⟩ : syracuseStep 2685055 = 4027583) B4027583
theorem B13793591 : Blo 1590994 13793591 := bstep (se 1 (by rfl) ⟨10345193, by rfl⟩ : syracuseStep 13793591 = 20690387) B20690387
theorem B3021455 : Blo 1590994 3021455 := bstep (se 1 (by rfl) ⟨2266091, by rfl⟩ : syracuseStep 3021455 = 4532183) B4532183
theorem B5372729 : Blo 1590994 5372729 := bstep (se 2 (by rfl) ⟨2014773, by rfl⟩ : syracuseStep 5372729 = 4029547) B4029547
theorem B33586427 : Blo 1590994 33586427 := bstep (se 1 (by rfl) ⟨25189820, by rfl⟩ : syracuseStep 33586427 = 50379641) B50379641
theorem B2686655 : Blo 1590994 2686655 := bstep (se 1 (by rfl) ⟨2014991, by rfl⟩ : syracuseStep 2686655 = 4029983) B4029983
theorem B5734127 : Blo 1590994 5734127 := bstep (se 1 (by rfl) ⟨4300595, by rfl⟩ : syracuseStep 5734127 = 8601191) B8601191
theorem B5521279 : Blo 1590994 5521279 := bstep (se 1 (by rfl) ⟨4140959, by rfl⟩ : syracuseStep 5521279 = 8281919) B8281919
theorem B27197531 : Blo 1590994 27197531 := bstep (se 1 (by rfl) ⟨20398148, by rfl⟩ : syracuseStep 27197531 = 40796297) B40796297
theorem B3580073 : Blo 1590994 3580073 := bstep (se 2 (by rfl) ⟨1342527, by rfl⟩ : syracuseStep 3580073 = 2685055) B2685055
theorem B16335067 : Blo 1590994 16335067 := bstep (se 1 (by rfl) ⟨12251300, by rfl⟩ : syracuseStep 16335067 = 24502601) B24502601
theorem B4030823 : Blo 1590994 4030823 := bstep (se 1 (by rfl) ⟨3023117, by rfl⟩ : syracuseStep 4030823 = 6046235) B6046235
theorem B2687647 : Blo 1590994 2687647 := bstep (se 1 (by rfl) ⟨2015735, by rfl⟩ : syracuseStep 2687647 = 4031471) B4031471
theorem B6046433 : Blo 1590994 6046433 := bstep (se 2 (by rfl) ⟨2267412, by rfl⟩ : syracuseStep 6046433 = 4534825) B4534825
theorem B3581351 : Blo 1590994 3581351 := bstep (se 1 (by rfl) ⟨2686013, by rfl⟩ : syracuseStep 3581351 = 5372027) B5372027
theorem B3581819 : Blo 1590994 3581819 := bstep (se 1 (by rfl) ⟨2686364, by rfl⟩ : syracuseStep 3581819 = 5372729) B5372729
theorem B6047723 : Blo 1590994 6047723 := bstep (se 1 (by rfl) ⟨4535792, by rfl⟩ : syracuseStep 6047723 = 9071585) B9071585
theorem B1591463 : Blo 1590994 1591463 := bstep (se 1 (by rfl) ⟨1193597, by rfl⟩ : syracuseStep 1591463 = 2387195) B2387195
theorem B22390951 : Blo 1590994 22390951 := bstep (se 1 (by rfl) ⟨16793213, by rfl⟩ : syracuseStep 22390951 = 33586427) B33586427
theorem B1591527 : Blo 1590994 1591527 := bstep (se 1 (by rfl) ⟨1193645, by rfl⟩ : syracuseStep 1591527 = 2387291) B2387291
theorem B1592047 : Blo 1590994 1592047 := bstep (se 1 (by rfl) ⟨1194035, by rfl⟩ : syracuseStep 1592047 = 2388071) B2388071
theorem B3582791 : Blo 1590994 3582791 := bstep (se 1 (by rfl) ⟨2687093, by rfl⟩ : syracuseStep 3582791 = 5374187) B5374187
theorem B4655951 : Blo 1590994 4655951 := bstep (se 1 (by rfl) ⟨3491963, by rfl⟩ : syracuseStep 4655951 = 6983927) B6983927
theorem B1592319 : Blo 1590994 1592319 := bstep (se 1 (by rfl) ⟨1194239, by rfl⟩ : syracuseStep 1592319 = 2388479) B2388479
theorem B1592347 : Blo 1590994 1592347 := bstep (se 1 (by rfl) ⟨1194260, by rfl⟩ : syracuseStep 1592347 = 2388521) B2388521
theorem B1592431 : Blo 1590994 1592431 := bstep (se 1 (by rfl) ⟨1194323, by rfl⟩ : syracuseStep 1592431 = 2388647) B2388647
theorem B12258623 : Blo 1590994 12258623 := bstep (se 1 (by rfl) ⟨9193967, by rfl⟩ : syracuseStep 12258623 = 18387935) B18387935
theorem B9063839 : Blo 1590994 9063839 := bstep (se 1 (by rfl) ⟨6797879, by rfl⟩ : syracuseStep 9063839 = 13595759) B13595759
theorem B1592767 : Blo 1590994 1592767 := bstep (se 1 (by rfl) ⟨1194575, by rfl⟩ : syracuseStep 1592767 = 2389151) B2389151
theorem B2387663 : Blo 1590994 2387663 := bstep (se 1 (by rfl) ⟨1790747, by rfl⟩ : syracuseStep 2387663 = 3581495) B3581495
theorem B3583871 : Blo 1590994 3583871 := bstep (se 1 (by rfl) ⟨2687903, by rfl⟩ : syracuseStep 3583871 = 5375807) B5375807
theorem B9195727 : Blo 1590994 9195727 := bstep (se 1 (by rfl) ⟨6896795, by rfl⟩ : syracuseStep 9195727 = 13793591) B13793591
theorem B130790153 : Blo 1590994 130790153 := bstep (se 2 (by rfl) ⟨49046307, by rfl⟩ : syracuseStep 130790153 = 98092615) B98092615
theorem B61174763 : Blo 1590994 61174763 := bstep (se 1 (by rfl) ⟨45881072, by rfl⟩ : syracuseStep 61174763 = 91762145) B91762145
theorem B1791103 : Blo 1590994 1791103 := bstep (se 1 (by rfl) ⟨1343327, by rfl⟩ : syracuseStep 1791103 = 2686655) B2686655
theorem B3822751 : Blo 1590994 3822751 := bstep (se 1 (by rfl) ⟨2867063, by rfl⟩ : syracuseStep 3822751 = 5734127) B5734127
theorem B7361705 : Blo 1590994 7361705 := bstep (se 2 (by rfl) ⟨2760639, by rfl⟩ : syracuseStep 7361705 = 5521279) B5521279
theorem B2389295 : Blo 1590994 2389295 := bstep (se 1 (by rfl) ⟨1791971, by rfl⟩ : syracuseStep 2389295 = 3583943) B3583943
theorem B2685035 : Blo 1590994 2685035 := bstep (se 1 (by rfl) ⟨2013776, by rfl⟩ : syracuseStep 2685035 = 4027553) B4027553
theorem B8059175 : Blo 1590994 8059175 := bstep (se 1 (by rfl) ⟨6044381, by rfl⟩ : syracuseStep 8059175 = 12088763) B12088763
theorem B13965635 : Blo 1590994 13965635 := bstep (se 1 (by rfl) ⟨10474226, by rfl⟩ : syracuseStep 13965635 = 20948453) B20948453
theorem B20388671 : Blo 1590994 20388671 := bstep (se 1 (by rfl) ⟨15291503, by rfl⟩ : syracuseStep 20388671 = 30583007) B30583007
theorem B2014303 : Blo 1590994 2014303 := bstep (se 1 (by rfl) ⟨1510727, by rfl⟩ : syracuseStep 2014303 = 3021455) B3021455
theorem B25828607 : Blo 1590994 25828607 := bstep (se 1 (by rfl) ⟨19371455, by rfl⟩ : syracuseStep 25828607 = 38742911) B38742911
theorem B392019749 : Blo 1590994 392019749 := bstep (se 4 (by rfl) ⟨36751851, by rfl⟩ : syracuseStep 392019749 = 73503703) B73503703
theorem B20684767 : Blo 1590994 20684767 := bstep (se 1 (by rfl) ⟨15513575, by rfl⟩ : syracuseStep 20684767 = 31027151) B31027151
theorem B2687215 : Blo 1590994 2687215 := bstep (se 1 (by rfl) ⟨2015411, by rfl⟩ : syracuseStep 2687215 = 4030823) B4030823
theorem B4030955 : Blo 1590994 4030955 := bstep (se 1 (by rfl) ⟨3023216, by rfl⟩ : syracuseStep 4030955 = 6046433) B6046433
theorem B4907803 : Blo 1590994 4907803 := bstep (se 1 (by rfl) ⟨3680852, by rfl⟩ : syracuseStep 4907803 = 7361705) B7361705
theorem B4031815 : Blo 1590994 4031815 := bstep (se 1 (by rfl) ⟨3023861, by rfl⟩ : syracuseStep 4031815 = 6047723) B6047723
theorem B5097001 : Blo 1590994 5097001 := bstep (se 2 (by rfl) ⟨1911375, by rfl⟩ : syracuseStep 5097001 = 3822751) B3822751
theorem B13592447 : Blo 1590994 13592447 := bstep (se 1 (by rfl) ⟨10194335, by rfl⟩ : syracuseStep 13592447 = 20388671) B20388671
theorem B1591775 : Blo 1590994 1591775 := bstep (se 1 (by rfl) ⟨1193831, by rfl⟩ : syracuseStep 1591775 = 2387663) B2387663
theorem B18131687 : Blo 1590994 18131687 := bstep (se 1 (by rfl) ⟨13598765, by rfl⟩ : syracuseStep 18131687 = 27197531) B27197531
theorem B2386715 : Blo 1590994 2386715 := bstep (se 1 (by rfl) ⟨1790036, by rfl⟩ : syracuseStep 2386715 = 3580073) B3580073
theorem B29854601 : Blo 1590994 29854601 := bstep (se 2 (by rfl) ⟨11195475, by rfl⟩ : syracuseStep 29854601 = 22390951) B22390951
theorem B40783175 : Blo 1590994 40783175 := bstep (se 1 (by rfl) ⟨30587381, by rfl⟩ : syracuseStep 40783175 = 61174763) B61174763
theorem B1592863 : Blo 1590994 1592863 := bstep (se 1 (by rfl) ⟨1194647, by rfl⟩ : syracuseStep 1592863 = 2389295) B2389295
theorem B3583529 : Blo 1590994 3583529 := bstep (se 2 (by rfl) ⟨1343823, by rfl⟩ : syracuseStep 3583529 = 2687647) B2687647
theorem B2387567 : Blo 1590994 2387567 := bstep (se 1 (by rfl) ⟨1790675, by rfl⟩ : syracuseStep 2387567 = 3581351) B3581351
theorem B2387879 : Blo 1590994 2387879 := bstep (se 1 (by rfl) ⟨1790909, by rfl⟩ : syracuseStep 2387879 = 3581819) B3581819
theorem B1790023 : Blo 1590994 1790023 := bstep (se 1 (by rfl) ⟨1342517, by rfl⟩ : syracuseStep 1790023 = 2685035) B2685035
theorem B2388137 : Blo 1590994 2388137 := bstep (se 2 (by rfl) ⟨895551, by rfl⟩ : syracuseStep 2388137 = 1791103) B1791103
theorem B9310423 : Blo 1590994 9310423 := bstep (se 1 (by rfl) ⟨6982817, by rfl⟩ : syracuseStep 9310423 = 13965635) B13965635
theorem B2388527 : Blo 1590994 2388527 := bstep (se 1 (by rfl) ⟨1791395, by rfl⟩ : syracuseStep 2388527 = 3582791) B3582791
theorem B8172415 : Blo 1590994 8172415 := bstep (se 1 (by rfl) ⟨6129311, by rfl⟩ : syracuseStep 8172415 = 12258623) B12258623
theorem B6042559 : Blo 1590994 6042559 := bstep (se 1 (by rfl) ⟨4531919, by rfl⟩ : syracuseStep 6042559 = 9063839) B9063839
theorem B261346499 : Blo 1590994 261346499 := bstep (se 1 (by rfl) ⟨196009874, by rfl⟩ : syracuseStep 261346499 = 392019749) B392019749
theorem B2389247 : Blo 1590994 2389247 := bstep (se 1 (by rfl) ⟨1791935, by rfl⟩ : syracuseStep 2389247 = 3583871) B3583871
theorem B27579689 : Blo 1590994 27579689 := bstep (se 2 (by rfl) ⟨10342383, by rfl⟩ : syracuseStep 27579689 = 20684767) B20684767
theorem B12260969 : Blo 1590994 12260969 := bstep (se 2 (by rfl) ⟨4597863, by rfl⟩ : syracuseStep 12260969 = 9195727) B9195727
theorem B21780089 : Blo 1590994 21780089 := bstep (se 2 (by rfl) ⟨8167533, by rfl⟩ : syracuseStep 21780089 = 16335067) B16335067
theorem B87193435 : Blo 1590994 87193435 := bstep (se 1 (by rfl) ⟨65395076, by rfl⟩ : syracuseStep 87193435 = 130790153) B130790153
theorem B2685737 : Blo 1590994 2685737 := bstep (se 2 (by rfl) ⟨1007151, by rfl⟩ : syracuseStep 2685737 = 2014303) B2014303
theorem B5372783 : Blo 1590994 5372783 := bstep (se 1 (by rfl) ⟨4029587, by rfl⟩ : syracuseStep 5372783 = 8059175) B8059175
theorem B3103967 : Blo 1590994 3103967 := bstep (se 1 (by rfl) ⟨2327975, by rfl⟩ : syracuseStep 3103967 = 4655951) B4655951
theorem B17219071 : Blo 1590994 17219071 := bstep (se 1 (by rfl) ⟨12914303, by rfl⟩ : syracuseStep 17219071 = 25828607) B25828607
theorem B2687303 : Blo 1590994 2687303 := bstep (se 1 (by rfl) ⟨2015477, by rfl⟩ : syracuseStep 2687303 = 4030955) B4030955
theorem B10896553 : Blo 1590994 10896553 := bstep (se 2 (by rfl) ⟨4086207, by rfl⟩ : syracuseStep 10896553 = 8172415) B8172415
theorem B9061631 : Blo 1590994 9061631 := bstep (se 1 (by rfl) ⟨6796223, by rfl⟩ : syracuseStep 9061631 = 13592447) B13592447
theorem B5375753 : Blo 1590994 5375753 := bstep (se 2 (by rfl) ⟨2015907, by rfl⟩ : syracuseStep 5375753 = 4031815) B4031815
theorem B1591143 : Blo 1590994 1591143 := bstep (se 1 (by rfl) ⟨1193357, by rfl⟩ : syracuseStep 1591143 = 2386715) B2386715
theorem B3581855 : Blo 1590994 3581855 := bstep (se 1 (by rfl) ⟨2686391, by rfl⟩ : syracuseStep 3581855 = 5372783) B5372783
theorem B1591711 : Blo 1590994 1591711 := bstep (se 1 (by rfl) ⟨1193783, by rfl⟩ : syracuseStep 1591711 = 2387567) B2387567
theorem B1591919 : Blo 1590994 1591919 := bstep (se 1 (by rfl) ⟨1193939, by rfl⟩ : syracuseStep 1591919 = 2387879) B2387879
theorem B2386697 : Blo 1590994 2386697 := bstep (se 2 (by rfl) ⟨895011, by rfl⟩ : syracuseStep 2386697 = 1790023) B1790023
theorem B1592091 : Blo 1590994 1592091 := bstep (se 1 (by rfl) ⟨1194068, by rfl⟩ : syracuseStep 1592091 = 2388137) B2388137
theorem B12413897 : Blo 1590994 12413897 := bstep (se 2 (by rfl) ⟨4655211, by rfl⟩ : syracuseStep 12413897 = 9310423) B9310423
theorem B3582953 : Blo 1590994 3582953 := bstep (se 2 (by rfl) ⟨1343607, by rfl⟩ : syracuseStep 3582953 = 2687215) B2687215
theorem B1592351 : Blo 1590994 1592351 := bstep (se 1 (by rfl) ⟨1194263, by rfl⟩ : syracuseStep 1592351 = 2388527) B2388527
theorem B174230999 : Blo 1590994 174230999 := bstep (se 1 (by rfl) ⟨130673249, by rfl⟩ : syracuseStep 174230999 = 261346499) B261346499
theorem B1592831 : Blo 1590994 1592831 := bstep (se 1 (by rfl) ⟨1194623, by rfl⟩ : syracuseStep 1592831 = 2389247) B2389247
theorem B18386459 : Blo 1590994 18386459 := bstep (se 1 (by rfl) ⟨13789844, by rfl⟩ : syracuseStep 18386459 = 27579689) B27579689
theorem B14520059 : Blo 1590994 14520059 := bstep (se 1 (by rfl) ⟨10890044, by rfl⟩ : syracuseStep 14520059 = 21780089) B21780089
theorem B8056745 : Blo 1590994 8056745 := bstep (se 2 (by rfl) ⟨3021279, by rfl⟩ : syracuseStep 8056745 = 6042559) B6042559
theorem B12087791 : Blo 1590994 12087791 := bstep (se 1 (by rfl) ⟨9065843, by rfl⟩ : syracuseStep 12087791 = 18131687) B18131687
theorem B1790491 : Blo 1590994 1790491 := bstep (se 1 (by rfl) ⟨1342868, by rfl⟩ : syracuseStep 1790491 = 2685737) B2685737
theorem B19903067 : Blo 1590994 19903067 := bstep (se 1 (by rfl) ⟨14927300, by rfl⟩ : syracuseStep 19903067 = 29854601) B29854601
theorem B22958761 : Blo 1590994 22958761 := bstep (se 2 (by rfl) ⟨8609535, by rfl⟩ : syracuseStep 22958761 = 17219071) B17219071
theorem B6796001 : Blo 1590994 6796001 := bstep (se 2 (by rfl) ⟨2548500, by rfl⟩ : syracuseStep 6796001 = 5097001) B5097001
theorem B2069311 : Blo 1590994 2069311 := bstep (se 1 (by rfl) ⟨1551983, by rfl⟩ : syracuseStep 2069311 = 3103967) B3103967
theorem B2389019 : Blo 1590994 2389019 := bstep (se 1 (by rfl) ⟨1791764, by rfl⟩ : syracuseStep 2389019 = 3583529) B3583529
theorem B116257913 : Blo 1590994 116257913 := bstep (se 2 (by rfl) ⟨43596717, by rfl⟩ : syracuseStep 116257913 = 87193435) B87193435
theorem B6543737 : Blo 1590994 6543737 := bstep (se 2 (by rfl) ⟨2453901, by rfl⟩ : syracuseStep 6543737 = 4907803) B4907803
theorem B8173979 : Blo 1590994 8173979 := bstep (se 1 (by rfl) ⟨6130484, by rfl⟩ : syracuseStep 8173979 = 12260969) B12260969
theorem B27188783 : Blo 1590994 27188783 := bstep (se 1 (by rfl) ⟨20391587, by rfl⟩ : syracuseStep 27188783 = 40783175) B40783175
theorem B4530667 : Blo 1590994 4530667 := bstep (se 1 (by rfl) ⟨3398000, by rfl⟩ : syracuseStep 4530667 = 6796001) B6796001
theorem B77505275 : Blo 1590994 77505275 := bstep (se 1 (by rfl) ⟨58128956, by rfl⟩ : syracuseStep 77505275 = 116257913) B116257913
theorem B5449319 : Blo 1590994 5449319 := bstep (se 1 (by rfl) ⟨4086989, by rfl⟩ : syracuseStep 5449319 = 8173979) B8173979
theorem B1591131 : Blo 1590994 1591131 := bstep (se 1 (by rfl) ⟨1193348, by rfl⟩ : syracuseStep 1591131 = 2386697) B2386697
theorem B8275931 : Blo 1590994 8275931 := bstep (se 1 (by rfl) ⟨6206948, by rfl⟩ : syracuseStep 8275931 = 12413897) B12413897
theorem B12257639 : Blo 1590994 12257639 := bstep (se 1 (by rfl) ⟨9193229, by rfl⟩ : syracuseStep 12257639 = 18386459) B18386459
theorem B1592679 : Blo 1590994 1592679 := bstep (se 1 (by rfl) ⟨1194509, by rfl⟩ : syracuseStep 1592679 = 2389019) B2389019
theorem B2387321 : Blo 1590994 2387321 := bstep (se 2 (by rfl) ⟨895245, by rfl⟩ : syracuseStep 2387321 = 1790491) B1790491
theorem B6041087 : Blo 1590994 6041087 := bstep (se 1 (by rfl) ⟨4530815, by rfl⟩ : syracuseStep 6041087 = 9061631) B9061631
theorem B3583835 : Blo 1590994 3583835 := bstep (se 1 (by rfl) ⟨2687876, by rfl⟩ : syracuseStep 3583835 = 5375753) B5375753
theorem B2387903 : Blo 1590994 2387903 := bstep (se 1 (by rfl) ⟨1790927, by rfl⟩ : syracuseStep 2387903 = 3581855) B3581855
theorem B14528737 : Blo 1590994 14528737 := bstep (se 2 (by rfl) ⟨5448276, by rfl⟩ : syracuseStep 14528737 = 10896553) B10896553
theorem B4362491 : Blo 1590994 4362491 := bstep (se 1 (by rfl) ⟨3271868, by rfl⟩ : syracuseStep 4362491 = 6543737) B6543737
theorem B2388635 : Blo 1590994 2388635 := bstep (se 1 (by rfl) ⟨1791476, by rfl⟩ : syracuseStep 2388635 = 3582953) B3582953
theorem B18125855 : Blo 1590994 18125855 := bstep (se 1 (by rfl) ⟨13594391, by rfl⟩ : syracuseStep 18125855 = 27188783) B27188783
theorem B9680039 : Blo 1590994 9680039 := bstep (se 1 (by rfl) ⟨7260029, by rfl⟩ : syracuseStep 9680039 = 14520059) B14520059
theorem B5371163 : Blo 1590994 5371163 := bstep (se 1 (by rfl) ⟨4028372, by rfl⟩ : syracuseStep 5371163 = 8056745) B8056745
theorem B1791535 : Blo 1590994 1791535 := bstep (se 1 (by rfl) ⟨1343651, by rfl⟩ : syracuseStep 1791535 = 2687303) B2687303
theorem B8058527 : Blo 1590994 8058527 := bstep (se 1 (by rfl) ⟨6043895, by rfl⟩ : syracuseStep 8058527 = 12087791) B12087791
theorem B13268711 : Blo 1590994 13268711 := bstep (se 1 (by rfl) ⟨9951533, by rfl⟩ : syracuseStep 13268711 = 19903067) B19903067
theorem B30611681 : Blo 1590994 30611681 := bstep (se 2 (by rfl) ⟨11479380, by rfl⟩ : syracuseStep 30611681 = 22958761) B22958761
theorem B2759081 : Blo 1590994 2759081 := bstep (se 2 (by rfl) ⟨1034655, by rfl⟩ : syracuseStep 2759081 = 2069311) B2069311
theorem B116153999 : Blo 1590994 116153999 := bstep (se 1 (by rfl) ⟨87115499, by rfl⟩ : syracuseStep 116153999 = 174230999) B174230999
theorem B11633309 : Blo 1590994 11633309 := bstep (se 3 (by rfl) ⟨2181245, by rfl⟩ : syracuseStep 11633309 = 4362491) B4362491
theorem B12083903 : Blo 1590994 12083903 := bstep (se 1 (by rfl) ⟨9062927, by rfl⟩ : syracuseStep 12083903 = 18125855) B18125855
theorem B3580775 : Blo 1590994 3580775 := bstep (se 1 (by rfl) ⟨2685581, by rfl⟩ : syracuseStep 3580775 = 5371163) B5371163
theorem B7357549 : Blo 1590994 7357549 := bstep (se 3 (by rfl) ⟨1379540, by rfl⟩ : syracuseStep 7357549 = 2759081) B2759081
theorem B20407787 : Blo 1590994 20407787 := bstep (se 1 (by rfl) ⟨15305840, by rfl⟩ : syracuseStep 20407787 = 30611681) B30611681
theorem B1591547 : Blo 1590994 1591547 := bstep (se 1 (by rfl) ⟨1193660, by rfl⟩ : syracuseStep 1591547 = 2387321) B2387321
theorem B1591935 : Blo 1590994 1591935 := bstep (se 1 (by rfl) ⟨1193951, by rfl⟩ : syracuseStep 1591935 = 2387903) B2387903
theorem B1592423 : Blo 1590994 1592423 := bstep (se 1 (by rfl) ⟨1194317, by rfl⟩ : syracuseStep 1592423 = 2388635) B2388635
theorem B51670183 : Blo 1590994 51670183 := bstep (se 1 (by rfl) ⟨38752637, by rfl⟩ : syracuseStep 51670183 = 77505275) B77505275
theorem B6040889 : Blo 1590994 6040889 := bstep (se 2 (by rfl) ⟨2265333, by rfl⟩ : syracuseStep 6040889 = 4530667) B4530667
theorem B3632879 : Blo 1590994 3632879 := bstep (se 1 (by rfl) ⟨2724659, by rfl⟩ : syracuseStep 3632879 = 5449319) B5449319
theorem B5517287 : Blo 1590994 5517287 := bstep (se 1 (by rfl) ⟨4137965, by rfl⟩ : syracuseStep 5517287 = 8275931) B8275931
theorem B8171759 : Blo 1590994 8171759 := bstep (se 1 (by rfl) ⟨6128819, by rfl⟩ : syracuseStep 8171759 = 12257639) B12257639
theorem B2388713 : Blo 1590994 2388713 := bstep (se 2 (by rfl) ⟨895767, by rfl⟩ : syracuseStep 2388713 = 1791535) B1791535
theorem B4027391 : Blo 1590994 4027391 := bstep (se 1 (by rfl) ⟨3020543, by rfl⟩ : syracuseStep 4027391 = 6041087) B6041087
theorem B77435999 : Blo 1590994 77435999 := bstep (se 1 (by rfl) ⟨58076999, by rfl⟩ : syracuseStep 77435999 = 116153999) B116153999
theorem B2389223 : Blo 1590994 2389223 := bstep (se 1 (by rfl) ⟨1791917, by rfl⟩ : syracuseStep 2389223 = 3583835) B3583835
theorem B19371649 : Blo 1590994 19371649 := bstep (se 2 (by rfl) ⟨7264368, by rfl⟩ : syracuseStep 19371649 = 14528737) B14528737
theorem B6453359 : Blo 1590994 6453359 := bstep (se 1 (by rfl) ⟨4840019, by rfl⟩ : syracuseStep 6453359 = 9680039) B9680039
theorem B5372351 : Blo 1590994 5372351 := bstep (se 1 (by rfl) ⟨4029263, by rfl⟩ : syracuseStep 5372351 = 8058527) B8058527
theorem B8845807 : Blo 1590994 8845807 := bstep (se 1 (by rfl) ⟨6634355, by rfl⟩ : syracuseStep 8845807 = 13268711) B13268711
theorem B5447839 : Blo 1590994 5447839 := bstep (se 1 (by rfl) ⟨4085879, by rfl⟩ : syracuseStep 5447839 = 8171759) B8171759
theorem B4302239 : Blo 1590994 4302239 := bstep (se 1 (by rfl) ⟨3226679, by rfl⟩ : syracuseStep 4302239 = 6453359) B6453359
theorem B3581567 : Blo 1590994 3581567 := bstep (se 1 (by rfl) ⟨2686175, by rfl⟩ : syracuseStep 3581567 = 5372351) B5372351
theorem B8055935 : Blo 1590994 8055935 := bstep (se 1 (by rfl) ⟨6041951, by rfl⟩ : syracuseStep 8055935 = 12083903) B12083903
theorem B1592475 : Blo 1590994 1592475 := bstep (se 1 (by rfl) ⟨1194356, by rfl⟩ : syracuseStep 1592475 = 2388713) B2388713
theorem B2387183 : Blo 1590994 2387183 := bstep (se 1 (by rfl) ⟨1790387, by rfl⟩ : syracuseStep 2387183 = 3580775) B3580775
theorem B1592815 : Blo 1590994 1592815 := bstep (se 1 (by rfl) ⟨1194611, by rfl⟩ : syracuseStep 1592815 = 2389223) B2389223
theorem B9810065 : Blo 1590994 9810065 := bstep (se 2 (by rfl) ⟨3678774, by rfl⟩ : syracuseStep 9810065 = 7357549) B7357549
theorem B4027259 : Blo 1590994 4027259 := bstep (se 1 (by rfl) ⟨3020444, by rfl⟩ : syracuseStep 4027259 = 6040889) B6040889
theorem B2421919 : Blo 1590994 2421919 := bstep (se 1 (by rfl) ⟨1816439, by rfl⟩ : syracuseStep 2421919 = 3632879) B3632879
theorem B7755539 : Blo 1590994 7755539 := bstep (se 1 (by rfl) ⟨5816654, by rfl⟩ : syracuseStep 7755539 = 11633309) B11633309
theorem B11794409 : Blo 1590994 11794409 := bstep (se 2 (by rfl) ⟨4422903, by rfl⟩ : syracuseStep 11794409 = 8845807) B8845807
theorem B2684927 : Blo 1590994 2684927 := bstep (se 1 (by rfl) ⟨2013695, by rfl⟩ : syracuseStep 2684927 = 4027391) B4027391
theorem B51623999 : Blo 1590994 51623999 := bstep (se 1 (by rfl) ⟨38717999, by rfl⟩ : syracuseStep 51623999 = 77435999) B77435999
theorem B13605191 : Blo 1590994 13605191 := bstep (se 1 (by rfl) ⟨10203893, by rfl⟩ : syracuseStep 13605191 = 20407787) B20407787
theorem B68893577 : Blo 1590994 68893577 := bstep (se 2 (by rfl) ⟨25835091, by rfl⟩ : syracuseStep 68893577 = 51670183) B51670183
theorem B25828865 : Blo 1590994 25828865 := bstep (se 2 (by rfl) ⟨9685824, by rfl⟩ : syracuseStep 25828865 = 19371649) B19371649
theorem B3678191 : Blo 1590994 3678191 := bstep (se 1 (by rfl) ⟨2758643, by rfl⟩ : syracuseStep 3678191 = 5517287) B5517287
theorem B34415999 : Blo 1590994 34415999 := bstep (se 1 (by rfl) ⟨25811999, by rfl⟩ : syracuseStep 34415999 = 51623999) B51623999
theorem B9070127 : Blo 1590994 9070127 := bstep (se 1 (by rfl) ⟨6802595, by rfl⟩ : syracuseStep 9070127 = 13605191) B13605191
theorem B1591455 : Blo 1590994 1591455 := bstep (se 1 (by rfl) ⟨1193591, by rfl⟩ : syracuseStep 1591455 = 2387183) B2387183
theorem B2452127 : Blo 1590994 2452127 := bstep (se 1 (by rfl) ⟨1839095, by rfl⟩ : syracuseStep 2452127 = 3678191) B3678191
theorem B6540043 : Blo 1590994 6540043 := bstep (se 1 (by rfl) ⟨4905032, by rfl⟩ : syracuseStep 6540043 = 9810065) B9810065
theorem B11472637 : Blo 1590994 11472637 := bstep (se 3 (by rfl) ⟨2151119, by rfl⟩ : syracuseStep 11472637 = 4302239) B4302239
theorem B2387711 : Blo 1590994 2387711 := bstep (se 1 (by rfl) ⟨1790783, by rfl⟩ : syracuseStep 2387711 = 3581567) B3581567
theorem B1789951 : Blo 1590994 1789951 := bstep (se 1 (by rfl) ⟨1342463, by rfl⟩ : syracuseStep 1789951 = 2684927) B2684927
theorem B45929051 : Blo 1590994 45929051 := bstep (se 1 (by rfl) ⟨34446788, by rfl⟩ : syracuseStep 45929051 = 68893577) B68893577
theorem B20681437 : Blo 1590994 20681437 := bstep (se 3 (by rfl) ⟨3877769, by rfl⟩ : syracuseStep 20681437 = 7755539) B7755539
theorem B5370623 : Blo 1590994 5370623 := bstep (se 1 (by rfl) ⟨4027967, by rfl⟩ : syracuseStep 5370623 = 8055935) B8055935
theorem B7263785 : Blo 1590994 7263785 := bstep (se 2 (by rfl) ⟨2723919, by rfl⟩ : syracuseStep 7263785 = 5447839) B5447839
theorem B2684839 : Blo 1590994 2684839 := bstep (se 1 (by rfl) ⟨2013629, by rfl⟩ : syracuseStep 2684839 = 4027259) B4027259
theorem B12916901 : Blo 1590994 12916901 := bstep (se 4 (by rfl) ⟨1210959, by rfl⟩ : syracuseStep 12916901 = 2421919) B2421919
theorem B7862939 : Blo 1590994 7862939 := bstep (se 1 (by rfl) ⟨5897204, by rfl⟩ : syracuseStep 7862939 = 11794409) B11794409
theorem B17219243 : Blo 1590994 17219243 := bstep (se 1 (by rfl) ⟨12914432, by rfl⟩ : syracuseStep 17219243 = 25828865) B25828865
theorem B3580415 : Blo 1590994 3580415 := bstep (se 1 (by rfl) ⟨2685311, by rfl⟩ : syracuseStep 3580415 = 5370623) B5370623
theorem B27575249 : Blo 1590994 27575249 := bstep (se 2 (by rfl) ⟨10340718, by rfl⟩ : syracuseStep 27575249 = 20681437) B20681437
theorem B4842523 : Blo 1590994 4842523 := bstep (se 1 (by rfl) ⟨3631892, by rfl⟩ : syracuseStep 4842523 = 7263785) B7263785
theorem B6046751 : Blo 1590994 6046751 := bstep (se 1 (by rfl) ⟨4535063, by rfl⟩ : syracuseStep 6046751 = 9070127) B9070127
theorem B8611267 : Blo 1590994 8611267 := bstep (se 1 (by rfl) ⟨6458450, by rfl⟩ : syracuseStep 8611267 = 12916901) B12916901
theorem B6539005 : Blo 1590994 6539005 := bstep (se 3 (by rfl) ⟨1226063, by rfl⟩ : syracuseStep 6539005 = 2452127) B2452127
theorem B15296849 : Blo 1590994 15296849 := bstep (se 2 (by rfl) ⟨5736318, by rfl⟩ : syracuseStep 15296849 = 11472637) B11472637
theorem B11479495 : Blo 1590994 11479495 := bstep (se 1 (by rfl) ⟨8609621, by rfl⟩ : syracuseStep 11479495 = 17219243) B17219243
theorem B1591807 : Blo 1590994 1591807 := bstep (se 1 (by rfl) ⟨1193855, by rfl⟩ : syracuseStep 1591807 = 2387711) B2387711
theorem B2386601 : Blo 1590994 2386601 := bstep (se 2 (by rfl) ⟨894975, by rfl⟩ : syracuseStep 2386601 = 1789951) B1789951
theorem B8720057 : Blo 1590994 8720057 := bstep (se 2 (by rfl) ⟨3270021, by rfl⟩ : syracuseStep 8720057 = 6540043) B6540043
theorem B30619367 : Blo 1590994 30619367 := bstep (se 1 (by rfl) ⟨22964525, by rfl⟩ : syracuseStep 30619367 = 45929051) B45929051
theorem B22943999 : Blo 1590994 22943999 := bstep (se 1 (by rfl) ⟨17207999, by rfl⟩ : syracuseStep 22943999 = 34415999) B34415999
theorem B5241959 : Blo 1590994 5241959 := bstep (se 1 (by rfl) ⟨3931469, by rfl⟩ : syracuseStep 5241959 = 7862939) B7862939
theorem B3579785 : Blo 1590994 3579785 := bstep (se 2 (by rfl) ⟨1342419, by rfl⟩ : syracuseStep 3579785 = 2684839) B2684839
theorem B4031167 : Blo 1590994 4031167 := bstep (se 1 (by rfl) ⟨3023375, by rfl⟩ : syracuseStep 4031167 = 6046751) B6046751
theorem B15295999 : Blo 1590994 15295999 := bstep (se 1 (by rfl) ⟨11471999, by rfl⟩ : syracuseStep 15295999 = 22943999) B22943999
theorem B1591067 : Blo 1590994 1591067 := bstep (se 1 (by rfl) ⟨1193300, by rfl⟩ : syracuseStep 1591067 = 2386601) B2386601
theorem B8718673 : Blo 1590994 8718673 := bstep (se 2 (by rfl) ⟨3269502, by rfl⟩ : syracuseStep 8718673 = 6539005) B6539005
theorem B73533997 : Blo 1590994 73533997 := bstep (se 3 (by rfl) ⟨13787624, by rfl⟩ : syracuseStep 73533997 = 27575249) B27575249
theorem B2386523 : Blo 1590994 2386523 := bstep (se 1 (by rfl) ⟨1789892, by rfl⟩ : syracuseStep 2386523 = 3579785) B3579785
theorem B2386943 : Blo 1590994 2386943 := bstep (se 1 (by rfl) ⟨1790207, by rfl⟩ : syracuseStep 2386943 = 3580415) B3580415
theorem B15305993 : Blo 1590994 15305993 := bstep (se 2 (by rfl) ⟨5739747, by rfl⟩ : syracuseStep 15305993 = 11479495) B11479495
theorem B11481689 : Blo 1590994 11481689 := bstep (se 2 (by rfl) ⟨4305633, by rfl⟩ : syracuseStep 11481689 = 8611267) B8611267
theorem B3494639 : Blo 1590994 3494639 := bstep (se 1 (by rfl) ⟨2620979, by rfl⟩ : syracuseStep 3494639 = 5241959) B5241959
theorem B5813371 : Blo 1590994 5813371 := bstep (se 1 (by rfl) ⟨4360028, by rfl⟩ : syracuseStep 5813371 = 8720057) B8720057
theorem B25826789 : Blo 1590994 25826789 := bstep (se 4 (by rfl) ⟨2421261, by rfl⟩ : syracuseStep 25826789 = 4842523) B4842523
theorem B20412911 : Blo 1590994 20412911 := bstep (se 1 (by rfl) ⟨15309683, by rfl⟩ : syracuseStep 20412911 = 30619367) B30619367
theorem B10197899 : Blo 1590994 10197899 := bstep (se 1 (by rfl) ⟨7648424, by rfl⟩ : syracuseStep 10197899 = 15296849) B15296849
theorem B11624897 : Blo 1590994 11624897 := bstep (se 2 (by rfl) ⟨4359336, by rfl⟩ : syracuseStep 11624897 = 8718673) B8718673
theorem B5374889 : Blo 1590994 5374889 := bstep (se 2 (by rfl) ⟨2015583, by rfl⟩ : syracuseStep 5374889 = 4031167) B4031167
theorem B7751161 : Blo 1590994 7751161 := bstep (se 2 (by rfl) ⟨2906685, by rfl⟩ : syracuseStep 7751161 = 5813371) B5813371
theorem B13608607 : Blo 1590994 13608607 := bstep (se 1 (by rfl) ⟨10206455, by rfl⟩ : syracuseStep 13608607 = 20412911) B20412911
theorem B1591015 : Blo 1590994 1591015 := bstep (se 1 (by rfl) ⟨1193261, by rfl⟩ : syracuseStep 1591015 = 2386523) B2386523
theorem B1591295 : Blo 1590994 1591295 := bstep (se 1 (by rfl) ⟨1193471, by rfl⟩ : syracuseStep 1591295 = 2386943) B2386943
theorem B7654459 : Blo 1590994 7654459 := bstep (se 1 (by rfl) ⟨5740844, by rfl⟩ : syracuseStep 7654459 = 11481689) B11481689
theorem B2329759 : Blo 1590994 2329759 := bstep (se 1 (by rfl) ⟨1747319, by rfl⟩ : syracuseStep 2329759 = 3494639) B3494639
theorem B98045329 : Blo 1590994 98045329 := bstep (se 2 (by rfl) ⟨36766998, by rfl⟩ : syracuseStep 98045329 = 73533997) B73533997
theorem B20394665 : Blo 1590994 20394665 := bstep (se 2 (by rfl) ⟨7647999, by rfl⟩ : syracuseStep 20394665 = 15295999) B15295999
theorem B10203995 : Blo 1590994 10203995 := bstep (se 1 (by rfl) ⟨7652996, by rfl⟩ : syracuseStep 10203995 = 15305993) B15305993
theorem B17217859 : Blo 1590994 17217859 := bstep (se 1 (by rfl) ⟨12913394, by rfl⟩ : syracuseStep 17217859 = 25826789) B25826789
theorem B6798599 : Blo 1590994 6798599 := bstep (se 1 (by rfl) ⟨5098949, by rfl⟩ : syracuseStep 6798599 = 10197899) B10197899
theorem B7749931 : Blo 1590994 7749931 := bstep (se 1 (by rfl) ⟨5812448, by rfl⟩ : syracuseStep 7749931 = 11624897) B11624897
theorem B3106345 : Blo 1590994 3106345 := bstep (se 2 (by rfl) ⟨1164879, by rfl⟩ : syracuseStep 3106345 = 2329759) B2329759
theorem B4532399 : Blo 1590994 4532399 := bstep (se 1 (by rfl) ⟨3399299, by rfl⟩ : syracuseStep 4532399 = 6798599) B6798599
theorem B22957145 : Blo 1590994 22957145 := bstep (se 2 (by rfl) ⟨8608929, by rfl⟩ : syracuseStep 22957145 = 17217859) B17217859
theorem B3583259 : Blo 1590994 3583259 := bstep (se 1 (by rfl) ⟨2687444, by rfl⟩ : syracuseStep 3583259 = 5374889) B5374889
theorem B10334881 : Blo 1590994 10334881 := bstep (se 2 (by rfl) ⟨3875580, by rfl⟩ : syracuseStep 10334881 = 7751161) B7751161
theorem B27210653 : Blo 1590994 27210653 := bstep (se 3 (by rfl) ⟨5101997, by rfl⟩ : syracuseStep 27210653 = 10203995) B10203995
theorem B13596443 : Blo 1590994 13596443 := bstep (se 1 (by rfl) ⟨10197332, by rfl⟩ : syracuseStep 13596443 = 20394665) B20394665
theorem B10205945 : Blo 1590994 10205945 := bstep (se 2 (by rfl) ⟨3827229, by rfl⟩ : syracuseStep 10205945 = 7654459) B7654459
theorem B130727105 : Blo 1590994 130727105 := bstep (se 2 (by rfl) ⟨49022664, by rfl⟩ : syracuseStep 130727105 = 98045329) B98045329
theorem B18144809 : Blo 1590994 18144809 := bstep (se 2 (by rfl) ⟨6804303, by rfl⟩ : syracuseStep 18144809 = 13608607) B13608607
theorem B13779841 : Blo 1590994 13779841 := bstep (se 2 (by rfl) ⟨5167440, by rfl⟩ : syracuseStep 13779841 = 10334881) B10334881
theorem B15304763 : Blo 1590994 15304763 := bstep (se 1 (by rfl) ⟨11478572, by rfl⟩ : syracuseStep 15304763 = 22957145) B22957145
theorem B10333241 : Blo 1590994 10333241 := bstep (se 2 (by rfl) ⟨3874965, by rfl⟩ : syracuseStep 10333241 = 7749931) B7749931
theorem B18140435 : Blo 1590994 18140435 := bstep (se 1 (by rfl) ⟨13605326, by rfl⟩ : syracuseStep 18140435 = 27210653) B27210653
theorem B9064295 : Blo 1590994 9064295 := bstep (se 1 (by rfl) ⟨6798221, by rfl⟩ : syracuseStep 9064295 = 13596443) B13596443
theorem B6803963 : Blo 1590994 6803963 := bstep (se 1 (by rfl) ⟨5102972, by rfl⟩ : syracuseStep 6803963 = 10205945) B10205945
theorem B4141793 : Blo 1590994 4141793 := bstep (se 2 (by rfl) ⟨1553172, by rfl⟩ : syracuseStep 4141793 = 3106345) B3106345
theorem B87151403 : Blo 1590994 87151403 := bstep (se 1 (by rfl) ⟨65363552, by rfl⟩ : syracuseStep 87151403 = 130727105) B130727105
theorem B2388839 : Blo 1590994 2388839 := bstep (se 1 (by rfl) ⟨1791629, by rfl⟩ : syracuseStep 2388839 = 3583259) B3583259
theorem B12096539 : Blo 1590994 12096539 := bstep (se 1 (by rfl) ⟨9072404, by rfl⟩ : syracuseStep 12096539 = 18144809) B18144809
theorem B3021599 : Blo 1590994 3021599 := bstep (se 1 (by rfl) ⟨2266199, by rfl⟩ : syracuseStep 3021599 = 4532399) B4532399
theorem B2761195 : Blo 1590994 2761195 := bstep (se 1 (by rfl) ⟨2070896, by rfl⟩ : syracuseStep 2761195 = 4141793) B4141793
theorem B12093623 : Blo 1590994 12093623 := bstep (se 1 (by rfl) ⟨9070217, by rfl⟩ : syracuseStep 12093623 = 18140435) B18140435
theorem B58100935 : Blo 1590994 58100935 := bstep (se 1 (by rfl) ⟨43575701, by rfl⟩ : syracuseStep 58100935 = 87151403) B87151403
theorem B1592559 : Blo 1590994 1592559 := bstep (se 1 (by rfl) ⟨1194419, by rfl⟩ : syracuseStep 1592559 = 2388839) B2388839
theorem B8064359 : Blo 1590994 8064359 := bstep (se 1 (by rfl) ⟨6048269, by rfl⟩ : syracuseStep 8064359 = 12096539) B12096539
theorem B10203175 : Blo 1590994 10203175 := bstep (se 1 (by rfl) ⟨7652381, by rfl⟩ : syracuseStep 10203175 = 15304763) B15304763
theorem B6042863 : Blo 1590994 6042863 := bstep (se 1 (by rfl) ⟨4532147, by rfl⟩ : syracuseStep 6042863 = 9064295) B9064295
theorem B4535975 : Blo 1590994 4535975 := bstep (se 1 (by rfl) ⟨3401981, by rfl⟩ : syracuseStep 4535975 = 6803963) B6803963
theorem B18373121 : Blo 1590994 18373121 := bstep (se 2 (by rfl) ⟨6889920, by rfl⟩ : syracuseStep 18373121 = 13779841) B13779841
theorem B2014399 : Blo 1590994 2014399 := bstep (se 1 (by rfl) ⟨1510799, by rfl⟩ : syracuseStep 2014399 = 3021599) B3021599
theorem B6888827 : Blo 1590994 6888827 := bstep (se 1 (by rfl) ⟨5166620, by rfl⟩ : syracuseStep 6888827 = 10333241) B10333241
theorem B3023983 : Blo 1590994 3023983 := bstep (se 1 (by rfl) ⟨2267987, by rfl⟩ : syracuseStep 3023983 = 4535975) B4535975
theorem B8062415 : Blo 1590994 8062415 := bstep (se 1 (by rfl) ⟨6046811, by rfl⟩ : syracuseStep 8062415 = 12093623) B12093623
theorem B12248747 : Blo 1590994 12248747 := bstep (se 1 (by rfl) ⟨9186560, by rfl⟩ : syracuseStep 12248747 = 18373121) B18373121
theorem B5376239 : Blo 1590994 5376239 := bstep (se 1 (by rfl) ⟨4032179, by rfl⟩ : syracuseStep 5376239 = 8064359) B8064359
theorem B3681593 : Blo 1590994 3681593 := bstep (se 2 (by rfl) ⟨1380597, by rfl⟩ : syracuseStep 3681593 = 2761195) B2761195
theorem B77467913 : Blo 1590994 77467913 := bstep (se 2 (by rfl) ⟨29050467, by rfl⟩ : syracuseStep 77467913 = 58100935) B58100935
theorem B4592551 : Blo 1590994 4592551 := bstep (se 1 (by rfl) ⟨3444413, by rfl⟩ : syracuseStep 4592551 = 6888827) B6888827
theorem B13604233 : Blo 1590994 13604233 := bstep (se 2 (by rfl) ⟨5101587, by rfl⟩ : syracuseStep 13604233 = 10203175) B10203175
theorem B4028575 : Blo 1590994 4028575 := bstep (se 1 (by rfl) ⟨3021431, by rfl⟩ : syracuseStep 4028575 = 6042863) B6042863
theorem B2685865 : Blo 1590994 2685865 := bstep (se 2 (by rfl) ⟨1007199, by rfl⟩ : syracuseStep 2685865 = 2014399) B2014399
theorem B5374943 : Blo 1590994 5374943 := bstep (se 1 (by rfl) ⟨4031207, by rfl⟩ : syracuseStep 5374943 = 8062415) B8062415
theorem B3581153 : Blo 1590994 3581153 := bstep (se 2 (by rfl) ⟨1342932, by rfl⟩ : syracuseStep 3581153 = 2685865) B2685865
theorem B4031977 : Blo 1590994 4031977 := bstep (se 2 (by rfl) ⟨1511991, by rfl⟩ : syracuseStep 4031977 = 3023983) B3023983
theorem B18138977 : Blo 1590994 18138977 := bstep (se 2 (by rfl) ⟨6802116, by rfl⟩ : syracuseStep 18138977 = 13604233) B13604233
theorem B51645275 : Blo 1590994 51645275 := bstep (se 1 (by rfl) ⟨38733956, by rfl⟩ : syracuseStep 51645275 = 77467913) B77467913
theorem B6123401 : Blo 1590994 6123401 := bstep (se 2 (by rfl) ⟨2296275, by rfl⟩ : syracuseStep 6123401 = 4592551) B4592551
theorem B3584159 : Blo 1590994 3584159 := bstep (se 1 (by rfl) ⟨2688119, by rfl⟩ : syracuseStep 3584159 = 5376239) B5376239
theorem B5371433 : Blo 1590994 5371433 := bstep (se 2 (by rfl) ⟨2014287, by rfl⟩ : syracuseStep 5371433 = 4028575) B4028575
theorem B39270325 : Blo 1590994 39270325 := bstep (se 5 (by rfl) ⟨1840796, by rfl⟩ : syracuseStep 39270325 = 3681593) B3681593
theorem B8165831 : Blo 1590994 8165831 := bstep (se 1 (by rfl) ⟨6124373, by rfl⟩ : syracuseStep 8165831 = 12248747) B12248747
theorem B3580955 : Blo 1590994 3580955 := bstep (se 1 (by rfl) ⟨2685716, by rfl⟩ : syracuseStep 3580955 = 5371433) B5371433
theorem B21775549 : Blo 1590994 21775549 := bstep (se 3 (by rfl) ⟨4082915, by rfl⟩ : syracuseStep 21775549 = 8165831) B8165831
theorem B12092651 : Blo 1590994 12092651 := bstep (se 1 (by rfl) ⟨9069488, by rfl⟩ : syracuseStep 12092651 = 18138977) B18138977
theorem B5375969 : Blo 1590994 5375969 := bstep (se 2 (by rfl) ⟨2015988, by rfl⟩ : syracuseStep 5375969 = 4031977) B4031977
theorem B4082267 : Blo 1590994 4082267 := bstep (se 1 (by rfl) ⟨3061700, by rfl⟩ : syracuseStep 4082267 = 6123401) B6123401
theorem B3583295 : Blo 1590994 3583295 := bstep (se 1 (by rfl) ⟨2687471, by rfl⟩ : syracuseStep 3583295 = 5374943) B5374943
theorem B2387435 : Blo 1590994 2387435 := bstep (se 1 (by rfl) ⟨1790576, by rfl⟩ : syracuseStep 2387435 = 3581153) B3581153
theorem B52360433 : Blo 1590994 52360433 := bstep (se 2 (by rfl) ⟨19635162, by rfl⟩ : syracuseStep 52360433 = 39270325) B39270325
theorem B2389439 : Blo 1590994 2389439 := bstep (se 1 (by rfl) ⟨1792079, by rfl⟩ : syracuseStep 2389439 = 3584159) B3584159
theorem B34430183 : Blo 1590994 34430183 := bstep (se 1 (by rfl) ⟨25822637, by rfl⟩ : syracuseStep 34430183 = 51645275) B51645275
theorem B8061767 : Blo 1590994 8061767 := bstep (se 1 (by rfl) ⟨6046325, by rfl⟩ : syracuseStep 8061767 = 12092651) B12092651
theorem B34906955 : Blo 1590994 34906955 := bstep (se 1 (by rfl) ⟨26180216, by rfl⟩ : syracuseStep 34906955 = 52360433) B52360433
theorem B29034065 : Blo 1590994 29034065 := bstep (se 2 (by rfl) ⟨10887774, by rfl⟩ : syracuseStep 29034065 = 21775549) B21775549
theorem B2721511 : Blo 1590994 2721511 := bstep (se 1 (by rfl) ⟨2041133, by rfl⟩ : syracuseStep 2721511 = 4082267) B4082267
theorem B1591623 : Blo 1590994 1591623 := bstep (se 1 (by rfl) ⟨1193717, by rfl⟩ : syracuseStep 1591623 = 2387435) B2387435
theorem B2387303 : Blo 1590994 2387303 := bstep (se 1 (by rfl) ⟨1790477, by rfl⟩ : syracuseStep 2387303 = 3580955) B3580955
theorem B1592959 : Blo 1590994 1592959 := bstep (se 1 (by rfl) ⟨1194719, by rfl⟩ : syracuseStep 1592959 = 2389439) B2389439
theorem B3583979 : Blo 1590994 3583979 := bstep (se 1 (by rfl) ⟨2687984, by rfl⟩ : syracuseStep 3583979 = 5375969) B5375969
theorem B2388863 : Blo 1590994 2388863 := bstep (se 1 (by rfl) ⟨1791647, by rfl⟩ : syracuseStep 2388863 = 3583295) B3583295
theorem B22953455 : Blo 1590994 22953455 := bstep (se 1 (by rfl) ⟨17215091, by rfl⟩ : syracuseStep 22953455 = 34430183) B34430183
theorem B5374511 : Blo 1590994 5374511 := bstep (se 1 (by rfl) ⟨4030883, by rfl⟩ : syracuseStep 5374511 = 8061767) B8061767
theorem B1591535 : Blo 1590994 1591535 := bstep (se 1 (by rfl) ⟨1193651, by rfl⟩ : syracuseStep 1591535 = 2387303) B2387303
theorem B1592575 : Blo 1590994 1592575 := bstep (se 1 (by rfl) ⟨1194431, by rfl⟩ : syracuseStep 1592575 = 2388863) B2388863
theorem B2389319 : Blo 1590994 2389319 := bstep (se 1 (by rfl) ⟨1791989, by rfl⟩ : syracuseStep 2389319 = 3583979) B3583979
theorem B19356043 : Blo 1590994 19356043 := bstep (se 1 (by rfl) ⟨14517032, by rfl⟩ : syracuseStep 19356043 = 29034065) B29034065
theorem B93085213 : Blo 1590994 93085213 := bstep (se 3 (by rfl) ⟨17453477, by rfl⟩ : syracuseStep 93085213 = 34906955) B34906955
theorem B3628681 : Blo 1590994 3628681 := bstep (se 2 (by rfl) ⟨1360755, by rfl⟩ : syracuseStep 3628681 = 2721511) B2721511
theorem B15302303 : Blo 1590994 15302303 := bstep (se 1 (by rfl) ⟨11476727, by rfl⟩ : syracuseStep 15302303 = 22953455) B22953455
theorem B10201535 : Blo 1590994 10201535 := bstep (se 1 (by rfl) ⟨7651151, by rfl⟩ : syracuseStep 10201535 = 15302303) B15302303
theorem B3583007 : Blo 1590994 3583007 := bstep (se 1 (by rfl) ⟨2687255, by rfl⟩ : syracuseStep 3583007 = 5374511) B5374511
theorem B25808057 : Blo 1590994 25808057 := bstep (se 2 (by rfl) ⟨9678021, by rfl⟩ : syracuseStep 25808057 = 19356043) B19356043
theorem B19352965 : Blo 1590994 19352965 := bstep (se 4 (by rfl) ⟨1814340, by rfl⟩ : syracuseStep 19352965 = 3628681) B3628681
theorem B1592879 : Blo 1590994 1592879 := bstep (se 1 (by rfl) ⟨1194659, by rfl⟩ : syracuseStep 1592879 = 2389319) B2389319
theorem B124113617 : Blo 1590994 124113617 := bstep (se 2 (by rfl) ⟨46542606, by rfl⟩ : syracuseStep 124113617 = 93085213) B93085213
theorem B6801023 : Blo 1590994 6801023 := bstep (se 1 (by rfl) ⟨5100767, by rfl⟩ : syracuseStep 6801023 = 10201535) B10201535
theorem B17205371 : Blo 1590994 17205371 := bstep (se 1 (by rfl) ⟨12904028, by rfl⟩ : syracuseStep 17205371 = 25808057) B25808057
theorem B82742411 : Blo 1590994 82742411 := bstep (se 1 (by rfl) ⟨62056808, by rfl⟩ : syracuseStep 82742411 = 124113617) B124113617
theorem B2388671 : Blo 1590994 2388671 := bstep (se 1 (by rfl) ⟨1791503, by rfl⟩ : syracuseStep 2388671 = 3583007) B3583007
theorem B25803953 : Blo 1590994 25803953 := bstep (se 2 (by rfl) ⟨9676482, by rfl⟩ : syracuseStep 25803953 = 19352965) B19352965
theorem B11470247 : Blo 1590994 11470247 := bstep (se 1 (by rfl) ⟨8602685, by rfl⟩ : syracuseStep 11470247 = 17205371) B17205371
theorem B1592447 : Blo 1590994 1592447 := bstep (se 1 (by rfl) ⟨1194335, by rfl⟩ : syracuseStep 1592447 = 2388671) B2388671
theorem B55161607 : Blo 1590994 55161607 := bstep (se 1 (by rfl) ⟨41371205, by rfl⟩ : syracuseStep 55161607 = 82742411) B82742411
theorem B18136061 : Blo 1590994 18136061 := bstep (se 3 (by rfl) ⟨3400511, by rfl⟩ : syracuseStep 18136061 = 6801023) B6801023
theorem B17202635 : Blo 1590994 17202635 := bstep (se 1 (by rfl) ⟨12901976, by rfl⟩ : syracuseStep 17202635 = 25803953) B25803953
theorem B73548809 : Blo 1590994 73548809 := bstep (se 2 (by rfl) ⟨27580803, by rfl⟩ : syracuseStep 73548809 = 55161607) B55161607
theorem B7646831 : Blo 1590994 7646831 := bstep (se 1 (by rfl) ⟨5735123, by rfl⟩ : syracuseStep 7646831 = 11470247) B11470247
theorem B12090707 : Blo 1590994 12090707 := bstep (se 1 (by rfl) ⟨9068030, by rfl⟩ : syracuseStep 12090707 = 18136061) B18136061
theorem B11468423 : Blo 1590994 11468423 := bstep (se 1 (by rfl) ⟨8601317, by rfl⟩ : syracuseStep 11468423 = 17202635) B17202635
theorem B30582461 : Blo 1590994 30582461 := bstep (se 3 (by rfl) ⟨5734211, by rfl⟩ : syracuseStep 30582461 = 11468423) B11468423
theorem B5097887 : Blo 1590994 5097887 := bstep (se 1 (by rfl) ⟨3823415, by rfl⟩ : syracuseStep 5097887 = 7646831) B7646831
theorem B49032539 : Blo 1590994 49032539 := bstep (se 1 (by rfl) ⟨36774404, by rfl⟩ : syracuseStep 49032539 = 73548809) B73548809
theorem B8060471 : Blo 1590994 8060471 := bstep (se 1 (by rfl) ⟨6045353, by rfl⟩ : syracuseStep 8060471 = 12090707) B12090707
theorem B32688359 : Blo 1590994 32688359 := bstep (se 1 (by rfl) ⟨24516269, by rfl⟩ : syracuseStep 32688359 = 49032539) B49032539
theorem B20388307 : Blo 1590994 20388307 := bstep (se 1 (by rfl) ⟨15291230, by rfl⟩ : syracuseStep 20388307 = 30582461) B30582461
theorem B3398591 : Blo 1590994 3398591 := bstep (se 1 (by rfl) ⟨2548943, by rfl⟩ : syracuseStep 3398591 = 5097887) B5097887
theorem B5373647 : Blo 1590994 5373647 := bstep (se 1 (by rfl) ⟨4030235, by rfl⟩ : syracuseStep 5373647 = 8060471) B8060471
theorem B21792239 : Blo 1590994 21792239 := bstep (se 1 (by rfl) ⟨16344179, by rfl⟩ : syracuseStep 21792239 = 32688359) B32688359
theorem B3582431 : Blo 1590994 3582431 := bstep (se 1 (by rfl) ⟨2686823, by rfl⟩ : syracuseStep 3582431 = 5373647) B5373647
theorem B27184409 : Blo 1590994 27184409 := bstep (se 2 (by rfl) ⟨10194153, by rfl⟩ : syracuseStep 27184409 = 20388307) B20388307
theorem B2265727 : Blo 1590994 2265727 := bstep (se 1 (by rfl) ⟨1699295, by rfl⟩ : syracuseStep 2265727 = 3398591) B3398591
theorem B18122939 : Blo 1590994 18122939 := bstep (se 1 (by rfl) ⟨13592204, by rfl⟩ : syracuseStep 18122939 = 27184409) B27184409
theorem B14528159 : Blo 1590994 14528159 := bstep (se 1 (by rfl) ⟨10896119, by rfl⟩ : syracuseStep 14528159 = 21792239) B21792239
theorem B2388287 : Blo 1590994 2388287 := bstep (se 1 (by rfl) ⟨1791215, by rfl⟩ : syracuseStep 2388287 = 3582431) B3582431
theorem B3020969 : Blo 1590994 3020969 := bstep (se 2 (by rfl) ⟨1132863, by rfl⟩ : syracuseStep 3020969 = 2265727) B2265727
theorem B9685439 : Blo 1590994 9685439 := bstep (se 1 (by rfl) ⟨7264079, by rfl⟩ : syracuseStep 9685439 = 14528159) B14528159
theorem B1592191 : Blo 1590994 1592191 := bstep (se 1 (by rfl) ⟨1194143, by rfl⟩ : syracuseStep 1592191 = 2388287) B2388287
theorem B2013979 : Blo 1590994 2013979 := bstep (se 1 (by rfl) ⟨1510484, by rfl⟩ : syracuseStep 2013979 = 3020969) B3020969
theorem B12081959 : Blo 1590994 12081959 := bstep (se 1 (by rfl) ⟨9061469, by rfl⟩ : syracuseStep 12081959 = 18122939) B18122939
theorem B6456959 : Blo 1590994 6456959 := bstep (se 1 (by rfl) ⟨4842719, by rfl⟩ : syracuseStep 6456959 = 9685439) B9685439
theorem B8054639 : Blo 1590994 8054639 := bstep (se 1 (by rfl) ⟨6040979, by rfl⟩ : syracuseStep 8054639 = 12081959) B12081959
theorem B2685305 : Blo 1590994 2685305 := bstep (se 2 (by rfl) ⟨1006989, by rfl⟩ : syracuseStep 2685305 = 2013979) B2013979
theorem B4304639 : Blo 1590994 4304639 := bstep (se 1 (by rfl) ⟨3228479, by rfl⟩ : syracuseStep 4304639 = 6456959) B6456959
theorem B5369759 : Blo 1590994 5369759 := bstep (se 1 (by rfl) ⟨4027319, by rfl⟩ : syracuseStep 5369759 = 8054639) B8054639
theorem B1790203 : Blo 1590994 1790203 := bstep (se 1 (by rfl) ⟨1342652, by rfl⟩ : syracuseStep 1790203 = 2685305) B2685305
theorem B2869759 : Blo 1590994 2869759 := bstep (se 1 (by rfl) ⟨2152319, by rfl⟩ : syracuseStep 2869759 = 4304639) B4304639
theorem B2386937 : Blo 1590994 2386937 := bstep (se 2 (by rfl) ⟨895101, by rfl⟩ : syracuseStep 2386937 = 1790203) B1790203
theorem B3579839 : Blo 1590994 3579839 := bstep (se 1 (by rfl) ⟨2684879, by rfl⟩ : syracuseStep 3579839 = 5369759) B5369759
theorem B3826345 : Blo 1590994 3826345 := bstep (se 2 (by rfl) ⟨1434879, by rfl⟩ : syracuseStep 3826345 = 2869759) B2869759
theorem B1591291 : Blo 1590994 1591291 := bstep (se 1 (by rfl) ⟨1193468, by rfl⟩ : syracuseStep 1591291 = 2386937) B2386937
theorem B2386559 : Blo 1590994 2386559 := bstep (se 1 (by rfl) ⟨1789919, by rfl⟩ : syracuseStep 2386559 = 3579839) B3579839
theorem B1591039 : Blo 1590994 1591039 := bstep (se 1 (by rfl) ⟨1193279, by rfl⟩ : syracuseStep 1591039 = 2386559) B2386559
theorem B5101793 : Blo 1590994 5101793 := bstep (se 2 (by rfl) ⟨1913172, by rfl⟩ : syracuseStep 5101793 = 3826345) B3826345
theorem B3401195 : Blo 1590994 3401195 := bstep (se 1 (by rfl) ⟨2550896, by rfl⟩ : syracuseStep 3401195 = 5101793) B5101793
theorem B9069853 : Blo 1590994 9069853 := bstep (se 3 (by rfl) ⟨1700597, by rfl⟩ : syracuseStep 9069853 = 3401195) B3401195
theorem B12093137 : Blo 1590994 12093137 := bstep (se 2 (by rfl) ⟨4534926, by rfl⟩ : syracuseStep 12093137 = 9069853) B9069853
theorem B8062091 : Blo 1590994 8062091 := bstep (se 1 (by rfl) ⟨6046568, by rfl⟩ : syracuseStep 8062091 = 12093137) B12093137
theorem B5374727 : Blo 1590994 5374727 := bstep (se 1 (by rfl) ⟨4031045, by rfl⟩ : syracuseStep 5374727 = 8062091) B8062091
theorem B3583151 : Blo 1590994 3583151 := bstep (se 1 (by rfl) ⟨2687363, by rfl⟩ : syracuseStep 3583151 = 5374727) B5374727
theorem B2388767 : Blo 1590994 2388767 := bstep (se 1 (by rfl) ⟨1791575, by rfl⟩ : syracuseStep 2388767 = 3583151) B3583151
theorem B1592511 : Blo 1590994 1592511 := bstep (se 1 (by rfl) ⟨1194383, by rfl⟩ : syracuseStep 1592511 = 2388767) B2388767

theorem C0 (j : ℕ) (h1 : 397748 ≤ j) (h2 : j ≤ 398247) : Blo 1590994 (4 * j + 3) := by
  interval_cases j
  · exact B1590995
  · exact B1590999
  · exact B1591003
  · exact B1591007
  · exact B1591011
  · exact B1591015
  · exact B1591019
  · exact B1591023
  · exact B1591027
  · exact B1591031
  · exact B1591035
  · exact B1591039
  · exact B1591043
  · exact B1591047
  · exact B1591051
  · exact B1591055
  · exact B1591059
  · exact B1591063
  · exact B1591067
  · exact B1591071
  · exact B1591075
  · exact B1591079
  · exact B1591083
  · exact B1591087
  · exact B1591091
  · exact B1591095
  · exact B1591099
  · exact B1591103
  · exact B1591107
  · exact B1591111
  · exact B1591115
  · exact B1591119
  · exact B1591123
  · exact B1591127
  · exact B1591131
  · exact B1591135
  · exact B1591139
  · exact B1591143
  · exact B1591147
  · exact B1591151
  · exact B1591155
  · exact B1591159
  · exact B1591163
  · exact B1591167
  · exact B1591171
  · exact B1591175
  · exact B1591179
  · exact B1591183
  · exact B1591187
  · exact B1591191
  · exact B1591195
  · exact B1591199
  · exact B1591203
  · exact B1591207
  · exact B1591211
  · exact B1591215
  · exact B1591219
  · exact B1591223
  · exact B1591227
  · exact B1591231
  · exact B1591235
  · exact B1591239
  · exact B1591243
  · exact B1591247
  · exact B1591251
  · exact B1591255
  · exact B1591259
  · exact B1591263
  · exact B1591267
  · exact B1591271
  · exact B1591275
  · exact B1591279
  · exact B1591283
  · exact B1591287
  · exact B1591291
  · exact B1591295
  · exact B1591299
  · exact B1591303
  · exact B1591307
  · exact B1591311
  · exact B1591315
  · exact B1591319
  · exact B1591323
  · exact B1591327
  · exact B1591331
  · exact B1591335
  · exact B1591339
  · exact B1591343
  · exact B1591347
  · exact B1591351
  · exact B1591355
  · exact B1591359
  · exact B1591363
  · exact B1591367
  · exact B1591371
  · exact B1591375
  · exact B1591379
  · exact B1591383
  · exact B1591387
  · exact B1591391
  · exact B1591395
  · exact B1591399
  · exact B1591403
  · exact B1591407
  · exact B1591411
  · exact B1591415
  · exact B1591419
  · exact B1591423
  · exact B1591427
  · exact B1591431
  · exact B1591435
  · exact B1591439
  · exact B1591443
  · exact B1591447
  · exact B1591451
  · exact B1591455
  · exact B1591459
  · exact B1591463
  · exact B1591467
  · exact B1591471
  · exact B1591475
  · exact B1591479
  · exact B1591483
  · exact B1591487
  · exact B1591491
  · exact B1591495
  · exact B1591499
  · exact B1591503
  · exact B1591507
  · exact B1591511
  · exact B1591515
  · exact B1591519
  · exact B1591523
  · exact B1591527
  · exact B1591531
  · exact B1591535
  · exact B1591539
  · exact B1591543
  · exact B1591547
  · exact B1591551
  · exact B1591555
  · exact B1591559
  · exact B1591563
  · exact B1591567
  · exact B1591571
  · exact B1591575
  · exact B1591579
  · exact B1591583
  · exact B1591587
  · exact B1591591
  · exact B1591595
  · exact B1591599
  · exact B1591603
  · exact B1591607
  · exact B1591611
  · exact B1591615
  · exact B1591619
  · exact B1591623
  · exact B1591627
  · exact B1591631
  · exact B1591635
  · exact B1591639
  · exact B1591643
  · exact B1591647
  · exact B1591651
  · exact B1591655
  · exact B1591659
  · exact B1591663
  · exact B1591667
  · exact B1591671
  · exact B1591675
  · exact B1591679
  · exact B1591683
  · exact B1591687
  · exact B1591691
  · exact B1591695
  · exact B1591699
  · exact B1591703
  · exact B1591707
  · exact B1591711
  · exact B1591715
  · exact B1591719
  · exact B1591723
  · exact B1591727
  · exact B1591731
  · exact B1591735
  · exact B1591739
  · exact B1591743
  · exact B1591747
  · exact B1591751
  · exact B1591755
  · exact B1591759
  · exact B1591763
  · exact B1591767
  · exact B1591771
  · exact B1591775
  · exact B1591779
  · exact B1591783
  · exact B1591787
  · exact B1591791
  · exact B1591795
  · exact B1591799
  · exact B1591803
  · exact B1591807
  · exact B1591811
  · exact B1591815
  · exact B1591819
  · exact B1591823
  · exact B1591827
  · exact B1591831
  · exact B1591835
  · exact B1591839
  · exact B1591843
  · exact B1591847
  · exact B1591851
  · exact B1591855
  · exact B1591859
  · exact B1591863
  · exact B1591867
  · exact B1591871
  · exact B1591875
  · exact B1591879
  · exact B1591883
  · exact B1591887
  · exact B1591891
  · exact B1591895
  · exact B1591899
  · exact B1591903
  · exact B1591907
  · exact B1591911
  · exact B1591915
  · exact B1591919
  · exact B1591923
  · exact B1591927
  · exact B1591931
  · exact B1591935
  · exact B1591939
  · exact B1591943
  · exact B1591947
  · exact B1591951
  · exact B1591955
  · exact B1591959
  · exact B1591963
  · exact B1591967
  · exact B1591971
  · exact B1591975
  · exact B1591979
  · exact B1591983
  · exact B1591987
  · exact B1591991
  · exact B1591995
  · exact B1591999
  · exact B1592003
  · exact B1592007
  · exact B1592011
  · exact B1592015
  · exact B1592019
  · exact B1592023
  · exact B1592027
  · exact B1592031
  · exact B1592035
  · exact B1592039
  · exact B1592043
  · exact B1592047
  · exact B1592051
  · exact B1592055
  · exact B1592059
  · exact B1592063
  · exact B1592067
  · exact B1592071
  · exact B1592075
  · exact B1592079
  · exact B1592083
  · exact B1592087
  · exact B1592091
  · exact B1592095
  · exact B1592099
  · exact B1592103
  · exact B1592107
  · exact B1592111
  · exact B1592115
  · exact B1592119
  · exact B1592123
  · exact B1592127
  · exact B1592131
  · exact B1592135
  · exact B1592139
  · exact B1592143
  · exact B1592147
  · exact B1592151
  · exact B1592155
  · exact B1592159
  · exact B1592163
  · exact B1592167
  · exact B1592171
  · exact B1592175
  · exact B1592179
  · exact B1592183
  · exact B1592187
  · exact B1592191
  · exact B1592195
  · exact B1592199
  · exact B1592203
  · exact B1592207
  · exact B1592211
  · exact B1592215
  · exact B1592219
  · exact B1592223
  · exact B1592227
  · exact B1592231
  · exact B1592235
  · exact B1592239
  · exact B1592243
  · exact B1592247
  · exact B1592251
  · exact B1592255
  · exact B1592259
  · exact B1592263
  · exact B1592267
  · exact B1592271
  · exact B1592275
  · exact B1592279
  · exact B1592283
  · exact B1592287
  · exact B1592291
  · exact B1592295
  · exact B1592299
  · exact B1592303
  · exact B1592307
  · exact B1592311
  · exact B1592315
  · exact B1592319
  · exact B1592323
  · exact B1592327
  · exact B1592331
  · exact B1592335
  · exact B1592339
  · exact B1592343
  · exact B1592347
  · exact B1592351
  · exact B1592355
  · exact B1592359
  · exact B1592363
  · exact B1592367
  · exact B1592371
  · exact B1592375
  · exact B1592379
  · exact B1592383
  · exact B1592387
  · exact B1592391
  · exact B1592395
  · exact B1592399
  · exact B1592403
  · exact B1592407
  · exact B1592411
  · exact B1592415
  · exact B1592419
  · exact B1592423
  · exact B1592427
  · exact B1592431
  · exact B1592435
  · exact B1592439
  · exact B1592443
  · exact B1592447
  · exact B1592451
  · exact B1592455
  · exact B1592459
  · exact B1592463
  · exact B1592467
  · exact B1592471
  · exact B1592475
  · exact B1592479
  · exact B1592483
  · exact B1592487
  · exact B1592491
  · exact B1592495
  · exact B1592499
  · exact B1592503
  · exact B1592507
  · exact B1592511
  · exact B1592515
  · exact B1592519
  · exact B1592523
  · exact B1592527
  · exact B1592531
  · exact B1592535
  · exact B1592539
  · exact B1592543
  · exact B1592547
  · exact B1592551
  · exact B1592555
  · exact B1592559
  · exact B1592563
  · exact B1592567
  · exact B1592571
  · exact B1592575
  · exact B1592579
  · exact B1592583
  · exact B1592587
  · exact B1592591
  · exact B1592595
  · exact B1592599
  · exact B1592603
  · exact B1592607
  · exact B1592611
  · exact B1592615
  · exact B1592619
  · exact B1592623
  · exact B1592627
  · exact B1592631
  · exact B1592635
  · exact B1592639
  · exact B1592643
  · exact B1592647
  · exact B1592651
  · exact B1592655
  · exact B1592659
  · exact B1592663
  · exact B1592667
  · exact B1592671
  · exact B1592675
  · exact B1592679
  · exact B1592683
  · exact B1592687
  · exact B1592691
  · exact B1592695
  · exact B1592699
  · exact B1592703
  · exact B1592707
  · exact B1592711
  · exact B1592715
  · exact B1592719
  · exact B1592723
  · exact B1592727
  · exact B1592731
  · exact B1592735
  · exact B1592739
  · exact B1592743
  · exact B1592747
  · exact B1592751
  · exact B1592755
  · exact B1592759
  · exact B1592763
  · exact B1592767
  · exact B1592771
  · exact B1592775
  · exact B1592779
  · exact B1592783
  · exact B1592787
  · exact B1592791
  · exact B1592795
  · exact B1592799
  · exact B1592803
  · exact B1592807
  · exact B1592811
  · exact B1592815
  · exact B1592819
  · exact B1592823
  · exact B1592827
  · exact B1592831
  · exact B1592835
  · exact B1592839
  · exact B1592843
  · exact B1592847
  · exact B1592851
  · exact B1592855
  · exact B1592859
  · exact B1592863
  · exact B1592867
  · exact B1592871
  · exact B1592875
  · exact B1592879
  · exact B1592883
  · exact B1592887
  · exact B1592891
  · exact B1592895
  · exact B1592899
  · exact B1592903
  · exact B1592907
  · exact B1592911
  · exact B1592915
  · exact B1592919
  · exact B1592923
  · exact B1592927
  · exact B1592931
  · exact B1592935
  · exact B1592939
  · exact B1592943
  · exact B1592947
  · exact B1592951
  · exact B1592955
  · exact B1592959
  · exact B1592963
  · exact B1592967
  · exact B1592971
  · exact B1592975
  · exact B1592979
  · exact B1592983
  · exact B1592987
  · exact B1592991

theorem solution (m : ℕ) (hlo : 1590994 ≤ m) (hhi : m ≤ 1592994) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 397748 ≤ j := by omega
    have hj2 : j ≤ 398247 := by omega
    have hb : Blo 1590994 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
