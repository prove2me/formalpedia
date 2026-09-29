-- Prove2me | solution 1 for syracuse_descends_range_582814_583287
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:48:41.522881+00:00
-- url     : https://prove2.me/submissions/f0e16d3a-0af1-45f1-89a2-4c054babc98f

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


theorem B874517 : Blo 582814 874517 := bbase (se 6 (by rfl) ⟨20496, by rfl⟩ : syracuseStep 874517 = 40993) (by norm_num)
theorem B874541 : Blo 582814 874541 := bbase (se 3 (by rfl) ⟨163976, by rfl⟩ : syracuseStep 874541 = 327953) (by norm_num)
theorem B1660981 : Blo 582814 1660981 := bbase (se 5 (by rfl) ⟨77858, by rfl⟩ : syracuseStep 1660981 = 155717) (by norm_num)
theorem B874565 : Blo 582814 874565 := bbase (se 4 (by rfl) ⟨81990, by rfl⟩ : syracuseStep 874565 = 163981) (by norm_num)
theorem B874589 : Blo 582814 874589 := bbase (se 3 (by rfl) ⟨163985, by rfl⟩ : syracuseStep 874589 = 327971) (by norm_num)
theorem B997469 : Blo 582814 997469 := bbase (se 3 (by rfl) ⟨187025, by rfl⟩ : syracuseStep 997469 = 374051) (by norm_num)
theorem B874613 : Blo 582814 874613 := bbase (se 5 (by rfl) ⟨40997, by rfl⟩ : syracuseStep 874613 = 81995) (by norm_num)
theorem B1968245 : Blo 582814 1968245 := bbase (se 5 (by rfl) ⟨92261, by rfl⟩ : syracuseStep 1968245 = 184523) (by norm_num)
theorem B874637 : Blo 582814 874637 := bbase (se 3 (by rfl) ⟨163994, by rfl⟩ : syracuseStep 874637 = 327989) (by norm_num)
theorem B700573 : Blo 582814 700573 := bbase (se 3 (by rfl) ⟨131357, by rfl⟩ : syracuseStep 700573 = 262715) (by norm_num)
theorem B1181861 : Blo 582814 1181861 := bbase (se 4 (by rfl) ⟨110799, by rfl⟩ : syracuseStep 1181861 = 221599) (by norm_num)
theorem B874661 : Blo 582814 874661 := bbase (se 4 (by rfl) ⟨81999, by rfl⟩ : syracuseStep 874661 = 163999) (by norm_num)
theorem B874685 : Blo 582814 874685 := bbase (se 3 (by rfl) ⟨164003, by rfl⟩ : syracuseStep 874685 = 328007) (by norm_num)
theorem B934085 : Blo 582814 934085 := bbase (se 4 (by rfl) ⟨87570, by rfl⟩ : syracuseStep 934085 = 175141) (by norm_num)
theorem B874709 : Blo 582814 874709 := bbase (se 7 (by rfl) ⟨10250, by rfl⟩ : syracuseStep 874709 = 20501) (by norm_num)
theorem B874733 : Blo 582814 874733 := bbase (se 3 (by rfl) ⟨164012, by rfl⟩ : syracuseStep 874733 = 328025) (by norm_num)
theorem B874757 : Blo 582814 874757 := bbase (se 4 (by rfl) ⟨82008, by rfl⟩ : syracuseStep 874757 = 164017) (by norm_num)
theorem B874781 : Blo 582814 874781 := bbase (se 3 (by rfl) ⟨164021, by rfl⟩ : syracuseStep 874781 = 328043) (by norm_num)
theorem B2951477 : Blo 582814 2951477 := bbase (se 5 (by rfl) ⟨138350, by rfl⟩ : syracuseStep 2951477 = 276701) (by norm_num)
theorem B874805 : Blo 582814 874805 := bbase (se 5 (by rfl) ⟨41006, by rfl⟩ : syracuseStep 874805 = 82013) (by norm_num)
theorem B655681 : Blo 582814 655681 := bbase (se 2 (by rfl) ⟨245880, by rfl⟩ : syracuseStep 655681 = 491761) (by norm_num)
theorem B874829 : Blo 582814 874829 := bbase (se 3 (by rfl) ⟨164030, by rfl⟩ : syracuseStep 874829 = 328061) (by norm_num)
theorem B655717 : Blo 582814 655717 := bbase (se 4 (by rfl) ⟨61473, by rfl⟩ : syracuseStep 655717 = 122947) (by norm_num)
theorem B874853 : Blo 582814 874853 := bbase (se 4 (by rfl) ⟨82017, by rfl⟩ : syracuseStep 874853 = 164035) (by norm_num)
theorem B1245557 : Blo 582814 1245557 := bbase (se 5 (by rfl) ⟨58385, by rfl⟩ : syracuseStep 1245557 = 116771) (by norm_num)
theorem B1245565 : Blo 582814 1245565 := bbase (se 3 (by rfl) ⟨233543, by rfl⟩ : syracuseStep 1245565 = 467087) (by norm_num)
theorem B874877 : Blo 582814 874877 := bbase (se 3 (by rfl) ⟨164039, by rfl⟩ : syracuseStep 874877 = 328079) (by norm_num)
theorem B655753 : Blo 582814 655753 := bbase (se 2 (by rfl) ⟨245907, by rfl⟩ : syracuseStep 655753 = 491815) (by norm_num)
theorem B737677 : Blo 582814 737677 := bbase (se 3 (by rfl) ⟨138314, by rfl⟩ : syracuseStep 737677 = 276629) (by norm_num)
theorem B874901 : Blo 582814 874901 := bbase (se 6 (by rfl) ⟨20505, by rfl⟩ : syracuseStep 874901 = 41011) (by norm_num)
theorem B655789 : Blo 582814 655789 := bbase (se 3 (by rfl) ⟨122960, by rfl⟩ : syracuseStep 655789 = 245921) (by norm_num)
theorem B747949 : Blo 582814 747949 := bbase (se 3 (by rfl) ⟨140240, by rfl⟩ : syracuseStep 747949 = 280481) (by norm_num)
theorem B874925 : Blo 582814 874925 := bbase (se 3 (by rfl) ⟨164048, by rfl⟩ : syracuseStep 874925 = 328097) (by norm_num)
theorem B655825 : Blo 582814 655825 := bbase (se 2 (by rfl) ⟨245934, by rfl⟩ : syracuseStep 655825 = 491869) (by norm_num)
theorem B655861 : Blo 582814 655861 := bbase (se 5 (by rfl) ⟨30743, by rfl⟩ : syracuseStep 655861 = 61487) (by norm_num)
theorem B983549 : Blo 582814 983549 := bbase (se 3 (by rfl) ⟨184415, by rfl⟩ : syracuseStep 983549 = 368831) (by norm_num)
theorem B10641941 : Blo 582814 10641941 := bbase (se 6 (by rfl) ⟨249420, by rfl⟩ : syracuseStep 10641941 = 498841) (by norm_num)
theorem B655897 : Blo 582814 655897 := bbase (se 2 (by rfl) ⟨245961, by rfl⟩ : syracuseStep 655897 = 491923) (by norm_num)
theorem B737849 : Blo 582814 737849 := bbase (se 2 (by rfl) ⟨276693, by rfl⟩ : syracuseStep 737849 = 553387) (by norm_num)
theorem B655933 : Blo 582814 655933 := bbase (se 3 (by rfl) ⟨122987, by rfl⟩ : syracuseStep 655933 = 245975) (by norm_num)
theorem B655969 : Blo 582814 655969 := bbase (se 2 (by rfl) ⟨245988, by rfl⟩ : syracuseStep 655969 = 491977) (by norm_num)
theorem B737905 : Blo 582814 737905 := bbase (se 2 (by rfl) ⟨276714, by rfl⟩ : syracuseStep 737905 = 553429) (by norm_num)
theorem B983677 : Blo 582814 983677 := bbase (se 3 (by rfl) ⟨184439, by rfl⟩ : syracuseStep 983677 = 368879) (by norm_num)
theorem B656005 : Blo 582814 656005 := bbase (se 4 (by rfl) ⟨61500, by rfl⟩ : syracuseStep 656005 = 123001) (by norm_num)
theorem B1311389 : Blo 582814 1311389 := bbase (se 3 (by rfl) ⟨245885, by rfl⟩ : syracuseStep 1311389 = 491771) (by norm_num)
theorem B656041 : Blo 582814 656041 := bbase (se 2 (by rfl) ⟨246015, by rfl⟩ : syracuseStep 656041 = 492031) (by norm_num)
theorem B656077 : Blo 582814 656077 := bbase (se 3 (by rfl) ⟨123014, by rfl⟩ : syracuseStep 656077 = 246029) (by norm_num)
theorem B738001 : Blo 582814 738001 := bbase (se 2 (by rfl) ⟨276750, by rfl⟩ : syracuseStep 738001 = 553501) (by norm_num)
theorem B983765 : Blo 582814 983765 := bbase (se 7 (by rfl) ⟨11528, by rfl⟩ : syracuseStep 983765 = 23057) (by norm_num)
theorem B1475293 : Blo 582814 1475293 := bbase (se 3 (by rfl) ⟨276617, by rfl⟩ : syracuseStep 1475293 = 553235) (by norm_num)
theorem B1311461 : Blo 582814 1311461 := bbase (se 4 (by rfl) ⟨122949, by rfl⟩ : syracuseStep 1311461 = 245899) (by norm_num)
theorem B830189 : Blo 582814 830189 := bbase (se 3 (by rfl) ⟨155660, by rfl⟩ : syracuseStep 830189 = 311321) (by norm_num)
theorem B656113 : Blo 582814 656113 := bbase (se 2 (by rfl) ⟨246042, by rfl⟩ : syracuseStep 656113 = 492085) (by norm_num)
theorem B656149 : Blo 582814 656149 := bbase (se 6 (by rfl) ⟨15378, by rfl⟩ : syracuseStep 656149 = 30757) (by norm_num)
theorem B1311533 : Blo 582814 1311533 := bbase (se 3 (by rfl) ⟨245912, by rfl⟩ : syracuseStep 1311533 = 491825) (by norm_num)
theorem B656185 : Blo 582814 656185 := bbase (se 2 (by rfl) ⟨246069, by rfl⟩ : syracuseStep 656185 = 492139) (by norm_num)
theorem B1475405 : Blo 582814 1475405 := bbase (se 3 (by rfl) ⟨276638, by rfl⟩ : syracuseStep 1475405 = 553277) (by norm_num)
theorem B983893 : Blo 582814 983893 := bbase (se 9 (by rfl) ⟨2882, by rfl⟩ : syracuseStep 983893 = 5765) (by norm_num)
theorem B1106797 : Blo 582814 1106797 := bbase (se 3 (by rfl) ⟨207524, by rfl⟩ : syracuseStep 1106797 = 415049) (by norm_num)
theorem B1311605 : Blo 582814 1311605 := bbase (se 5 (by rfl) ⟨61481, by rfl⟩ : syracuseStep 1311605 = 122963) (by norm_num)
theorem B738173 : Blo 582814 738173 := bbase (se 3 (by rfl) ⟨138407, by rfl⟩ : syracuseStep 738173 = 276815) (by norm_num)
theorem B1659797 : Blo 582814 1659797 := bbase (se 6 (by rfl) ⟨38901, by rfl⟩ : syracuseStep 1659797 = 77803) (by norm_num)
theorem B3990421 : Blo 582814 3990421 := bbase (se 6 (by rfl) ⟨93525, by rfl⟩ : syracuseStep 3990421 = 187051) (by norm_num)
theorem B983981 : Blo 582814 983981 := bbase (se 3 (by rfl) ⟨184496, by rfl⟩ : syracuseStep 983981 = 368993) (by norm_num)
theorem B959413 : Blo 582814 959413 := bbase (se 5 (by rfl) ⟨44972, by rfl⟩ : syracuseStep 959413 = 89945) (by norm_num)
theorem B1311677 : Blo 582814 1311677 := bbase (se 3 (by rfl) ⟨245939, by rfl⟩ : syracuseStep 1311677 = 491879) (by norm_num)
theorem B1106941 : Blo 582814 1106941 := bbase (se 3 (by rfl) ⟨207551, by rfl⟩ : syracuseStep 1106941 = 415103) (by norm_num)
theorem B1311749 : Blo 582814 1311749 := bbase (se 4 (by rfl) ⟨122976, by rfl⟩ : syracuseStep 1311749 = 245953) (by norm_num)
theorem B1475597 : Blo 582814 1475597 := bbase (se 3 (by rfl) ⟨276674, by rfl⟩ : syracuseStep 1475597 = 553349) (by norm_num)
theorem B984109 : Blo 582814 984109 := bbase (se 3 (by rfl) ⟨184520, by rfl⟩ : syracuseStep 984109 = 369041) (by norm_num)
theorem B1311821 : Blo 582814 1311821 := bbase (se 3 (by rfl) ⟨245966, by rfl⟩ : syracuseStep 1311821 = 491933) (by norm_num)
theorem B4428917 : Blo 582814 4428917 := bbase (se 5 (by rfl) ⟨207605, by rfl⟩ : syracuseStep 4428917 = 415211) (by norm_num)
theorem B664705 : Blo 582814 664705 := bbase (se 2 (by rfl) ⟨249264, by rfl⟩ : syracuseStep 664705 = 498529) (by norm_num)
theorem B984197 : Blo 582814 984197 := bbase (se 4 (by rfl) ⟨92268, by rfl⟩ : syracuseStep 984197 = 184537) (by norm_num)
theorem B1311893 : Blo 582814 1311893 := bbase (se 6 (by rfl) ⟨30747, by rfl⟩ : syracuseStep 1311893 = 61495) (by norm_num)
theorem B5680277 : Blo 582814 5680277 := bbase (se 6 (by rfl) ⟨133131, by rfl⟩ : syracuseStep 5680277 = 266263) (by norm_num)
theorem B1107101 : Blo 582814 1107101 := bbase (se 3 (by rfl) ⟨207581, by rfl⟩ : syracuseStep 1107101 = 415163) (by norm_num)
theorem B2489525 : Blo 582814 2489525 := bbase (se 5 (by rfl) ⟨116696, by rfl⟩ : syracuseStep 2489525 = 233393) (by norm_num)
theorem B2802869 : Blo 582814 2802869 := bbase (se 5 (by rfl) ⟨131384, by rfl⟩ : syracuseStep 2802869 = 262769) (by norm_num)
theorem B1311965 : Blo 582814 1311965 := bbase (se 3 (by rfl) ⟨245993, by rfl⟩ : syracuseStep 1311965 = 491987) (by norm_num)
theorem B591077 : Blo 582814 591077 := bbase (se 4 (by rfl) ⟨55413, by rfl⟩ : syracuseStep 591077 = 110827) (by norm_num)
theorem B1967381 : Blo 582814 1967381 := bbase (se 6 (by rfl) ⟨46110, by rfl⟩ : syracuseStep 1967381 = 92221) (by norm_num)
theorem B1312037 : Blo 582814 1312037 := bbase (se 4 (by rfl) ⟨123003, by rfl⟩ : syracuseStep 1312037 = 246007) (by norm_num)
theorem B1107245 : Blo 582814 1107245 := bbase (se 3 (by rfl) ⟨207608, by rfl⟩ : syracuseStep 1107245 = 415217) (by norm_num)
theorem B1475941 : Blo 582814 1475941 := bbase (se 4 (by rfl) ⟨138369, by rfl⟩ : syracuseStep 1475941 = 276739) (by norm_num)
theorem B1312109 : Blo 582814 1312109 := bbase (se 3 (by rfl) ⟨246020, by rfl⟩ : syracuseStep 1312109 = 492041) (by norm_num)
theorem B1312181 : Blo 582814 1312181 := bbase (se 5 (by rfl) ⟨61508, by rfl⟩ : syracuseStep 1312181 = 123017) (by norm_num)
theorem B1011133 : Blo 582814 1011133 := bbase (se 3 (by rfl) ⟨189587, by rfl⟩ : syracuseStep 1011133 = 379175) (by norm_num)
theorem B1476053 : Blo 582814 1476053 := bbase (se 7 (by rfl) ⟨17297, by rfl⟩ : syracuseStep 1476053 = 34595) (by norm_num)
theorem B2213365 : Blo 582814 2213365 := bbase (se 5 (by rfl) ⟨103751, by rfl⟩ : syracuseStep 2213365 = 207503) (by norm_num)
theorem B1312253 : Blo 582814 1312253 := bbase (se 3 (by rfl) ⟨246047, by rfl⟩ : syracuseStep 1312253 = 492095) (by norm_num)
theorem B1121861 : Blo 582814 1121861 := bbase (se 4 (by rfl) ⟨105174, by rfl⟩ : syracuseStep 1121861 = 210349) (by norm_num)
theorem B1312325 : Blo 582814 1312325 := bbase (se 4 (by rfl) ⟨123030, by rfl⟩ : syracuseStep 1312325 = 246061) (by norm_num)
theorem B2952773 : Blo 582814 2952773 := bbase (se 4 (by rfl) ⟨276822, by rfl⟩ : syracuseStep 2952773 = 553645) (by norm_num)
theorem B1867349 : Blo 582814 1867349 := bbase (se 8 (by rfl) ⟨10941, by rfl⟩ : syracuseStep 1867349 = 21883) (by norm_num)
theorem B2100853 : Blo 582814 2100853 := bbase (se 5 (by rfl) ⟨98477, by rfl⟩ : syracuseStep 2100853 = 196955) (by norm_num)
theorem B1244813 : Blo 582814 1244813 := bbase (se 3 (by rfl) ⟨233402, by rfl⟩ : syracuseStep 1244813 = 466805) (by norm_num)
theorem B1312397 : Blo 582814 1312397 := bbase (se 3 (by rfl) ⟨246074, by rfl⟩ : syracuseStep 1312397 = 492149) (by norm_num)
theorem B1476245 : Blo 582814 1476245 := bbase (se 6 (by rfl) ⟨34599, by rfl⟩ : syracuseStep 1476245 = 69199) (by norm_num)
theorem B1967813 : Blo 582814 1967813 := bbase (se 4 (by rfl) ⟨184482, by rfl⟩ : syracuseStep 1967813 = 368965) (by norm_num)
theorem B886493 : Blo 582814 886493 := bbase (se 3 (by rfl) ⟨166217, by rfl⟩ : syracuseStep 886493 = 332435) (by norm_num)
theorem B874229 : Blo 582814 874229 := bbase (se 5 (by rfl) ⟨40979, by rfl⟩ : syracuseStep 874229 = 81959) (by norm_num)
theorem B700169 : Blo 582814 700169 := bbase (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) (by norm_num)
theorem B874253 : Blo 582814 874253 := bbase (se 3 (by rfl) ⟨163922, by rfl⟩ : syracuseStep 874253 = 327845) (by norm_num)
theorem B874277 : Blo 582814 874277 := bbase (se 4 (by rfl) ⟨81963, by rfl⟩ : syracuseStep 874277 = 163927) (by norm_num)
theorem B2213669 : Blo 582814 2213669 := bbase (se 4 (by rfl) ⟨207531, by rfl⟩ : syracuseStep 2213669 = 415063) (by norm_num)
theorem B1050421 : Blo 582814 1050421 := bbase (se 5 (by rfl) ⟨49238, by rfl⟩ : syracuseStep 1050421 = 98477) (by norm_num)
theorem B874301 : Blo 582814 874301 := bbase (se 3 (by rfl) ⟨163931, by rfl⟩ : syracuseStep 874301 = 327863) (by norm_num)
theorem B874325 : Blo 582814 874325 := bbase (se 9 (by rfl) ⟨2561, by rfl⟩ : syracuseStep 874325 = 5123) (by norm_num)
theorem B622441 : Blo 582814 622441 := bbase (se 2 (by rfl) ⟨233415, by rfl⟩ : syracuseStep 622441 = 466831) (by norm_num)
theorem B874349 : Blo 582814 874349 := bbase (se 3 (by rfl) ⟨163940, by rfl⟩ : syracuseStep 874349 = 327881) (by norm_num)
theorem B1245053 : Blo 582814 1245053 := bbase (se 3 (by rfl) ⟨233447, by rfl⟩ : syracuseStep 1245053 = 466895) (by norm_num)
theorem B874373 : Blo 582814 874373 := bbase (se 4 (by rfl) ⟨81972, by rfl⟩ : syracuseStep 874373 = 163945) (by norm_num)
theorem B874397 : Blo 582814 874397 := bbase (se 3 (by rfl) ⟨163949, by rfl⟩ : syracuseStep 874397 = 327899) (by norm_num)
theorem B874421 : Blo 582814 874421 := bbase (se 5 (by rfl) ⟨40988, by rfl⟩ : syracuseStep 874421 = 81977) (by norm_num)
theorem B874445 : Blo 582814 874445 := bbase (se 3 (by rfl) ⟨163958, by rfl⟩ : syracuseStep 874445 = 327917) (by norm_num)
theorem B14378965 : Blo 582814 14378965 := bbase (se 7 (by rfl) ⟨168503, by rfl⟩ : syracuseStep 14378965 = 337007) (by norm_num)
theorem B874469 : Blo 582814 874469 := bbase (se 4 (by rfl) ⟨81981, by rfl⟩ : syracuseStep 874469 = 163963) (by norm_num)
theorem B874493 : Blo 582814 874493 := bbase (se 3 (by rfl) ⟨163967, by rfl⟩ : syracuseStep 874493 = 327935) (by norm_num)
theorem B874499 : Blo 582814 874499 := bstep (se 1 (by rfl) ⟨655874, by rfl⟩ : syracuseStep 874499 = 1311749) B1311749
theorem B3545093 : Blo 582814 3545093 := bstep (se 4 (by rfl) ⟨332352, by rfl⟩ : syracuseStep 3545093 = 664705) B664705
theorem B874529 : Blo 582814 874529 := bstep (se 2 (by rfl) ⟨327948, by rfl⟩ : syracuseStep 874529 = 655897) B655897
theorem B874547 : Blo 582814 874547 := bstep (se 1 (by rfl) ⟨655910, by rfl⟩ : syracuseStep 874547 = 1311821) B1311821
theorem B874577 : Blo 582814 874577 := bstep (se 2 (by rfl) ⟨327966, by rfl⟩ : syracuseStep 874577 = 655933) B655933
theorem B874595 : Blo 582814 874595 := bstep (se 1 (by rfl) ⟨655946, by rfl⟩ : syracuseStep 874595 = 1311893) B1311893
theorem B3786851 : Blo 582814 3786851 := bstep (se 1 (by rfl) ⟨2840138, by rfl⟩ : syracuseStep 3786851 = 5680277) B5680277
theorem B874625 : Blo 582814 874625 := bstep (se 2 (by rfl) ⟨327984, by rfl⟩ : syracuseStep 874625 = 655969) B655969
theorem B622723 : Blo 582814 622723 := bstep (se 1 (by rfl) ⟨467042, by rfl⟩ : syracuseStep 622723 = 934085) B934085
theorem B874643 : Blo 582814 874643 := bstep (se 1 (by rfl) ⟨655982, by rfl⟩ : syracuseStep 874643 = 1311965) B1311965
theorem B874673 : Blo 582814 874673 := bstep (se 2 (by rfl) ⟨328002, by rfl⟩ : syracuseStep 874673 = 656005) B656005
theorem B874691 : Blo 582814 874691 := bstep (se 1 (by rfl) ⟨656018, by rfl⟩ : syracuseStep 874691 = 1312037) B1312037
theorem B934097 : Blo 582814 934097 := bstep (se 2 (by rfl) ⟨350286, by rfl⟩ : syracuseStep 934097 = 700573) B700573
theorem B874721 : Blo 582814 874721 := bstep (se 2 (by rfl) ⟨328020, by rfl⟩ : syracuseStep 874721 = 656041) B656041
theorem B874739 : Blo 582814 874739 := bstep (se 1 (by rfl) ⟨656054, by rfl⟩ : syracuseStep 874739 = 1312109) B1312109
theorem B874769 : Blo 582814 874769 := bstep (se 2 (by rfl) ⟨328038, by rfl⟩ : syracuseStep 874769 = 656077) B656077
theorem B874787 : Blo 582814 874787 := bstep (se 1 (by rfl) ⟨656090, by rfl⟩ : syracuseStep 874787 = 1312181) B1312181
theorem B874817 : Blo 582814 874817 := bstep (se 2 (by rfl) ⟨328056, by rfl⟩ : syracuseStep 874817 = 656113) B656113
theorem B1968461 : Blo 582814 1968461 := bstep (se 3 (by rfl) ⟨369086, by rfl⟩ : syracuseStep 1968461 = 738173) B738173
theorem B655699 : Blo 582814 655699 := bstep (se 1 (by rfl) ⟨491774, by rfl⟩ : syracuseStep 655699 = 983549) B983549
theorem B874835 : Blo 582814 874835 := bstep (se 1 (by rfl) ⟨656126, by rfl⟩ : syracuseStep 874835 = 1312253) B1312253
theorem B7094627 : Blo 582814 7094627 := bstep (se 1 (by rfl) ⟨5320970, by rfl⟩ : syracuseStep 7094627 = 10641941) B10641941
theorem B874865 : Blo 582814 874865 := bstep (se 2 (by rfl) ⟨328074, by rfl⟩ : syracuseStep 874865 = 656149) B656149
theorem B874883 : Blo 582814 874883 := bstep (se 1 (by rfl) ⟨656162, by rfl⟩ : syracuseStep 874883 = 1312325) B1312325
theorem B1968515 : Blo 582814 1968515 := bstep (se 1 (by rfl) ⟨1476386, by rfl⟩ : syracuseStep 1968515 = 2952773) B2952773
theorem B874913 : Blo 582814 874913 := bstep (se 2 (by rfl) ⟨328092, by rfl⟩ : syracuseStep 874913 = 656185) B656185
theorem B874931 : Blo 582814 874931 := bstep (se 1 (by rfl) ⟨656198, by rfl⟩ : syracuseStep 874931 = 1312397) B1312397
theorem B76687813 : Blo 582814 76687813 := bstep (se 4 (by rfl) ⟨7189482, by rfl⟩ : syracuseStep 76687813 = 14378965) B14378965
theorem B829921 : Blo 582814 829921 := bstep (se 2 (by rfl) ⟨311220, by rfl⟩ : syracuseStep 829921 = 622441) B622441
theorem B655843 : Blo 582814 655843 := bstep (se 1 (by rfl) ⟨491882, by rfl⟩ : syracuseStep 655843 = 983765) B983765
theorem B983569 : Blo 582814 983569 := bstep (se 2 (by rfl) ⟨368838, by rfl⟩ : syracuseStep 983569 = 737677) B737677
theorem B983603 : Blo 582814 983603 := bstep (se 1 (by rfl) ⟨737702, by rfl⟩ : syracuseStep 983603 = 1475405) B1475405
theorem B1348177 : Blo 582814 1348177 := bstep (se 2 (by rfl) ⟨505566, by rfl⟩ : syracuseStep 1348177 = 1011133) B1011133
theorem B830035 : Blo 582814 830035 := bstep (se 1 (by rfl) ⟨622526, by rfl⟩ : syracuseStep 830035 = 1245053) B1245053
theorem B1106531 : Blo 582814 1106531 := bstep (se 1 (by rfl) ⟨829898, by rfl⟩ : syracuseStep 1106531 = 1659797) B1659797
theorem B655987 : Blo 582814 655987 := bstep (se 1 (by rfl) ⟨491990, by rfl⟩ : syracuseStep 655987 = 983981) B983981
theorem B983731 : Blo 582814 983731 := bstep (se 1 (by rfl) ⟨737798, by rfl⟩ : syracuseStep 983731 = 1475597) B1475597
theorem B2214641 : Blo 582814 2214641 := bstep (se 2 (by rfl) ⟨830490, by rfl⟩ : syracuseStep 2214641 = 1660981) B1660981
theorem B656131 : Blo 582814 656131 := bstep (se 1 (by rfl) ⟨492098, by rfl⟩ : syracuseStep 656131 = 984197) B984197
theorem B738067 : Blo 582814 738067 := bstep (se 1 (by rfl) ⟨553550, by rfl⟩ : syracuseStep 738067 = 1107101) B1107101
theorem B1659683 : Blo 582814 1659683 := bstep (se 1 (by rfl) ⟨1244762, by rfl⟩ : syracuseStep 1659683 = 2489525) B2489525
theorem B1868579 : Blo 582814 1868579 := bstep (se 1 (by rfl) ⟨1401434, by rfl⟩ : syracuseStep 1868579 = 2802869) B2802869
theorem B983873 : Blo 582814 983873 := bstep (se 2 (by rfl) ⟨368952, by rfl⟩ : syracuseStep 983873 = 737905) B737905
theorem B1311569 : Blo 582814 1311569 := bstep (se 2 (by rfl) ⟨491838, by rfl⟩ : syracuseStep 1311569 = 983677) B983677
theorem B1311587 : Blo 582814 1311587 := bstep (se 1 (by rfl) ⟨983690, by rfl⟩ : syracuseStep 1311587 = 1967381) B1967381
theorem B738163 : Blo 582814 738163 := bstep (se 1 (by rfl) ⟨553622, by rfl⟩ : syracuseStep 738163 = 1107245) B1107245
theorem B984001 : Blo 582814 984001 := bstep (se 2 (by rfl) ⟨369000, by rfl⟩ : syracuseStep 984001 = 738001) B738001
theorem B1967057 : Blo 582814 1967057 := bstep (se 2 (by rfl) ⟨737646, by rfl⟩ : syracuseStep 1967057 = 1475293) B1475293
theorem B984035 : Blo 582814 984035 := bstep (se 1 (by rfl) ⟨738026, by rfl⟩ : syracuseStep 984035 = 1476053) B1476053
theorem B984163 : Blo 582814 984163 := bstep (se 1 (by rfl) ⟨738122, by rfl⟩ : syracuseStep 984163 = 1476245) B1476245
theorem B1311857 : Blo 582814 1311857 := bstep (se 2 (by rfl) ⟨491946, by rfl⟩ : syracuseStep 1311857 = 983893) B983893
theorem B1311875 : Blo 582814 1311875 := bstep (se 1 (by rfl) ⟨983906, by rfl⟩ : syracuseStep 1311875 = 1967813) B1967813
theorem B1475729 : Blo 582814 1475729 := bstep (se 2 (by rfl) ⟨553398, by rfl⟩ : syracuseStep 1475729 = 1106797) B1106797
theorem B590995 : Blo 582814 590995 := bstep (se 1 (by rfl) ⟨443246, by rfl⟩ : syracuseStep 590995 = 886493) B886493
theorem B582819 : Blo 582814 582819 := bstep (se 1 (by rfl) ⟨437114, by rfl⟩ : syracuseStep 582819 = 874229) B874229
theorem B582835 : Blo 582814 582835 := bstep (se 1 (by rfl) ⟨437126, by rfl⟩ : syracuseStep 582835 = 874253) B874253
theorem B582851 : Blo 582814 582851 := bstep (se 1 (by rfl) ⟨437138, by rfl⟩ : syracuseStep 582851 = 874277) B874277
theorem B1475779 : Blo 582814 1475779 := bstep (se 1 (by rfl) ⟨1106834, by rfl⟩ : syracuseStep 1475779 = 2213669) B2213669
theorem B582867 : Blo 582814 582867 := bstep (se 1 (by rfl) ⟨437150, by rfl⟩ : syracuseStep 582867 = 874301) B874301
theorem B582883 : Blo 582814 582883 := bstep (se 1 (by rfl) ⟨437162, by rfl⟩ : syracuseStep 582883 = 874325) B874325
theorem B1279217 : Blo 582814 1279217 := bstep (se 2 (by rfl) ⟨479706, by rfl⟩ : syracuseStep 1279217 = 959413) B959413
theorem B582899 : Blo 582814 582899 := bstep (se 1 (by rfl) ⟨437174, by rfl⟩ : syracuseStep 582899 = 874349) B874349
theorem B582915 : Blo 582814 582915 := bstep (se 1 (by rfl) ⟨437186, by rfl⟩ : syracuseStep 582915 = 874373) B874373
theorem B1576205 : Blo 582814 1576205 := bstep (se 3 (by rfl) ⟨295538, by rfl⟩ : syracuseStep 1576205 = 591077) B591077
theorem B582931 : Blo 582814 582931 := bstep (se 1 (by rfl) ⟨437198, by rfl⟩ : syracuseStep 582931 = 874397) B874397
theorem B582947 : Blo 582814 582947 := bstep (se 1 (by rfl) ⟨437210, by rfl⟩ : syracuseStep 582947 = 874421) B874421
theorem B582963 : Blo 582814 582963 := bstep (se 1 (by rfl) ⟨437222, by rfl⟩ : syracuseStep 582963 = 874445) B874445
theorem B582979 : Blo 582814 582979 := bstep (se 1 (by rfl) ⟨437234, by rfl⟩ : syracuseStep 582979 = 874469) B874469
theorem B1475921 : Blo 582814 1475921 := bstep (se 2 (by rfl) ⟨553470, by rfl⟩ : syracuseStep 1475921 = 1106941) B1106941
theorem B582995 : Blo 582814 582995 := bstep (se 1 (by rfl) ⟨437246, by rfl⟩ : syracuseStep 582995 = 874493) B874493
theorem B583011 : Blo 582814 583011 := bstep (se 1 (by rfl) ⟨437258, by rfl⟩ : syracuseStep 583011 = 874517) B874517
theorem B583027 : Blo 582814 583027 := bstep (se 1 (by rfl) ⟨437270, by rfl⟩ : syracuseStep 583027 = 874541) B874541
theorem B583043 : Blo 582814 583043 := bstep (se 1 (by rfl) ⟨437282, by rfl⟩ : syracuseStep 583043 = 874565) B874565
theorem B1312145 : Blo 582814 1312145 := bstep (se 2 (by rfl) ⟨492054, by rfl⟩ : syracuseStep 1312145 = 984109) B984109
theorem B583059 : Blo 582814 583059 := bstep (se 1 (by rfl) ⟨437294, by rfl⟩ : syracuseStep 583059 = 874589) B874589
theorem B664979 : Blo 582814 664979 := bstep (se 1 (by rfl) ⟨498734, by rfl⟩ : syracuseStep 664979 = 997469) B997469
theorem B583075 : Blo 582814 583075 := bstep (se 1 (by rfl) ⟨437306, by rfl⟩ : syracuseStep 583075 = 874613) B874613
theorem B1312163 : Blo 582814 1312163 := bstep (se 1 (by rfl) ⟨984122, by rfl⟩ : syracuseStep 1312163 = 1968245) B1968245
theorem B2952611 : Blo 582814 2952611 := bstep (se 1 (by rfl) ⟨2214458, by rfl⟩ : syracuseStep 2952611 = 4428917) B4428917
theorem B583091 : Blo 582814 583091 := bstep (se 1 (by rfl) ⟨437318, by rfl⟩ : syracuseStep 583091 = 874637) B874637
theorem B7468469 : Blo 582814 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B787907 : Blo 582814 787907 := bstep (se 1 (by rfl) ⟨590930, by rfl⟩ : syracuseStep 787907 = 1181861) B1181861
theorem B583107 : Blo 582814 583107 := bstep (se 1 (by rfl) ⟨437330, by rfl⟩ : syracuseStep 583107 = 874661) B874661
theorem B583123 : Blo 582814 583123 := bstep (se 1 (by rfl) ⟨437342, by rfl⟩ : syracuseStep 583123 = 874685) B874685
theorem B583139 : Blo 582814 583139 := bstep (se 1 (by rfl) ⟨437354, by rfl⟩ : syracuseStep 583139 = 874709) B874709
theorem B1967597 : Blo 582814 1967597 := bstep (se 3 (by rfl) ⟨368924, by rfl⟩ : syracuseStep 1967597 = 737849) B737849
theorem B2801137 : Blo 582814 2801137 := bstep (se 2 (by rfl) ⟨1050426, by rfl⟩ : syracuseStep 2801137 = 2100853) B2100853
theorem B583155 : Blo 582814 583155 := bstep (se 1 (by rfl) ⟨437366, by rfl⟩ : syracuseStep 583155 = 874733) B874733
theorem B583171 : Blo 582814 583171 := bstep (se 1 (by rfl) ⟨437378, by rfl⟩ : syracuseStep 583171 = 874757) B874757
theorem B2991629 : Blo 582814 2991629 := bstep (se 3 (by rfl) ⟨560930, by rfl⟩ : syracuseStep 2991629 = 1121861) B1121861
theorem B583187 : Blo 582814 583187 := bstep (se 1 (by rfl) ⟨437390, by rfl⟩ : syracuseStep 583187 = 874781) B874781
theorem B1967651 : Blo 582814 1967651 := bstep (se 1 (by rfl) ⟨1475738, by rfl⟩ : syracuseStep 1967651 = 2951477) B2951477
theorem B583203 : Blo 582814 583203 := bstep (se 1 (by rfl) ⟨437402, by rfl⟩ : syracuseStep 583203 = 874805) B874805
theorem B583219 : Blo 582814 583219 := bstep (se 1 (by rfl) ⟨437414, by rfl⟩ : syracuseStep 583219 = 874829) B874829
theorem B583235 : Blo 582814 583235 := bstep (se 1 (by rfl) ⟨437426, by rfl⟩ : syracuseStep 583235 = 874853) B874853
theorem B583251 : Blo 582814 583251 := bstep (se 1 (by rfl) ⟨437438, by rfl⟩ : syracuseStep 583251 = 874877) B874877
theorem B583267 : Blo 582814 583267 := bstep (se 1 (by rfl) ⟨437450, by rfl⟩ : syracuseStep 583267 = 874901) B874901
theorem B583283 : Blo 582814 583283 := bstep (se 1 (by rfl) ⟨437462, by rfl⟩ : syracuseStep 583283 = 874925) B874925
theorem B3321485 : Blo 582814 3321485 := bstep (se 3 (by rfl) ⟨622778, by rfl⟩ : syracuseStep 3321485 = 1245557) B1245557
theorem B3319501 : Blo 582814 3319501 := bstep (se 3 (by rfl) ⟨622406, by rfl⟩ : syracuseStep 3319501 = 1244813) B1244813
theorem B1244899 : Blo 582814 1244899 := bstep (se 1 (by rfl) ⟨933674, by rfl⟩ : syracuseStep 1244899 = 1867349) B1867349
theorem B1400561 : Blo 582814 1400561 := bstep (se 2 (by rfl) ⟨525210, by rfl⟩ : syracuseStep 1400561 = 1050421) B1050421
theorem B874241 : Blo 582814 874241 := bstep (se 2 (by rfl) ⟨327840, by rfl⟩ : syracuseStep 874241 = 655681) B655681
theorem B874259 : Blo 582814 874259 := bstep (se 1 (by rfl) ⟨655694, by rfl⟩ : syracuseStep 874259 = 1311389) B1311389
theorem B874289 : Blo 582814 874289 := bstep (se 2 (by rfl) ⟨327858, by rfl⟩ : syracuseStep 874289 = 655717) B655717
theorem B1967921 : Blo 582814 1967921 := bstep (se 2 (by rfl) ⟨737970, by rfl⟩ : syracuseStep 1967921 = 1475941) B1475941
theorem B874307 : Blo 582814 874307 := bstep (se 1 (by rfl) ⟨655730, by rfl⟩ : syracuseStep 874307 = 1311461) B1311461
theorem B1660753 : Blo 582814 1660753 := bstep (se 2 (by rfl) ⟨622782, by rfl⟩ : syracuseStep 1660753 = 1245565) B1245565
theorem B874337 : Blo 582814 874337 := bstep (se 2 (by rfl) ⟨327876, by rfl⟩ : syracuseStep 874337 = 655753) B655753
theorem B5320561 : Blo 582814 5320561 := bstep (se 2 (by rfl) ⟨1995210, by rfl⟩ : syracuseStep 5320561 = 3990421) B3990421
theorem B874355 : Blo 582814 874355 := bstep (se 1 (by rfl) ⟨655766, by rfl⟩ : syracuseStep 874355 = 1311533) B1311533
theorem B874385 : Blo 582814 874385 := bstep (se 2 (by rfl) ⟨327894, by rfl⟩ : syracuseStep 874385 = 655789) B655789
theorem B997265 : Blo 582814 997265 := bstep (se 2 (by rfl) ⟨373974, by rfl⟩ : syracuseStep 997265 = 747949) B747949
theorem B874403 : Blo 582814 874403 := bstep (se 1 (by rfl) ⟨655802, by rfl⟩ : syracuseStep 874403 = 1311605) B1311605
theorem B874433 : Blo 582814 874433 := bstep (se 2 (by rfl) ⟨327912, by rfl⟩ : syracuseStep 874433 = 655825) B655825
theorem B2213837 : Blo 582814 2213837 := bstep (se 3 (by rfl) ⟨415094, by rfl⟩ : syracuseStep 2213837 = 830189) B830189
theorem B874451 : Blo 582814 874451 := bstep (se 1 (by rfl) ⟨655838, by rfl⟩ : syracuseStep 874451 = 1311677) B1311677
theorem B2951153 : Blo 582814 2951153 := bstep (se 2 (by rfl) ⟨1106682, by rfl⟩ : syracuseStep 2951153 = 2213365) B2213365
theorem B874481 : Blo 582814 874481 := bstep (se 2 (by rfl) ⟨327930, by rfl⟩ : syracuseStep 874481 = 655861) B655861
theorem B9453581 : Blo 582814 9453581 := bstep (se 3 (by rfl) ⟨1772546, by rfl⟩ : syracuseStep 9453581 = 3545093) B3545093
theorem B874571 : Blo 582814 874571 := bstep (se 1 (by rfl) ⟨655928, by rfl⟩ : syracuseStep 874571 = 1311857) B1311857
theorem B874583 : Blo 582814 874583 := bstep (se 1 (by rfl) ⟨655937, by rfl⟩ : syracuseStep 874583 = 1311875) B1311875
theorem B3151973 : Blo 582814 3151973 := bstep (se 4 (by rfl) ⟨295497, by rfl⟩ : syracuseStep 3151973 = 590995) B590995
theorem B874649 : Blo 582814 874649 := bstep (se 2 (by rfl) ⟨327993, by rfl⟩ : syracuseStep 874649 = 655987) B655987
theorem B1050803 : Blo 582814 1050803 := bstep (se 1 (by rfl) ⟨788102, by rfl⟩ : syracuseStep 1050803 = 1576205) B1576205
theorem B874763 : Blo 582814 874763 := bstep (se 1 (by rfl) ⟨656072, by rfl⟩ : syracuseStep 874763 = 1312145) B1312145
theorem B4426001 : Blo 582814 4426001 := bstep (se 2 (by rfl) ⟨1659750, by rfl⟩ : syracuseStep 4426001 = 3319501) B3319501
theorem B874775 : Blo 582814 874775 := bstep (se 1 (by rfl) ⟨656081, by rfl⟩ : syracuseStep 874775 = 1312163) B1312163
theorem B1968407 : Blo 582814 1968407 := bstep (se 1 (by rfl) ⟨1476305, by rfl⟩ : syracuseStep 1968407 = 2952611) B2952611
theorem B4978979 : Blo 582814 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B874841 : Blo 582814 874841 := bstep (se 2 (by rfl) ⟨328065, by rfl⟩ : syracuseStep 874841 = 656131) B656131
theorem B655735 : Blo 582814 655735 := bstep (se 1 (by rfl) ⟨491801, by rfl⟩ : syracuseStep 655735 = 983603) B983603
theorem B737687 : Blo 582814 737687 := bstep (se 1 (by rfl) ⟨553265, by rfl⟩ : syracuseStep 737687 = 1106531) B1106531
theorem B2214323 : Blo 582814 2214323 := bstep (se 1 (by rfl) ⟨1660742, by rfl⟩ : syracuseStep 2214323 = 3321485) B3321485
theorem B2214337 : Blo 582814 2214337 := bstep (se 2 (by rfl) ⟨830376, by rfl⟩ : syracuseStep 2214337 = 1660753) B1660753
theorem B1106455 : Blo 582814 1106455 := bstep (se 1 (by rfl) ⟨829841, by rfl⟩ : syracuseStep 1106455 = 1659683) B1659683
theorem B1245719 : Blo 582814 1245719 := bstep (se 1 (by rfl) ⟨934289, by rfl⟩ : syracuseStep 1245719 = 1868579) B1868579
theorem B655915 : Blo 582814 655915 := bstep (se 1 (by rfl) ⟨491936, by rfl⟩ : syracuseStep 655915 = 983873) B983873
theorem B2490925 : Blo 582814 2490925 := bstep (se 3 (by rfl) ⟨467048, by rfl⟩ : syracuseStep 2490925 = 934097) B934097
theorem B1106561 : Blo 582814 1106561 := bstep (se 2 (by rfl) ⟨414960, by rfl⟩ : syracuseStep 1106561 = 829921) B829921
theorem B1311371 : Blo 582814 1311371 := bstep (se 1 (by rfl) ⟨983528, by rfl⟩ : syracuseStep 1311371 = 1967057) B1967057
theorem B656023 : Blo 582814 656023 := bstep (se 1 (by rfl) ⟨492017, by rfl⟩ : syracuseStep 656023 = 984035) B984035
theorem B1311425 : Blo 582814 1311425 := bstep (se 2 (by rfl) ⟨491784, by rfl⟩ : syracuseStep 1311425 = 983569) B983569
theorem B983819 : Blo 582814 983819 := bstep (se 1 (by rfl) ⟨737864, by rfl⟩ : syracuseStep 983819 = 1475729) B1475729
theorem B1106713 : Blo 582814 1106713 := bstep (se 2 (by rfl) ⟨415017, by rfl⟩ : syracuseStep 1106713 = 830035) B830035
theorem B852811 : Blo 582814 852811 := bstep (se 1 (by rfl) ⟨639608, by rfl⟩ : syracuseStep 852811 = 1279217) B1279217
theorem B830297 : Blo 582814 830297 := bstep (se 2 (by rfl) ⟨311361, by rfl⟩ : syracuseStep 830297 = 622723) B622723
theorem B7093109 : Blo 582814 7093109 := bstep (se 5 (by rfl) ⟨332489, by rfl⟩ : syracuseStep 7093109 = 664979) B664979
theorem B983947 : Blo 582814 983947 := bstep (se 1 (by rfl) ⟨737960, by rfl⟩ : syracuseStep 983947 = 1475921) B1475921
theorem B4729751 : Blo 582814 4729751 := bstep (se 1 (by rfl) ⟨3547313, by rfl⟩ : syracuseStep 4729751 = 7094627) B7094627
theorem B1311641 : Blo 582814 1311641 := bstep (se 2 (by rfl) ⟨491865, by rfl⟩ : syracuseStep 1311641 = 983731) B983731
theorem B1659865 : Blo 582814 1659865 := bstep (se 2 (by rfl) ⟨622449, by rfl⟩ : syracuseStep 1659865 = 1244899) B1244899
theorem B1311731 : Blo 582814 1311731 := bstep (se 1 (by rfl) ⟨983798, by rfl⟩ : syracuseStep 1311731 = 1967597) B1967597
theorem B1311767 : Blo 582814 1311767 := bstep (se 1 (by rfl) ⟨983825, by rfl⟩ : syracuseStep 1311767 = 1967651) B1967651
theorem B984089 : Blo 582814 984089 := bstep (se 2 (by rfl) ⟨369033, by rfl⟩ : syracuseStep 984089 = 738067) B738067
theorem B984217 : Blo 582814 984217 := bstep (se 2 (by rfl) ⟨369081, by rfl⟩ : syracuseStep 984217 = 738163) B738163
theorem B582827 : Blo 582814 582827 := bstep (se 1 (by rfl) ⟨437120, by rfl⟩ : syracuseStep 582827 = 874241) B874241
theorem B582839 : Blo 582814 582839 := bstep (se 1 (by rfl) ⟨437129, by rfl⟩ : syracuseStep 582839 = 874259) B874259
theorem B582859 : Blo 582814 582859 := bstep (se 1 (by rfl) ⟨437144, by rfl⟩ : syracuseStep 582859 = 874289) B874289
theorem B1311947 : Blo 582814 1311947 := bstep (se 1 (by rfl) ⟨983960, by rfl⟩ : syracuseStep 1311947 = 1967921) B1967921
theorem B582871 : Blo 582814 582871 := bstep (se 1 (by rfl) ⟨437153, by rfl⟩ : syracuseStep 582871 = 874307) B874307
theorem B582891 : Blo 582814 582891 := bstep (se 1 (by rfl) ⟨437168, by rfl⟩ : syracuseStep 582891 = 874337) B874337
theorem B582903 : Blo 582814 582903 := bstep (se 1 (by rfl) ⟨437177, by rfl⟩ : syracuseStep 582903 = 874355) B874355
theorem B1312001 : Blo 582814 1312001 := bstep (se 2 (by rfl) ⟨492000, by rfl⟩ : syracuseStep 1312001 = 984001) B984001
theorem B582923 : Blo 582814 582923 := bstep (se 1 (by rfl) ⟨437192, by rfl⟩ : syracuseStep 582923 = 874385) B874385
theorem B664843 : Blo 582814 664843 := bstep (se 1 (by rfl) ⟨498632, by rfl⟩ : syracuseStep 664843 = 997265) B997265
theorem B582935 : Blo 582814 582935 := bstep (se 1 (by rfl) ⟨437201, by rfl⟩ : syracuseStep 582935 = 874403) B874403
theorem B582955 : Blo 582814 582955 := bstep (se 1 (by rfl) ⟨437216, by rfl⟩ : syracuseStep 582955 = 874433) B874433
theorem B1475891 : Blo 582814 1475891 := bstep (se 1 (by rfl) ⟨1106918, by rfl⟩ : syracuseStep 1475891 = 2213837) B2213837
theorem B582967 : Blo 582814 582967 := bstep (se 1 (by rfl) ⟨437225, by rfl⟩ : syracuseStep 582967 = 874451) B874451
theorem B3734849 : Blo 582814 3734849 := bstep (se 2 (by rfl) ⟨1400568, by rfl⟩ : syracuseStep 3734849 = 2801137) B2801137
theorem B1967435 : Blo 582814 1967435 := bstep (se 1 (by rfl) ⟨1475576, by rfl⟩ : syracuseStep 1967435 = 2951153) B2951153
theorem B582987 : Blo 582814 582987 := bstep (se 1 (by rfl) ⟨437240, by rfl⟩ : syracuseStep 582987 = 874481) B874481
theorem B582999 : Blo 582814 582999 := bstep (se 1 (by rfl) ⟨437249, by rfl⟩ : syracuseStep 582999 = 874499) B874499
theorem B583019 : Blo 582814 583019 := bstep (se 1 (by rfl) ⟨437264, by rfl⟩ : syracuseStep 583019 = 874529) B874529
theorem B583031 : Blo 582814 583031 := bstep (se 1 (by rfl) ⟨437273, by rfl⟩ : syracuseStep 583031 = 874547) B874547
theorem B583051 : Blo 582814 583051 := bstep (se 1 (by rfl) ⟨437288, by rfl⟩ : syracuseStep 583051 = 874577) B874577
theorem B583063 : Blo 582814 583063 := bstep (se 1 (by rfl) ⟨437297, by rfl⟩ : syracuseStep 583063 = 874595) B874595
theorem B583083 : Blo 582814 583083 := bstep (se 1 (by rfl) ⟨437312, by rfl⟩ : syracuseStep 583083 = 874625) B874625
theorem B583095 : Blo 582814 583095 := bstep (se 1 (by rfl) ⟨437321, by rfl⟩ : syracuseStep 583095 = 874643) B874643
theorem B1797569 : Blo 582814 1797569 := bstep (se 2 (by rfl) ⟨674088, by rfl⟩ : syracuseStep 1797569 = 1348177) B1348177
theorem B583115 : Blo 582814 583115 := bstep (se 1 (by rfl) ⟨437336, by rfl⟩ : syracuseStep 583115 = 874673) B874673
theorem B583127 : Blo 582814 583127 := bstep (se 1 (by rfl) ⟨437345, by rfl⟩ : syracuseStep 583127 = 874691) B874691
theorem B1312217 : Blo 582814 1312217 := bstep (se 2 (by rfl) ⟨492081, by rfl⟩ : syracuseStep 1312217 = 984163) B984163
theorem B583147 : Blo 582814 583147 := bstep (se 1 (by rfl) ⟨437360, by rfl⟩ : syracuseStep 583147 = 874721) B874721
theorem B583159 : Blo 582814 583159 := bstep (se 1 (by rfl) ⟨437369, by rfl⟩ : syracuseStep 583159 = 874739) B874739
theorem B583179 : Blo 582814 583179 := bstep (se 1 (by rfl) ⟨437384, by rfl⟩ : syracuseStep 583179 = 874769) B874769
theorem B583191 : Blo 582814 583191 := bstep (se 1 (by rfl) ⟨437393, by rfl⟩ : syracuseStep 583191 = 874787) B874787
theorem B583211 : Blo 582814 583211 := bstep (se 1 (by rfl) ⟨437408, by rfl⟩ : syracuseStep 583211 = 874817) B874817
theorem B1312307 : Blo 582814 1312307 := bstep (se 1 (by rfl) ⟨984230, by rfl⟩ : syracuseStep 1312307 = 1968461) B1968461
theorem B583223 : Blo 582814 583223 := bstep (se 1 (by rfl) ⟨437417, by rfl⟩ : syracuseStep 583223 = 874835) B874835
theorem B583243 : Blo 582814 583243 := bstep (se 1 (by rfl) ⟨437432, by rfl⟩ : syracuseStep 583243 = 874865) B874865
theorem B583255 : Blo 582814 583255 := bstep (se 1 (by rfl) ⟨437441, by rfl⟩ : syracuseStep 583255 = 874883) B874883
theorem B1312343 : Blo 582814 1312343 := bstep (se 1 (by rfl) ⟨984257, by rfl⟩ : syracuseStep 1312343 = 1968515) B1968515
theorem B1967705 : Blo 582814 1967705 := bstep (se 2 (by rfl) ⟨737889, by rfl⟩ : syracuseStep 1967705 = 1475779) B1475779
theorem B10098269 : Blo 582814 10098269 := bstep (se 3 (by rfl) ⟨1893425, by rfl⟩ : syracuseStep 10098269 = 3786851) B3786851
theorem B583275 : Blo 582814 583275 := bstep (se 1 (by rfl) ⟨437456, by rfl⟩ : syracuseStep 583275 = 874913) B874913
theorem B583287 : Blo 582814 583287 := bstep (se 1 (by rfl) ⟨437465, by rfl⟩ : syracuseStep 583287 = 874931) B874931
theorem B1994419 : Blo 582814 1994419 := bstep (se 1 (by rfl) ⟨1495814, by rfl⟩ : syracuseStep 1994419 = 2991629) B2991629
theorem B409001669 : Blo 582814 409001669 := bstep (se 4 (by rfl) ⟨38343906, by rfl⟩ : syracuseStep 409001669 = 76687813) B76687813
theorem B874265 : Blo 582814 874265 := bstep (se 2 (by rfl) ⟨327849, by rfl⟩ : syracuseStep 874265 = 655699) B655699
theorem B7094081 : Blo 582814 7094081 := bstep (se 2 (by rfl) ⟨2660280, by rfl⟩ : syracuseStep 7094081 = 5320561) B5320561
theorem B933707 : Blo 582814 933707 := bstep (se 1 (by rfl) ⟨700280, by rfl⟩ : syracuseStep 933707 = 1400561) B1400561
theorem B1476427 : Blo 582814 1476427 := bstep (se 1 (by rfl) ⟨1107320, by rfl⟩ : syracuseStep 1476427 = 2214641) B2214641
theorem B2101085 : Blo 582814 2101085 := bstep (se 3 (by rfl) ⟨393953, by rfl⟩ : syracuseStep 2101085 = 787907) B787907
theorem B874379 : Blo 582814 874379 := bstep (se 1 (by rfl) ⟨655784, by rfl⟩ : syracuseStep 874379 = 1311569) B1311569
theorem B874391 : Blo 582814 874391 := bstep (se 1 (by rfl) ⟨655793, by rfl⟩ : syracuseStep 874391 = 1311587) B1311587
theorem B874457 : Blo 582814 874457 := bstep (se 2 (by rfl) ⟨327921, by rfl⟩ : syracuseStep 874457 = 655843) B655843
theorem B874511 : Blo 582814 874511 := bstep (se 1 (by rfl) ⟨655883, by rfl⟩ : syracuseStep 874511 = 1311767) B1311767
theorem B874553 : Blo 582814 874553 := bstep (se 2 (by rfl) ⟨327957, by rfl⟩ : syracuseStep 874553 = 655915) B655915
theorem B3321917 : Blo 582814 3321917 := bstep (se 3 (by rfl) ⟨622859, by rfl⟩ : syracuseStep 3321917 = 1245719) B1245719
theorem B2101315 : Blo 582814 2101315 := bstep (se 1 (by rfl) ⟨1575986, by rfl⟩ : syracuseStep 2101315 = 3151973) B3151973
theorem B700535 : Blo 582814 700535 := bstep (se 1 (by rfl) ⟨525401, by rfl⟩ : syracuseStep 700535 = 1050803) B1050803
theorem B874631 : Blo 582814 874631 := bstep (se 1 (by rfl) ⟨655973, by rfl⟩ : syracuseStep 874631 = 1311947) B1311947
theorem B874667 : Blo 582814 874667 := bstep (se 1 (by rfl) ⟨656000, by rfl⟩ : syracuseStep 874667 = 1312001) B1312001
theorem B9959597 : Blo 582814 9959597 := bstep (se 3 (by rfl) ⟨1867424, by rfl⟩ : syracuseStep 9959597 = 3734849) B3734849
theorem B18917549 : Blo 582814 18917549 := bstep (se 3 (by rfl) ⟨3547040, by rfl⟩ : syracuseStep 18917549 = 7094081) B7094081
theorem B874697 : Blo 582814 874697 := bstep (se 2 (by rfl) ⟨328011, by rfl⟩ : syracuseStep 874697 = 656023) B656023
theorem B2214125 : Blo 582814 2214125 := bstep (se 3 (by rfl) ⟨415148, by rfl⟩ : syracuseStep 2214125 = 830297) B830297
theorem B1198379 : Blo 582814 1198379 := bstep (se 1 (by rfl) ⟨898784, by rfl⟩ : syracuseStep 1198379 = 1797569) B1797569
theorem B874811 : Blo 582814 874811 := bstep (se 1 (by rfl) ⟨656108, by rfl⟩ : syracuseStep 874811 = 1312217) B1312217
theorem B874871 : Blo 582814 874871 := bstep (se 1 (by rfl) ⟨656153, by rfl⟩ : syracuseStep 874871 = 1312307) B1312307
theorem B874895 : Blo 582814 874895 := bstep (se 1 (by rfl) ⟨656171, by rfl⟩ : syracuseStep 874895 = 1312343) B1312343
theorem B6732179 : Blo 582814 6732179 := bstep (se 1 (by rfl) ⟨5049134, by rfl⟩ : syracuseStep 6732179 = 10098269) B10098269
theorem B1968569 : Blo 582814 1968569 := bstep (se 2 (by rfl) ⟨738213, by rfl⟩ : syracuseStep 1968569 = 1476427) B1476427
theorem B655879 : Blo 582814 655879 := bstep (se 1 (by rfl) ⟨491909, by rfl⟩ : syracuseStep 655879 = 983819) B983819
theorem B6302387 : Blo 582814 6302387 := bstep (se 1 (by rfl) ⟨4726790, by rfl⟩ : syracuseStep 6302387 = 9453581) B9453581
theorem B656059 : Blo 582814 656059 := bstep (se 1 (by rfl) ⟨492044, by rfl⟩ : syracuseStep 656059 = 984089) B984089
theorem B1475273 : Blo 582814 1475273 := bstep (se 2 (by rfl) ⟨553227, by rfl⟩ : syracuseStep 1475273 = 1106455) B1106455
theorem B983927 : Blo 582814 983927 := bstep (se 1 (by rfl) ⟨737945, by rfl⟩ : syracuseStep 983927 = 1475891) B1475891
theorem B1311623 : Blo 582814 1311623 := bstep (se 1 (by rfl) ⟨983717, by rfl⟩ : syracuseStep 1311623 = 1967435) B1967435
theorem B2659225 : Blo 582814 2659225 := bstep (se 2 (by rfl) ⟨997209, by rfl⟩ : syracuseStep 2659225 = 1994419) B1994419
theorem B1475617 : Blo 582814 1475617 := bstep (se 2 (by rfl) ⟨553356, by rfl⟩ : syracuseStep 1475617 = 1106713) B1106713
theorem B1311803 : Blo 582814 1311803 := bstep (se 1 (by rfl) ⟨983852, by rfl⟩ : syracuseStep 1311803 = 1967705) B1967705
theorem B1967165 : Blo 582814 1967165 := bstep (se 3 (by rfl) ⟨368843, by rfl⟩ : syracuseStep 1967165 = 737687) B737687
theorem B272667779 : Blo 582814 272667779 := bstep (se 1 (by rfl) ⟨204500834, by rfl⟩ : syracuseStep 272667779 = 409001669) B409001669
theorem B1311929 : Blo 582814 1311929 := bstep (se 2 (by rfl) ⟨491973, by rfl⟩ : syracuseStep 1311929 = 983947) B983947
theorem B582843 : Blo 582814 582843 := bstep (se 1 (by rfl) ⟨437132, by rfl⟩ : syracuseStep 582843 = 874265) B874265
theorem B2952449 : Blo 582814 2952449 := bstep (se 2 (by rfl) ⟨1107168, by rfl⟩ : syracuseStep 2952449 = 2214337) B2214337
theorem B582919 : Blo 582814 582919 := bstep (se 1 (by rfl) ⟨437189, by rfl⟩ : syracuseStep 582919 = 874379) B874379
theorem B582927 : Blo 582814 582927 := bstep (se 1 (by rfl) ⟨437195, by rfl⟩ : syracuseStep 582927 = 874391) B874391
theorem B3153167 : Blo 582814 3153167 := bstep (se 1 (by rfl) ⟨2364875, by rfl⟩ : syracuseStep 3153167 = 4729751) B4729751
theorem B2213153 : Blo 582814 2213153 := bstep (se 2 (by rfl) ⟨829932, by rfl⟩ : syracuseStep 2213153 = 1659865) B1659865
theorem B582971 : Blo 582814 582971 := bstep (se 1 (by rfl) ⟨437228, by rfl⟩ : syracuseStep 582971 = 874457) B874457
theorem B583047 : Blo 582814 583047 := bstep (se 1 (by rfl) ⟨437285, by rfl⟩ : syracuseStep 583047 = 874571) B874571
theorem B583055 : Blo 582814 583055 := bstep (se 1 (by rfl) ⟨437291, by rfl⟩ : syracuseStep 583055 = 874583) B874583
theorem B3321233 : Blo 582814 3321233 := bstep (se 2 (by rfl) ⟨1245462, by rfl⟩ : syracuseStep 3321233 = 2490925) B2490925
theorem B583099 : Blo 582814 583099 := bstep (se 1 (by rfl) ⟨437324, by rfl⟩ : syracuseStep 583099 = 874649) B874649
theorem B583175 : Blo 582814 583175 := bstep (se 1 (by rfl) ⟨437381, by rfl⟩ : syracuseStep 583175 = 874763) B874763
theorem B2950667 : Blo 582814 2950667 := bstep (se 1 (by rfl) ⟨2213000, by rfl⟩ : syracuseStep 2950667 = 4426001) B4426001
theorem B583183 : Blo 582814 583183 := bstep (se 1 (by rfl) ⟨437387, by rfl⟩ : syracuseStep 583183 = 874775) B874775
theorem B1312271 : Blo 582814 1312271 := bstep (se 1 (by rfl) ⟨984203, by rfl⟩ : syracuseStep 1312271 = 1968407) B1968407
theorem B3319319 : Blo 582814 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B2489885 : Blo 582814 2489885 := bstep (se 3 (by rfl) ⟨466853, by rfl⟩ : syracuseStep 2489885 = 933707) B933707
theorem B1312289 : Blo 582814 1312289 := bstep (se 2 (by rfl) ⟨492108, by rfl⟩ : syracuseStep 1312289 = 984217) B984217
theorem B583227 : Blo 582814 583227 := bstep (se 1 (by rfl) ⟨437420, by rfl⟩ : syracuseStep 583227 = 874841) B874841
theorem B1476215 : Blo 582814 1476215 := bstep (se 1 (by rfl) ⟨1107161, by rfl⟩ : syracuseStep 1476215 = 2214323) B2214323
theorem B2950829 : Blo 582814 2950829 := bstep (se 3 (by rfl) ⟨553280, by rfl⟩ : syracuseStep 2950829 = 1106561) B1106561
theorem B886457 : Blo 582814 886457 := bstep (se 2 (by rfl) ⟨332421, by rfl⟩ : syracuseStep 886457 = 664843) B664843
theorem B4548325 : Blo 582814 4548325 := bstep (se 4 (by rfl) ⟨426405, by rfl⟩ : syracuseStep 4548325 = 852811) B852811
theorem B874247 : Blo 582814 874247 := bstep (se 1 (by rfl) ⟨655685, by rfl⟩ : syracuseStep 874247 = 1311371) B1311371
theorem B874283 : Blo 582814 874283 := bstep (se 1 (by rfl) ⟨655712, by rfl⟩ : syracuseStep 874283 = 1311425) B1311425
theorem B874313 : Blo 582814 874313 := bstep (se 2 (by rfl) ⟨327867, by rfl⟩ : syracuseStep 874313 = 655735) B655735
theorem B1400723 : Blo 582814 1400723 := bstep (se 1 (by rfl) ⟨1050542, by rfl⟩ : syracuseStep 1400723 = 2101085) B2101085
theorem B4728739 : Blo 582814 4728739 := bstep (se 1 (by rfl) ⟨3546554, by rfl⟩ : syracuseStep 4728739 = 7093109) B7093109
theorem B874427 : Blo 582814 874427 := bstep (se 1 (by rfl) ⟨655820, by rfl⟩ : syracuseStep 874427 = 1311641) B1311641
theorem B874487 : Blo 582814 874487 := bstep (se 1 (by rfl) ⟨655865, by rfl⟩ : syracuseStep 874487 = 1311731) B1311731
theorem B874505 : Blo 582814 874505 := bstep (se 2 (by rfl) ⟨327939, by rfl⟩ : syracuseStep 874505 = 655879) B655879
theorem B874535 : Blo 582814 874535 := bstep (se 1 (by rfl) ⟨655901, by rfl⟩ : syracuseStep 874535 = 1311803) B1311803
theorem B181778519 : Blo 582814 181778519 := bstep (se 1 (by rfl) ⟨136333889, by rfl⟩ : syracuseStep 181778519 = 272667779) B272667779
theorem B2801753 : Blo 582814 2801753 := bstep (se 2 (by rfl) ⟨1050657, by rfl⟩ : syracuseStep 2801753 = 2101315) B2101315
theorem B6639731 : Blo 582814 6639731 := bstep (se 1 (by rfl) ⟨4979798, by rfl⟩ : syracuseStep 6639731 = 9959597) B9959597
theorem B12611699 : Blo 582814 12611699 := bstep (se 1 (by rfl) ⟨9458774, by rfl⟩ : syracuseStep 12611699 = 18917549) B18917549
theorem B874619 : Blo 582814 874619 := bstep (se 1 (by rfl) ⟨655964, by rfl⟩ : syracuseStep 874619 = 1311929) B1311929
theorem B1968299 : Blo 582814 1968299 := bstep (se 1 (by rfl) ⟨1476224, by rfl⟩ : syracuseStep 1968299 = 2952449) B2952449
theorem B874745 : Blo 582814 874745 := bstep (se 2 (by rfl) ⟨328029, by rfl⟩ : syracuseStep 874745 = 656059) B656059
theorem B2214155 : Blo 582814 2214155 := bstep (se 1 (by rfl) ⟨1660616, by rfl⟩ : syracuseStep 2214155 = 3321233) B3321233
theorem B6064433 : Blo 582814 6064433 := bstep (se 2 (by rfl) ⟨2274162, by rfl⟩ : syracuseStep 6064433 = 4548325) B4548325
theorem B1868093 : Blo 582814 1868093 := bstep (se 3 (by rfl) ⟨350267, by rfl⟩ : syracuseStep 1868093 = 700535) B700535
theorem B874847 : Blo 582814 874847 := bstep (se 1 (by rfl) ⟨656135, by rfl⟩ : syracuseStep 874847 = 1312271) B1312271
theorem B874859 : Blo 582814 874859 := bstep (se 1 (by rfl) ⟨656144, by rfl⟩ : syracuseStep 874859 = 1312289) B1312289
theorem B983515 : Blo 582814 983515 := bstep (se 1 (by rfl) ⟨737636, by rfl⟩ : syracuseStep 983515 = 1475273) B1475273
theorem B16806365 : Blo 582814 16806365 := bstep (se 3 (by rfl) ⟨3151193, by rfl⟩ : syracuseStep 16806365 = 6302387) B6302387
theorem B3545633 : Blo 582814 3545633 := bstep (se 2 (by rfl) ⟨1329612, by rfl⟩ : syracuseStep 3545633 = 2659225) B2659225
theorem B655951 : Blo 582814 655951 := bstep (se 1 (by rfl) ⟨491963, by rfl⟩ : syracuseStep 655951 = 983927) B983927
theorem B1311443 : Blo 582814 1311443 := bstep (se 1 (by rfl) ⟨983582, by rfl⟩ : syracuseStep 1311443 = 1967165) B1967165
theorem B2214611 : Blo 582814 2214611 := bstep (se 1 (by rfl) ⟨1660958, by rfl⟩ : syracuseStep 2214611 = 3321917) B3321917
theorem B3195677 : Blo 582814 3195677 := bstep (se 3 (by rfl) ⟨599189, by rfl⟩ : syracuseStep 3195677 = 1198379) B1198379
theorem B2102111 : Blo 582814 2102111 := bstep (se 1 (by rfl) ⟨1576583, by rfl⟩ : syracuseStep 2102111 = 3153167) B3153167
theorem B1475435 : Blo 582814 1475435 := bstep (se 1 (by rfl) ⟨1106576, by rfl⟩ : syracuseStep 1475435 = 2213153) B2213153
theorem B4488119 : Blo 582814 4488119 := bstep (se 1 (by rfl) ⟨3366089, by rfl⟩ : syracuseStep 4488119 = 6732179) B6732179
theorem B1967111 : Blo 582814 1967111 := bstep (se 1 (by rfl) ⟨1475333, by rfl⟩ : syracuseStep 1967111 = 2950667) B2950667
theorem B2212879 : Blo 582814 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B1659923 : Blo 582814 1659923 := bstep (se 1 (by rfl) ⟨1244942, by rfl⟩ : syracuseStep 1659923 = 2489885) B2489885
theorem B984143 : Blo 582814 984143 := bstep (se 1 (by rfl) ⟨738107, by rfl⟩ : syracuseStep 984143 = 1476215) B1476215
theorem B1967219 : Blo 582814 1967219 := bstep (se 1 (by rfl) ⟨1475414, by rfl⟩ : syracuseStep 1967219 = 2950829) B2950829
theorem B590971 : Blo 582814 590971 := bstep (se 1 (by rfl) ⟨443228, by rfl⟩ : syracuseStep 590971 = 886457) B886457
theorem B582831 : Blo 582814 582831 := bstep (se 1 (by rfl) ⟨437123, by rfl⟩ : syracuseStep 582831 = 874247) B874247
theorem B582855 : Blo 582814 582855 := bstep (se 1 (by rfl) ⟨437141, by rfl⟩ : syracuseStep 582855 = 874283) B874283
theorem B6304985 : Blo 582814 6304985 := bstep (se 2 (by rfl) ⟨2364369, by rfl⟩ : syracuseStep 6304985 = 4728739) B4728739
theorem B582875 : Blo 582814 582875 := bstep (se 1 (by rfl) ⟨437156, by rfl⟩ : syracuseStep 582875 = 874313) B874313
theorem B582951 : Blo 582814 582951 := bstep (se 1 (by rfl) ⟨437213, by rfl⟩ : syracuseStep 582951 = 874427) B874427
theorem B582991 : Blo 582814 582991 := bstep (se 1 (by rfl) ⟨437243, by rfl⟩ : syracuseStep 582991 = 874487) B874487
theorem B583007 : Blo 582814 583007 := bstep (se 1 (by rfl) ⟨437255, by rfl⟩ : syracuseStep 583007 = 874511) B874511
theorem B583035 : Blo 582814 583035 := bstep (se 1 (by rfl) ⟨437276, by rfl⟩ : syracuseStep 583035 = 874553) B874553
theorem B1967489 : Blo 582814 1967489 := bstep (se 2 (by rfl) ⟨737808, by rfl⟩ : syracuseStep 1967489 = 1475617) B1475617
theorem B583087 : Blo 582814 583087 := bstep (se 1 (by rfl) ⟨437315, by rfl⟩ : syracuseStep 583087 = 874631) B874631
theorem B583111 : Blo 582814 583111 := bstep (se 1 (by rfl) ⟨437333, by rfl⟩ : syracuseStep 583111 = 874667) B874667
theorem B583131 : Blo 582814 583131 := bstep (se 1 (by rfl) ⟨437348, by rfl⟩ : syracuseStep 583131 = 874697) B874697
theorem B1476083 : Blo 582814 1476083 := bstep (se 1 (by rfl) ⟨1107062, by rfl⟩ : syracuseStep 1476083 = 2214125) B2214125
theorem B583207 : Blo 582814 583207 := bstep (se 1 (by rfl) ⟨437405, by rfl⟩ : syracuseStep 583207 = 874811) B874811
theorem B583247 : Blo 582814 583247 := bstep (se 1 (by rfl) ⟨437435, by rfl⟩ : syracuseStep 583247 = 874871) B874871
theorem B583263 : Blo 582814 583263 := bstep (se 1 (by rfl) ⟨437447, by rfl⟩ : syracuseStep 583263 = 874895) B874895
theorem B1312379 : Blo 582814 1312379 := bstep (se 1 (by rfl) ⟨984284, by rfl⟩ : syracuseStep 1312379 = 1968569) B1968569
theorem B874415 : Blo 582814 874415 := bstep (se 1 (by rfl) ⟨655811, by rfl⟩ : syracuseStep 874415 = 1311623) B1311623
theorem B933815 : Blo 582814 933815 := bstep (se 1 (by rfl) ⟨700361, by rfl⟩ : syracuseStep 933815 = 1400723) B1400723
theorem B1867835 : Blo 582814 1867835 := bstep (se 1 (by rfl) ⟨1400876, by rfl⟩ : syracuseStep 1867835 = 2801753) B2801753
theorem B8521805 : Blo 582814 8521805 := bstep (se 3 (by rfl) ⟨1597838, by rfl⟩ : syracuseStep 8521805 = 3195677) B3195677
theorem B874601 : Blo 582814 874601 := bstep (se 2 (by rfl) ⟨327975, by rfl⟩ : syracuseStep 874601 = 655951) B655951
theorem B4042955 : Blo 582814 4042955 := bstep (se 1 (by rfl) ⟨3032216, by rfl⟩ : syracuseStep 4042955 = 6064433) B6064433
theorem B1245395 : Blo 582814 1245395 := bstep (se 1 (by rfl) ⟨934046, by rfl⟩ : syracuseStep 1245395 = 1868093) B1868093
theorem B2363755 : Blo 582814 2363755 := bstep (se 1 (by rfl) ⟨1772816, by rfl⟩ : syracuseStep 2363755 = 3545633) B3545633
theorem B874919 : Blo 582814 874919 := bstep (se 1 (by rfl) ⟨656189, by rfl⟩ : syracuseStep 874919 = 1312379) B1312379
theorem B1401407 : Blo 582814 1401407 := bstep (se 1 (by rfl) ⟨1051055, by rfl⟩ : syracuseStep 1401407 = 2102111) B2102111
theorem B983623 : Blo 582814 983623 := bstep (se 1 (by rfl) ⟨737717, by rfl⟩ : syracuseStep 983623 = 1475435) B1475435
theorem B1311353 : Blo 582814 1311353 := bstep (se 2 (by rfl) ⟨491757, by rfl⟩ : syracuseStep 1311353 = 983515) B983515
theorem B1311407 : Blo 582814 1311407 := bstep (se 1 (by rfl) ⟨983555, by rfl⟩ : syracuseStep 1311407 = 1967111) B1967111
theorem B1106615 : Blo 582814 1106615 := bstep (se 1 (by rfl) ⟨829961, by rfl⟩ : syracuseStep 1106615 = 1659923) B1659923
theorem B656095 : Blo 582814 656095 := bstep (se 1 (by rfl) ⟨492071, by rfl⟩ : syracuseStep 656095 = 984143) B984143
theorem B1311479 : Blo 582814 1311479 := bstep (se 1 (by rfl) ⟨983609, by rfl⟩ : syracuseStep 1311479 = 1967219) B1967219
theorem B4426487 : Blo 582814 4426487 := bstep (se 1 (by rfl) ⟨3319865, by rfl⟩ : syracuseStep 4426487 = 6639731) B6639731
theorem B8407799 : Blo 582814 8407799 := bstep (se 1 (by rfl) ⟨6305849, by rfl⟩ : syracuseStep 8407799 = 12611699) B12611699
theorem B4203323 : Blo 582814 4203323 := bstep (se 1 (by rfl) ⟨3152492, by rfl⟩ : syracuseStep 4203323 = 6304985) B6304985
theorem B1311659 : Blo 582814 1311659 := bstep (se 1 (by rfl) ⟨983744, by rfl⟩ : syracuseStep 1311659 = 1967489) B1967489
theorem B984055 : Blo 582814 984055 := bstep (se 1 (by rfl) ⟨738041, by rfl⟩ : syracuseStep 984055 = 1476083) B1476083
theorem B582943 : Blo 582814 582943 := bstep (se 1 (by rfl) ⟨437207, by rfl⟩ : syracuseStep 582943 = 874415) B874415
theorem B583003 : Blo 582814 583003 := bstep (se 1 (by rfl) ⟨437252, by rfl⟩ : syracuseStep 583003 = 874505) B874505
theorem B2950505 : Blo 582814 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B583023 : Blo 582814 583023 := bstep (se 1 (by rfl) ⟨437267, by rfl⟩ : syracuseStep 583023 = 874535) B874535
theorem B121185679 : Blo 582814 121185679 := bstep (se 1 (by rfl) ⟨90889259, by rfl⟩ : syracuseStep 121185679 = 181778519) B181778519
theorem B583079 : Blo 582814 583079 := bstep (se 1 (by rfl) ⟨437309, by rfl⟩ : syracuseStep 583079 = 874619) B874619
theorem B1312199 : Blo 582814 1312199 := bstep (se 1 (by rfl) ⟨984149, by rfl⟩ : syracuseStep 1312199 = 1968299) B1968299
theorem B787961 : Blo 582814 787961 := bstep (se 2 (by rfl) ⟨295485, by rfl⟩ : syracuseStep 787961 = 590971) B590971
theorem B583163 : Blo 582814 583163 := bstep (se 1 (by rfl) ⟨437372, by rfl⟩ : syracuseStep 583163 = 874745) B874745
theorem B1476103 : Blo 582814 1476103 := bstep (se 1 (by rfl) ⟨1107077, by rfl⟩ : syracuseStep 1476103 = 2214155) B2214155
theorem B583231 : Blo 582814 583231 := bstep (se 1 (by rfl) ⟨437423, by rfl⟩ : syracuseStep 583231 = 874847) B874847
theorem B583239 : Blo 582814 583239 := bstep (se 1 (by rfl) ⟨437429, by rfl⟩ : syracuseStep 583239 = 874859) B874859
theorem B11204243 : Blo 582814 11204243 := bstep (se 1 (by rfl) ⟨8403182, by rfl⟩ : syracuseStep 11204243 = 16806365) B16806365
theorem B874295 : Blo 582814 874295 := bstep (se 1 (by rfl) ⟨655721, by rfl⟩ : syracuseStep 874295 = 1311443) B1311443
theorem B1476407 : Blo 582814 1476407 := bstep (se 1 (by rfl) ⟨1107305, by rfl⟩ : syracuseStep 1476407 = 2214611) B2214611
theorem B2490173 : Blo 582814 2490173 := bstep (se 3 (by rfl) ⟨466907, by rfl⟩ : syracuseStep 2490173 = 933815) B933815
theorem B2992079 : Blo 582814 2992079 := bstep (se 1 (by rfl) ⟨2244059, by rfl⟩ : syracuseStep 2992079 = 4488119) B4488119
theorem B1968137 : Blo 582814 1968137 := bstep (se 2 (by rfl) ⟨738051, by rfl⟩ : syracuseStep 1968137 = 1476103) B1476103
theorem B1245223 : Blo 582814 1245223 := bstep (se 1 (by rfl) ⟨933917, by rfl⟩ : syracuseStep 1245223 = 1867835) B1867835
theorem B2695303 : Blo 582814 2695303 := bstep (se 1 (by rfl) ⟨2021477, by rfl⟩ : syracuseStep 2695303 = 4042955) B4042955
theorem B22724813 : Blo 582814 22724813 := bstep (se 3 (by rfl) ⟨4260902, by rfl⟩ : syracuseStep 22724813 = 8521805) B8521805
theorem B874793 : Blo 582814 874793 := bstep (se 2 (by rfl) ⟨328047, by rfl⟩ : syracuseStep 874793 = 656095) B656095
theorem B874799 : Blo 582814 874799 := bstep (se 1 (by rfl) ⟨656099, by rfl⟩ : syracuseStep 874799 = 1312199) B1312199
theorem B934271 : Blo 582814 934271 := bstep (se 1 (by rfl) ⟨700703, by rfl⟩ : syracuseStep 934271 = 1401407) B1401407
theorem B7469495 : Blo 582814 7469495 := bstep (se 1 (by rfl) ⟨5602121, by rfl⟩ : syracuseStep 7469495 = 11204243) B11204243
theorem B737743 : Blo 582814 737743 := bstep (se 1 (by rfl) ⟨553307, by rfl⟩ : syracuseStep 737743 = 1106615) B1106615
theorem B2802215 : Blo 582814 2802215 := bstep (se 1 (by rfl) ⟨2101661, by rfl⟩ : syracuseStep 2802215 = 4203323) B4203323
theorem B1311497 : Blo 582814 1311497 := bstep (se 2 (by rfl) ⟨491811, by rfl⟩ : syracuseStep 1311497 = 983623) B983623
theorem B830263 : Blo 582814 830263 := bstep (se 1 (by rfl) ⟨622697, by rfl⟩ : syracuseStep 830263 = 1245395) B1245395
theorem B1967003 : Blo 582814 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B582863 : Blo 582814 582863 := bstep (se 1 (by rfl) ⟨437147, by rfl⟩ : syracuseStep 582863 = 874295) B874295
theorem B984271 : Blo 582814 984271 := bstep (se 1 (by rfl) ⟨738203, by rfl⟩ : syracuseStep 984271 = 1476407) B1476407
theorem B1660115 : Blo 582814 1660115 := bstep (se 1 (by rfl) ⟨1245086, by rfl⟩ : syracuseStep 1660115 = 2490173) B2490173
theorem B1312073 : Blo 582814 1312073 := bstep (se 2 (by rfl) ⟨492027, by rfl⟩ : syracuseStep 1312073 = 984055) B984055
theorem B583067 : Blo 582814 583067 := bstep (se 1 (by rfl) ⟨437300, by rfl⟩ : syracuseStep 583067 = 874601) B874601
theorem B583279 : Blo 582814 583279 := bstep (se 1 (by rfl) ⟨437459, by rfl⟩ : syracuseStep 583279 = 874919) B874919
theorem B874235 : Blo 582814 874235 := bstep (se 1 (by rfl) ⟨655676, by rfl⟩ : syracuseStep 874235 = 1311353) B1311353
theorem B874271 : Blo 582814 874271 := bstep (se 1 (by rfl) ⟨655703, by rfl⟩ : syracuseStep 874271 = 1311407) B1311407
theorem B3151673 : Blo 582814 3151673 := bstep (se 2 (by rfl) ⟨1181877, by rfl⟩ : syracuseStep 3151673 = 2363755) B2363755
theorem B874319 : Blo 582814 874319 := bstep (se 1 (by rfl) ⟨655739, by rfl⟩ : syracuseStep 874319 = 1311479) B1311479
theorem B2950991 : Blo 582814 2950991 := bstep (se 1 (by rfl) ⟨2213243, by rfl⟩ : syracuseStep 2950991 = 4426487) B4426487
theorem B5605199 : Blo 582814 5605199 := bstep (se 1 (by rfl) ⟨4203899, by rfl⟩ : syracuseStep 5605199 = 8407799) B8407799
theorem B161580905 : Blo 582814 161580905 := bstep (se 2 (by rfl) ⟨60592839, by rfl⟩ : syracuseStep 161580905 = 121185679) B121185679
theorem B874439 : Blo 582814 874439 := bstep (se 1 (by rfl) ⟨655829, by rfl⟩ : syracuseStep 874439 = 1311659) B1311659
theorem B1994719 : Blo 582814 1994719 := bstep (se 1 (by rfl) ⟨1496039, by rfl⟩ : syracuseStep 1994719 = 2992079) B2992079
theorem B2101229 : Blo 582814 2101229 := bstep (se 3 (by rfl) ⟨393980, by rfl⟩ : syracuseStep 2101229 = 787961) B787961
theorem B874715 : Blo 582814 874715 := bstep (se 1 (by rfl) ⟨656036, by rfl⟩ : syracuseStep 874715 = 1312073) B1312073
theorem B622847 : Blo 582814 622847 := bstep (se 1 (by rfl) ⟨467135, by rfl⟩ : syracuseStep 622847 = 934271) B934271
theorem B1868143 : Blo 582814 1868143 := bstep (se 1 (by rfl) ⟨1401107, by rfl⟩ : syracuseStep 1868143 = 2802215) B2802215
theorem B1311335 : Blo 582814 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B983657 : Blo 582814 983657 := bstep (se 2 (by rfl) ⟨368871, by rfl⟩ : syracuseStep 983657 = 737743) B737743
theorem B4979663 : Blo 582814 4979663 := bstep (se 1 (by rfl) ⟨3734747, by rfl⟩ : syracuseStep 4979663 = 7469495) B7469495
theorem B1107017 : Blo 582814 1107017 := bstep (se 2 (by rfl) ⟨415131, by rfl⟩ : syracuseStep 1107017 = 830263) B830263
theorem B582823 : Blo 582814 582823 := bstep (se 1 (by rfl) ⟨437117, by rfl⟩ : syracuseStep 582823 = 874235) B874235
theorem B582847 : Blo 582814 582847 := bstep (se 1 (by rfl) ⟨437135, by rfl⟩ : syracuseStep 582847 = 874271) B874271
theorem B60599501 : Blo 582814 60599501 := bstep (se 3 (by rfl) ⟨11362406, by rfl⟩ : syracuseStep 60599501 = 22724813) B22724813
theorem B4426973 : Blo 582814 4426973 := bstep (se 3 (by rfl) ⟨830057, by rfl⟩ : syracuseStep 4426973 = 1660115) B1660115
theorem B582879 : Blo 582814 582879 := bstep (se 1 (by rfl) ⟨437159, by rfl⟩ : syracuseStep 582879 = 874319) B874319
theorem B1967327 : Blo 582814 1967327 := bstep (se 1 (by rfl) ⟨1475495, by rfl⟩ : syracuseStep 1967327 = 2950991) B2950991
theorem B3736799 : Blo 582814 3736799 := bstep (se 1 (by rfl) ⟨2802599, by rfl⟩ : syracuseStep 3736799 = 5605199) B5605199
theorem B2659625 : Blo 582814 2659625 := bstep (se 2 (by rfl) ⟨997359, by rfl⟩ : syracuseStep 2659625 = 1994719) B1994719
theorem B582959 : Blo 582814 582959 := bstep (se 1 (by rfl) ⟨437219, by rfl⟩ : syracuseStep 582959 = 874439) B874439
theorem B1312091 : Blo 582814 1312091 := bstep (se 1 (by rfl) ⟨984068, by rfl⟩ : syracuseStep 1312091 = 1968137) B1968137
theorem B3593737 : Blo 582814 3593737 := bstep (se 2 (by rfl) ⟨1347651, by rfl⟩ : syracuseStep 3593737 = 2695303) B2695303
theorem B583195 : Blo 582814 583195 := bstep (se 1 (by rfl) ⟨437396, by rfl⟩ : syracuseStep 583195 = 874793) B874793
theorem B583199 : Blo 582814 583199 := bstep (se 1 (by rfl) ⟨437399, by rfl⟩ : syracuseStep 583199 = 874799) B874799
theorem B6641189 : Blo 582814 6641189 := bstep (se 4 (by rfl) ⟨622611, by rfl⟩ : syracuseStep 6641189 = 1245223) B1245223
theorem B1312361 : Blo 582814 1312361 := bstep (se 2 (by rfl) ⟨492135, by rfl⟩ : syracuseStep 1312361 = 984271) B984271
theorem B874331 : Blo 582814 874331 := bstep (se 1 (by rfl) ⟨655748, by rfl⟩ : syracuseStep 874331 = 1311497) B1311497
theorem B2101115 : Blo 582814 2101115 := bstep (se 1 (by rfl) ⟨1575836, by rfl⟩ : syracuseStep 2101115 = 3151673) B3151673
theorem B107720603 : Blo 582814 107720603 := bstep (se 1 (by rfl) ⟨80790452, by rfl⟩ : syracuseStep 107720603 = 161580905) B161580905
theorem B1400819 : Blo 582814 1400819 := bstep (se 1 (by rfl) ⟨1050614, by rfl⟩ : syracuseStep 1400819 = 2101229) B2101229
theorem B2951315 : Blo 582814 2951315 := bstep (se 1 (by rfl) ⟨2213486, by rfl⟩ : syracuseStep 2951315 = 4426973) B4426973
theorem B874727 : Blo 582814 874727 := bstep (se 1 (by rfl) ⟨656045, by rfl⟩ : syracuseStep 874727 = 1312091) B1312091
theorem B655771 : Blo 582814 655771 := bstep (se 1 (by rfl) ⟨491828, by rfl⟩ : syracuseStep 655771 = 983657) B983657
theorem B874907 : Blo 582814 874907 := bstep (se 1 (by rfl) ⟨656180, by rfl⟩ : syracuseStep 874907 = 1312361) B1312361
theorem B2490857 : Blo 582814 2490857 := bstep (se 2 (by rfl) ⟨934071, by rfl⟩ : syracuseStep 2490857 = 1868143) B1868143
theorem B71813735 : Blo 582814 71813735 := bstep (se 1 (by rfl) ⟨53860301, by rfl⟩ : syracuseStep 71813735 = 107720603) B107720603
theorem B1660925 : Blo 582814 1660925 := bstep (se 3 (by rfl) ⟨311423, by rfl⟩ : syracuseStep 1660925 = 622847) B622847
theorem B738011 : Blo 582814 738011 := bstep (se 1 (by rfl) ⟨553508, by rfl⟩ : syracuseStep 738011 = 1107017) B1107017
theorem B40399667 : Blo 582814 40399667 := bstep (se 1 (by rfl) ⟨30299750, by rfl⟩ : syracuseStep 40399667 = 60599501) B60599501
theorem B1311551 : Blo 582814 1311551 := bstep (se 1 (by rfl) ⟨983663, by rfl⟩ : syracuseStep 1311551 = 1967327) B1967327
theorem B2491199 : Blo 582814 2491199 := bstep (se 1 (by rfl) ⟨1868399, by rfl⟩ : syracuseStep 2491199 = 3736799) B3736799
theorem B582887 : Blo 582814 582887 := bstep (se 1 (by rfl) ⟨437165, by rfl⟩ : syracuseStep 582887 = 874331) B874331
theorem B4791649 : Blo 582814 4791649 := bstep (se 2 (by rfl) ⟨1796868, by rfl⟩ : syracuseStep 4791649 = 3593737) B3593737
theorem B583143 : Blo 582814 583143 := bstep (se 1 (by rfl) ⟨437357, by rfl⟩ : syracuseStep 583143 = 874715) B874715
theorem B1773083 : Blo 582814 1773083 := bstep (se 1 (by rfl) ⟨1329812, by rfl⟩ : syracuseStep 1773083 = 2659625) B2659625
theorem B4427459 : Blo 582814 4427459 := bstep (se 1 (by rfl) ⟨3320594, by rfl⟩ : syracuseStep 4427459 = 6641189) B6641189
theorem B874223 : Blo 582814 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B1400743 : Blo 582814 1400743 := bstep (se 1 (by rfl) ⟨1050557, by rfl⟩ : syracuseStep 1400743 = 2101115) B2101115
theorem B3735517 : Blo 582814 3735517 := bstep (se 3 (by rfl) ⟨700409, by rfl⟩ : syracuseStep 3735517 = 1400819) B1400819
theorem B3319775 : Blo 582814 3319775 := bstep (se 1 (by rfl) ⟨2489831, by rfl⟩ : syracuseStep 3319775 = 4979663) B4979663
theorem B1182055 : Blo 582814 1182055 := bstep (se 1 (by rfl) ⟨886541, by rfl⟩ : syracuseStep 1182055 = 1773083) B1773083
theorem B2951639 : Blo 582814 2951639 := bstep (se 1 (by rfl) ⟨2213729, by rfl⟩ : syracuseStep 2951639 = 4427459) B4427459
theorem B6388865 : Blo 582814 6388865 := bstep (se 2 (by rfl) ⟨2395824, by rfl⟩ : syracuseStep 6388865 = 4791649) B4791649
theorem B582815 : Blo 582814 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B2213183 : Blo 582814 2213183 := bstep (se 1 (by rfl) ⟨1659887, by rfl⟩ : syracuseStep 2213183 = 3319775) B3319775
theorem B1107283 : Blo 582814 1107283 := bstep (se 1 (by rfl) ⟨830462, by rfl⟩ : syracuseStep 1107283 = 1660925) B1660925
theorem B1967543 : Blo 582814 1967543 := bstep (se 1 (by rfl) ⟨1475657, by rfl⟩ : syracuseStep 1967543 = 2951315) B2951315
theorem B583151 : Blo 582814 583151 := bstep (se 1 (by rfl) ⟨437363, by rfl⟩ : syracuseStep 583151 = 874727) B874727
theorem B583271 : Blo 582814 583271 := bstep (se 1 (by rfl) ⟨437453, by rfl⟩ : syracuseStep 583271 = 874907) B874907
theorem B1660571 : Blo 582814 1660571 := bstep (se 1 (by rfl) ⟨1245428, by rfl⟩ : syracuseStep 1660571 = 2490857) B2490857
theorem B47875823 : Blo 582814 47875823 := bstep (se 1 (by rfl) ⟨35906867, by rfl⟩ : syracuseStep 47875823 = 71813735) B71813735
theorem B26933111 : Blo 582814 26933111 := bstep (se 1 (by rfl) ⟨20199833, by rfl⟩ : syracuseStep 26933111 = 40399667) B40399667
theorem B874361 : Blo 582814 874361 := bstep (se 2 (by rfl) ⟨327885, by rfl⟩ : syracuseStep 874361 = 655771) B655771
theorem B874367 : Blo 582814 874367 := bstep (se 1 (by rfl) ⟨655775, by rfl⟩ : syracuseStep 874367 = 1311551) B1311551
theorem B1660799 : Blo 582814 1660799 := bstep (se 1 (by rfl) ⟨1245599, by rfl⟩ : syracuseStep 1660799 = 2491199) B2491199
theorem B1867657 : Blo 582814 1867657 := bstep (se 2 (by rfl) ⟨700371, by rfl⟩ : syracuseStep 1867657 = 1400743) B1400743
theorem B1968029 : Blo 582814 1968029 := bstep (se 3 (by rfl) ⟨369005, by rfl⟩ : syracuseStep 1968029 = 738011) B738011
theorem B4980689 : Blo 582814 4980689 := bstep (se 2 (by rfl) ⟨1867758, by rfl⟩ : syracuseStep 4980689 = 3735517) B3735517
theorem B17955407 : Blo 582814 17955407 := bstep (se 1 (by rfl) ⟨13466555, by rfl⟩ : syracuseStep 17955407 = 26933111) B26933111
theorem B3320459 : Blo 582814 3320459 := bstep (se 1 (by rfl) ⟨2490344, by rfl⟩ : syracuseStep 3320459 = 4980689) B4980689
theorem B1475455 : Blo 582814 1475455 := bstep (se 1 (by rfl) ⟨1106591, by rfl⟩ : syracuseStep 1475455 = 2213183) B2213183
theorem B1311695 : Blo 582814 1311695 := bstep (se 1 (by rfl) ⟨983771, by rfl⟩ : syracuseStep 1311695 = 1967543) B1967543
theorem B1107047 : Blo 582814 1107047 := bstep (se 1 (by rfl) ⟨830285, by rfl⟩ : syracuseStep 1107047 = 1660571) B1660571
theorem B1576073 : Blo 582814 1576073 := bstep (se 2 (by rfl) ⟨591027, by rfl⟩ : syracuseStep 1576073 = 1182055) B1182055
theorem B31917215 : Blo 582814 31917215 := bstep (se 1 (by rfl) ⟨23937911, by rfl⟩ : syracuseStep 31917215 = 47875823) B47875823
theorem B582907 : Blo 582814 582907 := bstep (se 1 (by rfl) ⟨437180, by rfl⟩ : syracuseStep 582907 = 874361) B874361
theorem B582911 : Blo 582814 582911 := bstep (se 1 (by rfl) ⟨437183, by rfl⟩ : syracuseStep 582911 = 874367) B874367
theorem B1107199 : Blo 582814 1107199 := bstep (se 1 (by rfl) ⟨830399, by rfl⟩ : syracuseStep 1107199 = 1660799) B1660799
theorem B1312019 : Blo 582814 1312019 := bstep (se 1 (by rfl) ⟨984014, by rfl⟩ : syracuseStep 1312019 = 1968029) B1968029
theorem B4259243 : Blo 582814 4259243 := bstep (se 1 (by rfl) ⟨3194432, by rfl⟩ : syracuseStep 4259243 = 6388865) B6388865
theorem B1967759 : Blo 582814 1967759 := bstep (se 1 (by rfl) ⟨1475819, by rfl⟩ : syracuseStep 1967759 = 2951639) B2951639
theorem B1476377 : Blo 582814 1476377 := bstep (se 2 (by rfl) ⟨553641, by rfl⟩ : syracuseStep 1476377 = 1107283) B1107283
theorem B2490209 : Blo 582814 2490209 := bstep (se 2 (by rfl) ⟨933828, by rfl⟩ : syracuseStep 2490209 = 1867657) B1867657
theorem B1050715 : Blo 582814 1050715 := bstep (se 1 (by rfl) ⟨788036, by rfl⟩ : syracuseStep 1050715 = 1576073) B1576073
theorem B874679 : Blo 582814 874679 := bstep (se 1 (by rfl) ⟨656009, by rfl⟩ : syracuseStep 874679 = 1312019) B1312019
theorem B2952125 : Blo 582814 2952125 := bstep (se 3 (by rfl) ⟨553523, by rfl⟩ : syracuseStep 2952125 = 1107047) B1107047
theorem B1311839 : Blo 582814 1311839 := bstep (se 1 (by rfl) ⟨983879, by rfl⟩ : syracuseStep 1311839 = 1967759) B1967759
theorem B1967273 : Blo 582814 1967273 := bstep (se 2 (by rfl) ⟨737727, by rfl⟩ : syracuseStep 1967273 = 1475455) B1475455
theorem B984251 : Blo 582814 984251 := bstep (se 1 (by rfl) ⟨738188, by rfl⟩ : syracuseStep 984251 = 1476377) B1476377
theorem B1660139 : Blo 582814 1660139 := bstep (se 1 (by rfl) ⟨1245104, by rfl⟩ : syracuseStep 1660139 = 2490209) B2490209
theorem B21278143 : Blo 582814 21278143 := bstep (se 1 (by rfl) ⟨15958607, by rfl⟩ : syracuseStep 21278143 = 31917215) B31917215
theorem B1476265 : Blo 582814 1476265 := bstep (se 2 (by rfl) ⟨553599, by rfl⟩ : syracuseStep 1476265 = 1107199) B1107199
theorem B11970271 : Blo 582814 11970271 := bstep (se 1 (by rfl) ⟨8977703, by rfl⟩ : syracuseStep 11970271 = 17955407) B17955407
theorem B2213639 : Blo 582814 2213639 := bstep (se 1 (by rfl) ⟨1660229, by rfl⟩ : syracuseStep 2213639 = 3320459) B3320459
theorem B11357981 : Blo 582814 11357981 := bstep (se 3 (by rfl) ⟨2129621, by rfl⟩ : syracuseStep 11357981 = 4259243) B4259243
theorem B874463 : Blo 582814 874463 := bstep (se 1 (by rfl) ⟨655847, by rfl⟩ : syracuseStep 874463 = 1311695) B1311695
theorem B874559 : Blo 582814 874559 := bstep (se 1 (by rfl) ⟨655919, by rfl⟩ : syracuseStep 874559 = 1311839) B1311839
theorem B1968353 : Blo 582814 1968353 := bstep (se 2 (by rfl) ⟨738132, by rfl⟩ : syracuseStep 1968353 = 1476265) B1476265
theorem B15960361 : Blo 582814 15960361 := bstep (se 2 (by rfl) ⟨5985135, by rfl⟩ : syracuseStep 15960361 = 11970271) B11970271
theorem B5603813 : Blo 582814 5603813 := bstep (se 4 (by rfl) ⟨525357, by rfl⟩ : syracuseStep 5603813 = 1050715) B1050715
theorem B7571987 : Blo 582814 7571987 := bstep (se 1 (by rfl) ⟨5678990, by rfl⟩ : syracuseStep 7571987 = 11357981) B11357981
theorem B1311515 : Blo 582814 1311515 := bstep (se 1 (by rfl) ⟨983636, by rfl⟩ : syracuseStep 1311515 = 1967273) B1967273
theorem B656167 : Blo 582814 656167 := bstep (se 1 (by rfl) ⟨492125, by rfl⟩ : syracuseStep 656167 = 984251) B984251
theorem B1106759 : Blo 582814 1106759 := bstep (se 1 (by rfl) ⟨830069, by rfl⟩ : syracuseStep 1106759 = 1660139) B1660139
theorem B1475759 : Blo 582814 1475759 := bstep (se 1 (by rfl) ⟨1106819, by rfl⟩ : syracuseStep 1475759 = 2213639) B2213639
theorem B582975 : Blo 582814 582975 := bstep (se 1 (by rfl) ⟨437231, by rfl⟩ : syracuseStep 582975 = 874463) B874463
theorem B583119 : Blo 582814 583119 := bstep (se 1 (by rfl) ⟨437339, by rfl⟩ : syracuseStep 583119 = 874679) B874679
theorem B28370857 : Blo 582814 28370857 := bstep (se 2 (by rfl) ⟨10639071, by rfl⟩ : syracuseStep 28370857 = 21278143) B21278143
theorem B1968083 : Blo 582814 1968083 := bstep (se 1 (by rfl) ⟨1476062, by rfl⟩ : syracuseStep 1968083 = 2952125) B2952125
theorem B3735875 : Blo 582814 3735875 := bstep (se 1 (by rfl) ⟨2801906, by rfl⟩ : syracuseStep 3735875 = 5603813) B5603813
theorem B874889 : Blo 582814 874889 := bstep (se 2 (by rfl) ⟨328083, by rfl⟩ : syracuseStep 874889 = 656167) B656167
theorem B737839 : Blo 582814 737839 := bstep (se 1 (by rfl) ⟨553379, by rfl⟩ : syracuseStep 737839 = 1106759) B1106759
theorem B983839 : Blo 582814 983839 := bstep (se 1 (by rfl) ⟨737879, by rfl⟩ : syracuseStep 983839 = 1475759) B1475759
theorem B37827809 : Blo 582814 37827809 := bstep (se 2 (by rfl) ⟨14185428, by rfl⟩ : syracuseStep 37827809 = 28370857) B28370857
theorem B1312055 : Blo 582814 1312055 := bstep (se 1 (by rfl) ⟨984041, by rfl⟩ : syracuseStep 1312055 = 1968083) B1968083
theorem B583039 : Blo 582814 583039 := bstep (se 1 (by rfl) ⟨437279, by rfl⟩ : syracuseStep 583039 = 874559) B874559
theorem B1312235 : Blo 582814 1312235 := bstep (se 1 (by rfl) ⟨984176, by rfl⟩ : syracuseStep 1312235 = 1968353) B1968353
theorem B5047991 : Blo 582814 5047991 := bstep (se 1 (by rfl) ⟨3785993, by rfl⟩ : syracuseStep 5047991 = 7571987) B7571987
theorem B21280481 : Blo 582814 21280481 := bstep (se 2 (by rfl) ⟨7980180, by rfl⟩ : syracuseStep 21280481 = 15960361) B15960361
theorem B874343 : Blo 582814 874343 := bstep (se 1 (by rfl) ⟨655757, by rfl⟩ : syracuseStep 874343 = 1311515) B1311515
theorem B874703 : Blo 582814 874703 := bstep (se 1 (by rfl) ⟨656027, by rfl⟩ : syracuseStep 874703 = 1312055) B1312055
theorem B2490583 : Blo 582814 2490583 := bstep (se 1 (by rfl) ⟨1867937, by rfl⟩ : syracuseStep 2490583 = 3735875) B3735875
theorem B874823 : Blo 582814 874823 := bstep (se 1 (by rfl) ⟨656117, by rfl⟩ : syracuseStep 874823 = 1312235) B1312235
theorem B3365327 : Blo 582814 3365327 := bstep (se 1 (by rfl) ⟨2523995, by rfl⟩ : syracuseStep 3365327 = 5047991) B5047991
theorem B14186987 : Blo 582814 14186987 := bstep (se 1 (by rfl) ⟨10640240, by rfl⟩ : syracuseStep 14186987 = 21280481) B21280481
theorem B983785 : Blo 582814 983785 := bstep (se 2 (by rfl) ⟨368919, by rfl⟩ : syracuseStep 983785 = 737839) B737839
theorem B1311785 : Blo 582814 1311785 := bstep (se 2 (by rfl) ⟨491919, by rfl⟩ : syracuseStep 1311785 = 983839) B983839
theorem B582895 : Blo 582814 582895 := bstep (se 1 (by rfl) ⟨437171, by rfl⟩ : syracuseStep 582895 = 874343) B874343
theorem B25218539 : Blo 582814 25218539 := bstep (se 1 (by rfl) ⟨18913904, by rfl⟩ : syracuseStep 25218539 = 37827809) B37827809
theorem B583259 : Blo 582814 583259 := bstep (se 1 (by rfl) ⟨437444, by rfl⟩ : syracuseStep 583259 = 874889) B874889
theorem B874523 : Blo 582814 874523 := bstep (se 1 (by rfl) ⟨655892, by rfl⟩ : syracuseStep 874523 = 1311785) B1311785
theorem B16812359 : Blo 582814 16812359 := bstep (se 1 (by rfl) ⟨12609269, by rfl⟩ : syracuseStep 16812359 = 25218539) B25218539
theorem B9457991 : Blo 582814 9457991 := bstep (se 1 (by rfl) ⟨7093493, by rfl⟩ : syracuseStep 9457991 = 14186987) B14186987
theorem B3320777 : Blo 582814 3320777 := bstep (se 2 (by rfl) ⟨1245291, by rfl⟩ : syracuseStep 3320777 = 2490583) B2490583
theorem B2243551 : Blo 582814 2243551 := bstep (se 1 (by rfl) ⟨1682663, by rfl⟩ : syracuseStep 2243551 = 3365327) B3365327
theorem B1311713 : Blo 582814 1311713 := bstep (se 2 (by rfl) ⟨491892, by rfl⟩ : syracuseStep 1311713 = 983785) B983785
theorem B583135 : Blo 582814 583135 := bstep (se 1 (by rfl) ⟨437351, by rfl⟩ : syracuseStep 583135 = 874703) B874703
theorem B583215 : Blo 582814 583215 := bstep (se 1 (by rfl) ⟨437411, by rfl⟩ : syracuseStep 583215 = 874823) B874823
theorem B2991401 : Blo 582814 2991401 := bstep (se 2 (by rfl) ⟨1121775, by rfl⟩ : syracuseStep 2991401 = 2243551) B2243551
theorem B583015 : Blo 582814 583015 := bstep (se 1 (by rfl) ⟨437261, by rfl⟩ : syracuseStep 583015 = 874523) B874523
theorem B11208239 : Blo 582814 11208239 := bstep (se 1 (by rfl) ⟨8406179, by rfl⟩ : syracuseStep 11208239 = 16812359) B16812359
theorem B6305327 : Blo 582814 6305327 := bstep (se 1 (by rfl) ⟨4728995, by rfl⟩ : syracuseStep 6305327 = 9457991) B9457991
theorem B2213851 : Blo 582814 2213851 := bstep (se 1 (by rfl) ⟨1660388, by rfl⟩ : syracuseStep 2213851 = 3320777) B3320777
theorem B874475 : Blo 582814 874475 := bstep (se 1 (by rfl) ⟨655856, by rfl⟩ : syracuseStep 874475 = 1311713) B1311713
theorem B2951801 : Blo 582814 2951801 := bstep (se 2 (by rfl) ⟨1106925, by rfl⟩ : syracuseStep 2951801 = 2213851) B2213851
theorem B7472159 : Blo 582814 7472159 := bstep (se 1 (by rfl) ⟨5604119, by rfl⟩ : syracuseStep 7472159 = 11208239) B11208239
theorem B4203551 : Blo 582814 4203551 := bstep (se 1 (by rfl) ⟨3152663, by rfl⟩ : syracuseStep 4203551 = 6305327) B6305327
theorem B582983 : Blo 582814 582983 := bstep (se 1 (by rfl) ⟨437237, by rfl⟩ : syracuseStep 582983 = 874475) B874475
theorem B1994267 : Blo 582814 1994267 := bstep (se 1 (by rfl) ⟨1495700, by rfl⟩ : syracuseStep 1994267 = 2991401) B2991401
theorem B4981439 : Blo 582814 4981439 := bstep (se 1 (by rfl) ⟨3736079, by rfl⟩ : syracuseStep 4981439 = 7472159) B7472159
theorem B2802367 : Blo 582814 2802367 := bstep (se 1 (by rfl) ⟨2101775, by rfl⟩ : syracuseStep 2802367 = 4203551) B4203551
theorem B5318045 : Blo 582814 5318045 := bstep (se 3 (by rfl) ⟨997133, by rfl⟩ : syracuseStep 5318045 = 1994267) B1994267
theorem B1967867 : Blo 582814 1967867 := bstep (se 1 (by rfl) ⟨1475900, by rfl⟩ : syracuseStep 1967867 = 2951801) B2951801
theorem B3545363 : Blo 582814 3545363 := bstep (se 1 (by rfl) ⟨2659022, by rfl⟩ : syracuseStep 3545363 = 5318045) B5318045
theorem B3320959 : Blo 582814 3320959 := bstep (se 1 (by rfl) ⟨2490719, by rfl⟩ : syracuseStep 3320959 = 4981439) B4981439
theorem B1311911 : Blo 582814 1311911 := bstep (se 1 (by rfl) ⟨983933, by rfl⟩ : syracuseStep 1311911 = 1967867) B1967867
theorem B14945957 : Blo 582814 14945957 := bstep (se 4 (by rfl) ⟨1401183, by rfl⟩ : syracuseStep 14945957 = 2802367) B2802367
theorem B874607 : Blo 582814 874607 := bstep (se 1 (by rfl) ⟨655955, by rfl⟩ : syracuseStep 874607 = 1311911) B1311911
theorem B4427945 : Blo 582814 4427945 := bstep (se 2 (by rfl) ⟨1660479, by rfl⟩ : syracuseStep 4427945 = 3320959) B3320959
theorem B2363575 : Blo 582814 2363575 := bstep (se 1 (by rfl) ⟨1772681, by rfl⟩ : syracuseStep 2363575 = 3545363) B3545363
theorem B9963971 : Blo 582814 9963971 := bstep (se 1 (by rfl) ⟨7472978, by rfl⟩ : syracuseStep 9963971 = 14945957) B14945957
theorem B2951963 : Blo 582814 2951963 := bstep (se 1 (by rfl) ⟨2213972, by rfl⟩ : syracuseStep 2951963 = 4427945) B4427945
theorem B6642647 : Blo 582814 6642647 := bstep (se 1 (by rfl) ⟨4981985, by rfl⟩ : syracuseStep 6642647 = 9963971) B9963971
theorem B583071 : Blo 582814 583071 := bstep (se 1 (by rfl) ⟨437303, by rfl⟩ : syracuseStep 583071 = 874607) B874607
theorem B3151433 : Blo 582814 3151433 := bstep (se 2 (by rfl) ⟨1181787, by rfl⟩ : syracuseStep 3151433 = 2363575) B2363575
theorem B4428431 : Blo 582814 4428431 := bstep (se 1 (by rfl) ⟨3321323, by rfl⟩ : syracuseStep 4428431 = 6642647) B6642647
theorem B8403821 : Blo 582814 8403821 := bstep (se 3 (by rfl) ⟨1575716, by rfl⟩ : syracuseStep 8403821 = 3151433) B3151433
theorem B1967975 : Blo 582814 1967975 := bstep (se 1 (by rfl) ⟨1475981, by rfl⟩ : syracuseStep 1967975 = 2951963) B2951963
theorem B2952287 : Blo 582814 2952287 := bstep (se 1 (by rfl) ⟨2214215, by rfl⟩ : syracuseStep 2952287 = 4428431) B4428431
theorem B1311983 : Blo 582814 1311983 := bstep (se 1 (by rfl) ⟨983987, by rfl⟩ : syracuseStep 1311983 = 1967975) B1967975
theorem B5602547 : Blo 582814 5602547 := bstep (se 1 (by rfl) ⟨4201910, by rfl⟩ : syracuseStep 5602547 = 8403821) B8403821
theorem B1968191 : Blo 582814 1968191 := bstep (se 1 (by rfl) ⟨1476143, by rfl⟩ : syracuseStep 1968191 = 2952287) B2952287
theorem B874655 : Blo 582814 874655 := bstep (se 1 (by rfl) ⟨655991, by rfl⟩ : syracuseStep 874655 = 1311983) B1311983
theorem B3735031 : Blo 582814 3735031 := bstep (se 1 (by rfl) ⟨2801273, by rfl⟩ : syracuseStep 3735031 = 5602547) B5602547
theorem B4980041 : Blo 582814 4980041 := bstep (se 2 (by rfl) ⟨1867515, by rfl⟩ : syracuseStep 4980041 = 3735031) B3735031
theorem B1312127 : Blo 582814 1312127 := bstep (se 1 (by rfl) ⟨984095, by rfl⟩ : syracuseStep 1312127 = 1968191) B1968191
theorem B583103 : Blo 582814 583103 := bstep (se 1 (by rfl) ⟨437327, by rfl⟩ : syracuseStep 583103 = 874655) B874655
theorem B3320027 : Blo 582814 3320027 := bstep (se 1 (by rfl) ⟨2490020, by rfl⟩ : syracuseStep 3320027 = 4980041) B4980041
theorem B874751 : Blo 582814 874751 := bstep (se 1 (by rfl) ⟨656063, by rfl⟩ : syracuseStep 874751 = 1312127) B1312127
theorem B2213351 : Blo 582814 2213351 := bstep (se 1 (by rfl) ⟨1660013, by rfl⟩ : syracuseStep 2213351 = 3320027) B3320027
theorem B583167 : Blo 582814 583167 := bstep (se 1 (by rfl) ⟨437375, by rfl⟩ : syracuseStep 583167 = 874751) B874751
theorem B1475567 : Blo 582814 1475567 := bstep (se 1 (by rfl) ⟨1106675, by rfl⟩ : syracuseStep 1475567 = 2213351) B2213351
theorem B983711 : Blo 582814 983711 := bstep (se 1 (by rfl) ⟨737783, by rfl⟩ : syracuseStep 983711 = 1475567) B1475567
theorem B655807 : Blo 582814 655807 := bstep (se 1 (by rfl) ⟨491855, by rfl⟩ : syracuseStep 655807 = 983711) B983711
theorem B874409 : Blo 582814 874409 := bstep (se 2 (by rfl) ⟨327903, by rfl⟩ : syracuseStep 874409 = 655807) B655807
theorem B582939 : Blo 582814 582939 := bstep (se 1 (by rfl) ⟨437204, by rfl⟩ : syracuseStep 582939 = 874409) B874409

theorem C0 (j : ℕ) (h1 : 145703 ≤ j) (h2 : j ≤ 145821) : Blo 582814 (4 * j + 3) := by
  interval_cases j
  · exact B582815
  · exact B582819
  · exact B582823
  · exact B582827
  · exact B582831
  · exact B582835
  · exact B582839
  · exact B582843
  · exact B582847
  · exact B582851
  · exact B582855
  · exact B582859
  · exact B582863
  · exact B582867
  · exact B582871
  · exact B582875
  · exact B582879
  · exact B582883
  · exact B582887
  · exact B582891
  · exact B582895
  · exact B582899
  · exact B582903
  · exact B582907
  · exact B582911
  · exact B582915
  · exact B582919
  · exact B582923
  · exact B582927
  · exact B582931
  · exact B582935
  · exact B582939
  · exact B582943
  · exact B582947
  · exact B582951
  · exact B582955
  · exact B582959
  · exact B582963
  · exact B582967
  · exact B582971
  · exact B582975
  · exact B582979
  · exact B582983
  · exact B582987
  · exact B582991
  · exact B582995
  · exact B582999
  · exact B583003
  · exact B583007
  · exact B583011
  · exact B583015
  · exact B583019
  · exact B583023
  · exact B583027
  · exact B583031
  · exact B583035
  · exact B583039
  · exact B583043
  · exact B583047
  · exact B583051
  · exact B583055
  · exact B583059
  · exact B583063
  · exact B583067
  · exact B583071
  · exact B583075
  · exact B583079
  · exact B583083
  · exact B583087
  · exact B583091
  · exact B583095
  · exact B583099
  · exact B583103
  · exact B583107
  · exact B583111
  · exact B583115
  · exact B583119
  · exact B583123
  · exact B583127
  · exact B583131
  · exact B583135
  · exact B583139
  · exact B583143
  · exact B583147
  · exact B583151
  · exact B583155
  · exact B583159
  · exact B583163
  · exact B583167
  · exact B583171
  · exact B583175
  · exact B583179
  · exact B583183
  · exact B583187
  · exact B583191
  · exact B583195
  · exact B583199
  · exact B583203
  · exact B583207
  · exact B583211
  · exact B583215
  · exact B583219
  · exact B583223
  · exact B583227
  · exact B583231
  · exact B583235
  · exact B583239
  · exact B583243
  · exact B583247
  · exact B583251
  · exact B583255
  · exact B583259
  · exact B583263
  · exact B583267
  · exact B583271
  · exact B583275
  · exact B583279
  · exact B583283
  · exact B583287

theorem solution (m : ℕ) (hlo : 582814 ≤ m) (hhi : m ≤ 583287) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 145703 ≤ j := by omega
    have hj2 : j ≤ 145821 := by omega
    have hb : Blo 582814 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
