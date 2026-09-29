-- Prove2me | solution 1 for syracuse_descends_range_1325481_1327481
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:37.497265+00:00
-- url     : https://prove2.me/submissions/45166d74-11c5-4886-a3c4-c25e1449af69

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


theorem B1990661 : Blo 1325481 1990661 := bbase (se 4 (by rfl) ⟨186624, by rfl⟩ : syracuseStep 1990661 = 373249) (by norm_num)
theorem B3498013 : Blo 1325481 3498013 := bbase (se 3 (by rfl) ⟨655877, by rfl⟩ : syracuseStep 3498013 = 1311755) (by norm_num)
theorem B1990685 : Blo 1325481 1990685 := bbase (se 3 (by rfl) ⟨373253, by rfl⟩ : syracuseStep 1990685 = 746507) (by norm_num)
theorem B1679393 : Blo 1325481 1679393 := bbase (se 2 (by rfl) ⟨629772, by rfl⟩ : syracuseStep 1679393 = 1259545) (by norm_num)
theorem B1990709 : Blo 1325481 1990709 := bbase (se 5 (by rfl) ⟨93314, by rfl⟩ : syracuseStep 1990709 = 186629) (by norm_num)
theorem B1990733 : Blo 1325481 1990733 := bbase (se 3 (by rfl) ⟨373262, by rfl⟩ : syracuseStep 1990733 = 746525) (by norm_num)
theorem B1679449 : Blo 1325481 1679449 := bbase (se 2 (by rfl) ⟨629793, by rfl⟩ : syracuseStep 1679449 = 1259587) (by norm_num)
theorem B1990757 : Blo 1325481 1990757 := bbase (se 4 (by rfl) ⟨186633, by rfl⟩ : syracuseStep 1990757 = 373267) (by norm_num)
theorem B1990781 : Blo 1325481 1990781 := bbase (se 3 (by rfl) ⟨373271, by rfl⟩ : syracuseStep 1990781 = 746543) (by norm_num)
theorem B1990805 : Blo 1325481 1990805 := bbase (se 6 (by rfl) ⟨46659, by rfl⟩ : syracuseStep 1990805 = 93319) (by norm_num)
theorem B1417381 : Blo 1325481 1417381 := bbase (se 4 (by rfl) ⟨132879, by rfl⟩ : syracuseStep 1417381 = 265759) (by norm_num)
theorem B1990829 : Blo 1325481 1990829 := bbase (se 3 (by rfl) ⟨373280, by rfl⟩ : syracuseStep 1990829 = 746561) (by norm_num)
theorem B3186869 : Blo 1325481 3186869 := bbase (se 5 (by rfl) ⟨149384, by rfl⟩ : syracuseStep 3186869 = 298769) (by norm_num)
theorem B1679545 : Blo 1325481 1679545 := bbase (se 2 (by rfl) ⟨629829, by rfl⟩ : syracuseStep 1679545 = 1259659) (by norm_num)
theorem B1401025 : Blo 1325481 1401025 := bbase (se 2 (by rfl) ⟨525384, by rfl⟩ : syracuseStep 1401025 = 1050769) (by norm_num)
theorem B1990853 : Blo 1325481 1990853 := bbase (se 4 (by rfl) ⟨186642, by rfl⟩ : syracuseStep 1990853 = 373285) (by norm_num)
theorem B30613717 : Blo 1325481 30613717 := bbase (se 7 (by rfl) ⟨358754, by rfl⟩ : syracuseStep 30613717 = 717509) (by norm_num)
theorem B6717653 : Blo 1325481 6717653 := bbase (se 7 (by rfl) ⟨78722, by rfl⟩ : syracuseStep 6717653 = 157445) (by norm_num)
theorem B1990877 : Blo 1325481 1990877 := bbase (se 3 (by rfl) ⟨373289, by rfl⟩ : syracuseStep 1990877 = 746579) (by norm_num)
theorem B1491169 : Blo 1325481 1491169 := bbase (se 2 (by rfl) ⟨559188, by rfl⟩ : syracuseStep 1491169 = 1118377) (by norm_num)
theorem B1990901 : Blo 1325481 1990901 := bbase (se 5 (by rfl) ⟨93323, by rfl⟩ : syracuseStep 1990901 = 186647) (by norm_num)
theorem B1491205 : Blo 1325481 1491205 := bbase (se 4 (by rfl) ⟨139800, by rfl⟩ : syracuseStep 1491205 = 279601) (by norm_num)
theorem B5447941 : Blo 1325481 5447941 := bbase (se 4 (by rfl) ⟨510744, by rfl⟩ : syracuseStep 5447941 = 1021489) (by norm_num)
theorem B1990925 : Blo 1325481 1990925 := bbase (se 3 (by rfl) ⟨373298, by rfl⟩ : syracuseStep 1990925 = 746597) (by norm_num)
theorem B1417501 : Blo 1325481 1417501 := bbase (se 3 (by rfl) ⟨265781, by rfl⟩ : syracuseStep 1417501 = 531563) (by norm_num)
theorem B1990949 : Blo 1325481 1990949 := bbase (se 4 (by rfl) ⟨186651, by rfl⟩ : syracuseStep 1990949 = 373303) (by norm_num)
theorem B1491241 : Blo 1325481 1491241 := bbase (se 2 (by rfl) ⟨559215, by rfl⟩ : syracuseStep 1491241 = 1118431) (by norm_num)
theorem B3359029 : Blo 1325481 3359029 := bbase (se 5 (by rfl) ⟨157454, by rfl⟩ : syracuseStep 3359029 = 314909) (by norm_num)
theorem B1990973 : Blo 1325481 1990973 := bbase (se 3 (by rfl) ⟨373307, by rfl⟩ : syracuseStep 1990973 = 746615) (by norm_num)
theorem B4538693 : Blo 1325481 4538693 := bbase (se 4 (by rfl) ⟨425502, by rfl⟩ : syracuseStep 4538693 = 851005) (by norm_num)
theorem B1491277 : Blo 1325481 1491277 := bbase (se 3 (by rfl) ⟨279614, by rfl⟩ : syracuseStep 1491277 = 559229) (by norm_num)
theorem B1990997 : Blo 1325481 1990997 := bbase (se 10 (by rfl) ⟨2916, by rfl⟩ : syracuseStep 1990997 = 5833) (by norm_num)
theorem B1679717 : Blo 1325481 1679717 := bbase (se 4 (by rfl) ⟨157473, by rfl⟩ : syracuseStep 1679717 = 314947) (by norm_num)
theorem B2236781 : Blo 1325481 2236781 := bbase (se 3 (by rfl) ⟨419396, by rfl⟩ : syracuseStep 2236781 = 838793) (by norm_num)
theorem B2834797 : Blo 1325481 2834797 := bbase (se 3 (by rfl) ⟨531524, by rfl⟩ : syracuseStep 2834797 = 1063049) (by norm_num)
theorem B1991021 : Blo 1325481 1991021 := bbase (se 3 (by rfl) ⟨373316, by rfl⟩ : syracuseStep 1991021 = 746633) (by norm_num)
theorem B1491313 : Blo 1325481 1491313 := bbase (se 2 (by rfl) ⟨559242, by rfl⟩ : syracuseStep 1491313 = 1118485) (by norm_num)
theorem B5038469 : Blo 1325481 5038469 := bbase (se 4 (by rfl) ⟨472356, by rfl⟩ : syracuseStep 5038469 = 944713) (by norm_num)
theorem B1991045 : Blo 1325481 1991045 := bbase (se 4 (by rfl) ⟨186660, by rfl⟩ : syracuseStep 1991045 = 373321) (by norm_num)
theorem B1491349 : Blo 1325481 1491349 := bbase (se 6 (by rfl) ⟨34953, by rfl⟩ : syracuseStep 1491349 = 69907) (by norm_num)
theorem B1679773 : Blo 1325481 1679773 := bbase (se 3 (by rfl) ⟨314957, by rfl⟩ : syracuseStep 1679773 = 629915) (by norm_num)
theorem B1991069 : Blo 1325481 1991069 := bbase (se 3 (by rfl) ⟨373325, by rfl⟩ : syracuseStep 1991069 = 746651) (by norm_num)
theorem B3187109 : Blo 1325481 3187109 := bbase (se 4 (by rfl) ⟨298791, by rfl⟩ : syracuseStep 3187109 = 597583) (by norm_num)
theorem B3359141 : Blo 1325481 3359141 := bbase (se 4 (by rfl) ⟨314919, by rfl⟩ : syracuseStep 3359141 = 629839) (by norm_num)
theorem B1991093 : Blo 1325481 1991093 := bbase (se 5 (by rfl) ⟨93332, by rfl⟩ : syracuseStep 1991093 = 186665) (by norm_num)
theorem B1491385 : Blo 1325481 1491385 := bbase (se 2 (by rfl) ⟨559269, by rfl⟩ : syracuseStep 1491385 = 1118539) (by norm_num)
theorem B1991117 : Blo 1325481 1991117 := bbase (se 3 (by rfl) ⟨373334, by rfl⟩ : syracuseStep 1991117 = 746669) (by norm_num)
theorem B2982365 : Blo 1325481 2982365 := bbase (se 3 (by rfl) ⟨559193, by rfl⟩ : syracuseStep 2982365 = 1118387) (by norm_num)
theorem B1491421 : Blo 1325481 1491421 := bbase (se 3 (by rfl) ⟨279641, by rfl⟩ : syracuseStep 1491421 = 559283) (by norm_num)
theorem B1991141 : Blo 1325481 1991141 := bbase (se 4 (by rfl) ⟨186669, by rfl⟩ : syracuseStep 1991141 = 373339) (by norm_num)
theorem B2236909 : Blo 1325481 2236909 := bbase (se 3 (by rfl) ⟨419420, by rfl⟩ : syracuseStep 2236909 = 838841) (by norm_num)
theorem B1679869 : Blo 1325481 1679869 := bbase (se 3 (by rfl) ⟨314975, by rfl⟩ : syracuseStep 1679869 = 629951) (by norm_num)
theorem B1991165 : Blo 1325481 1991165 := bbase (se 3 (by rfl) ⟨373343, by rfl⟩ : syracuseStep 1991165 = 746687) (by norm_num)
theorem B1491457 : Blo 1325481 1491457 := bbase (se 2 (by rfl) ⟨559296, by rfl⟩ : syracuseStep 1491457 = 1118593) (by norm_num)
theorem B1991189 : Blo 1325481 1991189 := bbase (se 6 (by rfl) ⟨46668, by rfl⟩ : syracuseStep 1991189 = 93337) (by norm_num)
theorem B2982437 : Blo 1325481 2982437 := bbase (se 4 (by rfl) ⟨279603, by rfl⟩ : syracuseStep 2982437 = 559207) (by norm_num)
theorem B1491493 : Blo 1325481 1491493 := bbase (se 4 (by rfl) ⟨139827, by rfl⟩ : syracuseStep 1491493 = 279655) (by norm_num)
theorem B1991213 : Blo 1325481 1991213 := bbase (se 3 (by rfl) ⟨373352, by rfl⟩ : syracuseStep 1991213 = 746705) (by norm_num)
theorem B2236997 : Blo 1325481 2236997 := bbase (se 4 (by rfl) ⟨209718, by rfl⟩ : syracuseStep 2236997 = 419437) (by norm_num)
theorem B1491529 : Blo 1325481 1491529 := bbase (se 2 (by rfl) ⟨559323, by rfl⟩ : syracuseStep 1491529 = 1118647) (by norm_num)
theorem B5374549 : Blo 1325481 5374549 := bbase (se 8 (by rfl) ⟨31491, by rfl⟩ : syracuseStep 5374549 = 62983) (by norm_num)
theorem B25494101 : Blo 1325481 25494101 := bbase (se 8 (by rfl) ⟨149379, by rfl⟩ : syracuseStep 25494101 = 298759) (by norm_num)
theorem B3359333 : Blo 1325481 3359333 := bbase (se 4 (by rfl) ⟨314937, by rfl⟩ : syracuseStep 3359333 = 629875) (by norm_num)
theorem B2982509 : Blo 1325481 2982509 := bbase (se 3 (by rfl) ⟨559220, by rfl⟩ : syracuseStep 2982509 = 1118441) (by norm_num)
theorem B1491565 : Blo 1325481 1491565 := bbase (se 3 (by rfl) ⟨279668, by rfl⟩ : syracuseStep 1491565 = 559337) (by norm_num)
theorem B3023477 : Blo 1325481 3023477 := bbase (se 5 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 3023477 = 283451) (by norm_num)
theorem B1491601 : Blo 1325481 1491601 := bbase (se 2 (by rfl) ⟨559350, by rfl⟩ : syracuseStep 1491601 = 1118701) (by norm_num)
theorem B5038757 : Blo 1325481 5038757 := bbase (se 4 (by rfl) ⟨472383, by rfl⟩ : syracuseStep 5038757 = 944767) (by norm_num)
theorem B1680041 : Blo 1325481 1680041 := bbase (se 2 (by rfl) ⟨630015, by rfl⟩ : syracuseStep 1680041 = 1260031) (by norm_num)
theorem B2982581 : Blo 1325481 2982581 := bbase (se 5 (by rfl) ⟨139808, by rfl⟩ : syracuseStep 2982581 = 279617) (by norm_num)
theorem B1491637 : Blo 1325481 1491637 := bbase (se 5 (by rfl) ⟨69920, by rfl⟩ : syracuseStep 1491637 = 139841) (by norm_num)
theorem B2237125 : Blo 1325481 2237125 := bbase (se 4 (by rfl) ⟨209730, by rfl⟩ : syracuseStep 2237125 = 419461) (by norm_num)
theorem B1344205 : Blo 1325481 1344205 := bbase (se 3 (by rfl) ⟨252038, by rfl⟩ : syracuseStep 1344205 = 504077) (by norm_num)
theorem B1491673 : Blo 1325481 1491673 := bbase (se 2 (by rfl) ⟨559377, by rfl⟩ : syracuseStep 1491673 = 1118755) (by norm_num)
theorem B3023605 : Blo 1325481 3023605 := bbase (se 5 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 3023605 = 283463) (by norm_num)
theorem B2982653 : Blo 1325481 2982653 := bbase (se 3 (by rfl) ⟨559247, by rfl⟩ : syracuseStep 2982653 = 1118495) (by norm_num)
theorem B1491709 : Blo 1325481 1491709 := bbase (se 3 (by rfl) ⟨279695, by rfl⟩ : syracuseStep 1491709 = 559391) (by norm_num)
theorem B15319829 : Blo 1325481 15319829 := bbase (se 6 (by rfl) ⟨359058, by rfl⟩ : syracuseStep 15319829 = 718117) (by norm_num)
theorem B2237213 : Blo 1325481 2237213 := bbase (se 3 (by rfl) ⟨419477, by rfl⟩ : syracuseStep 2237213 = 838955) (by norm_num)
theorem B1491745 : Blo 1325481 1491745 := bbase (se 2 (by rfl) ⟨559404, by rfl⟩ : syracuseStep 1491745 = 1118809) (by norm_num)
theorem B2982725 : Blo 1325481 2982725 := bbase (se 4 (by rfl) ⟨279630, by rfl⟩ : syracuseStep 2982725 = 559261) (by norm_num)
theorem B1491781 : Blo 1325481 1491781 := bbase (se 4 (by rfl) ⟨139854, by rfl⟩ : syracuseStep 1491781 = 279709) (by norm_num)
theorem B1491817 : Blo 1325481 1491817 := bbase (se 2 (by rfl) ⟨559431, by rfl⟩ : syracuseStep 1491817 = 1118863) (by norm_num)
theorem B2982797 : Blo 1325481 2982797 := bbase (se 3 (by rfl) ⟨559274, by rfl⟩ : syracuseStep 2982797 = 1118549) (by norm_num)
theorem B1491853 : Blo 1325481 1491853 := bbase (se 3 (by rfl) ⟨279722, by rfl⟩ : syracuseStep 1491853 = 559445) (by norm_num)
theorem B2237341 : Blo 1325481 2237341 := bbase (se 3 (by rfl) ⟨419501, by rfl⟩ : syracuseStep 2237341 = 839003) (by norm_num)
theorem B1491889 : Blo 1325481 1491889 := bbase (se 2 (by rfl) ⟨559458, by rfl⟩ : syracuseStep 1491889 = 1118917) (by norm_num)
theorem B3359677 : Blo 1325481 3359677 := bbase (se 3 (by rfl) ⟨629939, by rfl⟩ : syracuseStep 3359677 = 1259879) (by norm_num)
theorem B2982869 : Blo 1325481 2982869 := bbase (se 7 (by rfl) ⟨34955, by rfl⟩ : syracuseStep 2982869 = 69911) (by norm_num)
theorem B8496085 : Blo 1325481 8496085 := bbase (se 7 (by rfl) ⟨99563, by rfl⟩ : syracuseStep 8496085 = 199127) (by norm_num)
theorem B1491925 : Blo 1325481 1491925 := bbase (se 7 (by rfl) ⟨17483, by rfl⟩ : syracuseStep 1491925 = 34967) (by norm_num)
theorem B1344481 : Blo 1325481 1344481 := bbase (se 2 (by rfl) ⟨504180, by rfl⟩ : syracuseStep 1344481 = 1008361) (by norm_num)
theorem B1344497 : Blo 1325481 1344497 := bbase (se 2 (by rfl) ⟨504186, by rfl⟩ : syracuseStep 1344497 = 1008373) (by norm_num)
theorem B4473845 : Blo 1325481 4473845 := bbase (se 5 (by rfl) ⟨209711, by rfl⟩ : syracuseStep 4473845 = 419423) (by norm_num)
theorem B2237429 : Blo 1325481 2237429 := bbase (se 5 (by rfl) ⟨104879, by rfl⟩ : syracuseStep 2237429 = 209759) (by norm_num)
theorem B1491961 : Blo 1325481 1491961 := bbase (se 2 (by rfl) ⟨559485, by rfl⟩ : syracuseStep 1491961 = 1118971) (by norm_num)
theorem B2982941 : Blo 1325481 2982941 := bbase (se 3 (by rfl) ⟨559301, by rfl⟩ : syracuseStep 2982941 = 1118603) (by norm_num)
theorem B1491997 : Blo 1325481 1491997 := bbase (se 3 (by rfl) ⟨279749, by rfl⟩ : syracuseStep 1491997 = 559499) (by norm_num)
theorem B3359789 : Blo 1325481 3359789 := bbase (se 3 (by rfl) ⟨629960, by rfl⟩ : syracuseStep 3359789 = 1259921) (by norm_num)
theorem B1492033 : Blo 1325481 1492033 := bbase (se 2 (by rfl) ⟨559512, by rfl⟩ : syracuseStep 1492033 = 1119025) (by norm_num)
theorem B2688085 : Blo 1325481 2688085 := bbase (se 8 (by rfl) ⟨15750, by rfl⟩ : syracuseStep 2688085 = 31501) (by norm_num)
theorem B2983013 : Blo 1325481 2983013 := bbase (se 4 (by rfl) ⟨279657, by rfl⟩ : syracuseStep 2983013 = 559315) (by norm_num)
theorem B1492069 : Blo 1325481 1492069 := bbase (se 4 (by rfl) ⟨139881, by rfl⟩ : syracuseStep 1492069 = 279763) (by norm_num)
theorem B2237557 : Blo 1325481 2237557 := bbase (se 5 (by rfl) ⟨104885, by rfl⟩ : syracuseStep 2237557 = 209771) (by norm_num)
theorem B1492105 : Blo 1325481 1492105 := bbase (se 2 (by rfl) ⟨559539, by rfl⟩ : syracuseStep 1492105 = 1119079) (by norm_num)
theorem B2983085 : Blo 1325481 2983085 := bbase (se 3 (by rfl) ⟨559328, by rfl⟩ : syracuseStep 2983085 = 1118657) (by norm_num)
theorem B1492141 : Blo 1325481 1492141 := bbase (se 3 (by rfl) ⟨279776, by rfl⟩ : syracuseStep 1492141 = 559553) (by norm_num)
theorem B2237645 : Blo 1325481 2237645 := bbase (se 3 (by rfl) ⟨419558, by rfl⟩ : syracuseStep 2237645 = 839117) (by norm_num)
theorem B1492177 : Blo 1325481 1492177 := bbase (se 2 (by rfl) ⟨559566, by rfl⟩ : syracuseStep 1492177 = 1119133) (by norm_num)
theorem B3359981 : Blo 1325481 3359981 := bbase (se 3 (by rfl) ⟨629996, by rfl⟩ : syracuseStep 3359981 = 1259993) (by norm_num)
theorem B2983157 : Blo 1325481 2983157 := bbase (se 5 (by rfl) ⟨139835, by rfl⟩ : syracuseStep 2983157 = 279671) (by norm_num)
theorem B1492213 : Blo 1325481 1492213 := bbase (se 5 (by rfl) ⟨69947, by rfl⟩ : syracuseStep 1492213 = 139895) (by norm_num)
theorem B1492249 : Blo 1325481 1492249 := bbase (se 2 (by rfl) ⟨559593, by rfl⟩ : syracuseStep 1492249 = 1119187) (by norm_num)
theorem B2983229 : Blo 1325481 2983229 := bbase (se 3 (by rfl) ⟨559355, by rfl⟩ : syracuseStep 2983229 = 1118711) (by norm_num)
theorem B1492285 : Blo 1325481 1492285 := bbase (se 3 (by rfl) ⟨279803, by rfl⟩ : syracuseStep 1492285 = 559607) (by norm_num)
theorem B2237773 : Blo 1325481 2237773 := bbase (se 3 (by rfl) ⟨419582, by rfl⟩ : syracuseStep 2237773 = 839165) (by norm_num)
theorem B1492321 : Blo 1325481 1492321 := bbase (se 2 (by rfl) ⟨559620, by rfl⟩ : syracuseStep 1492321 = 1119241) (by norm_num)
theorem B2983301 : Blo 1325481 2983301 := bbase (se 4 (by rfl) ⟨279684, by rfl⟩ : syracuseStep 2983301 = 559369) (by norm_num)
theorem B1492357 : Blo 1325481 1492357 := bbase (se 4 (by rfl) ⟨139908, by rfl⟩ : syracuseStep 1492357 = 279817) (by norm_num)
theorem B2270605 : Blo 1325481 2270605 := bbase (se 3 (by rfl) ⟨425738, by rfl⟩ : syracuseStep 2270605 = 851477) (by norm_num)
theorem B3777941 : Blo 1325481 3777941 := bbase (se 6 (by rfl) ⟨88545, by rfl⟩ : syracuseStep 3777941 = 177091) (by norm_num)
theorem B4474277 : Blo 1325481 4474277 := bbase (se 4 (by rfl) ⟨419463, by rfl⟩ : syracuseStep 4474277 = 838927) (by norm_num)
theorem B2237861 : Blo 1325481 2237861 := bbase (se 4 (by rfl) ⟨209799, by rfl⟩ : syracuseStep 2237861 = 419599) (by norm_num)
theorem B1492393 : Blo 1325481 1492393 := bbase (se 2 (by rfl) ⟨559647, by rfl⟩ : syracuseStep 1492393 = 1119295) (by norm_num)
theorem B3024317 : Blo 1325481 3024317 := bbase (se 3 (by rfl) ⟨567059, by rfl⟩ : syracuseStep 3024317 = 1134119) (by norm_num)
theorem B2983373 : Blo 1325481 2983373 := bbase (se 3 (by rfl) ⟨559382, by rfl⟩ : syracuseStep 2983373 = 1118765) (by norm_num)
theorem B1492429 : Blo 1325481 1492429 := bbase (se 3 (by rfl) ⟨279830, by rfl⟩ : syracuseStep 1492429 = 559661) (by norm_num)
theorem B9561557 : Blo 1325481 9561557 := bbase (se 7 (by rfl) ⟨112049, by rfl⟩ : syracuseStep 9561557 = 224099) (by norm_num)
theorem B6718949 : Blo 1325481 6718949 := bbase (se 4 (by rfl) ⟨629901, by rfl⟩ : syracuseStep 6718949 = 1259803) (by norm_num)
theorem B1492465 : Blo 1325481 1492465 := bbase (se 2 (by rfl) ⟨559674, by rfl⟩ : syracuseStep 1492465 = 1119349) (by norm_num)
theorem B2516501 : Blo 1325481 2516501 := bbase (se 6 (by rfl) ⟨58980, by rfl⟩ : syracuseStep 2516501 = 117961) (by norm_num)
theorem B2983445 : Blo 1325481 2983445 := bbase (se 6 (by rfl) ⟨69924, by rfl⟩ : syracuseStep 2983445 = 139849) (by norm_num)
theorem B1492501 : Blo 1325481 1492501 := bbase (se 6 (by rfl) ⟨34980, by rfl⟩ : syracuseStep 1492501 = 69961) (by norm_num)
theorem B2237989 : Blo 1325481 2237989 := bbase (se 4 (by rfl) ⟨209811, by rfl⟩ : syracuseStep 2237989 = 419623) (by norm_num)
theorem B1492537 : Blo 1325481 1492537 := bbase (se 2 (by rfl) ⟨559701, by rfl⟩ : syracuseStep 1492537 = 1119403) (by norm_num)
theorem B1345081 : Blo 1325481 1345081 := bbase (se 2 (by rfl) ⟨504405, by rfl⟩ : syracuseStep 1345081 = 1008811) (by norm_num)
theorem B2983517 : Blo 1325481 2983517 := bbase (se 3 (by rfl) ⟨559409, by rfl⟩ : syracuseStep 2983517 = 1118819) (by norm_num)
theorem B1492573 : Blo 1325481 1492573 := bbase (se 3 (by rfl) ⟨279857, by rfl⟩ : syracuseStep 1492573 = 559715) (by norm_num)
theorem B2123381 : Blo 1325481 2123381 := bbase (se 5 (by rfl) ⟨99533, by rfl⟩ : syracuseStep 2123381 = 199067) (by norm_num)
theorem B2238077 : Blo 1325481 2238077 := bbase (se 3 (by rfl) ⟨419639, by rfl⟩ : syracuseStep 2238077 = 839279) (by norm_num)
theorem B1492609 : Blo 1325481 1492609 := bbase (se 2 (by rfl) ⟨559728, by rfl⟩ : syracuseStep 1492609 = 1119457) (by norm_num)
theorem B2516645 : Blo 1325481 2516645 := bbase (se 4 (by rfl) ⟨235935, by rfl⟩ : syracuseStep 2516645 = 471871) (by norm_num)
theorem B2983589 : Blo 1325481 2983589 := bbase (se 4 (by rfl) ⟨279711, by rfl⟩ : syracuseStep 2983589 = 559423) (by norm_num)
theorem B1492645 : Blo 1325481 1492645 := bbase (se 4 (by rfl) ⟨139935, by rfl⟩ : syracuseStep 1492645 = 279871) (by norm_num)
theorem B1492681 : Blo 1325481 1492681 := bbase (se 2 (by rfl) ⟨559755, by rfl⟩ : syracuseStep 1492681 = 1119511) (by norm_num)
theorem B2983661 : Blo 1325481 2983661 := bbase (se 3 (by rfl) ⟨559436, by rfl⟩ : syracuseStep 2983661 = 1118873) (by norm_num)
theorem B1492717 : Blo 1325481 1492717 := bbase (se 3 (by rfl) ⟨279884, by rfl⟩ : syracuseStep 1492717 = 559769) (by norm_num)
theorem B2238205 : Blo 1325481 2238205 := bbase (se 3 (by rfl) ⟨419663, by rfl⟩ : syracuseStep 2238205 = 839327) (by norm_num)
theorem B1492753 : Blo 1325481 1492753 := bbase (se 2 (by rfl) ⟨559782, by rfl⟩ : syracuseStep 1492753 = 1119565) (by norm_num)
theorem B8619797 : Blo 1325481 8619797 := bbase (se 6 (by rfl) ⟨202026, by rfl⟩ : syracuseStep 8619797 = 404053) (by norm_num)
theorem B2983733 : Blo 1325481 2983733 := bbase (se 5 (by rfl) ⟨139862, by rfl⟩ : syracuseStep 2983733 = 279725) (by norm_num)
theorem B1492789 : Blo 1325481 1492789 := bbase (se 5 (by rfl) ⟨69974, by rfl⟩ : syracuseStep 1492789 = 139949) (by norm_num)
theorem B5039941 : Blo 1325481 5039941 := bbase (se 4 (by rfl) ⟨472494, by rfl⟩ : syracuseStep 5039941 = 944989) (by norm_num)
theorem B4474709 : Blo 1325481 4474709 := bbase (se 9 (by rfl) ⟨13109, by rfl⟩ : syracuseStep 4474709 = 26219) (by norm_num)
theorem B2238293 : Blo 1325481 2238293 := bbase (se 9 (by rfl) ⟨6557, by rfl⟩ : syracuseStep 2238293 = 13115) (by norm_num)
theorem B1492825 : Blo 1325481 1492825 := bbase (se 2 (by rfl) ⟨559809, by rfl⟩ : syracuseStep 1492825 = 1119619) (by norm_num)
theorem B2983805 : Blo 1325481 2983805 := bbase (se 3 (by rfl) ⟨559463, by rfl⟩ : syracuseStep 2983805 = 1118927) (by norm_num)
theorem B1492861 : Blo 1325481 1492861 := bbase (se 3 (by rfl) ⟨279911, by rfl⟩ : syracuseStep 1492861 = 559823) (by norm_num)
theorem B6711173 : Blo 1325481 6711173 := bbase (se 4 (by rfl) ⟨629172, by rfl⟩ : syracuseStep 6711173 = 1258345) (by norm_num)
theorem B3024773 : Blo 1325481 3024773 := bbase (se 4 (by rfl) ⟨283572, by rfl⟩ : syracuseStep 3024773 = 567145) (by norm_num)
theorem B20703125 : Blo 1325481 20703125 := bbase (se 6 (by rfl) ⟨485229, by rfl⟩ : syracuseStep 20703125 = 970459) (by norm_num)
theorem B1492897 : Blo 1325481 1492897 := bbase (se 2 (by rfl) ⟨559836, by rfl⟩ : syracuseStep 1492897 = 1119673) (by norm_num)
theorem B2516933 : Blo 1325481 2516933 := bbase (se 4 (by rfl) ⟨235962, by rfl⟩ : syracuseStep 2516933 = 471925) (by norm_num)
theorem B2983877 : Blo 1325481 2983877 := bbase (se 4 (by rfl) ⟨279738, by rfl⟩ : syracuseStep 2983877 = 559477) (by norm_num)
theorem B1492933 : Blo 1325481 1492933 := bbase (se 4 (by rfl) ⟨139962, by rfl⟩ : syracuseStep 1492933 = 279925) (by norm_num)
theorem B2238421 : Blo 1325481 2238421 := bbase (se 7 (by rfl) ⟨26231, by rfl⟩ : syracuseStep 2238421 = 52463) (by norm_num)
theorem B1492969 : Blo 1325481 1492969 := bbase (se 2 (by rfl) ⟨559863, by rfl⟩ : syracuseStep 1492969 = 1119727) (by norm_num)
theorem B2983949 : Blo 1325481 2983949 := bbase (se 3 (by rfl) ⟨559490, by rfl⟩ : syracuseStep 2983949 = 1118981) (by norm_num)
theorem B1493005 : Blo 1325481 1493005 := bbase (se 3 (by rfl) ⟨279938, by rfl⟩ : syracuseStep 1493005 = 559877) (by norm_num)
theorem B12757013 : Blo 1325481 12757013 := bbase (se 6 (by rfl) ⟨298992, by rfl⟩ : syracuseStep 12757013 = 597985) (by norm_num)
theorem B1361953 : Blo 1325481 1361953 := bbase (se 2 (by rfl) ⟨510732, by rfl⟩ : syracuseStep 1361953 = 1021465) (by norm_num)
theorem B2238509 : Blo 1325481 2238509 := bbase (se 3 (by rfl) ⟨419720, by rfl⟩ : syracuseStep 2238509 = 839441) (by norm_num)
theorem B1493041 : Blo 1325481 1493041 := bbase (se 2 (by rfl) ⟨559890, by rfl⟩ : syracuseStep 1493041 = 1119781) (by norm_num)
theorem B3778613 : Blo 1325481 3778613 := bbase (se 5 (by rfl) ⟨177122, by rfl⟩ : syracuseStep 3778613 = 354245) (by norm_num)
theorem B3024965 : Blo 1325481 3024965 := bbase (se 4 (by rfl) ⟨283590, by rfl⟩ : syracuseStep 3024965 = 567181) (by norm_num)
theorem B2984021 : Blo 1325481 2984021 := bbase (se 8 (by rfl) ⟨17484, by rfl⟩ : syracuseStep 2984021 = 34969) (by norm_num)
theorem B3188821 : Blo 1325481 3188821 := bbase (se 8 (by rfl) ⟨18684, by rfl⟩ : syracuseStep 3188821 = 37369) (by norm_num)
theorem B1493077 : Blo 1325481 1493077 := bbase (se 8 (by rfl) ⟨8748, by rfl⟩ : syracuseStep 1493077 = 17497) (by norm_num)
theorem B2517085 : Blo 1325481 2517085 := bbase (se 3 (by rfl) ⟨471953, by rfl⟩ : syracuseStep 2517085 = 943907) (by norm_num)
theorem B6457445 : Blo 1325481 6457445 := bbase (se 4 (by rfl) ⟨605385, by rfl⟩ : syracuseStep 6457445 = 1210771) (by norm_num)
theorem B5040245 : Blo 1325481 5040245 := bbase (se 5 (by rfl) ⟨236261, by rfl⟩ : syracuseStep 5040245 = 472523) (by norm_num)
theorem B1493113 : Blo 1325481 1493113 := bbase (se 2 (by rfl) ⟨559917, by rfl⟩ : syracuseStep 1493113 = 1119835) (by norm_num)
theorem B2984093 : Blo 1325481 2984093 := bbase (se 3 (by rfl) ⟨559517, by rfl⟩ : syracuseStep 2984093 = 1119035) (by norm_num)
theorem B1493149 : Blo 1325481 1493149 := bbase (se 3 (by rfl) ⟨279965, by rfl⟩ : syracuseStep 1493149 = 559931) (by norm_num)
theorem B2238637 : Blo 1325481 2238637 := bbase (se 3 (by rfl) ⟨419744, by rfl⟩ : syracuseStep 2238637 = 839489) (by norm_num)
theorem B1493185 : Blo 1325481 1493185 := bbase (se 2 (by rfl) ⟨559944, by rfl⟩ : syracuseStep 1493185 = 1119889) (by norm_num)
theorem B8063189 : Blo 1325481 8063189 := bbase (se 7 (by rfl) ⟨94490, by rfl⟩ : syracuseStep 8063189 = 188981) (by norm_num)
theorem B2984165 : Blo 1325481 2984165 := bbase (se 4 (by rfl) ⟨279765, by rfl⟩ : syracuseStep 2984165 = 559531) (by norm_num)
theorem B2689253 : Blo 1325481 2689253 := bbase (se 4 (by rfl) ⟨252117, by rfl⟩ : syracuseStep 2689253 = 504235) (by norm_num)
theorem B1493221 : Blo 1325481 1493221 := bbase (se 4 (by rfl) ⟨139989, by rfl⟩ : syracuseStep 1493221 = 279979) (by norm_num)
theorem B4475141 : Blo 1325481 4475141 := bbase (se 4 (by rfl) ⟨419544, by rfl⟩ : syracuseStep 4475141 = 839089) (by norm_num)
theorem B2238725 : Blo 1325481 2238725 := bbase (se 4 (by rfl) ⟨209880, by rfl⟩ : syracuseStep 2238725 = 419761) (by norm_num)
theorem B1493257 : Blo 1325481 1493257 := bbase (se 2 (by rfl) ⟨559971, by rfl⟩ : syracuseStep 1493257 = 1119943) (by norm_num)
theorem B2984237 : Blo 1325481 2984237 := bbase (se 3 (by rfl) ⟨559544, by rfl⟩ : syracuseStep 2984237 = 1119089) (by norm_num)
theorem B1493293 : Blo 1325481 1493293 := bbase (se 3 (by rfl) ⟨279992, by rfl⟩ : syracuseStep 1493293 = 559985) (by norm_num)
theorem B1493329 : Blo 1325481 1493329 := bbase (se 2 (by rfl) ⟨559998, by rfl⟩ : syracuseStep 1493329 = 1119997) (by norm_num)
theorem B2984309 : Blo 1325481 2984309 := bbase (se 5 (by rfl) ⟨139889, by rfl⟩ : syracuseStep 2984309 = 279779) (by norm_num)
theorem B1493365 : Blo 1325481 1493365 := bbase (se 5 (by rfl) ⟨70001, by rfl⟩ : syracuseStep 1493365 = 140003) (by norm_num)
theorem B2238853 : Blo 1325481 2238853 := bbase (se 4 (by rfl) ⟨209892, by rfl⟩ : syracuseStep 2238853 = 419785) (by norm_num)
theorem B2517389 : Blo 1325481 2517389 := bbase (se 3 (by rfl) ⟨472010, by rfl⟩ : syracuseStep 2517389 = 944021) (by norm_num)
theorem B8063381 : Blo 1325481 8063381 := bbase (se 6 (by rfl) ⟨188985, by rfl⟩ : syracuseStep 8063381 = 377971) (by norm_num)
theorem B1493401 : Blo 1325481 1493401 := bbase (se 2 (by rfl) ⟨560025, by rfl⟩ : syracuseStep 1493401 = 1120051) (by norm_num)
theorem B2984381 : Blo 1325481 2984381 := bbase (se 3 (by rfl) ⟨559571, by rfl⟩ : syracuseStep 2984381 = 1119143) (by norm_num)
theorem B2238941 : Blo 1325481 2238941 := bbase (se 3 (by rfl) ⟨419801, by rfl⟩ : syracuseStep 2238941 = 839603) (by norm_num)
theorem B3779045 : Blo 1325481 3779045 := bbase (se 4 (by rfl) ⟨354285, by rfl⟩ : syracuseStep 3779045 = 708571) (by norm_num)
theorem B2984453 : Blo 1325481 2984453 := bbase (se 4 (by rfl) ⟨279792, by rfl⟩ : syracuseStep 2984453 = 559585) (by norm_num)
theorem B2984525 : Blo 1325481 2984525 := bbase (se 3 (by rfl) ⟨559598, by rfl⟩ : syracuseStep 2984525 = 1119197) (by norm_num)
theorem B2239069 : Blo 1325481 2239069 := bbase (se 3 (by rfl) ⟨419825, by rfl⟩ : syracuseStep 2239069 = 839651) (by norm_num)
theorem B2984597 : Blo 1325481 2984597 := bbase (se 6 (by rfl) ⟨69951, by rfl⟩ : syracuseStep 2984597 = 139903) (by norm_num)
theorem B2869925 : Blo 1325481 2869925 := bbase (se 4 (by rfl) ⟨269055, by rfl⟩ : syracuseStep 2869925 = 538111) (by norm_num)
theorem B4475573 : Blo 1325481 4475573 := bbase (se 5 (by rfl) ⟨209792, by rfl⟩ : syracuseStep 4475573 = 419585) (by norm_num)
theorem B2239157 : Blo 1325481 2239157 := bbase (se 5 (by rfl) ⟨104960, by rfl⟩ : syracuseStep 2239157 = 209921) (by norm_num)
theorem B6810293 : Blo 1325481 6810293 := bbase (se 5 (by rfl) ⟨319232, by rfl⟩ : syracuseStep 6810293 = 638465) (by norm_num)
theorem B3025621 : Blo 1325481 3025621 := bbase (se 7 (by rfl) ⟨35456, by rfl⟩ : syracuseStep 3025621 = 70913) (by norm_num)
theorem B2984669 : Blo 1325481 2984669 := bbase (se 3 (by rfl) ⟨559625, by rfl⟩ : syracuseStep 2984669 = 1119251) (by norm_num)
theorem B6720245 : Blo 1325481 6720245 := bbase (se 5 (by rfl) ⟨315011, by rfl⟩ : syracuseStep 6720245 = 630023) (by norm_num)
theorem B2689805 : Blo 1325481 2689805 := bbase (se 3 (by rfl) ⟨504338, by rfl⟩ : syracuseStep 2689805 = 1008677) (by norm_num)
theorem B2984741 : Blo 1325481 2984741 := bbase (se 4 (by rfl) ⟨279819, by rfl⟩ : syracuseStep 2984741 = 559639) (by norm_num)
theorem B2239285 : Blo 1325481 2239285 := bbase (se 5 (by rfl) ⟨104966, by rfl⟩ : syracuseStep 2239285 = 209933) (by norm_num)
theorem B2984813 : Blo 1325481 2984813 := bbase (se 3 (by rfl) ⟨559652, by rfl⟩ : syracuseStep 2984813 = 1119305) (by norm_num)
theorem B2239373 : Blo 1325481 2239373 := bbase (se 3 (by rfl) ⟨419882, by rfl⟩ : syracuseStep 2239373 = 839765) (by norm_num)
theorem B2984885 : Blo 1325481 2984885 := bbase (se 5 (by rfl) ⟨139916, by rfl⟩ : syracuseStep 2984885 = 279833) (by norm_num)
theorem B9071605 : Blo 1325481 9071605 := bbase (se 5 (by rfl) ⟨425231, by rfl⟩ : syracuseStep 9071605 = 850463) (by norm_num)
theorem B2984957 : Blo 1325481 2984957 := bbase (se 3 (by rfl) ⟨559679, by rfl⟩ : syracuseStep 2984957 = 1119359) (by norm_num)
theorem B2239501 : Blo 1325481 2239501 := bbase (se 3 (by rfl) ⟨419906, by rfl⟩ : syracuseStep 2239501 = 839813) (by norm_num)
theorem B2985029 : Blo 1325481 2985029 := bbase (se 4 (by rfl) ⟨279846, by rfl⟩ : syracuseStep 2985029 = 559693) (by norm_num)
theorem B4598869 : Blo 1325481 4598869 := bbase (se 8 (by rfl) ⟨26946, by rfl⟩ : syracuseStep 4598869 = 53893) (by norm_num)
theorem B2124893 : Blo 1325481 2124893 := bbase (se 3 (by rfl) ⟨398417, by rfl⟩ : syracuseStep 2124893 = 796835) (by norm_num)
theorem B4476005 : Blo 1325481 4476005 := bbase (se 4 (by rfl) ⟨419625, by rfl⟩ : syracuseStep 4476005 = 839251) (by norm_num)
theorem B2239589 : Blo 1325481 2239589 := bbase (se 4 (by rfl) ⟨209961, by rfl⟩ : syracuseStep 2239589 = 419923) (by norm_num)
theorem B4090981 : Blo 1325481 4090981 := bbase (se 4 (by rfl) ⟨383529, by rfl⟩ : syracuseStep 4090981 = 767059) (by norm_num)
theorem B2518141 : Blo 1325481 2518141 := bbase (se 3 (by rfl) ⟨472151, by rfl⟩ : syracuseStep 2518141 = 944303) (by norm_num)
theorem B2985101 : Blo 1325481 2985101 := bbase (se 3 (by rfl) ⟨559706, by rfl⟩ : syracuseStep 2985101 = 1119413) (by norm_num)
theorem B6712469 : Blo 1325481 6712469 := bbase (se 6 (by rfl) ⟨157323, by rfl⟩ : syracuseStep 6712469 = 314647) (by norm_num)
theorem B2985173 : Blo 1325481 2985173 := bbase (se 7 (by rfl) ⟨34982, by rfl⟩ : syracuseStep 2985173 = 69965) (by norm_num)
theorem B3779797 : Blo 1325481 3779797 := bbase (se 7 (by rfl) ⟨44294, by rfl⟩ : syracuseStep 3779797 = 88589) (by norm_num)
theorem B2239717 : Blo 1325481 2239717 := bbase (se 4 (by rfl) ⟨209973, by rfl⟩ : syracuseStep 2239717 = 419947) (by norm_num)
theorem B4779269 : Blo 1325481 4779269 := bbase (se 4 (by rfl) ⟨448056, by rfl⟩ : syracuseStep 4779269 = 896113) (by norm_num)
theorem B2518285 : Blo 1325481 2518285 := bbase (se 3 (by rfl) ⟨472178, by rfl⟩ : syracuseStep 2518285 = 944357) (by norm_num)
theorem B2985245 : Blo 1325481 2985245 := bbase (se 3 (by rfl) ⟨559733, by rfl⟩ : syracuseStep 2985245 = 1119467) (by norm_num)
theorem B2239805 : Blo 1325481 2239805 := bbase (se 3 (by rfl) ⟨419963, by rfl⟩ : syracuseStep 2239805 = 839927) (by norm_num)
theorem B5107013 : Blo 1325481 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B2985317 : Blo 1325481 2985317 := bbase (se 4 (by rfl) ⟨279873, by rfl⟩ : syracuseStep 2985317 = 559747) (by norm_num)
theorem B2551213 : Blo 1325481 2551213 := bbase (se 3 (by rfl) ⟨478352, by rfl⟩ : syracuseStep 2551213 = 956705) (by norm_num)
theorem B2518445 : Blo 1325481 2518445 := bbase (se 3 (by rfl) ⟨472208, by rfl⟩ : syracuseStep 2518445 = 944417) (by norm_num)
theorem B2985389 : Blo 1325481 2985389 := bbase (se 3 (by rfl) ⟨559760, by rfl⟩ : syracuseStep 2985389 = 1119521) (by norm_num)
theorem B2239933 : Blo 1325481 2239933 := bbase (se 3 (by rfl) ⟨419987, by rfl⟩ : syracuseStep 2239933 = 839975) (by norm_num)
theorem B2985461 : Blo 1325481 2985461 := bbase (se 5 (by rfl) ⟨139943, by rfl⟩ : syracuseStep 2985461 = 279887) (by norm_num)
theorem B4476437 : Blo 1325481 4476437 := bbase (se 6 (by rfl) ⟨104916, by rfl⟩ : syracuseStep 4476437 = 209833) (by norm_num)
theorem B2240021 : Blo 1325481 2240021 := bbase (se 6 (by rfl) ⟨52500, by rfl⟩ : syracuseStep 2240021 = 105001) (by norm_num)
theorem B2125349 : Blo 1325481 2125349 := bbase (se 4 (by rfl) ⟨199251, by rfl⟩ : syracuseStep 2125349 = 398503) (by norm_num)
theorem B2518589 : Blo 1325481 2518589 := bbase (se 3 (by rfl) ⟨472235, by rfl⟩ : syracuseStep 2518589 = 944471) (by norm_num)
theorem B2985533 : Blo 1325481 2985533 := bbase (se 3 (by rfl) ⟨559787, by rfl⟩ : syracuseStep 2985533 = 1119575) (by norm_num)
theorem B1887877 : Blo 1325481 1887877 := bbase (se 4 (by rfl) ⟨176988, by rfl⟩ : syracuseStep 1887877 = 353977) (by norm_num)
theorem B2985605 : Blo 1325481 2985605 := bbase (se 4 (by rfl) ⟨279900, by rfl⟩ : syracuseStep 2985605 = 559801) (by norm_num)
theorem B22679189 : Blo 1325481 22679189 := bbase (se 6 (by rfl) ⟨531543, by rfl⟩ : syracuseStep 22679189 = 1063087) (by norm_num)
theorem B2985677 : Blo 1325481 2985677 := bbase (se 3 (by rfl) ⟨559814, by rfl⟩ : syracuseStep 2985677 = 1119629) (by norm_num)
theorem B12095189 : Blo 1325481 12095189 := bbase (se 7 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 12095189 = 283481) (by norm_num)
theorem B7171861 : Blo 1325481 7171861 := bbase (se 6 (by rfl) ⟨168090, by rfl⟩ : syracuseStep 7171861 = 336181) (by norm_num)
theorem B2985749 : Blo 1325481 2985749 := bbase (se 6 (by rfl) ⟨69978, by rfl⟩ : syracuseStep 2985749 = 139957) (by norm_num)
theorem B2518877 : Blo 1325481 2518877 := bbase (se 3 (by rfl) ⟨472289, by rfl⟩ : syracuseStep 2518877 = 944579) (by norm_num)
theorem B2985821 : Blo 1325481 2985821 := bbase (se 3 (by rfl) ⟨559841, by rfl⟩ : syracuseStep 2985821 = 1119683) (by norm_num)
theorem B2985893 : Blo 1325481 2985893 := bbase (se 4 (by rfl) ⟨279927, by rfl⟩ : syracuseStep 2985893 = 559855) (by norm_num)
theorem B1593281 : Blo 1325481 1593281 := bbase (se 2 (by rfl) ⟨597480, by rfl⟩ : syracuseStep 1593281 = 1194961) (by norm_num)
theorem B4476869 : Blo 1325481 4476869 := bbase (se 4 (by rfl) ⟨419706, by rfl⟩ : syracuseStep 4476869 = 839413) (by norm_num)
theorem B1888213 : Blo 1325481 1888213 := bbase (se 7 (by rfl) ⟨22127, by rfl⟩ : syracuseStep 1888213 = 44255) (by norm_num)
theorem B5664725 : Blo 1325481 5664725 := bbase (se 7 (by rfl) ⟨66383, by rfl⟩ : syracuseStep 5664725 = 132767) (by norm_num)
theorem B6377429 : Blo 1325481 6377429 := bbase (se 7 (by rfl) ⟨74735, by rfl⟩ : syracuseStep 6377429 = 149471) (by norm_num)
theorem B2985965 : Blo 1325481 2985965 := bbase (se 3 (by rfl) ⟨559868, by rfl⟩ : syracuseStep 2985965 = 1119737) (by norm_num)
theorem B2519029 : Blo 1325481 2519029 := bbase (se 5 (by rfl) ⟨118079, by rfl⟩ : syracuseStep 2519029 = 236159) (by norm_num)
theorem B2986037 : Blo 1325481 2986037 := bbase (se 5 (by rfl) ⟨139970, by rfl⟩ : syracuseStep 2986037 = 279941) (by norm_num)
theorem B6377525 : Blo 1325481 6377525 := bbase (se 5 (by rfl) ⟨298946, by rfl⟩ : syracuseStep 6377525 = 597893) (by norm_num)
theorem B1511537 : Blo 1325481 1511537 := bbase (se 2 (by rfl) ⟨566826, by rfl⟩ : syracuseStep 1511537 = 1133653) (by norm_num)
theorem B2986109 : Blo 1325481 2986109 := bbase (se 3 (by rfl) ⟨559895, by rfl⟩ : syracuseStep 2986109 = 1119791) (by norm_num)
theorem B1888429 : Blo 1325481 1888429 := bbase (se 3 (by rfl) ⟨354080, by rfl⟩ : syracuseStep 1888429 = 708161) (by norm_num)
theorem B2986181 : Blo 1325481 2986181 := bbase (se 4 (by rfl) ⟨279954, by rfl⟩ : syracuseStep 2986181 = 559909) (by norm_num)
theorem B11325653 : Blo 1325481 11325653 := bbase (se 7 (by rfl) ⟨132722, by rfl⟩ : syracuseStep 11325653 = 265445) (by norm_num)
theorem B1593589 : Blo 1325481 1593589 := bbase (se 5 (by rfl) ⟨74699, by rfl⟩ : syracuseStep 1593589 = 149399) (by norm_num)
theorem B2986253 : Blo 1325481 2986253 := bbase (se 3 (by rfl) ⟨559922, by rfl⟩ : syracuseStep 2986253 = 1119845) (by norm_num)
theorem B2519333 : Blo 1325481 2519333 := bbase (se 4 (by rfl) ⟨236187, by rfl⟩ : syracuseStep 2519333 = 472375) (by norm_num)
theorem B2986325 : Blo 1325481 2986325 := bbase (se 10 (by rfl) ⟨4374, by rfl⟩ : syracuseStep 2986325 = 8749) (by norm_num)
theorem B1593689 : Blo 1325481 1593689 := bbase (se 2 (by rfl) ⟨597633, by rfl⟩ : syracuseStep 1593689 = 1195267) (by norm_num)
theorem B4477301 : Blo 1325481 4477301 := bbase (se 5 (by rfl) ⟨209873, by rfl⟩ : syracuseStep 4477301 = 419747) (by norm_num)
theorem B2986397 : Blo 1325481 2986397 := bbase (se 3 (by rfl) ⟨559949, by rfl⟩ : syracuseStep 2986397 = 1119899) (by norm_num)
theorem B6713765 : Blo 1325481 6713765 := bbase (se 4 (by rfl) ⟨629415, by rfl⟩ : syracuseStep 6713765 = 1258831) (by norm_num)
theorem B2986469 : Blo 1325481 2986469 := bbase (se 4 (by rfl) ⟨279981, by rfl⟩ : syracuseStep 2986469 = 559963) (by norm_num)
theorem B3355141 : Blo 1325481 3355141 := bbase (se 4 (by rfl) ⟨314544, by rfl⟩ : syracuseStep 3355141 = 629089) (by norm_num)
theorem B2126341 : Blo 1325481 2126341 := bbase (se 4 (by rfl) ⟨199344, by rfl⟩ : syracuseStep 2126341 = 398689) (by norm_num)
theorem B1888805 : Blo 1325481 1888805 := bbase (se 4 (by rfl) ⟨177075, by rfl⟩ : syracuseStep 1888805 = 354151) (by norm_num)
theorem B2986541 : Blo 1325481 2986541 := bbase (se 3 (by rfl) ⟨559976, by rfl⟩ : syracuseStep 2986541 = 1119953) (by norm_num)
theorem B5034581 : Blo 1325481 5034581 := bbase (se 8 (by rfl) ⟨29499, by rfl⟩ : syracuseStep 5034581 = 58999) (by norm_num)
theorem B3355253 : Blo 1325481 3355253 := bbase (se 5 (by rfl) ⟨157277, by rfl⟩ : syracuseStep 3355253 = 314555) (by norm_num)
theorem B7172725 : Blo 1325481 7172725 := bbase (se 5 (by rfl) ⟨336221, by rfl⟩ : syracuseStep 7172725 = 672443) (by norm_num)
theorem B2986613 : Blo 1325481 2986613 := bbase (se 5 (by rfl) ⟨139997, by rfl⟩ : syracuseStep 2986613 = 279995) (by norm_num)
theorem B4248197 : Blo 1325481 4248197 := bbase (se 4 (by rfl) ⟨398268, by rfl⟩ : syracuseStep 4248197 = 796537) (by norm_num)
theorem B2831021 : Blo 1325481 2831021 := bbase (se 3 (by rfl) ⟨530816, by rfl⟩ : syracuseStep 2831021 = 1061633) (by norm_num)
theorem B2986685 : Blo 1325481 2986685 := bbase (se 3 (by rfl) ⟨560003, by rfl⟩ : syracuseStep 2986685 = 1120007) (by norm_num)
theorem B3584741 : Blo 1325481 3584741 := bbase (se 4 (by rfl) ⟨336069, by rfl⟩ : syracuseStep 3584741 = 672139) (by norm_num)
theorem B1594093 : Blo 1325481 1594093 := bbase (se 3 (by rfl) ⟨298892, by rfl⟩ : syracuseStep 1594093 = 597785) (by norm_num)
theorem B7549685 : Blo 1325481 7549685 := bbase (se 5 (by rfl) ⟨353891, by rfl⟩ : syracuseStep 7549685 = 707783) (by norm_num)
theorem B2986757 : Blo 1325481 2986757 := bbase (se 4 (by rfl) ⟨280008, by rfl⟩ : syracuseStep 2986757 = 560017) (by norm_num)
theorem B4477733 : Blo 1325481 4477733 := bbase (se 4 (by rfl) ⟨419787, by rfl⟩ : syracuseStep 4477733 = 839575) (by norm_num)
theorem B3355445 : Blo 1325481 3355445 := bbase (se 5 (by rfl) ⟨157286, by rfl⟩ : syracuseStep 3355445 = 314573) (by norm_num)
theorem B2986829 : Blo 1325481 2986829 := bbase (se 3 (by rfl) ⟨560030, by rfl⟩ : syracuseStep 2986829 = 1120061) (by norm_num)
theorem B5034869 : Blo 1325481 5034869 := bbase (se 5 (by rfl) ⟨236009, by rfl⟩ : syracuseStep 5034869 = 472019) (by norm_num)
theorem B8500085 : Blo 1325481 8500085 := bbase (se 5 (by rfl) ⟨398441, by rfl⟩ : syracuseStep 8500085 = 796883) (by norm_num)
theorem B2831269 : Blo 1325481 2831269 := bbase (se 4 (by rfl) ⟨265431, by rfl⟩ : syracuseStep 2831269 = 530863) (by norm_num)
theorem B5665733 : Blo 1325481 5665733 := bbase (se 4 (by rfl) ⟨531162, by rfl⟩ : syracuseStep 5665733 = 1062325) (by norm_num)
theorem B1512413 : Blo 1325481 1512413 := bbase (se 3 (by rfl) ⟨283577, by rfl⟩ : syracuseStep 1512413 = 567155) (by norm_num)
theorem B2421733 : Blo 1325481 2421733 := bbase (se 4 (by rfl) ⟨227037, by rfl⟩ : syracuseStep 2421733 = 454075) (by norm_num)
theorem B2552813 : Blo 1325481 2552813 := bbase (se 3 (by rfl) ⟨478652, by rfl⟩ : syracuseStep 2552813 = 957305) (by norm_num)
theorem B2520085 : Blo 1325481 2520085 := bbase (se 6 (by rfl) ⟨59064, by rfl⟩ : syracuseStep 2520085 = 118129) (by norm_num)
theorem B1594477 : Blo 1325481 1594477 := bbase (se 3 (by rfl) ⟨298964, by rfl⟩ : syracuseStep 1594477 = 597929) (by norm_num)
theorem B3355789 : Blo 1325481 3355789 := bbase (se 3 (by rfl) ⟨629210, by rfl⟩ : syracuseStep 3355789 = 1258421) (by norm_num)
theorem B1512605 : Blo 1325481 1512605 := bbase (se 3 (by rfl) ⟨283613, by rfl⟩ : syracuseStep 1512605 = 567227) (by norm_num)
theorem B4478165 : Blo 1325481 4478165 := bbase (se 7 (by rfl) ⟨52478, by rfl⟩ : syracuseStep 4478165 = 104957) (by norm_num)
theorem B3355901 : Blo 1325481 3355901 := bbase (se 3 (by rfl) ⟨629231, by rfl⟩ : syracuseStep 3355901 = 1258463) (by norm_num)
theorem B2831773 : Blo 1325481 2831773 := bbase (se 3 (by rfl) ⟨530957, by rfl⟩ : syracuseStep 2831773 = 1061915) (by norm_num)
theorem B3356093 : Blo 1325481 3356093 := bbase (se 3 (by rfl) ⟨629267, by rfl⟩ : syracuseStep 3356093 = 1258535) (by norm_num)
theorem B2553277 : Blo 1325481 2553277 := bbase (se 3 (by rfl) ⟨478739, by rfl⟩ : syracuseStep 2553277 = 957479) (by norm_num)
theorem B6305365 : Blo 1325481 6305365 := bbase (se 8 (by rfl) ⟨36945, by rfl⟩ : syracuseStep 6305365 = 73891) (by norm_num)
theorem B4781701 : Blo 1325481 4781701 := bbase (se 4 (by rfl) ⟨448284, by rfl⟩ : syracuseStep 4781701 = 896569) (by norm_num)
theorem B4478597 : Blo 1325481 4478597 := bbase (se 4 (by rfl) ⟨419868, by rfl⟩ : syracuseStep 4478597 = 839737) (by norm_num)
theorem B1988237 : Blo 1325481 1988237 := bbase (se 3 (by rfl) ⟨372794, by rfl⟩ : syracuseStep 1988237 = 745589) (by norm_num)
theorem B1988261 : Blo 1325481 1988261 := bbase (se 4 (by rfl) ⟨186399, by rfl⟩ : syracuseStep 1988261 = 372799) (by norm_num)
theorem B6715061 : Blo 1325481 6715061 := bbase (se 5 (by rfl) ⟨314768, by rfl⟩ : syracuseStep 6715061 = 629537) (by norm_num)
theorem B1988285 : Blo 1325481 1988285 := bbase (se 3 (by rfl) ⟨372803, by rfl⟩ : syracuseStep 1988285 = 745607) (by norm_num)
theorem B1988309 : Blo 1325481 1988309 := bbase (se 7 (by rfl) ⟨23300, by rfl⟩ : syracuseStep 1988309 = 46601) (by norm_num)
theorem B1988333 : Blo 1325481 1988333 := bbase (se 3 (by rfl) ⟨372812, by rfl⟩ : syracuseStep 1988333 = 745625) (by norm_num)
theorem B1988357 : Blo 1325481 1988357 := bbase (se 4 (by rfl) ⟨186408, by rfl⟩ : syracuseStep 1988357 = 372817) (by norm_num)
theorem B3356437 : Blo 1325481 3356437 := bbase (se 6 (by rfl) ⟨78666, by rfl⟩ : syracuseStep 3356437 = 157333) (by norm_num)
theorem B2045717 : Blo 1325481 2045717 := bbase (se 6 (by rfl) ⟨47946, by rfl⟩ : syracuseStep 2045717 = 95893) (by norm_num)
theorem B1988381 : Blo 1325481 1988381 := bbase (se 3 (by rfl) ⟨372821, by rfl⟩ : syracuseStep 1988381 = 745643) (by norm_num)
theorem B1988405 : Blo 1325481 1988405 := bbase (se 5 (by rfl) ⟨93206, by rfl⟩ : syracuseStep 1988405 = 186413) (by norm_num)
theorem B6371141 : Blo 1325481 6371141 := bbase (se 4 (by rfl) ⟨597294, by rfl⟩ : syracuseStep 6371141 = 1194589) (by norm_num)
theorem B1513289 : Blo 1325481 1513289 := bbase (se 2 (by rfl) ⟨567483, by rfl⟩ : syracuseStep 1513289 = 1134967) (by norm_num)
theorem B1988429 : Blo 1325481 1988429 := bbase (se 3 (by rfl) ⟨372830, by rfl⟩ : syracuseStep 1988429 = 745661) (by norm_num)
theorem B1988453 : Blo 1325481 1988453 := bbase (se 4 (by rfl) ⟨186417, by rfl⟩ : syracuseStep 1988453 = 372835) (by norm_num)
theorem B1988477 : Blo 1325481 1988477 := bbase (se 3 (by rfl) ⟨372839, by rfl⟩ : syracuseStep 1988477 = 745679) (by norm_num)
theorem B1513345 : Blo 1325481 1513345 := bbase (se 2 (by rfl) ⟨567504, by rfl⟩ : syracuseStep 1513345 = 1135009) (by norm_num)
theorem B3356549 : Blo 1325481 3356549 := bbase (se 4 (by rfl) ⟨314676, by rfl⟩ : syracuseStep 3356549 = 629353) (by norm_num)
theorem B1988501 : Blo 1325481 1988501 := bbase (se 6 (by rfl) ⟨46605, by rfl⟩ : syracuseStep 1988501 = 93211) (by norm_num)
theorem B1988525 : Blo 1325481 1988525 := bbase (se 3 (by rfl) ⟨372848, by rfl⟩ : syracuseStep 1988525 = 745697) (by norm_num)
theorem B1988549 : Blo 1325481 1988549 := bbase (se 4 (by rfl) ⟨186426, by rfl⟩ : syracuseStep 1988549 = 372853) (by norm_num)
theorem B1988573 : Blo 1325481 1988573 := bbase (se 3 (by rfl) ⟨372857, by rfl⟩ : syracuseStep 1988573 = 745715) (by norm_num)
theorem B1988597 : Blo 1325481 1988597 := bbase (se 5 (by rfl) ⟨93215, by rfl⟩ : syracuseStep 1988597 = 186431) (by norm_num)
theorem B1988621 : Blo 1325481 1988621 := bbase (se 3 (by rfl) ⟨372866, by rfl⟩ : syracuseStep 1988621 = 745733) (by norm_num)
theorem B5036053 : Blo 1325481 5036053 := bbase (se 6 (by rfl) ⟨118032, by rfl⟩ : syracuseStep 5036053 = 236065) (by norm_num)
theorem B1988645 : Blo 1325481 1988645 := bbase (se 4 (by rfl) ⟨186435, by rfl⟩ : syracuseStep 1988645 = 372871) (by norm_num)
theorem B4479029 : Blo 1325481 4479029 := bbase (se 5 (by rfl) ⟨209954, by rfl⟩ : syracuseStep 4479029 = 419909) (by norm_num)
theorem B1988669 : Blo 1325481 1988669 := bbase (se 3 (by rfl) ⟨372875, by rfl⟩ : syracuseStep 1988669 = 745751) (by norm_num)
theorem B3356741 : Blo 1325481 3356741 := bbase (se 4 (by rfl) ⟨314694, by rfl⟩ : syracuseStep 3356741 = 629389) (by norm_num)
theorem B1988693 : Blo 1325481 1988693 := bbase (se 8 (by rfl) ⟨11652, by rfl⟩ : syracuseStep 1988693 = 23305) (by norm_num)
theorem B5380181 : Blo 1325481 5380181 := bbase (se 8 (by rfl) ⟨31524, by rfl⟩ : syracuseStep 5380181 = 63049) (by norm_num)
theorem B5740645 : Blo 1325481 5740645 := bbase (se 4 (by rfl) ⟨538185, by rfl⟩ : syracuseStep 5740645 = 1076371) (by norm_num)
theorem B1988717 : Blo 1325481 1988717 := bbase (se 3 (by rfl) ⟨372884, by rfl⟩ : syracuseStep 1988717 = 745769) (by norm_num)
theorem B1988741 : Blo 1325481 1988741 := bbase (se 4 (by rfl) ⟨186444, by rfl⟩ : syracuseStep 1988741 = 372889) (by norm_num)
theorem B1988765 : Blo 1325481 1988765 := bbase (se 3 (by rfl) ⟨372893, by rfl⟩ : syracuseStep 1988765 = 745787) (by norm_num)
theorem B1988789 : Blo 1325481 1988789 := bbase (se 5 (by rfl) ⟨93224, by rfl⟩ : syracuseStep 1988789 = 186449) (by norm_num)
theorem B10074293 : Blo 1325481 10074293 := bbase (se 5 (by rfl) ⟨472232, by rfl⟩ : syracuseStep 10074293 = 944465) (by norm_num)
theorem B1988813 : Blo 1325481 1988813 := bbase (se 3 (by rfl) ⟨372902, by rfl⟩ : syracuseStep 1988813 = 745805) (by norm_num)
theorem B1988837 : Blo 1325481 1988837 := bbase (se 4 (by rfl) ⟨186453, by rfl⟩ : syracuseStep 1988837 = 372907) (by norm_num)
theorem B1988861 : Blo 1325481 1988861 := bbase (se 3 (by rfl) ⟨372911, by rfl⟩ : syracuseStep 1988861 = 745823) (by norm_num)
theorem B4536581 : Blo 1325481 4536581 := bbase (se 4 (by rfl) ⟨425304, by rfl⟩ : syracuseStep 4536581 = 850609) (by norm_num)
theorem B1988885 : Blo 1325481 1988885 := bbase (se 6 (by rfl) ⟨46614, by rfl⟩ : syracuseStep 1988885 = 93229) (by norm_num)
theorem B2832661 : Blo 1325481 2832661 := bbase (se 6 (by rfl) ⟨66390, by rfl⟩ : syracuseStep 2832661 = 132781) (by norm_num)
theorem B1677601 : Blo 1325481 1677601 := bbase (se 2 (by rfl) ⟨629100, by rfl⟩ : syracuseStep 1677601 = 1258201) (by norm_num)
theorem B1988909 : Blo 1325481 1988909 := bbase (se 3 (by rfl) ⟨372920, by rfl⟩ : syracuseStep 1988909 = 745841) (by norm_num)
theorem B1415485 : Blo 1325481 1415485 := bbase (se 3 (by rfl) ⟨265403, by rfl⟩ : syracuseStep 1415485 = 530807) (by norm_num)
theorem B1988933 : Blo 1325481 1988933 := bbase (se 4 (by rfl) ⟨186462, by rfl⟩ : syracuseStep 1988933 = 372925) (by norm_num)
theorem B5036357 : Blo 1325481 5036357 := bbase (se 4 (by rfl) ⟨472158, by rfl⟩ : syracuseStep 5036357 = 944317) (by norm_num)
theorem B1988957 : Blo 1325481 1988957 := bbase (se 3 (by rfl) ⟨372929, by rfl⟩ : syracuseStep 1988957 = 745859) (by norm_num)
theorem B1988981 : Blo 1325481 1988981 := bbase (se 5 (by rfl) ⟨93233, by rfl⟩ : syracuseStep 1988981 = 186467) (by norm_num)
theorem B3774853 : Blo 1325481 3774853 := bbase (se 4 (by rfl) ⟨353892, by rfl⟩ : syracuseStep 3774853 = 707785) (by norm_num)
theorem B1989005 : Blo 1325481 1989005 := bbase (se 3 (by rfl) ⟨372938, by rfl⟩ : syracuseStep 1989005 = 745877) (by norm_num)
theorem B3357085 : Blo 1325481 3357085 := bbase (se 3 (by rfl) ⟨629453, by rfl⟩ : syracuseStep 3357085 = 1258907) (by norm_num)
theorem B1989029 : Blo 1325481 1989029 := bbase (se 4 (by rfl) ⟨186471, by rfl⟩ : syracuseStep 1989029 = 372943) (by norm_num)
theorem B1989053 : Blo 1325481 1989053 := bbase (se 3 (by rfl) ⟨372947, by rfl⟩ : syracuseStep 1989053 = 745895) (by norm_num)
theorem B1677773 : Blo 1325481 1677773 := bbase (se 3 (by rfl) ⟨314582, by rfl⟩ : syracuseStep 1677773 = 629165) (by norm_num)
theorem B1989077 : Blo 1325481 1989077 := bbase (se 7 (by rfl) ⟨23309, by rfl⟩ : syracuseStep 1989077 = 46619) (by norm_num)
theorem B4479461 : Blo 1325481 4479461 := bbase (se 4 (by rfl) ⟨419949, by rfl⟩ : syracuseStep 4479461 = 839899) (by norm_num)
theorem B1989101 : Blo 1325481 1989101 := bbase (se 3 (by rfl) ⟨372956, by rfl⟩ : syracuseStep 1989101 = 745913) (by norm_num)
theorem B1677829 : Blo 1325481 1677829 := bbase (se 4 (by rfl) ⟨157296, by rfl⟩ : syracuseStep 1677829 = 314593) (by norm_num)
theorem B1989125 : Blo 1325481 1989125 := bbase (se 4 (by rfl) ⟨186480, by rfl⟩ : syracuseStep 1989125 = 372961) (by norm_num)
theorem B3357197 : Blo 1325481 3357197 := bbase (se 3 (by rfl) ⟨629474, by rfl⟩ : syracuseStep 3357197 = 1258949) (by norm_num)
theorem B1989149 : Blo 1325481 1989149 := bbase (se 3 (by rfl) ⟨372965, by rfl⟩ : syracuseStep 1989149 = 745931) (by norm_num)
theorem B1989173 : Blo 1325481 1989173 := bbase (se 5 (by rfl) ⟨93242, by rfl⟩ : syracuseStep 1989173 = 186485) (by norm_num)
theorem B1989197 : Blo 1325481 1989197 := bbase (se 3 (by rfl) ⟨372974, by rfl⟩ : syracuseStep 1989197 = 745949) (by norm_num)
theorem B10066517 : Blo 1325481 10066517 := bbase (se 8 (by rfl) ⟨58983, by rfl⟩ : syracuseStep 10066517 = 117967) (by norm_num)
theorem B1677925 : Blo 1325481 1677925 := bbase (se 4 (by rfl) ⟨157305, by rfl⟩ : syracuseStep 1677925 = 314611) (by norm_num)
theorem B1989221 : Blo 1325481 1989221 := bbase (se 4 (by rfl) ⟨186489, by rfl⟩ : syracuseStep 1989221 = 372979) (by norm_num)
theorem B1915501 : Blo 1325481 1915501 := bbase (se 3 (by rfl) ⟨359156, by rfl⟩ : syracuseStep 1915501 = 718313) (by norm_num)
theorem B1989245 : Blo 1325481 1989245 := bbase (se 3 (by rfl) ⟨372983, by rfl⟩ : syracuseStep 1989245 = 745967) (by norm_num)
theorem B1989269 : Blo 1325481 1989269 := bbase (se 6 (by rfl) ⟨46623, by rfl⟩ : syracuseStep 1989269 = 93247) (by norm_num)
theorem B8182421 : Blo 1325481 8182421 := bbase (se 6 (by rfl) ⟨191775, by rfl⟩ : syracuseStep 8182421 = 383551) (by norm_num)
theorem B1989293 : Blo 1325481 1989293 := bbase (se 3 (by rfl) ⟨372992, by rfl⟩ : syracuseStep 1989293 = 745985) (by norm_num)
theorem B10902197 : Blo 1325481 10902197 := bbase (se 5 (by rfl) ⟨511040, by rfl⟩ : syracuseStep 10902197 = 1022081) (by norm_num)
theorem B5667509 : Blo 1325481 5667509 := bbase (se 5 (by rfl) ⟨265664, by rfl⟩ : syracuseStep 5667509 = 531329) (by norm_num)
theorem B1989317 : Blo 1325481 1989317 := bbase (se 4 (by rfl) ⟨186498, by rfl⟩ : syracuseStep 1989317 = 372997) (by norm_num)
theorem B3357389 : Blo 1325481 3357389 := bbase (se 3 (by rfl) ⟨629510, by rfl⟩ : syracuseStep 3357389 = 1259021) (by norm_num)
theorem B1989341 : Blo 1325481 1989341 := bbase (se 3 (by rfl) ⟨373001, by rfl⟩ : syracuseStep 1989341 = 746003) (by norm_num)
theorem B1989365 : Blo 1325481 1989365 := bbase (se 5 (by rfl) ⟨93251, by rfl⟩ : syracuseStep 1989365 = 186503) (by norm_num)
theorem B1415929 : Blo 1325481 1415929 := bbase (se 2 (by rfl) ⟨530973, by rfl⟩ : syracuseStep 1415929 = 1061947) (by norm_num)
theorem B2833157 : Blo 1325481 2833157 := bbase (se 4 (by rfl) ⟨265608, by rfl⟩ : syracuseStep 2833157 = 531217) (by norm_num)
theorem B1989389 : Blo 1325481 1989389 := bbase (se 3 (by rfl) ⟨373010, by rfl⟩ : syracuseStep 1989389 = 746021) (by norm_num)
theorem B1678097 : Blo 1325481 1678097 := bbase (se 2 (by rfl) ⟨629286, by rfl⟩ : syracuseStep 1678097 = 1258573) (by norm_num)
theorem B4250389 : Blo 1325481 4250389 := bbase (se 6 (by rfl) ⟨99618, by rfl⟩ : syracuseStep 4250389 = 199237) (by norm_num)
theorem B1989413 : Blo 1325481 1989413 := bbase (se 4 (by rfl) ⟨186507, by rfl⟩ : syracuseStep 1989413 = 373015) (by norm_num)
theorem B1415989 : Blo 1325481 1415989 := bbase (se 5 (by rfl) ⟨66374, by rfl⟩ : syracuseStep 1415989 = 132749) (by norm_num)
theorem B1989437 : Blo 1325481 1989437 := bbase (se 3 (by rfl) ⟨373019, by rfl⟩ : syracuseStep 1989437 = 746039) (by norm_num)
theorem B1678153 : Blo 1325481 1678153 := bbase (se 2 (by rfl) ⟨629307, by rfl⟩ : syracuseStep 1678153 = 1258615) (by norm_num)
theorem B1989461 : Blo 1325481 1989461 := bbase (se 9 (by rfl) ⟨5828, by rfl⟩ : syracuseStep 1989461 = 11657) (by norm_num)
theorem B1989485 : Blo 1325481 1989485 := bbase (se 3 (by rfl) ⟨373028, by rfl⟩ : syracuseStep 1989485 = 746057) (by norm_num)
theorem B1989509 : Blo 1325481 1989509 := bbase (se 4 (by rfl) ⟨186516, by rfl⟩ : syracuseStep 1989509 = 373033) (by norm_num)
theorem B7551893 : Blo 1325481 7551893 := bbase (se 6 (by rfl) ⟨176997, by rfl⟩ : syracuseStep 7551893 = 353995) (by norm_num)
theorem B4479893 : Blo 1325481 4479893 := bbase (se 6 (by rfl) ⟨104997, by rfl⟩ : syracuseStep 4479893 = 209995) (by norm_num)
theorem B1989533 : Blo 1325481 1989533 := bbase (se 3 (by rfl) ⟨373037, by rfl⟩ : syracuseStep 1989533 = 746075) (by norm_num)
theorem B1678249 : Blo 1325481 1678249 := bbase (se 2 (by rfl) ⟨629343, by rfl⟩ : syracuseStep 1678249 = 1258687) (by norm_num)
theorem B1989557 : Blo 1325481 1989557 := bbase (se 5 (by rfl) ⟨93260, by rfl⟩ : syracuseStep 1989557 = 186521) (by norm_num)
theorem B6716357 : Blo 1325481 6716357 := bbase (se 4 (by rfl) ⟨629658, by rfl⟩ : syracuseStep 6716357 = 1259317) (by norm_num)
theorem B1989581 : Blo 1325481 1989581 := bbase (se 3 (by rfl) ⟨373046, by rfl⟩ : syracuseStep 1989581 = 746093) (by norm_num)
theorem B1989605 : Blo 1325481 1989605 := bbase (se 4 (by rfl) ⟨186525, by rfl⟩ : syracuseStep 1989605 = 373051) (by norm_num)
theorem B1989629 : Blo 1325481 1989629 := bbase (se 3 (by rfl) ⟨373055, by rfl⟩ : syracuseStep 1989629 = 746111) (by norm_num)
theorem B1989653 : Blo 1325481 1989653 := bbase (se 6 (by rfl) ⟨46632, by rfl⟩ : syracuseStep 1989653 = 93265) (by norm_num)
theorem B3357733 : Blo 1325481 3357733 := bbase (se 4 (by rfl) ⟨314787, by rfl⟩ : syracuseStep 3357733 = 629575) (by norm_num)
theorem B1989677 : Blo 1325481 1989677 := bbase (se 3 (by rfl) ⟨373064, by rfl⟩ : syracuseStep 1989677 = 746129) (by norm_num)
theorem B3185725 : Blo 1325481 3185725 := bbase (se 3 (by rfl) ⟨597323, by rfl⟩ : syracuseStep 3185725 = 1194647) (by norm_num)
theorem B1989701 : Blo 1325481 1989701 := bbase (se 4 (by rfl) ⟨186534, by rfl⟩ : syracuseStep 1989701 = 373069) (by norm_num)
theorem B1678421 : Blo 1325481 1678421 := bbase (se 8 (by rfl) ⟨9834, by rfl⟩ : syracuseStep 1678421 = 19669) (by norm_num)
theorem B1989725 : Blo 1325481 1989725 := bbase (se 3 (by rfl) ⟨373073, by rfl⟩ : syracuseStep 1989725 = 746147) (by norm_num)
theorem B1416305 : Blo 1325481 1416305 := bbase (se 2 (by rfl) ⟨531114, by rfl⟩ : syracuseStep 1416305 = 1062229) (by norm_num)
theorem B1989749 : Blo 1325481 1989749 := bbase (se 5 (by rfl) ⟨93269, by rfl⟩ : syracuseStep 1989749 = 186539) (by norm_num)
theorem B1678477 : Blo 1325481 1678477 := bbase (se 3 (by rfl) ⟨314714, by rfl⟩ : syracuseStep 1678477 = 629429) (by norm_num)
theorem B1989773 : Blo 1325481 1989773 := bbase (se 3 (by rfl) ⟨373082, by rfl⟩ : syracuseStep 1989773 = 746165) (by norm_num)
theorem B3357845 : Blo 1325481 3357845 := bbase (se 6 (by rfl) ⟨78699, by rfl⟩ : syracuseStep 3357845 = 157399) (by norm_num)
theorem B3185821 : Blo 1325481 3185821 := bbase (se 3 (by rfl) ⟨597341, by rfl⟩ : syracuseStep 3185821 = 1194683) (by norm_num)
theorem B1989797 : Blo 1325481 1989797 := bbase (se 4 (by rfl) ⟨186543, by rfl⟩ : syracuseStep 1989797 = 373087) (by norm_num)
theorem B2268341 : Blo 1325481 2268341 := bbase (se 5 (by rfl) ⟨106328, by rfl⟩ : syracuseStep 2268341 = 212657) (by norm_num)
theorem B1989821 : Blo 1325481 1989821 := bbase (se 3 (by rfl) ⟨373091, by rfl⟩ : syracuseStep 1989821 = 746183) (by norm_num)
theorem B1989845 : Blo 1325481 1989845 := bbase (se 7 (by rfl) ⟨23318, by rfl⟩ : syracuseStep 1989845 = 46637) (by norm_num)
theorem B1678573 : Blo 1325481 1678573 := bbase (se 3 (by rfl) ⟨314732, by rfl⟩ : syracuseStep 1678573 = 629465) (by norm_num)
theorem B1989869 : Blo 1325481 1989869 := bbase (se 3 (by rfl) ⟨373100, by rfl⟩ : syracuseStep 1989869 = 746201) (by norm_num)
theorem B12745973 : Blo 1325481 12745973 := bbase (se 5 (by rfl) ⟨597467, by rfl⟩ : syracuseStep 12745973 = 1194935) (by norm_num)
theorem B1989893 : Blo 1325481 1989893 := bbase (se 4 (by rfl) ⟨186552, by rfl⟩ : syracuseStep 1989893 = 373105) (by norm_num)
theorem B1989917 : Blo 1325481 1989917 := bbase (se 3 (by rfl) ⟨373109, by rfl⟩ : syracuseStep 1989917 = 746219) (by norm_num)
theorem B2424109 : Blo 1325481 2424109 := bbase (se 3 (by rfl) ⟨454520, by rfl⟩ : syracuseStep 2424109 = 909041) (by norm_num)
theorem B1400113 : Blo 1325481 1400113 := bbase (se 2 (by rfl) ⟨525042, by rfl⟩ : syracuseStep 1400113 = 1050085) (by norm_num)
theorem B1989941 : Blo 1325481 1989941 := bbase (se 5 (by rfl) ⟨93278, by rfl⟩ : syracuseStep 1989941 = 186557) (by norm_num)
theorem B1989965 : Blo 1325481 1989965 := bbase (se 3 (by rfl) ⟨373118, by rfl⟩ : syracuseStep 1989965 = 746237) (by norm_num)
theorem B3358037 : Blo 1325481 3358037 := bbase (se 11 (by rfl) ⟨2459, by rfl⟩ : syracuseStep 3358037 = 4919) (by norm_num)
theorem B1989989 : Blo 1325481 1989989 := bbase (se 4 (by rfl) ⟨186561, by rfl⟩ : syracuseStep 1989989 = 373123) (by norm_num)
theorem B1990013 : Blo 1325481 1990013 := bbase (se 3 (by rfl) ⟨373127, by rfl⟩ : syracuseStep 1990013 = 746255) (by norm_num)
theorem B1990037 : Blo 1325481 1990037 := bbase (se 6 (by rfl) ⟨46641, by rfl⟩ : syracuseStep 1990037 = 93283) (by norm_num)
theorem B1678745 : Blo 1325481 1678745 := bbase (se 2 (by rfl) ⟨629529, by rfl⟩ : syracuseStep 1678745 = 1259059) (by norm_num)
theorem B1990061 : Blo 1325481 1990061 := bbase (se 3 (by rfl) ⟨373136, by rfl⟩ : syracuseStep 1990061 = 746273) (by norm_num)
theorem B1990085 : Blo 1325481 1990085 := bbase (se 4 (by rfl) ⟨186570, by rfl⟩ : syracuseStep 1990085 = 373141) (by norm_num)
theorem B1678801 : Blo 1325481 1678801 := bbase (se 2 (by rfl) ⟨629550, by rfl⟩ : syracuseStep 1678801 = 1259101) (by norm_num)
theorem B1990109 : Blo 1325481 1990109 := bbase (se 3 (by rfl) ⟨373145, by rfl⟩ : syracuseStep 1990109 = 746291) (by norm_num)
theorem B1990133 : Blo 1325481 1990133 := bbase (se 5 (by rfl) ⟨93287, by rfl⟩ : syracuseStep 1990133 = 186575) (by norm_num)
theorem B1990157 : Blo 1325481 1990157 := bbase (se 3 (by rfl) ⟨373154, by rfl⟩ : syracuseStep 1990157 = 746309) (by norm_num)
theorem B1990181 : Blo 1325481 1990181 := bbase (se 4 (by rfl) ⟨186579, by rfl⟩ : syracuseStep 1990181 = 373159) (by norm_num)
theorem B1416749 : Blo 1325481 1416749 := bbase (se 3 (by rfl) ⟨265640, by rfl⟩ : syracuseStep 1416749 = 531281) (by norm_num)
theorem B1678897 : Blo 1325481 1678897 := bbase (se 2 (by rfl) ⟨629586, by rfl⟩ : syracuseStep 1678897 = 1259173) (by norm_num)
theorem B1990205 : Blo 1325481 1990205 := bbase (se 3 (by rfl) ⟨373163, by rfl⟩ : syracuseStep 1990205 = 746327) (by norm_num)
theorem B1990229 : Blo 1325481 1990229 := bbase (se 8 (by rfl) ⟨11661, by rfl⟩ : syracuseStep 1990229 = 23323) (by norm_num)
theorem B4251221 : Blo 1325481 4251221 := bbase (se 8 (by rfl) ⟨24909, by rfl⟩ : syracuseStep 4251221 = 49819) (by norm_num)
theorem B1416809 : Blo 1325481 1416809 := bbase (se 2 (by rfl) ⟨531303, by rfl⟩ : syracuseStep 1416809 = 1062607) (by norm_num)
theorem B1990253 : Blo 1325481 1990253 := bbase (se 3 (by rfl) ⟨373172, by rfl⟩ : syracuseStep 1990253 = 746345) (by norm_num)
theorem B2834045 : Blo 1325481 2834045 := bbase (se 3 (by rfl) ⟨531383, by rfl⟩ : syracuseStep 2834045 = 1062767) (by norm_num)
theorem B1990277 : Blo 1325481 1990277 := bbase (se 4 (by rfl) ⟨186588, by rfl⟩ : syracuseStep 1990277 = 373177) (by norm_num)
theorem B1990301 : Blo 1325481 1990301 := bbase (se 3 (by rfl) ⟨373181, by rfl⟩ : syracuseStep 1990301 = 746363) (by norm_num)
theorem B3186341 : Blo 1325481 3186341 := bbase (se 4 (by rfl) ⟨298719, by rfl⟩ : syracuseStep 3186341 = 597439) (by norm_num)
theorem B1793701 : Blo 1325481 1793701 := bbase (se 4 (by rfl) ⟨168159, by rfl⟩ : syracuseStep 1793701 = 336319) (by norm_num)
theorem B3358381 : Blo 1325481 3358381 := bbase (se 3 (by rfl) ⟨629696, by rfl⟩ : syracuseStep 3358381 = 1259393) (by norm_num)
theorem B1990325 : Blo 1325481 1990325 := bbase (se 5 (by rfl) ⟨93296, by rfl⟩ : syracuseStep 1990325 = 186593) (by norm_num)
theorem B1990349 : Blo 1325481 1990349 := bbase (se 3 (by rfl) ⟨373190, by rfl⟩ : syracuseStep 1990349 = 746381) (by norm_num)
theorem B1679069 : Blo 1325481 1679069 := bbase (se 3 (by rfl) ⟨314825, by rfl⟩ : syracuseStep 1679069 = 629651) (by norm_num)
theorem B2391773 : Blo 1325481 2391773 := bbase (se 3 (by rfl) ⟨448457, by rfl⟩ : syracuseStep 2391773 = 896915) (by norm_num)
theorem B1990373 : Blo 1325481 1990373 := bbase (se 4 (by rfl) ⟨186597, by rfl⟩ : syracuseStep 1990373 = 373195) (by norm_num)
theorem B1416937 : Blo 1325481 1416937 := bbase (se 2 (by rfl) ⟨531351, by rfl⟩ : syracuseStep 1416937 = 1062703) (by norm_num)
theorem B2834165 : Blo 1325481 2834165 := bbase (se 5 (by rfl) ⟨132851, by rfl⟩ : syracuseStep 2834165 = 265703) (by norm_num)
theorem B9567989 : Blo 1325481 9567989 := bbase (se 5 (by rfl) ⟨448499, by rfl⟩ : syracuseStep 9567989 = 896999) (by norm_num)
theorem B4849397 : Blo 1325481 4849397 := bbase (se 5 (by rfl) ⟨227315, by rfl⟩ : syracuseStep 4849397 = 454631) (by norm_num)
theorem B1990397 : Blo 1325481 1990397 := bbase (se 3 (by rfl) ⟨373199, by rfl⟩ : syracuseStep 1990397 = 746399) (by norm_num)
theorem B1679125 : Blo 1325481 1679125 := bbase (se 6 (by rfl) ⟨39354, by rfl⟩ : syracuseStep 1679125 = 78709) (by norm_num)
theorem B1990421 : Blo 1325481 1990421 := bbase (se 6 (by rfl) ⟨46650, by rfl⟩ : syracuseStep 1990421 = 93301) (by norm_num)
theorem B3358493 : Blo 1325481 3358493 := bbase (se 3 (by rfl) ⟨629717, by rfl⟩ : syracuseStep 3358493 = 1259435) (by norm_num)
theorem B1990445 : Blo 1325481 1990445 := bbase (se 3 (by rfl) ⟨373208, by rfl⟩ : syracuseStep 1990445 = 746417) (by norm_num)
theorem B1990469 : Blo 1325481 1990469 := bbase (se 4 (by rfl) ⟨186606, by rfl⟩ : syracuseStep 1990469 = 373213) (by norm_num)
theorem B1990493 : Blo 1325481 1990493 := bbase (se 3 (by rfl) ⟨373217, by rfl⟩ : syracuseStep 1990493 = 746435) (by norm_num)
theorem B3776357 : Blo 1325481 3776357 := bbase (se 4 (by rfl) ⟨354033, by rfl⟩ : syracuseStep 3776357 = 708067) (by norm_num)
theorem B1679221 : Blo 1325481 1679221 := bbase (se 5 (by rfl) ⟨78713, by rfl⟩ : syracuseStep 1679221 = 157427) (by norm_num)
theorem B1990517 : Blo 1325481 1990517 := bbase (se 5 (by rfl) ⟨93305, by rfl⟩ : syracuseStep 1990517 = 186611) (by norm_num)
theorem B1793917 : Blo 1325481 1793917 := bbase (se 3 (by rfl) ⟨336359, by rfl⟩ : syracuseStep 1793917 = 672719) (by norm_num)
theorem B1990541 : Blo 1325481 1990541 := bbase (se 3 (by rfl) ⟨373226, by rfl⟩ : syracuseStep 1990541 = 746453) (by norm_num)
theorem B1990565 : Blo 1325481 1990565 := bbase (se 4 (by rfl) ⟨186615, by rfl⟩ : syracuseStep 1990565 = 373231) (by norm_num)
theorem B1990589 : Blo 1325481 1990589 := bbase (se 3 (by rfl) ⟨373235, by rfl⟩ : syracuseStep 1990589 = 746471) (by norm_num)
theorem B1990613 : Blo 1325481 1990613 := bbase (se 7 (by rfl) ⟨23327, by rfl⟩ : syracuseStep 1990613 = 46655) (by norm_num)
theorem B3358685 : Blo 1325481 3358685 := bbase (se 3 (by rfl) ⟨629753, by rfl⟩ : syracuseStep 3358685 = 1259507) (by norm_num)
theorem B1990637 : Blo 1325481 1990637 := bbase (se 3 (by rfl) ⟨373244, by rfl⟩ : syracuseStep 1990637 = 746489) (by norm_num)
theorem B1327107 : Blo 1325481 1327107 := bstep (se 1 (by rfl) ⟨995330, by rfl⟩ : syracuseStep 1327107 = 1990661) B1990661
theorem B1990673 : Blo 1325481 1990673 := bstep (se 2 (by rfl) ⟨746502, by rfl⟩ : syracuseStep 1990673 = 1493005) B1493005
theorem B1327123 : Blo 1325481 1327123 := bstep (se 1 (by rfl) ⟨995342, by rfl⟩ : syracuseStep 1327123 = 1990685) B1990685
theorem B1990691 : Blo 1325481 1990691 := bstep (se 1 (by rfl) ⟨1493018, by rfl⟩ : syracuseStep 1990691 = 2986037) B2986037
theorem B1327139 : Blo 1325481 1327139 := bstep (se 1 (by rfl) ⟨995354, by rfl⟩ : syracuseStep 1327139 = 1990709) B1990709
theorem B4251683 : Blo 1325481 4251683 := bstep (se 1 (by rfl) ⟨3188762, by rfl⟩ : syracuseStep 4251683 = 6377525) B6377525
theorem B1327155 : Blo 1325481 1327155 := bstep (se 1 (by rfl) ⟨995366, by rfl⟩ : syracuseStep 1327155 = 1990733) B1990733
theorem B1990721 : Blo 1325481 1990721 := bstep (se 2 (by rfl) ⟨746520, by rfl⟩ : syracuseStep 1990721 = 1493041) B1493041
theorem B1327171 : Blo 1325481 1327171 := bstep (se 1 (by rfl) ⟨995378, by rfl⟩ : syracuseStep 1327171 = 1990757) B1990757
theorem B1990739 : Blo 1325481 1990739 := bstep (se 1 (by rfl) ⟨1493054, by rfl⟩ : syracuseStep 1990739 = 2986109) B2986109
theorem B1327187 : Blo 1325481 1327187 := bstep (se 1 (by rfl) ⟨995390, by rfl⟩ : syracuseStep 1327187 = 1990781) B1990781
theorem B1327203 : Blo 1325481 1327203 := bstep (se 1 (by rfl) ⟨995402, by rfl⟩ : syracuseStep 1327203 = 1990805) B1990805
theorem B4251761 : Blo 1325481 4251761 := bstep (se 2 (by rfl) ⟨1594410, by rfl⟩ : syracuseStep 4251761 = 3188821) B3188821
theorem B1990769 : Blo 1325481 1990769 := bstep (se 2 (by rfl) ⟨746538, by rfl⟩ : syracuseStep 1990769 = 1493077) B1493077
theorem B1327219 : Blo 1325481 1327219 := bstep (se 1 (by rfl) ⟨995414, by rfl⟩ : syracuseStep 1327219 = 1990829) B1990829
theorem B1990787 : Blo 1325481 1990787 := bstep (se 1 (by rfl) ⟨1493090, by rfl⟩ : syracuseStep 1990787 = 2986181) B2986181
theorem B1327235 : Blo 1325481 1327235 := bstep (se 1 (by rfl) ⟨995426, by rfl⟩ : syracuseStep 1327235 = 1990853) B1990853
theorem B1327251 : Blo 1325481 1327251 := bstep (se 1 (by rfl) ⟨995438, by rfl⟩ : syracuseStep 1327251 = 1990877) B1990877
theorem B1990817 : Blo 1325481 1990817 := bstep (se 2 (by rfl) ⟨746556, by rfl⟩ : syracuseStep 1990817 = 1493113) B1493113
theorem B1327267 : Blo 1325481 1327267 := bstep (se 1 (by rfl) ⟨995450, by rfl⟩ : syracuseStep 1327267 = 1990901) B1990901
theorem B1990835 : Blo 1325481 1990835 := bstep (se 1 (by rfl) ⟨1493126, by rfl⟩ : syracuseStep 1990835 = 2986253) B2986253
theorem B1327283 : Blo 1325481 1327283 := bstep (se 1 (by rfl) ⟨995462, by rfl⟩ : syracuseStep 1327283 = 1990925) B1990925
theorem B1679555 : Blo 1325481 1679555 := bstep (se 1 (by rfl) ⟨1259666, by rfl⟩ : syracuseStep 1679555 = 2519333) B2519333
theorem B1327299 : Blo 1325481 1327299 := bstep (se 1 (by rfl) ⟨995474, by rfl⟩ : syracuseStep 1327299 = 1990949) B1990949
theorem B1990865 : Blo 1325481 1990865 := bstep (se 2 (by rfl) ⟨746574, by rfl⟩ : syracuseStep 1990865 = 1493149) B1493149
theorem B1327315 : Blo 1325481 1327315 := bstep (se 1 (by rfl) ⟨995486, by rfl⟩ : syracuseStep 1327315 = 1990973) B1990973
theorem B1990883 : Blo 1325481 1990883 := bstep (se 1 (by rfl) ⟨1493162, by rfl⟩ : syracuseStep 1990883 = 2986325) B2986325
theorem B1327331 : Blo 1325481 1327331 := bstep (se 1 (by rfl) ⟨995498, by rfl⟩ : syracuseStep 1327331 = 1990997) B1990997
theorem B1491187 : Blo 1325481 1491187 := bstep (se 1 (by rfl) ⟨1118390, by rfl⟩ : syracuseStep 1491187 = 2236781) B2236781
theorem B1327347 : Blo 1325481 1327347 := bstep (se 1 (by rfl) ⟨995510, by rfl⟩ : syracuseStep 1327347 = 1991021) B1991021
theorem B1868033 : Blo 1325481 1868033 := bstep (se 2 (by rfl) ⟨700512, by rfl⟩ : syracuseStep 1868033 = 1401025) B1401025
theorem B1990913 : Blo 1325481 1990913 := bstep (se 2 (by rfl) ⟨746592, by rfl⟩ : syracuseStep 1990913 = 1493185) B1493185
theorem B3358979 : Blo 1325481 3358979 := bstep (se 1 (by rfl) ⟨2519234, by rfl⟩ : syracuseStep 3358979 = 5038469) B5038469
theorem B1327363 : Blo 1325481 1327363 := bstep (se 1 (by rfl) ⟨995522, by rfl⟩ : syracuseStep 1327363 = 1991045) B1991045
theorem B1990931 : Blo 1325481 1990931 := bstep (se 1 (by rfl) ⟨1493198, by rfl⟩ : syracuseStep 1990931 = 2986397) B2986397
theorem B1327379 : Blo 1325481 1327379 := bstep (se 1 (by rfl) ⟨995534, by rfl⟩ : syracuseStep 1327379 = 1991069) B1991069
theorem B1327395 : Blo 1325481 1327395 := bstep (se 1 (by rfl) ⟨995546, by rfl⟩ : syracuseStep 1327395 = 1991093) B1991093
theorem B4030765 : Blo 1325481 4030765 := bstep (se 3 (by rfl) ⟨755768, by rfl⟩ : syracuseStep 4030765 = 1511537) B1511537
theorem B3776813 : Blo 1325481 3776813 := bstep (se 3 (by rfl) ⟨708152, by rfl⟩ : syracuseStep 3776813 = 1416305) B1416305
theorem B1990961 : Blo 1325481 1990961 := bstep (se 2 (by rfl) ⟨746610, by rfl⟩ : syracuseStep 1990961 = 1493221) B1493221
theorem B1327411 : Blo 1325481 1327411 := bstep (se 1 (by rfl) ⟨995558, by rfl⟩ : syracuseStep 1327411 = 1991117) B1991117
theorem B1990979 : Blo 1325481 1990979 := bstep (se 1 (by rfl) ⟨1493234, by rfl⟩ : syracuseStep 1990979 = 2986469) B2986469
theorem B1327427 : Blo 1325481 1327427 := bstep (se 1 (by rfl) ⟨995570, by rfl⟩ : syracuseStep 1327427 = 1991141) B1991141
theorem B1327443 : Blo 1325481 1327443 := bstep (se 1 (by rfl) ⟨995582, by rfl⟩ : syracuseStep 1327443 = 1991165) B1991165
theorem B1991009 : Blo 1325481 1991009 := bstep (se 2 (by rfl) ⟨746628, by rfl⟩ : syracuseStep 1991009 = 1493257) B1493257
theorem B1327459 : Blo 1325481 1327459 := bstep (se 1 (by rfl) ⟨995594, by rfl⟩ : syracuseStep 1327459 = 1991189) B1991189
theorem B3776881 : Blo 1325481 3776881 := bstep (se 2 (by rfl) ⟨1416330, by rfl⟩ : syracuseStep 3776881 = 2832661) B2832661
theorem B1991027 : Blo 1325481 1991027 := bstep (se 1 (by rfl) ⟨1493270, by rfl⟩ : syracuseStep 1991027 = 2986541) B2986541
theorem B1327475 : Blo 1325481 1327475 := bstep (se 1 (by rfl) ⟨995606, by rfl⟩ : syracuseStep 1327475 = 1991213) B1991213
theorem B2236801 : Blo 1325481 2236801 := bstep (se 2 (by rfl) ⟨838800, by rfl⟩ : syracuseStep 2236801 = 1677601) B1677601
theorem B1491331 : Blo 1325481 1491331 := bstep (se 1 (by rfl) ⟨1118498, by rfl⟩ : syracuseStep 1491331 = 2236997) B2236997
theorem B1991057 : Blo 1325481 1991057 := bstep (se 2 (by rfl) ⟨746646, by rfl⟩ : syracuseStep 1991057 = 1493293) B1493293
theorem B2236835 : Blo 1325481 2236835 := bstep (se 1 (by rfl) ⟨1677626, by rfl⟩ : syracuseStep 2236835 = 3355253) B3355253
theorem B2015651 : Blo 1325481 2015651 := bstep (se 1 (by rfl) ⟨1511738, by rfl⟩ : syracuseStep 2015651 = 3023477) B3023477
theorem B1991075 : Blo 1325481 1991075 := bstep (se 1 (by rfl) ⟨1493306, by rfl⟩ : syracuseStep 1991075 = 2986613) B2986613
theorem B1991105 : Blo 1325481 1991105 := bstep (se 2 (by rfl) ⟨746664, by rfl⟩ : syracuseStep 1991105 = 1493329) B1493329
theorem B3359171 : Blo 1325481 3359171 := bstep (se 1 (by rfl) ⟨2519378, by rfl⟩ : syracuseStep 3359171 = 5038757) B5038757
theorem B14336453 : Blo 1325481 14336453 := bstep (se 4 (by rfl) ⟨1344042, by rfl⟩ : syracuseStep 14336453 = 2688085) B2688085
theorem B1991123 : Blo 1325481 1991123 := bstep (se 1 (by rfl) ⟨1493342, by rfl⟩ : syracuseStep 1991123 = 2986685) B2986685
theorem B1991153 : Blo 1325481 1991153 := bstep (se 2 (by rfl) ⟨746682, by rfl⟩ : syracuseStep 1991153 = 1493365) B1493365
theorem B1991171 : Blo 1325481 1991171 := bstep (se 1 (by rfl) ⟨1493378, by rfl⟩ : syracuseStep 1991171 = 2986757) B2986757
theorem B1491475 : Blo 1325481 1491475 := bstep (se 1 (by rfl) ⟨1118606, by rfl⟩ : syracuseStep 1491475 = 2237213) B2237213
theorem B1991201 : Blo 1325481 1991201 := bstep (se 2 (by rfl) ⟨746700, by rfl⟩ : syracuseStep 1991201 = 1493401) B1493401
theorem B2236963 : Blo 1325481 2236963 := bstep (se 1 (by rfl) ⟨1677722, by rfl⟩ : syracuseStep 2236963 = 3355445) B3355445
theorem B1991219 : Blo 1325481 1991219 := bstep (se 1 (by rfl) ⟨1493414, by rfl⟩ : syracuseStep 1991219 = 2986829) B2986829
theorem B3777155 : Blo 1325481 3777155 := bstep (se 1 (by rfl) ⟨2832866, by rfl⟩ : syracuseStep 3777155 = 5665733) B5665733
theorem B2982545 : Blo 1325481 2982545 := bstep (se 2 (by rfl) ⟨1118454, by rfl⟩ : syracuseStep 2982545 = 2236909) B2236909
theorem B2982563 : Blo 1325481 2982563 := bstep (se 1 (by rfl) ⟨2236922, by rfl⟩ : syracuseStep 2982563 = 4473845) B4473845
theorem B1491619 : Blo 1325481 1491619 := bstep (se 1 (by rfl) ⟨1118714, by rfl⟩ : syracuseStep 1491619 = 2237429) B2237429
theorem B4473521 : Blo 1325481 4473521 := bstep (se 2 (by rfl) ⟨1677570, by rfl⟩ : syracuseStep 4473521 = 3355141) B3355141
theorem B2237105 : Blo 1325481 2237105 := bstep (se 2 (by rfl) ⟨838914, by rfl⟩ : syracuseStep 2237105 = 1677829) B1677829
theorem B2237233 : Blo 1325481 2237233 := bstep (se 2 (by rfl) ⟨838962, by rfl⟩ : syracuseStep 2237233 = 1677925) B1677925
theorem B1491763 : Blo 1325481 1491763 := bstep (se 1 (by rfl) ⟨1118822, by rfl⟩ : syracuseStep 1491763 = 2237645) B2237645
theorem B16991045 : Blo 1325481 16991045 := bstep (se 4 (by rfl) ⟨1592910, by rfl⟩ : syracuseStep 16991045 = 3185821) B3185821
theorem B2237267 : Blo 1325481 2237267 := bstep (se 1 (by rfl) ⟨1677950, by rfl⟩ : syracuseStep 2237267 = 3355901) B3355901
theorem B2982833 : Blo 1325481 2982833 := bstep (se 2 (by rfl) ⟨1118562, by rfl⟩ : syracuseStep 2982833 = 2237125) B2237125
theorem B2982851 : Blo 1325481 2982851 := bstep (se 1 (by rfl) ⟨2237138, by rfl⟩ : syracuseStep 2982851 = 4474277) B4474277
theorem B1491907 : Blo 1325481 1491907 := bstep (se 1 (by rfl) ⟨1118930, by rfl⟩ : syracuseStep 1491907 = 2237861) B2237861
theorem B2237395 : Blo 1325481 2237395 := bstep (se 1 (by rfl) ⟨1678046, by rfl⟩ : syracuseStep 2237395 = 3356093) B3356093
theorem B6374371 : Blo 1325481 6374371 := bstep (se 1 (by rfl) ⟨4780778, by rfl⟩ : syracuseStep 6374371 = 9561557) B9561557
theorem B4031473 : Blo 1325481 4031473 := bstep (se 2 (by rfl) ⟨1511802, by rfl⟩ : syracuseStep 4031473 = 3023605) B3023605
theorem B7169093 : Blo 1325481 7169093 := bstep (se 4 (by rfl) ⟨672102, by rfl⟩ : syracuseStep 7169093 = 1344205) B1344205
theorem B1492051 : Blo 1325481 1492051 := bstep (se 1 (by rfl) ⟨1119038, by rfl⟩ : syracuseStep 1492051 = 2238077) B2238077
theorem B2237537 : Blo 1325481 2237537 := bstep (se 2 (by rfl) ⟨839076, by rfl⟩ : syracuseStep 2237537 = 1678153) B1678153
theorem B4474061 : Blo 1325481 4474061 := bstep (se 3 (by rfl) ⟨838886, by rfl⟩ : syracuseStep 4474061 = 1677773) B1677773
theorem B2983121 : Blo 1325481 2983121 := bstep (se 2 (by rfl) ⟨1118670, by rfl⟩ : syracuseStep 2983121 = 2237341) B2237341
theorem B2237665 : Blo 1325481 2237665 := bstep (se 2 (by rfl) ⟨839124, by rfl⟩ : syracuseStep 2237665 = 1678249) B1678249
theorem B2983139 : Blo 1325481 2983139 := bstep (se 1 (by rfl) ⟨2237354, by rfl⟩ : syracuseStep 2983139 = 4474709) B4474709
theorem B1492195 : Blo 1325481 1492195 := bstep (se 1 (by rfl) ⟨1119146, by rfl⟩ : syracuseStep 1492195 = 2238293) B2238293
theorem B4474115 : Blo 1325481 4474115 := bstep (se 1 (by rfl) ⟨3355586, by rfl⟩ : syracuseStep 4474115 = 6711173) B6711173
theorem B2237699 : Blo 1325481 2237699 := bstep (se 1 (by rfl) ⟨1678274, by rfl⟩ : syracuseStep 2237699 = 3356549) B3356549
theorem B2016515 : Blo 1325481 2016515 := bstep (se 1 (by rfl) ⟨1512386, by rfl⟩ : syracuseStep 2016515 = 3024773) B3024773
theorem B3228977 : Blo 1325481 3228977 := bstep (se 2 (by rfl) ⟨1210866, by rfl⟩ : syracuseStep 3228977 = 2421733) B2421733
theorem B8504675 : Blo 1325481 8504675 := bstep (se 1 (by rfl) ⟨6378506, by rfl⟩ : syracuseStep 8504675 = 12757013) B12757013
theorem B3360113 : Blo 1325481 3360113 := bstep (se 2 (by rfl) ⟨1260042, by rfl⟩ : syracuseStep 3360113 = 2520085) B2520085
theorem B1492339 : Blo 1325481 1492339 := bstep (se 1 (by rfl) ⟨1119254, by rfl⟩ : syracuseStep 1492339 = 2238509) B2238509
theorem B2237827 : Blo 1325481 2237827 := bstep (se 1 (by rfl) ⟨1678370, by rfl⟩ : syracuseStep 2237827 = 3356741) B3356741
theorem B3360163 : Blo 1325481 3360163 := bstep (se 1 (by rfl) ⟨2520122, by rfl⟩ : syracuseStep 3360163 = 5040245) B5040245
theorem B3777997 : Blo 1325481 3777997 := bstep (se 3 (by rfl) ⟨708374, by rfl⟩ : syracuseStep 3777997 = 1416749) B1416749
theorem B5375459 : Blo 1325481 5375459 := bstep (se 1 (by rfl) ⟨4031594, by rfl⟩ : syracuseStep 5375459 = 8063189) B8063189
theorem B2983409 : Blo 1325481 2983409 := bstep (se 2 (by rfl) ⟨1118778, by rfl⟩ : syracuseStep 2983409 = 2237557) B2237557
theorem B2983427 : Blo 1325481 2983427 := bstep (se 1 (by rfl) ⟨2237570, by rfl⟩ : syracuseStep 2983427 = 4475141) B4475141
theorem B1492483 : Blo 1325481 1492483 := bstep (se 1 (by rfl) ⟨1119362, by rfl⟩ : syracuseStep 1492483 = 2238725) B2238725
theorem B4474385 : Blo 1325481 4474385 := bstep (se 2 (by rfl) ⟨1677894, by rfl⟩ : syracuseStep 4474385 = 3355789) B3355789
theorem B2237969 : Blo 1325481 2237969 := bstep (se 2 (by rfl) ⟨839238, by rfl⟩ : syracuseStep 2237969 = 1678477) B1678477
theorem B5375587 : Blo 1325481 5375587 := bstep (se 1 (by rfl) ⟨4031690, by rfl⟩ : syracuseStep 5375587 = 8063381) B8063381
theorem B3778157 : Blo 1325481 3778157 := bstep (se 3 (by rfl) ⟨708404, by rfl⟩ : syracuseStep 3778157 = 1416809) B1416809
theorem B5039729 : Blo 1325481 5039729 := bstep (se 2 (by rfl) ⟨1889898, by rfl⟩ : syracuseStep 5039729 = 3779797) B3779797
theorem B5662349 : Blo 1325481 5662349 := bstep (se 3 (by rfl) ⟨1061690, by rfl⟩ : syracuseStep 5662349 = 2123381) B2123381
theorem B2238097 : Blo 1325481 2238097 := bstep (se 2 (by rfl) ⟨839286, by rfl⟩ : syracuseStep 2238097 = 1678573) B1678573
theorem B1492627 : Blo 1325481 1492627 := bstep (se 1 (by rfl) ⟨1119470, by rfl⟩ : syracuseStep 1492627 = 2238941) B2238941
theorem B2238131 : Blo 1325481 2238131 := bstep (se 1 (by rfl) ⟨1678598, by rfl⟩ : syracuseStep 2238131 = 3357197) B3357197
theorem B6711011 : Blo 1325481 6711011 := bstep (se 1 (by rfl) ⟨5033258, by rfl⟩ : syracuseStep 6711011 = 10066517) B10066517
theorem B7653133 : Blo 1325481 7653133 := bstep (se 3 (by rfl) ⟨1434962, by rfl⟩ : syracuseStep 7653133 = 2869925) B2869925
theorem B2983697 : Blo 1325481 2983697 := bstep (se 2 (by rfl) ⟨1118886, by rfl⟩ : syracuseStep 2983697 = 2237773) B2237773
theorem B2983715 : Blo 1325481 2983715 := bstep (se 1 (by rfl) ⟨2237786, by rfl⟩ : syracuseStep 2983715 = 4475573) B4475573
theorem B7268131 : Blo 1325481 7268131 := bstep (se 1 (by rfl) ⟨5451098, by rfl⟩ : syracuseStep 7268131 = 10902197) B10902197
theorem B3778339 : Blo 1325481 3778339 := bstep (se 1 (by rfl) ⟨2833754, by rfl⟩ : syracuseStep 3778339 = 5667509) B5667509
theorem B1492771 : Blo 1325481 1492771 := bstep (se 1 (by rfl) ⟨1119578, by rfl⟩ : syracuseStep 1492771 = 2239157) B2239157
theorem B4540195 : Blo 1325481 4540195 := bstep (se 1 (by rfl) ⟨3405146, by rfl⟩ : syracuseStep 4540195 = 6810293) B6810293
theorem B2238259 : Blo 1325481 2238259 := bstep (se 1 (by rfl) ⟨1678694, by rfl⟩ : syracuseStep 2238259 = 3357389) B3357389
theorem B3401617 : Blo 1325481 3401617 := bstep (se 2 (by rfl) ⟨1275606, by rfl⟩ : syracuseStep 3401617 = 2551213) B2551213
theorem B1492915 : Blo 1325481 1492915 := bstep (se 1 (by rfl) ⟨1119686, by rfl⟩ : syracuseStep 1492915 = 2239373) B2239373
theorem B2238401 : Blo 1325481 2238401 := bstep (se 2 (by rfl) ⟨839400, by rfl⟩ : syracuseStep 2238401 = 1678801) B1678801
theorem B4474925 : Blo 1325481 4474925 := bstep (se 3 (by rfl) ⟨839048, by rfl⟩ : syracuseStep 4474925 = 1678097) B1678097
theorem B2983985 : Blo 1325481 2983985 := bstep (se 2 (by rfl) ⟨1118994, by rfl⟩ : syracuseStep 2983985 = 2237989) B2237989
theorem B2238529 : Blo 1325481 2238529 := bstep (se 2 (by rfl) ⟨839448, by rfl⟩ : syracuseStep 2238529 = 1678897) B1678897
theorem B2984003 : Blo 1325481 2984003 := bstep (se 1 (by rfl) ⟨2238002, by rfl⟩ : syracuseStep 2984003 = 4476005) B4476005
theorem B1493059 : Blo 1325481 1493059 := bstep (se 1 (by rfl) ⟨1119794, by rfl⟩ : syracuseStep 1493059 = 2239589) B2239589
theorem B4474979 : Blo 1325481 4474979 := bstep (se 1 (by rfl) ⟨3356234, by rfl⟩ : syracuseStep 4474979 = 6712469) B6712469
theorem B2238563 : Blo 1325481 2238563 := bstep (se 1 (by rfl) ⟨1678922, by rfl⟩ : syracuseStep 2238563 = 3357845) B3357845
theorem B8407153 : Blo 1325481 8407153 := bstep (se 2 (by rfl) ⟨3152682, by rfl⟩ : syracuseStep 8407153 = 6305365) B6305365
theorem B8497315 : Blo 1325481 8497315 := bstep (se 1 (by rfl) ⟨6372986, by rfl⟩ : syracuseStep 8497315 = 12745973) B12745973
theorem B2517169 : Blo 1325481 2517169 := bstep (se 2 (by rfl) ⟨943938, by rfl⟩ : syracuseStep 2517169 = 1887877) B1887877
theorem B6375601 : Blo 1325481 6375601 := bstep (se 2 (by rfl) ⟨2390850, by rfl⟩ : syracuseStep 6375601 = 4781701) B4781701
theorem B1493203 : Blo 1325481 1493203 := bstep (se 1 (by rfl) ⟨1119902, by rfl⟩ : syracuseStep 1493203 = 2239805) B2239805
theorem B2238691 : Blo 1325481 2238691 := bstep (se 1 (by rfl) ⟨1679018, by rfl⟩ : syracuseStep 2238691 = 3358037) B3358037
theorem B16132405 : Blo 1325481 16132405 := bstep (se 5 (by rfl) ⟨756206, by rfl⟩ : syracuseStep 16132405 = 1512413) B1512413
theorem B25512245 : Blo 1325481 25512245 := bstep (se 5 (by rfl) ⟨1195886, by rfl⟩ : syracuseStep 25512245 = 2391773) B2391773
theorem B2984273 : Blo 1325481 2984273 := bstep (se 2 (by rfl) ⟨1119102, by rfl⟩ : syracuseStep 2984273 = 2238205) B2238205
theorem B2984291 : Blo 1325481 2984291 := bstep (se 1 (by rfl) ⟨2238218, by rfl⟩ : syracuseStep 2984291 = 4476437) B4476437
theorem B1493347 : Blo 1325481 1493347 := bstep (se 1 (by rfl) ⟨1120010, by rfl⟩ : syracuseStep 1493347 = 2240021) B2240021
theorem B4475249 : Blo 1325481 4475249 := bstep (se 2 (by rfl) ⟨1678218, by rfl⟩ : syracuseStep 4475249 = 3356437) B3356437
theorem B9562481 : Blo 1325481 9562481 := bstep (se 2 (by rfl) ⟨3585930, by rfl⟩ : syracuseStep 9562481 = 7171861) B7171861
theorem B2238833 : Blo 1325481 2238833 := bstep (se 2 (by rfl) ⟨839562, by rfl⟩ : syracuseStep 2238833 = 1679125) B1679125
theorem B6719921 : Blo 1325481 6719921 := bstep (se 2 (by rfl) ⟨2519970, by rfl⟩ : syracuseStep 6719921 = 5039941) B5039941
theorem B2124227 : Blo 1325481 2124227 := bstep (se 1 (by rfl) ⟨1593170, by rfl⟩ : syracuseStep 2124227 = 3186341) B3186341
theorem B8063459 : Blo 1325481 8063459 := bstep (se 1 (by rfl) ⟨6047594, by rfl⟩ : syracuseStep 8063459 = 12095189) B12095189
theorem B2238961 : Blo 1325481 2238961 := bstep (se 2 (by rfl) ⟨839610, by rfl⟩ : syracuseStep 2238961 = 1679221) B1679221
theorem B2017793 : Blo 1325481 2017793 := bstep (se 2 (by rfl) ⟨756672, by rfl⟩ : syracuseStep 2017793 = 1513345) B1513345
theorem B7170565 : Blo 1325481 7170565 := bstep (se 4 (by rfl) ⟨672240, by rfl⟩ : syracuseStep 7170565 = 1344481) B1344481
theorem B6711821 : Blo 1325481 6711821 := bstep (se 3 (by rfl) ⟨1258466, by rfl⟩ : syracuseStep 6711821 = 2516933) B2516933
theorem B2238995 : Blo 1325481 2238995 := bstep (se 1 (by rfl) ⟨1679246, by rfl⟩ : syracuseStep 2238995 = 3358493) B3358493
theorem B2517571 : Blo 1325481 2517571 := bstep (se 1 (by rfl) ⟨1888178, by rfl⟩ : syracuseStep 2517571 = 3776357) B3776357
theorem B2517617 : Blo 1325481 2517617 := bstep (se 2 (by rfl) ⟨944106, by rfl⟩ : syracuseStep 2517617 = 1888213) B1888213
theorem B2984561 : Blo 1325481 2984561 := bstep (se 2 (by rfl) ⟨1119210, by rfl⟩ : syracuseStep 2984561 = 2238421) B2238421
theorem B2984579 : Blo 1325481 2984579 := bstep (se 1 (by rfl) ⟨2238434, by rfl⟩ : syracuseStep 2984579 = 4476869) B4476869
theorem B2239123 : Blo 1325481 2239123 := bstep (se 1 (by rfl) ⟨1679342, by rfl⟩ : syracuseStep 2239123 = 3358685) B3358685
theorem B11340485 : Blo 1325481 11340485 := bstep (se 4 (by rfl) ⟨1063170, by rfl⟩ : syracuseStep 11340485 = 2126341) B2126341
theorem B4664017 : Blo 1325481 4664017 := bstep (se 2 (by rfl) ⟨1749006, by rfl⟩ : syracuseStep 4664017 = 3498013) B3498013
theorem B2239265 : Blo 1325481 2239265 := bstep (se 2 (by rfl) ⟨839724, by rfl⟩ : syracuseStep 2239265 = 1679449) B1679449
theorem B7654193 : Blo 1325481 7654193 := bstep (se 2 (by rfl) ⟨2870322, by rfl⟩ : syracuseStep 7654193 = 5740645) B5740645
theorem B3025795 : Blo 1325481 3025795 := bstep (se 1 (by rfl) ⟨2269346, by rfl⟩ : syracuseStep 3025795 = 4538693) B4538693
theorem B4475789 : Blo 1325481 4475789 := bstep (se 3 (by rfl) ⟨839210, by rfl⟩ : syracuseStep 4475789 = 1678421) B1678421
theorem B2517905 : Blo 1325481 2517905 := bstep (se 2 (by rfl) ⟨944214, by rfl⟩ : syracuseStep 2517905 = 1888429) B1888429
theorem B2984849 : Blo 1325481 2984849 := bstep (se 2 (by rfl) ⟨1119318, by rfl⟩ : syracuseStep 2984849 = 2238637) B2238637
theorem B2239393 : Blo 1325481 2239393 := bstep (se 2 (by rfl) ⟨839772, by rfl⟩ : syracuseStep 2239393 = 1679545) B1679545
theorem B2984867 : Blo 1325481 2984867 := bstep (se 1 (by rfl) ⟨2238650, by rfl⟩ : syracuseStep 2984867 = 4477301) B4477301
theorem B4475843 : Blo 1325481 4475843 := bstep (se 1 (by rfl) ⟨3356882, by rfl⟩ : syracuseStep 4475843 = 6713765) B6713765
theorem B2124739 : Blo 1325481 2124739 := bstep (se 1 (by rfl) ⟨1593554, by rfl⟩ : syracuseStep 2124739 = 3187109) B3187109
theorem B2239427 : Blo 1325481 2239427 := bstep (se 1 (by rfl) ⟨1679570, by rfl⟩ : syracuseStep 2239427 = 3359141) B3359141
theorem B2124785 : Blo 1325481 2124785 := bstep (se 2 (by rfl) ⟨796794, by rfl⟩ : syracuseStep 2124785 = 1593589) B1593589
theorem B2239555 : Blo 1325481 2239555 := bstep (se 1 (by rfl) ⟨1679666, by rfl⟩ : syracuseStep 2239555 = 3359333) B3359333
theorem B4033613 : Blo 1325481 4033613 := bstep (se 3 (by rfl) ⟨756302, by rfl⟩ : syracuseStep 4033613 = 1512605) B1512605
theorem B1887313 : Blo 1325481 1887313 := bstep (se 2 (by rfl) ⟨707742, by rfl⟩ : syracuseStep 1887313 = 1415485) B1415485
theorem B1887347 : Blo 1325481 1887347 := bstep (se 1 (by rfl) ⟨1415510, by rfl⟩ : syracuseStep 1887347 = 2831021) B2831021
theorem B8498317 : Blo 1325481 8498317 := bstep (se 3 (by rfl) ⟨1593434, by rfl⟩ : syracuseStep 8498317 = 3186869) B3186869
theorem B3779729 : Blo 1325481 3779729 := bstep (se 2 (by rfl) ⟨1417398, by rfl⟩ : syracuseStep 3779729 = 2834797) B2834797
theorem B5033123 : Blo 1325481 5033123 := bstep (se 1 (by rfl) ⟨3774842, by rfl⟩ : syracuseStep 5033123 = 7549685) B7549685
theorem B5033137 : Blo 1325481 5033137 := bstep (se 2 (by rfl) ⟨1887426, by rfl⟩ : syracuseStep 5033137 = 3774853) B3774853
theorem B2985137 : Blo 1325481 2985137 := bstep (se 2 (by rfl) ⟨1119426, by rfl⟩ : syracuseStep 2985137 = 2238853) B2238853
theorem B2985155 : Blo 1325481 2985155 := bstep (se 1 (by rfl) ⟨2238866, by rfl⟩ : syracuseStep 2985155 = 4477733) B4477733
theorem B4476113 : Blo 1325481 4476113 := bstep (se 2 (by rfl) ⟨1678542, by rfl⟩ : syracuseStep 4476113 = 3357085) B3357085
theorem B2239697 : Blo 1325481 2239697 := bstep (se 2 (by rfl) ⟨839886, by rfl⟩ : syracuseStep 2239697 = 1679773) B1679773
theorem B2239825 : Blo 1325481 2239825 := bstep (se 2 (by rfl) ⟨839934, by rfl⟩ : syracuseStep 2239825 = 1679869) B1679869
theorem B2239859 : Blo 1325481 2239859 := bstep (se 1 (by rfl) ⟨1679894, by rfl⟩ : syracuseStep 2239859 = 3359789) B3359789
theorem B2985425 : Blo 1325481 2985425 := bstep (se 2 (by rfl) ⟨1119534, by rfl⟩ : syracuseStep 2985425 = 2239069) B2239069
theorem B2985443 : Blo 1325481 2985443 := bstep (se 1 (by rfl) ⟨2239082, by rfl⟩ : syracuseStep 2985443 = 4478165) B4478165
theorem B9563633 : Blo 1325481 9563633 := bstep (se 2 (by rfl) ⟨3586362, by rfl⟩ : syracuseStep 9563633 = 7172725) B7172725
theorem B2239987 : Blo 1325481 2239987 := bstep (se 1 (by rfl) ⟨1679990, by rfl⟩ : syracuseStep 2239987 = 3359981) B3359981
theorem B2518627 : Blo 1325481 2518627 := bstep (se 1 (by rfl) ⟨1888970, by rfl⟩ : syracuseStep 2518627 = 3777941) B3777941
theorem B4034161 : Blo 1325481 4034161 := bstep (se 2 (by rfl) ⟨1512810, by rfl⟩ : syracuseStep 4034161 = 3025621) B3025621
theorem B2125457 : Blo 1325481 2125457 := bstep (se 2 (by rfl) ⟨797046, by rfl⟩ : syracuseStep 2125457 = 1594093) B1594093
theorem B1887905 : Blo 1325481 1887905 := bstep (se 2 (by rfl) ⟨707964, by rfl⟩ : syracuseStep 1887905 = 1415929) B1415929
theorem B4476653 : Blo 1325481 4476653 := bstep (se 3 (by rfl) ⟨839372, by rfl⟩ : syracuseStep 4476653 = 1678745) B1678745
theorem B1887985 : Blo 1325481 1887985 := bstep (se 2 (by rfl) ⟨707994, by rfl⟩ : syracuseStep 1887985 = 1415989) B1415989
theorem B2985713 : Blo 1325481 2985713 := bstep (se 2 (by rfl) ⟨1119642, by rfl⟩ : syracuseStep 2985713 = 2239285) B2239285
theorem B2985731 : Blo 1325481 2985731 := bstep (se 1 (by rfl) ⟨2239298, by rfl⟩ : syracuseStep 2985731 = 4478597) B4478597
theorem B4476707 : Blo 1325481 4476707 := bstep (se 1 (by rfl) ⟨3357530, by rfl⟩ : syracuseStep 4476707 = 6715061) B6715061
theorem B8064845 : Blo 1325481 8064845 := bstep (se 3 (by rfl) ⟨1512158, by rfl⟩ : syracuseStep 8064845 = 3024317) B3024317
theorem B5746531 : Blo 1325481 5746531 := bstep (se 1 (by rfl) ⟨4309898, by rfl⟩ : syracuseStep 5746531 = 8619797) B8619797
theorem B1363811 : Blo 1325481 1363811 := bstep (se 1 (by rfl) ⟨1022858, by rfl⟩ : syracuseStep 1363811 = 2045717) B2045717
theorem B2986001 : Blo 1325481 2986001 := bstep (se 2 (by rfl) ⟨1119750, by rfl⟩ : syracuseStep 2986001 = 2239501) B2239501
theorem B2519075 : Blo 1325481 2519075 := bstep (se 1 (by rfl) ⟨1889306, by rfl⟩ : syracuseStep 2519075 = 3778613) B3778613
theorem B2986019 : Blo 1325481 2986019 := bstep (se 1 (by rfl) ⟨2239514, by rfl⟩ : syracuseStep 2986019 = 4479029) B4479029
theorem B4476977 : Blo 1325481 4476977 := bstep (se 2 (by rfl) ⟨1678866, by rfl⟩ : syracuseStep 4476977 = 3357733) B3357733
theorem B4304963 : Blo 1325481 4304963 := bstep (se 1 (by rfl) ⟨3228722, by rfl⟩ : syracuseStep 4304963 = 6457445) B6457445
theorem B4247633 : Blo 1325481 4247633 := bstep (se 2 (by rfl) ⟨1592862, by rfl⟩ : syracuseStep 4247633 = 3185725) B3185725
theorem B6131825 : Blo 1325481 6131825 := bstep (se 2 (by rfl) ⟨2299434, by rfl⟩ : syracuseStep 6131825 = 4598869) B4598869
theorem B2125969 : Blo 1325481 2125969 := bstep (se 2 (by rfl) ⟨797238, by rfl⟩ : syracuseStep 2125969 = 1594477) B1594477
theorem B2986289 : Blo 1325481 2986289 := bstep (se 2 (by rfl) ⟨1119858, by rfl⟩ : syracuseStep 2986289 = 2239717) B2239717
theorem B2519363 : Blo 1325481 2519363 := bstep (se 1 (by rfl) ⟨1889522, by rfl⟩ : syracuseStep 2519363 = 3779045) B3779045
theorem B2986307 : Blo 1325481 2986307 := bstep (se 1 (by rfl) ⟨2239730, by rfl⟩ : syracuseStep 2986307 = 4479461) B4479461
theorem B3232145 : Blo 1325481 3232145 := bstep (se 2 (by rfl) ⟨1212054, by rfl⟩ : syracuseStep 3232145 = 2424109) B2424109
theorem B1888771 : Blo 1325481 1888771 := bstep (se 1 (by rfl) ⟨1416578, by rfl⟩ : syracuseStep 1888771 = 2833157) B2833157
theorem B3027473 : Blo 1325481 3027473 := bstep (se 2 (by rfl) ⟨1135302, by rfl⟩ : syracuseStep 3027473 = 2270605) B2270605
theorem B4477517 : Blo 1325481 4477517 := bstep (se 3 (by rfl) ⟨839534, by rfl⟩ : syracuseStep 4477517 = 1679069) B1679069
theorem B3404369 : Blo 1325481 3404369 := bstep (se 2 (by rfl) ⟨1276638, by rfl⟩ : syracuseStep 3404369 = 2553277) B2553277
theorem B2986577 : Blo 1325481 2986577 := bstep (se 2 (by rfl) ⟨1119966, by rfl⟩ : syracuseStep 2986577 = 2239933) B2239933
theorem B5034595 : Blo 1325481 5034595 := bstep (se 1 (by rfl) ⟨3775946, by rfl⟩ : syracuseStep 5034595 = 7551893) B7551893
theorem B2986595 : Blo 1325481 2986595 := bstep (se 1 (by rfl) ⟨2239946, by rfl⟩ : syracuseStep 2986595 = 4479893) B4479893
theorem B4477571 : Blo 1325481 4477571 := bstep (se 1 (by rfl) ⟨3358178, by rfl⟩ : syracuseStep 4477571 = 6716357) B6716357
theorem B7172813 : Blo 1325481 7172813 := bstep (se 3 (by rfl) ⟨1344902, by rfl⟩ : syracuseStep 7172813 = 2689805) B2689805
theorem B1512227 : Blo 1325481 1512227 := bstep (se 1 (by rfl) ⟨1134170, by rfl⟩ : syracuseStep 1512227 = 2268341) B2268341
theorem B4035437 : Blo 1325481 4035437 := bstep (se 3 (by rfl) ⟨756644, by rfl⟩ : syracuseStep 4035437 = 1513289) B1513289
theorem B3404675 : Blo 1325481 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B4477841 : Blo 1325481 4477841 := bstep (se 2 (by rfl) ⟨1679190, by rfl⟩ : syracuseStep 4477841 = 3358381) B3358381
theorem B1889249 : Blo 1325481 1889249 := bstep (se 2 (by rfl) ⟨708468, by rfl⟩ : syracuseStep 1889249 = 1416937) B1416937
theorem B1889363 : Blo 1325481 1889363 := bstep (se 1 (by rfl) ⟨1417022, by rfl⟩ : syracuseStep 1889363 = 2834045) B2834045
theorem B15119459 : Blo 1325481 15119459 := bstep (se 1 (by rfl) ⟨11339594, by rfl⟩ : syracuseStep 15119459 = 22679189) B22679189
theorem B1889443 : Blo 1325481 1889443 := bstep (se 1 (by rfl) ⟨1417082, by rfl⟩ : syracuseStep 1889443 = 2834165) B2834165
theorem B6378659 : Blo 1325481 6378659 := bstep (se 1 (by rfl) ⟨4783994, by rfl⟩ : syracuseStep 6378659 = 9567989) B9567989
theorem B3232931 : Blo 1325481 3232931 := bstep (se 1 (by rfl) ⟨2424698, by rfl⟩ : syracuseStep 3232931 = 4849397) B4849397
theorem B4248749 : Blo 1325481 4248749 := bstep (se 3 (by rfl) ⟨796640, by rfl⟩ : syracuseStep 4248749 = 1593281) B1593281
theorem B3585325 : Blo 1325481 3585325 := bstep (se 3 (by rfl) ⟨672248, by rfl⟩ : syracuseStep 3585325 = 1344497) B1344497
theorem B6714737 : Blo 1325481 6714737 := bstep (se 2 (by rfl) ⟨2518026, by rfl⟩ : syracuseStep 6714737 = 5036053) B5036053
theorem B4478381 : Blo 1325481 4478381 := bstep (se 3 (by rfl) ⟨839696, by rfl⟩ : syracuseStep 4478381 = 1679393) B1679393
theorem B3356113 : Blo 1325481 3356113 := bstep (se 2 (by rfl) ⟨1258542, by rfl⟩ : syracuseStep 3356113 = 2517085) B2517085
theorem B7550435 : Blo 1325481 7550435 := bstep (se 1 (by rfl) ⟨5662826, by rfl⟩ : syracuseStep 7550435 = 11325653) B11325653
theorem B4478435 : Blo 1325481 4478435 := bstep (se 1 (by rfl) ⟨3358826, by rfl⟩ : syracuseStep 4478435 = 6717653) B6717653
theorem B7263749 : Blo 1325481 7263749 := bstep (se 4 (by rfl) ⟨680976, by rfl⟩ : syracuseStep 7263749 = 1361953) B1361953
theorem B8066573 : Blo 1325481 8066573 := bstep (se 3 (by rfl) ⟨1512482, by rfl⟩ : syracuseStep 8066573 = 3024965) B3024965
theorem B5666381 : Blo 1325481 5666381 := bstep (se 3 (by rfl) ⟨1062446, by rfl⟩ : syracuseStep 5666381 = 2124893) B2124893
theorem B40818289 : Blo 1325481 40818289 := bstep (se 2 (by rfl) ⟨15306858, by rfl⟩ : syracuseStep 40818289 = 30613717) B30613717
theorem B1988225 : Blo 1325481 1988225 := bstep (se 2 (by rfl) ⟨745584, by rfl⟩ : syracuseStep 1988225 = 1491169) B1491169
theorem B1988243 : Blo 1325481 1988243 := bstep (se 1 (by rfl) ⟨1491182, by rfl⟩ : syracuseStep 1988243 = 2982365) B2982365
theorem B1988273 : Blo 1325481 1988273 := bstep (se 2 (by rfl) ⟨745602, by rfl⟩ : syracuseStep 1988273 = 1491205) B1491205
theorem B1988291 : Blo 1325481 1988291 := bstep (se 1 (by rfl) ⟨1491218, by rfl⟩ : syracuseStep 1988291 = 2982437) B2982437
theorem B1890001 : Blo 1325481 1890001 := bstep (se 2 (by rfl) ⟨708750, by rfl⟩ : syracuseStep 1890001 = 1417501) B1417501
theorem B1988321 : Blo 1325481 1988321 := bstep (se 2 (by rfl) ⟨745620, by rfl⟩ : syracuseStep 1988321 = 1491241) B1491241
theorem B3356387 : Blo 1325481 3356387 := bstep (se 1 (by rfl) ⟨2517290, by rfl⟩ : syracuseStep 3356387 = 5034581) B5034581
theorem B16996067 : Blo 1325481 16996067 := bstep (se 1 (by rfl) ⟨12747050, by rfl⟩ : syracuseStep 16996067 = 25494101) B25494101
theorem B4478705 : Blo 1325481 4478705 := bstep (se 2 (by rfl) ⟨1679514, by rfl⟩ : syracuseStep 4478705 = 3359029) B3359029
theorem B1988339 : Blo 1325481 1988339 := bstep (se 1 (by rfl) ⟨1491254, by rfl⟩ : syracuseStep 1988339 = 2982509) B2982509
theorem B2832131 : Blo 1325481 2832131 := bstep (se 1 (by rfl) ⟨2124098, by rfl⟩ : syracuseStep 2832131 = 4248197) B4248197
theorem B1988369 : Blo 1325481 1988369 := bstep (se 2 (by rfl) ⟨745638, by rfl⟩ : syracuseStep 1988369 = 1491277) B1491277
theorem B1988387 : Blo 1325481 1988387 := bstep (se 1 (by rfl) ⟨1491290, by rfl⟩ : syracuseStep 1988387 = 2982581) B2982581
theorem B1988417 : Blo 1325481 1988417 := bstep (se 2 (by rfl) ⟨745656, by rfl⟩ : syracuseStep 1988417 = 1491313) B1491313
theorem B1988435 : Blo 1325481 1988435 := bstep (se 1 (by rfl) ⟨1491326, by rfl⟩ : syracuseStep 1988435 = 2982653) B2982653
theorem B10213219 : Blo 1325481 10213219 := bstep (se 1 (by rfl) ⟨7659914, by rfl⟩ : syracuseStep 10213219 = 15319829) B15319829
theorem B1988465 : Blo 1325481 1988465 := bstep (se 2 (by rfl) ⟨745674, by rfl⟩ : syracuseStep 1988465 = 1491349) B1491349
theorem B1988483 : Blo 1325481 1988483 := bstep (se 1 (by rfl) ⟨1491362, by rfl⟩ : syracuseStep 1988483 = 2982725) B2982725
theorem B1988513 : Blo 1325481 1988513 := bstep (se 2 (by rfl) ⟨745692, by rfl⟩ : syracuseStep 1988513 = 1491385) B1491385
theorem B3356579 : Blo 1325481 3356579 := bstep (se 1 (by rfl) ⟨2517434, by rfl⟩ : syracuseStep 3356579 = 5034869) B5034869
theorem B5666723 : Blo 1325481 5666723 := bstep (se 1 (by rfl) ⟨4250042, by rfl⟩ : syracuseStep 5666723 = 8500085) B8500085
theorem B1988531 : Blo 1325481 1988531 := bstep (se 1 (by rfl) ⟨1491398, by rfl⟩ : syracuseStep 1988531 = 2982797) B2982797
theorem B1988561 : Blo 1325481 1988561 := bstep (se 2 (by rfl) ⟨745710, by rfl⟩ : syracuseStep 1988561 = 1491421) B1491421
theorem B1988579 : Blo 1325481 1988579 := bstep (se 1 (by rfl) ⟨1491434, by rfl⟩ : syracuseStep 1988579 = 2982869) B2982869
theorem B1701875 : Blo 1325481 1701875 := bstep (se 1 (by rfl) ⟨1276406, by rfl⟩ : syracuseStep 1701875 = 2552813) B2552813
theorem B1988609 : Blo 1325481 1988609 := bstep (se 2 (by rfl) ⟨745728, by rfl⟩ : syracuseStep 1988609 = 1491457) B1491457
theorem B12097549 : Blo 1325481 12097549 := bstep (se 3 (by rfl) ⟨2268290, by rfl⟩ : syracuseStep 12097549 = 4536581) B4536581
theorem B1988627 : Blo 1325481 1988627 := bstep (se 1 (by rfl) ⟨1491470, by rfl⟩ : syracuseStep 1988627 = 2982941) B2982941
theorem B1988657 : Blo 1325481 1988657 := bstep (se 2 (by rfl) ⟨745746, by rfl⟩ : syracuseStep 1988657 = 1491493) B1491493
theorem B1988675 : Blo 1325481 1988675 := bstep (se 1 (by rfl) ⟨1491506, by rfl⟩ : syracuseStep 1988675 = 2983013) B2983013
theorem B1988705 : Blo 1325481 1988705 := bstep (se 2 (by rfl) ⟨745764, by rfl⟩ : syracuseStep 1988705 = 1491529) B1491529
theorem B7166065 : Blo 1325481 7166065 := bstep (se 2 (by rfl) ⟨2687274, by rfl⟩ : syracuseStep 7166065 = 5374549) B5374549
theorem B1988723 : Blo 1325481 1988723 := bstep (se 1 (by rfl) ⟨1491542, by rfl⟩ : syracuseStep 1988723 = 2983085) B2983085
theorem B1988753 : Blo 1325481 1988753 := bstep (se 2 (by rfl) ⟨745782, by rfl⟩ : syracuseStep 1988753 = 1491565) B1491565
theorem B2554001 : Blo 1325481 2554001 := bstep (se 2 (by rfl) ⟨957750, by rfl⟩ : syracuseStep 2554001 = 1915501) B1915501
theorem B1988771 : Blo 1325481 1988771 := bstep (se 1 (by rfl) ⟨1491578, by rfl⟩ : syracuseStep 1988771 = 2983157) B2983157
theorem B1988801 : Blo 1325481 1988801 := bstep (se 2 (by rfl) ⟨745800, by rfl⟩ : syracuseStep 1988801 = 1491601) B1491601
theorem B7559365 : Blo 1325481 7559365 := bstep (se 4 (by rfl) ⟨708690, by rfl⟩ : syracuseStep 7559365 = 1417381) B1417381
theorem B1988819 : Blo 1325481 1988819 := bstep (se 1 (by rfl) ⟨1491614, by rfl⟩ : syracuseStep 1988819 = 2983229) B2983229
theorem B4249837 : Blo 1325481 4249837 := bstep (se 3 (by rfl) ⟨796844, by rfl⟩ : syracuseStep 4249837 = 1593689) B1593689
theorem B1988849 : Blo 1325481 1988849 := bstep (se 2 (by rfl) ⟨745818, by rfl⟩ : syracuseStep 1988849 = 1491637) B1491637
theorem B1988867 : Blo 1325481 1988867 := bstep (se 1 (by rfl) ⟨1491650, by rfl⟩ : syracuseStep 1988867 = 2983301) B2983301
theorem B4479245 : Blo 1325481 4479245 := bstep (se 3 (by rfl) ⟨839858, by rfl⟩ : syracuseStep 4479245 = 1679717) B1679717
theorem B1988897 : Blo 1325481 1988897 := bstep (se 2 (by rfl) ⟨745836, by rfl⟩ : syracuseStep 1988897 = 1491673) B1491673
theorem B1988915 : Blo 1325481 1988915 := bstep (se 1 (by rfl) ⟨1491686, by rfl⟩ : syracuseStep 1988915 = 2983373) B2983373
theorem B4479299 : Blo 1325481 4479299 := bstep (se 1 (by rfl) ⟨3359474, by rfl⟩ : syracuseStep 4479299 = 6718949) B6718949
theorem B1988945 : Blo 1325481 1988945 := bstep (se 2 (by rfl) ⟨745854, by rfl⟩ : syracuseStep 1988945 = 1491709) B1491709
theorem B1677667 : Blo 1325481 1677667 := bstep (se 1 (by rfl) ⟨1258250, by rfl⟩ : syracuseStep 1677667 = 2516501) B2516501
theorem B1988963 : Blo 1325481 1988963 := bstep (se 1 (by rfl) ⟨1491722, by rfl⟩ : syracuseStep 1988963 = 2983445) B2983445
theorem B5667185 : Blo 1325481 5667185 := bstep (se 2 (by rfl) ⟨2125194, by rfl⟩ : syracuseStep 5667185 = 4250389) B4250389
theorem B1988993 : Blo 1325481 1988993 := bstep (se 2 (by rfl) ⟨745872, by rfl⟩ : syracuseStep 1988993 = 1491745) B1491745
theorem B1989011 : Blo 1325481 1989011 := bstep (se 1 (by rfl) ⟨1491758, by rfl⟩ : syracuseStep 1989011 = 2983517) B2983517
theorem B1989041 : Blo 1325481 1989041 := bstep (se 2 (by rfl) ⟨745890, by rfl⟩ : syracuseStep 1989041 = 1491781) B1491781
theorem B1325491 : Blo 1325481 1325491 := bstep (se 1 (by rfl) ⟨994118, by rfl⟩ : syracuseStep 1325491 = 1988237) B1988237
theorem B1325507 : Blo 1325481 1325507 := bstep (se 1 (by rfl) ⟨994130, by rfl⟩ : syracuseStep 1325507 = 1988261) B1988261
theorem B1677763 : Blo 1325481 1677763 := bstep (se 1 (by rfl) ⟨1258322, by rfl⟩ : syracuseStep 1677763 = 2516645) B2516645
theorem B1989059 : Blo 1325481 1989059 := bstep (se 1 (by rfl) ⟨1491794, by rfl⟩ : syracuseStep 1989059 = 2983589) B2983589
theorem B1325523 : Blo 1325481 1325523 := bstep (se 1 (by rfl) ⟨994142, by rfl⟩ : syracuseStep 1325523 = 1988285) B1988285
theorem B1989089 : Blo 1325481 1989089 := bstep (se 2 (by rfl) ⟨745908, by rfl⟩ : syracuseStep 1989089 = 1491817) B1491817
theorem B1325539 : Blo 1325481 1325539 := bstep (se 1 (by rfl) ⟨994154, by rfl⟩ : syracuseStep 1325539 = 1988309) B1988309
theorem B1325555 : Blo 1325481 1325555 := bstep (se 1 (by rfl) ⟨994166, by rfl⟩ : syracuseStep 1325555 = 1988333) B1988333
theorem B1989107 : Blo 1325481 1989107 := bstep (se 1 (by rfl) ⟨1491830, by rfl⟩ : syracuseStep 1989107 = 2983661) B2983661
theorem B1325571 : Blo 1325481 1325571 := bstep (se 1 (by rfl) ⟨994178, by rfl⟩ : syracuseStep 1325571 = 1988357) B1988357
theorem B1989137 : Blo 1325481 1989137 := bstep (se 2 (by rfl) ⟨745926, by rfl⟩ : syracuseStep 1989137 = 1491853) B1491853
theorem B1325587 : Blo 1325481 1325587 := bstep (se 1 (by rfl) ⟨994190, by rfl⟩ : syracuseStep 1325587 = 1988381) B1988381
theorem B1325603 : Blo 1325481 1325603 := bstep (se 1 (by rfl) ⟨994202, by rfl⟩ : syracuseStep 1325603 = 1988405) B1988405
theorem B1989155 : Blo 1325481 1989155 := bstep (se 1 (by rfl) ⟨1491866, by rfl⟩ : syracuseStep 1989155 = 2983733) B2983733
theorem B3775025 : Blo 1325481 3775025 := bstep (se 2 (by rfl) ⟨1415634, by rfl⟩ : syracuseStep 3775025 = 2831269) B2831269
theorem B1325619 : Blo 1325481 1325619 := bstep (se 1 (by rfl) ⟨994214, by rfl⟩ : syracuseStep 1325619 = 1988429) B1988429
theorem B1989185 : Blo 1325481 1989185 := bstep (se 2 (by rfl) ⟨745944, by rfl⟩ : syracuseStep 1989185 = 1491889) B1491889
theorem B1325635 : Blo 1325481 1325635 := bstep (se 1 (by rfl) ⟨994226, by rfl⟩ : syracuseStep 1325635 = 1988453) B1988453
theorem B4479569 : Blo 1325481 4479569 := bstep (se 2 (by rfl) ⟨1679838, by rfl⟩ : syracuseStep 4479569 = 3359677) B3359677
theorem B1325651 : Blo 1325481 1325651 := bstep (se 1 (by rfl) ⟨994238, by rfl⟩ : syracuseStep 1325651 = 1988477) B1988477
theorem B1989203 : Blo 1325481 1989203 := bstep (se 1 (by rfl) ⟨1491902, by rfl⟩ : syracuseStep 1989203 = 2983805) B2983805
theorem B1325667 : Blo 1325481 1325667 := bstep (se 1 (by rfl) ⟨994250, by rfl⟩ : syracuseStep 1325667 = 1988501) B1988501
theorem B13802083 : Blo 1325481 13802083 := bstep (se 1 (by rfl) ⟨10351562, by rfl⟩ : syracuseStep 13802083 = 20703125) B20703125
theorem B11328113 : Blo 1325481 11328113 := bstep (se 2 (by rfl) ⟨4248042, by rfl⟩ : syracuseStep 11328113 = 8496085) B8496085
theorem B1325683 : Blo 1325481 1325683 := bstep (se 1 (by rfl) ⟨994262, by rfl⟩ : syracuseStep 1325683 = 1988525) B1988525
theorem B1989233 : Blo 1325481 1989233 := bstep (se 2 (by rfl) ⟨745962, by rfl⟩ : syracuseStep 1989233 = 1491925) B1491925
theorem B1325699 : Blo 1325481 1325699 := bstep (se 1 (by rfl) ⟨994274, by rfl⟩ : syracuseStep 1325699 = 1988549) B1988549
theorem B1989251 : Blo 1325481 1989251 := bstep (se 1 (by rfl) ⟨1491938, by rfl⟩ : syracuseStep 1989251 = 2983877) B2983877
theorem B1325715 : Blo 1325481 1325715 := bstep (se 1 (by rfl) ⟨994286, by rfl⟩ : syracuseStep 1325715 = 1988573) B1988573
theorem B1989281 : Blo 1325481 1989281 := bstep (se 2 (by rfl) ⟨745980, by rfl⟩ : syracuseStep 1989281 = 1491961) B1491961
theorem B1325731 : Blo 1325481 1325731 := bstep (se 1 (by rfl) ⟨994298, by rfl⟩ : syracuseStep 1325731 = 1988597) B1988597
theorem B1325747 : Blo 1325481 1325747 := bstep (se 1 (by rfl) ⟨994310, by rfl⟩ : syracuseStep 1325747 = 1988621) B1988621
theorem B1989299 : Blo 1325481 1989299 := bstep (se 1 (by rfl) ⟨1491974, by rfl⟩ : syracuseStep 1989299 = 2983949) B2983949
theorem B1325763 : Blo 1325481 1325763 := bstep (se 1 (by rfl) ⟨994322, by rfl⟩ : syracuseStep 1325763 = 1988645) B1988645
theorem B29055685 : Blo 1325481 29055685 := bstep (se 4 (by rfl) ⟨2723970, by rfl⟩ : syracuseStep 29055685 = 5447941) B5447941
theorem B1989329 : Blo 1325481 1989329 := bstep (se 2 (by rfl) ⟨745998, by rfl⟩ : syracuseStep 1989329 = 1491997) B1491997
theorem B1325779 : Blo 1325481 1325779 := bstep (se 1 (by rfl) ⟨994334, by rfl⟩ : syracuseStep 1325779 = 1988669) B1988669
theorem B1325795 : Blo 1325481 1325795 := bstep (se 1 (by rfl) ⟨994346, by rfl⟩ : syracuseStep 1325795 = 1988693) B1988693
theorem B1989347 : Blo 1325481 1989347 := bstep (se 1 (by rfl) ⟨1492010, by rfl⟩ : syracuseStep 1989347 = 2984021) B2984021
theorem B3586787 : Blo 1325481 3586787 := bstep (se 1 (by rfl) ⟨2690090, by rfl⟩ : syracuseStep 3586787 = 5380181) B5380181
theorem B1325811 : Blo 1325481 1325811 := bstep (se 1 (by rfl) ⟨994358, by rfl⟩ : syracuseStep 1325811 = 1988717) B1988717
theorem B1989377 : Blo 1325481 1989377 := bstep (se 2 (by rfl) ⟨746016, by rfl⟩ : syracuseStep 1989377 = 1492033) B1492033
theorem B1325827 : Blo 1325481 1325827 := bstep (se 1 (by rfl) ⟨994370, by rfl⟩ : syracuseStep 1325827 = 1988741) B1988741
theorem B5036813 : Blo 1325481 5036813 := bstep (se 3 (by rfl) ⟨944402, by rfl⟩ : syracuseStep 5036813 = 1888805) B1888805
theorem B1325843 : Blo 1325481 1325843 := bstep (se 1 (by rfl) ⟨994382, by rfl⟩ : syracuseStep 1325843 = 1988765) B1988765
theorem B1989395 : Blo 1325481 1989395 := bstep (se 1 (by rfl) ⟨1492046, by rfl⟩ : syracuseStep 1989395 = 2984093) B2984093
theorem B1325859 : Blo 1325481 1325859 := bstep (se 1 (by rfl) ⟨994394, by rfl⟩ : syracuseStep 1325859 = 1988789) B1988789
theorem B6716195 : Blo 1325481 6716195 := bstep (se 1 (by rfl) ⟨5037146, by rfl⟩ : syracuseStep 6716195 = 10074293) B10074293
theorem B1989425 : Blo 1325481 1989425 := bstep (se 2 (by rfl) ⟨746034, by rfl⟩ : syracuseStep 1989425 = 1492069) B1492069
theorem B5454641 : Blo 1325481 5454641 := bstep (se 2 (by rfl) ⟨2045490, by rfl⟩ : syracuseStep 5454641 = 4090981) B4090981
theorem B1325875 : Blo 1325481 1325875 := bstep (se 1 (by rfl) ⟨994406, by rfl⟩ : syracuseStep 1325875 = 1988813) B1988813
theorem B1325891 : Blo 1325481 1325891 := bstep (se 1 (by rfl) ⟨994418, by rfl⟩ : syracuseStep 1325891 = 1988837) B1988837
theorem B1989443 : Blo 1325481 1989443 := bstep (se 1 (by rfl) ⟨1492082, by rfl⟩ : syracuseStep 1989443 = 2984165) B2984165
theorem B1792835 : Blo 1325481 1792835 := bstep (se 1 (by rfl) ⟨1344626, by rfl⟩ : syracuseStep 1792835 = 2689253) B2689253
theorem B3357521 : Blo 1325481 3357521 := bstep (se 2 (by rfl) ⟨1259070, by rfl⟩ : syracuseStep 3357521 = 2518141) B2518141
theorem B1325907 : Blo 1325481 1325907 := bstep (se 1 (by rfl) ⟨994430, by rfl⟩ : syracuseStep 1325907 = 1988861) B1988861
theorem B1989473 : Blo 1325481 1989473 := bstep (se 2 (by rfl) ⟨746052, by rfl⟩ : syracuseStep 1989473 = 1492105) B1492105
theorem B1325923 : Blo 1325481 1325923 := bstep (se 1 (by rfl) ⟨994442, by rfl⟩ : syracuseStep 1325923 = 1988885) B1988885
theorem B1325939 : Blo 1325481 1325939 := bstep (se 1 (by rfl) ⟨994454, by rfl⟩ : syracuseStep 1325939 = 1988909) B1988909
theorem B1989491 : Blo 1325481 1989491 := bstep (se 1 (by rfl) ⟨1492118, by rfl⟩ : syracuseStep 1989491 = 2984237) B2984237
theorem B1325955 : Blo 1325481 1325955 := bstep (se 1 (by rfl) ⟨994466, by rfl⟩ : syracuseStep 1325955 = 1988933) B1988933
theorem B3357571 : Blo 1325481 3357571 := bstep (se 1 (by rfl) ⟨2518178, by rfl⟩ : syracuseStep 3357571 = 5036357) B5036357
theorem B1989521 : Blo 1325481 1989521 := bstep (se 2 (by rfl) ⟨746070, by rfl⟩ : syracuseStep 1989521 = 1492141) B1492141
theorem B1325971 : Blo 1325481 1325971 := bstep (se 1 (by rfl) ⟨994478, by rfl⟩ : syracuseStep 1325971 = 1988957) B1988957
theorem B1325987 : Blo 1325481 1325987 := bstep (se 1 (by rfl) ⟨994490, by rfl⟩ : syracuseStep 1325987 = 1988981) B1988981
theorem B1989539 : Blo 1325481 1989539 := bstep (se 1 (by rfl) ⟨1492154, by rfl⟩ : syracuseStep 1989539 = 2984309) B2984309
theorem B1326003 : Blo 1325481 1326003 := bstep (se 1 (by rfl) ⟨994502, by rfl⟩ : syracuseStep 1326003 = 1989005) B1989005
theorem B1678259 : Blo 1325481 1678259 := bstep (se 1 (by rfl) ⟨1258694, by rfl⟩ : syracuseStep 1678259 = 2517389) B2517389
theorem B1989569 : Blo 1325481 1989569 := bstep (se 2 (by rfl) ⟨746088, by rfl⟩ : syracuseStep 1989569 = 1492177) B1492177
theorem B1326019 : Blo 1325481 1326019 := bstep (se 1 (by rfl) ⟨994514, by rfl⟩ : syracuseStep 1326019 = 1989029) B1989029
theorem B1326035 : Blo 1325481 1326035 := bstep (se 1 (by rfl) ⟨994526, by rfl⟩ : syracuseStep 1326035 = 1989053) B1989053
theorem B1989587 : Blo 1325481 1989587 := bstep (se 1 (by rfl) ⟨1492190, by rfl⟩ : syracuseStep 1989587 = 2984381) B2984381
theorem B1326051 : Blo 1325481 1326051 := bstep (se 1 (by rfl) ⟨994538, by rfl⟩ : syracuseStep 1326051 = 1989077) B1989077
theorem B1989617 : Blo 1325481 1989617 := bstep (se 2 (by rfl) ⟨746106, by rfl⟩ : syracuseStep 1989617 = 1492213) B1492213
theorem B1326067 : Blo 1325481 1326067 := bstep (se 1 (by rfl) ⟨994550, by rfl⟩ : syracuseStep 1326067 = 1989101) B1989101
theorem B1326083 : Blo 1325481 1326083 := bstep (se 1 (by rfl) ⟨994562, by rfl⟩ : syracuseStep 1326083 = 1989125) B1989125
theorem B1989635 : Blo 1325481 1989635 := bstep (se 1 (by rfl) ⟨1492226, by rfl⟩ : syracuseStep 1989635 = 2984453) B2984453
theorem B1326099 : Blo 1325481 1326099 := bstep (se 1 (by rfl) ⟨994574, by rfl⟩ : syracuseStep 1326099 = 1989149) B1989149
theorem B3357713 : Blo 1325481 3357713 := bstep (se 2 (by rfl) ⟨1259142, by rfl⟩ : syracuseStep 3357713 = 2518285) B2518285
theorem B1989665 : Blo 1325481 1989665 := bstep (se 2 (by rfl) ⟨746124, by rfl⟩ : syracuseStep 1989665 = 1492249) B1492249
theorem B1326115 : Blo 1325481 1326115 := bstep (se 1 (by rfl) ⟨994586, by rfl⟩ : syracuseStep 1326115 = 1989173) B1989173
theorem B1326131 : Blo 1325481 1326131 := bstep (se 1 (by rfl) ⟨994598, by rfl⟩ : syracuseStep 1326131 = 1989197) B1989197
theorem B1989683 : Blo 1325481 1989683 := bstep (se 1 (by rfl) ⟨1492262, by rfl⟩ : syracuseStep 1989683 = 2984525) B2984525
theorem B1866817 : Blo 1325481 1866817 := bstep (se 2 (by rfl) ⟨700056, by rfl⟩ : syracuseStep 1866817 = 1400113) B1400113
theorem B1326147 : Blo 1325481 1326147 := bstep (se 1 (by rfl) ⟨994610, by rfl⟩ : syracuseStep 1326147 = 1989221) B1989221
theorem B1989713 : Blo 1325481 1989713 := bstep (se 2 (by rfl) ⟨746142, by rfl⟩ : syracuseStep 1989713 = 1492285) B1492285
theorem B1326163 : Blo 1325481 1326163 := bstep (se 1 (by rfl) ⟨994622, by rfl⟩ : syracuseStep 1326163 = 1989245) B1989245
theorem B1326179 : Blo 1325481 1326179 := bstep (se 1 (by rfl) ⟨994634, by rfl⟩ : syracuseStep 1326179 = 1989269) B1989269
theorem B1989731 : Blo 1325481 1989731 := bstep (se 1 (by rfl) ⟨1492298, by rfl⟩ : syracuseStep 1989731 = 2984597) B2984597
theorem B5454947 : Blo 1325481 5454947 := bstep (se 1 (by rfl) ⟨4091210, by rfl⟩ : syracuseStep 5454947 = 8182421) B8182421
theorem B4480109 : Blo 1325481 4480109 := bstep (se 3 (by rfl) ⟨840020, by rfl⟩ : syracuseStep 4480109 = 1680041) B1680041
theorem B1326195 : Blo 1325481 1326195 := bstep (se 1 (by rfl) ⟨994646, by rfl⟩ : syracuseStep 1326195 = 1989293) B1989293
theorem B1989761 : Blo 1325481 1989761 := bstep (se 2 (by rfl) ⟨746160, by rfl⟩ : syracuseStep 1989761 = 1492321) B1492321
theorem B1326211 : Blo 1325481 1326211 := bstep (se 1 (by rfl) ⟨994658, by rfl⟩ : syracuseStep 1326211 = 1989317) B1989317
theorem B1326227 : Blo 1325481 1326227 := bstep (se 1 (by rfl) ⟨994670, by rfl⟩ : syracuseStep 1326227 = 1989341) B1989341
theorem B1989779 : Blo 1325481 1989779 := bstep (se 1 (by rfl) ⟨1492334, by rfl⟩ : syracuseStep 1989779 = 2984669) B2984669
theorem B1326243 : Blo 1325481 1326243 := bstep (se 1 (by rfl) ⟨994682, by rfl⟩ : syracuseStep 1326243 = 1989365) B1989365
theorem B4480163 : Blo 1325481 4480163 := bstep (se 1 (by rfl) ⟨3360122, by rfl⟩ : syracuseStep 4480163 = 6720245) B6720245
theorem B1989809 : Blo 1325481 1989809 := bstep (se 2 (by rfl) ⟨746178, by rfl⟩ : syracuseStep 1989809 = 1492357) B1492357
theorem B1326259 : Blo 1325481 1326259 := bstep (se 1 (by rfl) ⟨994694, by rfl⟩ : syracuseStep 1326259 = 1989389) B1989389
theorem B1326275 : Blo 1325481 1326275 := bstep (se 1 (by rfl) ⟨994706, by rfl⟩ : syracuseStep 1326275 = 1989413) B1989413
theorem B1989827 : Blo 1325481 1989827 := bstep (se 1 (by rfl) ⟨1492370, by rfl⟩ : syracuseStep 1989827 = 2984741) B2984741
theorem B3775697 : Blo 1325481 3775697 := bstep (se 2 (by rfl) ⟨1415886, by rfl⟩ : syracuseStep 3775697 = 2831773) B2831773
theorem B1326291 : Blo 1325481 1326291 := bstep (se 1 (by rfl) ⟨994718, by rfl⟩ : syracuseStep 1326291 = 1989437) B1989437
theorem B1989857 : Blo 1325481 1989857 := bstep (se 2 (by rfl) ⟨746196, by rfl⟩ : syracuseStep 1989857 = 1492393) B1492393
theorem B1326307 : Blo 1325481 1326307 := bstep (se 1 (by rfl) ⟨994730, by rfl⟩ : syracuseStep 1326307 = 1989461) B1989461
theorem B1326323 : Blo 1325481 1326323 := bstep (se 1 (by rfl) ⟨994742, by rfl⟩ : syracuseStep 1326323 = 1989485) B1989485
theorem B1989875 : Blo 1325481 1989875 := bstep (se 1 (by rfl) ⟨1492406, by rfl⟩ : syracuseStep 1989875 = 2984813) B2984813
theorem B1326339 : Blo 1325481 1326339 := bstep (se 1 (by rfl) ⟨994754, by rfl⟩ : syracuseStep 1326339 = 1989509) B1989509
theorem B9559309 : Blo 1325481 9559309 := bstep (se 3 (by rfl) ⟨1792370, by rfl⟩ : syracuseStep 9559309 = 3584741) B3584741
theorem B1989905 : Blo 1325481 1989905 := bstep (se 2 (by rfl) ⟨746214, by rfl⟩ : syracuseStep 1989905 = 1492429) B1492429
theorem B1326355 : Blo 1325481 1326355 := bstep (se 1 (by rfl) ⟨994766, by rfl⟩ : syracuseStep 1326355 = 1989533) B1989533
theorem B1326371 : Blo 1325481 1326371 := bstep (se 1 (by rfl) ⟨994778, by rfl⟩ : syracuseStep 1326371 = 1989557) B1989557
theorem B1989923 : Blo 1325481 1989923 := bstep (se 1 (by rfl) ⟨1492442, by rfl⟩ : syracuseStep 1989923 = 2984885) B2984885
theorem B1326387 : Blo 1325481 1326387 := bstep (se 1 (by rfl) ⟨994790, by rfl⟩ : syracuseStep 1326387 = 1989581) B1989581
theorem B1989953 : Blo 1325481 1989953 := bstep (se 2 (by rfl) ⟨746232, by rfl⟩ : syracuseStep 1989953 = 1492465) B1492465
theorem B1326403 : Blo 1325481 1326403 := bstep (se 1 (by rfl) ⟨994802, by rfl⟩ : syracuseStep 1326403 = 1989605) B1989605
theorem B9567557 : Blo 1325481 9567557 := bstep (se 4 (by rfl) ⟨896958, by rfl⟩ : syracuseStep 9567557 = 1793917) B1793917
theorem B1326419 : Blo 1325481 1326419 := bstep (se 1 (by rfl) ⟨994814, by rfl⟩ : syracuseStep 1326419 = 1989629) B1989629
theorem B1989971 : Blo 1325481 1989971 := bstep (se 1 (by rfl) ⟨1492478, by rfl⟩ : syracuseStep 1989971 = 2984957) B2984957
theorem B1326435 : Blo 1325481 1326435 := bstep (se 1 (by rfl) ⟨994826, by rfl⟩ : syracuseStep 1326435 = 1989653) B1989653
theorem B1990001 : Blo 1325481 1990001 := bstep (se 2 (by rfl) ⟨746250, by rfl⟩ : syracuseStep 1990001 = 1492501) B1492501
theorem B1326451 : Blo 1325481 1326451 := bstep (se 1 (by rfl) ⟨994838, by rfl⟩ : syracuseStep 1326451 = 1989677) B1989677
theorem B1326467 : Blo 1325481 1326467 := bstep (se 1 (by rfl) ⟨994850, by rfl⟩ : syracuseStep 1326467 = 1989701) B1989701
theorem B1990019 : Blo 1325481 1990019 := bstep (se 1 (by rfl) ⟨1492514, by rfl⟩ : syracuseStep 1990019 = 2985029) B2985029
theorem B1326483 : Blo 1325481 1326483 := bstep (se 1 (by rfl) ⟨994862, by rfl⟩ : syracuseStep 1326483 = 1989725) B1989725
theorem B1990049 : Blo 1325481 1990049 := bstep (se 2 (by rfl) ⟨746268, by rfl⟩ : syracuseStep 1990049 = 1492537) B1492537
theorem B1793441 : Blo 1325481 1793441 := bstep (se 2 (by rfl) ⟨672540, by rfl⟩ : syracuseStep 1793441 = 1345081) B1345081
theorem B1326499 : Blo 1325481 1326499 := bstep (se 1 (by rfl) ⟨994874, by rfl⟩ : syracuseStep 1326499 = 1989749) B1989749
theorem B1326515 : Blo 1325481 1326515 := bstep (se 1 (by rfl) ⟨994886, by rfl⟩ : syracuseStep 1326515 = 1989773) B1989773
theorem B1990067 : Blo 1325481 1990067 := bstep (se 1 (by rfl) ⟨1492550, by rfl⟩ : syracuseStep 1990067 = 2985101) B2985101
theorem B1326531 : Blo 1325481 1326531 := bstep (se 1 (by rfl) ⟨994898, by rfl⟩ : syracuseStep 1326531 = 1989797) B1989797
theorem B1990097 : Blo 1325481 1990097 := bstep (se 2 (by rfl) ⟨746286, by rfl⟩ : syracuseStep 1990097 = 1492573) B1492573
theorem B1326547 : Blo 1325481 1326547 := bstep (se 1 (by rfl) ⟨994910, by rfl⟩ : syracuseStep 1326547 = 1989821) B1989821
theorem B1326563 : Blo 1325481 1326563 := bstep (se 1 (by rfl) ⟨994922, by rfl⟩ : syracuseStep 1326563 = 1989845) B1989845
theorem B1990115 : Blo 1325481 1990115 := bstep (se 1 (by rfl) ⟨1492586, by rfl⟩ : syracuseStep 1990115 = 2985173) B2985173
theorem B1326579 : Blo 1325481 1326579 := bstep (se 1 (by rfl) ⟨994934, by rfl⟩ : syracuseStep 1326579 = 1989869) B1989869
theorem B1990145 : Blo 1325481 1990145 := bstep (se 2 (by rfl) ⟨746304, by rfl⟩ : syracuseStep 1990145 = 1492609) B1492609
theorem B3186179 : Blo 1325481 3186179 := bstep (se 1 (by rfl) ⟨2389634, by rfl⟩ : syracuseStep 3186179 = 4779269) B4779269
theorem B1326595 : Blo 1325481 1326595 := bstep (se 1 (by rfl) ⟨994946, by rfl⟩ : syracuseStep 1326595 = 1989893) B1989893
theorem B16989709 : Blo 1325481 16989709 := bstep (se 3 (by rfl) ⟨3185570, by rfl⟩ : syracuseStep 16989709 = 6371141) B6371141
theorem B1326611 : Blo 1325481 1326611 := bstep (se 1 (by rfl) ⟨994958, by rfl⟩ : syracuseStep 1326611 = 1989917) B1989917
theorem B1990163 : Blo 1325481 1990163 := bstep (se 1 (by rfl) ⟨1492622, by rfl⟩ : syracuseStep 1990163 = 2985245) B2985245
theorem B1326627 : Blo 1325481 1326627 := bstep (se 1 (by rfl) ⟨994970, by rfl⟩ : syracuseStep 1326627 = 1989941) B1989941
theorem B1990193 : Blo 1325481 1990193 := bstep (se 2 (by rfl) ⟨746322, by rfl⟩ : syracuseStep 1990193 = 1492645) B1492645
theorem B1326643 : Blo 1325481 1326643 := bstep (se 1 (by rfl) ⟨994982, by rfl⟩ : syracuseStep 1326643 = 1989965) B1989965
theorem B2391601 : Blo 1325481 2391601 := bstep (se 2 (by rfl) ⟨896850, by rfl⟩ : syracuseStep 2391601 = 1793701) B1793701
theorem B1326659 : Blo 1325481 1326659 := bstep (se 1 (by rfl) ⟨994994, by rfl⟩ : syracuseStep 1326659 = 1989989) B1989989
theorem B1990211 : Blo 1325481 1990211 := bstep (se 1 (by rfl) ⟨1492658, by rfl⟩ : syracuseStep 1990211 = 2985317) B2985317
theorem B6717005 : Blo 1325481 6717005 := bstep (se 3 (by rfl) ⟨1259438, by rfl⟩ : syracuseStep 6717005 = 2518877) B2518877
theorem B1326675 : Blo 1325481 1326675 := bstep (se 1 (by rfl) ⟨995006, by rfl⟩ : syracuseStep 1326675 = 1990013) B1990013
theorem B1990241 : Blo 1325481 1990241 := bstep (se 2 (by rfl) ⟨746340, by rfl⟩ : syracuseStep 1990241 = 1492681) B1492681
theorem B1326691 : Blo 1325481 1326691 := bstep (se 1 (by rfl) ⟨995018, by rfl⟩ : syracuseStep 1326691 = 1990037) B1990037
theorem B1678963 : Blo 1325481 1678963 := bstep (se 1 (by rfl) ⟨1259222, by rfl⟩ : syracuseStep 1678963 = 2518445) B2518445
theorem B1326707 : Blo 1325481 1326707 := bstep (se 1 (by rfl) ⟨995030, by rfl⟩ : syracuseStep 1326707 = 1990061) B1990061
theorem B1990259 : Blo 1325481 1990259 := bstep (se 1 (by rfl) ⟨1492694, by rfl⟩ : syracuseStep 1990259 = 2985389) B2985389
theorem B1326723 : Blo 1325481 1326723 := bstep (se 1 (by rfl) ⟨995042, by rfl⟩ : syracuseStep 1326723 = 1990085) B1990085
theorem B1990289 : Blo 1325481 1990289 := bstep (se 2 (by rfl) ⟨746358, by rfl⟩ : syracuseStep 1990289 = 1492717) B1492717
theorem B1326739 : Blo 1325481 1326739 := bstep (se 1 (by rfl) ⟨995054, by rfl⟩ : syracuseStep 1326739 = 1990109) B1990109
theorem B1326755 : Blo 1325481 1326755 := bstep (se 1 (by rfl) ⟨995066, by rfl⟩ : syracuseStep 1326755 = 1990133) B1990133
theorem B1990307 : Blo 1325481 1990307 := bstep (se 1 (by rfl) ⟨1492730, by rfl⟩ : syracuseStep 1990307 = 2985461) B2985461
theorem B1326771 : Blo 1325481 1326771 := bstep (se 1 (by rfl) ⟨995078, by rfl⟩ : syracuseStep 1326771 = 1990157) B1990157
theorem B1990337 : Blo 1325481 1990337 := bstep (se 2 (by rfl) ⟨746376, by rfl⟩ : syracuseStep 1990337 = 1492753) B1492753
theorem B1326787 : Blo 1325481 1326787 := bstep (se 1 (by rfl) ⟨995090, by rfl⟩ : syracuseStep 1326787 = 1990181) B1990181
theorem B1416899 : Blo 1325481 1416899 := bstep (se 1 (by rfl) ⟨1062674, by rfl⟩ : syracuseStep 1416899 = 2125349) B2125349
theorem B1679059 : Blo 1325481 1679059 := bstep (se 1 (by rfl) ⟨1259294, by rfl⟩ : syracuseStep 1679059 = 2518589) B2518589
theorem B1326803 : Blo 1325481 1326803 := bstep (se 1 (by rfl) ⟨995102, by rfl⟩ : syracuseStep 1326803 = 1990205) B1990205
theorem B1990355 : Blo 1325481 1990355 := bstep (se 1 (by rfl) ⟨1492766, by rfl⟩ : syracuseStep 1990355 = 2985533) B2985533
theorem B1326819 : Blo 1325481 1326819 := bstep (se 1 (by rfl) ⟨995114, by rfl⟩ : syracuseStep 1326819 = 1990229) B1990229
theorem B2834147 : Blo 1325481 2834147 := bstep (se 1 (by rfl) ⟨2125610, by rfl⟩ : syracuseStep 2834147 = 4251221) B4251221
theorem B1990385 : Blo 1325481 1990385 := bstep (se 2 (by rfl) ⟨746394, by rfl⟩ : syracuseStep 1990385 = 1492789) B1492789
theorem B1326835 : Blo 1325481 1326835 := bstep (se 1 (by rfl) ⟨995126, by rfl⟩ : syracuseStep 1326835 = 1990253) B1990253
theorem B1326851 : Blo 1325481 1326851 := bstep (se 1 (by rfl) ⟨995138, by rfl⟩ : syracuseStep 1326851 = 1990277) B1990277
theorem B1990403 : Blo 1325481 1990403 := bstep (se 1 (by rfl) ⟨1492802, by rfl⟩ : syracuseStep 1990403 = 2985605) B2985605
theorem B1326867 : Blo 1325481 1326867 := bstep (se 1 (by rfl) ⟨995150, by rfl⟩ : syracuseStep 1326867 = 1990301) B1990301
theorem B1990433 : Blo 1325481 1990433 := bstep (se 2 (by rfl) ⟨746412, by rfl⟩ : syracuseStep 1990433 = 1492825) B1492825
theorem B1326883 : Blo 1325481 1326883 := bstep (se 1 (by rfl) ⟨995162, by rfl⟩ : syracuseStep 1326883 = 1990325) B1990325
theorem B1326899 : Blo 1325481 1326899 := bstep (se 1 (by rfl) ⟨995174, by rfl⟩ : syracuseStep 1326899 = 1990349) B1990349
theorem B1990451 : Blo 1325481 1990451 := bstep (se 1 (by rfl) ⟨1492838, by rfl⟩ : syracuseStep 1990451 = 2985677) B2985677
theorem B1326915 : Blo 1325481 1326915 := bstep (se 1 (by rfl) ⟨995186, by rfl⟩ : syracuseStep 1326915 = 1990373) B1990373
theorem B1990481 : Blo 1325481 1990481 := bstep (se 2 (by rfl) ⟨746430, by rfl⟩ : syracuseStep 1990481 = 1492861) B1492861
theorem B1326931 : Blo 1325481 1326931 := bstep (se 1 (by rfl) ⟨995198, by rfl⟩ : syracuseStep 1326931 = 1990397) B1990397
theorem B1326947 : Blo 1325481 1326947 := bstep (se 1 (by rfl) ⟨995210, by rfl⟩ : syracuseStep 1326947 = 1990421) B1990421
theorem B1990499 : Blo 1325481 1990499 := bstep (se 1 (by rfl) ⟨1492874, by rfl⟩ : syracuseStep 1990499 = 2985749) B2985749
theorem B1326963 : Blo 1325481 1326963 := bstep (se 1 (by rfl) ⟨995222, by rfl⟩ : syracuseStep 1326963 = 1990445) B1990445
theorem B1990529 : Blo 1325481 1990529 := bstep (se 2 (by rfl) ⟨746448, by rfl⟩ : syracuseStep 1990529 = 1492897) B1492897
theorem B1326979 : Blo 1325481 1326979 := bstep (se 1 (by rfl) ⟨995234, by rfl⟩ : syracuseStep 1326979 = 1990469) B1990469
theorem B1326995 : Blo 1325481 1326995 := bstep (se 1 (by rfl) ⟨995246, by rfl⟩ : syracuseStep 1326995 = 1990493) B1990493
theorem B1990547 : Blo 1325481 1990547 := bstep (se 1 (by rfl) ⟨1492910, by rfl⟩ : syracuseStep 1990547 = 2985821) B2985821
theorem B1327011 : Blo 1325481 1327011 := bstep (se 1 (by rfl) ⟨995258, by rfl⟩ : syracuseStep 1327011 = 1990517) B1990517
theorem B1990577 : Blo 1325481 1990577 := bstep (se 2 (by rfl) ⟨746466, by rfl⟩ : syracuseStep 1990577 = 1492933) B1492933
theorem B1327027 : Blo 1325481 1327027 := bstep (se 1 (by rfl) ⟨995270, by rfl⟩ : syracuseStep 1327027 = 1990541) B1990541
theorem B1327043 : Blo 1325481 1327043 := bstep (se 1 (by rfl) ⟨995282, by rfl⟩ : syracuseStep 1327043 = 1990565) B1990565
theorem B1990595 : Blo 1325481 1990595 := bstep (se 1 (by rfl) ⟨1492946, by rfl⟩ : syracuseStep 1990595 = 2985893) B2985893
theorem B48381893 : Blo 1325481 48381893 := bstep (se 4 (by rfl) ⟨4535802, by rfl⟩ : syracuseStep 48381893 = 9071605) B9071605
theorem B1327059 : Blo 1325481 1327059 := bstep (se 1 (by rfl) ⟨995294, by rfl⟩ : syracuseStep 1327059 = 1990589) B1990589
theorem B1990625 : Blo 1325481 1990625 := bstep (se 2 (by rfl) ⟨746484, by rfl⟩ : syracuseStep 1990625 = 1492969) B1492969
theorem B3776483 : Blo 1325481 3776483 := bstep (se 1 (by rfl) ⟨2832362, by rfl⟩ : syracuseStep 3776483 = 5664725) B5664725
theorem B1327075 : Blo 1325481 1327075 := bstep (se 1 (by rfl) ⟨995306, by rfl⟩ : syracuseStep 1327075 = 1990613) B1990613
theorem B4251619 : Blo 1325481 4251619 := bstep (se 1 (by rfl) ⟨3188714, by rfl⟩ : syracuseStep 4251619 = 6377429) B6377429
theorem B3358705 : Blo 1325481 3358705 := bstep (se 2 (by rfl) ⟨1259514, by rfl⟩ : syracuseStep 3358705 = 2519029) B2519029
theorem B1327091 : Blo 1325481 1327091 := bstep (se 1 (by rfl) ⟨995318, by rfl⟩ : syracuseStep 1327091 = 1990637) B1990637
theorem B1990643 : Blo 1325481 1990643 := bstep (se 1 (by rfl) ⟨1492982, by rfl⟩ : syracuseStep 1990643 = 2985965) B2985965
theorem B1990667 : Blo 1325481 1990667 := bstep (se 1 (by rfl) ⟨1493000, by rfl⟩ : syracuseStep 1990667 = 2986001) B2986001
theorem B1327115 : Blo 1325481 1327115 := bstep (se 1 (by rfl) ⟨995336, by rfl⟩ : syracuseStep 1327115 = 1990673) B1990673
theorem B16130065 : Blo 1325481 16130065 := bstep (se 2 (by rfl) ⟨6048774, by rfl⟩ : syracuseStep 16130065 = 12097549) B12097549
theorem B1679383 : Blo 1325481 1679383 := bstep (se 1 (by rfl) ⟨1259537, by rfl⟩ : syracuseStep 1679383 = 2519075) B2519075
theorem B1990679 : Blo 1325481 1990679 := bstep (se 1 (by rfl) ⟨1493009, by rfl⟩ : syracuseStep 1990679 = 2986019) B2986019
theorem B1327127 : Blo 1325481 1327127 := bstep (se 1 (by rfl) ⟨995345, by rfl⟩ : syracuseStep 1327127 = 1990691) B1990691
theorem B2834455 : Blo 1325481 2834455 := bstep (se 1 (by rfl) ⟨2125841, by rfl⟩ : syracuseStep 2834455 = 4251683) B4251683
theorem B1327147 : Blo 1325481 1327147 := bstep (se 1 (by rfl) ⟨995360, by rfl⟩ : syracuseStep 1327147 = 1990721) B1990721
theorem B1327159 : Blo 1325481 1327159 := bstep (se 1 (by rfl) ⟨995369, by rfl⟩ : syracuseStep 1327159 = 1990739) B1990739
theorem B4087883 : Blo 1325481 4087883 := bstep (se 1 (by rfl) ⟨3065912, by rfl⟩ : syracuseStep 4087883 = 6131825) B6131825
theorem B2834507 : Blo 1325481 2834507 := bstep (se 1 (by rfl) ⟨2125880, by rfl⟩ : syracuseStep 2834507 = 4251761) B4251761
theorem B1327179 : Blo 1325481 1327179 := bstep (se 1 (by rfl) ⟨995384, by rfl⟩ : syracuseStep 1327179 = 1990769) B1990769
theorem B1327191 : Blo 1325481 1327191 := bstep (se 1 (by rfl) ⟨995393, by rfl⟩ : syracuseStep 1327191 = 1990787) B1990787
theorem B1990745 : Blo 1325481 1990745 := bstep (se 2 (by rfl) ⟨746529, by rfl⟩ : syracuseStep 1990745 = 1493059) B1493059
theorem B1327211 : Blo 1325481 1327211 := bstep (se 1 (by rfl) ⟨995408, by rfl⟩ : syracuseStep 1327211 = 1990817) B1990817
theorem B1327223 : Blo 1325481 1327223 := bstep (se 1 (by rfl) ⟨995417, by rfl⟩ : syracuseStep 1327223 = 1990835) B1990835
theorem B1327243 : Blo 1325481 1327243 := bstep (se 1 (by rfl) ⟨995432, by rfl⟩ : syracuseStep 1327243 = 1990865) B1990865
theorem B1327255 : Blo 1325481 1327255 := bstep (se 1 (by rfl) ⟨995441, by rfl⟩ : syracuseStep 1327255 = 1990883) B1990883
theorem B1327275 : Blo 1325481 1327275 := bstep (se 1 (by rfl) ⟨995456, by rfl⟩ : syracuseStep 1327275 = 1990913) B1990913
theorem B1327287 : Blo 1325481 1327287 := bstep (se 1 (by rfl) ⟨995465, by rfl⟩ : syracuseStep 1327287 = 1990931) B1990931
theorem B1990859 : Blo 1325481 1990859 := bstep (se 1 (by rfl) ⟨1493144, by rfl⟩ : syracuseStep 1990859 = 2986289) B2986289
theorem B1327307 : Blo 1325481 1327307 := bstep (se 1 (by rfl) ⟨995480, by rfl⟩ : syracuseStep 1327307 = 1990961) B1990961
theorem B1990871 : Blo 1325481 1990871 := bstep (se 1 (by rfl) ⟨1493153, by rfl⟩ : syracuseStep 1990871 = 2986307) B2986307
theorem B1327319 : Blo 1325481 1327319 := bstep (se 1 (by rfl) ⟨995489, by rfl⟩ : syracuseStep 1327319 = 1990979) B1990979
theorem B11329753 : Blo 1325481 11329753 := bstep (se 2 (by rfl) ⟨4248657, by rfl⟩ : syracuseStep 11329753 = 8497315) B8497315
theorem B5038301 : Blo 1325481 5038301 := bstep (se 3 (by rfl) ⟨944681, by rfl⟩ : syracuseStep 5038301 = 1889363) B1889363
theorem B1327339 : Blo 1325481 1327339 := bstep (se 1 (by rfl) ⟨995504, by rfl⟩ : syracuseStep 1327339 = 1991009) B1991009
theorem B1327351 : Blo 1325481 1327351 := bstep (se 1 (by rfl) ⟨995513, by rfl⟩ : syracuseStep 1327351 = 1991027) B1991027
theorem B2154763 : Blo 1325481 2154763 := bstep (se 1 (by rfl) ⟨1616072, by rfl⟩ : syracuseStep 2154763 = 3232145) B3232145
theorem B1327371 : Blo 1325481 1327371 := bstep (se 1 (by rfl) ⟨995528, by rfl⟩ : syracuseStep 1327371 = 1991057) B1991057
theorem B1491223 : Blo 1325481 1491223 := bstep (se 1 (by rfl) ⟨1118417, by rfl⟩ : syracuseStep 1491223 = 2236835) B2236835
theorem B1990937 : Blo 1325481 1990937 := bstep (se 2 (by rfl) ⟨746601, by rfl⟩ : syracuseStep 1990937 = 1493203) B1493203
theorem B1327383 : Blo 1325481 1327383 := bstep (se 1 (by rfl) ⟨995537, by rfl⟩ : syracuseStep 1327383 = 1991075) B1991075
theorem B1327403 : Blo 1325481 1327403 := bstep (se 1 (by rfl) ⟨995552, by rfl⟩ : syracuseStep 1327403 = 1991105) B1991105
theorem B1327415 : Blo 1325481 1327415 := bstep (se 1 (by rfl) ⟨995561, by rfl⟩ : syracuseStep 1327415 = 1991123) B1991123
theorem B1327435 : Blo 1325481 1327435 := bstep (se 1 (by rfl) ⟨995576, by rfl⟩ : syracuseStep 1327435 = 1991153) B1991153
theorem B1327447 : Blo 1325481 1327447 := bstep (se 1 (by rfl) ⟨995585, by rfl⟩ : syracuseStep 1327447 = 1991171) B1991171
theorem B1327467 : Blo 1325481 1327467 := bstep (se 1 (by rfl) ⟨995600, by rfl⟩ : syracuseStep 1327467 = 1991201) B1991201
theorem B1327479 : Blo 1325481 1327479 := bstep (se 1 (by rfl) ⟨995609, by rfl⟩ : syracuseStep 1327479 = 1991219) B1991219
theorem B2269579 : Blo 1325481 2269579 := bstep (se 1 (by rfl) ⟨1702184, by rfl⟩ : syracuseStep 2269579 = 3404369) B3404369
theorem B1991051 : Blo 1325481 1991051 := bstep (se 1 (by rfl) ⟨1493288, by rfl⟩ : syracuseStep 1991051 = 2986577) B2986577
theorem B1991063 : Blo 1325481 1991063 := bstep (se 1 (by rfl) ⟨1493297, by rfl⟩ : syracuseStep 1991063 = 2986595) B2986595
theorem B1491403 : Blo 1325481 1491403 := bstep (se 1 (by rfl) ⟨1118552, by rfl⟩ : syracuseStep 1491403 = 2237105) B2237105
theorem B2982347 : Blo 1325481 2982347 := bstep (se 1 (by rfl) ⟨2236760, by rfl⟩ : syracuseStep 2982347 = 4473521) B4473521
theorem B2236889 : Blo 1325481 2236889 := bstep (se 2 (by rfl) ⟨838833, by rfl⟩ : syracuseStep 2236889 = 1677667) B1677667
theorem B1991129 : Blo 1325481 1991129 := bstep (se 2 (by rfl) ⟨746673, by rfl⟩ : syracuseStep 1991129 = 1493347) B1493347
theorem B2982401 : Blo 1325481 2982401 := bstep (se 2 (by rfl) ⟨1118400, by rfl⟩ : syracuseStep 2982401 = 2236801) B2236801
theorem B1491511 : Blo 1325481 1491511 := bstep (se 1 (by rfl) ⟨1118633, by rfl⟩ : syracuseStep 1491511 = 2237267) B2237267
theorem B2269783 : Blo 1325481 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B2237017 : Blo 1325481 2237017 := bstep (se 2 (by rfl) ⟨838881, by rfl⟩ : syracuseStep 2237017 = 1677763) B1677763
theorem B4981421 : Blo 1325481 4981421 := bstep (se 3 (by rfl) ⟨934016, by rfl⟩ : syracuseStep 4981421 = 1868033) B1868033
theorem B9560753 : Blo 1325481 9560753 := bstep (se 2 (by rfl) ⟨3585282, by rfl⟩ : syracuseStep 9560753 = 7170565) B7170565
theorem B2982617 : Blo 1325481 2982617 := bstep (se 2 (by rfl) ⟨1118481, by rfl⟩ : syracuseStep 2982617 = 2236963) B2236963
theorem B1491691 : Blo 1325481 1491691 := bstep (se 1 (by rfl) ⟨1118768, by rfl⟩ : syracuseStep 1491691 = 2237537) B2237537
theorem B11338501 : Blo 1325481 11338501 := bstep (se 4 (by rfl) ⟨1062984, by rfl⟩ : syracuseStep 11338501 = 2125969) B2125969
theorem B4252439 : Blo 1325481 4252439 := bstep (se 1 (by rfl) ⟨3189329, by rfl⟩ : syracuseStep 4252439 = 6378659) B6378659
theorem B2982707 : Blo 1325481 2982707 := bstep (se 1 (by rfl) ⟨2237030, by rfl⟩ : syracuseStep 2982707 = 4474061) B4474061
theorem B2982743 : Blo 1325481 2982743 := bstep (se 1 (by rfl) ⟨2237057, by rfl⟩ : syracuseStep 2982743 = 4474115) B4474115
theorem B1491799 : Blo 1325481 1491799 := bstep (se 1 (by rfl) ⟨1118849, by rfl⟩ : syracuseStep 1491799 = 2237699) B2237699
theorem B6718301 : Blo 1325481 6718301 := bstep (se 3 (by rfl) ⟨1259681, by rfl⟩ : syracuseStep 6718301 = 2519363) B2519363
theorem B5669783 : Blo 1325481 5669783 := bstep (se 1 (by rfl) ⟨4252337, by rfl⟩ : syracuseStep 5669783 = 8504675) B8504675
theorem B38740913 : Blo 1325481 38740913 := bstep (se 2 (by rfl) ⟨14527842, by rfl⟩ : syracuseStep 38740913 = 29055685) B29055685
theorem B6218689 : Blo 1325481 6218689 := bstep (se 2 (by rfl) ⟨2332008, by rfl⟩ : syracuseStep 6218689 = 4664017) B4664017
theorem B4842499 : Blo 1325481 4842499 := bstep (se 1 (by rfl) ⟨3631874, by rfl⟩ : syracuseStep 4842499 = 7263749) B7263749
theorem B2982923 : Blo 1325481 2982923 := bstep (se 1 (by rfl) ⟨2237192, by rfl⟩ : syracuseStep 2982923 = 4474385) B4474385
theorem B1491979 : Blo 1325481 1491979 := bstep (se 1 (by rfl) ⟨1118984, by rfl⟩ : syracuseStep 1491979 = 2237969) B2237969
theorem B3777587 : Blo 1325481 3777587 := bstep (se 1 (by rfl) ⟨2833190, by rfl⟩ : syracuseStep 3777587 = 5666381) B5666381
theorem B2982977 : Blo 1325481 2982977 := bstep (se 2 (by rfl) ⟨1118616, by rfl⟩ : syracuseStep 2982977 = 2237233) B2237233
theorem B3359819 : Blo 1325481 3359819 := bstep (se 1 (by rfl) ⟨2519864, by rfl⟩ : syracuseStep 3359819 = 5039729) B5039729
theorem B5375069 : Blo 1325481 5375069 := bstep (se 3 (by rfl) ⟨1007825, by rfl⟩ : syracuseStep 5375069 = 2015651) B2015651
theorem B1492087 : Blo 1325481 1492087 := bstep (se 1 (by rfl) ⟨1119065, by rfl⟩ : syracuseStep 1492087 = 2238131) B2238131
theorem B4474007 : Blo 1325481 4474007 := bstep (se 1 (by rfl) ⟨3355505, by rfl⟩ : syracuseStep 4474007 = 6711011) B6711011
theorem B2237591 : Blo 1325481 2237591 := bstep (se 1 (by rfl) ⟨1678193, by rfl⟩ : syracuseStep 2237591 = 3356387) B3356387
theorem B11330711 : Blo 1325481 11330711 := bstep (se 1 (by rfl) ⟨8498033, by rfl⟩ : syracuseStep 11330711 = 16996067) B16996067
theorem B2237719 : Blo 1325481 2237719 := bstep (se 1 (by rfl) ⟨1678289, by rfl⟩ : syracuseStep 2237719 = 3356579) B3356579
theorem B3777815 : Blo 1325481 3777815 := bstep (se 1 (by rfl) ⟨2833361, by rfl⟩ : syracuseStep 3777815 = 5666723) B5666723
theorem B2983193 : Blo 1325481 2983193 := bstep (se 2 (by rfl) ⟨1118697, by rfl⟩ : syracuseStep 2983193 = 2237395) B2237395
theorem B1492267 : Blo 1325481 1492267 := bstep (se 1 (by rfl) ⟨1119200, by rfl⟩ : syracuseStep 1492267 = 2238401) B2238401
theorem B5375297 : Blo 1325481 5375297 := bstep (se 2 (by rfl) ⟨2015736, by rfl⟩ : syracuseStep 5375297 = 4031473) B4031473
theorem B2983283 : Blo 1325481 2983283 := bstep (se 1 (by rfl) ⟨2237462, by rfl⟩ : syracuseStep 2983283 = 4474925) B4474925
theorem B2983319 : Blo 1325481 2983319 := bstep (se 1 (by rfl) ⟨2237489, by rfl⟩ : syracuseStep 2983319 = 4474979) B4474979
theorem B1492375 : Blo 1325481 1492375 := bstep (se 1 (by rfl) ⟨1119281, by rfl⟩ : syracuseStep 1492375 = 2238563) B2238563
theorem B2516417 : Blo 1325481 2516417 := bstep (se 2 (by rfl) ⟨943656, by rfl⟩ : syracuseStep 2516417 = 1887313) B1887313
theorem B11331089 : Blo 1325481 11331089 := bstep (se 2 (by rfl) ⟨4249158, by rfl⟩ : syracuseStep 11331089 = 8498317) B8498317
theorem B17008163 : Blo 1325481 17008163 := bstep (se 1 (by rfl) ⟨12756122, by rfl⟩ : syracuseStep 17008163 = 25512245) B25512245
theorem B6710849 : Blo 1325481 6710849 := bstep (se 2 (by rfl) ⟨2516568, by rfl⟩ : syracuseStep 6710849 = 5033137) B5033137
theorem B21497413 : Blo 1325481 21497413 := bstep (se 4 (by rfl) ⟨2015382, by rfl⟩ : syracuseStep 21497413 = 4030765) B4030765
theorem B2983499 : Blo 1325481 2983499 := bstep (se 1 (by rfl) ⟨2237624, by rfl⟩ : syracuseStep 2983499 = 4475249) B4475249
theorem B6374987 : Blo 1325481 6374987 := bstep (se 1 (by rfl) ⟨4781240, by rfl⟩ : syracuseStep 6374987 = 9562481) B9562481
theorem B1492555 : Blo 1325481 1492555 := bstep (se 1 (by rfl) ⟨1119416, by rfl⟩ : syracuseStep 1492555 = 2238833) B2238833
theorem B3778123 : Blo 1325481 3778123 := bstep (se 1 (by rfl) ⟨2833592, by rfl⟩ : syracuseStep 3778123 = 5667185) B5667185
theorem B2983553 : Blo 1325481 2983553 := bstep (se 2 (by rfl) ⟨1118832, by rfl⟩ : syracuseStep 2983553 = 2237665) B2237665
theorem B5375639 : Blo 1325481 5375639 := bstep (se 1 (by rfl) ⟨4031729, by rfl⟩ : syracuseStep 5375639 = 8063459) B8063459
theorem B1345195 : Blo 1325481 1345195 := bstep (se 1 (by rfl) ⟨1008896, by rfl⟩ : syracuseStep 1345195 = 2017793) B2017793
theorem B4474547 : Blo 1325481 4474547 := bstep (se 1 (by rfl) ⟨3355910, by rfl⟩ : syracuseStep 4474547 = 6711821) B6711821
theorem B1492663 : Blo 1325481 1492663 := bstep (se 1 (by rfl) ⟨1119497, by rfl⟩ : syracuseStep 1492663 = 2238995) B2238995
theorem B2516683 : Blo 1325481 2516683 := bstep (se 1 (by rfl) ⟨1887512, by rfl⟩ : syracuseStep 2516683 = 3775025) B3775025
theorem B2983769 : Blo 1325481 2983769 := bstep (se 2 (by rfl) ⟨1118913, by rfl⟩ : syracuseStep 2983769 = 2237827) B2237827
theorem B3778397 : Blo 1325481 3778397 := bstep (se 3 (by rfl) ⟨708449, by rfl⟩ : syracuseStep 3778397 = 1416899) B1416899
theorem B54470501 : Blo 1325481 54470501 := bstep (se 4 (by rfl) ⟨5106609, by rfl⟩ : syracuseStep 54470501 = 10213219) B10213219
theorem B1492843 : Blo 1325481 1492843 := bstep (se 1 (by rfl) ⟨1119632, by rfl⟩ : syracuseStep 1492843 = 2239265) B2239265
theorem B2238347 : Blo 1325481 2238347 := bstep (se 1 (by rfl) ⟨1678760, by rfl⟩ : syracuseStep 2238347 = 3357521) B3357521
theorem B2983859 : Blo 1325481 2983859 := bstep (se 1 (by rfl) ⟨2237894, by rfl⟩ : syracuseStep 2983859 = 4475789) B4475789
theorem B4474817 : Blo 1325481 4474817 := bstep (se 2 (by rfl) ⟨1678056, by rfl⟩ : syracuseStep 4474817 = 3356113) B3356113
theorem B2983895 : Blo 1325481 2983895 := bstep (se 1 (by rfl) ⟨2237921, by rfl⟩ : syracuseStep 2983895 = 4475843) B4475843
theorem B1492951 : Blo 1325481 1492951 := bstep (se 1 (by rfl) ⟨1119713, by rfl⟩ : syracuseStep 1492951 = 2239427) B2239427
theorem B2238475 : Blo 1325481 2238475 := bstep (se 1 (by rfl) ⟨1678856, by rfl⟩ : syracuseStep 2238475 = 3357713) B3357713
theorem B22652945 : Blo 1325481 22652945 := bstep (se 2 (by rfl) ⟨8494854, by rfl⟩ : syracuseStep 22652945 = 16989709) B16989709
theorem B2689075 : Blo 1325481 2689075 := bstep (se 1 (by rfl) ⟨2016806, by rfl⟩ : syracuseStep 2689075 = 4033613) B4033613
theorem B3188801 : Blo 1325481 3188801 := bstep (se 2 (by rfl) ⟨1195800, by rfl⟩ : syracuseStep 3188801 = 2391601) B2391601
theorem B4032605 : Blo 1325481 4032605 := bstep (se 3 (by rfl) ⟨756113, by rfl⟩ : syracuseStep 4032605 = 1512227) B1512227
theorem B2517131 : Blo 1325481 2517131 := bstep (se 1 (by rfl) ⟨1887848, by rfl⟩ : syracuseStep 2517131 = 3775697) B3775697
theorem B2984075 : Blo 1325481 2984075 := bstep (se 1 (by rfl) ⟨2238056, by rfl⟩ : syracuseStep 2984075 = 4476113) B4476113
theorem B1493131 : Blo 1325481 1493131 := bstep (se 1 (by rfl) ⟨1119848, by rfl⟩ : syracuseStep 1493131 = 2239697) B2239697
theorem B2238617 : Blo 1325481 2238617 := bstep (se 2 (by rfl) ⟨839481, by rfl⟩ : syracuseStep 2238617 = 1678963) B1678963
theorem B2984129 : Blo 1325481 2984129 := bstep (se 2 (by rfl) ⟨1119048, by rfl⟩ : syracuseStep 2984129 = 2238097) B2238097
theorem B1493239 : Blo 1325481 1493239 := bstep (se 1 (by rfl) ⟨1119929, by rfl⟩ : syracuseStep 1493239 = 2239859) B2239859
theorem B2238745 : Blo 1325481 2238745 := bstep (se 2 (by rfl) ⟨839529, by rfl⟩ : syracuseStep 2238745 = 1679059) B1679059
theorem B2517313 : Blo 1325481 2517313 := bstep (se 2 (by rfl) ⟨943992, by rfl⟩ : syracuseStep 2517313 = 1887985) B1887985
theorem B6375755 : Blo 1325481 6375755 := bstep (se 1 (by rfl) ⟨4781816, by rfl⟩ : syracuseStep 6375755 = 9563633) B9563633
theorem B2124119 : Blo 1325481 2124119 := bstep (se 1 (by rfl) ⟨1593089, by rfl⟩ : syracuseStep 2124119 = 3186179) B3186179
theorem B2984345 : Blo 1325481 2984345 := bstep (se 2 (by rfl) ⟨1119129, by rfl⟩ : syracuseStep 2984345 = 2238259) B2238259
theorem B7662041 : Blo 1325481 7662041 := bstep (se 2 (by rfl) ⟨2873265, by rfl⟩ : syracuseStep 7662041 = 5746531) B5746531
theorem B4475357 : Blo 1325481 4475357 := bstep (se 3 (by rfl) ⟨839129, by rfl⟩ : syracuseStep 4475357 = 1678259) B1678259
theorem B2984435 : Blo 1325481 2984435 := bstep (se 1 (by rfl) ⟨2238326, by rfl⟩ : syracuseStep 2984435 = 4476653) B4476653
theorem B2984471 : Blo 1325481 2984471 := bstep (se 1 (by rfl) ⟨2238353, by rfl⟩ : syracuseStep 2984471 = 4476707) B4476707
theorem B5376563 : Blo 1325481 5376563 := bstep (se 1 (by rfl) ⟨4032422, by rfl⟩ : syracuseStep 5376563 = 8064845) B8064845
theorem B32254595 : Blo 1325481 32254595 := bstep (se 1 (by rfl) ⟨24190946, by rfl⟩ : syracuseStep 32254595 = 48381893) B48381893
theorem B2517655 : Blo 1325481 2517655 := bstep (se 1 (by rfl) ⟨1888241, by rfl⟩ : syracuseStep 2517655 = 3776483) B3776483
theorem B2984651 : Blo 1325481 2984651 := bstep (se 1 (by rfl) ⟨2238488, by rfl⟩ : syracuseStep 2984651 = 4476977) B4476977
theorem B2869975 : Blo 1325481 2869975 := bstep (se 1 (by rfl) ⟨2152481, by rfl⟩ : syracuseStep 2869975 = 4304963) B4304963
theorem B2984705 : Blo 1325481 2984705 := bstep (se 2 (by rfl) ⟨1119264, by rfl⟩ : syracuseStep 2984705 = 2238529) B2238529
theorem B9554753 : Blo 1325481 9554753 := bstep (se 2 (by rfl) ⟨3583032, by rfl⟩ : syracuseStep 9554753 = 7166065) B7166065
theorem B11209537 : Blo 1325481 11209537 := bstep (se 2 (by rfl) ⟨4203576, by rfl⟩ : syracuseStep 11209537 = 8407153) B8407153
theorem B2239319 : Blo 1325481 2239319 := bstep (se 1 (by rfl) ⟨1679489, by rfl⟩ : syracuseStep 2239319 = 3358979) B3358979
theorem B2517875 : Blo 1325481 2517875 := bstep (se 1 (by rfl) ⟨1888406, by rfl⟩ : syracuseStep 2517875 = 3776813) B3776813
theorem B10079153 : Blo 1325481 10079153 := bstep (se 2 (by rfl) ⟨3779682, by rfl⟩ : syracuseStep 10079153 = 7559365) B7559365
theorem B2239447 : Blo 1325481 2239447 := bstep (se 1 (by rfl) ⟨1679585, by rfl⟩ : syracuseStep 2239447 = 3359171) B3359171
theorem B2984921 : Blo 1325481 2984921 := bstep (se 2 (by rfl) ⟨1119345, by rfl⟩ : syracuseStep 2984921 = 2238691) B2238691
theorem B5032925 : Blo 1325481 5032925 := bstep (se 3 (by rfl) ⟨943673, by rfl⟩ : syracuseStep 5032925 = 1887347) B1887347
theorem B9956357 : Blo 1325481 9956357 := bstep (se 4 (by rfl) ⟨933408, by rfl⟩ : syracuseStep 9956357 = 1866817) B1866817
theorem B2018315 : Blo 1325481 2018315 := bstep (se 1 (by rfl) ⟨1513736, by rfl⟩ : syracuseStep 2018315 = 3027473) B3027473
theorem B2985011 : Blo 1325481 2985011 := bstep (se 1 (by rfl) ⟨2238758, by rfl⟩ : syracuseStep 2985011 = 4477517) B4477517
theorem B2518103 : Blo 1325481 2518103 := bstep (se 1 (by rfl) ⟨1888577, by rfl⟩ : syracuseStep 2518103 = 3777155) B3777155
theorem B2985047 : Blo 1325481 2985047 := bstep (se 1 (by rfl) ⟨2238785, by rfl⟩ : syracuseStep 2985047 = 4477571) B4477571
theorem B8621149 : Blo 1325481 8621149 := bstep (se 3 (by rfl) ⟨1616465, by rfl⟩ : syracuseStep 8621149 = 3232931) B3232931
theorem B2690291 : Blo 1325481 2690291 := bstep (se 1 (by rfl) ⟨2017718, by rfl⟩ : syracuseStep 2690291 = 4035437) B4035437
theorem B2985227 : Blo 1325481 2985227 := bstep (se 1 (by rfl) ⟨2238920, by rfl⟩ : syracuseStep 2985227 = 4477841) B4477841
theorem B2985281 : Blo 1325481 2985281 := bstep (se 2 (by rfl) ⟨1119480, by rfl⟩ : syracuseStep 2985281 = 2238961) B2238961
theorem B2518361 : Blo 1325481 2518361 := bstep (se 2 (by rfl) ⟨944385, by rfl⟩ : syracuseStep 2518361 = 1888771) B1888771
theorem B5377373 : Blo 1325481 5377373 := bstep (se 3 (by rfl) ⟨1008257, by rfl⟩ : syracuseStep 5377373 = 2016515) B2016515
theorem B19123573 : Blo 1325481 19123573 := bstep (se 5 (by rfl) ⟨896417, by rfl⟩ : syracuseStep 19123573 = 1792835) B1792835
theorem B4779395 : Blo 1325481 4779395 := bstep (se 1 (by rfl) ⟨3584546, by rfl⟩ : syracuseStep 4779395 = 7169093) B7169093
theorem B10079639 : Blo 1325481 10079639 := bstep (se 1 (by rfl) ⟨7559729, by rfl⟩ : syracuseStep 10079639 = 15119459) B15119459
theorem B6712793 : Blo 1325481 6712793 := bstep (se 2 (by rfl) ⟨2517297, by rfl⟩ : syracuseStep 6712793 = 5034595) B5034595
theorem B2985497 : Blo 1325481 2985497 := bstep (se 2 (by rfl) ⟨1119561, by rfl⟩ : syracuseStep 2985497 = 2239123) B2239123
theorem B4476491 : Blo 1325481 4476491 := bstep (se 1 (by rfl) ⟨3357368, by rfl⟩ : syracuseStep 4476491 = 6714737) B6714737
theorem B2240075 : Blo 1325481 2240075 := bstep (se 1 (by rfl) ⟨1680056, by rfl⟩ : syracuseStep 2240075 = 3360113) B3360113
theorem B2985587 : Blo 1325481 2985587 := bstep (se 1 (by rfl) ⟨2239190, by rfl⟩ : syracuseStep 2985587 = 4478381) B4478381
theorem B5033623 : Blo 1325481 5033623 := bstep (se 1 (by rfl) ⟨3775217, by rfl⟩ : syracuseStep 5033623 = 7550435) B7550435
theorem B3583639 : Blo 1325481 3583639 := bstep (se 1 (by rfl) ⟨2687729, by rfl⟩ : syracuseStep 3583639 = 5375459) B5375459
theorem B2985623 : Blo 1325481 2985623 := bstep (se 1 (by rfl) ⟨2239217, by rfl⟩ : syracuseStep 2985623 = 4478435) B4478435
theorem B5377715 : Blo 1325481 5377715 := bstep (se 1 (by rfl) ⟨4033286, by rfl⟩ : syracuseStep 5377715 = 8066573) B8066573
theorem B2518771 : Blo 1325481 2518771 := bstep (se 1 (by rfl) ⟨1889078, by rfl⟩ : syracuseStep 2518771 = 3778157) B3778157
theorem B2985803 : Blo 1325481 2985803 := bstep (se 1 (by rfl) ⟨2239352, by rfl⟩ : syracuseStep 2985803 = 4478705) B4478705
theorem B4476761 : Blo 1325481 4476761 := bstep (se 2 (by rfl) ⟨1678785, by rfl⟩ : syracuseStep 4476761 = 3357571) B3357571
theorem B4034393 : Blo 1325481 4034393 := bstep (se 2 (by rfl) ⟨1512897, by rfl⟩ : syracuseStep 4034393 = 3025795) B3025795
theorem B2985857 : Blo 1325481 2985857 := bstep (se 2 (by rfl) ⟨1119696, by rfl⟩ : syracuseStep 2985857 = 2239393) B2239393
theorem B8499161 : Blo 1325481 8499161 := bstep (se 2 (by rfl) ⟨3187185, by rfl⟩ : syracuseStep 8499161 = 6374371) B6374371
theorem B2986073 : Blo 1325481 2986073 := bstep (se 2 (by rfl) ⟨1119777, by rfl⟩ : syracuseStep 2986073 = 2239555) B2239555
theorem B2986163 : Blo 1325481 2986163 := bstep (se 1 (by rfl) ⟨2239622, by rfl⟩ : syracuseStep 2986163 = 4479245) B4479245
theorem B2986199 : Blo 1325481 2986199 := bstep (se 1 (by rfl) ⟨2239649, by rfl⟩ : syracuseStep 2986199 = 4479299) B4479299
theorem B2519257 : Blo 1325481 2519257 := bstep (se 2 (by rfl) ⟨944721, by rfl⟩ : syracuseStep 2519257 = 1889443) B1889443
theorem B2986379 : Blo 1325481 2986379 := bstep (se 1 (by rfl) ⟨2239784, by rfl⟩ : syracuseStep 2986379 = 4479569) B4479569
theorem B4780433 : Blo 1325481 4780433 := bstep (se 2 (by rfl) ⟨1792662, by rfl⟩ : syracuseStep 4780433 = 3585325) B3585325
theorem B5034413 : Blo 1325481 5034413 := bstep (se 3 (by rfl) ⟨943952, by rfl⟩ : syracuseStep 5034413 = 1887905) B1887905
theorem B2986433 : Blo 1325481 2986433 := bstep (se 2 (by rfl) ⟨1119912, by rfl⟩ : syracuseStep 2986433 = 2239825) B2239825
theorem B4477463 : Blo 1325481 4477463 := bstep (se 1 (by rfl) ⟨3358097, by rfl⟩ : syracuseStep 4477463 = 6716195) B6716195
theorem B7557725 : Blo 1325481 7557725 := bstep (se 3 (by rfl) ⟨1417073, by rfl⟩ : syracuseStep 7557725 = 2834147) B2834147
theorem B2986649 : Blo 1325481 2986649 := bstep (se 2 (by rfl) ⟨1119993, by rfl⟩ : syracuseStep 2986649 = 2239987) B2239987
theorem B2986739 : Blo 1325481 2986739 := bstep (se 1 (by rfl) ⟨2240054, by rfl⟩ : syracuseStep 2986739 = 4480109) B4480109
theorem B2519819 : Blo 1325481 2519819 := bstep (se 1 (by rfl) ⟨1889864, by rfl⟩ : syracuseStep 2519819 = 3779729) B3779729
theorem B3355415 : Blo 1325481 3355415 := bstep (se 1 (by rfl) ⟨2516561, by rfl⟩ : syracuseStep 3355415 = 5033123) B5033123
theorem B2986775 : Blo 1325481 2986775 := bstep (se 1 (by rfl) ⟨2240081, by rfl⟩ : syracuseStep 2986775 = 4480163) B4480163
theorem B54424385 : Blo 1325481 54424385 := bstep (se 2 (by rfl) ⟨20409144, by rfl⟩ : syracuseStep 54424385 = 40818289) B40818289
theorem B5378881 : Blo 1325481 5378881 := bstep (se 2 (by rfl) ⟨2017080, by rfl⟩ : syracuseStep 5378881 = 4034161) B4034161
theorem B6378371 : Blo 1325481 6378371 := bstep (se 1 (by rfl) ⟨4783778, by rfl⟩ : syracuseStep 6378371 = 9567557) B9567557
theorem B2520001 : Blo 1325481 2520001 := bstep (se 2 (by rfl) ⟨945000, by rfl⟩ : syracuseStep 2520001 = 1890001) B1890001
theorem B10204177 : Blo 1325481 10204177 := bstep (se 2 (by rfl) ⟨3826566, by rfl⟩ : syracuseStep 10204177 = 7653133) B7653133
theorem B6714413 : Blo 1325481 6714413 := bstep (se 3 (by rfl) ⟨1258952, by rfl⟩ : syracuseStep 6714413 = 2517905) B2517905
theorem B4478003 : Blo 1325481 4478003 := bstep (se 1 (by rfl) ⟨3358502, by rfl⟩ : syracuseStep 4478003 = 6717005) B6717005
theorem B4535489 : Blo 1325481 4535489 := bstep (se 2 (by rfl) ⟨1700808, by rfl⟩ : syracuseStep 4535489 = 3401617) B3401617
theorem B4478273 : Blo 1325481 4478273 := bstep (se 2 (by rfl) ⟨1679352, by rfl⟩ : syracuseStep 4478273 = 3358705) B3358705
theorem B2831755 : Blo 1325481 2831755 := bstep (se 1 (by rfl) ⟨2123816, by rfl⟩ : syracuseStep 2831755 = 4247633) B4247633
theorem B3356225 : Blo 1325481 3356225 := bstep (se 2 (by rfl) ⟨1258584, by rfl⟩ : syracuseStep 3356225 = 2517169) B2517169
theorem B8500801 : Blo 1325481 8500801 := bstep (se 2 (by rfl) ⟨3187800, by rfl⟩ : syracuseStep 8500801 = 6375601) B6375601
theorem B9557635 : Blo 1325481 9557635 := bstep (se 1 (by rfl) ⟨7168226, by rfl⟩ : syracuseStep 9557635 = 14336453) B14336453
theorem B5666449 : Blo 1325481 5666449 := bstep (se 2 (by rfl) ⟨2124918, by rfl⟩ : syracuseStep 5666449 = 4249837) B4249837
theorem B1988249 : Blo 1325481 1988249 := bstep (se 2 (by rfl) ⟨745593, by rfl⟩ : syracuseStep 1988249 = 1491187) B1491187
theorem B21509873 : Blo 1325481 21509873 := bstep (se 2 (by rfl) ⟨8066202, by rfl⟩ : syracuseStep 21509873 = 16132405) B16132405
theorem B1988363 : Blo 1325481 1988363 := bstep (se 1 (by rfl) ⟨1491272, by rfl⟩ : syracuseStep 1988363 = 2982545) B2982545
theorem B1988375 : Blo 1325481 1988375 := bstep (se 1 (by rfl) ⟨1491281, by rfl⟩ : syracuseStep 1988375 = 2982563) B2982563
theorem B5035841 : Blo 1325481 5035841 := bstep (se 2 (by rfl) ⟨1888440, by rfl⟩ : syracuseStep 5035841 = 3776881) B3776881
theorem B1988441 : Blo 1325481 1988441 := bstep (se 2 (by rfl) ⟨745665, by rfl⟩ : syracuseStep 1988441 = 1491331) B1491331
theorem B4478813 : Blo 1325481 4478813 := bstep (se 3 (by rfl) ⟨839777, by rfl⟩ : syracuseStep 4478813 = 1679555) B1679555
theorem B73611109 : Blo 1325481 73611109 := bstep (se 4 (by rfl) ⟨6901041, by rfl⟩ : syracuseStep 73611109 = 13802083) B13802083
theorem B11327363 : Blo 1325481 11327363 := bstep (se 1 (by rfl) ⟨8495522, by rfl⟩ : syracuseStep 11327363 = 16991045) B16991045
theorem B1988555 : Blo 1325481 1988555 := bstep (se 1 (by rfl) ⟨1491416, by rfl⟩ : syracuseStep 1988555 = 2982833) B2982833
theorem B1988567 : Blo 1325481 1988567 := bstep (se 1 (by rfl) ⟨1491425, by rfl⟩ : syracuseStep 1988567 = 2982851) B2982851
theorem B1988633 : Blo 1325481 1988633 := bstep (se 2 (by rfl) ⟨745737, by rfl⟩ : syracuseStep 1988633 = 1491475) B1491475
theorem B3356761 : Blo 1325481 3356761 := bstep (se 2 (by rfl) ⟨1258785, by rfl⟩ : syracuseStep 3356761 = 2517571) B2517571
theorem B2832499 : Blo 1325481 2832499 := bstep (se 1 (by rfl) ⟨2124374, by rfl⟩ : syracuseStep 2832499 = 4248749) B4248749
theorem B1988747 : Blo 1325481 1988747 := bstep (se 1 (by rfl) ⟨1491560, by rfl⟩ : syracuseStep 1988747 = 2983121) B2983121
theorem B1988759 : Blo 1325481 1988759 := bstep (se 1 (by rfl) ⟨1491569, by rfl⟩ : syracuseStep 1988759 = 2983139) B2983139
theorem B2152651 : Blo 1325481 2152651 := bstep (se 1 (by rfl) ⟨1614488, by rfl⟩ : syracuseStep 2152651 = 3228977) B3228977
theorem B1988825 : Blo 1325481 1988825 := bstep (se 2 (by rfl) ⟨745809, by rfl⟩ : syracuseStep 1988825 = 1491619) B1491619
theorem B1988939 : Blo 1325481 1988939 := bstep (se 1 (by rfl) ⟨1491704, by rfl⟩ : syracuseStep 1988939 = 2983409) B2983409
theorem B1988951 : Blo 1325481 1988951 := bstep (se 1 (by rfl) ⟨1491713, by rfl⟩ : syracuseStep 1988951 = 2983427) B2983427
theorem B1989017 : Blo 1325481 1989017 := bstep (se 2 (by rfl) ⟨745881, by rfl⟩ : syracuseStep 1989017 = 1491763) B1491763
theorem B1325483 : Blo 1325481 1325483 := bstep (se 1 (by rfl) ⟨994112, by rfl⟩ : syracuseStep 1325483 = 1988225) B1988225
theorem B4782509 : Blo 1325481 4782509 := bstep (se 3 (by rfl) ⟨896720, by rfl⟩ : syracuseStep 4782509 = 1793441) B1793441
theorem B3774899 : Blo 1325481 3774899 := bstep (se 1 (by rfl) ⟨2831174, by rfl⟩ : syracuseStep 3774899 = 5662349) B5662349
theorem B1325495 : Blo 1325481 1325495 := bstep (se 1 (by rfl) ⟨994121, by rfl⟩ : syracuseStep 1325495 = 1988243) B1988243
theorem B1325515 : Blo 1325481 1325515 := bstep (se 1 (by rfl) ⟨994136, by rfl⟩ : syracuseStep 1325515 = 1988273) B1988273
theorem B1325527 : Blo 1325481 1325527 := bstep (se 1 (by rfl) ⟨994145, by rfl⟩ : syracuseStep 1325527 = 1988291) B1988291
theorem B1325547 : Blo 1325481 1325547 := bstep (se 1 (by rfl) ⟨994160, by rfl⟩ : syracuseStep 1325547 = 1988321) B1988321
theorem B1325559 : Blo 1325481 1325559 := bstep (se 1 (by rfl) ⟨994169, by rfl⟩ : syracuseStep 1325559 = 1988339) B1988339
theorem B1325579 : Blo 1325481 1325579 := bstep (se 1 (by rfl) ⟨994184, by rfl⟩ : syracuseStep 1325579 = 1988369) B1988369
theorem B1989131 : Blo 1325481 1989131 := bstep (se 1 (by rfl) ⟨1491848, by rfl⟩ : syracuseStep 1989131 = 2983697) B2983697
theorem B1325591 : Blo 1325481 1325591 := bstep (se 1 (by rfl) ⟨994193, by rfl⟩ : syracuseStep 1325591 = 1988387) B1988387
theorem B1989143 : Blo 1325481 1989143 := bstep (se 1 (by rfl) ⟨1491857, by rfl⟩ : syracuseStep 1989143 = 2983715) B2983715
theorem B1325611 : Blo 1325481 1325611 := bstep (se 1 (by rfl) ⟨994208, by rfl⟩ : syracuseStep 1325611 = 1988417) B1988417
theorem B1325623 : Blo 1325481 1325623 := bstep (se 1 (by rfl) ⟨994217, by rfl⟩ : syracuseStep 1325623 = 1988435) B1988435
theorem B1325643 : Blo 1325481 1325643 := bstep (se 1 (by rfl) ⟨994232, by rfl⟩ : syracuseStep 1325643 = 1988465) B1988465
theorem B1325655 : Blo 1325481 1325655 := bstep (se 1 (by rfl) ⟨994241, by rfl⟩ : syracuseStep 1325655 = 1988483) B1988483
theorem B1989209 : Blo 1325481 1989209 := bstep (se 2 (by rfl) ⟨745953, by rfl⟩ : syracuseStep 1989209 = 1491907) B1491907
theorem B2832985 : Blo 1325481 2832985 := bstep (se 2 (by rfl) ⟨1062369, by rfl⟩ : syracuseStep 2832985 = 2124739) B2124739
theorem B1325675 : Blo 1325481 1325675 := bstep (se 1 (by rfl) ⟨994256, by rfl⟩ : syracuseStep 1325675 = 1988513) B1988513
theorem B1325687 : Blo 1325481 1325687 := bstep (se 1 (by rfl) ⟨994265, by rfl⟩ : syracuseStep 1325687 = 1988531) B1988531
theorem B1325707 : Blo 1325481 1325707 := bstep (se 1 (by rfl) ⟨994280, by rfl⟩ : syracuseStep 1325707 = 1988561) B1988561
theorem B1325719 : Blo 1325481 1325719 := bstep (se 1 (by rfl) ⟨994289, by rfl⟩ : syracuseStep 1325719 = 1988579) B1988579
theorem B1325739 : Blo 1325481 1325739 := bstep (se 1 (by rfl) ⟨994304, by rfl⟩ : syracuseStep 1325739 = 1988609) B1988609
theorem B1325751 : Blo 1325481 1325751 := bstep (se 1 (by rfl) ⟨994313, by rfl⟩ : syracuseStep 1325751 = 1988627) B1988627
theorem B1325771 : Blo 1325481 1325771 := bstep (se 1 (by rfl) ⟨994328, by rfl⟩ : syracuseStep 1325771 = 1988657) B1988657
theorem B1989323 : Blo 1325481 1989323 := bstep (se 1 (by rfl) ⟨1491992, by rfl⟩ : syracuseStep 1989323 = 2983985) B2983985
theorem B1325783 : Blo 1325481 1325783 := bstep (se 1 (by rfl) ⟨994337, by rfl⟩ : syracuseStep 1325783 = 1988675) B1988675
theorem B1989335 : Blo 1325481 1989335 := bstep (se 1 (by rfl) ⟨1492001, by rfl⟩ : syracuseStep 1989335 = 2984003) B2984003
theorem B1325803 : Blo 1325481 1325803 := bstep (se 1 (by rfl) ⟨994352, by rfl⟩ : syracuseStep 1325803 = 1988705) B1988705
theorem B1325815 : Blo 1325481 1325815 := bstep (se 1 (by rfl) ⟨994361, by rfl⟩ : syracuseStep 1325815 = 1988723) B1988723
theorem B1325835 : Blo 1325481 1325835 := bstep (se 1 (by rfl) ⟨994376, by rfl⟩ : syracuseStep 1325835 = 1988753) B1988753
theorem B1702667 : Blo 1325481 1702667 := bstep (se 1 (by rfl) ⟨1277000, by rfl⟩ : syracuseStep 1702667 = 2554001) B2554001
theorem B1325847 : Blo 1325481 1325847 := bstep (se 1 (by rfl) ⟨994385, by rfl⟩ : syracuseStep 1325847 = 1988771) B1988771
theorem B1989401 : Blo 1325481 1989401 := bstep (se 2 (by rfl) ⟨746025, by rfl⟩ : syracuseStep 1989401 = 1492051) B1492051
theorem B1325867 : Blo 1325481 1325867 := bstep (se 1 (by rfl) ⟨994400, by rfl⟩ : syracuseStep 1325867 = 1988801) B1988801
theorem B1325879 : Blo 1325481 1325879 := bstep (se 1 (by rfl) ⟨994409, by rfl⟩ : syracuseStep 1325879 = 1988819) B1988819
theorem B1325899 : Blo 1325481 1325899 := bstep (se 1 (by rfl) ⟨994424, by rfl⟩ : syracuseStep 1325899 = 1988849) B1988849
theorem B1325911 : Blo 1325481 1325911 := bstep (se 1 (by rfl) ⟨994433, by rfl⟩ : syracuseStep 1325911 = 1988867) B1988867
theorem B24214373 : Blo 1325481 24214373 := bstep (se 4 (by rfl) ⟨2270097, by rfl⟩ : syracuseStep 24214373 = 4540195) B4540195
theorem B1325931 : Blo 1325481 1325931 := bstep (se 1 (by rfl) ⟨994448, by rfl⟩ : syracuseStep 1325931 = 1988897) B1988897
theorem B1325943 : Blo 1325481 1325943 := bstep (se 1 (by rfl) ⟨994457, by rfl⟩ : syracuseStep 1325943 = 1988915) B1988915
theorem B1325963 : Blo 1325481 1325963 := bstep (se 1 (by rfl) ⟨994472, by rfl⟩ : syracuseStep 1325963 = 1988945) B1988945
theorem B1989515 : Blo 1325481 1989515 := bstep (se 1 (by rfl) ⟨1492136, by rfl⟩ : syracuseStep 1989515 = 2984273) B2984273
theorem B1325975 : Blo 1325481 1325975 := bstep (se 1 (by rfl) ⟨994481, by rfl⟩ : syracuseStep 1325975 = 1988963) B1988963
theorem B1989527 : Blo 1325481 1989527 := bstep (se 1 (by rfl) ⟨1492145, by rfl⟩ : syracuseStep 1989527 = 2984291) B2984291
theorem B1325995 : Blo 1325481 1325995 := bstep (se 1 (by rfl) ⟨994496, by rfl⟩ : syracuseStep 1325995 = 1988993) B1988993
theorem B1326007 : Blo 1325481 1326007 := bstep (se 1 (by rfl) ⟨994505, by rfl⟩ : syracuseStep 1326007 = 1989011) B1989011
theorem B1326027 : Blo 1325481 1326027 := bstep (se 1 (by rfl) ⟨994520, by rfl⟩ : syracuseStep 1326027 = 1989041) B1989041
theorem B4479947 : Blo 1325481 4479947 := bstep (se 1 (by rfl) ⟨3359960, by rfl⟩ : syracuseStep 4479947 = 6719921) B6719921
theorem B1326039 : Blo 1325481 1326039 := bstep (se 1 (by rfl) ⟨994529, by rfl⟩ : syracuseStep 1326039 = 1989059) B1989059
theorem B1416151 : Blo 1325481 1416151 := bstep (se 1 (by rfl) ⟨1062113, by rfl⟩ : syracuseStep 1416151 = 2124227) B2124227
theorem B1989593 : Blo 1325481 1989593 := bstep (se 2 (by rfl) ⟨746097, by rfl⟩ : syracuseStep 1989593 = 1492195) B1492195
theorem B1326059 : Blo 1325481 1326059 := bstep (se 1 (by rfl) ⟨994544, by rfl⟩ : syracuseStep 1326059 = 1989089) B1989089
theorem B1326071 : Blo 1325481 1326071 := bstep (se 1 (by rfl) ⟨994553, by rfl⟩ : syracuseStep 1326071 = 1989107) B1989107
theorem B1326091 : Blo 1325481 1326091 := bstep (se 1 (by rfl) ⟨994568, by rfl⟩ : syracuseStep 1326091 = 1989137) B1989137
theorem B12745745 : Blo 1325481 12745745 := bstep (se 2 (by rfl) ⟨4779654, by rfl⟩ : syracuseStep 12745745 = 9559309) B9559309
theorem B1326103 : Blo 1325481 1326103 := bstep (se 1 (by rfl) ⟨994577, by rfl⟩ : syracuseStep 1326103 = 1989155) B1989155
theorem B1326123 : Blo 1325481 1326123 := bstep (se 1 (by rfl) ⟨994592, by rfl⟩ : syracuseStep 1326123 = 1989185) B1989185
theorem B1326135 : Blo 1325481 1326135 := bstep (se 1 (by rfl) ⟨994601, by rfl⟩ : syracuseStep 1326135 = 1989203) B1989203
theorem B7552075 : Blo 1325481 7552075 := bstep (se 1 (by rfl) ⟨5664056, by rfl⟩ : syracuseStep 7552075 = 11328113) B11328113
theorem B1678411 : Blo 1325481 1678411 := bstep (se 1 (by rfl) ⟨1258808, by rfl⟩ : syracuseStep 1678411 = 2517617) B2517617
theorem B1326155 : Blo 1325481 1326155 := bstep (se 1 (by rfl) ⟨994616, by rfl⟩ : syracuseStep 1326155 = 1989233) B1989233
theorem B1989707 : Blo 1325481 1989707 := bstep (se 1 (by rfl) ⟨1492280, by rfl⟩ : syracuseStep 1989707 = 2984561) B2984561
theorem B1326167 : Blo 1325481 1326167 := bstep (se 1 (by rfl) ⟨994625, by rfl⟩ : syracuseStep 1326167 = 1989251) B1989251
theorem B1989719 : Blo 1325481 1989719 := bstep (se 1 (by rfl) ⟨1492289, by rfl⟩ : syracuseStep 1989719 = 2984579) B2984579
theorem B1326187 : Blo 1325481 1326187 := bstep (se 1 (by rfl) ⟨994640, by rfl⟩ : syracuseStep 1326187 = 1989281) B1989281
theorem B1326199 : Blo 1325481 1326199 := bstep (se 1 (by rfl) ⟨994649, by rfl⟩ : syracuseStep 1326199 = 1989299) B1989299
theorem B7560323 : Blo 1325481 7560323 := bstep (se 1 (by rfl) ⟨5670242, by rfl⟩ : syracuseStep 7560323 = 11340485) B11340485
theorem B1326219 : Blo 1325481 1326219 := bstep (se 1 (by rfl) ⟨994664, by rfl⟩ : syracuseStep 1326219 = 1989329) B1989329
theorem B1326231 : Blo 1325481 1326231 := bstep (se 1 (by rfl) ⟨994673, by rfl⟩ : syracuseStep 1326231 = 1989347) B1989347
theorem B2391191 : Blo 1325481 2391191 := bstep (se 1 (by rfl) ⟨1793393, by rfl⟩ : syracuseStep 2391191 = 3586787) B3586787
theorem B1989785 : Blo 1325481 1989785 := bstep (se 2 (by rfl) ⟨746169, by rfl⟩ : syracuseStep 1989785 = 1492339) B1492339
theorem B1326251 : Blo 1325481 1326251 := bstep (se 1 (by rfl) ⟨994688, by rfl⟩ : syracuseStep 1326251 = 1989377) B1989377
theorem B3357875 : Blo 1325481 3357875 := bstep (se 1 (by rfl) ⟨2518406, by rfl⟩ : syracuseStep 3357875 = 5036813) B5036813
theorem B1326263 : Blo 1325481 1326263 := bstep (se 1 (by rfl) ⟨994697, by rfl⟩ : syracuseStep 1326263 = 1989395) B1989395
theorem B5102795 : Blo 1325481 5102795 := bstep (se 1 (by rfl) ⟨3827096, by rfl⟩ : syracuseStep 5102795 = 7654193) B7654193
theorem B1326283 : Blo 1325481 1326283 := bstep (se 1 (by rfl) ⟨994712, by rfl⟩ : syracuseStep 1326283 = 1989425) B1989425
theorem B19127501 : Blo 1325481 19127501 := bstep (se 3 (by rfl) ⟨3586406, by rfl⟩ : syracuseStep 19127501 = 7172813) B7172813
theorem B3636427 : Blo 1325481 3636427 := bstep (se 1 (by rfl) ⟨2727320, by rfl⟩ : syracuseStep 3636427 = 5454641) B5454641
theorem B1326295 : Blo 1325481 1326295 := bstep (se 1 (by rfl) ⟨994721, by rfl⟩ : syracuseStep 1326295 = 1989443) B1989443
theorem B4480217 : Blo 1325481 4480217 := bstep (se 2 (by rfl) ⟨1680081, by rfl⟩ : syracuseStep 4480217 = 3360163) B3360163
theorem B1326315 : Blo 1325481 1326315 := bstep (se 1 (by rfl) ⟨994736, by rfl⟩ : syracuseStep 1326315 = 1989473) B1989473
theorem B1326327 : Blo 1325481 1326327 := bstep (se 1 (by rfl) ⟨994745, by rfl⟩ : syracuseStep 1326327 = 1989491) B1989491
theorem B1326347 : Blo 1325481 1326347 := bstep (se 1 (by rfl) ⟨994760, by rfl⟩ : syracuseStep 1326347 = 1989521) B1989521
theorem B1989899 : Blo 1325481 1989899 := bstep (se 1 (by rfl) ⟨1492424, by rfl⟩ : syracuseStep 1989899 = 2984849) B2984849
theorem B5037329 : Blo 1325481 5037329 := bstep (se 2 (by rfl) ⟨1888998, by rfl⟩ : syracuseStep 5037329 = 3777997) B3777997
theorem B1326359 : Blo 1325481 1326359 := bstep (se 1 (by rfl) ⟨994769, by rfl⟩ : syracuseStep 1326359 = 1989539) B1989539
theorem B1989911 : Blo 1325481 1989911 := bstep (se 1 (by rfl) ⟨1492433, by rfl⟩ : syracuseStep 1989911 = 2984867) B2984867
theorem B1326379 : Blo 1325481 1326379 := bstep (se 1 (by rfl) ⟨994784, by rfl⟩ : syracuseStep 1326379 = 1989569) B1989569
theorem B1326391 : Blo 1325481 1326391 := bstep (se 1 (by rfl) ⟨994793, by rfl⟩ : syracuseStep 1326391 = 1989587) B1989587
theorem B1326411 : Blo 1325481 1326411 := bstep (se 1 (by rfl) ⟨994808, by rfl⟩ : syracuseStep 1326411 = 1989617) B1989617
theorem B1416523 : Blo 1325481 1416523 := bstep (se 1 (by rfl) ⟨1062392, by rfl⟩ : syracuseStep 1416523 = 2124785) B2124785
theorem B1326423 : Blo 1325481 1326423 := bstep (se 1 (by rfl) ⟨994817, by rfl⟩ : syracuseStep 1326423 = 1989635) B1989635
theorem B1989977 : Blo 1325481 1989977 := bstep (se 2 (by rfl) ⟨746241, by rfl⟩ : syracuseStep 1989977 = 1492483) B1492483
theorem B7552349 : Blo 1325481 7552349 := bstep (se 3 (by rfl) ⟨1416065, by rfl⟩ : syracuseStep 7552349 = 2832131) B2832131
theorem B1326443 : Blo 1325481 1326443 := bstep (se 1 (by rfl) ⟨994832, by rfl⟩ : syracuseStep 1326443 = 1989665) B1989665
theorem B1326455 : Blo 1325481 1326455 := bstep (se 1 (by rfl) ⟨994841, by rfl⟩ : syracuseStep 1326455 = 1989683) B1989683
theorem B1326475 : Blo 1325481 1326475 := bstep (se 1 (by rfl) ⟨994856, by rfl⟩ : syracuseStep 1326475 = 1989713) B1989713
theorem B1326487 : Blo 1325481 1326487 := bstep (se 1 (by rfl) ⟨994865, by rfl⟩ : syracuseStep 1326487 = 1989731) B1989731
theorem B3636631 : Blo 1325481 3636631 := bstep (se 1 (by rfl) ⟨2727473, by rfl⟩ : syracuseStep 3636631 = 5454947) B5454947
theorem B1326507 : Blo 1325481 1326507 := bstep (se 1 (by rfl) ⟨994880, by rfl⟩ : syracuseStep 1326507 = 1989761) B1989761
theorem B1326519 : Blo 1325481 1326519 := bstep (se 1 (by rfl) ⟨994889, by rfl⟩ : syracuseStep 1326519 = 1989779) B1989779
theorem B1326539 : Blo 1325481 1326539 := bstep (se 1 (by rfl) ⟨994904, by rfl⟩ : syracuseStep 1326539 = 1989809) B1989809
theorem B1990091 : Blo 1325481 1990091 := bstep (se 1 (by rfl) ⟨1492568, by rfl⟩ : syracuseStep 1990091 = 2985137) B2985137
theorem B1326551 : Blo 1325481 1326551 := bstep (se 1 (by rfl) ⟨994913, by rfl⟩ : syracuseStep 1326551 = 1989827) B1989827
theorem B1990103 : Blo 1325481 1990103 := bstep (se 1 (by rfl) ⟨1492577, by rfl⟩ : syracuseStep 1990103 = 2985155) B2985155
theorem B7167449 : Blo 1325481 7167449 := bstep (se 2 (by rfl) ⟨2687793, by rfl⟩ : syracuseStep 7167449 = 5375587) B5375587
theorem B3358169 : Blo 1325481 3358169 := bstep (se 2 (by rfl) ⟨1259313, by rfl⟩ : syracuseStep 3358169 = 2518627) B2518627
theorem B1326571 : Blo 1325481 1326571 := bstep (se 1 (by rfl) ⟨994928, by rfl⟩ : syracuseStep 1326571 = 1989857) B1989857
theorem B1326583 : Blo 1325481 1326583 := bstep (se 1 (by rfl) ⟨994937, by rfl⟩ : syracuseStep 1326583 = 1989875) B1989875
theorem B1326603 : Blo 1325481 1326603 := bstep (se 1 (by rfl) ⟨994952, by rfl⟩ : syracuseStep 1326603 = 1989905) B1989905
theorem B1326615 : Blo 1325481 1326615 := bstep (se 1 (by rfl) ⟨994961, by rfl⟩ : syracuseStep 1326615 = 1989923) B1989923
theorem B1990169 : Blo 1325481 1990169 := bstep (se 2 (by rfl) ⟨746313, by rfl⟩ : syracuseStep 1990169 = 1492627) B1492627
theorem B1326635 : Blo 1325481 1326635 := bstep (se 1 (by rfl) ⟨994976, by rfl⟩ : syracuseStep 1326635 = 1989953) B1989953
theorem B1326647 : Blo 1325481 1326647 := bstep (se 1 (by rfl) ⟨994985, by rfl⟩ : syracuseStep 1326647 = 1989971) B1989971
theorem B1326667 : Blo 1325481 1326667 := bstep (se 1 (by rfl) ⟨995000, by rfl⟩ : syracuseStep 1326667 = 1990001) B1990001
theorem B1326679 : Blo 1325481 1326679 := bstep (se 1 (by rfl) ⟨995009, by rfl⟩ : syracuseStep 1326679 = 1990019) B1990019
theorem B3636829 : Blo 1325481 3636829 := bstep (se 3 (by rfl) ⟨681905, by rfl⟩ : syracuseStep 3636829 = 1363811) B1363811
theorem B1326699 : Blo 1325481 1326699 := bstep (se 1 (by rfl) ⟨995024, by rfl⟩ : syracuseStep 1326699 = 1990049) B1990049
theorem B1326711 : Blo 1325481 1326711 := bstep (se 1 (by rfl) ⟨995033, by rfl⟩ : syracuseStep 1326711 = 1990067) B1990067
theorem B1326731 : Blo 1325481 1326731 := bstep (se 1 (by rfl) ⟨995048, by rfl⟩ : syracuseStep 1326731 = 1990097) B1990097
theorem B1990283 : Blo 1325481 1990283 := bstep (se 1 (by rfl) ⟨1492712, by rfl⟩ : syracuseStep 1990283 = 2985425) B2985425
theorem B1326743 : Blo 1325481 1326743 := bstep (se 1 (by rfl) ⟨995057, by rfl⟩ : syracuseStep 1326743 = 1990115) B1990115
theorem B1990295 : Blo 1325481 1990295 := bstep (se 1 (by rfl) ⟨1492721, by rfl⟩ : syracuseStep 1990295 = 2985443) B2985443
theorem B1326763 : Blo 1325481 1326763 := bstep (se 1 (by rfl) ⟨995072, by rfl⟩ : syracuseStep 1326763 = 1990145) B1990145
theorem B1326775 : Blo 1325481 1326775 := bstep (se 1 (by rfl) ⟨995081, by rfl⟩ : syracuseStep 1326775 = 1990163) B1990163
theorem B1326795 : Blo 1325481 1326795 := bstep (se 1 (by rfl) ⟨995096, by rfl⟩ : syracuseStep 1326795 = 1990193) B1990193
theorem B1326807 : Blo 1325481 1326807 := bstep (se 1 (by rfl) ⟨995105, by rfl⟩ : syracuseStep 1326807 = 1990211) B1990211
theorem B9690841 : Blo 1325481 9690841 := bstep (se 2 (by rfl) ⟨3634065, by rfl⟩ : syracuseStep 9690841 = 7268131) B7268131
theorem B5037785 : Blo 1325481 5037785 := bstep (se 2 (by rfl) ⟨1889169, by rfl⟩ : syracuseStep 5037785 = 3778339) B3778339
theorem B1990361 : Blo 1325481 1990361 := bstep (se 2 (by rfl) ⟨746385, by rfl⟩ : syracuseStep 1990361 = 1492771) B1492771
theorem B1326827 : Blo 1325481 1326827 := bstep (se 1 (by rfl) ⟨995120, by rfl⟩ : syracuseStep 1326827 = 1990241) B1990241
theorem B1326839 : Blo 1325481 1326839 := bstep (se 1 (by rfl) ⟨995129, by rfl⟩ : syracuseStep 1326839 = 1990259) B1990259
theorem B1326859 : Blo 1325481 1326859 := bstep (se 1 (by rfl) ⟨995144, by rfl⟩ : syracuseStep 1326859 = 1990289) B1990289
theorem B1416971 : Blo 1325481 1416971 := bstep (se 1 (by rfl) ⟨1062728, by rfl⟩ : syracuseStep 1416971 = 2125457) B2125457
theorem B1326871 : Blo 1325481 1326871 := bstep (se 1 (by rfl) ⟨995153, by rfl⟩ : syracuseStep 1326871 = 1990307) B1990307
theorem B1326891 : Blo 1325481 1326891 := bstep (se 1 (by rfl) ⟨995168, by rfl⟩ : syracuseStep 1326891 = 1990337) B1990337
theorem B1326903 : Blo 1325481 1326903 := bstep (se 1 (by rfl) ⟨995177, by rfl⟩ : syracuseStep 1326903 = 1990355) B1990355
theorem B1326923 : Blo 1325481 1326923 := bstep (se 1 (by rfl) ⟨995192, by rfl⟩ : syracuseStep 1326923 = 1990385) B1990385
theorem B1990475 : Blo 1325481 1990475 := bstep (se 1 (by rfl) ⟨1492856, by rfl⟩ : syracuseStep 1990475 = 2985713) B2985713
theorem B1326935 : Blo 1325481 1326935 := bstep (se 1 (by rfl) ⟨995201, by rfl⟩ : syracuseStep 1326935 = 1990403) B1990403
theorem B1990487 : Blo 1325481 1990487 := bstep (se 1 (by rfl) ⟨1492865, by rfl⟩ : syracuseStep 1990487 = 2985731) B2985731
theorem B1326955 : Blo 1325481 1326955 := bstep (se 1 (by rfl) ⟨995216, by rfl⟩ : syracuseStep 1326955 = 1990433) B1990433
theorem B1326967 : Blo 1325481 1326967 := bstep (se 1 (by rfl) ⟨995225, by rfl⟩ : syracuseStep 1326967 = 1990451) B1990451
theorem B1326987 : Blo 1325481 1326987 := bstep (se 1 (by rfl) ⟨995240, by rfl⟩ : syracuseStep 1326987 = 1990481) B1990481
theorem B1326999 : Blo 1325481 1326999 := bstep (se 1 (by rfl) ⟨995249, by rfl⟩ : syracuseStep 1326999 = 1990499) B1990499
theorem B1990553 : Blo 1325481 1990553 := bstep (se 2 (by rfl) ⟨746457, by rfl⟩ : syracuseStep 1990553 = 1492915) B1492915
theorem B1327019 : Blo 1325481 1327019 := bstep (se 1 (by rfl) ⟨995264, by rfl⟩ : syracuseStep 1327019 = 1990529) B1990529
theorem B5037997 : Blo 1325481 5037997 := bstep (se 3 (by rfl) ⟨944624, by rfl⟩ : syracuseStep 5037997 = 1889249) B1889249
theorem B1327031 : Blo 1325481 1327031 := bstep (se 1 (by rfl) ⟨995273, by rfl⟩ : syracuseStep 1327031 = 1990547) B1990547
theorem B1327051 : Blo 1325481 1327051 := bstep (se 1 (by rfl) ⟨995288, by rfl⟩ : syracuseStep 1327051 = 1990577) B1990577
theorem B1327063 : Blo 1325481 1327063 := bstep (se 1 (by rfl) ⟨995297, by rfl⟩ : syracuseStep 1327063 = 1990595) B1990595
theorem B5668825 : Blo 1325481 5668825 := bstep (se 2 (by rfl) ⟨2125809, by rfl⟩ : syracuseStep 5668825 = 4251619) B4251619
theorem B4538333 : Blo 1325481 4538333 := bstep (se 3 (by rfl) ⟨850937, by rfl⟩ : syracuseStep 4538333 = 1701875) B1701875
theorem B1327083 : Blo 1325481 1327083 := bstep (se 1 (by rfl) ⟨995312, by rfl⟩ : syracuseStep 1327083 = 1990625) B1990625
theorem B1327095 : Blo 1325481 1327095 := bstep (se 1 (by rfl) ⟨995321, by rfl⟩ : syracuseStep 1327095 = 1990643) B1990643
theorem B1327111 : Blo 1325481 1327111 := bstep (se 1 (by rfl) ⟨995333, by rfl⟩ : syracuseStep 1327111 = 1990667) B1990667
theorem B1327119 : Blo 1325481 1327119 := bstep (se 1 (by rfl) ⟨995339, by rfl⟩ : syracuseStep 1327119 = 1990679) B1990679
theorem B5382173 : Blo 1325481 5382173 := bstep (se 3 (by rfl) ⟨1009157, by rfl⟩ : syracuseStep 5382173 = 2018315) B2018315
theorem B1990715 : Blo 1325481 1990715 := bstep (se 1 (by rfl) ⟨1493036, by rfl⟩ : syracuseStep 1990715 = 2986073) B2986073
theorem B1327163 : Blo 1325481 1327163 := bstep (se 1 (by rfl) ⟨995372, by rfl⟩ : syracuseStep 1327163 = 1990745) B1990745
theorem B1990775 : Blo 1325481 1990775 := bstep (se 1 (by rfl) ⟨1493081, by rfl⟩ : syracuseStep 1990775 = 2986163) B2986163
theorem B1327239 : Blo 1325481 1327239 := bstep (se 1 (by rfl) ⟨995429, by rfl⟩ : syracuseStep 1327239 = 1990859) B1990859
theorem B1990799 : Blo 1325481 1990799 := bstep (se 1 (by rfl) ⟨1493099, by rfl⟩ : syracuseStep 1990799 = 2986199) B2986199
theorem B1327247 : Blo 1325481 1327247 := bstep (se 1 (by rfl) ⟨995435, by rfl⟩ : syracuseStep 1327247 = 1990871) B1990871
theorem B3358867 : Blo 1325481 3358867 := bstep (se 1 (by rfl) ⟨2519150, by rfl⟩ : syracuseStep 3358867 = 5038301) B5038301
theorem B3776665 : Blo 1325481 3776665 := bstep (se 2 (by rfl) ⟨1416249, by rfl⟩ : syracuseStep 3776665 = 2832499) B2832499
theorem B1990841 : Blo 1325481 1990841 := bstep (se 2 (by rfl) ⟨746565, by rfl⟩ : syracuseStep 1990841 = 1493131) B1493131
theorem B1327291 : Blo 1325481 1327291 := bstep (se 1 (by rfl) ⟨995468, by rfl⟩ : syracuseStep 1327291 = 1990937) B1990937
theorem B1990919 : Blo 1325481 1990919 := bstep (se 1 (by rfl) ⟨1493189, by rfl⟩ : syracuseStep 1990919 = 2986379) B2986379
theorem B1327367 : Blo 1325481 1327367 := bstep (se 1 (by rfl) ⟨995525, by rfl⟩ : syracuseStep 1327367 = 1991051) B1991051
theorem B3186955 : Blo 1325481 3186955 := bstep (se 1 (by rfl) ⟨2390216, by rfl⟩ : syracuseStep 3186955 = 4780433) B4780433
theorem B1327375 : Blo 1325481 1327375 := bstep (se 1 (by rfl) ⟨995531, by rfl⟩ : syracuseStep 1327375 = 1991063) B1991063
theorem B15106337 : Blo 1325481 15106337 := bstep (se 2 (by rfl) ⟨5664876, by rfl⟩ : syracuseStep 15106337 = 11329753) B11329753
theorem B3359009 : Blo 1325481 3359009 := bstep (se 2 (by rfl) ⟨1259628, by rfl⟩ : syracuseStep 3359009 = 2519257) B2519257
theorem B1990955 : Blo 1325481 1990955 := bstep (se 1 (by rfl) ⟨1493216, by rfl⟩ : syracuseStep 1990955 = 2986433) B2986433
theorem B1491259 : Blo 1325481 1491259 := bstep (se 1 (by rfl) ⟨1118444, by rfl⟩ : syracuseStep 1491259 = 2236889) B2236889
theorem B1327419 : Blo 1325481 1327419 := bstep (se 1 (by rfl) ⟨995564, by rfl⟩ : syracuseStep 1327419 = 1991129) B1991129
theorem B1990985 : Blo 1325481 1990985 := bstep (se 2 (by rfl) ⟨746619, by rfl⟩ : syracuseStep 1990985 = 1493239) B1493239
theorem B5038483 : Blo 1325481 5038483 := bstep (se 1 (by rfl) ⟨3778862, by rfl⟩ : syracuseStep 5038483 = 7557725) B7557725
theorem B1991099 : Blo 1325481 1991099 := bstep (se 1 (by rfl) ⟨1493324, by rfl⟩ : syracuseStep 1991099 = 2986649) B2986649
theorem B6373835 : Blo 1325481 6373835 := bstep (se 1 (by rfl) ⟨4780376, by rfl⟩ : syracuseStep 6373835 = 9560753) B9560753
theorem B1991159 : Blo 1325481 1991159 := bstep (se 1 (by rfl) ⟨1493369, by rfl⟩ : syracuseStep 1991159 = 2986739) B2986739
theorem B1679879 : Blo 1325481 1679879 := bstep (se 1 (by rfl) ⟨1259909, by rfl⟩ : syracuseStep 1679879 = 2519819) B2519819
theorem B2236943 : Blo 1325481 2236943 := bstep (se 1 (by rfl) ⟨1677707, by rfl⟩ : syracuseStep 2236943 = 3355415) B3355415
theorem B1991183 : Blo 1325481 1991183 := bstep (se 1 (by rfl) ⟨1493387, by rfl⟩ : syracuseStep 1991183 = 2986775) B2986775
theorem B13607453 : Blo 1325481 13607453 := bstep (se 3 (by rfl) ⟨2551397, by rfl⟩ : syracuseStep 13607453 = 5102795) B5102795
theorem B36282923 : Blo 1325481 36282923 := bstep (se 1 (by rfl) ⟨27212192, by rfl⟩ : syracuseStep 36282923 = 54424385) B54424385
theorem B4252247 : Blo 1325481 4252247 := bstep (se 1 (by rfl) ⟨3189185, by rfl⟩ : syracuseStep 4252247 = 6378371) B6378371
theorem B2982671 : Blo 1325481 2982671 := bstep (se 1 (by rfl) ⟨2237003, by rfl⟩ : syracuseStep 2982671 = 4474007) B4474007
theorem B1491727 : Blo 1325481 1491727 := bstep (se 1 (by rfl) ⟨1118795, by rfl⟩ : syracuseStep 1491727 = 2237591) B2237591
theorem B7553807 : Blo 1325481 7553807 := bstep (se 1 (by rfl) ⟨5665355, by rfl⟩ : syracuseStep 7553807 = 11330711) B11330711
theorem B2982689 : Blo 1325481 2982689 := bstep (se 2 (by rfl) ⟨1118508, by rfl⟩ : syracuseStep 2982689 = 2237017) B2237017
theorem B3023659 : Blo 1325481 3023659 := bstep (se 1 (by rfl) ⟨2267744, by rfl⟩ : syracuseStep 3023659 = 4535489) B4535489
theorem B7554059 : Blo 1325481 7554059 := bstep (se 1 (by rfl) ⟨5665544, by rfl⟩ : syracuseStep 7554059 = 11331089) B11331089
theorem B11338775 : Blo 1325481 11338775 := bstep (se 1 (by rfl) ⟨8504081, by rfl⟩ : syracuseStep 11338775 = 17008163) B17008163
theorem B4473899 : Blo 1325481 4473899 := bstep (se 1 (by rfl) ⟨3355424, by rfl⟩ : syracuseStep 4473899 = 6710849) B6710849
theorem B2237483 : Blo 1325481 2237483 := bstep (se 1 (by rfl) ⟨1678112, by rfl⟩ : syracuseStep 2237483 = 3356225) B3356225
theorem B2983031 : Blo 1325481 2983031 := bstep (se 1 (by rfl) ⟨2237273, by rfl⟩ : syracuseStep 2983031 = 4474547) B4474547
theorem B8291585 : Blo 1325481 8291585 := bstep (se 2 (by rfl) ⟨3109344, by rfl⟩ : syracuseStep 8291585 = 6218689) B6218689
theorem B3360001 : Blo 1325481 3360001 := bstep (se 2 (by rfl) ⟨1260000, by rfl⟩ : syracuseStep 3360001 = 2520001) B2520001
theorem B1492231 : Blo 1325481 1492231 := bstep (se 1 (by rfl) ⟨1119173, by rfl⟩ : syracuseStep 1492231 = 2238347) B2238347
theorem B2983211 : Blo 1325481 2983211 := bstep (se 1 (by rfl) ⟨2237408, by rfl⟩ : syracuseStep 2983211 = 4474817) B4474817
theorem B6456665 : Blo 1325481 6456665 := bstep (se 2 (by rfl) ⟨2421249, by rfl⟩ : syracuseStep 6456665 = 4842499) B4842499
theorem B2688403 : Blo 1325481 2688403 := bstep (se 1 (by rfl) ⟨2016302, by rfl⟩ : syracuseStep 2688403 = 4032605) B4032605
theorem B10069433 : Blo 1325481 10069433 := bstep (se 2 (by rfl) ⟨3776037, by rfl⟩ : syracuseStep 10069433 = 7552075) B7552075
theorem B2237881 : Blo 1325481 2237881 := bstep (se 2 (by rfl) ⟨839205, by rfl⟩ : syracuseStep 2237881 = 1678411) B1678411
theorem B1492411 : Blo 1325481 1492411 := bstep (se 1 (by rfl) ⟨1119308, by rfl⟩ : syracuseStep 1492411 = 2238617) B2238617
theorem B11494865 : Blo 1325481 11494865 := bstep (se 2 (by rfl) ⟨4310574, by rfl⟩ : syracuseStep 11494865 = 8621149) B8621149
theorem B3188339 : Blo 1325481 3188339 := bstep (se 1 (by rfl) ⟨2391254, by rfl⟩ : syracuseStep 3188339 = 4782509) B4782509
theorem B2516599 : Blo 1325481 2516599 := bstep (se 1 (by rfl) ⟨1887449, by rfl⟩ : syracuseStep 2516599 = 3774899) B3774899
theorem B2983571 : Blo 1325481 2983571 := bstep (se 1 (by rfl) ⟨2237678, by rfl⟩ : syracuseStep 2983571 = 4475357) B4475357
theorem B2983625 : Blo 1325481 2983625 := bstep (se 2 (by rfl) ⟨1118859, by rfl⟩ : syracuseStep 2983625 = 2237719) B2237719
theorem B1492879 : Blo 1325481 1492879 := bstep (se 1 (by rfl) ⟨1119659, by rfl⟩ : syracuseStep 1492879 = 2239319) B2239319
theorem B6719435 : Blo 1325481 6719435 := bstep (se 1 (by rfl) ⟨5039576, by rfl⟩ : syracuseStep 6719435 = 10079153) B10079153
theorem B6637571 : Blo 1325481 6637571 := bstep (se 1 (by rfl) ⟨4978178, by rfl⟩ : syracuseStep 6637571 = 9956357) B9956357
theorem B8497163 : Blo 1325481 8497163 := bstep (se 1 (by rfl) ⟨6372872, by rfl⟩ : syracuseStep 8497163 = 12745745) B12745745
theorem B3778589 : Blo 1325481 3778589 := bstep (se 3 (by rfl) ⟨708485, by rfl⟩ : syracuseStep 3778589 = 1416971) B1416971
theorem B4540445 : Blo 1325481 4540445 := bstep (se 3 (by rfl) ⟨851333, by rfl⟩ : syracuseStep 4540445 = 1702667) B1702667
theorem B11339837 : Blo 1325481 11339837 := bstep (se 3 (by rfl) ⟨2126219, by rfl⟩ : syracuseStep 11339837 = 4252439) B4252439
theorem B5040215 : Blo 1325481 5040215 := bstep (se 1 (by rfl) ⟨3780161, by rfl⟩ : syracuseStep 5040215 = 7560323) B7560323
theorem B2238583 : Blo 1325481 2238583 := bstep (se 1 (by rfl) ⟨1678937, by rfl⟩ : syracuseStep 2238583 = 3357875) B3357875
theorem B7555265 : Blo 1325481 7555265 := bstep (se 2 (by rfl) ⟨2833224, by rfl⟩ : syracuseStep 7555265 = 5666449) B5666449
theorem B6711497 : Blo 1325481 6711497 := bstep (se 2 (by rfl) ⟨2516811, by rfl⟩ : syracuseStep 6711497 = 5033623) B5033623
theorem B4778185 : Blo 1325481 4778185 := bstep (se 2 (by rfl) ⟨1791819, by rfl⟩ : syracuseStep 4778185 = 3583639) B3583639
theorem B6719759 : Blo 1325481 6719759 := bstep (se 1 (by rfl) ⟨5039819, by rfl⟩ : syracuseStep 6719759 = 10079639) B10079639
theorem B12921121 : Blo 1325481 12921121 := bstep (se 2 (by rfl) ⟨4845420, by rfl⟩ : syracuseStep 12921121 = 9690841) B9690841
theorem B4778299 : Blo 1325481 4778299 := bstep (se 1 (by rfl) ⟨3583724, by rfl⟩ : syracuseStep 4778299 = 7167449) B7167449
theorem B4475195 : Blo 1325481 4475195 := bstep (se 1 (by rfl) ⟨3356396, by rfl⟩ : syracuseStep 4475195 = 6712793) B6712793
theorem B2238779 : Blo 1325481 2238779 := bstep (se 1 (by rfl) ⟨1679084, by rfl⟩ : syracuseStep 2238779 = 3358169) B3358169
theorem B2984327 : Blo 1325481 2984327 := bstep (se 1 (by rfl) ⟨2238245, by rfl⟩ : syracuseStep 2984327 = 4476491) B4476491
theorem B1493383 : Blo 1325481 1493383 := bstep (se 1 (by rfl) ⟨1120037, by rfl⟩ : syracuseStep 1493383 = 2240075) B2240075
theorem B2984507 : Blo 1325481 2984507 := bstep (se 1 (by rfl) ⟨2238380, by rfl⟩ : syracuseStep 2984507 = 4476761) B4476761
theorem B2689595 : Blo 1325481 2689595 := bstep (se 1 (by rfl) ⟨2017196, by rfl⟩ : syracuseStep 2689595 = 4034393) B4034393
theorem B3025555 : Blo 1325481 3025555 := bstep (se 1 (by rfl) ⟨2269166, by rfl⟩ : syracuseStep 3025555 = 4538333) B4538333
theorem B2984633 : Blo 1325481 2984633 := bstep (se 2 (by rfl) ⟨1119237, by rfl⟩ : syracuseStep 2984633 = 2238475) B2238475
theorem B21506753 : Blo 1325481 21506753 := bstep (se 2 (by rfl) ⟨8065032, by rfl⟩ : syracuseStep 21506753 = 16130065) B16130065
theorem B2239177 : Blo 1325481 2239177 := bstep (se 2 (by rfl) ⟨839691, by rfl⟩ : syracuseStep 2239177 = 1679383) B1679383
theorem B3779273 : Blo 1325481 3779273 := bstep (se 2 (by rfl) ⟨1417227, by rfl⟩ : syracuseStep 3779273 = 2834455) B2834455
theorem B4475681 : Blo 1325481 4475681 := bstep (se 2 (by rfl) ⟨1678380, by rfl⟩ : syracuseStep 4475681 = 3356761) B3356761
theorem B2870201 : Blo 1325481 2870201 := bstep (se 2 (by rfl) ⟨1076325, by rfl⟩ : syracuseStep 2870201 = 2152651) B2152651
theorem B2984975 : Blo 1325481 2984975 := bstep (se 1 (by rfl) ⟨2238731, by rfl⟩ : syracuseStep 2984975 = 4477463) B4477463
theorem B2984993 : Blo 1325481 2984993 := bstep (se 2 (by rfl) ⟨1119372, by rfl⟩ : syracuseStep 2984993 = 2238745) B2238745
theorem B3320947 : Blo 1325481 3320947 := bstep (se 1 (by rfl) ⟨2490710, by rfl⟩ : syracuseStep 3320947 = 4981421) B4981421
theorem B15109253 : Blo 1325481 15109253 := bstep (se 4 (by rfl) ⟨1416492, by rfl⟩ : syracuseStep 15109253 = 2832985) B2832985
theorem B3026105 : Blo 1325481 3026105 := bstep (se 2 (by rfl) ⟨1134789, by rfl⟩ : syracuseStep 3026105 = 2269579) B2269579
theorem B3779855 : Blo 1325481 3779855 := bstep (se 1 (by rfl) ⟨2834891, by rfl⟩ : syracuseStep 3779855 = 5669783) B5669783
theorem B4476275 : Blo 1325481 4476275 := bstep (se 1 (by rfl) ⟨3357206, by rfl⟩ : syracuseStep 4476275 = 6714413) B6714413
theorem B2518391 : Blo 1325481 2518391 := bstep (se 1 (by rfl) ⟨1888793, by rfl⟩ : syracuseStep 2518391 = 3777587) B3777587
theorem B2985335 : Blo 1325481 2985335 := bstep (se 1 (by rfl) ⟨2239001, by rfl⟩ : syracuseStep 2985335 = 4478003) B4478003
theorem B2239879 : Blo 1325481 2239879 := bstep (se 1 (by rfl) ⟨1679909, by rfl⟩ : syracuseStep 2239879 = 3359819) B3359819
theorem B3583379 : Blo 1325481 3583379 := bstep (se 1 (by rfl) ⟨2687534, by rfl⟩ : syracuseStep 3583379 = 5375069) B5375069
theorem B3026377 : Blo 1325481 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B2518543 : Blo 1325481 2518543 := bstep (se 1 (by rfl) ⟨1888907, by rfl⟩ : syracuseStep 2518543 = 3777815) B3777815
theorem B3583531 : Blo 1325481 3583531 := bstep (se 1 (by rfl) ⟨2687648, by rfl⟩ : syracuseStep 3583531 = 5375297) B5375297
theorem B2985515 : Blo 1325481 2985515 := bstep (se 1 (by rfl) ⟨2239136, by rfl⟩ : syracuseStep 2985515 = 4478273) B4478273
theorem B15118001 : Blo 1325481 15118001 := bstep (se 2 (by rfl) ⟨5669250, by rfl⟩ : syracuseStep 15118001 = 11338501) B11338501
theorem B7171841 : Blo 1325481 7171841 := bstep (se 2 (by rfl) ⟨2689440, by rfl⟩ : syracuseStep 7171841 = 5378881) B5378881
theorem B14946049 : Blo 1325481 14946049 := bstep (se 2 (by rfl) ⟨5604768, by rfl⟩ : syracuseStep 14946049 = 11209537) B11209537
theorem B3583759 : Blo 1325481 3583759 := bstep (se 1 (by rfl) ⟨2687819, by rfl⟩ : syracuseStep 3583759 = 5375639) B5375639
theorem B15306533 : Blo 1325481 15306533 := bstep (se 4 (by rfl) ⟨1434987, by rfl⟩ : syracuseStep 15306533 = 2869975) B2869975
theorem B14339915 : Blo 1325481 14339915 := bstep (se 1 (by rfl) ⟨10754936, by rfl⟩ : syracuseStep 14339915 = 21509873) B21509873
theorem B2518931 : Blo 1325481 2518931 := bstep (se 1 (by rfl) ⟨1889198, by rfl⟩ : syracuseStep 2518931 = 3778397) B3778397
theorem B2985875 : Blo 1325481 2985875 := bstep (se 1 (by rfl) ⟨2239406, by rfl⟩ : syracuseStep 2985875 = 4478813) B4478813
theorem B1888201 : Blo 1325481 1888201 := bstep (se 2 (by rfl) ⟨708075, by rfl⟩ : syracuseStep 1888201 = 1416151) B1416151
theorem B2985929 : Blo 1325481 2985929 := bstep (se 2 (by rfl) ⟨1119723, by rfl⟩ : syracuseStep 2985929 = 2239447) B2239447
theorem B15101963 : Blo 1325481 15101963 := bstep (se 1 (by rfl) ⟨11326472, by rfl⟩ : syracuseStep 15101963 = 22652945) B22652945
theorem B2125867 : Blo 1325481 2125867 := bstep (se 1 (by rfl) ⟨1594400, by rfl⟩ : syracuseStep 2125867 = 3188801) B3188801
theorem B5108027 : Blo 1325481 5108027 := bstep (se 1 (by rfl) ⟨3831020, by rfl⟩ : syracuseStep 5108027 = 7662041) B7662041
theorem B3584375 : Blo 1325481 3584375 := bstep (se 1 (by rfl) ⟨2688281, by rfl⟩ : syracuseStep 3584375 = 5376563) B5376563
theorem B1888697 : Blo 1325481 1888697 := bstep (se 2 (by rfl) ⟨708261, by rfl⟩ : syracuseStep 1888697 = 1416523) B1416523
theorem B25498097 : Blo 1325481 25498097 := bstep (se 2 (by rfl) ⟨9561786, by rfl⟩ : syracuseStep 25498097 = 19123573) B19123573
theorem B6369835 : Blo 1325481 6369835 := bstep (se 1 (by rfl) ⟨4777376, by rfl⟩ : syracuseStep 6369835 = 9554753) B9554753
theorem B16142915 : Blo 1325481 16142915 := bstep (se 1 (by rfl) ⟨12107186, by rfl⟩ : syracuseStep 16142915 = 24214373) B24214373
theorem B2986631 : Blo 1325481 2986631 := bstep (se 1 (by rfl) ⟨2239973, by rfl⟩ : syracuseStep 2986631 = 4479947) B4479947
theorem B3355283 : Blo 1325481 3355283 := bstep (se 1 (by rfl) ⟨2516462, by rfl⟩ : syracuseStep 3355283 = 5032925) B5032925
theorem B11334401 : Blo 1325481 11334401 := bstep (se 2 (by rfl) ⟨4250400, by rfl⟩ : syracuseStep 11334401 = 8500801) B8500801
theorem B1594127 : Blo 1325481 1594127 := bstep (se 1 (by rfl) ⟨1195595, by rfl⟩ : syracuseStep 1594127 = 2391191) B2391191
theorem B12751667 : Blo 1325481 12751667 := bstep (se 1 (by rfl) ⟨9563750, by rfl⟩ : syracuseStep 12751667 = 19127501) B19127501
theorem B2986811 : Blo 1325481 2986811 := bstep (se 1 (by rfl) ⟨2240108, by rfl⟩ : syracuseStep 2986811 = 4480217) B4480217
theorem B12743513 : Blo 1325481 12743513 := bstep (se 2 (by rfl) ⟨4778817, by rfl⟩ : syracuseStep 12743513 = 9557635) B9557635
theorem B5034899 : Blo 1325481 5034899 := bstep (se 1 (by rfl) ⟨3776174, by rfl⟩ : syracuseStep 5034899 = 7552349) B7552349
theorem B3584915 : Blo 1325481 3584915 := bstep (se 1 (by rfl) ⟨2688686, by rfl⟩ : syracuseStep 3584915 = 5377373) B5377373
theorem B3355577 : Blo 1325481 3355577 := bstep (se 2 (by rfl) ⟨1258341, by rfl⟩ : syracuseStep 3355577 = 2516683) B2516683
theorem B3585143 : Blo 1325481 3585143 := bstep (se 1 (by rfl) ⟨2688857, by rfl⟩ : syracuseStep 3585143 = 5377715) B5377715
theorem B7558433 : Blo 1325481 7558433 := bstep (se 2 (by rfl) ⟨2834412, by rfl⟩ : syracuseStep 7558433 = 5668825) B5668825
theorem B5666107 : Blo 1325481 5666107 := bstep (se 1 (by rfl) ⟨4249580, by rfl⟩ : syracuseStep 5666107 = 8499161) B8499161
theorem B2725255 : Blo 1325481 2725255 := bstep (se 1 (by rfl) ⟨2043941, by rfl⟩ : syracuseStep 2725255 = 4087883) B4087883
theorem B1889671 : Blo 1325481 1889671 := bstep (se 1 (by rfl) ⟨1417253, by rfl⟩ : syracuseStep 1889671 = 2834507) B2834507
theorem B3585433 : Blo 1325481 3585433 := bstep (se 2 (by rfl) ⟨1344537, by rfl⟩ : syracuseStep 3585433 = 2689075) B2689075
theorem B3356275 : Blo 1325481 3356275 := bstep (se 1 (by rfl) ⟨2517206, by rfl⟩ : syracuseStep 3356275 = 5034413) B5034413
theorem B1988231 : Blo 1325481 1988231 := bstep (se 1 (by rfl) ⟨1491173, by rfl⟩ : syracuseStep 1988231 = 2982347) B2982347
theorem B1988267 : Blo 1325481 1988267 := bstep (se 1 (by rfl) ⟨1491200, by rfl⟩ : syracuseStep 1988267 = 2982401) B2982401
theorem B2873017 : Blo 1325481 2873017 := bstep (se 2 (by rfl) ⟨1077381, by rfl⟩ : syracuseStep 2873017 = 2154763) B2154763
theorem B1988297 : Blo 1325481 1988297 := bstep (se 2 (by rfl) ⟨745611, by rfl⟩ : syracuseStep 1988297 = 1491223) B1491223
theorem B3356417 : Blo 1325481 3356417 := bstep (se 2 (by rfl) ⟨1258656, by rfl⟩ : syracuseStep 3356417 = 2517313) B2517313
theorem B1988411 : Blo 1325481 1988411 := bstep (se 1 (by rfl) ⟨1491308, by rfl⟩ : syracuseStep 1988411 = 2982617) B2982617
theorem B19396421 : Blo 1325481 19396421 := bstep (se 4 (by rfl) ⟨1818414, by rfl⟩ : syracuseStep 19396421 = 3636829) B3636829
theorem B1988471 : Blo 1325481 1988471 := bstep (se 1 (by rfl) ⟨1491353, by rfl⟩ : syracuseStep 1988471 = 2982707) B2982707
theorem B1988495 : Blo 1325481 1988495 := bstep (se 1 (by rfl) ⟨1491371, by rfl⟩ : syracuseStep 1988495 = 2982743) B2982743
theorem B4478867 : Blo 1325481 4478867 := bstep (se 1 (by rfl) ⟨3359150, by rfl⟩ : syracuseStep 4478867 = 6718301) B6718301
theorem B1988537 : Blo 1325481 1988537 := bstep (se 2 (by rfl) ⟨745701, by rfl⟩ : syracuseStep 1988537 = 1491403) B1491403
theorem B25827275 : Blo 1325481 25827275 := bstep (se 1 (by rfl) ⟨19370456, by rfl⟩ : syracuseStep 25827275 = 38740913) B38740913
theorem B7174109 : Blo 1325481 7174109 := bstep (se 3 (by rfl) ⟨1345145, by rfl⟩ : syracuseStep 7174109 = 2690291) B2690291
theorem B1988615 : Blo 1325481 1988615 := bstep (se 1 (by rfl) ⟨1491461, by rfl⟩ : syracuseStep 1988615 = 2982923) B2982923
theorem B1988651 : Blo 1325481 1988651 := bstep (se 1 (by rfl) ⟨1491488, by rfl⟩ : syracuseStep 1988651 = 2982977) B2982977
theorem B1988681 : Blo 1325481 1988681 := bstep (se 2 (by rfl) ⟨745755, by rfl⟩ : syracuseStep 1988681 = 1491511) B1491511
theorem B1988795 : Blo 1325481 1988795 := bstep (se 1 (by rfl) ⟨1491596, by rfl⟩ : syracuseStep 1988795 = 2983193) B2983193
theorem B3356873 : Blo 1325481 3356873 := bstep (se 2 (by rfl) ⟨1258827, by rfl⟩ : syracuseStep 3356873 = 2517655) B2517655
theorem B1988855 : Blo 1325481 1988855 := bstep (se 1 (by rfl) ⟨1491641, by rfl⟩ : syracuseStep 1988855 = 2983283) B2983283
theorem B1988879 : Blo 1325481 1988879 := bstep (se 1 (by rfl) ⟨1491659, by rfl⟩ : syracuseStep 1988879 = 2983319) B2983319
theorem B1677611 : Blo 1325481 1677611 := bstep (se 1 (by rfl) ⟨1258208, by rfl⟩ : syracuseStep 1677611 = 2516417) B2516417
theorem B1988921 : Blo 1325481 1988921 := bstep (se 2 (by rfl) ⟨745845, by rfl⟩ : syracuseStep 1988921 = 1491691) B1491691
theorem B1988999 : Blo 1325481 1988999 := bstep (se 1 (by rfl) ⟨1491749, by rfl⟩ : syracuseStep 1988999 = 2983499) B2983499
theorem B4249991 : Blo 1325481 4249991 := bstep (se 1 (by rfl) ⟨3187493, by rfl⟩ : syracuseStep 4249991 = 6374987) B6374987
theorem B1989035 : Blo 1325481 1989035 := bstep (se 1 (by rfl) ⟨1491776, by rfl⟩ : syracuseStep 1989035 = 2983553) B2983553
theorem B1325499 : Blo 1325481 1325499 := bstep (se 1 (by rfl) ⟨994124, by rfl⟩ : syracuseStep 1325499 = 1988249) B1988249
theorem B1989065 : Blo 1325481 1989065 := bstep (se 2 (by rfl) ⟨745899, by rfl⟩ : syracuseStep 1989065 = 1491799) B1491799
theorem B1325575 : Blo 1325481 1325575 := bstep (se 1 (by rfl) ⟨994181, by rfl⟩ : syracuseStep 1325575 = 1988363) B1988363
theorem B1325583 : Blo 1325481 1325583 := bstep (se 1 (by rfl) ⟨994187, by rfl⟩ : syracuseStep 1325583 = 1988375) B1988375
theorem B3357227 : Blo 1325481 3357227 := bstep (se 1 (by rfl) ⟨2517920, by rfl⟩ : syracuseStep 3357227 = 5035841) B5035841
theorem B1325627 : Blo 1325481 1325627 := bstep (se 1 (by rfl) ⟨994220, by rfl⟩ : syracuseStep 1325627 = 1988441) B1988441
theorem B1989179 : Blo 1325481 1989179 := bstep (se 1 (by rfl) ⟨1491884, by rfl⟩ : syracuseStep 1989179 = 2983769) B2983769
theorem B36313667 : Blo 1325481 36313667 := bstep (se 1 (by rfl) ⟨27235250, by rfl⟩ : syracuseStep 36313667 = 54470501) B54470501
theorem B7551575 : Blo 1325481 7551575 := bstep (se 1 (by rfl) ⟨5663681, by rfl⟩ : syracuseStep 7551575 = 11327363) B11327363
theorem B1989239 : Blo 1325481 1989239 := bstep (se 1 (by rfl) ⟨1491929, by rfl⟩ : syracuseStep 1989239 = 2983859) B2983859
theorem B1325703 : Blo 1325481 1325703 := bstep (se 1 (by rfl) ⟨994277, by rfl⟩ : syracuseStep 1325703 = 1988555) B1988555
theorem B1325711 : Blo 1325481 1325711 := bstep (se 1 (by rfl) ⟨994283, by rfl⟩ : syracuseStep 1325711 = 1988567) B1988567
theorem B1989263 : Blo 1325481 1989263 := bstep (se 1 (by rfl) ⟨1491947, by rfl⟩ : syracuseStep 1989263 = 2983895) B2983895
theorem B1989305 : Blo 1325481 1989305 := bstep (se 2 (by rfl) ⟨745989, by rfl⟩ : syracuseStep 1989305 = 1491979) B1491979
theorem B1325755 : Blo 1325481 1325755 := bstep (se 1 (by rfl) ⟨994316, by rfl⟩ : syracuseStep 1325755 = 1988633) B1988633
theorem B13605569 : Blo 1325481 13605569 := bstep (se 2 (by rfl) ⟨5102088, by rfl⟩ : syracuseStep 13605569 = 10204177) B10204177
theorem B1325831 : Blo 1325481 1325831 := bstep (se 1 (by rfl) ⟨994373, by rfl⟩ : syracuseStep 1325831 = 1988747) B1988747
theorem B1678087 : Blo 1325481 1678087 := bstep (se 1 (by rfl) ⟨1258565, by rfl⟩ : syracuseStep 1678087 = 2517131) B2517131
theorem B1989383 : Blo 1325481 1989383 := bstep (se 1 (by rfl) ⟨1492037, by rfl⟩ : syracuseStep 1989383 = 2984075) B2984075
theorem B1325839 : Blo 1325481 1325839 := bstep (se 1 (by rfl) ⟨994379, by rfl⟩ : syracuseStep 1325839 = 1988759) B1988759
theorem B1989419 : Blo 1325481 1989419 := bstep (se 1 (by rfl) ⟨1492064, by rfl⟩ : syracuseStep 1989419 = 2984129) B2984129
theorem B1325883 : Blo 1325481 1325883 := bstep (se 1 (by rfl) ⟨994412, by rfl⟩ : syracuseStep 1325883 = 1988825) B1988825
theorem B1989449 : Blo 1325481 1989449 := bstep (se 2 (by rfl) ⟨746043, by rfl⟩ : syracuseStep 1989449 = 1492087) B1492087
theorem B1325959 : Blo 1325481 1325959 := bstep (se 1 (by rfl) ⟨994469, by rfl⟩ : syracuseStep 1325959 = 1988939) B1988939
theorem B4250503 : Blo 1325481 4250503 := bstep (se 1 (by rfl) ⟨3187877, by rfl⟩ : syracuseStep 4250503 = 6375755) B6375755
theorem B1325967 : Blo 1325481 1325967 := bstep (se 1 (by rfl) ⟨994475, by rfl⟩ : syracuseStep 1325967 = 1988951) B1988951
theorem B1416079 : Blo 1325481 1416079 := bstep (se 1 (by rfl) ⟨1062059, by rfl⟩ : syracuseStep 1416079 = 2124119) B2124119
theorem B4848569 : Blo 1325481 4848569 := bstep (se 2 (by rfl) ⟨1818213, by rfl⟩ : syracuseStep 4848569 = 3636427) B3636427
theorem B1326011 : Blo 1325481 1326011 := bstep (se 1 (by rfl) ⟨994508, by rfl⟩ : syracuseStep 1326011 = 1989017) B1989017
theorem B1989563 : Blo 1325481 1989563 := bstep (se 1 (by rfl) ⟨1492172, by rfl⟩ : syracuseStep 1989563 = 2984345) B2984345
theorem B1989623 : Blo 1325481 1989623 := bstep (se 1 (by rfl) ⟨1492217, by rfl⟩ : syracuseStep 1989623 = 2984435) B2984435
theorem B1326087 : Blo 1325481 1326087 := bstep (se 1 (by rfl) ⟨994565, by rfl⟩ : syracuseStep 1326087 = 1989131) B1989131
theorem B1326095 : Blo 1325481 1326095 := bstep (se 1 (by rfl) ⟨994571, by rfl⟩ : syracuseStep 1326095 = 1989143) B1989143
theorem B1989647 : Blo 1325481 1989647 := bstep (se 1 (by rfl) ⟨1492235, by rfl⟩ : syracuseStep 1989647 = 2984471) B2984471
theorem B1989689 : Blo 1325481 1989689 := bstep (se 2 (by rfl) ⟨746133, by rfl⟩ : syracuseStep 1989689 = 1492267) B1492267
theorem B1326139 : Blo 1325481 1326139 := bstep (se 1 (by rfl) ⟨994604, by rfl⟩ : syracuseStep 1326139 = 1989209) B1989209
theorem B21503063 : Blo 1325481 21503063 := bstep (se 1 (by rfl) ⟨16127297, by rfl⟩ : syracuseStep 21503063 = 32254595) B32254595
theorem B1326215 : Blo 1325481 1326215 := bstep (se 1 (by rfl) ⟨994661, by rfl⟩ : syracuseStep 1326215 = 1989323) B1989323
theorem B1989767 : Blo 1325481 1989767 := bstep (se 1 (by rfl) ⟨1492325, by rfl⟩ : syracuseStep 1989767 = 2984651) B2984651
theorem B1326223 : Blo 1325481 1326223 := bstep (se 1 (by rfl) ⟨994667, by rfl⟩ : syracuseStep 1326223 = 1989335) B1989335
theorem B1989803 : Blo 1325481 1989803 := bstep (se 1 (by rfl) ⟨1492352, by rfl⟩ : syracuseStep 1989803 = 2984705) B2984705
theorem B3775673 : Blo 1325481 3775673 := bstep (se 2 (by rfl) ⟨1415877, by rfl⟩ : syracuseStep 3775673 = 2831755) B2831755
theorem B1326267 : Blo 1325481 1326267 := bstep (se 1 (by rfl) ⟨994700, by rfl⟩ : syracuseStep 1326267 = 1989401) B1989401
theorem B1989833 : Blo 1325481 1989833 := bstep (se 2 (by rfl) ⟨746187, by rfl⟩ : syracuseStep 1989833 = 1492375) B1492375
theorem B1678583 : Blo 1325481 1678583 := bstep (se 1 (by rfl) ⟨1258937, by rfl⟩ : syracuseStep 1678583 = 2517875) B2517875
theorem B1326343 : Blo 1325481 1326343 := bstep (se 1 (by rfl) ⟨994757, by rfl⟩ : syracuseStep 1326343 = 1989515) B1989515
theorem B1326351 : Blo 1325481 1326351 := bstep (se 1 (by rfl) ⟨994763, by rfl⟩ : syracuseStep 1326351 = 1989527) B1989527
theorem B1326395 : Blo 1325481 1326395 := bstep (se 1 (by rfl) ⟨994796, by rfl⟩ : syracuseStep 1326395 = 1989593) B1989593
theorem B1989947 : Blo 1325481 1989947 := bstep (se 1 (by rfl) ⟨1492460, by rfl⟩ : syracuseStep 1989947 = 2984921) B2984921
theorem B1990007 : Blo 1325481 1990007 := bstep (se 1 (by rfl) ⟨1492505, by rfl⟩ : syracuseStep 1990007 = 2985011) B2985011
theorem B1326471 : Blo 1325481 1326471 := bstep (se 1 (by rfl) ⟨994853, by rfl⟩ : syracuseStep 1326471 = 1989707) B1989707
theorem B1678735 : Blo 1325481 1678735 := bstep (se 1 (by rfl) ⟨1259051, by rfl⟩ : syracuseStep 1678735 = 2518103) B2518103
theorem B1326479 : Blo 1325481 1326479 := bstep (se 1 (by rfl) ⟨994859, by rfl⟩ : syracuseStep 1326479 = 1989719) B1989719
theorem B1990031 : Blo 1325481 1990031 := bstep (se 1 (by rfl) ⟨1492523, by rfl⟩ : syracuseStep 1990031 = 2985047) B2985047
theorem B28663217 : Blo 1325481 28663217 := bstep (se 2 (by rfl) ⟨10748706, by rfl⟩ : syracuseStep 28663217 = 21497413) B21497413
theorem B1990073 : Blo 1325481 1990073 := bstep (se 2 (by rfl) ⟨746277, by rfl⟩ : syracuseStep 1990073 = 1492555) B1492555
theorem B5037497 : Blo 1325481 5037497 := bstep (se 2 (by rfl) ⟨1889061, by rfl⟩ : syracuseStep 5037497 = 3778123) B3778123
theorem B1326523 : Blo 1325481 1326523 := bstep (se 1 (by rfl) ⟨994892, by rfl⟩ : syracuseStep 1326523 = 1989785) B1989785
theorem B1326599 : Blo 1325481 1326599 := bstep (se 1 (by rfl) ⟨994949, by rfl⟩ : syracuseStep 1326599 = 1989899) B1989899
theorem B1990151 : Blo 1325481 1990151 := bstep (se 1 (by rfl) ⟨1492613, by rfl⟩ : syracuseStep 1990151 = 2985227) B2985227
theorem B3358219 : Blo 1325481 3358219 := bstep (se 1 (by rfl) ⟨2518664, by rfl⟩ : syracuseStep 3358219 = 5037329) B5037329
theorem B1326607 : Blo 1325481 1326607 := bstep (se 1 (by rfl) ⟨994955, by rfl⟩ : syracuseStep 1326607 = 1989911) B1989911
theorem B1990187 : Blo 1325481 1990187 := bstep (se 1 (by rfl) ⟨1492640, by rfl⟩ : syracuseStep 1990187 = 2985281) B2985281
theorem B1793593 : Blo 1325481 1793593 := bstep (se 2 (by rfl) ⟨672597, by rfl⟩ : syracuseStep 1793593 = 1345195) B1345195
theorem B1678907 : Blo 1325481 1678907 := bstep (se 1 (by rfl) ⟨1259180, by rfl⟩ : syracuseStep 1678907 = 2518361) B2518361
theorem B1326651 : Blo 1325481 1326651 := bstep (se 1 (by rfl) ⟨994988, by rfl⟩ : syracuseStep 1326651 = 1989977) B1989977
theorem B1990217 : Blo 1325481 1990217 := bstep (se 2 (by rfl) ⟨746331, by rfl⟩ : syracuseStep 1990217 = 1492663) B1492663
theorem B3186263 : Blo 1325481 3186263 := bstep (se 1 (by rfl) ⟨2389697, by rfl⟩ : syracuseStep 3186263 = 4779395) B4779395
theorem B1326727 : Blo 1325481 1326727 := bstep (se 1 (by rfl) ⟨995045, by rfl⟩ : syracuseStep 1326727 = 1990091) B1990091
theorem B1326735 : Blo 1325481 1326735 := bstep (se 1 (by rfl) ⟨995051, by rfl⟩ : syracuseStep 1326735 = 1990103) B1990103
theorem B3358361 : Blo 1325481 3358361 := bstep (se 2 (by rfl) ⟨1259385, by rfl⟩ : syracuseStep 3358361 = 2518771) B2518771
theorem B1326779 : Blo 1325481 1326779 := bstep (se 1 (by rfl) ⟨995084, by rfl⟩ : syracuseStep 1326779 = 1990169) B1990169
theorem B1990331 : Blo 1325481 1990331 := bstep (se 1 (by rfl) ⟨1492748, by rfl⟩ : syracuseStep 1990331 = 2985497) B2985497
theorem B1990391 : Blo 1325481 1990391 := bstep (se 1 (by rfl) ⟨1492793, by rfl⟩ : syracuseStep 1990391 = 2985587) B2985587
theorem B1326855 : Blo 1325481 1326855 := bstep (se 1 (by rfl) ⟨995141, by rfl⟩ : syracuseStep 1326855 = 1990283) B1990283
theorem B1326863 : Blo 1325481 1326863 := bstep (se 1 (by rfl) ⟨995147, by rfl⟩ : syracuseStep 1326863 = 1990295) B1990295
theorem B1990415 : Blo 1325481 1990415 := bstep (se 1 (by rfl) ⟨1492811, by rfl⟩ : syracuseStep 1990415 = 2985623) B2985623
theorem B98148145 : Blo 1325481 98148145 := bstep (se 2 (by rfl) ⟨36805554, by rfl⟩ : syracuseStep 98148145 = 73611109) B73611109
theorem B1990457 : Blo 1325481 1990457 := bstep (se 2 (by rfl) ⟨746421, by rfl⟩ : syracuseStep 1990457 = 1492843) B1492843
theorem B3358523 : Blo 1325481 3358523 := bstep (se 1 (by rfl) ⟨2518892, by rfl⟩ : syracuseStep 3358523 = 5037785) B5037785
theorem B1326907 : Blo 1325481 1326907 := bstep (se 1 (by rfl) ⟨995180, by rfl⟩ : syracuseStep 1326907 = 1990361) B1990361
theorem B1326983 : Blo 1325481 1326983 := bstep (se 1 (by rfl) ⟨995237, by rfl⟩ : syracuseStep 1326983 = 1990475) B1990475
theorem B1990535 : Blo 1325481 1990535 := bstep (se 1 (by rfl) ⟨1492901, by rfl⟩ : syracuseStep 1990535 = 2985803) B2985803
theorem B1326991 : Blo 1325481 1326991 := bstep (se 1 (by rfl) ⟨995243, by rfl⟩ : syracuseStep 1326991 = 1990487) B1990487
theorem B6717329 : Blo 1325481 6717329 := bstep (se 2 (by rfl) ⟨2518998, by rfl⟩ : syracuseStep 6717329 = 5037997) B5037997
theorem B1990571 : Blo 1325481 1990571 := bstep (se 1 (by rfl) ⟨1492928, by rfl⟩ : syracuseStep 1990571 = 2985857) B2985857
theorem B1327035 : Blo 1325481 1327035 := bstep (se 1 (by rfl) ⟨995276, by rfl⟩ : syracuseStep 1327035 = 1990553) B1990553
theorem B1990601 : Blo 1325481 1990601 := bstep (se 2 (by rfl) ⟨746475, by rfl⟩ : syracuseStep 1990601 = 1492951) B1492951
theorem B4848841 : Blo 1325481 4848841 := bstep (se 2 (by rfl) ⟨1818315, by rfl⟩ : syracuseStep 4848841 = 3636631) B3636631
theorem B10067975 : Blo 1325481 10067975 := bstep (se 1 (by rfl) ⟨7550981, by rfl⟩ : syracuseStep 10067975 = 15101963) B15101963
theorem B1327143 : Blo 1325481 1327143 := bstep (se 1 (by rfl) ⟨995357, by rfl⟩ : syracuseStep 1327143 = 1990715) B1990715
theorem B2834489 : Blo 1325481 2834489 := bstep (se 2 (by rfl) ⟨1062933, by rfl⟩ : syracuseStep 2834489 = 2125867) B2125867
theorem B10076237 : Blo 1325481 10076237 := bstep (se 3 (by rfl) ⟨1889294, by rfl⟩ : syracuseStep 10076237 = 3778589) B3778589
theorem B1327183 : Blo 1325481 1327183 := bstep (se 1 (by rfl) ⟨995387, by rfl⟩ : syracuseStep 1327183 = 1990775) B1990775
theorem B14352461 : Blo 1325481 14352461 := bstep (se 3 (by rfl) ⟨2691086, by rfl⟩ : syracuseStep 14352461 = 5382173) B5382173
theorem B1327199 : Blo 1325481 1327199 := bstep (se 1 (by rfl) ⟨995399, by rfl⟩ : syracuseStep 1327199 = 1990799) B1990799
theorem B1327227 : Blo 1325481 1327227 := bstep (se 1 (by rfl) ⟨995420, by rfl⟩ : syracuseStep 1327227 = 1990841) B1990841
theorem B1327279 : Blo 1325481 1327279 := bstep (se 1 (by rfl) ⟨995459, by rfl⟩ : syracuseStep 1327279 = 1990919) B1990919
theorem B1327303 : Blo 1325481 1327303 := bstep (se 1 (by rfl) ⟨995477, by rfl⟩ : syracuseStep 1327303 = 1990955) B1990955
theorem B1327323 : Blo 1325481 1327323 := bstep (se 1 (by rfl) ⟨995492, by rfl⟩ : syracuseStep 1327323 = 1990985) B1990985
theorem B1327399 : Blo 1325481 1327399 := bstep (se 1 (by rfl) ⟨995549, by rfl⟩ : syracuseStep 1327399 = 1991099) B1991099
theorem B16998731 : Blo 1325481 16998731 := bstep (se 1 (by rfl) ⟨12749048, by rfl⟩ : syracuseStep 16998731 = 25498097) B25498097
theorem B1327439 : Blo 1325481 1327439 := bstep (se 1 (by rfl) ⟨995579, by rfl⟩ : syracuseStep 1327439 = 1991159) B1991159
theorem B1491295 : Blo 1325481 1491295 := bstep (se 1 (by rfl) ⟨1118471, by rfl⟩ : syracuseStep 1491295 = 2236943) B2236943
theorem B1327455 : Blo 1325481 1327455 := bstep (se 1 (by rfl) ⟨995591, by rfl⟩ : syracuseStep 1327455 = 1991183) B1991183
theorem B17228161 : Blo 1325481 17228161 := bstep (se 2 (by rfl) ⟨6460560, by rfl⟩ : syracuseStep 17228161 = 12921121) B12921121
theorem B2834831 : Blo 1325481 2834831 := bstep (se 1 (by rfl) ⟨2126123, by rfl⟩ : syracuseStep 2834831 = 4252247) B4252247
theorem B64545173 : Blo 1325481 64545173 := bstep (se 6 (by rfl) ⟨1512777, by rfl⟩ : syracuseStep 64545173 = 3025555) B3025555
theorem B1991087 : Blo 1325481 1991087 := bstep (se 1 (by rfl) ⟨1493315, by rfl⟩ : syracuseStep 1991087 = 2986631) B2986631
theorem B2236855 : Blo 1325481 2236855 := bstep (se 1 (by rfl) ⟨1677641, by rfl⟩ : syracuseStep 2236855 = 3355283) B3355283
theorem B10068461 : Blo 1325481 10068461 := bstep (se 3 (by rfl) ⟨1887836, by rfl⟩ : syracuseStep 10068461 = 3775673) B3775673
theorem B1991177 : Blo 1325481 1991177 := bstep (se 2 (by rfl) ⟨746691, by rfl⟩ : syracuseStep 1991177 = 1493383) B1493383
theorem B6717977 : Blo 1325481 6717977 := bstep (se 2 (by rfl) ⟨2519241, by rfl⟩ : syracuseStep 6717977 = 5038483) B5038483
theorem B1991207 : Blo 1325481 1991207 := bstep (se 1 (by rfl) ⟨1493405, by rfl⟩ : syracuseStep 1991207 = 2986811) B2986811
theorem B8495675 : Blo 1325481 8495675 := bstep (se 1 (by rfl) ⟨6371756, by rfl⟩ : syracuseStep 8495675 = 12743513) B12743513
theorem B54485621 : Blo 1325481 54485621 := bstep (se 5 (by rfl) ⟨2554013, by rfl⟩ : syracuseStep 54485621 = 5108027) B5108027
theorem B2237051 : Blo 1325481 2237051 := bstep (se 1 (by rfl) ⟨1677788, by rfl⟩ : syracuseStep 2237051 = 3355577) B3355577
theorem B2982599 : Blo 1325481 2982599 := bstep (se 1 (by rfl) ⟨2236949, by rfl⟩ : syracuseStep 2982599 = 4473899) B4473899
theorem B1491655 : Blo 1325481 1491655 := bstep (se 1 (by rfl) ⟨1118741, by rfl⟩ : syracuseStep 1491655 = 2237483) B2237483
theorem B4473629 : Blo 1325481 4473629 := bstep (se 3 (by rfl) ⟨838805, by rfl⟩ : syracuseStep 4473629 = 1677611) B1677611
theorem B5038955 : Blo 1325481 5038955 := bstep (se 1 (by rfl) ⟨3779216, by rfl⟩ : syracuseStep 5038955 = 7558433) B7558433
theorem B2237449 : Blo 1325481 2237449 := bstep (se 2 (by rfl) ⟨839043, by rfl⟩ : syracuseStep 2237449 = 1678087) B1678087
theorem B4031545 : Blo 1325481 4031545 := bstep (se 2 (by rfl) ⟨1511829, by rfl⟩ : syracuseStep 4031545 = 3023659) B3023659
theorem B2237611 : Blo 1325481 2237611 := bstep (se 1 (by rfl) ⟨1678208, by rfl⟩ : syracuseStep 2237611 = 3356417) B3356417
theorem B4425047 : Blo 1325481 4425047 := bstep (se 1 (by rfl) ⟨3318785, by rfl⟩ : syracuseStep 4425047 = 6637571) B6637571
theorem B3360143 : Blo 1325481 3360143 := bstep (se 1 (by rfl) ⟨2520107, by rfl⟩ : syracuseStep 3360143 = 5040215) B5040215
theorem B4474331 : Blo 1325481 4474331 := bstep (se 1 (by rfl) ⟨3355748, by rfl⟩ : syracuseStep 4474331 = 6711497) B6711497
theorem B2237915 : Blo 1325481 2237915 := bstep (se 1 (by rfl) ⟨1678436, by rfl⟩ : syracuseStep 2237915 = 3356873) B3356873
theorem B2983463 : Blo 1325481 2983463 := bstep (se 1 (by rfl) ⟨2237597, by rfl⟩ : syracuseStep 2983463 = 4475195) B4475195
theorem B1492519 : Blo 1325481 1492519 := bstep (se 1 (by rfl) ⟨1119389, by rfl⟩ : syracuseStep 1492519 = 2238779) B2238779
theorem B8496701 : Blo 1325481 8496701 := bstep (se 3 (by rfl) ⟨1593131, by rfl⟩ : syracuseStep 8496701 = 3186263) B3186263
theorem B2238151 : Blo 1325481 2238151 := bstep (se 1 (by rfl) ⟨1678613, by rfl⟩ : syracuseStep 2238151 = 3357227) B3357227
theorem B24209111 : Blo 1325481 24209111 := bstep (se 1 (by rfl) ⟨18156833, by rfl⟩ : syracuseStep 24209111 = 36313667) B36313667
theorem B7554809 : Blo 1325481 7554809 := bstep (se 2 (by rfl) ⟨2833053, by rfl⟩ : syracuseStep 7554809 = 5666107) B5666107
theorem B9070379 : Blo 1325481 9070379 := bstep (se 1 (by rfl) ⟨6802784, by rfl⟩ : syracuseStep 9070379 = 13605569) B13605569
theorem B2238313 : Blo 1325481 2238313 := bstep (se 2 (by rfl) ⟨839367, by rfl⟩ : syracuseStep 2238313 = 1678735) B1678735
theorem B2983787 : Blo 1325481 2983787 := bstep (se 1 (by rfl) ⟨2237840, by rfl⟩ : syracuseStep 2983787 = 4475681) B4475681
theorem B2983841 : Blo 1325481 2983841 := bstep (se 2 (by rfl) ⟨1118940, by rfl⟩ : syracuseStep 2983841 = 2237881) B2237881
theorem B4778041 : Blo 1325481 4778041 := bstep (se 2 (by rfl) ⟨1791765, by rfl⟩ : syracuseStep 4778041 = 3583531) B3583531
theorem B2017403 : Blo 1325481 2017403 := bstep (se 1 (by rfl) ⟨1513052, by rfl⟩ : syracuseStep 2017403 = 3026105) B3026105
theorem B4475033 : Blo 1325481 4475033 := bstep (se 2 (by rfl) ⟨1678137, by rfl⟩ : syracuseStep 4475033 = 3356275) B3356275
theorem B2984183 : Blo 1325481 2984183 := bstep (se 1 (by rfl) ⟨2238137, by rfl⟩ : syracuseStep 2984183 = 4476275) B4476275
theorem B4778345 : Blo 1325481 4778345 := bstep (se 2 (by rfl) ⟨1791879, by rfl⟩ : syracuseStep 4778345 = 3583759) B3583759
theorem B10070405 : Blo 1325481 10070405 := bstep (se 4 (by rfl) ⟨944100, by rfl⟩ : syracuseStep 10070405 = 1888201) B1888201
theorem B2238907 : Blo 1325481 2238907 := bstep (se 1 (by rfl) ⟨1679180, by rfl⟩ : syracuseStep 2238907 = 3358361) B3358361
theorem B10078667 : Blo 1325481 10078667 := bstep (se 1 (by rfl) ⟨7559000, by rfl⟩ : syracuseStep 10078667 = 15118001) B15118001
theorem B2239015 : Blo 1325481 2239015 := bstep (se 1 (by rfl) ⟨1679261, by rfl⟩ : syracuseStep 2239015 = 3358523) B3358523
theorem B2984777 : Blo 1325481 2984777 := bstep (se 2 (by rfl) ⟨1119291, by rfl⟩ : syracuseStep 2984777 = 2238583) B2238583
theorem B10070891 : Blo 1325481 10070891 := bstep (se 1 (by rfl) ⟨7553168, by rfl⟩ : syracuseStep 10070891 = 15106337) B15106337
theorem B2239339 : Blo 1325481 2239339 := bstep (se 1 (by rfl) ⟨1679504, by rfl⟩ : syracuseStep 2239339 = 3359009) B3359009
theorem B9071635 : Blo 1325481 9071635 := bstep (se 1 (by rfl) ⟨6803726, by rfl⟩ : syracuseStep 9071635 = 13607453) B13607453
theorem B7556267 : Blo 1325481 7556267 := bstep (se 1 (by rfl) ⟨5667200, by rfl⟩ : syracuseStep 7556267 = 11334401) B11334401
theorem B4476221 : Blo 1325481 4476221 := bstep (se 3 (by rfl) ⟨839291, by rfl⟩ : syracuseStep 4476221 = 1678583) B1678583
theorem B2985569 : Blo 1325481 2985569 := bstep (se 2 (by rfl) ⟨1119588, by rfl⟩ : syracuseStep 2985569 = 2239177) B2239177
theorem B6712955 : Blo 1325481 6712955 := bstep (se 1 (by rfl) ⟨5034716, by rfl⟩ : syracuseStep 6712955 = 10069433) B10069433
theorem B7663243 : Blo 1325481 7663243 := bstep (se 1 (by rfl) ⟨5747432, by rfl⟩ : syracuseStep 7663243 = 11494865) B11494865
theorem B9555677 : Blo 1325481 9555677 := bstep (se 3 (by rfl) ⟨1791689, by rfl⟩ : syracuseStep 9555677 = 3583379) B3583379
theorem B2125559 : Blo 1325481 2125559 := bstep (se 1 (by rfl) ⟨1594169, by rfl⟩ : syracuseStep 2125559 = 3188339) B3188339
theorem B1888105 : Blo 1325481 1888105 := bstep (se 2 (by rfl) ⟨708039, by rfl⟩ : syracuseStep 1888105 = 1416079) B1416079
theorem B12930947 : Blo 1325481 12930947 := bstep (se 1 (by rfl) ⟨9698210, by rfl⟩ : syracuseStep 12930947 = 19396421) B19396421
theorem B2985911 : Blo 1325481 2985911 := bstep (se 1 (by rfl) ⟨2239433, by rfl⟩ : syracuseStep 2985911 = 4478867) B4478867
theorem B5664775 : Blo 1325481 5664775 := bstep (se 1 (by rfl) ⟨4248581, by rfl⟩ : syracuseStep 5664775 = 8497163) B8497163
theorem B3026963 : Blo 1325481 3026963 := bstep (se 1 (by rfl) ⟨2270222, by rfl⟩ : syracuseStep 3026963 = 4540445) B4540445
theorem B4427929 : Blo 1325481 4427929 := bstep (se 2 (by rfl) ⟨1660473, by rfl⟩ : syracuseStep 4427929 = 3320947) B3320947
theorem B4477085 : Blo 1325481 4477085 := bstep (se 3 (by rfl) ⟨839453, by rfl⟩ : syracuseStep 4477085 = 1678907) B1678907
theorem B5034383 : Blo 1325481 5034383 := bstep (se 1 (by rfl) ⟨3775787, by rfl⟩ : syracuseStep 5034383 = 7551575) B7551575
theorem B2519515 : Blo 1325481 2519515 := bstep (se 1 (by rfl) ⟨1889636, by rfl⟩ : syracuseStep 2519515 = 3779273) B3779273
theorem B3633673 : Blo 1325481 3633673 := bstep (se 2 (by rfl) ⟨1362627, by rfl⟩ : syracuseStep 3633673 = 2725255) B2725255
theorem B2519561 : Blo 1325481 2519561 := bstep (se 2 (by rfl) ⟨944835, by rfl⟩ : syracuseStep 2519561 = 1889671) B1889671
theorem B2986505 : Blo 1325481 2986505 := bstep (se 2 (by rfl) ⟨1119939, by rfl⟩ : syracuseStep 2986505 = 2239879) B2239879
theorem B3584537 : Blo 1325481 3584537 := bstep (se 2 (by rfl) ⟨1344201, by rfl⟩ : syracuseStep 3584537 = 2688403) B2688403
theorem B4780577 : Blo 1325481 4780577 := bstep (se 2 (by rfl) ⟨1792716, by rfl⟩ : syracuseStep 4780577 = 3585433) B3585433
theorem B4035169 : Blo 1325481 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B1913467 : Blo 1325481 1913467 := bstep (se 1 (by rfl) ⟨1435100, by rfl⟩ : syracuseStep 1913467 = 2870201) B2870201
theorem B3232379 : Blo 1325481 3232379 := bstep (se 1 (by rfl) ⟨2424284, by rfl⟩ : syracuseStep 3232379 = 4848569) B4848569
theorem B4477625 : Blo 1325481 4477625 := bstep (se 2 (by rfl) ⟨1679109, by rfl⟩ : syracuseStep 4477625 = 3358219) B3358219
theorem B10072835 : Blo 1325481 10072835 := bstep (se 1 (by rfl) ⟨7554626, by rfl⟩ : syracuseStep 10072835 = 15109253) B15109253
theorem B3355465 : Blo 1325481 3355465 := bstep (se 2 (by rfl) ⟨1258299, by rfl⟩ : syracuseStep 3355465 = 2516599) B2516599
theorem B2519903 : Blo 1325481 2519903 := bstep (se 1 (by rfl) ⟨1889927, by rfl⟩ : syracuseStep 2519903 = 3779855) B3779855
theorem B3830689 : Blo 1325481 3830689 := bstep (se 2 (by rfl) ⟨1436508, by rfl⟩ : syracuseStep 3830689 = 2873017) B2873017
theorem B19108811 : Blo 1325481 19108811 := bstep (se 1 (by rfl) ⟨14331608, by rfl⟩ : syracuseStep 19108811 = 28663217) B28663217
theorem B19928065 : Blo 1325481 19928065 := bstep (se 2 (by rfl) ⟨7473024, by rfl⟩ : syracuseStep 19928065 = 14946049) B14946049
theorem B130864193 : Blo 1325481 130864193 := bstep (se 2 (by rfl) ⟨49074072, by rfl⟩ : syracuseStep 130864193 = 98148145) B98148145
theorem B4781227 : Blo 1325481 4781227 := bstep (se 1 (by rfl) ⟨3585920, by rfl⟩ : syracuseStep 4781227 = 7171841) B7171841
theorem B10204355 : Blo 1325481 10204355 := bstep (se 1 (by rfl) ⟨7653266, by rfl⟩ : syracuseStep 10204355 = 15306533) B15306533
theorem B4478219 : Blo 1325481 4478219 := bstep (se 1 (by rfl) ⟨3358664, by rfl⟩ : syracuseStep 4478219 = 6717329) B6717329
theorem B4478489 : Blo 1325481 4478489 := bstep (se 2 (by rfl) ⟨1679433, by rfl⟩ : syracuseStep 4478489 = 3358867) B3358867
theorem B5035553 : Blo 1325481 5035553 := bstep (se 2 (by rfl) ⟨1888332, by rfl⟩ : syracuseStep 5035553 = 3776665) B3776665
theorem B2389583 : Blo 1325481 2389583 := bstep (se 1 (by rfl) ⟨1792187, by rfl⟩ : syracuseStep 2389583 = 3584375) B3584375
theorem B6370913 : Blo 1325481 6370913 := bstep (se 2 (by rfl) ⟨2389092, by rfl⟩ : syracuseStep 6370913 = 4778185) B4778185
theorem B4249223 : Blo 1325481 4249223 := bstep (se 1 (by rfl) ⟨3186917, by rfl⟩ : syracuseStep 4249223 = 6373835) B6373835
theorem B4249273 : Blo 1325481 4249273 := bstep (se 2 (by rfl) ⟨1593477, by rfl⟩ : syracuseStep 4249273 = 3186955) B3186955
theorem B24188615 : Blo 1325481 24188615 := bstep (se 1 (by rfl) ⟨18141461, by rfl⟩ : syracuseStep 24188615 = 36282923) B36282923
theorem B10761943 : Blo 1325481 10761943 := bstep (se 1 (by rfl) ⟨8071457, by rfl⟩ : syracuseStep 10761943 = 16142915) B16142915
theorem B1988345 : Blo 1325481 1988345 := bstep (se 2 (by rfl) ⟨745629, by rfl⟩ : syracuseStep 1988345 = 1491259) B1491259
theorem B6371065 : Blo 1325481 6371065 := bstep (se 2 (by rfl) ⟨2389149, by rfl⟩ : syracuseStep 6371065 = 4778299) B4778299
theorem B1988447 : Blo 1325481 1988447 := bstep (se 1 (by rfl) ⟨1491335, by rfl⟩ : syracuseStep 1988447 = 2982671) B2982671
theorem B5035871 : Blo 1325481 5035871 := bstep (se 1 (by rfl) ⟨3776903, by rfl⟩ : syracuseStep 5035871 = 7553807) B7553807
theorem B1988459 : Blo 1325481 1988459 := bstep (se 1 (by rfl) ⟨1491344, by rfl⟩ : syracuseStep 1988459 = 2982689) B2982689
theorem B8501111 : Blo 1325481 8501111 := bstep (se 1 (by rfl) ⟨6375833, by rfl⟩ : syracuseStep 8501111 = 12751667) B12751667
theorem B3356599 : Blo 1325481 3356599 := bstep (se 1 (by rfl) ⟨2517449, by rfl⟩ : syracuseStep 3356599 = 5034899) B5034899
theorem B2389943 : Blo 1325481 2389943 := bstep (se 1 (by rfl) ⟨1792457, by rfl⟩ : syracuseStep 2389943 = 3584915) B3584915
theorem B5036039 : Blo 1325481 5036039 := bstep (se 1 (by rfl) ⟨3777029, by rfl⟩ : syracuseStep 5036039 = 7554059) B7554059
theorem B7559183 : Blo 1325481 7559183 := bstep (se 1 (by rfl) ⟨5669387, by rfl⟩ : syracuseStep 7559183 = 11338775) B11338775
theorem B8493113 : Blo 1325481 8493113 := bstep (se 2 (by rfl) ⟨3184917, by rfl⟩ : syracuseStep 8493113 = 6369835) B6369835
theorem B1988687 : Blo 1325481 1988687 := bstep (se 1 (by rfl) ⟨1491515, by rfl⟩ : syracuseStep 1988687 = 2983031) B2983031
theorem B2390095 : Blo 1325481 2390095 := bstep (se 1 (by rfl) ⟨1792571, by rfl⟩ : syracuseStep 2390095 = 3585143) B3585143
theorem B5527723 : Blo 1325481 5527723 := bstep (se 1 (by rfl) ⟨4145792, by rfl⟩ : syracuseStep 5527723 = 8291585) B8291585
theorem B1988807 : Blo 1325481 1988807 := bstep (se 1 (by rfl) ⟨1491605, by rfl⟩ : syracuseStep 1988807 = 2983211) B2983211
theorem B17217773 : Blo 1325481 17217773 := bstep (se 3 (by rfl) ⟨3228332, by rfl⟩ : syracuseStep 17217773 = 6456665) B6456665
theorem B6715709 : Blo 1325481 6715709 := bstep (se 3 (by rfl) ⟨1259195, by rfl⟩ : syracuseStep 6715709 = 2518391) B2518391
theorem B1988969 : Blo 1325481 1988969 := bstep (se 2 (by rfl) ⟨745863, by rfl⟩ : syracuseStep 1988969 = 1491727) B1491727
theorem B25860485 : Blo 1325481 25860485 := bstep (se 4 (by rfl) ⟨2424420, by rfl⟩ : syracuseStep 25860485 = 4848841) B4848841
theorem B1325487 : Blo 1325481 1325487 := bstep (se 1 (by rfl) ⟨994115, by rfl⟩ : syracuseStep 1325487 = 1988231) B1988231
theorem B1989047 : Blo 1325481 1989047 := bstep (se 1 (by rfl) ⟨1491785, by rfl⟩ : syracuseStep 1989047 = 2983571) B2983571
theorem B1325511 : Blo 1325481 1325511 := bstep (se 1 (by rfl) ⟨994133, by rfl⟩ : syracuseStep 1325511 = 1988267) B1988267
theorem B1325531 : Blo 1325481 1325531 := bstep (se 1 (by rfl) ⟨994148, by rfl⟩ : syracuseStep 1325531 = 1988297) B1988297
theorem B1989083 : Blo 1325481 1989083 := bstep (se 1 (by rfl) ⟨1491812, by rfl⟩ : syracuseStep 1989083 = 2983625) B2983625
theorem B5036525 : Blo 1325481 5036525 := bstep (se 3 (by rfl) ⟨944348, by rfl⟩ : syracuseStep 5036525 = 1888697) B1888697
theorem B5667337 : Blo 1325481 5667337 := bstep (se 2 (by rfl) ⟨2125251, by rfl⟩ : syracuseStep 5667337 = 4250503) B4250503
theorem B1325607 : Blo 1325481 1325607 := bstep (se 1 (by rfl) ⟨994205, by rfl⟩ : syracuseStep 1325607 = 1988411) B1988411
theorem B1325647 : Blo 1325481 1325647 := bstep (se 1 (by rfl) ⟨994235, by rfl⟩ : syracuseStep 1325647 = 1988471) B1988471
theorem B1325663 : Blo 1325481 1325663 := bstep (se 1 (by rfl) ⟨994247, by rfl⟩ : syracuseStep 1325663 = 1988495) B1988495
theorem B1325691 : Blo 1325481 1325691 := bstep (se 1 (by rfl) ⟨994268, by rfl⟩ : syracuseStep 1325691 = 1988537) B1988537
theorem B17218183 : Blo 1325481 17218183 := bstep (se 1 (by rfl) ⟨12913637, by rfl⟩ : syracuseStep 17218183 = 25827275) B25827275
theorem B4479623 : Blo 1325481 4479623 := bstep (se 1 (by rfl) ⟨3359717, by rfl⟩ : syracuseStep 4479623 = 6719435) B6719435
theorem B4782739 : Blo 1325481 4782739 := bstep (se 1 (by rfl) ⟨3587054, by rfl⟩ : syracuseStep 4782739 = 7174109) B7174109
theorem B1325743 : Blo 1325481 1325743 := bstep (se 1 (by rfl) ⟨994307, by rfl⟩ : syracuseStep 1325743 = 1988615) B1988615
theorem B4479677 : Blo 1325481 4479677 := bstep (se 3 (by rfl) ⟨839939, by rfl⟩ : syracuseStep 4479677 = 1679879) B1679879
theorem B1325767 : Blo 1325481 1325767 := bstep (se 1 (by rfl) ⟨994325, by rfl⟩ : syracuseStep 1325767 = 1988651) B1988651
theorem B7559891 : Blo 1325481 7559891 := bstep (se 1 (by rfl) ⟨5669918, by rfl⟩ : syracuseStep 7559891 = 11339837) B11339837
theorem B1325787 : Blo 1325481 1325787 := bstep (se 1 (by rfl) ⟨994340, by rfl⟩ : syracuseStep 1325787 = 1988681) B1988681
theorem B1325863 : Blo 1325481 1325863 := bstep (se 1 (by rfl) ⟨994397, by rfl⟩ : syracuseStep 1325863 = 1988795) B1988795
theorem B5036843 : Blo 1325481 5036843 := bstep (se 1 (by rfl) ⟨3777632, by rfl⟩ : syracuseStep 5036843 = 7555265) B7555265
theorem B1325903 : Blo 1325481 1325903 := bstep (se 1 (by rfl) ⟨994427, by rfl⟩ : syracuseStep 1325903 = 1988855) B1988855
theorem B1325919 : Blo 1325481 1325919 := bstep (se 1 (by rfl) ⟨994439, by rfl⟩ : syracuseStep 1325919 = 1988879) B1988879
theorem B4479839 : Blo 1325481 4479839 := bstep (se 1 (by rfl) ⟨3359879, by rfl⟩ : syracuseStep 4479839 = 6719759) B6719759
theorem B1325947 : Blo 1325481 1325947 := bstep (se 1 (by rfl) ⟨994460, by rfl⟩ : syracuseStep 1325947 = 1988921) B1988921
theorem B1325999 : Blo 1325481 1325999 := bstep (se 1 (by rfl) ⟨994499, by rfl⟩ : syracuseStep 1325999 = 1988999) B1988999
theorem B1989551 : Blo 1325481 1989551 := bstep (se 1 (by rfl) ⟨1492163, by rfl⟩ : syracuseStep 1989551 = 2984327) B2984327
theorem B2833327 : Blo 1325481 2833327 := bstep (se 1 (by rfl) ⟨2124995, by rfl⟩ : syracuseStep 2833327 = 4249991) B4249991
theorem B1326023 : Blo 1325481 1326023 := bstep (se 1 (by rfl) ⟨994517, by rfl⟩ : syracuseStep 1326023 = 1989035) B1989035
theorem B1326043 : Blo 1325481 1326043 := bstep (se 1 (by rfl) ⟨994532, by rfl⟩ : syracuseStep 1326043 = 1989065) B1989065
theorem B4480001 : Blo 1325481 4480001 := bstep (se 2 (by rfl) ⟨1680000, by rfl⟩ : syracuseStep 4480001 = 3360001) B3360001
theorem B1989641 : Blo 1325481 1989641 := bstep (se 2 (by rfl) ⟨746115, by rfl⟩ : syracuseStep 1989641 = 1492231) B1492231
theorem B1326119 : Blo 1325481 1326119 := bstep (se 1 (by rfl) ⟨994589, by rfl⟩ : syracuseStep 1326119 = 1989179) B1989179
theorem B1989671 : Blo 1325481 1989671 := bstep (se 1 (by rfl) ⟨1492253, by rfl⟩ : syracuseStep 1989671 = 2984507) B2984507
theorem B1793063 : Blo 1325481 1793063 := bstep (se 1 (by rfl) ⟨1344797, by rfl⟩ : syracuseStep 1793063 = 2689595) B2689595
theorem B1326159 : Blo 1325481 1326159 := bstep (se 1 (by rfl) ⟨994619, by rfl⟩ : syracuseStep 1326159 = 1989239) B1989239
theorem B1326175 : Blo 1325481 1326175 := bstep (se 1 (by rfl) ⟨994631, by rfl⟩ : syracuseStep 1326175 = 1989263) B1989263
theorem B1326203 : Blo 1325481 1326203 := bstep (se 1 (by rfl) ⟨994652, by rfl⟩ : syracuseStep 1326203 = 1989305) B1989305
theorem B1989755 : Blo 1325481 1989755 := bstep (se 1 (by rfl) ⟨1492316, by rfl⟩ : syracuseStep 1989755 = 2984633) B2984633
theorem B57351341 : Blo 1325481 57351341 := bstep (se 3 (by rfl) ⟨10753376, by rfl⟩ : syracuseStep 57351341 = 21506753) B21506753
theorem B1326255 : Blo 1325481 1326255 := bstep (se 1 (by rfl) ⟨994691, by rfl⟩ : syracuseStep 1326255 = 1989383) B1989383
theorem B1326279 : Blo 1325481 1326279 := bstep (se 1 (by rfl) ⟨994709, by rfl⟩ : syracuseStep 1326279 = 1989419) B1989419
theorem B1326299 : Blo 1325481 1326299 := bstep (se 1 (by rfl) ⟨994724, by rfl⟩ : syracuseStep 1326299 = 1989449) B1989449
theorem B1989881 : Blo 1325481 1989881 := bstep (se 2 (by rfl) ⟨746205, by rfl⟩ : syracuseStep 1989881 = 1492411) B1492411
theorem B1326375 : Blo 1325481 1326375 := bstep (se 1 (by rfl) ⟨994781, by rfl⟩ : syracuseStep 1326375 = 1989563) B1989563
theorem B1326415 : Blo 1325481 1326415 := bstep (se 1 (by rfl) ⟨994811, by rfl⟩ : syracuseStep 1326415 = 1989623) B1989623
theorem B1326431 : Blo 1325481 1326431 := bstep (se 1 (by rfl) ⟨994823, by rfl⟩ : syracuseStep 1326431 = 1989647) B1989647
theorem B1989983 : Blo 1325481 1989983 := bstep (se 1 (by rfl) ⟨1492487, by rfl⟩ : syracuseStep 1989983 = 2984975) B2984975
theorem B3358057 : Blo 1325481 3358057 := bstep (se 2 (by rfl) ⟨1259271, by rfl⟩ : syracuseStep 3358057 = 2518543) B2518543
theorem B1989995 : Blo 1325481 1989995 := bstep (se 1 (by rfl) ⟨1492496, by rfl⟩ : syracuseStep 1989995 = 2984993) B2984993
theorem B1326459 : Blo 1325481 1326459 := bstep (se 1 (by rfl) ⟨994844, by rfl⟩ : syracuseStep 1326459 = 1989689) B1989689
theorem B4251005 : Blo 1325481 4251005 := bstep (se 3 (by rfl) ⟨797063, by rfl⟩ : syracuseStep 4251005 = 1594127) B1594127
theorem B14335375 : Blo 1325481 14335375 := bstep (se 1 (by rfl) ⟨10751531, by rfl⟩ : syracuseStep 14335375 = 21503063) B21503063
theorem B2391457 : Blo 1325481 2391457 := bstep (se 2 (by rfl) ⟨896796, by rfl⟩ : syracuseStep 2391457 = 1793593) B1793593
theorem B1326511 : Blo 1325481 1326511 := bstep (se 1 (by rfl) ⟨994883, by rfl⟩ : syracuseStep 1326511 = 1989767) B1989767
theorem B1326535 : Blo 1325481 1326535 := bstep (se 1 (by rfl) ⟨994901, by rfl⟩ : syracuseStep 1326535 = 1989803) B1989803
theorem B1326555 : Blo 1325481 1326555 := bstep (se 1 (by rfl) ⟨994916, by rfl⟩ : syracuseStep 1326555 = 1989833) B1989833
theorem B1326631 : Blo 1325481 1326631 := bstep (se 1 (by rfl) ⟨994973, by rfl⟩ : syracuseStep 1326631 = 1989947) B1989947
theorem B1326671 : Blo 1325481 1326671 := bstep (se 1 (by rfl) ⟨995003, by rfl⟩ : syracuseStep 1326671 = 1990007) B1990007
theorem B1990223 : Blo 1325481 1990223 := bstep (se 1 (by rfl) ⟨1492667, by rfl⟩ : syracuseStep 1990223 = 2985335) B2985335
theorem B1326687 : Blo 1325481 1326687 := bstep (se 1 (by rfl) ⟨995015, by rfl⟩ : syracuseStep 1326687 = 1990031) B1990031
theorem B1326715 : Blo 1325481 1326715 := bstep (se 1 (by rfl) ⟨995036, by rfl⟩ : syracuseStep 1326715 = 1990073) B1990073
theorem B3358331 : Blo 1325481 3358331 := bstep (se 1 (by rfl) ⟨2518748, by rfl⟩ : syracuseStep 3358331 = 5037497) B5037497
theorem B1326767 : Blo 1325481 1326767 := bstep (se 1 (by rfl) ⟨995075, by rfl⟩ : syracuseStep 1326767 = 1990151) B1990151
theorem B1326791 : Blo 1325481 1326791 := bstep (se 1 (by rfl) ⟨995093, by rfl⟩ : syracuseStep 1326791 = 1990187) B1990187
theorem B1990343 : Blo 1325481 1990343 := bstep (se 1 (by rfl) ⟨1492757, by rfl⟩ : syracuseStep 1990343 = 2985515) B2985515
theorem B1326811 : Blo 1325481 1326811 := bstep (se 1 (by rfl) ⟨995108, by rfl⟩ : syracuseStep 1326811 = 1990217) B1990217
theorem B1326887 : Blo 1325481 1326887 := bstep (se 1 (by rfl) ⟨995165, by rfl⟩ : syracuseStep 1326887 = 1990331) B1990331
theorem B1326927 : Blo 1325481 1326927 := bstep (se 1 (by rfl) ⟨995195, by rfl⟩ : syracuseStep 1326927 = 1990391) B1990391
theorem B1326943 : Blo 1325481 1326943 := bstep (se 1 (by rfl) ⟨995207, by rfl⟩ : syracuseStep 1326943 = 1990415) B1990415
theorem B1990505 : Blo 1325481 1990505 := bstep (se 2 (by rfl) ⟨746439, by rfl⟩ : syracuseStep 1990505 = 1492879) B1492879
theorem B1326971 : Blo 1325481 1326971 := bstep (se 1 (by rfl) ⟨995228, by rfl⟩ : syracuseStep 1326971 = 1990457) B1990457
theorem B9559943 : Blo 1325481 9559943 := bstep (se 1 (by rfl) ⟨7169957, by rfl⟩ : syracuseStep 9559943 = 14339915) B14339915
theorem B1327023 : Blo 1325481 1327023 := bstep (se 1 (by rfl) ⟨995267, by rfl⟩ : syracuseStep 1327023 = 1990535) B1990535
theorem B1679287 : Blo 1325481 1679287 := bstep (se 1 (by rfl) ⟨1259465, by rfl⟩ : syracuseStep 1679287 = 2518931) B2518931
theorem B1990583 : Blo 1325481 1990583 := bstep (se 1 (by rfl) ⟨1492937, by rfl⟩ : syracuseStep 1990583 = 2985875) B2985875
theorem B1327047 : Blo 1325481 1327047 := bstep (se 1 (by rfl) ⟨995285, by rfl⟩ : syracuseStep 1327047 = 1990571) B1990571
theorem B1327067 : Blo 1325481 1327067 := bstep (se 1 (by rfl) ⟨995300, by rfl⟩ : syracuseStep 1327067 = 1990601) B1990601
theorem B1990619 : Blo 1325481 1990619 := bstep (se 1 (by rfl) ⟨1492964, by rfl⟩ : syracuseStep 1990619 = 2985929) B2985929
theorem B7553033 : Blo 1325481 7553033 := bstep (se 2 (by rfl) ⟨2832387, by rfl⟩ : syracuseStep 7553033 = 5664775) B5664775
theorem B6717491 : Blo 1325481 6717491 := bstep (se 1 (by rfl) ⟨5038118, by rfl⟩ : syracuseStep 6717491 = 10076237) B10076237
theorem B9568307 : Blo 1325481 9568307 := bstep (se 1 (by rfl) ⟨7176230, by rfl⟩ : syracuseStep 9568307 = 14352461) B14352461
theorem B3186793 : Blo 1325481 3186793 := bstep (se 2 (by rfl) ⟨1195047, by rfl⟩ : syracuseStep 3186793 = 2390095) B2390095
theorem B1327391 : Blo 1325481 1327391 := bstep (se 1 (by rfl) ⟨995543, by rfl⟩ : syracuseStep 1327391 = 1991087) B1991087
theorem B1679707 : Blo 1325481 1679707 := bstep (se 1 (by rfl) ⟨1259780, by rfl⟩ : syracuseStep 1679707 = 2519561) B2519561
theorem B1991003 : Blo 1325481 1991003 := bstep (se 1 (by rfl) ⟨1493252, by rfl⟩ : syracuseStep 1991003 = 2986505) B2986505
theorem B1327451 : Blo 1325481 1327451 := bstep (se 1 (by rfl) ⟨995588, by rfl⟩ : syracuseStep 1327451 = 1991177) B1991177
theorem B1327471 : Blo 1325481 1327471 := bstep (se 1 (by rfl) ⟨995603, by rfl⟩ : syracuseStep 1327471 = 1991207) B1991207
theorem B1491367 : Blo 1325481 1491367 := bstep (se 1 (by rfl) ⟨1118525, by rfl⟩ : syracuseStep 1491367 = 2237051) B2237051
theorem B2154919 : Blo 1325481 2154919 := bstep (se 1 (by rfl) ⟨1616189, by rfl⟩ : syracuseStep 2154919 = 3232379) B3232379
theorem B36323747 : Blo 1325481 36323747 := bstep (se 1 (by rfl) ⟨27242810, by rfl⟩ : syracuseStep 36323747 = 54485621) B54485621
theorem B22970881 : Blo 1325481 22970881 := bstep (se 2 (by rfl) ⟨8614080, by rfl⟩ : syracuseStep 22970881 = 17228161) B17228161
theorem B2982419 : Blo 1325481 2982419 := bstep (se 1 (by rfl) ⟨2236814, by rfl⟩ : syracuseStep 2982419 = 4473629) B4473629
theorem B1679935 : Blo 1325481 1679935 := bstep (se 1 (by rfl) ⟨1259951, by rfl⟩ : syracuseStep 1679935 = 2519903) B2519903
theorem B3359303 : Blo 1325481 3359303 := bstep (se 1 (by rfl) ⟨2519477, by rfl⟩ : syracuseStep 3359303 = 5038955) B5038955
theorem B2982473 : Blo 1325481 2982473 := bstep (se 2 (by rfl) ⟨1118427, by rfl⟩ : syracuseStep 2982473 = 2236855) B2236855
theorem B3359353 : Blo 1325481 3359353 := bstep (se 2 (by rfl) ⟨1259757, by rfl⟩ : syracuseStep 3359353 = 2519515) B2519515
theorem B12739207 : Blo 1325481 12739207 := bstep (se 1 (by rfl) ⟨9554405, by rfl⟩ : syracuseStep 12739207 = 19108811) B19108811
theorem B2950031 : Blo 1325481 2950031 := bstep (se 1 (by rfl) ⟨2212523, by rfl⟩ : syracuseStep 2950031 = 4425047) B4425047
theorem B2982887 : Blo 1325481 2982887 := bstep (se 1 (by rfl) ⟨2237165, by rfl⟩ : syracuseStep 2982887 = 4474331) B4474331
theorem B1491943 : Blo 1325481 1491943 := bstep (se 1 (by rfl) ⟨1118957, by rfl⟩ : syracuseStep 1491943 = 2237915) B2237915
theorem B4473953 : Blo 1325481 4473953 := bstep (se 2 (by rfl) ⟨1677732, by rfl⟩ : syracuseStep 4473953 = 3355465) B3355465
theorem B16139407 : Blo 1325481 16139407 := bstep (se 1 (by rfl) ⟨12104555, by rfl⟩ : syracuseStep 16139407 = 24209111) B24209111
theorem B6046919 : Blo 1325481 6046919 := bstep (se 1 (by rfl) ⟨4535189, by rfl⟩ : syracuseStep 6046919 = 9070379) B9070379
theorem B3777769 : Blo 1325481 3777769 := bstep (se 2 (by rfl) ⟨1416663, by rfl⟩ : syracuseStep 3777769 = 2833327) B2833327
theorem B5039455 : Blo 1325481 5039455 := bstep (se 1 (by rfl) ⟨3779591, by rfl⟩ : syracuseStep 5039455 = 7559183) B7559183
theorem B2983265 : Blo 1325481 2983265 := bstep (se 2 (by rfl) ⟨1118724, by rfl⟩ : syracuseStep 2983265 = 2237449) B2237449
theorem B5662075 : Blo 1325481 5662075 := bstep (se 1 (by rfl) ⟨4246556, by rfl⟩ : syracuseStep 5662075 = 8493113) B8493113
theorem B5375393 : Blo 1325481 5375393 := bstep (se 2 (by rfl) ⟨2015772, by rfl⟩ : syracuseStep 5375393 = 4031545) B4031545
theorem B1344935 : Blo 1325481 1344935 := bstep (se 1 (by rfl) ⟨1008701, by rfl⟩ : syracuseStep 1344935 = 2017403) B2017403
theorem B12748205 : Blo 1325481 12748205 := bstep (se 3 (by rfl) ⟨2390288, by rfl⟩ : syracuseStep 12748205 = 4780577) B4780577
theorem B2983355 : Blo 1325481 2983355 := bstep (se 1 (by rfl) ⟨2237516, by rfl⟩ : syracuseStep 2983355 = 4475033) B4475033
theorem B11478515 : Blo 1325481 11478515 := bstep (se 1 (by rfl) ⟨8608886, by rfl⟩ : syracuseStep 11478515 = 17217773) B17217773
theorem B2983481 : Blo 1325481 2983481 := bstep (se 2 (by rfl) ⟨1118805, by rfl⟩ : syracuseStep 2983481 = 2237611) B2237611
theorem B6374969 : Blo 1325481 6374969 := bstep (se 2 (by rfl) ⟨2390613, by rfl⟩ : syracuseStep 6374969 = 4781227) B4781227
theorem B6719111 : Blo 1325481 6719111 := bstep (se 1 (by rfl) ⟨5039333, by rfl⟩ : syracuseStep 6719111 = 10078667) B10078667
theorem B5039927 : Blo 1325481 5039927 := bstep (se 1 (by rfl) ⟨3779945, by rfl⟩ : syracuseStep 5039927 = 7559891) B7559891
theorem B19113833 : Blo 1325481 19113833 := bstep (se 2 (by rfl) ⟨7167687, by rfl⟩ : syracuseStep 19113833 = 14335375) B14335375
theorem B3188609 : Blo 1325481 3188609 := bstep (se 2 (by rfl) ⟨1195728, by rfl⟩ : syracuseStep 3188609 = 2391457) B2391457
theorem B38234227 : Blo 1325481 38234227 := bstep (se 1 (by rfl) ⟨28675670, by rfl⟩ : syracuseStep 38234227 = 57351341) B57351341
theorem B10217657 : Blo 1325481 10217657 := bstep (se 2 (by rfl) ⟨3831621, by rfl⟩ : syracuseStep 10217657 = 7663243) B7663243
theorem B2984147 : Blo 1325481 2984147 := bstep (se 1 (by rfl) ⟨2238110, by rfl⟩ : syracuseStep 2984147 = 4476221) B4476221
theorem B2984201 : Blo 1325481 2984201 := bstep (se 2 (by rfl) ⟨1119075, by rfl⟩ : syracuseStep 2984201 = 2238151) B2238151
theorem B4475303 : Blo 1325481 4475303 := bstep (se 1 (by rfl) ⟨3356477, by rfl⟩ : syracuseStep 4475303 = 6712955) B6712955
theorem B2238887 : Blo 1325481 2238887 := bstep (se 1 (by rfl) ⟨1679165, by rfl⟩ : syracuseStep 2238887 = 3358331) B3358331
theorem B2517473 : Blo 1325481 2517473 := bstep (se 2 (by rfl) ⟨944052, by rfl⟩ : syracuseStep 2517473 = 1888105) B1888105
theorem B2984417 : Blo 1325481 2984417 := bstep (se 2 (by rfl) ⟨1119156, by rfl⟩ : syracuseStep 2984417 = 2238313) B2238313
theorem B4475465 : Blo 1325481 4475465 := bstep (se 2 (by rfl) ⟨1678299, by rfl⟩ : syracuseStep 4475465 = 3356599) B3356599
theorem B2239049 : Blo 1325481 2239049 := bstep (se 2 (by rfl) ⟨839643, by rfl⟩ : syracuseStep 2239049 = 1679287) B1679287
theorem B8620631 : Blo 1325481 8620631 := bstep (se 1 (by rfl) ⟨6465473, by rfl⟩ : syracuseStep 8620631 = 12930947) B12930947
theorem B6711983 : Blo 1325481 6711983 := bstep (se 1 (by rfl) ⟨5033987, by rfl⟩ : syracuseStep 6711983 = 10067975) B10067975
theorem B2017975 : Blo 1325481 2017975 := bstep (se 1 (by rfl) ⟨1513481, by rfl⟩ : syracuseStep 2017975 = 3026963) B3026963
theorem B2984723 : Blo 1325481 2984723 := bstep (se 1 (by rfl) ⟨2238542, by rfl⟩ : syracuseStep 2984723 = 4477085) B4477085
theorem B11332487 : Blo 1325481 11332487 := bstep (se 1 (by rfl) ⟨8499365, by rfl⟩ : syracuseStep 11332487 = 16998731) B16998731
theorem B6712307 : Blo 1325481 6712307 := bstep (se 1 (by rfl) ⟨5034230, by rfl⟩ : syracuseStep 6712307 = 10068461) B10068461
theorem B5663783 : Blo 1325481 5663783 := bstep (se 1 (by rfl) ⟨4247837, by rfl⟩ : syracuseStep 5663783 = 8495675) B8495675
theorem B2985083 : Blo 1325481 2985083 := bstep (se 1 (by rfl) ⟨2238812, by rfl⟩ : syracuseStep 2985083 = 4477625) B4477625
theorem B2985209 : Blo 1325481 2985209 := bstep (se 2 (by rfl) ⟨1119453, by rfl⟩ : syracuseStep 2985209 = 2238907) B2238907
theorem B4844897 : Blo 1325481 4844897 := bstep (se 2 (by rfl) ⟨1816836, by rfl⟩ : syracuseStep 4844897 = 3633673) B3633673
theorem B7556449 : Blo 1325481 7556449 := bstep (se 2 (by rfl) ⟨2833668, by rfl⟩ : syracuseStep 7556449 = 5667337) B5667337
theorem B2985353 : Blo 1325481 2985353 := bstep (se 2 (by rfl) ⟨1119507, by rfl⟩ : syracuseStep 2985353 = 2239015) B2239015
theorem B6802903 : Blo 1325481 6802903 := bstep (se 1 (by rfl) ⟨5102177, by rfl⟩ : syracuseStep 6802903 = 10204355) B10204355
theorem B2551289 : Blo 1325481 2551289 := bstep (se 2 (by rfl) ⟨956733, by rfl⟩ : syracuseStep 2551289 = 1913467) B1913467
theorem B2985479 : Blo 1325481 2985479 := bstep (se 1 (by rfl) ⟨2239109, by rfl⟩ : syracuseStep 2985479 = 4478219) B4478219
theorem B22957577 : Blo 1325481 22957577 := bstep (se 2 (by rfl) ⟨8609091, by rfl⟩ : syracuseStep 22957577 = 17218183) B17218183
theorem B6376985 : Blo 1325481 6376985 := bstep (se 2 (by rfl) ⟨2391369, by rfl⟩ : syracuseStep 6376985 = 4782739) B4782739
theorem B2240095 : Blo 1325481 2240095 := bstep (se 1 (by rfl) ⟨1680071, by rfl⟩ : syracuseStep 2240095 = 3360143) B3360143
theorem B2985659 : Blo 1325481 2985659 := bstep (se 1 (by rfl) ⟨2239244, by rfl⟩ : syracuseStep 2985659 = 4478489) B4478489
theorem B5664467 : Blo 1325481 5664467 := bstep (se 1 (by rfl) ⟨4248350, by rfl⟩ : syracuseStep 5664467 = 8496701) B8496701
theorem B1593055 : Blo 1325481 1593055 := bstep (se 1 (by rfl) ⟨1194791, by rfl⟩ : syracuseStep 1593055 = 2389583) B2389583
theorem B4247275 : Blo 1325481 4247275 := bstep (se 1 (by rfl) ⟨3185456, by rfl⟩ : syracuseStep 4247275 = 6370913) B6370913
theorem B16125743 : Blo 1325481 16125743 := bstep (se 1 (by rfl) ⟨12094307, by rfl⟩ : syracuseStep 16125743 = 24188615) B24188615
theorem B2985785 : Blo 1325481 2985785 := bstep (se 2 (by rfl) ⟨1119669, by rfl⟩ : syracuseStep 2985785 = 2239339) B2239339
theorem B5107585 : Blo 1325481 5107585 := bstep (se 2 (by rfl) ⟨1915344, by rfl⟩ : syracuseStep 5107585 = 3830689) B3830689
theorem B26570753 : Blo 1325481 26570753 := bstep (se 2 (by rfl) ⟨9964032, by rfl⟩ : syracuseStep 26570753 = 19928065) B19928065
theorem B12095513 : Blo 1325481 12095513 := bstep (se 2 (by rfl) ⟨4535817, by rfl⟩ : syracuseStep 12095513 = 9071635) B9071635
theorem B4477139 : Blo 1325481 4477139 := bstep (se 1 (by rfl) ⟨3357854, by rfl⟩ : syracuseStep 4477139 = 6715709) B6715709
theorem B6713603 : Blo 1325481 6713603 := bstep (se 1 (by rfl) ⟨5035202, by rfl⟩ : syracuseStep 6713603 = 10070405) B10070405
theorem B17240323 : Blo 1325481 17240323 := bstep (se 1 (by rfl) ⟨12930242, by rfl⟩ : syracuseStep 17240323 = 25860485) B25860485
theorem B2986415 : Blo 1325481 2986415 := bstep (se 1 (by rfl) ⟨2239811, by rfl⟩ : syracuseStep 2986415 = 4479623) B4479623
theorem B2986451 : Blo 1325481 2986451 := bstep (se 1 (by rfl) ⟨2239838, by rfl⟩ : syracuseStep 2986451 = 4479677) B4479677
theorem B4477409 : Blo 1325481 4477409 := bstep (se 2 (by rfl) ⟨1679028, by rfl⟩ : syracuseStep 4477409 = 3358057) B3358057
theorem B2986559 : Blo 1325481 2986559 := bstep (se 1 (by rfl) ⟨2239919, by rfl⟩ : syracuseStep 2986559 = 4479839) B4479839
theorem B6713927 : Blo 1325481 6713927 := bstep (se 1 (by rfl) ⟨5035445, by rfl⟩ : syracuseStep 6713927 = 10070891) B10070891
theorem B2986667 : Blo 1325481 2986667 := bstep (se 1 (by rfl) ⟨2240000, by rfl⟩ : syracuseStep 2986667 = 4480001) B4480001
theorem B5665697 : Blo 1325481 5665697 := bstep (se 2 (by rfl) ⟨2124636, by rfl⟩ : syracuseStep 5665697 = 4249273) B4249273
theorem B14349257 : Blo 1325481 14349257 := bstep (se 2 (by rfl) ⟨5380971, by rfl⟩ : syracuseStep 14349257 = 10761943) B10761943
theorem B6370451 : Blo 1325481 6370451 := bstep (se 1 (by rfl) ⟨4777838, by rfl⟩ : syracuseStep 6370451 = 9555677) B9555677
theorem B1889659 : Blo 1325481 1889659 := bstep (se 1 (by rfl) ⟨1417244, by rfl⟩ : syracuseStep 1889659 = 2834489) B2834489
theorem B6370721 : Blo 1325481 6370721 := bstep (se 2 (by rfl) ⟨2389020, by rfl⟩ : syracuseStep 6370721 = 4778041) B4778041
theorem B4781501 : Blo 1325481 4781501 := bstep (se 3 (by rfl) ⟨896531, by rfl⟩ : syracuseStep 4781501 = 1793063) B1793063
theorem B7370297 : Blo 1325481 7370297 := bstep (se 2 (by rfl) ⟨2763861, by rfl⟩ : syracuseStep 7370297 = 5527723) B5527723
theorem B3356255 : Blo 1325481 3356255 := bstep (se 1 (by rfl) ⟨2517191, by rfl⟩ : syracuseStep 3356255 = 5034383) B5034383
theorem B1889887 : Blo 1325481 1889887 := bstep (se 1 (by rfl) ⟨1417415, by rfl⟩ : syracuseStep 1889887 = 2834831) B2834831
theorem B43030115 : Blo 1325481 43030115 := bstep (se 1 (by rfl) ⟨32272586, by rfl⟩ : syracuseStep 43030115 = 64545173) B64545173
theorem B2389691 : Blo 1325481 2389691 := bstep (se 1 (by rfl) ⟨1792268, by rfl⟩ : syracuseStep 2389691 = 3584537) B3584537
theorem B4478651 : Blo 1325481 4478651 := bstep (se 1 (by rfl) ⟨3358988, by rfl⟩ : syracuseStep 4478651 = 6717977) B6717977
theorem B1988393 : Blo 1325481 1988393 := bstep (se 2 (by rfl) ⟨745647, by rfl⟩ : syracuseStep 1988393 = 1491295) B1491295
theorem B1988399 : Blo 1325481 1988399 := bstep (se 1 (by rfl) ⟨1491299, by rfl⟩ : syracuseStep 1988399 = 2982599) B2982599
theorem B6715223 : Blo 1325481 6715223 := bstep (se 1 (by rfl) ⟨5036417, by rfl⟩ : syracuseStep 6715223 = 10072835) B10072835
theorem B87242795 : Blo 1325481 87242795 := bstep (se 1 (by rfl) ⟨65432096, by rfl⟩ : syracuseStep 87242795 = 130864193) B130864193
theorem B5380225 : Blo 1325481 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B23615621 : Blo 1325481 23615621 := bstep (se 4 (by rfl) ⟨2213964, by rfl⟩ : syracuseStep 23615621 = 4427929) B4427929
theorem B1988873 : Blo 1325481 1988873 := bstep (se 2 (by rfl) ⟨745827, by rfl⟩ : syracuseStep 1988873 = 1491655) B1491655
theorem B3357035 : Blo 1325481 3357035 := bstep (se 1 (by rfl) ⟨2517776, by rfl⟩ : syracuseStep 3357035 = 5035553) B5035553
theorem B1988975 : Blo 1325481 1988975 := bstep (se 1 (by rfl) ⟨1491731, by rfl⟩ : syracuseStep 1988975 = 2983463) B2983463
theorem B2832815 : Blo 1325481 2832815 := bstep (se 1 (by rfl) ⟨2124611, by rfl⟩ : syracuseStep 2832815 = 4249223) B4249223
theorem B1325563 : Blo 1325481 1325563 := bstep (se 1 (by rfl) ⟨994172, by rfl⟩ : syracuseStep 1325563 = 1988345) B1988345
theorem B5036539 : Blo 1325481 5036539 := bstep (se 1 (by rfl) ⟨3777404, by rfl⟩ : syracuseStep 5036539 = 7554809) B7554809
theorem B1325631 : Blo 1325481 1325631 := bstep (se 1 (by rfl) ⟨994223, by rfl⟩ : syracuseStep 1325631 = 1988447) B1988447
theorem B3357247 : Blo 1325481 3357247 := bstep (se 1 (by rfl) ⟨2517935, by rfl⟩ : syracuseStep 3357247 = 5035871) B5035871
theorem B1325639 : Blo 1325481 1325639 := bstep (se 1 (by rfl) ⟨994229, by rfl⟩ : syracuseStep 1325639 = 1988459) B1988459
theorem B1989191 : Blo 1325481 1989191 := bstep (se 1 (by rfl) ⟨1491893, by rfl⟩ : syracuseStep 1989191 = 2983787) B2983787
theorem B5667407 : Blo 1325481 5667407 := bstep (se 1 (by rfl) ⟨4250555, by rfl⟩ : syracuseStep 5667407 = 8501111) B8501111
theorem B1989227 : Blo 1325481 1989227 := bstep (se 1 (by rfl) ⟨1491920, by rfl⟩ : syracuseStep 1989227 = 2983841) B2983841
theorem B3357359 : Blo 1325481 3357359 := bstep (se 1 (by rfl) ⟨2518019, by rfl⟩ : syracuseStep 3357359 = 5036039) B5036039
theorem B1325791 : Blo 1325481 1325791 := bstep (se 1 (by rfl) ⟨994343, by rfl⟩ : syracuseStep 1325791 = 1988687) B1988687
theorem B1325871 : Blo 1325481 1325871 := bstep (se 1 (by rfl) ⟨994403, by rfl⟩ : syracuseStep 1325871 = 1988807) B1988807
theorem B1989455 : Blo 1325481 1989455 := bstep (se 1 (by rfl) ⟨1492091, by rfl⟩ : syracuseStep 1989455 = 2984183) B2984183
theorem B3185563 : Blo 1325481 3185563 := bstep (se 1 (by rfl) ⟨2389172, by rfl⟩ : syracuseStep 3185563 = 4778345) B4778345
theorem B1325979 : Blo 1325481 1325979 := bstep (se 1 (by rfl) ⟨994484, by rfl⟩ : syracuseStep 1325979 = 1988969) B1988969
theorem B1326031 : Blo 1325481 1326031 := bstep (se 1 (by rfl) ⟨994523, by rfl⟩ : syracuseStep 1326031 = 1989047) B1989047
theorem B1326055 : Blo 1325481 1326055 := bstep (se 1 (by rfl) ⟨994541, by rfl⟩ : syracuseStep 1326055 = 1989083) B1989083
theorem B3357683 : Blo 1325481 3357683 := bstep (se 1 (by rfl) ⟨2518262, by rfl⟩ : syracuseStep 3357683 = 5036525) B5036525
theorem B3357895 : Blo 1325481 3357895 := bstep (se 1 (by rfl) ⟨2518421, by rfl⟩ : syracuseStep 3357895 = 5036843) B5036843
theorem B1989851 : Blo 1325481 1989851 := bstep (se 1 (by rfl) ⟨1492388, by rfl⟩ : syracuseStep 1989851 = 2984777) B2984777
theorem B1326367 : Blo 1325481 1326367 := bstep (se 1 (by rfl) ⟨994775, by rfl⟩ : syracuseStep 1326367 = 1989551) B1989551
theorem B5668157 : Blo 1325481 5668157 := bstep (se 3 (by rfl) ⟨1062779, by rfl⟩ : syracuseStep 5668157 = 2125559) B2125559
theorem B1326427 : Blo 1325481 1326427 := bstep (se 1 (by rfl) ⟨994820, by rfl⟩ : syracuseStep 1326427 = 1989641) B1989641
theorem B1326447 : Blo 1325481 1326447 := bstep (se 1 (by rfl) ⟨994835, by rfl⟩ : syracuseStep 1326447 = 1989671) B1989671
theorem B1990025 : Blo 1325481 1990025 := bstep (se 2 (by rfl) ⟨746259, by rfl⟩ : syracuseStep 1990025 = 1492519) B1492519
theorem B1326503 : Blo 1325481 1326503 := bstep (se 1 (by rfl) ⟨994877, by rfl⟩ : syracuseStep 1326503 = 1989755) B1989755
theorem B5037511 : Blo 1325481 5037511 := bstep (se 1 (by rfl) ⟨3778133, by rfl⟩ : syracuseStep 5037511 = 7556267) B7556267
theorem B1326587 : Blo 1325481 1326587 := bstep (se 1 (by rfl) ⟨994940, by rfl⟩ : syracuseStep 1326587 = 1989881) B1989881
theorem B1326655 : Blo 1325481 1326655 := bstep (se 1 (by rfl) ⟨994991, by rfl⟩ : syracuseStep 1326655 = 1989983) B1989983
theorem B1326663 : Blo 1325481 1326663 := bstep (se 1 (by rfl) ⟨994997, by rfl⟩ : syracuseStep 1326663 = 1989995) B1989995
theorem B2834003 : Blo 1325481 2834003 := bstep (se 1 (by rfl) ⟨2125502, by rfl⟩ : syracuseStep 2834003 = 4251005) B4251005
theorem B8494753 : Blo 1325481 8494753 := bstep (se 2 (by rfl) ⟨3185532, by rfl⟩ : syracuseStep 8494753 = 6371065) B6371065
theorem B1326815 : Blo 1325481 1326815 := bstep (se 1 (by rfl) ⟨995111, by rfl⟩ : syracuseStep 1326815 = 1990223) B1990223
theorem B1990379 : Blo 1325481 1990379 := bstep (se 1 (by rfl) ⟨1492784, by rfl⟩ : syracuseStep 1990379 = 2985569) B2985569
theorem B1326895 : Blo 1325481 1326895 := bstep (se 1 (by rfl) ⟨995171, by rfl⟩ : syracuseStep 1326895 = 1990343) B1990343
theorem B6373181 : Blo 1325481 6373181 := bstep (se 3 (by rfl) ⟨1194971, by rfl⟩ : syracuseStep 6373181 = 2389943) B2389943
theorem B1327003 : Blo 1325481 1327003 := bstep (se 1 (by rfl) ⟨995252, by rfl⟩ : syracuseStep 1327003 = 1990505) B1990505
theorem B6373295 : Blo 1325481 6373295 := bstep (se 1 (by rfl) ⟨4779971, by rfl⟩ : syracuseStep 6373295 = 9559943) B9559943
theorem B1327055 : Blo 1325481 1327055 := bstep (se 1 (by rfl) ⟨995291, by rfl⟩ : syracuseStep 1327055 = 1990583) B1990583
theorem B1990607 : Blo 1325481 1990607 := bstep (se 1 (by rfl) ⟨1492955, by rfl⟩ : syracuseStep 1990607 = 2985911) B2985911
theorem B1327079 : Blo 1325481 1327079 := bstep (se 1 (by rfl) ⟨995309, by rfl⟩ : syracuseStep 1327079 = 1990619) B1990619
theorem B50978969 : Blo 1325481 50978969 := bstep (se 2 (by rfl) ⟨19117113, by rfl⟩ : syracuseStep 50978969 = 38234227) B38234227
theorem B1327335 : Blo 1325481 1327335 := bstep (se 1 (by rfl) ⟨995501, by rfl⟩ : syracuseStep 1327335 = 1991003) B1991003
theorem B24215831 : Blo 1325481 24215831 := bstep (se 1 (by rfl) ⟨18161873, by rfl⟩ : syracuseStep 24215831 = 36323747) B36323747
theorem B1990943 : Blo 1325481 1990943 := bstep (se 1 (by rfl) ⟨1493207, by rfl⟩ : syracuseStep 1990943 = 2986415) B2986415
theorem B1990967 : Blo 1325481 1990967 := bstep (se 1 (by rfl) ⟨1493225, by rfl⟩ : syracuseStep 1990967 = 2986451) B2986451
theorem B22987097 : Blo 1325481 22987097 := bstep (se 2 (by rfl) ⟨8620161, by rfl⟩ : syracuseStep 22987097 = 17240323) B17240323
theorem B1991039 : Blo 1325481 1991039 := bstep (se 1 (by rfl) ⟨1493279, by rfl⟩ : syracuseStep 1991039 = 2986559) B2986559
theorem B1991111 : Blo 1325481 1991111 := bstep (se 1 (by rfl) ⟨1493333, by rfl⟩ : syracuseStep 1991111 = 2986667) B2986667
theorem B1966687 : Blo 1325481 1966687 := bstep (se 1 (by rfl) ⟨1475015, by rfl⟩ : syracuseStep 1966687 = 2950031) B2950031
theorem B3777131 : Blo 1325481 3777131 := bstep (se 1 (by rfl) ⟨2832848, by rfl⟩ : syracuseStep 3777131 = 5665697) B5665697
theorem B2982635 : Blo 1325481 2982635 := bstep (se 1 (by rfl) ⟨2236976, by rfl⟩ : syracuseStep 2982635 = 4473953) B4473953
theorem B4031279 : Blo 1325481 4031279 := bstep (se 1 (by rfl) ⟨3023459, by rfl⟩ : syracuseStep 4031279 = 6046919) B6046919
theorem B15115085 : Blo 1325481 15115085 := bstep (se 3 (by rfl) ⟨2834078, by rfl⟩ : syracuseStep 15115085 = 5668157) B5668157
theorem B3187667 : Blo 1325481 3187667 := bstep (se 1 (by rfl) ⟨2390750, by rfl⟩ : syracuseStep 3187667 = 4781501) B4781501
theorem B2237503 : Blo 1325481 2237503 := bstep (se 1 (by rfl) ⟨1678127, by rfl⟩ : syracuseStep 2237503 = 3356255) B3356255
theorem B3359951 : Blo 1325481 3359951 := bstep (se 1 (by rfl) ⟨2519963, by rfl⟩ : syracuseStep 3359951 = 5039927) B5039927
theorem B2238023 : Blo 1325481 2238023 := bstep (se 1 (by rfl) ⟨1678517, by rfl⟩ : syracuseStep 2238023 = 3357035) B3357035
theorem B2983535 : Blo 1325481 2983535 := bstep (se 1 (by rfl) ⟨2237651, by rfl⟩ : syracuseStep 2983535 = 4475303) B4475303
theorem B1492591 : Blo 1325481 1492591 := bstep (se 1 (by rfl) ⟨1119443, by rfl⟩ : syracuseStep 1492591 = 2238887) B2238887
theorem B2983643 : Blo 1325481 2983643 := bstep (se 1 (by rfl) ⟨2237732, by rfl⟩ : syracuseStep 2983643 = 4475465) B4475465
theorem B1492699 : Blo 1325481 1492699 := bstep (se 1 (by rfl) ⟨1119524, by rfl⟩ : syracuseStep 1492699 = 2239049) B2239049
theorem B3778271 : Blo 1325481 3778271 := bstep (se 1 (by rfl) ⟨2833703, by rfl⟩ : syracuseStep 3778271 = 5667407) B5667407
theorem B4474655 : Blo 1325481 4474655 := bstep (se 1 (by rfl) ⟨3355991, by rfl⟩ : syracuseStep 4474655 = 6711983) B6711983
theorem B2238239 : Blo 1325481 2238239 := bstep (se 1 (by rfl) ⟨1678679, by rfl⟩ : syracuseStep 2238239 = 3357359) B3357359
theorem B6719273 : Blo 1325481 6719273 := bstep (se 2 (by rfl) ⟨2519727, by rfl⟩ : syracuseStep 6719273 = 5039455) B5039455
theorem B7554991 : Blo 1325481 7554991 := bstep (se 1 (by rfl) ⟨5666243, by rfl⟩ : syracuseStep 7554991 = 11332487) B11332487
theorem B9070537 : Blo 1325481 9070537 := bstep (se 2 (by rfl) ⟨3401451, by rfl⟩ : syracuseStep 9070537 = 6802903) B6802903
theorem B10078181 : Blo 1325481 10078181 := bstep (se 4 (by rfl) ⟨944829, by rfl⟩ : syracuseStep 10078181 = 1889659) B1889659
theorem B4474871 : Blo 1325481 4474871 := bstep (se 1 (by rfl) ⟨3356153, by rfl⟩ : syracuseStep 4474871 = 6712307) B6712307
theorem B2238455 : Blo 1325481 2238455 := bstep (se 1 (by rfl) ⟨1678841, by rfl⟩ : syracuseStep 2238455 = 3357683) B3357683
theorem B3229931 : Blo 1325481 3229931 := bstep (se 1 (by rfl) ⟨2422448, by rfl⟩ : syracuseStep 3229931 = 4844897) B4844897
theorem B2124073 : Blo 1325481 2124073 := bstep (se 2 (by rfl) ⟨796527, by rfl⟩ : syracuseStep 2124073 = 1593055) B1593055
theorem B5663033 : Blo 1325481 5663033 := bstep (se 2 (by rfl) ⟨2123637, by rfl⟩ : syracuseStep 5663033 = 4247275) B4247275
theorem B15305051 : Blo 1325481 15305051 := bstep (se 1 (by rfl) ⟨11478788, by rfl⟩ : syracuseStep 15305051 = 22957577) B22957577
theorem B6810113 : Blo 1325481 6810113 := bstep (se 2 (by rfl) ⟨2553792, by rfl⟩ : syracuseStep 6810113 = 5107585) B5107585
theorem B10750495 : Blo 1325481 10750495 := bstep (se 1 (by rfl) ⟨8062871, by rfl⟩ : syracuseStep 10750495 = 16125743) B16125743
theorem B17713835 : Blo 1325481 17713835 := bstep (se 1 (by rfl) ⟨13285376, by rfl⟩ : syracuseStep 17713835 = 26570753) B26570753
theorem B8063675 : Blo 1325481 8063675 := bstep (se 1 (by rfl) ⟨6047756, by rfl⟩ : syracuseStep 8063675 = 12095513) B12095513
theorem B2984759 : Blo 1325481 2984759 := bstep (se 1 (by rfl) ⟨2238569, by rfl⟩ : syracuseStep 2984759 = 4477139) B4477139
theorem B4475735 : Blo 1325481 4475735 := bstep (se 1 (by rfl) ⟨3356801, by rfl⟩ : syracuseStep 4475735 = 6713603) B6713603
theorem B2984939 : Blo 1325481 2984939 := bstep (se 1 (by rfl) ⟨2238704, by rfl⟩ : syracuseStep 2984939 = 4477409) B4477409
theorem B4475951 : Blo 1325481 4475951 := bstep (se 1 (by rfl) ⟨3356963, by rfl⟩ : syracuseStep 4475951 = 6713927) B6713927
theorem B2239535 : Blo 1325481 2239535 := bstep (se 1 (by rfl) ⟨1679651, by rfl⟩ : syracuseStep 2239535 = 3359303) B3359303
theorem B2239609 : Blo 1325481 2239609 := bstep (se 2 (by rfl) ⟨839853, by rfl⟩ : syracuseStep 2239609 = 1679707) B1679707
theorem B4476329 : Blo 1325481 4476329 := bstep (se 2 (by rfl) ⟨1678623, by rfl⟩ : syracuseStep 4476329 = 3357247) B3357247
theorem B2239913 : Blo 1325481 2239913 := bstep (se 2 (by rfl) ⟨839967, by rfl⟩ : syracuseStep 2239913 = 1679935) B1679935
theorem B4246967 : Blo 1325481 4246967 := bstep (se 1 (by rfl) ⟨3185225, by rfl⟩ : syracuseStep 4246967 = 6370451) B6370451
theorem B16985609 : Blo 1325481 16985609 := bstep (se 2 (by rfl) ⟨6369603, by rfl⟩ : syracuseStep 16985609 = 12739207) B12739207
theorem B2690633 : Blo 1325481 2690633 := bstep (se 2 (by rfl) ⟨1008987, by rfl⟩ : syracuseStep 2690633 = 2017975) B2017975
theorem B4247147 : Blo 1325481 4247147 := bstep (se 1 (by rfl) ⟨3185360, by rfl⟩ : syracuseStep 4247147 = 6370721) B6370721
theorem B3583595 : Blo 1325481 3583595 := bstep (se 1 (by rfl) ⟨2687696, by rfl⟩ : syracuseStep 3583595 = 5375393) B5375393
theorem B8498803 : Blo 1325481 8498803 := bstep (se 1 (by rfl) ⟨6374102, by rfl⟩ : syracuseStep 8498803 = 12748205) B12748205
theorem B1593127 : Blo 1325481 1593127 := bstep (se 1 (by rfl) ⟨1194845, by rfl⟩ : syracuseStep 1593127 = 2389691) B2389691
theorem B2985767 : Blo 1325481 2985767 := bstep (se 1 (by rfl) ⟨2239325, by rfl⟩ : syracuseStep 2985767 = 4478651) B4478651
theorem B4247417 : Blo 1325481 4247417 := bstep (se 2 (by rfl) ⟨1592781, by rfl⟩ : syracuseStep 4247417 = 3185563) B3185563
theorem B4476815 : Blo 1325481 4476815 := bstep (se 1 (by rfl) ⟨3357611, by rfl⟩ : syracuseStep 4476815 = 6715223) B6715223
theorem B12742555 : Blo 1325481 12742555 := bstep (se 1 (by rfl) ⟨9556916, by rfl⟩ : syracuseStep 12742555 = 19113833) B19113833
theorem B2125739 : Blo 1325481 2125739 := bstep (se 1 (by rfl) ⟨1594304, by rfl⟩ : syracuseStep 2125739 = 3188609) B3188609
theorem B30609373 : Blo 1325481 30609373 := bstep (se 3 (by rfl) ⟨5739257, by rfl⟩ : syracuseStep 30609373 = 11478515) B11478515
theorem B6803437 : Blo 1325481 6803437 := bstep (se 3 (by rfl) ⟨1275644, by rfl⟩ : syracuseStep 6803437 = 2551289) B2551289
theorem B6811771 : Blo 1325481 6811771 := bstep (se 1 (by rfl) ⟨5108828, by rfl⟩ : syracuseStep 6811771 = 10217657) B10217657
theorem B4477193 : Blo 1325481 4477193 := bstep (se 2 (by rfl) ⟨1678947, by rfl⟩ : syracuseStep 4477193 = 3357895) B3357895
theorem B1888543 : Blo 1325481 1888543 := bstep (se 1 (by rfl) ⟨1416407, by rfl⟩ : syracuseStep 1888543 = 2832815) B2832815
theorem B5747087 : Blo 1325481 5747087 := bstep (se 1 (by rfl) ⟨4310315, by rfl⟩ : syracuseStep 5747087 = 8620631) B8620631
theorem B7549433 : Blo 1325481 7549433 := bstep (se 2 (by rfl) ⟨2831037, by rfl⟩ : syracuseStep 7549433 = 5662075) B5662075
theorem B2519849 : Blo 1325481 2519849 := bstep (se 2 (by rfl) ⟨944943, by rfl⟩ : syracuseStep 2519849 = 1889887) B1889887
theorem B2986793 : Blo 1325481 2986793 := bstep (se 2 (by rfl) ⟨1120047, by rfl⟩ : syracuseStep 2986793 = 2240095) B2240095
theorem B11326337 : Blo 1325481 11326337 := bstep (se 2 (by rfl) ⟨4247376, by rfl⟩ : syracuseStep 11326337 = 8494753) B8494753
theorem B1889335 : Blo 1325481 1889335 := bstep (se 1 (by rfl) ⟨1417001, by rfl⟩ : syracuseStep 1889335 = 2834003) B2834003
theorem B4248787 : Blo 1325481 4248787 := bstep (se 1 (by rfl) ⟨3186590, by rfl⟩ : syracuseStep 4248787 = 6373181) B6373181
theorem B4248863 : Blo 1325481 4248863 := bstep (se 1 (by rfl) ⟨3186647, by rfl⟩ : syracuseStep 4248863 = 6373295) B6373295
theorem B5035355 : Blo 1325481 5035355 := bstep (se 1 (by rfl) ⟨3776516, by rfl⟩ : syracuseStep 5035355 = 7553033) B7553033
theorem B4478327 : Blo 1325481 4478327 := bstep (se 1 (by rfl) ⟨3358745, by rfl⟩ : syracuseStep 4478327 = 6717491) B6717491
theorem B6378871 : Blo 1325481 6378871 := bstep (se 1 (by rfl) ⟨4784153, by rfl⟩ : syracuseStep 6378871 = 9568307) B9568307
theorem B15103421 : Blo 1325481 15103421 := bstep (se 3 (by rfl) ⟨2831891, by rfl⟩ : syracuseStep 15103421 = 5663783) B5663783
theorem B4249057 : Blo 1325481 4249057 := bstep (se 2 (by rfl) ⟨1593396, by rfl⟩ : syracuseStep 4249057 = 3186793) B3186793
theorem B1988279 : Blo 1325481 1988279 := bstep (se 1 (by rfl) ⟨1491209, by rfl⟩ : syracuseStep 1988279 = 2982419) B2982419
theorem B1988315 : Blo 1325481 1988315 := bstep (se 1 (by rfl) ⟨1491236, by rfl⟩ : syracuseStep 1988315 = 2982473) B2982473
theorem B1988489 : Blo 1325481 1988489 := bstep (se 2 (by rfl) ⟨745683, by rfl⟩ : syracuseStep 1988489 = 1491367) B1491367
theorem B2873225 : Blo 1325481 2873225 := bstep (se 2 (by rfl) ⟨1077459, by rfl⟩ : syracuseStep 2873225 = 2154919) B2154919
theorem B9566171 : Blo 1325481 9566171 := bstep (se 1 (by rfl) ⟨7174628, by rfl⟩ : syracuseStep 9566171 = 14349257) B14349257
theorem B1988591 : Blo 1325481 1988591 := bstep (se 1 (by rfl) ⟨1491443, by rfl⟩ : syracuseStep 1988591 = 2982887) B2982887
theorem B6715385 : Blo 1325481 6715385 := bstep (se 2 (by rfl) ⟨2518269, by rfl⟩ : syracuseStep 6715385 = 5036539) B5036539
theorem B30627841 : Blo 1325481 30627841 := bstep (se 2 (by rfl) ⟨11485440, by rfl⟩ : syracuseStep 30627841 = 22970881) B22970881
theorem B28694533 : Blo 1325481 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B4479137 : Blo 1325481 4479137 := bstep (se 2 (by rfl) ⟨1679676, by rfl⟩ : syracuseStep 4479137 = 3359353) B3359353
theorem B1988843 : Blo 1325481 1988843 := bstep (se 1 (by rfl) ⟨1491632, by rfl⟩ : syracuseStep 1988843 = 2983265) B2983265
theorem B1988903 : Blo 1325481 1988903 := bstep (se 1 (by rfl) ⟨1491677, by rfl⟩ : syracuseStep 1988903 = 2983355) B2983355
theorem B1988987 : Blo 1325481 1988987 := bstep (se 1 (by rfl) ⟨1491740, by rfl⟩ : syracuseStep 1988987 = 2983481) B2983481
theorem B4249979 : Blo 1325481 4249979 := bstep (se 1 (by rfl) ⟨3187484, by rfl⟩ : syracuseStep 4249979 = 6374969) B6374969
theorem B4913531 : Blo 1325481 4913531 := bstep (se 1 (by rfl) ⟨3685148, by rfl⟩ : syracuseStep 4913531 = 7370297) B7370297
theorem B28686743 : Blo 1325481 28686743 := bstep (se 1 (by rfl) ⟨21515057, by rfl⟩ : syracuseStep 28686743 = 43030115) B43030115
theorem B4479407 : Blo 1325481 4479407 := bstep (se 1 (by rfl) ⟨3359555, by rfl⟩ : syracuseStep 4479407 = 6719111) B6719111
theorem B3586493 : Blo 1325481 3586493 := bstep (se 3 (by rfl) ⟨672467, by rfl⟩ : syracuseStep 3586493 = 1344935) B1344935
theorem B1325595 : Blo 1325481 1325595 := bstep (se 1 (by rfl) ⟨994196, by rfl⟩ : syracuseStep 1325595 = 1988393) B1988393
theorem B1325599 : Blo 1325481 1325599 := bstep (se 1 (by rfl) ⟨994199, by rfl⟩ : syracuseStep 1325599 = 1988399) B1988399
theorem B1989257 : Blo 1325481 1989257 := bstep (se 2 (by rfl) ⟨745971, by rfl⟩ : syracuseStep 1989257 = 1491943) B1491943
theorem B58161863 : Blo 1325481 58161863 := bstep (se 1 (by rfl) ⟨43621397, by rfl⟩ : syracuseStep 58161863 = 87242795) B87242795
theorem B15743747 : Blo 1325481 15743747 := bstep (se 1 (by rfl) ⟨11807810, by rfl⟩ : syracuseStep 15743747 = 23615621) B23615621
theorem B1989431 : Blo 1325481 1989431 := bstep (se 1 (by rfl) ⟨1492073, by rfl⟩ : syracuseStep 1989431 = 2984147) B2984147
theorem B1325915 : Blo 1325481 1325915 := bstep (se 1 (by rfl) ⟨994436, by rfl⟩ : syracuseStep 1325915 = 1988873) B1988873
theorem B1989467 : Blo 1325481 1989467 := bstep (se 1 (by rfl) ⟨1492100, by rfl⟩ : syracuseStep 1989467 = 2984201) B2984201
theorem B21519209 : Blo 1325481 21519209 := bstep (se 2 (by rfl) ⟨8069703, by rfl⟩ : syracuseStep 21519209 = 16139407) B16139407
theorem B1325983 : Blo 1325481 1325983 := bstep (se 1 (by rfl) ⟨994487, by rfl⟩ : syracuseStep 1325983 = 1988975) B1988975
theorem B5037025 : Blo 1325481 5037025 := bstep (se 2 (by rfl) ⟨1888884, by rfl⟩ : syracuseStep 5037025 = 3777769) B3777769
theorem B1678315 : Blo 1325481 1678315 := bstep (se 1 (by rfl) ⟨1258736, by rfl⟩ : syracuseStep 1678315 = 2517473) B2517473
theorem B1989611 : Blo 1325481 1989611 := bstep (se 1 (by rfl) ⟨1492208, by rfl⟩ : syracuseStep 1989611 = 2984417) B2984417
theorem B1326127 : Blo 1325481 1326127 := bstep (se 1 (by rfl) ⟨994595, by rfl⟩ : syracuseStep 1326127 = 1989191) B1989191
theorem B1326151 : Blo 1325481 1326151 := bstep (se 1 (by rfl) ⟨994613, by rfl⟩ : syracuseStep 1326151 = 1989227) B1989227
theorem B10075265 : Blo 1325481 10075265 := bstep (se 2 (by rfl) ⟨3778224, by rfl⟩ : syracuseStep 10075265 = 7556449) B7556449
theorem B1989815 : Blo 1325481 1989815 := bstep (se 1 (by rfl) ⟨1492361, by rfl⟩ : syracuseStep 1989815 = 2984723) B2984723
theorem B1326303 : Blo 1325481 1326303 := bstep (se 1 (by rfl) ⟨994727, by rfl⟩ : syracuseStep 1326303 = 1989455) B1989455
theorem B6716681 : Blo 1325481 6716681 := bstep (se 2 (by rfl) ⟨2518755, by rfl⟩ : syracuseStep 6716681 = 5037511) B5037511
theorem B1990055 : Blo 1325481 1990055 := bstep (se 1 (by rfl) ⟨1492541, by rfl⟩ : syracuseStep 1990055 = 2985083) B2985083
theorem B1326567 : Blo 1325481 1326567 := bstep (se 1 (by rfl) ⟨994925, by rfl⟩ : syracuseStep 1326567 = 1989851) B1989851
theorem B1990139 : Blo 1325481 1990139 := bstep (se 1 (by rfl) ⟨1492604, by rfl⟩ : syracuseStep 1990139 = 2985209) B2985209
theorem B1326683 : Blo 1325481 1326683 := bstep (se 1 (by rfl) ⟨995012, by rfl⟩ : syracuseStep 1326683 = 1990025) B1990025
theorem B1990235 : Blo 1325481 1990235 := bstep (se 1 (by rfl) ⟨1492676, by rfl⟩ : syracuseStep 1990235 = 2985353) B2985353
theorem B1990319 : Blo 1325481 1990319 := bstep (se 1 (by rfl) ⟨1492739, by rfl⟩ : syracuseStep 1990319 = 2985479) B2985479
theorem B4251323 : Blo 1325481 4251323 := bstep (se 1 (by rfl) ⟨3188492, by rfl⟩ : syracuseStep 4251323 = 6376985) B6376985
theorem B1990439 : Blo 1325481 1990439 := bstep (se 1 (by rfl) ⟨1492829, by rfl⟩ : syracuseStep 1990439 = 2985659) B2985659
theorem B3776311 : Blo 1325481 3776311 := bstep (se 1 (by rfl) ⟨2832233, by rfl⟩ : syracuseStep 3776311 = 5664467) B5664467
theorem B1326919 : Blo 1325481 1326919 := bstep (se 1 (by rfl) ⟨995189, by rfl⟩ : syracuseStep 1326919 = 1990379) B1990379
theorem B1990523 : Blo 1325481 1990523 := bstep (se 1 (by rfl) ⟨1492892, by rfl⟩ : syracuseStep 1990523 = 2985785) B2985785
theorem B1327071 : Blo 1325481 1327071 := bstep (se 1 (by rfl) ⟨995303, by rfl⟩ : syracuseStep 1327071 = 1990607) B1990607
theorem B40837121 : Blo 1325481 40837121 := bstep (se 2 (by rfl) ⟨15313920, by rfl⟩ : syracuseStep 40837121 = 30627841) B30627841
theorem B1327295 : Blo 1325481 1327295 := bstep (se 1 (by rfl) ⟨995471, by rfl⟩ : syracuseStep 1327295 = 1990943) B1990943
theorem B1327311 : Blo 1325481 1327311 := bstep (se 1 (by rfl) ⟨995483, by rfl⟩ : syracuseStep 1327311 = 1990967) B1990967
theorem B1327359 : Blo 1325481 1327359 := bstep (se 1 (by rfl) ⟨995519, by rfl⟩ : syracuseStep 1327359 = 1991039) B1991039
theorem B1327407 : Blo 1325481 1327407 := bstep (se 1 (by rfl) ⟨995555, by rfl⟩ : syracuseStep 1327407 = 1991111) B1991111
theorem B1991195 : Blo 1325481 1991195 := bstep (se 1 (by rfl) ⟨1493396, by rfl⟩ : syracuseStep 1991195 = 2986793) B2986793
theorem B2687519 : Blo 1325481 2687519 := bstep (se 1 (by rfl) ⟨2015639, by rfl⟩ : syracuseStep 2687519 = 4031279) B4031279
theorem B10076723 : Blo 1325481 10076723 := bstep (se 1 (by rfl) ⟨7557542, by rfl⟩ : syracuseStep 10076723 = 15115085) B15115085
theorem B10068947 : Blo 1325481 10068947 := bstep (se 1 (by rfl) ⟨7551710, by rfl⟩ : syracuseStep 10068947 = 15103421) B15103421
theorem B1492015 : Blo 1325481 1492015 := bstep (se 1 (by rfl) ⟨1119011, by rfl⟩ : syracuseStep 1492015 = 2238023) B2238023
theorem B2983103 : Blo 1325481 2983103 := bstep (se 1 (by rfl) ⟨2237327, by rfl⟩ : syracuseStep 2983103 = 4474655) B4474655
theorem B1492159 : Blo 1325481 1492159 := bstep (se 1 (by rfl) ⟨1119119, by rfl⟩ : syracuseStep 1492159 = 2238239) B2238239
theorem B2237753 : Blo 1325481 2237753 := bstep (se 2 (by rfl) ⟨839157, by rfl⟩ : syracuseStep 2237753 = 1678315) B1678315
theorem B6718787 : Blo 1325481 6718787 := bstep (se 1 (by rfl) ⟨5039090, by rfl⟩ : syracuseStep 6718787 = 10078181) B10078181
theorem B2983247 : Blo 1325481 2983247 := bstep (se 1 (by rfl) ⟨2237435, by rfl⟩ : syracuseStep 2983247 = 4474871) B4474871
theorem B1492303 : Blo 1325481 1492303 := bstep (se 1 (by rfl) ⟨1119227, by rfl⟩ : syracuseStep 1492303 = 2238455) B2238455
theorem B2983337 : Blo 1325481 2983337 := bstep (se 2 (by rfl) ⟨1118751, by rfl⟩ : syracuseStep 2983337 = 2237503) B2237503
theorem B8496677 : Blo 1325481 8496677 := bstep (se 4 (by rfl) ⟨796563, by rfl⟩ : syracuseStep 8496677 = 1593127) B1593127
theorem B5375783 : Blo 1325481 5375783 := bstep (se 1 (by rfl) ⟨4031837, by rfl⟩ : syracuseStep 5375783 = 8063675) B8063675
theorem B38774575 : Blo 1325481 38774575 := bstep (se 1 (by rfl) ⟨29080931, by rfl⟩ : syracuseStep 38774575 = 58161863) B58161863
theorem B8505161 : Blo 1325481 8505161 := bstep (se 2 (by rfl) ⟨3189435, by rfl⟩ : syracuseStep 8505161 = 6378871) B6378871
theorem B10495831 : Blo 1325481 10495831 := bstep (se 1 (by rfl) ⟨7871873, by rfl⟩ : syracuseStep 10495831 = 15743747) B15743747
theorem B2983823 : Blo 1325481 2983823 := bstep (se 1 (by rfl) ⟨2237867, by rfl⟩ : syracuseStep 2983823 = 4475735) B4475735
theorem B2983967 : Blo 1325481 2983967 := bstep (se 1 (by rfl) ⟨2237975, by rfl⟩ : syracuseStep 2983967 = 4475951) B4475951
theorem B1493023 : Blo 1325481 1493023 := bstep (se 1 (by rfl) ⟨1119767, by rfl⟩ : syracuseStep 1493023 = 2239535) B2239535
theorem B6719597 : Blo 1325481 6719597 := bstep (se 3 (by rfl) ⟨1259924, by rfl⟩ : syracuseStep 6719597 = 2519849) B2519849
theorem B11331737 : Blo 1325481 11331737 := bstep (se 2 (by rfl) ⟨4249401, by rfl⟩ : syracuseStep 11331737 = 8498803) B8498803
theorem B2984219 : Blo 1325481 2984219 := bstep (se 1 (by rfl) ⟨2238164, by rfl⟩ : syracuseStep 2984219 = 4476329) B4476329
theorem B1493275 : Blo 1325481 1493275 := bstep (se 1 (by rfl) ⟨1119956, by rfl⟩ : syracuseStep 1493275 = 2239913) B2239913
theorem B11323739 : Blo 1325481 11323739 := bstep (se 1 (by rfl) ⟨8492804, by rfl⟩ : syracuseStep 11323739 = 16985609) B16985609
theorem B2984543 : Blo 1325481 2984543 := bstep (se 1 (by rfl) ⟨2238407, by rfl⟩ : syracuseStep 2984543 = 4476815) B4476815
theorem B12094049 : Blo 1325481 12094049 := bstep (se 2 (by rfl) ⟨4535268, by rfl⟩ : syracuseStep 12094049 = 9070537) B9070537
theorem B9071249 : Blo 1325481 9071249 := bstep (se 2 (by rfl) ⟨3401718, by rfl⟩ : syracuseStep 9071249 = 6803437) B6803437
theorem B38259377 : Blo 1325481 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B2984795 : Blo 1325481 2984795 := bstep (se 1 (by rfl) ⟨2238596, by rfl⟩ : syracuseStep 2984795 = 4477193) B4477193
theorem B5032955 : Blo 1325481 5032955 := bstep (se 1 (by rfl) ⟨3774716, by rfl⟩ : syracuseStep 5032955 = 7549433) B7549433
theorem B2518057 : Blo 1325481 2518057 := bstep (se 2 (by rfl) ⟨944271, by rfl⟩ : syracuseStep 2518057 = 1888543) B1888543
theorem B10488997 : Blo 1325481 10488997 := bstep (se 4 (by rfl) ⟨983343, by rfl⟩ : syracuseStep 10488997 = 1966687) B1966687
theorem B2125111 : Blo 1325481 2125111 := bstep (se 1 (by rfl) ⟨1593833, by rfl⟩ : syracuseStep 2125111 = 3187667) B3187667
theorem B2239967 : Blo 1325481 2239967 := bstep (se 1 (by rfl) ⟨1679975, by rfl⟩ : syracuseStep 2239967 = 3359951) B3359951
theorem B2985551 : Blo 1325481 2985551 := bstep (se 1 (by rfl) ⟨2239163, by rfl⟩ : syracuseStep 2985551 = 4478327) B4478327
theorem B2518847 : Blo 1325481 2518847 := bstep (se 1 (by rfl) ⟨1889135, by rfl⟩ : syracuseStep 2518847 = 3778271) B3778271
theorem B6377447 : Blo 1325481 6377447 := bstep (se 1 (by rfl) ⟨4783085, by rfl⟩ : syracuseStep 6377447 = 9566171) B9566171
theorem B4476923 : Blo 1325481 4476923 := bstep (se 1 (by rfl) ⟨3357692, by rfl⟩ : syracuseStep 4476923 = 6715385) B6715385
theorem B2519113 : Blo 1325481 2519113 := bstep (se 2 (by rfl) ⟨944667, by rfl⟩ : syracuseStep 2519113 = 1889335) B1889335
theorem B2986091 : Blo 1325481 2986091 := bstep (se 1 (by rfl) ⟨2239568, by rfl⟩ : syracuseStep 2986091 = 4479137) B4479137
theorem B2986145 : Blo 1325481 2986145 := bstep (se 2 (by rfl) ⟨1119804, by rfl⟩ : syracuseStep 2986145 = 2239609) B2239609
theorem B10203367 : Blo 1325481 10203367 := bstep (se 1 (by rfl) ⟨7652525, by rfl⟩ : syracuseStep 10203367 = 15305051) B15305051
theorem B19124495 : Blo 1325481 19124495 := bstep (se 1 (by rfl) ⟨14343371, by rfl⟩ : syracuseStep 19124495 = 28686743) B28686743
theorem B5665049 : Blo 1325481 5665049 := bstep (se 2 (by rfl) ⟨2124393, by rfl⟩ : syracuseStep 5665049 = 4248787) B4248787
theorem B10072349 : Blo 1325481 10072349 := bstep (se 3 (by rfl) ⟨1888565, by rfl⟩ : syracuseStep 10072349 = 3777131) B3777131
theorem B2986271 : Blo 1325481 2986271 := bstep (se 1 (by rfl) ⟨2239703, by rfl⟩ : syracuseStep 2986271 = 4479407) B4479407
theorem B11809223 : Blo 1325481 11809223 := bstep (se 1 (by rfl) ⟨8856917, by rfl⟩ : syracuseStep 11809223 = 17713835) B17713835
theorem B5665409 : Blo 1325481 5665409 := bstep (se 2 (by rfl) ⟨2124528, by rfl⟩ : syracuseStep 5665409 = 4249057) B4249057
theorem B4477787 : Blo 1325481 4477787 := bstep (se 1 (by rfl) ⟨3358340, by rfl⟩ : syracuseStep 4477787 = 6716681) B6716681
theorem B2831311 : Blo 1325481 2831311 := bstep (se 1 (by rfl) ⟨2123483, by rfl⟩ : syracuseStep 2831311 = 4246967) B4246967
theorem B2831431 : Blo 1325481 2831431 := bstep (se 1 (by rfl) ⟨2123573, by rfl⟩ : syracuseStep 2831431 = 4247147) B4247147
theorem B2389063 : Blo 1325481 2389063 := bstep (se 1 (by rfl) ⟨1791797, by rfl⟩ : syracuseStep 2389063 = 3583595) B3583595
theorem B5035081 : Blo 1325481 5035081 := bstep (se 2 (by rfl) ⟨1888155, by rfl⟩ : syracuseStep 5035081 = 3776311) B3776311
theorem B10073321 : Blo 1325481 10073321 := bstep (se 2 (by rfl) ⟨3777495, by rfl⟩ : syracuseStep 10073321 = 7554991) B7554991
theorem B2831611 : Blo 1325481 2831611 := bstep (se 1 (by rfl) ⟨2123708, by rfl⟩ : syracuseStep 2831611 = 4247417) B4247417
theorem B33985979 : Blo 1325481 33985979 := bstep (se 1 (by rfl) ⟨25489484, by rfl⟩ : syracuseStep 33985979 = 50978969) B50978969
theorem B9082361 : Blo 1325481 9082361 := bstep (se 2 (by rfl) ⟨3405885, by rfl⟩ : syracuseStep 9082361 = 6811771) B6811771
theorem B16143887 : Blo 1325481 16143887 := bstep (se 1 (by rfl) ⟨12107915, by rfl⟩ : syracuseStep 16143887 = 24215831) B24215831
theorem B15324731 : Blo 1325481 15324731 := bstep (se 1 (by rfl) ⟨11493548, by rfl⟩ : syracuseStep 15324731 = 22987097) B22987097
theorem B3831391 : Blo 1325481 3831391 := bstep (se 1 (by rfl) ⟨2873543, by rfl⟩ : syracuseStep 3831391 = 5747087) B5747087
theorem B2832097 : Blo 1325481 2832097 := bstep (se 2 (by rfl) ⟨1062036, by rfl⟩ : syracuseStep 2832097 = 2124073) B2124073
theorem B1988423 : Blo 1325481 1988423 := bstep (se 1 (by rfl) ⟨1491317, by rfl⟩ : syracuseStep 1988423 = 2982635) B2982635
theorem B7550891 : Blo 1325481 7550891 := bstep (se 1 (by rfl) ⟨5663168, by rfl⟩ : syracuseStep 7550891 = 11326337) B11326337
theorem B14333993 : Blo 1325481 14333993 := bstep (se 2 (by rfl) ⟨5375247, by rfl⟩ : syracuseStep 14333993 = 10750495) B10750495
theorem B2832575 : Blo 1325481 2832575 := bstep (se 1 (by rfl) ⟨2124431, by rfl⟩ : syracuseStep 2832575 = 4248863) B4248863
theorem B3356903 : Blo 1325481 3356903 := bstep (se 1 (by rfl) ⟨2517677, by rfl⟩ : syracuseStep 3356903 = 5035355) B5035355
theorem B1989023 : Blo 1325481 1989023 := bstep (se 1 (by rfl) ⟨1491767, by rfl⟩ : syracuseStep 1989023 = 2983535) B2983535
theorem B1325519 : Blo 1325481 1325519 := bstep (se 1 (by rfl) ⟨994139, by rfl⟩ : syracuseStep 1325519 = 1988279) B1988279
theorem B1325543 : Blo 1325481 1325543 := bstep (se 1 (by rfl) ⟨994157, by rfl⟩ : syracuseStep 1325543 = 1988315) B1988315
theorem B1989095 : Blo 1325481 1989095 := bstep (se 1 (by rfl) ⟨1491821, by rfl⟩ : syracuseStep 1989095 = 2983643) B2983643
theorem B4479515 : Blo 1325481 4479515 := bstep (se 1 (by rfl) ⟨3359636, by rfl⟩ : syracuseStep 4479515 = 6719273) B6719273
theorem B1325659 : Blo 1325481 1325659 := bstep (se 1 (by rfl) ⟨994244, by rfl⟩ : syracuseStep 1325659 = 1988489) B1988489
theorem B1915483 : Blo 1325481 1915483 := bstep (se 1 (by rfl) ⟨1436612, by rfl⟩ : syracuseStep 1915483 = 2873225) B2873225
theorem B6716033 : Blo 1325481 6716033 := bstep (se 2 (by rfl) ⟨2518512, by rfl⟩ : syracuseStep 6716033 = 5037025) B5037025
theorem B1325727 : Blo 1325481 1325727 := bstep (se 1 (by rfl) ⟨994295, by rfl⟩ : syracuseStep 1325727 = 1988591) B1988591
theorem B18160301 : Blo 1325481 18160301 := bstep (se 3 (by rfl) ⟨3405056, by rfl⟩ : syracuseStep 18160301 = 6810113) B6810113
theorem B1325895 : Blo 1325481 1325895 := bstep (se 1 (by rfl) ⟨994421, by rfl⟩ : syracuseStep 1325895 = 1988843) B1988843
theorem B2153287 : Blo 1325481 2153287 := bstep (se 1 (by rfl) ⟨1614965, by rfl⟩ : syracuseStep 2153287 = 3229931) B3229931
theorem B1325935 : Blo 1325481 1325935 := bstep (se 1 (by rfl) ⟨994451, by rfl⟩ : syracuseStep 1325935 = 1988903) B1988903
theorem B3775355 : Blo 1325481 3775355 := bstep (se 1 (by rfl) ⟨2831516, by rfl⟩ : syracuseStep 3775355 = 5663033) B5663033
theorem B1325991 : Blo 1325481 1325991 := bstep (se 1 (by rfl) ⟨994493, by rfl⟩ : syracuseStep 1325991 = 1988987) B1988987
theorem B2833319 : Blo 1325481 2833319 := bstep (se 1 (by rfl) ⟨2124989, by rfl⟩ : syracuseStep 2833319 = 4249979) B4249979
theorem B3275687 : Blo 1325481 3275687 := bstep (se 1 (by rfl) ⟨2456765, by rfl⟩ : syracuseStep 3275687 = 4913531) B4913531
theorem B2390995 : Blo 1325481 2390995 := bstep (se 1 (by rfl) ⟨1793246, by rfl⟩ : syracuseStep 2390995 = 3586493) B3586493
theorem B1326171 : Blo 1325481 1326171 := bstep (se 1 (by rfl) ⟨994628, by rfl⟩ : syracuseStep 1326171 = 1989257) B1989257
theorem B11336861 : Blo 1325481 11336861 := bstep (se 3 (by rfl) ⟨2125661, by rfl⟩ : syracuseStep 11336861 = 4251323) B4251323
theorem B1326287 : Blo 1325481 1326287 := bstep (se 1 (by rfl) ⟨994715, by rfl⟩ : syracuseStep 1326287 = 1989431) B1989431
theorem B1989839 : Blo 1325481 1989839 := bstep (se 1 (by rfl) ⟨1492379, by rfl⟩ : syracuseStep 1989839 = 2984759) B2984759
theorem B1326311 : Blo 1325481 1326311 := bstep (se 1 (by rfl) ⟨994733, by rfl⟩ : syracuseStep 1326311 = 1989467) B1989467
theorem B1326407 : Blo 1325481 1326407 := bstep (se 1 (by rfl) ⟨994805, by rfl⟩ : syracuseStep 1326407 = 1989611) B1989611
theorem B1989959 : Blo 1325481 1989959 := bstep (se 1 (by rfl) ⟨1492469, by rfl⟩ : syracuseStep 1989959 = 2984939) B2984939
theorem B6716843 : Blo 1325481 6716843 := bstep (se 1 (by rfl) ⟨5037632, by rfl⟩ : syracuseStep 6716843 = 10075265) B10075265
theorem B1326543 : Blo 1325481 1326543 := bstep (se 1 (by rfl) ⟨994907, by rfl⟩ : syracuseStep 1326543 = 1989815) B1989815
theorem B1990121 : Blo 1325481 1990121 := bstep (se 2 (by rfl) ⟨746295, by rfl⟩ : syracuseStep 1990121 = 1492591) B1492591
theorem B57384557 : Blo 1325481 57384557 := bstep (se 3 (by rfl) ⟨10759604, by rfl⟩ : syracuseStep 57384557 = 21519209) B21519209
theorem B1326703 : Blo 1325481 1326703 := bstep (se 1 (by rfl) ⟨995027, by rfl⟩ : syracuseStep 1326703 = 1990055) B1990055
theorem B1990265 : Blo 1325481 1990265 := bstep (se 2 (by rfl) ⟨746349, by rfl⟩ : syracuseStep 1990265 = 1492699) B1492699
theorem B1326759 : Blo 1325481 1326759 := bstep (se 1 (by rfl) ⟨995069, by rfl⟩ : syracuseStep 1326759 = 1990139) B1990139
theorem B1793755 : Blo 1325481 1793755 := bstep (se 1 (by rfl) ⟨1345316, by rfl⟩ : syracuseStep 1793755 = 2690633) B2690633
theorem B1326823 : Blo 1325481 1326823 := bstep (se 1 (by rfl) ⟨995117, by rfl⟩ : syracuseStep 1326823 = 1990235) B1990235
theorem B1326879 : Blo 1325481 1326879 := bstep (se 1 (by rfl) ⟨995159, by rfl⟩ : syracuseStep 1326879 = 1990319) B1990319
theorem B1326959 : Blo 1325481 1326959 := bstep (se 1 (by rfl) ⟨995219, by rfl⟩ : syracuseStep 1326959 = 1990439) B1990439
theorem B1990511 : Blo 1325481 1990511 := bstep (se 1 (by rfl) ⟨1492883, by rfl⟩ : syracuseStep 1990511 = 2985767) B2985767
theorem B16990073 : Blo 1325481 16990073 := bstep (se 2 (by rfl) ⟨6371277, by rfl⟩ : syracuseStep 16990073 = 12742555) B12742555
theorem B1327015 : Blo 1325481 1327015 := bstep (se 1 (by rfl) ⟨995261, by rfl⟩ : syracuseStep 1327015 = 1990523) B1990523
theorem B1417159 : Blo 1325481 1417159 := bstep (se 1 (by rfl) ⟨1062869, by rfl⟩ : syracuseStep 1417159 = 2125739) B2125739
theorem B40812497 : Blo 1325481 40812497 := bstep (se 2 (by rfl) ⟨15304686, by rfl⟩ : syracuseStep 40812497 = 30609373) B30609373
theorem B1990697 : Blo 1325481 1990697 := bstep (se 2 (by rfl) ⟨746511, by rfl⟩ : syracuseStep 1990697 = 1493023) B1493023
theorem B1990727 : Blo 1325481 1990727 := bstep (se 1 (by rfl) ⟨1493045, by rfl⟩ : syracuseStep 1990727 = 2986091) B2986091
theorem B3358817 : Blo 1325481 3358817 := bstep (se 2 (by rfl) ⟨1259556, by rfl⟩ : syracuseStep 3358817 = 2519113) B2519113
theorem B1990763 : Blo 1325481 1990763 := bstep (se 1 (by rfl) ⟨1493072, by rfl⟩ : syracuseStep 1990763 = 2986145) B2986145
theorem B3776699 : Blo 1325481 3776699 := bstep (se 1 (by rfl) ⟨2832524, by rfl⟩ : syracuseStep 3776699 = 5665049) B5665049
theorem B1990847 : Blo 1325481 1990847 := bstep (se 1 (by rfl) ⟨1493135, by rfl⟩ : syracuseStep 1990847 = 2986271) B2986271
theorem B7872815 : Blo 1325481 7872815 := bstep (se 1 (by rfl) ⟨5904611, by rfl⟩ : syracuseStep 7872815 = 11809223) B11809223
theorem B1327463 : Blo 1325481 1327463 := bstep (se 1 (by rfl) ⟨995597, by rfl⟩ : syracuseStep 1327463 = 1991195) B1991195
theorem B6717815 : Blo 1325481 6717815 := bstep (se 1 (by rfl) ⟨5038361, by rfl⟩ : syracuseStep 6717815 = 10076723) B10076723
theorem B1991033 : Blo 1325481 1991033 := bstep (se 2 (by rfl) ⟨746637, by rfl⟩ : syracuseStep 1991033 = 1493275) B1493275
theorem B3776939 : Blo 1325481 3776939 := bstep (se 1 (by rfl) ⟨2832704, by rfl⟩ : syracuseStep 3776939 = 5665409) B5665409
theorem B7553533 : Blo 1325481 7553533 := bstep (se 3 (by rfl) ⟨1416287, by rfl⟩ : syracuseStep 7553533 = 2832575) B2832575
theorem B1491835 : Blo 1325481 1491835 := bstep (se 1 (by rfl) ⟨1118876, by rfl⟩ : syracuseStep 1491835 = 2237753) B2237753
theorem B6054907 : Blo 1325481 6054907 := bstep (se 1 (by rfl) ⟨4541180, by rfl⟩ : syracuseStep 6054907 = 9082361) B9082361
theorem B10216487 : Blo 1325481 10216487 := bstep (se 1 (by rfl) ⟨7662365, by rfl⟩ : syracuseStep 10216487 = 15324731) B15324731
theorem B5670107 : Blo 1325481 5670107 := bstep (se 1 (by rfl) ⟨4252580, by rfl⟩ : syracuseStep 5670107 = 8505161) B8505161
theorem B3187993 : Blo 1325481 3187993 := bstep (se 2 (by rfl) ⟨1195497, by rfl⟩ : syracuseStep 3187993 = 2390995) B2390995
theorem B43050365 : Blo 1325481 43050365 := bstep (se 3 (by rfl) ⟨8071943, by rfl⟩ : syracuseStep 43050365 = 16143887) B16143887
theorem B7554491 : Blo 1325481 7554491 := bstep (se 1 (by rfl) ⟨5665868, by rfl⟩ : syracuseStep 7554491 = 11331737) B11331737
theorem B2237935 : Blo 1325481 2237935 := bstep (se 1 (by rfl) ⟨1678451, by rfl⟩ : syracuseStep 2237935 = 3356903) B3356903
theorem B13985329 : Blo 1325481 13985329 := bstep (se 2 (by rfl) ⟨5244498, by rfl⟩ : syracuseStep 13985329 = 10488997) B10488997
theorem B8062699 : Blo 1325481 8062699 := bstep (se 1 (by rfl) ⟨6047024, by rfl⟩ : syracuseStep 8062699 = 12094049) B12094049
theorem B2516903 : Blo 1325481 2516903 := bstep (se 1 (by rfl) ⟨1887677, by rfl⟩ : syracuseStep 2516903 = 3775355) B3775355
theorem B1493311 : Blo 1325481 1493311 := bstep (se 1 (by rfl) ⟨1119983, by rfl⟩ : syracuseStep 1493311 = 2239967) B2239967
theorem B7555517 : Blo 1325481 7555517 := bstep (se 3 (by rfl) ⟨1416659, by rfl⟩ : syracuseStep 7555517 = 2833319) B2833319
theorem B13994441 : Blo 1325481 13994441 := bstep (se 2 (by rfl) ⟨5247915, by rfl⟩ : syracuseStep 13994441 = 10495831) B10495831
theorem B27208331 : Blo 1325481 27208331 := bstep (se 1 (by rfl) ⟨20406248, by rfl⟩ : syracuseStep 27208331 = 40812497) B40812497
theorem B2984615 : Blo 1325481 2984615 := bstep (se 1 (by rfl) ⟨2238461, by rfl⟩ : syracuseStep 2984615 = 4476923) B4476923
theorem B27224747 : Blo 1325481 27224747 := bstep (se 1 (by rfl) ⟨20418560, by rfl⟩ : syracuseStep 27224747 = 40837121) B40837121
theorem B12749663 : Blo 1325481 12749663 := bstep (se 1 (by rfl) ⟨9562247, by rfl⟩ : syracuseStep 12749663 = 19124495) B19124495
theorem B2985191 : Blo 1325481 2985191 := bstep (se 1 (by rfl) ⟨2238893, by rfl⟩ : syracuseStep 2985191 = 4477787) B4477787
theorem B6712631 : Blo 1325481 6712631 := bstep (se 1 (by rfl) ⟨5034473, by rfl⟩ : syracuseStep 6712631 = 10068947) B10068947
theorem B5664451 : Blo 1325481 5664451 := bstep (se 1 (by rfl) ⟨4248338, by rfl⟩ : syracuseStep 5664451 = 8496677) B8496677
theorem B2871049 : Blo 1325481 2871049 := bstep (se 2 (by rfl) ⟨1076643, by rfl⟩ : syracuseStep 2871049 = 2153287) B2153287
theorem B3583855 : Blo 1325481 3583855 := bstep (se 1 (by rfl) ⟨2687891, by rfl⟩ : syracuseStep 3583855 = 5375783) B5375783
theorem B5033927 : Blo 1325481 5033927 := bstep (se 1 (by rfl) ⟨3775445, by rfl⟩ : syracuseStep 5033927 = 7550891) B7550891
theorem B9555995 : Blo 1325481 9555995 := bstep (se 1 (by rfl) ⟨7166996, by rfl⟩ : syracuseStep 9555995 = 14333993) B14333993
theorem B6713441 : Blo 1325481 6713441 := bstep (se 2 (by rfl) ⟨2517540, by rfl⟩ : syracuseStep 6713441 = 5035081) B5035081
theorem B7549159 : Blo 1325481 7549159 := bstep (se 1 (by rfl) ⟨5661869, by rfl⟩ : syracuseStep 7549159 = 11323739) B11323739
theorem B2986343 : Blo 1325481 2986343 := bstep (se 1 (by rfl) ⟨2239757, by rfl⟩ : syracuseStep 2986343 = 4479515) B4479515
theorem B4477355 : Blo 1325481 4477355 := bstep (se 1 (by rfl) ⟨3358016, by rfl⟩ : syracuseStep 4477355 = 6716033) B6716033
theorem B25506251 : Blo 1325481 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B2183791 : Blo 1325481 2183791 := bstep (se 1 (by rfl) ⟨1637843, by rfl⟩ : syracuseStep 2183791 = 3275687) B3275687
theorem B3355303 : Blo 1325481 3355303 := bstep (se 1 (by rfl) ⟨2516477, by rfl⟩ : syracuseStep 3355303 = 5032955) B5032955
theorem B7557907 : Blo 1325481 7557907 := bstep (se 1 (by rfl) ⟨5668430, by rfl⟩ : syracuseStep 7557907 = 11336861) B11336861
theorem B5108521 : Blo 1325481 5108521 := bstep (se 2 (by rfl) ⟨1915695, by rfl⟩ : syracuseStep 5108521 = 3831391) B3831391
theorem B4477895 : Blo 1325481 4477895 := bstep (se 1 (by rfl) ⟨3358421, by rfl⟩ : syracuseStep 4477895 = 6716843) B6716843
theorem B7558181 : Blo 1325481 7558181 := bstep (se 4 (by rfl) ⟨708579, by rfl⟩ : syracuseStep 7558181 = 1417159) B1417159
theorem B11326715 : Blo 1325481 11326715 := bstep (se 1 (by rfl) ⟨8495036, by rfl⟩ : syracuseStep 11326715 = 16990073) B16990073
theorem B6714899 : Blo 1325481 6714899 := bstep (se 1 (by rfl) ⟨5036174, by rfl⟩ : syracuseStep 6714899 = 10072349) B10072349
theorem B13604489 : Blo 1325481 13604489 := bstep (se 2 (by rfl) ⟨5101683, by rfl⟩ : syracuseStep 13604489 = 10203367) B10203367
theorem B2553977 : Blo 1325481 2553977 := bstep (se 2 (by rfl) ⟨957741, by rfl⟩ : syracuseStep 2553977 = 1915483) B1915483
theorem B1988735 : Blo 1325481 1988735 := bstep (se 1 (by rfl) ⟨1491551, by rfl⟩ : syracuseStep 1988735 = 2983103) B2983103
theorem B6715547 : Blo 1325481 6715547 := bstep (se 1 (by rfl) ⟨5036660, by rfl⟩ : syracuseStep 6715547 = 10073321) B10073321
theorem B4479191 : Blo 1325481 4479191 := bstep (se 1 (by rfl) ⟨3359393, by rfl⟩ : syracuseStep 4479191 = 6718787) B6718787
theorem B1988831 : Blo 1325481 1988831 := bstep (se 1 (by rfl) ⟨1491623, by rfl⟩ : syracuseStep 1988831 = 2983247) B2983247
theorem B1988891 : Blo 1325481 1988891 := bstep (se 1 (by rfl) ⟨1491668, by rfl⟩ : syracuseStep 1988891 = 2983337) B2983337
theorem B22657319 : Blo 1325481 22657319 := bstep (se 1 (by rfl) ⟨16992989, by rfl⟩ : syracuseStep 22657319 = 33985979) B33985979
theorem B1325615 : Blo 1325481 1325615 := bstep (se 1 (by rfl) ⟨994211, by rfl⟩ : syracuseStep 1325615 = 1988423) B1988423
theorem B1989215 : Blo 1325481 1989215 := bstep (se 1 (by rfl) ⟨1491911, by rfl⟩ : syracuseStep 1989215 = 2983823) B2983823
theorem B3775081 : Blo 1325481 3775081 := bstep (se 2 (by rfl) ⟨1415655, by rfl⟩ : syracuseStep 3775081 = 2831311) B2831311
theorem B1989311 : Blo 1325481 1989311 := bstep (se 1 (by rfl) ⟨1491983, by rfl⟩ : syracuseStep 1989311 = 2983967) B2983967
theorem B3357409 : Blo 1325481 3357409 := bstep (se 2 (by rfl) ⟨1259028, by rfl⟩ : syracuseStep 3357409 = 2518057) B2518057
theorem B1989353 : Blo 1325481 1989353 := bstep (se 2 (by rfl) ⟨746007, by rfl⟩ : syracuseStep 1989353 = 1492015) B1492015
theorem B4479731 : Blo 1325481 4479731 := bstep (se 1 (by rfl) ⟨3359798, by rfl⟩ : syracuseStep 4479731 = 6719597) B6719597
theorem B7166717 : Blo 1325481 7166717 := bstep (se 3 (by rfl) ⟨1343759, by rfl⟩ : syracuseStep 7166717 = 2687519) B2687519
theorem B3775241 : Blo 1325481 3775241 := bstep (se 2 (by rfl) ⟨1415715, by rfl⟩ : syracuseStep 3775241 = 2831431) B2831431
theorem B3185417 : Blo 1325481 3185417 := bstep (se 2 (by rfl) ⟨1194531, by rfl⟩ : syracuseStep 3185417 = 2389063) B2389063
theorem B1989479 : Blo 1325481 1989479 := bstep (se 1 (by rfl) ⟨1492109, by rfl⟩ : syracuseStep 1989479 = 2984219) B2984219
theorem B1989545 : Blo 1325481 1989545 := bstep (se 2 (by rfl) ⟨746079, by rfl⟩ : syracuseStep 1989545 = 1492159) B1492159
theorem B1326015 : Blo 1325481 1326015 := bstep (se 1 (by rfl) ⟨994511, by rfl⟩ : syracuseStep 1326015 = 1989023) B1989023
theorem B1326063 : Blo 1325481 1326063 := bstep (se 1 (by rfl) ⟨994547, by rfl⟩ : syracuseStep 1326063 = 1989095) B1989095
theorem B3775481 : Blo 1325481 3775481 := bstep (se 2 (by rfl) ⟨1415805, by rfl⟩ : syracuseStep 3775481 = 2831611) B2831611
theorem B24189997 : Blo 1325481 24189997 := bstep (se 3 (by rfl) ⟨4535624, by rfl⟩ : syracuseStep 24189997 = 9071249) B9071249
theorem B1989695 : Blo 1325481 1989695 := bstep (se 1 (by rfl) ⟨1492271, by rfl⟩ : syracuseStep 1989695 = 2984543) B2984543
theorem B2833481 : Blo 1325481 2833481 := bstep (se 2 (by rfl) ⟨1062555, by rfl⟩ : syracuseStep 2833481 = 2125111) B2125111
theorem B1989737 : Blo 1325481 1989737 := bstep (se 2 (by rfl) ⟨746151, by rfl⟩ : syracuseStep 1989737 = 1492303) B1492303
theorem B12106867 : Blo 1325481 12106867 := bstep (se 1 (by rfl) ⟨9080150, by rfl⟩ : syracuseStep 12106867 = 18160301) B18160301
theorem B1989863 : Blo 1325481 1989863 := bstep (se 1 (by rfl) ⟨1492397, by rfl⟩ : syracuseStep 1989863 = 2984795) B2984795
theorem B1326559 : Blo 1325481 1326559 := bstep (se 1 (by rfl) ⟨994919, by rfl⟩ : syracuseStep 1326559 = 1989839) B1989839
theorem B1326639 : Blo 1325481 1326639 := bstep (se 1 (by rfl) ⟨994979, by rfl⟩ : syracuseStep 1326639 = 1989959) B1989959
theorem B2391673 : Blo 1325481 2391673 := bstep (se 2 (by rfl) ⟨896877, by rfl⟩ : syracuseStep 2391673 = 1793755) B1793755
theorem B3776129 : Blo 1325481 3776129 := bstep (se 2 (by rfl) ⟨1416048, by rfl⟩ : syracuseStep 3776129 = 2832097) B2832097
theorem B1326747 : Blo 1325481 1326747 := bstep (se 1 (by rfl) ⟨995060, by rfl⟩ : syracuseStep 1326747 = 1990121) B1990121
theorem B1990367 : Blo 1325481 1990367 := bstep (se 1 (by rfl) ⟨1492775, by rfl⟩ : syracuseStep 1990367 = 2985551) B2985551
theorem B51699433 : Blo 1325481 51699433 := bstep (se 2 (by rfl) ⟨19387287, by rfl⟩ : syracuseStep 51699433 = 38774575) B38774575
theorem B38256371 : Blo 1325481 38256371 := bstep (se 1 (by rfl) ⟨28692278, by rfl⟩ : syracuseStep 38256371 = 57384557) B57384557
theorem B1326843 : Blo 1325481 1326843 := bstep (se 1 (by rfl) ⟨995132, by rfl⟩ : syracuseStep 1326843 = 1990265) B1990265
theorem B1679231 : Blo 1325481 1679231 := bstep (se 1 (by rfl) ⟨1259423, by rfl⟩ : syracuseStep 1679231 = 2518847) B2518847
theorem B1327007 : Blo 1325481 1327007 := bstep (se 1 (by rfl) ⟨995255, by rfl⟩ : syracuseStep 1327007 = 1990511) B1990511
theorem B4251631 : Blo 1325481 4251631 := bstep (se 1 (by rfl) ⟨3188723, by rfl⟩ : syracuseStep 4251631 = 6377447) B6377447
theorem B1327131 : Blo 1325481 1327131 := bstep (se 1 (by rfl) ⟨995348, by rfl⟩ : syracuseStep 1327131 = 1990697) B1990697
theorem B1327151 : Blo 1325481 1327151 := bstep (se 1 (by rfl) ⟨995363, by rfl⟩ : syracuseStep 1327151 = 1990727) B1990727
theorem B1327175 : Blo 1325481 1327175 := bstep (se 1 (by rfl) ⟨995381, by rfl⟩ : syracuseStep 1327175 = 1990763) B1990763
theorem B1327231 : Blo 1325481 1327231 := bstep (se 1 (by rfl) ⟨995423, by rfl⟩ : syracuseStep 1327231 = 1990847) B1990847
theorem B1990895 : Blo 1325481 1990895 := bstep (se 1 (by rfl) ⟨1493171, by rfl⟩ : syracuseStep 1990895 = 2986343) B2986343
theorem B1327355 : Blo 1325481 1327355 := bstep (se 1 (by rfl) ⟨995516, by rfl⟩ : syracuseStep 1327355 = 1991033) B1991033
theorem B1991081 : Blo 1325481 1991081 := bstep (se 2 (by rfl) ⟨746655, by rfl⟩ : syracuseStep 1991081 = 1493311) B1493311
theorem B5038787 : Blo 1325481 5038787 := bstep (se 1 (by rfl) ⟨3779090, by rfl⟩ : syracuseStep 5038787 = 7558181) B7558181
theorem B4473737 : Blo 1325481 4473737 := bstep (se 2 (by rfl) ⟨1677651, by rfl⟩ : syracuseStep 4473737 = 3355303) B3355303
theorem B10077209 : Blo 1325481 10077209 := bstep (se 2 (by rfl) ⟨3778953, by rfl⟩ : syracuseStep 10077209 = 7557907) B7557907
theorem B9069659 : Blo 1325481 9069659 := bstep (se 1 (by rfl) ⟨6802244, by rfl⟩ : syracuseStep 9069659 = 13604489) B13604489
theorem B32253329 : Blo 1325481 32253329 := bstep (se 2 (by rfl) ⟨12094998, by rfl⟩ : syracuseStep 32253329 = 24189997) B24189997
theorem B18138887 : Blo 1325481 18138887 := bstep (se 1 (by rfl) ⟨13604165, by rfl⟩ : syracuseStep 18138887 = 27208331) B27208331
theorem B4777811 : Blo 1325481 4777811 := bstep (se 1 (by rfl) ⟨3583358, by rfl⟩ : syracuseStep 4777811 = 7166717) B7166717
theorem B2516827 : Blo 1325481 2516827 := bstep (se 1 (by rfl) ⟨1887620, by rfl⟩ : syracuseStep 2516827 = 3775241) B3775241
theorem B2983913 : Blo 1325481 2983913 := bstep (se 2 (by rfl) ⟨1118967, by rfl⟩ : syracuseStep 2983913 = 2237935) B2237935
theorem B2516987 : Blo 1325481 2516987 := bstep (se 1 (by rfl) ⟨1887740, by rfl⟩ : syracuseStep 2516987 = 3775481) B3775481
theorem B18647105 : Blo 1325481 18647105 := bstep (se 2 (by rfl) ⟨6992664, by rfl⟩ : syracuseStep 18647105 = 13985329) B13985329
theorem B3188897 : Blo 1325481 3188897 := bstep (se 2 (by rfl) ⟨1195836, by rfl⟩ : syracuseStep 3188897 = 2391673) B2391673
theorem B4475087 : Blo 1325481 4475087 := bstep (se 1 (by rfl) ⟨3356315, by rfl⟩ : syracuseStep 4475087 = 6712631) B6712631
theorem B33999101 : Blo 1325481 33999101 := bstep (se 3 (by rfl) ⟨6374831, by rfl⟩ : syracuseStep 33999101 = 12749663) B12749663
theorem B10750265 : Blo 1325481 10750265 := bstep (se 2 (by rfl) ⟨4031349, by rfl⟩ : syracuseStep 10750265 = 8062699) B8062699
theorem B3828065 : Blo 1325481 3828065 := bstep (se 2 (by rfl) ⟨1435524, by rfl⟩ : syracuseStep 3828065 = 2871049) B2871049
theorem B2517419 : Blo 1325481 2517419 := bstep (se 1 (by rfl) ⟨1888064, by rfl⟩ : syracuseStep 2517419 = 3776129) B3776129
theorem B4778473 : Blo 1325481 4778473 := bstep (se 2 (by rfl) ⟨1791927, by rfl⟩ : syracuseStep 4778473 = 3583855) B3583855
theorem B25504247 : Blo 1325481 25504247 := bstep (se 1 (by rfl) ⟨19128185, by rfl⟩ : syracuseStep 25504247 = 38256371) B38256371
theorem B4475627 : Blo 1325481 4475627 := bstep (se 1 (by rfl) ⟨3356720, by rfl⟩ : syracuseStep 4475627 = 6713441) B6713441
theorem B2239211 : Blo 1325481 2239211 := bstep (se 1 (by rfl) ⟨1679408, by rfl⟩ : syracuseStep 2239211 = 3358817) B3358817
theorem B2517799 : Blo 1325481 2517799 := bstep (se 1 (by rfl) ⟨1888349, by rfl⟩ : syracuseStep 2517799 = 3776699) B3776699
theorem B7555949 : Blo 1325481 7555949 := bstep (se 3 (by rfl) ⟨1416740, by rfl⟩ : syracuseStep 7555949 = 2833481) B2833481
theorem B2517959 : Blo 1325481 2517959 := bstep (se 1 (by rfl) ⟨1888469, by rfl⟩ : syracuseStep 2517959 = 3776939) B3776939
theorem B2984903 : Blo 1325481 2984903 := bstep (se 1 (by rfl) ⟨2238677, by rfl⟩ : syracuseStep 2984903 = 4477355) B4477355
theorem B2985263 : Blo 1325481 2985263 := bstep (se 1 (by rfl) ⟨2238947, by rfl⟩ : syracuseStep 2985263 = 4477895) B4477895
theorem B10071377 : Blo 1325481 10071377 := bstep (se 2 (by rfl) ⟨3776766, by rfl⟩ : syracuseStep 10071377 = 7553533) B7553533
theorem B5033441 : Blo 1325481 5033441 := bstep (se 2 (by rfl) ⟨1887540, by rfl⟩ : syracuseStep 5033441 = 3775081) B3775081
theorem B3780071 : Blo 1325481 3780071 := bstep (se 1 (by rfl) ⟨2835053, by rfl⟩ : syracuseStep 3780071 = 5670107) B5670107
theorem B2911721 : Blo 1325481 2911721 := bstep (se 2 (by rfl) ⟨1091895, by rfl⟩ : syracuseStep 2911721 = 2183791) B2183791
theorem B28700243 : Blo 1325481 28700243 := bstep (se 1 (by rfl) ⟨21525182, by rfl⟩ : syracuseStep 28700243 = 43050365) B43050365
theorem B4476545 : Blo 1325481 4476545 := bstep (se 2 (by rfl) ⟨1678704, by rfl⟩ : syracuseStep 4476545 = 3357409) B3357409
theorem B4476599 : Blo 1325481 4476599 := bstep (se 1 (by rfl) ⟨3357449, by rfl⟩ : syracuseStep 4476599 = 6714899) B6714899
theorem B6811361 : Blo 1325481 6811361 := bstep (se 2 (by rfl) ⟨2554260, by rfl⟩ : syracuseStep 6811361 = 5108521) B5108521
theorem B8073209 : Blo 1325481 8073209 := bstep (se 2 (by rfl) ⟨3027453, by rfl⟩ : syracuseStep 8073209 = 6054907) B6054907
theorem B4477031 : Blo 1325481 4477031 := bstep (se 1 (by rfl) ⟨3357773, by rfl⟩ : syracuseStep 4477031 = 6715547) B6715547
theorem B2986127 : Blo 1325481 2986127 := bstep (se 1 (by rfl) ⟨2239595, by rfl⟩ : syracuseStep 2986127 = 4479191) B4479191
theorem B16142489 : Blo 1325481 16142489 := bstep (se 2 (by rfl) ⟨6053433, by rfl⟩ : syracuseStep 16142489 = 12106867) B12106867
theorem B18149831 : Blo 1325481 18149831 := bstep (se 1 (by rfl) ⟨13612373, by rfl⟩ : syracuseStep 18149831 = 27224747) B27224747
theorem B2986487 : Blo 1325481 2986487 := bstep (se 1 (by rfl) ⟨2239865, by rfl⟩ : syracuseStep 2986487 = 4479731) B4479731
theorem B68932577 : Blo 1325481 68932577 := bstep (se 2 (by rfl) ⟨25849716, by rfl⟩ : syracuseStep 68932577 = 51699433) B51699433
theorem B4477949 : Blo 1325481 4477949 := bstep (se 3 (by rfl) ⟨839615, by rfl⟩ : syracuseStep 4477949 = 1679231) B1679231
theorem B3355951 : Blo 1325481 3355951 := bstep (se 1 (by rfl) ⟨2516963, by rfl⟩ : syracuseStep 3355951 = 5033927) B5033927
theorem B6370663 : Blo 1325481 6370663 := bstep (se 1 (by rfl) ⟨4777997, by rfl⟩ : syracuseStep 6370663 = 9555995) B9555995
theorem B27243965 : Blo 1325481 27243965 := bstep (se 3 (by rfl) ⟨5108243, by rfl⟩ : syracuseStep 27243965 = 10216487) B10216487
theorem B5248543 : Blo 1325481 5248543 := bstep (se 1 (by rfl) ⟨3936407, by rfl⟩ : syracuseStep 5248543 = 7872815) B7872815
theorem B4478543 : Blo 1325481 4478543 := bstep (se 1 (by rfl) ⟨3358907, by rfl⟩ : syracuseStep 4478543 = 6717815) B6717815
theorem B10065545 : Blo 1325481 10065545 := bstep (se 2 (by rfl) ⟨3774579, by rfl⟩ : syracuseStep 10065545 = 7549159) B7549159
theorem B17004167 : Blo 1325481 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B7551143 : Blo 1325481 7551143 := bstep (se 1 (by rfl) ⟨5663357, by rfl⟩ : syracuseStep 7551143 = 11326715) B11326715
theorem B5036327 : Blo 1325481 5036327 := bstep (se 1 (by rfl) ⟨3777245, by rfl⟩ : syracuseStep 5036327 = 7554491) B7554491
theorem B1989113 : Blo 1325481 1989113 := bstep (se 2 (by rfl) ⟨745917, by rfl⟩ : syracuseStep 1989113 = 1491835) B1491835
theorem B1677935 : Blo 1325481 1677935 := bstep (se 1 (by rfl) ⟨1258451, by rfl⟩ : syracuseStep 1677935 = 2516903) B2516903
theorem B1702651 : Blo 1325481 1702651 := bstep (se 1 (by rfl) ⟨1276988, by rfl⟩ : syracuseStep 1702651 = 2553977) B2553977
theorem B1325823 : Blo 1325481 1325823 := bstep (se 1 (by rfl) ⟨994367, by rfl⟩ : syracuseStep 1325823 = 1988735) B1988735
theorem B1325887 : Blo 1325481 1325887 := bstep (se 1 (by rfl) ⟨994415, by rfl⟩ : syracuseStep 1325887 = 1988831) B1988831
theorem B1325927 : Blo 1325481 1325927 := bstep (se 1 (by rfl) ⟨994445, by rfl⟩ : syracuseStep 1325927 = 1988891) B1988891
theorem B15104879 : Blo 1325481 15104879 := bstep (se 1 (by rfl) ⟨11328659, by rfl⟩ : syracuseStep 15104879 = 22657319) B22657319
theorem B5037011 : Blo 1325481 5037011 := bstep (se 1 (by rfl) ⟨3777758, by rfl⟩ : syracuseStep 5037011 = 7555517) B7555517
theorem B9329627 : Blo 1325481 9329627 := bstep (se 1 (by rfl) ⟨6997220, by rfl⟩ : syracuseStep 9329627 = 13994441) B13994441
theorem B4250657 : Blo 1325481 4250657 := bstep (se 2 (by rfl) ⟨1593996, by rfl⟩ : syracuseStep 4250657 = 3187993) B3187993
theorem B1326143 : Blo 1325481 1326143 := bstep (se 1 (by rfl) ⟨994607, by rfl⟩ : syracuseStep 1326143 = 1989215) B1989215
theorem B1989743 : Blo 1325481 1989743 := bstep (se 1 (by rfl) ⟨1492307, by rfl⟩ : syracuseStep 1989743 = 2984615) B2984615
theorem B1326207 : Blo 1325481 1326207 := bstep (se 1 (by rfl) ⟨994655, by rfl⟩ : syracuseStep 1326207 = 1989311) B1989311
theorem B1326235 : Blo 1325481 1326235 := bstep (se 1 (by rfl) ⟨994676, by rfl⟩ : syracuseStep 1326235 = 1989353) B1989353
theorem B1326319 : Blo 1325481 1326319 := bstep (se 1 (by rfl) ⟨994739, by rfl⟩ : syracuseStep 1326319 = 1989479) B1989479
theorem B1326363 : Blo 1325481 1326363 := bstep (se 1 (by rfl) ⟨994772, by rfl⟩ : syracuseStep 1326363 = 1989545) B1989545
theorem B8494445 : Blo 1325481 8494445 := bstep (se 3 (by rfl) ⟨1592708, by rfl⟩ : syracuseStep 8494445 = 3185417) B3185417
theorem B1326463 : Blo 1325481 1326463 := bstep (se 1 (by rfl) ⟨994847, by rfl⟩ : syracuseStep 1326463 = 1989695) B1989695
theorem B1326491 : Blo 1325481 1326491 := bstep (se 1 (by rfl) ⟨994868, by rfl⟩ : syracuseStep 1326491 = 1989737) B1989737
theorem B1326575 : Blo 1325481 1326575 := bstep (se 1 (by rfl) ⟨994931, by rfl⟩ : syracuseStep 1326575 = 1989863) B1989863
theorem B1990127 : Blo 1325481 1990127 := bstep (se 1 (by rfl) ⟨1492595, by rfl⟩ : syracuseStep 1990127 = 2985191) B2985191
theorem B7552601 : Blo 1325481 7552601 := bstep (se 2 (by rfl) ⟨2832225, by rfl⟩ : syracuseStep 7552601 = 5664451) B5664451
theorem B1326911 : Blo 1325481 1326911 := bstep (se 1 (by rfl) ⟨995183, by rfl⟩ : syracuseStep 1326911 = 1990367) B1990367
theorem B5668841 : Blo 1325481 5668841 := bstep (se 2 (by rfl) ⟨2125815, by rfl⟩ : syracuseStep 5668841 = 4251631) B4251631
theorem B1990751 : Blo 1325481 1990751 := bstep (se 1 (by rfl) ⟨1493063, by rfl⟩ : syracuseStep 1990751 = 2986127) B2986127
theorem B1327263 : Blo 1325481 1327263 := bstep (se 1 (by rfl) ⟨995447, by rfl⟩ : syracuseStep 1327263 = 1990895) B1990895
theorem B49725613 : Blo 1325481 49725613 := bstep (se 3 (by rfl) ⟨9323552, by rfl⟩ : syracuseStep 49725613 = 18647105) B18647105
theorem B1327387 : Blo 1325481 1327387 := bstep (se 1 (by rfl) ⟨995540, by rfl⟩ : syracuseStep 1327387 = 1991081) B1991081
theorem B12099887 : Blo 1325481 12099887 := bstep (se 1 (by rfl) ⟨9074915, by rfl⟩ : syracuseStep 12099887 = 18149831) B18149831
theorem B1990991 : Blo 1325481 1990991 := bstep (se 1 (by rfl) ⟨1493243, by rfl⟩ : syracuseStep 1990991 = 2986487) B2986487
theorem B3359191 : Blo 1325481 3359191 := bstep (se 1 (by rfl) ⟨2519393, by rfl⟩ : syracuseStep 3359191 = 5038787) B5038787
theorem B2982491 : Blo 1325481 2982491 := bstep (se 1 (by rfl) ⟨2236868, by rfl⟩ : syracuseStep 2982491 = 4473737) B4473737
theorem B6718139 : Blo 1325481 6718139 := bstep (se 1 (by rfl) ⟨5038604, by rfl⟩ : syracuseStep 6718139 = 10077209) B10077209
theorem B6046439 : Blo 1325481 6046439 := bstep (se 1 (by rfl) ⟨4534829, by rfl⟩ : syracuseStep 6046439 = 9069659) B9069659
theorem B18162643 : Blo 1325481 18162643 := bstep (se 1 (by rfl) ⟨13621982, by rfl⟩ : syracuseStep 18162643 = 27243965) B27243965
theorem B2270201 : Blo 1325481 2270201 := bstep (se 2 (by rfl) ⟨851325, by rfl⟩ : syracuseStep 2270201 = 1702651) B1702651
theorem B6710363 : Blo 1325481 6710363 := bstep (se 1 (by rfl) ⟨5032772, by rfl⟩ : syracuseStep 6710363 = 10065545) B10065545
theorem B12092591 : Blo 1325481 12092591 := bstep (se 1 (by rfl) ⟨9069443, by rfl⟩ : syracuseStep 12092591 = 18138887) B18138887
theorem B2983391 : Blo 1325481 2983391 := bstep (se 1 (by rfl) ⟨2237543, by rfl⟩ : syracuseStep 2983391 = 4475087) B4475087
theorem B4474493 : Blo 1325481 4474493 := bstep (se 3 (by rfl) ⟨838967, by rfl⟩ : syracuseStep 4474493 = 1677935) B1677935
theorem B4474601 : Blo 1325481 4474601 := bstep (se 2 (by rfl) ⟨1677975, by rfl⟩ : syracuseStep 4474601 = 3355951) B3355951
theorem B2983751 : Blo 1325481 2983751 := bstep (se 1 (by rfl) ⟨2237813, by rfl⟩ : syracuseStep 2983751 = 4475627) B4475627
theorem B1492807 : Blo 1325481 1492807 := bstep (se 1 (by rfl) ⟨1119605, by rfl⟩ : syracuseStep 1492807 = 2239211) B2239211
theorem B10069919 : Blo 1325481 10069919 := bstep (se 1 (by rfl) ⟨7552439, by rfl⟩ : syracuseStep 10069919 = 15104879) B15104879
theorem B6998057 : Blo 1325481 6998057 := bstep (se 2 (by rfl) ⟨2624271, by rfl⟩ : syracuseStep 6998057 = 5248543) B5248543
theorem B5662963 : Blo 1325481 5662963 := bstep (se 1 (by rfl) ⟨4247222, by rfl⟩ : syracuseStep 5662963 = 8494445) B8494445
theorem B2984363 : Blo 1325481 2984363 := bstep (se 1 (by rfl) ⟨2238272, by rfl⟩ : syracuseStep 2984363 = 4476545) B4476545
theorem B2984399 : Blo 1325481 2984399 := bstep (se 1 (by rfl) ⟨2238299, by rfl⟩ : syracuseStep 2984399 = 4476599) B4476599
theorem B4540907 : Blo 1325481 4540907 := bstep (se 1 (by rfl) ⟨3405680, by rfl⟩ : syracuseStep 4540907 = 6811361) B6811361
theorem B3779227 : Blo 1325481 3779227 := bstep (se 1 (by rfl) ⟨2834420, by rfl⟩ : syracuseStep 3779227 = 5668841) B5668841
theorem B2984687 : Blo 1325481 2984687 := bstep (se 1 (by rfl) ⟨2238515, by rfl⟩ : syracuseStep 2984687 = 4477031) B4477031
theorem B2985299 : Blo 1325481 2985299 := bstep (se 1 (by rfl) ⟨2238974, by rfl⟩ : syracuseStep 2985299 = 4477949) B4477949
theorem B40832693 : Blo 1325481 40832693 := bstep (se 5 (by rfl) ⟨1914032, by rfl⟩ : syracuseStep 40832693 = 3828065) B3828065
theorem B2985695 : Blo 1325481 2985695 := bstep (se 1 (by rfl) ⟨2239271, by rfl⟩ : syracuseStep 2985695 = 4478543) B4478543
theorem B6713117 : Blo 1325481 6713117 := bstep (se 3 (by rfl) ⟨1258709, by rfl⟩ : syracuseStep 6713117 = 2517419) B2517419
theorem B2125931 : Blo 1325481 2125931 := bstep (se 1 (by rfl) ⟨1594448, by rfl⟩ : syracuseStep 2125931 = 3188897) B3188897
theorem B5034095 : Blo 1325481 5034095 := bstep (se 1 (by rfl) ⟨3775571, by rfl⟩ : syracuseStep 5034095 = 7551143) B7551143
theorem B5382139 : Blo 1325481 5382139 := bstep (se 1 (by rfl) ⟨4036604, by rfl⟩ : syracuseStep 5382139 = 8073209) B8073209
theorem B17002831 : Blo 1325481 17002831 := bstep (se 1 (by rfl) ⟨12752123, by rfl⟩ : syracuseStep 17002831 = 25504247) B25504247
theorem B6714251 : Blo 1325481 6714251 := bstep (se 1 (by rfl) ⟨5035688, by rfl⟩ : syracuseStep 6714251 = 10071377) B10071377
theorem B3355627 : Blo 1325481 3355627 := bstep (se 1 (by rfl) ⟨2516720, by rfl⟩ : syracuseStep 3355627 = 5033441) B5033441
theorem B2520047 : Blo 1325481 2520047 := bstep (se 1 (by rfl) ⟨1890035, by rfl⟩ : syracuseStep 2520047 = 3780071) B3780071
theorem B19133495 : Blo 1325481 19133495 := bstep (se 1 (by rfl) ⟨14350121, by rfl⟩ : syracuseStep 19133495 = 28700243) B28700243
theorem B5035067 : Blo 1325481 5035067 := bstep (se 1 (by rfl) ⟨3776300, by rfl⟩ : syracuseStep 5035067 = 7552601) B7552601
theorem B3355769 : Blo 1325481 3355769 := bstep (se 2 (by rfl) ⟨1258413, by rfl⟩ : syracuseStep 3355769 = 2516827) B2516827
theorem B11335085 : Blo 1325481 11335085 := bstep (se 3 (by rfl) ⟨2125328, by rfl⟩ : syracuseStep 11335085 = 4250657) B4250657
theorem B10761659 : Blo 1325481 10761659 := bstep (se 1 (by rfl) ⟨8071244, by rfl⟩ : syracuseStep 10761659 = 16142489) B16142489
theorem B6371297 : Blo 1325481 6371297 := bstep (se 2 (by rfl) ⟨2389236, by rfl⟩ : syracuseStep 6371297 = 4778473) B4778473
theorem B21502219 : Blo 1325481 21502219 := bstep (se 1 (by rfl) ⟨16126664, by rfl⟩ : syracuseStep 21502219 = 32253329) B32253329
theorem B3357065 : Blo 1325481 3357065 := bstep (se 2 (by rfl) ⟨1258899, by rfl⟩ : syracuseStep 3357065 = 2517799) B2517799
theorem B11336111 : Blo 1325481 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B3185207 : Blo 1325481 3185207 := bstep (se 1 (by rfl) ⟨2388905, by rfl⟩ : syracuseStep 3185207 = 4777811) B4777811
theorem B7764589 : Blo 1325481 7764589 := bstep (se 3 (by rfl) ⟨1455860, by rfl⟩ : syracuseStep 7764589 = 2911721) B2911721
theorem B1989275 : Blo 1325481 1989275 := bstep (se 1 (by rfl) ⟨1491956, by rfl⟩ : syracuseStep 1989275 = 2983913) B2983913
theorem B1677991 : Blo 1325481 1677991 := bstep (se 1 (by rfl) ⟨1258493, by rfl⟩ : syracuseStep 1677991 = 2516987) B2516987
theorem B22666067 : Blo 1325481 22666067 := bstep (se 1 (by rfl) ⟨16999550, by rfl⟩ : syracuseStep 22666067 = 33999101) B33999101
theorem B3357551 : Blo 1325481 3357551 := bstep (se 1 (by rfl) ⟨2518163, by rfl⟩ : syracuseStep 3357551 = 5036327) B5036327
theorem B7166843 : Blo 1325481 7166843 := bstep (se 1 (by rfl) ⟨5375132, by rfl⟩ : syracuseStep 7166843 = 10750265) B10750265
theorem B1326075 : Blo 1325481 1326075 := bstep (se 1 (by rfl) ⟨994556, by rfl⟩ : syracuseStep 1326075 = 1989113) B1989113
theorem B8494217 : Blo 1325481 8494217 := bstep (se 2 (by rfl) ⟨3185331, by rfl⟩ : syracuseStep 8494217 = 6370663) B6370663
theorem B5037299 : Blo 1325481 5037299 := bstep (se 1 (by rfl) ⟨3777974, by rfl⟩ : syracuseStep 5037299 = 7555949) B7555949
theorem B1678639 : Blo 1325481 1678639 := bstep (se 1 (by rfl) ⟨1258979, by rfl⟩ : syracuseStep 1678639 = 2517959) B2517959
theorem B1989935 : Blo 1325481 1989935 := bstep (se 1 (by rfl) ⟨1492451, by rfl⟩ : syracuseStep 1989935 = 2984903) B2984903
theorem B3358007 : Blo 1325481 3358007 := bstep (se 1 (by rfl) ⟨2518505, by rfl⟩ : syracuseStep 3358007 = 5037011) B5037011
theorem B1326495 : Blo 1325481 1326495 := bstep (se 1 (by rfl) ⟨994871, by rfl⟩ : syracuseStep 1326495 = 1989743) B1989743
theorem B1990175 : Blo 1325481 1990175 := bstep (se 1 (by rfl) ⟨1492631, by rfl⟩ : syracuseStep 1990175 = 2985263) B2985263
theorem B1326751 : Blo 1325481 1326751 := bstep (se 1 (by rfl) ⟨995063, by rfl⟩ : syracuseStep 1326751 = 1990127) B1990127
theorem B24879005 : Blo 1325481 24879005 := bstep (se 3 (by rfl) ⟨4664813, by rfl⟩ : syracuseStep 24879005 = 9329627) B9329627
theorem B183820205 : Blo 1325481 183820205 := bstep (se 3 (by rfl) ⟨34466288, by rfl⟩ : syracuseStep 183820205 = 68932577) B68932577
theorem B1327167 : Blo 1325481 1327167 := bstep (se 1 (by rfl) ⟨995375, by rfl⟩ : syracuseStep 1327167 = 1990751) B1990751
theorem B1327327 : Blo 1325481 1327327 := bstep (se 1 (by rfl) ⟨995495, by rfl⟩ : syracuseStep 1327327 = 1990991) B1990991
theorem B5669149 : Blo 1325481 5669149 := bstep (se 3 (by rfl) ⟨1062965, by rfl⟩ : syracuseStep 5669149 = 2125931) B2125931
theorem B1680031 : Blo 1325481 1680031 := bstep (se 1 (by rfl) ⟨1260023, by rfl⟩ : syracuseStep 1680031 = 2520047) B2520047
theorem B12755663 : Blo 1325481 12755663 := bstep (se 1 (by rfl) ⟨9566747, by rfl⟩ : syracuseStep 12755663 = 19133495) B19133495
theorem B4473575 : Blo 1325481 4473575 := bstep (se 1 (by rfl) ⟨3355181, by rfl⟩ : syracuseStep 4473575 = 6710363) B6710363
theorem B2237179 : Blo 1325481 2237179 := bstep (se 1 (by rfl) ⟨1677884, by rfl⟩ : syracuseStep 2237179 = 3355769) B3355769
theorem B8061727 : Blo 1325481 8061727 := bstep (se 1 (by rfl) ⟨6046295, by rfl⟩ : syracuseStep 8061727 = 12092591) B12092591
theorem B5038969 : Blo 1325481 5038969 := bstep (se 2 (by rfl) ⟨1889613, by rfl⟩ : syracuseStep 5038969 = 3779227) B3779227
theorem B2237321 : Blo 1325481 2237321 := bstep (se 2 (by rfl) ⟨838995, by rfl⟩ : syracuseStep 2237321 = 1677991) B1677991
theorem B2982995 : Blo 1325481 2982995 := bstep (se 1 (by rfl) ⟨2237246, by rfl⟩ : syracuseStep 2982995 = 4474493) B4474493
theorem B2983067 : Blo 1325481 2983067 := bstep (se 1 (by rfl) ⟨2237300, by rfl⟩ : syracuseStep 2983067 = 4474601) B4474601
theorem B24216857 : Blo 1325481 24216857 := bstep (se 2 (by rfl) ⟨9081321, by rfl⟩ : syracuseStep 24216857 = 18162643) B18162643
theorem B12109085 : Blo 1325481 12109085 := bstep (se 3 (by rfl) ⟨2270453, by rfl⟩ : syracuseStep 12109085 = 4540907) B4540907
theorem B4474169 : Blo 1325481 4474169 := bstep (se 2 (by rfl) ⟨1677813, by rfl⟩ : syracuseStep 4474169 = 3355627) B3355627
theorem B2238043 : Blo 1325481 2238043 := bstep (se 1 (by rfl) ⟨1678532, by rfl⟩ : syracuseStep 2238043 = 3357065) B3357065
theorem B2123471 : Blo 1325481 2123471 := bstep (se 1 (by rfl) ⟨1592603, by rfl⟩ : syracuseStep 2123471 = 3185207) B3185207
theorem B2238185 : Blo 1325481 2238185 := bstep (se 2 (by rfl) ⟨839319, by rfl⟩ : syracuseStep 2238185 = 1678639) B1678639
theorem B2238367 : Blo 1325481 2238367 := bstep (se 1 (by rfl) ⟨1678775, by rfl⟩ : syracuseStep 2238367 = 3357551) B3357551
theorem B4777895 : Blo 1325481 4777895 := bstep (se 1 (by rfl) ⟨3583421, by rfl⟩ : syracuseStep 4777895 = 7166843) B7166843
theorem B5662811 : Blo 1325481 5662811 := bstep (se 1 (by rfl) ⟨4247108, by rfl⟩ : syracuseStep 5662811 = 8494217) B8494217
theorem B2238671 : Blo 1325481 2238671 := bstep (se 1 (by rfl) ⟨1679003, by rfl⟩ : syracuseStep 2238671 = 3358007) B3358007
theorem B4475411 : Blo 1325481 4475411 := bstep (se 1 (by rfl) ⟨3356558, by rfl⟩ : syracuseStep 4475411 = 6713117) B6713117
theorem B122546803 : Blo 1325481 122546803 := bstep (se 1 (by rfl) ⟨91910102, by rfl⟩ : syracuseStep 122546803 = 183820205) B183820205
theorem B66300817 : Blo 1325481 66300817 := bstep (se 2 (by rfl) ⟨24862806, by rfl⟩ : syracuseStep 66300817 = 49725613) B49725613
theorem B7176185 : Blo 1325481 7176185 := bstep (se 2 (by rfl) ⟨2691069, by rfl⟩ : syracuseStep 7176185 = 5382139) B5382139
theorem B22670441 : Blo 1325481 22670441 := bstep (se 2 (by rfl) ⟨8501415, by rfl⟩ : syracuseStep 22670441 = 17002831) B17002831
theorem B4476167 : Blo 1325481 4476167 := bstep (se 1 (by rfl) ⟨3357125, by rfl⟩ : syracuseStep 4476167 = 6714251) B6714251
theorem B7556723 : Blo 1325481 7556723 := bstep (se 1 (by rfl) ⟨5667542, by rfl⟩ : syracuseStep 7556723 = 11335085) B11335085
theorem B6713279 : Blo 1325481 6713279 := bstep (se 1 (by rfl) ⟨5034959, by rfl⟩ : syracuseStep 6713279 = 10069919) B10069919
theorem B4247531 : Blo 1325481 4247531 := bstep (se 1 (by rfl) ⟨3185648, by rfl⟩ : syracuseStep 4247531 = 6371297) B6371297
theorem B4665371 : Blo 1325481 4665371 := bstep (se 1 (by rfl) ⟨3499028, by rfl⟩ : syracuseStep 4665371 = 6998057) B6998057
theorem B7557407 : Blo 1325481 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B15110711 : Blo 1325481 15110711 := bstep (se 1 (by rfl) ⟨11333033, by rfl⟩ : syracuseStep 15110711 = 22666067) B22666067
theorem B16586003 : Blo 1325481 16586003 := bstep (se 1 (by rfl) ⟨12439502, by rfl⟩ : syracuseStep 16586003 = 24879005) B24879005
theorem B3356063 : Blo 1325481 3356063 := bstep (se 1 (by rfl) ⟨2517047, by rfl⟩ : syracuseStep 3356063 = 5034095) B5034095
theorem B8066591 : Blo 1325481 8066591 := bstep (se 1 (by rfl) ⟨6049943, by rfl⟩ : syracuseStep 8066591 = 12099887) B12099887
theorem B7550617 : Blo 1325481 7550617 := bstep (se 2 (by rfl) ⟨2831481, by rfl⟩ : syracuseStep 7550617 = 5662963) B5662963
theorem B28669625 : Blo 1325481 28669625 := bstep (se 2 (by rfl) ⟨10751109, by rfl⟩ : syracuseStep 28669625 = 21502219) B21502219
theorem B1988327 : Blo 1325481 1988327 := bstep (se 1 (by rfl) ⟨1491245, by rfl⟩ : syracuseStep 1988327 = 2982491) B2982491
theorem B4478759 : Blo 1325481 4478759 := bstep (se 1 (by rfl) ⟨3359069, by rfl⟩ : syracuseStep 4478759 = 6718139) B6718139
theorem B4478921 : Blo 1325481 4478921 := bstep (se 2 (by rfl) ⟨1679595, by rfl⟩ : syracuseStep 4478921 = 3359191) B3359191
theorem B3356711 : Blo 1325481 3356711 := bstep (se 1 (by rfl) ⟨2517533, by rfl⟩ : syracuseStep 3356711 = 5035067) B5035067
theorem B10352785 : Blo 1325481 10352785 := bstep (se 2 (by rfl) ⟨3882294, by rfl⟩ : syracuseStep 10352785 = 7764589) B7764589
theorem B7174439 : Blo 1325481 7174439 := bstep (se 1 (by rfl) ⟨5380829, by rfl⟩ : syracuseStep 7174439 = 10761659) B10761659
theorem B1988927 : Blo 1325481 1988927 := bstep (se 1 (by rfl) ⟨1491695, by rfl⟩ : syracuseStep 1988927 = 2983391) B2983391
theorem B1989167 : Blo 1325481 1989167 := bstep (se 1 (by rfl) ⟨1491875, by rfl⟩ : syracuseStep 1989167 = 2983751) B2983751
theorem B1989575 : Blo 1325481 1989575 := bstep (se 1 (by rfl) ⟨1492181, by rfl⟩ : syracuseStep 1989575 = 2984363) B2984363
theorem B1989599 : Blo 1325481 1989599 := bstep (se 1 (by rfl) ⟨1492199, by rfl⟩ : syracuseStep 1989599 = 2984399) B2984399
theorem B1326183 : Blo 1325481 1326183 := bstep (se 1 (by rfl) ⟨994637, by rfl⟩ : syracuseStep 1326183 = 1989275) B1989275
theorem B1989791 : Blo 1325481 1989791 := bstep (se 1 (by rfl) ⟨1492343, by rfl⟩ : syracuseStep 1989791 = 2984687) B2984687
theorem B3358199 : Blo 1325481 3358199 := bstep (se 1 (by rfl) ⟨2518649, by rfl⟩ : syracuseStep 3358199 = 5037299) B5037299
theorem B1326623 : Blo 1325481 1326623 := bstep (se 1 (by rfl) ⟨994967, by rfl⟩ : syracuseStep 1326623 = 1989935) B1989935
theorem B1990199 : Blo 1325481 1990199 := bstep (se 1 (by rfl) ⟨1492649, by rfl⟩ : syracuseStep 1990199 = 2985299) B2985299
theorem B1326783 : Blo 1325481 1326783 := bstep (se 1 (by rfl) ⟨995087, by rfl⟩ : syracuseStep 1326783 = 1990175) B1990175
theorem B64495349 : Blo 1325481 64495349 := bstep (se 5 (by rfl) ⟨3023219, by rfl⟩ : syracuseStep 64495349 = 6046439) B6046439
theorem B1990409 : Blo 1325481 1990409 := bstep (se 2 (by rfl) ⟨746403, by rfl⟩ : syracuseStep 1990409 = 1492807) B1492807
theorem B27221795 : Blo 1325481 27221795 := bstep (se 1 (by rfl) ⟨20416346, by rfl⟩ : syracuseStep 27221795 = 40832693) B40832693
theorem B1990463 : Blo 1325481 1990463 := bstep (se 1 (by rfl) ⟨1492847, by rfl⟩ : syracuseStep 1990463 = 2985695) B2985695
theorem B6053869 : Blo 1325481 6053869 := bstep (se 3 (by rfl) ⟨1135100, by rfl⟩ : syracuseStep 6053869 = 2270201) B2270201
theorem B5038271 : Blo 1325481 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B13803713 : Blo 1325481 13803713 := bstep (se 2 (by rfl) ⟨5176392, by rfl⟩ : syracuseStep 13803713 = 10352785) B10352785
theorem B8503775 : Blo 1325481 8503775 := bstep (se 1 (by rfl) ⟨6377831, by rfl⟩ : syracuseStep 8503775 = 12755663) B12755663
theorem B2982383 : Blo 1325481 2982383 := bstep (se 1 (by rfl) ⟨2236787, by rfl⟩ : syracuseStep 2982383 = 4473575) B4473575
theorem B1491547 : Blo 1325481 1491547 := bstep (se 1 (by rfl) ⟨1118660, by rfl⟩ : syracuseStep 1491547 = 2237321) B2237321
theorem B44229341 : Blo 1325481 44229341 := bstep (se 3 (by rfl) ⟨8293001, by rfl⟩ : syracuseStep 44229341 = 16586003) B16586003
theorem B2982779 : Blo 1325481 2982779 := bstep (se 1 (by rfl) ⟨2237084, by rfl⟩ : syracuseStep 2982779 = 4474169) B4474169
theorem B2237375 : Blo 1325481 2237375 := bstep (se 1 (by rfl) ⟨1678031, by rfl⟩ : syracuseStep 2237375 = 3356063) B3356063
theorem B2982905 : Blo 1325481 2982905 := bstep (se 2 (by rfl) ⟨1118589, by rfl⟩ : syracuseStep 2982905 = 2237179) B2237179
theorem B10748969 : Blo 1325481 10748969 := bstep (se 2 (by rfl) ⟨4030863, by rfl⟩ : syracuseStep 10748969 = 8061727) B8061727
theorem B19113083 : Blo 1325481 19113083 := bstep (se 1 (by rfl) ⟨14334812, by rfl⟩ : syracuseStep 19113083 = 28669625) B28669625
theorem B1492123 : Blo 1325481 1492123 := bstep (se 1 (by rfl) ⟨1119092, by rfl⟩ : syracuseStep 1492123 = 2238185) B2238185
theorem B6718625 : Blo 1325481 6718625 := bstep (se 2 (by rfl) ⟨2519484, by rfl⟩ : syracuseStep 6718625 = 5038969) B5038969
theorem B88401089 : Blo 1325481 88401089 := bstep (se 2 (by rfl) ⟨33150408, by rfl⟩ : syracuseStep 88401089 = 66300817) B66300817
theorem B2237807 : Blo 1325481 2237807 := bstep (se 1 (by rfl) ⟨1678355, by rfl⟩ : syracuseStep 2237807 = 3356711) B3356711
theorem B1492447 : Blo 1325481 1492447 := bstep (se 1 (by rfl) ⟨1119335, by rfl⟩ : syracuseStep 1492447 = 2238671) B2238671
theorem B2983607 : Blo 1325481 2983607 := bstep (se 1 (by rfl) ⟨2237705, by rfl⟩ : syracuseStep 2983607 = 4475411) B4475411
theorem B4784123 : Blo 1325481 4784123 := bstep (se 1 (by rfl) ⟨3588092, by rfl⟩ : syracuseStep 4784123 = 7176185) B7176185
theorem B2984057 : Blo 1325481 2984057 := bstep (se 2 (by rfl) ⟨1119021, by rfl⟩ : syracuseStep 2984057 = 2238043) B2238043
theorem B2984111 : Blo 1325481 2984111 := bstep (se 1 (by rfl) ⟨2238083, by rfl⟩ : syracuseStep 2984111 = 4476167) B4476167
theorem B2238799 : Blo 1325481 2238799 := bstep (se 1 (by rfl) ⟨1679099, by rfl⟩ : syracuseStep 2238799 = 3358199) B3358199
theorem B18147863 : Blo 1325481 18147863 := bstep (se 1 (by rfl) ⟨13610897, by rfl⟩ : syracuseStep 18147863 = 27221795) B27221795
theorem B2984489 : Blo 1325481 2984489 := bstep (se 2 (by rfl) ⟨1119183, by rfl⟩ : syracuseStep 2984489 = 2238367) B2238367
theorem B4475519 : Blo 1325481 4475519 := bstep (se 1 (by rfl) ⟨3356639, by rfl⟩ : syracuseStep 4475519 = 6713279) B6713279
theorem B8071825 : Blo 1325481 8071825 := bstep (se 2 (by rfl) ⟨3026934, by rfl⟩ : syracuseStep 8071825 = 6053869) B6053869
theorem B8072723 : Blo 1325481 8072723 := bstep (se 1 (by rfl) ⟨6054542, by rfl⟩ : syracuseStep 8072723 = 12109085) B12109085
theorem B2240041 : Blo 1325481 2240041 := bstep (se 2 (by rfl) ⟨840015, by rfl⟩ : syracuseStep 2240041 = 1680031) B1680031
theorem B5377727 : Blo 1325481 5377727 := bstep (se 1 (by rfl) ⟨4033295, by rfl⟩ : syracuseStep 5377727 = 8066591) B8066591
theorem B2985839 : Blo 1325481 2985839 := bstep (se 1 (by rfl) ⟨2239379, by rfl⟩ : syracuseStep 2985839 = 4478759) B4478759
theorem B2985947 : Blo 1325481 2985947 := bstep (se 1 (by rfl) ⟨2239460, by rfl⟩ : syracuseStep 2985947 = 4478921) B4478921
theorem B42996899 : Blo 1325481 42996899 := bstep (se 1 (by rfl) ⟨32247674, by rfl⟩ : syracuseStep 42996899 = 64495349) B64495349
theorem B2831687 : Blo 1325481 2831687 := bstep (se 1 (by rfl) ⟨2123765, by rfl⟩ : syracuseStep 2831687 = 4247531) B4247531
theorem B12440989 : Blo 1325481 12440989 := bstep (se 3 (by rfl) ⟨2332685, by rfl⟩ : syracuseStep 12440989 = 4665371) B4665371
theorem B10073807 : Blo 1325481 10073807 := bstep (se 1 (by rfl) ⟨7555355, by rfl⟩ : syracuseStep 10073807 = 15110711) B15110711
theorem B7558865 : Blo 1325481 7558865 := bstep (se 2 (by rfl) ⟨2834574, by rfl⟩ : syracuseStep 7558865 = 5669149) B5669149
theorem B1988663 : Blo 1325481 1988663 := bstep (se 1 (by rfl) ⟨1491497, by rfl⟩ : syracuseStep 1988663 = 2982995) B2982995
theorem B1988711 : Blo 1325481 1988711 := bstep (se 1 (by rfl) ⟨1491533, by rfl⟩ : syracuseStep 1988711 = 2983067) B2983067
theorem B163395737 : Blo 1325481 163395737 := bstep (se 2 (by rfl) ⟨61273401, by rfl⟩ : syracuseStep 163395737 = 122546803) B122546803
theorem B16144571 : Blo 1325481 16144571 := bstep (se 1 (by rfl) ⟨12108428, by rfl⟩ : syracuseStep 16144571 = 24216857) B24216857
theorem B1415647 : Blo 1325481 1415647 := bstep (se 1 (by rfl) ⟨1061735, by rfl⟩ : syracuseStep 1415647 = 2123471) B2123471
theorem B1325551 : Blo 1325481 1325551 := bstep (se 1 (by rfl) ⟨994163, by rfl⟩ : syracuseStep 1325551 = 1988327) B1988327
theorem B3185263 : Blo 1325481 3185263 := bstep (se 1 (by rfl) ⟨2388947, by rfl⟩ : syracuseStep 3185263 = 4777895) B4777895
theorem B3775207 : Blo 1325481 3775207 := bstep (se 1 (by rfl) ⟨2831405, by rfl⟩ : syracuseStep 3775207 = 5662811) B5662811
theorem B4782959 : Blo 1325481 4782959 := bstep (se 1 (by rfl) ⟨3587219, by rfl⟩ : syracuseStep 4782959 = 7174439) B7174439
theorem B1325951 : Blo 1325481 1325951 := bstep (se 1 (by rfl) ⟨994463, by rfl⟩ : syracuseStep 1325951 = 1988927) B1988927
theorem B1326111 : Blo 1325481 1326111 := bstep (se 1 (by rfl) ⟨994583, by rfl⟩ : syracuseStep 1326111 = 1989167) B1989167
theorem B1326383 : Blo 1325481 1326383 := bstep (se 1 (by rfl) ⟨994787, by rfl⟩ : syracuseStep 1326383 = 1989575) B1989575
theorem B1326399 : Blo 1325481 1326399 := bstep (se 1 (by rfl) ⟨994799, by rfl⟩ : syracuseStep 1326399 = 1989599) B1989599
theorem B15113627 : Blo 1325481 15113627 := bstep (se 1 (by rfl) ⟨11335220, by rfl⟩ : syracuseStep 15113627 = 22670441) B22670441
theorem B1326527 : Blo 1325481 1326527 := bstep (se 1 (by rfl) ⟨994895, by rfl⟩ : syracuseStep 1326527 = 1989791) B1989791
theorem B10067489 : Blo 1325481 10067489 := bstep (se 2 (by rfl) ⟨3775308, by rfl⟩ : syracuseStep 10067489 = 7550617) B7550617
theorem B1326799 : Blo 1325481 1326799 := bstep (se 1 (by rfl) ⟨995099, by rfl⟩ : syracuseStep 1326799 = 1990199) B1990199
theorem B5037815 : Blo 1325481 5037815 := bstep (se 1 (by rfl) ⟨3778361, by rfl⟩ : syracuseStep 5037815 = 7556723) B7556723
theorem B1326939 : Blo 1325481 1326939 := bstep (se 1 (by rfl) ⟨995204, by rfl⟩ : syracuseStep 1326939 = 1990409) B1990409
theorem B1326975 : Blo 1325481 1326975 := bstep (se 1 (by rfl) ⟨995231, by rfl⟩ : syracuseStep 1326975 = 1990463) B1990463
theorem B3358847 : Blo 1325481 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B5669183 : Blo 1325481 5669183 := bstep (se 1 (by rfl) ⟨4251887, by rfl⟩ : syracuseStep 5669183 = 8503775) B8503775
theorem B1491583 : Blo 1325481 1491583 := bstep (se 1 (by rfl) ⟨1118687, by rfl⟩ : syracuseStep 1491583 = 2237375) B2237375
theorem B28664599 : Blo 1325481 28664599 := bstep (se 1 (by rfl) ⟨21498449, by rfl⟩ : syracuseStep 28664599 = 42996899) B42996899
theorem B1491871 : Blo 1325481 1491871 := bstep (se 1 (by rfl) ⟨1118903, by rfl⟩ : syracuseStep 1491871 = 2237807) B2237807
theorem B5039243 : Blo 1325481 5039243 := bstep (se 1 (by rfl) ⟨3779432, by rfl⟩ : syracuseStep 5039243 = 7558865) B7558865
theorem B108930491 : Blo 1325481 108930491 := bstep (se 1 (by rfl) ⟨81697868, by rfl⟩ : syracuseStep 108930491 = 163395737) B163395737
theorem B2983679 : Blo 1325481 2983679 := bstep (se 1 (by rfl) ⟨2237759, by rfl⟩ : syracuseStep 2983679 = 4475519) B4475519
theorem B3188639 : Blo 1325481 3188639 := bstep (se 1 (by rfl) ⟨2391479, by rfl⟩ : syracuseStep 3188639 = 4782959) B4782959
theorem B6711659 : Blo 1325481 6711659 := bstep (se 1 (by rfl) ⟨5033744, by rfl⟩ : syracuseStep 6711659 = 10067489) B10067489
theorem B12757661 : Blo 1325481 12757661 := bstep (se 3 (by rfl) ⟨2392061, by rfl⟩ : syracuseStep 12757661 = 4784123) B4784123
theorem B9202475 : Blo 1325481 9202475 := bstep (se 1 (by rfl) ⟨6901856, by rfl⟩ : syracuseStep 9202475 = 13803713) B13803713
theorem B2985065 : Blo 1325481 2985065 := bstep (se 2 (by rfl) ⟨1119399, by rfl⟩ : syracuseStep 2985065 = 2238799) B2238799
theorem B29486227 : Blo 1325481 29486227 := bstep (se 1 (by rfl) ⟨22114670, by rfl⟩ : syracuseStep 29486227 = 44229341) B44229341
theorem B235736237 : Blo 1325481 235736237 := bstep (se 3 (by rfl) ⟨44200544, by rfl⟩ : syracuseStep 235736237 = 88401089) B88401089
theorem B12742055 : Blo 1325481 12742055 := bstep (se 1 (by rfl) ⟨9556541, by rfl⟩ : syracuseStep 12742055 = 19113083) B19113083
theorem B1887791 : Blo 1325481 1887791 := bstep (se 1 (by rfl) ⟨1415843, by rfl⟩ : syracuseStep 1887791 = 2831687) B2831687
theorem B5033609 : Blo 1325481 5033609 := bstep (se 2 (by rfl) ⟨1887603, by rfl⟩ : syracuseStep 5033609 = 3775207) B3775207
theorem B2986721 : Blo 1325481 2986721 := bstep (se 2 (by rfl) ⟨1120020, by rfl⟩ : syracuseStep 2986721 = 2240041) B2240041
theorem B3585151 : Blo 1325481 3585151 := bstep (se 1 (by rfl) ⟨2688863, by rfl⟩ : syracuseStep 3585151 = 5377727) B5377727
theorem B7550117 : Blo 1325481 7550117 := bstep (se 4 (by rfl) ⟨707823, by rfl⟩ : syracuseStep 7550117 = 1415647) B1415647
theorem B1988255 : Blo 1325481 1988255 := bstep (se 1 (by rfl) ⟨1491191, by rfl⟩ : syracuseStep 1988255 = 2982383) B2982383
theorem B16988069 : Blo 1325481 16988069 := bstep (se 4 (by rfl) ⟨1592631, by rfl⟩ : syracuseStep 16988069 = 3185263) B3185263
theorem B1988519 : Blo 1325481 1988519 := bstep (se 1 (by rfl) ⟨1491389, by rfl⟩ : syracuseStep 1988519 = 2982779) B2982779
theorem B1988603 : Blo 1325481 1988603 := bstep (se 1 (by rfl) ⟨1491452, by rfl⟩ : syracuseStep 1988603 = 2982905) B2982905
theorem B7165979 : Blo 1325481 7165979 := bstep (se 1 (by rfl) ⟨5374484, by rfl⟩ : syracuseStep 7165979 = 10748969) B10748969
theorem B4479083 : Blo 1325481 4479083 := bstep (se 1 (by rfl) ⟨3359312, by rfl⟩ : syracuseStep 4479083 = 6718625) B6718625
theorem B1988729 : Blo 1325481 1988729 := bstep (se 2 (by rfl) ⟨745773, by rfl⟩ : syracuseStep 1988729 = 1491547) B1491547
theorem B10762433 : Blo 1325481 10762433 := bstep (se 2 (by rfl) ⟨4035912, by rfl⟩ : syracuseStep 10762433 = 8071825) B8071825
theorem B1989071 : Blo 1325481 1989071 := bstep (se 1 (by rfl) ⟨1491803, by rfl⟩ : syracuseStep 1989071 = 2983607) B2983607
theorem B6715871 : Blo 1325481 6715871 := bstep (se 1 (by rfl) ⟨5036903, by rfl⟩ : syracuseStep 6715871 = 10073807) B10073807
theorem B1325775 : Blo 1325481 1325775 := bstep (se 1 (by rfl) ⟨994331, by rfl⟩ : syracuseStep 1325775 = 1988663) B1988663
theorem B1325807 : Blo 1325481 1325807 := bstep (se 1 (by rfl) ⟨994355, by rfl⟩ : syracuseStep 1325807 = 1988711) B1988711
theorem B1989371 : Blo 1325481 1989371 := bstep (se 1 (by rfl) ⟨1492028, by rfl⟩ : syracuseStep 1989371 = 2984057) B2984057
theorem B1989407 : Blo 1325481 1989407 := bstep (se 1 (by rfl) ⟨1492055, by rfl⟩ : syracuseStep 1989407 = 2984111) B2984111
theorem B10763047 : Blo 1325481 10763047 := bstep (se 1 (by rfl) ⟨8072285, by rfl⟩ : syracuseStep 10763047 = 16144571) B16144571
theorem B1989497 : Blo 1325481 1989497 := bstep (se 2 (by rfl) ⟨746061, by rfl⟩ : syracuseStep 1989497 = 1492123) B1492123
theorem B12098575 : Blo 1325481 12098575 := bstep (se 1 (by rfl) ⟨9073931, by rfl⟩ : syracuseStep 12098575 = 18147863) B18147863
theorem B1989659 : Blo 1325481 1989659 := bstep (se 1 (by rfl) ⟨1492244, by rfl⟩ : syracuseStep 1989659 = 2984489) B2984489
theorem B16587985 : Blo 1325481 16587985 := bstep (se 2 (by rfl) ⟨6220494, by rfl⟩ : syracuseStep 16587985 = 12440989) B12440989
theorem B1989929 : Blo 1325481 1989929 := bstep (se 2 (by rfl) ⟨746223, by rfl⟩ : syracuseStep 1989929 = 1492447) B1492447
theorem B10075751 : Blo 1325481 10075751 := bstep (se 1 (by rfl) ⟨7556813, by rfl⟩ : syracuseStep 10075751 = 15113627) B15113627
theorem B5381815 : Blo 1325481 5381815 := bstep (se 1 (by rfl) ⟨4036361, by rfl⟩ : syracuseStep 5381815 = 8072723) B8072723
theorem B3358543 : Blo 1325481 3358543 := bstep (se 1 (by rfl) ⟨2518907, by rfl⟩ : syracuseStep 3358543 = 5037815) B5037815
theorem B1990559 : Blo 1325481 1990559 := bstep (se 1 (by rfl) ⟨1492919, by rfl⟩ : syracuseStep 1990559 = 2985839) B2985839
theorem B1990631 : Blo 1325481 1990631 := bstep (se 1 (by rfl) ⟨1492973, by rfl⟩ : syracuseStep 1990631 = 2985947) B2985947
theorem B1991147 : Blo 1325481 1991147 := bstep (se 1 (by rfl) ⟨1493360, by rfl⟩ : syracuseStep 1991147 = 2986721) B2986721
theorem B19120805 : Blo 1325481 19120805 := bstep (se 4 (by rfl) ⟨1792575, by rfl⟩ : syracuseStep 19120805 = 3585151) B3585151
theorem B3359495 : Blo 1325481 3359495 := bstep (se 1 (by rfl) ⟨2519621, by rfl⟩ : syracuseStep 3359495 = 5039243) B5039243
theorem B4777319 : Blo 1325481 4777319 := bstep (se 1 (by rfl) ⟨3582989, by rfl⟩ : syracuseStep 4777319 = 7165979) B7165979
theorem B16131433 : Blo 1325481 16131433 := bstep (se 2 (by rfl) ⟨6049287, by rfl⟩ : syracuseStep 16131433 = 12098575) B12098575
theorem B39314969 : Blo 1325481 39314969 := bstep (se 2 (by rfl) ⟨14743113, by rfl⟩ : syracuseStep 39314969 = 29486227) B29486227
theorem B4474439 : Blo 1325481 4474439 := bstep (se 1 (by rfl) ⟨3355829, by rfl⟩ : syracuseStep 4474439 = 6711659) B6711659
theorem B8505107 : Blo 1325481 8505107 := bstep (se 1 (by rfl) ⟨6378830, by rfl⟩ : syracuseStep 8505107 = 12757661) B12757661
theorem B157157491 : Blo 1325481 157157491 := bstep (se 1 (by rfl) ⟨117868118, by rfl⟩ : syracuseStep 157157491 = 235736237) B235736237
theorem B2239231 : Blo 1325481 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B3779455 : Blo 1325481 3779455 := bstep (se 1 (by rfl) ⟨2834591, by rfl⟩ : syracuseStep 3779455 = 5669183) B5669183
theorem B5033411 : Blo 1325481 5033411 := bstep (se 1 (by rfl) ⟨3775058, by rfl⟩ : syracuseStep 5033411 = 7550117) B7550117
theorem B38219465 : Blo 1325481 38219465 := bstep (se 2 (by rfl) ⟨14332299, by rfl⟩ : syracuseStep 38219465 = 28664599) B28664599
theorem B2125759 : Blo 1325481 2125759 := bstep (se 1 (by rfl) ⟨1594319, by rfl⟩ : syracuseStep 2125759 = 3188639) B3188639
theorem B11325379 : Blo 1325481 11325379 := bstep (se 1 (by rfl) ⟨8494034, by rfl⟩ : syracuseStep 11325379 = 16988069) B16988069
theorem B2986055 : Blo 1325481 2986055 := bstep (se 1 (by rfl) ⟨2239541, by rfl⟩ : syracuseStep 2986055 = 4479083) B4479083
theorem B5034109 : Blo 1325481 5034109 := bstep (se 3 (by rfl) ⟨943895, by rfl⟩ : syracuseStep 5034109 = 1887791) B1887791
theorem B4477247 : Blo 1325481 4477247 := bstep (se 1 (by rfl) ⟨3357935, by rfl⟩ : syracuseStep 4477247 = 6715871) B6715871
theorem B3355739 : Blo 1325481 3355739 := bstep (se 1 (by rfl) ⟨2516804, by rfl⟩ : syracuseStep 3355739 = 5033609) B5033609
theorem B4478057 : Blo 1325481 4478057 := bstep (se 2 (by rfl) ⟨1679271, by rfl⟩ : syracuseStep 4478057 = 3358543) B3358543
theorem B1988777 : Blo 1325481 1988777 := bstep (se 2 (by rfl) ⟨745791, by rfl⟩ : syracuseStep 1988777 = 1491583) B1491583
theorem B72620327 : Blo 1325481 72620327 := bstep (se 1 (by rfl) ⟨54465245, by rfl⟩ : syracuseStep 72620327 = 108930491) B108930491
theorem B14350729 : Blo 1325481 14350729 := bstep (se 2 (by rfl) ⟨5381523, by rfl⟩ : syracuseStep 14350729 = 10763047) B10763047
theorem B1325503 : Blo 1325481 1325503 := bstep (se 1 (by rfl) ⟨994127, by rfl⟩ : syracuseStep 1325503 = 1988255) B1988255
theorem B1989119 : Blo 1325481 1989119 := bstep (se 1 (by rfl) ⟨1491839, by rfl⟩ : syracuseStep 1989119 = 2983679) B2983679
theorem B1989161 : Blo 1325481 1989161 := bstep (se 2 (by rfl) ⟨745935, by rfl⟩ : syracuseStep 1989161 = 1491871) B1491871
theorem B1325679 : Blo 1325481 1325679 := bstep (se 1 (by rfl) ⟨994259, by rfl⟩ : syracuseStep 1325679 = 1988519) B1988519
theorem B1325735 : Blo 1325481 1325735 := bstep (se 1 (by rfl) ⟨994301, by rfl⟩ : syracuseStep 1325735 = 1988603) B1988603
theorem B1325819 : Blo 1325481 1325819 := bstep (se 1 (by rfl) ⟨994364, by rfl⟩ : syracuseStep 1325819 = 1988729) B1988729
theorem B7174955 : Blo 1325481 7174955 := bstep (se 1 (by rfl) ⟨5381216, by rfl⟩ : syracuseStep 7174955 = 10762433) B10762433
theorem B22117313 : Blo 1325481 22117313 := bstep (se 2 (by rfl) ⟨8293992, by rfl⟩ : syracuseStep 22117313 = 16587985) B16587985
theorem B1326047 : Blo 1325481 1326047 := bstep (se 1 (by rfl) ⟨994535, by rfl⟩ : syracuseStep 1326047 = 1989071) B1989071
theorem B1326247 : Blo 1325481 1326247 := bstep (se 1 (by rfl) ⟨994685, by rfl⟩ : syracuseStep 1326247 = 1989371) B1989371
theorem B1326271 : Blo 1325481 1326271 := bstep (se 1 (by rfl) ⟨994703, by rfl⟩ : syracuseStep 1326271 = 1989407) B1989407
theorem B6134983 : Blo 1325481 6134983 := bstep (se 1 (by rfl) ⟨4601237, by rfl⟩ : syracuseStep 6134983 = 9202475) B9202475
theorem B1326331 : Blo 1325481 1326331 := bstep (se 1 (by rfl) ⟨994748, by rfl⟩ : syracuseStep 1326331 = 1989497) B1989497
theorem B1326439 : Blo 1325481 1326439 := bstep (se 1 (by rfl) ⟨994829, by rfl⟩ : syracuseStep 1326439 = 1989659) B1989659
theorem B1990043 : Blo 1325481 1990043 := bstep (se 1 (by rfl) ⟨1492532, by rfl⟩ : syracuseStep 1990043 = 2985065) B2985065
theorem B1326619 : Blo 1325481 1326619 := bstep (se 1 (by rfl) ⟨994964, by rfl⟩ : syracuseStep 1326619 = 1989929) B1989929
theorem B7175753 : Blo 1325481 7175753 := bstep (se 2 (by rfl) ⟨2690907, by rfl⟩ : syracuseStep 7175753 = 5381815) B5381815
theorem B8494703 : Blo 1325481 8494703 := bstep (se 1 (by rfl) ⟨6371027, by rfl⟩ : syracuseStep 8494703 = 12742055) B12742055
theorem B6717167 : Blo 1325481 6717167 := bstep (se 1 (by rfl) ⟨5037875, by rfl⟩ : syracuseStep 6717167 = 10075751) B10075751
theorem B1327039 : Blo 1325481 1327039 := bstep (se 1 (by rfl) ⟨995279, by rfl⟩ : syracuseStep 1327039 = 1990559) B1990559
theorem B1327087 : Blo 1325481 1327087 := bstep (se 1 (by rfl) ⟨995315, by rfl⟩ : syracuseStep 1327087 = 1990631) B1990631
theorem B1990703 : Blo 1325481 1990703 := bstep (se 1 (by rfl) ⟨1493027, by rfl⟩ : syracuseStep 1990703 = 2986055) B2986055
theorem B209543321 : Blo 1325481 209543321 := bstep (se 2 (by rfl) ⟨78578745, by rfl⟩ : syracuseStep 209543321 = 157157491) B157157491
theorem B1327431 : Blo 1325481 1327431 := bstep (se 1 (by rfl) ⟨995573, by rfl⟩ : syracuseStep 1327431 = 1991147) B1991147
theorem B12747203 : Blo 1325481 12747203 := bstep (se 1 (by rfl) ⟨9560402, by rfl⟩ : syracuseStep 12747203 = 19120805) B19120805
theorem B2237159 : Blo 1325481 2237159 := bstep (se 1 (by rfl) ⟨1677869, by rfl⟩ : syracuseStep 2237159 = 3355739) B3355739
theorem B12739517 : Blo 1325481 12739517 := bstep (se 3 (by rfl) ⟨2388659, by rfl⟩ : syracuseStep 12739517 = 4777319) B4777319
theorem B32719909 : Blo 1325481 32719909 := bstep (se 4 (by rfl) ⟨3067491, by rfl⟩ : syracuseStep 32719909 = 6134983) B6134983
theorem B2982959 : Blo 1325481 2982959 := bstep (se 1 (by rfl) ⟨2237219, by rfl⟩ : syracuseStep 2982959 = 4474439) B4474439
theorem B5039273 : Blo 1325481 5039273 := bstep (se 2 (by rfl) ⟨1889727, by rfl⟩ : syracuseStep 5039273 = 3779455) B3779455
theorem B5670071 : Blo 1325481 5670071 := bstep (se 1 (by rfl) ⟨4252553, by rfl⟩ : syracuseStep 5670071 = 8505107) B8505107
theorem B5663135 : Blo 1325481 5663135 := bstep (se 1 (by rfl) ⟨4247351, by rfl⟩ : syracuseStep 5663135 = 8494703) B8494703
theorem B25479643 : Blo 1325481 25479643 := bstep (se 1 (by rfl) ⟨19109732, by rfl⟩ : syracuseStep 25479643 = 38219465) B38219465
theorem B15100505 : Blo 1325481 15100505 := bstep (se 2 (by rfl) ⟨5662689, by rfl⟩ : syracuseStep 15100505 = 11325379) B11325379
theorem B6712145 : Blo 1325481 6712145 := bstep (se 2 (by rfl) ⟨2517054, by rfl⟩ : syracuseStep 6712145 = 5034109) B5034109
theorem B2984831 : Blo 1325481 2984831 := bstep (se 1 (by rfl) ⟨2238623, by rfl⟩ : syracuseStep 2984831 = 4477247) B4477247
theorem B2239663 : Blo 1325481 2239663 := bstep (se 1 (by rfl) ⟨1679747, by rfl⟩ : syracuseStep 2239663 = 3359495) B3359495
theorem B2985371 : Blo 1325481 2985371 := bstep (se 1 (by rfl) ⟨2239028, by rfl⟩ : syracuseStep 2985371 = 4478057) B4478057
theorem B2985641 : Blo 1325481 2985641 := bstep (se 2 (by rfl) ⟨1119615, by rfl⟩ : syracuseStep 2985641 = 2239231) B2239231
theorem B26209979 : Blo 1325481 26209979 := bstep (se 1 (by rfl) ⟨19657484, by rfl⟩ : syracuseStep 26209979 = 39314969) B39314969
theorem B21508577 : Blo 1325481 21508577 := bstep (se 2 (by rfl) ⟨8065716, by rfl⟩ : syracuseStep 21508577 = 16131433) B16131433
theorem B3355607 : Blo 1325481 3355607 := bstep (se 1 (by rfl) ⟨2516705, by rfl⟩ : syracuseStep 3355607 = 5033411) B5033411
theorem B4478111 : Blo 1325481 4478111 := bstep (se 1 (by rfl) ⟨3358583, by rfl⟩ : syracuseStep 4478111 = 6717167) B6717167
theorem B19134305 : Blo 1325481 19134305 := bstep (se 2 (by rfl) ⟨7175364, by rfl⟩ : syracuseStep 19134305 = 14350729) B14350729
theorem B1325851 : Blo 1325481 1325851 := bstep (se 1 (by rfl) ⟨994388, by rfl⟩ : syracuseStep 1325851 = 1988777) B1988777
theorem B48413551 : Blo 1325481 48413551 := bstep (se 1 (by rfl) ⟨36310163, by rfl⟩ : syracuseStep 48413551 = 72620327) B72620327
theorem B1326079 : Blo 1325481 1326079 := bstep (se 1 (by rfl) ⟨994559, by rfl⟩ : syracuseStep 1326079 = 1989119) B1989119
theorem B1326107 : Blo 1325481 1326107 := bstep (se 1 (by rfl) ⟨994580, by rfl⟩ : syracuseStep 1326107 = 1989161) B1989161
theorem B4783303 : Blo 1325481 4783303 := bstep (se 1 (by rfl) ⟨3587477, by rfl⟩ : syracuseStep 4783303 = 7174955) B7174955
theorem B14744875 : Blo 1325481 14744875 := bstep (se 1 (by rfl) ⟨11058656, by rfl⟩ : syracuseStep 14744875 = 22117313) B22117313
theorem B1326695 : Blo 1325481 1326695 := bstep (se 1 (by rfl) ⟨995021, by rfl⟩ : syracuseStep 1326695 = 1990043) B1990043
theorem B4783835 : Blo 1325481 4783835 := bstep (se 1 (by rfl) ⟨3587876, by rfl⟩ : syracuseStep 4783835 = 7175753) B7175753
theorem B2834345 : Blo 1325481 2834345 := bstep (se 2 (by rfl) ⟨1062879, by rfl⟩ : syracuseStep 2834345 = 2125759) B2125759
theorem B1327135 : Blo 1325481 1327135 := bstep (se 1 (by rfl) ⟨995351, by rfl⟩ : syracuseStep 1327135 = 1990703) B1990703
theorem B1491439 : Blo 1325481 1491439 := bstep (se 1 (by rfl) ⟨1118579, by rfl⟩ : syracuseStep 1491439 = 2237159) B2237159
theorem B33972857 : Blo 1325481 33972857 := bstep (se 2 (by rfl) ⟨12739821, by rfl⟩ : syracuseStep 33972857 = 25479643) B25479643
theorem B2237071 : Blo 1325481 2237071 := bstep (se 1 (by rfl) ⟨1677803, by rfl⟩ : syracuseStep 2237071 = 3355607) B3355607
theorem B3359515 : Blo 1325481 3359515 := bstep (se 1 (by rfl) ⟨2519636, by rfl⟩ : syracuseStep 3359515 = 5039273) B5039273
theorem B12756203 : Blo 1325481 12756203 := bstep (se 1 (by rfl) ⟨9567152, by rfl⟩ : syracuseStep 12756203 = 19134305) B19134305
theorem B4474763 : Blo 1325481 4474763 := bstep (se 1 (by rfl) ⟨3356072, by rfl⟩ : syracuseStep 4474763 = 6712145) B6712145
theorem B3189223 : Blo 1325481 3189223 := bstep (se 1 (by rfl) ⟨2391917, by rfl⟩ : syracuseStep 3189223 = 4783835) B4783835
theorem B8498135 : Blo 1325481 8498135 := bstep (se 1 (by rfl) ⟨6373601, by rfl⟩ : syracuseStep 8498135 = 12747203) B12747203
theorem B14339051 : Blo 1325481 14339051 := bstep (se 1 (by rfl) ⟨10754288, by rfl⟩ : syracuseStep 14339051 = 21508577) B21508577
theorem B2985407 : Blo 1325481 2985407 := bstep (se 1 (by rfl) ⟨2239055, by rfl⟩ : syracuseStep 2985407 = 4478111) B4478111
theorem B3780047 : Blo 1325481 3780047 := bstep (se 1 (by rfl) ⟨2835035, by rfl⟩ : syracuseStep 3780047 = 5670071) B5670071
theorem B43626545 : Blo 1325481 43626545 := bstep (se 2 (by rfl) ⟨16359954, by rfl⟩ : syracuseStep 43626545 = 32719909) B32719909
theorem B2986217 : Blo 1325481 2986217 := bstep (se 2 (by rfl) ⟨1119831, by rfl⟩ : syracuseStep 2986217 = 2239663) B2239663
theorem B6377737 : Blo 1325481 6377737 := bstep (se 2 (by rfl) ⟨2391651, by rfl⟩ : syracuseStep 6377737 = 4783303) B4783303
theorem B1889563 : Blo 1325481 1889563 := bstep (se 1 (by rfl) ⟨1417172, by rfl⟩ : syracuseStep 1889563 = 2834345) B2834345
theorem B139695547 : Blo 1325481 139695547 := bstep (se 1 (by rfl) ⟨104771660, by rfl⟩ : syracuseStep 139695547 = 209543321) B209543321
theorem B8493011 : Blo 1325481 8493011 := bstep (se 1 (by rfl) ⟨6369758, by rfl⟩ : syracuseStep 8493011 = 12739517) B12739517
theorem B1988639 : Blo 1325481 1988639 := bstep (se 1 (by rfl) ⟨1491479, by rfl⟩ : syracuseStep 1988639 = 2982959) B2982959
theorem B64551401 : Blo 1325481 64551401 := bstep (se 2 (by rfl) ⟨24206775, by rfl⟩ : syracuseStep 64551401 = 48413551) B48413551
theorem B3775423 : Blo 1325481 3775423 := bstep (se 1 (by rfl) ⟨2831567, by rfl⟩ : syracuseStep 3775423 = 5663135) B5663135
theorem B19659833 : Blo 1325481 19659833 := bstep (se 2 (by rfl) ⟨7372437, by rfl⟩ : syracuseStep 19659833 = 14744875) B14744875
theorem B10067003 : Blo 1325481 10067003 := bstep (se 1 (by rfl) ⟨7550252, by rfl⟩ : syracuseStep 10067003 = 15100505) B15100505
theorem B1989887 : Blo 1325481 1989887 := bstep (se 1 (by rfl) ⟨1492415, by rfl⟩ : syracuseStep 1989887 = 2984831) B2984831
theorem B1990247 : Blo 1325481 1990247 := bstep (se 1 (by rfl) ⟨1492685, by rfl⟩ : syracuseStep 1990247 = 2985371) B2985371
theorem B1990427 : Blo 1325481 1990427 := bstep (se 1 (by rfl) ⟨1492820, by rfl⟩ : syracuseStep 1990427 = 2985641) B2985641
theorem B17473319 : Blo 1325481 17473319 := bstep (se 1 (by rfl) ⟨13104989, by rfl⟩ : syracuseStep 17473319 = 26209979) B26209979
theorem B1990811 : Blo 1325481 1990811 := bstep (se 1 (by rfl) ⟨1493108, by rfl⟩ : syracuseStep 1990811 = 2986217) B2986217
theorem B8503649 : Blo 1325481 8503649 := bstep (se 2 (by rfl) ⟨3188868, by rfl⟩ : syracuseStep 8503649 = 6377737) B6377737
theorem B8504135 : Blo 1325481 8504135 := bstep (se 1 (by rfl) ⟨6378101, by rfl⟩ : syracuseStep 8504135 = 12756203) B12756203
theorem B2982761 : Blo 1325481 2982761 := bstep (se 2 (by rfl) ⟨1118535, by rfl⟩ : syracuseStep 2982761 = 2237071) B2237071
theorem B2983175 : Blo 1325481 2983175 := bstep (se 1 (by rfl) ⟨2237381, by rfl⟩ : syracuseStep 2983175 = 4474763) B4474763
theorem B5662007 : Blo 1325481 5662007 := bstep (se 1 (by rfl) ⟨4246505, by rfl⟩ : syracuseStep 5662007 = 8493011) B8493011
theorem B43034267 : Blo 1325481 43034267 := bstep (se 1 (by rfl) ⟨32275700, by rfl⟩ : syracuseStep 43034267 = 64551401) B64551401
theorem B6711335 : Blo 1325481 6711335 := bstep (se 1 (by rfl) ⟨5033501, by rfl⟩ : syracuseStep 6711335 = 10067003) B10067003
theorem B17009189 : Blo 1325481 17009189 := bstep (se 4 (by rfl) ⟨1594611, by rfl⟩ : syracuseStep 17009189 = 3189223) B3189223
theorem B22661693 : Blo 1325481 22661693 := bstep (se 3 (by rfl) ⟨4249067, by rfl⟩ : syracuseStep 22661693 = 8498135) B8498135
theorem B29084363 : Blo 1325481 29084363 := bstep (se 1 (by rfl) ⟨21813272, by rfl⟩ : syracuseStep 29084363 = 43626545) B43626545
theorem B10080125 : Blo 1325481 10080125 := bstep (se 3 (by rfl) ⟨1890023, by rfl⟩ : syracuseStep 10080125 = 3780047) B3780047
theorem B5033897 : Blo 1325481 5033897 := bstep (se 2 (by rfl) ⟨1887711, by rfl⟩ : syracuseStep 5033897 = 3775423) B3775423
theorem B2519417 : Blo 1325481 2519417 := bstep (se 2 (by rfl) ⟨944781, by rfl⟩ : syracuseStep 2519417 = 1889563) B1889563
theorem B22648571 : Blo 1325481 22648571 := bstep (se 1 (by rfl) ⟨16986428, by rfl⟩ : syracuseStep 22648571 = 33972857) B33972857
theorem B1988585 : Blo 1325481 1988585 := bstep (se 2 (by rfl) ⟨745719, by rfl⟩ : syracuseStep 1988585 = 1491439) B1491439
theorem B4479353 : Blo 1325481 4479353 := bstep (se 2 (by rfl) ⟨1679757, by rfl⟩ : syracuseStep 4479353 = 3359515) B3359515
theorem B1325759 : Blo 1325481 1325759 := bstep (se 1 (by rfl) ⟨994319, by rfl⟩ : syracuseStep 1325759 = 1988639) B1988639
theorem B186260729 : Blo 1325481 186260729 := bstep (se 2 (by rfl) ⟨69847773, by rfl⟩ : syracuseStep 186260729 = 139695547) B139695547
theorem B9559367 : Blo 1325481 9559367 := bstep (se 1 (by rfl) ⟨7169525, by rfl⟩ : syracuseStep 9559367 = 14339051) B14339051
theorem B13106555 : Blo 1325481 13106555 := bstep (se 1 (by rfl) ⟨9829916, by rfl⟩ : syracuseStep 13106555 = 19659833) B19659833
theorem B1326591 : Blo 1325481 1326591 := bstep (se 1 (by rfl) ⟨994943, by rfl⟩ : syracuseStep 1326591 = 1989887) B1989887
theorem B1990271 : Blo 1325481 1990271 := bstep (se 1 (by rfl) ⟨1492703, by rfl⟩ : syracuseStep 1990271 = 2985407) B2985407
theorem B1326831 : Blo 1325481 1326831 := bstep (se 1 (by rfl) ⟨995123, by rfl⟩ : syracuseStep 1326831 = 1990247) B1990247
theorem B1326951 : Blo 1325481 1326951 := bstep (se 1 (by rfl) ⟨995213, by rfl⟩ : syracuseStep 1326951 = 1990427) B1990427
theorem B11648879 : Blo 1325481 11648879 := bstep (se 1 (by rfl) ⟨8736659, by rfl⟩ : syracuseStep 11648879 = 17473319) B17473319
theorem B1327207 : Blo 1325481 1327207 := bstep (se 1 (by rfl) ⟨995405, by rfl⟩ : syracuseStep 1327207 = 1990811) B1990811
theorem B5669099 : Blo 1325481 5669099 := bstep (se 1 (by rfl) ⟨4251824, by rfl⟩ : syracuseStep 5669099 = 8503649) B8503649
theorem B1679611 : Blo 1325481 1679611 := bstep (se 1 (by rfl) ⟨1259708, by rfl⟩ : syracuseStep 1679611 = 2519417) B2519417
theorem B5669423 : Blo 1325481 5669423 := bstep (se 1 (by rfl) ⟨4252067, by rfl⟩ : syracuseStep 5669423 = 8504135) B8504135
theorem B28689511 : Blo 1325481 28689511 := bstep (se 1 (by rfl) ⟨21517133, by rfl⟩ : syracuseStep 28689511 = 43034267) B43034267
theorem B15099047 : Blo 1325481 15099047 := bstep (se 1 (by rfl) ⟨11324285, by rfl⟩ : syracuseStep 15099047 = 22648571) B22648571
theorem B4474223 : Blo 1325481 4474223 := bstep (se 1 (by rfl) ⟨3355667, by rfl⟩ : syracuseStep 4474223 = 6711335) B6711335
theorem B11339459 : Blo 1325481 11339459 := bstep (se 1 (by rfl) ⟨8504594, by rfl⟩ : syracuseStep 11339459 = 17009189) B17009189
theorem B15107795 : Blo 1325481 15107795 := bstep (se 1 (by rfl) ⟨11330846, by rfl⟩ : syracuseStep 15107795 = 22661693) B22661693
theorem B6720083 : Blo 1325481 6720083 := bstep (se 1 (by rfl) ⟨5040062, by rfl⟩ : syracuseStep 6720083 = 10080125) B10080125
theorem B2986235 : Blo 1325481 2986235 := bstep (se 1 (by rfl) ⟨2239676, by rfl⟩ : syracuseStep 2986235 = 4479353) B4479353
theorem B8737703 : Blo 1325481 8737703 := bstep (se 1 (by rfl) ⟨6553277, by rfl⟩ : syracuseStep 8737703 = 13106555) B13106555
theorem B3355931 : Blo 1325481 3355931 := bstep (se 1 (by rfl) ⟨2516948, by rfl⟩ : syracuseStep 3355931 = 5033897) B5033897
theorem B1988507 : Blo 1325481 1988507 := bstep (se 1 (by rfl) ⟨1491380, by rfl⟩ : syracuseStep 1988507 = 2982761) B2982761
theorem B496695277 : Blo 1325481 496695277 := bstep (se 3 (by rfl) ⟨93130364, by rfl⟩ : syracuseStep 496695277 = 186260729) B186260729
theorem B1988783 : Blo 1325481 1988783 := bstep (se 1 (by rfl) ⟨1491587, by rfl⟩ : syracuseStep 1988783 = 2983175) B2983175
theorem B3774671 : Blo 1325481 3774671 := bstep (se 1 (by rfl) ⟨2831003, by rfl⟩ : syracuseStep 3774671 = 5662007) B5662007
theorem B1325723 : Blo 1325481 1325723 := bstep (se 1 (by rfl) ⟨994292, by rfl⟩ : syracuseStep 1325723 = 1988585) B1988585
theorem B19389575 : Blo 1325481 19389575 := bstep (se 1 (by rfl) ⟨14542181, by rfl⟩ : syracuseStep 19389575 = 29084363) B29084363
theorem B6372911 : Blo 1325481 6372911 := bstep (se 1 (by rfl) ⟨4779683, by rfl⟩ : syracuseStep 6372911 = 9559367) B9559367
theorem B1326847 : Blo 1325481 1326847 := bstep (se 1 (by rfl) ⟨995135, by rfl⟩ : syracuseStep 1326847 = 1990271) B1990271
theorem B7765919 : Blo 1325481 7765919 := bstep (se 1 (by rfl) ⟨5824439, by rfl⟩ : syracuseStep 7765919 = 11648879) B11648879
theorem B1990823 : Blo 1325481 1990823 := bstep (se 1 (by rfl) ⟨1493117, by rfl⟩ : syracuseStep 1990823 = 2986235) B2986235
theorem B5825135 : Blo 1325481 5825135 := bstep (se 1 (by rfl) ⟨4368851, by rfl⟩ : syracuseStep 5825135 = 8737703) B8737703
theorem B2237287 : Blo 1325481 2237287 := bstep (se 1 (by rfl) ⟨1677965, by rfl⟩ : syracuseStep 2237287 = 3355931) B3355931
theorem B2982815 : Blo 1325481 2982815 := bstep (se 1 (by rfl) ⟨2237111, by rfl⟩ : syracuseStep 2982815 = 4474223) B4474223
theorem B2516447 : Blo 1325481 2516447 := bstep (se 1 (by rfl) ⟨1887335, by rfl⟩ : syracuseStep 2516447 = 3774671) B3774671
theorem B662260369 : Blo 1325481 662260369 := bstep (se 2 (by rfl) ⟨248347638, by rfl⟩ : syracuseStep 662260369 = 496695277) B496695277
theorem B3779399 : Blo 1325481 3779399 := bstep (se 1 (by rfl) ⟨2834549, by rfl⟩ : syracuseStep 3779399 = 5669099) B5669099
theorem B2239481 : Blo 1325481 2239481 := bstep (se 2 (by rfl) ⟨839805, by rfl⟩ : syracuseStep 2239481 = 1679611) B1679611
theorem B3779615 : Blo 1325481 3779615 := bstep (se 1 (by rfl) ⟨2834711, by rfl⟩ : syracuseStep 3779615 = 5669423) B5669423
theorem B10071863 : Blo 1325481 10071863 := bstep (se 1 (by rfl) ⟨7553897, by rfl⟩ : syracuseStep 10071863 = 15107795) B15107795
theorem B38252681 : Blo 1325481 38252681 := bstep (se 2 (by rfl) ⟨14344755, by rfl⟩ : syracuseStep 38252681 = 28689511) B28689511
theorem B4248607 : Blo 1325481 4248607 := bstep (se 1 (by rfl) ⟨3186455, by rfl⟩ : syracuseStep 4248607 = 6372911) B6372911
theorem B51705533 : Blo 1325481 51705533 := bstep (se 3 (by rfl) ⟨9694787, by rfl⟩ : syracuseStep 51705533 = 19389575) B19389575
theorem B10066031 : Blo 1325481 10066031 := bstep (se 1 (by rfl) ⟨7549523, by rfl⟩ : syracuseStep 10066031 = 15099047) B15099047
theorem B7559639 : Blo 1325481 7559639 := bstep (se 1 (by rfl) ⟨5669729, by rfl⟩ : syracuseStep 7559639 = 11339459) B11339459
theorem B1325671 : Blo 1325481 1325671 := bstep (se 1 (by rfl) ⟨994253, by rfl⟩ : syracuseStep 1325671 = 1988507) B1988507
theorem B1325855 : Blo 1325481 1325855 := bstep (se 1 (by rfl) ⟨994391, by rfl⟩ : syracuseStep 1325855 = 1988783) B1988783
theorem B4480055 : Blo 1325481 4480055 := bstep (se 1 (by rfl) ⟨3360041, by rfl⟩ : syracuseStep 4480055 = 6720083) B6720083
theorem B5177279 : Blo 1325481 5177279 := bstep (se 1 (by rfl) ⟨3882959, by rfl⟩ : syracuseStep 5177279 = 7765919) B7765919
theorem B25501787 : Blo 1325481 25501787 := bstep (se 1 (by rfl) ⟨19126340, by rfl⟩ : syracuseStep 25501787 = 38252681) B38252681
theorem B1327215 : Blo 1325481 1327215 := bstep (se 1 (by rfl) ⟨995411, by rfl⟩ : syracuseStep 1327215 = 1990823) B1990823
theorem B2983049 : Blo 1325481 2983049 := bstep (se 2 (by rfl) ⟨1118643, by rfl⟩ : syracuseStep 2983049 = 2237287) B2237287
theorem B6710525 : Blo 1325481 6710525 := bstep (se 3 (by rfl) ⟨1258223, by rfl⟩ : syracuseStep 6710525 = 2516447) B2516447
theorem B6710687 : Blo 1325481 6710687 := bstep (se 1 (by rfl) ⟨5033015, by rfl⟩ : syracuseStep 6710687 = 10066031) B10066031
theorem B15533693 : Blo 1325481 15533693 := bstep (se 3 (by rfl) ⟨2912567, by rfl⟩ : syracuseStep 15533693 = 5825135) B5825135
theorem B5039759 : Blo 1325481 5039759 := bstep (se 1 (by rfl) ⟨3779819, by rfl⟩ : syracuseStep 5039759 = 7559639) B7559639
theorem B1492987 : Blo 1325481 1492987 := bstep (se 1 (by rfl) ⟨1119740, by rfl⟩ : syracuseStep 1492987 = 2239481) B2239481
theorem B13806077 : Blo 1325481 13806077 := bstep (se 3 (by rfl) ⟨2588639, by rfl⟩ : syracuseStep 13806077 = 5177279) B5177279
theorem B5664809 : Blo 1325481 5664809 := bstep (se 2 (by rfl) ⟨2124303, by rfl⟩ : syracuseStep 5664809 = 4248607) B4248607
theorem B2519599 : Blo 1325481 2519599 := bstep (se 1 (by rfl) ⟨1889699, by rfl⟩ : syracuseStep 2519599 = 3779399) B3779399
theorem B2519743 : Blo 1325481 2519743 := bstep (se 1 (by rfl) ⟨1889807, by rfl⟩ : syracuseStep 2519743 = 3779615) B3779615
theorem B2986703 : Blo 1325481 2986703 := bstep (se 1 (by rfl) ⟨2240027, by rfl⟩ : syracuseStep 2986703 = 4480055) B4480055
theorem B6714575 : Blo 1325481 6714575 := bstep (se 1 (by rfl) ⟨5035931, by rfl⟩ : syracuseStep 6714575 = 10071863) B10071863
theorem B1988543 : Blo 1325481 1988543 := bstep (se 1 (by rfl) ⟨1491407, by rfl⟩ : syracuseStep 1988543 = 2982815) B2982815
theorem B883013825 : Blo 1325481 883013825 := bstep (se 2 (by rfl) ⟨331130184, by rfl⟩ : syracuseStep 883013825 = 662260369) B662260369
theorem B34470355 : Blo 1325481 34470355 := bstep (se 1 (by rfl) ⟨25852766, by rfl⟩ : syracuseStep 34470355 = 51705533) B51705533
theorem B3776539 : Blo 1325481 3776539 := bstep (se 1 (by rfl) ⟨2832404, by rfl⟩ : syracuseStep 3776539 = 5664809) B5664809
theorem B1991135 : Blo 1325481 1991135 := bstep (se 1 (by rfl) ⟨1493351, by rfl⟩ : syracuseStep 1991135 = 2986703) B2986703
theorem B3359465 : Blo 1325481 3359465 := bstep (se 2 (by rfl) ⟨1259799, by rfl⟩ : syracuseStep 3359465 = 2519599) B2519599
theorem B4473683 : Blo 1325481 4473683 := bstep (se 1 (by rfl) ⟨3355262, by rfl⟩ : syracuseStep 4473683 = 6710525) B6710525
theorem B3359657 : Blo 1325481 3359657 := bstep (se 2 (by rfl) ⟨1259871, by rfl⟩ : syracuseStep 3359657 = 2519743) B2519743
theorem B4473791 : Blo 1325481 4473791 := bstep (se 1 (by rfl) ⟨3355343, by rfl⟩ : syracuseStep 4473791 = 6710687) B6710687
theorem B10355795 : Blo 1325481 10355795 := bstep (se 1 (by rfl) ⟨7766846, by rfl⟩ : syracuseStep 10355795 = 15533693) B15533693
theorem B3359839 : Blo 1325481 3359839 := bstep (se 1 (by rfl) ⟨2519879, by rfl⟩ : syracuseStep 3359839 = 5039759) B5039759
theorem B36816205 : Blo 1325481 36816205 := bstep (se 3 (by rfl) ⟨6903038, by rfl⟩ : syracuseStep 36816205 = 13806077) B13806077
theorem B17001191 : Blo 1325481 17001191 := bstep (se 1 (by rfl) ⟨12750893, by rfl⟩ : syracuseStep 17001191 = 25501787) B25501787
theorem B45960473 : Blo 1325481 45960473 := bstep (se 2 (by rfl) ⟨17235177, by rfl⟩ : syracuseStep 45960473 = 34470355) B34470355
theorem B4476383 : Blo 1325481 4476383 := bstep (se 1 (by rfl) ⟨3357287, by rfl⟩ : syracuseStep 4476383 = 6714575) B6714575
theorem B1988699 : Blo 1325481 1988699 := bstep (se 1 (by rfl) ⟨1491524, by rfl⟩ : syracuseStep 1988699 = 2983049) B2983049
theorem B1325695 : Blo 1325481 1325695 := bstep (se 1 (by rfl) ⟨994271, by rfl⟩ : syracuseStep 1325695 = 1988543) B1988543
theorem B588675883 : Blo 1325481 588675883 := bstep (se 1 (by rfl) ⟨441506912, by rfl⟩ : syracuseStep 588675883 = 883013825) B883013825
theorem B1990649 : Blo 1325481 1990649 := bstep (se 2 (by rfl) ⟨746493, by rfl⟩ : syracuseStep 1990649 = 1492987) B1492987
theorem B1327423 : Blo 1325481 1327423 := bstep (se 1 (by rfl) ⟨995567, by rfl⟩ : syracuseStep 1327423 = 1991135) B1991135
theorem B2982455 : Blo 1325481 2982455 := bstep (se 1 (by rfl) ⟨2236841, by rfl⟩ : syracuseStep 2982455 = 4473683) B4473683
theorem B2982527 : Blo 1325481 2982527 := bstep (se 1 (by rfl) ⟨2236895, by rfl⟩ : syracuseStep 2982527 = 4473791) B4473791
theorem B784901177 : Blo 1325481 784901177 := bstep (se 2 (by rfl) ⟨294337941, by rfl⟩ : syracuseStep 784901177 = 588675883) B588675883
theorem B49088273 : Blo 1325481 49088273 := bstep (se 2 (by rfl) ⟨18408102, by rfl⟩ : syracuseStep 49088273 = 36816205) B36816205
theorem B30640315 : Blo 1325481 30640315 := bstep (se 1 (by rfl) ⟨22980236, by rfl⟩ : syracuseStep 30640315 = 45960473) B45960473
theorem B2984255 : Blo 1325481 2984255 := bstep (se 1 (by rfl) ⟨2238191, by rfl⟩ : syracuseStep 2984255 = 4476383) B4476383
theorem B2239643 : Blo 1325481 2239643 := bstep (se 1 (by rfl) ⟨1679732, by rfl⟩ : syracuseStep 2239643 = 3359465) B3359465
theorem B2239771 : Blo 1325481 2239771 := bstep (se 1 (by rfl) ⟨1679828, by rfl⟩ : syracuseStep 2239771 = 3359657) B3359657
theorem B11334127 : Blo 1325481 11334127 := bstep (se 1 (by rfl) ⟨8500595, by rfl⟩ : syracuseStep 11334127 = 17001191) B17001191
theorem B5035385 : Blo 1325481 5035385 := bstep (se 2 (by rfl) ⟨1888269, by rfl⟩ : syracuseStep 5035385 = 3776539) B3776539
theorem B6903863 : Blo 1325481 6903863 := bstep (se 1 (by rfl) ⟨5177897, by rfl⟩ : syracuseStep 6903863 = 10355795) B10355795
theorem B1325799 : Blo 1325481 1325799 := bstep (se 1 (by rfl) ⟨994349, by rfl⟩ : syracuseStep 1325799 = 1988699) B1988699
theorem B4479785 : Blo 1325481 4479785 := bstep (se 2 (by rfl) ⟨1679919, by rfl⟩ : syracuseStep 4479785 = 3359839) B3359839
theorem B1327099 : Blo 1325481 1327099 := bstep (se 1 (by rfl) ⟨995324, by rfl⟩ : syracuseStep 1327099 = 1990649) B1990649
theorem B523608245 : Blo 1325481 523608245 := bstep (se 5 (by rfl) ⟨24544136, by rfl⟩ : syracuseStep 523608245 = 49088273) B49088273
theorem B40853753 : Blo 1325481 40853753 := bstep (se 2 (by rfl) ⟨15320157, by rfl⟩ : syracuseStep 40853753 = 30640315) B30640315
theorem B1493095 : Blo 1325481 1493095 := bstep (se 1 (by rfl) ⟨1119821, by rfl⟩ : syracuseStep 1493095 = 2239643) B2239643
theorem B523267451 : Blo 1325481 523267451 := bstep (se 1 (by rfl) ⟨392450588, by rfl⟩ : syracuseStep 523267451 = 784901177) B784901177
theorem B2986361 : Blo 1325481 2986361 := bstep (se 2 (by rfl) ⟨1119885, by rfl⟩ : syracuseStep 2986361 = 2239771) B2239771
theorem B2986523 : Blo 1325481 2986523 := bstep (se 1 (by rfl) ⟨2239892, by rfl⟩ : syracuseStep 2986523 = 4479785) B4479785
theorem B1988303 : Blo 1325481 1988303 := bstep (se 1 (by rfl) ⟨1491227, by rfl⟩ : syracuseStep 1988303 = 2982455) B2982455
theorem B1988351 : Blo 1325481 1988351 := bstep (se 1 (by rfl) ⟨1491263, by rfl⟩ : syracuseStep 1988351 = 2982527) B2982527
theorem B15112169 : Blo 1325481 15112169 := bstep (se 2 (by rfl) ⟨5667063, by rfl⟩ : syracuseStep 15112169 = 11334127) B11334127
theorem B3356923 : Blo 1325481 3356923 := bstep (se 1 (by rfl) ⟨2517692, by rfl⟩ : syracuseStep 3356923 = 5035385) B5035385
theorem B4602575 : Blo 1325481 4602575 := bstep (se 1 (by rfl) ⟨3451931, by rfl⟩ : syracuseStep 4602575 = 6903863) B6903863
theorem B1989503 : Blo 1325481 1989503 := bstep (se 1 (by rfl) ⟨1492127, by rfl⟩ : syracuseStep 1989503 = 2984255) B2984255
theorem B1990793 : Blo 1325481 1990793 := bstep (se 2 (by rfl) ⟨746547, by rfl⟩ : syracuseStep 1990793 = 1493095) B1493095
theorem B1990907 : Blo 1325481 1990907 := bstep (se 1 (by rfl) ⟨1493180, by rfl⟩ : syracuseStep 1990907 = 2986361) B2986361
theorem B1991015 : Blo 1325481 1991015 := bstep (se 1 (by rfl) ⟨1493261, by rfl⟩ : syracuseStep 1991015 = 2986523) B2986523
theorem B349072163 : Blo 1325481 349072163 := bstep (se 1 (by rfl) ⟨261804122, by rfl⟩ : syracuseStep 349072163 = 523608245) B523608245
theorem B4475897 : Blo 1325481 4475897 := bstep (se 2 (by rfl) ⟨1678461, by rfl⟩ : syracuseStep 4475897 = 3356923) B3356923
theorem B3068383 : Blo 1325481 3068383 := bstep (se 1 (by rfl) ⟨2301287, by rfl⟩ : syracuseStep 3068383 = 4602575) B4602575
theorem B348844967 : Blo 1325481 348844967 := bstep (se 1 (by rfl) ⟨261633725, by rfl⟩ : syracuseStep 348844967 = 523267451) B523267451
theorem B27235835 : Blo 1325481 27235835 := bstep (se 1 (by rfl) ⟨20426876, by rfl⟩ : syracuseStep 27235835 = 40853753) B40853753
theorem B1325535 : Blo 1325481 1325535 := bstep (se 1 (by rfl) ⟨994151, by rfl⟩ : syracuseStep 1325535 = 1988303) B1988303
theorem B1325567 : Blo 1325481 1325567 := bstep (se 1 (by rfl) ⟨994175, by rfl⟩ : syracuseStep 1325567 = 1988351) B1988351
theorem B10074779 : Blo 1325481 10074779 := bstep (se 1 (by rfl) ⟨7556084, by rfl⟩ : syracuseStep 10074779 = 15112169) B15112169
theorem B1326335 : Blo 1325481 1326335 := bstep (se 1 (by rfl) ⟨994751, by rfl⟩ : syracuseStep 1326335 = 1989503) B1989503
theorem B1327195 : Blo 1325481 1327195 := bstep (se 1 (by rfl) ⟨995396, by rfl⟩ : syracuseStep 1327195 = 1990793) B1990793
theorem B1327271 : Blo 1325481 1327271 := bstep (se 1 (by rfl) ⟨995453, by rfl⟩ : syracuseStep 1327271 = 1990907) B1990907
theorem B1327343 : Blo 1325481 1327343 := bstep (se 1 (by rfl) ⟨995507, by rfl⟩ : syracuseStep 1327343 = 1991015) B1991015
theorem B232563311 : Blo 1325481 232563311 := bstep (se 1 (by rfl) ⟨174422483, by rfl⟩ : syracuseStep 232563311 = 348844967) B348844967
theorem B2983931 : Blo 1325481 2983931 := bstep (se 1 (by rfl) ⟨2237948, by rfl⟩ : syracuseStep 2983931 = 4475897) B4475897
theorem B4091177 : Blo 1325481 4091177 := bstep (se 2 (by rfl) ⟨1534191, by rfl⟩ : syracuseStep 4091177 = 3068383) B3068383
theorem B18157223 : Blo 1325481 18157223 := bstep (se 1 (by rfl) ⟨13617917, by rfl⟩ : syracuseStep 18157223 = 27235835) B27235835
theorem B232714775 : Blo 1325481 232714775 := bstep (se 1 (by rfl) ⟨174536081, by rfl⟩ : syracuseStep 232714775 = 349072163) B349072163
theorem B6716519 : Blo 1325481 6716519 := bstep (se 1 (by rfl) ⟨5037389, by rfl⟩ : syracuseStep 6716519 = 10074779) B10074779
theorem B155042207 : Blo 1325481 155042207 := bstep (se 1 (by rfl) ⟨116281655, by rfl⟩ : syracuseStep 155042207 = 232563311) B232563311
theorem B155143183 : Blo 1325481 155143183 := bstep (se 1 (by rfl) ⟨116357387, by rfl⟩ : syracuseStep 155143183 = 232714775) B232714775
theorem B4477679 : Blo 1325481 4477679 := bstep (se 1 (by rfl) ⟨3358259, by rfl⟩ : syracuseStep 4477679 = 6716519) B6716519
theorem B12104815 : Blo 1325481 12104815 := bstep (se 1 (by rfl) ⟨9078611, by rfl⟩ : syracuseStep 12104815 = 18157223) B18157223
theorem B1989287 : Blo 1325481 1989287 := bstep (se 1 (by rfl) ⟨1491965, by rfl⟩ : syracuseStep 1989287 = 2983931) B2983931
theorem B2727451 : Blo 1325481 2727451 := bstep (se 1 (by rfl) ⟨2045588, by rfl⟩ : syracuseStep 2727451 = 4091177) B4091177
theorem B206857577 : Blo 1325481 206857577 := bstep (se 2 (by rfl) ⟨77571591, by rfl⟩ : syracuseStep 206857577 = 155143183) B155143183
theorem B16139753 : Blo 1325481 16139753 := bstep (se 2 (by rfl) ⟨6052407, by rfl⟩ : syracuseStep 16139753 = 12104815) B12104815
theorem B103361471 : Blo 1325481 103361471 := bstep (se 1 (by rfl) ⟨77521103, by rfl⟩ : syracuseStep 103361471 = 155042207) B155042207
theorem B2985119 : Blo 1325481 2985119 := bstep (se 1 (by rfl) ⟨2238839, by rfl⟩ : syracuseStep 2985119 = 4477679) B4477679
theorem B14546405 : Blo 1325481 14546405 := bstep (se 4 (by rfl) ⟨1363725, by rfl⟩ : syracuseStep 14546405 = 2727451) B2727451
theorem B1326191 : Blo 1325481 1326191 := bstep (se 1 (by rfl) ⟨994643, by rfl⟩ : syracuseStep 1326191 = 1989287) B1989287
theorem B137905051 : Blo 1325481 137905051 := bstep (se 1 (by rfl) ⟨103428788, by rfl⟩ : syracuseStep 137905051 = 206857577) B206857577
theorem B10759835 : Blo 1325481 10759835 := bstep (se 1 (by rfl) ⟨8069876, by rfl⟩ : syracuseStep 10759835 = 16139753) B16139753
theorem B68907647 : Blo 1325481 68907647 := bstep (se 1 (by rfl) ⟨51680735, by rfl⟩ : syracuseStep 68907647 = 103361471) B103361471
theorem B9697603 : Blo 1325481 9697603 := bstep (se 1 (by rfl) ⟨7273202, by rfl⟩ : syracuseStep 9697603 = 14546405) B14546405
theorem B1990079 : Blo 1325481 1990079 := bstep (se 1 (by rfl) ⟨1492559, by rfl⟩ : syracuseStep 1990079 = 2985119) B2985119
theorem B12930137 : Blo 1325481 12930137 := bstep (se 2 (by rfl) ⟨4848801, by rfl⟩ : syracuseStep 12930137 = 9697603) B9697603
theorem B183873401 : Blo 1325481 183873401 := bstep (se 2 (by rfl) ⟨68952525, by rfl⟩ : syracuseStep 183873401 = 137905051) B137905051
theorem B28692893 : Blo 1325481 28692893 := bstep (se 3 (by rfl) ⟨5379917, by rfl⟩ : syracuseStep 28692893 = 10759835) B10759835
theorem B45938431 : Blo 1325481 45938431 := bstep (se 1 (by rfl) ⟨34453823, by rfl⟩ : syracuseStep 45938431 = 68907647) B68907647
theorem B1326719 : Blo 1325481 1326719 := bstep (se 1 (by rfl) ⟨995039, by rfl⟩ : syracuseStep 1326719 = 1990079) B1990079
theorem B19128595 : Blo 1325481 19128595 := bstep (se 1 (by rfl) ⟨14346446, by rfl⟩ : syracuseStep 19128595 = 28692893) B28692893
theorem B8620091 : Blo 1325481 8620091 := bstep (se 1 (by rfl) ⟨6465068, by rfl⟩ : syracuseStep 8620091 = 12930137) B12930137
theorem B122582267 : Blo 1325481 122582267 := bstep (se 1 (by rfl) ⟨91936700, by rfl⟩ : syracuseStep 122582267 = 183873401) B183873401
theorem B61251241 : Blo 1325481 61251241 := bstep (se 2 (by rfl) ⟨22969215, by rfl⟩ : syracuseStep 61251241 = 45938431) B45938431
theorem B81668321 : Blo 1325481 81668321 := bstep (se 2 (by rfl) ⟨30625620, by rfl⟩ : syracuseStep 81668321 = 61251241) B61251241
theorem B25504793 : Blo 1325481 25504793 := bstep (se 2 (by rfl) ⟨9564297, by rfl⟩ : syracuseStep 25504793 = 19128595) B19128595
theorem B5746727 : Blo 1325481 5746727 := bstep (se 1 (by rfl) ⟨4310045, by rfl⟩ : syracuseStep 5746727 = 8620091) B8620091
theorem B81721511 : Blo 1325481 81721511 := bstep (se 1 (by rfl) ⟨61291133, by rfl⟩ : syracuseStep 81721511 = 122582267) B122582267
theorem B54445547 : Blo 1325481 54445547 := bstep (se 1 (by rfl) ⟨40834160, by rfl⟩ : syracuseStep 54445547 = 81668321) B81668321
theorem B54481007 : Blo 1325481 54481007 := bstep (se 1 (by rfl) ⟨40860755, by rfl⟩ : syracuseStep 54481007 = 81721511) B81721511
theorem B17003195 : Blo 1325481 17003195 := bstep (se 1 (by rfl) ⟨12752396, by rfl⟩ : syracuseStep 17003195 = 25504793) B25504793
theorem B3831151 : Blo 1325481 3831151 := bstep (se 1 (by rfl) ⟨2873363, by rfl⟩ : syracuseStep 3831151 = 5746727) B5746727
theorem B5108201 : Blo 1325481 5108201 := bstep (se 2 (by rfl) ⟨1915575, by rfl⟩ : syracuseStep 5108201 = 3831151) B3831151
theorem B36320671 : Blo 1325481 36320671 := bstep (se 1 (by rfl) ⟨27240503, by rfl⟩ : syracuseStep 36320671 = 54481007) B54481007
theorem B11335463 : Blo 1325481 11335463 := bstep (se 1 (by rfl) ⟨8501597, by rfl⟩ : syracuseStep 11335463 = 17003195) B17003195
theorem B36297031 : Blo 1325481 36297031 := bstep (se 1 (by rfl) ⟨27222773, by rfl⟩ : syracuseStep 36297031 = 54445547) B54445547
theorem B7556975 : Blo 1325481 7556975 := bstep (se 1 (by rfl) ⟨5667731, by rfl⟩ : syracuseStep 7556975 = 11335463) B11335463
theorem B48427561 : Blo 1325481 48427561 := bstep (se 2 (by rfl) ⟨18160335, by rfl⟩ : syracuseStep 48427561 = 36320671) B36320671
theorem B3405467 : Blo 1325481 3405467 := bstep (se 1 (by rfl) ⟨2554100, by rfl⟩ : syracuseStep 3405467 = 5108201) B5108201
theorem B48396041 : Blo 1325481 48396041 := bstep (se 2 (by rfl) ⟨18148515, by rfl⟩ : syracuseStep 48396041 = 36297031) B36297031
theorem B2270311 : Blo 1325481 2270311 := bstep (se 1 (by rfl) ⟨1702733, by rfl⟩ : syracuseStep 2270311 = 3405467) B3405467
theorem B258280325 : Blo 1325481 258280325 := bstep (se 4 (by rfl) ⟨24213780, by rfl⟩ : syracuseStep 258280325 = 48427561) B48427561
theorem B32264027 : Blo 1325481 32264027 := bstep (se 1 (by rfl) ⟨24198020, by rfl⟩ : syracuseStep 32264027 = 48396041) B48396041
theorem B5037983 : Blo 1325481 5037983 := bstep (se 1 (by rfl) ⟨3778487, by rfl⟩ : syracuseStep 5037983 = 7556975) B7556975
theorem B12108325 : Blo 1325481 12108325 := bstep (se 4 (by rfl) ⟨1135155, by rfl⟩ : syracuseStep 12108325 = 2270311) B2270311
theorem B21509351 : Blo 1325481 21509351 := bstep (se 1 (by rfl) ⟨16132013, by rfl⟩ : syracuseStep 21509351 = 32264027) B32264027
theorem B172186883 : Blo 1325481 172186883 := bstep (se 1 (by rfl) ⟨129140162, by rfl⟩ : syracuseStep 172186883 = 258280325) B258280325
theorem B3358655 : Blo 1325481 3358655 := bstep (se 1 (by rfl) ⟨2518991, by rfl⟩ : syracuseStep 3358655 = 5037983) B5037983
theorem B2239103 : Blo 1325481 2239103 := bstep (se 1 (by rfl) ⟨1679327, by rfl⟩ : syracuseStep 2239103 = 3358655) B3358655
theorem B14339567 : Blo 1325481 14339567 := bstep (se 1 (by rfl) ⟨10754675, by rfl⟩ : syracuseStep 14339567 = 21509351) B21509351
theorem B114791255 : Blo 1325481 114791255 := bstep (se 1 (by rfl) ⟨86093441, by rfl⟩ : syracuseStep 114791255 = 172186883) B172186883
theorem B16144433 : Blo 1325481 16144433 := bstep (se 2 (by rfl) ⟨6054162, by rfl⟩ : syracuseStep 16144433 = 12108325) B12108325
theorem B1492735 : Blo 1325481 1492735 := bstep (se 1 (by rfl) ⟨1119551, by rfl⟩ : syracuseStep 1492735 = 2239103) B2239103
theorem B76527503 : Blo 1325481 76527503 := bstep (se 1 (by rfl) ⟨57395627, by rfl⟩ : syracuseStep 76527503 = 114791255) B114791255
theorem B10762955 : Blo 1325481 10762955 := bstep (se 1 (by rfl) ⟨8072216, by rfl⟩ : syracuseStep 10762955 = 16144433) B16144433
theorem B9559711 : Blo 1325481 9559711 := bstep (se 1 (by rfl) ⟨7169783, by rfl⟩ : syracuseStep 9559711 = 14339567) B14339567
theorem B51018335 : Blo 1325481 51018335 := bstep (se 1 (by rfl) ⟨38263751, by rfl⟩ : syracuseStep 51018335 = 76527503) B76527503
theorem B7175303 : Blo 1325481 7175303 := bstep (se 1 (by rfl) ⟨5381477, by rfl⟩ : syracuseStep 7175303 = 10762955) B10762955
theorem B12746281 : Blo 1325481 12746281 := bstep (se 2 (by rfl) ⟨4779855, by rfl⟩ : syracuseStep 12746281 = 9559711) B9559711
theorem B1990313 : Blo 1325481 1990313 := bstep (se 2 (by rfl) ⟨746367, by rfl⟩ : syracuseStep 1990313 = 1492735) B1492735
theorem B16995041 : Blo 1325481 16995041 := bstep (se 2 (by rfl) ⟨6373140, by rfl⟩ : syracuseStep 16995041 = 12746281) B12746281
theorem B34012223 : Blo 1325481 34012223 := bstep (se 1 (by rfl) ⟨25509167, by rfl⟩ : syracuseStep 34012223 = 51018335) B51018335
theorem B4783535 : Blo 1325481 4783535 := bstep (se 1 (by rfl) ⟨3587651, by rfl⟩ : syracuseStep 4783535 = 7175303) B7175303
theorem B1326875 : Blo 1325481 1326875 := bstep (se 1 (by rfl) ⟨995156, by rfl⟩ : syracuseStep 1326875 = 1990313) B1990313
theorem B11330027 : Blo 1325481 11330027 := bstep (se 1 (by rfl) ⟨8497520, by rfl⟩ : syracuseStep 11330027 = 16995041) B16995041
theorem B3189023 : Blo 1325481 3189023 := bstep (se 1 (by rfl) ⟨2391767, by rfl⟩ : syracuseStep 3189023 = 4783535) B4783535
theorem B22674815 : Blo 1325481 22674815 := bstep (se 1 (by rfl) ⟨17006111, by rfl⟩ : syracuseStep 22674815 = 34012223) B34012223
theorem B7553351 : Blo 1325481 7553351 := bstep (se 1 (by rfl) ⟨5665013, by rfl⟩ : syracuseStep 7553351 = 11330027) B11330027
theorem B15116543 : Blo 1325481 15116543 := bstep (se 1 (by rfl) ⟨11337407, by rfl⟩ : syracuseStep 15116543 = 22674815) B22674815
theorem B2126015 : Blo 1325481 2126015 := bstep (se 1 (by rfl) ⟨1594511, by rfl⟩ : syracuseStep 2126015 = 3189023) B3189023
theorem B1417343 : Blo 1325481 1417343 := bstep (se 1 (by rfl) ⟨1063007, by rfl⟩ : syracuseStep 1417343 = 2126015) B2126015
theorem B10077695 : Blo 1325481 10077695 := bstep (se 1 (by rfl) ⟨7558271, by rfl⟩ : syracuseStep 10077695 = 15116543) B15116543
theorem B5035567 : Blo 1325481 5035567 := bstep (se 1 (by rfl) ⟨3776675, by rfl⟩ : syracuseStep 5035567 = 7553351) B7553351
theorem B6718463 : Blo 1325481 6718463 := bstep (se 1 (by rfl) ⟨5038847, by rfl⟩ : syracuseStep 6718463 = 10077695) B10077695
theorem B3779581 : Blo 1325481 3779581 := bstep (se 3 (by rfl) ⟨708671, by rfl⟩ : syracuseStep 3779581 = 1417343) B1417343
theorem B6714089 : Blo 1325481 6714089 := bstep (se 2 (by rfl) ⟨2517783, by rfl⟩ : syracuseStep 6714089 = 5035567) B5035567
theorem B5039441 : Blo 1325481 5039441 := bstep (se 2 (by rfl) ⟨1889790, by rfl⟩ : syracuseStep 5039441 = 3779581) B3779581
theorem B4476059 : Blo 1325481 4476059 := bstep (se 1 (by rfl) ⟨3357044, by rfl⟩ : syracuseStep 4476059 = 6714089) B6714089
theorem B4478975 : Blo 1325481 4478975 := bstep (se 1 (by rfl) ⟨3359231, by rfl⟩ : syracuseStep 4478975 = 6718463) B6718463
theorem B3359627 : Blo 1325481 3359627 := bstep (se 1 (by rfl) ⟨2519720, by rfl⟩ : syracuseStep 3359627 = 5039441) B5039441
theorem B2984039 : Blo 1325481 2984039 := bstep (se 1 (by rfl) ⟨2238029, by rfl⟩ : syracuseStep 2984039 = 4476059) B4476059
theorem B2985983 : Blo 1325481 2985983 := bstep (se 1 (by rfl) ⟨2239487, by rfl⟩ : syracuseStep 2985983 = 4478975) B4478975
theorem B2239751 : Blo 1325481 2239751 := bstep (se 1 (by rfl) ⟨1679813, by rfl⟩ : syracuseStep 2239751 = 3359627) B3359627
theorem B1990655 : Blo 1325481 1990655 := bstep (se 1 (by rfl) ⟨1492991, by rfl⟩ : syracuseStep 1990655 = 2985983) B2985983
theorem B1989359 : Blo 1325481 1989359 := bstep (se 1 (by rfl) ⟨1492019, by rfl⟩ : syracuseStep 1989359 = 2984039) B2984039
theorem B1493167 : Blo 1325481 1493167 := bstep (se 1 (by rfl) ⟨1119875, by rfl⟩ : syracuseStep 1493167 = 2239751) B2239751
theorem B1326239 : Blo 1325481 1326239 := bstep (se 1 (by rfl) ⟨994679, by rfl⟩ : syracuseStep 1326239 = 1989359) B1989359
theorem B1327103 : Blo 1325481 1327103 := bstep (se 1 (by rfl) ⟨995327, by rfl⟩ : syracuseStep 1327103 = 1990655) B1990655
theorem B1990889 : Blo 1325481 1990889 := bstep (se 2 (by rfl) ⟨746583, by rfl⟩ : syracuseStep 1990889 = 1493167) B1493167
theorem B1327259 : Blo 1325481 1327259 := bstep (se 1 (by rfl) ⟨995444, by rfl⟩ : syracuseStep 1327259 = 1990889) B1990889

theorem C0 (j : ℕ) (h1 : 331370 ≤ j) (h2 : j ≤ 331869) : Blo 1325481 (4 * j + 3) := by
  interval_cases j
  · exact B1325483
  · exact B1325487
  · exact B1325491
  · exact B1325495
  · exact B1325499
  · exact B1325503
  · exact B1325507
  · exact B1325511
  · exact B1325515
  · exact B1325519
  · exact B1325523
  · exact B1325527
  · exact B1325531
  · exact B1325535
  · exact B1325539
  · exact B1325543
  · exact B1325547
  · exact B1325551
  · exact B1325555
  · exact B1325559
  · exact B1325563
  · exact B1325567
  · exact B1325571
  · exact B1325575
  · exact B1325579
  · exact B1325583
  · exact B1325587
  · exact B1325591
  · exact B1325595
  · exact B1325599
  · exact B1325603
  · exact B1325607
  · exact B1325611
  · exact B1325615
  · exact B1325619
  · exact B1325623
  · exact B1325627
  · exact B1325631
  · exact B1325635
  · exact B1325639
  · exact B1325643
  · exact B1325647
  · exact B1325651
  · exact B1325655
  · exact B1325659
  · exact B1325663
  · exact B1325667
  · exact B1325671
  · exact B1325675
  · exact B1325679
  · exact B1325683
  · exact B1325687
  · exact B1325691
  · exact B1325695
  · exact B1325699
  · exact B1325703
  · exact B1325707
  · exact B1325711
  · exact B1325715
  · exact B1325719
  · exact B1325723
  · exact B1325727
  · exact B1325731
  · exact B1325735
  · exact B1325739
  · exact B1325743
  · exact B1325747
  · exact B1325751
  · exact B1325755
  · exact B1325759
  · exact B1325763
  · exact B1325767
  · exact B1325771
  · exact B1325775
  · exact B1325779
  · exact B1325783
  · exact B1325787
  · exact B1325791
  · exact B1325795
  · exact B1325799
  · exact B1325803
  · exact B1325807
  · exact B1325811
  · exact B1325815
  · exact B1325819
  · exact B1325823
  · exact B1325827
  · exact B1325831
  · exact B1325835
  · exact B1325839
  · exact B1325843
  · exact B1325847
  · exact B1325851
  · exact B1325855
  · exact B1325859
  · exact B1325863
  · exact B1325867
  · exact B1325871
  · exact B1325875
  · exact B1325879
  · exact B1325883
  · exact B1325887
  · exact B1325891
  · exact B1325895
  · exact B1325899
  · exact B1325903
  · exact B1325907
  · exact B1325911
  · exact B1325915
  · exact B1325919
  · exact B1325923
  · exact B1325927
  · exact B1325931
  · exact B1325935
  · exact B1325939
  · exact B1325943
  · exact B1325947
  · exact B1325951
  · exact B1325955
  · exact B1325959
  · exact B1325963
  · exact B1325967
  · exact B1325971
  · exact B1325975
  · exact B1325979
  · exact B1325983
  · exact B1325987
  · exact B1325991
  · exact B1325995
  · exact B1325999
  · exact B1326003
  · exact B1326007
  · exact B1326011
  · exact B1326015
  · exact B1326019
  · exact B1326023
  · exact B1326027
  · exact B1326031
  · exact B1326035
  · exact B1326039
  · exact B1326043
  · exact B1326047
  · exact B1326051
  · exact B1326055
  · exact B1326059
  · exact B1326063
  · exact B1326067
  · exact B1326071
  · exact B1326075
  · exact B1326079
  · exact B1326083
  · exact B1326087
  · exact B1326091
  · exact B1326095
  · exact B1326099
  · exact B1326103
  · exact B1326107
  · exact B1326111
  · exact B1326115
  · exact B1326119
  · exact B1326123
  · exact B1326127
  · exact B1326131
  · exact B1326135
  · exact B1326139
  · exact B1326143
  · exact B1326147
  · exact B1326151
  · exact B1326155
  · exact B1326159
  · exact B1326163
  · exact B1326167
  · exact B1326171
  · exact B1326175
  · exact B1326179
  · exact B1326183
  · exact B1326187
  · exact B1326191
  · exact B1326195
  · exact B1326199
  · exact B1326203
  · exact B1326207
  · exact B1326211
  · exact B1326215
  · exact B1326219
  · exact B1326223
  · exact B1326227
  · exact B1326231
  · exact B1326235
  · exact B1326239
  · exact B1326243
  · exact B1326247
  · exact B1326251
  · exact B1326255
  · exact B1326259
  · exact B1326263
  · exact B1326267
  · exact B1326271
  · exact B1326275
  · exact B1326279
  · exact B1326283
  · exact B1326287
  · exact B1326291
  · exact B1326295
  · exact B1326299
  · exact B1326303
  · exact B1326307
  · exact B1326311
  · exact B1326315
  · exact B1326319
  · exact B1326323
  · exact B1326327
  · exact B1326331
  · exact B1326335
  · exact B1326339
  · exact B1326343
  · exact B1326347
  · exact B1326351
  · exact B1326355
  · exact B1326359
  · exact B1326363
  · exact B1326367
  · exact B1326371
  · exact B1326375
  · exact B1326379
  · exact B1326383
  · exact B1326387
  · exact B1326391
  · exact B1326395
  · exact B1326399
  · exact B1326403
  · exact B1326407
  · exact B1326411
  · exact B1326415
  · exact B1326419
  · exact B1326423
  · exact B1326427
  · exact B1326431
  · exact B1326435
  · exact B1326439
  · exact B1326443
  · exact B1326447
  · exact B1326451
  · exact B1326455
  · exact B1326459
  · exact B1326463
  · exact B1326467
  · exact B1326471
  · exact B1326475
  · exact B1326479
  · exact B1326483
  · exact B1326487
  · exact B1326491
  · exact B1326495
  · exact B1326499
  · exact B1326503
  · exact B1326507
  · exact B1326511
  · exact B1326515
  · exact B1326519
  · exact B1326523
  · exact B1326527
  · exact B1326531
  · exact B1326535
  · exact B1326539
  · exact B1326543
  · exact B1326547
  · exact B1326551
  · exact B1326555
  · exact B1326559
  · exact B1326563
  · exact B1326567
  · exact B1326571
  · exact B1326575
  · exact B1326579
  · exact B1326583
  · exact B1326587
  · exact B1326591
  · exact B1326595
  · exact B1326599
  · exact B1326603
  · exact B1326607
  · exact B1326611
  · exact B1326615
  · exact B1326619
  · exact B1326623
  · exact B1326627
  · exact B1326631
  · exact B1326635
  · exact B1326639
  · exact B1326643
  · exact B1326647
  · exact B1326651
  · exact B1326655
  · exact B1326659
  · exact B1326663
  · exact B1326667
  · exact B1326671
  · exact B1326675
  · exact B1326679
  · exact B1326683
  · exact B1326687
  · exact B1326691
  · exact B1326695
  · exact B1326699
  · exact B1326703
  · exact B1326707
  · exact B1326711
  · exact B1326715
  · exact B1326719
  · exact B1326723
  · exact B1326727
  · exact B1326731
  · exact B1326735
  · exact B1326739
  · exact B1326743
  · exact B1326747
  · exact B1326751
  · exact B1326755
  · exact B1326759
  · exact B1326763
  · exact B1326767
  · exact B1326771
  · exact B1326775
  · exact B1326779
  · exact B1326783
  · exact B1326787
  · exact B1326791
  · exact B1326795
  · exact B1326799
  · exact B1326803
  · exact B1326807
  · exact B1326811
  · exact B1326815
  · exact B1326819
  · exact B1326823
  · exact B1326827
  · exact B1326831
  · exact B1326835
  · exact B1326839
  · exact B1326843
  · exact B1326847
  · exact B1326851
  · exact B1326855
  · exact B1326859
  · exact B1326863
  · exact B1326867
  · exact B1326871
  · exact B1326875
  · exact B1326879
  · exact B1326883
  · exact B1326887
  · exact B1326891
  · exact B1326895
  · exact B1326899
  · exact B1326903
  · exact B1326907
  · exact B1326911
  · exact B1326915
  · exact B1326919
  · exact B1326923
  · exact B1326927
  · exact B1326931
  · exact B1326935
  · exact B1326939
  · exact B1326943
  · exact B1326947
  · exact B1326951
  · exact B1326955
  · exact B1326959
  · exact B1326963
  · exact B1326967
  · exact B1326971
  · exact B1326975
  · exact B1326979
  · exact B1326983
  · exact B1326987
  · exact B1326991
  · exact B1326995
  · exact B1326999
  · exact B1327003
  · exact B1327007
  · exact B1327011
  · exact B1327015
  · exact B1327019
  · exact B1327023
  · exact B1327027
  · exact B1327031
  · exact B1327035
  · exact B1327039
  · exact B1327043
  · exact B1327047
  · exact B1327051
  · exact B1327055
  · exact B1327059
  · exact B1327063
  · exact B1327067
  · exact B1327071
  · exact B1327075
  · exact B1327079
  · exact B1327083
  · exact B1327087
  · exact B1327091
  · exact B1327095
  · exact B1327099
  · exact B1327103
  · exact B1327107
  · exact B1327111
  · exact B1327115
  · exact B1327119
  · exact B1327123
  · exact B1327127
  · exact B1327131
  · exact B1327135
  · exact B1327139
  · exact B1327143
  · exact B1327147
  · exact B1327151
  · exact B1327155
  · exact B1327159
  · exact B1327163
  · exact B1327167
  · exact B1327171
  · exact B1327175
  · exact B1327179
  · exact B1327183
  · exact B1327187
  · exact B1327191
  · exact B1327195
  · exact B1327199
  · exact B1327203
  · exact B1327207
  · exact B1327211
  · exact B1327215
  · exact B1327219
  · exact B1327223
  · exact B1327227
  · exact B1327231
  · exact B1327235
  · exact B1327239
  · exact B1327243
  · exact B1327247
  · exact B1327251
  · exact B1327255
  · exact B1327259
  · exact B1327263
  · exact B1327267
  · exact B1327271
  · exact B1327275
  · exact B1327279
  · exact B1327283
  · exact B1327287
  · exact B1327291
  · exact B1327295
  · exact B1327299
  · exact B1327303
  · exact B1327307
  · exact B1327311
  · exact B1327315
  · exact B1327319
  · exact B1327323
  · exact B1327327
  · exact B1327331
  · exact B1327335
  · exact B1327339
  · exact B1327343
  · exact B1327347
  · exact B1327351
  · exact B1327355
  · exact B1327359
  · exact B1327363
  · exact B1327367
  · exact B1327371
  · exact B1327375
  · exact B1327379
  · exact B1327383
  · exact B1327387
  · exact B1327391
  · exact B1327395
  · exact B1327399
  · exact B1327403
  · exact B1327407
  · exact B1327411
  · exact B1327415
  · exact B1327419
  · exact B1327423
  · exact B1327427
  · exact B1327431
  · exact B1327435
  · exact B1327439
  · exact B1327443
  · exact B1327447
  · exact B1327451
  · exact B1327455
  · exact B1327459
  · exact B1327463
  · exact B1327467
  · exact B1327471
  · exact B1327475
  · exact B1327479

theorem solution (m : ℕ) (hlo : 1325481 ≤ m) (hhi : m ≤ 1327481) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 331370 ≤ j := by omega
    have hj2 : j ≤ 331869 := by omega
    have hb : Blo 1325481 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
