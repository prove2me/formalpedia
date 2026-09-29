-- Prove2me | solution 1 for syracuse_descends_range_1364501_1366501
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:12:57.588215+00:00
-- url     : https://prove2.me/submissions/c7f19456-45be-446b-92dd-125d4c3f1260

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


theorem B3072005 : Blo 1364501 3072005 := bbase (se 4 (by rfl) ⟨288000, by rfl⟩ : syracuseStep 3072005 = 576001) (by norm_num)
theorem B2048021 : Blo 1364501 2048021 := bbase (se 6 (by rfl) ⟨48000, by rfl⟩ : syracuseStep 2048021 = 96001) (by norm_num)
theorem B2048045 : Blo 1364501 2048045 := bbase (se 3 (by rfl) ⟨384008, by rfl⟩ : syracuseStep 2048045 = 768017) (by norm_num)
theorem B1663033 : Blo 1364501 1663033 := bbase (se 2 (by rfl) ⟨623637, by rfl⟩ : syracuseStep 1663033 = 1247275) (by norm_num)
theorem B2187325 : Blo 1364501 2187325 := bbase (se 3 (by rfl) ⟨410123, by rfl⟩ : syracuseStep 2187325 = 820247) (by norm_num)
theorem B2048069 : Blo 1364501 2048069 := bbase (se 4 (by rfl) ⟨192006, by rfl⟩ : syracuseStep 2048069 = 384013) (by norm_num)
theorem B3072077 : Blo 1364501 3072077 := bbase (se 3 (by rfl) ⟨576014, by rfl⟩ : syracuseStep 3072077 = 1152029) (by norm_num)
theorem B22134869 : Blo 1364501 22134869 := bbase (se 8 (by rfl) ⟨129696, by rfl⟩ : syracuseStep 22134869 = 259393) (by norm_num)
theorem B2048093 : Blo 1364501 2048093 := bbase (se 3 (by rfl) ⟨384017, by rfl⟩ : syracuseStep 2048093 = 768035) (by norm_num)
theorem B1458281 : Blo 1364501 1458281 := bbase (se 2 (by rfl) ⟨546855, by rfl⟩ : syracuseStep 1458281 = 1093711) (by norm_num)
theorem B2048117 : Blo 1364501 2048117 := bbase (se 5 (by rfl) ⟨96005, by rfl⟩ : syracuseStep 2048117 = 192011) (by norm_num)
theorem B1728641 : Blo 1364501 1728641 := bbase (se 2 (by rfl) ⟨648240, by rfl⟩ : syracuseStep 1728641 = 1296481) (by norm_num)
theorem B2048141 : Blo 1364501 2048141 := bbase (se 3 (by rfl) ⟨384026, by rfl⟩ : syracuseStep 2048141 = 768053) (by norm_num)
theorem B3072149 : Blo 1364501 3072149 := bbase (se 6 (by rfl) ⟨72003, by rfl⟩ : syracuseStep 3072149 = 144007) (by norm_num)
theorem B3457181 : Blo 1364501 3457181 := bbase (se 3 (by rfl) ⟨648221, by rfl⟩ : syracuseStep 3457181 = 1296443) (by norm_num)
theorem B2048165 : Blo 1364501 2048165 := bbase (se 4 (by rfl) ⟨192015, by rfl⟩ : syracuseStep 2048165 = 384031) (by norm_num)
theorem B1728697 : Blo 1364501 1728697 := bbase (se 2 (by rfl) ⟨648261, by rfl⟩ : syracuseStep 1728697 = 1296523) (by norm_num)
theorem B2048189 : Blo 1364501 2048189 := bbase (se 3 (by rfl) ⟨384035, by rfl⟩ : syracuseStep 2048189 = 768071) (by norm_num)
theorem B2048213 : Blo 1364501 2048213 := bbase (se 7 (by rfl) ⟨24002, by rfl⟩ : syracuseStep 2048213 = 48005) (by norm_num)
theorem B3072221 : Blo 1364501 3072221 := bbase (se 3 (by rfl) ⟨576041, by rfl⟩ : syracuseStep 3072221 = 1152083) (by norm_num)
theorem B2048237 : Blo 1364501 2048237 := bbase (se 3 (by rfl) ⟨384044, by rfl⟩ : syracuseStep 2048237 = 768089) (by norm_num)
theorem B2048261 : Blo 1364501 2048261 := bbase (se 4 (by rfl) ⟨192024, by rfl⟩ : syracuseStep 2048261 = 384049) (by norm_num)
theorem B1728793 : Blo 1364501 1728793 := bbase (se 2 (by rfl) ⟨648297, by rfl⟩ : syracuseStep 1728793 = 1296595) (by norm_num)
theorem B2048285 : Blo 1364501 2048285 := bbase (se 3 (by rfl) ⟨384053, by rfl⟩ : syracuseStep 2048285 = 768107) (by norm_num)
theorem B3072293 : Blo 1364501 3072293 := bbase (se 4 (by rfl) ⟨288027, by rfl⟩ : syracuseStep 3072293 = 576055) (by norm_num)
theorem B2048309 : Blo 1364501 2048309 := bbase (se 5 (by rfl) ⟨96014, by rfl⟩ : syracuseStep 2048309 = 192029) (by norm_num)
theorem B2187581 : Blo 1364501 2187581 := bbase (se 3 (by rfl) ⟨410171, by rfl⟩ : syracuseStep 2187581 = 820343) (by norm_num)
theorem B2048333 : Blo 1364501 2048333 := bbase (se 3 (by rfl) ⟨384062, by rfl⟩ : syracuseStep 2048333 = 768125) (by norm_num)
theorem B1556833 : Blo 1364501 1556833 := bbase (se 2 (by rfl) ⟨583812, by rfl⟩ : syracuseStep 1556833 = 1167625) (by norm_num)
theorem B2048357 : Blo 1364501 2048357 := bbase (se 4 (by rfl) ⟨192033, by rfl⟩ : syracuseStep 2048357 = 384067) (by norm_num)
theorem B1458533 : Blo 1364501 1458533 := bbase (se 4 (by rfl) ⟨136737, by rfl⟩ : syracuseStep 1458533 = 273475) (by norm_num)
theorem B3072365 : Blo 1364501 3072365 := bbase (se 3 (by rfl) ⟨576068, by rfl⟩ : syracuseStep 3072365 = 1152137) (by norm_num)
theorem B2048381 : Blo 1364501 2048381 := bbase (se 3 (by rfl) ⟨384071, by rfl⟩ : syracuseStep 2048381 = 768143) (by norm_num)
theorem B2048405 : Blo 1364501 2048405 := bbase (se 6 (by rfl) ⟨48009, by rfl⟩ : syracuseStep 2048405 = 96019) (by norm_num)
theorem B2048429 : Blo 1364501 2048429 := bbase (se 3 (by rfl) ⟨384080, by rfl⟩ : syracuseStep 2048429 = 768161) (by norm_num)
theorem B3072437 : Blo 1364501 3072437 := bbase (se 5 (by rfl) ⟨144020, by rfl⟩ : syracuseStep 3072437 = 288041) (by norm_num)
theorem B2048453 : Blo 1364501 2048453 := bbase (se 4 (by rfl) ⟨192042, by rfl⟩ : syracuseStep 2048453 = 384085) (by norm_num)
theorem B1728965 : Blo 1364501 1728965 := bbase (se 4 (by rfl) ⟨162090, by rfl⟩ : syracuseStep 1728965 = 324181) (by norm_num)
theorem B2769365 : Blo 1364501 2769365 := bbase (se 7 (by rfl) ⟨32453, by rfl⟩ : syracuseStep 2769365 = 64907) (by norm_num)
theorem B2048477 : Blo 1364501 2048477 := bbase (se 3 (by rfl) ⟨384089, by rfl⟩ : syracuseStep 2048477 = 768179) (by norm_num)
theorem B2048501 : Blo 1364501 2048501 := bbase (se 5 (by rfl) ⟨96023, by rfl⟩ : syracuseStep 2048501 = 192047) (by norm_num)
theorem B3457525 : Blo 1364501 3457525 := bbase (se 5 (by rfl) ⟨162071, by rfl⟩ : syracuseStep 3457525 = 324143) (by norm_num)
theorem B3072509 : Blo 1364501 3072509 := bbase (se 3 (by rfl) ⟨576095, by rfl⟩ : syracuseStep 3072509 = 1152191) (by norm_num)
theorem B1729021 : Blo 1364501 1729021 := bbase (se 3 (by rfl) ⟨324191, by rfl⟩ : syracuseStep 1729021 = 648383) (by norm_num)
theorem B2048525 : Blo 1364501 2048525 := bbase (se 3 (by rfl) ⟨384098, by rfl⟩ : syracuseStep 2048525 = 768197) (by norm_num)
theorem B2769437 : Blo 1364501 2769437 := bbase (se 3 (by rfl) ⟨519269, by rfl⟩ : syracuseStep 2769437 = 1038539) (by norm_num)
theorem B2048549 : Blo 1364501 2048549 := bbase (se 4 (by rfl) ⟨192051, by rfl⟩ : syracuseStep 2048549 = 384103) (by norm_num)
theorem B2048573 : Blo 1364501 2048573 := bbase (se 3 (by rfl) ⟨384107, by rfl⟩ : syracuseStep 2048573 = 768215) (by norm_num)
theorem B3072581 : Blo 1364501 3072581 := bbase (se 4 (by rfl) ⟨288054, by rfl⟩ : syracuseStep 3072581 = 576109) (by norm_num)
theorem B2048597 : Blo 1364501 2048597 := bbase (se 8 (by rfl) ⟨12003, by rfl⟩ : syracuseStep 2048597 = 24007) (by norm_num)
theorem B6914645 : Blo 1364501 6914645 := bbase (se 8 (by rfl) ⟨40515, by rfl⟩ : syracuseStep 6914645 = 81031) (by norm_num)
theorem B1729117 : Blo 1364501 1729117 := bbase (se 3 (by rfl) ⟨324209, by rfl⟩ : syracuseStep 1729117 = 648419) (by norm_num)
theorem B3457637 : Blo 1364501 3457637 := bbase (se 4 (by rfl) ⟨324153, by rfl⟩ : syracuseStep 3457637 = 648307) (by norm_num)
theorem B2048621 : Blo 1364501 2048621 := bbase (se 3 (by rfl) ⟨384116, by rfl⟩ : syracuseStep 2048621 = 768233) (by norm_num)
theorem B2048645 : Blo 1364501 2048645 := bbase (se 4 (by rfl) ⟨192060, by rfl⟩ : syracuseStep 2048645 = 384121) (by norm_num)
theorem B3072653 : Blo 1364501 3072653 := bbase (se 3 (by rfl) ⟨576122, by rfl⟩ : syracuseStep 3072653 = 1152245) (by norm_num)
theorem B2048669 : Blo 1364501 2048669 := bbase (se 3 (by rfl) ⟨384125, by rfl⟩ : syracuseStep 2048669 = 768251) (by norm_num)
theorem B5186213 : Blo 1364501 5186213 := bbase (se 4 (by rfl) ⟨486207, by rfl⟩ : syracuseStep 5186213 = 972415) (by norm_num)
theorem B5833397 : Blo 1364501 5833397 := bbase (se 5 (by rfl) ⟨273440, by rfl⟩ : syracuseStep 5833397 = 546881) (by norm_num)
theorem B2048693 : Blo 1364501 2048693 := bbase (se 5 (by rfl) ⟨96032, by rfl⟩ : syracuseStep 2048693 = 192065) (by norm_num)
theorem B2302661 : Blo 1364501 2302661 := bbase (se 4 (by rfl) ⟨215874, by rfl⟩ : syracuseStep 2302661 = 431749) (by norm_num)
theorem B2048717 : Blo 1364501 2048717 := bbase (se 3 (by rfl) ⟨384134, by rfl⟩ : syracuseStep 2048717 = 768269) (by norm_num)
theorem B3072725 : Blo 1364501 3072725 := bbase (se 7 (by rfl) ⟨36008, by rfl⟩ : syracuseStep 3072725 = 72017) (by norm_num)
theorem B2048741 : Blo 1364501 2048741 := bbase (se 4 (by rfl) ⟨192069, by rfl⟩ : syracuseStep 2048741 = 384139) (by norm_num)
theorem B2917109 : Blo 1364501 2917109 := bbase (se 5 (by rfl) ⟨136739, by rfl⟩ : syracuseStep 2917109 = 273479) (by norm_num)
theorem B2048765 : Blo 1364501 2048765 := bbase (se 3 (by rfl) ⟨384143, by rfl⟩ : syracuseStep 2048765 = 768287) (by norm_num)
theorem B1729289 : Blo 1364501 1729289 := bbase (se 2 (by rfl) ⟨648483, by rfl⟩ : syracuseStep 1729289 = 1296967) (by norm_num)
theorem B2048789 : Blo 1364501 2048789 := bbase (se 6 (by rfl) ⟨48018, by rfl⟩ : syracuseStep 2048789 = 96037) (by norm_num)
theorem B3072797 : Blo 1364501 3072797 := bbase (se 3 (by rfl) ⟨576149, by rfl⟩ : syracuseStep 3072797 = 1152299) (by norm_num)
theorem B1458977 : Blo 1364501 1458977 := bbase (se 2 (by rfl) ⟨547116, by rfl⟩ : syracuseStep 1458977 = 1094233) (by norm_num)
theorem B3457829 : Blo 1364501 3457829 := bbase (se 4 (by rfl) ⟨324171, by rfl⟩ : syracuseStep 3457829 = 648343) (by norm_num)
theorem B2048813 : Blo 1364501 2048813 := bbase (se 3 (by rfl) ⟨384152, by rfl⟩ : syracuseStep 2048813 = 768305) (by norm_num)
theorem B1729345 : Blo 1364501 1729345 := bbase (se 2 (by rfl) ⟨648504, by rfl⟩ : syracuseStep 1729345 = 1297009) (by norm_num)
theorem B2302789 : Blo 1364501 2302789 := bbase (se 4 (by rfl) ⟨215886, by rfl⟩ : syracuseStep 2302789 = 431773) (by norm_num)
theorem B2048837 : Blo 1364501 2048837 := bbase (se 4 (by rfl) ⟨192078, by rfl⟩ : syracuseStep 2048837 = 384157) (by norm_num)
theorem B2048861 : Blo 1364501 2048861 := bbase (se 3 (by rfl) ⟨384161, by rfl⟩ : syracuseStep 2048861 = 768323) (by norm_num)
theorem B3072869 : Blo 1364501 3072869 := bbase (se 4 (by rfl) ⟨288081, by rfl⟩ : syracuseStep 3072869 = 576163) (by norm_num)
theorem B2048885 : Blo 1364501 2048885 := bbase (se 5 (by rfl) ⟨96041, by rfl⟩ : syracuseStep 2048885 = 192083) (by norm_num)
theorem B2917253 : Blo 1364501 2917253 := bbase (se 4 (by rfl) ⟨273492, by rfl⟩ : syracuseStep 2917253 = 546985) (by norm_num)
theorem B2048909 : Blo 1364501 2048909 := bbase (se 3 (by rfl) ⟨384170, by rfl⟩ : syracuseStep 2048909 = 768341) (by norm_num)
theorem B2302877 : Blo 1364501 2302877 := bbase (se 3 (by rfl) ⟨431789, by rfl⟩ : syracuseStep 2302877 = 863579) (by norm_num)
theorem B1729441 : Blo 1364501 1729441 := bbase (se 2 (by rfl) ⟨648540, by rfl⟩ : syracuseStep 1729441 = 1297081) (by norm_num)
theorem B2048933 : Blo 1364501 2048933 := bbase (se 4 (by rfl) ⟨192087, by rfl⟩ : syracuseStep 2048933 = 384175) (by norm_num)
theorem B3072941 : Blo 1364501 3072941 := bbase (se 3 (by rfl) ⟨576176, by rfl⟩ : syracuseStep 3072941 = 1152353) (by norm_num)
theorem B2048957 : Blo 1364501 2048957 := bbase (se 3 (by rfl) ⟨384179, by rfl⟩ : syracuseStep 2048957 = 768359) (by norm_num)
theorem B5186501 : Blo 1364501 5186501 := bbase (se 4 (by rfl) ⟨486234, by rfl⟩ : syracuseStep 5186501 = 972469) (by norm_num)
theorem B2048981 : Blo 1364501 2048981 := bbase (se 7 (by rfl) ⟨24011, by rfl⟩ : syracuseStep 2048981 = 48023) (by norm_num)
theorem B3113957 : Blo 1364501 3113957 := bbase (se 4 (by rfl) ⟨291933, by rfl⟩ : syracuseStep 3113957 = 583867) (by norm_num)
theorem B2049005 : Blo 1364501 2049005 := bbase (se 3 (by rfl) ⟨384188, by rfl⟩ : syracuseStep 2049005 = 768377) (by norm_num)
theorem B3073013 : Blo 1364501 3073013 := bbase (se 5 (by rfl) ⟨144047, by rfl⟩ : syracuseStep 3073013 = 288095) (by norm_num)
theorem B2049029 : Blo 1364501 2049029 := bbase (se 4 (by rfl) ⟨192096, by rfl⟩ : syracuseStep 2049029 = 384193) (by norm_num)
theorem B1459225 : Blo 1364501 1459225 := bbase (se 2 (by rfl) ⟨547209, by rfl⟩ : syracuseStep 1459225 = 1094419) (by norm_num)
theorem B2303005 : Blo 1364501 2303005 := bbase (se 3 (by rfl) ⟨431813, by rfl⟩ : syracuseStep 2303005 = 863627) (by norm_num)
theorem B2049053 : Blo 1364501 2049053 := bbase (se 3 (by rfl) ⟨384197, by rfl⟩ : syracuseStep 2049053 = 768395) (by norm_num)
theorem B2049077 : Blo 1364501 2049077 := bbase (se 5 (by rfl) ⟨96050, by rfl⟩ : syracuseStep 2049077 = 192101) (by norm_num)
theorem B3073085 : Blo 1364501 3073085 := bbase (se 3 (by rfl) ⟨576203, by rfl⟩ : syracuseStep 3073085 = 1152407) (by norm_num)
theorem B2049101 : Blo 1364501 2049101 := bbase (se 3 (by rfl) ⟨384206, by rfl⟩ : syracuseStep 2049101 = 768413) (by norm_num)
theorem B2049125 : Blo 1364501 2049125 := bbase (se 4 (by rfl) ⟨192105, by rfl⟩ : syracuseStep 2049125 = 384211) (by norm_num)
theorem B2303093 : Blo 1364501 2303093 := bbase (se 5 (by rfl) ⟨107957, by rfl⟩ : syracuseStep 2303093 = 215915) (by norm_num)
theorem B9847925 : Blo 1364501 9847925 := bbase (se 5 (by rfl) ⟨461621, by rfl⟩ : syracuseStep 9847925 = 923243) (by norm_num)
theorem B2049149 : Blo 1364501 2049149 := bbase (se 3 (by rfl) ⟨384215, by rfl⟩ : syracuseStep 2049149 = 768431) (by norm_num)
theorem B3458173 : Blo 1364501 3458173 := bbase (se 3 (by rfl) ⟨648407, by rfl⟩ : syracuseStep 3458173 = 1296815) (by norm_num)
theorem B3073157 : Blo 1364501 3073157 := bbase (se 4 (by rfl) ⟨288108, by rfl⟩ : syracuseStep 3073157 = 576217) (by norm_num)
theorem B2049173 : Blo 1364501 2049173 := bbase (se 6 (by rfl) ⟨48027, by rfl⟩ : syracuseStep 2049173 = 96055) (by norm_num)
theorem B2188453 : Blo 1364501 2188453 := bbase (se 4 (by rfl) ⟨205167, by rfl⟩ : syracuseStep 2188453 = 410335) (by norm_num)
theorem B2049197 : Blo 1364501 2049197 := bbase (se 3 (by rfl) ⟨384224, by rfl⟩ : syracuseStep 2049197 = 768449) (by norm_num)
theorem B2049221 : Blo 1364501 2049221 := bbase (se 4 (by rfl) ⟨192114, by rfl⟩ : syracuseStep 2049221 = 384229) (by norm_num)
theorem B3073229 : Blo 1364501 3073229 := bbase (se 3 (by rfl) ⟨576230, by rfl⟩ : syracuseStep 3073229 = 1152461) (by norm_num)
theorem B2049245 : Blo 1364501 2049245 := bbase (se 3 (by rfl) ⟨384233, by rfl⟩ : syracuseStep 2049245 = 768467) (by norm_num)
theorem B2917613 : Blo 1364501 2917613 := bbase (se 3 (by rfl) ⟨547052, by rfl⟩ : syracuseStep 2917613 = 1094105) (by norm_num)
theorem B3458285 : Blo 1364501 3458285 := bbase (se 3 (by rfl) ⟨648428, by rfl⟩ : syracuseStep 3458285 = 1296857) (by norm_num)
theorem B2303221 : Blo 1364501 2303221 := bbase (se 5 (by rfl) ⟨107963, by rfl⟩ : syracuseStep 2303221 = 215927) (by norm_num)
theorem B2049269 : Blo 1364501 2049269 := bbase (se 5 (by rfl) ⟨96059, by rfl⟩ : syracuseStep 2049269 = 192119) (by norm_num)
theorem B2188549 : Blo 1364501 2188549 := bbase (se 4 (by rfl) ⟨205176, by rfl⟩ : syracuseStep 2188549 = 410353) (by norm_num)
theorem B2049293 : Blo 1364501 2049293 := bbase (se 3 (by rfl) ⟨384242, by rfl⟩ : syracuseStep 2049293 = 768485) (by norm_num)
theorem B3073301 : Blo 1364501 3073301 := bbase (se 6 (by rfl) ⟨72030, by rfl⟩ : syracuseStep 3073301 = 144061) (by norm_num)
theorem B2049317 : Blo 1364501 2049317 := bbase (se 4 (by rfl) ⟨192123, by rfl⟩ : syracuseStep 2049317 = 384247) (by norm_num)
theorem B2458925 : Blo 1364501 2458925 := bbase (se 3 (by rfl) ⟨461048, by rfl⟩ : syracuseStep 2458925 = 922097) (by norm_num)
theorem B2049341 : Blo 1364501 2049341 := bbase (se 3 (by rfl) ⟨384251, by rfl⟩ : syracuseStep 2049341 = 768503) (by norm_num)
theorem B1402181 : Blo 1364501 1402181 := bbase (se 4 (by rfl) ⟨131454, by rfl⟩ : syracuseStep 1402181 = 262909) (by norm_num)
theorem B2303309 : Blo 1364501 2303309 := bbase (se 3 (by rfl) ⟨431870, by rfl⟩ : syracuseStep 2303309 = 863741) (by norm_num)
theorem B2049365 : Blo 1364501 2049365 := bbase (se 12 (by rfl) ⟨750, by rfl⟩ : syracuseStep 2049365 = 1501) (by norm_num)
theorem B3073373 : Blo 1364501 3073373 := bbase (se 3 (by rfl) ⟨576257, by rfl⟩ : syracuseStep 3073373 = 1152515) (by norm_num)
theorem B2049389 : Blo 1364501 2049389 := bbase (se 3 (by rfl) ⟨384260, by rfl⟩ : syracuseStep 2049389 = 768521) (by norm_num)
theorem B2049413 : Blo 1364501 2049413 := bbase (se 4 (by rfl) ⟨192132, by rfl⟩ : syracuseStep 2049413 = 384265) (by norm_num)
theorem B2049437 : Blo 1364501 2049437 := bbase (se 3 (by rfl) ⟨384269, by rfl⟩ : syracuseStep 2049437 = 768539) (by norm_num)
theorem B3073445 : Blo 1364501 3073445 := bbase (se 4 (by rfl) ⟨288135, by rfl⟩ : syracuseStep 3073445 = 576271) (by norm_num)
theorem B2188709 : Blo 1364501 2188709 := bbase (se 4 (by rfl) ⟨205191, by rfl⟩ : syracuseStep 2188709 = 410383) (by norm_num)
theorem B3458477 : Blo 1364501 3458477 := bbase (se 3 (by rfl) ⟨648464, by rfl⟩ : syracuseStep 3458477 = 1296929) (by norm_num)
theorem B2049461 : Blo 1364501 2049461 := bbase (se 5 (by rfl) ⟨96068, by rfl⟩ : syracuseStep 2049461 = 192137) (by norm_num)
theorem B2303437 : Blo 1364501 2303437 := bbase (se 3 (by rfl) ⟨431894, by rfl⟩ : syracuseStep 2303437 = 863789) (by norm_num)
theorem B2049485 : Blo 1364501 2049485 := bbase (se 3 (by rfl) ⟨384278, by rfl⟩ : syracuseStep 2049485 = 768557) (by norm_num)
theorem B2336213 : Blo 1364501 2336213 := bbase (se 7 (by rfl) ⟨27377, by rfl⟩ : syracuseStep 2336213 = 54755) (by norm_num)
theorem B2049509 : Blo 1364501 2049509 := bbase (se 4 (by rfl) ⟨192141, by rfl⟩ : syracuseStep 2049509 = 384283) (by norm_num)
theorem B3073517 : Blo 1364501 3073517 := bbase (se 3 (by rfl) ⟨576284, by rfl⟩ : syracuseStep 3073517 = 1152569) (by norm_num)
theorem B2049533 : Blo 1364501 2049533 := bbase (se 3 (by rfl) ⟨384287, by rfl⟩ : syracuseStep 2049533 = 768575) (by norm_num)
theorem B2049557 : Blo 1364501 2049557 := bbase (se 6 (by rfl) ⟨48036, by rfl⟩ : syracuseStep 2049557 = 96073) (by norm_num)
theorem B2303525 : Blo 1364501 2303525 := bbase (se 4 (by rfl) ⟨215955, by rfl⟩ : syracuseStep 2303525 = 431911) (by norm_num)
theorem B3114541 : Blo 1364501 3114541 := bbase (se 3 (by rfl) ⟨583976, by rfl⟩ : syracuseStep 3114541 = 1167953) (by norm_num)
theorem B2049581 : Blo 1364501 2049581 := bbase (se 3 (by rfl) ⟨384296, by rfl⟩ : syracuseStep 2049581 = 768593) (by norm_num)
theorem B3073589 : Blo 1364501 3073589 := bbase (se 5 (by rfl) ⟨144074, by rfl⟩ : syracuseStep 3073589 = 288149) (by norm_num)
theorem B4154933 : Blo 1364501 4154933 := bbase (se 5 (by rfl) ⟨194762, by rfl⟩ : syracuseStep 4154933 = 389525) (by norm_num)
theorem B2049605 : Blo 1364501 2049605 := bbase (se 4 (by rfl) ⟨192150, by rfl⟩ : syracuseStep 2049605 = 384301) (by norm_num)
theorem B2049629 : Blo 1364501 2049629 := bbase (se 3 (by rfl) ⟨384305, by rfl⟩ : syracuseStep 2049629 = 768611) (by norm_num)
theorem B2336357 : Blo 1364501 2336357 := bbase (se 4 (by rfl) ⟨219033, by rfl⟩ : syracuseStep 2336357 = 438067) (by norm_num)
theorem B2049653 : Blo 1364501 2049653 := bbase (se 5 (by rfl) ⟨96077, by rfl⟩ : syracuseStep 2049653 = 192155) (by norm_num)
theorem B3073661 : Blo 1364501 3073661 := bbase (se 3 (by rfl) ⟨576311, by rfl⟩ : syracuseStep 3073661 = 1152623) (by norm_num)
theorem B2049677 : Blo 1364501 2049677 := bbase (se 3 (by rfl) ⟨384314, by rfl⟩ : syracuseStep 2049677 = 768629) (by norm_num)
theorem B4605605 : Blo 1364501 4605605 := bbase (se 4 (by rfl) ⟨431775, by rfl⟩ : syracuseStep 4605605 = 863551) (by norm_num)
theorem B2303653 : Blo 1364501 2303653 := bbase (se 4 (by rfl) ⟨215967, by rfl⟩ : syracuseStep 2303653 = 431935) (by norm_num)
theorem B2049701 : Blo 1364501 2049701 := bbase (se 4 (by rfl) ⟨192159, by rfl⟩ : syracuseStep 2049701 = 384319) (by norm_num)
theorem B2049725 : Blo 1364501 2049725 := bbase (se 3 (by rfl) ⟨384323, by rfl⟩ : syracuseStep 2049725 = 768647) (by norm_num)
theorem B3073733 : Blo 1364501 3073733 := bbase (se 4 (by rfl) ⟨288162, by rfl⟩ : syracuseStep 3073733 = 576325) (by norm_num)
theorem B2049749 : Blo 1364501 2049749 := bbase (se 7 (by rfl) ⟨24020, by rfl⟩ : syracuseStep 2049749 = 48041) (by norm_num)
theorem B2303741 : Blo 1364501 2303741 := bbase (se 3 (by rfl) ⟨431951, by rfl⟩ : syracuseStep 2303741 = 863903) (by norm_num)
theorem B3458821 : Blo 1364501 3458821 := bbase (se 4 (by rfl) ⟨324264, by rfl⟩ : syracuseStep 3458821 = 648529) (by norm_num)
theorem B1943309 : Blo 1364501 1943309 := bbase (se 3 (by rfl) ⟨364370, by rfl⟩ : syracuseStep 1943309 = 728741) (by norm_num)
theorem B3073805 : Blo 1364501 3073805 := bbase (se 3 (by rfl) ⟨576338, by rfl⟩ : syracuseStep 3073805 = 1152677) (by norm_num)
theorem B2590517 : Blo 1364501 2590517 := bbase (se 5 (by rfl) ⟨121430, by rfl⟩ : syracuseStep 2590517 = 242861) (by norm_num)
theorem B5539637 : Blo 1364501 5539637 := bbase (se 5 (by rfl) ⟨259670, by rfl⟩ : syracuseStep 5539637 = 519341) (by norm_num)
theorem B3073877 : Blo 1364501 3073877 := bbase (se 9 (by rfl) ⟨9005, by rfl⟩ : syracuseStep 3073877 = 18011) (by norm_num)
theorem B1943389 : Blo 1364501 1943389 := bbase (se 3 (by rfl) ⟨364385, by rfl⟩ : syracuseStep 1943389 = 728771) (by norm_num)
theorem B6915941 : Blo 1364501 6915941 := bbase (se 4 (by rfl) ⟨648369, by rfl⟩ : syracuseStep 6915941 = 1296739) (by norm_num)
theorem B3458933 : Blo 1364501 3458933 := bbase (se 5 (by rfl) ⟨162137, by rfl⟩ : syracuseStep 3458933 = 324275) (by norm_num)
theorem B2303869 : Blo 1364501 2303869 := bbase (se 3 (by rfl) ⟨431975, by rfl⟩ : syracuseStep 2303869 = 863951) (by norm_num)
theorem B3073949 : Blo 1364501 3073949 := bbase (se 3 (by rfl) ⟨576365, by rfl⟩ : syracuseStep 3073949 = 1152731) (by norm_num)
theorem B1943509 : Blo 1364501 1943509 := bbase (se 7 (by rfl) ⟨22775, by rfl⟩ : syracuseStep 1943509 = 45551) (by norm_num)
theorem B2303957 : Blo 1364501 2303957 := bbase (se 7 (by rfl) ⟨26999, by rfl⟩ : syracuseStep 2303957 = 53999) (by norm_num)
theorem B1640417 : Blo 1364501 1640417 := bbase (se 2 (by rfl) ⟨615156, by rfl⟩ : syracuseStep 1640417 = 1230313) (by norm_num)
theorem B3074021 : Blo 1364501 3074021 := bbase (se 4 (by rfl) ⟨288189, by rfl⟩ : syracuseStep 3074021 = 576379) (by norm_num)
theorem B6563861 : Blo 1364501 6563861 := bbase (se 6 (by rfl) ⟨153840, by rfl⟩ : syracuseStep 6563861 = 307681) (by norm_num)
theorem B4376597 : Blo 1364501 4376597 := bbase (se 6 (by rfl) ⟨102576, by rfl⟩ : syracuseStep 4376597 = 205153) (by norm_num)
theorem B3074093 : Blo 1364501 3074093 := bbase (se 3 (by rfl) ⟨576392, by rfl⟩ : syracuseStep 3074093 = 1152785) (by norm_num)
theorem B1943605 : Blo 1364501 1943605 := bbase (se 5 (by rfl) ⟨91106, by rfl⟩ : syracuseStep 1943605 = 182213) (by norm_num)
theorem B11667509 : Blo 1364501 11667509 := bbase (se 5 (by rfl) ⟨546914, by rfl⟩ : syracuseStep 11667509 = 1093829) (by norm_num)
theorem B2590805 : Blo 1364501 2590805 := bbase (se 8 (by rfl) ⟨15180, by rfl⟩ : syracuseStep 2590805 = 30361) (by norm_num)
theorem B4606037 : Blo 1364501 4606037 := bbase (se 8 (by rfl) ⟨26988, by rfl⟩ : syracuseStep 4606037 = 53977) (by norm_num)
theorem B2304085 : Blo 1364501 2304085 := bbase (se 8 (by rfl) ⟨13500, by rfl⟩ : syracuseStep 2304085 = 27001) (by norm_num)
theorem B5187685 : Blo 1364501 5187685 := bbase (se 4 (by rfl) ⟨486345, by rfl⟩ : syracuseStep 5187685 = 972691) (by norm_num)
theorem B9341045 : Blo 1364501 9341045 := bbase (se 5 (by rfl) ⟨437861, by rfl⟩ : syracuseStep 9341045 = 875723) (by norm_num)
theorem B3074165 : Blo 1364501 3074165 := bbase (se 5 (by rfl) ⟨144101, by rfl⟩ : syracuseStep 3074165 = 288203) (by norm_num)
theorem B2304173 : Blo 1364501 2304173 := bbase (se 3 (by rfl) ⟨432032, by rfl⟩ : syracuseStep 2304173 = 864065) (by norm_num)
theorem B3074237 : Blo 1364501 3074237 := bbase (se 3 (by rfl) ⟨576419, by rfl⟩ : syracuseStep 3074237 = 1152839) (by norm_num)
theorem B2590957 : Blo 1364501 2590957 := bbase (se 3 (by rfl) ⟨485804, by rfl⟩ : syracuseStep 2590957 = 971609) (by norm_num)
theorem B6908165 : Blo 1364501 6908165 := bbase (se 4 (by rfl) ⟨647640, by rfl⟩ : syracuseStep 6908165 = 1295281) (by norm_num)
theorem B3074309 : Blo 1364501 3074309 := bbase (se 4 (by rfl) ⟨288216, by rfl⟩ : syracuseStep 3074309 = 576433) (by norm_num)
theorem B2074901 : Blo 1364501 2074901 := bbase (se 6 (by rfl) ⟨48630, by rfl⟩ : syracuseStep 2074901 = 97261) (by norm_num)
theorem B3279133 : Blo 1364501 3279133 := bbase (se 3 (by rfl) ⟨614837, by rfl⟩ : syracuseStep 3279133 = 1229675) (by norm_num)
theorem B2304301 : Blo 1364501 2304301 := bbase (se 3 (by rfl) ⟨432056, by rfl⟩ : syracuseStep 2304301 = 864113) (by norm_num)
theorem B3074381 : Blo 1364501 3074381 := bbase (se 3 (by rfl) ⟨576446, by rfl⟩ : syracuseStep 3074381 = 1152893) (by norm_num)
theorem B2304389 : Blo 1364501 2304389 := bbase (se 4 (by rfl) ⟨216036, by rfl⟩ : syracuseStep 2304389 = 432073) (by norm_num)
theorem B1477001 : Blo 1364501 1477001 := bbase (se 2 (by rfl) ⟨553875, by rfl⟩ : syracuseStep 1477001 = 1107751) (by norm_num)
theorem B5187989 : Blo 1364501 5187989 := bbase (se 6 (by rfl) ⟨121593, by rfl⟩ : syracuseStep 5187989 = 243187) (by norm_num)
theorem B3074453 : Blo 1364501 3074453 := bbase (se 6 (by rfl) ⟨72057, by rfl⟩ : syracuseStep 3074453 = 144115) (by norm_num)
theorem B6228389 : Blo 1364501 6228389 := bbase (se 4 (by rfl) ⟨583911, by rfl⟩ : syracuseStep 6228389 = 1167823) (by norm_num)
theorem B1845685 : Blo 1364501 1845685 := bbase (se 5 (by rfl) ⟨86516, by rfl⟩ : syracuseStep 1845685 = 173033) (by norm_num)
theorem B3074525 : Blo 1364501 3074525 := bbase (se 3 (by rfl) ⟨576473, by rfl⟩ : syracuseStep 3074525 = 1152947) (by norm_num)
theorem B4606469 : Blo 1364501 4606469 := bbase (se 4 (by rfl) ⟨431856, by rfl⟩ : syracuseStep 4606469 = 863713) (by norm_num)
theorem B2304517 : Blo 1364501 2304517 := bbase (se 4 (by rfl) ⟨216048, by rfl⟩ : syracuseStep 2304517 = 432097) (by norm_num)
theorem B2591261 : Blo 1364501 2591261 := bbase (se 3 (by rfl) ⟨485861, by rfl⟩ : syracuseStep 2591261 = 971723) (by norm_num)
theorem B1944101 : Blo 1364501 1944101 := bbase (se 4 (by rfl) ⟨182259, by rfl⟩ : syracuseStep 1944101 = 364519) (by norm_num)
theorem B3074597 : Blo 1364501 3074597 := bbase (se 4 (by rfl) ⟨288243, by rfl⟩ : syracuseStep 3074597 = 576487) (by norm_num)
theorem B2304605 : Blo 1364501 2304605 := bbase (se 3 (by rfl) ⟨432113, by rfl⟩ : syracuseStep 2304605 = 864227) (by norm_num)
theorem B1641109 : Blo 1364501 1641109 := bbase (se 6 (by rfl) ⟨38463, by rfl⟩ : syracuseStep 1641109 = 76927) (by norm_num)
theorem B3115709 : Blo 1364501 3115709 := bbase (se 3 (by rfl) ⟨584195, by rfl⟩ : syracuseStep 3115709 = 1168391) (by norm_num)
theorem B2304733 : Blo 1364501 2304733 := bbase (se 3 (by rfl) ⟨432137, by rfl⟩ : syracuseStep 2304733 = 864275) (by norm_num)
theorem B1641205 : Blo 1364501 1641205 := bbase (se 5 (by rfl) ⟨76931, by rfl⟩ : syracuseStep 1641205 = 153863) (by norm_num)
theorem B2304821 : Blo 1364501 2304821 := bbase (se 5 (by rfl) ⟨108038, by rfl⟩ : syracuseStep 2304821 = 216077) (by norm_num)
theorem B4377509 : Blo 1364501 4377509 := bbase (se 4 (by rfl) ⟨410391, by rfl⟩ : syracuseStep 4377509 = 820783) (by norm_num)
theorem B4606901 : Blo 1364501 4606901 := bbase (se 5 (by rfl) ⟨215948, by rfl⟩ : syracuseStep 4606901 = 431897) (by norm_num)
theorem B3279797 : Blo 1364501 3279797 := bbase (se 5 (by rfl) ⟨153740, by rfl⟩ : syracuseStep 3279797 = 307481) (by norm_num)
theorem B2304949 : Blo 1364501 2304949 := bbase (se 5 (by rfl) ⟨108044, by rfl⟩ : syracuseStep 2304949 = 216089) (by norm_num)
theorem B2305037 : Blo 1364501 2305037 := bbase (se 3 (by rfl) ⟨432194, by rfl⟩ : syracuseStep 2305037 = 864389) (by norm_num)
theorem B1944653 : Blo 1364501 1944653 := bbase (se 3 (by rfl) ⟨364622, by rfl⟩ : syracuseStep 1944653 = 729245) (by norm_num)
theorem B8744021 : Blo 1364501 8744021 := bbase (se 8 (by rfl) ⟨51234, by rfl⟩ : syracuseStep 8744021 = 102469) (by norm_num)
theorem B1535089 : Blo 1364501 1535089 := bbase (se 2 (by rfl) ⟨575658, by rfl⟩ : syracuseStep 1535089 = 1151317) (by norm_num)
theorem B6917237 : Blo 1364501 6917237 := bbase (se 5 (by rfl) ⟨324245, by rfl⟩ : syracuseStep 6917237 = 648491) (by norm_num)
theorem B2305165 : Blo 1364501 2305165 := bbase (se 3 (by rfl) ⟨432218, by rfl⟩ : syracuseStep 2305165 = 864437) (by norm_num)
theorem B1535125 : Blo 1364501 1535125 := bbase (se 6 (by rfl) ⟨35979, by rfl⟩ : syracuseStep 1535125 = 71959) (by norm_num)
theorem B3599509 : Blo 1364501 3599509 := bbase (se 6 (by rfl) ⟨84363, by rfl⟩ : syracuseStep 3599509 = 168727) (by norm_num)
theorem B1477801 : Blo 1364501 1477801 := bbase (se 2 (by rfl) ⟨554175, by rfl⟩ : syracuseStep 1477801 = 1108351) (by norm_num)
theorem B1535161 : Blo 1364501 1535161 := bbase (se 2 (by rfl) ⟨575685, by rfl⟩ : syracuseStep 1535161 = 1151371) (by norm_num)
theorem B3280085 : Blo 1364501 3280085 := bbase (se 7 (by rfl) ⟨38438, by rfl⟩ : syracuseStep 3280085 = 76877) (by norm_num)
theorem B5328085 : Blo 1364501 5328085 := bbase (se 7 (by rfl) ⟨62438, by rfl⟩ : syracuseStep 5328085 = 124877) (by norm_num)
theorem B1535197 : Blo 1364501 1535197 := bbase (se 3 (by rfl) ⟨287849, by rfl⟩ : syracuseStep 1535197 = 575699) (by norm_num)
theorem B2305253 : Blo 1364501 2305253 := bbase (se 4 (by rfl) ⟨216117, by rfl⟩ : syracuseStep 2305253 = 432235) (by norm_num)
theorem B3689717 : Blo 1364501 3689717 := bbase (se 5 (by rfl) ⟨172955, by rfl⟩ : syracuseStep 3689717 = 345911) (by norm_num)
theorem B1535233 : Blo 1364501 1535233 := bbase (se 2 (by rfl) ⟨575712, by rfl⟩ : syracuseStep 1535233 = 1151425) (by norm_num)
theorem B2592013 : Blo 1364501 2592013 := bbase (se 3 (by rfl) ⟨486002, by rfl⟩ : syracuseStep 2592013 = 972005) (by norm_num)
theorem B1535269 : Blo 1364501 1535269 := bbase (se 4 (by rfl) ⟨143931, by rfl⟩ : syracuseStep 1535269 = 287863) (by norm_num)
theorem B1535305 : Blo 1364501 1535305 := bbase (se 2 (by rfl) ⟨575739, by rfl⟩ : syracuseStep 1535305 = 1151479) (by norm_num)
theorem B4607333 : Blo 1364501 4607333 := bbase (se 4 (by rfl) ⟨431937, by rfl⟩ : syracuseStep 4607333 = 863875) (by norm_num)
theorem B2305381 : Blo 1364501 2305381 := bbase (se 4 (by rfl) ⟨216129, by rfl⟩ : syracuseStep 2305381 = 432259) (by norm_num)
theorem B1535341 : Blo 1364501 1535341 := bbase (se 3 (by rfl) ⟨287876, by rfl⟩ : syracuseStep 1535341 = 575753) (by norm_num)
theorem B1535377 : Blo 1364501 1535377 := bbase (se 2 (by rfl) ⟨575766, by rfl⟩ : syracuseStep 1535377 = 1151533) (by norm_num)
theorem B2592157 : Blo 1364501 2592157 := bbase (se 3 (by rfl) ⟨486029, by rfl⟩ : syracuseStep 2592157 = 972059) (by norm_num)
theorem B1535413 : Blo 1364501 1535413 := bbase (se 5 (by rfl) ⟨71972, by rfl⟩ : syracuseStep 1535413 = 143945) (by norm_num)
theorem B2305469 : Blo 1364501 2305469 := bbase (se 3 (by rfl) ⟨432275, by rfl⟩ : syracuseStep 2305469 = 864551) (by norm_num)
theorem B1535449 : Blo 1364501 1535449 := bbase (se 2 (by rfl) ⟨575793, by rfl⟩ : syracuseStep 1535449 = 1151587) (by norm_num)
theorem B1535485 : Blo 1364501 1535485 := bbase (se 3 (by rfl) ⟨287903, by rfl⟩ : syracuseStep 1535485 = 575807) (by norm_num)
theorem B6909461 : Blo 1364501 6909461 := bbase (se 6 (by rfl) ⟨161940, by rfl⟩ : syracuseStep 6909461 = 323881) (by norm_num)
theorem B1535521 : Blo 1364501 1535521 := bbase (se 2 (by rfl) ⟨575820, by rfl⟩ : syracuseStep 1535521 = 1151641) (by norm_num)
theorem B13119029 : Blo 1364501 13119029 := bbase (se 5 (by rfl) ⟨614954, by rfl⟩ : syracuseStep 13119029 = 1229909) (by norm_num)
theorem B2592317 : Blo 1364501 2592317 := bbase (se 3 (by rfl) ⟨486059, by rfl⟩ : syracuseStep 2592317 = 972119) (by norm_num)
theorem B2305597 : Blo 1364501 2305597 := bbase (se 3 (by rfl) ⟨432299, by rfl⟩ : syracuseStep 2305597 = 864599) (by norm_num)
theorem B1535557 : Blo 1364501 1535557 := bbase (se 4 (by rfl) ⟨143958, by rfl⟩ : syracuseStep 1535557 = 287917) (by norm_num)
theorem B1535593 : Blo 1364501 1535593 := bbase (se 2 (by rfl) ⟨575847, by rfl⟩ : syracuseStep 1535593 = 1151695) (by norm_num)
theorem B1535629 : Blo 1364501 1535629 := bbase (se 3 (by rfl) ⟨287930, by rfl⟩ : syracuseStep 1535629 = 575861) (by norm_num)
theorem B2305685 : Blo 1364501 2305685 := bbase (se 6 (by rfl) ⟨54039, by rfl⟩ : syracuseStep 2305685 = 108079) (by norm_num)
theorem B1535665 : Blo 1364501 1535665 := bbase (se 2 (by rfl) ⟨575874, by rfl⟩ : syracuseStep 1535665 = 1151749) (by norm_num)
theorem B2592461 : Blo 1364501 2592461 := bbase (se 3 (by rfl) ⟨486086, by rfl⟩ : syracuseStep 2592461 = 972173) (by norm_num)
theorem B1535701 : Blo 1364501 1535701 := bbase (se 7 (by rfl) ⟨17996, by rfl⟩ : syracuseStep 1535701 = 35993) (by norm_num)
theorem B1535737 : Blo 1364501 1535737 := bbase (se 2 (by rfl) ⟨575901, by rfl⟩ : syracuseStep 1535737 = 1151803) (by norm_num)
theorem B4607765 : Blo 1364501 4607765 := bbase (se 6 (by rfl) ⟨107994, by rfl⟩ : syracuseStep 4607765 = 215989) (by norm_num)
theorem B2305813 : Blo 1364501 2305813 := bbase (se 6 (by rfl) ⟨54042, by rfl⟩ : syracuseStep 2305813 = 108085) (by norm_num)
theorem B1535773 : Blo 1364501 1535773 := bbase (se 3 (by rfl) ⟨287957, by rfl⟩ : syracuseStep 1535773 = 575915) (by norm_num)
theorem B1945405 : Blo 1364501 1945405 := bbase (se 3 (by rfl) ⟨364763, by rfl⟩ : syracuseStep 1945405 = 729527) (by norm_num)
theorem B1535809 : Blo 1364501 1535809 := bbase (se 2 (by rfl) ⟨575928, by rfl⟩ : syracuseStep 1535809 = 1151857) (by norm_num)
theorem B1535845 : Blo 1364501 1535845 := bbase (se 4 (by rfl) ⟨143985, by rfl⟩ : syracuseStep 1535845 = 287971) (by norm_num)
theorem B2461549 : Blo 1364501 2461549 := bbase (se 3 (by rfl) ⟨461540, by rfl⟩ : syracuseStep 2461549 = 923081) (by norm_num)
theorem B2305901 : Blo 1364501 2305901 := bbase (se 3 (by rfl) ⟨432356, by rfl⟩ : syracuseStep 2305901 = 864713) (by norm_num)
theorem B3501949 : Blo 1364501 3501949 := bbase (se 3 (by rfl) ⟨656615, by rfl⟩ : syracuseStep 3501949 = 1313231) (by norm_num)
theorem B1535881 : Blo 1364501 1535881 := bbase (se 2 (by rfl) ⟨575955, by rfl⟩ : syracuseStep 1535881 = 1151911) (by norm_num)
theorem B5836693 : Blo 1364501 5836693 := bbase (se 6 (by rfl) ⟨136797, by rfl⟩ : syracuseStep 5836693 = 273595) (by norm_num)
theorem B1535917 : Blo 1364501 1535917 := bbase (se 3 (by rfl) ⟨287984, by rfl⟩ : syracuseStep 1535917 = 575969) (by norm_num)
theorem B6074309 : Blo 1364501 6074309 := bbase (se 4 (by rfl) ⟨569466, by rfl⟩ : syracuseStep 6074309 = 1138933) (by norm_num)
theorem B1535953 : Blo 1364501 1535953 := bbase (se 2 (by rfl) ⟨575982, by rfl⟩ : syracuseStep 1535953 = 1151965) (by norm_num)
theorem B6557669 : Blo 1364501 6557669 := bbase (se 4 (by rfl) ⟨614781, by rfl⟩ : syracuseStep 6557669 = 1229563) (by norm_num)
theorem B2592749 : Blo 1364501 2592749 := bbase (se 3 (by rfl) ⟨486140, by rfl⟩ : syracuseStep 2592749 = 972281) (by norm_num)
theorem B1535989 : Blo 1364501 1535989 := bbase (se 5 (by rfl) ⟨71999, by rfl⟩ : syracuseStep 1535989 = 143999) (by norm_num)
theorem B2461693 : Blo 1364501 2461693 := bbase (se 3 (by rfl) ⟨461567, by rfl⟩ : syracuseStep 2461693 = 923135) (by norm_num)
theorem B1536025 : Blo 1364501 1536025 := bbase (se 2 (by rfl) ⟨576009, by rfl⟩ : syracuseStep 1536025 = 1152019) (by norm_num)
theorem B1536061 : Blo 1364501 1536061 := bbase (se 3 (by rfl) ⟨288011, by rfl⟩ : syracuseStep 1536061 = 576023) (by norm_num)
theorem B1536097 : Blo 1364501 1536097 := bbase (se 2 (by rfl) ⟨576036, by rfl⟩ : syracuseStep 1536097 = 1152073) (by norm_num)
theorem B7008373 : Blo 1364501 7008373 := bbase (se 5 (by rfl) ⟨328517, by rfl⟩ : syracuseStep 7008373 = 657035) (by norm_num)
theorem B1536133 : Blo 1364501 1536133 := bbase (se 4 (by rfl) ⟨144012, by rfl⟩ : syracuseStep 1536133 = 288025) (by norm_num)
theorem B2592901 : Blo 1364501 2592901 := bbase (se 4 (by rfl) ⟨243084, by rfl⟩ : syracuseStep 2592901 = 486169) (by norm_num)
theorem B1536169 : Blo 1364501 1536169 := bbase (se 2 (by rfl) ⟨576063, by rfl⟩ : syracuseStep 1536169 = 1152127) (by norm_num)
theorem B4608197 : Blo 1364501 4608197 := bbase (se 4 (by rfl) ⟨432018, by rfl⟩ : syracuseStep 4608197 = 864037) (by norm_num)
theorem B1536205 : Blo 1364501 1536205 := bbase (se 3 (by rfl) ⟨288038, by rfl⟩ : syracuseStep 1536205 = 576077) (by norm_num)
theorem B2461909 : Blo 1364501 2461909 := bbase (se 7 (by rfl) ⟨28850, by rfl⟩ : syracuseStep 2461909 = 57701) (by norm_num)
theorem B1536241 : Blo 1364501 1536241 := bbase (se 2 (by rfl) ⟨576090, by rfl⟩ : syracuseStep 1536241 = 1152181) (by norm_num)
theorem B1536277 : Blo 1364501 1536277 := bbase (se 6 (by rfl) ⟨36006, by rfl⟩ : syracuseStep 1536277 = 72013) (by norm_num)
theorem B1536313 : Blo 1364501 1536313 := bbase (se 2 (by rfl) ⟨576117, by rfl⟩ : syracuseStep 1536313 = 1152235) (by norm_num)
theorem B1536349 : Blo 1364501 1536349 := bbase (se 3 (by rfl) ⟨288065, by rfl⟩ : syracuseStep 1536349 = 576131) (by norm_num)
theorem B1536385 : Blo 1364501 1536385 := bbase (se 2 (by rfl) ⟨576144, by rfl⟩ : syracuseStep 1536385 = 1152289) (by norm_num)
theorem B1536421 : Blo 1364501 1536421 := bbase (se 4 (by rfl) ⟨144039, by rfl⟩ : syracuseStep 1536421 = 288079) (by norm_num)
theorem B2593205 : Blo 1364501 2593205 := bbase (se 5 (by rfl) ⟨121556, by rfl⟩ : syracuseStep 2593205 = 243113) (by norm_num)
theorem B1536457 : Blo 1364501 1536457 := bbase (se 2 (by rfl) ⟨576171, by rfl⟩ : syracuseStep 1536457 = 1152343) (by norm_num)
theorem B1536493 : Blo 1364501 1536493 := bbase (se 3 (by rfl) ⟨288092, by rfl⟩ : syracuseStep 1536493 = 576185) (by norm_num)
theorem B3887621 : Blo 1364501 3887621 := bbase (se 4 (by rfl) ⟨364464, by rfl⟩ : syracuseStep 3887621 = 728929) (by norm_num)
theorem B1536529 : Blo 1364501 1536529 := bbase (se 2 (by rfl) ⟨576198, by rfl⟩ : syracuseStep 1536529 = 1152397) (by norm_num)
theorem B1536565 : Blo 1364501 1536565 := bbase (se 5 (by rfl) ⟨72026, by rfl⟩ : syracuseStep 1536565 = 144053) (by norm_num)
theorem B1536601 : Blo 1364501 1536601 := bbase (se 2 (by rfl) ⟨576225, by rfl⟩ : syracuseStep 1536601 = 1152451) (by norm_num)
theorem B4608629 : Blo 1364501 4608629 := bbase (se 5 (by rfl) ⟨216029, by rfl⟩ : syracuseStep 4608629 = 432059) (by norm_num)
theorem B1536637 : Blo 1364501 1536637 := bbase (se 3 (by rfl) ⟨288119, by rfl⟩ : syracuseStep 1536637 = 576239) (by norm_num)
theorem B1536673 : Blo 1364501 1536673 := bbase (se 2 (by rfl) ⟨576252, by rfl⟩ : syracuseStep 1536673 = 1152505) (by norm_num)
theorem B1536709 : Blo 1364501 1536709 := bbase (se 4 (by rfl) ⟨144066, by rfl⟩ : syracuseStep 1536709 = 288133) (by norm_num)
theorem B1536745 : Blo 1364501 1536745 := bbase (se 2 (by rfl) ⟨576279, by rfl⟩ : syracuseStep 1536745 = 1152559) (by norm_num)
theorem B1536781 : Blo 1364501 1536781 := bbase (se 3 (by rfl) ⟨288146, by rfl⟩ : syracuseStep 1536781 = 576293) (by norm_num)
theorem B6910757 : Blo 1364501 6910757 := bbase (se 4 (by rfl) ⟨647883, by rfl⟩ : syracuseStep 6910757 = 1295767) (by norm_num)
theorem B1536817 : Blo 1364501 1536817 := bbase (se 2 (by rfl) ⟨576306, by rfl⟩ : syracuseStep 1536817 = 1152613) (by norm_num)
theorem B1536853 : Blo 1364501 1536853 := bbase (se 9 (by rfl) ⟨4502, by rfl⟩ : syracuseStep 1536853 = 9005) (by norm_num)
theorem B5182325 : Blo 1364501 5182325 := bbase (se 5 (by rfl) ⟨242921, by rfl⟩ : syracuseStep 5182325 = 485843) (by norm_num)
theorem B1536889 : Blo 1364501 1536889 := bbase (se 2 (by rfl) ⟨576333, by rfl⟩ : syracuseStep 1536889 = 1152667) (by norm_num)
theorem B16610197 : Blo 1364501 16610197 := bbase (se 6 (by rfl) ⟨389301, by rfl⟩ : syracuseStep 16610197 = 778603) (by norm_num)
theorem B1536925 : Blo 1364501 1536925 := bbase (se 3 (by rfl) ⟨288173, by rfl⟩ : syracuseStep 1536925 = 576347) (by norm_num)
theorem B1536961 : Blo 1364501 1536961 := bbase (se 2 (by rfl) ⟨576360, by rfl⟩ : syracuseStep 1536961 = 1152721) (by norm_num)
theorem B2077661 : Blo 1364501 2077661 := bbase (se 3 (by rfl) ⟨389561, by rfl⟩ : syracuseStep 2077661 = 779123) (by norm_num)
theorem B1684453 : Blo 1364501 1684453 := bbase (se 4 (by rfl) ⟨157917, by rfl⟩ : syracuseStep 1684453 = 315835) (by norm_num)
theorem B1536997 : Blo 1364501 1536997 := bbase (se 4 (by rfl) ⟨144093, by rfl⟩ : syracuseStep 1536997 = 288187) (by norm_num)
theorem B3453941 : Blo 1364501 3453941 := bbase (se 5 (by rfl) ⟨161903, by rfl⟩ : syracuseStep 3453941 = 323807) (by norm_num)
theorem B1537033 : Blo 1364501 1537033 := bbase (se 2 (by rfl) ⟨576387, by rfl⟩ : syracuseStep 1537033 = 1152775) (by norm_num)
theorem B4609061 : Blo 1364501 4609061 := bbase (se 4 (by rfl) ⟨432099, by rfl⟩ : syracuseStep 4609061 = 864199) (by norm_num)
theorem B1537069 : Blo 1364501 1537069 := bbase (se 3 (by rfl) ⟨288200, by rfl⟩ : syracuseStep 1537069 = 576401) (by norm_num)
theorem B1537105 : Blo 1364501 1537105 := bbase (se 2 (by rfl) ⟨576414, by rfl⟩ : syracuseStep 1537105 = 1152829) (by norm_num)
theorem B5534837 : Blo 1364501 5534837 := bbase (se 5 (by rfl) ⟨259445, by rfl⟩ : syracuseStep 5534837 = 518891) (by norm_num)
theorem B1537141 : Blo 1364501 1537141 := bbase (se 5 (by rfl) ⟨72053, by rfl⟩ : syracuseStep 1537141 = 144107) (by norm_num)
theorem B5182613 : Blo 1364501 5182613 := bbase (se 6 (by rfl) ⟨121467, by rfl⟩ : syracuseStep 5182613 = 242935) (by norm_num)
theorem B1537177 : Blo 1364501 1537177 := bbase (se 2 (by rfl) ⟨576441, by rfl⟩ : syracuseStep 1537177 = 1152883) (by norm_num)
theorem B2593957 : Blo 1364501 2593957 := bbase (se 4 (by rfl) ⟨243183, by rfl⟩ : syracuseStep 2593957 = 486367) (by norm_num)
theorem B1537213 : Blo 1364501 1537213 := bbase (se 3 (by rfl) ⟨288227, by rfl⟩ : syracuseStep 1537213 = 576455) (by norm_num)
theorem B3282133 : Blo 1364501 3282133 := bbase (se 7 (by rfl) ⟨38462, by rfl⟩ : syracuseStep 3282133 = 76925) (by norm_num)
theorem B1537249 : Blo 1364501 1537249 := bbase (se 2 (by rfl) ⟨576468, by rfl⟩ : syracuseStep 1537249 = 1152937) (by norm_num)
theorem B1537285 : Blo 1364501 1537285 := bbase (se 4 (by rfl) ⟨144120, by rfl⟩ : syracuseStep 1537285 = 288241) (by norm_num)
theorem B19674389 : Blo 1364501 19674389 := bbase (se 6 (by rfl) ⟨461118, by rfl⟩ : syracuseStep 19674389 = 922237) (by norm_num)
theorem B2594101 : Blo 1364501 2594101 := bbase (se 5 (by rfl) ⟨121598, by rfl⟩ : syracuseStep 2594101 = 243197) (by norm_num)
theorem B3454285 : Blo 1364501 3454285 := bbase (se 3 (by rfl) ⟨647678, by rfl⟩ : syracuseStep 3454285 = 1295357) (by norm_num)
theorem B3454397 : Blo 1364501 3454397 := bbase (se 3 (by rfl) ⟨647699, by rfl⟩ : syracuseStep 3454397 = 1295399) (by norm_num)
theorem B4609493 : Blo 1364501 4609493 := bbase (se 7 (by rfl) ⟨54017, by rfl⟩ : syracuseStep 4609493 = 108035) (by norm_num)
theorem B7779797 : Blo 1364501 7779797 := bbase (se 7 (by rfl) ⟨91169, by rfl⟩ : syracuseStep 7779797 = 182339) (by norm_num)
theorem B7771733 : Blo 1364501 7771733 := bbase (se 8 (by rfl) ⟨45537, by rfl⟩ : syracuseStep 7771733 = 91075) (by norm_num)
theorem B3454589 : Blo 1364501 3454589 := bbase (se 3 (by rfl) ⟨647735, by rfl⟩ : syracuseStep 3454589 = 1295471) (by norm_num)
theorem B5060245 : Blo 1364501 5060245 := bbase (se 6 (by rfl) ⟨118599, by rfl⟩ : syracuseStep 5060245 = 237199) (by norm_num)
theorem B3888805 : Blo 1364501 3888805 := bbase (se 4 (by rfl) ⟨364575, by rfl⟩ : syracuseStep 3888805 = 729151) (by norm_num)
theorem B7100117 : Blo 1364501 7100117 := bbase (se 7 (by rfl) ⟨83204, by rfl⟩ : syracuseStep 7100117 = 166409) (by norm_num)
theorem B3888965 : Blo 1364501 3888965 := bbase (se 4 (by rfl) ⟨364590, by rfl⟩ : syracuseStep 3888965 = 729181) (by norm_num)
theorem B4609925 : Blo 1364501 4609925 := bbase (se 4 (by rfl) ⟨432180, by rfl⟩ : syracuseStep 4609925 = 864361) (by norm_num)
theorem B4151189 : Blo 1364501 4151189 := bbase (se 6 (by rfl) ⟨97293, by rfl⟩ : syracuseStep 4151189 = 194587) (by norm_num)
theorem B3454933 : Blo 1364501 3454933 := bbase (se 7 (by rfl) ⟨40487, by rfl⟩ : syracuseStep 3454933 = 80975) (by norm_num)
theorem B2807765 : Blo 1364501 2807765 := bbase (se 7 (by rfl) ⟨32903, by rfl⟩ : syracuseStep 2807765 = 65807) (by norm_num)
theorem B4151333 : Blo 1364501 4151333 := bbase (se 4 (by rfl) ⟨389187, by rfl⟩ : syracuseStep 4151333 = 778375) (by norm_num)
theorem B6912053 : Blo 1364501 6912053 := bbase (se 5 (by rfl) ⟨324002, by rfl⟩ : syracuseStep 6912053 = 648005) (by norm_num)
theorem B3889205 : Blo 1364501 3889205 := bbase (se 5 (by rfl) ⟨182306, by rfl⟩ : syracuseStep 3889205 = 364613) (by norm_num)
theorem B3455045 : Blo 1364501 3455045 := bbase (se 4 (by rfl) ⟨323910, by rfl⟩ : syracuseStep 3455045 = 647821) (by norm_num)
theorem B6559861 : Blo 1364501 6559861 := bbase (se 5 (by rfl) ⟨307493, by rfl⟩ : syracuseStep 6559861 = 614987) (by norm_num)
theorem B2627749 : Blo 1364501 2627749 := bbase (se 4 (by rfl) ⟨246351, by rfl⟩ : syracuseStep 2627749 = 492703) (by norm_num)
theorem B3070133 : Blo 1364501 3070133 := bbase (se 5 (by rfl) ⟨143912, by rfl⟩ : syracuseStep 3070133 = 287825) (by norm_num)
theorem B4987109 : Blo 1364501 4987109 := bbase (se 4 (by rfl) ⟨467541, by rfl⟩ : syracuseStep 4987109 = 935083) (by norm_num)
theorem B3889397 : Blo 1364501 3889397 := bbase (se 5 (by rfl) ⟨182315, by rfl⟩ : syracuseStep 3889397 = 364631) (by norm_num)
theorem B3070205 : Blo 1364501 3070205 := bbase (se 3 (by rfl) ⟨575663, by rfl⟩ : syracuseStep 3070205 = 1151327) (by norm_num)
theorem B3455237 : Blo 1364501 3455237 := bbase (se 4 (by rfl) ⟨323928, by rfl⟩ : syracuseStep 3455237 = 647857) (by norm_num)
theorem B5183797 : Blo 1364501 5183797 := bbase (se 5 (by rfl) ⟨242990, by rfl⟩ : syracuseStep 5183797 = 485981) (by norm_num)
theorem B4610357 : Blo 1364501 4610357 := bbase (se 5 (by rfl) ⟨216110, by rfl⟩ : syracuseStep 4610357 = 432221) (by norm_num)
theorem B3070277 : Blo 1364501 3070277 := bbase (se 4 (by rfl) ⟨287838, by rfl⟩ : syracuseStep 3070277 = 575677) (by norm_num)
theorem B4372805 : Blo 1364501 4372805 := bbase (se 4 (by rfl) ⟨409950, by rfl⟩ : syracuseStep 4372805 = 819901) (by norm_num)
theorem B17733973 : Blo 1364501 17733973 := bbase (se 10 (by rfl) ⟨25977, by rfl⟩ : syracuseStep 17733973 = 51955) (by norm_num)
theorem B3070349 : Blo 1364501 3070349 := bbase (se 3 (by rfl) ⟨575690, by rfl⟩ : syracuseStep 3070349 = 1151381) (by norm_num)
theorem B2914717 : Blo 1364501 2914717 := bbase (se 3 (by rfl) ⟨546509, by rfl⟩ : syracuseStep 2914717 = 1093019) (by norm_num)
theorem B2185685 : Blo 1364501 2185685 := bbase (se 7 (by rfl) ⟨25613, by rfl⟩ : syracuseStep 2185685 = 51227) (by norm_num)
theorem B3070421 : Blo 1364501 3070421 := bbase (se 7 (by rfl) ⟨35981, by rfl⟩ : syracuseStep 3070421 = 71963) (by norm_num)
theorem B6224357 : Blo 1364501 6224357 := bbase (se 4 (by rfl) ⟨583533, by rfl⟩ : syracuseStep 6224357 = 1167067) (by norm_num)
theorem B5536277 : Blo 1364501 5536277 := bbase (se 6 (by rfl) ⟨129756, by rfl⟩ : syracuseStep 5536277 = 259513) (by norm_num)
theorem B3070493 : Blo 1364501 3070493 := bbase (se 3 (by rfl) ⟨575717, by rfl⟩ : syracuseStep 3070493 = 1151435) (by norm_num)
theorem B4151845 : Blo 1364501 4151845 := bbase (se 4 (by rfl) ⟨389235, by rfl⟩ : syracuseStep 4151845 = 778471) (by norm_num)
theorem B1727021 : Blo 1364501 1727021 := bbase (se 3 (by rfl) ⟨323816, by rfl⟩ : syracuseStep 1727021 = 647633) (by norm_num)
theorem B2914861 : Blo 1364501 2914861 := bbase (se 3 (by rfl) ⟨546536, by rfl⟩ : syracuseStep 2914861 = 1093073) (by norm_num)
theorem B2185813 : Blo 1364501 2185813 := bbase (se 8 (by rfl) ⟨12807, by rfl⟩ : syracuseStep 2185813 = 25615) (by norm_num)
theorem B3455581 : Blo 1364501 3455581 := bbase (se 3 (by rfl) ⟨647921, by rfl⟩ : syracuseStep 3455581 = 1295843) (by norm_num)
theorem B1727077 : Blo 1364501 1727077 := bbase (se 4 (by rfl) ⟨161913, by rfl⟩ : syracuseStep 1727077 = 323827) (by norm_num)
theorem B3070565 : Blo 1364501 3070565 := bbase (se 4 (by rfl) ⟨287865, by rfl⟩ : syracuseStep 3070565 = 575731) (by norm_num)
theorem B5184101 : Blo 1364501 5184101 := bbase (se 4 (by rfl) ⟨486009, by rfl⟩ : syracuseStep 5184101 = 972019) (by norm_num)
theorem B7780981 : Blo 1364501 7780981 := bbase (se 5 (by rfl) ⟨364733, by rfl⟩ : syracuseStep 7780981 = 729467) (by norm_num)
theorem B3070637 : Blo 1364501 3070637 := bbase (se 3 (by rfl) ⟨575744, by rfl⟩ : syracuseStep 3070637 = 1151489) (by norm_num)
theorem B1727173 : Blo 1364501 1727173 := bbase (se 4 (by rfl) ⟨161922, by rfl⟩ : syracuseStep 1727173 = 323845) (by norm_num)
theorem B3455693 : Blo 1364501 3455693 := bbase (se 3 (by rfl) ⟨647942, by rfl⟩ : syracuseStep 3455693 = 1295885) (by norm_num)
theorem B4610789 : Blo 1364501 4610789 := bbase (se 4 (by rfl) ⟨432261, by rfl⟩ : syracuseStep 4610789 = 864523) (by norm_num)
theorem B1776361 : Blo 1364501 1776361 := bbase (se 2 (by rfl) ⟨666135, by rfl⟩ : syracuseStep 1776361 = 1332271) (by norm_num)
theorem B3070709 : Blo 1364501 3070709 := bbase (se 5 (by rfl) ⟨143939, by rfl⟩ : syracuseStep 3070709 = 287879) (by norm_num)
theorem B10369781 : Blo 1364501 10369781 := bbase (se 5 (by rfl) ⟨486083, by rfl⟩ : syracuseStep 10369781 = 972167) (by norm_num)
theorem B2767621 : Blo 1364501 2767621 := bbase (se 4 (by rfl) ⟨259464, by rfl⟩ : syracuseStep 2767621 = 518929) (by norm_num)
theorem B4922117 : Blo 1364501 4922117 := bbase (se 4 (by rfl) ⟨461448, by rfl⟩ : syracuseStep 4922117 = 922897) (by norm_num)
theorem B2046773 : Blo 1364501 2046773 := bbase (se 5 (by rfl) ⟨95942, by rfl⟩ : syracuseStep 2046773 = 191885) (by norm_num)
theorem B3070781 : Blo 1364501 3070781 := bbase (se 3 (by rfl) ⟨575771, by rfl⟩ : syracuseStep 3070781 = 1151543) (by norm_num)
theorem B2046797 : Blo 1364501 2046797 := bbase (se 3 (by rfl) ⟨383774, by rfl⟩ : syracuseStep 2046797 = 767549) (by norm_num)
theorem B1686353 : Blo 1364501 1686353 := bbase (se 2 (by rfl) ⟨632382, by rfl⟩ : syracuseStep 1686353 = 1264765) (by norm_num)
theorem B2046821 : Blo 1364501 2046821 := bbase (se 4 (by rfl) ⟨191889, by rfl⟩ : syracuseStep 2046821 = 383779) (by norm_num)
theorem B1727345 : Blo 1364501 1727345 := bbase (se 2 (by rfl) ⟨647754, by rfl⟩ : syracuseStep 1727345 = 1295509) (by norm_num)
theorem B2046845 : Blo 1364501 2046845 := bbase (se 3 (by rfl) ⟨383783, by rfl⟩ : syracuseStep 2046845 = 767567) (by norm_num)
theorem B3070853 : Blo 1364501 3070853 := bbase (se 4 (by rfl) ⟨287892, by rfl⟩ : syracuseStep 3070853 = 575785) (by norm_num)
theorem B3455885 : Blo 1364501 3455885 := bbase (se 3 (by rfl) ⟨647978, by rfl⟩ : syracuseStep 3455885 = 1295957) (by norm_num)
theorem B2046869 : Blo 1364501 2046869 := bbase (se 6 (by rfl) ⟨47973, by rfl⟩ : syracuseStep 2046869 = 95947) (by norm_num)
theorem B2915237 : Blo 1364501 2915237 := bbase (se 4 (by rfl) ⟨273303, by rfl⟩ : syracuseStep 2915237 = 546607) (by norm_num)
theorem B1727401 : Blo 1364501 1727401 := bbase (se 2 (by rfl) ⟨647775, by rfl⟩ : syracuseStep 1727401 = 1295551) (by norm_num)
theorem B2046893 : Blo 1364501 2046893 := bbase (se 3 (by rfl) ⟨383792, by rfl⟩ : syracuseStep 2046893 = 767585) (by norm_num)
theorem B2046917 : Blo 1364501 2046917 := bbase (se 4 (by rfl) ⟨191898, by rfl⟩ : syracuseStep 2046917 = 383797) (by norm_num)
theorem B5831621 : Blo 1364501 5831621 := bbase (se 4 (by rfl) ⟨546714, by rfl⟩ : syracuseStep 5831621 = 1093429) (by norm_num)
theorem B3070925 : Blo 1364501 3070925 := bbase (se 3 (by rfl) ⟨575798, by rfl⟩ : syracuseStep 3070925 = 1151597) (by norm_num)
theorem B2046941 : Blo 1364501 2046941 := bbase (se 3 (by rfl) ⟨383801, by rfl⟩ : syracuseStep 2046941 = 767603) (by norm_num)
theorem B2046965 : Blo 1364501 2046965 := bbase (se 5 (by rfl) ⟨95951, by rfl⟩ : syracuseStep 2046965 = 191903) (by norm_num)
theorem B3505141 : Blo 1364501 3505141 := bbase (se 5 (by rfl) ⟨164303, by rfl⟩ : syracuseStep 3505141 = 328607) (by norm_num)
theorem B1727497 : Blo 1364501 1727497 := bbase (se 2 (by rfl) ⟨647811, by rfl⟩ : syracuseStep 1727497 = 1295623) (by norm_num)
theorem B2046989 : Blo 1364501 2046989 := bbase (se 3 (by rfl) ⟨383810, by rfl⟩ : syracuseStep 2046989 = 767621) (by norm_num)
theorem B3070997 : Blo 1364501 3070997 := bbase (se 6 (by rfl) ⟨71976, by rfl⟩ : syracuseStep 3070997 = 143953) (by norm_num)
theorem B2047013 : Blo 1364501 2047013 := bbase (se 4 (by rfl) ⟨191907, by rfl⟩ : syracuseStep 2047013 = 383815) (by norm_num)
theorem B2047037 : Blo 1364501 2047037 := bbase (se 3 (by rfl) ⟨383819, by rfl⟩ : syracuseStep 2047037 = 767639) (by norm_num)
theorem B2047061 : Blo 1364501 2047061 := bbase (se 8 (by rfl) ⟨11994, by rfl⟩ : syracuseStep 2047061 = 23989) (by norm_num)
theorem B3071069 : Blo 1364501 3071069 := bbase (se 3 (by rfl) ⟨575825, by rfl⟩ : syracuseStep 3071069 = 1151651) (by norm_num)
theorem B2047085 : Blo 1364501 2047085 := bbase (se 3 (by rfl) ⟨383828, by rfl⟩ : syracuseStep 2047085 = 767657) (by norm_num)
theorem B13130869 : Blo 1364501 13130869 := bbase (se 5 (by rfl) ⟨615509, by rfl⟩ : syracuseStep 13130869 = 1231019) (by norm_num)
theorem B6225029 : Blo 1364501 6225029 := bbase (se 4 (by rfl) ⟨583596, by rfl⟩ : syracuseStep 6225029 = 1167193) (by norm_num)
theorem B2047109 : Blo 1364501 2047109 := bbase (se 4 (by rfl) ⟨191916, by rfl⟩ : syracuseStep 2047109 = 383833) (by norm_num)
theorem B10362005 : Blo 1364501 10362005 := bbase (se 6 (by rfl) ⟨242859, by rfl⟩ : syracuseStep 10362005 = 485719) (by norm_num)
theorem B4611221 : Blo 1364501 4611221 := bbase (se 6 (by rfl) ⟨108075, by rfl⟩ : syracuseStep 4611221 = 216151) (by norm_num)
theorem B2047133 : Blo 1364501 2047133 := bbase (se 3 (by rfl) ⟨383837, by rfl⟩ : syracuseStep 2047133 = 767675) (by norm_num)
theorem B3071141 : Blo 1364501 3071141 := bbase (se 4 (by rfl) ⟨287919, by rfl⟩ : syracuseStep 3071141 = 575839) (by norm_num)
theorem B2047157 : Blo 1364501 2047157 := bbase (se 5 (by rfl) ⟨95960, by rfl⟩ : syracuseStep 2047157 = 191921) (by norm_num)
theorem B1727669 : Blo 1364501 1727669 := bbase (se 5 (by rfl) ⟨80984, by rfl⟩ : syracuseStep 1727669 = 161969) (by norm_num)
theorem B1752257 : Blo 1364501 1752257 := bbase (se 2 (by rfl) ⟨657096, by rfl⟩ : syracuseStep 1752257 = 1314193) (by norm_num)
theorem B2047181 : Blo 1364501 2047181 := bbase (se 3 (by rfl) ⟨383846, by rfl⟩ : syracuseStep 2047181 = 767693) (by norm_num)
theorem B3890389 : Blo 1364501 3890389 := bbase (se 7 (by rfl) ⟨45590, by rfl⟩ : syracuseStep 3890389 = 91181) (by norm_num)
theorem B2047205 : Blo 1364501 2047205 := bbase (se 4 (by rfl) ⟨191925, by rfl⟩ : syracuseStep 2047205 = 383851) (by norm_num)
theorem B5831909 : Blo 1364501 5831909 := bbase (se 4 (by rfl) ⟨546741, by rfl⟩ : syracuseStep 5831909 = 1093483) (by norm_num)
theorem B3456229 : Blo 1364501 3456229 := bbase (se 4 (by rfl) ⟨324021, by rfl⟩ : syracuseStep 3456229 = 648043) (by norm_num)
theorem B3071213 : Blo 1364501 3071213 := bbase (se 3 (by rfl) ⟨575852, by rfl⟩ : syracuseStep 3071213 = 1151705) (by norm_num)
theorem B1727725 : Blo 1364501 1727725 := bbase (se 3 (by rfl) ⟨323948, by rfl⟩ : syracuseStep 1727725 = 647897) (by norm_num)
theorem B7888117 : Blo 1364501 7888117 := bbase (se 5 (by rfl) ⟨369755, by rfl⟩ : syracuseStep 7888117 = 739511) (by norm_num)
theorem B2047229 : Blo 1364501 2047229 := bbase (se 3 (by rfl) ⟨383855, by rfl⟩ : syracuseStep 2047229 = 767711) (by norm_num)
theorem B2047253 : Blo 1364501 2047253 := bbase (se 6 (by rfl) ⟨47982, by rfl⟩ : syracuseStep 2047253 = 95965) (by norm_num)
theorem B2915605 : Blo 1364501 2915605 := bbase (se 6 (by rfl) ⟨68334, by rfl⟩ : syracuseStep 2915605 = 136669) (by norm_num)
theorem B2047277 : Blo 1364501 2047277 := bbase (se 3 (by rfl) ⟨383864, by rfl⟩ : syracuseStep 2047277 = 767729) (by norm_num)
theorem B1457461 : Blo 1364501 1457461 := bbase (se 5 (by rfl) ⟨68318, by rfl⟩ : syracuseStep 1457461 = 136637) (by norm_num)
theorem B3071285 : Blo 1364501 3071285 := bbase (se 5 (by rfl) ⟨143966, by rfl⟩ : syracuseStep 3071285 = 287933) (by norm_num)
theorem B2047301 : Blo 1364501 2047301 := bbase (se 4 (by rfl) ⟨191934, by rfl⟩ : syracuseStep 2047301 = 383869) (by norm_num)
theorem B6913349 : Blo 1364501 6913349 := bbase (se 4 (by rfl) ⟨648126, by rfl⟩ : syracuseStep 6913349 = 1296253) (by norm_num)
theorem B1727821 : Blo 1364501 1727821 := bbase (se 3 (by rfl) ⟨323966, by rfl⟩ : syracuseStep 1727821 = 647933) (by norm_num)
theorem B3456341 : Blo 1364501 3456341 := bbase (se 11 (by rfl) ⟨2531, by rfl⟩ : syracuseStep 3456341 = 5063) (by norm_num)
theorem B2047325 : Blo 1364501 2047325 := bbase (se 3 (by rfl) ⟨383873, by rfl⟩ : syracuseStep 2047325 = 767747) (by norm_num)
theorem B2047349 : Blo 1364501 2047349 := bbase (se 5 (by rfl) ⟨95969, by rfl⟩ : syracuseStep 2047349 = 191939) (by norm_num)
theorem B5913973 : Blo 1364501 5913973 := bbase (se 5 (by rfl) ⟨277217, by rfl⟩ : syracuseStep 5913973 = 554435) (by norm_num)
theorem B1457533 : Blo 1364501 1457533 := bbase (se 3 (by rfl) ⟨273287, by rfl⟩ : syracuseStep 1457533 = 546575) (by norm_num)
theorem B3071357 : Blo 1364501 3071357 := bbase (se 3 (by rfl) ⟨575879, by rfl⟩ : syracuseStep 3071357 = 1151759) (by norm_num)
theorem B2047373 : Blo 1364501 2047373 := bbase (se 3 (by rfl) ⟨383882, by rfl⟩ : syracuseStep 2047373 = 767765) (by norm_num)
theorem B2768269 : Blo 1364501 2768269 := bbase (se 3 (by rfl) ⟨519050, by rfl⟩ : syracuseStep 2768269 = 1038101) (by norm_num)
theorem B2047397 : Blo 1364501 2047397 := bbase (se 4 (by rfl) ⟨191943, by rfl⟩ : syracuseStep 2047397 = 383887) (by norm_num)
theorem B2047421 : Blo 1364501 2047421 := bbase (se 3 (by rfl) ⟨383891, by rfl⟩ : syracuseStep 2047421 = 767783) (by norm_num)
theorem B3071429 : Blo 1364501 3071429 := bbase (se 4 (by rfl) ⟨287946, by rfl⟩ : syracuseStep 3071429 = 575893) (by norm_num)
theorem B2047445 : Blo 1364501 2047445 := bbase (se 7 (by rfl) ⟨23993, by rfl⟩ : syracuseStep 2047445 = 47987) (by norm_num)
theorem B2047469 : Blo 1364501 2047469 := bbase (se 3 (by rfl) ⟨383900, by rfl⟩ : syracuseStep 2047469 = 767801) (by norm_num)
theorem B1727993 : Blo 1364501 1727993 := bbase (se 2 (by rfl) ⟨647997, by rfl⟩ : syracuseStep 1727993 = 1295995) (by norm_num)
theorem B2047493 : Blo 1364501 2047493 := bbase (se 4 (by rfl) ⟨191952, by rfl⟩ : syracuseStep 2047493 = 383905) (by norm_num)
theorem B3071501 : Blo 1364501 3071501 := bbase (se 3 (by rfl) ⟨575906, by rfl⟩ : syracuseStep 3071501 = 1151813) (by norm_num)
theorem B3456533 : Blo 1364501 3456533 := bbase (se 6 (by rfl) ⟨81012, by rfl⟩ : syracuseStep 3456533 = 162025) (by norm_num)
theorem B2047517 : Blo 1364501 2047517 := bbase (se 3 (by rfl) ⟨383909, by rfl⟩ : syracuseStep 2047517 = 767819) (by norm_num)
theorem B3939877 : Blo 1364501 3939877 := bbase (se 4 (by rfl) ⟨369363, by rfl⟩ : syracuseStep 3939877 = 738727) (by norm_num)
theorem B1457713 : Blo 1364501 1457713 := bbase (se 2 (by rfl) ⟨546642, by rfl⟩ : syracuseStep 1457713 = 1093285) (by norm_num)
theorem B1728049 : Blo 1364501 1728049 := bbase (se 2 (by rfl) ⟨648018, by rfl⟩ : syracuseStep 1728049 = 1296037) (by norm_num)
theorem B2047541 : Blo 1364501 2047541 := bbase (se 5 (by rfl) ⟨95978, by rfl⟩ : syracuseStep 2047541 = 191957) (by norm_num)
theorem B2186813 : Blo 1364501 2186813 := bbase (se 3 (by rfl) ⟨410027, by rfl⟩ : syracuseStep 2186813 = 820055) (by norm_num)
theorem B4611653 : Blo 1364501 4611653 := bbase (se 4 (by rfl) ⟨432342, by rfl⟩ : syracuseStep 4611653 = 864685) (by norm_num)
theorem B2047565 : Blo 1364501 2047565 := bbase (se 3 (by rfl) ⟨383918, by rfl⟩ : syracuseStep 2047565 = 767837) (by norm_num)
theorem B3071573 : Blo 1364501 3071573 := bbase (se 8 (by rfl) ⟨17997, by rfl⟩ : syracuseStep 3071573 = 35995) (by norm_num)
theorem B2047589 : Blo 1364501 2047589 := bbase (se 4 (by rfl) ⟨191961, by rfl⟩ : syracuseStep 2047589 = 383923) (by norm_num)
theorem B4922981 : Blo 1364501 4922981 := bbase (se 4 (by rfl) ⟨461529, by rfl⟩ : syracuseStep 4922981 = 923059) (by norm_num)
theorem B2047613 : Blo 1364501 2047613 := bbase (se 3 (by rfl) ⟨383927, by rfl⟩ : syracuseStep 2047613 = 767855) (by norm_num)
theorem B1728145 : Blo 1364501 1728145 := bbase (se 2 (by rfl) ⟨648054, by rfl⟩ : syracuseStep 1728145 = 1296109) (by norm_num)
theorem B13115029 : Blo 1364501 13115029 := bbase (se 6 (by rfl) ⟨307383, by rfl⟩ : syracuseStep 13115029 = 614767) (by norm_num)
theorem B2047637 : Blo 1364501 2047637 := bbase (se 6 (by rfl) ⟨47991, by rfl⟩ : syracuseStep 2047637 = 95983) (by norm_num)
theorem B3071645 : Blo 1364501 3071645 := bbase (se 3 (by rfl) ⟨575933, by rfl⟩ : syracuseStep 3071645 = 1151867) (by norm_num)
theorem B2047661 : Blo 1364501 2047661 := bbase (se 3 (by rfl) ⟨383936, by rfl⟩ : syracuseStep 2047661 = 767873) (by norm_num)
theorem B2186941 : Blo 1364501 2186941 := bbase (se 3 (by rfl) ⟨410051, by rfl⟩ : syracuseStep 2186941 = 820103) (by norm_num)
theorem B2047685 : Blo 1364501 2047685 := bbase (se 4 (by rfl) ⟨191970, by rfl⟩ : syracuseStep 2047685 = 383941) (by norm_num)
theorem B1752781 : Blo 1364501 1752781 := bbase (se 3 (by rfl) ⟨328646, by rfl⟩ : syracuseStep 1752781 = 657293) (by norm_num)
theorem B2047709 : Blo 1364501 2047709 := bbase (se 3 (by rfl) ⟨383945, by rfl⟩ : syracuseStep 2047709 = 767891) (by norm_num)
theorem B3071717 : Blo 1364501 3071717 := bbase (se 4 (by rfl) ⟨287973, by rfl⟩ : syracuseStep 3071717 = 575947) (by norm_num)
theorem B2047733 : Blo 1364501 2047733 := bbase (se 5 (by rfl) ⟨95987, by rfl⟩ : syracuseStep 2047733 = 191975) (by norm_num)
theorem B2334469 : Blo 1364501 2334469 := bbase (se 4 (by rfl) ⟨218856, by rfl⟩ : syracuseStep 2334469 = 437713) (by norm_num)
theorem B2047757 : Blo 1364501 2047757 := bbase (se 3 (by rfl) ⟨383954, by rfl⟩ : syracuseStep 2047757 = 767909) (by norm_num)
theorem B2047781 : Blo 1364501 2047781 := bbase (se 4 (by rfl) ⟨191979, by rfl⟩ : syracuseStep 2047781 = 383959) (by norm_num)
theorem B3071789 : Blo 1364501 3071789 := bbase (se 3 (by rfl) ⟨575960, by rfl⟩ : syracuseStep 3071789 = 1151921) (by norm_num)
theorem B2047805 : Blo 1364501 2047805 := bbase (se 3 (by rfl) ⟨383963, by rfl⟩ : syracuseStep 2047805 = 767927) (by norm_num)
theorem B1728317 : Blo 1364501 1728317 := bbase (se 3 (by rfl) ⟨324059, by rfl⟩ : syracuseStep 1728317 = 648119) (by norm_num)
theorem B3112789 : Blo 1364501 3112789 := bbase (se 9 (by rfl) ⟨9119, by rfl⟩ : syracuseStep 3112789 = 18239) (by norm_num)
theorem B2047829 : Blo 1364501 2047829 := bbase (se 9 (by rfl) ⟨5999, by rfl⟩ : syracuseStep 2047829 = 11999) (by norm_num)
theorem B2047853 : Blo 1364501 2047853 := bbase (se 3 (by rfl) ⟨383972, by rfl⟩ : syracuseStep 2047853 = 767945) (by norm_num)
theorem B3456877 : Blo 1364501 3456877 := bbase (se 3 (by rfl) ⟨648164, by rfl⟩ : syracuseStep 3456877 = 1296329) (by norm_num)
theorem B3071861 : Blo 1364501 3071861 := bbase (se 5 (by rfl) ⟨143993, by rfl⟩ : syracuseStep 3071861 = 287987) (by norm_num)
theorem B1728373 : Blo 1364501 1728373 := bbase (se 5 (by rfl) ⟨81017, by rfl⟩ : syracuseStep 1728373 = 162035) (by norm_num)
theorem B2047877 : Blo 1364501 2047877 := bbase (se 4 (by rfl) ⟨191988, by rfl⟩ : syracuseStep 2047877 = 383977) (by norm_num)
theorem B2047901 : Blo 1364501 2047901 := bbase (se 3 (by rfl) ⟨383981, by rfl⟩ : syracuseStep 2047901 = 767963) (by norm_num)
theorem B2047925 : Blo 1364501 2047925 := bbase (se 5 (by rfl) ⟨95996, by rfl⟩ : syracuseStep 2047925 = 191993) (by norm_num)
theorem B3071933 : Blo 1364501 3071933 := bbase (se 3 (by rfl) ⟨575987, by rfl⟩ : syracuseStep 3071933 = 1151975) (by norm_num)
theorem B2047949 : Blo 1364501 2047949 := bbase (se 3 (by rfl) ⟨383990, by rfl⟩ : syracuseStep 2047949 = 767981) (by norm_num)
theorem B5832661 : Blo 1364501 5832661 := bbase (se 7 (by rfl) ⟨68351, by rfl⟩ : syracuseStep 5832661 = 136703) (by norm_num)
theorem B1728469 : Blo 1364501 1728469 := bbase (se 7 (by rfl) ⟨20255, by rfl⟩ : syracuseStep 1728469 = 40511) (by norm_num)
theorem B2842589 : Blo 1364501 2842589 := bbase (se 3 (by rfl) ⟨532985, by rfl⟩ : syracuseStep 2842589 = 1065971) (by norm_num)
theorem B3456989 : Blo 1364501 3456989 := bbase (se 3 (by rfl) ⟨648185, by rfl⟩ : syracuseStep 3456989 = 1296371) (by norm_num)
theorem B2047973 : Blo 1364501 2047973 := bbase (se 4 (by rfl) ⟨191997, by rfl⟩ : syracuseStep 2047973 = 383995) (by norm_num)
theorem B1458157 : Blo 1364501 1458157 := bbase (se 3 (by rfl) ⟨273404, by rfl⟩ : syracuseStep 1458157 = 546809) (by norm_num)
theorem B2047997 : Blo 1364501 2047997 := bbase (se 3 (by rfl) ⟨383999, by rfl⟩ : syracuseStep 2047997 = 767999) (by norm_num)
theorem B2048003 : Blo 1364501 2048003 := bstep (se 1 (by rfl) ⟨1536002, by rfl⟩ : syracuseStep 2048003 = 3072005) B3072005
theorem B2048033 : Blo 1364501 2048033 := bstep (se 2 (by rfl) ⟨768012, by rfl⟩ : syracuseStep 2048033 = 1536025) B1536025
theorem B2048051 : Blo 1364501 2048051 := bstep (se 1 (by rfl) ⟨1536038, by rfl⟩ : syracuseStep 2048051 = 3072077) B3072077
theorem B2048081 : Blo 1364501 2048081 := bstep (se 2 (by rfl) ⟨768030, by rfl⟩ : syracuseStep 2048081 = 1536061) B1536061
theorem B2916433 : Blo 1364501 2916433 := bstep (se 2 (by rfl) ⟨1093662, by rfl⟩ : syracuseStep 2916433 = 2187325) B2187325
theorem B2048099 : Blo 1364501 2048099 := bstep (se 1 (by rfl) ⟨1536074, by rfl⟩ : syracuseStep 2048099 = 3072149) B3072149
theorem B3072113 : Blo 1364501 3072113 := bstep (se 2 (by rfl) ⟨1152042, by rfl⟩ : syracuseStep 3072113 = 2304085) B2304085
theorem B2048129 : Blo 1364501 2048129 := bstep (se 2 (by rfl) ⟨768048, by rfl⟩ : syracuseStep 2048129 = 1536097) B1536097
theorem B3072131 : Blo 1364501 3072131 := bstep (se 1 (by rfl) ⟨2304098, by rfl⟩ : syracuseStep 3072131 = 4608197) B4608197
theorem B2048147 : Blo 1364501 2048147 := bstep (se 1 (by rfl) ⟨1536110, by rfl⟩ : syracuseStep 2048147 = 3072221) B3072221
theorem B2048177 : Blo 1364501 2048177 := bstep (se 2 (by rfl) ⟨768066, by rfl⟩ : syracuseStep 2048177 = 1536133) B1536133
theorem B3457201 : Blo 1364501 3457201 := bstep (se 2 (by rfl) ⟨1296450, by rfl⟩ : syracuseStep 3457201 = 2592901) B2592901
theorem B2048195 : Blo 1364501 2048195 := bstep (se 1 (by rfl) ⟨1536146, by rfl⟩ : syracuseStep 2048195 = 3072293) B3072293
theorem B5185741 : Blo 1364501 5185741 := bstep (se 3 (by rfl) ⟨972326, by rfl⟩ : syracuseStep 5185741 = 1944653) B1944653
theorem B2048225 : Blo 1364501 2048225 := bstep (se 2 (by rfl) ⟨768084, by rfl⟩ : syracuseStep 2048225 = 1536169) B1536169
theorem B2048243 : Blo 1364501 2048243 := bstep (se 1 (by rfl) ⟨1536182, by rfl⟩ : syracuseStep 2048243 = 3072365) B3072365
theorem B2048273 : Blo 1364501 2048273 := bstep (se 2 (by rfl) ⟨768102, by rfl⟩ : syracuseStep 2048273 = 1536205) B1536205
theorem B2048291 : Blo 1364501 2048291 := bstep (se 1 (by rfl) ⟨1536218, by rfl⟩ : syracuseStep 2048291 = 3072437) B3072437
theorem B1728803 : Blo 1364501 1728803 := bstep (se 1 (by rfl) ⟨1296602, by rfl⟩ : syracuseStep 1728803 = 2593205) B2593205
theorem B2048321 : Blo 1364501 2048321 := bstep (se 2 (by rfl) ⟨768120, by rfl⟩ : syracuseStep 2048321 = 1536241) B1536241
theorem B2048339 : Blo 1364501 2048339 := bstep (se 1 (by rfl) ⟨1536254, by rfl⟩ : syracuseStep 2048339 = 3072509) B3072509
theorem B2048369 : Blo 1364501 2048369 := bstep (se 2 (by rfl) ⟨768138, by rfl⟩ : syracuseStep 2048369 = 1536277) B1536277
theorem B2048387 : Blo 1364501 2048387 := bstep (se 1 (by rfl) ⟨1536290, by rfl⟩ : syracuseStep 2048387 = 3072581) B3072581
theorem B3072401 : Blo 1364501 3072401 := bstep (se 2 (by rfl) ⟨1152150, by rfl⟩ : syracuseStep 3072401 = 2304301) B2304301
theorem B2048417 : Blo 1364501 2048417 := bstep (se 2 (by rfl) ⟨768156, by rfl⟩ : syracuseStep 2048417 = 1536313) B1536313
theorem B3072419 : Blo 1364501 3072419 := bstep (se 1 (by rfl) ⟨2304314, by rfl⟩ : syracuseStep 3072419 = 4608629) B4608629
theorem B2048435 : Blo 1364501 2048435 := bstep (se 1 (by rfl) ⟨1536326, by rfl⟩ : syracuseStep 2048435 = 3072653) B3072653
theorem B3457475 : Blo 1364501 3457475 := bstep (se 1 (by rfl) ⟨2593106, by rfl⟩ : syracuseStep 3457475 = 5186213) B5186213
theorem B2048465 : Blo 1364501 2048465 := bstep (se 2 (by rfl) ⟨768174, by rfl⟩ : syracuseStep 2048465 = 1536349) B1536349
theorem B2048483 : Blo 1364501 2048483 := bstep (se 1 (by rfl) ⟨1536362, by rfl⟩ : syracuseStep 2048483 = 3072725) B3072725
theorem B2048513 : Blo 1364501 2048513 := bstep (se 2 (by rfl) ⟨768192, by rfl⟩ : syracuseStep 2048513 = 1536385) B1536385
theorem B2048531 : Blo 1364501 2048531 := bstep (se 1 (by rfl) ⟨1536398, by rfl⟩ : syracuseStep 2048531 = 3072797) B3072797
theorem B2048561 : Blo 1364501 2048561 := bstep (se 2 (by rfl) ⟨768210, by rfl⟩ : syracuseStep 2048561 = 1536421) B1536421
theorem B2048579 : Blo 1364501 2048579 := bstep (se 1 (by rfl) ⟨1536434, by rfl⟩ : syracuseStep 2048579 = 3072869) B3072869
theorem B2048609 : Blo 1364501 2048609 := bstep (se 2 (by rfl) ⟨768228, by rfl⟩ : syracuseStep 2048609 = 1536457) B1536457
theorem B2048627 : Blo 1364501 2048627 := bstep (se 1 (by rfl) ⟨1536470, by rfl⟩ : syracuseStep 2048627 = 3072941) B3072941
theorem B3457667 : Blo 1364501 3457667 := bstep (se 1 (by rfl) ⟨2593250, by rfl⟩ : syracuseStep 3457667 = 5186501) B5186501
theorem B9839245 : Blo 1364501 9839245 := bstep (se 3 (by rfl) ⟨1844858, by rfl⟩ : syracuseStep 9839245 = 3689717) B3689717
theorem B10371725 : Blo 1364501 10371725 := bstep (se 3 (by rfl) ⟨1944698, by rfl⟩ : syracuseStep 10371725 = 3889397) B3889397
theorem B2048657 : Blo 1364501 2048657 := bstep (se 2 (by rfl) ⟨768246, by rfl⟩ : syracuseStep 2048657 = 1536493) B1536493
theorem B2302627 : Blo 1364501 2302627 := bstep (se 1 (by rfl) ⟨1726970, by rfl⟩ : syracuseStep 2302627 = 3453941) B3453941
theorem B2048675 : Blo 1364501 2048675 := bstep (se 1 (by rfl) ⟨1536506, by rfl⟩ : syracuseStep 2048675 = 3073013) B3073013
theorem B3072689 : Blo 1364501 3072689 := bstep (se 2 (by rfl) ⟨1152258, by rfl⟩ : syracuseStep 3072689 = 2304517) B2304517
theorem B2048705 : Blo 1364501 2048705 := bstep (se 2 (by rfl) ⟨768264, by rfl⟩ : syracuseStep 2048705 = 1536529) B1536529
theorem B3072707 : Blo 1364501 3072707 := bstep (se 1 (by rfl) ⟨2304530, by rfl⟩ : syracuseStep 3072707 = 4609061) B4609061
theorem B2048723 : Blo 1364501 2048723 := bstep (se 1 (by rfl) ⟨1536542, by rfl⟩ : syracuseStep 2048723 = 3073085) B3073085
theorem B2048753 : Blo 1364501 2048753 := bstep (se 2 (by rfl) ⟨768282, by rfl⟩ : syracuseStep 2048753 = 1536565) B1536565
theorem B2048771 : Blo 1364501 2048771 := bstep (se 1 (by rfl) ⟨1536578, by rfl⟩ : syracuseStep 2048771 = 3073157) B3073157
theorem B2048801 : Blo 1364501 2048801 := bstep (se 2 (by rfl) ⟨768300, by rfl⟩ : syracuseStep 2048801 = 1536601) B1536601
theorem B2302769 : Blo 1364501 2302769 := bstep (se 2 (by rfl) ⟨863538, by rfl⟩ : syracuseStep 2302769 = 1727077) B1727077
theorem B2048819 : Blo 1364501 2048819 := bstep (se 1 (by rfl) ⟨1536614, by rfl⟩ : syracuseStep 2048819 = 3073229) B3073229
theorem B5833549 : Blo 1364501 5833549 := bstep (se 3 (by rfl) ⟨1093790, by rfl⟩ : syracuseStep 5833549 = 2187581) B2187581
theorem B2048849 : Blo 1364501 2048849 := bstep (se 2 (by rfl) ⟨768318, by rfl⟩ : syracuseStep 2048849 = 1536637) B1536637
theorem B13116259 : Blo 1364501 13116259 := bstep (se 1 (by rfl) ⟨9837194, by rfl⟩ : syracuseStep 13116259 = 19674389) B19674389
theorem B2048867 : Blo 1364501 2048867 := bstep (se 1 (by rfl) ⟨1536650, by rfl⟩ : syracuseStep 2048867 = 3073301) B3073301
theorem B2188145 : Blo 1364501 2188145 := bstep (se 2 (by rfl) ⟨820554, by rfl⟩ : syracuseStep 2188145 = 1641109) B1641109
theorem B1639283 : Blo 1364501 1639283 := bstep (se 1 (by rfl) ⟨1229462, by rfl⟩ : syracuseStep 1639283 = 2458925) B2458925
theorem B2048897 : Blo 1364501 2048897 := bstep (se 2 (by rfl) ⟨768336, by rfl⟩ : syracuseStep 2048897 = 1536673) B1536673
theorem B2048915 : Blo 1364501 2048915 := bstep (se 1 (by rfl) ⟨1536686, by rfl⟩ : syracuseStep 2048915 = 3073373) B3073373
theorem B2302897 : Blo 1364501 2302897 := bstep (se 2 (by rfl) ⟨863586, by rfl⟩ : syracuseStep 2302897 = 1727173) B1727173
theorem B2048945 : Blo 1364501 2048945 := bstep (se 2 (by rfl) ⟨768354, by rfl⟩ : syracuseStep 2048945 = 1536709) B1536709
theorem B2048963 : Blo 1364501 2048963 := bstep (se 1 (by rfl) ⟨1536722, by rfl⟩ : syracuseStep 2048963 = 3073445) B3073445
theorem B1459139 : Blo 1364501 1459139 := bstep (se 1 (by rfl) ⟨1094354, by rfl⟩ : syracuseStep 1459139 = 2188709) B2188709
theorem B3072977 : Blo 1364501 3072977 := bstep (se 2 (by rfl) ⟨1152366, by rfl⟩ : syracuseStep 3072977 = 2304733) B2304733
theorem B2302931 : Blo 1364501 2302931 := bstep (se 1 (by rfl) ⟨1727198, by rfl⟩ : syracuseStep 2302931 = 3454397) B3454397
theorem B2048993 : Blo 1364501 2048993 := bstep (se 2 (by rfl) ⟨768372, by rfl⟩ : syracuseStep 2048993 = 1536745) B1536745
theorem B2368481 : Blo 1364501 2368481 := bstep (se 2 (by rfl) ⟨888180, by rfl⟩ : syracuseStep 2368481 = 1776361) B1776361
theorem B3072995 : Blo 1364501 3072995 := bstep (se 1 (by rfl) ⟨2304746, by rfl⟩ : syracuseStep 3072995 = 4609493) B4609493
theorem B5186531 : Blo 1364501 5186531 := bstep (se 1 (by rfl) ⟨3889898, by rfl⟩ : syracuseStep 5186531 = 7779797) B7779797
theorem B2049011 : Blo 1364501 2049011 := bstep (se 1 (by rfl) ⟨1536758, by rfl⟩ : syracuseStep 2049011 = 3073517) B3073517
theorem B2049041 : Blo 1364501 2049041 := bstep (se 2 (by rfl) ⟨768390, by rfl⟩ : syracuseStep 2049041 = 1536781) B1536781
theorem B2049059 : Blo 1364501 2049059 := bstep (se 1 (by rfl) ⟨1536794, by rfl⟩ : syracuseStep 2049059 = 3073589) B3073589
theorem B2049089 : Blo 1364501 2049089 := bstep (se 2 (by rfl) ⟨768408, by rfl⟩ : syracuseStep 2049089 = 1536817) B1536817
theorem B2303059 : Blo 1364501 2303059 := bstep (se 1 (by rfl) ⟨1727294, by rfl⟩ : syracuseStep 2303059 = 3454589) B3454589
theorem B2049107 : Blo 1364501 2049107 := bstep (se 1 (by rfl) ⟨1536830, by rfl⟩ : syracuseStep 2049107 = 3073661) B3073661
theorem B2049137 : Blo 1364501 2049137 := bstep (se 2 (by rfl) ⟨768426, by rfl⟩ : syracuseStep 2049137 = 1536853) B1536853
theorem B2049155 : Blo 1364501 2049155 := bstep (se 1 (by rfl) ⟨1536866, by rfl⟩ : syracuseStep 2049155 = 3073733) B3073733
theorem B2049185 : Blo 1364501 2049185 := bstep (se 2 (by rfl) ⟨768444, by rfl⟩ : syracuseStep 2049185 = 1536889) B1536889
theorem B2049203 : Blo 1364501 2049203 := bstep (se 1 (by rfl) ⟨1536902, by rfl⟩ : syracuseStep 2049203 = 3073805) B3073805
theorem B2049233 : Blo 1364501 2049233 := bstep (se 2 (by rfl) ⟨768462, by rfl⟩ : syracuseStep 2049233 = 1536925) B1536925
theorem B2303201 : Blo 1364501 2303201 := bstep (se 2 (by rfl) ⟨863700, by rfl⟩ : syracuseStep 2303201 = 1727401) B1727401
theorem B2049251 : Blo 1364501 2049251 := bstep (se 1 (by rfl) ⟨1536938, by rfl⟩ : syracuseStep 2049251 = 3073877) B3073877
theorem B3073265 : Blo 1364501 3073265 := bstep (se 2 (by rfl) ⟨1152474, by rfl⟩ : syracuseStep 3073265 = 2304949) B2304949
theorem B2049281 : Blo 1364501 2049281 := bstep (se 2 (by rfl) ⟨768480, by rfl⟩ : syracuseStep 2049281 = 1536961) B1536961
theorem B3073283 : Blo 1364501 3073283 := bstep (se 1 (by rfl) ⟨2304962, by rfl⟩ : syracuseStep 3073283 = 4609925) B4609925
theorem B2049299 : Blo 1364501 2049299 := bstep (se 1 (by rfl) ⟨1536974, by rfl⟩ : syracuseStep 2049299 = 3073949) B3073949
theorem B2245937 : Blo 1364501 2245937 := bstep (se 2 (by rfl) ⟨842226, by rfl⟩ : syracuseStep 2245937 = 1684453) B1684453
theorem B2049329 : Blo 1364501 2049329 := bstep (se 2 (by rfl) ⟨768498, by rfl⟩ : syracuseStep 2049329 = 1536997) B1536997
theorem B2049347 : Blo 1364501 2049347 := bstep (se 1 (by rfl) ⟨1537010, by rfl⟩ : syracuseStep 2049347 = 3074021) B3074021
theorem B2303329 : Blo 1364501 2303329 := bstep (se 2 (by rfl) ⟨863748, by rfl⟩ : syracuseStep 2303329 = 1727497) B1727497
theorem B4375907 : Blo 1364501 4375907 := bstep (se 1 (by rfl) ⟨3281930, by rfl⟩ : syracuseStep 4375907 = 6563861) B6563861
theorem B2049377 : Blo 1364501 2049377 := bstep (se 2 (by rfl) ⟨768516, by rfl⟩ : syracuseStep 2049377 = 1537033) B1537033
theorem B2049395 : Blo 1364501 2049395 := bstep (se 1 (by rfl) ⟨1537046, by rfl⟩ : syracuseStep 2049395 = 3074093) B3074093
theorem B2303363 : Blo 1364501 2303363 := bstep (se 1 (by rfl) ⟨1727522, by rfl⟩ : syracuseStep 2303363 = 3455045) B3455045
theorem B2049425 : Blo 1364501 2049425 := bstep (se 2 (by rfl) ⟨768534, by rfl⟩ : syracuseStep 2049425 = 1537069) B1537069
theorem B6227363 : Blo 1364501 6227363 := bstep (se 1 (by rfl) ⟨4670522, by rfl⟩ : syracuseStep 6227363 = 9341045) B9341045
theorem B2049443 : Blo 1364501 2049443 := bstep (se 1 (by rfl) ⟨1537082, by rfl⟩ : syracuseStep 2049443 = 3074165) B3074165
theorem B2049473 : Blo 1364501 2049473 := bstep (se 2 (by rfl) ⟨768552, by rfl⟩ : syracuseStep 2049473 = 1537105) B1537105
theorem B4605389 : Blo 1364501 4605389 := bstep (se 3 (by rfl) ⟨863510, by rfl⟩ : syracuseStep 4605389 = 1727021) B1727021
theorem B2049491 : Blo 1364501 2049491 := bstep (se 1 (by rfl) ⟨1537118, by rfl⟩ : syracuseStep 2049491 = 3074237) B3074237
theorem B17507825 : Blo 1364501 17507825 := bstep (se 2 (by rfl) ⟨6565434, by rfl⟩ : syracuseStep 17507825 = 13130869) B13130869
theorem B2049521 : Blo 1364501 2049521 := bstep (se 2 (by rfl) ⟨768570, by rfl⟩ : syracuseStep 2049521 = 1537141) B1537141
theorem B4605443 : Blo 1364501 4605443 := bstep (se 1 (by rfl) ⟨3454082, by rfl⟩ : syracuseStep 4605443 = 6908165) B6908165
theorem B2303491 : Blo 1364501 2303491 := bstep (se 1 (by rfl) ⟨1727618, by rfl⟩ : syracuseStep 2303491 = 3455237) B3455237
theorem B2049539 : Blo 1364501 2049539 := bstep (se 1 (by rfl) ⟨1537154, by rfl⟩ : syracuseStep 2049539 = 3074309) B3074309
theorem B3073553 : Blo 1364501 3073553 := bstep (se 2 (by rfl) ⟨1152582, by rfl⟩ : syracuseStep 3073553 = 2305165) B2305165
theorem B2049569 : Blo 1364501 2049569 := bstep (se 2 (by rfl) ⟨768588, by rfl⟩ : syracuseStep 2049569 = 1537177) B1537177
theorem B3073571 : Blo 1364501 3073571 := bstep (se 1 (by rfl) ⟨2305178, by rfl⟩ : syracuseStep 3073571 = 4610357) B4610357
theorem B2917937 : Blo 1364501 2917937 := bstep (se 2 (by rfl) ⟨1094226, by rfl⟩ : syracuseStep 2917937 = 2188453) B2188453
theorem B3458609 : Blo 1364501 3458609 := bstep (se 2 (by rfl) ⟨1296978, by rfl⟩ : syracuseStep 3458609 = 2593957) B2593957
theorem B2049587 : Blo 1364501 2049587 := bstep (se 1 (by rfl) ⟨1537190, by rfl⟩ : syracuseStep 2049587 = 3074381) B3074381
theorem B2049617 : Blo 1364501 2049617 := bstep (se 2 (by rfl) ⟨768606, by rfl⟩ : syracuseStep 2049617 = 1537213) B1537213
theorem B3458659 : Blo 1364501 3458659 := bstep (se 1 (by rfl) ⟨2593994, by rfl⟩ : syracuseStep 3458659 = 5187989) B5187989
theorem B2049635 : Blo 1364501 2049635 := bstep (se 1 (by rfl) ⟨1537226, by rfl⟩ : syracuseStep 2049635 = 3074453) B3074453
theorem B7104113 : Blo 1364501 7104113 := bstep (se 2 (by rfl) ⟨2664042, by rfl⟩ : syracuseStep 7104113 = 5328085) B5328085
theorem B4376177 : Blo 1364501 4376177 := bstep (se 2 (by rfl) ⟨1641066, by rfl⟩ : syracuseStep 4376177 = 3282133) B3282133
theorem B5187185 : Blo 1364501 5187185 := bstep (se 2 (by rfl) ⟨1945194, by rfl⟩ : syracuseStep 5187185 = 3890389) B3890389
theorem B2049665 : Blo 1364501 2049665 := bstep (se 2 (by rfl) ⟨768624, by rfl⟩ : syracuseStep 2049665 = 1537249) B1537249
theorem B2303633 : Blo 1364501 2303633 := bstep (se 2 (by rfl) ⟨863862, by rfl⟩ : syracuseStep 2303633 = 1727725) B1727725
theorem B2049683 : Blo 1364501 2049683 := bstep (se 1 (by rfl) ⟨1537262, by rfl⟩ : syracuseStep 2049683 = 3074525) B3074525
theorem B2049713 : Blo 1364501 2049713 := bstep (se 2 (by rfl) ⟨768642, by rfl⟩ : syracuseStep 2049713 = 1537285) B1537285
theorem B2049731 : Blo 1364501 2049731 := bstep (se 1 (by rfl) ⟨1537298, by rfl⟩ : syracuseStep 2049731 = 3074597) B3074597
theorem B1943281 : Blo 1364501 1943281 := bstep (se 2 (by rfl) ⟨728730, by rfl⟩ : syracuseStep 1943281 = 1457461) B1457461
theorem B3458801 : Blo 1364501 3458801 := bstep (se 2 (by rfl) ⟨1297050, by rfl⟩ : syracuseStep 3458801 = 2594101) B2594101
theorem B4605713 : Blo 1364501 4605713 := bstep (se 2 (by rfl) ⟨1727142, by rfl⟩ : syracuseStep 4605713 = 3454285) B3454285
theorem B2303761 : Blo 1364501 2303761 := bstep (se 2 (by rfl) ⟨863910, by rfl⟩ : syracuseStep 2303761 = 1727821) B1727821
theorem B3073841 : Blo 1364501 3073841 := bstep (se 2 (by rfl) ⟨1152690, by rfl⟩ : syracuseStep 3073841 = 2305381) B2305381
theorem B2303795 : Blo 1364501 2303795 := bstep (se 1 (by rfl) ⟨1727846, by rfl⟩ : syracuseStep 2303795 = 3455693) B3455693
theorem B3073859 : Blo 1364501 3073859 := bstep (se 1 (by rfl) ⟨2305394, by rfl⟩ : syracuseStep 3073859 = 4610789) B4610789
theorem B2303923 : Blo 1364501 2303923 := bstep (se 1 (by rfl) ⟨1727942, by rfl⟩ : syracuseStep 2303923 = 3455885) B3455885
theorem B2918339 : Blo 1364501 2918339 := bstep (se 1 (by rfl) ⟨2188754, by rfl⟩ : syracuseStep 2918339 = 4377509) B4377509
theorem B5253169 : Blo 1364501 5253169 := bstep (se 2 (by rfl) ⟨1969938, by rfl⟩ : syracuseStep 5253169 = 3939877) B3939877
theorem B1943617 : Blo 1364501 1943617 := bstep (se 2 (by rfl) ⟨728856, by rfl⟩ : syracuseStep 1943617 = 1457713) B1457713
theorem B2304065 : Blo 1364501 2304065 := bstep (se 2 (by rfl) ⟨864024, by rfl⟩ : syracuseStep 2304065 = 1728049) B1728049
theorem B3074129 : Blo 1364501 3074129 := bstep (se 2 (by rfl) ⟨1152798, by rfl⟩ : syracuseStep 3074129 = 2305597) B2305597
theorem B6908003 : Blo 1364501 6908003 := bstep (se 1 (by rfl) ⟨5181002, by rfl⟩ : syracuseStep 6908003 = 10362005) B10362005
theorem B3074147 : Blo 1364501 3074147 := bstep (se 1 (by rfl) ⟨2305610, by rfl⟩ : syracuseStep 3074147 = 4611221) B4611221
theorem B14772365 : Blo 1364501 14772365 := bstep (se 3 (by rfl) ⟨2769818, by rfl⟩ : syracuseStep 14772365 = 5539637) B5539637
theorem B2304193 : Blo 1364501 2304193 := bstep (se 2 (by rfl) ⟨864072, by rfl⟩ : syracuseStep 2304193 = 1728145) B1728145
theorem B2304227 : Blo 1364501 2304227 := bstep (se 1 (by rfl) ⟨1728170, by rfl⟩ : syracuseStep 2304227 = 3456341) B3456341
theorem B2337041 : Blo 1364501 2337041 := bstep (se 2 (by rfl) ⟨876390, by rfl⟩ : syracuseStep 2337041 = 1752781) B1752781
theorem B4606253 : Blo 1364501 4606253 := bstep (se 3 (by rfl) ⟨863672, by rfl⟩ : syracuseStep 4606253 = 1727345) B1727345
theorem B4606307 : Blo 1364501 4606307 := bstep (se 1 (by rfl) ⟨3454730, by rfl⟩ : syracuseStep 4606307 = 6909461) B6909461
theorem B2304355 : Blo 1364501 2304355 := bstep (se 1 (by rfl) ⟨1728266, by rfl⟩ : syracuseStep 2304355 = 3456533) B3456533
theorem B3074417 : Blo 1364501 3074417 := bstep (se 2 (by rfl) ⟨1152906, by rfl⟩ : syracuseStep 3074417 = 2305813) B2305813
theorem B3074435 : Blo 1364501 3074435 := bstep (se 1 (by rfl) ⟨2305826, by rfl⟩ : syracuseStep 3074435 = 4611653) B4611653
theorem B2591185 : Blo 1364501 2591185 := bstep (se 2 (by rfl) ⟨971694, by rfl⟩ : syracuseStep 2591185 = 1943389) B1943389
theorem B2304497 : Blo 1364501 2304497 := bstep (se 2 (by rfl) ⟨864186, by rfl⟩ : syracuseStep 2304497 = 1728373) B1728373
theorem B16198157 : Blo 1364501 16198157 := bstep (se 3 (by rfl) ⟨3037154, by rfl⟩ : syracuseStep 16198157 = 6074309) B6074309
theorem B5540429 : Blo 1364501 5540429 := bstep (se 3 (by rfl) ⟨1038830, by rfl⟩ : syracuseStep 5540429 = 2077661) B2077661
theorem B4606577 : Blo 1364501 4606577 := bstep (se 2 (by rfl) ⟨1727466, by rfl⟩ : syracuseStep 4606577 = 3454933) B3454933
theorem B2591345 : Blo 1364501 2591345 := bstep (se 2 (by rfl) ⟨971754, by rfl⟩ : syracuseStep 2591345 = 1943509) B1943509
theorem B7776881 : Blo 1364501 7776881 := bstep (se 2 (by rfl) ⟨2916330, by rfl⟩ : syracuseStep 7776881 = 5832661) B5832661
theorem B2304625 : Blo 1364501 2304625 := bstep (se 2 (by rfl) ⟨864234, by rfl⟩ : syracuseStep 2304625 = 1728469) B1728469
theorem B1944209 : Blo 1364501 1944209 := bstep (se 2 (by rfl) ⟨729078, by rfl⟩ : syracuseStep 1944209 = 1458157) B1458157
theorem B1895059 : Blo 1364501 1895059 := bstep (se 1 (by rfl) ⟨1421294, by rfl⟩ : syracuseStep 1895059 = 2842589) B2842589
theorem B2304659 : Blo 1364501 2304659 := bstep (se 1 (by rfl) ⟨1728494, by rfl⟩ : syracuseStep 2304659 = 3456989) B3456989
theorem B14756579 : Blo 1364501 14756579 := bstep (se 1 (by rfl) ⟨11067434, by rfl⟩ : syracuseStep 14756579 = 22134869) B22134869
theorem B2304787 : Blo 1364501 2304787 := bstep (se 1 (by rfl) ⟨1728590, by rfl⟩ : syracuseStep 2304787 = 3457181) B3457181
theorem B6916913 : Blo 1364501 6916913 := bstep (se 2 (by rfl) ⟨2593842, by rfl⟩ : syracuseStep 6916913 = 5187685) B5187685
theorem B6908813 : Blo 1364501 6908813 := bstep (se 3 (by rfl) ⟨1295402, by rfl⟩ : syracuseStep 6908813 = 2590805) B2590805
theorem B2304929 : Blo 1364501 2304929 := bstep (se 2 (by rfl) ⟨864348, by rfl⟩ : syracuseStep 2304929 = 1728697) B1728697
theorem B10365893 : Blo 1364501 10365893 := bstep (se 4 (by rfl) ⟨971802, by rfl⟩ : syracuseStep 10365893 = 1943605) B1943605
theorem B1846243 : Blo 1364501 1846243 := bstep (se 1 (by rfl) ⟨1384682, by rfl⟩ : syracuseStep 1846243 = 2769365) B2769365
theorem B2591747 : Blo 1364501 2591747 := bstep (se 1 (by rfl) ⟨1943810, by rfl⟩ : syracuseStep 2591747 = 3887621) B3887621
theorem B2305057 : Blo 1364501 2305057 := bstep (se 2 (by rfl) ⟨864396, by rfl⟩ : syracuseStep 2305057 = 1728793) B1728793
theorem B2305091 : Blo 1364501 2305091 := bstep (se 1 (by rfl) ⟨1728818, by rfl⟩ : syracuseStep 2305091 = 3457637) B3457637
theorem B23645297 : Blo 1364501 23645297 := bstep (se 2 (by rfl) ⟨8866986, by rfl⟩ : syracuseStep 23645297 = 17733973) B17733973
theorem B2075777 : Blo 1364501 2075777 := bstep (se 2 (by rfl) ⟨778416, by rfl⟩ : syracuseStep 2075777 = 1556833) B1556833
theorem B1535107 : Blo 1364501 1535107 := bstep (se 1 (by rfl) ⟨1151330, by rfl⟩ : syracuseStep 1535107 = 2302661) B2302661
theorem B4607117 : Blo 1364501 4607117 := bstep (se 3 (by rfl) ⟨863834, by rfl⟩ : syracuseStep 4607117 = 1727669) B1727669
theorem B1944739 : Blo 1364501 1944739 := bstep (se 1 (by rfl) ⟨1458554, by rfl⟩ : syracuseStep 1944739 = 2917109) B2917109
theorem B4672685 : Blo 1364501 4672685 := bstep (se 3 (by rfl) ⟨876128, by rfl⟩ : syracuseStep 4672685 = 1752257) B1752257
theorem B4607171 : Blo 1364501 4607171 := bstep (se 1 (by rfl) ⟨3455378, by rfl⟩ : syracuseStep 4607171 = 6910757) B6910757
theorem B2305219 : Blo 1364501 2305219 := bstep (se 1 (by rfl) ⟨1728914, by rfl⟩ : syracuseStep 2305219 = 3457829) B3457829
theorem B3886289 : Blo 1364501 3886289 := bstep (se 2 (by rfl) ⟨1457358, by rfl⟩ : syracuseStep 3886289 = 2914717) B2914717
theorem B1535251 : Blo 1364501 1535251 := bstep (se 1 (by rfl) ⟨1151438, by rfl⟩ : syracuseStep 1535251 = 2302877) B2302877
theorem B2075971 : Blo 1364501 2075971 := bstep (se 1 (by rfl) ⟨1556978, by rfl⟩ : syracuseStep 2075971 = 3113957) B3113957
theorem B2305361 : Blo 1364501 2305361 := bstep (se 2 (by rfl) ⟨864510, by rfl⟩ : syracuseStep 2305361 = 1729021) B1729021
theorem B5533069 : Blo 1364501 5533069 := bstep (se 3 (by rfl) ⟨1037450, by rfl⟩ : syracuseStep 5533069 = 2074901) B2074901
theorem B3886481 : Blo 1364501 3886481 := bstep (se 2 (by rfl) ⟨1457430, by rfl⟩ : syracuseStep 3886481 = 2914861) B2914861
theorem B1535395 : Blo 1364501 1535395 := bstep (se 1 (by rfl) ⟨1151546, by rfl⟩ : syracuseStep 1535395 = 2303093) B2303093
theorem B3689891 : Blo 1364501 3689891 := bstep (se 1 (by rfl) ⟨2767418, by rfl⟩ : syracuseStep 3689891 = 5534837) B5534837
theorem B6565283 : Blo 1364501 6565283 := bstep (se 1 (by rfl) ⟨4923962, by rfl⟩ : syracuseStep 6565283 = 9847925) B9847925
theorem B4607441 : Blo 1364501 4607441 := bstep (se 2 (by rfl) ⟨1727790, by rfl⟩ : syracuseStep 4607441 = 3455581) B3455581
theorem B2305489 : Blo 1364501 2305489 := bstep (se 2 (by rfl) ⟨864558, by rfl⟩ : syracuseStep 2305489 = 1729117) B1729117
theorem B10374641 : Blo 1364501 10374641 := bstep (se 2 (by rfl) ⟨3890490, by rfl⟩ : syracuseStep 10374641 = 7780981) B7780981
theorem B1945075 : Blo 1364501 1945075 := bstep (se 1 (by rfl) ⟨1458806, by rfl⟩ : syracuseStep 1945075 = 2917613) B2917613
theorem B2305523 : Blo 1364501 2305523 := bstep (se 1 (by rfl) ⟨1729142, by rfl⟩ : syracuseStep 2305523 = 3458285) B3458285
theorem B1535539 : Blo 1364501 1535539 := bstep (se 1 (by rfl) ⟨1151654, by rfl⟩ : syracuseStep 1535539 = 2303309) B2303309
theorem B2305651 : Blo 1364501 2305651 := bstep (se 1 (by rfl) ⟨1729238, by rfl⟩ : syracuseStep 2305651 = 3458477) B3458477
theorem B3690161 : Blo 1364501 3690161 := bstep (se 2 (by rfl) ⟨1383810, by rfl⟩ : syracuseStep 3690161 = 2767621) B2767621
theorem B1535683 : Blo 1364501 1535683 := bstep (se 1 (by rfl) ⟨1151762, by rfl⟩ : syracuseStep 1535683 = 2303525) B2303525
theorem B5181155 : Blo 1364501 5181155 := bstep (se 1 (by rfl) ⟨3885866, by rfl⟩ : syracuseStep 5181155 = 7771733) B7771733
theorem B2305793 : Blo 1364501 2305793 := bstep (se 2 (by rfl) ⟨864672, by rfl⟩ : syracuseStep 2305793 = 1729345) B1729345
theorem B1535827 : Blo 1364501 1535827 := bstep (se 1 (by rfl) ⟨1151870, by rfl⟩ : syracuseStep 1535827 = 2303741) B2303741
theorem B22146929 : Blo 1364501 22146929 := bstep (se 2 (by rfl) ⟨8305098, by rfl⟩ : syracuseStep 22146929 = 16610197) B16610197
theorem B2305921 : Blo 1364501 2305921 := bstep (se 2 (by rfl) ⟨864720, by rfl⟩ : syracuseStep 2305921 = 1729441) B1729441
theorem B2592643 : Blo 1364501 2592643 := bstep (se 1 (by rfl) ⟨1944482, by rfl⟩ : syracuseStep 2592643 = 3888965) B3888965
theorem B6229901 : Blo 1364501 6229901 := bstep (se 3 (by rfl) ⟨1168106, by rfl⟩ : syracuseStep 6229901 = 2336213) B2336213
theorem B2305955 : Blo 1364501 2305955 := bstep (se 1 (by rfl) ⟨1729466, by rfl⟩ : syracuseStep 2305955 = 3458933) B3458933
theorem B8753093 : Blo 1364501 8753093 := bstep (se 4 (by rfl) ⟨820602, by rfl⟩ : syracuseStep 8753093 = 1641205) B1641205
theorem B1535971 : Blo 1364501 1535971 := bstep (se 1 (by rfl) ⟨1151978, by rfl⟩ : syracuseStep 1535971 = 2303957) B2303957
theorem B1871843 : Blo 1364501 1871843 := bstep (se 1 (by rfl) ⟨1403882, by rfl⟩ : syracuseStep 1871843 = 2807765) B2807765
theorem B4607981 : Blo 1364501 4607981 := bstep (se 3 (by rfl) ⟨863996, by rfl⟩ : syracuseStep 4607981 = 1727993) B1727993
theorem B4673521 : Blo 1364501 4673521 := bstep (se 2 (by rfl) ⟨1752570, by rfl⟩ : syracuseStep 4673521 = 3505141) B3505141
theorem B4608035 : Blo 1364501 4608035 := bstep (se 1 (by rfl) ⟨3456026, by rfl⟩ : syracuseStep 4608035 = 6912053) B6912053
theorem B7778339 : Blo 1364501 7778339 := bstep (se 1 (by rfl) ⟨5833754, by rfl⟩ : syracuseStep 7778339 = 11667509) B11667509
theorem B2592803 : Blo 1364501 2592803 := bstep (se 1 (by rfl) ⟨1944602, by rfl⟩ : syracuseStep 2592803 = 3889205) B3889205
theorem B1945633 : Blo 1364501 1945633 := bstep (se 2 (by rfl) ⟨729612, by rfl⟩ : syracuseStep 1945633 = 1459225) B1459225
theorem B7385165 : Blo 1364501 7385165 := bstep (se 3 (by rfl) ⟨1384718, by rfl⟩ : syracuseStep 7385165 = 2769437) B2769437
theorem B1536115 : Blo 1364501 1536115 := bstep (se 1 (by rfl) ⟨1152086, by rfl⟩ : syracuseStep 1536115 = 2304173) B2304173
theorem B11079821 : Blo 1364501 11079821 := bstep (se 3 (by rfl) ⟨2077466, by rfl⟩ : syracuseStep 11079821 = 4154933) B4154933
theorem B1970401 : Blo 1364501 1970401 := bstep (se 2 (by rfl) ⟨738900, by rfl⟩ : syracuseStep 1970401 = 1477801) B1477801
theorem B1536259 : Blo 1364501 1536259 := bstep (se 1 (by rfl) ⟨1152194, by rfl⟩ : syracuseStep 1536259 = 2304389) B2304389
theorem B6230285 : Blo 1364501 6230285 := bstep (se 3 (by rfl) ⟨1168178, by rfl⟩ : syracuseStep 6230285 = 2336357) B2336357
theorem B4608305 : Blo 1364501 4608305 := bstep (se 2 (by rfl) ⟨1728114, by rfl⟩ : syracuseStep 4608305 = 3456229) B3456229
theorem B4149571 : Blo 1364501 4149571 := bstep (se 1 (by rfl) ⟨3112178, by rfl⟩ : syracuseStep 4149571 = 6224357) B6224357
theorem B3690851 : Blo 1364501 3690851 := bstep (se 1 (by rfl) ⟨2768138, by rfl⟩ : syracuseStep 3690851 = 5536277) B5536277
theorem B3887473 : Blo 1364501 3887473 := bstep (se 2 (by rfl) ⟨1457802, by rfl⟩ : syracuseStep 3887473 = 2915605) B2915605
theorem B1536403 : Blo 1364501 1536403 := bstep (se 1 (by rfl) ⟨1152302, by rfl⟩ : syracuseStep 1536403 = 2304605) B2304605
theorem B2077139 : Blo 1364501 2077139 := bstep (se 1 (by rfl) ⟨1557854, by rfl⟩ : syracuseStep 2077139 = 3115709) B3115709
theorem B7885297 : Blo 1364501 7885297 := bstep (se 2 (by rfl) ⟨2956986, by rfl⟩ : syracuseStep 7885297 = 5913973) B5913973
theorem B3281411 : Blo 1364501 3281411 := bstep (se 1 (by rfl) ⟨2461058, by rfl⟩ : syracuseStep 3281411 = 4922117) B4922117
theorem B3691025 : Blo 1364501 3691025 := bstep (se 2 (by rfl) ⟨1384134, by rfl⟩ : syracuseStep 3691025 = 2768269) B2768269
theorem B1364515 : Blo 1364501 1364515 := bstep (se 1 (by rfl) ⟨1023386, by rfl⟩ : syracuseStep 1364515 = 2046773) B2046773
theorem B1536547 : Blo 1364501 1536547 := bstep (se 1 (by rfl) ⟨1152410, by rfl⟩ : syracuseStep 1536547 = 2304821) B2304821
theorem B1364531 : Blo 1364501 1364531 := bstep (se 1 (by rfl) ⟨1023398, by rfl⟩ : syracuseStep 1364531 = 2046797) B2046797
theorem B1364547 : Blo 1364501 1364547 := bstep (se 1 (by rfl) ⟨1023410, by rfl⟩ : syracuseStep 1364547 = 2046821) B2046821
theorem B1364563 : Blo 1364501 1364563 := bstep (se 1 (by rfl) ⟨1023422, by rfl⟩ : syracuseStep 1364563 = 2046845) B2046845
theorem B1364579 : Blo 1364501 1364579 := bstep (se 1 (by rfl) ⟨1023434, by rfl⟩ : syracuseStep 1364579 = 2046869) B2046869
theorem B1364595 : Blo 1364501 1364595 := bstep (se 1 (by rfl) ⟨1023446, by rfl⟩ : syracuseStep 1364595 = 2046893) B2046893
theorem B1364611 : Blo 1364501 1364611 := bstep (se 1 (by rfl) ⟨1023458, by rfl⟩ : syracuseStep 1364611 = 2046917) B2046917
theorem B3887747 : Blo 1364501 3887747 := bstep (se 1 (by rfl) ⟨2915810, by rfl⟩ : syracuseStep 3887747 = 5831621) B5831621
theorem B1364627 : Blo 1364501 1364627 := bstep (se 1 (by rfl) ⟨1023470, by rfl⟩ : syracuseStep 1364627 = 2046941) B2046941
theorem B1364643 : Blo 1364501 1364643 := bstep (se 1 (by rfl) ⟨1023482, by rfl⟩ : syracuseStep 1364643 = 2046965) B2046965
theorem B1364659 : Blo 1364501 1364659 := bstep (se 1 (by rfl) ⟨1023494, by rfl⟩ : syracuseStep 1364659 = 2046989) B2046989
theorem B1536691 : Blo 1364501 1536691 := bstep (se 1 (by rfl) ⟨1152518, by rfl⟩ : syracuseStep 1536691 = 2305037) B2305037
theorem B1364675 : Blo 1364501 1364675 := bstep (se 1 (by rfl) ⟨1023506, by rfl⟩ : syracuseStep 1364675 = 2047013) B2047013
theorem B5182157 : Blo 1364501 5182157 := bstep (se 3 (by rfl) ⟨971654, by rfl⟩ : syracuseStep 5182157 = 1943309) B1943309
theorem B1364691 : Blo 1364501 1364691 := bstep (se 1 (by rfl) ⟨1023518, by rfl⟩ : syracuseStep 1364691 = 2047037) B2047037
theorem B1364707 : Blo 1364501 1364707 := bstep (se 1 (by rfl) ⟨1023530, by rfl⟩ : syracuseStep 1364707 = 2047061) B2047061
theorem B5829347 : Blo 1364501 5829347 := bstep (se 1 (by rfl) ⟨4372010, by rfl⟩ : syracuseStep 5829347 = 8744021) B8744021
theorem B1364723 : Blo 1364501 1364723 := bstep (se 1 (by rfl) ⟨1023542, by rfl⟩ : syracuseStep 1364723 = 2047085) B2047085
theorem B4150019 : Blo 1364501 4150019 := bstep (se 1 (by rfl) ⟨3112514, by rfl⟩ : syracuseStep 4150019 = 6225029) B6225029
theorem B1364739 : Blo 1364501 1364739 := bstep (se 1 (by rfl) ⟨1023554, by rfl⟩ : syracuseStep 1364739 = 2047109) B2047109
theorem B1364755 : Blo 1364501 1364755 := bstep (se 1 (by rfl) ⟨1023566, by rfl⟩ : syracuseStep 1364755 = 2047133) B2047133
theorem B1364771 : Blo 1364501 1364771 := bstep (se 1 (by rfl) ⟨1023578, by rfl⟩ : syracuseStep 1364771 = 2047157) B2047157
theorem B1364787 : Blo 1364501 1364787 := bstep (se 1 (by rfl) ⟨1023590, by rfl⟩ : syracuseStep 1364787 = 2047181) B2047181
theorem B1364803 : Blo 1364501 1364803 := bstep (se 1 (by rfl) ⟨1023602, by rfl⟩ : syracuseStep 1364803 = 2047205) B2047205
theorem B3887939 : Blo 1364501 3887939 := bstep (se 1 (by rfl) ⟨2915954, by rfl⟩ : syracuseStep 3887939 = 5831909) B5831909
theorem B1536835 : Blo 1364501 1536835 := bstep (se 1 (by rfl) ⟨1152626, by rfl⟩ : syracuseStep 1536835 = 2305253) B2305253
theorem B4608845 : Blo 1364501 4608845 := bstep (se 3 (by rfl) ⟨864158, by rfl⟩ : syracuseStep 4608845 = 1728317) B1728317
theorem B1364819 : Blo 1364501 1364819 := bstep (se 1 (by rfl) ⟨1023614, by rfl⟩ : syracuseStep 1364819 = 2047229) B2047229
theorem B1364835 : Blo 1364501 1364835 := bstep (se 1 (by rfl) ⟨1023626, by rfl⟩ : syracuseStep 1364835 = 2047253) B2047253
theorem B17486705 : Blo 1364501 17486705 := bstep (se 2 (by rfl) ⟨6557514, by rfl⟩ : syracuseStep 17486705 = 13115029) B13115029
theorem B6746993 : Blo 1364501 6746993 := bstep (se 2 (by rfl) ⟨2530122, by rfl⟩ : syracuseStep 6746993 = 5060245) B5060245
theorem B1364851 : Blo 1364501 1364851 := bstep (se 1 (by rfl) ⟨1023638, by rfl⟩ : syracuseStep 1364851 = 2047277) B2047277
theorem B1364867 : Blo 1364501 1364867 := bstep (se 1 (by rfl) ⟨1023650, by rfl⟩ : syracuseStep 1364867 = 2047301) B2047301
theorem B4608899 : Blo 1364501 4608899 := bstep (se 1 (by rfl) ⟨3456674, by rfl⟩ : syracuseStep 4608899 = 6913349) B6913349
theorem B1364883 : Blo 1364501 1364883 := bstep (se 1 (by rfl) ⟨1023662, by rfl⟩ : syracuseStep 1364883 = 2047325) B2047325
theorem B1364899 : Blo 1364501 1364899 := bstep (se 1 (by rfl) ⟨1023674, by rfl⟩ : syracuseStep 1364899 = 2047349) B2047349
theorem B1364915 : Blo 1364501 1364915 := bstep (se 1 (by rfl) ⟨1023686, by rfl⟩ : syracuseStep 1364915 = 2047373) B2047373
theorem B1364931 : Blo 1364501 1364931 := bstep (se 1 (by rfl) ⟨1023698, by rfl⟩ : syracuseStep 1364931 = 2047397) B2047397
theorem B9843653 : Blo 1364501 9843653 := bstep (se 4 (by rfl) ⟨922842, by rfl⟩ : syracuseStep 9843653 = 1845685) B1845685
theorem B1364947 : Blo 1364501 1364947 := bstep (se 1 (by rfl) ⟨1023710, by rfl⟩ : syracuseStep 1364947 = 2047421) B2047421
theorem B1536979 : Blo 1364501 1536979 := bstep (se 1 (by rfl) ⟨1152734, by rfl⟩ : syracuseStep 1536979 = 2305469) B2305469
theorem B1364963 : Blo 1364501 1364963 := bstep (se 1 (by rfl) ⟨1023722, by rfl⟩ : syracuseStep 1364963 = 2047445) B2047445
theorem B1364979 : Blo 1364501 1364979 := bstep (se 1 (by rfl) ⟨1023734, by rfl⟩ : syracuseStep 1364979 = 2047469) B2047469
theorem B1364995 : Blo 1364501 1364995 := bstep (se 1 (by rfl) ⟨1023746, by rfl⟩ : syracuseStep 1364995 = 2047493) B2047493
theorem B7779341 : Blo 1364501 7779341 := bstep (se 3 (by rfl) ⟨1458626, by rfl⟩ : syracuseStep 7779341 = 2917253) B2917253
theorem B1365011 : Blo 1364501 1365011 := bstep (se 1 (by rfl) ⟨1023758, by rfl⟩ : syracuseStep 1365011 = 2047517) B2047517
theorem B8746019 : Blo 1364501 8746019 := bstep (se 1 (by rfl) ⟨6559514, by rfl⟩ : syracuseStep 8746019 = 13119029) B13119029
theorem B1365027 : Blo 1364501 1365027 := bstep (se 1 (by rfl) ⟨1023770, by rfl⟩ : syracuseStep 1365027 = 2047541) B2047541
theorem B1365043 : Blo 1364501 1365043 := bstep (se 1 (by rfl) ⟨1023782, by rfl⟩ : syracuseStep 1365043 = 2047565) B2047565
theorem B1365059 : Blo 1364501 1365059 := bstep (se 1 (by rfl) ⟨1023794, by rfl⟩ : syracuseStep 1365059 = 2047589) B2047589
theorem B3281987 : Blo 1364501 3281987 := bstep (se 1 (by rfl) ⟨2461490, by rfl⟩ : syracuseStep 3281987 = 4922981) B4922981
theorem B2593873 : Blo 1364501 2593873 := bstep (se 2 (by rfl) ⟨972702, by rfl⟩ : syracuseStep 2593873 = 1945405) B1945405
theorem B1365075 : Blo 1364501 1365075 := bstep (se 1 (by rfl) ⟨1023806, by rfl⟩ : syracuseStep 1365075 = 2047613) B2047613
theorem B1365091 : Blo 1364501 1365091 := bstep (se 1 (by rfl) ⟨1023818, by rfl⟩ : syracuseStep 1365091 = 2047637) B2047637
theorem B1537123 : Blo 1364501 1537123 := bstep (se 1 (by rfl) ⟨1152842, by rfl⟩ : syracuseStep 1537123 = 2305685) B2305685
theorem B4150385 : Blo 1364501 4150385 := bstep (se 2 (by rfl) ⟨1556394, by rfl⟩ : syracuseStep 4150385 = 3112789) B3112789
theorem B1365107 : Blo 1364501 1365107 := bstep (se 1 (by rfl) ⟨1023830, by rfl⟩ : syracuseStep 1365107 = 2047661) B2047661
theorem B1365123 : Blo 1364501 1365123 := bstep (se 1 (by rfl) ⟨1023842, by rfl⟩ : syracuseStep 1365123 = 2047685) B2047685
theorem B4609169 : Blo 1364501 4609169 := bstep (se 2 (by rfl) ⟨1728438, by rfl⟩ : syracuseStep 4609169 = 3456877) B3456877
theorem B3282065 : Blo 1364501 3282065 := bstep (se 2 (by rfl) ⟨1230774, by rfl⟩ : syracuseStep 3282065 = 2461549) B2461549
theorem B1365139 : Blo 1364501 1365139 := bstep (se 1 (by rfl) ⟨1023854, by rfl⟩ : syracuseStep 1365139 = 2047709) B2047709
theorem B1365155 : Blo 1364501 1365155 := bstep (se 1 (by rfl) ⟨1023866, by rfl⟩ : syracuseStep 1365155 = 2047733) B2047733
theorem B1365171 : Blo 1364501 1365171 := bstep (se 1 (by rfl) ⟨1023878, by rfl⟩ : syracuseStep 1365171 = 2047757) B2047757
theorem B1365187 : Blo 1364501 1365187 := bstep (se 1 (by rfl) ⟨1023890, by rfl⟩ : syracuseStep 1365187 = 2047781) B2047781
theorem B1365203 : Blo 1364501 1365203 := bstep (se 1 (by rfl) ⟨1023902, by rfl⟩ : syracuseStep 1365203 = 2047805) B2047805
theorem B1365219 : Blo 1364501 1365219 := bstep (se 1 (by rfl) ⟨1023914, by rfl⟩ : syracuseStep 1365219 = 2047829) B2047829
theorem B1365235 : Blo 1364501 1365235 := bstep (se 1 (by rfl) ⟨1023926, by rfl⟩ : syracuseStep 1365235 = 2047853) B2047853
theorem B1537267 : Blo 1364501 1537267 := bstep (se 1 (by rfl) ⟨1152950, by rfl⟩ : syracuseStep 1537267 = 2305901) B2305901
theorem B1365251 : Blo 1364501 1365251 := bstep (se 1 (by rfl) ⟨1023938, by rfl⟩ : syracuseStep 1365251 = 2047877) B2047877
theorem B1365267 : Blo 1364501 1365267 := bstep (se 1 (by rfl) ⟨1023950, by rfl⟩ : syracuseStep 1365267 = 2047901) B2047901
theorem B1365283 : Blo 1364501 1365283 := bstep (se 1 (by rfl) ⟨1023962, by rfl⟩ : syracuseStep 1365283 = 2047925) B2047925
theorem B1365299 : Blo 1364501 1365299 := bstep (se 1 (by rfl) ⟨1023974, by rfl⟩ : syracuseStep 1365299 = 2047949) B2047949
theorem B1365315 : Blo 1364501 1365315 := bstep (se 1 (by rfl) ⟨1023986, by rfl⟩ : syracuseStep 1365315 = 2047973) B2047973
theorem B4371779 : Blo 1364501 4371779 := bstep (se 1 (by rfl) ⟨3278834, by rfl⟩ : syracuseStep 4371779 = 6557669) B6557669
theorem B3282257 : Blo 1364501 3282257 := bstep (se 2 (by rfl) ⟨1230846, by rfl⟩ : syracuseStep 3282257 = 2461693) B2461693
theorem B1365331 : Blo 1364501 1365331 := bstep (se 1 (by rfl) ⟨1023998, by rfl⟩ : syracuseStep 1365331 = 2047997) B2047997
theorem B1365347 : Blo 1364501 1365347 := bstep (se 1 (by rfl) ⟨1024010, by rfl⟩ : syracuseStep 1365347 = 2048021) B2048021
theorem B1365363 : Blo 1364501 1365363 := bstep (se 1 (by rfl) ⟨1024022, by rfl⟩ : syracuseStep 1365363 = 2048045) B2048045
theorem B1365379 : Blo 1364501 1365379 := bstep (se 1 (by rfl) ⟨1024034, by rfl⟩ : syracuseStep 1365379 = 2048069) B2048069
theorem B11670925 : Blo 1364501 11670925 := bstep (se 3 (by rfl) ⟨2188298, by rfl⟩ : syracuseStep 11670925 = 4376597) B4376597
theorem B1365395 : Blo 1364501 1365395 := bstep (se 1 (by rfl) ⟨1024046, by rfl⟩ : syracuseStep 1365395 = 2048093) B2048093
theorem B2217377 : Blo 1364501 2217377 := bstep (se 2 (by rfl) ⟨831516, by rfl⟩ : syracuseStep 2217377 = 1663033) B1663033
theorem B1365411 : Blo 1364501 1365411 := bstep (se 1 (by rfl) ⟨1024058, by rfl⟩ : syracuseStep 1365411 = 2048117) B2048117
theorem B1365427 : Blo 1364501 1365427 := bstep (se 1 (by rfl) ⟨1024070, by rfl⟩ : syracuseStep 1365427 = 2048141) B2048141
theorem B1365443 : Blo 1364501 1365443 := bstep (se 1 (by rfl) ⟨1024082, by rfl⟩ : syracuseStep 1365443 = 2048165) B2048165
theorem B1365459 : Blo 1364501 1365459 := bstep (se 1 (by rfl) ⟨1024094, by rfl⟩ : syracuseStep 1365459 = 2048189) B2048189
theorem B1365475 : Blo 1364501 1365475 := bstep (se 1 (by rfl) ⟨1024106, by rfl⟩ : syracuseStep 1365475 = 2048213) B2048213
theorem B8746481 : Blo 1364501 8746481 := bstep (se 2 (by rfl) ⟨3279930, by rfl⟩ : syracuseStep 8746481 = 6559861) B6559861
theorem B1365491 : Blo 1364501 1365491 := bstep (se 1 (by rfl) ⟨1024118, by rfl⟩ : syracuseStep 1365491 = 2048237) B2048237
theorem B9344497 : Blo 1364501 9344497 := bstep (se 2 (by rfl) ⟨3504186, by rfl⟩ : syracuseStep 9344497 = 7008373) B7008373
theorem B1365507 : Blo 1364501 1365507 := bstep (se 1 (by rfl) ⟨1024130, by rfl⟩ : syracuseStep 1365507 = 2048261) B2048261
theorem B1365523 : Blo 1364501 1365523 := bstep (se 1 (by rfl) ⟨1024142, by rfl⟩ : syracuseStep 1365523 = 2048285) B2048285
theorem B1365539 : Blo 1364501 1365539 := bstep (se 1 (by rfl) ⟨1024154, by rfl⟩ : syracuseStep 1365539 = 2048309) B2048309
theorem B3503665 : Blo 1364501 3503665 := bstep (se 2 (by rfl) ⟨1313874, by rfl⟩ : syracuseStep 3503665 = 2627749) B2627749
theorem B1365555 : Blo 1364501 1365555 := bstep (se 1 (by rfl) ⟨1024166, by rfl⟩ : syracuseStep 1365555 = 2048333) B2048333
theorem B1365571 : Blo 1364501 1365571 := bstep (se 1 (by rfl) ⟨1024178, by rfl⟩ : syracuseStep 1365571 = 2048357) B2048357
theorem B1365587 : Blo 1364501 1365587 := bstep (se 1 (by rfl) ⟨1024190, by rfl⟩ : syracuseStep 1365587 = 2048381) B2048381
theorem B1365603 : Blo 1364501 1365603 := bstep (se 1 (by rfl) ⟨1024202, by rfl⟩ : syracuseStep 1365603 = 2048405) B2048405
theorem B3888749 : Blo 1364501 3888749 := bstep (se 3 (by rfl) ⟨729140, by rfl⟩ : syracuseStep 3888749 = 1458281) B1458281
theorem B3282545 : Blo 1364501 3282545 := bstep (se 2 (by rfl) ⟨1230954, by rfl⟩ : syracuseStep 3282545 = 2461909) B2461909
theorem B1365619 : Blo 1364501 1365619 := bstep (se 1 (by rfl) ⟨1024214, by rfl⟩ : syracuseStep 1365619 = 2048429) B2048429
theorem B1365635 : Blo 1364501 1365635 := bstep (se 1 (by rfl) ⟨1024226, by rfl⟩ : syracuseStep 1365635 = 2048453) B2048453
theorem B3454609 : Blo 1364501 3454609 := bstep (se 2 (by rfl) ⟨1295478, by rfl⟩ : syracuseStep 3454609 = 2590957) B2590957
theorem B1365651 : Blo 1364501 1365651 := bstep (se 1 (by rfl) ⟨1024238, by rfl⟩ : syracuseStep 1365651 = 2048477) B2048477
theorem B1365667 : Blo 1364501 1365667 := bstep (se 1 (by rfl) ⟨1024250, by rfl⟩ : syracuseStep 1365667 = 2048501) B2048501
theorem B4609709 : Blo 1364501 4609709 := bstep (se 3 (by rfl) ⟨864320, by rfl⟩ : syracuseStep 4609709 = 1728641) B1728641
theorem B1365683 : Blo 1364501 1365683 := bstep (se 1 (by rfl) ⟨1024262, by rfl⟩ : syracuseStep 1365683 = 2048525) B2048525
theorem B1365699 : Blo 1364501 1365699 := bstep (se 1 (by rfl) ⟨1024274, by rfl⟩ : syracuseStep 1365699 = 2048549) B2048549
theorem B1365715 : Blo 1364501 1365715 := bstep (se 1 (by rfl) ⟨1024286, by rfl⟩ : syracuseStep 1365715 = 2048573) B2048573
theorem B1365731 : Blo 1364501 1365731 := bstep (se 1 (by rfl) ⟨1024298, by rfl⟩ : syracuseStep 1365731 = 2048597) B2048597
theorem B4609763 : Blo 1364501 4609763 := bstep (se 1 (by rfl) ⟨3457322, by rfl⟩ : syracuseStep 4609763 = 6914645) B6914645
theorem B6911729 : Blo 1364501 6911729 := bstep (se 2 (by rfl) ⟨2591898, by rfl⟩ : syracuseStep 6911729 = 5183797) B5183797
theorem B1365747 : Blo 1364501 1365747 := bstep (se 1 (by rfl) ⟨1024310, by rfl⟩ : syracuseStep 1365747 = 2048621) B2048621
theorem B1365763 : Blo 1364501 1365763 := bstep (se 1 (by rfl) ⟨1024322, by rfl⟩ : syracuseStep 1365763 = 2048645) B2048645
theorem B1365779 : Blo 1364501 1365779 := bstep (se 1 (by rfl) ⟨1024334, by rfl⟩ : syracuseStep 1365779 = 2048669) B2048669
theorem B3888931 : Blo 1364501 3888931 := bstep (se 1 (by rfl) ⟨2916698, by rfl⟩ : syracuseStep 3888931 = 5833397) B5833397
theorem B1365795 : Blo 1364501 1365795 := bstep (se 1 (by rfl) ⟨1024346, by rfl⟩ : syracuseStep 1365795 = 2048693) B2048693
theorem B1365811 : Blo 1364501 1365811 := bstep (se 1 (by rfl) ⟨1024358, by rfl⟩ : syracuseStep 1365811 = 2048717) B2048717
theorem B1365827 : Blo 1364501 1365827 := bstep (se 1 (by rfl) ⟨1024370, by rfl⟩ : syracuseStep 1365827 = 2048741) B2048741
theorem B1365843 : Blo 1364501 1365843 := bstep (se 1 (by rfl) ⟨1024382, by rfl⟩ : syracuseStep 1365843 = 2048765) B2048765
theorem B1365859 : Blo 1364501 1365859 := bstep (se 1 (by rfl) ⟨1024394, by rfl⟩ : syracuseStep 1365859 = 2048789) B2048789
theorem B1365875 : Blo 1364501 1365875 := bstep (se 1 (by rfl) ⟨1024406, by rfl⟩ : syracuseStep 1365875 = 2048813) B2048813
theorem B1365891 : Blo 1364501 1365891 := bstep (se 1 (by rfl) ⟨1024418, by rfl⟩ : syracuseStep 1365891 = 2048837) B2048837
theorem B1365907 : Blo 1364501 1365907 := bstep (se 1 (by rfl) ⟨1024430, by rfl⟩ : syracuseStep 1365907 = 2048861) B2048861
theorem B3454883 : Blo 1364501 3454883 := bstep (se 1 (by rfl) ⟨2591162, by rfl⟩ : syracuseStep 3454883 = 5182325) B5182325
theorem B1365923 : Blo 1364501 1365923 := bstep (se 1 (by rfl) ⟨1024442, by rfl⟩ : syracuseStep 1365923 = 2048885) B2048885
theorem B1365939 : Blo 1364501 1365939 := bstep (se 1 (by rfl) ⟨1024454, by rfl⟩ : syracuseStep 1365939 = 2048909) B2048909
theorem B1365955 : Blo 1364501 1365955 := bstep (se 1 (by rfl) ⟨1024466, by rfl⟩ : syracuseStep 1365955 = 2048933) B2048933
theorem B1365971 : Blo 1364501 1365971 := bstep (se 1 (by rfl) ⟨1024478, by rfl⟩ : syracuseStep 1365971 = 2048957) B2048957
theorem B1365987 : Blo 1364501 1365987 := bstep (se 1 (by rfl) ⟨1024490, by rfl⟩ : syracuseStep 1365987 = 2048981) B2048981
theorem B4610033 : Blo 1364501 4610033 := bstep (se 2 (by rfl) ⟨1728762, by rfl⟩ : syracuseStep 4610033 = 3457525) B3457525
theorem B1366003 : Blo 1364501 1366003 := bstep (se 1 (by rfl) ⟨1024502, by rfl⟩ : syracuseStep 1366003 = 2049005) B2049005
theorem B1366019 : Blo 1364501 1366019 := bstep (se 1 (by rfl) ⟨1024514, by rfl⟩ : syracuseStep 1366019 = 2049029) B2049029
theorem B1366035 : Blo 1364501 1366035 := bstep (se 1 (by rfl) ⟨1024526, by rfl⟩ : syracuseStep 1366035 = 2049053) B2049053
theorem B1366051 : Blo 1364501 1366051 := bstep (se 1 (by rfl) ⟨1024538, by rfl⟩ : syracuseStep 1366051 = 2049077) B2049077
theorem B5535793 : Blo 1364501 5535793 := bstep (se 2 (by rfl) ⟨2075922, by rfl⟩ : syracuseStep 5535793 = 4151845) B4151845
theorem B1366067 : Blo 1364501 1366067 := bstep (se 1 (by rfl) ⟨1024550, by rfl⟩ : syracuseStep 1366067 = 2049101) B2049101
theorem B14956597 : Blo 1364501 14956597 := bstep (se 5 (by rfl) ⟨701090, by rfl⟩ : syracuseStep 14956597 = 1402181) B1402181
theorem B1366083 : Blo 1364501 1366083 := bstep (se 1 (by rfl) ⟨1024562, by rfl⟩ : syracuseStep 1366083 = 2049125) B2049125
theorem B1366099 : Blo 1364501 1366099 := bstep (se 1 (by rfl) ⟨1024574, by rfl⟩ : syracuseStep 1366099 = 2049149) B2049149
theorem B3455075 : Blo 1364501 3455075 := bstep (se 1 (by rfl) ⟨2591306, by rfl⟩ : syracuseStep 3455075 = 5182613) B5182613
theorem B1366115 : Blo 1364501 1366115 := bstep (se 1 (by rfl) ⟨1024586, by rfl⟩ : syracuseStep 1366115 = 2049173) B2049173
theorem B2914417 : Blo 1364501 2914417 := bstep (se 2 (by rfl) ⟨1092906, by rfl⟩ : syracuseStep 2914417 = 2185813) B2185813
theorem B1366131 : Blo 1364501 1366131 := bstep (se 1 (by rfl) ⟨1024598, by rfl⟩ : syracuseStep 1366131 = 2049197) B2049197
theorem B1366147 : Blo 1364501 1366147 := bstep (se 1 (by rfl) ⟨1024610, by rfl⟩ : syracuseStep 1366147 = 2049221) B2049221
theorem B1366163 : Blo 1364501 1366163 := bstep (se 1 (by rfl) ⟨1024622, by rfl⟩ : syracuseStep 1366163 = 2049245) B2049245
theorem B1366179 : Blo 1364501 1366179 := bstep (se 1 (by rfl) ⟨1024634, by rfl⟩ : syracuseStep 1366179 = 2049269) B2049269
theorem B1366195 : Blo 1364501 1366195 := bstep (se 1 (by rfl) ⟨1024646, by rfl⟩ : syracuseStep 1366195 = 2049293) B2049293
theorem B1366211 : Blo 1364501 1366211 := bstep (se 1 (by rfl) ⟨1024658, by rfl⟩ : syracuseStep 1366211 = 2049317) B2049317
theorem B1366227 : Blo 1364501 1366227 := bstep (se 1 (by rfl) ⟨1024670, by rfl⟩ : syracuseStep 1366227 = 2049341) B2049341
theorem B1366243 : Blo 1364501 1366243 := bstep (se 1 (by rfl) ⟨1024682, by rfl⟩ : syracuseStep 1366243 = 2049365) B2049365
theorem B1366259 : Blo 1364501 1366259 := bstep (se 1 (by rfl) ⟨1024694, by rfl⟩ : syracuseStep 1366259 = 2049389) B2049389
theorem B1366275 : Blo 1364501 1366275 := bstep (se 1 (by rfl) ⟨1024706, by rfl⟩ : syracuseStep 1366275 = 2049413) B2049413
theorem B3889421 : Blo 1364501 3889421 := bstep (se 3 (by rfl) ⟨729266, by rfl⟩ : syracuseStep 3889421 = 1458533) B1458533
theorem B1366291 : Blo 1364501 1366291 := bstep (se 1 (by rfl) ⟨1024718, by rfl⟩ : syracuseStep 1366291 = 2049437) B2049437
theorem B1366307 : Blo 1364501 1366307 := bstep (se 1 (by rfl) ⟨1024730, by rfl⟩ : syracuseStep 1366307 = 2049461) B2049461
theorem B1366323 : Blo 1364501 1366323 := bstep (se 1 (by rfl) ⟨1024742, by rfl⟩ : syracuseStep 1366323 = 2049485) B2049485
theorem B1366339 : Blo 1364501 1366339 := bstep (se 1 (by rfl) ⟨1024754, by rfl⟩ : syracuseStep 1366339 = 2049509) B2049509
theorem B1366355 : Blo 1364501 1366355 := bstep (se 1 (by rfl) ⟨1024766, by rfl⟩ : syracuseStep 1366355 = 2049533) B2049533
theorem B1366371 : Blo 1364501 1366371 := bstep (se 1 (by rfl) ⟨1024778, by rfl⟩ : syracuseStep 1366371 = 2049557) B2049557
theorem B3938669 : Blo 1364501 3938669 := bstep (se 3 (by rfl) ⟨738500, by rfl⟩ : syracuseStep 3938669 = 1477001) B1477001
theorem B1366387 : Blo 1364501 1366387 := bstep (se 1 (by rfl) ⟨1024790, by rfl⟩ : syracuseStep 1366387 = 2049581) B2049581
theorem B1366403 : Blo 1364501 1366403 := bstep (se 1 (by rfl) ⟨1024802, by rfl⟩ : syracuseStep 1366403 = 2049605) B2049605
theorem B1366419 : Blo 1364501 1366419 := bstep (se 1 (by rfl) ⟨1024814, by rfl⟩ : syracuseStep 1366419 = 2049629) B2049629
theorem B1366435 : Blo 1364501 1366435 := bstep (se 1 (by rfl) ⟨1024826, by rfl⟩ : syracuseStep 1366435 = 2049653) B2049653
theorem B3070385 : Blo 1364501 3070385 := bstep (se 2 (by rfl) ⟨1151394, by rfl⟩ : syracuseStep 3070385 = 2302789) B2302789
theorem B1366451 : Blo 1364501 1366451 := bstep (se 1 (by rfl) ⟨1024838, by rfl⟩ : syracuseStep 1366451 = 2049677) B2049677
theorem B3070403 : Blo 1364501 3070403 := bstep (se 1 (by rfl) ⟨2302802, by rfl⟩ : syracuseStep 3070403 = 4605605) B4605605
theorem B1366467 : Blo 1364501 1366467 := bstep (se 1 (by rfl) ⟨1024850, by rfl⟩ : syracuseStep 1366467 = 2049701) B2049701
theorem B1366483 : Blo 1364501 1366483 := bstep (se 1 (by rfl) ⟨1024862, by rfl⟩ : syracuseStep 1366483 = 2049725) B2049725
theorem B4733411 : Blo 1364501 4733411 := bstep (se 1 (by rfl) ⟨3550058, by rfl⟩ : syracuseStep 4733411 = 7100117) B7100117
theorem B1366499 : Blo 1364501 1366499 := bstep (se 1 (by rfl) ⟨1024874, by rfl⟩ : syracuseStep 1366499 = 2049749) B2049749
theorem B4610573 : Blo 1364501 4610573 := bstep (se 3 (by rfl) ⟨864482, by rfl⟩ : syracuseStep 4610573 = 1728965) B1728965
theorem B1727011 : Blo 1364501 1727011 := bstep (se 1 (by rfl) ⟨1295258, by rfl⟩ : syracuseStep 1727011 = 2590517) B2590517
theorem B4610627 : Blo 1364501 4610627 := bstep (se 1 (by rfl) ⟨3457970, by rfl⟩ : syracuseStep 4610627 = 6915941) B6915941
theorem B2767459 : Blo 1364501 2767459 := bstep (se 1 (by rfl) ⟨2075594, by rfl⟩ : syracuseStep 2767459 = 4151189) B4151189
theorem B2767555 : Blo 1364501 2767555 := bstep (se 1 (by rfl) ⟨2075666, by rfl⟩ : syracuseStep 2767555 = 4151333) B4151333
theorem B11672261 : Blo 1364501 11672261 := bstep (se 4 (by rfl) ⟨1094274, by rfl⟩ : syracuseStep 11672261 = 2188549) B2188549
theorem B3070673 : Blo 1364501 3070673 := bstep (se 2 (by rfl) ⟨1151502, by rfl⟩ : syracuseStep 3070673 = 2303005) B2303005
theorem B3070691 : Blo 1364501 3070691 := bstep (se 1 (by rfl) ⟨2303018, by rfl⟩ : syracuseStep 3070691 = 4606037) B4606037
theorem B5184269 : Blo 1364501 5184269 := bstep (se 3 (by rfl) ⟨972050, by rfl⟩ : syracuseStep 5184269 = 1944101) B1944101
theorem B2046755 : Blo 1364501 2046755 := bstep (se 1 (by rfl) ⟨1535066, by rfl⟩ : syracuseStep 2046755 = 3070133) B3070133
theorem B2046785 : Blo 1364501 2046785 := bstep (se 2 (by rfl) ⟨767544, by rfl⟩ : syracuseStep 2046785 = 1535089) B1535089
theorem B3324739 : Blo 1364501 3324739 := bstep (se 1 (by rfl) ⟨2493554, by rfl⟩ : syracuseStep 3324739 = 4987109) B4987109
theorem B17488709 : Blo 1364501 17488709 := bstep (se 4 (by rfl) ⟨1639566, by rfl⟩ : syracuseStep 17488709 = 3279133) B3279133
theorem B4610897 : Blo 1364501 4610897 := bstep (se 2 (by rfl) ⟨1729086, by rfl⟩ : syracuseStep 4610897 = 3458173) B3458173
theorem B2046803 : Blo 1364501 2046803 := bstep (se 1 (by rfl) ⟨1535102, by rfl⟩ : syracuseStep 2046803 = 3070205) B3070205
theorem B2046833 : Blo 1364501 2046833 := bstep (se 2 (by rfl) ⟨767562, by rfl⟩ : syracuseStep 2046833 = 1535125) B1535125
theorem B4799345 : Blo 1364501 4799345 := bstep (se 2 (by rfl) ⟨1799754, by rfl⟩ : syracuseStep 4799345 = 3599509) B3599509
theorem B2046851 : Blo 1364501 2046851 := bstep (se 1 (by rfl) ⟨1535138, by rfl⟩ : syracuseStep 2046851 = 3070277) B3070277
theorem B2915203 : Blo 1364501 2915203 := bstep (se 1 (by rfl) ⟨2186402, by rfl⟩ : syracuseStep 2915203 = 4372805) B4372805
theorem B2046881 : Blo 1364501 2046881 := bstep (se 2 (by rfl) ⟨767580, by rfl⟩ : syracuseStep 2046881 = 1535161) B1535161
theorem B2046899 : Blo 1364501 2046899 := bstep (se 1 (by rfl) ⟨1535174, by rfl⟩ : syracuseStep 2046899 = 3070349) B3070349
theorem B4152259 : Blo 1364501 4152259 := bstep (se 1 (by rfl) ⟨3114194, by rfl⟩ : syracuseStep 4152259 = 6228389) B6228389
theorem B2046929 : Blo 1364501 2046929 := bstep (se 2 (by rfl) ⟨767598, by rfl⟩ : syracuseStep 2046929 = 1535197) B1535197
theorem B1457123 : Blo 1364501 1457123 := bstep (se 1 (by rfl) ⟨1092842, by rfl⟩ : syracuseStep 1457123 = 2185685) B2185685
theorem B2046947 : Blo 1364501 2046947 := bstep (se 1 (by rfl) ⟨1535210, by rfl⟩ : syracuseStep 2046947 = 3070421) B3070421
theorem B3070961 : Blo 1364501 3070961 := bstep (se 2 (by rfl) ⟨1151610, by rfl⟩ : syracuseStep 3070961 = 2303221) B2303221
theorem B10517489 : Blo 1364501 10517489 := bstep (se 2 (by rfl) ⟨3944058, by rfl⟩ : syracuseStep 10517489 = 7888117) B7888117
theorem B2046977 : Blo 1364501 2046977 := bstep (se 2 (by rfl) ⟨767616, by rfl⟩ : syracuseStep 2046977 = 1535233) B1535233
theorem B3070979 : Blo 1364501 3070979 := bstep (se 1 (by rfl) ⟨2303234, by rfl⟩ : syracuseStep 3070979 = 4606469) B4606469
theorem B3456017 : Blo 1364501 3456017 := bstep (se 2 (by rfl) ⟨1296006, by rfl⟩ : syracuseStep 3456017 = 2592013) B2592013
theorem B2046995 : Blo 1364501 2046995 := bstep (se 1 (by rfl) ⟨1535246, by rfl⟩ : syracuseStep 2046995 = 3070493) B3070493
theorem B1727507 : Blo 1364501 1727507 := bstep (se 1 (by rfl) ⟨1295630, by rfl⟩ : syracuseStep 1727507 = 2591261) B2591261
theorem B2047025 : Blo 1364501 2047025 := bstep (se 2 (by rfl) ⟨767634, by rfl⟩ : syracuseStep 2047025 = 1535269) B1535269
theorem B2047043 : Blo 1364501 2047043 := bstep (se 1 (by rfl) ⟨1535282, by rfl⟩ : syracuseStep 2047043 = 3070565) B3070565
theorem B3456067 : Blo 1364501 3456067 := bstep (se 1 (by rfl) ⟨2592050, by rfl⟩ : syracuseStep 3456067 = 5184101) B5184101
theorem B2047073 : Blo 1364501 2047073 := bstep (se 2 (by rfl) ⟨767652, by rfl⟩ : syracuseStep 2047073 = 1535305) B1535305
theorem B2047091 : Blo 1364501 2047091 := bstep (se 1 (by rfl) ⟨1535318, by rfl⟩ : syracuseStep 2047091 = 3070637) B3070637
theorem B2047121 : Blo 1364501 2047121 := bstep (se 2 (by rfl) ⟨767670, by rfl⟩ : syracuseStep 2047121 = 1535341) B1535341
theorem B2047139 : Blo 1364501 2047139 := bstep (se 1 (by rfl) ⟨1535354, by rfl⟩ : syracuseStep 2047139 = 3070709) B3070709
theorem B6913187 : Blo 1364501 6913187 := bstep (se 1 (by rfl) ⟨5184890, by rfl⟩ : syracuseStep 6913187 = 10369781) B10369781
theorem B2047169 : Blo 1364501 2047169 := bstep (se 2 (by rfl) ⟨767688, by rfl⟩ : syracuseStep 2047169 = 1535377) B1535377
theorem B3456209 : Blo 1364501 3456209 := bstep (se 2 (by rfl) ⟨1296078, by rfl⟩ : syracuseStep 3456209 = 2592157) B2592157
theorem B2047187 : Blo 1364501 2047187 := bstep (se 1 (by rfl) ⟨1535390, by rfl⟩ : syracuseStep 2047187 = 3070781) B3070781
theorem B2047217 : Blo 1364501 2047217 := bstep (se 2 (by rfl) ⟨767706, by rfl⟩ : syracuseStep 2047217 = 1535413) B1535413
theorem B2047235 : Blo 1364501 2047235 := bstep (se 1 (by rfl) ⟨1535426, by rfl⟩ : syracuseStep 2047235 = 3070853) B3070853
theorem B3071249 : Blo 1364501 3071249 := bstep (se 2 (by rfl) ⟨1151718, by rfl⟩ : syracuseStep 3071249 = 2303437) B2303437
theorem B2047265 : Blo 1364501 2047265 := bstep (se 2 (by rfl) ⟨767724, by rfl⟩ : syracuseStep 2047265 = 1535449) B1535449
theorem B3071267 : Blo 1364501 3071267 := bstep (se 1 (by rfl) ⟨2303450, by rfl⟩ : syracuseStep 3071267 = 4606901) B4606901
theorem B2186531 : Blo 1364501 2186531 := bstep (se 1 (by rfl) ⟨1639898, by rfl⟩ : syracuseStep 2186531 = 3279797) B3279797
theorem B2047283 : Blo 1364501 2047283 := bstep (se 1 (by rfl) ⟨1535462, by rfl⟩ : syracuseStep 2047283 = 3070925) B3070925
theorem B7773509 : Blo 1364501 7773509 := bstep (se 4 (by rfl) ⟨728766, by rfl⟩ : syracuseStep 7773509 = 1457533) B1457533
theorem B2047313 : Blo 1364501 2047313 := bstep (se 2 (by rfl) ⟨767742, by rfl⟩ : syracuseStep 2047313 = 1535485) B1535485
theorem B2047331 : Blo 1364501 2047331 := bstep (se 1 (by rfl) ⟨1535498, by rfl⟩ : syracuseStep 2047331 = 3070997) B3070997
theorem B4611437 : Blo 1364501 4611437 := bstep (se 3 (by rfl) ⟨864644, by rfl⟩ : syracuseStep 4611437 = 1729289) B1729289
theorem B2047361 : Blo 1364501 2047361 := bstep (se 2 (by rfl) ⟨767760, by rfl⟩ : syracuseStep 2047361 = 1535521) B1535521
theorem B4152721 : Blo 1364501 4152721 := bstep (se 2 (by rfl) ⟨1557270, by rfl⟩ : syracuseStep 4152721 = 3114541) B3114541
theorem B2047379 : Blo 1364501 2047379 := bstep (se 1 (by rfl) ⟨1535534, by rfl⟩ : syracuseStep 2047379 = 3071069) B3071069
theorem B4611491 : Blo 1364501 4611491 := bstep (se 1 (by rfl) ⟨3458618, by rfl⟩ : syracuseStep 4611491 = 6917237) B6917237
theorem B3890605 : Blo 1364501 3890605 := bstep (se 3 (by rfl) ⟨729488, by rfl⟩ : syracuseStep 3890605 = 1458977) B1458977
theorem B2047409 : Blo 1364501 2047409 := bstep (se 2 (by rfl) ⟨767778, by rfl⟩ : syracuseStep 2047409 = 1535557) B1535557
theorem B2047427 : Blo 1364501 2047427 := bstep (se 1 (by rfl) ⟨1535570, by rfl⟩ : syracuseStep 2047427 = 3071141) B3071141
theorem B2047457 : Blo 1364501 2047457 := bstep (se 2 (by rfl) ⟨767796, by rfl⟩ : syracuseStep 2047457 = 1535593) B1535593
theorem B2186723 : Blo 1364501 2186723 := bstep (se 1 (by rfl) ⟨1640042, by rfl⟩ : syracuseStep 2186723 = 3280085) B3280085
theorem B2047475 : Blo 1364501 2047475 := bstep (se 1 (by rfl) ⟨1535606, by rfl⟩ : syracuseStep 2047475 = 3071213) B3071213
theorem B2047505 : Blo 1364501 2047505 := bstep (se 2 (by rfl) ⟨767814, by rfl⟩ : syracuseStep 2047505 = 1535629) B1535629
theorem B2047523 : Blo 1364501 2047523 := bstep (se 1 (by rfl) ⟨1535642, by rfl⟩ : syracuseStep 2047523 = 3071285) B3071285
theorem B4496941 : Blo 1364501 4496941 := bstep (se 3 (by rfl) ⟨843176, by rfl⟩ : syracuseStep 4496941 = 1686353) B1686353
theorem B3071537 : Blo 1364501 3071537 := bstep (se 2 (by rfl) ⟨1151826, by rfl⟩ : syracuseStep 3071537 = 2303653) B2303653
theorem B5185073 : Blo 1364501 5185073 := bstep (se 2 (by rfl) ⟨1944402, by rfl⟩ : syracuseStep 5185073 = 3888805) B3888805
theorem B2047553 : Blo 1364501 2047553 := bstep (se 2 (by rfl) ⟨767832, by rfl⟩ : syracuseStep 2047553 = 1535665) B1535665
theorem B3071555 : Blo 1364501 3071555 := bstep (se 1 (by rfl) ⟨2303666, by rfl⟩ : syracuseStep 3071555 = 4607333) B4607333
theorem B2915921 : Blo 1364501 2915921 := bstep (se 2 (by rfl) ⟨1093470, by rfl⟩ : syracuseStep 2915921 = 2186941) B2186941
theorem B2047571 : Blo 1364501 2047571 := bstep (se 1 (by rfl) ⟨1535678, by rfl⟩ : syracuseStep 2047571 = 3071357) B3071357
theorem B2047601 : Blo 1364501 2047601 := bstep (se 2 (by rfl) ⟨767850, by rfl⟩ : syracuseStep 2047601 = 1535701) B1535701
theorem B2047619 : Blo 1364501 2047619 := bstep (se 1 (by rfl) ⟨1535714, by rfl⟩ : syracuseStep 2047619 = 3071429) B3071429
theorem B2047649 : Blo 1364501 2047649 := bstep (se 2 (by rfl) ⟨767868, by rfl⟩ : syracuseStep 2047649 = 1535737) B1535737
theorem B3112625 : Blo 1364501 3112625 := bstep (se 2 (by rfl) ⟨1167234, by rfl⟩ : syracuseStep 3112625 = 2334469) B2334469
theorem B4611761 : Blo 1364501 4611761 := bstep (se 2 (by rfl) ⟨1729410, by rfl⟩ : syracuseStep 4611761 = 3458821) B3458821
theorem B2047667 : Blo 1364501 2047667 := bstep (se 1 (by rfl) ⟨1535750, by rfl⟩ : syracuseStep 2047667 = 3071501) B3071501
theorem B2047697 : Blo 1364501 2047697 := bstep (se 2 (by rfl) ⟨767886, by rfl⟩ : syracuseStep 2047697 = 1535773) B1535773
theorem B1457875 : Blo 1364501 1457875 := bstep (se 1 (by rfl) ⟨1093406, by rfl⟩ : syracuseStep 1457875 = 2186813) B2186813
theorem B1728211 : Blo 1364501 1728211 := bstep (se 1 (by rfl) ⟨1296158, by rfl⟩ : syracuseStep 1728211 = 2592317) B2592317
theorem B2047715 : Blo 1364501 2047715 := bstep (se 1 (by rfl) ⟨1535786, by rfl⟩ : syracuseStep 2047715 = 3071573) B3071573
theorem B2047745 : Blo 1364501 2047745 := bstep (se 2 (by rfl) ⟨767904, by rfl⟩ : syracuseStep 2047745 = 1535809) B1535809
theorem B7773965 : Blo 1364501 7773965 := bstep (se 3 (by rfl) ⟨1457618, by rfl⟩ : syracuseStep 7773965 = 2915237) B2915237
theorem B2047763 : Blo 1364501 2047763 := bstep (se 1 (by rfl) ⟨1535822, by rfl⟩ : syracuseStep 2047763 = 3071645) B3071645
theorem B2047793 : Blo 1364501 2047793 := bstep (se 2 (by rfl) ⟨767922, by rfl⟩ : syracuseStep 2047793 = 1535845) B1535845
theorem B1728307 : Blo 1364501 1728307 := bstep (se 1 (by rfl) ⟨1296230, by rfl⟩ : syracuseStep 1728307 = 2592461) B2592461
theorem B2047811 : Blo 1364501 2047811 := bstep (se 1 (by rfl) ⟨1535858, by rfl⟩ : syracuseStep 2047811 = 3071717) B3071717
theorem B4669265 : Blo 1364501 4669265 := bstep (se 2 (by rfl) ⟨1750974, by rfl⟩ : syracuseStep 4669265 = 3501949) B3501949
theorem B3071825 : Blo 1364501 3071825 := bstep (se 2 (by rfl) ⟨1151934, by rfl⟩ : syracuseStep 3071825 = 2303869) B2303869
theorem B2047841 : Blo 1364501 2047841 := bstep (se 2 (by rfl) ⟨767940, by rfl⟩ : syracuseStep 2047841 = 1535881) B1535881
theorem B3071843 : Blo 1364501 3071843 := bstep (se 1 (by rfl) ⟨2303882, by rfl⟩ : syracuseStep 3071843 = 4607765) B4607765
theorem B7782257 : Blo 1364501 7782257 := bstep (se 2 (by rfl) ⟨2918346, by rfl⟩ : syracuseStep 7782257 = 5836693) B5836693
theorem B2047859 : Blo 1364501 2047859 := bstep (se 1 (by rfl) ⟨1535894, by rfl⟩ : syracuseStep 2047859 = 3071789) B3071789
theorem B2047889 : Blo 1364501 2047889 := bstep (se 2 (by rfl) ⟨767958, by rfl⟩ : syracuseStep 2047889 = 1535917) B1535917
theorem B2047907 : Blo 1364501 2047907 := bstep (se 1 (by rfl) ⟨1535930, by rfl⟩ : syracuseStep 2047907 = 3071861) B3071861
theorem B4374445 : Blo 1364501 4374445 := bstep (se 3 (by rfl) ⟨820208, by rfl⟩ : syracuseStep 4374445 = 1640417) B1640417
theorem B2047937 : Blo 1364501 2047937 := bstep (se 2 (by rfl) ⟨767976, by rfl⟩ : syracuseStep 2047937 = 1535953) B1535953
theorem B6913997 : Blo 1364501 6913997 := bstep (se 3 (by rfl) ⟨1296374, by rfl⟩ : syracuseStep 6913997 = 2592749) B2592749
theorem B2047955 : Blo 1364501 2047955 := bstep (se 1 (by rfl) ⟨1535966, by rfl⟩ : syracuseStep 2047955 = 3071933) B3071933
theorem B2047985 : Blo 1364501 2047985 := bstep (se 2 (by rfl) ⟨767994, by rfl⟩ : syracuseStep 2047985 = 1535989) B1535989
theorem B3072023 : Blo 1364501 3072023 := bstep (se 1 (by rfl) ⟨2304017, by rfl⟩ : syracuseStep 3072023 = 4608035) B4608035
theorem B5185559 : Blo 1364501 5185559 := bstep (se 1 (by rfl) ⟨3889169, by rfl⟩ : syracuseStep 5185559 = 7778339) B7778339
theorem B1728535 : Blo 1364501 1728535 := bstep (se 1 (by rfl) ⟨1296401, by rfl⟩ : syracuseStep 1728535 = 2592803) B2592803
theorem B4923443 : Blo 1364501 4923443 := bstep (se 1 (by rfl) ⟨3692582, by rfl⟩ : syracuseStep 4923443 = 7385165) B7385165
theorem B7004225 : Blo 1364501 7004225 := bstep (se 2 (by rfl) ⟨2626584, by rfl⟩ : syracuseStep 7004225 = 5253169) B5253169
theorem B7381057 : Blo 1364501 7381057 := bstep (se 2 (by rfl) ⟨2767896, by rfl⟩ : syracuseStep 7381057 = 5535793) B5535793
theorem B2048075 : Blo 1364501 2048075 := bstep (se 1 (by rfl) ⟨1536056, by rfl⟩ : syracuseStep 2048075 = 3072113) B3072113
theorem B2048087 : Blo 1364501 2048087 := bstep (se 1 (by rfl) ⟨1536065, by rfl⟩ : syracuseStep 2048087 = 3072131) B3072131
theorem B2048153 : Blo 1364501 2048153 := bstep (se 2 (by rfl) ⟨768057, by rfl⟩ : syracuseStep 2048153 = 1536115) B1536115
theorem B4153523 : Blo 1364501 4153523 := bstep (se 1 (by rfl) ⟨3115142, by rfl⟩ : syracuseStep 4153523 = 6230285) B6230285
theorem B3072203 : Blo 1364501 3072203 := bstep (se 1 (by rfl) ⟨2304152, by rfl⟩ : syracuseStep 3072203 = 4608305) B4608305
theorem B3072257 : Blo 1364501 3072257 := bstep (se 2 (by rfl) ⟨1152096, by rfl⟩ : syracuseStep 3072257 = 2304193) B2304193
theorem B2048267 : Blo 1364501 2048267 := bstep (se 1 (by rfl) ⟨1536200, by rfl⟩ : syracuseStep 2048267 = 3072401) B3072401
theorem B6914321 : Blo 1364501 6914321 := bstep (se 2 (by rfl) ⟨2592870, by rfl⟩ : syracuseStep 6914321 = 5185741) B5185741
theorem B2048279 : Blo 1364501 2048279 := bstep (se 1 (by rfl) ⟨1536209, by rfl⟩ : syracuseStep 2048279 = 3072419) B3072419
theorem B1384759 : Blo 1364501 1384759 := bstep (se 1 (by rfl) ⟨1038569, by rfl⟩ : syracuseStep 1384759 = 2077139) B2077139
theorem B2048345 : Blo 1364501 2048345 := bstep (se 2 (by rfl) ⟨768129, by rfl⟩ : syracuseStep 2048345 = 1536259) B1536259
theorem B6914483 : Blo 1364501 6914483 := bstep (se 1 (by rfl) ⟨5185862, by rfl⟩ : syracuseStep 6914483 = 10371725) B10371725
theorem B2048459 : Blo 1364501 2048459 := bstep (se 1 (by rfl) ⟨1536344, by rfl⟩ : syracuseStep 2048459 = 3072689) B3072689
theorem B12460493 : Blo 1364501 12460493 := bstep (se 3 (by rfl) ⟨2336342, by rfl⟩ : syracuseStep 12460493 = 4672685) B4672685
theorem B2048471 : Blo 1364501 2048471 := bstep (se 1 (by rfl) ⟨1536353, by rfl⟩ : syracuseStep 2048471 = 3072707) B3072707
theorem B3072473 : Blo 1364501 3072473 := bstep (se 2 (by rfl) ⟨1152177, by rfl⟩ : syracuseStep 3072473 = 2304355) B2304355
theorem B2048537 : Blo 1364501 2048537 := bstep (se 2 (by rfl) ⟨768201, by rfl⟩ : syracuseStep 2048537 = 1536403) B1536403
theorem B3072563 : Blo 1364501 3072563 := bstep (se 1 (by rfl) ⟨2304422, by rfl⟩ : syracuseStep 3072563 = 4608845) B4608845
theorem B11657803 : Blo 1364501 11657803 := bstep (se 1 (by rfl) ⟨8743352, by rfl⟩ : syracuseStep 11657803 = 17486705) B17486705
theorem B4497995 : Blo 1364501 4497995 := bstep (se 1 (by rfl) ⟨3373496, by rfl⟩ : syracuseStep 4497995 = 6746993) B6746993
theorem B3072599 : Blo 1364501 3072599 := bstep (se 1 (by rfl) ⟨2304449, by rfl⟩ : syracuseStep 3072599 = 4608899) B4608899
theorem B2048651 : Blo 1364501 2048651 := bstep (se 1 (by rfl) ⟨1536488, by rfl⟩ : syracuseStep 2048651 = 3072977) B3072977
theorem B2048663 : Blo 1364501 2048663 := bstep (se 1 (by rfl) ⟨1536497, by rfl⟩ : syracuseStep 2048663 = 3072995) B3072995
theorem B3457687 : Blo 1364501 3457687 := bstep (se 1 (by rfl) ⟨2593265, by rfl⟩ : syracuseStep 3457687 = 5186531) B5186531
theorem B5186227 : Blo 1364501 5186227 := bstep (se 1 (by rfl) ⟨3889670, by rfl⟩ : syracuseStep 5186227 = 7779341) B7779341
theorem B2187991 : Blo 1364501 2187991 := bstep (se 1 (by rfl) ⟨1640993, by rfl⟩ : syracuseStep 2187991 = 3281987) B3281987
theorem B2302681 : Blo 1364501 2302681 := bstep (se 2 (by rfl) ⟨863505, by rfl⟩ : syracuseStep 2302681 = 1727011) B1727011
theorem B2048729 : Blo 1364501 2048729 := bstep (se 2 (by rfl) ⟨768273, by rfl⟩ : syracuseStep 2048729 = 1536547) B1536547
theorem B3072779 : Blo 1364501 3072779 := bstep (se 1 (by rfl) ⟨2304584, by rfl⟩ : syracuseStep 3072779 = 4609169) B4609169
theorem B2188043 : Blo 1364501 2188043 := bstep (se 1 (by rfl) ⟨1641032, by rfl⟩ : syracuseStep 2188043 = 3282065) B3282065
theorem B3072833 : Blo 1364501 3072833 := bstep (se 2 (by rfl) ⟨1152312, by rfl⟩ : syracuseStep 3072833 = 2304625) B2304625
theorem B2048843 : Blo 1364501 2048843 := bstep (se 1 (by rfl) ⟨1536632, by rfl⟩ : syracuseStep 2048843 = 3073265) B3073265
theorem B2048855 : Blo 1364501 2048855 := bstep (se 1 (by rfl) ⟨1536641, by rfl⟩ : syracuseStep 2048855 = 3073283) B3073283
theorem B11658077 : Blo 1364501 11658077 := bstep (se 3 (by rfl) ⟨2185889, by rfl⟩ : syracuseStep 11658077 = 4371779) B4371779
theorem B2188171 : Blo 1364501 2188171 := bstep (se 1 (by rfl) ⟨1641128, by rfl⟩ : syracuseStep 2188171 = 3282257) B3282257
theorem B2917271 : Blo 1364501 2917271 := bstep (se 1 (by rfl) ⟨2187953, by rfl⟩ : syracuseStep 2917271 = 4375907) B4375907
theorem B2048921 : Blo 1364501 2048921 := bstep (se 2 (by rfl) ⟨768345, by rfl⟩ : syracuseStep 2048921 = 1536691) B1536691
theorem B2049035 : Blo 1364501 2049035 := bstep (se 1 (by rfl) ⟨1536776, by rfl⟩ : syracuseStep 2049035 = 3073553) B3073553
theorem B2049047 : Blo 1364501 2049047 := bstep (se 1 (by rfl) ⟨1536785, by rfl⟩ : syracuseStep 2049047 = 3073571) B3073571
theorem B3073049 : Blo 1364501 3073049 := bstep (se 2 (by rfl) ⟨1152393, by rfl⟩ : syracuseStep 3073049 = 2304787) B2304787
theorem B10363949 : Blo 1364501 10363949 := bstep (se 3 (by rfl) ⟨1943240, by rfl⟩ : syracuseStep 10363949 = 3886481) B3886481
theorem B4736075 : Blo 1364501 4736075 := bstep (se 1 (by rfl) ⟨3552056, by rfl⟩ : syracuseStep 4736075 = 7104113) B7104113
theorem B2917451 : Blo 1364501 2917451 := bstep (se 1 (by rfl) ⟨2188088, by rfl⟩ : syracuseStep 2917451 = 4376177) B4376177
theorem B3458123 : Blo 1364501 3458123 := bstep (se 1 (by rfl) ⟨2593592, by rfl⟩ : syracuseStep 3458123 = 5187185) B5187185
theorem B4432985 : Blo 1364501 4432985 := bstep (se 2 (by rfl) ⟨1662369, by rfl⟩ : syracuseStep 4432985 = 3324739) B3324739
theorem B2049113 : Blo 1364501 2049113 := bstep (se 2 (by rfl) ⟨768417, by rfl⟩ : syracuseStep 2049113 = 1536835) B1536835
theorem B16606301 : Blo 1364501 16606301 := bstep (se 3 (by rfl) ⟨3113681, by rfl⟩ : syracuseStep 16606301 = 6227363) B6227363
theorem B3073139 : Blo 1364501 3073139 := bstep (se 1 (by rfl) ⟨2304854, by rfl⟩ : syracuseStep 3073139 = 4609709) B4609709
theorem B3073175 : Blo 1364501 3073175 := bstep (se 1 (by rfl) ⟨2304881, by rfl⟩ : syracuseStep 3073175 = 4609763) B4609763
theorem B2049227 : Blo 1364501 2049227 := bstep (se 1 (by rfl) ⟨1536920, by rfl⟩ : syracuseStep 2049227 = 3073841) B3073841
theorem B2049239 : Blo 1364501 2049239 := bstep (se 1 (by rfl) ⟨1536929, by rfl⟩ : syracuseStep 2049239 = 3073859) B3073859
theorem B2303255 : Blo 1364501 2303255 := bstep (se 1 (by rfl) ⟨1727441, by rfl⟩ : syracuseStep 2303255 = 3454883) B3454883
theorem B2049305 : Blo 1364501 2049305 := bstep (se 2 (by rfl) ⟨768489, by rfl⟩ : syracuseStep 2049305 = 1536979) B1536979
theorem B3073355 : Blo 1364501 3073355 := bstep (se 1 (by rfl) ⟨2305016, by rfl⟩ : syracuseStep 3073355 = 4610033) B4610033
theorem B8750429 : Blo 1364501 8750429 := bstep (se 3 (by rfl) ⟨1640705, by rfl⟩ : syracuseStep 8750429 = 3281411) B3281411
theorem B3073409 : Blo 1364501 3073409 := bstep (se 2 (by rfl) ⟨1152528, by rfl⟩ : syracuseStep 3073409 = 2305057) B2305057
theorem B2049419 : Blo 1364501 2049419 := bstep (se 1 (by rfl) ⟨1537064, by rfl⟩ : syracuseStep 2049419 = 3074129) B3074129
theorem B4605335 : Blo 1364501 4605335 := bstep (se 1 (by rfl) ⟨3454001, by rfl⟩ : syracuseStep 4605335 = 6908003) B6908003
theorem B2303383 : Blo 1364501 2303383 := bstep (se 1 (by rfl) ⟨1727537, by rfl⟩ : syracuseStep 2303383 = 3455075) B3455075
theorem B2049431 : Blo 1364501 2049431 := bstep (se 1 (by rfl) ⟨1537073, by rfl⟩ : syracuseStep 2049431 = 3074147) B3074147
theorem B9848243 : Blo 1364501 9848243 := bstep (se 1 (by rfl) ⟨7386182, by rfl⟩ : syracuseStep 9848243 = 14772365) B14772365
theorem B3458497 : Blo 1364501 3458497 := bstep (se 2 (by rfl) ⟨1296936, by rfl⟩ : syracuseStep 3458497 = 2593873) B2593873
theorem B2049497 : Blo 1364501 2049497 := bstep (se 2 (by rfl) ⟨768561, by rfl⟩ : syracuseStep 2049497 = 1537123) B1537123
theorem B1558027 : Blo 1364501 1558027 := bstep (se 1 (by rfl) ⟨1168520, by rfl⟩ : syracuseStep 1558027 = 2337041) B2337041
theorem B2049611 : Blo 1364501 2049611 := bstep (se 1 (by rfl) ⟨1537208, by rfl⟩ : syracuseStep 2049611 = 3074417) B3074417
theorem B2049623 : Blo 1364501 2049623 := bstep (se 1 (by rfl) ⟨1537217, by rfl⟩ : syracuseStep 2049623 = 3074435) B3074435
theorem B3073625 : Blo 1364501 3073625 := bstep (se 2 (by rfl) ⟨1152609, by rfl⟩ : syracuseStep 3073625 = 2305219) B2305219
theorem B2049689 : Blo 1364501 2049689 := bstep (se 2 (by rfl) ⟨768633, by rfl⟩ : syracuseStep 2049689 = 1537267) B1537267
theorem B10798771 : Blo 1364501 10798771 := bstep (se 1 (by rfl) ⟨8099078, by rfl⟩ : syracuseStep 10798771 = 16198157) B16198157
theorem B3073715 : Blo 1364501 3073715 := bstep (se 1 (by rfl) ⟨2305286, by rfl⟩ : syracuseStep 3073715 = 4610573) B4610573
theorem B3073751 : Blo 1364501 3073751 := bstep (se 1 (by rfl) ⟨2305313, by rfl⟩ : syracuseStep 3073751 = 4610627) B4610627
theorem B8300333 : Blo 1364501 8300333 := bstep (se 3 (by rfl) ⟨1556312, by rfl⟩ : syracuseStep 8300333 = 3112625) B3112625
theorem B11659139 : Blo 1364501 11659139 := bstep (se 1 (by rfl) ⟨8744354, by rfl⟩ : syracuseStep 11659139 = 17488709) B17488709
theorem B3073931 : Blo 1364501 3073931 := bstep (se 1 (by rfl) ⟨2305448, by rfl⟩ : syracuseStep 3073931 = 4610897) B4610897
theorem B5187473 : Blo 1364501 5187473 := bstep (se 2 (by rfl) ⟨1945302, by rfl⟩ : syracuseStep 5187473 = 3890605) B3890605
theorem B4605875 : Blo 1364501 4605875 := bstep (se 1 (by rfl) ⟨3454406, by rfl⟩ : syracuseStep 4605875 = 6908813) B6908813
theorem B3073985 : Blo 1364501 3073985 := bstep (se 2 (by rfl) ⟨1152744, by rfl⟩ : syracuseStep 3073985 = 2305489) B2305489
theorem B2304011 : Blo 1364501 2304011 := bstep (se 1 (by rfl) ⟨1728008, by rfl⟩ : syracuseStep 2304011 = 3456017) B3456017
theorem B4671553 : Blo 1364501 4671553 := bstep (se 2 (by rfl) ⟨1751832, by rfl⟩ : syracuseStep 4671553 = 3503665) B3503665
theorem B15763531 : Blo 1364501 15763531 := bstep (se 1 (by rfl) ⟨11822648, by rfl⟩ : syracuseStep 15763531 = 23645297) B23645297
theorem B2590859 : Blo 1364501 2590859 := bstep (se 1 (by rfl) ⟨1943144, by rfl⟩ : syracuseStep 2590859 = 3886289) B3886289
theorem B2304139 : Blo 1364501 2304139 := bstep (se 1 (by rfl) ⟨1728104, by rfl⟩ : syracuseStep 2304139 = 3456209) B3456209
theorem B3074201 : Blo 1364501 3074201 := bstep (se 2 (by rfl) ⟨1152825, by rfl⟩ : syracuseStep 3074201 = 2305651) B2305651
theorem B4606145 : Blo 1364501 4606145 := bstep (se 2 (by rfl) ⟨1727304, by rfl⟩ : syracuseStep 4606145 = 3454609) B3454609
theorem B3074291 : Blo 1364501 3074291 := bstep (se 1 (by rfl) ⟨2305718, by rfl⟩ : syracuseStep 3074291 = 4611437) B4611437
theorem B2459927 : Blo 1364501 2459927 := bstep (se 1 (by rfl) ⟨1844945, by rfl⟩ : syracuseStep 2459927 = 3689891) B3689891
theorem B4376855 : Blo 1364501 4376855 := bstep (se 1 (by rfl) ⟨3282641, by rfl⟩ : syracuseStep 4376855 = 6565283) B6565283
theorem B1943833 : Blo 1364501 1943833 := bstep (se 2 (by rfl) ⟨728937, by rfl⟩ : syracuseStep 1943833 = 1457875) B1457875
theorem B2304281 : Blo 1364501 2304281 := bstep (se 2 (by rfl) ⟨864105, by rfl⟩ : syracuseStep 2304281 = 1728211) B1728211
theorem B3074327 : Blo 1364501 3074327 := bstep (se 1 (by rfl) ⟨2305745, by rfl⟩ : syracuseStep 3074327 = 4611491) B4611491
theorem B12798253 : Blo 1364501 12798253 := bstep (se 3 (by rfl) ⟨2399672, by rfl⟩ : syracuseStep 12798253 = 4799345) B4799345
theorem B5835053 : Blo 1364501 5835053 := bstep (se 3 (by rfl) ⟨1094072, by rfl⟩ : syracuseStep 5835053 = 2188145) B2188145
theorem B2591041 : Blo 1364501 2591041 := bstep (se 2 (by rfl) ⟨971640, by rfl⟩ : syracuseStep 2591041 = 1943281) B1943281
theorem B6916427 : Blo 1364501 6916427 := bstep (se 1 (by rfl) ⟨5187320, by rfl⟩ : syracuseStep 6916427 = 10374641) B10374641
theorem B1943947 : Blo 1364501 1943947 := bstep (se 1 (by rfl) ⟨1457960, by rfl⟩ : syracuseStep 1943947 = 2915921) B2915921
theorem B2304409 : Blo 1364501 2304409 := bstep (se 2 (by rfl) ⟨864153, by rfl⟩ : syracuseStep 2304409 = 1728307) B1728307
theorem B2460107 : Blo 1364501 2460107 := bstep (se 1 (by rfl) ⟨1845080, by rfl⟩ : syracuseStep 2460107 = 3690161) B3690161
theorem B3074507 : Blo 1364501 3074507 := bstep (se 1 (by rfl) ⟨2305880, by rfl⟩ : syracuseStep 3074507 = 4611761) B4611761
theorem B3074561 : Blo 1364501 3074561 := bstep (se 2 (by rfl) ⟨1152960, by rfl⟩ : syracuseStep 3074561 = 2305921) B2305921
theorem B26249741 : Blo 1364501 26249741 := bstep (se 3 (by rfl) ⟨4921826, by rfl⟩ : syracuseStep 26249741 = 9843653) B9843653
theorem B14764619 : Blo 1364501 14764619 := bstep (se 1 (by rfl) ⟨11073464, by rfl⟩ : syracuseStep 14764619 = 22146929) B22146929
theorem B5188171 : Blo 1364501 5188171 := bstep (se 1 (by rfl) ⟨3891128, by rfl⟩ : syracuseStep 5188171 = 7782257) B7782257
theorem B3885661 : Blo 1364501 3885661 := bstep (se 3 (by rfl) ⟨728561, by rfl⟩ : syracuseStep 3885661 = 1457123) B1457123
theorem B4991581 : Blo 1364501 4991581 := bstep (se 3 (by rfl) ⟨935921, by rfl⟩ : syracuseStep 4991581 = 1871843) B1871843
theorem B5835395 : Blo 1364501 5835395 := bstep (se 1 (by rfl) ⟨4376546, by rfl⟩ : syracuseStep 5835395 = 8753093) B8753093
theorem B4606685 : Blo 1364501 4606685 := bstep (se 3 (by rfl) ⟨863753, by rfl⟩ : syracuseStep 4606685 = 1727507) B1727507
theorem B19942129 : Blo 1364501 19942129 := bstep (se 2 (by rfl) ⟨7478298, by rfl⟩ : syracuseStep 19942129 = 14956597) B14956597
theorem B2591489 : Blo 1364501 2591489 := bstep (se 2 (by rfl) ⟨971808, by rfl⟩ : syracuseStep 2591489 = 1943617) B1943617
theorem B3885889 : Blo 1364501 3885889 := bstep (se 2 (by rfl) ⟨1457208, by rfl⟩ : syracuseStep 3885889 = 2914417) B2914417
theorem B2304983 : Blo 1364501 2304983 := bstep (se 1 (by rfl) ⟨1728737, by rfl⟩ : syracuseStep 2304983 = 3457475) B3457475
theorem B2460683 : Blo 1364501 2460683 := bstep (se 1 (by rfl) ⟨1845512, by rfl⟩ : syracuseStep 2460683 = 3691025) B3691025
theorem B2591831 : Blo 1364501 2591831 := bstep (se 1 (by rfl) ⟨1943873, by rfl⟩ : syracuseStep 2591831 = 3887747) B3887747
theorem B5532761 : Blo 1364501 5532761 := bstep (se 2 (by rfl) ⟨2074785, by rfl⟩ : syracuseStep 5532761 = 4149571) B4149571
theorem B2305111 : Blo 1364501 2305111 := bstep (se 1 (by rfl) ⟨1728833, by rfl⟩ : syracuseStep 2305111 = 3457667) B3457667
theorem B3886231 : Blo 1364501 3886231 := bstep (se 1 (by rfl) ⟨2914673, by rfl⟩ : syracuseStep 3886231 = 5829347) B5829347
theorem B23956661 : Blo 1364501 23956661 := bstep (se 5 (by rfl) ⟨1122968, by rfl⟩ : syracuseStep 23956661 = 2245937) B2245937
theorem B1535179 : Blo 1364501 1535179 := bstep (se 1 (by rfl) ⟨1151384, by rfl⟩ : syracuseStep 1535179 = 2302769) B2302769
theorem B1535287 : Blo 1364501 1535287 := bstep (se 1 (by rfl) ⟨1151465, by rfl⟩ : syracuseStep 1535287 = 2302931) B2302931
theorem B10513729 : Blo 1364501 10513729 := bstep (se 2 (by rfl) ⟨3942648, by rfl⟩ : syracuseStep 10513729 = 7885297) B7885297
theorem B3689945 : Blo 1364501 3689945 := bstep (se 2 (by rfl) ⟨1383729, by rfl⟩ : syracuseStep 3689945 = 2767459) B2767459
theorem B1535467 : Blo 1364501 1535467 := bstep (se 1 (by rfl) ⟨1151600, by rfl⟩ : syracuseStep 1535467 = 2303201) B2303201
theorem B13118993 : Blo 1364501 13118993 := bstep (se 2 (by rfl) ⟨4919622, by rfl⟩ : syracuseStep 13118993 = 9839245) B9839245
theorem B1535575 : Blo 1364501 1535575 := bstep (se 1 (by rfl) ⟨1151681, by rfl⟩ : syracuseStep 1535575 = 2303363) B2303363
theorem B3690073 : Blo 1364501 3690073 := bstep (se 2 (by rfl) ⟨1383777, by rfl⟩ : syracuseStep 3690073 = 2767555) B2767555
theorem B1478251 : Blo 1364501 1478251 := bstep (se 1 (by rfl) ⟨1108688, by rfl⟩ : syracuseStep 1478251 = 2217377) B2217377
theorem B1945291 : Blo 1364501 1945291 := bstep (se 1 (by rfl) ⟨1458968, by rfl⟩ : syracuseStep 1945291 = 2917937) B2917937
theorem B2305739 : Blo 1364501 2305739 := bstep (se 1 (by rfl) ⟨1729304, by rfl⟩ : syracuseStep 2305739 = 3458609) B3458609
theorem B2592499 : Blo 1364501 2592499 := bstep (se 1 (by rfl) ⟨1944374, by rfl⟩ : syracuseStep 2592499 = 3888749) B3888749
theorem B1535755 : Blo 1364501 1535755 := bstep (se 1 (by rfl) ⟨1151816, by rfl⟩ : syracuseStep 1535755 = 2303633) B2303633
theorem B7778065 : Blo 1364501 7778065 := bstep (se 2 (by rfl) ⟨2916774, by rfl⟩ : syracuseStep 7778065 = 5833549) B5833549
theorem B4607819 : Blo 1364501 4607819 := bstep (se 1 (by rfl) ⟨3455864, by rfl⟩ : syracuseStep 4607819 = 6911729) B6911729
theorem B2305867 : Blo 1364501 2305867 := bstep (se 1 (by rfl) ⟨1729400, by rfl⟩ : syracuseStep 2305867 = 3458801) B3458801
theorem B3886937 : Blo 1364501 3886937 := bstep (se 2 (by rfl) ⟨1457601, by rfl⟩ : syracuseStep 3886937 = 2915203) B2915203
theorem B1535863 : Blo 1364501 1535863 := bstep (se 1 (by rfl) ⟨1151897, by rfl⟩ : syracuseStep 1535863 = 2303795) B2303795
theorem B1945559 : Blo 1364501 1945559 := bstep (se 1 (by rfl) ⟨1459169, by rfl⟩ : syracuseStep 1945559 = 2918339) B2918339
theorem B2461657 : Blo 1364501 2461657 := bstep (se 2 (by rfl) ⟨923121, by rfl⟩ : syracuseStep 2461657 = 1846243) B1846243
theorem B1536043 : Blo 1364501 1536043 := bstep (se 1 (by rfl) ⟨1152032, by rfl⟩ : syracuseStep 1536043 = 2304065) B2304065
theorem B4608089 : Blo 1364501 4608089 := bstep (se 2 (by rfl) ⟨1728033, by rfl⟩ : syracuseStep 4608089 = 3456067) B3456067
theorem B1536151 : Blo 1364501 1536151 := bstep (se 1 (by rfl) ⟨1152113, by rfl⟩ : syracuseStep 1536151 = 2304227) B2304227
theorem B2592947 : Blo 1364501 2592947 := bstep (se 1 (by rfl) ⟨1944710, by rfl⟩ : syracuseStep 2592947 = 3889421) B3889421
theorem B2592985 : Blo 1364501 2592985 := bstep (se 2 (by rfl) ⟨972369, by rfl⟩ : syracuseStep 2592985 = 1944739) B1944739
theorem B2625779 : Blo 1364501 2625779 := bstep (se 1 (by rfl) ⟨1969334, by rfl⟩ : syracuseStep 2625779 = 3938669) B3938669
theorem B8753453 : Blo 1364501 8753453 := bstep (se 3 (by rfl) ⟨1641272, by rfl⟩ : syracuseStep 8753453 = 3282545) B3282545
theorem B1536331 : Blo 1364501 1536331 := bstep (se 1 (by rfl) ⟨1152248, by rfl⟩ : syracuseStep 1536331 = 2304497) B2304497
theorem B1536439 : Blo 1364501 1536439 := bstep (se 1 (by rfl) ⟨1152329, by rfl⟩ : syracuseStep 1536439 = 2304659) B2304659
theorem B7377425 : Blo 1364501 7377425 := bstep (se 2 (by rfl) ⟨2766534, by rfl⟩ : syracuseStep 7377425 = 5533069) B5533069
theorem B15561233 : Blo 1364501 15561233 := bstep (se 2 (by rfl) ⟨5835462, by rfl⟩ : syracuseStep 15561233 = 11670925) B11670925
theorem B1364503 : Blo 1364501 1364503 := bstep (se 1 (by rfl) ⟨1023377, by rfl⟩ : syracuseStep 1364503 = 2046755) B2046755
theorem B1364523 : Blo 1364501 1364523 := bstep (se 1 (by rfl) ⟨1023392, by rfl⟩ : syracuseStep 1364523 = 2046785) B2046785
theorem B1364535 : Blo 1364501 1364535 := bstep (se 1 (by rfl) ⟨1023401, by rfl⟩ : syracuseStep 1364535 = 2046803) B2046803
theorem B1364555 : Blo 1364501 1364555 := bstep (se 1 (by rfl) ⟨1023416, by rfl⟩ : syracuseStep 1364555 = 2046833) B2046833
theorem B1364567 : Blo 1364501 1364567 := bstep (se 1 (by rfl) ⟨1023425, by rfl⟩ : syracuseStep 1364567 = 2046851) B2046851
theorem B1364587 : Blo 1364501 1364587 := bstep (se 1 (by rfl) ⟨1023440, by rfl⟩ : syracuseStep 1364587 = 2046881) B2046881
theorem B1536619 : Blo 1364501 1536619 := bstep (se 1 (by rfl) ⟨1152464, by rfl⟩ : syracuseStep 1536619 = 2304929) B2304929
theorem B1364599 : Blo 1364501 1364599 := bstep (se 1 (by rfl) ⟨1023449, by rfl⟩ : syracuseStep 1364599 = 2046899) B2046899
theorem B6910595 : Blo 1364501 6910595 := bstep (se 1 (by rfl) ⟨5182946, by rfl⟩ : syracuseStep 6910595 = 10365893) B10365893
theorem B1364619 : Blo 1364501 1364619 := bstep (se 1 (by rfl) ⟨1023464, by rfl⟩ : syracuseStep 1364619 = 2046929) B2046929
theorem B1364631 : Blo 1364501 1364631 := bstep (se 1 (by rfl) ⟨1023473, by rfl⟩ : syracuseStep 1364631 = 2046947) B2046947
theorem B2593433 : Blo 1364501 2593433 := bstep (se 2 (by rfl) ⟨972537, by rfl⟩ : syracuseStep 2593433 = 1945075) B1945075
theorem B1364651 : Blo 1364501 1364651 := bstep (se 1 (by rfl) ⟨1023488, by rfl⟩ : syracuseStep 1364651 = 2046977) B2046977
theorem B1364663 : Blo 1364501 1364663 := bstep (se 1 (by rfl) ⟨1023497, by rfl⟩ : syracuseStep 1364663 = 2046995) B2046995
theorem B1364683 : Blo 1364501 1364683 := bstep (se 1 (by rfl) ⟨1023512, by rfl⟩ : syracuseStep 1364683 = 2047025) B2047025
theorem B1364695 : Blo 1364501 1364695 := bstep (se 1 (by rfl) ⟨1023521, by rfl⟩ : syracuseStep 1364695 = 2047043) B2047043
theorem B1536727 : Blo 1364501 1536727 := bstep (se 1 (by rfl) ⟨1152545, by rfl⟩ : syracuseStep 1536727 = 2305091) B2305091
theorem B1364715 : Blo 1364501 1364715 := bstep (se 1 (by rfl) ⟨1023536, by rfl⟩ : syracuseStep 1364715 = 2047073) B2047073
theorem B1364727 : Blo 1364501 1364727 := bstep (se 1 (by rfl) ⟨1023545, by rfl⟩ : syracuseStep 1364727 = 2047091) B2047091
theorem B1364747 : Blo 1364501 1364747 := bstep (se 1 (by rfl) ⟨1023560, by rfl⟩ : syracuseStep 1364747 = 2047121) B2047121
theorem B1364759 : Blo 1364501 1364759 := bstep (se 1 (by rfl) ⟨1023569, by rfl⟩ : syracuseStep 1364759 = 2047139) B2047139
theorem B4608791 : Blo 1364501 4608791 := bstep (se 1 (by rfl) ⟨3456593, by rfl⟩ : syracuseStep 4608791 = 6913187) B6913187
theorem B1364779 : Blo 1364501 1364779 := bstep (se 1 (by rfl) ⟨1023584, by rfl⟩ : syracuseStep 1364779 = 2047169) B2047169
theorem B1364791 : Blo 1364501 1364791 := bstep (se 1 (by rfl) ⟨1023593, by rfl⟩ : syracuseStep 1364791 = 2047187) B2047187
theorem B1364811 : Blo 1364501 1364811 := bstep (se 1 (by rfl) ⟨1023608, by rfl⟩ : syracuseStep 1364811 = 2047217) B2047217
theorem B1364823 : Blo 1364501 1364823 := bstep (se 1 (by rfl) ⟨1023617, by rfl⟩ : syracuseStep 1364823 = 2047235) B2047235
theorem B10367837 : Blo 1364501 10367837 := bstep (se 3 (by rfl) ⟨1943969, by rfl⟩ : syracuseStep 10367837 = 3887939) B3887939
theorem B1364843 : Blo 1364501 1364843 := bstep (se 1 (by rfl) ⟨1023632, by rfl⟩ : syracuseStep 1364843 = 2047265) B2047265
theorem B1364855 : Blo 1364501 1364855 := bstep (se 1 (by rfl) ⟨1023641, by rfl⟩ : syracuseStep 1364855 = 2047283) B2047283
theorem B5182339 : Blo 1364501 5182339 := bstep (se 1 (by rfl) ⟨3886754, by rfl⟩ : syracuseStep 5182339 = 7773509) B7773509
theorem B1364875 : Blo 1364501 1364875 := bstep (se 1 (by rfl) ⟨1023656, by rfl⟩ : syracuseStep 1364875 = 2047313) B2047313
theorem B1536907 : Blo 1364501 1536907 := bstep (se 1 (by rfl) ⟨1152680, by rfl⟩ : syracuseStep 1536907 = 2305361) B2305361
theorem B1364887 : Blo 1364501 1364887 := bstep (se 1 (by rfl) ⟨1023665, by rfl⟩ : syracuseStep 1364887 = 2047331) B2047331
theorem B1364907 : Blo 1364501 1364907 := bstep (se 1 (by rfl) ⟨1023680, by rfl⟩ : syracuseStep 1364907 = 2047361) B2047361
theorem B1364919 : Blo 1364501 1364919 := bstep (se 1 (by rfl) ⟨1023689, by rfl⟩ : syracuseStep 1364919 = 2047379) B2047379
theorem B1364939 : Blo 1364501 1364939 := bstep (se 1 (by rfl) ⟨1023704, by rfl⟩ : syracuseStep 1364939 = 2047409) B2047409
theorem B1364951 : Blo 1364501 1364951 := bstep (se 1 (by rfl) ⟨1023713, by rfl⟩ : syracuseStep 1364951 = 2047427) B2047427
theorem B4371421 : Blo 1364501 4371421 := bstep (se 3 (by rfl) ⟨819641, by rfl⟩ : syracuseStep 4371421 = 1639283) B1639283
theorem B1364971 : Blo 1364501 1364971 := bstep (se 1 (by rfl) ⟨1023728, by rfl⟩ : syracuseStep 1364971 = 2047457) B2047457
theorem B1364983 : Blo 1364501 1364983 := bstep (se 1 (by rfl) ⟨1023737, by rfl⟩ : syracuseStep 1364983 = 2047475) B2047475
theorem B1537015 : Blo 1364501 1537015 := bstep (se 1 (by rfl) ⟨1152761, by rfl⟩ : syracuseStep 1537015 = 2305523) B2305523
theorem B1365003 : Blo 1364501 1365003 := bstep (se 1 (by rfl) ⟨1023752, by rfl⟩ : syracuseStep 1365003 = 2047505) B2047505
theorem B1365015 : Blo 1364501 1365015 := bstep (se 1 (by rfl) ⟨1023761, by rfl⟩ : syracuseStep 1365015 = 2047523) B2047523
theorem B1365035 : Blo 1364501 1365035 := bstep (se 1 (by rfl) ⟨1023776, by rfl⟩ : syracuseStep 1365035 = 2047553) B2047553
theorem B1365047 : Blo 1364501 1365047 := bstep (se 1 (by rfl) ⟨1023785, by rfl⟩ : syracuseStep 1365047 = 2047571) B2047571
theorem B1365067 : Blo 1364501 1365067 := bstep (se 1 (by rfl) ⟨1023800, by rfl⟩ : syracuseStep 1365067 = 2047601) B2047601
theorem B1365079 : Blo 1364501 1365079 := bstep (se 1 (by rfl) ⟨1023809, by rfl⟩ : syracuseStep 1365079 = 2047619) B2047619
theorem B1365099 : Blo 1364501 1365099 := bstep (se 1 (by rfl) ⟨1023824, by rfl⟩ : syracuseStep 1365099 = 2047649) B2047649
theorem B1365111 : Blo 1364501 1365111 := bstep (se 1 (by rfl) ⟨1023833, by rfl⟩ : syracuseStep 1365111 = 2047667) B2047667
theorem B1365131 : Blo 1364501 1365131 := bstep (se 1 (by rfl) ⟨1023848, by rfl⟩ : syracuseStep 1365131 = 2047697) B2047697
theorem B3454103 : Blo 1364501 3454103 := bstep (se 1 (by rfl) ⟨2590577, by rfl⟩ : syracuseStep 3454103 = 5181155) B5181155
theorem B1365143 : Blo 1364501 1365143 := bstep (se 1 (by rfl) ⟨1023857, by rfl⟩ : syracuseStep 1365143 = 2047715) B2047715
theorem B1365163 : Blo 1364501 1365163 := bstep (se 1 (by rfl) ⟨1023872, by rfl⟩ : syracuseStep 1365163 = 2047745) B2047745
theorem B1537195 : Blo 1364501 1537195 := bstep (se 1 (by rfl) ⟨1152896, by rfl⟩ : syracuseStep 1537195 = 2305793) B2305793
theorem B5182643 : Blo 1364501 5182643 := bstep (se 1 (by rfl) ⟨3886982, by rfl⟩ : syracuseStep 5182643 = 7773965) B7773965
theorem B1365175 : Blo 1364501 1365175 := bstep (se 1 (by rfl) ⟨1023881, by rfl⟩ : syracuseStep 1365175 = 2047763) B2047763
theorem B1365195 : Blo 1364501 1365195 := bstep (se 1 (by rfl) ⟨1023896, by rfl⟩ : syracuseStep 1365195 = 2047793) B2047793
theorem B1365207 : Blo 1364501 1365207 := bstep (se 1 (by rfl) ⟨1023905, by rfl⟩ : syracuseStep 1365207 = 2047811) B2047811
theorem B1365227 : Blo 1364501 1365227 := bstep (se 1 (by rfl) ⟨1023920, by rfl⟩ : syracuseStep 1365227 = 2047841) B2047841
theorem B1365239 : Blo 1364501 1365239 := bstep (se 1 (by rfl) ⟨1023929, by rfl⟩ : syracuseStep 1365239 = 2047859) B2047859
theorem B24925445 : Blo 1364501 24925445 := bstep (se 4 (by rfl) ⟨2336760, by rfl⟩ : syracuseStep 24925445 = 4673521) B4673521
theorem B1365259 : Blo 1364501 1365259 := bstep (se 1 (by rfl) ⟨1023944, by rfl⟩ : syracuseStep 1365259 = 2047889) B2047889
theorem B1365271 : Blo 1364501 1365271 := bstep (se 1 (by rfl) ⟨1023953, by rfl⟩ : syracuseStep 1365271 = 2047907) B2047907
theorem B1537303 : Blo 1364501 1537303 := bstep (se 1 (by rfl) ⟨1152977, by rfl⟩ : syracuseStep 1537303 = 2305955) B2305955
theorem B1365291 : Blo 1364501 1365291 := bstep (se 1 (by rfl) ⟨1023968, by rfl⟩ : syracuseStep 1365291 = 2047937) B2047937
theorem B4609331 : Blo 1364501 4609331 := bstep (se 1 (by rfl) ⟨3456998, by rfl⟩ : syracuseStep 4609331 = 6913997) B6913997
theorem B1365303 : Blo 1364501 1365303 := bstep (se 1 (by rfl) ⟨1023977, by rfl⟩ : syracuseStep 1365303 = 2047955) B2047955
theorem B1365323 : Blo 1364501 1365323 := bstep (se 1 (by rfl) ⟨1023992, by rfl⟩ : syracuseStep 1365323 = 2047985) B2047985
theorem B1365335 : Blo 1364501 1365335 := bstep (se 1 (by rfl) ⟨1024001, by rfl⟩ : syracuseStep 1365335 = 2048003) B2048003
theorem B1365355 : Blo 1364501 1365355 := bstep (se 1 (by rfl) ⟨1024016, by rfl⟩ : syracuseStep 1365355 = 2048033) B2048033
theorem B1365367 : Blo 1364501 1365367 := bstep (se 1 (by rfl) ⟨1024025, by rfl⟩ : syracuseStep 1365367 = 2048051) B2048051
theorem B2594177 : Blo 1364501 2594177 := bstep (se 2 (by rfl) ⟨972816, by rfl⟩ : syracuseStep 2594177 = 1945633) B1945633
theorem B1365387 : Blo 1364501 1365387 := bstep (se 1 (by rfl) ⟨1024040, by rfl⟩ : syracuseStep 1365387 = 2048081) B2048081
theorem B1365399 : Blo 1364501 1365399 := bstep (se 1 (by rfl) ⟨1024049, by rfl⟩ : syracuseStep 1365399 = 2048099) B2048099
theorem B1365419 : Blo 1364501 1365419 := bstep (se 1 (by rfl) ⟨1024064, by rfl⟩ : syracuseStep 1365419 = 2048129) B2048129
theorem B7386547 : Blo 1364501 7386547 := bstep (se 1 (by rfl) ⟨5539910, by rfl⟩ : syracuseStep 7386547 = 11079821) B11079821
theorem B1365431 : Blo 1364501 1365431 := bstep (se 1 (by rfl) ⟨1024073, by rfl⟩ : syracuseStep 1365431 = 2048147) B2048147
theorem B3888577 : Blo 1364501 3888577 := bstep (se 2 (by rfl) ⟨1458216, by rfl⟩ : syracuseStep 3888577 = 2916433) B2916433
theorem B1365451 : Blo 1364501 1365451 := bstep (se 1 (by rfl) ⟨1024088, by rfl⟩ : syracuseStep 1365451 = 2048177) B2048177
theorem B1365463 : Blo 1364501 1365463 := bstep (se 1 (by rfl) ⟨1024097, by rfl⟩ : syracuseStep 1365463 = 2048195) B2048195
theorem B1365483 : Blo 1364501 1365483 := bstep (se 1 (by rfl) ⟨1024112, by rfl⟩ : syracuseStep 1365483 = 2048225) B2048225
theorem B1365495 : Blo 1364501 1365495 := bstep (se 1 (by rfl) ⟨1024121, by rfl⟩ : syracuseStep 1365495 = 2048243) B2048243
theorem B1365515 : Blo 1364501 1365515 := bstep (se 1 (by rfl) ⟨1024136, by rfl⟩ : syracuseStep 1365515 = 2048273) B2048273
theorem B1365527 : Blo 1364501 1365527 := bstep (se 1 (by rfl) ⟨1024145, by rfl⟩ : syracuseStep 1365527 = 2048291) B2048291
theorem B1365547 : Blo 1364501 1365547 := bstep (se 1 (by rfl) ⟨1024160, by rfl⟩ : syracuseStep 1365547 = 2048321) B2048321
theorem B1365559 : Blo 1364501 1365559 := bstep (se 1 (by rfl) ⟨1024169, by rfl⟩ : syracuseStep 1365559 = 2048339) B2048339
theorem B4609601 : Blo 1364501 4609601 := bstep (se 2 (by rfl) ⟨1728600, by rfl⟩ : syracuseStep 4609601 = 3457201) B3457201
theorem B23983685 : Blo 1364501 23983685 := bstep (se 4 (by rfl) ⟨2248470, by rfl⟩ : syracuseStep 23983685 = 4496941) B4496941
theorem B1365579 : Blo 1364501 1365579 := bstep (se 1 (by rfl) ⟨1024184, by rfl⟩ : syracuseStep 1365579 = 2048369) B2048369
theorem B1365591 : Blo 1364501 1365591 := bstep (se 1 (by rfl) ⟨1024193, by rfl⟩ : syracuseStep 1365591 = 2048387) B2048387
theorem B1365611 : Blo 1364501 1365611 := bstep (se 1 (by rfl) ⟨1024208, by rfl⟩ : syracuseStep 1365611 = 2048417) B2048417
theorem B1365623 : Blo 1364501 1365623 := bstep (se 1 (by rfl) ⟨1024217, by rfl⟩ : syracuseStep 1365623 = 2048435) B2048435
theorem B2627201 : Blo 1364501 2627201 := bstep (se 2 (by rfl) ⟨985200, by rfl⟩ : syracuseStep 2627201 = 1970401) B1970401
theorem B1365643 : Blo 1364501 1365643 := bstep (se 1 (by rfl) ⟨1024232, by rfl⟩ : syracuseStep 1365643 = 2048465) B2048465
theorem B1365655 : Blo 1364501 1365655 := bstep (se 1 (by rfl) ⟨1024241, by rfl⟩ : syracuseStep 1365655 = 2048483) B2048483
theorem B1365675 : Blo 1364501 1365675 := bstep (se 1 (by rfl) ⟨1024256, by rfl⟩ : syracuseStep 1365675 = 2048513) B2048513
theorem B1365687 : Blo 1364501 1365687 := bstep (se 1 (by rfl) ⟨1024265, by rfl⟩ : syracuseStep 1365687 = 2048531) B2048531
theorem B1365707 : Blo 1364501 1365707 := bstep (se 1 (by rfl) ⟨1024280, by rfl⟩ : syracuseStep 1365707 = 2048561) B2048561
theorem B1365719 : Blo 1364501 1365719 := bstep (se 1 (by rfl) ⟨1024289, by rfl⟩ : syracuseStep 1365719 = 2048579) B2048579
theorem B1365739 : Blo 1364501 1365739 := bstep (se 1 (by rfl) ⟨1024304, by rfl⟩ : syracuseStep 1365739 = 2048609) B2048609
theorem B1365751 : Blo 1364501 1365751 := bstep (se 1 (by rfl) ⟨1024313, by rfl⟩ : syracuseStep 1365751 = 2048627) B2048627
theorem B1365771 : Blo 1364501 1365771 := bstep (se 1 (by rfl) ⟨1024328, by rfl⟩ : syracuseStep 1365771 = 2048657) B2048657
theorem B1365783 : Blo 1364501 1365783 := bstep (se 1 (by rfl) ⟨1024337, by rfl⟩ : syracuseStep 1365783 = 2048675) B2048675
theorem B1365803 : Blo 1364501 1365803 := bstep (se 1 (by rfl) ⟨1024352, by rfl⟩ : syracuseStep 1365803 = 2048705) B2048705
theorem B3454771 : Blo 1364501 3454771 := bstep (se 1 (by rfl) ⟨2591078, by rfl⟩ : syracuseStep 3454771 = 5182157) B5182157
theorem B1365815 : Blo 1364501 1365815 := bstep (se 1 (by rfl) ⟨1024361, by rfl⟩ : syracuseStep 1365815 = 2048723) B2048723
theorem B5183297 : Blo 1364501 5183297 := bstep (se 2 (by rfl) ⟨1943736, by rfl⟩ : syracuseStep 5183297 = 3887473) B3887473
theorem B1365835 : Blo 1364501 1365835 := bstep (se 1 (by rfl) ⟨1024376, by rfl⟩ : syracuseStep 1365835 = 2048753) B2048753
theorem B2766679 : Blo 1364501 2766679 := bstep (se 1 (by rfl) ⟨2075009, by rfl⟩ : syracuseStep 2766679 = 4150019) B4150019
theorem B1365847 : Blo 1364501 1365847 := bstep (se 1 (by rfl) ⟨1024385, by rfl⟩ : syracuseStep 1365847 = 2048771) B2048771
theorem B1365867 : Blo 1364501 1365867 := bstep (se 1 (by rfl) ⟨1024400, by rfl⟩ : syracuseStep 1365867 = 2048801) B2048801
theorem B1365879 : Blo 1364501 1365879 := bstep (se 1 (by rfl) ⟨1024409, by rfl⟩ : syracuseStep 1365879 = 2048819) B2048819
theorem B1365899 : Blo 1364501 1365899 := bstep (se 1 (by rfl) ⟨1024424, by rfl⟩ : syracuseStep 1365899 = 2048849) B2048849
theorem B1365911 : Blo 1364501 1365911 := bstep (se 1 (by rfl) ⟨1024433, by rfl⟩ : syracuseStep 1365911 = 2048867) B2048867
theorem B1365931 : Blo 1364501 1365931 := bstep (se 1 (by rfl) ⟨1024448, by rfl⟩ : syracuseStep 1365931 = 2048897) B2048897
theorem B1365943 : Blo 1364501 1365943 := bstep (se 1 (by rfl) ⟨1024457, by rfl⟩ : syracuseStep 1365943 = 2048915) B2048915
theorem B3454913 : Blo 1364501 3454913 := bstep (se 2 (by rfl) ⟨1295592, by rfl⟩ : syracuseStep 3454913 = 2591185) B2591185
theorem B1365963 : Blo 1364501 1365963 := bstep (se 1 (by rfl) ⟨1024472, by rfl⟩ : syracuseStep 1365963 = 2048945) B2048945
theorem B1365975 : Blo 1364501 1365975 := bstep (se 1 (by rfl) ⟨1024481, by rfl⟩ : syracuseStep 1365975 = 2048963) B2048963
theorem B1365995 : Blo 1364501 1365995 := bstep (se 1 (by rfl) ⟨1024496, by rfl⟩ : syracuseStep 1365995 = 2048993) B2048993
theorem B1366007 : Blo 1364501 1366007 := bstep (se 1 (by rfl) ⟨1024505, by rfl⟩ : syracuseStep 1366007 = 2049011) B2049011
theorem B1366027 : Blo 1364501 1366027 := bstep (se 1 (by rfl) ⟨1024520, by rfl⟩ : syracuseStep 1366027 = 2049041) B2049041
theorem B5830679 : Blo 1364501 5830679 := bstep (se 1 (by rfl) ⟨4373009, by rfl⟩ : syracuseStep 5830679 = 8746019) B8746019
theorem B1366039 : Blo 1364501 1366039 := bstep (se 1 (by rfl) ⟨1024529, by rfl⟩ : syracuseStep 1366039 = 2049059) B2049059
theorem B1366059 : Blo 1364501 1366059 := bstep (se 1 (by rfl) ⟨1024544, by rfl⟩ : syracuseStep 1366059 = 2049089) B2049089
theorem B1366071 : Blo 1364501 1366071 := bstep (se 1 (by rfl) ⟨1024553, by rfl⟩ : syracuseStep 1366071 = 2049107) B2049107
theorem B2766923 : Blo 1364501 2766923 := bstep (se 1 (by rfl) ⟨2075192, by rfl⟩ : syracuseStep 2766923 = 4150385) B4150385
theorem B1366091 : Blo 1364501 1366091 := bstep (se 1 (by rfl) ⟨1024568, by rfl⟩ : syracuseStep 1366091 = 2049137) B2049137
theorem B1366103 : Blo 1364501 1366103 := bstep (se 1 (by rfl) ⟨1024577, by rfl⟩ : syracuseStep 1366103 = 2049155) B2049155
theorem B4610141 : Blo 1364501 4610141 := bstep (se 3 (by rfl) ⟨864401, by rfl⟩ : syracuseStep 4610141 = 1728803) B1728803
theorem B10106981 : Blo 1364501 10106981 := bstep (se 4 (by rfl) ⟨947529, by rfl⟩ : syracuseStep 10106981 = 1895059) B1895059
theorem B1366123 : Blo 1364501 1366123 := bstep (se 1 (by rfl) ⟨1024592, by rfl⟩ : syracuseStep 1366123 = 2049185) B2049185
theorem B1366135 : Blo 1364501 1366135 := bstep (se 1 (by rfl) ⟨1024601, by rfl⟩ : syracuseStep 1366135 = 2049203) B2049203
theorem B1366155 : Blo 1364501 1366155 := bstep (se 1 (by rfl) ⟨1024616, by rfl⟩ : syracuseStep 1366155 = 2049233) B2049233
theorem B1366167 : Blo 1364501 1366167 := bstep (se 1 (by rfl) ⟨1024625, by rfl⟩ : syracuseStep 1366167 = 2049251) B2049251
theorem B1366187 : Blo 1364501 1366187 := bstep (se 1 (by rfl) ⟨1024640, by rfl⟩ : syracuseStep 1366187 = 2049281) B2049281
theorem B1366199 : Blo 1364501 1366199 := bstep (se 1 (by rfl) ⟨1024649, by rfl⟩ : syracuseStep 1366199 = 2049299) B2049299
theorem B1366219 : Blo 1364501 1366219 := bstep (se 1 (by rfl) ⟨1024664, by rfl⟩ : syracuseStep 1366219 = 2049329) B2049329
theorem B3070169 : Blo 1364501 3070169 := bstep (se 2 (by rfl) ⟨1151313, by rfl⟩ : syracuseStep 3070169 = 2302627) B2302627
theorem B1366231 : Blo 1364501 1366231 := bstep (se 1 (by rfl) ⟨1024673, by rfl⟩ : syracuseStep 1366231 = 2049347) B2049347
theorem B1366251 : Blo 1364501 1366251 := bstep (se 1 (by rfl) ⟨1024688, by rfl⟩ : syracuseStep 1366251 = 2049377) B2049377
theorem B1366263 : Blo 1364501 1366263 := bstep (se 1 (by rfl) ⟨1024697, by rfl⟩ : syracuseStep 1366263 = 2049395) B2049395
theorem B1366283 : Blo 1364501 1366283 := bstep (se 1 (by rfl) ⟨1024712, by rfl⟩ : syracuseStep 1366283 = 2049425) B2049425
theorem B1366295 : Blo 1364501 1366295 := bstep (se 1 (by rfl) ⟨1024721, by rfl⟩ : syracuseStep 1366295 = 2049443) B2049443
theorem B1366315 : Blo 1364501 1366315 := bstep (se 1 (by rfl) ⟨1024736, by rfl⟩ : syracuseStep 1366315 = 2049473) B2049473
theorem B3070259 : Blo 1364501 3070259 := bstep (se 1 (by rfl) ⟨2302694, by rfl⟩ : syracuseStep 3070259 = 4605389) B4605389
theorem B1366327 : Blo 1364501 1366327 := bstep (se 1 (by rfl) ⟨1024745, by rfl⟩ : syracuseStep 1366327 = 2049491) B2049491
theorem B5830987 : Blo 1364501 5830987 := bstep (se 1 (by rfl) ⟨4373240, by rfl⟩ : syracuseStep 5830987 = 8746481) B8746481
theorem B11671883 : Blo 1364501 11671883 := bstep (se 1 (by rfl) ⟨8753912, by rfl⟩ : syracuseStep 11671883 = 17507825) B17507825
theorem B1366347 : Blo 1364501 1366347 := bstep (se 1 (by rfl) ⟨1024760, by rfl⟩ : syracuseStep 1366347 = 2049521) B2049521
theorem B3070295 : Blo 1364501 3070295 := bstep (se 1 (by rfl) ⟨2302721, by rfl⟩ : syracuseStep 3070295 = 4605443) B4605443
theorem B1366359 : Blo 1364501 1366359 := bstep (se 1 (by rfl) ⟨1024769, by rfl⟩ : syracuseStep 1366359 = 2049539) B2049539
theorem B1366379 : Blo 1364501 1366379 := bstep (se 1 (by rfl) ⟨1024784, by rfl⟩ : syracuseStep 1366379 = 2049569) B2049569
theorem B39369077 : Blo 1364501 39369077 := bstep (se 5 (by rfl) ⟨1845425, by rfl⟩ : syracuseStep 39369077 = 3690851) B3690851
theorem B1366391 : Blo 1364501 1366391 := bstep (se 1 (by rfl) ⟨1024793, by rfl⟩ : syracuseStep 1366391 = 2049587) B2049587
theorem B1366411 : Blo 1364501 1366411 := bstep (se 1 (by rfl) ⟨1024808, by rfl⟩ : syracuseStep 1366411 = 2049617) B2049617
theorem B1366423 : Blo 1364501 1366423 := bstep (se 1 (by rfl) ⟨1024817, by rfl⟩ : syracuseStep 1366423 = 2049635) B2049635
theorem B1366443 : Blo 1364501 1366443 := bstep (se 1 (by rfl) ⟨1024832, by rfl⟩ : syracuseStep 1366443 = 2049665) B2049665
theorem B1366455 : Blo 1364501 1366455 := bstep (se 1 (by rfl) ⟨1024841, by rfl⟩ : syracuseStep 1366455 = 2049683) B2049683
theorem B1366475 : Blo 1364501 1366475 := bstep (se 1 (by rfl) ⟨1024856, by rfl⟩ : syracuseStep 1366475 = 2049713) B2049713
theorem B1366487 : Blo 1364501 1366487 := bstep (se 1 (by rfl) ⟨1024865, by rfl⟩ : syracuseStep 1366487 = 2049731) B2049731
theorem B17488345 : Blo 1364501 17488345 := bstep (se 2 (by rfl) ⟨6558129, by rfl⟩ : syracuseStep 17488345 = 13116259) B13116259
theorem B3070475 : Blo 1364501 3070475 := bstep (se 1 (by rfl) ⟨2302856, by rfl⟩ : syracuseStep 3070475 = 4605713) B4605713
theorem B3070529 : Blo 1364501 3070529 := bstep (se 2 (by rfl) ⟨1151448, by rfl⟩ : syracuseStep 3070529 = 2302897) B2302897
theorem B5536345 : Blo 1364501 5536345 := bstep (se 2 (by rfl) ⟨2076129, by rfl⟩ : syracuseStep 5536345 = 4152259) B4152259
theorem B12622429 : Blo 1364501 12622429 := bstep (se 3 (by rfl) ⟨2366705, by rfl⟩ : syracuseStep 12622429 = 4733411) B4733411
theorem B5831261 : Blo 1364501 5831261 := bstep (se 3 (by rfl) ⟨1093361, by rfl⟩ : syracuseStep 5831261 = 2186723) B2186723
theorem B3070745 : Blo 1364501 3070745 := bstep (se 2 (by rfl) ⟨1151529, by rfl⟩ : syracuseStep 3070745 = 2303059) B2303059
theorem B2046809 : Blo 1364501 2046809 := bstep (se 2 (by rfl) ⟨767553, by rfl⟩ : syracuseStep 2046809 = 1535107) B1535107
theorem B3070835 : Blo 1364501 3070835 := bstep (se 1 (by rfl) ⟨2303126, by rfl⟩ : syracuseStep 3070835 = 4606253) B4606253
theorem B3070871 : Blo 1364501 3070871 := bstep (se 1 (by rfl) ⟨2303153, by rfl⟩ : syracuseStep 3070871 = 4606307) B4606307
theorem B2046923 : Blo 1364501 2046923 := bstep (se 1 (by rfl) ⟨1535192, by rfl⟩ : syracuseStep 2046923 = 3070385) B3070385
theorem B2046935 : Blo 1364501 2046935 := bstep (se 1 (by rfl) ⟨1535201, by rfl⟩ : syracuseStep 2046935 = 3070403) B3070403
theorem B2047001 : Blo 1364501 2047001 := bstep (se 2 (by rfl) ⟨767625, by rfl⟩ : syracuseStep 2047001 = 1535251) B1535251
theorem B5184557 : Blo 1364501 5184557 := bstep (se 3 (by rfl) ⟨972104, by rfl⟩ : syracuseStep 5184557 = 1944209) B1944209
theorem B3693619 : Blo 1364501 3693619 := bstep (se 1 (by rfl) ⟨2770214, by rfl⟩ : syracuseStep 3693619 = 5540429) B5540429
theorem B3071051 : Blo 1364501 3071051 := bstep (se 1 (by rfl) ⟨2303288, by rfl⟩ : syracuseStep 3071051 = 4606577) B4606577
theorem B1727563 : Blo 1364501 1727563 := bstep (se 1 (by rfl) ⟨1295672, by rfl⟩ : syracuseStep 1727563 = 2591345) B2591345
theorem B5184587 : Blo 1364501 5184587 := bstep (se 1 (by rfl) ⟨3888440, by rfl⟩ : syracuseStep 5184587 = 7776881) B7776881
theorem B2767961 : Blo 1364501 2767961 := bstep (se 2 (by rfl) ⟨1037985, by rfl⟩ : syracuseStep 2767961 = 2075971) B2075971
theorem B3071105 : Blo 1364501 3071105 := bstep (se 2 (by rfl) ⟨1151664, by rfl⟩ : syracuseStep 3071105 = 2303329) B2303329
theorem B7781507 : Blo 1364501 7781507 := bstep (se 1 (by rfl) ⟨5836130, by rfl⟩ : syracuseStep 7781507 = 11672261) B11672261
theorem B2047115 : Blo 1364501 2047115 := bstep (se 1 (by rfl) ⟨1535336, by rfl⟩ : syracuseStep 2047115 = 3070673) B3070673
theorem B2047127 : Blo 1364501 2047127 := bstep (se 1 (by rfl) ⟨1535345, by rfl⟩ : syracuseStep 2047127 = 3070691) B3070691
theorem B9837719 : Blo 1364501 9837719 := bstep (se 1 (by rfl) ⟨7378289, by rfl⟩ : syracuseStep 9837719 = 14756579) B14756579
theorem B3456179 : Blo 1364501 3456179 := bstep (se 1 (by rfl) ⟨2592134, by rfl⟩ : syracuseStep 3456179 = 5184269) B5184269
theorem B5536961 : Blo 1364501 5536961 := bstep (se 2 (by rfl) ⟨2076360, by rfl⟩ : syracuseStep 5536961 = 4152721) B4152721
theorem B4611275 : Blo 1364501 4611275 := bstep (se 1 (by rfl) ⟨3458456, by rfl⟩ : syracuseStep 4611275 = 6916913) B6916913
theorem B2047193 : Blo 1364501 2047193 := bstep (se 2 (by rfl) ⟨767697, by rfl⟩ : syracuseStep 2047193 = 1535395) B1535395
theorem B12459329 : Blo 1364501 12459329 := bstep (se 2 (by rfl) ⟨4672248, by rfl⟩ : syracuseStep 12459329 = 9344497) B9344497
theorem B2047307 : Blo 1364501 2047307 := bstep (se 1 (by rfl) ⟨1535480, by rfl⟩ : syracuseStep 2047307 = 3070961) B3070961
theorem B7011659 : Blo 1364501 7011659 := bstep (se 1 (by rfl) ⟨5258744, by rfl⟩ : syracuseStep 7011659 = 10517489) B10517489
theorem B2047319 : Blo 1364501 2047319 := bstep (se 1 (by rfl) ⟨1535489, by rfl⟩ : syracuseStep 2047319 = 3070979) B3070979
theorem B1727831 : Blo 1364501 1727831 := bstep (se 1 (by rfl) ⟨1295873, by rfl⟩ : syracuseStep 1727831 = 2591747) B2591747
theorem B3071321 : Blo 1364501 3071321 := bstep (se 2 (by rfl) ⟨1151745, by rfl⟩ : syracuseStep 3071321 = 2303491) B2303491
theorem B15564149 : Blo 1364501 15564149 := bstep (se 5 (by rfl) ⟨729569, by rfl⟩ : syracuseStep 15564149 = 1459139) B1459139
theorem B2047385 : Blo 1364501 2047385 := bstep (se 2 (by rfl) ⟨767769, by rfl⟩ : syracuseStep 2047385 = 1535539) B1535539
theorem B1383851 : Blo 1364501 1383851 := bstep (se 1 (by rfl) ⟨1037888, by rfl⟩ : syracuseStep 1383851 = 2075777) B2075777
theorem B3071411 : Blo 1364501 3071411 := bstep (se 1 (by rfl) ⟨2303558, by rfl⟩ : syracuseStep 3071411 = 4607117) B4607117
theorem B3071447 : Blo 1364501 3071447 := bstep (se 1 (by rfl) ⟨2303585, by rfl⟩ : syracuseStep 3071447 = 4607171) B4607171
theorem B4611545 : Blo 1364501 4611545 := bstep (se 2 (by rfl) ⟨1729329, by rfl⟩ : syracuseStep 4611545 = 3458659) B3458659
theorem B2047499 : Blo 1364501 2047499 := bstep (se 1 (by rfl) ⟨1535624, by rfl⟩ : syracuseStep 2047499 = 3071249) B3071249
theorem B2047511 : Blo 1364501 2047511 := bstep (se 1 (by rfl) ⟨1535633, by rfl⟩ : syracuseStep 2047511 = 3071267) B3071267
theorem B1457687 : Blo 1364501 1457687 := bstep (se 1 (by rfl) ⟨1093265, by rfl⟩ : syracuseStep 1457687 = 2186531) B2186531
theorem B2047577 : Blo 1364501 2047577 := bstep (se 2 (by rfl) ⟨767841, by rfl⟩ : syracuseStep 2047577 = 1535683) B1535683
theorem B3071627 : Blo 1364501 3071627 := bstep (se 1 (by rfl) ⟨2303720, by rfl⟩ : syracuseStep 3071627 = 4607441) B4607441
theorem B25263797 : Blo 1364501 25263797 := bstep (se 5 (by rfl) ⟨1184240, by rfl⟩ : syracuseStep 25263797 = 2368481) B2368481
theorem B3071681 : Blo 1364501 3071681 := bstep (se 2 (by rfl) ⟨1151880, by rfl⟩ : syracuseStep 3071681 = 2303761) B2303761
theorem B2047691 : Blo 1364501 2047691 := bstep (se 1 (by rfl) ⟨1535768, by rfl⟩ : syracuseStep 2047691 = 3071537) B3071537
theorem B3456715 : Blo 1364501 3456715 := bstep (se 1 (by rfl) ⟨2592536, by rfl⟩ : syracuseStep 3456715 = 5185073) B5185073
theorem B2047703 : Blo 1364501 2047703 := bstep (se 1 (by rfl) ⟨1535777, by rfl⟩ : syracuseStep 2047703 = 3071555) B3071555
theorem B5185241 : Blo 1364501 5185241 := bstep (se 2 (by rfl) ⟨1944465, by rfl⟩ : syracuseStep 5185241 = 3888931) B3888931
theorem B2047769 : Blo 1364501 2047769 := bstep (se 2 (by rfl) ⟨767913, by rfl⟩ : syracuseStep 2047769 = 1535827) B1535827
theorem B3456857 : Blo 1364501 3456857 := bstep (se 2 (by rfl) ⟨1296321, by rfl⟩ : syracuseStep 3456857 = 2592643) B2592643
theorem B3112843 : Blo 1364501 3112843 := bstep (se 1 (by rfl) ⟨2334632, by rfl⟩ : syracuseStep 3112843 = 4669265) B4669265
theorem B2047883 : Blo 1364501 2047883 := bstep (se 1 (by rfl) ⟨1535912, by rfl⟩ : syracuseStep 2047883 = 3071825) B3071825
theorem B5832593 : Blo 1364501 5832593 := bstep (se 2 (by rfl) ⟨2187222, by rfl⟩ : syracuseStep 5832593 = 4374445) B4374445
theorem B2047895 : Blo 1364501 2047895 := bstep (se 1 (by rfl) ⟨1535921, by rfl⟩ : syracuseStep 2047895 = 3071843) B3071843
theorem B3071897 : Blo 1364501 3071897 := bstep (se 2 (by rfl) ⟨1151961, by rfl⟩ : syracuseStep 3071897 = 2303923) B2303923
theorem B4153267 : Blo 1364501 4153267 := bstep (se 1 (by rfl) ⟨3114950, by rfl⟩ : syracuseStep 4153267 = 6229901) B6229901
theorem B2047961 : Blo 1364501 2047961 := bstep (se 2 (by rfl) ⟨767985, by rfl⟩ : syracuseStep 2047961 = 1535971) B1535971
theorem B3071987 : Blo 1364501 3071987 := bstep (se 1 (by rfl) ⟨2303990, by rfl⟩ : syracuseStep 3071987 = 4607981) B4607981
theorem B2048015 : Blo 1364501 2048015 := bstep (se 1 (by rfl) ⟨1536011, by rfl⟩ : syracuseStep 2048015 = 3072023) B3072023
theorem B3457039 : Blo 1364501 3457039 := bstep (se 1 (by rfl) ⟨2592779, by rfl⟩ : syracuseStep 3457039 = 5185559) B5185559
theorem B4669483 : Blo 1364501 4669483 := bstep (se 1 (by rfl) ⟨3502112, by rfl⟩ : syracuseStep 4669483 = 7004225) B7004225
theorem B2048057 : Blo 1364501 2048057 := bstep (se 2 (by rfl) ⟨768021, by rfl⟩ : syracuseStep 2048057 = 1536043) B1536043
theorem B3072059 : Blo 1364501 3072059 := bstep (se 1 (by rfl) ⟨2304044, by rfl⟩ : syracuseStep 3072059 = 4608089) B4608089
theorem B1728631 : Blo 1364501 1728631 := bstep (se 1 (by rfl) ⟨1296473, by rfl⟩ : syracuseStep 1728631 = 2592947) B2592947
theorem B2048135 : Blo 1364501 2048135 := bstep (se 1 (by rfl) ⟨1536101, by rfl⟩ : syracuseStep 2048135 = 3072203) B3072203
theorem B2048171 : Blo 1364501 2048171 := bstep (se 1 (by rfl) ⟨1536128, by rfl⟩ : syracuseStep 2048171 = 3072257) B3072257
theorem B3072185 : Blo 1364501 3072185 := bstep (se 2 (by rfl) ⟨1152069, by rfl⟩ : syracuseStep 3072185 = 2304139) B2304139
theorem B2048201 : Blo 1364501 2048201 := bstep (se 2 (by rfl) ⟨768075, by rfl⟩ : syracuseStep 2048201 = 1536151) B1536151
theorem B3457313 : Blo 1364501 3457313 := bstep (se 2 (by rfl) ⟨1296492, by rfl⟩ : syracuseStep 3457313 = 2592985) B2592985
theorem B2048315 : Blo 1364501 2048315 := bstep (se 1 (by rfl) ⟨1536236, by rfl⟩ : syracuseStep 2048315 = 3072473) B3072473
theorem B2048375 : Blo 1364501 2048375 := bstep (se 1 (by rfl) ⟨1536281, by rfl⟩ : syracuseStep 2048375 = 3072563) B3072563
theorem B2998663 : Blo 1364501 2998663 := bstep (se 1 (by rfl) ⟨2248997, by rfl⟩ : syracuseStep 2998663 = 4497995) B4497995
theorem B2048399 : Blo 1364501 2048399 := bstep (se 1 (by rfl) ⟨1536299, by rfl⟩ : syracuseStep 2048399 = 3072599) B3072599
theorem B7774649 : Blo 1364501 7774649 := bstep (se 2 (by rfl) ⟨2915493, by rfl⟩ : syracuseStep 7774649 = 5830987) B5830987
theorem B2048441 : Blo 1364501 2048441 := bstep (se 2 (by rfl) ⟨768165, by rfl⟩ : syracuseStep 2048441 = 1536331) B1536331
theorem B1728955 : Blo 1364501 1728955 := bstep (se 1 (by rfl) ⟨1296716, by rfl⟩ : syracuseStep 1728955 = 2593433) B2593433
theorem B11076061 : Blo 1364501 11076061 := bstep (se 3 (by rfl) ⟨2076761, by rfl⟩ : syracuseStep 11076061 = 4153523) B4153523
theorem B2048519 : Blo 1364501 2048519 := bstep (se 1 (by rfl) ⟨1536389, by rfl⟩ : syracuseStep 2048519 = 3072779) B3072779
theorem B1458695 : Blo 1364501 1458695 := bstep (se 1 (by rfl) ⟨1094021, by rfl⟩ : syracuseStep 1458695 = 2188043) B2188043
theorem B3072527 : Blo 1364501 3072527 := bstep (se 1 (by rfl) ⟨2304395, by rfl⟩ : syracuseStep 3072527 = 4608791) B4608791
theorem B3072545 : Blo 1364501 3072545 := bstep (se 2 (by rfl) ⟨1152204, by rfl⟩ : syracuseStep 3072545 = 2304409) B2304409
theorem B2048555 : Blo 1364501 2048555 := bstep (se 1 (by rfl) ⟨1536416, by rfl⟩ : syracuseStep 2048555 = 3072833) B3072833
theorem B2048585 : Blo 1364501 2048585 := bstep (se 2 (by rfl) ⟨768219, by rfl⟩ : syracuseStep 2048585 = 1536439) B1536439
theorem B2048699 : Blo 1364501 2048699 := bstep (se 1 (by rfl) ⟨1536524, by rfl⟩ : syracuseStep 2048699 = 3073049) B3073049
theorem B2048759 : Blo 1364501 2048759 := bstep (se 1 (by rfl) ⟨1536569, by rfl⟩ : syracuseStep 2048759 = 3073139) B3073139
theorem B2302735 : Blo 1364501 2302735 := bstep (se 1 (by rfl) ⟨1727051, by rfl⟩ : syracuseStep 2302735 = 3454103) B3454103
theorem B2048783 : Blo 1364501 2048783 := bstep (se 1 (by rfl) ⟨1536587, by rfl⟩ : syracuseStep 2048783 = 3073175) B3073175
theorem B7381793 : Blo 1364501 7381793 := bstep (se 2 (by rfl) ⟨2768172, by rfl⟩ : syracuseStep 7381793 = 5536345) B5536345
theorem B2048825 : Blo 1364501 2048825 := bstep (se 2 (by rfl) ⟨768309, by rfl⟩ : syracuseStep 2048825 = 1536619) B1536619
theorem B3072887 : Blo 1364501 3072887 := bstep (se 1 (by rfl) ⟨2304665, by rfl⟩ : syracuseStep 3072887 = 4609331) B4609331
theorem B2048903 : Blo 1364501 2048903 := bstep (se 1 (by rfl) ⟨1536677, by rfl⟩ : syracuseStep 2048903 = 3073355) B3073355
theorem B5833619 : Blo 1364501 5833619 := bstep (se 1 (by rfl) ⟨4375214, by rfl⟩ : syracuseStep 5833619 = 8750429) B8750429
theorem B6914969 : Blo 1364501 6914969 := bstep (se 2 (by rfl) ⟨2593113, by rfl⟩ : syracuseStep 6914969 = 5186227) B5186227
theorem B2048939 : Blo 1364501 2048939 := bstep (se 1 (by rfl) ⟨1536704, by rfl⟩ : syracuseStep 2048939 = 3073409) B3073409
theorem B1729451 : Blo 1364501 1729451 := bstep (se 1 (by rfl) ⟨1297088, by rfl⟩ : syracuseStep 1729451 = 2594177) B2594177
theorem B2048969 : Blo 1364501 2048969 := bstep (se 2 (by rfl) ⟨768363, by rfl⟩ : syracuseStep 2048969 = 1536727) B1536727
theorem B3073067 : Blo 1364501 3073067 := bstep (se 1 (by rfl) ⟨2304800, by rfl⟩ : syracuseStep 3073067 = 4609601) B4609601
theorem B2049083 : Blo 1364501 2049083 := bstep (se 1 (by rfl) ⟨1536812, by rfl⟩ : syracuseStep 2049083 = 3073625) B3073625
theorem B2049143 : Blo 1364501 2049143 := bstep (se 1 (by rfl) ⟨1536857, by rfl⟩ : syracuseStep 2049143 = 3073715) B3073715
theorem B2049167 : Blo 1364501 2049167 := bstep (se 1 (by rfl) ⟨1536875, by rfl⟩ : syracuseStep 2049167 = 3073751) B3073751
theorem B2917561 : Blo 1364501 2917561 := bstep (se 2 (by rfl) ⟨1094085, by rfl⟩ : syracuseStep 2917561 = 2188171) B2188171
theorem B2049209 : Blo 1364501 2049209 := bstep (se 2 (by rfl) ⟨768453, by rfl⟩ : syracuseStep 2049209 = 1536907) B1536907
theorem B33227981 : Blo 1364501 33227981 := bstep (se 3 (by rfl) ⟨6230246, by rfl⟩ : syracuseStep 33227981 = 12460493) B12460493
theorem B2049287 : Blo 1364501 2049287 := bstep (se 1 (by rfl) ⟨1536965, by rfl⟩ : syracuseStep 2049287 = 3073931) B3073931
theorem B3458315 : Blo 1364501 3458315 := bstep (se 1 (by rfl) ⟨2593736, by rfl⟩ : syracuseStep 3458315 = 5187473) B5187473
theorem B2303275 : Blo 1364501 2303275 := bstep (se 1 (by rfl) ⟨1727456, by rfl⟩ : syracuseStep 2303275 = 3454913) B3454913
theorem B2049323 : Blo 1364501 2049323 := bstep (se 1 (by rfl) ⟨1536992, by rfl⟩ : syracuseStep 2049323 = 3073985) B3073985
theorem B2049353 : Blo 1364501 2049353 := bstep (se 2 (by rfl) ⟨768507, by rfl⟩ : syracuseStep 2049353 = 1537015) B1537015
theorem B1844615 : Blo 1364501 1844615 := bstep (se 1 (by rfl) ⟨1383461, by rfl⟩ : syracuseStep 1844615 = 2766923) B2766923
theorem B3073427 : Blo 1364501 3073427 := bstep (se 1 (by rfl) ⟨2305070, by rfl⟩ : syracuseStep 3073427 = 4610141) B4610141
theorem B2303417 : Blo 1364501 2303417 := bstep (se 2 (by rfl) ⟨863781, by rfl⟩ : syracuseStep 2303417 = 1727563) B1727563
theorem B2049467 : Blo 1364501 2049467 := bstep (se 1 (by rfl) ⟨1537100, by rfl⟩ : syracuseStep 2049467 = 3074201) B3074201
theorem B3073481 : Blo 1364501 3073481 := bstep (se 2 (by rfl) ⟨1152555, by rfl⟩ : syracuseStep 3073481 = 2305111) B2305111
theorem B2049527 : Blo 1364501 2049527 := bstep (se 1 (by rfl) ⟨1537145, by rfl⟩ : syracuseStep 2049527 = 3074291) B3074291
theorem B2917903 : Blo 1364501 2917903 := bstep (se 1 (by rfl) ⟨2188427, by rfl⟩ : syracuseStep 2917903 = 4376855) B4376855
theorem B2049551 : Blo 1364501 2049551 := bstep (se 1 (by rfl) ⟨1537163, by rfl⟩ : syracuseStep 2049551 = 3074327) B3074327
theorem B2049593 : Blo 1364501 2049593 := bstep (se 2 (by rfl) ⟨768597, by rfl⟩ : syracuseStep 2049593 = 1537195) B1537195
theorem B68257349 : Blo 1364501 68257349 := bstep (se 4 (by rfl) ⟨6399126, by rfl⟩ : syracuseStep 68257349 = 12798253) B12798253
theorem B1640071 : Blo 1364501 1640071 := bstep (se 1 (by rfl) ⟨1230053, by rfl⟩ : syracuseStep 1640071 = 2460107) B2460107
theorem B2049671 : Blo 1364501 2049671 := bstep (se 1 (by rfl) ⟨1537253, by rfl⟩ : syracuseStep 2049671 = 3074507) B3074507
theorem B2049707 : Blo 1364501 2049707 := bstep (se 1 (by rfl) ⟨1537280, by rfl⟩ : syracuseStep 2049707 = 3074561) B3074561
theorem B17499827 : Blo 1364501 17499827 := bstep (se 1 (by rfl) ⟨13124870, by rfl⟩ : syracuseStep 17499827 = 26249741) B26249741
theorem B2049737 : Blo 1364501 2049737 := bstep (se 2 (by rfl) ⟨768651, by rfl⟩ : syracuseStep 2049737 = 1537303) B1537303
theorem B14018305 : Blo 1364501 14018305 := bstep (se 2 (by rfl) ⟨5256864, by rfl⟩ : syracuseStep 14018305 = 10513729) B10513729
theorem B14755621 : Blo 1364501 14755621 := bstep (se 4 (by rfl) ⟨1383339, by rfl⟩ : syracuseStep 14755621 = 2766679) B2766679
theorem B9848729 : Blo 1364501 9848729 := bstep (se 2 (by rfl) ⟨3693273, by rfl⟩ : syracuseStep 9848729 = 7386547) B7386547
theorem B1640455 : Blo 1364501 1640455 := bstep (se 1 (by rfl) ⟨1230341, by rfl⟩ : syracuseStep 1640455 = 2460683) B2460683
theorem B3688507 : Blo 1364501 3688507 := bstep (se 1 (by rfl) ⟨2766380, by rfl⟩ : syracuseStep 3688507 = 5532761) B5532761
theorem B1845307 : Blo 1364501 1845307 := bstep (se 1 (by rfl) ⟨1383980, by rfl⟩ : syracuseStep 1845307 = 2767961) B2767961
theorem B5187671 : Blo 1364501 5187671 := bstep (se 1 (by rfl) ⟨3890753, by rfl⟩ : syracuseStep 5187671 = 7781507) B7781507
theorem B2304119 : Blo 1364501 2304119 := bstep (se 1 (by rfl) ⟨1728089, by rfl⟩ : syracuseStep 2304119 = 3456179) B3456179
theorem B3074183 : Blo 1364501 3074183 := bstep (se 1 (by rfl) ⟨2305637, by rfl⟩ : syracuseStep 3074183 = 4611275) B4611275
theorem B2459963 : Blo 1364501 2459963 := bstep (se 1 (by rfl) ⟨1844972, by rfl⟩ : syracuseStep 2459963 = 3689945) B3689945
theorem B3074363 : Blo 1364501 3074363 := bstep (se 1 (by rfl) ⟨2305772, by rfl⟩ : syracuseStep 3074363 = 4611545) B4611545
theorem B4606361 : Blo 1364501 4606361 := bstep (se 2 (by rfl) ⟨1727385, by rfl⟩ : syracuseStep 4606361 = 3454771) B3454771
theorem B3074489 : Blo 1364501 3074489 := bstep (se 2 (by rfl) ⟨1152933, by rfl⟩ : syracuseStep 3074489 = 2305867) B2305867
theorem B2591291 : Blo 1364501 2591291 := bstep (se 1 (by rfl) ⟨1943468, by rfl⟩ : syracuseStep 2591291 = 3886937) B3886937
theorem B2304571 : Blo 1364501 2304571 := bstep (se 1 (by rfl) ⟨1728428, by rfl⟩ : syracuseStep 2304571 = 3456857) B3456857
theorem B5188157 : Blo 1364501 5188157 := bstep (se 3 (by rfl) ⟨972779, by rfl⟩ : syracuseStep 5188157 = 1945559) B1945559
theorem B2304713 : Blo 1364501 2304713 := bstep (se 2 (by rfl) ⟨864267, by rfl⟩ : syracuseStep 2304713 = 1728535) B1728535
theorem B9841409 : Blo 1364501 9841409 := bstep (se 2 (by rfl) ⟨3690528, by rfl⟩ : syracuseStep 9841409 = 7381057) B7381057
theorem B6228737 : Blo 1364501 6228737 := bstep (se 2 (by rfl) ⟨2335776, by rfl⟩ : syracuseStep 6228737 = 4671553) B4671553
theorem B5835635 : Blo 1364501 5835635 := bstep (se 1 (by rfl) ⟨4376726, by rfl⟩ : syracuseStep 5835635 = 8753453) B8753453
theorem B4918283 : Blo 1364501 4918283 := bstep (se 1 (by rfl) ⟨3688712, by rfl⟩ : syracuseStep 4918283 = 7377425) B7377425
theorem B10374155 : Blo 1364501 10374155 := bstep (se 1 (by rfl) ⟨7780616, by rfl⟩ : syracuseStep 10374155 = 15561233) B15561233
theorem B2591777 : Blo 1364501 2591777 := bstep (se 2 (by rfl) ⟨971916, by rfl⟩ : syracuseStep 2591777 = 1943833) B1943833
theorem B4607063 : Blo 1364501 4607063 := bstep (se 1 (by rfl) ⟨3455297, by rfl⟩ : syracuseStep 4607063 = 6910595) B6910595
theorem B2591929 : Blo 1364501 2591929 := bstep (se 2 (by rfl) ⟨971973, by rfl⟩ : syracuseStep 2591929 = 1943947) B1943947
theorem B1944847 : Blo 1364501 1944847 := bstep (se 1 (by rfl) ⟨1458635, by rfl⟩ : syracuseStep 1944847 = 2917271) B2917271
theorem B23317793 : Blo 1364501 23317793 := bstep (se 2 (by rfl) ⟨8744172, by rfl⟩ : syracuseStep 23317793 = 17488345) B17488345
theorem B6909299 : Blo 1364501 6909299 := bstep (se 1 (by rfl) ⟨5181974, by rfl⟩ : syracuseStep 6909299 = 10363949) B10363949
theorem B1944967 : Blo 1364501 1944967 := bstep (se 1 (by rfl) ⟨1458725, by rfl⟩ : syracuseStep 1944967 = 2917451) B2917451
theorem B2305415 : Blo 1364501 2305415 := bstep (se 1 (by rfl) ⟨1729061, by rfl⟩ : syracuseStep 2305415 = 3458123) B3458123
theorem B15543737 : Blo 1364501 15543737 := bstep (se 2 (by rfl) ⟨5828901, by rfl⟩ : syracuseStep 15543737 = 11657803) B11657803
theorem B6917561 : Blo 1364501 6917561 := bstep (se 2 (by rfl) ⟨2594085, by rfl⟩ : syracuseStep 6917561 = 5188171) B5188171
theorem B5180881 : Blo 1364501 5180881 := bstep (se 2 (by rfl) ⟨1942830, by rfl⟩ : syracuseStep 5180881 = 3885661) B3885661
theorem B16829905 : Blo 1364501 16829905 := bstep (se 2 (by rfl) ⟨6311214, by rfl⟩ : syracuseStep 16829905 = 12622429) B12622429
theorem B6655441 : Blo 1364501 6655441 := bstep (se 2 (by rfl) ⟨2495790, by rfl⟩ : syracuseStep 6655441 = 4991581) B4991581
theorem B16616963 : Blo 1364501 16616963 := bstep (se 1 (by rfl) ⟨12462722, by rfl⟩ : syracuseStep 16616963 = 24925445) B24925445
theorem B1535503 : Blo 1364501 1535503 := bstep (se 1 (by rfl) ⟨1151627, by rfl⟩ : syracuseStep 1535503 = 2303255) B2303255
theorem B4607549 : Blo 1364501 4607549 := bstep (se 3 (by rfl) ⟨863915, by rfl⟩ : syracuseStep 4607549 = 1727831) B1727831
theorem B6565495 : Blo 1364501 6565495 := bstep (se 1 (by rfl) ⟨4924121, by rfl⟩ : syracuseStep 6565495 = 9848243) B9848243
theorem B5181185 : Blo 1364501 5181185 := bstep (se 2 (by rfl) ⟨1942944, by rfl⟩ : syracuseStep 5181185 = 3885889) B3885889
theorem B3690269 : Blo 1364501 3690269 := bstep (se 3 (by rfl) ⟨691925, by rfl⟩ : syracuseStep 3690269 = 1383851) B1383851
theorem B11669285 : Blo 1364501 11669285 := bstep (se 4 (by rfl) ⟨1093995, by rfl⟩ : syracuseStep 11669285 = 2187991) B2187991
theorem B6909785 : Blo 1364501 6909785 := bstep (se 2 (by rfl) ⟨2591169, by rfl⟩ : syracuseStep 6909785 = 5182339) B5182339
theorem B5533555 : Blo 1364501 5533555 := bstep (se 1 (by rfl) ⟨4150166, by rfl⟩ : syracuseStep 5533555 = 8300333) B8300333
theorem B5828561 : Blo 1364501 5828561 := bstep (se 2 (by rfl) ⟨2185710, by rfl⟩ : syracuseStep 5828561 = 4371421) B4371421
theorem B1536007 : Blo 1364501 1536007 := bstep (se 1 (by rfl) ⟨1152005, by rfl⟩ : syracuseStep 1536007 = 2304011) B2304011
theorem B3887119 : Blo 1364501 3887119 := bstep (se 1 (by rfl) ⟨2915339, by rfl⟩ : syracuseStep 3887119 = 5830679) B5830679
theorem B3887165 : Blo 1364501 3887165 := bstep (se 3 (by rfl) ⟨728843, by rfl⟩ : syracuseStep 3887165 = 1457687) B1457687
theorem B6737987 : Blo 1364501 6737987 := bstep (se 1 (by rfl) ⟨5053490, by rfl⟩ : syracuseStep 6737987 = 10106981) B10106981
theorem B1536187 : Blo 1364501 1536187 := bstep (se 1 (by rfl) ⟨1152140, by rfl⟩ : syracuseStep 1536187 = 2304281) B2304281
theorem B5181641 : Blo 1364501 5181641 := bstep (se 2 (by rfl) ⟨1943115, by rfl⟩ : syracuseStep 5181641 = 3886231) B3886231
theorem B7385381 : Blo 1364501 7385381 := bstep (se 4 (by rfl) ⟨692379, by rfl⟩ : syracuseStep 7385381 = 1384759) B1384759
theorem B9843079 : Blo 1364501 9843079 := bstep (se 1 (by rfl) ⟨7382309, by rfl⟩ : syracuseStep 9843079 = 14764619) B14764619
theorem B3887507 : Blo 1364501 3887507 := bstep (se 1 (by rfl) ⟨2915630, by rfl⟩ : syracuseStep 3887507 = 5831261) B5831261
theorem B1364539 : Blo 1364501 1364539 := bstep (se 1 (by rfl) ⟨1023404, by rfl⟩ : syracuseStep 1364539 = 2046809) B2046809
theorem B1364615 : Blo 1364501 1364615 := bstep (se 1 (by rfl) ⟨1023461, by rfl⟩ : syracuseStep 1364615 = 2046923) B2046923
theorem B1364623 : Blo 1364501 1364623 := bstep (se 1 (by rfl) ⟨1023467, by rfl⟩ : syracuseStep 1364623 = 2046935) B2046935
theorem B1536655 : Blo 1364501 1536655 := bstep (se 1 (by rfl) ⟨1152491, by rfl⟩ : syracuseStep 1536655 = 2304983) B2304983
theorem B2077369 : Blo 1364501 2077369 := bstep (se 2 (by rfl) ⟨779013, by rfl⟩ : syracuseStep 2077369 = 1558027) B1558027
theorem B1364667 : Blo 1364501 1364667 := bstep (se 1 (by rfl) ⟨1023500, by rfl⟩ : syracuseStep 1364667 = 2047001) B2047001
theorem B1364743 : Blo 1364501 1364743 := bstep (se 1 (by rfl) ⟨1023557, by rfl⟩ : syracuseStep 1364743 = 2047115) B2047115
theorem B1364751 : Blo 1364501 1364751 := bstep (se 1 (by rfl) ⟨1023563, by rfl⟩ : syracuseStep 1364751 = 2047127) B2047127
theorem B6558479 : Blo 1364501 6558479 := bstep (se 1 (by rfl) ⟨4918859, by rfl⟩ : syracuseStep 6558479 = 9837719) B9837719
theorem B4920097 : Blo 1364501 4920097 := bstep (se 2 (by rfl) ⟨1845036, by rfl⟩ : syracuseStep 4920097 = 3690073) B3690073
theorem B15971107 : Blo 1364501 15971107 := bstep (se 1 (by rfl) ⟨11978330, by rfl⟩ : syracuseStep 15971107 = 23956661) B23956661
theorem B3691307 : Blo 1364501 3691307 := bstep (se 1 (by rfl) ⟨2768480, by rfl⟩ : syracuseStep 3691307 = 5536961) B5536961
theorem B1971001 : Blo 1364501 1971001 := bstep (se 2 (by rfl) ⟨739125, by rfl⟩ : syracuseStep 1971001 = 1478251) B1478251
theorem B1364795 : Blo 1364501 1364795 := bstep (se 1 (by rfl) ⟨1023596, by rfl⟩ : syracuseStep 1364795 = 2047193) B2047193
theorem B1364871 : Blo 1364501 1364871 := bstep (se 1 (by rfl) ⟨1023653, by rfl⟩ : syracuseStep 1364871 = 2047307) B2047307
theorem B4674439 : Blo 1364501 4674439 := bstep (se 1 (by rfl) ⟨3505829, by rfl⟩ : syracuseStep 4674439 = 7011659) B7011659
theorem B1364879 : Blo 1364501 1364879 := bstep (se 1 (by rfl) ⟨1023659, by rfl⟩ : syracuseStep 1364879 = 2047319) B2047319
theorem B14398361 : Blo 1364501 14398361 := bstep (se 2 (by rfl) ⟨5399385, by rfl⟩ : syracuseStep 14398361 = 10798771) B10798771
theorem B10376099 : Blo 1364501 10376099 := bstep (se 1 (by rfl) ⟨7782074, by rfl⟩ : syracuseStep 10376099 = 15564149) B15564149
theorem B4608953 : Blo 1364501 4608953 := bstep (se 2 (by rfl) ⟨1728357, by rfl⟩ : syracuseStep 4608953 = 3456715) B3456715
theorem B2593721 : Blo 1364501 2593721 := bstep (se 2 (by rfl) ⟨972645, by rfl⟩ : syracuseStep 2593721 = 1945291) B1945291
theorem B1364923 : Blo 1364501 1364923 := bstep (se 1 (by rfl) ⟨1023692, by rfl⟩ : syracuseStep 1364923 = 2047385) B2047385
theorem B1364999 : Blo 1364501 1364999 := bstep (se 1 (by rfl) ⟨1023749, by rfl⟩ : syracuseStep 1364999 = 2047499) B2047499
theorem B8745995 : Blo 1364501 8745995 := bstep (se 1 (by rfl) ⟨6559496, by rfl⟩ : syracuseStep 8745995 = 13118993) B13118993
theorem B1365007 : Blo 1364501 1365007 := bstep (se 1 (by rfl) ⟨1023755, by rfl⟩ : syracuseStep 1365007 = 2047511) B2047511
theorem B1365051 : Blo 1364501 1365051 := bstep (se 1 (by rfl) ⟨1023788, by rfl⟩ : syracuseStep 1365051 = 2047577) B2047577
theorem B1365127 : Blo 1364501 1365127 := bstep (se 1 (by rfl) ⟨1023845, by rfl⟩ : syracuseStep 1365127 = 2047691) B2047691
theorem B1537159 : Blo 1364501 1537159 := bstep (se 1 (by rfl) ⟨1152869, by rfl⟩ : syracuseStep 1537159 = 2305739) B2305739
theorem B1365135 : Blo 1364501 1365135 := bstep (se 1 (by rfl) ⟨1023851, by rfl⟩ : syracuseStep 1365135 = 2047703) B2047703
theorem B4150457 : Blo 1364501 4150457 := bstep (se 2 (by rfl) ⟨1556421, by rfl⟩ : syracuseStep 4150457 = 3112843) B3112843
theorem B1365179 : Blo 1364501 1365179 := bstep (se 1 (by rfl) ⟨1023884, by rfl⟩ : syracuseStep 1365179 = 2047769) B2047769
theorem B1365255 : Blo 1364501 1365255 := bstep (se 1 (by rfl) ⟨1023941, by rfl⟩ : syracuseStep 1365255 = 2047883) B2047883
theorem B3888395 : Blo 1364501 3888395 := bstep (se 1 (by rfl) ⟨2916296, by rfl⟩ : syracuseStep 3888395 = 5832593) B5832593
theorem B1365263 : Blo 1364501 1365263 := bstep (se 1 (by rfl) ⟨1023947, by rfl⟩ : syracuseStep 1365263 = 2047895) B2047895
theorem B3282209 : Blo 1364501 3282209 := bstep (se 2 (by rfl) ⟨1230828, by rfl⟩ : syracuseStep 3282209 = 2461657) B2461657
theorem B1365307 : Blo 1364501 1365307 := bstep (se 1 (by rfl) ⟨1023980, by rfl⟩ : syracuseStep 1365307 = 2047961) B2047961
theorem B3282295 : Blo 1364501 3282295 := bstep (se 1 (by rfl) ⟨2461721, by rfl⟩ : syracuseStep 3282295 = 4923443) B4923443
theorem B1365383 : Blo 1364501 1365383 := bstep (se 1 (by rfl) ⟨1024037, by rfl⟩ : syracuseStep 1365383 = 2048075) B2048075
theorem B1365391 : Blo 1364501 1365391 := bstep (se 1 (by rfl) ⟨1024043, by rfl⟩ : syracuseStep 1365391 = 2048087) B2048087
theorem B21018041 : Blo 1364501 21018041 := bstep (se 2 (by rfl) ⟨7881765, by rfl⟩ : syracuseStep 21018041 = 15763531) B15763531
theorem B1365435 : Blo 1364501 1365435 := bstep (se 1 (by rfl) ⟨1024076, by rfl⟩ : syracuseStep 1365435 = 2048153) B2048153
theorem B1750519 : Blo 1364501 1750519 := bstep (se 1 (by rfl) ⟨1312889, by rfl⟩ : syracuseStep 1750519 = 2625779) B2625779
theorem B1365511 : Blo 1364501 1365511 := bstep (se 1 (by rfl) ⟨1024133, by rfl⟩ : syracuseStep 1365511 = 2048267) B2048267
theorem B4609547 : Blo 1364501 4609547 := bstep (se 1 (by rfl) ⟨3457160, by rfl⟩ : syracuseStep 4609547 = 6914321) B6914321
theorem B1365519 : Blo 1364501 1365519 := bstep (se 1 (by rfl) ⟨1024139, by rfl⟩ : syracuseStep 1365519 = 2048279) B2048279
theorem B12629533 : Blo 1364501 12629533 := bstep (se 3 (by rfl) ⟨2368037, by rfl⟩ : syracuseStep 12629533 = 4736075) B4736075
theorem B1365563 : Blo 1364501 1365563 := bstep (se 1 (by rfl) ⟨1024172, by rfl⟩ : syracuseStep 1365563 = 2048345) B2048345
theorem B44283469 : Blo 1364501 44283469 := bstep (se 3 (by rfl) ⟨8303150, by rfl⟩ : syracuseStep 44283469 = 16606301) B16606301
theorem B19699301 : Blo 1364501 19699301 := bstep (se 4 (by rfl) ⟨1846809, by rfl⟩ : syracuseStep 19699301 = 3693619) B3693619
theorem B4609655 : Blo 1364501 4609655 := bstep (se 1 (by rfl) ⟨3457241, by rfl⟩ : syracuseStep 4609655 = 6914483) B6914483
theorem B1365639 : Blo 1364501 1365639 := bstep (se 1 (by rfl) ⟨1024229, by rfl⟩ : syracuseStep 1365639 = 2048459) B2048459
theorem B1365647 : Blo 1364501 1365647 := bstep (se 1 (by rfl) ⟨1024235, by rfl⟩ : syracuseStep 1365647 = 2048471) B2048471
theorem B1365691 : Blo 1364501 1365691 := bstep (se 1 (by rfl) ⟨1024268, by rfl⟩ : syracuseStep 1365691 = 2048537) B2048537
theorem B3454721 : Blo 1364501 3454721 := bstep (se 2 (by rfl) ⟨1295520, by rfl⟩ : syracuseStep 3454721 = 2591041) B2591041
theorem B1365767 : Blo 1364501 1365767 := bstep (se 1 (by rfl) ⟨1024325, by rfl⟩ : syracuseStep 1365767 = 2048651) B2048651
theorem B1365775 : Blo 1364501 1365775 := bstep (se 1 (by rfl) ⟨1024331, by rfl⟩ : syracuseStep 1365775 = 2048663) B2048663
theorem B1365819 : Blo 1364501 1365819 := bstep (se 1 (by rfl) ⟨1024364, by rfl⟩ : syracuseStep 1365819 = 2048729) B2048729
theorem B1365895 : Blo 1364501 1365895 := bstep (se 1 (by rfl) ⟨1024421, by rfl⟩ : syracuseStep 1365895 = 2048843) B2048843
theorem B1365903 : Blo 1364501 1365903 := bstep (se 1 (by rfl) ⟨1024427, by rfl⟩ : syracuseStep 1365903 = 2048855) B2048855
theorem B7772051 : Blo 1364501 7772051 := bstep (se 1 (by rfl) ⟨5829038, by rfl⟩ : syracuseStep 7772051 = 11658077) B11658077
theorem B6911891 : Blo 1364501 6911891 := bstep (se 1 (by rfl) ⟨5183918, by rfl⟩ : syracuseStep 6911891 = 10367837) B10367837
theorem B1365947 : Blo 1364501 1365947 := bstep (se 1 (by rfl) ⟨1024460, by rfl⟩ : syracuseStep 1365947 = 2048921) B2048921
theorem B1366023 : Blo 1364501 1366023 := bstep (se 1 (by rfl) ⟨1024517, by rfl⟩ : syracuseStep 1366023 = 2049035) B2049035
theorem B1366031 : Blo 1364501 1366031 := bstep (se 1 (by rfl) ⟨1024523, by rfl⟩ : syracuseStep 1366031 = 2049047) B2049047
theorem B2955323 : Blo 1364501 2955323 := bstep (se 1 (by rfl) ⟨2216492, by rfl⟩ : syracuseStep 2955323 = 4432985) B4432985
theorem B1366075 : Blo 1364501 1366075 := bstep (se 1 (by rfl) ⟨1024556, by rfl⟩ : syracuseStep 1366075 = 2049113) B2049113
theorem B6559805 : Blo 1364501 6559805 := bstep (se 3 (by rfl) ⟨1229963, by rfl⟩ : syracuseStep 6559805 = 2459927) B2459927
theorem B3455095 : Blo 1364501 3455095 := bstep (se 1 (by rfl) ⟨2591321, by rfl⟩ : syracuseStep 3455095 = 5182643) B5182643
theorem B1366151 : Blo 1364501 1366151 := bstep (se 1 (by rfl) ⟨1024613, by rfl⟩ : syracuseStep 1366151 = 2049227) B2049227
theorem B1366159 : Blo 1364501 1366159 := bstep (se 1 (by rfl) ⟨1024619, by rfl⟩ : syracuseStep 1366159 = 2049239) B2049239
theorem B1366203 : Blo 1364501 1366203 := bstep (se 1 (by rfl) ⟨1024652, by rfl⟩ : syracuseStep 1366203 = 2049305) B2049305
theorem B4610249 : Blo 1364501 4610249 := bstep (se 2 (by rfl) ⟨1728843, by rfl⟩ : syracuseStep 4610249 = 3457687) B3457687
theorem B1366279 : Blo 1364501 1366279 := bstep (se 1 (by rfl) ⟨1024709, by rfl⟩ : syracuseStep 1366279 = 2049419) B2049419
theorem B3070223 : Blo 1364501 3070223 := bstep (se 1 (by rfl) ⟨2302667, by rfl⟩ : syracuseStep 3070223 = 4605335) B4605335
theorem B1366287 : Blo 1364501 1366287 := bstep (se 1 (by rfl) ⟨1024715, by rfl⟩ : syracuseStep 1366287 = 2049431) B2049431
theorem B3070241 : Blo 1364501 3070241 := bstep (se 2 (by rfl) ⟨1151340, by rfl⟩ : syracuseStep 3070241 = 2302681) B2302681
theorem B1366331 : Blo 1364501 1366331 := bstep (se 1 (by rfl) ⟨1024748, by rfl⟩ : syracuseStep 1366331 = 2049497) B2049497
theorem B26589505 : Blo 1364501 26589505 := bstep (se 2 (by rfl) ⟨9971064, by rfl⟩ : syracuseStep 26589505 = 19942129) B19942129
theorem B15989123 : Blo 1364501 15989123 := bstep (se 1 (by rfl) ⟨11991842, by rfl⟩ : syracuseStep 15989123 = 23983685) B23983685
theorem B1366407 : Blo 1364501 1366407 := bstep (se 1 (by rfl) ⟨1024805, by rfl⟩ : syracuseStep 1366407 = 2049611) B2049611
theorem B1366415 : Blo 1364501 1366415 := bstep (se 1 (by rfl) ⟨1024811, by rfl⟩ : syracuseStep 1366415 = 2049623) B2049623
theorem B1751467 : Blo 1364501 1751467 := bstep (se 1 (by rfl) ⟨1313600, by rfl⟩ : syracuseStep 1751467 = 2627201) B2627201
theorem B1366459 : Blo 1364501 1366459 := bstep (se 1 (by rfl) ⟨1024844, by rfl⟩ : syracuseStep 1366459 = 2049689) B2049689
theorem B3455531 : Blo 1364501 3455531 := bstep (se 1 (by rfl) ⟨2591648, by rfl⟩ : syracuseStep 3455531 = 5183297) B5183297
theorem B7772759 : Blo 1364501 7772759 := bstep (se 1 (by rfl) ⟨5829569, by rfl⟩ : syracuseStep 7772759 = 11659139) B11659139
theorem B3070583 : Blo 1364501 3070583 := bstep (se 1 (by rfl) ⟨2302937, by rfl⟩ : syracuseStep 3070583 = 4605875) B4605875
theorem B1727239 : Blo 1364501 1727239 := bstep (se 1 (by rfl) ⟨1295429, by rfl⟩ : syracuseStep 1727239 = 2590859) B2590859
theorem B3070763 : Blo 1364501 3070763 := bstep (se 1 (by rfl) ⟨2303072, by rfl⟩ : syracuseStep 3070763 = 4606145) B4606145
theorem B2046779 : Blo 1364501 2046779 := bstep (se 1 (by rfl) ⟨1535084, by rfl⟩ : syracuseStep 2046779 = 3070169) B3070169
theorem B3890035 : Blo 1364501 3890035 := bstep (se 1 (by rfl) ⟨2917526, by rfl⟩ : syracuseStep 3890035 = 5835053) B5835053
theorem B2046839 : Blo 1364501 2046839 := bstep (se 1 (by rfl) ⟨1535129, by rfl⟩ : syracuseStep 2046839 = 3070259) B3070259
theorem B4610951 : Blo 1364501 4610951 := bstep (se 1 (by rfl) ⟨3458213, by rfl⟩ : syracuseStep 4610951 = 6916427) B6916427
theorem B7781255 : Blo 1364501 7781255 := bstep (se 1 (by rfl) ⟨5835941, by rfl⟩ : syracuseStep 7781255 = 11671883) B11671883
theorem B2046863 : Blo 1364501 2046863 := bstep (se 1 (by rfl) ⟨1535147, by rfl⟩ : syracuseStep 2046863 = 3070295) B3070295
theorem B26246051 : Blo 1364501 26246051 := bstep (se 1 (by rfl) ⟨19684538, by rfl⟩ : syracuseStep 26246051 = 39369077) B39369077
theorem B2046905 : Blo 1364501 2046905 := bstep (se 2 (by rfl) ⟨767589, by rfl⟩ : syracuseStep 2046905 = 1535179) B1535179
theorem B2046983 : Blo 1364501 2046983 := bstep (se 1 (by rfl) ⟨1535237, by rfl⟩ : syracuseStep 2046983 = 3070475) B3070475
theorem B2047019 : Blo 1364501 2047019 := bstep (se 1 (by rfl) ⟨1535264, by rfl⟩ : syracuseStep 2047019 = 3070529) B3070529
theorem B2047049 : Blo 1364501 2047049 := bstep (se 2 (by rfl) ⟨767643, by rfl⟩ : syracuseStep 2047049 = 1535287) B1535287
theorem B3890263 : Blo 1364501 3890263 := bstep (se 1 (by rfl) ⟨2917697, by rfl⟩ : syracuseStep 3890263 = 5835395) B5835395
theorem B67370125 : Blo 1364501 67370125 := bstep (se 3 (by rfl) ⟨12631898, by rfl⟩ : syracuseStep 67370125 = 25263797) B25263797
theorem B3071123 : Blo 1364501 3071123 := bstep (se 1 (by rfl) ⟨2303342, by rfl⟩ : syracuseStep 3071123 = 4606685) B4606685
theorem B1727659 : Blo 1364501 1727659 := bstep (se 1 (by rfl) ⟨1295744, by rfl⟩ : syracuseStep 1727659 = 2591489) B2591489
theorem B2047163 : Blo 1364501 2047163 := bstep (se 1 (by rfl) ⟨1535372, by rfl⟩ : syracuseStep 2047163 = 3070745) B3070745
theorem B3071177 : Blo 1364501 3071177 := bstep (se 2 (by rfl) ⟨1151691, by rfl⟩ : syracuseStep 3071177 = 2303383) B2303383
theorem B2047223 : Blo 1364501 2047223 := bstep (se 1 (by rfl) ⟨1535417, by rfl⟩ : syracuseStep 2047223 = 3070835) B3070835
theorem B5184769 : Blo 1364501 5184769 := bstep (se 2 (by rfl) ⟨1944288, by rfl⟩ : syracuseStep 5184769 = 3888577) B3888577
theorem B4611329 : Blo 1364501 4611329 := bstep (se 2 (by rfl) ⟨1729248, by rfl⟩ : syracuseStep 4611329 = 3458497) B3458497
theorem B2047247 : Blo 1364501 2047247 := bstep (se 1 (by rfl) ⟨1535435, by rfl⟩ : syracuseStep 2047247 = 3070871) B3070871
theorem B2047289 : Blo 1364501 2047289 := bstep (se 2 (by rfl) ⟨767733, by rfl⟩ : syracuseStep 2047289 = 1535467) B1535467
theorem B3456371 : Blo 1364501 3456371 := bstep (se 1 (by rfl) ⟨2592278, by rfl⟩ : syracuseStep 3456371 = 5184557) B5184557
theorem B2047367 : Blo 1364501 2047367 := bstep (se 1 (by rfl) ⟨1535525, by rfl⟩ : syracuseStep 2047367 = 3071051) B3071051
theorem B3456391 : Blo 1364501 3456391 := bstep (se 1 (by rfl) ⟨2592293, by rfl⟩ : syracuseStep 3456391 = 5184587) B5184587
theorem B1727887 : Blo 1364501 1727887 := bstep (se 1 (by rfl) ⟨1295915, by rfl⟩ : syracuseStep 1727887 = 2591831) B2591831
theorem B2047403 : Blo 1364501 2047403 := bstep (se 1 (by rfl) ⟨1535552, by rfl⟩ : syracuseStep 2047403 = 3071105) B3071105
theorem B2047433 : Blo 1364501 2047433 := bstep (se 2 (by rfl) ⟨767787, by rfl⟩ : syracuseStep 2047433 = 1535575) B1535575
theorem B8306219 : Blo 1364501 8306219 := bstep (se 1 (by rfl) ⟨6229664, by rfl⟩ : syracuseStep 8306219 = 12459329) B12459329
theorem B2047547 : Blo 1364501 2047547 := bstep (se 1 (by rfl) ⟨1535660, by rfl⟩ : syracuseStep 2047547 = 3071321) B3071321
theorem B2047607 : Blo 1364501 2047607 := bstep (se 1 (by rfl) ⟨1535705, by rfl⟩ : syracuseStep 2047607 = 3071411) B3071411
theorem B2047631 : Blo 1364501 2047631 := bstep (se 1 (by rfl) ⟨1535723, by rfl⟩ : syracuseStep 2047631 = 3071447) B3071447
theorem B3456665 : Blo 1364501 3456665 := bstep (se 2 (by rfl) ⟨1296249, by rfl⟩ : syracuseStep 3456665 = 2592499) B2592499
theorem B2047673 : Blo 1364501 2047673 := bstep (se 2 (by rfl) ⟨767877, by rfl⟩ : syracuseStep 2047673 = 1535755) B1535755
theorem B10370753 : Blo 1364501 10370753 := bstep (se 2 (by rfl) ⟨3889032, by rfl⟩ : syracuseStep 10370753 = 7778065) B7778065
theorem B2047751 : Blo 1364501 2047751 := bstep (se 1 (by rfl) ⟨1535813, by rfl⟩ : syracuseStep 2047751 = 3071627) B3071627
theorem B2047787 : Blo 1364501 2047787 := bstep (se 1 (by rfl) ⟨1535840, by rfl⟩ : syracuseStep 2047787 = 3071681) B3071681
theorem B3456827 : Blo 1364501 3456827 := bstep (se 1 (by rfl) ⟨2592620, by rfl⟩ : syracuseStep 3456827 = 5185241) B5185241
theorem B2047817 : Blo 1364501 2047817 := bstep (se 2 (by rfl) ⟨767931, by rfl⟩ : syracuseStep 2047817 = 1535863) B1535863
theorem B3071879 : Blo 1364501 3071879 := bstep (se 1 (by rfl) ⟨2303909, by rfl⟩ : syracuseStep 3071879 = 4607819) B4607819
theorem B5537689 : Blo 1364501 5537689 := bstep (se 2 (by rfl) ⟨2076633, by rfl⟩ : syracuseStep 5537689 = 4153267) B4153267
theorem B2047931 : Blo 1364501 2047931 := bstep (se 1 (by rfl) ⟨1535948, by rfl⟩ : syracuseStep 2047931 = 3071897) B3071897
theorem B2047991 : Blo 1364501 2047991 := bstep (se 1 (by rfl) ⟨1535993, by rfl⟩ : syracuseStep 2047991 = 3071987) B3071987
theorem B2048009 : Blo 1364501 2048009 := bstep (se 2 (by rfl) ⟨768003, by rfl⟩ : syracuseStep 2048009 = 1536007) B1536007
theorem B2048039 : Blo 1364501 2048039 := bstep (se 1 (by rfl) ⟨1536029, by rfl⟩ : syracuseStep 2048039 = 3072059) B3072059
theorem B6225977 : Blo 1364501 6225977 := bstep (se 2 (by rfl) ⟨2334741, by rfl⟩ : syracuseStep 6225977 = 4669483) B4669483
theorem B2048123 : Blo 1364501 2048123 := bstep (se 1 (by rfl) ⟨1536092, by rfl⟩ : syracuseStep 2048123 = 3072185) B3072185
theorem B34996373 : Blo 1364501 34996373 := bstep (se 6 (by rfl) ⟨820227, by rfl⟩ : syracuseStep 34996373 = 1640455) B1640455
theorem B63971477 : Blo 1364501 63971477 := bstep (se 6 (by rfl) ⟨1499331, by rfl⟩ : syracuseStep 63971477 = 2998663) B2998663
theorem B7880861 : Blo 1364501 7880861 := bstep (se 3 (by rfl) ⟨1477661, by rfl⟩ : syracuseStep 7880861 = 2955323) B2955323
theorem B4923587 : Blo 1364501 4923587 := bstep (se 1 (by rfl) ⟨3692690, by rfl⟩ : syracuseStep 4923587 = 7385381) B7385381
theorem B2048249 : Blo 1364501 2048249 := bstep (se 2 (by rfl) ⟨768093, by rfl⟩ : syracuseStep 2048249 = 1536187) B1536187
theorem B2048351 : Blo 1364501 2048351 := bstep (se 1 (by rfl) ⟨1536263, by rfl⟩ : syracuseStep 2048351 = 3072527) B3072527
theorem B2048363 : Blo 1364501 2048363 := bstep (se 1 (by rfl) ⟨1536272, by rfl⟩ : syracuseStep 2048363 = 3072545) B3072545
theorem B13124105 : Blo 1364501 13124105 := bstep (se 2 (by rfl) ⟨4921539, by rfl⟩ : syracuseStep 13124105 = 9843079) B9843079
theorem B2335289 : Blo 1364501 2335289 := bstep (se 2 (by rfl) ⟨875733, by rfl⟩ : syracuseStep 2335289 = 1751467) B1751467
theorem B2048591 : Blo 1364501 2048591 := bstep (se 1 (by rfl) ⟨1536443, by rfl⟩ : syracuseStep 2048591 = 3072887) B3072887
theorem B3072635 : Blo 1364501 3072635 := bstep (se 1 (by rfl) ⟨2304476, by rfl⟩ : syracuseStep 3072635 = 4608953) B4608953
theorem B2048711 : Blo 1364501 2048711 := bstep (se 1 (by rfl) ⟨1536533, by rfl⟩ : syracuseStep 2048711 = 3073067) B3073067
theorem B3072761 : Blo 1364501 3072761 := bstep (se 2 (by rfl) ⟨1152285, by rfl⟩ : syracuseStep 3072761 = 2304571) B2304571
theorem B22151987 : Blo 1364501 22151987 := bstep (se 1 (by rfl) ⟨16613990, by rfl⟩ : syracuseStep 22151987 = 33227981) B33227981
theorem B2048873 : Blo 1364501 2048873 := bstep (se 2 (by rfl) ⟨768327, by rfl⟩ : syracuseStep 2048873 = 1536655) B1536655
theorem B2188139 : Blo 1364501 2188139 := bstep (se 1 (by rfl) ⟨1641104, by rfl⟩ : syracuseStep 2188139 = 3282209) B3282209
theorem B2048951 : Blo 1364501 2048951 := bstep (se 1 (by rfl) ⟨1536713, by rfl⟩ : syracuseStep 2048951 = 3073427) B3073427
theorem B2048987 : Blo 1364501 2048987 := bstep (se 1 (by rfl) ⟨1536740, by rfl⟩ : syracuseStep 2048987 = 3073481) B3073481
theorem B3073031 : Blo 1364501 3073031 := bstep (se 1 (by rfl) ⟨2304773, by rfl⟩ : syracuseStep 3073031 = 4609547) B4609547
theorem B2302985 : Blo 1364501 2302985 := bstep (se 2 (by rfl) ⟨863619, by rfl⟩ : syracuseStep 2302985 = 1727239) B1727239
theorem B13132867 : Blo 1364501 13132867 := bstep (se 1 (by rfl) ⟨9849650, by rfl⟩ : syracuseStep 13132867 = 19699301) B19699301
theorem B3073103 : Blo 1364501 3073103 := bstep (se 1 (by rfl) ⟨2304827, by rfl⟩ : syracuseStep 3073103 = 4609655) B4609655
theorem B11666551 : Blo 1364501 11666551 := bstep (se 1 (by rfl) ⟨8749913, by rfl⟩ : syracuseStep 11666551 = 17499827) B17499827
theorem B5186713 : Blo 1364501 5186713 := bstep (se 2 (by rfl) ⟨1945017, by rfl⟩ : syracuseStep 5186713 = 3890035) B3890035
theorem B2303147 : Blo 1364501 2303147 := bstep (se 1 (by rfl) ⟨1727360, by rfl⟩ : syracuseStep 2303147 = 3454721) B3454721
theorem B3458447 : Blo 1364501 3458447 := bstep (se 1 (by rfl) ⟨2593835, by rfl⟩ : syracuseStep 3458447 = 5187671) B5187671
theorem B2049455 : Blo 1364501 2049455 := bstep (se 1 (by rfl) ⟨1537091, by rfl⟩ : syracuseStep 2049455 = 3074183) B3074183
theorem B5187017 : Blo 1364501 5187017 := bstep (se 2 (by rfl) ⟨1945131, by rfl⟩ : syracuseStep 5187017 = 3890263) B3890263
theorem B3073499 : Blo 1364501 3073499 := bstep (se 1 (by rfl) ⟨2305124, by rfl⟩ : syracuseStep 3073499 = 4610249) B4610249
theorem B2049545 : Blo 1364501 2049545 := bstep (se 2 (by rfl) ⟨768579, by rfl⟩ : syracuseStep 2049545 = 1537159) B1537159
theorem B89826833 : Blo 1364501 89826833 := bstep (se 2 (by rfl) ⟨33685062, by rfl⟩ : syracuseStep 89826833 = 67370125) B67370125
theorem B1639975 : Blo 1364501 1639975 := bstep (se 1 (by rfl) ⟨1229981, by rfl⟩ : syracuseStep 1639975 = 2459963) B2459963
theorem B2049575 : Blo 1364501 2049575 := bstep (se 1 (by rfl) ⟨1537181, by rfl⟩ : syracuseStep 2049575 = 3074363) B3074363
theorem B2303545 : Blo 1364501 2303545 := bstep (se 2 (by rfl) ⟨863829, by rfl⟩ : syracuseStep 2303545 = 1727659) B1727659
theorem B2049659 : Blo 1364501 2049659 := bstep (se 1 (by rfl) ⟨1537244, by rfl⟩ : syracuseStep 2049659 = 3074489) B3074489
theorem B2303687 : Blo 1364501 2303687 := bstep (se 1 (by rfl) ⟨1727765, by rfl⟩ : syracuseStep 2303687 = 3455531) B3455531
theorem B3458771 : Blo 1364501 3458771 := bstep (se 1 (by rfl) ⟨2594078, by rfl⟩ : syracuseStep 3458771 = 5188157) B5188157
theorem B4376393 : Blo 1364501 4376393 := bstep (se 2 (by rfl) ⟨1641147, by rfl⟩ : syracuseStep 4376393 = 3282295) B3282295
theorem B2303849 : Blo 1364501 2303849 := bstep (se 2 (by rfl) ⟨863943, by rfl⟩ : syracuseStep 2303849 = 1727887) B1727887
theorem B3073967 : Blo 1364501 3073967 := bstep (se 1 (by rfl) ⟨2305475, by rfl⟩ : syracuseStep 3073967 = 4610951) B4610951
theorem B5187503 : Blo 1364501 5187503 := bstep (se 1 (by rfl) ⟨3890627, by rfl⟩ : syracuseStep 5187503 = 7781255) B7781255
theorem B6907841 : Blo 1364501 6907841 := bstep (se 2 (by rfl) ⟨2590440, by rfl⟩ : syracuseStep 6907841 = 5180881) B5180881
theorem B22439873 : Blo 1364501 22439873 := bstep (se 2 (by rfl) ⟨8414952, by rfl⟩ : syracuseStep 22439873 = 16829905) B16829905
theorem B8873921 : Blo 1364501 8873921 := bstep (se 2 (by rfl) ⟨3327720, by rfl⟩ : syracuseStep 8873921 = 6655441) B6655441
theorem B3278855 : Blo 1364501 3278855 := bstep (se 1 (by rfl) ⟨2459141, by rfl⟩ : syracuseStep 3278855 = 4918283) B4918283
theorem B6916103 : Blo 1364501 6916103 := bstep (se 1 (by rfl) ⟨5187077, by rfl⟩ : syracuseStep 6916103 = 10374155) B10374155
theorem B29534341 : Blo 1364501 29534341 := bstep (se 4 (by rfl) ⟨2768844, by rfl⟩ : syracuseStep 29534341 = 5537689) B5537689
theorem B3074219 : Blo 1364501 3074219 := bstep (se 1 (by rfl) ⟨2305664, by rfl⟩ : syracuseStep 3074219 = 4611329) B4611329
theorem B4606199 : Blo 1364501 4606199 := bstep (se 1 (by rfl) ⟨3454649, by rfl⟩ : syracuseStep 4606199 = 6909299) B6909299
theorem B2304247 : Blo 1364501 2304247 := bstep (se 1 (by rfl) ⟨1728185, by rfl⟩ : syracuseStep 2304247 = 3456371) B3456371
theorem B11077975 : Blo 1364501 11077975 := bstep (se 1 (by rfl) ⟨8308481, by rfl⟩ : syracuseStep 11077975 = 16616963) B16616963
theorem B2304443 : Blo 1364501 2304443 := bstep (se 1 (by rfl) ⟨1728332, by rfl⟩ : syracuseStep 2304443 = 3456665) B3456665
theorem B6916589 : Blo 1364501 6916589 := bstep (se 3 (by rfl) ⟨1296860, by rfl⟩ : syracuseStep 6916589 = 2593721) B2593721
theorem B2460179 : Blo 1364501 2460179 := bstep (se 1 (by rfl) ⟨1845134, by rfl⟩ : syracuseStep 2460179 = 3690269) B3690269
theorem B2304551 : Blo 1364501 2304551 := bstep (se 1 (by rfl) ⟨1728413, by rfl⟩ : syracuseStep 2304551 = 3456827) B3456827
theorem B4606523 : Blo 1364501 4606523 := bstep (se 1 (by rfl) ⟨3454892, by rfl⟩ : syracuseStep 4606523 = 6909785) B6909785
theorem B3885707 : Blo 1364501 3885707 := bstep (se 1 (by rfl) ⟨2914280, by rfl⟩ : syracuseStep 3885707 = 5828561) B5828561
theorem B2591443 : Blo 1364501 2591443 := bstep (se 1 (by rfl) ⟨1943582, by rfl⟩ : syracuseStep 2591443 = 3887165) B3887165
theorem B4918009 : Blo 1364501 4918009 := bstep (se 2 (by rfl) ⟨1844253, by rfl⟩ : syracuseStep 4918009 = 3688507) B3688507
theorem B4606793 : Blo 1364501 4606793 := bstep (se 2 (by rfl) ⟨1727547, by rfl⟩ : syracuseStep 4606793 = 3455095) B3455095
theorem B2304841 : Blo 1364501 2304841 := bstep (se 2 (by rfl) ⟨864315, by rfl⟩ : syracuseStep 2304841 = 1728631) B1728631
theorem B17967965 : Blo 1364501 17967965 := bstep (se 3 (by rfl) ⟨3368993, by rfl⟩ : syracuseStep 17967965 = 6737987) B6737987
theorem B2304875 : Blo 1364501 2304875 := bstep (se 1 (by rfl) ⟨1728656, by rfl⟩ : syracuseStep 2304875 = 3457313) B3457313
theorem B2591671 : Blo 1364501 2591671 := bstep (se 1 (by rfl) ⟨1943753, by rfl⟩ : syracuseStep 2591671 = 3887507) B3887507
theorem B9841637 : Blo 1364501 9841637 := bstep (se 4 (by rfl) ⟨922653, by rfl⟩ : syracuseStep 9841637 = 1845307) B1845307
theorem B2460871 : Blo 1364501 2460871 := bstep (se 1 (by rfl) ⟨1845653, by rfl⟩ : syracuseStep 2460871 = 3691307) B3691307
theorem B2305273 : Blo 1364501 2305273 := bstep (se 2 (by rfl) ⟨864477, by rfl⟩ : syracuseStep 2305273 = 1728955) B1728955
theorem B6917399 : Blo 1364501 6917399 := bstep (se 1 (by rfl) ⟨5188049, by rfl⟩ : syracuseStep 6917399 = 10376099) B10376099
theorem B2592263 : Blo 1364501 2592263 := bstep (se 1 (by rfl) ⟨1944197, by rfl⟩ : syracuseStep 2592263 = 3888395) B3888395
theorem B2305543 : Blo 1364501 2305543 := bstep (se 1 (by rfl) ⟨1729157, by rfl⟩ : syracuseStep 2305543 = 3458315) B3458315
theorem B1535611 : Blo 1364501 1535611 := bstep (se 1 (by rfl) ⟨1151708, by rfl⟩ : syracuseStep 1535611 = 2303417) B2303417
theorem B14012027 : Blo 1364501 14012027 := bstep (se 1 (by rfl) ⟨10509020, by rfl⟩ : syracuseStep 14012027 = 21018041) B21018041
theorem B11079301 : Blo 1364501 11079301 := bstep (se 4 (by rfl) ⟨1038684, by rfl⟩ : syracuseStep 11079301 = 2077369) B2077369
theorem B4918973 : Blo 1364501 4918973 := bstep (se 3 (by rfl) ⟨922307, by rfl⟩ : syracuseStep 4918973 = 1844615) B1844615
theorem B21294809 : Blo 1364501 21294809 := bstep (se 2 (by rfl) ⟨7985553, by rfl⟩ : syracuseStep 21294809 = 15971107) B15971107
theorem B5181367 : Blo 1364501 5181367 := bstep (se 1 (by rfl) ⟨3886025, by rfl⟩ : syracuseStep 5181367 = 7772051) B7772051
theorem B4607927 : Blo 1364501 4607927 := bstep (se 1 (by rfl) ⟨3455945, by rfl⟩ : syracuseStep 4607927 = 6911891) B6911891
theorem B6565819 : Blo 1364501 6565819 := bstep (se 1 (by rfl) ⟨4924364, by rfl⟩ : syracuseStep 6565819 = 9848729) B9848729
theorem B1536079 : Blo 1364501 1536079 := bstep (se 1 (by rfl) ⟨1152059, by rfl⟩ : syracuseStep 1536079 = 2304119) B2304119
theorem B6910109 : Blo 1364501 6910109 := bstep (se 3 (by rfl) ⟨1295645, by rfl⟩ : syracuseStep 6910109 = 2591291) B2591291
theorem B2593129 : Blo 1364501 2593129 := bstep (se 2 (by rfl) ⟨972423, by rfl⟩ : syracuseStep 2593129 = 1944847) B1944847
theorem B5181839 : Blo 1364501 5181839 := bstep (se 1 (by rfl) ⟨3886379, by rfl⟩ : syracuseStep 5181839 = 7772759) B7772759
theorem B1536475 : Blo 1364501 1536475 := bstep (se 1 (by rfl) ⟨1152356, by rfl⟩ : syracuseStep 1536475 = 2304713) B2304713
theorem B4608521 : Blo 1364501 4608521 := bstep (se 2 (by rfl) ⟨1728195, by rfl⟩ : syracuseStep 4608521 = 3456391) B3456391
theorem B2593289 : Blo 1364501 2593289 := bstep (se 2 (by rfl) ⟨972483, by rfl⟩ : syracuseStep 2593289 = 1944967) B1944967
theorem B1364519 : Blo 1364501 1364519 := bstep (se 1 (by rfl) ⟨1023389, by rfl⟩ : syracuseStep 1364519 = 2046779) B2046779
theorem B1364559 : Blo 1364501 1364559 := bstep (se 1 (by rfl) ⟨1023419, by rfl⟩ : syracuseStep 1364559 = 2046839) B2046839
theorem B1364575 : Blo 1364501 1364575 := bstep (se 1 (by rfl) ⟨1023431, by rfl⟩ : syracuseStep 1364575 = 2046863) B2046863
theorem B1364603 : Blo 1364501 1364603 := bstep (se 1 (by rfl) ⟨1023452, by rfl⟩ : syracuseStep 1364603 = 2046905) B2046905
theorem B1364655 : Blo 1364501 1364655 := bstep (se 1 (by rfl) ⟨1023491, by rfl⟩ : syracuseStep 1364655 = 2046983) B2046983
theorem B1364679 : Blo 1364501 1364679 := bstep (se 1 (by rfl) ⟨1023509, by rfl⟩ : syracuseStep 1364679 = 2047019) B2047019
theorem B16839377 : Blo 1364501 16839377 := bstep (se 2 (by rfl) ⟨6314766, by rfl⟩ : syracuseStep 16839377 = 12629533) B12629533
theorem B1364699 : Blo 1364501 1364699 := bstep (se 1 (by rfl) ⟨1023524, by rfl⟩ : syracuseStep 1364699 = 2047049) B2047049
theorem B59044625 : Blo 1364501 59044625 := bstep (se 2 (by rfl) ⟨22141734, by rfl⟩ : syracuseStep 59044625 = 44283469) B44283469
theorem B1364775 : Blo 1364501 1364775 := bstep (se 1 (by rfl) ⟨1023581, by rfl⟩ : syracuseStep 1364775 = 2047163) B2047163
theorem B8753993 : Blo 1364501 8753993 := bstep (se 2 (by rfl) ⟨3282747, by rfl⟩ : syracuseStep 8753993 = 6565495) B6565495
theorem B1364815 : Blo 1364501 1364815 := bstep (se 1 (by rfl) ⟨1023611, by rfl⟩ : syracuseStep 1364815 = 2047223) B2047223
theorem B1364831 : Blo 1364501 1364831 := bstep (se 1 (by rfl) ⟨1023623, by rfl⟩ : syracuseStep 1364831 = 2047247) B2047247
theorem B15545195 : Blo 1364501 15545195 := bstep (se 1 (by rfl) ⟨11658896, by rfl⟩ : syracuseStep 15545195 = 23317793) B23317793
theorem B1364859 : Blo 1364501 1364859 := bstep (se 1 (by rfl) ⟨1023644, by rfl⟩ : syracuseStep 1364859 = 2047289) B2047289
theorem B1364911 : Blo 1364501 1364911 := bstep (se 1 (by rfl) ⟨1023683, by rfl⟩ : syracuseStep 1364911 = 2047367) B2047367
theorem B1536943 : Blo 1364501 1536943 := bstep (se 1 (by rfl) ⟨1152707, by rfl⟩ : syracuseStep 1536943 = 2305415) B2305415
theorem B1364935 : Blo 1364501 1364935 := bstep (se 1 (by rfl) ⟨1023701, by rfl⟩ : syracuseStep 1364935 = 2047403) B2047403
theorem B1364955 : Blo 1364501 1364955 := bstep (se 1 (by rfl) ⟨1023716, by rfl⟩ : syracuseStep 1364955 = 2047433) B2047433
theorem B18691073 : Blo 1364501 18691073 := bstep (se 2 (by rfl) ⟨7009152, by rfl⟩ : syracuseStep 18691073 = 14018305) B14018305
theorem B1365031 : Blo 1364501 1365031 := bstep (se 1 (by rfl) ⟨1023773, by rfl⟩ : syracuseStep 1365031 = 2047547) B2047547
theorem B19674161 : Blo 1364501 19674161 := bstep (se 2 (by rfl) ⟨7377810, by rfl⟩ : syracuseStep 19674161 = 14755621) B14755621
theorem B1365071 : Blo 1364501 1365071 := bstep (se 1 (by rfl) ⟨1023803, by rfl⟩ : syracuseStep 1365071 = 2047607) B2047607
theorem B1365087 : Blo 1364501 1365087 := bstep (se 1 (by rfl) ⟨1023815, by rfl⟩ : syracuseStep 1365087 = 2047631) B2047631
theorem B1365115 : Blo 1364501 1365115 := bstep (se 1 (by rfl) ⟨1023836, by rfl⟩ : syracuseStep 1365115 = 2047673) B2047673
theorem B7378073 : Blo 1364501 7378073 := bstep (se 2 (by rfl) ⟨2766777, by rfl⟩ : syracuseStep 7378073 = 5533555) B5533555
theorem B3454123 : Blo 1364501 3454123 := bstep (se 1 (by rfl) ⟨2590592, by rfl⟩ : syracuseStep 3454123 = 5181185) B5181185
theorem B1365167 : Blo 1364501 1365167 := bstep (se 1 (by rfl) ⟨1023875, by rfl⟩ : syracuseStep 1365167 = 2047751) B2047751
theorem B7779523 : Blo 1364501 7779523 := bstep (se 1 (by rfl) ⟨5834642, by rfl⟩ : syracuseStep 7779523 = 11669285) B11669285
theorem B1365191 : Blo 1364501 1365191 := bstep (se 1 (by rfl) ⟨1023893, by rfl⟩ : syracuseStep 1365191 = 2047787) B2047787
theorem B1365211 : Blo 1364501 1365211 := bstep (se 1 (by rfl) ⟨1023908, by rfl⟩ : syracuseStep 1365211 = 2047817) B2047817
theorem B1365287 : Blo 1364501 1365287 := bstep (se 1 (by rfl) ⟨1023965, by rfl⟩ : syracuseStep 1365287 = 2047931) B2047931
theorem B1365327 : Blo 1364501 1365327 := bstep (se 1 (by rfl) ⟨1023995, by rfl⟩ : syracuseStep 1365327 = 2047991) B2047991
theorem B1365343 : Blo 1364501 1365343 := bstep (se 1 (by rfl) ⟨1024007, by rfl⟩ : syracuseStep 1365343 = 2048015) B2048015
theorem B5182825 : Blo 1364501 5182825 := bstep (se 2 (by rfl) ⟨1943559, by rfl⟩ : syracuseStep 5182825 = 3887119) B3887119
theorem B4609385 : Blo 1364501 4609385 := bstep (se 2 (by rfl) ⟨1728519, by rfl⟩ : syracuseStep 4609385 = 3457039) B3457039
theorem B1365371 : Blo 1364501 1365371 := bstep (se 1 (by rfl) ⟨1024028, by rfl⟩ : syracuseStep 1365371 = 2048057) B2048057
theorem B6911405 : Blo 1364501 6911405 := bstep (se 3 (by rfl) ⟨1295888, by rfl⟩ : syracuseStep 6911405 = 2591777) B2591777
theorem B1365423 : Blo 1364501 1365423 := bstep (se 1 (by rfl) ⟨1024067, by rfl⟩ : syracuseStep 1365423 = 2048135) B2048135
theorem B1365447 : Blo 1364501 1365447 := bstep (se 1 (by rfl) ⟨1024085, by rfl⟩ : syracuseStep 1365447 = 2048171) B2048171
theorem B3454427 : Blo 1364501 3454427 := bstep (se 1 (by rfl) ⟨2590820, by rfl⟩ : syracuseStep 3454427 = 5181641) B5181641
theorem B1365467 : Blo 1364501 1365467 := bstep (se 1 (by rfl) ⟨1024100, by rfl⟩ : syracuseStep 1365467 = 2048201) B2048201
theorem B1365543 : Blo 1364501 1365543 := bstep (se 1 (by rfl) ⟨1024157, by rfl⟩ : syracuseStep 1365543 = 2048315) B2048315
theorem B1365583 : Blo 1364501 1365583 := bstep (se 1 (by rfl) ⟨1024187, by rfl⟩ : syracuseStep 1365583 = 2048375) B2048375
theorem B1365599 : Blo 1364501 1365599 := bstep (se 1 (by rfl) ⟨1024199, by rfl⟩ : syracuseStep 1365599 = 2048399) B2048399
theorem B5183099 : Blo 1364501 5183099 := bstep (se 1 (by rfl) ⟨3887324, by rfl⟩ : syracuseStep 5183099 = 7774649) B7774649
theorem B1365627 : Blo 1364501 1365627 := bstep (se 1 (by rfl) ⟨1024220, by rfl⟩ : syracuseStep 1365627 = 2048441) B2048441
theorem B1365679 : Blo 1364501 1365679 := bstep (se 1 (by rfl) ⟨1024259, by rfl⟩ : syracuseStep 1365679 = 2048519) B2048519
theorem B1365703 : Blo 1364501 1365703 := bstep (se 1 (by rfl) ⟨1024277, by rfl⟩ : syracuseStep 1365703 = 2048555) B2048555
theorem B1365723 : Blo 1364501 1365723 := bstep (se 1 (by rfl) ⟨1024292, by rfl⟩ : syracuseStep 1365723 = 2048585) B2048585
theorem B35452673 : Blo 1364501 35452673 := bstep (se 2 (by rfl) ⟨13294752, by rfl⟩ : syracuseStep 35452673 = 26589505) B26589505
theorem B1365799 : Blo 1364501 1365799 := bstep (se 1 (by rfl) ⟨1024349, by rfl⟩ : syracuseStep 1365799 = 2048699) B2048699
theorem B1365839 : Blo 1364501 1365839 := bstep (se 1 (by rfl) ⟨1024379, by rfl⟩ : syracuseStep 1365839 = 2048759) B2048759
theorem B4372319 : Blo 1364501 4372319 := bstep (se 1 (by rfl) ⟨3279239, by rfl⟩ : syracuseStep 4372319 = 6558479) B6558479
theorem B1365855 : Blo 1364501 1365855 := bstep (se 1 (by rfl) ⟨1024391, by rfl⟩ : syracuseStep 1365855 = 2048783) B2048783
theorem B4921195 : Blo 1364501 4921195 := bstep (se 1 (by rfl) ⟨3690896, by rfl⟩ : syracuseStep 4921195 = 7381793) B7381793
theorem B1365883 : Blo 1364501 1365883 := bstep (se 1 (by rfl) ⟨1024412, by rfl⟩ : syracuseStep 1365883 = 2048825) B2048825
theorem B1365935 : Blo 1364501 1365935 := bstep (se 1 (by rfl) ⟨1024451, by rfl⟩ : syracuseStep 1365935 = 2048903) B2048903
theorem B3889079 : Blo 1364501 3889079 := bstep (se 1 (by rfl) ⟨2916809, by rfl⟩ : syracuseStep 3889079 = 5833619) B5833619
theorem B9598907 : Blo 1364501 9598907 := bstep (se 1 (by rfl) ⟨7199180, by rfl⟩ : syracuseStep 9598907 = 14398361) B14398361
theorem B4609979 : Blo 1364501 4609979 := bstep (se 1 (by rfl) ⟨3457484, by rfl⟩ : syracuseStep 4609979 = 6914969) B6914969
theorem B1365959 : Blo 1364501 1365959 := bstep (se 1 (by rfl) ⟨1024469, by rfl⟩ : syracuseStep 1365959 = 2048939) B2048939
theorem B14768081 : Blo 1364501 14768081 := bstep (se 2 (by rfl) ⟨5538030, by rfl⟩ : syracuseStep 14768081 = 11076061) B11076061
theorem B1365979 : Blo 1364501 1365979 := bstep (se 1 (by rfl) ⟨1024484, by rfl⟩ : syracuseStep 1365979 = 2048969) B2048969
theorem B5830663 : Blo 1364501 5830663 := bstep (se 1 (by rfl) ⟨4372997, by rfl⟩ : syracuseStep 5830663 = 8745995) B8745995
theorem B1366055 : Blo 1364501 1366055 := bstep (se 1 (by rfl) ⟨1024541, by rfl⟩ : syracuseStep 1366055 = 2049083) B2049083
theorem B1366095 : Blo 1364501 1366095 := bstep (se 1 (by rfl) ⟨1024571, by rfl⟩ : syracuseStep 1366095 = 2049143) B2049143
theorem B1366111 : Blo 1364501 1366111 := bstep (se 1 (by rfl) ⟨1024583, by rfl⟩ : syracuseStep 1366111 = 2049167) B2049167
theorem B2766971 : Blo 1364501 2766971 := bstep (se 1 (by rfl) ⟨2075228, by rfl⟩ : syracuseStep 2766971 = 4150457) B4150457
theorem B1366139 : Blo 1364501 1366139 := bstep (se 1 (by rfl) ⟨1024604, by rfl⟩ : syracuseStep 1366139 = 2049209) B2049209
theorem B1366191 : Blo 1364501 1366191 := bstep (se 1 (by rfl) ⟨1024643, by rfl⟩ : syracuseStep 1366191 = 2049287) B2049287
theorem B1366215 : Blo 1364501 1366215 := bstep (se 1 (by rfl) ⟨1024661, by rfl⟩ : syracuseStep 1366215 = 2049323) B2049323
theorem B1366235 : Blo 1364501 1366235 := bstep (se 1 (by rfl) ⟨1024676, by rfl⟩ : syracuseStep 1366235 = 2049353) B2049353
theorem B1366311 : Blo 1364501 1366311 := bstep (se 1 (by rfl) ⟨1024733, by rfl⟩ : syracuseStep 1366311 = 2049467) B2049467
theorem B1366351 : Blo 1364501 1366351 := bstep (se 1 (by rfl) ⟨1024763, by rfl⟩ : syracuseStep 1366351 = 2049527) B2049527
theorem B42637661 : Blo 1364501 42637661 := bstep (se 3 (by rfl) ⟨7994561, by rfl⟩ : syracuseStep 42637661 = 15989123) B15989123
theorem B1366367 : Blo 1364501 1366367 := bstep (se 1 (by rfl) ⟨1024775, by rfl⟩ : syracuseStep 1366367 = 2049551) B2049551
theorem B3070313 : Blo 1364501 3070313 := bstep (se 2 (by rfl) ⟨1151367, by rfl⟩ : syracuseStep 3070313 = 2302735) B2302735
theorem B1366395 : Blo 1364501 1366395 := bstep (se 1 (by rfl) ⟨1024796, by rfl⟩ : syracuseStep 1366395 = 2049593) B2049593
theorem B6560129 : Blo 1364501 6560129 := bstep (se 2 (by rfl) ⟨2460048, by rfl⟩ : syracuseStep 6560129 = 4920097) B4920097
theorem B45504899 : Blo 1364501 45504899 := bstep (se 1 (by rfl) ⟨34128674, by rfl⟩ : syracuseStep 45504899 = 68257349) B68257349
theorem B2628001 : Blo 1364501 2628001 := bstep (se 2 (by rfl) ⟨985500, by rfl⟩ : syracuseStep 2628001 = 1971001) B1971001
theorem B1366447 : Blo 1364501 1366447 := bstep (se 1 (by rfl) ⟨1024835, by rfl⟩ : syracuseStep 1366447 = 2049671) B2049671
theorem B1366471 : Blo 1364501 1366471 := bstep (se 1 (by rfl) ⟨1024853, by rfl⟩ : syracuseStep 1366471 = 2049707) B2049707
theorem B1366491 : Blo 1364501 1366491 := bstep (se 1 (by rfl) ⟨1024868, by rfl⟩ : syracuseStep 1366491 = 2049737) B2049737
theorem B6232585 : Blo 1364501 6232585 := bstep (se 2 (by rfl) ⟨2337219, by rfl⟩ : syracuseStep 6232585 = 4674439) B4674439
theorem B3889853 : Blo 1364501 3889853 := bstep (se 3 (by rfl) ⟨729347, by rfl⟩ : syracuseStep 3889853 = 1458695) B1458695
theorem B4373203 : Blo 1364501 4373203 := bstep (se 1 (by rfl) ⟨3279902, by rfl⟩ : syracuseStep 4373203 = 6559805) B6559805
theorem B2046815 : Blo 1364501 2046815 := bstep (se 1 (by rfl) ⟨1535111, by rfl⟩ : syracuseStep 2046815 = 3070223) B3070223
theorem B2046827 : Blo 1364501 2046827 := bstep (se 1 (by rfl) ⟨1535120, by rfl⟩ : syracuseStep 2046827 = 3070241) B3070241
theorem B3455905 : Blo 1364501 3455905 := bstep (se 2 (by rfl) ⟨1295964, by rfl⟩ : syracuseStep 3455905 = 2591929) B2591929
theorem B3890081 : Blo 1364501 3890081 := bstep (se 2 (by rfl) ⟨1458780, by rfl⟩ : syracuseStep 3890081 = 2917561) B2917561
theorem B3070907 : Blo 1364501 3070907 := bstep (se 1 (by rfl) ⟨2303180, by rfl⟩ : syracuseStep 3070907 = 4606361) B4606361
theorem B6913025 : Blo 1364501 6913025 := bstep (se 2 (by rfl) ⟨2592384, by rfl⟩ : syracuseStep 6913025 = 5184769) B5184769
theorem B3071033 : Blo 1364501 3071033 := bstep (se 2 (by rfl) ⟨1151637, by rfl⟩ : syracuseStep 3071033 = 2303275) B2303275
theorem B2047055 : Blo 1364501 2047055 := bstep (se 1 (by rfl) ⟨1535291, by rfl⟩ : syracuseStep 2047055 = 3070583) B3070583
theorem B6560939 : Blo 1364501 6560939 := bstep (se 1 (by rfl) ⟨4920704, by rfl⟩ : syracuseStep 6560939 = 9841409) B9841409
theorem B4152491 : Blo 1364501 4152491 := bstep (se 1 (by rfl) ⟨3114368, by rfl⟩ : syracuseStep 4152491 = 6228737) B6228737
theorem B2047175 : Blo 1364501 2047175 := bstep (se 1 (by rfl) ⟨1535381, by rfl⟩ : syracuseStep 2047175 = 3070763) B3070763
theorem B3890423 : Blo 1364501 3890423 := bstep (se 1 (by rfl) ⟨2917817, by rfl⟩ : syracuseStep 3890423 = 5835635) B5835635
theorem B17497367 : Blo 1364501 17497367 := bstep (se 1 (by rfl) ⟨13123025, by rfl⟩ : syracuseStep 17497367 = 26246051) B26246051
theorem B2334025 : Blo 1364501 2334025 := bstep (se 2 (by rfl) ⟨875259, by rfl⟩ : syracuseStep 2334025 = 1750519) B1750519
theorem B2047337 : Blo 1364501 2047337 := bstep (se 2 (by rfl) ⟨767751, by rfl⟩ : syracuseStep 2047337 = 1535503) B1535503
theorem B3890537 : Blo 1364501 3890537 := bstep (se 2 (by rfl) ⟨1458951, by rfl⟩ : syracuseStep 3890537 = 2917903) B2917903
theorem B3071375 : Blo 1364501 3071375 := bstep (se 1 (by rfl) ⟨2303531, by rfl⟩ : syracuseStep 3071375 = 4607063) B4607063
theorem B2047415 : Blo 1364501 2047415 := bstep (se 1 (by rfl) ⟨1535561, by rfl⟩ : syracuseStep 2047415 = 3071123) B3071123
theorem B2047451 : Blo 1364501 2047451 := bstep (se 1 (by rfl) ⟨1535588, by rfl⟩ : syracuseStep 2047451 = 3071177) B3071177
theorem B2186761 : Blo 1364501 2186761 := bstep (se 2 (by rfl) ⟨820035, by rfl⟩ : syracuseStep 2186761 = 1640071) B1640071
theorem B10362491 : Blo 1364501 10362491 := bstep (se 1 (by rfl) ⟨7771868, by rfl⟩ : syracuseStep 10362491 = 15543737) B15543737
theorem B4611707 : Blo 1364501 4611707 := bstep (se 1 (by rfl) ⟨3458780, by rfl⟩ : syracuseStep 4611707 = 6917561) B6917561
theorem B5537479 : Blo 1364501 5537479 := bstep (se 1 (by rfl) ⟨4153109, by rfl⟩ : syracuseStep 5537479 = 8306219) B8306219
theorem B3071699 : Blo 1364501 3071699 := bstep (se 1 (by rfl) ⟨2303774, by rfl⟩ : syracuseStep 3071699 = 4607549) B4607549
theorem B4611869 : Blo 1364501 4611869 := bstep (se 3 (by rfl) ⟨864725, by rfl⟩ : syracuseStep 4611869 = 1729451) B1729451
theorem B6913835 : Blo 1364501 6913835 := bstep (se 1 (by rfl) ⟨5185376, by rfl⟩ : syracuseStep 6913835 = 10370753) B10370753
theorem B2047919 : Blo 1364501 2047919 := bstep (se 1 (by rfl) ⟨1535939, by rfl⟩ : syracuseStep 2047919 = 3071879) B3071879
theorem B7774217 : Blo 1364501 7774217 := bstep (se 2 (by rfl) ⟨2915331, by rfl⟩ : syracuseStep 7774217 = 5830663) B5830663
theorem B23330915 : Blo 1364501 23330915 := bstep (se 1 (by rfl) ⟨17498186, by rfl⟩ : syracuseStep 23330915 = 34996373) B34996373
theorem B42647651 : Blo 1364501 42647651 := bstep (se 1 (by rfl) ⟨31985738, by rfl⟩ : syracuseStep 42647651 = 63971477) B63971477
theorem B2048105 : Blo 1364501 2048105 := bstep (se 2 (by rfl) ⟨768039, by rfl⟩ : syracuseStep 2048105 = 1536079) B1536079
theorem B39379121 : Blo 1364501 39379121 := bstep (se 2 (by rfl) ⟨14767170, by rfl⟩ : syracuseStep 39379121 = 29534341) B29534341
theorem B3072329 : Blo 1364501 3072329 := bstep (se 2 (by rfl) ⟨1152123, by rfl⟩ : syracuseStep 3072329 = 2304247) B2304247
theorem B3072347 : Blo 1364501 3072347 := bstep (se 1 (by rfl) ⟨2304260, by rfl⟩ : syracuseStep 3072347 = 4608521) B4608521
theorem B8749403 : Blo 1364501 8749403 := bstep (se 1 (by rfl) ⟨6562052, by rfl⟩ : syracuseStep 8749403 = 13124105) B13124105
theorem B1728859 : Blo 1364501 1728859 := bstep (se 1 (by rfl) ⟨1296644, by rfl⟩ : syracuseStep 1728859 = 2593289) B2593289
theorem B2048423 : Blo 1364501 2048423 := bstep (se 1 (by rfl) ⟨1536317, by rfl⟩ : syracuseStep 2048423 = 3072635) B3072635
theorem B14770633 : Blo 1364501 14770633 := bstep (se 2 (by rfl) ⟨5538987, by rfl⟩ : syracuseStep 14770633 = 11077975) B11077975
theorem B3457505 : Blo 1364501 3457505 := bstep (se 2 (by rfl) ⟨1296564, by rfl⟩ : syracuseStep 3457505 = 2593129) B2593129
theorem B2048507 : Blo 1364501 2048507 := bstep (se 1 (by rfl) ⟨1536380, by rfl⟩ : syracuseStep 2048507 = 3072761) B3072761
theorem B39363083 : Blo 1364501 39363083 := bstep (se 1 (by rfl) ⟨29522312, by rfl⟩ : syracuseStep 39363083 = 59044625) B59044625
theorem B10363463 : Blo 1364501 10363463 := bstep (se 1 (by rfl) ⟨7772597, by rfl⟩ : syracuseStep 10363463 = 15545195) B15545195
theorem B2048633 : Blo 1364501 2048633 := bstep (se 2 (by rfl) ⟨768237, by rfl⟩ : syracuseStep 2048633 = 1536475) B1536475
theorem B12460715 : Blo 1364501 12460715 := bstep (se 1 (by rfl) ⟨9345536, by rfl⟩ : syracuseStep 12460715 = 18691073) B18691073
theorem B2048687 : Blo 1364501 2048687 := bstep (se 1 (by rfl) ⟨1536515, by rfl⟩ : syracuseStep 2048687 = 3073031) B3073031
theorem B13116107 : Blo 1364501 13116107 := bstep (se 1 (by rfl) ⟨9837080, by rfl⟩ : syracuseStep 13116107 = 19674161) B19674161
theorem B2048735 : Blo 1364501 2048735 := bstep (se 1 (by rfl) ⟨1536551, by rfl⟩ : syracuseStep 2048735 = 3073103) B3073103
theorem B3072923 : Blo 1364501 3072923 := bstep (se 1 (by rfl) ⟨2304692, by rfl⟩ : syracuseStep 3072923 = 4609385) B4609385
theorem B3458011 : Blo 1364501 3458011 := bstep (se 1 (by rfl) ⟨2593508, by rfl⟩ : syracuseStep 3458011 = 5187017) B5187017
theorem B2302951 : Blo 1364501 2302951 := bstep (se 1 (by rfl) ⟨1727213, by rfl⟩ : syracuseStep 2302951 = 3454427) B3454427
theorem B2048999 : Blo 1364501 2048999 := bstep (se 1 (by rfl) ⟨1536749, by rfl⟩ : syracuseStep 2048999 = 3073499) B3073499
theorem B59884555 : Blo 1364501 59884555 := bstep (se 1 (by rfl) ⟨44913416, by rfl⟩ : syracuseStep 59884555 = 89826833) B89826833
theorem B3073121 : Blo 1364501 3073121 := bstep (se 2 (by rfl) ⟨1152420, by rfl⟩ : syracuseStep 3073121 = 2304841) B2304841
theorem B23635115 : Blo 1364501 23635115 := bstep (se 1 (by rfl) ⟨17726336, by rfl⟩ : syracuseStep 23635115 = 35452673) B35452673
theorem B2917595 : Blo 1364501 2917595 := bstep (se 1 (by rfl) ⟨2188196, by rfl⟩ : syracuseStep 2917595 = 4376393) B4376393
theorem B2049257 : Blo 1364501 2049257 := bstep (se 2 (by rfl) ⟨768471, by rfl⟩ : syracuseStep 2049257 = 1536943) B1536943
theorem B2049311 : Blo 1364501 2049311 := bstep (se 1 (by rfl) ⟨1536983, by rfl⟩ : syracuseStep 2049311 = 3073967) B3073967
theorem B3458335 : Blo 1364501 3458335 := bstep (se 1 (by rfl) ⟨2593751, by rfl⟩ : syracuseStep 3458335 = 5187503) B5187503
theorem B6399271 : Blo 1364501 6399271 := bstep (se 1 (by rfl) ⟨4799453, by rfl⟩ : syracuseStep 6399271 = 9598907) B9598907
theorem B3073319 : Blo 1364501 3073319 := bstep (se 1 (by rfl) ⟨2304989, by rfl⟩ : syracuseStep 3073319 = 4609979) B4609979
theorem B4605227 : Blo 1364501 4605227 := bstep (se 1 (by rfl) ⟨3453920, by rfl⟩ : syracuseStep 4605227 = 6907841) B6907841
theorem B2049479 : Blo 1364501 2049479 := bstep (se 1 (by rfl) ⟨1537109, by rfl⟩ : syracuseStep 2049479 = 3074219) B3074219
theorem B6227437 : Blo 1364501 6227437 := bstep (se 3 (by rfl) ⟨1167644, by rfl⟩ : syracuseStep 6227437 = 2335289) B2335289
theorem B6915617 : Blo 1364501 6915617 := bstep (se 2 (by rfl) ⟨2593356, by rfl⟩ : syracuseStep 6915617 = 5186713) B5186713
theorem B4605497 : Blo 1364501 4605497 := bstep (se 2 (by rfl) ⟨1727061, by rfl⟩ : syracuseStep 4605497 = 3454123) B3454123
theorem B30336599 : Blo 1364501 30336599 := bstep (se 1 (by rfl) ⟨22752449, by rfl⟩ : syracuseStep 30336599 = 45504899) B45504899
theorem B10372697 : Blo 1364501 10372697 := bstep (se 2 (by rfl) ⟨3889761, by rfl⟩ : syracuseStep 10372697 = 7779523) B7779523
theorem B3073697 : Blo 1364501 3073697 := bstep (se 2 (by rfl) ⟨1152636, by rfl⟩ : syracuseStep 3073697 = 2305273) B2305273
theorem B2590471 : Blo 1364501 2590471 := bstep (se 1 (by rfl) ⟨1942853, by rfl⟩ : syracuseStep 2590471 = 3885707) B3885707
theorem B13117261 : Blo 1364501 13117261 := bstep (se 3 (by rfl) ⟨2459486, by rfl⟩ : syracuseStep 13117261 = 4918973) B4918973
theorem B3074057 : Blo 1364501 3074057 := bstep (se 2 (by rfl) ⟨1152771, by rfl⟩ : syracuseStep 3074057 = 2305543) B2305543
theorem B14772401 : Blo 1364501 14772401 := bstep (se 2 (by rfl) ⟨5539650, by rfl⟩ : syracuseStep 14772401 = 11079301) B11079301
theorem B7383305 : Blo 1364501 7383305 := bstep (se 2 (by rfl) ⟨2768739, by rfl⟩ : syracuseStep 7383305 = 5537479) B5537479
theorem B5835037 : Blo 1364501 5835037 := bstep (se 3 (by rfl) ⟨1094069, by rfl⟩ : syracuseStep 5835037 = 2188139) B2188139
theorem B6908327 : Blo 1364501 6908327 := bstep (se 1 (by rfl) ⟨5181245, by rfl⟩ : syracuseStep 6908327 = 10362491) B10362491
theorem B9341351 : Blo 1364501 9341351 := bstep (se 1 (by rfl) ⟨7006013, by rfl⟩ : syracuseStep 9341351 = 14012027) B14012027
theorem B3074471 : Blo 1364501 3074471 := bstep (se 1 (by rfl) ⟨2305853, by rfl⟩ : syracuseStep 3074471 = 4611707) B4611707
theorem B3074579 : Blo 1364501 3074579 := bstep (se 1 (by rfl) ⟨2305934, by rfl⟩ : syracuseStep 3074579 = 4611869) B4611869
theorem B6908489 : Blo 1364501 6908489 := bstep (se 2 (by rfl) ⟨2590683, by rfl⟩ : syracuseStep 6908489 = 5181367) B5181367
theorem B4606739 : Blo 1364501 4606739 := bstep (se 1 (by rfl) ⟨3455054, by rfl⟩ : syracuseStep 4606739 = 6910109) B6910109
theorem B5253907 : Blo 1364501 5253907 := bstep (se 1 (by rfl) ⟨3940430, by rfl⟩ : syracuseStep 5253907 = 7880861) B7880861
theorem B11226251 : Blo 1364501 11226251 := bstep (se 1 (by rfl) ⟨8419688, by rfl⟩ : syracuseStep 11226251 = 16839377) B16839377
theorem B5835995 : Blo 1364501 5835995 := bstep (se 1 (by rfl) ⟨4376996, by rfl⟩ : syracuseStep 5835995 = 8753993) B8753993
theorem B1535323 : Blo 1364501 1535323 := bstep (se 1 (by rfl) ⟨1151492, by rfl⟩ : syracuseStep 1535323 = 2302985) B2302985
theorem B8310113 : Blo 1364501 8310113 := bstep (se 2 (by rfl) ⟨3116292, by rfl⟩ : syracuseStep 8310113 = 6232585) B6232585
theorem B4918715 : Blo 1364501 4918715 := bstep (se 1 (by rfl) ⟨3689036, by rfl⟩ : syracuseStep 4918715 = 7378073) B7378073
theorem B1535431 : Blo 1364501 1535431 := bstep (se 1 (by rfl) ⟨1151573, by rfl⟩ : syracuseStep 1535431 = 2303147) B2303147
theorem B2305631 : Blo 1364501 2305631 := bstep (se 1 (by rfl) ⟨1729223, by rfl⟩ : syracuseStep 2305631 = 3458447) B3458447
theorem B4607603 : Blo 1364501 4607603 := bstep (se 1 (by rfl) ⟨3455702, by rfl⟩ : syracuseStep 4607603 = 6911405) B6911405
theorem B6557345 : Blo 1364501 6557345 := bstep (se 2 (by rfl) ⟨2459004, by rfl⟩ : syracuseStep 6557345 = 4918009) B4918009
theorem B17493677 : Blo 1364501 17493677 := bstep (se 3 (by rfl) ⟨3280064, by rfl⟩ : syracuseStep 17493677 = 6560129) B6560129
theorem B1535791 : Blo 1364501 1535791 := bstep (se 1 (by rfl) ⟨1151843, by rfl⟩ : syracuseStep 1535791 = 2303687) B2303687
theorem B2305847 : Blo 1364501 2305847 := bstep (se 1 (by rfl) ⟨1729385, by rfl⟩ : syracuseStep 2305847 = 3458771) B3458771
theorem B4607873 : Blo 1364501 4607873 := bstep (se 2 (by rfl) ⟨1727952, by rfl⟩ : syracuseStep 4607873 = 3455905) B3455905
theorem B1535899 : Blo 1364501 1535899 := bstep (se 1 (by rfl) ⟨1151924, by rfl⟩ : syracuseStep 1535899 = 2303849) B2303849
theorem B2592719 : Blo 1364501 2592719 := bstep (se 1 (by rfl) ⟨1944539, by rfl⟩ : syracuseStep 2592719 = 3889079) B3889079
theorem B17510489 : Blo 1364501 17510489 := bstep (se 2 (by rfl) ⟨6566433, by rfl⟩ : syracuseStep 17510489 = 13132867) B13132867
theorem B3281161 : Blo 1364501 3281161 := bstep (se 2 (by rfl) ⟨1230435, by rfl⟩ : syracuseStep 3281161 = 2460871) B2460871
theorem B1536295 : Blo 1364501 1536295 := bstep (se 1 (by rfl) ⟨1152221, by rfl⟩ : syracuseStep 1536295 = 2304443) B2304443
theorem B1536367 : Blo 1364501 1536367 := bstep (se 1 (by rfl) ⟨1152275, by rfl⟩ : syracuseStep 1536367 = 2304551) B2304551
theorem B2593235 : Blo 1364501 2593235 := bstep (se 1 (by rfl) ⟨1944926, by rfl⟩ : syracuseStep 2593235 = 3889853) B3889853
theorem B6910433 : Blo 1364501 6910433 := bstep (se 2 (by rfl) ⟨2591412, by rfl⟩ : syracuseStep 6910433 = 5182825) B5182825
theorem B1364543 : Blo 1364501 1364543 := bstep (se 1 (by rfl) ⟨1023407, by rfl⟩ : syracuseStep 1364543 = 2046815) B2046815
theorem B1364551 : Blo 1364501 1364551 := bstep (se 1 (by rfl) ⟨1023413, by rfl⟩ : syracuseStep 1364551 = 2046827) B2046827
theorem B1536583 : Blo 1364501 1536583 := bstep (se 1 (by rfl) ⟨1152437, by rfl⟩ : syracuseStep 1536583 = 2304875) B2304875
theorem B2593387 : Blo 1364501 2593387 := bstep (se 1 (by rfl) ⟨1945040, by rfl⟩ : syracuseStep 2593387 = 3890081) B3890081
theorem B4608683 : Blo 1364501 4608683 := bstep (se 1 (by rfl) ⟨3456512, by rfl⟩ : syracuseStep 4608683 = 6913025) B6913025
theorem B1364703 : Blo 1364501 1364703 := bstep (se 1 (by rfl) ⟨1023527, by rfl⟩ : syracuseStep 1364703 = 2047055) B2047055
theorem B1364783 : Blo 1364501 1364783 := bstep (se 1 (by rfl) ⟨1023587, by rfl⟩ : syracuseStep 1364783 = 2047175) B2047175
theorem B2593615 : Blo 1364501 2593615 := bstep (se 1 (by rfl) ⟨1945211, by rfl⟩ : syracuseStep 2593615 = 3890423) B3890423
theorem B1364891 : Blo 1364501 1364891 := bstep (se 1 (by rfl) ⟨1023668, by rfl⟩ : syracuseStep 1364891 = 2047337) B2047337
theorem B2593691 : Blo 1364501 2593691 := bstep (se 1 (by rfl) ⟨1945268, by rfl⟩ : syracuseStep 2593691 = 3890537) B3890537
theorem B1364943 : Blo 1364501 1364943 := bstep (se 1 (by rfl) ⟨1023707, by rfl⟩ : syracuseStep 1364943 = 2047415) B2047415
theorem B1364967 : Blo 1364501 1364967 := bstep (se 1 (by rfl) ⟨1023725, by rfl⟩ : syracuseStep 1364967 = 2047451) B2047451
theorem B59839661 : Blo 1364501 59839661 := bstep (se 3 (by rfl) ⟨11219936, by rfl⟩ : syracuseStep 59839661 = 22439873) B22439873
theorem B23663789 : Blo 1364501 23663789 := bstep (se 3 (by rfl) ⟨4436960, by rfl⟩ : syracuseStep 23663789 = 8873921) B8873921
theorem B4609223 : Blo 1364501 4609223 := bstep (se 1 (by rfl) ⟨3456917, by rfl⟩ : syracuseStep 4609223 = 6913835) B6913835
theorem B8754425 : Blo 1364501 8754425 := bstep (se 2 (by rfl) ⟨3282909, by rfl⟩ : syracuseStep 8754425 = 6565819) B6565819
theorem B1365279 : Blo 1364501 1365279 := bstep (se 1 (by rfl) ⟨1023959, by rfl⟩ : syracuseStep 1365279 = 2047919) B2047919
theorem B1365339 : Blo 1364501 1365339 := bstep (se 1 (by rfl) ⟨1024004, by rfl⟩ : syracuseStep 1365339 = 2048009) B2048009
theorem B1365359 : Blo 1364501 1365359 := bstep (se 1 (by rfl) ⟨1024019, by rfl⟩ : syracuseStep 1365359 = 2048039) B2048039
theorem B4150651 : Blo 1364501 4150651 := bstep (se 1 (by rfl) ⟨3112988, by rfl⟩ : syracuseStep 4150651 = 6225977) B6225977
theorem B1365415 : Blo 1364501 1365415 := bstep (se 1 (by rfl) ⟨1024061, by rfl⟩ : syracuseStep 1365415 = 2048123) B2048123
theorem B3282391 : Blo 1364501 3282391 := bstep (se 1 (by rfl) ⟨2461793, by rfl⟩ : syracuseStep 3282391 = 4923587) B4923587
theorem B1365499 : Blo 1364501 1365499 := bstep (se 1 (by rfl) ⟨1024124, by rfl⟩ : syracuseStep 1365499 = 2048249) B2048249
theorem B1365567 : Blo 1364501 1365567 := bstep (se 1 (by rfl) ⟨1024175, by rfl⟩ : syracuseStep 1365567 = 2048351) B2048351
theorem B1365575 : Blo 1364501 1365575 := bstep (se 1 (by rfl) ⟨1024181, by rfl⟩ : syracuseStep 1365575 = 2048363) B2048363
theorem B3454559 : Blo 1364501 3454559 := bstep (se 1 (by rfl) ⟨2590919, by rfl⟩ : syracuseStep 3454559 = 5181839) B5181839
theorem B7378589 : Blo 1364501 7378589 := bstep (se 3 (by rfl) ⟨1383485, by rfl⟩ : syracuseStep 7378589 = 2766971) B2766971
theorem B1365727 : Blo 1364501 1365727 := bstep (se 1 (by rfl) ⟨1024295, by rfl⟩ : syracuseStep 1365727 = 2048591) B2048591
theorem B1365807 : Blo 1364501 1365807 := bstep (se 1 (by rfl) ⟨1024355, by rfl⟩ : syracuseStep 1365807 = 2048711) B2048711
theorem B14767991 : Blo 1364501 14767991 := bstep (se 1 (by rfl) ⟨11075993, by rfl⟩ : syracuseStep 14767991 = 22151987) B22151987
theorem B3504001 : Blo 1364501 3504001 := bstep (se 2 (by rfl) ⟨1314000, by rfl⟩ : syracuseStep 3504001 = 2628001) B2628001
theorem B1365915 : Blo 1364501 1365915 := bstep (se 1 (by rfl) ⟨1024436, by rfl⟩ : syracuseStep 1365915 = 2048873) B2048873
theorem B1365967 : Blo 1364501 1365967 := bstep (se 1 (by rfl) ⟨1024475, by rfl⟩ : syracuseStep 1365967 = 2048951) B2048951
theorem B1365991 : Blo 1364501 1365991 := bstep (se 1 (by rfl) ⟨1024493, by rfl⟩ : syracuseStep 1365991 = 2048987) B2048987
theorem B3455257 : Blo 1364501 3455257 := bstep (se 2 (by rfl) ⟨1295721, by rfl⟩ : syracuseStep 3455257 = 2591443) B2591443
theorem B5830937 : Blo 1364501 5830937 := bstep (se 2 (by rfl) ⟨2186601, by rfl⟩ : syracuseStep 5830937 = 4373203) B4373203
theorem B1366303 : Blo 1364501 1366303 := bstep (se 1 (by rfl) ⟨1024727, by rfl⟩ : syracuseStep 1366303 = 2049455) B2049455
theorem B1366363 : Blo 1364501 1366363 := bstep (se 1 (by rfl) ⟨1024772, by rfl⟩ : syracuseStep 1366363 = 2049545) B2049545
theorem B1366383 : Blo 1364501 1366383 := bstep (se 1 (by rfl) ⟨1024787, by rfl⟩ : syracuseStep 1366383 = 2049575) B2049575
theorem B3455399 : Blo 1364501 3455399 := bstep (se 1 (by rfl) ⟨2591549, by rfl⟩ : syracuseStep 3455399 = 5183099) B5183099
theorem B1366439 : Blo 1364501 1366439 := bstep (se 1 (by rfl) ⟨1024829, by rfl⟩ : syracuseStep 1366439 = 2049659) B2049659
theorem B2914879 : Blo 1364501 2914879 := bstep (se 1 (by rfl) ⟨2186159, by rfl⟩ : syracuseStep 2914879 = 4372319) B4372319
theorem B3455561 : Blo 1364501 3455561 := bstep (se 2 (by rfl) ⟨1295835, by rfl⟩ : syracuseStep 3455561 = 2591671) B2591671
theorem B9845387 : Blo 1364501 9845387 := bstep (se 1 (by rfl) ⟨7384040, by rfl⟩ : syracuseStep 9845387 = 14768081) B14768081
theorem B2185903 : Blo 1364501 2185903 := bstep (se 1 (by rfl) ⟨1639427, by rfl⟩ : syracuseStep 2185903 = 3278855) B3278855
theorem B4610735 : Blo 1364501 4610735 := bstep (se 1 (by rfl) ⟨3458051, by rfl⟩ : syracuseStep 4610735 = 6916103) B6916103
theorem B6912701 : Blo 1364501 6912701 := bstep (se 3 (by rfl) ⟨1296131, by rfl⟩ : syracuseStep 6912701 = 2592263) B2592263
theorem B6560477 : Blo 1364501 6560477 := bstep (se 3 (by rfl) ⟨1230089, by rfl⟩ : syracuseStep 6560477 = 2460179) B2460179
theorem B15555401 : Blo 1364501 15555401 := bstep (se 2 (by rfl) ⟨5833275, by rfl⟩ : syracuseStep 15555401 = 11666551) B11666551
theorem B3070799 : Blo 1364501 3070799 := bstep (se 1 (by rfl) ⟨2303099, by rfl⟩ : syracuseStep 3070799 = 4606199) B4606199
theorem B28425107 : Blo 1364501 28425107 := bstep (se 1 (by rfl) ⟨21318830, by rfl⟩ : syracuseStep 28425107 = 42637661) B42637661
theorem B2046875 : Blo 1364501 2046875 := bstep (se 1 (by rfl) ⟨1535156, by rfl⟩ : syracuseStep 2046875 = 3070313) B3070313
theorem B4611059 : Blo 1364501 4611059 := bstep (se 1 (by rfl) ⟨3458294, by rfl⟩ : syracuseStep 4611059 = 6916589) B6916589
theorem B3071015 : Blo 1364501 3071015 := bstep (se 1 (by rfl) ⟨2303261, by rfl⟩ : syracuseStep 3071015 = 4606523) B4606523
theorem B3112033 : Blo 1364501 3112033 := bstep (se 2 (by rfl) ⟨1167012, by rfl⟩ : syracuseStep 3112033 = 2334025) B2334025
theorem B3071195 : Blo 1364501 3071195 := bstep (se 1 (by rfl) ⟨2303396, by rfl⟩ : syracuseStep 3071195 = 4606793) B4606793
theorem B2047271 : Blo 1364501 2047271 := bstep (se 1 (by rfl) ⟨1535453, by rfl⟩ : syracuseStep 2047271 = 3070907) B3070907
theorem B6561091 : Blo 1364501 6561091 := bstep (se 1 (by rfl) ⟨4920818, by rfl⟩ : syracuseStep 6561091 = 9841637) B9841637
theorem B2915681 : Blo 1364501 2915681 := bstep (se 2 (by rfl) ⟨1093380, by rfl⟩ : syracuseStep 2915681 = 2186761) B2186761
theorem B2047355 : Blo 1364501 2047355 := bstep (se 1 (by rfl) ⟨1535516, by rfl⟩ : syracuseStep 2047355 = 3071033) B3071033
theorem B2186633 : Blo 1364501 2186633 := bstep (se 2 (by rfl) ⟨819987, by rfl⟩ : syracuseStep 2186633 = 1639975) B1639975
theorem B3071393 : Blo 1364501 3071393 := bstep (se 2 (by rfl) ⟨1151772, by rfl⟩ : syracuseStep 3071393 = 2303545) B2303545
theorem B4373959 : Blo 1364501 4373959 := bstep (se 1 (by rfl) ⟨3280469, by rfl⟩ : syracuseStep 4373959 = 6560939) B6560939
theorem B2768327 : Blo 1364501 2768327 := bstep (se 1 (by rfl) ⟨2076245, by rfl⟩ : syracuseStep 2768327 = 4152491) B4152491
theorem B2047481 : Blo 1364501 2047481 := bstep (se 2 (by rfl) ⟨767805, by rfl⟩ : syracuseStep 2047481 = 1535611) B1535611
theorem B11664911 : Blo 1364501 11664911 := bstep (se 1 (by rfl) ⟨8748683, by rfl⟩ : syracuseStep 11664911 = 17497367) B17497367
theorem B4611599 : Blo 1364501 4611599 := bstep (se 1 (by rfl) ⟨3458699, by rfl⟩ : syracuseStep 4611599 = 6917399) B6917399
theorem B47914573 : Blo 1364501 47914573 := bstep (se 3 (by rfl) ⟨8983982, by rfl⟩ : syracuseStep 47914573 = 17967965) B17967965
theorem B2047583 : Blo 1364501 2047583 := bstep (se 1 (by rfl) ⟨1535687, by rfl⟩ : syracuseStep 2047583 = 3071375) B3071375
theorem B2047799 : Blo 1364501 2047799 := bstep (se 1 (by rfl) ⟨1535849, by rfl⟩ : syracuseStep 2047799 = 3071699) B3071699
theorem B6561593 : Blo 1364501 6561593 := bstep (se 2 (by rfl) ⟨2460597, by rfl⟩ : syracuseStep 6561593 = 4921195) B4921195
theorem B14196539 : Blo 1364501 14196539 := bstep (se 1 (by rfl) ⟨10647404, by rfl⟩ : syracuseStep 14196539 = 21294809) B21294809
theorem B3071951 : Blo 1364501 3071951 := bstep (se 1 (by rfl) ⟨2303963, by rfl⟩ : syracuseStep 3071951 = 4607927) B4607927
theorem B11673659 : Blo 1364501 11673659 := bstep (se 1 (by rfl) ⟨8755244, by rfl⟩ : syracuseStep 11673659 = 17510489) B17510489
theorem B2048219 : Blo 1364501 2048219 := bstep (se 1 (by rfl) ⟨1536164, by rfl⟩ : syracuseStep 2048219 = 3072329) B3072329
theorem B2048231 : Blo 1364501 2048231 := bstep (se 1 (by rfl) ⟨1536173, by rfl⟩ : syracuseStep 2048231 = 3072347) B3072347
theorem B5832935 : Blo 1364501 5832935 := bstep (se 1 (by rfl) ⟨4374701, by rfl⟩ : syracuseStep 5832935 = 8749403) B8749403
theorem B4374881 : Blo 1364501 4374881 := bstep (se 2 (by rfl) ⟨1640580, by rfl⟩ : syracuseStep 4374881 = 3281161) B3281161
theorem B2048393 : Blo 1364501 2048393 := bstep (se 2 (by rfl) ⟨768147, by rfl⟩ : syracuseStep 2048393 = 1536295) B1536295
theorem B3072455 : Blo 1364501 3072455 := bstep (se 1 (by rfl) ⟨2304341, by rfl⟩ : syracuseStep 3072455 = 4608683) B4608683
theorem B8307143 : Blo 1364501 8307143 := bstep (se 1 (by rfl) ⟨6230357, by rfl⟩ : syracuseStep 8307143 = 12460715) B12460715
theorem B159572429 : Blo 1364501 159572429 := bstep (se 3 (by rfl) ⟨29919830, by rfl⟩ : syracuseStep 159572429 = 59839661) B59839661
theorem B2048489 : Blo 1364501 2048489 := bstep (se 2 (by rfl) ⟨768183, by rfl⟩ : syracuseStep 2048489 = 1536367) B1536367
theorem B19694177 : Blo 1364501 19694177 := bstep (se 2 (by rfl) ⟨7385316, by rfl⟩ : syracuseStep 19694177 = 14770633) B14770633
theorem B2048615 : Blo 1364501 2048615 := bstep (se 1 (by rfl) ⟨1536461, by rfl⟩ : syracuseStep 2048615 = 3072923) B3072923
theorem B1729127 : Blo 1364501 1729127 := bstep (se 1 (by rfl) ⟨1296845, by rfl⟩ : syracuseStep 1729127 = 2593691) B2593691
theorem B2048747 : Blo 1364501 2048747 := bstep (se 1 (by rfl) ⟨1536560, by rfl⟩ : syracuseStep 2048747 = 3073121) B3073121
theorem B2048777 : Blo 1364501 2048777 := bstep (se 2 (by rfl) ⟨768291, by rfl⟩ : syracuseStep 2048777 = 1536583) B1536583
theorem B3072815 : Blo 1364501 3072815 := bstep (se 1 (by rfl) ⟨2304611, by rfl⟩ : syracuseStep 3072815 = 4609223) B4609223
theorem B3457849 : Blo 1364501 3457849 := bstep (se 2 (by rfl) ⟨1296693, by rfl⟩ : syracuseStep 3457849 = 2593387) B2593387
theorem B2048879 : Blo 1364501 2048879 := bstep (se 1 (by rfl) ⟨1536659, by rfl⟩ : syracuseStep 2048879 = 3073319) B3073319
theorem B7775149 : Blo 1364501 7775149 := bstep (se 3 (by rfl) ⟨1457840, by rfl⟩ : syracuseStep 7775149 = 2915681) B2915681
theorem B7005209 : Blo 1364501 7005209 := bstep (se 2 (by rfl) ⟨2626953, by rfl⟩ : syracuseStep 7005209 = 5253907) B5253907
theorem B6915131 : Blo 1364501 6915131 := bstep (se 1 (by rfl) ⟨5186348, by rfl⟩ : syracuseStep 6915131 = 10372697) B10372697
theorem B2303039 : Blo 1364501 2303039 := bstep (se 1 (by rfl) ⟨1727279, by rfl⟩ : syracuseStep 2303039 = 3454559) B3454559
theorem B3458153 : Blo 1364501 3458153 := bstep (se 2 (by rfl) ⟨1296807, by rfl⟩ : syracuseStep 3458153 = 2593615) B2593615
theorem B2049131 : Blo 1364501 2049131 := bstep (se 1 (by rfl) ⟨1536848, by rfl⟩ : syracuseStep 2049131 = 3073697) B3073697
theorem B6915293 : Blo 1364501 6915293 := bstep (se 3 (by rfl) ⟨1296617, by rfl⟩ : syracuseStep 6915293 = 2593235) B2593235
theorem B2049371 : Blo 1364501 2049371 := bstep (se 1 (by rfl) ⟨1537028, by rfl⟩ : syracuseStep 2049371 = 3074057) B3074057
theorem B9848267 : Blo 1364501 9848267 := bstep (se 1 (by rfl) ⟨7386200, by rfl⟩ : syracuseStep 9848267 = 14772401) B14772401
theorem B4605551 : Blo 1364501 4605551 := bstep (se 1 (by rfl) ⟨3454163, by rfl⟩ : syracuseStep 4605551 = 6908327) B6908327
theorem B2303599 : Blo 1364501 2303599 := bstep (se 1 (by rfl) ⟨1727699, by rfl⟩ : syracuseStep 2303599 = 3455399) B3455399
theorem B6227567 : Blo 1364501 6227567 := bstep (se 1 (by rfl) ⟨4670675, by rfl⟩ : syracuseStep 6227567 = 9341351) B9341351
theorem B2049647 : Blo 1364501 2049647 := bstep (se 1 (by rfl) ⟨1537235, by rfl⟩ : syracuseStep 2049647 = 3074471) B3074471
theorem B2049719 : Blo 1364501 2049719 := bstep (se 1 (by rfl) ⟨1537289, by rfl⟩ : syracuseStep 2049719 = 3074579) B3074579
theorem B4605659 : Blo 1364501 4605659 := bstep (se 1 (by rfl) ⟨3454244, by rfl⟩ : syracuseStep 4605659 = 6908489) B6908489
theorem B2303707 : Blo 1364501 2303707 := bstep (se 1 (by rfl) ⟨1727780, by rfl⟩ : syracuseStep 2303707 = 3455561) B3455561
theorem B6563591 : Blo 1364501 6563591 := bstep (se 1 (by rfl) ⟨4922693, by rfl⟩ : syracuseStep 6563591 = 9845387) B9845387
theorem B3073823 : Blo 1364501 3073823 := bstep (se 1 (by rfl) ⟨2305367, by rfl⟩ : syracuseStep 3073823 = 4610735) B4610735
theorem B18950071 : Blo 1364501 18950071 := bstep (se 1 (by rfl) ⟨14212553, by rfl⟩ : syracuseStep 18950071 = 28425107) B28425107
theorem B4376521 : Blo 1364501 4376521 := bstep (se 2 (by rfl) ⟨1641195, by rfl⟩ : syracuseStep 4376521 = 3282391) B3282391
theorem B3074039 : Blo 1364501 3074039 := bstep (se 1 (by rfl) ⟨2305529, by rfl⟩ : syracuseStep 3074039 = 4611059) B4611059
theorem B5540075 : Blo 1364501 5540075 := bstep (se 1 (by rfl) ⟨4155056, by rfl⟩ : syracuseStep 5540075 = 8310113) B8310113
theorem B3279143 : Blo 1364501 3279143 := bstep (se 1 (by rfl) ⟨2459357, by rfl⟩ : syracuseStep 3279143 = 4918715) B4918715
theorem B1845551 : Blo 1364501 1845551 := bstep (se 1 (by rfl) ⟨1384163, by rfl⟩ : syracuseStep 1845551 = 2768327) B2768327
theorem B7776607 : Blo 1364501 7776607 := bstep (se 1 (by rfl) ⟨5832455, by rfl⟩ : syracuseStep 7776607 = 11664911) B11664911
theorem B3074399 : Blo 1364501 3074399 := bstep (se 1 (by rfl) ⟨2305799, by rfl⟩ : syracuseStep 3074399 = 4611599) B4611599
theorem B4672001 : Blo 1364501 4672001 := bstep (se 2 (by rfl) ⟨1752000, by rfl⟩ : syracuseStep 4672001 = 3504001) B3504001
theorem B9464359 : Blo 1364501 9464359 := bstep (se 1 (by rfl) ⟨7098269, by rfl⟩ : syracuseStep 9464359 = 14196539) B14196539
theorem B4606955 : Blo 1364501 4606955 := bstep (se 1 (by rfl) ⟨3455216, by rfl⟩ : syracuseStep 4606955 = 6910433) B6910433
theorem B2305003 : Blo 1364501 2305003 := bstep (se 1 (by rfl) ⟨1728752, by rfl⟩ : syracuseStep 2305003 = 3457505) B3457505
theorem B26242055 : Blo 1364501 26242055 := bstep (se 1 (by rfl) ⟨19681541, by rfl⟩ : syracuseStep 26242055 = 39363083) B39363083
theorem B4607009 : Blo 1364501 4607009 := bstep (se 2 (by rfl) ⟨1727628, by rfl⟩ : syracuseStep 4607009 = 3455257) B3455257
theorem B6908975 : Blo 1364501 6908975 := bstep (se 1 (by rfl) ⟨5181731, by rfl⟩ : syracuseStep 6908975 = 10363463) B10363463
theorem B2305145 : Blo 1364501 2305145 := bstep (se 2 (by rfl) ⟨864429, by rfl⟩ : syracuseStep 2305145 = 1728859) B1728859
theorem B8744071 : Blo 1364501 8744071 := bstep (se 1 (by rfl) ⟨6558053, by rfl⟩ : syracuseStep 8744071 = 13116107) B13116107
theorem B3886505 : Blo 1364501 3886505 := bstep (se 2 (by rfl) ⟨1457439, by rfl⟩ : syracuseStep 3886505 = 2914879) B2914879
theorem B15756743 : Blo 1364501 15756743 := bstep (se 1 (by rfl) ⟨11817557, by rfl⟩ : syracuseStep 15756743 = 23635115) B23635115
theorem B1945063 : Blo 1364501 1945063 := bstep (se 1 (by rfl) ⟨1458797, by rfl⟩ : syracuseStep 1945063 = 2917595) B2917595
theorem B5836283 : Blo 1364501 5836283 := bstep (se 1 (by rfl) ⟨4377212, by rfl⟩ : syracuseStep 5836283 = 8754425) B8754425
theorem B4919059 : Blo 1364501 4919059 := bstep (se 1 (by rfl) ⟨3689294, by rfl⟩ : syracuseStep 4919059 = 7378589) B7378589
theorem B4149377 : Blo 1364501 4149377 := bstep (se 2 (by rfl) ⟨1556016, by rfl⟩ : syracuseStep 4149377 = 3112033) B3112033
theorem B3887291 : Blo 1364501 3887291 := bstep (se 1 (by rfl) ⟨2915468, by rfl⟩ : syracuseStep 3887291 = 5830937) B5830937
theorem B8532361 : Blo 1364501 8532361 := bstep (se 2 (by rfl) ⟨3199635, by rfl⟩ : syracuseStep 8532361 = 6399271) B6399271
theorem B4608467 : Blo 1364501 4608467 := bstep (se 1 (by rfl) ⟨3456350, by rfl⟩ : syracuseStep 4608467 = 6912701) B6912701
theorem B5534201 : Blo 1364501 5534201 := bstep (se 2 (by rfl) ⟨2075325, by rfl⟩ : syracuseStep 5534201 = 4150651) B4150651
theorem B1364583 : Blo 1364501 1364583 := bstep (se 1 (by rfl) ⟨1023437, by rfl⟩ : syracuseStep 1364583 = 2046875) B2046875
theorem B8303249 : Blo 1364501 8303249 := bstep (se 2 (by rfl) ⟨3113718, by rfl⟩ : syracuseStep 8303249 = 6227437) B6227437
theorem B7484167 : Blo 1364501 7484167 := bstep (se 1 (by rfl) ⟨5613125, by rfl⟩ : syracuseStep 7484167 = 11226251) B11226251
theorem B63886097 : Blo 1364501 63886097 := bstep (se 2 (by rfl) ⟨23957286, by rfl⟩ : syracuseStep 63886097 = 47914573) B47914573
theorem B1364847 : Blo 1364501 1364847 := bstep (se 1 (by rfl) ⟨1023635, by rfl⟩ : syracuseStep 1364847 = 2047271) B2047271
theorem B1364903 : Blo 1364501 1364903 := bstep (se 1 (by rfl) ⟨1023677, by rfl⟩ : syracuseStep 1364903 = 2047355) B2047355
theorem B1364987 : Blo 1364501 1364987 := bstep (se 1 (by rfl) ⟨1023740, by rfl⟩ : syracuseStep 1364987 = 2047481) B2047481
theorem B3453961 : Blo 1364501 3453961 := bstep (se 2 (by rfl) ⟨1295235, by rfl⟩ : syracuseStep 3453961 = 2590471) B2590471
theorem B1365055 : Blo 1364501 1365055 := bstep (se 1 (by rfl) ⟨1023791, by rfl⟩ : syracuseStep 1365055 = 2047583) B2047583
theorem B1537087 : Blo 1364501 1537087 := bstep (se 1 (by rfl) ⟨1152815, by rfl⟩ : syracuseStep 1537087 = 2305631) B2305631
theorem B4371563 : Blo 1364501 4371563 := bstep (se 1 (by rfl) ⟨3278672, by rfl⟩ : syracuseStep 4371563 = 6557345) B6557345
theorem B11662451 : Blo 1364501 11662451 := bstep (se 1 (by rfl) ⟨8746838, by rfl⟩ : syracuseStep 11662451 = 17493677) B17493677
theorem B1365199 : Blo 1364501 1365199 := bstep (se 1 (by rfl) ⟨1023899, by rfl⟩ : syracuseStep 1365199 = 2047799) B2047799
theorem B1537231 : Blo 1364501 1537231 := bstep (se 1 (by rfl) ⟨1152923, by rfl⟩ : syracuseStep 1537231 = 2305847) B2305847
theorem B5182811 : Blo 1364501 5182811 := bstep (se 1 (by rfl) ⟨3887108, by rfl⟩ : syracuseStep 5182811 = 7774217) B7774217
theorem B15553943 : Blo 1364501 15553943 := bstep (se 1 (by rfl) ⟨11665457, by rfl⟩ : syracuseStep 15553943 = 23330915) B23330915
theorem B28431767 : Blo 1364501 28431767 := bstep (se 1 (by rfl) ⟨21323825, by rfl⟩ : syracuseStep 28431767 = 42647651) B42647651
theorem B1365403 : Blo 1364501 1365403 := bstep (se 1 (by rfl) ⟨1024052, by rfl⟩ : syracuseStep 1365403 = 2048105) B2048105
theorem B26252747 : Blo 1364501 26252747 := bstep (se 1 (by rfl) ⟨19689560, by rfl⟩ : syracuseStep 26252747 = 39379121) B39379121
theorem B1365615 : Blo 1364501 1365615 := bstep (se 1 (by rfl) ⟨1024211, by rfl⟩ : syracuseStep 1365615 = 2048423) B2048423
theorem B1365671 : Blo 1364501 1365671 := bstep (se 1 (by rfl) ⟨1024253, by rfl⟩ : syracuseStep 1365671 = 2048507) B2048507
theorem B7780049 : Blo 1364501 7780049 := bstep (se 2 (by rfl) ⟨2917518, by rfl⟩ : syracuseStep 7780049 = 5835037) B5835037
theorem B1365755 : Blo 1364501 1365755 := bstep (se 1 (by rfl) ⟨1024316, by rfl⟩ : syracuseStep 1365755 = 2048633) B2048633
theorem B1365791 : Blo 1364501 1365791 := bstep (se 1 (by rfl) ⟨1024343, by rfl⟩ : syracuseStep 1365791 = 2048687) B2048687
theorem B1365823 : Blo 1364501 1365823 := bstep (se 1 (by rfl) ⟨1024367, by rfl⟩ : syracuseStep 1365823 = 2048735) B2048735
theorem B1365999 : Blo 1364501 1365999 := bstep (se 1 (by rfl) ⟨1024499, by rfl⟩ : syracuseStep 1365999 = 2048999) B2048999
theorem B15775859 : Blo 1364501 15775859 := bstep (se 1 (by rfl) ⟨11831894, by rfl⟩ : syracuseStep 15775859 = 23663789) B23663789
theorem B1366171 : Blo 1364501 1366171 := bstep (se 1 (by rfl) ⟨1024628, by rfl⟩ : syracuseStep 1366171 = 2049257) B2049257
theorem B1366207 : Blo 1364501 1366207 := bstep (se 1 (by rfl) ⟨1024655, by rfl⟩ : syracuseStep 1366207 = 2049311) B2049311
theorem B3070151 : Blo 1364501 3070151 := bstep (se 1 (by rfl) ⟨2302613, by rfl⟩ : syracuseStep 3070151 = 4605227) B4605227
theorem B2914537 : Blo 1364501 2914537 := bstep (se 2 (by rfl) ⟨1092951, by rfl⟩ : syracuseStep 2914537 = 2185903) B2185903
theorem B1366319 : Blo 1364501 1366319 := bstep (se 1 (by rfl) ⟨1024739, by rfl⟩ : syracuseStep 1366319 = 2049479) B2049479
theorem B4610411 : Blo 1364501 4610411 := bstep (se 1 (by rfl) ⟨3457808, by rfl⟩ : syracuseStep 4610411 = 6915617) B6915617
theorem B5831021 : Blo 1364501 5831021 := bstep (se 3 (by rfl) ⟨1093316, by rfl⟩ : syracuseStep 5831021 = 2186633) B2186633
theorem B3070331 : Blo 1364501 3070331 := bstep (se 1 (by rfl) ⟨2302748, by rfl⟩ : syracuseStep 3070331 = 4605497) B4605497
theorem B20224399 : Blo 1364501 20224399 := bstep (se 1 (by rfl) ⟨15168299, by rfl⟩ : syracuseStep 20224399 = 30336599) B30336599
theorem B9845327 : Blo 1364501 9845327 := bstep (se 1 (by rfl) ⟨7383995, by rfl⟩ : syracuseStep 9845327 = 14767991) B14767991
theorem B4610681 : Blo 1364501 4610681 := bstep (se 2 (by rfl) ⟨1729005, by rfl⟩ : syracuseStep 4610681 = 3458011) B3458011
theorem B3070601 : Blo 1364501 3070601 := bstep (se 2 (by rfl) ⟨1151475, by rfl⟩ : syracuseStep 3070601 = 2302951) B2302951
theorem B79846073 : Blo 1364501 79846073 := bstep (se 2 (by rfl) ⟨29942277, by rfl⟩ : syracuseStep 79846073 = 59884555) B59884555
theorem B4922203 : Blo 1364501 4922203 := bstep (se 1 (by rfl) ⟨3691652, by rfl⟩ : syracuseStep 4922203 = 7383305) B7383305
theorem B4611113 : Blo 1364501 4611113 := bstep (se 2 (by rfl) ⟨1729167, by rfl⟩ : syracuseStep 4611113 = 3458335) B3458335
theorem B8748121 : Blo 1364501 8748121 := bstep (se 2 (by rfl) ⟨3280545, by rfl⟩ : syracuseStep 8748121 = 6561091) B6561091
theorem B2047097 : Blo 1364501 2047097 := bstep (se 2 (by rfl) ⟨767661, by rfl⟩ : syracuseStep 2047097 = 1535323) B1535323
theorem B4373651 : Blo 1364501 4373651 := bstep (se 1 (by rfl) ⟨3280238, by rfl⟩ : syracuseStep 4373651 = 6560477) B6560477
theorem B3071159 : Blo 1364501 3071159 := bstep (se 1 (by rfl) ⟨2303369, by rfl⟩ : syracuseStep 3071159 = 4606739) B4606739
theorem B10370267 : Blo 1364501 10370267 := bstep (se 1 (by rfl) ⟨7777700, by rfl⟩ : syracuseStep 10370267 = 15555401) B15555401
theorem B2047199 : Blo 1364501 2047199 := bstep (se 1 (by rfl) ⟨1535399, by rfl⟩ : syracuseStep 2047199 = 3070799) B3070799
theorem B2047241 : Blo 1364501 2047241 := bstep (se 2 (by rfl) ⟨767715, by rfl⟩ : syracuseStep 2047241 = 1535431) B1535431
theorem B5831945 : Blo 1364501 5831945 := bstep (se 2 (by rfl) ⟨2186979, by rfl⟩ : syracuseStep 5831945 = 4373959) B4373959
theorem B2047343 : Blo 1364501 2047343 := bstep (se 1 (by rfl) ⟨1535507, by rfl⟩ : syracuseStep 2047343 = 3071015) B3071015
theorem B2047463 : Blo 1364501 2047463 := bstep (se 1 (by rfl) ⟨1535597, by rfl⟩ : syracuseStep 2047463 = 3071195) B3071195
theorem B3890663 : Blo 1364501 3890663 := bstep (se 1 (by rfl) ⟨2917997, by rfl⟩ : syracuseStep 3890663 = 5835995) B5835995
theorem B2047595 : Blo 1364501 2047595 := bstep (se 1 (by rfl) ⟨1535696, by rfl⟩ : syracuseStep 2047595 = 3071393) B3071393
theorem B2047721 : Blo 1364501 2047721 := bstep (se 2 (by rfl) ⟨767895, by rfl⟩ : syracuseStep 2047721 = 1535791) B1535791
theorem B3071735 : Blo 1364501 3071735 := bstep (se 1 (by rfl) ⟨2303801, by rfl⟩ : syracuseStep 3071735 = 4607603) B4607603
theorem B17489681 : Blo 1364501 17489681 := bstep (se 2 (by rfl) ⟨6558630, by rfl⟩ : syracuseStep 17489681 = 13117261) B13117261
theorem B2047865 : Blo 1364501 2047865 := bstep (se 2 (by rfl) ⟨767949, by rfl⟩ : syracuseStep 2047865 = 1535899) B1535899
theorem B4374395 : Blo 1364501 4374395 := bstep (se 1 (by rfl) ⟨3280796, by rfl⟩ : syracuseStep 4374395 = 6561593) B6561593
theorem B3071915 : Blo 1364501 3071915 := bstep (se 1 (by rfl) ⟨2303936, by rfl⟩ : syracuseStep 3071915 = 4607873) B4607873
theorem B2047967 : Blo 1364501 2047967 := bstep (se 1 (by rfl) ⟨1535975, by rfl⟩ : syracuseStep 2047967 = 3071951) B3071951
theorem B1728479 : Blo 1364501 1728479 := bstep (se 1 (by rfl) ⟨1296359, by rfl⟩ : syracuseStep 1728479 = 2592719) B2592719
theorem B7782439 : Blo 1364501 7782439 := bstep (se 1 (by rfl) ⟨5836829, by rfl⟩ : syracuseStep 7782439 = 11673659) B11673659
theorem B2916587 : Blo 1364501 2916587 := bstep (se 1 (by rfl) ⟨2187440, by rfl⟩ : syracuseStep 2916587 = 4374881) B4374881
theorem B2048303 : Blo 1364501 2048303 := bstep (se 1 (by rfl) ⟨1536227, by rfl⟩ : syracuseStep 2048303 = 3072455) B3072455
theorem B5538095 : Blo 1364501 5538095 := bstep (se 1 (by rfl) ⟨4153571, by rfl⟩ : syracuseStep 5538095 = 8307143) B8307143
theorem B106381619 : Blo 1364501 106381619 := bstep (se 1 (by rfl) ⟨79786214, by rfl⟩ : syracuseStep 106381619 = 159572429) B159572429
theorem B3072311 : Blo 1364501 3072311 := bstep (se 1 (by rfl) ⟨2304233, by rfl⟩ : syracuseStep 3072311 = 4608467) B4608467
theorem B2048543 : Blo 1364501 2048543 := bstep (se 1 (by rfl) ⟨1536407, by rfl⟩ : syracuseStep 2048543 = 3072815) B3072815
theorem B7774967 : Blo 1364501 7774967 := bstep (se 1 (by rfl) ⟨5831225, by rfl⟩ : syracuseStep 7774967 = 11662451) B11662451
theorem B9978889 : Blo 1364501 9978889 := bstep (se 2 (by rfl) ⟨3742083, by rfl⟩ : syracuseStep 9978889 = 7484167) B7484167
theorem B75818045 : Blo 1364501 75818045 := bstep (se 3 (by rfl) ⟨14215883, by rfl⟩ : syracuseStep 75818045 = 28431767) B28431767
theorem B6562937 : Blo 1364501 6562937 := bstep (se 2 (by rfl) ⟨2461101, by rfl⟩ : syracuseStep 6562937 = 4922203) B4922203
theorem B5186699 : Blo 1364501 5186699 := bstep (se 1 (by rfl) ⟨3890024, by rfl⟩ : syracuseStep 5186699 = 7780049) B7780049
theorem B4375727 : Blo 1364501 4375727 := bstep (se 1 (by rfl) ⟨3281795, by rfl⟩ : syracuseStep 4375727 = 6563591) B6563591
theorem B2049215 : Blo 1364501 2049215 := bstep (se 1 (by rfl) ⟨1536911, by rfl⟩ : syracuseStep 2049215 = 3073823) B3073823
theorem B3073337 : Blo 1364501 3073337 := bstep (se 2 (by rfl) ⟨1152501, by rfl⟩ : syracuseStep 3073337 = 2305003) B2305003
theorem B2049359 : Blo 1364501 2049359 := bstep (se 1 (by rfl) ⟨1537019, by rfl⟩ : syracuseStep 2049359 = 3074039) B3074039
theorem B4605281 : Blo 1364501 4605281 := bstep (se 2 (by rfl) ⟨1726980, by rfl⟩ : syracuseStep 4605281 = 3453961) B3453961
theorem B2049449 : Blo 1364501 2049449 := bstep (se 2 (by rfl) ⟨768543, by rfl⟩ : syracuseStep 2049449 = 1537087) B1537087
theorem B11658761 : Blo 1364501 11658761 := bstep (se 2 (by rfl) ⟨4372035, by rfl⟩ : syracuseStep 11658761 = 8744071) B8744071
theorem B2049599 : Blo 1364501 2049599 := bstep (se 1 (by rfl) ⟨1537199, by rfl⟩ : syracuseStep 2049599 = 3074399) B3074399
theorem B3073607 : Blo 1364501 3073607 := bstep (se 1 (by rfl) ⟨2305205, by rfl⟩ : syracuseStep 3073607 = 4610411) B4610411
theorem B2049641 : Blo 1364501 2049641 := bstep (se 2 (by rfl) ⟨768615, by rfl⟩ : syracuseStep 2049641 = 1537231) B1537231
theorem B3114667 : Blo 1364501 3114667 := bstep (se 1 (by rfl) ⟨2336000, by rfl⟩ : syracuseStep 3114667 = 4672001) B4672001
theorem B3073787 : Blo 1364501 3073787 := bstep (se 1 (by rfl) ⟨2305340, by rfl⟩ : syracuseStep 3073787 = 4610681) B4610681
theorem B3074075 : Blo 1364501 3074075 := bstep (se 1 (by rfl) ⟨2305556, by rfl⟩ : syracuseStep 3074075 = 4611113) B4611113
theorem B4605983 : Blo 1364501 4605983 := bstep (se 1 (by rfl) ⟨3454487, by rfl⟩ : syracuseStep 4605983 = 6908975) B6908975
theorem B170362925 : Blo 1364501 170362925 := bstep (se 3 (by rfl) ⟨31943048, by rfl⟩ : syracuseStep 170362925 = 63886097) B63886097
theorem B2591003 : Blo 1364501 2591003 := bstep (se 1 (by rfl) ⟨1943252, by rfl⟩ : syracuseStep 2591003 = 3886505) B3886505
theorem B10504495 : Blo 1364501 10504495 := bstep (se 1 (by rfl) ⟨7878371, by rfl⟩ : syracuseStep 10504495 = 15756743) B15756743
theorem B11659787 : Blo 1364501 11659787 := bstep (se 1 (by rfl) ⟨8744840, by rfl⟩ : syracuseStep 11659787 = 17489681) B17489681
theorem B10373669 : Blo 1364501 10373669 := bstep (se 4 (by rfl) ⟨972531, by rfl⟩ : syracuseStep 10373669 = 1945063) B1945063
theorem B25266761 : Blo 1364501 25266761 := bstep (se 2 (by rfl) ⟨9475035, by rfl⟩ : syracuseStep 25266761 = 18950071) B18950071
theorem B5835361 : Blo 1364501 5835361 := bstep (se 2 (by rfl) ⟨2188260, by rfl⟩ : syracuseStep 5835361 = 4376521) B4376521
theorem B18680557 : Blo 1364501 18680557 := bstep (se 3 (by rfl) ⟨3502604, by rfl⟩ : syracuseStep 18680557 = 7005209) B7005209
theorem B2591527 : Blo 1364501 2591527 := bstep (se 1 (by rfl) ⟨1943645, by rfl⟩ : syracuseStep 2591527 = 3887291) B3887291
theorem B3886049 : Blo 1364501 3886049 := bstep (se 2 (by rfl) ⟨1457268, by rfl⟩ : syracuseStep 3886049 = 2914537) B2914537
theorem B1535359 : Blo 1364501 1535359 := bstep (se 1 (by rfl) ⟨1151519, by rfl⟩ : syracuseStep 1535359 = 2303039) B2303039
theorem B12619145 : Blo 1364501 12619145 := bstep (se 2 (by rfl) ⟨4732179, by rfl⟩ : syracuseStep 12619145 = 9464359) B9464359
theorem B2305435 : Blo 1364501 2305435 := bstep (se 1 (by rfl) ⟨1729076, by rfl⟩ : syracuseStep 2305435 = 3458153) B3458153
theorem B17501831 : Blo 1364501 17501831 := bstep (se 1 (by rfl) ⟨13126373, by rfl⟩ : syracuseStep 17501831 = 26252747) B26252747
theorem B6565511 : Blo 1364501 6565511 := bstep (se 1 (by rfl) ⟨4924133, by rfl⟩ : syracuseStep 6565511 = 9848267) B9848267
theorem B10366865 : Blo 1364501 10366865 := bstep (se 2 (by rfl) ⟨3887574, by rfl⟩ : syracuseStep 10366865 = 7775149) B7775149
theorem B14757869 : Blo 1364501 14757869 := bstep (se 3 (by rfl) ⟨2767100, by rfl⟩ : syracuseStep 14757869 = 5534201) B5534201
theorem B3887347 : Blo 1364501 3887347 := bstep (se 1 (by rfl) ⟨2915510, by rfl⟩ : syracuseStep 3887347 = 5831021) B5831021
theorem B17494703 : Blo 1364501 17494703 := bstep (se 1 (by rfl) ⟨13121027, by rfl⟩ : syracuseStep 17494703 = 26242055) B26242055
theorem B1364731 : Blo 1364501 1364731 := bstep (se 1 (by rfl) ⟨1023548, by rfl⟩ : syracuseStep 1364731 = 2047097) B2047097
theorem B1536763 : Blo 1364501 1536763 := bstep (se 1 (by rfl) ⟨1152572, by rfl⟩ : syracuseStep 1536763 = 2305145) B2305145
theorem B1364799 : Blo 1364501 1364799 := bstep (se 1 (by rfl) ⟨1023599, by rfl⟩ : syracuseStep 1364799 = 2047199) B2047199
theorem B1364827 : Blo 1364501 1364827 := bstep (se 1 (by rfl) ⟨1023620, by rfl⟩ : syracuseStep 1364827 = 2047241) B2047241
theorem B3887963 : Blo 1364501 3887963 := bstep (se 1 (by rfl) ⟨2915972, by rfl⟩ : syracuseStep 3887963 = 5831945) B5831945
theorem B1364895 : Blo 1364501 1364895 := bstep (se 1 (by rfl) ⟨1023671, by rfl⟩ : syracuseStep 1364895 = 2047343) B2047343
theorem B1364975 : Blo 1364501 1364975 := bstep (se 1 (by rfl) ⟨1023731, by rfl⟩ : syracuseStep 1364975 = 2047463) B2047463
theorem B2593775 : Blo 1364501 2593775 := bstep (se 1 (by rfl) ⟨1945331, by rfl⟩ : syracuseStep 2593775 = 3890663) B3890663
theorem B6558745 : Blo 1364501 6558745 := bstep (se 2 (by rfl) ⟨2459529, by rfl⟩ : syracuseStep 6558745 = 4919059) B4919059
theorem B1365063 : Blo 1364501 1365063 := bstep (se 1 (by rfl) ⟨1023797, by rfl⟩ : syracuseStep 1365063 = 2047595) B2047595
theorem B1365147 : Blo 1364501 1365147 := bstep (se 1 (by rfl) ⟨1023860, by rfl⟩ : syracuseStep 1365147 = 2047721) B2047721
theorem B1365243 : Blo 1364501 1365243 := bstep (se 1 (by rfl) ⟨1023932, by rfl⟩ : syracuseStep 1365243 = 2047865) B2047865
theorem B4609277 : Blo 1364501 4609277 := bstep (se 3 (by rfl) ⟨864239, by rfl⟩ : syracuseStep 4609277 = 1728479) B1728479
theorem B1365311 : Blo 1364501 1365311 := bstep (se 1 (by rfl) ⟨1023983, by rfl⟩ : syracuseStep 1365311 = 2047967) B2047967
theorem B2766251 : Blo 1364501 2766251 := bstep (se 1 (by rfl) ⟨2074688, by rfl⟩ : syracuseStep 2766251 = 4149377) B4149377
theorem B1365479 : Blo 1364501 1365479 := bstep (se 1 (by rfl) ⟨1024109, by rfl⟩ : syracuseStep 1365479 = 2048219) B2048219
theorem B1365487 : Blo 1364501 1365487 := bstep (se 1 (by rfl) ⟨1024115, by rfl⟩ : syracuseStep 1365487 = 2048231) B2048231
theorem B3888623 : Blo 1364501 3888623 := bstep (se 1 (by rfl) ⟨2916467, by rfl⟩ : syracuseStep 3888623 = 5832935) B5832935
theorem B1365595 : Blo 1364501 1365595 := bstep (se 1 (by rfl) ⟨1024196, by rfl⟩ : syracuseStep 1365595 = 2048393) B2048393
theorem B1365659 : Blo 1364501 1365659 := bstep (se 1 (by rfl) ⟨1024244, by rfl⟩ : syracuseStep 1365659 = 2048489) B2048489
theorem B13129451 : Blo 1364501 13129451 := bstep (se 1 (by rfl) ⟨9847088, by rfl⟩ : syracuseStep 13129451 = 19694177) B19694177
theorem B1365743 : Blo 1364501 1365743 := bstep (se 1 (by rfl) ⟨1024307, by rfl⟩ : syracuseStep 1365743 = 2048615) B2048615
theorem B5535499 : Blo 1364501 5535499 := bstep (se 1 (by rfl) ⟨4151624, by rfl⟩ : syracuseStep 5535499 = 8303249) B8303249
theorem B10368809 : Blo 1364501 10368809 := bstep (se 2 (by rfl) ⟨3888303, by rfl⟩ : syracuseStep 10368809 = 7776607) B7776607
theorem B1365831 : Blo 1364501 1365831 := bstep (se 1 (by rfl) ⟨1024373, by rfl⟩ : syracuseStep 1365831 = 2048747) B2048747
theorem B1365851 : Blo 1364501 1365851 := bstep (se 1 (by rfl) ⟨1024388, by rfl⟩ : syracuseStep 1365851 = 2048777) B2048777
theorem B26965865 : Blo 1364501 26965865 := bstep (se 2 (by rfl) ⟨10112199, by rfl⟩ : syracuseStep 26965865 = 20224399) B20224399
theorem B1365919 : Blo 1364501 1365919 := bstep (se 1 (by rfl) ⟨1024439, by rfl⟩ : syracuseStep 1365919 = 2048879) B2048879
theorem B4610087 : Blo 1364501 4610087 := bstep (se 1 (by rfl) ⟨3457565, by rfl⟩ : syracuseStep 4610087 = 6915131) B6915131
theorem B2914375 : Blo 1364501 2914375 := bstep (se 1 (by rfl) ⟨2185781, by rfl⟩ : syracuseStep 2914375 = 4371563) B4371563
theorem B1366087 : Blo 1364501 1366087 := bstep (se 1 (by rfl) ⟨1024565, by rfl⟩ : syracuseStep 1366087 = 2049131) B2049131
theorem B4921469 : Blo 1364501 4921469 := bstep (se 3 (by rfl) ⟨922775, by rfl⟩ : syracuseStep 4921469 = 1845551) B1845551
theorem B4610195 : Blo 1364501 4610195 := bstep (se 1 (by rfl) ⟨3457646, by rfl⟩ : syracuseStep 4610195 = 6915293) B6915293
theorem B3455207 : Blo 1364501 3455207 := bstep (se 1 (by rfl) ⟨2591405, by rfl⟩ : syracuseStep 3455207 = 5182811) B5182811
theorem B1366247 : Blo 1364501 1366247 := bstep (se 1 (by rfl) ⟨1024685, by rfl⟩ : syracuseStep 1366247 = 2049371) B2049371
theorem B10369295 : Blo 1364501 10369295 := bstep (se 1 (by rfl) ⟨7776971, by rfl⟩ : syracuseStep 10369295 = 15553943) B15553943
theorem B3070367 : Blo 1364501 3070367 := bstep (se 1 (by rfl) ⟨2302775, by rfl⟩ : syracuseStep 3070367 = 4605551) B4605551
theorem B4151711 : Blo 1364501 4151711 := bstep (se 1 (by rfl) ⟨3113783, by rfl⟩ : syracuseStep 4151711 = 6227567) B6227567
theorem B4610465 : Blo 1364501 4610465 := bstep (se 2 (by rfl) ⟨1728924, by rfl⟩ : syracuseStep 4610465 = 3457849) B3457849
theorem B1366431 : Blo 1364501 1366431 := bstep (se 1 (by rfl) ⟨1024823, by rfl⟩ : syracuseStep 1366431 = 2049647) B2049647
theorem B1366479 : Blo 1364501 1366479 := bstep (se 1 (by rfl) ⟨1024859, by rfl⟩ : syracuseStep 1366479 = 2049719) B2049719
theorem B3070439 : Blo 1364501 3070439 := bstep (se 1 (by rfl) ⟨2302829, by rfl⟩ : syracuseStep 3070439 = 4605659) B4605659
theorem B10517239 : Blo 1364501 10517239 := bstep (se 1 (by rfl) ⟨7887929, by rfl⟩ : syracuseStep 10517239 = 15775859) B15775859
theorem B11664161 : Blo 1364501 11664161 := bstep (se 2 (by rfl) ⟨4374060, by rfl⟩ : syracuseStep 11664161 = 8748121) B8748121
theorem B2046767 : Blo 1364501 2046767 := bstep (se 1 (by rfl) ⟨1535075, by rfl⟩ : syracuseStep 2046767 = 3070151) B3070151
theorem B3693383 : Blo 1364501 3693383 := bstep (se 1 (by rfl) ⟨2770037, by rfl⟩ : syracuseStep 3693383 = 5540075) B5540075
theorem B2186095 : Blo 1364501 2186095 := bstep (se 1 (by rfl) ⟨1639571, by rfl⟩ : syracuseStep 2186095 = 3279143) B3279143
theorem B26254205 : Blo 1364501 26254205 := bstep (se 3 (by rfl) ⟨4922663, by rfl⟩ : syracuseStep 26254205 = 9845327) B9845327
theorem B2046887 : Blo 1364501 2046887 := bstep (se 1 (by rfl) ⟨1535165, by rfl⟩ : syracuseStep 2046887 = 3070331) B3070331
theorem B4611005 : Blo 1364501 4611005 := bstep (se 3 (by rfl) ⟨864563, by rfl⟩ : syracuseStep 4611005 = 1729127) B1729127
theorem B2047067 : Blo 1364501 2047067 := bstep (se 1 (by rfl) ⟨1535300, by rfl⟩ : syracuseStep 2047067 = 3070601) B3070601
theorem B53230715 : Blo 1364501 53230715 := bstep (se 1 (by rfl) ⟨39923036, by rfl⟩ : syracuseStep 53230715 = 79846073) B79846073
theorem B3071303 : Blo 1364501 3071303 := bstep (se 1 (by rfl) ⟨2303477, by rfl⟩ : syracuseStep 3071303 = 4606955) B4606955
theorem B3071339 : Blo 1364501 3071339 := bstep (se 1 (by rfl) ⟨2303504, by rfl⟩ : syracuseStep 3071339 = 4607009) B4607009
theorem B45505925 : Blo 1364501 45505925 := bstep (se 4 (by rfl) ⟨4266180, by rfl⟩ : syracuseStep 45505925 = 8532361) B8532361
theorem B2915767 : Blo 1364501 2915767 := bstep (se 1 (by rfl) ⟨2186825, by rfl⟩ : syracuseStep 2915767 = 4373651) B4373651
theorem B2047439 : Blo 1364501 2047439 := bstep (se 1 (by rfl) ⟨1535579, by rfl⟩ : syracuseStep 2047439 = 3071159) B3071159
theorem B6913511 : Blo 1364501 6913511 := bstep (se 1 (by rfl) ⟨5185133, by rfl⟩ : syracuseStep 6913511 = 10370267) B10370267
theorem B3071465 : Blo 1364501 3071465 := bstep (se 2 (by rfl) ⟨1151799, by rfl⟩ : syracuseStep 3071465 = 2303599) B2303599
theorem B3071609 : Blo 1364501 3071609 := bstep (se 2 (by rfl) ⟨1151853, by rfl⟩ : syracuseStep 3071609 = 2303707) B2303707
theorem B3890855 : Blo 1364501 3890855 := bstep (se 1 (by rfl) ⟨2918141, by rfl⟩ : syracuseStep 3890855 = 5836283) B5836283
theorem B2047823 : Blo 1364501 2047823 := bstep (se 1 (by rfl) ⟨1535867, by rfl⟩ : syracuseStep 2047823 = 3071735) B3071735
theorem B2916263 : Blo 1364501 2916263 := bstep (se 1 (by rfl) ⟨2187197, by rfl⟩ : syracuseStep 2916263 = 4374395) B4374395
theorem B2047943 : Blo 1364501 2047943 := bstep (se 1 (by rfl) ⟨1535957, by rfl⟩ : syracuseStep 2047943 = 3071915) B3071915
theorem B2048207 : Blo 1364501 2048207 := bstep (se 1 (by rfl) ⟨1536155, by rfl⟩ : syracuseStep 2048207 = 3072311) B3072311
theorem B1729183 : Blo 1364501 1729183 := bstep (se 1 (by rfl) ⟨1296887, by rfl⟩ : syracuseStep 1729183 = 2593775) B2593775
theorem B4375291 : Blo 1364501 4375291 := bstep (se 1 (by rfl) ⟨3281468, by rfl⟩ : syracuseStep 4375291 = 6562937) B6562937
theorem B3457799 : Blo 1364501 3457799 := bstep (se 1 (by rfl) ⟨2593349, by rfl⟩ : syracuseStep 3457799 = 5186699) B5186699
theorem B2917151 : Blo 1364501 2917151 := bstep (se 1 (by rfl) ⟨2187863, by rfl⟩ : syracuseStep 2917151 = 4375727) B4375727
theorem B3072851 : Blo 1364501 3072851 := bstep (se 1 (by rfl) ⟨2304638, by rfl⟩ : syracuseStep 3072851 = 4609277) B4609277
theorem B2048891 : Blo 1364501 2048891 := bstep (se 1 (by rfl) ⟨1536668, by rfl⟩ : syracuseStep 2048891 = 3073337) B3073337
theorem B2049017 : Blo 1364501 2049017 := bstep (se 2 (by rfl) ⟨768381, by rfl⟩ : syracuseStep 2049017 = 1536763) B1536763
theorem B2049071 : Blo 1364501 2049071 := bstep (se 1 (by rfl) ⟨1536803, by rfl⟩ : syracuseStep 2049071 = 3073607) B3073607
theorem B2049191 : Blo 1364501 2049191 := bstep (se 1 (by rfl) ⟨1536893, by rfl⟩ : syracuseStep 2049191 = 3073787) B3073787
theorem B13305185 : Blo 1364501 13305185 := bstep (se 2 (by rfl) ⟨4989444, by rfl⟩ : syracuseStep 13305185 = 9978889) B9978889
theorem B2049383 : Blo 1364501 2049383 := bstep (se 1 (by rfl) ⟨1537037, by rfl⟩ : syracuseStep 2049383 = 3074075) B3074075
theorem B3073391 : Blo 1364501 3073391 := bstep (se 1 (by rfl) ⟨2305043, by rfl⟩ : syracuseStep 3073391 = 4610087) B4610087
theorem B113575283 : Blo 1364501 113575283 := bstep (se 1 (by rfl) ⟨85181462, by rfl⟩ : syracuseStep 113575283 = 170362925) B170362925
theorem B3073463 : Blo 1364501 3073463 := bstep (se 1 (by rfl) ⟨2305097, by rfl⟩ : syracuseStep 3073463 = 4610195) B4610195
theorem B2303471 : Blo 1364501 2303471 := bstep (se 1 (by rfl) ⟨1727603, by rfl⟩ : syracuseStep 2303471 = 3455207) B3455207
theorem B3073643 : Blo 1364501 3073643 := bstep (se 1 (by rfl) ⟨2305232, by rfl⟩ : syracuseStep 3073643 = 4610465) B4610465
theorem B6915779 : Blo 1364501 6915779 := bstep (se 1 (by rfl) ⟨5186834, by rfl⟩ : syracuseStep 6915779 = 10373669) B10373669
theorem B16844507 : Blo 1364501 16844507 := bstep (se 1 (by rfl) ⟨12633380, by rfl⟩ : syracuseStep 16844507 = 25266761) B25266761
theorem B7776107 : Blo 1364501 7776107 := bstep (se 1 (by rfl) ⟨5832080, by rfl⟩ : syracuseStep 7776107 = 11664161) B11664161
theorem B3073913 : Blo 1364501 3073913 := bstep (se 2 (by rfl) ⟨1152717, by rfl⟩ : syracuseStep 3073913 = 2305435) B2305435
theorem B3074003 : Blo 1364501 3074003 := bstep (se 1 (by rfl) ⟨2305502, by rfl⟩ : syracuseStep 3074003 = 4611005) B4611005
theorem B2590699 : Blo 1364501 2590699 := bstep (se 1 (by rfl) ⟨1943024, by rfl⟩ : syracuseStep 2590699 = 3886049) B3886049
theorem B30337283 : Blo 1364501 30337283 := bstep (se 1 (by rfl) ⟨22752962, by rfl⟩ : syracuseStep 30337283 = 45505925) B45505925
theorem B11667887 : Blo 1364501 11667887 := bstep (se 1 (by rfl) ⟨8750915, by rfl⟩ : syracuseStep 11667887 = 17501831) B17501831
theorem B4377007 : Blo 1364501 4377007 := bstep (se 1 (by rfl) ⟨3282755, by rfl⟩ : syracuseStep 4377007 = 6565511) B6565511
theorem B1944175 : Blo 1364501 1944175 := bstep (se 1 (by rfl) ⟨1458131, by rfl⟩ : syracuseStep 1944175 = 2916263) B2916263
theorem B3885833 : Blo 1364501 3885833 := bstep (se 2 (by rfl) ⟨1457187, by rfl⟩ : syracuseStep 3885833 = 2914375) B2914375
theorem B202181453 : Blo 1364501 202181453 := bstep (se 3 (by rfl) ⟨37909022, by rfl⟩ : syracuseStep 202181453 = 75818045) B75818045
theorem B70921079 : Blo 1364501 70921079 := bstep (se 1 (by rfl) ⟨53190809, by rfl⟩ : syracuseStep 70921079 = 106381619) B106381619
theorem B2591975 : Blo 1364501 2591975 := bstep (se 1 (by rfl) ⟨1943981, by rfl⟩ : syracuseStep 2591975 = 3887963) B3887963
theorem B7777565 : Blo 1364501 7777565 := bstep (se 3 (by rfl) ⟨1458293, by rfl⟩ : syracuseStep 7777565 = 2916587) B2916587
theorem B24907409 : Blo 1364501 24907409 := bstep (se 2 (by rfl) ⟨9340278, by rfl⟩ : syracuseStep 24907409 = 18680557) B18680557
theorem B2592415 : Blo 1364501 2592415 := bstep (se 1 (by rfl) ⟨1944311, by rfl⟩ : syracuseStep 2592415 = 3888623) B3888623
theorem B7376669 : Blo 1364501 7376669 := bstep (se 3 (by rfl) ⟨1383125, by rfl⟩ : syracuseStep 7376669 = 2766251) B2766251
theorem B8752967 : Blo 1364501 8752967 := bstep (se 1 (by rfl) ⟨6564725, by rfl⟩ : syracuseStep 8752967 = 13129451) B13129451
theorem B17977243 : Blo 1364501 17977243 := bstep (se 1 (by rfl) ⟨13482932, by rfl⟩ : syracuseStep 17977243 = 26965865) B26965865
theorem B8744993 : Blo 1364501 8744993 := bstep (se 2 (by rfl) ⟨3279372, by rfl⟩ : syracuseStep 8744993 = 6558745) B6558745
theorem B3280979 : Blo 1364501 3280979 := bstep (se 1 (by rfl) ⟨2460734, by rfl⟩ : syracuseStep 3280979 = 4921469) B4921469
theorem B10375613 : Blo 1364501 10375613 := bstep (se 3 (by rfl) ⟨1945427, by rfl⟩ : syracuseStep 10375613 = 3890855) B3890855
theorem B1364511 : Blo 1364501 1364511 := bstep (se 1 (by rfl) ⟨1023383, by rfl⟩ : syracuseStep 1364511 = 2046767) B2046767
theorem B2462255 : Blo 1364501 2462255 := bstep (se 1 (by rfl) ⟨1846691, by rfl⟩ : syracuseStep 2462255 = 3693383) B3693383
theorem B3887689 : Blo 1364501 3887689 := bstep (se 2 (by rfl) ⟨1457883, by rfl⟩ : syracuseStep 3887689 = 2915767) B2915767
theorem B17502803 : Blo 1364501 17502803 := bstep (se 1 (by rfl) ⟨13127102, by rfl⟩ : syracuseStep 17502803 = 26254205) B26254205
theorem B1364591 : Blo 1364501 1364591 := bstep (se 1 (by rfl) ⟨1023443, by rfl⟩ : syracuseStep 1364591 = 2046887) B2046887
theorem B1364711 : Blo 1364501 1364711 := bstep (se 1 (by rfl) ⟨1023533, by rfl⟩ : syracuseStep 1364711 = 2047067) B2047067
theorem B1364959 : Blo 1364501 1364959 := bstep (se 1 (by rfl) ⟨1023719, by rfl⟩ : syracuseStep 1364959 = 2047439) B2047439
theorem B4609007 : Blo 1364501 4609007 := bstep (se 1 (by rfl) ⟨3456755, by rfl⟩ : syracuseStep 4609007 = 6913511) B6913511
theorem B1365215 : Blo 1364501 1365215 := bstep (se 1 (by rfl) ⟨1023911, by rfl⟩ : syracuseStep 1365215 = 2047823) B2047823
theorem B6911243 : Blo 1364501 6911243 := bstep (se 1 (by rfl) ⟨5183432, by rfl⟩ : syracuseStep 6911243 = 10366865) B10366865
theorem B1365295 : Blo 1364501 1365295 := bstep (se 1 (by rfl) ⟨1023971, by rfl⟩ : syracuseStep 1365295 = 2047943) B2047943
theorem B10376585 : Blo 1364501 10376585 := bstep (se 2 (by rfl) ⟨3891219, by rfl⟩ : syracuseStep 10376585 = 7782439) B7782439
theorem B1365535 : Blo 1364501 1365535 := bstep (se 1 (by rfl) ⟨1024151, by rfl⟩ : syracuseStep 1365535 = 2048303) B2048303
theorem B3692063 : Blo 1364501 3692063 := bstep (se 1 (by rfl) ⟨2769047, by rfl⟩ : syracuseStep 3692063 = 5538095) B5538095
theorem B5183129 : Blo 1364501 5183129 := bstep (se 2 (by rfl) ⟨1943673, by rfl⟩ : syracuseStep 5183129 = 3887347) B3887347
theorem B1365695 : Blo 1364501 1365695 := bstep (se 1 (by rfl) ⟨1024271, by rfl⟩ : syracuseStep 1365695 = 2048543) B2048543
theorem B14005993 : Blo 1364501 14005993 := bstep (se 2 (by rfl) ⟨5252247, by rfl⟩ : syracuseStep 14005993 = 10504495) B10504495
theorem B11663135 : Blo 1364501 11663135 := bstep (se 1 (by rfl) ⟨8747351, by rfl⟩ : syracuseStep 11663135 = 17494703) B17494703
theorem B5183311 : Blo 1364501 5183311 := bstep (se 1 (by rfl) ⟨3887483, by rfl⟩ : syracuseStep 5183311 = 7774967) B7774967
theorem B1366143 : Blo 1364501 1366143 := bstep (se 1 (by rfl) ⟨1024607, by rfl⟩ : syracuseStep 1366143 = 2049215) B2049215
theorem B7780481 : Blo 1364501 7780481 := bstep (se 2 (by rfl) ⟨2917680, by rfl⟩ : syracuseStep 7780481 = 5835361) B5835361
theorem B1366239 : Blo 1364501 1366239 := bstep (se 1 (by rfl) ⟨1024679, by rfl⟩ : syracuseStep 1366239 = 2049359) B2049359
theorem B3070187 : Blo 1364501 3070187 := bstep (se 1 (by rfl) ⟨2302640, by rfl⟩ : syracuseStep 3070187 = 4605281) B4605281
theorem B1366299 : Blo 1364501 1366299 := bstep (se 1 (by rfl) ⟨1024724, by rfl⟩ : syracuseStep 1366299 = 2049449) B2049449
theorem B14022985 : Blo 1364501 14022985 := bstep (se 2 (by rfl) ⟨5258619, by rfl⟩ : syracuseStep 14022985 = 10517239) B10517239
theorem B7772507 : Blo 1364501 7772507 := bstep (se 1 (by rfl) ⟨5829380, by rfl⟩ : syracuseStep 7772507 = 11658761) B11658761
theorem B1366399 : Blo 1364501 1366399 := bstep (se 1 (by rfl) ⟨1024799, by rfl⟩ : syracuseStep 1366399 = 2049599) B2049599
theorem B3455369 : Blo 1364501 3455369 := bstep (se 2 (by rfl) ⟨1295763, by rfl⟩ : syracuseStep 3455369 = 2591527) B2591527
theorem B1366427 : Blo 1364501 1366427 := bstep (se 1 (by rfl) ⟨1024820, by rfl⟩ : syracuseStep 1366427 = 2049641) B2049641
theorem B2914793 : Blo 1364501 2914793 := bstep (se 2 (by rfl) ⟨1093047, by rfl⟩ : syracuseStep 2914793 = 2186095) B2186095
theorem B6912539 : Blo 1364501 6912539 := bstep (se 1 (by rfl) ⟨5184404, by rfl⟩ : syracuseStep 6912539 = 10368809) B10368809
theorem B3070655 : Blo 1364501 3070655 := bstep (se 1 (by rfl) ⟨2302991, by rfl⟩ : syracuseStep 3070655 = 4605983) B4605983
theorem B6912863 : Blo 1364501 6912863 := bstep (se 1 (by rfl) ⟨5184647, by rfl⟩ : syracuseStep 6912863 = 10369295) B10369295
theorem B1727335 : Blo 1364501 1727335 := bstep (se 1 (by rfl) ⟨1295501, by rfl⟩ : syracuseStep 1727335 = 2591003) B2591003
theorem B2046911 : Blo 1364501 2046911 := bstep (se 1 (by rfl) ⟨1535183, by rfl⟩ : syracuseStep 2046911 = 3070367) B3070367
theorem B2767807 : Blo 1364501 2767807 := bstep (se 1 (by rfl) ⟨2075855, by rfl⟩ : syracuseStep 2767807 = 4151711) B4151711
theorem B2046959 : Blo 1364501 2046959 := bstep (se 1 (by rfl) ⟨1535219, by rfl⟩ : syracuseStep 2046959 = 3070439) B3070439
theorem B7773191 : Blo 1364501 7773191 := bstep (se 1 (by rfl) ⟨5829893, by rfl⟩ : syracuseStep 7773191 = 11659787) B11659787
theorem B2047145 : Blo 1364501 2047145 := bstep (se 2 (by rfl) ⟨767679, by rfl⟩ : syracuseStep 2047145 = 1535359) B1535359
theorem B35487143 : Blo 1364501 35487143 := bstep (se 1 (by rfl) ⟨26615357, by rfl⟩ : syracuseStep 35487143 = 53230715) B53230715
theorem B2047535 : Blo 1364501 2047535 := bstep (se 1 (by rfl) ⟨1535651, by rfl⟩ : syracuseStep 2047535 = 3071303) B3071303
theorem B4152889 : Blo 1364501 4152889 := bstep (se 2 (by rfl) ⟨1557333, by rfl⟩ : syracuseStep 4152889 = 3114667) B3114667
theorem B2047559 : Blo 1364501 2047559 := bstep (se 1 (by rfl) ⟨1535669, by rfl⟩ : syracuseStep 2047559 = 3071339) B3071339
theorem B8412763 : Blo 1364501 8412763 := bstep (se 1 (by rfl) ⟨6309572, by rfl⟩ : syracuseStep 8412763 = 12619145) B12619145
theorem B2047643 : Blo 1364501 2047643 := bstep (se 1 (by rfl) ⟨1535732, by rfl⟩ : syracuseStep 2047643 = 3071465) B3071465
theorem B7380665 : Blo 1364501 7380665 := bstep (se 2 (by rfl) ⟨2767749, by rfl⟩ : syracuseStep 7380665 = 5535499) B5535499
theorem B2047739 : Blo 1364501 2047739 := bstep (se 1 (by rfl) ⟨1535804, by rfl⟩ : syracuseStep 2047739 = 3071609) B3071609
theorem B9838579 : Blo 1364501 9838579 := bstep (se 1 (by rfl) ⟨7378934, by rfl⟩ : syracuseStep 9838579 = 14757869) B14757869
theorem B2187319 : Blo 1364501 2187319 := bstep (se 1 (by rfl) ⟨1640489, by rfl⟩ : syracuseStep 2187319 = 3280979) B3280979
theorem B2048567 : Blo 1364501 2048567 := bstep (se 1 (by rfl) ⟨1536425, by rfl⟩ : syracuseStep 2048567 = 3072851) B3072851
theorem B3072671 : Blo 1364501 3072671 := bstep (se 1 (by rfl) ⟨2304503, by rfl⟩ : syracuseStep 3072671 = 4609007) B4609007
theorem B2048927 : Blo 1364501 2048927 := bstep (se 1 (by rfl) ⟨1536695, by rfl⟩ : syracuseStep 2048927 = 3073391) B3073391
theorem B2048975 : Blo 1364501 2048975 := bstep (se 1 (by rfl) ⟨1536731, by rfl⟩ : syracuseStep 2048975 = 3073463) B3073463
theorem B5833721 : Blo 1364501 5833721 := bstep (se 2 (by rfl) ⟨2187645, by rfl⟩ : syracuseStep 5833721 = 4375291) B4375291
theorem B2049095 : Blo 1364501 2049095 := bstep (se 1 (by rfl) ⟨1536821, by rfl⟩ : syracuseStep 2049095 = 3073643) B3073643
theorem B2303113 : Blo 1364501 2303113 := bstep (se 2 (by rfl) ⟨863667, by rfl⟩ : syracuseStep 2303113 = 1727335) B1727335
theorem B7775423 : Blo 1364501 7775423 := bstep (se 1 (by rfl) ⟨5831567, by rfl⟩ : syracuseStep 7775423 = 11663135) B11663135
theorem B2049275 : Blo 1364501 2049275 := bstep (se 1 (by rfl) ⟨1536956, by rfl⟩ : syracuseStep 2049275 = 3073913) B3073913
theorem B2049335 : Blo 1364501 2049335 := bstep (se 1 (by rfl) ⟨1537001, by rfl⟩ : syracuseStep 2049335 = 3074003) B3074003
theorem B5186987 : Blo 1364501 5186987 := bstep (se 1 (by rfl) ⟨3890240, by rfl⟩ : syracuseStep 5186987 = 7780481) B7780481
theorem B2303579 : Blo 1364501 2303579 := bstep (se 1 (by rfl) ⟨1727684, by rfl⟩ : syracuseStep 2303579 = 3455369) B3455369
theorem B1943195 : Blo 1364501 1943195 := bstep (se 1 (by rfl) ⟨1457396, by rfl⟩ : syracuseStep 1943195 = 2914793) B2914793
theorem B2590555 : Blo 1364501 2590555 := bstep (se 1 (by rfl) ⟨1942916, by rfl⟩ : syracuseStep 2590555 = 3885833) B3885833
theorem B11217017 : Blo 1364501 11217017 := bstep (se 2 (by rfl) ⟨4206381, by rfl⟩ : syracuseStep 11217017 = 8412763) B8412763
theorem B4917779 : Blo 1364501 4917779 := bstep (se 1 (by rfl) ⟨3688334, by rfl⟩ : syracuseStep 4917779 = 7376669) B7376669
theorem B5835311 : Blo 1364501 5835311 := bstep (se 1 (by rfl) ⟨4376483, by rfl⟩ : syracuseStep 5835311 = 8752967) B8752967
theorem B13118105 : Blo 1364501 13118105 := bstep (se 2 (by rfl) ⟨4919289, by rfl⟩ : syracuseStep 13118105 = 9838579) B9838579
theorem B6917075 : Blo 1364501 6917075 := bstep (se 1 (by rfl) ⟨5187806, by rfl⟩ : syracuseStep 6917075 = 10375613) B10375613
theorem B1641503 : Blo 1364501 1641503 := bstep (se 1 (by rfl) ⟨1231127, by rfl⟩ : syracuseStep 1641503 = 2462255) B2462255
theorem B11668535 : Blo 1364501 11668535 := bstep (se 1 (by rfl) ⟨8751401, by rfl⟩ : syracuseStep 11668535 = 17502803) B17502803
theorem B18697313 : Blo 1364501 18697313 := bstep (se 2 (by rfl) ⟨7011492, by rfl⟩ : syracuseStep 18697313 = 14022985) B14022985
theorem B2305199 : Blo 1364501 2305199 := bstep (se 1 (by rfl) ⟨1728899, by rfl⟩ : syracuseStep 2305199 = 3457799) B3457799
theorem B1944767 : Blo 1364501 1944767 := bstep (se 1 (by rfl) ⟨1458575, by rfl⟩ : syracuseStep 1944767 = 2917151) B2917151
theorem B2592233 : Blo 1364501 2592233 := bstep (se 2 (by rfl) ⟨972087, by rfl⟩ : syracuseStep 2592233 = 1944175) B1944175
theorem B4607495 : Blo 1364501 4607495 := bstep (se 1 (by rfl) ⟨3455621, by rfl⟩ : syracuseStep 4607495 = 6911243) B6911243
theorem B2305577 : Blo 1364501 2305577 := bstep (se 2 (by rfl) ⟨864591, by rfl⟩ : syracuseStep 2305577 = 1729183) B1729183
theorem B6917723 : Blo 1364501 6917723 := bstep (se 1 (by rfl) ⟨5188292, by rfl⟩ : syracuseStep 6917723 = 10376585) B10376585
theorem B1535647 : Blo 1364501 1535647 := bstep (se 1 (by rfl) ⟨1151735, by rfl⟩ : syracuseStep 1535647 = 2303471) B2303471
theorem B2461375 : Blo 1364501 2461375 := bstep (se 1 (by rfl) ⟨1846031, by rfl⟩ : syracuseStep 2461375 = 3692063) B3692063
theorem B3690409 : Blo 1364501 3690409 := bstep (se 2 (by rfl) ⟨1383903, by rfl⟩ : syracuseStep 3690409 = 2767807) B2767807
theorem B5181671 : Blo 1364501 5181671 := bstep (se 1 (by rfl) ⟨3886253, by rfl⟩ : syracuseStep 5181671 = 7772507) B7772507
theorem B7778591 : Blo 1364501 7778591 := bstep (se 1 (by rfl) ⟨5833943, by rfl⟩ : syracuseStep 7778591 = 11667887) B11667887
theorem B4608359 : Blo 1364501 4608359 := bstep (se 1 (by rfl) ⟨3456269, by rfl⟩ : syracuseStep 4608359 = 6912539) B6912539
theorem B134787635 : Blo 1364501 134787635 := bstep (se 1 (by rfl) ⟨101090726, by rfl⟩ : syracuseStep 134787635 = 202181453) B202181453
theorem B4608575 : Blo 1364501 4608575 := bstep (se 1 (by rfl) ⟨3456431, by rfl⟩ : syracuseStep 4608575 = 6912863) B6912863
theorem B47280719 : Blo 1364501 47280719 := bstep (se 1 (by rfl) ⟨35460539, by rfl⟩ : syracuseStep 47280719 = 70921079) B70921079
theorem B1364607 : Blo 1364501 1364607 := bstep (se 1 (by rfl) ⟨1023455, by rfl⟩ : syracuseStep 1364607 = 2046911) B2046911
theorem B1364639 : Blo 1364501 1364639 := bstep (se 1 (by rfl) ⟨1023479, by rfl⟩ : syracuseStep 1364639 = 2046959) B2046959
theorem B5182127 : Blo 1364501 5182127 := bstep (se 1 (by rfl) ⟨3886595, by rfl⟩ : syracuseStep 5182127 = 7773191) B7773191
theorem B1364763 : Blo 1364501 1364763 := bstep (se 1 (by rfl) ⟨1023572, by rfl⟩ : syracuseStep 1364763 = 2047145) B2047145
theorem B23344037 : Blo 1364501 23344037 := bstep (se 4 (by rfl) ⟨2188503, by rfl⟩ : syracuseStep 23344037 = 4377007) B4377007
theorem B18674657 : Blo 1364501 18674657 := bstep (se 2 (by rfl) ⟨7002996, by rfl⟩ : syracuseStep 18674657 = 14005993) B14005993
theorem B1365023 : Blo 1364501 1365023 := bstep (se 1 (by rfl) ⟨1023767, by rfl⟩ : syracuseStep 1365023 = 2047535) B2047535
theorem B1365039 : Blo 1364501 1365039 := bstep (se 1 (by rfl) ⟨1023779, by rfl⟩ : syracuseStep 1365039 = 2047559) B2047559
theorem B1365095 : Blo 1364501 1365095 := bstep (se 1 (by rfl) ⟨1023821, by rfl⟩ : syracuseStep 1365095 = 2047643) B2047643
theorem B6911081 : Blo 1364501 6911081 := bstep (se 2 (by rfl) ⟨2591655, by rfl⟩ : syracuseStep 6911081 = 5183311) B5183311
theorem B4920443 : Blo 1364501 4920443 := bstep (se 1 (by rfl) ⟨3690332, by rfl⟩ : syracuseStep 4920443 = 7380665) B7380665
theorem B1365159 : Blo 1364501 1365159 := bstep (se 1 (by rfl) ⟨1023869, by rfl⟩ : syracuseStep 1365159 = 2047739) B2047739
theorem B3454265 : Blo 1364501 3454265 := bstep (se 2 (by rfl) ⟨1295349, by rfl⟩ : syracuseStep 3454265 = 2590699) B2590699
theorem B5829995 : Blo 1364501 5829995 := bstep (se 1 (by rfl) ⟨4372496, by rfl⟩ : syracuseStep 5829995 = 8744993) B8744993
theorem B1365471 : Blo 1364501 1365471 := bstep (se 1 (by rfl) ⟨1024103, by rfl⟩ : syracuseStep 1365471 = 2048207) B2048207
theorem B22148741 : Blo 1364501 22148741 := bstep (se 4 (by rfl) ⟨2076444, by rfl⟩ : syracuseStep 22148741 = 4152889) B4152889
theorem B1365927 : Blo 1364501 1365927 := bstep (se 1 (by rfl) ⟨1024445, by rfl⟩ : syracuseStep 1365927 = 2048891) B2048891
theorem B1366011 : Blo 1364501 1366011 := bstep (se 1 (by rfl) ⟨1024508, by rfl⟩ : syracuseStep 1366011 = 2049017) B2049017
theorem B1366047 : Blo 1364501 1366047 := bstep (se 1 (by rfl) ⟨1024535, by rfl⟩ : syracuseStep 1366047 = 2049071) B2049071
theorem B5183585 : Blo 1364501 5183585 := bstep (se 2 (by rfl) ⟨1943844, by rfl⟩ : syracuseStep 5183585 = 3887689) B3887689
theorem B1366127 : Blo 1364501 1366127 := bstep (se 1 (by rfl) ⟨1024595, by rfl⟩ : syracuseStep 1366127 = 2049191) B2049191
theorem B8870123 : Blo 1364501 8870123 := bstep (se 1 (by rfl) ⟨6652592, by rfl⟩ : syracuseStep 8870123 = 13305185) B13305185
theorem B1366255 : Blo 1364501 1366255 := bstep (se 1 (by rfl) ⟨1024691, by rfl⟩ : syracuseStep 1366255 = 2049383) B2049383
theorem B75716855 : Blo 1364501 75716855 := bstep (se 1 (by rfl) ⟨56787641, by rfl⟩ : syracuseStep 75716855 = 113575283) B113575283
theorem B3455419 : Blo 1364501 3455419 := bstep (se 1 (by rfl) ⟨2591564, by rfl⟩ : syracuseStep 3455419 = 5183129) B5183129
theorem B4610519 : Blo 1364501 4610519 := bstep (se 1 (by rfl) ⟨3457889, by rfl⟩ : syracuseStep 4610519 = 6915779) B6915779
theorem B11229671 : Blo 1364501 11229671 := bstep (se 1 (by rfl) ⟨8422253, by rfl⟩ : syracuseStep 11229671 = 16844507) B16844507
theorem B5184071 : Blo 1364501 5184071 := bstep (se 1 (by rfl) ⟨3888053, by rfl⟩ : syracuseStep 5184071 = 7776107) B7776107
theorem B2046791 : Blo 1364501 2046791 := bstep (se 1 (by rfl) ⟨1535093, by rfl⟩ : syracuseStep 2046791 = 3070187) B3070187
theorem B20224855 : Blo 1364501 20224855 := bstep (se 1 (by rfl) ⟨15168641, by rfl⟩ : syracuseStep 20224855 = 30337283) B30337283
theorem B2047103 : Blo 1364501 2047103 := bstep (se 1 (by rfl) ⟨1535327, by rfl⟩ : syracuseStep 2047103 = 3070655) B3070655
theorem B1727983 : Blo 1364501 1727983 := bstep (se 1 (by rfl) ⟨1295987, by rfl⟩ : syracuseStep 1727983 = 2591975) B2591975
theorem B5185043 : Blo 1364501 5185043 := bstep (se 1 (by rfl) ⟨3888782, by rfl⟩ : syracuseStep 5185043 = 7777565) B7777565
theorem B3456553 : Blo 1364501 3456553 := bstep (se 2 (by rfl) ⟨1296207, by rfl⟩ : syracuseStep 3456553 = 2592415) B2592415
theorem B23658095 : Blo 1364501 23658095 := bstep (se 1 (by rfl) ⟨17743571, by rfl⟩ : syracuseStep 23658095 = 35487143) B35487143
theorem B16604939 : Blo 1364501 16604939 := bstep (se 1 (by rfl) ⟨12453704, by rfl⟩ : syracuseStep 16604939 = 24907409) B24907409
theorem B23969657 : Blo 1364501 23969657 := bstep (se 2 (by rfl) ⟨8988621, by rfl⟩ : syracuseStep 23969657 = 17977243) B17977243
theorem B2916425 : Blo 1364501 2916425 := bstep (se 2 (by rfl) ⟨1093659, by rfl⟩ : syracuseStep 2916425 = 2187319) B2187319
theorem B5185727 : Blo 1364501 5185727 := bstep (se 1 (by rfl) ⟨3889295, by rfl⟩ : syracuseStep 5185727 = 7778591) B7778591
theorem B3072239 : Blo 1364501 3072239 := bstep (se 1 (by rfl) ⟨2304179, by rfl⟩ : syracuseStep 3072239 = 4608359) B4608359
theorem B89858423 : Blo 1364501 89858423 := bstep (se 1 (by rfl) ⟨67393817, by rfl⟩ : syracuseStep 89858423 = 134787635) B134787635
theorem B3072383 : Blo 1364501 3072383 := bstep (se 1 (by rfl) ⟨2304287, by rfl⟩ : syracuseStep 3072383 = 4608575) B4608575
theorem B2048447 : Blo 1364501 2048447 := bstep (se 1 (by rfl) ⟨1536335, by rfl⟩ : syracuseStep 2048447 = 3072671) B3072671
theorem B5186045 : Blo 1364501 5186045 := bstep (se 3 (by rfl) ⟨972383, by rfl⟩ : syracuseStep 5186045 = 1944767) B1944767
theorem B2302843 : Blo 1364501 2302843 := bstep (se 1 (by rfl) ⟨1727132, by rfl⟩ : syracuseStep 2302843 = 3454265) B3454265
theorem B3457991 : Blo 1364501 3457991 := bstep (se 1 (by rfl) ⟨2593493, by rfl⟩ : syracuseStep 3457991 = 5186987) B5186987
theorem B63088253 : Blo 1364501 63088253 := bstep (se 3 (by rfl) ⟨11829047, by rfl⟩ : syracuseStep 63088253 = 23658095) B23658095
theorem B3073679 : Blo 1364501 3073679 := bstep (se 1 (by rfl) ⟨2305259, by rfl⟩ : syracuseStep 3073679 = 4610519) B4610519
theorem B3278519 : Blo 1364501 3278519 := bstep (se 1 (by rfl) ⟨2458889, by rfl⟩ : syracuseStep 3278519 = 4917779) B4917779
theorem B107865893 : Blo 1364501 107865893 := bstep (se 4 (by rfl) ⟨10112427, by rfl⟩ : syracuseStep 107865893 = 20224855) B20224855
theorem B2303977 : Blo 1364501 2303977 := bstep (se 2 (by rfl) ⟨863991, by rfl⟩ : syracuseStep 2303977 = 1727983) B1727983
theorem B11069959 : Blo 1364501 11069959 := bstep (se 1 (by rfl) ⟨8302469, by rfl⟩ : syracuseStep 11069959 = 16604939) B16604939
theorem B4377341 : Blo 1364501 4377341 := bstep (se 3 (by rfl) ⟨820751, by rfl⟩ : syracuseStep 4377341 = 1641503) B1641503
theorem B4607225 : Blo 1364501 4607225 := bstep (se 2 (by rfl) ⟨1727709, by rfl⟩ : syracuseStep 4607225 = 3455419) B3455419
theorem B23653661 : Blo 1364501 23653661 := bstep (se 3 (by rfl) ⟨4435061, by rfl⟩ : syracuseStep 23653661 = 8870123) B8870123
theorem B4607387 : Blo 1364501 4607387 := bstep (se 1 (by rfl) ⟨3455540, by rfl⟩ : syracuseStep 4607387 = 6911081) B6911081
theorem B3280295 : Blo 1364501 3280295 := bstep (se 1 (by rfl) ⟨2460221, by rfl⟩ : syracuseStep 3280295 = 4920443) B4920443
theorem B1535719 : Blo 1364501 1535719 := bstep (se 1 (by rfl) ⟨1151789, by rfl⟩ : syracuseStep 1535719 = 2303579) B2303579
theorem B14765827 : Blo 1364501 14765827 := bstep (se 1 (by rfl) ⟨11074370, by rfl⟩ : syracuseStep 14765827 = 22148741) B22148741
theorem B5181853 : Blo 1364501 5181853 := bstep (se 3 (by rfl) ⟨971597, by rfl⟩ : syracuseStep 5181853 = 1943195) B1943195
theorem B8745403 : Blo 1364501 8745403 := bstep (se 1 (by rfl) ⟨6559052, by rfl⟩ : syracuseStep 8745403 = 13118105) B13118105
theorem B1364527 : Blo 1364501 1364527 := bstep (se 1 (by rfl) ⟨1023395, by rfl⟩ : syracuseStep 1364527 = 2046791) B2046791
theorem B7779023 : Blo 1364501 7779023 := bstep (se 1 (by rfl) ⟨5834267, by rfl⟩ : syracuseStep 7779023 = 11668535) B11668535
theorem B4608737 : Blo 1364501 4608737 := bstep (se 2 (by rfl) ⟨1728276, by rfl⟩ : syracuseStep 4608737 = 3456553) B3456553
theorem B12464875 : Blo 1364501 12464875 := bstep (se 1 (by rfl) ⟨9348656, by rfl⟩ : syracuseStep 12464875 = 18697313) B18697313
theorem B1364735 : Blo 1364501 1364735 := bstep (se 1 (by rfl) ⟨1023551, by rfl⟩ : syracuseStep 1364735 = 2047103) B2047103
theorem B1536799 : Blo 1364501 1536799 := bstep (se 1 (by rfl) ⟨1152599, by rfl⟩ : syracuseStep 1536799 = 2305199) B2305199
theorem B3281833 : Blo 1364501 3281833 := bstep (se 2 (by rfl) ⟨1230687, by rfl⟩ : syracuseStep 3281833 = 2461375) B2461375
theorem B1537051 : Blo 1364501 1537051 := bstep (se 1 (by rfl) ⟨1152788, by rfl⟩ : syracuseStep 1537051 = 2305577) B2305577
theorem B3454073 : Blo 1364501 3454073 := bstep (se 2 (by rfl) ⟨1295277, by rfl⟩ : syracuseStep 3454073 = 2590555) B2590555
theorem B4920545 : Blo 1364501 4920545 := bstep (se 2 (by rfl) ⟨1845204, by rfl⟩ : syracuseStep 4920545 = 3690409) B3690409
theorem B15979771 : Blo 1364501 15979771 := bstep (se 1 (by rfl) ⟨11984828, by rfl⟩ : syracuseStep 15979771 = 23969657) B23969657
theorem B3454447 : Blo 1364501 3454447 := bstep (se 1 (by rfl) ⟨2590835, by rfl⟩ : syracuseStep 3454447 = 5181671) B5181671
theorem B1365711 : Blo 1364501 1365711 := bstep (se 1 (by rfl) ⟨1024283, by rfl⟩ : syracuseStep 1365711 = 2048567) B2048567
theorem B3454751 : Blo 1364501 3454751 := bstep (se 1 (by rfl) ⟨2591063, by rfl⟩ : syracuseStep 3454751 = 5182127) B5182127
theorem B1365951 : Blo 1364501 1365951 := bstep (se 1 (by rfl) ⟨1024463, by rfl⟩ : syracuseStep 1365951 = 2048927) B2048927
theorem B15562691 : Blo 1364501 15562691 := bstep (se 1 (by rfl) ⟨11672018, by rfl⟩ : syracuseStep 15562691 = 23344037) B23344037
theorem B1365983 : Blo 1364501 1365983 := bstep (se 1 (by rfl) ⟨1024487, by rfl⟩ : syracuseStep 1365983 = 2048975) B2048975
theorem B12449771 : Blo 1364501 12449771 := bstep (se 1 (by rfl) ⟨9337328, by rfl⟩ : syracuseStep 12449771 = 18674657) B18674657
theorem B3889147 : Blo 1364501 3889147 := bstep (se 1 (by rfl) ⟨2916860, by rfl⟩ : syracuseStep 3889147 = 5833721) B5833721
theorem B1366063 : Blo 1364501 1366063 := bstep (se 1 (by rfl) ⟨1024547, by rfl⟩ : syracuseStep 1366063 = 2049095) B2049095
theorem B5183615 : Blo 1364501 5183615 := bstep (se 1 (by rfl) ⟨3887711, by rfl⟩ : syracuseStep 5183615 = 7775423) B7775423
theorem B1366183 : Blo 1364501 1366183 := bstep (se 1 (by rfl) ⟨1024637, by rfl⟩ : syracuseStep 1366183 = 2049275) B2049275
theorem B1366223 : Blo 1364501 1366223 := bstep (se 1 (by rfl) ⟨1024667, by rfl⟩ : syracuseStep 1366223 = 2049335) B2049335
theorem B15546653 : Blo 1364501 15546653 := bstep (se 3 (by rfl) ⟨2914997, by rfl⟩ : syracuseStep 15546653 = 5829995) B5829995
theorem B3455723 : Blo 1364501 3455723 := bstep (se 1 (by rfl) ⟨2591792, by rfl⟩ : syracuseStep 3455723 = 5183585) B5183585
theorem B7478011 : Blo 1364501 7478011 := bstep (se 1 (by rfl) ⟨5608508, by rfl⟩ : syracuseStep 7478011 = 11217017) B11217017
theorem B50477903 : Blo 1364501 50477903 := bstep (se 1 (by rfl) ⟨37858427, by rfl⟩ : syracuseStep 50477903 = 75716855) B75716855
theorem B3070817 : Blo 1364501 3070817 := bstep (se 2 (by rfl) ⟨1151556, by rfl⟩ : syracuseStep 3070817 = 2303113) B2303113
theorem B126081917 : Blo 1364501 126081917 := bstep (se 3 (by rfl) ⟨23640359, by rfl⟩ : syracuseStep 126081917 = 47280719) B47280719
theorem B7486447 : Blo 1364501 7486447 := bstep (se 1 (by rfl) ⟨5614835, by rfl⟩ : syracuseStep 7486447 = 11229671) B11229671
theorem B3890207 : Blo 1364501 3890207 := bstep (se 1 (by rfl) ⟨2917655, by rfl⟩ : syracuseStep 3890207 = 5835311) B5835311
theorem B3456047 : Blo 1364501 3456047 := bstep (se 1 (by rfl) ⟨2592035, by rfl⟩ : syracuseStep 3456047 = 5184071) B5184071
theorem B4611383 : Blo 1364501 4611383 := bstep (se 1 (by rfl) ⟨3458537, by rfl⟩ : syracuseStep 4611383 = 6917075) B6917075
theorem B2047529 : Blo 1364501 2047529 := bstep (se 2 (by rfl) ⟨767823, by rfl⟩ : syracuseStep 2047529 = 1535647) B1535647
theorem B1728155 : Blo 1364501 1728155 := bstep (se 1 (by rfl) ⟨1296116, by rfl⟩ : syracuseStep 1728155 = 2592233) B2592233
theorem B3071663 : Blo 1364501 3071663 := bstep (se 1 (by rfl) ⟨2303747, by rfl⟩ : syracuseStep 3071663 = 4607495) B4607495
theorem B3456695 : Blo 1364501 3456695 := bstep (se 1 (by rfl) ⟨2592521, by rfl⟩ : syracuseStep 3456695 = 5185043) B5185043
theorem B4611815 : Blo 1364501 4611815 := bstep (se 1 (by rfl) ⟨3458861, by rfl⟩ : syracuseStep 4611815 = 6917723) B6917723
theorem B3457151 : Blo 1364501 3457151 := bstep (se 1 (by rfl) ⟨2592863, by rfl⟩ : syracuseStep 3457151 = 5185727) B5185727
theorem B2048159 : Blo 1364501 2048159 := bstep (se 1 (by rfl) ⟨1536119, by rfl⟩ : syracuseStep 2048159 = 3072239) B3072239
theorem B2048255 : Blo 1364501 2048255 := bstep (se 1 (by rfl) ⟨1536191, by rfl⟩ : syracuseStep 2048255 = 3072383) B3072383
theorem B3457363 : Blo 1364501 3457363 := bstep (se 1 (by rfl) ⟨2593022, by rfl⟩ : syracuseStep 3457363 = 5186045) B5186045
theorem B5186015 : Blo 1364501 5186015 := bstep (se 1 (by rfl) ⟨3889511, by rfl⟩ : syracuseStep 5186015 = 7779023) B7779023
theorem B3072491 : Blo 1364501 3072491 := bstep (se 1 (by rfl) ⟨2304368, by rfl⟩ : syracuseStep 3072491 = 4608737) B4608737
theorem B2302715 : Blo 1364501 2302715 := bstep (se 1 (by rfl) ⟨1727036, by rfl⟩ : syracuseStep 2302715 = 3454073) B3454073
theorem B2049065 : Blo 1364501 2049065 := bstep (se 2 (by rfl) ⟨768399, by rfl⟩ : syracuseStep 2049065 = 1536799) B1536799
theorem B42058835 : Blo 1364501 42058835 := bstep (se 1 (by rfl) ⟨31544126, by rfl⟩ : syracuseStep 42058835 = 63088253) B63088253
theorem B2049119 : Blo 1364501 2049119 := bstep (se 1 (by rfl) ⟨1536839, by rfl⟩ : syracuseStep 2049119 = 3073679) B3073679
theorem B2303167 : Blo 1364501 2303167 := bstep (se 1 (by rfl) ⟨1727375, by rfl⟩ : syracuseStep 2303167 = 3454751) B3454751
theorem B71910595 : Blo 1364501 71910595 := bstep (se 1 (by rfl) ⟨53932946, by rfl⟩ : syracuseStep 71910595 = 107865893) B107865893
theorem B4375777 : Blo 1364501 4375777 := bstep (se 2 (by rfl) ⟨1640916, by rfl⟩ : syracuseStep 4375777 = 3281833) B3281833
theorem B8299847 : Blo 1364501 8299847 := bstep (se 1 (by rfl) ⟨6224885, by rfl⟩ : syracuseStep 8299847 = 12449771) B12449771
theorem B2049401 : Blo 1364501 2049401 := bstep (se 2 (by rfl) ⟨768525, by rfl⟩ : syracuseStep 2049401 = 1537051) B1537051
theorem B10364435 : Blo 1364501 10364435 := bstep (se 1 (by rfl) ⟨7773326, by rfl⟩ : syracuseStep 10364435 = 15546653) B15546653
theorem B2303815 : Blo 1364501 2303815 := bstep (se 1 (by rfl) ⟨1727861, by rfl⟩ : syracuseStep 2303815 = 3455723) B3455723
theorem B4605929 : Blo 1364501 4605929 := bstep (se 2 (by rfl) ⟨1727223, by rfl⟩ : syracuseStep 4605929 = 3454447) B3454447
theorem B2304031 : Blo 1364501 2304031 := bstep (se 1 (by rfl) ⟨1728023, by rfl⟩ : syracuseStep 2304031 = 3456047) B3456047
theorem B3074255 : Blo 1364501 3074255 := bstep (se 1 (by rfl) ⟨2305691, by rfl⟩ : syracuseStep 3074255 = 4611383) B4611383
theorem B19687769 : Blo 1364501 19687769 := bstep (se 2 (by rfl) ⟨7382913, by rfl⟩ : syracuseStep 19687769 = 14765827) B14765827
theorem B2304463 : Blo 1364501 2304463 := bstep (se 1 (by rfl) ⟨1728347, by rfl⟩ : syracuseStep 2304463 = 3456695) B3456695
theorem B3074543 : Blo 1364501 3074543 := bstep (se 1 (by rfl) ⟨2305907, by rfl⟩ : syracuseStep 3074543 = 4611815) B4611815
theorem B7777133 : Blo 1364501 7777133 := bstep (se 3 (by rfl) ⟨1458212, by rfl⟩ : syracuseStep 7777133 = 2916425) B2916425
theorem B6909137 : Blo 1364501 6909137 := bstep (se 2 (by rfl) ⟨2590926, by rfl⟩ : syracuseStep 6909137 = 5181853) B5181853
theorem B11660537 : Blo 1364501 11660537 := bstep (se 2 (by rfl) ⟨4372701, by rfl⟩ : syracuseStep 11660537 = 8745403) B8745403
theorem B2305327 : Blo 1364501 2305327 := bstep (se 1 (by rfl) ⟨1728995, by rfl⟩ : syracuseStep 2305327 = 3457991) B3457991
theorem B10375127 : Blo 1364501 10375127 := bstep (se 1 (by rfl) ⟨7781345, by rfl⟩ : syracuseStep 10375127 = 15562691) B15562691
theorem B39882725 : Blo 1364501 39882725 := bstep (se 4 (by rfl) ⟨3739005, by rfl⟩ : syracuseStep 39882725 = 7478011) B7478011
theorem B85225445 : Blo 1364501 85225445 := bstep (se 4 (by rfl) ⟨7989885, by rfl⟩ : syracuseStep 85225445 = 15979771) B15979771
theorem B9981929 : Blo 1364501 9981929 := bstep (se 2 (by rfl) ⟨3743223, by rfl⟩ : syracuseStep 9981929 = 7486447) B7486447
theorem B4608413 : Blo 1364501 4608413 := bstep (se 3 (by rfl) ⟨864077, by rfl⟩ : syracuseStep 4608413 = 1728155) B1728155
theorem B84054611 : Blo 1364501 84054611 := bstep (se 1 (by rfl) ⟨63040958, by rfl⟩ : syracuseStep 84054611 = 126081917) B126081917
theorem B2593471 : Blo 1364501 2593471 := bstep (se 1 (by rfl) ⟨1945103, by rfl⟩ : syracuseStep 2593471 = 3890207) B3890207
theorem B1365019 : Blo 1364501 1365019 := bstep (se 1 (by rfl) ⟨1023764, by rfl⟩ : syracuseStep 1365019 = 2047529) B2047529
theorem B1365631 : Blo 1364501 1365631 := bstep (se 1 (by rfl) ⟨1024223, by rfl⟩ : syracuseStep 1365631 = 2048447) B2048447
theorem B13121453 : Blo 1364501 13121453 := bstep (se 3 (by rfl) ⟨2460272, by rfl⟩ : syracuseStep 13121453 = 4920545) B4920545
theorem B14759945 : Blo 1364501 14759945 := bstep (se 2 (by rfl) ⟨5534979, by rfl⟩ : syracuseStep 14759945 = 11069959) B11069959
theorem B63076429 : Blo 1364501 63076429 := bstep (se 3 (by rfl) ⟨11826830, by rfl⟩ : syracuseStep 63076429 = 23653661) B23653661
theorem B16619833 : Blo 1364501 16619833 := bstep (se 2 (by rfl) ⟨6232437, by rfl⟩ : syracuseStep 16619833 = 12464875) B12464875
theorem B239622461 : Blo 1364501 239622461 := bstep (se 3 (by rfl) ⟨44929211, by rfl⟩ : syracuseStep 239622461 = 89858423) B89858423
theorem B8747453 : Blo 1364501 8747453 := bstep (se 3 (by rfl) ⟨1640147, by rfl⟩ : syracuseStep 8747453 = 3280295) B3280295
theorem B2185679 : Blo 1364501 2185679 := bstep (se 1 (by rfl) ⟨1639259, by rfl⟩ : syracuseStep 2185679 = 3278519) B3278519
theorem B3070457 : Blo 1364501 3070457 := bstep (se 2 (by rfl) ⟨1151421, by rfl⟩ : syracuseStep 3070457 = 2302843) B2302843
theorem B3455743 : Blo 1364501 3455743 := bstep (se 1 (by rfl) ⟨2591807, by rfl⟩ : syracuseStep 3455743 = 5183615) B5183615
theorem B33651935 : Blo 1364501 33651935 := bstep (se 1 (by rfl) ⟨25238951, by rfl⟩ : syracuseStep 33651935 = 50477903) B50477903
theorem B2047211 : Blo 1364501 2047211 := bstep (se 1 (by rfl) ⟨1535408, by rfl⟩ : syracuseStep 2047211 = 3070817) B3070817
theorem B11672909 : Blo 1364501 11672909 := bstep (se 3 (by rfl) ⟨2188670, by rfl⟩ : syracuseStep 11672909 = 4377341) B4377341
theorem B3071483 : Blo 1364501 3071483 := bstep (se 1 (by rfl) ⟨2303612, by rfl⟩ : syracuseStep 3071483 = 4607225) B4607225
theorem B3071591 : Blo 1364501 3071591 := bstep (se 1 (by rfl) ⟨2303693, by rfl⟩ : syracuseStep 3071591 = 4607387) B4607387
theorem B2047625 : Blo 1364501 2047625 := bstep (se 2 (by rfl) ⟨767859, by rfl⟩ : syracuseStep 2047625 = 1535719) B1535719
theorem B2047775 : Blo 1364501 2047775 := bstep (se 1 (by rfl) ⟨1535831, by rfl⟩ : syracuseStep 2047775 = 3071663) B3071663
theorem B3071969 : Blo 1364501 3071969 := bstep (se 2 (by rfl) ⟨1151988, by rfl⟩ : syracuseStep 3071969 = 2303977) B2303977
theorem B5185529 : Blo 1364501 5185529 := bstep (se 2 (by rfl) ⟨1944573, by rfl⟩ : syracuseStep 5185529 = 3889147) B3889147
theorem B3072041 : Blo 1364501 3072041 := bstep (se 2 (by rfl) ⟨1152015, by rfl⟩ : syracuseStep 3072041 = 2304031) B2304031
theorem B3072275 : Blo 1364501 3072275 := bstep (se 1 (by rfl) ⟨2304206, by rfl⟩ : syracuseStep 3072275 = 4608413) B4608413
theorem B3457343 : Blo 1364501 3457343 := bstep (se 1 (by rfl) ⟨2593007, by rfl⟩ : syracuseStep 3457343 = 5186015) B5186015
theorem B2048327 : Blo 1364501 2048327 := bstep (se 1 (by rfl) ⟨1536245, by rfl⟩ : syracuseStep 2048327 = 3072491) B3072491
theorem B22159777 : Blo 1364501 22159777 := bstep (se 2 (by rfl) ⟨8309916, by rfl⟩ : syracuseStep 22159777 = 16619833) B16619833
theorem B3072617 : Blo 1364501 3072617 := bstep (se 2 (by rfl) ⟨1152231, by rfl⟩ : syracuseStep 3072617 = 2304463) B2304463
theorem B3457961 : Blo 1364501 3457961 := bstep (se 2 (by rfl) ⟨1296735, by rfl⟩ : syracuseStep 3457961 = 2593471) B2593471
theorem B9839963 : Blo 1364501 9839963 := bstep (se 1 (by rfl) ⟨7379972, by rfl⟩ : syracuseStep 9839963 = 14759945) B14759945
theorem B2049503 : Blo 1364501 2049503 := bstep (se 1 (by rfl) ⟨1537127, by rfl⟩ : syracuseStep 2049503 = 3074255) B3074255
theorem B13125179 : Blo 1364501 13125179 := bstep (se 1 (by rfl) ⟨9843884, by rfl⟩ : syracuseStep 13125179 = 19687769) B19687769
theorem B5834369 : Blo 1364501 5834369 := bstep (se 2 (by rfl) ⟨2187888, by rfl⟩ : syracuseStep 5834369 = 4375777) B4375777
theorem B2049695 : Blo 1364501 2049695 := bstep (se 1 (by rfl) ⟨1537271, by rfl⟩ : syracuseStep 2049695 = 3074543) B3074543
theorem B3073769 : Blo 1364501 3073769 := bstep (se 2 (by rfl) ⟨1152663, by rfl⟩ : syracuseStep 3073769 = 2305327) B2305327
theorem B4606091 : Blo 1364501 4606091 := bstep (se 1 (by rfl) ⟨3454568, by rfl⟩ : syracuseStep 4606091 = 6909137) B6909137
theorem B6916751 : Blo 1364501 6916751 := bstep (se 1 (by rfl) ⟨5187563, by rfl⟩ : syracuseStep 6916751 = 10375127) B10375127
theorem B6654619 : Blo 1364501 6654619 := bstep (se 1 (by rfl) ⟨4990964, by rfl⟩ : syracuseStep 6654619 = 9981929) B9981929
theorem B2304767 : Blo 1364501 2304767 := bstep (se 1 (by rfl) ⟨1728575, by rfl⟩ : syracuseStep 2304767 = 3457151) B3457151
theorem B84101905 : Blo 1364501 84101905 := bstep (se 2 (by rfl) ⟨31538214, by rfl⟩ : syracuseStep 84101905 = 63076429) B63076429
theorem B1535143 : Blo 1364501 1535143 := bstep (se 1 (by rfl) ⟨1151357, by rfl⟩ : syracuseStep 1535143 = 2302715) B2302715
theorem B5533231 : Blo 1364501 5533231 := bstep (se 1 (by rfl) ⟨4149923, by rfl⟩ : syracuseStep 5533231 = 8299847) B8299847
theorem B4607657 : Blo 1364501 4607657 := bstep (se 2 (by rfl) ⟨1727871, by rfl⟩ : syracuseStep 4607657 = 3455743) B3455743
theorem B6909623 : Blo 1364501 6909623 := bstep (se 1 (by rfl) ⟨5182217, by rfl⟩ : syracuseStep 6909623 = 10364435) B10364435
theorem B23326541 : Blo 1364501 23326541 := bstep (se 3 (by rfl) ⟨4373726, by rfl⟩ : syracuseStep 23326541 = 8747453) B8747453
theorem B159748307 : Blo 1364501 159748307 := bstep (se 1 (by rfl) ⟨119811230, by rfl⟩ : syracuseStep 159748307 = 239622461) B239622461
theorem B224145629 : Blo 1364501 224145629 := bstep (se 3 (by rfl) ⟨42027305, by rfl⟩ : syracuseStep 224145629 = 84054611) B84054611
theorem B22434623 : Blo 1364501 22434623 := bstep (se 1 (by rfl) ⟨16825967, by rfl⟩ : syracuseStep 22434623 = 33651935) B33651935
theorem B1364807 : Blo 1364501 1364807 := bstep (se 1 (by rfl) ⟨1023605, by rfl⟩ : syracuseStep 1364807 = 2047211) B2047211
theorem B1365083 : Blo 1364501 1365083 := bstep (se 1 (by rfl) ⟨1023812, by rfl⟩ : syracuseStep 1365083 = 2047625) B2047625
theorem B1365183 : Blo 1364501 1365183 := bstep (se 1 (by rfl) ⟨1023887, by rfl⟩ : syracuseStep 1365183 = 2047775) B2047775
theorem B26588483 : Blo 1364501 26588483 := bstep (se 1 (by rfl) ⟨19941362, by rfl⟩ : syracuseStep 26588483 = 39882725) B39882725
theorem B56816963 : Blo 1364501 56816963 := bstep (se 1 (by rfl) ⟨42612722, by rfl⟩ : syracuseStep 56816963 = 85225445) B85225445
theorem B1365439 : Blo 1364501 1365439 := bstep (se 1 (by rfl) ⟨1024079, by rfl⟩ : syracuseStep 1365439 = 2048159) B2048159
theorem B1365503 : Blo 1364501 1365503 := bstep (se 1 (by rfl) ⟨1024127, by rfl⟩ : syracuseStep 1365503 = 2048255) B2048255
theorem B4609817 : Blo 1364501 4609817 := bstep (se 2 (by rfl) ⟨1728681, by rfl⟩ : syracuseStep 4609817 = 3457363) B3457363
theorem B1366043 : Blo 1364501 1366043 := bstep (se 1 (by rfl) ⟨1024532, by rfl⟩ : syracuseStep 1366043 = 2049065) B2049065
theorem B28039223 : Blo 1364501 28039223 := bstep (se 1 (by rfl) ⟨21029417, by rfl⟩ : syracuseStep 28039223 = 42058835) B42058835
theorem B1366079 : Blo 1364501 1366079 := bstep (se 1 (by rfl) ⟨1024559, by rfl⟩ : syracuseStep 1366079 = 2049119) B2049119
theorem B1366267 : Blo 1364501 1366267 := bstep (se 1 (by rfl) ⟨1024700, by rfl⟩ : syracuseStep 1366267 = 2049401) B2049401
theorem B383523173 : Blo 1364501 383523173 := bstep (se 4 (by rfl) ⟨35955297, by rfl⟩ : syracuseStep 383523173 = 71910595) B71910595
theorem B8747635 : Blo 1364501 8747635 := bstep (se 1 (by rfl) ⟨6560726, by rfl⟩ : syracuseStep 8747635 = 13121453) B13121453
theorem B3070619 : Blo 1364501 3070619 := bstep (se 1 (by rfl) ⟨2302964, by rfl⟩ : syracuseStep 3070619 = 4605929) B4605929
theorem B3070889 : Blo 1364501 3070889 := bstep (se 2 (by rfl) ⟨1151583, by rfl⟩ : syracuseStep 3070889 = 2303167) B2303167
theorem B1457119 : Blo 1364501 1457119 := bstep (se 1 (by rfl) ⟨1092839, by rfl⟩ : syracuseStep 1457119 = 2185679) B2185679
theorem B2046971 : Blo 1364501 2046971 := bstep (se 1 (by rfl) ⟨1535228, by rfl⟩ : syracuseStep 2046971 = 3070457) B3070457
theorem B5184755 : Blo 1364501 5184755 := bstep (se 1 (by rfl) ⟨3888566, by rfl⟩ : syracuseStep 5184755 = 7777133) B7777133
theorem B7773691 : Blo 1364501 7773691 := bstep (se 1 (by rfl) ⟨5830268, by rfl⟩ : syracuseStep 7773691 = 11660537) B11660537
theorem B7781939 : Blo 1364501 7781939 := bstep (se 1 (by rfl) ⟨5836454, by rfl⟩ : syracuseStep 7781939 = 11672909) B11672909
theorem B2047655 : Blo 1364501 2047655 := bstep (se 1 (by rfl) ⟨1535741, by rfl⟩ : syracuseStep 2047655 = 3071483) B3071483
theorem B2047727 : Blo 1364501 2047727 := bstep (se 1 (by rfl) ⟨1535795, by rfl⟩ : syracuseStep 2047727 = 3071591) B3071591
theorem B3071753 : Blo 1364501 3071753 := bstep (se 2 (by rfl) ⟨1151907, by rfl⟩ : syracuseStep 3071753 = 2303815) B2303815
theorem B2047979 : Blo 1364501 2047979 := bstep (se 1 (by rfl) ⟨1535984, by rfl⟩ : syracuseStep 2047979 = 3071969) B3071969
theorem B3457019 : Blo 1364501 3457019 := bstep (se 1 (by rfl) ⟨2592764, by rfl⟩ : syracuseStep 3457019 = 5185529) B5185529
theorem B2048027 : Blo 1364501 2048027 := bstep (se 1 (by rfl) ⟨1536020, by rfl⟩ : syracuseStep 2048027 = 3072041) B3072041
theorem B149430419 : Blo 1364501 149430419 := bstep (se 1 (by rfl) ⟨112072814, by rfl⟩ : syracuseStep 149430419 = 224145629) B224145629
theorem B2048183 : Blo 1364501 2048183 := bstep (se 1 (by rfl) ⟨1536137, by rfl⟩ : syracuseStep 2048183 = 3072275) B3072275
theorem B2048411 : Blo 1364501 2048411 := bstep (se 1 (by rfl) ⟨1536308, by rfl⟩ : syracuseStep 2048411 = 3072617) B3072617
theorem B8750119 : Blo 1364501 8750119 := bstep (se 1 (by rfl) ⟨6562589, by rfl⟩ : syracuseStep 8750119 = 13125179) B13125179
theorem B2049179 : Blo 1364501 2049179 := bstep (se 1 (by rfl) ⟨1536884, by rfl⟩ : syracuseStep 2049179 = 3073769) B3073769
theorem B3073211 : Blo 1364501 3073211 := bstep (se 1 (by rfl) ⟨2304908, by rfl⟩ : syracuseStep 3073211 = 4609817) B4609817
theorem B255682115 : Blo 1364501 255682115 := bstep (se 1 (by rfl) ⟨191761586, by rfl⟩ : syracuseStep 255682115 = 383523173) B383523173
theorem B15558317 : Blo 1364501 15558317 := bstep (se 3 (by rfl) ⟨2917184, by rfl⟩ : syracuseStep 15558317 = 5834369) B5834369
theorem B10364921 : Blo 1364501 10364921 := bstep (se 2 (by rfl) ⟨3886845, by rfl⟩ : syracuseStep 10364921 = 7773691) B7773691
theorem B5187959 : Blo 1364501 5187959 := bstep (se 1 (by rfl) ⟨3890969, by rfl⟩ : syracuseStep 5187959 = 7781939) B7781939
theorem B4606415 : Blo 1364501 4606415 := bstep (se 1 (by rfl) ⟨3454811, by rfl⟩ : syracuseStep 4606415 = 6909623) B6909623
theorem B15551027 : Blo 1364501 15551027 := bstep (se 1 (by rfl) ⟨11663270, by rfl⟩ : syracuseStep 15551027 = 23326541) B23326541
theorem B2304679 : Blo 1364501 2304679 := bstep (se 1 (by rfl) ⟨1728509, by rfl⟩ : syracuseStep 2304679 = 3457019) B3457019
theorem B106498871 : Blo 1364501 106498871 := bstep (se 1 (by rfl) ⟨79874153, by rfl⟩ : syracuseStep 106498871 = 159748307) B159748307
theorem B74771261 : Blo 1364501 74771261 := bstep (se 3 (by rfl) ⟨14019611, by rfl⟩ : syracuseStep 74771261 = 28039223) B28039223
theorem B2304895 : Blo 1364501 2304895 := bstep (se 1 (by rfl) ⟨1728671, by rfl⟩ : syracuseStep 2304895 = 3457343) B3457343
theorem B2305307 : Blo 1364501 2305307 := bstep (se 1 (by rfl) ⟨1728980, by rfl⟩ : syracuseStep 2305307 = 3457961) B3457961
theorem B35491301 : Blo 1364501 35491301 := bstep (se 4 (by rfl) ⟨3327309, by rfl⟩ : syracuseStep 35491301 = 6654619) B6654619
theorem B112135873 : Blo 1364501 112135873 := bstep (se 2 (by rfl) ⟨42050952, by rfl⟩ : syracuseStep 112135873 = 84101905) B84101905
theorem B1536511 : Blo 1364501 1536511 := bstep (se 1 (by rfl) ⟨1152383, by rfl⟩ : syracuseStep 1536511 = 2304767) B2304767
theorem B1364647 : Blo 1364501 1364647 := bstep (se 1 (by rfl) ⟨1023485, by rfl⟩ : syracuseStep 1364647 = 2046971) B2046971
theorem B7377641 : Blo 1364501 7377641 := bstep (se 2 (by rfl) ⟨2766615, by rfl⟩ : syracuseStep 7377641 = 5533231) B5533231
theorem B1365103 : Blo 1364501 1365103 := bstep (se 1 (by rfl) ⟨1023827, by rfl⟩ : syracuseStep 1365103 = 2047655) B2047655
theorem B1365151 : Blo 1364501 1365151 := bstep (se 1 (by rfl) ⟨1023863, by rfl⟩ : syracuseStep 1365151 = 2047727) B2047727
theorem B7771301 : Blo 1364501 7771301 := bstep (se 4 (by rfl) ⟨728559, by rfl⟩ : syracuseStep 7771301 = 1457119) B1457119
theorem B1365319 : Blo 1364501 1365319 := bstep (se 1 (by rfl) ⟨1023989, by rfl⟩ : syracuseStep 1365319 = 2047979) B2047979
theorem B1365551 : Blo 1364501 1365551 := bstep (se 1 (by rfl) ⟨1024163, by rfl⟩ : syracuseStep 1365551 = 2048327) B2048327
theorem B14956415 : Blo 1364501 14956415 := bstep (se 1 (by rfl) ⟨11217311, by rfl⟩ : syracuseStep 14956415 = 22434623) B22434623
theorem B29546369 : Blo 1364501 29546369 := bstep (se 2 (by rfl) ⟨11079888, by rfl⟩ : syracuseStep 29546369 = 22159777) B22159777
theorem B11663513 : Blo 1364501 11663513 := bstep (se 2 (by rfl) ⟨4373817, by rfl⟩ : syracuseStep 11663513 = 8747635) B8747635
theorem B17725655 : Blo 1364501 17725655 := bstep (se 1 (by rfl) ⟨13294241, by rfl⟩ : syracuseStep 17725655 = 26588483) B26588483
theorem B37877975 : Blo 1364501 37877975 := bstep (se 1 (by rfl) ⟨28408481, by rfl⟩ : syracuseStep 37877975 = 56816963) B56816963
theorem B6559975 : Blo 1364501 6559975 := bstep (se 1 (by rfl) ⟨4919981, by rfl⟩ : syracuseStep 6559975 = 9839963) B9839963
theorem B1366335 : Blo 1364501 1366335 := bstep (se 1 (by rfl) ⟨1024751, by rfl⟩ : syracuseStep 1366335 = 2049503) B2049503
theorem B1366463 : Blo 1364501 1366463 := bstep (se 1 (by rfl) ⟨1024847, by rfl⟩ : syracuseStep 1366463 = 2049695) B2049695
theorem B3070727 : Blo 1364501 3070727 := bstep (se 1 (by rfl) ⟨2303045, by rfl⟩ : syracuseStep 3070727 = 4606091) B4606091
theorem B2046857 : Blo 1364501 2046857 := bstep (se 2 (by rfl) ⟨767571, by rfl⟩ : syracuseStep 2046857 = 1535143) B1535143
theorem B4611167 : Blo 1364501 4611167 := bstep (se 1 (by rfl) ⟨3458375, by rfl⟩ : syracuseStep 4611167 = 6916751) B6916751
theorem B2047079 : Blo 1364501 2047079 := bstep (se 1 (by rfl) ⟨1535309, by rfl⟩ : syracuseStep 2047079 = 3070619) B3070619
theorem B2047259 : Blo 1364501 2047259 := bstep (se 1 (by rfl) ⟨1535444, by rfl⟩ : syracuseStep 2047259 = 3070889) B3070889
theorem B3456503 : Blo 1364501 3456503 := bstep (se 1 (by rfl) ⟨2592377, by rfl⟩ : syracuseStep 3456503 = 5184755) B5184755
theorem B3071771 : Blo 1364501 3071771 := bstep (se 1 (by rfl) ⟨2303828, by rfl⟩ : syracuseStep 3071771 = 4607657) B4607657
theorem B2047835 : Blo 1364501 2047835 := bstep (se 1 (by rfl) ⟨1535876, by rfl⟩ : syracuseStep 2047835 = 3071753) B3071753
theorem B2048681 : Blo 1364501 2048681 := bstep (se 2 (by rfl) ⟨768255, by rfl⟩ : syracuseStep 2048681 = 1536511) B1536511
theorem B2048807 : Blo 1364501 2048807 := bstep (se 1 (by rfl) ⟨1536605, by rfl⟩ : syracuseStep 2048807 = 3073211) B3073211
theorem B3072905 : Blo 1364501 3072905 := bstep (se 2 (by rfl) ⟨1152339, by rfl⟩ : syracuseStep 3072905 = 2304679) B2304679
theorem B10372211 : Blo 1364501 10372211 := bstep (se 1 (by rfl) ⟨7779158, by rfl⟩ : syracuseStep 10372211 = 15558317) B15558317
theorem B3073193 : Blo 1364501 3073193 := bstep (se 2 (by rfl) ⟨1152447, by rfl⟩ : syracuseStep 3073193 = 2304895) B2304895
theorem B9970943 : Blo 1364501 9970943 := bstep (se 1 (by rfl) ⟨7478207, by rfl⟩ : syracuseStep 9970943 = 14956415) B14956415
theorem B11666825 : Blo 1364501 11666825 := bstep (se 2 (by rfl) ⟨4375059, by rfl⟩ : syracuseStep 11666825 = 8750119) B8750119
theorem B7775675 : Blo 1364501 7775675 := bstep (se 1 (by rfl) ⟨5831756, by rfl⟩ : syracuseStep 7775675 = 11663513) B11663513
theorem B3458639 : Blo 1364501 3458639 := bstep (se 1 (by rfl) ⟨2593979, by rfl⟩ : syracuseStep 3458639 = 5187959) B5187959
theorem B3074111 : Blo 1364501 3074111 := bstep (se 1 (by rfl) ⟨2305583, by rfl⟩ : syracuseStep 3074111 = 4611167) B4611167
theorem B149514497 : Blo 1364501 149514497 := bstep (se 2 (by rfl) ⟨56067936, by rfl⟩ : syracuseStep 149514497 = 112135873) B112135873
theorem B23660867 : Blo 1364501 23660867 := bstep (se 1 (by rfl) ⟨17745650, by rfl⟩ : syracuseStep 23660867 = 35491301) B35491301
theorem B2304335 : Blo 1364501 2304335 := bstep (se 1 (by rfl) ⟨1728251, by rfl⟩ : syracuseStep 2304335 = 3456503) B3456503
theorem B4918427 : Blo 1364501 4918427 := bstep (se 1 (by rfl) ⟨3688820, by rfl⟩ : syracuseStep 4918427 = 7377641) B7377641
theorem B5180867 : Blo 1364501 5180867 := bstep (se 1 (by rfl) ⟨3885650, by rfl⟩ : syracuseStep 5180867 = 7771301) B7771301
theorem B170454743 : Blo 1364501 170454743 := bstep (se 1 (by rfl) ⟨127841057, by rfl⟩ : syracuseStep 170454743 = 255682115) B255682115
theorem B19697579 : Blo 1364501 19697579 := bstep (se 1 (by rfl) ⟨14773184, by rfl⟩ : syracuseStep 19697579 = 29546369) B29546369
theorem B6909947 : Blo 1364501 6909947 := bstep (se 1 (by rfl) ⟨5182460, by rfl⟩ : syracuseStep 6909947 = 10364921) B10364921
theorem B11817103 : Blo 1364501 11817103 := bstep (se 1 (by rfl) ⟨8862827, by rfl⟩ : syracuseStep 11817103 = 17725655) B17725655
theorem B25251983 : Blo 1364501 25251983 := bstep (se 1 (by rfl) ⟨18938987, by rfl⟩ : syracuseStep 25251983 = 37877975) B37877975
theorem B10367351 : Blo 1364501 10367351 := bstep (se 1 (by rfl) ⟨7775513, by rfl⟩ : syracuseStep 10367351 = 15551027) B15551027
theorem B1364571 : Blo 1364501 1364571 := bstep (se 1 (by rfl) ⟨1023428, by rfl⟩ : syracuseStep 1364571 = 2046857) B2046857
theorem B1364719 : Blo 1364501 1364719 := bstep (se 1 (by rfl) ⟨1023539, by rfl⟩ : syracuseStep 1364719 = 2047079) B2047079
theorem B1364839 : Blo 1364501 1364839 := bstep (se 1 (by rfl) ⟨1023629, by rfl⟩ : syracuseStep 1364839 = 2047259) B2047259
theorem B1536871 : Blo 1364501 1536871 := bstep (se 1 (by rfl) ⟨1152653, by rfl⟩ : syracuseStep 1536871 = 2305307) B2305307
theorem B1365223 : Blo 1364501 1365223 := bstep (se 1 (by rfl) ⟨1023917, by rfl⟩ : syracuseStep 1365223 = 2047835) B2047835
theorem B1365351 : Blo 1364501 1365351 := bstep (se 1 (by rfl) ⟨1024013, by rfl⟩ : syracuseStep 1365351 = 2048027) B2048027
theorem B99620279 : Blo 1364501 99620279 := bstep (se 1 (by rfl) ⟨74715209, by rfl⟩ : syracuseStep 99620279 = 149430419) B149430419
theorem B1365455 : Blo 1364501 1365455 := bstep (se 1 (by rfl) ⟨1024091, by rfl⟩ : syracuseStep 1365455 = 2048183) B2048183
theorem B1365607 : Blo 1364501 1365607 := bstep (se 1 (by rfl) ⟨1024205, by rfl⟩ : syracuseStep 1365607 = 2048411) B2048411
theorem B8746633 : Blo 1364501 8746633 := bstep (se 2 (by rfl) ⟨3279987, by rfl⟩ : syracuseStep 8746633 = 6559975) B6559975
theorem B1366119 : Blo 1364501 1366119 := bstep (se 1 (by rfl) ⟨1024589, by rfl⟩ : syracuseStep 1366119 = 2049179) B2049179
theorem B3070943 : Blo 1364501 3070943 := bstep (se 1 (by rfl) ⟨2303207, by rfl⟩ : syracuseStep 3070943 = 4606415) B4606415
theorem B2047151 : Blo 1364501 2047151 := bstep (se 1 (by rfl) ⟨1535363, by rfl⟩ : syracuseStep 2047151 = 3070727) B3070727
theorem B70999247 : Blo 1364501 70999247 := bstep (se 1 (by rfl) ⟨53249435, by rfl⟩ : syracuseStep 70999247 = 106498871) B106498871
theorem B49847507 : Blo 1364501 49847507 := bstep (se 1 (by rfl) ⟨37385630, by rfl⟩ : syracuseStep 49847507 = 74771261) B74771261
theorem B2047847 : Blo 1364501 2047847 := bstep (se 1 (by rfl) ⟨1535885, by rfl⟩ : syracuseStep 2047847 = 3071771) B3071771
theorem B16834655 : Blo 1364501 16834655 := bstep (se 1 (by rfl) ⟨12625991, by rfl⟩ : syracuseStep 16834655 = 25251983) B25251983
theorem B2048603 : Blo 1364501 2048603 := bstep (se 1 (by rfl) ⟨1536452, by rfl⟩ : syracuseStep 2048603 = 3072905) B3072905
theorem B6914807 : Blo 1364501 6914807 := bstep (se 1 (by rfl) ⟨5186105, by rfl⟩ : syracuseStep 6914807 = 10372211) B10372211
theorem B2048795 : Blo 1364501 2048795 := bstep (se 1 (by rfl) ⟨1536596, by rfl⟩ : syracuseStep 2048795 = 3073193) B3073193
theorem B63095645 : Blo 1364501 63095645 := bstep (se 3 (by rfl) ⟨11830433, by rfl⟩ : syracuseStep 63095645 = 23660867) B23660867
theorem B66413519 : Blo 1364501 66413519 := bstep (se 1 (by rfl) ⟨49810139, by rfl⟩ : syracuseStep 66413519 = 99620279) B99620279
theorem B2049161 : Blo 1364501 2049161 := bstep (se 2 (by rfl) ⟨768435, by rfl⟩ : syracuseStep 2049161 = 1536871) B1536871
theorem B2049407 : Blo 1364501 2049407 := bstep (se 1 (by rfl) ⟨1537055, by rfl⟩ : syracuseStep 2049407 = 3074111) B3074111
theorem B3278951 : Blo 1364501 3278951 := bstep (se 1 (by rfl) ⟨2459213, by rfl⟩ : syracuseStep 3278951 = 4918427) B4918427
theorem B4606631 : Blo 1364501 4606631 := bstep (se 1 (by rfl) ⟨3454973, by rfl⟩ : syracuseStep 4606631 = 6909947) B6909947
theorem B15756137 : Blo 1364501 15756137 := bstep (se 2 (by rfl) ⟨5908551, by rfl⟩ : syracuseStep 15756137 = 11817103) B11817103
theorem B7777883 : Blo 1364501 7777883 := bstep (se 1 (by rfl) ⟨5833412, by rfl⟩ : syracuseStep 7777883 = 11666825) B11666825
theorem B2305759 : Blo 1364501 2305759 := bstep (se 1 (by rfl) ⟨1729319, by rfl⟩ : syracuseStep 2305759 = 3458639) B3458639
theorem B99676331 : Blo 1364501 99676331 := bstep (se 1 (by rfl) ⟨74757248, by rfl⟩ : syracuseStep 99676331 = 149514497) B149514497
theorem B1536223 : Blo 1364501 1536223 := bstep (se 1 (by rfl) ⟨1152167, by rfl⟩ : syracuseStep 1536223 = 2304335) B2304335
theorem B1364767 : Blo 1364501 1364767 := bstep (se 1 (by rfl) ⟨1023575, by rfl⟩ : syracuseStep 1364767 = 2047151) B2047151
theorem B33231671 : Blo 1364501 33231671 := bstep (se 1 (by rfl) ⟨24923753, by rfl⟩ : syracuseStep 33231671 = 49847507) B49847507
theorem B11662177 : Blo 1364501 11662177 := bstep (se 2 (by rfl) ⟨4373316, by rfl⟩ : syracuseStep 11662177 = 8746633) B8746633
theorem B3453911 : Blo 1364501 3453911 := bstep (se 1 (by rfl) ⟨2590433, by rfl⟩ : syracuseStep 3453911 = 5180867) B5180867
theorem B113636495 : Blo 1364501 113636495 := bstep (se 1 (by rfl) ⟨85227371, by rfl⟩ : syracuseStep 113636495 = 170454743) B170454743
theorem B1365231 : Blo 1364501 1365231 := bstep (se 1 (by rfl) ⟨1023923, by rfl⟩ : syracuseStep 1365231 = 2047847) B2047847
theorem B6911567 : Blo 1364501 6911567 := bstep (se 1 (by rfl) ⟨5183675, by rfl⟩ : syracuseStep 6911567 = 10367351) B10367351
theorem B1365787 : Blo 1364501 1365787 := bstep (se 1 (by rfl) ⟨1024340, by rfl⟩ : syracuseStep 1365787 = 2048681) B2048681
theorem B1365871 : Blo 1364501 1365871 := bstep (se 1 (by rfl) ⟨1024403, by rfl⟩ : syracuseStep 1365871 = 2048807) B2048807
theorem B26589181 : Blo 1364501 26589181 := bstep (se 3 (by rfl) ⟨4985471, by rfl⟩ : syracuseStep 26589181 = 9970943) B9970943
theorem B5183783 : Blo 1364501 5183783 := bstep (se 1 (by rfl) ⟨3887837, by rfl⟩ : syracuseStep 5183783 = 7775675) B7775675
theorem B2047295 : Blo 1364501 2047295 := bstep (se 1 (by rfl) ⟨1535471, by rfl⟩ : syracuseStep 2047295 = 3070943) B3070943
theorem B47332831 : Blo 1364501 47332831 := bstep (se 1 (by rfl) ⟨35499623, by rfl⟩ : syracuseStep 47332831 = 70999247) B70999247
theorem B13131719 : Blo 1364501 13131719 := bstep (se 1 (by rfl) ⟨9848789, by rfl⟩ : syracuseStep 13131719 = 19697579) B19697579
theorem B44892413 : Blo 1364501 44892413 := bstep (se 3 (by rfl) ⟨8417327, by rfl⟩ : syracuseStep 44892413 = 16834655) B16834655
theorem B2048297 : Blo 1364501 2048297 := bstep (se 2 (by rfl) ⟨768111, by rfl⟩ : syracuseStep 2048297 = 1536223) B1536223
theorem B2302607 : Blo 1364501 2302607 := bstep (se 1 (by rfl) ⟨1726955, by rfl⟩ : syracuseStep 2302607 = 3453911) B3453911
theorem B15549569 : Blo 1364501 15549569 := bstep (se 2 (by rfl) ⟨5831088, by rfl⟩ : syracuseStep 15549569 = 11662177) B11662177
theorem B10504091 : Blo 1364501 10504091 := bstep (se 1 (by rfl) ⟨7878068, by rfl⟩ : syracuseStep 10504091 = 15756137) B15756137
theorem B3074345 : Blo 1364501 3074345 := bstep (se 2 (by rfl) ⟨1152879, by rfl⟩ : syracuseStep 3074345 = 2305759) B2305759
theorem B22154447 : Blo 1364501 22154447 := bstep (se 1 (by rfl) ⟨16615835, by rfl⟩ : syracuseStep 22154447 = 33231671) B33231671
theorem B4607711 : Blo 1364501 4607711 := bstep (se 1 (by rfl) ⟨3455783, by rfl⟩ : syracuseStep 4607711 = 6911567) B6911567
theorem B1364863 : Blo 1364501 1364863 := bstep (se 1 (by rfl) ⟨1023647, by rfl⟩ : syracuseStep 1364863 = 2047295) B2047295
theorem B8754479 : Blo 1364501 8754479 := bstep (se 1 (by rfl) ⟨6565859, by rfl⟩ : syracuseStep 8754479 = 13131719) B13131719
theorem B35452241 : Blo 1364501 35452241 := bstep (se 2 (by rfl) ⟨13294590, by rfl⟩ : syracuseStep 35452241 = 26589181) B26589181
theorem B66450887 : Blo 1364501 66450887 := bstep (se 1 (by rfl) ⟨49838165, by rfl⟩ : syracuseStep 66450887 = 99676331) B99676331
theorem B1365735 : Blo 1364501 1365735 := bstep (se 1 (by rfl) ⟨1024301, by rfl⟩ : syracuseStep 1365735 = 2048603) B2048603
theorem B4609871 : Blo 1364501 4609871 := bstep (se 1 (by rfl) ⟨3457403, by rfl⟩ : syracuseStep 4609871 = 6914807) B6914807
theorem B1365863 : Blo 1364501 1365863 := bstep (se 1 (by rfl) ⟨1024397, by rfl⟩ : syracuseStep 1365863 = 2048795) B2048795
theorem B44275679 : Blo 1364501 44275679 := bstep (se 1 (by rfl) ⟨33206759, by rfl⟩ : syracuseStep 44275679 = 66413519) B66413519
theorem B1366107 : Blo 1364501 1366107 := bstep (se 1 (by rfl) ⟨1024580, by rfl⟩ : syracuseStep 1366107 = 2049161) B2049161
theorem B75757663 : Blo 1364501 75757663 := bstep (se 1 (by rfl) ⟨56818247, by rfl⟩ : syracuseStep 75757663 = 113636495) B113636495
theorem B1366271 : Blo 1364501 1366271 := bstep (se 1 (by rfl) ⟨1024703, by rfl⟩ : syracuseStep 1366271 = 2049407) B2049407
theorem B2185967 : Blo 1364501 2185967 := bstep (se 1 (by rfl) ⟨1639475, by rfl⟩ : syracuseStep 2185967 = 3278951) B3278951
theorem B3455855 : Blo 1364501 3455855 := bstep (se 1 (by rfl) ⟨2591891, by rfl⟩ : syracuseStep 3455855 = 5183783) B5183783
theorem B3071087 : Blo 1364501 3071087 := bstep (se 1 (by rfl) ⟨2303315, by rfl⟩ : syracuseStep 3071087 = 4606631) B4606631
theorem B63110441 : Blo 1364501 63110441 := bstep (se 2 (by rfl) ⟨23666415, by rfl⟩ : syracuseStep 63110441 = 47332831) B47332831
theorem B168255053 : Blo 1364501 168255053 := bstep (se 3 (by rfl) ⟨31547822, by rfl⟩ : syracuseStep 168255053 = 63095645) B63095645
theorem B5185255 : Blo 1364501 5185255 := bstep (se 1 (by rfl) ⟨3888941, by rfl⟩ : syracuseStep 5185255 = 7777883) B7777883
theorem B23634827 : Blo 1364501 23634827 := bstep (se 1 (by rfl) ⟨17726120, by rfl⟩ : syracuseStep 23634827 = 35452241) B35452241
theorem B3073247 : Blo 1364501 3073247 := bstep (se 1 (by rfl) ⟨2304935, by rfl⟩ : syracuseStep 3073247 = 4609871) B4609871
theorem B29517119 : Blo 1364501 29517119 := bstep (se 1 (by rfl) ⟨22137839, by rfl⟩ : syracuseStep 29517119 = 44275679) B44275679
theorem B2049563 : Blo 1364501 2049563 := bstep (se 1 (by rfl) ⟨1537172, by rfl⟩ : syracuseStep 2049563 = 3074345) B3074345
theorem B2303903 : Blo 1364501 2303903 := bstep (se 1 (by rfl) ⟨1727927, by rfl⟩ : syracuseStep 2303903 = 3455855) B3455855
theorem B28010909 : Blo 1364501 28010909 := bstep (se 3 (by rfl) ⟨5252045, by rfl⟩ : syracuseStep 28010909 = 10504091) B10504091
theorem B29928275 : Blo 1364501 29928275 := bstep (se 1 (by rfl) ⟨22446206, by rfl⟩ : syracuseStep 29928275 = 44892413) B44892413
theorem B1535071 : Blo 1364501 1535071 := bstep (se 1 (by rfl) ⟨1151303, by rfl⟩ : syracuseStep 1535071 = 2302607) B2302607
theorem B404040869 : Blo 1364501 404040869 := bstep (se 4 (by rfl) ⟨37878831, by rfl⟩ : syracuseStep 404040869 = 75757663) B75757663
theorem B10366379 : Blo 1364501 10366379 := bstep (se 1 (by rfl) ⟨7774784, by rfl⟩ : syracuseStep 10366379 = 15549569) B15549569
theorem B5836319 : Blo 1364501 5836319 := bstep (se 1 (by rfl) ⟨4377239, by rfl⟩ : syracuseStep 5836319 = 8754479) B8754479
theorem B5829245 : Blo 1364501 5829245 := bstep (se 3 (by rfl) ⟨1092983, by rfl⟩ : syracuseStep 5829245 = 2185967) B2185967
theorem B112170035 : Blo 1364501 112170035 := bstep (se 1 (by rfl) ⟨84127526, by rfl⟩ : syracuseStep 112170035 = 168255053) B168255053
theorem B1365531 : Blo 1364501 1365531 := bstep (se 1 (by rfl) ⟨1024148, by rfl⟩ : syracuseStep 1365531 = 2048297) B2048297
theorem B44300591 : Blo 1364501 44300591 := bstep (se 1 (by rfl) ⟨33225443, by rfl⟩ : syracuseStep 44300591 = 66450887) B66450887
theorem B2047391 : Blo 1364501 2047391 := bstep (se 1 (by rfl) ⟨1535543, by rfl⟩ : syracuseStep 2047391 = 3071087) B3071087
theorem B14769631 : Blo 1364501 14769631 := bstep (se 1 (by rfl) ⟨11077223, by rfl⟩ : syracuseStep 14769631 = 22154447) B22154447
theorem B42073627 : Blo 1364501 42073627 := bstep (se 1 (by rfl) ⟨31555220, by rfl⟩ : syracuseStep 42073627 = 63110441) B63110441
theorem B6913673 : Blo 1364501 6913673 := bstep (se 2 (by rfl) ⟨2592627, by rfl⟩ : syracuseStep 6913673 = 5185255) B5185255
theorem B3071807 : Blo 1364501 3071807 := bstep (se 1 (by rfl) ⟨2303855, by rfl⟩ : syracuseStep 3071807 = 4607711) B4607711
theorem B2048831 : Blo 1364501 2048831 := bstep (se 1 (by rfl) ⟨1536623, by rfl⟩ : syracuseStep 2048831 = 3073247) B3073247
theorem B19678079 : Blo 1364501 19678079 := bstep (se 1 (by rfl) ⟨14758559, by rfl⟩ : syracuseStep 19678079 = 29517119) B29517119
theorem B29533727 : Blo 1364501 29533727 := bstep (se 1 (by rfl) ⟨22150295, by rfl⟩ : syracuseStep 29533727 = 44300591) B44300591
theorem B3886163 : Blo 1364501 3886163 := bstep (se 1 (by rfl) ⟨2914622, by rfl⟩ : syracuseStep 3886163 = 5829245) B5829245
theorem B15756551 : Blo 1364501 15756551 := bstep (se 1 (by rfl) ⟨11817413, by rfl⟩ : syracuseStep 15756551 = 23634827) B23634827
theorem B74780023 : Blo 1364501 74780023 := bstep (se 1 (by rfl) ⟨56085017, by rfl⟩ : syracuseStep 74780023 = 112170035) B112170035
theorem B1535935 : Blo 1364501 1535935 := bstep (se 1 (by rfl) ⟨1151951, by rfl⟩ : syracuseStep 1535935 = 2303903) B2303903
theorem B18673939 : Blo 1364501 18673939 := bstep (se 1 (by rfl) ⟨14005454, by rfl⟩ : syracuseStep 18673939 = 28010909) B28010909
theorem B19952183 : Blo 1364501 19952183 := bstep (se 1 (by rfl) ⟨14964137, by rfl⟩ : syracuseStep 19952183 = 29928275) B29928275
theorem B1364927 : Blo 1364501 1364927 := bstep (se 1 (by rfl) ⟨1023695, by rfl⟩ : syracuseStep 1364927 = 2047391) B2047391
theorem B6910919 : Blo 1364501 6910919 := bstep (se 1 (by rfl) ⟨5183189, by rfl⟩ : syracuseStep 6910919 = 10366379) B10366379
theorem B4609115 : Blo 1364501 4609115 := bstep (se 1 (by rfl) ⟨3456836, by rfl⟩ : syracuseStep 4609115 = 6913673) B6913673
theorem B78771365 : Blo 1364501 78771365 := bstep (se 4 (by rfl) ⟨7384815, by rfl⟩ : syracuseStep 78771365 = 14769631) B14769631
theorem B1366375 : Blo 1364501 1366375 := bstep (se 1 (by rfl) ⟨1024781, by rfl⟩ : syracuseStep 1366375 = 2049563) B2049563
theorem B2046761 : Blo 1364501 2046761 := bstep (se 2 (by rfl) ⟨767535, by rfl⟩ : syracuseStep 2046761 = 1535071) B1535071
theorem B56098169 : Blo 1364501 56098169 := bstep (se 2 (by rfl) ⟨21036813, by rfl⟩ : syracuseStep 56098169 = 42073627) B42073627
theorem B269360579 : Blo 1364501 269360579 := bstep (se 1 (by rfl) ⟨202020434, by rfl⟩ : syracuseStep 269360579 = 404040869) B404040869
theorem B3890879 : Blo 1364501 3890879 := bstep (se 1 (by rfl) ⟨2918159, by rfl⟩ : syracuseStep 3890879 = 5836319) B5836319
theorem B2047871 : Blo 1364501 2047871 := bstep (se 1 (by rfl) ⟨1535903, by rfl⟩ : syracuseStep 2047871 = 3071807) B3071807
theorem B3072743 : Blo 1364501 3072743 := bstep (se 1 (by rfl) ⟨2304557, by rfl⟩ : syracuseStep 3072743 = 4609115) B4609115
theorem B99706697 : Blo 1364501 99706697 := bstep (se 2 (by rfl) ⟨37390011, by rfl⟩ : syracuseStep 99706697 = 74780023) B74780023
theorem B2590775 : Blo 1364501 2590775 := bstep (se 1 (by rfl) ⟨1943081, by rfl⟩ : syracuseStep 2590775 = 3886163) B3886163
theorem B10504367 : Blo 1364501 10504367 := bstep (se 1 (by rfl) ⟨7878275, by rfl⟩ : syracuseStep 10504367 = 15756551) B15756551
theorem B37398779 : Blo 1364501 37398779 := bstep (se 1 (by rfl) ⟨28049084, by rfl⟩ : syracuseStep 37398779 = 56098169) B56098169
theorem B24898585 : Blo 1364501 24898585 := bstep (se 2 (by rfl) ⟨9336969, by rfl⟩ : syracuseStep 24898585 = 18673939) B18673939
theorem B4607279 : Blo 1364501 4607279 := bstep (se 1 (by rfl) ⟨3455459, by rfl⟩ : syracuseStep 4607279 = 6910919) B6910919
theorem B52514243 : Blo 1364501 52514243 := bstep (se 1 (by rfl) ⟨39385682, by rfl⟩ : syracuseStep 52514243 = 78771365) B78771365
theorem B19689151 : Blo 1364501 19689151 := bstep (se 1 (by rfl) ⟨14766863, by rfl⟩ : syracuseStep 19689151 = 29533727) B29533727
theorem B718294877 : Blo 1364501 718294877 := bstep (se 3 (by rfl) ⟨134680289, by rfl⟩ : syracuseStep 718294877 = 269360579) B269360579
theorem B1364507 : Blo 1364501 1364507 := bstep (se 1 (by rfl) ⟨1023380, by rfl⟩ : syracuseStep 1364507 = 2046761) B2046761
theorem B52474877 : Blo 1364501 52474877 := bstep (se 3 (by rfl) ⟨9839039, by rfl⟩ : syracuseStep 52474877 = 19678079) B19678079
theorem B2593919 : Blo 1364501 2593919 := bstep (se 1 (by rfl) ⟨1945439, by rfl⟩ : syracuseStep 2593919 = 3890879) B3890879
theorem B1365247 : Blo 1364501 1365247 := bstep (se 1 (by rfl) ⟨1023935, by rfl⟩ : syracuseStep 1365247 = 2047871) B2047871
theorem B13301455 : Blo 1364501 13301455 := bstep (se 1 (by rfl) ⟨9976091, by rfl⟩ : syracuseStep 13301455 = 19952183) B19952183
theorem B1365887 : Blo 1364501 1365887 := bstep (se 1 (by rfl) ⟨1024415, by rfl⟩ : syracuseStep 1365887 = 2048831) B2048831
theorem B2047913 : Blo 1364501 2047913 := bstep (se 2 (by rfl) ⟨767967, by rfl⟩ : syracuseStep 2047913 = 1535935) B1535935
theorem B2048495 : Blo 1364501 2048495 := bstep (se 1 (by rfl) ⟨1536371, by rfl⟩ : syracuseStep 2048495 = 3072743) B3072743
theorem B1729279 : Blo 1364501 1729279 := bstep (se 1 (by rfl) ⟨1296959, by rfl⟩ : syracuseStep 1729279 = 2593919) B2593919
theorem B66471131 : Blo 1364501 66471131 := bstep (se 1 (by rfl) ⟨49853348, by rfl⟩ : syracuseStep 66471131 = 99706697) B99706697
theorem B34983251 : Blo 1364501 34983251 := bstep (se 1 (by rfl) ⟨26237438, by rfl⟩ : syracuseStep 34983251 = 52474877) B52474877
theorem B33198113 : Blo 1364501 33198113 := bstep (se 2 (by rfl) ⟨12449292, by rfl⟩ : syracuseStep 33198113 = 24898585) B24898585
theorem B24932519 : Blo 1364501 24932519 := bstep (se 1 (by rfl) ⟨18699389, by rfl⟩ : syracuseStep 24932519 = 37398779) B37398779
theorem B26252201 : Blo 1364501 26252201 := bstep (se 2 (by rfl) ⟨9844575, by rfl⟩ : syracuseStep 26252201 = 19689151) B19689151
theorem B35009495 : Blo 1364501 35009495 := bstep (se 1 (by rfl) ⟨26257121, by rfl⟩ : syracuseStep 35009495 = 52514243) B52514243
theorem B1365275 : Blo 1364501 1365275 := bstep (se 1 (by rfl) ⟨1023956, by rfl⟩ : syracuseStep 1365275 = 2047913) B2047913
theorem B1727183 : Blo 1364501 1727183 := bstep (se 1 (by rfl) ⟨1295387, by rfl⟩ : syracuseStep 1727183 = 2590775) B2590775
theorem B7002911 : Blo 1364501 7002911 := bstep (se 1 (by rfl) ⟨5252183, by rfl⟩ : syracuseStep 7002911 = 10504367) B10504367
theorem B3071519 : Blo 1364501 3071519 := bstep (se 1 (by rfl) ⟨2303639, by rfl⟩ : syracuseStep 3071519 = 4607279) B4607279
theorem B17735273 : Blo 1364501 17735273 := bstep (se 2 (by rfl) ⟨6650727, by rfl⟩ : syracuseStep 17735273 = 13301455) B13301455
theorem B478863251 : Blo 1364501 478863251 := bstep (se 1 (by rfl) ⟨359147438, by rfl⟩ : syracuseStep 478863251 = 718294877) B718294877
theorem B16621679 : Blo 1364501 16621679 := bstep (se 1 (by rfl) ⟨12466259, by rfl⟩ : syracuseStep 16621679 = 24932519) B24932519
theorem B23339663 : Blo 1364501 23339663 := bstep (se 1 (by rfl) ⟨17504747, by rfl⟩ : syracuseStep 23339663 = 35009495) B35009495
theorem B4605821 : Blo 1364501 4605821 := bstep (se 3 (by rfl) ⟨863591, by rfl⟩ : syracuseStep 4605821 = 1727183) B1727183
theorem B11823515 : Blo 1364501 11823515 := bstep (se 1 (by rfl) ⟨8867636, by rfl⟩ : syracuseStep 11823515 = 17735273) B17735273
theorem B17501467 : Blo 1364501 17501467 := bstep (se 1 (by rfl) ⟨13126100, by rfl⟩ : syracuseStep 17501467 = 26252201) B26252201
theorem B44314087 : Blo 1364501 44314087 := bstep (se 1 (by rfl) ⟨33235565, by rfl⟩ : syracuseStep 44314087 = 66471131) B66471131
theorem B2305705 : Blo 1364501 2305705 := bstep (se 2 (by rfl) ⟨864639, by rfl⟩ : syracuseStep 2305705 = 1729279) B1729279
theorem B22132075 : Blo 1364501 22132075 := bstep (se 1 (by rfl) ⟨16599056, by rfl⟩ : syracuseStep 22132075 = 33198113) B33198113
theorem B1365663 : Blo 1364501 1365663 := bstep (se 1 (by rfl) ⟨1024247, by rfl⟩ : syracuseStep 1365663 = 2048495) B2048495
theorem B4668607 : Blo 1364501 4668607 := bstep (se 1 (by rfl) ⟨3501455, by rfl⟩ : syracuseStep 4668607 = 7002911) B7002911
theorem B23322167 : Blo 1364501 23322167 := bstep (se 1 (by rfl) ⟨17491625, by rfl⟩ : syracuseStep 23322167 = 34983251) B34983251
theorem B2047679 : Blo 1364501 2047679 := bstep (se 1 (by rfl) ⟨1535759, by rfl⟩ : syracuseStep 2047679 = 3071519) B3071519
theorem B319242167 : Blo 1364501 319242167 := bstep (se 1 (by rfl) ⟨239431625, by rfl⟩ : syracuseStep 319242167 = 478863251) B478863251
theorem B7882343 : Blo 1364501 7882343 := bstep (se 1 (by rfl) ⟨5911757, by rfl⟩ : syracuseStep 7882343 = 11823515) B11823515
theorem B29509433 : Blo 1364501 29509433 := bstep (se 2 (by rfl) ⟨11066037, by rfl⟩ : syracuseStep 29509433 = 22132075) B22132075
theorem B3074273 : Blo 1364501 3074273 := bstep (se 2 (by rfl) ⟨1152852, by rfl⟩ : syracuseStep 3074273 = 2305705) B2305705
theorem B15559775 : Blo 1364501 15559775 := bstep (se 1 (by rfl) ⟨11669831, by rfl⟩ : syracuseStep 15559775 = 23339663) B23339663
theorem B24899237 : Blo 1364501 24899237 := bstep (se 4 (by rfl) ⟨2334303, by rfl⟩ : syracuseStep 24899237 = 4668607) B4668607
theorem B23335289 : Blo 1364501 23335289 := bstep (se 2 (by rfl) ⟨8750733, by rfl⟩ : syracuseStep 23335289 = 17501467) B17501467
theorem B59085449 : Blo 1364501 59085449 := bstep (se 2 (by rfl) ⟨22157043, by rfl⟩ : syracuseStep 59085449 = 44314087) B44314087
theorem B1365119 : Blo 1364501 1365119 := bstep (se 1 (by rfl) ⟨1023839, by rfl⟩ : syracuseStep 1365119 = 2047679) B2047679
theorem B11081119 : Blo 1364501 11081119 := bstep (se 1 (by rfl) ⟨8310839, by rfl⟩ : syracuseStep 11081119 = 16621679) B16621679
theorem B3070547 : Blo 1364501 3070547 := bstep (se 1 (by rfl) ⟨2302910, by rfl⟩ : syracuseStep 3070547 = 4605821) B4605821
theorem B15548111 : Blo 1364501 15548111 := bstep (se 1 (by rfl) ⟨11661083, by rfl⟩ : syracuseStep 15548111 = 23322167) B23322167
theorem B212828111 : Blo 1364501 212828111 := bstep (se 1 (by rfl) ⟨159621083, by rfl⟩ : syracuseStep 212828111 = 319242167) B319242167
theorem B15556859 : Blo 1364501 15556859 := bstep (se 1 (by rfl) ⟨11667644, by rfl⟩ : syracuseStep 15556859 = 23335289) B23335289
theorem B2049515 : Blo 1364501 2049515 := bstep (se 1 (by rfl) ⟨1537136, by rfl⟩ : syracuseStep 2049515 = 3074273) B3074273
theorem B10373183 : Blo 1364501 10373183 := bstep (se 1 (by rfl) ⟨7779887, by rfl⟩ : syracuseStep 10373183 = 15559775) B15559775
theorem B16599491 : Blo 1364501 16599491 := bstep (se 1 (by rfl) ⟨12449618, by rfl⟩ : syracuseStep 16599491 = 24899237) B24899237
theorem B10365407 : Blo 1364501 10365407 := bstep (se 1 (by rfl) ⟨7774055, by rfl⟩ : syracuseStep 10365407 = 15548111) B15548111
theorem B39390299 : Blo 1364501 39390299 := bstep (se 1 (by rfl) ⟨29542724, by rfl⟩ : syracuseStep 39390299 = 59085449) B59085449
theorem B5254895 : Blo 1364501 5254895 := bstep (se 1 (by rfl) ⟨3941171, by rfl⟩ : syracuseStep 5254895 = 7882343) B7882343
theorem B19672955 : Blo 1364501 19672955 := bstep (se 1 (by rfl) ⟨14754716, by rfl⟩ : syracuseStep 19672955 = 29509433) B29509433
theorem B14774825 : Blo 1364501 14774825 := bstep (se 2 (by rfl) ⟨5540559, by rfl⟩ : syracuseStep 14774825 = 11081119) B11081119
theorem B2047031 : Blo 1364501 2047031 := bstep (se 1 (by rfl) ⟨1535273, by rfl⟩ : syracuseStep 2047031 = 3070547) B3070547
theorem B141885407 : Blo 1364501 141885407 := bstep (se 1 (by rfl) ⟨106414055, by rfl⟩ : syracuseStep 141885407 = 212828111) B212828111
theorem B10371239 : Blo 1364501 10371239 := bstep (se 1 (by rfl) ⟨7778429, by rfl⟩ : syracuseStep 10371239 = 15556859) B15556859
theorem B6915455 : Blo 1364501 6915455 := bstep (se 1 (by rfl) ⟨5186591, by rfl⟩ : syracuseStep 6915455 = 10373183) B10373183
theorem B9849883 : Blo 1364501 9849883 := bstep (se 1 (by rfl) ⟨7387412, by rfl⟩ : syracuseStep 9849883 = 14774825) B14774825
theorem B6910271 : Blo 1364501 6910271 := bstep (se 1 (by rfl) ⟨5182703, by rfl⟩ : syracuseStep 6910271 = 10365407) B10365407
theorem B1364687 : Blo 1364501 1364687 := bstep (se 1 (by rfl) ⟨1023515, by rfl⟩ : syracuseStep 1364687 = 2047031) B2047031
theorem B26260199 : Blo 1364501 26260199 := bstep (se 1 (by rfl) ⟨19695149, by rfl⟩ : syracuseStep 26260199 = 39390299) B39390299
theorem B3503263 : Blo 1364501 3503263 := bstep (se 1 (by rfl) ⟨2627447, by rfl⟩ : syracuseStep 3503263 = 5254895) B5254895
theorem B94590271 : Blo 1364501 94590271 := bstep (se 1 (by rfl) ⟨70942703, by rfl⟩ : syracuseStep 94590271 = 141885407) B141885407
theorem B1366343 : Blo 1364501 1366343 := bstep (se 1 (by rfl) ⟨1024757, by rfl⟩ : syracuseStep 1366343 = 2049515) B2049515
theorem B11066327 : Blo 1364501 11066327 := bstep (se 1 (by rfl) ⟨8299745, by rfl⟩ : syracuseStep 11066327 = 16599491) B16599491
theorem B13115303 : Blo 1364501 13115303 := bstep (se 1 (by rfl) ⟨9836477, by rfl⟩ : syracuseStep 13115303 = 19672955) B19672955
theorem B6914159 : Blo 1364501 6914159 := bstep (se 1 (by rfl) ⟨5185619, by rfl⟩ : syracuseStep 6914159 = 10371239) B10371239
theorem B17506799 : Blo 1364501 17506799 := bstep (se 1 (by rfl) ⟨13130099, by rfl⟩ : syracuseStep 17506799 = 26260199) B26260199
theorem B13133177 : Blo 1364501 13133177 := bstep (se 2 (by rfl) ⟨4924941, by rfl⟩ : syracuseStep 13133177 = 9849883) B9849883
theorem B4671017 : Blo 1364501 4671017 := bstep (se 2 (by rfl) ⟨1751631, by rfl⟩ : syracuseStep 4671017 = 3503263) B3503263
theorem B8743535 : Blo 1364501 8743535 := bstep (se 1 (by rfl) ⟨6557651, by rfl⟩ : syracuseStep 8743535 = 13115303) B13115303
theorem B4606847 : Blo 1364501 4606847 := bstep (se 1 (by rfl) ⟨3455135, by rfl⟩ : syracuseStep 4606847 = 6910271) B6910271
theorem B126120361 : Blo 1364501 126120361 := bstep (se 2 (by rfl) ⟨47295135, by rfl⟩ : syracuseStep 126120361 = 94590271) B94590271
theorem B7377551 : Blo 1364501 7377551 := bstep (se 1 (by rfl) ⟨5533163, by rfl⟩ : syracuseStep 7377551 = 11066327) B11066327
theorem B4610303 : Blo 1364501 4610303 := bstep (se 1 (by rfl) ⟨3457727, by rfl⟩ : syracuseStep 4610303 = 6915455) B6915455
theorem B3114011 : Blo 1364501 3114011 := bstep (se 1 (by rfl) ⟨2335508, by rfl⟩ : syracuseStep 3114011 = 4671017) B4671017
theorem B3073535 : Blo 1364501 3073535 := bstep (se 1 (by rfl) ⟨2305151, by rfl⟩ : syracuseStep 3073535 = 4610303) B4610303
theorem B4918367 : Blo 1364501 4918367 := bstep (se 1 (by rfl) ⟨3688775, by rfl⟩ : syracuseStep 4918367 = 7377551) B7377551
theorem B168160481 : Blo 1364501 168160481 := bstep (se 2 (by rfl) ⟨63060180, by rfl⟩ : syracuseStep 168160481 = 126120361) B126120361
theorem B5829023 : Blo 1364501 5829023 := bstep (se 1 (by rfl) ⟨4371767, by rfl⟩ : syracuseStep 5829023 = 8743535) B8743535
theorem B4609439 : Blo 1364501 4609439 := bstep (se 1 (by rfl) ⟨3457079, by rfl⟩ : syracuseStep 4609439 = 6914159) B6914159
theorem B11671199 : Blo 1364501 11671199 := bstep (se 1 (by rfl) ⟨8753399, by rfl⟩ : syracuseStep 11671199 = 17506799) B17506799
theorem B8755451 : Blo 1364501 8755451 := bstep (se 1 (by rfl) ⟨6566588, by rfl⟩ : syracuseStep 8755451 = 13133177) B13133177
theorem B3071231 : Blo 1364501 3071231 := bstep (se 1 (by rfl) ⟨2303423, by rfl⟩ : syracuseStep 3071231 = 4606847) B4606847
theorem B13115645 : Blo 1364501 13115645 := bstep (se 3 (by rfl) ⟨2459183, by rfl⟩ : syracuseStep 13115645 = 4918367) B4918367
theorem B3072959 : Blo 1364501 3072959 := bstep (se 1 (by rfl) ⟨2304719, by rfl⟩ : syracuseStep 3072959 = 4609439) B4609439
theorem B2049023 : Blo 1364501 2049023 := bstep (se 1 (by rfl) ⟨1536767, by rfl⟩ : syracuseStep 2049023 = 3073535) B3073535
theorem B3886015 : Blo 1364501 3886015 := bstep (se 1 (by rfl) ⟨2914511, by rfl⟩ : syracuseStep 3886015 = 5829023) B5829023
theorem B5836967 : Blo 1364501 5836967 := bstep (se 1 (by rfl) ⟨4377725, by rfl⟩ : syracuseStep 5836967 = 8755451) B8755451
theorem B8304029 : Blo 1364501 8304029 := bstep (se 3 (by rfl) ⟨1557005, by rfl⟩ : syracuseStep 8304029 = 3114011) B3114011
theorem B7780799 : Blo 1364501 7780799 := bstep (se 1 (by rfl) ⟨5835599, by rfl⟩ : syracuseStep 7780799 = 11671199) B11671199
theorem B112106987 : Blo 1364501 112106987 := bstep (se 1 (by rfl) ⟨84080240, by rfl⟩ : syracuseStep 112106987 = 168160481) B168160481
theorem B2047487 : Blo 1364501 2047487 := bstep (se 1 (by rfl) ⟨1535615, by rfl⟩ : syracuseStep 2047487 = 3071231) B3071231
theorem B3891311 : Blo 1364501 3891311 := bstep (se 1 (by rfl) ⟨2918483, by rfl⟩ : syracuseStep 3891311 = 5836967) B5836967
theorem B2048639 : Blo 1364501 2048639 := bstep (se 1 (by rfl) ⟨1536479, by rfl⟩ : syracuseStep 2048639 = 3072959) B3072959
theorem B5187199 : Blo 1364501 5187199 := bstep (se 1 (by rfl) ⟨3890399, by rfl⟩ : syracuseStep 5187199 = 7780799) B7780799
theorem B74737991 : Blo 1364501 74737991 := bstep (se 1 (by rfl) ⟨56053493, by rfl⟩ : syracuseStep 74737991 = 112106987) B112106987
theorem B8743763 : Blo 1364501 8743763 := bstep (se 1 (by rfl) ⟨6557822, by rfl⟩ : syracuseStep 8743763 = 13115645) B13115645
theorem B5181353 : Blo 1364501 5181353 := bstep (se 2 (by rfl) ⟨1943007, by rfl⟩ : syracuseStep 5181353 = 3886015) B3886015
theorem B1364991 : Blo 1364501 1364991 := bstep (se 1 (by rfl) ⟨1023743, by rfl⟩ : syracuseStep 1364991 = 2047487) B2047487
theorem B1366015 : Blo 1364501 1366015 := bstep (se 1 (by rfl) ⟨1024511, by rfl⟩ : syracuseStep 1366015 = 2049023) B2049023
theorem B5536019 : Blo 1364501 5536019 := bstep (se 1 (by rfl) ⟨4152014, by rfl⟩ : syracuseStep 5536019 = 8304029) B8304029
theorem B49825327 : Blo 1364501 49825327 := bstep (se 1 (by rfl) ⟨37368995, by rfl⟩ : syracuseStep 49825327 = 74737991) B74737991
theorem B6916265 : Blo 1364501 6916265 := bstep (se 2 (by rfl) ⟨2593599, by rfl⟩ : syracuseStep 6916265 = 5187199) B5187199
theorem B3690679 : Blo 1364501 3690679 := bstep (se 1 (by rfl) ⟨2768009, by rfl⟩ : syracuseStep 3690679 = 5536019) B5536019
theorem B5829175 : Blo 1364501 5829175 := bstep (se 1 (by rfl) ⟨4371881, by rfl⟩ : syracuseStep 5829175 = 8743763) B8743763
theorem B3454235 : Blo 1364501 3454235 := bstep (se 1 (by rfl) ⟨2590676, by rfl⟩ : syracuseStep 3454235 = 5181353) B5181353
theorem B2594207 : Blo 1364501 2594207 := bstep (se 1 (by rfl) ⟨1945655, by rfl⟩ : syracuseStep 2594207 = 3891311) B3891311
theorem B1365759 : Blo 1364501 1365759 := bstep (se 1 (by rfl) ⟨1024319, by rfl⟩ : syracuseStep 1365759 = 2048639) B2048639
theorem B2302823 : Blo 1364501 2302823 := bstep (se 1 (by rfl) ⟨1727117, by rfl⟩ : syracuseStep 2302823 = 3454235) B3454235
theorem B6917885 : Blo 1364501 6917885 := bstep (se 3 (by rfl) ⟨1297103, by rfl⟩ : syracuseStep 6917885 = 2594207) B2594207
theorem B66433769 : Blo 1364501 66433769 := bstep (se 2 (by rfl) ⟨24912663, by rfl⟩ : syracuseStep 66433769 = 49825327) B49825327
theorem B4920905 : Blo 1364501 4920905 := bstep (se 2 (by rfl) ⟨1845339, by rfl⟩ : syracuseStep 4920905 = 3690679) B3690679
theorem B7772233 : Blo 1364501 7772233 := bstep (se 2 (by rfl) ⟨2914587, by rfl⟩ : syracuseStep 7772233 = 5829175) B5829175
theorem B4610843 : Blo 1364501 4610843 := bstep (se 1 (by rfl) ⟨3458132, by rfl⟩ : syracuseStep 4610843 = 6916265) B6916265
theorem B10362977 : Blo 1364501 10362977 := bstep (se 2 (by rfl) ⟨3886116, by rfl⟩ : syracuseStep 10362977 = 7772233) B7772233
theorem B3073895 : Blo 1364501 3073895 := bstep (se 1 (by rfl) ⟨2305421, by rfl⟩ : syracuseStep 3073895 = 4610843) B4610843
theorem B44289179 : Blo 1364501 44289179 := bstep (se 1 (by rfl) ⟨33216884, by rfl⟩ : syracuseStep 44289179 = 66433769) B66433769
theorem B1535215 : Blo 1364501 1535215 := bstep (se 1 (by rfl) ⟨1151411, by rfl⟩ : syracuseStep 1535215 = 2302823) B2302823
theorem B3280603 : Blo 1364501 3280603 := bstep (se 1 (by rfl) ⟨2460452, by rfl⟩ : syracuseStep 3280603 = 4920905) B4920905
theorem B4611923 : Blo 1364501 4611923 := bstep (se 1 (by rfl) ⟨3458942, by rfl⟩ : syracuseStep 4611923 = 6917885) B6917885
theorem B2049263 : Blo 1364501 2049263 := bstep (se 1 (by rfl) ⟨1536947, by rfl⟩ : syracuseStep 2049263 = 3073895) B3073895
theorem B29526119 : Blo 1364501 29526119 := bstep (se 1 (by rfl) ⟨22144589, by rfl⟩ : syracuseStep 29526119 = 44289179) B44289179
theorem B3074615 : Blo 1364501 3074615 := bstep (se 1 (by rfl) ⟨2305961, by rfl⟩ : syracuseStep 3074615 = 4611923) B4611923
theorem B6908651 : Blo 1364501 6908651 := bstep (se 1 (by rfl) ⟨5181488, by rfl⟩ : syracuseStep 6908651 = 10362977) B10362977
theorem B2046953 : Blo 1364501 2046953 := bstep (se 2 (by rfl) ⟨767607, by rfl⟩ : syracuseStep 2046953 = 1535215) B1535215
theorem B4374137 : Blo 1364501 4374137 := bstep (se 2 (by rfl) ⟨1640301, by rfl⟩ : syracuseStep 4374137 = 3280603) B3280603
theorem B2049743 : Blo 1364501 2049743 := bstep (se 1 (by rfl) ⟨1537307, by rfl⟩ : syracuseStep 2049743 = 3074615) B3074615
theorem B4605767 : Blo 1364501 4605767 := bstep (se 1 (by rfl) ⟨3454325, by rfl⟩ : syracuseStep 4605767 = 6908651) B6908651
theorem B1364635 : Blo 1364501 1364635 := bstep (se 1 (by rfl) ⟨1023476, by rfl⟩ : syracuseStep 1364635 = 2046953) B2046953
theorem B1366175 : Blo 1364501 1366175 := bstep (se 1 (by rfl) ⟨1024631, by rfl⟩ : syracuseStep 1366175 = 2049263) B2049263
theorem B19684079 : Blo 1364501 19684079 := bstep (se 1 (by rfl) ⟨14763059, by rfl⟩ : syracuseStep 19684079 = 29526119) B29526119
theorem B2916091 : Blo 1364501 2916091 := bstep (se 1 (by rfl) ⟨2187068, by rfl⟩ : syracuseStep 2916091 = 4374137) B4374137
theorem B15552485 : Blo 1364501 15552485 := bstep (se 4 (by rfl) ⟨1458045, by rfl⟩ : syracuseStep 15552485 = 2916091) B2916091
theorem B1366495 : Blo 1364501 1366495 := bstep (se 1 (by rfl) ⟨1024871, by rfl⟩ : syracuseStep 1366495 = 2049743) B2049743
theorem B3070511 : Blo 1364501 3070511 := bstep (se 1 (by rfl) ⟨2302883, by rfl⟩ : syracuseStep 3070511 = 4605767) B4605767
theorem B13122719 : Blo 1364501 13122719 := bstep (se 1 (by rfl) ⟨9842039, by rfl⟩ : syracuseStep 13122719 = 19684079) B19684079
theorem B10368323 : Blo 1364501 10368323 := bstep (se 1 (by rfl) ⟨7776242, by rfl⟩ : syracuseStep 10368323 = 15552485) B15552485
theorem B2047007 : Blo 1364501 2047007 := bstep (se 1 (by rfl) ⟨1535255, by rfl⟩ : syracuseStep 2047007 = 3070511) B3070511
theorem B8748479 : Blo 1364501 8748479 := bstep (se 1 (by rfl) ⟨6561359, by rfl⟩ : syracuseStep 8748479 = 13122719) B13122719
theorem B1364671 : Blo 1364501 1364671 := bstep (se 1 (by rfl) ⟨1023503, by rfl⟩ : syracuseStep 1364671 = 2047007) B2047007
theorem B6912215 : Blo 1364501 6912215 := bstep (se 1 (by rfl) ⟨5184161, by rfl⟩ : syracuseStep 6912215 = 10368323) B10368323
theorem B5832319 : Blo 1364501 5832319 := bstep (se 1 (by rfl) ⟨4374239, by rfl⟩ : syracuseStep 5832319 = 8748479) B8748479
theorem B7776425 : Blo 1364501 7776425 := bstep (se 2 (by rfl) ⟨2916159, by rfl⟩ : syracuseStep 7776425 = 5832319) B5832319
theorem B4608143 : Blo 1364501 4608143 := bstep (se 1 (by rfl) ⟨3456107, by rfl⟩ : syracuseStep 4608143 = 6912215) B6912215
theorem B3072095 : Blo 1364501 3072095 := bstep (se 1 (by rfl) ⟨2304071, by rfl⟩ : syracuseStep 3072095 = 4608143) B4608143
theorem B5184283 : Blo 1364501 5184283 := bstep (se 1 (by rfl) ⟨3888212, by rfl⟩ : syracuseStep 5184283 = 7776425) B7776425
theorem B2048063 : Blo 1364501 2048063 := bstep (se 1 (by rfl) ⟨1536047, by rfl⟩ : syracuseStep 2048063 = 3072095) B3072095
theorem B6912377 : Blo 1364501 6912377 := bstep (se 2 (by rfl) ⟨2592141, by rfl⟩ : syracuseStep 6912377 = 5184283) B5184283
theorem B4608251 : Blo 1364501 4608251 := bstep (se 1 (by rfl) ⟨3456188, by rfl⟩ : syracuseStep 4608251 = 6912377) B6912377
theorem B1365375 : Blo 1364501 1365375 := bstep (se 1 (by rfl) ⟨1024031, by rfl⟩ : syracuseStep 1365375 = 2048063) B2048063
theorem B3072167 : Blo 1364501 3072167 := bstep (se 1 (by rfl) ⟨2304125, by rfl⟩ : syracuseStep 3072167 = 4608251) B4608251
theorem B2048111 : Blo 1364501 2048111 := bstep (se 1 (by rfl) ⟨1536083, by rfl⟩ : syracuseStep 2048111 = 3072167) B3072167
theorem B1365407 : Blo 1364501 1365407 := bstep (se 1 (by rfl) ⟨1024055, by rfl⟩ : syracuseStep 1365407 = 2048111) B2048111

theorem C0 (j : ℕ) (h1 : 341125 ≤ j) (h2 : j ≤ 341624) : Blo 1364501 (4 * j + 3) := by
  interval_cases j
  · exact B1364503
  · exact B1364507
  · exact B1364511
  · exact B1364515
  · exact B1364519
  · exact B1364523
  · exact B1364527
  · exact B1364531
  · exact B1364535
  · exact B1364539
  · exact B1364543
  · exact B1364547
  · exact B1364551
  · exact B1364555
  · exact B1364559
  · exact B1364563
  · exact B1364567
  · exact B1364571
  · exact B1364575
  · exact B1364579
  · exact B1364583
  · exact B1364587
  · exact B1364591
  · exact B1364595
  · exact B1364599
  · exact B1364603
  · exact B1364607
  · exact B1364611
  · exact B1364615
  · exact B1364619
  · exact B1364623
  · exact B1364627
  · exact B1364631
  · exact B1364635
  · exact B1364639
  · exact B1364643
  · exact B1364647
  · exact B1364651
  · exact B1364655
  · exact B1364659
  · exact B1364663
  · exact B1364667
  · exact B1364671
  · exact B1364675
  · exact B1364679
  · exact B1364683
  · exact B1364687
  · exact B1364691
  · exact B1364695
  · exact B1364699
  · exact B1364703
  · exact B1364707
  · exact B1364711
  · exact B1364715
  · exact B1364719
  · exact B1364723
  · exact B1364727
  · exact B1364731
  · exact B1364735
  · exact B1364739
  · exact B1364743
  · exact B1364747
  · exact B1364751
  · exact B1364755
  · exact B1364759
  · exact B1364763
  · exact B1364767
  · exact B1364771
  · exact B1364775
  · exact B1364779
  · exact B1364783
  · exact B1364787
  · exact B1364791
  · exact B1364795
  · exact B1364799
  · exact B1364803
  · exact B1364807
  · exact B1364811
  · exact B1364815
  · exact B1364819
  · exact B1364823
  · exact B1364827
  · exact B1364831
  · exact B1364835
  · exact B1364839
  · exact B1364843
  · exact B1364847
  · exact B1364851
  · exact B1364855
  · exact B1364859
  · exact B1364863
  · exact B1364867
  · exact B1364871
  · exact B1364875
  · exact B1364879
  · exact B1364883
  · exact B1364887
  · exact B1364891
  · exact B1364895
  · exact B1364899
  · exact B1364903
  · exact B1364907
  · exact B1364911
  · exact B1364915
  · exact B1364919
  · exact B1364923
  · exact B1364927
  · exact B1364931
  · exact B1364935
  · exact B1364939
  · exact B1364943
  · exact B1364947
  · exact B1364951
  · exact B1364955
  · exact B1364959
  · exact B1364963
  · exact B1364967
  · exact B1364971
  · exact B1364975
  · exact B1364979
  · exact B1364983
  · exact B1364987
  · exact B1364991
  · exact B1364995
  · exact B1364999
  · exact B1365003
  · exact B1365007
  · exact B1365011
  · exact B1365015
  · exact B1365019
  · exact B1365023
  · exact B1365027
  · exact B1365031
  · exact B1365035
  · exact B1365039
  · exact B1365043
  · exact B1365047
  · exact B1365051
  · exact B1365055
  · exact B1365059
  · exact B1365063
  · exact B1365067
  · exact B1365071
  · exact B1365075
  · exact B1365079
  · exact B1365083
  · exact B1365087
  · exact B1365091
  · exact B1365095
  · exact B1365099
  · exact B1365103
  · exact B1365107
  · exact B1365111
  · exact B1365115
  · exact B1365119
  · exact B1365123
  · exact B1365127
  · exact B1365131
  · exact B1365135
  · exact B1365139
  · exact B1365143
  · exact B1365147
  · exact B1365151
  · exact B1365155
  · exact B1365159
  · exact B1365163
  · exact B1365167
  · exact B1365171
  · exact B1365175
  · exact B1365179
  · exact B1365183
  · exact B1365187
  · exact B1365191
  · exact B1365195
  · exact B1365199
  · exact B1365203
  · exact B1365207
  · exact B1365211
  · exact B1365215
  · exact B1365219
  · exact B1365223
  · exact B1365227
  · exact B1365231
  · exact B1365235
  · exact B1365239
  · exact B1365243
  · exact B1365247
  · exact B1365251
  · exact B1365255
  · exact B1365259
  · exact B1365263
  · exact B1365267
  · exact B1365271
  · exact B1365275
  · exact B1365279
  · exact B1365283
  · exact B1365287
  · exact B1365291
  · exact B1365295
  · exact B1365299
  · exact B1365303
  · exact B1365307
  · exact B1365311
  · exact B1365315
  · exact B1365319
  · exact B1365323
  · exact B1365327
  · exact B1365331
  · exact B1365335
  · exact B1365339
  · exact B1365343
  · exact B1365347
  · exact B1365351
  · exact B1365355
  · exact B1365359
  · exact B1365363
  · exact B1365367
  · exact B1365371
  · exact B1365375
  · exact B1365379
  · exact B1365383
  · exact B1365387
  · exact B1365391
  · exact B1365395
  · exact B1365399
  · exact B1365403
  · exact B1365407
  · exact B1365411
  · exact B1365415
  · exact B1365419
  · exact B1365423
  · exact B1365427
  · exact B1365431
  · exact B1365435
  · exact B1365439
  · exact B1365443
  · exact B1365447
  · exact B1365451
  · exact B1365455
  · exact B1365459
  · exact B1365463
  · exact B1365467
  · exact B1365471
  · exact B1365475
  · exact B1365479
  · exact B1365483
  · exact B1365487
  · exact B1365491
  · exact B1365495
  · exact B1365499
  · exact B1365503
  · exact B1365507
  · exact B1365511
  · exact B1365515
  · exact B1365519
  · exact B1365523
  · exact B1365527
  · exact B1365531
  · exact B1365535
  · exact B1365539
  · exact B1365543
  · exact B1365547
  · exact B1365551
  · exact B1365555
  · exact B1365559
  · exact B1365563
  · exact B1365567
  · exact B1365571
  · exact B1365575
  · exact B1365579
  · exact B1365583
  · exact B1365587
  · exact B1365591
  · exact B1365595
  · exact B1365599
  · exact B1365603
  · exact B1365607
  · exact B1365611
  · exact B1365615
  · exact B1365619
  · exact B1365623
  · exact B1365627
  · exact B1365631
  · exact B1365635
  · exact B1365639
  · exact B1365643
  · exact B1365647
  · exact B1365651
  · exact B1365655
  · exact B1365659
  · exact B1365663
  · exact B1365667
  · exact B1365671
  · exact B1365675
  · exact B1365679
  · exact B1365683
  · exact B1365687
  · exact B1365691
  · exact B1365695
  · exact B1365699
  · exact B1365703
  · exact B1365707
  · exact B1365711
  · exact B1365715
  · exact B1365719
  · exact B1365723
  · exact B1365727
  · exact B1365731
  · exact B1365735
  · exact B1365739
  · exact B1365743
  · exact B1365747
  · exact B1365751
  · exact B1365755
  · exact B1365759
  · exact B1365763
  · exact B1365767
  · exact B1365771
  · exact B1365775
  · exact B1365779
  · exact B1365783
  · exact B1365787
  · exact B1365791
  · exact B1365795
  · exact B1365799
  · exact B1365803
  · exact B1365807
  · exact B1365811
  · exact B1365815
  · exact B1365819
  · exact B1365823
  · exact B1365827
  · exact B1365831
  · exact B1365835
  · exact B1365839
  · exact B1365843
  · exact B1365847
  · exact B1365851
  · exact B1365855
  · exact B1365859
  · exact B1365863
  · exact B1365867
  · exact B1365871
  · exact B1365875
  · exact B1365879
  · exact B1365883
  · exact B1365887
  · exact B1365891
  · exact B1365895
  · exact B1365899
  · exact B1365903
  · exact B1365907
  · exact B1365911
  · exact B1365915
  · exact B1365919
  · exact B1365923
  · exact B1365927
  · exact B1365931
  · exact B1365935
  · exact B1365939
  · exact B1365943
  · exact B1365947
  · exact B1365951
  · exact B1365955
  · exact B1365959
  · exact B1365963
  · exact B1365967
  · exact B1365971
  · exact B1365975
  · exact B1365979
  · exact B1365983
  · exact B1365987
  · exact B1365991
  · exact B1365995
  · exact B1365999
  · exact B1366003
  · exact B1366007
  · exact B1366011
  · exact B1366015
  · exact B1366019
  · exact B1366023
  · exact B1366027
  · exact B1366031
  · exact B1366035
  · exact B1366039
  · exact B1366043
  · exact B1366047
  · exact B1366051
  · exact B1366055
  · exact B1366059
  · exact B1366063
  · exact B1366067
  · exact B1366071
  · exact B1366075
  · exact B1366079
  · exact B1366083
  · exact B1366087
  · exact B1366091
  · exact B1366095
  · exact B1366099
  · exact B1366103
  · exact B1366107
  · exact B1366111
  · exact B1366115
  · exact B1366119
  · exact B1366123
  · exact B1366127
  · exact B1366131
  · exact B1366135
  · exact B1366139
  · exact B1366143
  · exact B1366147
  · exact B1366151
  · exact B1366155
  · exact B1366159
  · exact B1366163
  · exact B1366167
  · exact B1366171
  · exact B1366175
  · exact B1366179
  · exact B1366183
  · exact B1366187
  · exact B1366191
  · exact B1366195
  · exact B1366199
  · exact B1366203
  · exact B1366207
  · exact B1366211
  · exact B1366215
  · exact B1366219
  · exact B1366223
  · exact B1366227
  · exact B1366231
  · exact B1366235
  · exact B1366239
  · exact B1366243
  · exact B1366247
  · exact B1366251
  · exact B1366255
  · exact B1366259
  · exact B1366263
  · exact B1366267
  · exact B1366271
  · exact B1366275
  · exact B1366279
  · exact B1366283
  · exact B1366287
  · exact B1366291
  · exact B1366295
  · exact B1366299
  · exact B1366303
  · exact B1366307
  · exact B1366311
  · exact B1366315
  · exact B1366319
  · exact B1366323
  · exact B1366327
  · exact B1366331
  · exact B1366335
  · exact B1366339
  · exact B1366343
  · exact B1366347
  · exact B1366351
  · exact B1366355
  · exact B1366359
  · exact B1366363
  · exact B1366367
  · exact B1366371
  · exact B1366375
  · exact B1366379
  · exact B1366383
  · exact B1366387
  · exact B1366391
  · exact B1366395
  · exact B1366399
  · exact B1366403
  · exact B1366407
  · exact B1366411
  · exact B1366415
  · exact B1366419
  · exact B1366423
  · exact B1366427
  · exact B1366431
  · exact B1366435
  · exact B1366439
  · exact B1366443
  · exact B1366447
  · exact B1366451
  · exact B1366455
  · exact B1366459
  · exact B1366463
  · exact B1366467
  · exact B1366471
  · exact B1366475
  · exact B1366479
  · exact B1366483
  · exact B1366487
  · exact B1366491
  · exact B1366495
  · exact B1366499

theorem solution (m : ℕ) (hlo : 1364501 ≤ m) (hhi : m ≤ 1366501) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 341125 ≤ j := by omega
    have hj2 : j ≤ 341624 := by omega
    have hb : Blo 1364501 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
