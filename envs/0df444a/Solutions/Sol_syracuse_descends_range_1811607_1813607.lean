-- Prove2me | solution 1 for syracuse_descends_range_1811607_1813607
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-10T00:53:41.872968+00:00
-- url     : https://prove2.me/submissions/3207a0fb-e635-4576-8652-806ed6fc3c02

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


theorem B2039809 : Blo 1811607 2039809 := bbase (se 2 (by rfl) ⟨764928, by rfl⟩ : syracuseStep 2039809 = 1529857) (by norm_num)
theorem B3489797 : Blo 1811607 3489797 := bbase (se 4 (by rfl) ⟨327168, by rfl⟩ : syracuseStep 3489797 = 654337) (by norm_num)
theorem B2719757 : Blo 1811607 2719757 := bbase (se 3 (by rfl) ⟨509954, by rfl⟩ : syracuseStep 2719757 = 1019909) (by norm_num)
theorem B4079645 : Blo 1811607 4079645 := bbase (se 3 (by rfl) ⟨764933, by rfl⟩ : syracuseStep 4079645 = 1529867) (by norm_num)
theorem B2719781 : Blo 1811607 2719781 := bbase (se 4 (by rfl) ⟨254979, by rfl⟩ : syracuseStep 2719781 = 509959) (by norm_num)
theorem B2039845 : Blo 1811607 2039845 := bbase (se 4 (by rfl) ⟨191235, by rfl⟩ : syracuseStep 2039845 = 382471) (by norm_num)
theorem B2326573 : Blo 1811607 2326573 := bbase (se 3 (by rfl) ⟨436232, by rfl⟩ : syracuseStep 2326573 = 872465) (by norm_num)
theorem B2719805 : Blo 1811607 2719805 := bbase (se 3 (by rfl) ⟨509963, by rfl⟩ : syracuseStep 2719805 = 1019927) (by norm_num)
theorem B2039881 : Blo 1811607 2039881 := bbase (se 2 (by rfl) ⟨764955, by rfl⟩ : syracuseStep 2039881 = 1529911) (by norm_num)
theorem B2719829 : Blo 1811607 2719829 := bbase (se 8 (by rfl) ⟨15936, by rfl⟩ : syracuseStep 2719829 = 31873) (by norm_num)
theorem B2293849 : Blo 1811607 2293849 := bbase (se 2 (by rfl) ⟨860193, by rfl⟩ : syracuseStep 2293849 = 1720387) (by norm_num)
theorem B6881381 : Blo 1811607 6881381 := bbase (se 4 (by rfl) ⟨645129, by rfl⟩ : syracuseStep 6881381 = 1290259) (by norm_num)
theorem B4079717 : Blo 1811607 4079717 := bbase (se 4 (by rfl) ⟨382473, by rfl⟩ : syracuseStep 4079717 = 764947) (by norm_num)
theorem B2719853 : Blo 1811607 2719853 := bbase (se 3 (by rfl) ⟨509972, by rfl⟩ : syracuseStep 2719853 = 1019945) (by norm_num)
theorem B2039917 : Blo 1811607 2039917 := bbase (se 3 (by rfl) ⟨382484, by rfl⟩ : syracuseStep 2039917 = 764969) (by norm_num)
theorem B4587637 : Blo 1811607 4587637 := bbase (se 5 (by rfl) ⟨215045, by rfl⟩ : syracuseStep 4587637 = 430091) (by norm_num)
theorem B2719877 : Blo 1811607 2719877 := bbase (se 4 (by rfl) ⟨254988, by rfl⟩ : syracuseStep 2719877 = 509977) (by norm_num)
theorem B2039953 : Blo 1811607 2039953 := bbase (se 2 (by rfl) ⟨764982, by rfl⟩ : syracuseStep 2039953 = 1529965) (by norm_num)
theorem B3440789 : Blo 1811607 3440789 := bbase (se 6 (by rfl) ⟨80643, by rfl⟩ : syracuseStep 3440789 = 161287) (by norm_num)
theorem B2719901 : Blo 1811607 2719901 := bbase (se 3 (by rfl) ⟨509981, by rfl⟩ : syracuseStep 2719901 = 1019963) (by norm_num)
theorem B4079789 : Blo 1811607 4079789 := bbase (se 3 (by rfl) ⟨764960, by rfl⟩ : syracuseStep 4079789 = 1529921) (by norm_num)
theorem B2719925 : Blo 1811607 2719925 := bbase (se 5 (by rfl) ⟨127496, by rfl⟩ : syracuseStep 2719925 = 254993) (by norm_num)
theorem B2039989 : Blo 1811607 2039989 := bbase (se 5 (by rfl) ⟨95624, by rfl⟩ : syracuseStep 2039989 = 191249) (by norm_num)
theorem B2719949 : Blo 1811607 2719949 := bbase (se 3 (by rfl) ⟨509990, by rfl⟩ : syracuseStep 2719949 = 1019981) (by norm_num)
theorem B2040025 : Blo 1811607 2040025 := bbase (se 2 (by rfl) ⟨765009, by rfl⟩ : syracuseStep 2040025 = 1530019) (by norm_num)
theorem B4587749 : Blo 1811607 4587749 := bbase (se 4 (by rfl) ⟨430101, by rfl⟩ : syracuseStep 4587749 = 860203) (by norm_num)
theorem B2719973 : Blo 1811607 2719973 := bbase (se 4 (by rfl) ⟨254997, by rfl⟩ : syracuseStep 2719973 = 509995) (by norm_num)
theorem B4079861 : Blo 1811607 4079861 := bbase (se 5 (by rfl) ⟨191243, by rfl⟩ : syracuseStep 4079861 = 382487) (by norm_num)
theorem B4653301 : Blo 1811607 4653301 := bbase (se 5 (by rfl) ⟨218123, by rfl⟩ : syracuseStep 4653301 = 436247) (by norm_num)
theorem B3776765 : Blo 1811607 3776765 := bbase (se 3 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 3776765 = 1416287) (by norm_num)
theorem B2719997 : Blo 1811607 2719997 := bbase (se 3 (by rfl) ⟨509999, by rfl⟩ : syracuseStep 2719997 = 1019999) (by norm_num)
theorem B2040061 : Blo 1811607 2040061 := bbase (se 3 (by rfl) ⟨382511, by rfl⟩ : syracuseStep 2040061 = 765023) (by norm_num)
theorem B2294021 : Blo 1811607 2294021 := bbase (se 4 (by rfl) ⟨215064, by rfl⟩ : syracuseStep 2294021 = 430129) (by norm_num)
theorem B2720021 : Blo 1811607 2720021 := bbase (se 6 (by rfl) ⟨63750, by rfl⟩ : syracuseStep 2720021 = 127501) (by norm_num)
theorem B2040097 : Blo 1811607 2040097 := bbase (se 2 (by rfl) ⟨765036, by rfl⟩ : syracuseStep 2040097 = 1530073) (by norm_num)
theorem B2720045 : Blo 1811607 2720045 := bbase (se 3 (by rfl) ⟨510008, by rfl⟩ : syracuseStep 2720045 = 1020017) (by norm_num)
theorem B2294077 : Blo 1811607 2294077 := bbase (se 3 (by rfl) ⟨430139, by rfl⟩ : syracuseStep 2294077 = 860279) (by norm_num)
theorem B4079933 : Blo 1811607 4079933 := bbase (se 3 (by rfl) ⟨764987, by rfl⟩ : syracuseStep 4079933 = 1529975) (by norm_num)
theorem B2720069 : Blo 1811607 2720069 := bbase (se 4 (by rfl) ⟨255006, by rfl⟩ : syracuseStep 2720069 = 510013) (by norm_num)
theorem B2040133 : Blo 1811607 2040133 := bbase (se 4 (by rfl) ⟨191262, by rfl⟩ : syracuseStep 2040133 = 382525) (by norm_num)
theorem B39739733 : Blo 1811607 39739733 := bbase (se 10 (by rfl) ⟨58212, by rfl⟩ : syracuseStep 39739733 = 116425) (by norm_num)
theorem B6119765 : Blo 1811607 6119765 := bbase (se 10 (by rfl) ⟨8964, by rfl⟩ : syracuseStep 6119765 = 17929) (by norm_num)
theorem B2720093 : Blo 1811607 2720093 := bbase (se 3 (by rfl) ⟨510017, by rfl⟩ : syracuseStep 2720093 = 1020035) (by norm_num)
theorem B5808485 : Blo 1811607 5808485 := bbase (se 4 (by rfl) ⟨544545, by rfl⟩ : syracuseStep 5808485 = 1089091) (by norm_num)
theorem B2040169 : Blo 1811607 2040169 := bbase (se 2 (by rfl) ⟨765063, by rfl⟩ : syracuseStep 2040169 = 1530127) (by norm_num)
theorem B2720117 : Blo 1811607 2720117 := bbase (se 5 (by rfl) ⟨127505, by rfl⟩ : syracuseStep 2720117 = 255011) (by norm_num)
theorem B6881669 : Blo 1811607 6881669 := bbase (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) (by norm_num)
theorem B4080005 : Blo 1811607 4080005 := bbase (se 4 (by rfl) ⟨382500, by rfl⟩ : syracuseStep 4080005 = 765001) (by norm_num)
theorem B2720141 : Blo 1811607 2720141 := bbase (se 3 (by rfl) ⟨510026, by rfl⟩ : syracuseStep 2720141 = 1020053) (by norm_num)
theorem B2040205 : Blo 1811607 2040205 := bbase (se 3 (by rfl) ⟨382538, by rfl⟩ : syracuseStep 2040205 = 765077) (by norm_num)
theorem B2294173 : Blo 1811607 2294173 := bbase (se 3 (by rfl) ⟨430157, by rfl⟩ : syracuseStep 2294173 = 860315) (by norm_num)
theorem B4587941 : Blo 1811607 4587941 := bbase (se 4 (by rfl) ⟨430119, by rfl⟩ : syracuseStep 4587941 = 860239) (by norm_num)
theorem B2720165 : Blo 1811607 2720165 := bbase (se 4 (by rfl) ⟨255015, by rfl⟩ : syracuseStep 2720165 = 510031) (by norm_num)
theorem B2040241 : Blo 1811607 2040241 := bbase (se 2 (by rfl) ⟨765090, by rfl⟩ : syracuseStep 2040241 = 1530181) (by norm_num)
theorem B2720189 : Blo 1811607 2720189 := bbase (se 3 (by rfl) ⟨510035, by rfl⟩ : syracuseStep 2720189 = 1020071) (by norm_num)
theorem B4080077 : Blo 1811607 4080077 := bbase (se 3 (by rfl) ⟨765014, by rfl⟩ : syracuseStep 4080077 = 1530029) (by norm_num)
theorem B2720213 : Blo 1811607 2720213 := bbase (se 7 (by rfl) ⟨31877, by rfl⟩ : syracuseStep 2720213 = 63755) (by norm_num)
theorem B2040277 : Blo 1811607 2040277 := bbase (se 7 (by rfl) ⟨23909, by rfl⟩ : syracuseStep 2040277 = 47819) (by norm_num)
theorem B2720237 : Blo 1811607 2720237 := bbase (se 3 (by rfl) ⟨510044, by rfl⟩ : syracuseStep 2720237 = 1020089) (by norm_num)
theorem B2720261 : Blo 1811607 2720261 := bbase (se 4 (by rfl) ⟨255024, by rfl⟩ : syracuseStep 2720261 = 510049) (by norm_num)
theorem B15483413 : Blo 1811607 15483413 := bbase (se 6 (by rfl) ⟨362892, by rfl⟩ : syracuseStep 15483413 = 725785) (by norm_num)
theorem B4080149 : Blo 1811607 4080149 := bbase (se 6 (by rfl) ⟨95628, by rfl⟩ : syracuseStep 4080149 = 191257) (by norm_num)
theorem B2720285 : Blo 1811607 2720285 := bbase (se 3 (by rfl) ⟨510053, by rfl⟩ : syracuseStep 2720285 = 1020107) (by norm_num)
theorem B2720309 : Blo 1811607 2720309 := bbase (se 5 (by rfl) ⟨127514, by rfl⟩ : syracuseStep 2720309 = 255029) (by norm_num)
theorem B2294345 : Blo 1811607 2294345 := bbase (se 2 (by rfl) ⟨860379, by rfl⟩ : syracuseStep 2294345 = 1720759) (by norm_num)
theorem B2720333 : Blo 1811607 2720333 := bbase (se 3 (by rfl) ⟨510062, by rfl⟩ : syracuseStep 2720333 = 1020125) (by norm_num)
theorem B4080221 : Blo 1811607 4080221 := bbase (se 3 (by rfl) ⟨765041, by rfl⟩ : syracuseStep 4080221 = 1530083) (by norm_num)
theorem B2581093 : Blo 1811607 2581093 := bbase (se 4 (by rfl) ⟨241977, by rfl⟩ : syracuseStep 2581093 = 483955) (by norm_num)
theorem B2720357 : Blo 1811607 2720357 := bbase (se 4 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 2720357 = 510067) (by norm_num)
theorem B10322549 : Blo 1811607 10322549 := bbase (se 5 (by rfl) ⟨483869, by rfl⟩ : syracuseStep 10322549 = 967739) (by norm_num)
theorem B2720381 : Blo 1811607 2720381 := bbase (se 3 (by rfl) ⟨510071, by rfl⟩ : syracuseStep 2720381 = 1020143) (by norm_num)
theorem B2294401 : Blo 1811607 2294401 := bbase (se 2 (by rfl) ⟨860400, by rfl⟩ : syracuseStep 2294401 = 1720801) (by norm_num)
theorem B7742101 : Blo 1811607 7742101 := bbase (se 6 (by rfl) ⟨181455, by rfl⟩ : syracuseStep 7742101 = 362911) (by norm_num)
theorem B2720405 : Blo 1811607 2720405 := bbase (se 6 (by rfl) ⟨63759, by rfl⟩ : syracuseStep 2720405 = 127519) (by norm_num)
theorem B2761381 : Blo 1811607 2761381 := bbase (se 4 (by rfl) ⟨258879, by rfl⟩ : syracuseStep 2761381 = 517759) (by norm_num)
theorem B7742117 : Blo 1811607 7742117 := bbase (se 4 (by rfl) ⟨725823, by rfl⟩ : syracuseStep 7742117 = 1451647) (by norm_num)
theorem B4080293 : Blo 1811607 4080293 := bbase (se 4 (by rfl) ⟨382527, by rfl⟩ : syracuseStep 4080293 = 765055) (by norm_num)
theorem B2294497 : Blo 1811607 2294497 := bbase (se 2 (by rfl) ⟨860436, by rfl⟩ : syracuseStep 2294497 = 1720873) (by norm_num)
theorem B4080365 : Blo 1811607 4080365 := bbase (se 3 (by rfl) ⟨765068, by rfl⟩ : syracuseStep 4080365 = 1530137) (by norm_num)
theorem B4588285 : Blo 1811607 4588285 := bbase (se 3 (by rfl) ⟨860303, by rfl⟩ : syracuseStep 4588285 = 1720607) (by norm_num)
theorem B6120197 : Blo 1811607 6120197 := bbase (se 4 (by rfl) ⟨573768, by rfl⟩ : syracuseStep 6120197 = 1147537) (by norm_num)
theorem B5161765 : Blo 1811607 5161765 := bbase (se 4 (by rfl) ⟨483915, by rfl⟩ : syracuseStep 5161765 = 967831) (by norm_num)
theorem B4080437 : Blo 1811607 4080437 := bbase (se 5 (by rfl) ⟨191270, by rfl⟩ : syracuseStep 4080437 = 382541) (by norm_num)
theorem B4588397 : Blo 1811607 4588397 := bbase (se 3 (by rfl) ⟨860324, by rfl⟩ : syracuseStep 4588397 = 1720649) (by norm_num)
theorem B3924845 : Blo 1811607 3924845 := bbase (se 3 (by rfl) ⟨735908, by rfl⟩ : syracuseStep 3924845 = 1471817) (by norm_num)
theorem B4080509 : Blo 1811607 4080509 := bbase (se 3 (by rfl) ⟨765095, by rfl⟩ : syracuseStep 4080509 = 1530191) (by norm_num)
theorem B3441541 : Blo 1811607 3441541 := bbase (se 4 (by rfl) ⟨322644, by rfl⟩ : syracuseStep 3441541 = 645289) (by norm_num)
theorem B2294669 : Blo 1811607 2294669 := bbase (se 3 (by rfl) ⟨430250, by rfl⟩ : syracuseStep 2294669 = 860501) (by norm_num)
theorem B6046645 : Blo 1811607 6046645 := bbase (se 5 (by rfl) ⟨283436, by rfl⟩ : syracuseStep 6046645 = 566873) (by norm_num)
theorem B13067189 : Blo 1811607 13067189 := bbase (se 5 (by rfl) ⟨612524, by rfl⟩ : syracuseStep 13067189 = 1225049) (by norm_num)
theorem B2294725 : Blo 1811607 2294725 := bbase (se 4 (by rfl) ⟨215130, by rfl⟩ : syracuseStep 2294725 = 430261) (by norm_num)
theorem B4080581 : Blo 1811607 4080581 := bbase (se 4 (by rfl) ⟨382554, by rfl⟩ : syracuseStep 4080581 = 765109) (by norm_num)
theorem B3441685 : Blo 1811607 3441685 := bbase (se 6 (by rfl) ⟨80664, by rfl⟩ : syracuseStep 3441685 = 161329) (by norm_num)
theorem B19604501 : Blo 1811607 19604501 := bbase (se 6 (by rfl) ⟨459480, by rfl⟩ : syracuseStep 19604501 = 918961) (by norm_num)
theorem B2294821 : Blo 1811607 2294821 := bbase (se 4 (by rfl) ⟨215139, by rfl⟩ : syracuseStep 2294821 = 430279) (by norm_num)
theorem B4588589 : Blo 1811607 4588589 := bbase (se 3 (by rfl) ⟨860360, by rfl⟩ : syracuseStep 4588589 = 1720721) (by norm_num)
theorem B9176165 : Blo 1811607 9176165 := bbase (se 4 (by rfl) ⟨860265, by rfl⟩ : syracuseStep 9176165 = 1720531) (by norm_num)
theorem B3310709 : Blo 1811607 3310709 := bbase (se 5 (by rfl) ⟨155189, by rfl⟩ : syracuseStep 3310709 = 310379) (by norm_num)
theorem B3441845 : Blo 1811607 3441845 := bbase (se 5 (by rfl) ⟨161336, by rfl⟩ : syracuseStep 3441845 = 322673) (by norm_num)
theorem B6120629 : Blo 1811607 6120629 := bbase (se 5 (by rfl) ⟨286904, by rfl⟩ : syracuseStep 6120629 = 573809) (by norm_num)
theorem B2294993 : Blo 1811607 2294993 := bbase (se 2 (by rfl) ⟨860622, by rfl⟩ : syracuseStep 2294993 = 1721245) (by norm_num)
theorem B2450693 : Blo 1811607 2450693 := bbase (se 4 (by rfl) ⟨229752, by rfl⟩ : syracuseStep 2450693 = 459505) (by norm_num)
theorem B2295049 : Blo 1811607 2295049 := bbase (se 2 (by rfl) ⟨860643, by rfl⟩ : syracuseStep 2295049 = 1721287) (by norm_num)
theorem B1934641 : Blo 1811607 1934641 := bbase (se 2 (by rfl) ⟨725490, by rfl⟩ : syracuseStep 1934641 = 1450981) (by norm_num)
theorem B3441989 : Blo 1811607 3441989 := bbase (se 4 (by rfl) ⟨322686, by rfl⟩ : syracuseStep 3441989 = 645373) (by norm_num)
theorem B2295145 : Blo 1811607 2295145 := bbase (se 2 (by rfl) ⟨860679, by rfl⟩ : syracuseStep 2295145 = 1721359) (by norm_num)
theorem B2581885 : Blo 1811607 2581885 := bbase (se 3 (by rfl) ⟨484103, by rfl⟩ : syracuseStep 2581885 = 968207) (by norm_num)
theorem B4588933 : Blo 1811607 4588933 := bbase (se 4 (by rfl) ⟨430212, by rfl⟩ : syracuseStep 4588933 = 860425) (by norm_num)
theorem B26142101 : Blo 1811607 26142101 := bbase (se 6 (by rfl) ⟨612705, by rfl⟩ : syracuseStep 26142101 = 1225411) (by norm_num)
theorem B4589045 : Blo 1811607 4589045 := bbase (se 5 (by rfl) ⟨215111, by rfl⟩ : syracuseStep 4589045 = 430223) (by norm_num)
theorem B3057149 : Blo 1811607 3057149 := bbase (se 3 (by rfl) ⟨573215, by rfl⟩ : syracuseStep 3057149 = 1146431) (by norm_num)
theorem B2295317 : Blo 1811607 2295317 := bbase (se 6 (by rfl) ⟨53796, by rfl⟩ : syracuseStep 2295317 = 107593) (by norm_num)
theorem B6882853 : Blo 1811607 6882853 := bbase (se 4 (by rfl) ⟨645267, by rfl⟩ : syracuseStep 6882853 = 1290535) (by norm_num)
theorem B2065981 : Blo 1811607 2065981 := bbase (se 3 (by rfl) ⟨387371, by rfl⟩ : syracuseStep 2065981 = 774743) (by norm_num)
theorem B3442277 : Blo 1811607 3442277 := bbase (se 4 (by rfl) ⟨322713, by rfl⟩ : syracuseStep 3442277 = 645427) (by norm_num)
theorem B3057277 : Blo 1811607 3057277 := bbase (se 3 (by rfl) ⟨573239, by rfl⟩ : syracuseStep 3057277 = 1146479) (by norm_num)
theorem B4589237 : Blo 1811607 4589237 := bbase (se 5 (by rfl) ⟨215120, by rfl⟩ : syracuseStep 4589237 = 430241) (by norm_num)
theorem B2582221 : Blo 1811607 2582221 := bbase (se 3 (by rfl) ⟨484166, by rfl⟩ : syracuseStep 2582221 = 968333) (by norm_num)
theorem B3057365 : Blo 1811607 3057365 := bbase (se 7 (by rfl) ⟨35828, by rfl⟩ : syracuseStep 3057365 = 71657) (by norm_num)
theorem B3442429 : Blo 1811607 3442429 := bbase (se 3 (by rfl) ⟨645455, by rfl⟩ : syracuseStep 3442429 = 1290911) (by norm_num)
theorem B10323733 : Blo 1811607 10323733 := bbase (se 6 (by rfl) ⟨241962, by rfl⟩ : syracuseStep 10323733 = 483925) (by norm_num)
theorem B3057493 : Blo 1811607 3057493 := bbase (se 9 (by rfl) ⟨8957, by rfl⟩ : syracuseStep 3057493 = 17915) (by norm_num)
theorem B6883157 : Blo 1811607 6883157 := bbase (se 9 (by rfl) ⟨20165, by rfl⟩ : syracuseStep 6883157 = 40331) (by norm_num)
theorem B2901853 : Blo 1811607 2901853 := bbase (se 3 (by rfl) ⟨544097, by rfl⟩ : syracuseStep 2901853 = 1088195) (by norm_num)
theorem B1836901 : Blo 1811607 1836901 := bbase (se 4 (by rfl) ⟨172209, by rfl⟩ : syracuseStep 1836901 = 344419) (by norm_num)
theorem B5162869 : Blo 1811607 5162869 := bbase (se 5 (by rfl) ⟨242009, by rfl⟩ : syracuseStep 5162869 = 484019) (by norm_num)
theorem B1836949 : Blo 1811607 1836949 := bbase (se 6 (by rfl) ⟨43053, by rfl⟩ : syracuseStep 1836949 = 86107) (by norm_num)
theorem B8710037 : Blo 1811607 8710037 := bbase (se 6 (by rfl) ⟨204141, by rfl⟩ : syracuseStep 8710037 = 408283) (by norm_num)
theorem B3057581 : Blo 1811607 3057581 := bbase (se 3 (by rfl) ⟨573296, by rfl⟩ : syracuseStep 3057581 = 1146593) (by norm_num)
theorem B4589581 : Blo 1811607 4589581 := bbase (se 3 (by rfl) ⟨860546, by rfl⟩ : syracuseStep 4589581 = 1721093) (by norm_num)
theorem B3057709 : Blo 1811607 3057709 := bbase (se 3 (by rfl) ⟨573320, by rfl⟩ : syracuseStep 3057709 = 1146641) (by norm_num)
theorem B3442733 : Blo 1811607 3442733 := bbase (se 3 (by rfl) ⟨645512, by rfl⟩ : syracuseStep 3442733 = 1291025) (by norm_num)
theorem B8710229 : Blo 1811607 8710229 := bbase (se 8 (by rfl) ⟨51036, by rfl⟩ : syracuseStep 8710229 = 102073) (by norm_num)
theorem B2484317 : Blo 1811607 2484317 := bbase (se 3 (by rfl) ⟨465809, by rfl⟩ : syracuseStep 2484317 = 931619) (by norm_num)
theorem B1935461 : Blo 1811607 1935461 := bbase (se 4 (by rfl) ⟨181449, by rfl⟩ : syracuseStep 1935461 = 362899) (by norm_num)
theorem B4589693 : Blo 1811607 4589693 := bbase (se 3 (by rfl) ⟨860567, by rfl⟩ : syracuseStep 4589693 = 1721135) (by norm_num)
theorem B3057797 : Blo 1811607 3057797 := bbase (se 4 (by rfl) ⟨286668, by rfl⟩ : syracuseStep 3057797 = 573337) (by norm_num)
theorem B9799829 : Blo 1811607 9799829 := bbase (se 6 (by rfl) ⟨229683, by rfl⟩ : syracuseStep 9799829 = 459367) (by norm_num)
theorem B6531317 : Blo 1811607 6531317 := bbase (se 5 (by rfl) ⟨306155, by rfl⟩ : syracuseStep 6531317 = 612311) (by norm_num)
theorem B3057925 : Blo 1811607 3057925 := bbase (se 4 (by rfl) ⟨286680, by rfl⟩ : syracuseStep 3057925 = 573361) (by norm_num)
theorem B4589885 : Blo 1811607 4589885 := bbase (se 3 (by rfl) ⟨860603, by rfl⟩ : syracuseStep 4589885 = 1721207) (by norm_num)
theorem B3058013 : Blo 1811607 3058013 := bbase (se 3 (by rfl) ⟨573377, by rfl⟩ : syracuseStep 3058013 = 1146755) (by norm_num)
theorem B9177461 : Blo 1811607 9177461 := bbase (se 5 (by rfl) ⟨430193, by rfl⟩ : syracuseStep 9177461 = 860387) (by norm_num)
theorem B2902397 : Blo 1811607 2902397 := bbase (se 3 (by rfl) ⟨544199, by rfl⟩ : syracuseStep 2902397 = 1088399) (by norm_num)
theorem B4778389 : Blo 1811607 4778389 := bbase (se 6 (by rfl) ⟨111993, by rfl⟩ : syracuseStep 4778389 = 223987) (by norm_num)
theorem B3058141 : Blo 1811607 3058141 := bbase (se 3 (by rfl) ⟨573401, by rfl⟩ : syracuseStep 3058141 = 1146803) (by norm_num)
theorem B2066965 : Blo 1811607 2066965 := bbase (se 6 (by rfl) ⟨48444, by rfl⟩ : syracuseStep 2066965 = 96889) (by norm_num)
theorem B3869213 : Blo 1811607 3869213 := bbase (se 3 (by rfl) ⟨725477, by rfl⟩ : syracuseStep 3869213 = 1450955) (by norm_num)
theorem B1935905 : Blo 1811607 1935905 := bbase (se 2 (by rfl) ⟨725964, by rfl⟩ : syracuseStep 1935905 = 1451929) (by norm_num)
theorem B3058229 : Blo 1811607 3058229 := bbase (se 5 (by rfl) ⟨143354, by rfl⟩ : syracuseStep 3058229 = 286709) (by norm_num)
theorem B4590229 : Blo 1811607 4590229 := bbase (se 6 (by rfl) ⟨107583, by rfl⟩ : syracuseStep 4590229 = 215167) (by norm_num)
theorem B3058357 : Blo 1811607 3058357 := bbase (se 5 (by rfl) ⟨143360, by rfl⟩ : syracuseStep 3058357 = 286721) (by norm_num)
theorem B2067125 : Blo 1811607 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B4590341 : Blo 1811607 4590341 := bbase (se 4 (by rfl) ⟨430344, by rfl⟩ : syracuseStep 4590341 = 860689) (by norm_num)
theorem B3869453 : Blo 1811607 3869453 := bbase (se 3 (by rfl) ⟨725522, by rfl⟩ : syracuseStep 3869453 = 1451045) (by norm_num)
theorem B3058445 : Blo 1811607 3058445 := bbase (se 3 (by rfl) ⟨573458, by rfl⟩ : syracuseStep 3058445 = 1146917) (by norm_num)
theorem B1936153 : Blo 1811607 1936153 := bbase (se 2 (by rfl) ⟨726057, by rfl⟩ : syracuseStep 1936153 = 1452115) (by norm_num)
theorem B7744373 : Blo 1811607 7744373 := bbase (se 5 (by rfl) ⟨363017, by rfl⟩ : syracuseStep 7744373 = 726035) (by norm_num)
theorem B3058573 : Blo 1811607 3058573 := bbase (se 3 (by rfl) ⟨573482, by rfl⟩ : syracuseStep 3058573 = 1146965) (by norm_num)
theorem B13069205 : Blo 1811607 13069205 := bbase (se 6 (by rfl) ⟨306309, by rfl⟩ : syracuseStep 13069205 = 612619) (by norm_num)
theorem B2902949 : Blo 1811607 2902949 := bbase (se 4 (by rfl) ⟨272151, by rfl⟩ : syracuseStep 2902949 = 544303) (by norm_num)
theorem B2902981 : Blo 1811607 2902981 := bbase (se 4 (by rfl) ⟨272154, by rfl⟩ : syracuseStep 2902981 = 544309) (by norm_num)
theorem B4590533 : Blo 1811607 4590533 := bbase (se 4 (by rfl) ⟨430362, by rfl⟩ : syracuseStep 4590533 = 860725) (by norm_num)
theorem B3058661 : Blo 1811607 3058661 := bbase (se 4 (by rfl) ⟨286749, by rfl⟩ : syracuseStep 3058661 = 573499) (by norm_num)
theorem B3533885 : Blo 1811607 3533885 := bbase (se 3 (by rfl) ⟨662603, by rfl⟩ : syracuseStep 3533885 = 1325207) (by norm_num)
theorem B3058789 : Blo 1811607 3058789 := bbase (se 4 (by rfl) ⟨286761, by rfl⟩ : syracuseStep 3058789 = 573523) (by norm_num)
theorem B4353173 : Blo 1811607 4353173 := bbase (se 6 (by rfl) ⟨102027, by rfl⟩ : syracuseStep 4353173 = 204055) (by norm_num)
theorem B3058877 : Blo 1811607 3058877 := bbase (se 3 (by rfl) ⟨573539, by rfl⟩ : syracuseStep 3058877 = 1147079) (by norm_num)
theorem B1936585 : Blo 1811607 1936585 := bbase (se 2 (by rfl) ⟨726219, by rfl⟩ : syracuseStep 1936585 = 1452439) (by norm_num)
theorem B4353269 : Blo 1811607 4353269 := bbase (se 5 (by rfl) ⟨204059, by rfl⟩ : syracuseStep 4353269 = 408119) (by norm_num)
theorem B2067709 : Blo 1811607 2067709 := bbase (se 3 (by rfl) ⟨387695, by rfl⟩ : syracuseStep 2067709 = 775391) (by norm_num)
theorem B3869957 : Blo 1811607 3869957 := bbase (se 4 (by rfl) ⟨362808, by rfl⟩ : syracuseStep 3869957 = 725617) (by norm_num)
theorem B3869965 : Blo 1811607 3869965 := bbase (se 3 (by rfl) ⟨725618, by rfl⟩ : syracuseStep 3869965 = 1451237) (by norm_num)
theorem B1936657 : Blo 1811607 1936657 := bbase (se 2 (by rfl) ⟨726246, by rfl⟩ : syracuseStep 1936657 = 1452493) (by norm_num)
theorem B6114581 : Blo 1811607 6114581 := bbase (se 6 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 6114581 = 286621) (by norm_num)
theorem B3059005 : Blo 1811607 3059005 := bbase (se 3 (by rfl) ⟨573563, by rfl⟩ : syracuseStep 3059005 = 1147127) (by norm_num)
theorem B5164373 : Blo 1811607 5164373 := bbase (se 11 (by rfl) ⟨3782, by rfl⟩ : syracuseStep 5164373 = 7565) (by norm_num)
theorem B3100045 : Blo 1811607 3100045 := bbase (se 3 (by rfl) ⟨581258, by rfl⟩ : syracuseStep 3100045 = 1162517) (by norm_num)
theorem B3059093 : Blo 1811607 3059093 := bbase (se 6 (by rfl) ⟨71697, by rfl⟩ : syracuseStep 3059093 = 143395) (by norm_num)
theorem B15486389 : Blo 1811607 15486389 := bbase (se 5 (by rfl) ⟨725924, by rfl⟩ : syracuseStep 15486389 = 1451849) (by norm_num)
theorem B9301445 : Blo 1811607 9301445 := bbase (se 4 (by rfl) ⟨872010, by rfl⟩ : syracuseStep 9301445 = 1744021) (by norm_num)
theorem B4132333 : Blo 1811607 4132333 := bbase (se 3 (by rfl) ⟨774812, by rfl⟩ : syracuseStep 4132333 = 1549625) (by norm_num)
theorem B3100141 : Blo 1811607 3100141 := bbase (se 3 (by rfl) ⟨581276, by rfl⟩ : syracuseStep 3100141 = 1162553) (by norm_num)
theorem B3059221 : Blo 1811607 3059221 := bbase (se 6 (by rfl) ⟨71700, by rfl⟩ : syracuseStep 3059221 = 143401) (by norm_num)
theorem B3403301 : Blo 1811607 3403301 := bbase (se 4 (by rfl) ⟨319059, by rfl⟩ : syracuseStep 3403301 = 638119) (by norm_num)
theorem B2756197 : Blo 1811607 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B3059309 : Blo 1811607 3059309 := bbase (se 3 (by rfl) ⟨573620, by rfl⟩ : syracuseStep 3059309 = 1147241) (by norm_num)
theorem B3100285 : Blo 1811607 3100285 := bbase (se 3 (by rfl) ⟨581303, by rfl⟩ : syracuseStep 3100285 = 1162607) (by norm_num)
theorem B9178757 : Blo 1811607 9178757 := bbase (se 4 (by rfl) ⟨860508, by rfl⟩ : syracuseStep 9178757 = 1721017) (by norm_num)
theorem B3534509 : Blo 1811607 3534509 := bbase (se 3 (by rfl) ⟨662720, by rfl⟩ : syracuseStep 3534509 = 1325441) (by norm_num)
theorem B6115013 : Blo 1811607 6115013 := bbase (se 4 (by rfl) ⟨573282, by rfl⟩ : syracuseStep 6115013 = 1146565) (by norm_num)
theorem B10325717 : Blo 1811607 10325717 := bbase (se 7 (by rfl) ⟨121004, by rfl⟩ : syracuseStep 10325717 = 242009) (by norm_num)
theorem B9301733 : Blo 1811607 9301733 := bbase (se 4 (by rfl) ⟨872037, by rfl⟩ : syracuseStep 9301733 = 1744075) (by norm_num)
theorem B3059437 : Blo 1811607 3059437 := bbase (se 3 (by rfl) ⟨573644, by rfl⟩ : syracuseStep 3059437 = 1147289) (by norm_num)
theorem B3059525 : Blo 1811607 3059525 := bbase (se 4 (by rfl) ⟨286830, by rfl⟩ : syracuseStep 3059525 = 573661) (by norm_num)
theorem B2903909 : Blo 1811607 2903909 := bbase (se 4 (by rfl) ⟨272241, by rfl⟩ : syracuseStep 2903909 = 544483) (by norm_num)
theorem B26480533 : Blo 1811607 26480533 := bbase (se 6 (by rfl) ⟨620637, by rfl⟩ : syracuseStep 26480533 = 1241275) (by norm_num)
theorem B6885269 : Blo 1811607 6885269 := bbase (se 6 (by rfl) ⟨161373, by rfl⟩ : syracuseStep 6885269 = 322747) (by norm_num)
theorem B3059653 : Blo 1811607 3059653 := bbase (se 4 (by rfl) ⟨286842, by rfl⟩ : syracuseStep 3059653 = 573685) (by norm_num)
theorem B5230565 : Blo 1811607 5230565 := bbase (se 4 (by rfl) ⟨490365, by rfl⟩ : syracuseStep 5230565 = 980731) (by norm_num)
theorem B3059741 : Blo 1811607 3059741 := bbase (se 3 (by rfl) ⟨573701, by rfl⟩ : syracuseStep 3059741 = 1147403) (by norm_num)
theorem B1962041 : Blo 1811607 1962041 := bbase (se 2 (by rfl) ⟨735765, by rfl⟩ : syracuseStep 1962041 = 1471531) (by norm_num)
theorem B33083477 : Blo 1811607 33083477 := bbase (se 8 (by rfl) ⟨193848, by rfl⟩ : syracuseStep 33083477 = 387697) (by norm_num)
theorem B3723365 : Blo 1811607 3723365 := bbase (se 4 (by rfl) ⟨349065, by rfl⟩ : syracuseStep 3723365 = 698131) (by norm_num)
theorem B6115445 : Blo 1811607 6115445 := bbase (se 5 (by rfl) ⟨286661, by rfl⟩ : syracuseStep 6115445 = 573323) (by norm_num)
theorem B3059869 : Blo 1811607 3059869 := bbase (se 3 (by rfl) ⟨573725, by rfl⟩ : syracuseStep 3059869 = 1147451) (by norm_num)
theorem B6885557 : Blo 1811607 6885557 := bbase (se 5 (by rfl) ⟨322760, by rfl⟩ : syracuseStep 6885557 = 645521) (by norm_num)
theorem B3059957 : Blo 1811607 3059957 := bbase (se 5 (by rfl) ⟨143435, by rfl⟩ : syracuseStep 3059957 = 286871) (by norm_num)
theorem B2756909 : Blo 1811607 2756909 := bbase (se 3 (by rfl) ⟨516920, by rfl⟩ : syracuseStep 2756909 = 1033841) (by norm_num)
theorem B3871093 : Blo 1811607 3871093 := bbase (se 5 (by rfl) ⟨181457, by rfl⟩ : syracuseStep 3871093 = 362915) (by norm_num)
theorem B3060085 : Blo 1811607 3060085 := bbase (se 5 (by rfl) ⟨143441, by rfl⟩ : syracuseStep 3060085 = 286883) (by norm_num)
theorem B2421181 : Blo 1811607 2421181 := bbase (se 3 (by rfl) ⟨453971, by rfl⟩ : syracuseStep 2421181 = 907943) (by norm_num)
theorem B3060173 : Blo 1811607 3060173 := bbase (se 3 (by rfl) ⟨573782, by rfl⟩ : syracuseStep 3060173 = 1147565) (by norm_num)
theorem B2904589 : Blo 1811607 2904589 := bbase (se 3 (by rfl) ⟨544610, by rfl⟩ : syracuseStep 2904589 = 1089221) (by norm_num)
theorem B6115877 : Blo 1811607 6115877 := bbase (se 4 (by rfl) ⟨573363, by rfl⟩ : syracuseStep 6115877 = 1146727) (by norm_num)
theorem B2904653 : Blo 1811607 2904653 := bbase (se 3 (by rfl) ⟨544622, by rfl⟩ : syracuseStep 2904653 = 1089245) (by norm_num)
theorem B3060301 : Blo 1811607 3060301 := bbase (se 3 (by rfl) ⟨573806, by rfl⟩ : syracuseStep 3060301 = 1147613) (by norm_num)
theorem B4076117 : Blo 1811607 4076117 := bbase (se 8 (by rfl) ⟨23883, by rfl⟩ : syracuseStep 4076117 = 47767) (by norm_num)
theorem B3674741 : Blo 1811607 3674741 := bbase (se 5 (by rfl) ⟨172253, by rfl⟩ : syracuseStep 3674741 = 344507) (by norm_num)
theorem B5804693 : Blo 1811607 5804693 := bbase (se 6 (by rfl) ⟨136047, by rfl⟩ : syracuseStep 5804693 = 272095) (by norm_num)
theorem B4076189 : Blo 1811607 4076189 := bbase (se 3 (by rfl) ⟨764285, by rfl⟩ : syracuseStep 4076189 = 1528571) (by norm_num)
theorem B3060389 : Blo 1811607 3060389 := bbase (se 4 (by rfl) ⟨286911, by rfl⟩ : syracuseStep 3060389 = 573823) (by norm_num)
theorem B4076261 : Blo 1811607 4076261 := bbase (se 4 (by rfl) ⟨382149, by rfl⟩ : syracuseStep 4076261 = 764299) (by norm_num)
theorem B3871469 : Blo 1811607 3871469 := bbase (se 3 (by rfl) ⟨725900, by rfl⟩ : syracuseStep 3871469 = 1451801) (by norm_num)
theorem B2757413 : Blo 1811607 2757413 := bbase (se 4 (by rfl) ⟨258507, by rfl⟩ : syracuseStep 2757413 = 517015) (by norm_num)
theorem B4076333 : Blo 1811607 4076333 := bbase (se 3 (by rfl) ⟨764312, by rfl⟩ : syracuseStep 4076333 = 1528625) (by norm_num)
theorem B4076405 : Blo 1811607 4076405 := bbase (se 5 (by rfl) ⟨191081, by rfl⟩ : syracuseStep 4076405 = 382163) (by norm_num)
theorem B9180053 : Blo 1811607 9180053 := bbase (se 6 (by rfl) ⟨215157, by rfl⟩ : syracuseStep 9180053 = 430315) (by norm_num)
theorem B5510069 : Blo 1811607 5510069 := bbase (se 5 (by rfl) ⟨258284, by rfl⟩ : syracuseStep 5510069 = 516569) (by norm_num)
theorem B4076477 : Blo 1811607 4076477 := bbase (se 3 (by rfl) ⟨764339, by rfl⟩ : syracuseStep 4076477 = 1528679) (by norm_num)
theorem B3724237 : Blo 1811607 3724237 := bbase (se 3 (by rfl) ⟨698294, by rfl⟩ : syracuseStep 3724237 = 1396589) (by norm_num)
theorem B7738325 : Blo 1811607 7738325 := bbase (se 7 (by rfl) ⟨90683, by rfl⟩ : syracuseStep 7738325 = 181367) (by norm_num)
theorem B6116309 : Blo 1811607 6116309 := bbase (se 7 (by rfl) ⟨71675, by rfl⟩ : syracuseStep 6116309 = 143351) (by norm_num)
theorem B4076549 : Blo 1811607 4076549 := bbase (se 4 (by rfl) ⟨382176, by rfl⟩ : syracuseStep 4076549 = 764353) (by norm_num)
theorem B4076621 : Blo 1811607 4076621 := bbase (se 3 (by rfl) ⟨764366, by rfl⟩ : syracuseStep 4076621 = 1528733) (by norm_num)
theorem B4076693 : Blo 1811607 4076693 := bbase (se 6 (by rfl) ⟨95547, by rfl⟩ : syracuseStep 4076693 = 191095) (by norm_num)
theorem B3675325 : Blo 1811607 3675325 := bbase (se 3 (by rfl) ⟨689123, by rfl⟩ : syracuseStep 3675325 = 1378247) (by norm_num)
theorem B13767893 : Blo 1811607 13767893 := bbase (se 7 (by rfl) ⟨161342, by rfl⟩ : syracuseStep 13767893 = 322685) (by norm_num)
theorem B4076765 : Blo 1811607 4076765 := bbase (se 3 (by rfl) ⟨764393, by rfl⟩ : syracuseStep 4076765 = 1528787) (by norm_num)
theorem B4076837 : Blo 1811607 4076837 := bbase (se 4 (by rfl) ⟨382203, by rfl⟩ : syracuseStep 4076837 = 764407) (by norm_num)
theorem B4355365 : Blo 1811607 4355365 := bbase (se 4 (by rfl) ⟨408315, by rfl⟩ : syracuseStep 4355365 = 816631) (by norm_num)
theorem B9172277 : Blo 1811607 9172277 := bbase (se 5 (by rfl) ⟨429950, by rfl⟩ : syracuseStep 9172277 = 859901) (by norm_num)
theorem B4076909 : Blo 1811607 4076909 := bbase (se 3 (by rfl) ⟨764420, by rfl⟩ : syracuseStep 4076909 = 1528841) (by norm_num)
theorem B6116741 : Blo 1811607 6116741 := bbase (se 4 (by rfl) ⟨573444, by rfl⟩ : syracuseStep 6116741 = 1146889) (by norm_num)
theorem B4076981 : Blo 1811607 4076981 := bbase (se 5 (by rfl) ⟨191108, by rfl⟩ : syracuseStep 4076981 = 382217) (by norm_num)
theorem B2176481 : Blo 1811607 2176481 := bbase (se 2 (by rfl) ⟨816180, by rfl⟩ : syracuseStep 2176481 = 1632361) (by norm_num)
theorem B4077053 : Blo 1811607 4077053 := bbase (se 3 (by rfl) ⟨764447, by rfl⟩ : syracuseStep 4077053 = 1528895) (by norm_num)
theorem B5805589 : Blo 1811607 5805589 := bbase (se 6 (by rfl) ⟨136068, by rfl⟩ : syracuseStep 5805589 = 272137) (by norm_num)
theorem B4077125 : Blo 1811607 4077125 := bbase (se 4 (by rfl) ⟨382230, by rfl⟩ : syracuseStep 4077125 = 764461) (by norm_num)
theorem B37189205 : Blo 1811607 37189205 := bbase (se 8 (by rfl) ⟨217905, by rfl⟩ : syracuseStep 37189205 = 435811) (by norm_num)
theorem B13760117 : Blo 1811607 13760117 := bbase (se 5 (by rfl) ⟨645005, by rfl⟩ : syracuseStep 13760117 = 1290011) (by norm_num)
theorem B3675773 : Blo 1811607 3675773 := bbase (se 3 (by rfl) ⟨689207, by rfl⟩ : syracuseStep 3675773 = 1378415) (by norm_num)
theorem B4077197 : Blo 1811607 4077197 := bbase (se 3 (by rfl) ⟨764474, by rfl⟩ : syracuseStep 4077197 = 1528949) (by norm_num)
theorem B3675797 : Blo 1811607 3675797 := bbase (se 6 (by rfl) ⟨86151, by rfl⟩ : syracuseStep 3675797 = 172303) (by norm_num)
theorem B4077269 : Blo 1811607 4077269 := bbase (se 7 (by rfl) ⟨47780, by rfl⟩ : syracuseStep 4077269 = 95561) (by norm_num)
theorem B2717429 : Blo 1811607 2717429 := bbase (se 5 (by rfl) ⟨127379, by rfl⟩ : syracuseStep 2717429 = 254759) (by norm_num)
theorem B6878965 : Blo 1811607 6878965 := bbase (se 5 (by rfl) ⟨322451, by rfl⟩ : syracuseStep 6878965 = 644903) (by norm_num)
theorem B2717453 : Blo 1811607 2717453 := bbase (se 3 (by rfl) ⟨509522, by rfl⟩ : syracuseStep 2717453 = 1019045) (by norm_num)
theorem B2176789 : Blo 1811607 2176789 := bbase (se 6 (by rfl) ⟨51018, by rfl⟩ : syracuseStep 2176789 = 102037) (by norm_num)
theorem B4077341 : Blo 1811607 4077341 := bbase (se 3 (by rfl) ⟨764501, by rfl⟩ : syracuseStep 4077341 = 1529003) (by norm_num)
theorem B2717477 : Blo 1811607 2717477 := bbase (se 4 (by rfl) ⟨254763, by rfl⟩ : syracuseStep 2717477 = 509527) (by norm_num)
theorem B6117173 : Blo 1811607 6117173 := bbase (se 5 (by rfl) ⟨286742, by rfl⟩ : syracuseStep 6117173 = 573485) (by norm_num)
theorem B2717501 : Blo 1811607 2717501 := bbase (se 3 (by rfl) ⟨509531, by rfl⟩ : syracuseStep 2717501 = 1019063) (by norm_num)
theorem B2717525 : Blo 1811607 2717525 := bbase (se 9 (by rfl) ⟨7961, by rfl⟩ : syracuseStep 2717525 = 15923) (by norm_num)
theorem B3585877 : Blo 1811607 3585877 := bbase (se 9 (by rfl) ⟨10505, by rfl⟩ : syracuseStep 3585877 = 21011) (by norm_num)
theorem B4077413 : Blo 1811607 4077413 := bbase (se 4 (by rfl) ⟨382257, by rfl⟩ : syracuseStep 4077413 = 764515) (by norm_num)
theorem B2717549 : Blo 1811607 2717549 := bbase (se 3 (by rfl) ⟨509540, by rfl⟩ : syracuseStep 2717549 = 1019081) (by norm_num)
theorem B10327925 : Blo 1811607 10327925 := bbase (se 5 (by rfl) ⟨484121, by rfl⟩ : syracuseStep 10327925 = 968243) (by norm_num)
theorem B2717573 : Blo 1811607 2717573 := bbase (se 4 (by rfl) ⟨254772, by rfl⟩ : syracuseStep 2717573 = 509545) (by norm_num)
theorem B4355981 : Blo 1811607 4355981 := bbase (se 3 (by rfl) ⟨816746, by rfl⟩ : syracuseStep 4355981 = 1633493) (by norm_num)
theorem B2717597 : Blo 1811607 2717597 := bbase (se 3 (by rfl) ⟨509549, by rfl⟩ : syracuseStep 2717597 = 1019099) (by norm_num)
theorem B4077485 : Blo 1811607 4077485 := bbase (se 3 (by rfl) ⟨764528, by rfl⟩ : syracuseStep 4077485 = 1529057) (by norm_num)
theorem B2717621 : Blo 1811607 2717621 := bbase (se 5 (by rfl) ⟨127388, by rfl⟩ : syracuseStep 2717621 = 254777) (by norm_num)
theorem B2717645 : Blo 1811607 2717645 := bbase (se 3 (by rfl) ⟨509558, by rfl⟩ : syracuseStep 2717645 = 1019117) (by norm_num)
theorem B2293753 : Blo 1811607 2293753 := bbase (se 2 (by rfl) ⟨860157, by rfl⟩ : syracuseStep 2293753 = 1720315) (by norm_num)
theorem B2717669 : Blo 1811607 2717669 := bbase (se 4 (by rfl) ⟨254781, by rfl⟩ : syracuseStep 2717669 = 509563) (by norm_num)
theorem B2177005 : Blo 1811607 2177005 := bbase (se 3 (by rfl) ⟨408188, by rfl⟩ : syracuseStep 2177005 = 816377) (by norm_num)
theorem B8706037 : Blo 1811607 8706037 := bbase (se 5 (by rfl) ⟨408095, by rfl⟩ : syracuseStep 8706037 = 816191) (by norm_num)
theorem B4077557 : Blo 1811607 4077557 := bbase (se 5 (by rfl) ⟨191135, by rfl⟩ : syracuseStep 4077557 = 382271) (by norm_num)
theorem B2717693 : Blo 1811607 2717693 := bbase (se 3 (by rfl) ⟨509567, by rfl⟩ : syracuseStep 2717693 = 1019135) (by norm_num)
theorem B2717717 : Blo 1811607 2717717 := bbase (se 6 (by rfl) ⟨63696, by rfl⟩ : syracuseStep 2717717 = 127393) (by norm_num)
theorem B6879269 : Blo 1811607 6879269 := bbase (se 4 (by rfl) ⟨644931, by rfl⟩ : syracuseStep 6879269 = 1289863) (by norm_num)
theorem B2717741 : Blo 1811607 2717741 := bbase (se 3 (by rfl) ⟨509576, by rfl⟩ : syracuseStep 2717741 = 1019153) (by norm_num)
theorem B4077629 : Blo 1811607 4077629 := bbase (se 3 (by rfl) ⟨764555, by rfl⟩ : syracuseStep 4077629 = 1529111) (by norm_num)
theorem B2717765 : Blo 1811607 2717765 := bbase (se 4 (by rfl) ⟨254790, by rfl⟩ : syracuseStep 2717765 = 509581) (by norm_num)
theorem B3536965 : Blo 1811607 3536965 := bbase (se 4 (by rfl) ⟨331590, by rfl⟩ : syracuseStep 3536965 = 663181) (by norm_num)
theorem B5158997 : Blo 1811607 5158997 := bbase (se 8 (by rfl) ⟨30228, by rfl⟩ : syracuseStep 5158997 = 60457) (by norm_num)
theorem B2717789 : Blo 1811607 2717789 := bbase (se 3 (by rfl) ⟨509585, by rfl⟩ : syracuseStep 2717789 = 1019171) (by norm_num)
theorem B8714341 : Blo 1811607 8714341 := bbase (se 4 (by rfl) ⟨816969, by rfl⟩ : syracuseStep 8714341 = 1633939) (by norm_num)
theorem B2717813 : Blo 1811607 2717813 := bbase (se 5 (by rfl) ⟨127397, by rfl⟩ : syracuseStep 2717813 = 254795) (by norm_num)
theorem B4077701 : Blo 1811607 4077701 := bbase (se 4 (by rfl) ⟨382284, by rfl⟩ : syracuseStep 4077701 = 764569) (by norm_num)
theorem B2717837 : Blo 1811607 2717837 := bbase (se 3 (by rfl) ⟨509594, by rfl⟩ : syracuseStep 2717837 = 1019189) (by norm_num)
theorem B2717861 : Blo 1811607 2717861 := bbase (se 4 (by rfl) ⟨254799, by rfl⟩ : syracuseStep 2717861 = 509599) (by norm_num)
theorem B3266725 : Blo 1811607 3266725 := bbase (se 4 (by rfl) ⟨306255, by rfl⟩ : syracuseStep 3266725 = 612511) (by norm_num)
theorem B9181349 : Blo 1811607 9181349 := bbase (se 4 (by rfl) ⟨860751, by rfl⟩ : syracuseStep 9181349 = 1721503) (by norm_num)
theorem B2717885 : Blo 1811607 2717885 := bbase (se 3 (by rfl) ⟨509603, by rfl⟩ : syracuseStep 2717885 = 1019207) (by norm_num)
theorem B4077773 : Blo 1811607 4077773 := bbase (se 3 (by rfl) ⟨764582, by rfl⟩ : syracuseStep 4077773 = 1529165) (by norm_num)
theorem B2717909 : Blo 1811607 2717909 := bbase (se 7 (by rfl) ⟨31850, by rfl⟩ : syracuseStep 2717909 = 63701) (by norm_num)
theorem B4585693 : Blo 1811607 4585693 := bbase (se 3 (by rfl) ⟨859817, by rfl⟩ : syracuseStep 4585693 = 1719635) (by norm_num)
theorem B4356317 : Blo 1811607 4356317 := bbase (se 3 (by rfl) ⟨816809, by rfl⟩ : syracuseStep 4356317 = 1633619) (by norm_num)
theorem B6117605 : Blo 1811607 6117605 := bbase (se 4 (by rfl) ⟨573525, by rfl⟩ : syracuseStep 6117605 = 1147051) (by norm_num)
theorem B2717933 : Blo 1811607 2717933 := bbase (se 3 (by rfl) ⟨509612, by rfl⟩ : syracuseStep 2717933 = 1019225) (by norm_num)
theorem B2717957 : Blo 1811607 2717957 := bbase (se 4 (by rfl) ⟨254808, by rfl⟩ : syracuseStep 2717957 = 509617) (by norm_num)
theorem B4077845 : Blo 1811607 4077845 := bbase (se 6 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 4077845 = 191149) (by norm_num)
theorem B17422613 : Blo 1811607 17422613 := bbase (se 6 (by rfl) ⟨408342, by rfl⟩ : syracuseStep 17422613 = 816685) (by norm_num)
theorem B2717981 : Blo 1811607 2717981 := bbase (se 3 (by rfl) ⟨509621, by rfl⟩ : syracuseStep 2717981 = 1019243) (by norm_num)
theorem B2177317 : Blo 1811607 2177317 := bbase (se 4 (by rfl) ⟨204123, by rfl⟩ : syracuseStep 2177317 = 408247) (by norm_num)
theorem B2718005 : Blo 1811607 2718005 := bbase (se 5 (by rfl) ⟨127406, by rfl⟩ : syracuseStep 2718005 = 254813) (by norm_num)
theorem B2038081 : Blo 1811607 2038081 := bbase (se 2 (by rfl) ⟨764280, by rfl⟩ : syracuseStep 2038081 = 1528561) (by norm_num)
theorem B4585805 : Blo 1811607 4585805 := bbase (se 3 (by rfl) ⟨859838, by rfl⟩ : syracuseStep 4585805 = 1719677) (by norm_num)
theorem B2718029 : Blo 1811607 2718029 := bbase (se 3 (by rfl) ⟨509630, by rfl⟩ : syracuseStep 2718029 = 1019261) (by norm_num)
theorem B3873109 : Blo 1811607 3873109 := bbase (se 10 (by rfl) ⟨5673, by rfl⟩ : syracuseStep 3873109 = 11347) (by norm_num)
theorem B4077917 : Blo 1811607 4077917 := bbase (se 3 (by rfl) ⟨764609, by rfl⟩ : syracuseStep 4077917 = 1529219) (by norm_num)
theorem B2038117 : Blo 1811607 2038117 := bbase (se 4 (by rfl) ⟨191073, by rfl⟩ : syracuseStep 2038117 = 382147) (by norm_num)
theorem B2718053 : Blo 1811607 2718053 := bbase (se 4 (by rfl) ⟨254817, by rfl⟩ : syracuseStep 2718053 = 509635) (by norm_num)
theorem B2718077 : Blo 1811607 2718077 := bbase (se 3 (by rfl) ⟨509639, by rfl⟩ : syracuseStep 2718077 = 1019279) (by norm_num)
theorem B2038153 : Blo 1811607 2038153 := bbase (se 2 (by rfl) ⟨764307, by rfl⟩ : syracuseStep 2038153 = 1528615) (by norm_num)
theorem B2718101 : Blo 1811607 2718101 := bbase (se 6 (by rfl) ⟨63705, by rfl⟩ : syracuseStep 2718101 = 127411) (by norm_num)
theorem B15702421 : Blo 1811607 15702421 := bbase (se 6 (by rfl) ⟨368025, by rfl⟩ : syracuseStep 15702421 = 736051) (by norm_num)
theorem B4077989 : Blo 1811607 4077989 := bbase (se 4 (by rfl) ⟨382311, by rfl⟩ : syracuseStep 4077989 = 764623) (by norm_num)
theorem B2038189 : Blo 1811607 2038189 := bbase (se 3 (by rfl) ⟨382160, by rfl⟩ : syracuseStep 2038189 = 764321) (by norm_num)
theorem B2718125 : Blo 1811607 2718125 := bbase (se 3 (by rfl) ⟨509648, by rfl⟩ : syracuseStep 2718125 = 1019297) (by norm_num)
theorem B7346629 : Blo 1811607 7346629 := bbase (se 4 (by rfl) ⟨688746, by rfl⟩ : syracuseStep 7346629 = 1377493) (by norm_num)
theorem B2718149 : Blo 1811607 2718149 := bbase (se 4 (by rfl) ⟨254826, by rfl⟩ : syracuseStep 2718149 = 509653) (by norm_num)
theorem B2038225 : Blo 1811607 2038225 := bbase (se 2 (by rfl) ⟨764334, by rfl⟩ : syracuseStep 2038225 = 1528669) (by norm_num)
theorem B3267029 : Blo 1811607 3267029 := bbase (se 7 (by rfl) ⟨38285, by rfl⟩ : syracuseStep 3267029 = 76571) (by norm_num)
theorem B2718173 : Blo 1811607 2718173 := bbase (se 3 (by rfl) ⟨509657, by rfl⟩ : syracuseStep 2718173 = 1019315) (by norm_num)
theorem B4078061 : Blo 1811607 4078061 := bbase (se 3 (by rfl) ⟨764636, by rfl⟩ : syracuseStep 4078061 = 1529273) (by norm_num)
theorem B2038261 : Blo 1811607 2038261 := bbase (se 5 (by rfl) ⟨95543, by rfl⟩ : syracuseStep 2038261 = 191087) (by norm_num)
theorem B2718197 : Blo 1811607 2718197 := bbase (se 5 (by rfl) ⟨127415, by rfl⟩ : syracuseStep 2718197 = 254831) (by norm_num)
theorem B4585997 : Blo 1811607 4585997 := bbase (se 3 (by rfl) ⟨859874, by rfl⟩ : syracuseStep 4585997 = 1719749) (by norm_num)
theorem B2718221 : Blo 1811607 2718221 := bbase (se 3 (by rfl) ⟨509666, by rfl⟩ : syracuseStep 2718221 = 1019333) (by norm_num)
theorem B2038297 : Blo 1811607 2038297 := bbase (se 2 (by rfl) ⟨764361, by rfl⟩ : syracuseStep 2038297 = 1528723) (by norm_num)
theorem B2718245 : Blo 1811607 2718245 := bbase (se 4 (by rfl) ⟨254835, by rfl⟩ : syracuseStep 2718245 = 509671) (by norm_num)
theorem B4078133 : Blo 1811607 4078133 := bbase (se 5 (by rfl) ⟨191162, by rfl⟩ : syracuseStep 4078133 = 382325) (by norm_num)
theorem B10467893 : Blo 1811607 10467893 := bbase (se 5 (by rfl) ⟨490682, by rfl⟩ : syracuseStep 10467893 = 981365) (by norm_num)
theorem B2038333 : Blo 1811607 2038333 := bbase (se 3 (by rfl) ⟨382187, by rfl⟩ : syracuseStep 2038333 = 764375) (by norm_num)
theorem B2718269 : Blo 1811607 2718269 := bbase (se 3 (by rfl) ⟨509675, by rfl⟩ : syracuseStep 2718269 = 1019351) (by norm_num)
theorem B9173573 : Blo 1811607 9173573 := bbase (se 4 (by rfl) ⟨860022, by rfl⟩ : syracuseStep 9173573 = 1720045) (by norm_num)
theorem B2718293 : Blo 1811607 2718293 := bbase (se 8 (by rfl) ⟨15927, by rfl⟩ : syracuseStep 2718293 = 31855) (by norm_num)
theorem B2038369 : Blo 1811607 2038369 := bbase (se 2 (by rfl) ⟨764388, by rfl⟩ : syracuseStep 2038369 = 1528777) (by norm_num)
theorem B4356709 : Blo 1811607 4356709 := bbase (se 4 (by rfl) ⟨408441, by rfl⟩ : syracuseStep 4356709 = 816883) (by norm_num)
theorem B2718317 : Blo 1811607 2718317 := bbase (se 3 (by rfl) ⟨509684, by rfl⟩ : syracuseStep 2718317 = 1019369) (by norm_num)
theorem B4078205 : Blo 1811607 4078205 := bbase (se 3 (by rfl) ⟨764663, by rfl⟩ : syracuseStep 4078205 = 1529327) (by norm_num)
theorem B2038405 : Blo 1811607 2038405 := bbase (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) (by norm_num)
theorem B2718341 : Blo 1811607 2718341 := bbase (se 4 (by rfl) ⟨254844, by rfl⟩ : syracuseStep 2718341 = 509689) (by norm_num)
theorem B6118037 : Blo 1811607 6118037 := bbase (se 6 (by rfl) ⟨143391, by rfl⟩ : syracuseStep 6118037 = 286783) (by norm_num)
theorem B2718365 : Blo 1811607 2718365 := bbase (se 3 (by rfl) ⟨509693, by rfl⟩ : syracuseStep 2718365 = 1019387) (by norm_num)
theorem B2038441 : Blo 1811607 2038441 := bbase (se 2 (by rfl) ⟨764415, by rfl⟩ : syracuseStep 2038441 = 1528831) (by norm_num)
theorem B2718389 : Blo 1811607 2718389 := bbase (se 5 (by rfl) ⟨127424, by rfl⟩ : syracuseStep 2718389 = 254849) (by norm_num)
theorem B4078277 : Blo 1811607 4078277 := bbase (se 4 (by rfl) ⟨382338, by rfl⟩ : syracuseStep 4078277 = 764677) (by norm_num)
theorem B2038477 : Blo 1811607 2038477 := bbase (se 3 (by rfl) ⟨382214, by rfl⟩ : syracuseStep 2038477 = 764429) (by norm_num)
theorem B2718413 : Blo 1811607 2718413 := bbase (se 3 (by rfl) ⟨509702, by rfl⟩ : syracuseStep 2718413 = 1019405) (by norm_num)
theorem B4897493 : Blo 1811607 4897493 := bbase (se 7 (by rfl) ⟨57392, by rfl⟩ : syracuseStep 4897493 = 114785) (by norm_num)
theorem B2718437 : Blo 1811607 2718437 := bbase (se 4 (by rfl) ⟨254853, by rfl⟩ : syracuseStep 2718437 = 509707) (by norm_num)
theorem B2038513 : Blo 1811607 2038513 := bbase (se 2 (by rfl) ⟨764442, by rfl⟩ : syracuseStep 2038513 = 1528885) (by norm_num)
theorem B2718461 : Blo 1811607 2718461 := bbase (se 3 (by rfl) ⟨509711, by rfl⟩ : syracuseStep 2718461 = 1019423) (by norm_num)
theorem B4078349 : Blo 1811607 4078349 := bbase (se 3 (by rfl) ⟨764690, by rfl⟩ : syracuseStep 4078349 = 1529381) (by norm_num)
theorem B23214869 : Blo 1811607 23214869 := bbase (se 6 (by rfl) ⟨544098, by rfl⟩ : syracuseStep 23214869 = 1088197) (by norm_num)
theorem B2038549 : Blo 1811607 2038549 := bbase (se 6 (by rfl) ⟨47778, by rfl⟩ : syracuseStep 2038549 = 95557) (by norm_num)
theorem B2718485 : Blo 1811607 2718485 := bbase (se 6 (by rfl) ⟨63714, by rfl⟩ : syracuseStep 2718485 = 127429) (by norm_num)
theorem B2718509 : Blo 1811607 2718509 := bbase (se 3 (by rfl) ⟨509720, by rfl⟩ : syracuseStep 2718509 = 1019441) (by norm_num)
theorem B2038585 : Blo 1811607 2038585 := bbase (se 2 (by rfl) ⟨764469, by rfl⟩ : syracuseStep 2038585 = 1528939) (by norm_num)
theorem B2718533 : Blo 1811607 2718533 := bbase (se 4 (by rfl) ⟨254862, by rfl⟩ : syracuseStep 2718533 = 509725) (by norm_num)
theorem B4078421 : Blo 1811607 4078421 := bbase (se 9 (by rfl) ⟨11948, by rfl⟩ : syracuseStep 4078421 = 23897) (by norm_num)
theorem B2038621 : Blo 1811607 2038621 := bbase (se 3 (by rfl) ⟨382241, by rfl⟩ : syracuseStep 2038621 = 764483) (by norm_num)
theorem B2718557 : Blo 1811607 2718557 := bbase (se 3 (by rfl) ⟨509729, by rfl⟩ : syracuseStep 2718557 = 1019459) (by norm_num)
theorem B4586341 : Blo 1811607 4586341 := bbase (se 4 (by rfl) ⟨429969, by rfl⟩ : syracuseStep 4586341 = 859939) (by norm_num)
theorem B2718581 : Blo 1811607 2718581 := bbase (se 5 (by rfl) ⟨127433, by rfl⟩ : syracuseStep 2718581 = 254867) (by norm_num)
theorem B2038657 : Blo 1811607 2038657 := bbase (se 2 (by rfl) ⟨764496, by rfl⟩ : syracuseStep 2038657 = 1528993) (by norm_num)
theorem B2718605 : Blo 1811607 2718605 := bbase (se 3 (by rfl) ⟨509738, by rfl⟩ : syracuseStep 2718605 = 1019477) (by norm_num)
theorem B4078493 : Blo 1811607 4078493 := bbase (se 3 (by rfl) ⟨764717, by rfl⟩ : syracuseStep 4078493 = 1529435) (by norm_num)
theorem B2038693 : Blo 1811607 2038693 := bbase (se 4 (by rfl) ⟨191127, by rfl⟩ : syracuseStep 2038693 = 382255) (by norm_num)
theorem B2718629 : Blo 1811607 2718629 := bbase (se 4 (by rfl) ⟨254871, by rfl⟩ : syracuseStep 2718629 = 509743) (by norm_num)
theorem B2718653 : Blo 1811607 2718653 := bbase (se 3 (by rfl) ⟨509747, by rfl⟩ : syracuseStep 2718653 = 1019495) (by norm_num)
theorem B2038729 : Blo 1811607 2038729 := bbase (se 2 (by rfl) ⟨764523, by rfl⟩ : syracuseStep 2038729 = 1529047) (by norm_num)
theorem B4586453 : Blo 1811607 4586453 := bbase (se 7 (by rfl) ⟨53747, by rfl⟩ : syracuseStep 4586453 = 107495) (by norm_num)
theorem B2718677 : Blo 1811607 2718677 := bbase (se 7 (by rfl) ⟨31859, by rfl⟩ : syracuseStep 2718677 = 63719) (by norm_num)
theorem B4078565 : Blo 1811607 4078565 := bbase (se 4 (by rfl) ⟨382365, by rfl⟩ : syracuseStep 4078565 = 764731) (by norm_num)
theorem B3439597 : Blo 1811607 3439597 := bbase (se 3 (by rfl) ⟨644924, by rfl⟩ : syracuseStep 3439597 = 1289849) (by norm_num)
theorem B2038765 : Blo 1811607 2038765 := bbase (se 3 (by rfl) ⟨382268, by rfl⟩ : syracuseStep 2038765 = 764537) (by norm_num)
theorem B2718701 : Blo 1811607 2718701 := bbase (se 3 (by rfl) ⟨509756, by rfl⟩ : syracuseStep 2718701 = 1019513) (by norm_num)
theorem B2718725 : Blo 1811607 2718725 := bbase (se 4 (by rfl) ⟨254880, by rfl⟩ : syracuseStep 2718725 = 509761) (by norm_num)
theorem B2038801 : Blo 1811607 2038801 := bbase (se 2 (by rfl) ⟨764550, by rfl⟩ : syracuseStep 2038801 = 1529101) (by norm_num)
theorem B2718749 : Blo 1811607 2718749 := bbase (se 3 (by rfl) ⟨509765, by rfl⟩ : syracuseStep 2718749 = 1019531) (by norm_num)
theorem B4078637 : Blo 1811607 4078637 := bbase (se 3 (by rfl) ⟨764744, by rfl⟩ : syracuseStep 4078637 = 1529489) (by norm_num)
theorem B2038837 : Blo 1811607 2038837 := bbase (se 5 (by rfl) ⟨95570, by rfl⟩ : syracuseStep 2038837 = 191141) (by norm_num)
theorem B2718773 : Blo 1811607 2718773 := bbase (se 5 (by rfl) ⟨127442, by rfl⟩ : syracuseStep 2718773 = 254885) (by norm_num)
theorem B6118469 : Blo 1811607 6118469 := bbase (se 4 (by rfl) ⟨573606, by rfl⟩ : syracuseStep 6118469 = 1147213) (by norm_num)
theorem B2718797 : Blo 1811607 2718797 := bbase (se 3 (by rfl) ⟨509774, by rfl⟩ : syracuseStep 2718797 = 1019549) (by norm_num)
theorem B2038873 : Blo 1811607 2038873 := bbase (se 2 (by rfl) ⟨764577, by rfl⟩ : syracuseStep 2038873 = 1529155) (by norm_num)
theorem B2718821 : Blo 1811607 2718821 := bbase (se 4 (by rfl) ⟨254889, by rfl⟩ : syracuseStep 2718821 = 509779) (by norm_num)
theorem B4078709 : Blo 1811607 4078709 := bbase (se 5 (by rfl) ⟨191189, by rfl⟩ : syracuseStep 4078709 = 382379) (by norm_num)
theorem B3439741 : Blo 1811607 3439741 := bbase (se 3 (by rfl) ⟨644951, by rfl⟩ : syracuseStep 3439741 = 1289903) (by norm_num)
theorem B2038909 : Blo 1811607 2038909 := bbase (se 3 (by rfl) ⟨382295, by rfl⟩ : syracuseStep 2038909 = 764591) (by norm_num)
theorem B2718845 : Blo 1811607 2718845 := bbase (se 3 (by rfl) ⟨509783, by rfl⟩ : syracuseStep 2718845 = 1019567) (by norm_num)
theorem B2292877 : Blo 1811607 2292877 := bbase (se 3 (by rfl) ⟨429914, by rfl⟩ : syracuseStep 2292877 = 859829) (by norm_num)
theorem B4586645 : Blo 1811607 4586645 := bbase (se 6 (by rfl) ⟨107499, by rfl⟩ : syracuseStep 4586645 = 214999) (by norm_num)
theorem B2718869 : Blo 1811607 2718869 := bbase (se 6 (by rfl) ⟨63723, by rfl⟩ : syracuseStep 2718869 = 127447) (by norm_num)
theorem B2038945 : Blo 1811607 2038945 := bbase (se 2 (by rfl) ⟨764604, by rfl⟩ : syracuseStep 2038945 = 1529209) (by norm_num)
theorem B2718893 : Blo 1811607 2718893 := bbase (se 3 (by rfl) ⟨509792, by rfl⟩ : syracuseStep 2718893 = 1019585) (by norm_num)
theorem B4078781 : Blo 1811607 4078781 := bbase (se 3 (by rfl) ⟨764771, by rfl⟩ : syracuseStep 4078781 = 1529543) (by norm_num)
theorem B7740613 : Blo 1811607 7740613 := bbase (se 4 (by rfl) ⟨725682, by rfl⟩ : syracuseStep 7740613 = 1451365) (by norm_num)
theorem B2038981 : Blo 1811607 2038981 := bbase (se 4 (by rfl) ⟨191154, by rfl⟩ : syracuseStep 2038981 = 382309) (by norm_num)
theorem B2718917 : Blo 1811607 2718917 := bbase (se 4 (by rfl) ⟨254898, by rfl⟩ : syracuseStep 2718917 = 509797) (by norm_num)
theorem B2718941 : Blo 1811607 2718941 := bbase (se 3 (by rfl) ⟨509801, by rfl⟩ : syracuseStep 2718941 = 1019603) (by norm_num)
theorem B2039017 : Blo 1811607 2039017 := bbase (se 2 (by rfl) ⟨764631, by rfl⟩ : syracuseStep 2039017 = 1529263) (by norm_num)
theorem B5160181 : Blo 1811607 5160181 := bbase (se 5 (by rfl) ⟨241883, by rfl⟩ : syracuseStep 5160181 = 483767) (by norm_num)
theorem B2718965 : Blo 1811607 2718965 := bbase (se 5 (by rfl) ⟨127451, by rfl⟩ : syracuseStep 2718965 = 254903) (by norm_num)
theorem B4078853 : Blo 1811607 4078853 := bbase (se 4 (by rfl) ⟨382392, by rfl⟩ : syracuseStep 4078853 = 764785) (by norm_num)
theorem B2039053 : Blo 1811607 2039053 := bbase (se 3 (by rfl) ⟨382322, by rfl⟩ : syracuseStep 2039053 = 764645) (by norm_num)
theorem B2718989 : Blo 1811607 2718989 := bbase (se 3 (by rfl) ⟨509810, by rfl⟩ : syracuseStep 2718989 = 1019621) (by norm_num)
theorem B3439901 : Blo 1811607 3439901 := bbase (se 3 (by rfl) ⟨644981, by rfl⟩ : syracuseStep 3439901 = 1289963) (by norm_num)
theorem B2719013 : Blo 1811607 2719013 := bbase (se 4 (by rfl) ⟨254907, by rfl⟩ : syracuseStep 2719013 = 509815) (by norm_num)
theorem B2039089 : Blo 1811607 2039089 := bbase (se 2 (by rfl) ⟨764658, by rfl⟩ : syracuseStep 2039089 = 1529317) (by norm_num)
theorem B2293049 : Blo 1811607 2293049 := bbase (se 2 (by rfl) ⟨859893, by rfl⟩ : syracuseStep 2293049 = 1719787) (by norm_num)
theorem B2719037 : Blo 1811607 2719037 := bbase (se 3 (by rfl) ⟨509819, by rfl⟩ : syracuseStep 2719037 = 1019639) (by norm_num)
theorem B2579789 : Blo 1811607 2579789 := bbase (se 3 (by rfl) ⟨483710, by rfl⟩ : syracuseStep 2579789 = 967421) (by norm_num)
theorem B4078925 : Blo 1811607 4078925 := bbase (se 3 (by rfl) ⟨764798, by rfl⟩ : syracuseStep 4078925 = 1529597) (by norm_num)
theorem B2039125 : Blo 1811607 2039125 := bbase (se 11 (by rfl) ⟨1493, by rfl⟩ : syracuseStep 2039125 = 2987) (by norm_num)
theorem B2719061 : Blo 1811607 2719061 := bbase (se 11 (by rfl) ⟨1991, by rfl⟩ : syracuseStep 2719061 = 3983) (by norm_num)
theorem B2719085 : Blo 1811607 2719085 := bbase (se 3 (by rfl) ⟨509828, by rfl⟩ : syracuseStep 2719085 = 1019657) (by norm_num)
theorem B2293105 : Blo 1811607 2293105 := bbase (se 2 (by rfl) ⟨859914, by rfl⟩ : syracuseStep 2293105 = 1719829) (by norm_num)
theorem B2039161 : Blo 1811607 2039161 := bbase (se 2 (by rfl) ⟨764685, by rfl⟩ : syracuseStep 2039161 = 1529371) (by norm_num)
theorem B3267965 : Blo 1811607 3267965 := bbase (se 3 (by rfl) ⟨612743, by rfl⟩ : syracuseStep 3267965 = 1225487) (by norm_num)
theorem B2719109 : Blo 1811607 2719109 := bbase (se 4 (by rfl) ⟨254916, by rfl⟩ : syracuseStep 2719109 = 509833) (by norm_num)
theorem B5160341 : Blo 1811607 5160341 := bbase (se 6 (by rfl) ⟨120945, by rfl⟩ : syracuseStep 5160341 = 241891) (by norm_num)
theorem B4078997 : Blo 1811607 4078997 := bbase (se 6 (by rfl) ⟨95601, by rfl⟩ : syracuseStep 4078997 = 191203) (by norm_num)
theorem B2039197 : Blo 1811607 2039197 := bbase (se 3 (by rfl) ⟨382349, by rfl⟩ : syracuseStep 2039197 = 764699) (by norm_num)
theorem B2719133 : Blo 1811607 2719133 := bbase (se 3 (by rfl) ⟨509837, by rfl⟩ : syracuseStep 2719133 = 1019675) (by norm_num)
theorem B3440045 : Blo 1811607 3440045 := bbase (se 3 (by rfl) ⟨645008, by rfl⟩ : syracuseStep 3440045 = 1290017) (by norm_num)
theorem B2719157 : Blo 1811607 2719157 := bbase (se 5 (by rfl) ⟨127460, by rfl⟩ : syracuseStep 2719157 = 254921) (by norm_num)
theorem B2039233 : Blo 1811607 2039233 := bbase (se 2 (by rfl) ⟨764712, by rfl⟩ : syracuseStep 2039233 = 1529425) (by norm_num)
theorem B2719181 : Blo 1811607 2719181 := bbase (se 3 (by rfl) ⟨509846, by rfl⟩ : syracuseStep 2719181 = 1019693) (by norm_num)
theorem B2293201 : Blo 1811607 2293201 := bbase (se 2 (by rfl) ⟨859950, by rfl⟩ : syracuseStep 2293201 = 1719901) (by norm_num)
theorem B4079069 : Blo 1811607 4079069 := bbase (se 3 (by rfl) ⟨764825, by rfl⟩ : syracuseStep 4079069 = 1529651) (by norm_num)
theorem B2039269 : Blo 1811607 2039269 := bbase (se 4 (by rfl) ⟨191181, by rfl⟩ : syracuseStep 2039269 = 382363) (by norm_num)
theorem B2719205 : Blo 1811607 2719205 := bbase (se 4 (by rfl) ⟨254925, by rfl⟩ : syracuseStep 2719205 = 509851) (by norm_num)
theorem B4586989 : Blo 1811607 4586989 := bbase (se 3 (by rfl) ⟨860060, by rfl⟩ : syracuseStep 4586989 = 1720121) (by norm_num)
theorem B6118901 : Blo 1811607 6118901 := bbase (se 5 (by rfl) ⟨286823, by rfl⟩ : syracuseStep 6118901 = 573647) (by norm_num)
theorem B2719229 : Blo 1811607 2719229 := bbase (se 3 (by rfl) ⟨509855, by rfl⟩ : syracuseStep 2719229 = 1019711) (by norm_num)
theorem B2039305 : Blo 1811607 2039305 := bbase (se 2 (by rfl) ⟨764739, by rfl⟩ : syracuseStep 2039305 = 1529479) (by norm_num)
theorem B2719253 : Blo 1811607 2719253 := bbase (se 6 (by rfl) ⟨63732, by rfl⟩ : syracuseStep 2719253 = 127465) (by norm_num)
theorem B4079141 : Blo 1811607 4079141 := bbase (se 4 (by rfl) ⟨382419, by rfl⟩ : syracuseStep 4079141 = 764839) (by norm_num)
theorem B2039341 : Blo 1811607 2039341 := bbase (se 3 (by rfl) ⟨382376, by rfl⟩ : syracuseStep 2039341 = 764753) (by norm_num)
theorem B2719277 : Blo 1811607 2719277 := bbase (se 3 (by rfl) ⟨509864, by rfl⟩ : syracuseStep 2719277 = 1019729) (by norm_num)
theorem B5103173 : Blo 1811607 5103173 := bbase (se 4 (by rfl) ⟨478422, by rfl⟩ : syracuseStep 5103173 = 956845) (by norm_num)
theorem B2719301 : Blo 1811607 2719301 := bbase (se 4 (by rfl) ⟨254934, by rfl⟩ : syracuseStep 2719301 = 509869) (by norm_num)
theorem B2039377 : Blo 1811607 2039377 := bbase (se 2 (by rfl) ⟨764766, by rfl⟩ : syracuseStep 2039377 = 1529533) (by norm_num)
theorem B4587101 : Blo 1811607 4587101 := bbase (se 3 (by rfl) ⟨860081, by rfl⟩ : syracuseStep 4587101 = 1720163) (by norm_num)
theorem B2719325 : Blo 1811607 2719325 := bbase (se 3 (by rfl) ⟨509873, by rfl⟩ : syracuseStep 2719325 = 1019747) (by norm_num)
theorem B4079213 : Blo 1811607 4079213 := bbase (se 3 (by rfl) ⟨764852, by rfl⟩ : syracuseStep 4079213 = 1529705) (by norm_num)
theorem B2039413 : Blo 1811607 2039413 := bbase (se 5 (by rfl) ⟨95597, by rfl⟩ : syracuseStep 2039413 = 191195) (by norm_num)
theorem B2719349 : Blo 1811607 2719349 := bbase (se 5 (by rfl) ⟨127469, by rfl⟩ : syracuseStep 2719349 = 254939) (by norm_num)
theorem B2293373 : Blo 1811607 2293373 := bbase (se 3 (by rfl) ⟨430007, by rfl⟩ : syracuseStep 2293373 = 860015) (by norm_num)
theorem B5160581 : Blo 1811607 5160581 := bbase (se 4 (by rfl) ⟨483804, by rfl⟩ : syracuseStep 5160581 = 967609) (by norm_num)
theorem B2719373 : Blo 1811607 2719373 := bbase (se 3 (by rfl) ⟨509882, by rfl⟩ : syracuseStep 2719373 = 1019765) (by norm_num)
theorem B2449045 : Blo 1811607 2449045 := bbase (se 6 (by rfl) ⟨57399, by rfl⟩ : syracuseStep 2449045 = 114799) (by norm_num)
theorem B2039449 : Blo 1811607 2039449 := bbase (se 2 (by rfl) ⟨764793, by rfl⟩ : syracuseStep 2039449 = 1529587) (by norm_num)
theorem B2719397 : Blo 1811607 2719397 := bbase (se 4 (by rfl) ⟨254943, by rfl⟩ : syracuseStep 2719397 = 509887) (by norm_num)
theorem B2293429 : Blo 1811607 2293429 := bbase (se 5 (by rfl) ⟨107504, by rfl⟩ : syracuseStep 2293429 = 215009) (by norm_num)
theorem B4079285 : Blo 1811607 4079285 := bbase (se 5 (by rfl) ⟨191216, by rfl⟩ : syracuseStep 4079285 = 382433) (by norm_num)
theorem B2039485 : Blo 1811607 2039485 := bbase (se 3 (by rfl) ⟨382403, by rfl⟩ : syracuseStep 2039485 = 764807) (by norm_num)
theorem B2719421 : Blo 1811607 2719421 := bbase (se 3 (by rfl) ⟨509891, by rfl⟩ : syracuseStep 2719421 = 1019783) (by norm_num)
theorem B3440333 : Blo 1811607 3440333 := bbase (se 3 (by rfl) ⟨645062, by rfl⟩ : syracuseStep 3440333 = 1290125) (by norm_num)
theorem B2719445 : Blo 1811607 2719445 := bbase (se 7 (by rfl) ⟨31868, by rfl⟩ : syracuseStep 2719445 = 63737) (by norm_num)
theorem B2039521 : Blo 1811607 2039521 := bbase (se 2 (by rfl) ⟨764820, by rfl⟩ : syracuseStep 2039521 = 1529641) (by norm_num)
theorem B2719469 : Blo 1811607 2719469 := bbase (se 3 (by rfl) ⟨509900, by rfl⟩ : syracuseStep 2719469 = 1019801) (by norm_num)
theorem B4079357 : Blo 1811607 4079357 := bbase (se 3 (by rfl) ⟨764879, by rfl⟩ : syracuseStep 4079357 = 1529759) (by norm_num)
theorem B2039557 : Blo 1811607 2039557 := bbase (se 4 (by rfl) ⟨191208, by rfl⟩ : syracuseStep 2039557 = 382417) (by norm_num)
theorem B2719493 : Blo 1811607 2719493 := bbase (se 4 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 2719493 = 509905) (by norm_num)
theorem B2293525 : Blo 1811607 2293525 := bbase (se 6 (by rfl) ⟨53754, by rfl⟩ : syracuseStep 2293525 = 107509) (by norm_num)
theorem B4587293 : Blo 1811607 4587293 := bbase (se 3 (by rfl) ⟨860117, by rfl⟩ : syracuseStep 4587293 = 1720235) (by norm_num)
theorem B2719517 : Blo 1811607 2719517 := bbase (se 3 (by rfl) ⟨509909, by rfl⟩ : syracuseStep 2719517 = 1019819) (by norm_num)
theorem B2039593 : Blo 1811607 2039593 := bbase (se 2 (by rfl) ⟨764847, by rfl⟩ : syracuseStep 2039593 = 1529695) (by norm_num)
theorem B4415285 : Blo 1811607 4415285 := bbase (se 5 (by rfl) ⟨206966, by rfl⟩ : syracuseStep 4415285 = 413933) (by norm_num)
theorem B2719541 : Blo 1811607 2719541 := bbase (se 5 (by rfl) ⟨127478, by rfl⟩ : syracuseStep 2719541 = 254957) (by norm_num)
theorem B5160773 : Blo 1811607 5160773 := bbase (se 4 (by rfl) ⟨483822, by rfl⟩ : syracuseStep 5160773 = 967645) (by norm_num)
theorem B4079429 : Blo 1811607 4079429 := bbase (se 4 (by rfl) ⟨382446, by rfl⟩ : syracuseStep 4079429 = 764893) (by norm_num)
theorem B2039629 : Blo 1811607 2039629 := bbase (se 3 (by rfl) ⟨382430, by rfl⟩ : syracuseStep 2039629 = 764861) (by norm_num)
theorem B2719565 : Blo 1811607 2719565 := bbase (se 3 (by rfl) ⟨509918, by rfl⟩ : syracuseStep 2719565 = 1019837) (by norm_num)
theorem B9174869 : Blo 1811607 9174869 := bbase (se 9 (by rfl) ⟨26879, by rfl⟩ : syracuseStep 9174869 = 53759) (by norm_num)
theorem B12910421 : Blo 1811607 12910421 := bbase (se 9 (by rfl) ⟨37823, by rfl⟩ : syracuseStep 12910421 = 75647) (by norm_num)
theorem B3440485 : Blo 1811607 3440485 := bbase (se 4 (by rfl) ⟨322545, by rfl⟩ : syracuseStep 3440485 = 645091) (by norm_num)
theorem B2719589 : Blo 1811607 2719589 := bbase (se 4 (by rfl) ⟨254961, by rfl⟩ : syracuseStep 2719589 = 509923) (by norm_num)
theorem B2039665 : Blo 1811607 2039665 := bbase (se 2 (by rfl) ⟨764874, by rfl⟩ : syracuseStep 2039665 = 1529749) (by norm_num)
theorem B2580341 : Blo 1811607 2580341 := bbase (se 5 (by rfl) ⟨120953, by rfl⟩ : syracuseStep 2580341 = 241907) (by norm_num)
theorem B2719613 : Blo 1811607 2719613 := bbase (se 3 (by rfl) ⟨509927, by rfl⟩ : syracuseStep 2719613 = 1019855) (by norm_num)
theorem B4079501 : Blo 1811607 4079501 := bbase (se 3 (by rfl) ⟨764906, by rfl⟩ : syracuseStep 4079501 = 1529813) (by norm_num)
theorem B11616149 : Blo 1811607 11616149 := bbase (se 6 (by rfl) ⟨272253, by rfl⟩ : syracuseStep 11616149 = 544507) (by norm_num)
theorem B2039701 : Blo 1811607 2039701 := bbase (se 6 (by rfl) ⟨47805, by rfl⟩ : syracuseStep 2039701 = 95611) (by norm_num)
theorem B2719637 : Blo 1811607 2719637 := bbase (se 6 (by rfl) ⟨63741, by rfl⟩ : syracuseStep 2719637 = 127483) (by norm_num)
theorem B6119333 : Blo 1811607 6119333 := bbase (se 4 (by rfl) ⟨573687, by rfl⟩ : syracuseStep 6119333 = 1147375) (by norm_num)
theorem B2719661 : Blo 1811607 2719661 := bbase (se 3 (by rfl) ⟨509936, by rfl⟩ : syracuseStep 2719661 = 1019873) (by norm_num)
theorem B2039737 : Blo 1811607 2039737 := bbase (se 2 (by rfl) ⟨764901, by rfl⟩ : syracuseStep 2039737 = 1529803) (by norm_num)
theorem B2293697 : Blo 1811607 2293697 := bbase (se 2 (by rfl) ⟨860136, by rfl⟩ : syracuseStep 2293697 = 1720273) (by norm_num)
theorem B2719685 : Blo 1811607 2719685 := bbase (se 4 (by rfl) ⟨254970, by rfl⟩ : syracuseStep 2719685 = 509941) (by norm_num)
theorem B4079573 : Blo 1811607 4079573 := bbase (se 7 (by rfl) ⟨47807, by rfl⟩ : syracuseStep 4079573 = 95615) (by norm_num)
theorem B2039773 : Blo 1811607 2039773 := bbase (se 3 (by rfl) ⟨382457, by rfl⟩ : syracuseStep 2039773 = 764915) (by norm_num)
theorem B2719709 : Blo 1811607 2719709 := bbase (se 3 (by rfl) ⟨509945, by rfl⟩ : syracuseStep 2719709 = 1019891) (by norm_num)
theorem B2719733 : Blo 1811607 2719733 := bbase (se 5 (by rfl) ⟨127487, by rfl⟩ : syracuseStep 2719733 = 254975) (by norm_num)
theorem B2719745 : Blo 1811607 2719745 := bstep (se 2 (by rfl) ⟨1019904, by rfl⟩ : syracuseStep 2719745 = 2039809) B2039809
theorem B2326531 : Blo 1811607 2326531 := bstep (se 1 (by rfl) ⟨1744898, by rfl⟩ : syracuseStep 2326531 = 3489797) B3489797
theorem B6119441 : Blo 1811607 6119441 := bstep (se 2 (by rfl) ⟨2294790, by rfl⟩ : syracuseStep 6119441 = 4589581) B4589581
theorem B2719763 : Blo 1811607 2719763 := bstep (se 1 (by rfl) ⟨2039822, by rfl⟩ : syracuseStep 2719763 = 4079645) B4079645
theorem B2039827 : Blo 1811607 2039827 := bstep (se 1 (by rfl) ⟨1529870, by rfl⟩ : syracuseStep 2039827 = 3059741) B3059741
theorem B2719793 : Blo 1811607 2719793 := bstep (se 2 (by rfl) ⟨1019922, by rfl⟩ : syracuseStep 2719793 = 2039845) B2039845
theorem B4587587 : Blo 1811607 4587587 := bstep (se 1 (by rfl) ⟨3440690, by rfl⟩ : syracuseStep 4587587 = 6881381) B6881381
theorem B2719811 : Blo 1811607 2719811 := bstep (se 1 (by rfl) ⟨2039858, by rfl⟩ : syracuseStep 2719811 = 4079717) B4079717
theorem B2719841 : Blo 1811607 2719841 := bstep (se 2 (by rfl) ⟨1019940, by rfl⟩ : syracuseStep 2719841 = 2039881) B2039881
theorem B2293859 : Blo 1811607 2293859 := bstep (se 1 (by rfl) ⟨1720394, by rfl⟩ : syracuseStep 2293859 = 3440789) B3440789
theorem B2719859 : Blo 1811607 2719859 := bstep (se 1 (by rfl) ⟨2039894, by rfl⟩ : syracuseStep 2719859 = 4079789) B4079789
theorem B2719889 : Blo 1811607 2719889 := bstep (se 2 (by rfl) ⟨1019958, by rfl⟩ : syracuseStep 2719889 = 2039917) B2039917
theorem B2719907 : Blo 1811607 2719907 := bstep (se 1 (by rfl) ⟨2039930, by rfl⟩ : syracuseStep 2719907 = 4079861) B4079861
theorem B2039971 : Blo 1811607 2039971 := bstep (se 1 (by rfl) ⟨1529978, by rfl⟩ : syracuseStep 2039971 = 3059957) B3059957
theorem B2719937 : Blo 1811607 2719937 := bstep (se 2 (by rfl) ⟨1019976, by rfl⟩ : syracuseStep 2719937 = 2039953) B2039953
theorem B4079825 : Blo 1811607 4079825 := bstep (se 2 (by rfl) ⟨1529934, by rfl⟩ : syracuseStep 4079825 = 3059869) B3059869
theorem B2719955 : Blo 1811607 2719955 := bstep (se 1 (by rfl) ⟨2039966, by rfl⟩ : syracuseStep 2719955 = 4079933) B4079933
theorem B26493155 : Blo 1811607 26493155 := bstep (se 1 (by rfl) ⟨19869866, by rfl⟩ : syracuseStep 26493155 = 39739733) B39739733
theorem B4079843 : Blo 1811607 4079843 := bstep (se 1 (by rfl) ⟨3059882, by rfl⟩ : syracuseStep 4079843 = 6119765) B6119765
theorem B2719985 : Blo 1811607 2719985 := bstep (se 2 (by rfl) ⟨1019994, by rfl⟩ : syracuseStep 2719985 = 2039989) B2039989
theorem B4587779 : Blo 1811607 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B2720003 : Blo 1811607 2720003 := bstep (se 1 (by rfl) ⟨2040002, by rfl⟩ : syracuseStep 2720003 = 4080005) B4080005
theorem B9928973 : Blo 1811607 9928973 := bstep (se 3 (by rfl) ⟨1861682, by rfl⟩ : syracuseStep 9928973 = 3723365) B3723365
theorem B5161229 : Blo 1811607 5161229 := bstep (se 3 (by rfl) ⟨967730, by rfl⟩ : syracuseStep 5161229 = 1935461) B1935461
theorem B2720033 : Blo 1811607 2720033 := bstep (se 2 (by rfl) ⟨1020012, by rfl⟩ : syracuseStep 2720033 = 2040025) B2040025
theorem B2720051 : Blo 1811607 2720051 := bstep (se 1 (by rfl) ⟨2040038, by rfl⟩ : syracuseStep 2720051 = 4080077) B4080077
theorem B2040115 : Blo 1811607 2040115 := bstep (se 1 (by rfl) ⟨1530086, by rfl⟩ : syracuseStep 2040115 = 3060173) B3060173
theorem B2720081 : Blo 1811607 2720081 := bstep (se 2 (by rfl) ⟨1020030, by rfl⟩ : syracuseStep 2720081 = 2040061) B2040061
theorem B10322275 : Blo 1811607 10322275 := bstep (se 1 (by rfl) ⟨7741706, by rfl⟩ : syracuseStep 10322275 = 15483413) B15483413
theorem B2720099 : Blo 1811607 2720099 := bstep (se 1 (by rfl) ⟨2040074, by rfl⟩ : syracuseStep 2720099 = 4080149) B4080149
theorem B2720129 : Blo 1811607 2720129 := bstep (se 2 (by rfl) ⟨1020048, by rfl⟩ : syracuseStep 2720129 = 2040097) B2040097
theorem B2720147 : Blo 1811607 2720147 := bstep (se 1 (by rfl) ⟨2040110, by rfl⟩ : syracuseStep 2720147 = 4080221) B4080221
theorem B6881699 : Blo 1811607 6881699 := bstep (se 1 (by rfl) ⟨5161274, by rfl⟩ : syracuseStep 6881699 = 10322549) B10322549
theorem B2720177 : Blo 1811607 2720177 := bstep (se 2 (by rfl) ⟨1020066, by rfl⟩ : syracuseStep 2720177 = 2040133) B2040133
theorem B5161411 : Blo 1811607 5161411 := bstep (se 1 (by rfl) ⟨3871058, by rfl⟩ : syracuseStep 5161411 = 7742117) B7742117
theorem B2720195 : Blo 1811607 2720195 := bstep (se 1 (by rfl) ⟨2040146, by rfl⟩ : syracuseStep 2720195 = 4080293) B4080293
theorem B2040259 : Blo 1811607 2040259 := bstep (se 1 (by rfl) ⟨1530194, by rfl⟩ : syracuseStep 2040259 = 3060389) B3060389
theorem B2720225 : Blo 1811607 2720225 := bstep (se 2 (by rfl) ⟨1020084, by rfl⟩ : syracuseStep 2720225 = 2040169) B2040169
theorem B5161457 : Blo 1811607 5161457 := bstep (se 2 (by rfl) ⟨1935546, by rfl⟩ : syracuseStep 5161457 = 3871093) B3871093
theorem B4080113 : Blo 1811607 4080113 := bstep (se 2 (by rfl) ⟨1530042, by rfl⟩ : syracuseStep 4080113 = 3060085) B3060085
theorem B2580979 : Blo 1811607 2580979 := bstep (se 1 (by rfl) ⟨1935734, by rfl⟩ : syracuseStep 2580979 = 3871469) B3871469
theorem B2720243 : Blo 1811607 2720243 := bstep (se 1 (by rfl) ⟨2040182, by rfl⟩ : syracuseStep 2720243 = 4080365) B4080365
theorem B4080131 : Blo 1811607 4080131 := bstep (se 1 (by rfl) ⟨3060098, by rfl⟩ : syracuseStep 4080131 = 6120197) B6120197
theorem B2720273 : Blo 1811607 2720273 := bstep (se 2 (by rfl) ⟨1020102, by rfl⟩ : syracuseStep 2720273 = 2040205) B2040205
theorem B2720291 : Blo 1811607 2720291 := bstep (se 1 (by rfl) ⟨2040218, by rfl⟩ : syracuseStep 2720291 = 4080437) B4080437
theorem B6119981 : Blo 1811607 6119981 := bstep (se 3 (by rfl) ⟨1147496, by rfl⟩ : syracuseStep 6119981 = 2294993) B2294993
theorem B2720321 : Blo 1811607 2720321 := bstep (se 2 (by rfl) ⟨1020120, by rfl⟩ : syracuseStep 2720321 = 2040241) B2040241
theorem B2720339 : Blo 1811607 2720339 := bstep (se 1 (by rfl) ⟨2040254, by rfl⟩ : syracuseStep 2720339 = 4080509) B4080509
theorem B6120035 : Blo 1811607 6120035 := bstep (se 1 (by rfl) ⟨4590026, by rfl⟩ : syracuseStep 6120035 = 9180053) B9180053
theorem B2720369 : Blo 1811607 2720369 := bstep (se 2 (by rfl) ⟨1020138, by rfl⟩ : syracuseStep 2720369 = 2040277) B2040277
theorem B2720387 : Blo 1811607 2720387 := bstep (se 1 (by rfl) ⟨2040290, by rfl⟩ : syracuseStep 2720387 = 4080581) B4080581
theorem B11608717 : Blo 1811607 11608717 := bstep (se 3 (by rfl) ⟨2176634, by rfl⟩ : syracuseStep 11608717 = 4353269) B4353269
theorem B4080401 : Blo 1811607 4080401 := bstep (se 2 (by rfl) ⟨1530150, by rfl⟩ : syracuseStep 4080401 = 3060301) B3060301
theorem B2294563 : Blo 1811607 2294563 := bstep (se 1 (by rfl) ⟨1720922, by rfl⟩ : syracuseStep 2294563 = 3441845) B3441845
theorem B4080419 : Blo 1811607 4080419 := bstep (se 1 (by rfl) ⟨3060314, by rfl⟩ : syracuseStep 4080419 = 6120629) B6120629
theorem B3441457 : Blo 1811607 3441457 := bstep (se 2 (by rfl) ⟨1290546, by rfl⟩ : syracuseStep 3441457 = 2581093) B2581093
theorem B10322801 : Blo 1811607 10322801 := bstep (se 2 (by rfl) ⟨3871050, by rfl⟩ : syracuseStep 10322801 = 7742101) B7742101
theorem B6120305 : Blo 1811607 6120305 := bstep (se 2 (by rfl) ⟨2295114, by rfl⟩ : syracuseStep 6120305 = 4590229) B4590229
theorem B2294659 : Blo 1811607 2294659 := bstep (se 1 (by rfl) ⟨1720994, by rfl⟩ : syracuseStep 2294659 = 3441989) B3441989
theorem B6882353 : Blo 1811607 6882353 := bstep (se 2 (by rfl) ⟨2580882, by rfl⟩ : syracuseStep 6882353 = 5161765) B5161765
theorem B2450515 : Blo 1811607 2450515 := bstep (se 1 (by rfl) ⟨1837886, by rfl⟩ : syracuseStep 2450515 = 3675773) B3675773
theorem B2450531 : Blo 1811607 2450531 := bstep (se 1 (by rfl) ⟨1837898, by rfl⟩ : syracuseStep 2450531 = 3675797) B3675797
theorem B1811619 : Blo 1811607 1811619 := bstep (se 1 (by rfl) ⟨1358714, by rfl⟩ : syracuseStep 1811619 = 2717429) B2717429
theorem B4588721 : Blo 1811607 4588721 := bstep (se 2 (by rfl) ⟨1720770, by rfl⟩ : syracuseStep 4588721 = 3441541) B3441541
theorem B1811635 : Blo 1811607 1811635 := bstep (se 1 (by rfl) ⟨1358726, by rfl⟩ : syracuseStep 1811635 = 2717453) B2717453
theorem B1811651 : Blo 1811607 1811651 := bstep (se 1 (by rfl) ⟨1358738, by rfl⟩ : syracuseStep 1811651 = 2717477) B2717477
theorem B1811667 : Blo 1811607 1811667 := bstep (se 1 (by rfl) ⟨1358750, by rfl⟩ : syracuseStep 1811667 = 2717501) B2717501
theorem B1811683 : Blo 1811607 1811683 := bstep (se 1 (by rfl) ⟨1358762, by rfl⟩ : syracuseStep 1811683 = 2717525) B2717525
theorem B4588771 : Blo 1811607 4588771 := bstep (se 1 (by rfl) ⟨3441578, by rfl⟩ : syracuseStep 4588771 = 6883157) B6883157
theorem B8062193 : Blo 1811607 8062193 := bstep (se 2 (by rfl) ⟨3023322, by rfl⟩ : syracuseStep 8062193 = 6046645) B6046645
theorem B1811699 : Blo 1811607 1811699 := bstep (se 1 (by rfl) ⟨1358774, by rfl⟩ : syracuseStep 1811699 = 2717549) B2717549
theorem B1811715 : Blo 1811607 1811715 := bstep (se 1 (by rfl) ⟨1358786, by rfl⟩ : syracuseStep 1811715 = 2717573) B2717573
theorem B1811731 : Blo 1811607 1811731 := bstep (se 1 (by rfl) ⟨1358798, by rfl⟩ : syracuseStep 1811731 = 2717597) B2717597
theorem B1811747 : Blo 1811607 1811747 := bstep (se 1 (by rfl) ⟨1358810, by rfl⟩ : syracuseStep 1811747 = 2717621) B2717621
theorem B1811763 : Blo 1811607 1811763 := bstep (se 1 (by rfl) ⟨1358822, by rfl⟩ : syracuseStep 1811763 = 2717645) B2717645
theorem B1811779 : Blo 1811607 1811779 := bstep (se 1 (by rfl) ⟨1358834, by rfl⟩ : syracuseStep 1811779 = 2717669) B2717669
theorem B1811795 : Blo 1811607 1811795 := bstep (se 1 (by rfl) ⟨1358846, by rfl⟩ : syracuseStep 1811795 = 2717693) B2717693
theorem B1811811 : Blo 1811607 1811811 := bstep (se 1 (by rfl) ⟨1358858, by rfl⟩ : syracuseStep 1811811 = 2717717) B2717717
theorem B4588913 : Blo 1811607 4588913 := bstep (se 2 (by rfl) ⟨1720842, by rfl⟩ : syracuseStep 4588913 = 3441685) B3441685
theorem B1811827 : Blo 1811607 1811827 := bstep (se 1 (by rfl) ⟨1358870, by rfl⟩ : syracuseStep 1811827 = 2717741) B2717741
theorem B2295155 : Blo 1811607 2295155 := bstep (se 1 (by rfl) ⟨1721366, by rfl⟩ : syracuseStep 2295155 = 3442733) B3442733
theorem B1811843 : Blo 1811607 1811843 := bstep (se 1 (by rfl) ⟨1358882, by rfl⟩ : syracuseStep 1811843 = 2717765) B2717765
theorem B6120845 : Blo 1811607 6120845 := bstep (se 3 (by rfl) ⟨1147658, by rfl⟩ : syracuseStep 6120845 = 2295317) B2295317
theorem B1811859 : Blo 1811607 1811859 := bstep (se 1 (by rfl) ⟨1358894, by rfl⟩ : syracuseStep 1811859 = 2717789) B2717789
theorem B1811875 : Blo 1811607 1811875 := bstep (se 1 (by rfl) ⟨1358906, by rfl⟩ : syracuseStep 1811875 = 2717813) B2717813
theorem B1811891 : Blo 1811607 1811891 := bstep (se 1 (by rfl) ⟨1358918, by rfl⟩ : syracuseStep 1811891 = 2717837) B2717837
theorem B1811907 : Blo 1811607 1811907 := bstep (se 1 (by rfl) ⟨1358930, by rfl⟩ : syracuseStep 1811907 = 2717861) B2717861
theorem B6120899 : Blo 1811607 6120899 := bstep (se 1 (by rfl) ⟨4590674, by rfl⟩ : syracuseStep 6120899 = 9181349) B9181349
theorem B1811923 : Blo 1811607 1811923 := bstep (se 1 (by rfl) ⟨1358942, by rfl⟩ : syracuseStep 1811923 = 2717885) B2717885
theorem B1811939 : Blo 1811607 1811939 := bstep (se 1 (by rfl) ⟨1358954, by rfl⟩ : syracuseStep 1811939 = 2717909) B2717909
theorem B1811955 : Blo 1811607 1811955 := bstep (se 1 (by rfl) ⟨1358966, by rfl⟩ : syracuseStep 1811955 = 2717933) B2717933
theorem B1811971 : Blo 1811607 1811971 := bstep (se 1 (by rfl) ⟨1358978, by rfl⟩ : syracuseStep 1811971 = 2717957) B2717957
theorem B13608461 : Blo 1811607 13608461 := bstep (se 3 (by rfl) ⟨2551586, by rfl⟩ : syracuseStep 13608461 = 5103173) B5103173
theorem B3057169 : Blo 1811607 3057169 := bstep (se 2 (by rfl) ⟨1146438, by rfl⟩ : syracuseStep 3057169 = 2292877) B2292877
theorem B1811987 : Blo 1811607 1811987 := bstep (se 1 (by rfl) ⟨1358990, by rfl⟩ : syracuseStep 1811987 = 2717981) B2717981
theorem B1812003 : Blo 1811607 1812003 := bstep (se 1 (by rfl) ⟨1359002, by rfl⟩ : syracuseStep 1812003 = 2718005) B2718005
theorem B3057203 : Blo 1811607 3057203 := bstep (se 1 (by rfl) ⟨2292902, by rfl⟩ : syracuseStep 3057203 = 4585805) B4585805
theorem B1812019 : Blo 1811607 1812019 := bstep (se 1 (by rfl) ⟨1359014, by rfl⟩ : syracuseStep 1812019 = 2718029) B2718029
theorem B1812035 : Blo 1811607 1812035 := bstep (se 1 (by rfl) ⟨1359026, by rfl⟩ : syracuseStep 1812035 = 2718053) B2718053
theorem B1812051 : Blo 1811607 1812051 := bstep (se 1 (by rfl) ⟨1359038, by rfl⟩ : syracuseStep 1812051 = 2718077) B2718077
theorem B4900433 : Blo 1811607 4900433 := bstep (se 2 (by rfl) ⟨1837662, by rfl⟩ : syracuseStep 4900433 = 3675325) B3675325
theorem B2582113 : Blo 1811607 2582113 := bstep (se 2 (by rfl) ⟨968292, by rfl⟩ : syracuseStep 2582113 = 1936585) B1936585
theorem B1812067 : Blo 1811607 1812067 := bstep (se 1 (by rfl) ⟨1359050, by rfl⟩ : syracuseStep 1812067 = 2718101) B2718101
theorem B1812083 : Blo 1811607 1812083 := bstep (se 1 (by rfl) ⟨1359062, by rfl⟩ : syracuseStep 1812083 = 2718125) B2718125
theorem B1812099 : Blo 1811607 1812099 := bstep (se 1 (by rfl) ⟨1359074, by rfl⟩ : syracuseStep 1812099 = 2718149) B2718149
theorem B9799309 : Blo 1811607 9799309 := bstep (se 3 (by rfl) ⟨1837370, by rfl⟩ : syracuseStep 9799309 = 3674741) B3674741
theorem B1812115 : Blo 1811607 1812115 := bstep (se 1 (by rfl) ⟨1359086, by rfl⟩ : syracuseStep 1812115 = 2718173) B2718173
theorem B1812131 : Blo 1811607 1812131 := bstep (se 1 (by rfl) ⟨1359098, by rfl⟩ : syracuseStep 1812131 = 2718197) B2718197
theorem B3057331 : Blo 1811607 3057331 := bstep (se 1 (by rfl) ⟨2292998, by rfl⟩ : syracuseStep 3057331 = 4585997) B4585997
theorem B1812147 : Blo 1811607 1812147 := bstep (se 1 (by rfl) ⟨1359110, by rfl⟩ : syracuseStep 1812147 = 2718221) B2718221
theorem B2582209 : Blo 1811607 2582209 := bstep (se 2 (by rfl) ⟨968328, by rfl⟩ : syracuseStep 2582209 = 1936657) B1936657
theorem B1812163 : Blo 1811607 1812163 := bstep (se 1 (by rfl) ⟨1359122, by rfl⟩ : syracuseStep 1812163 = 2718245) B2718245
theorem B1812179 : Blo 1811607 1812179 := bstep (se 1 (by rfl) ⟨1359134, by rfl⟩ : syracuseStep 1812179 = 2718269) B2718269
theorem B1812195 : Blo 1811607 1812195 := bstep (se 1 (by rfl) ⟨1359146, by rfl⟩ : syracuseStep 1812195 = 2718293) B2718293
theorem B1812211 : Blo 1811607 1812211 := bstep (se 1 (by rfl) ⟨1359158, by rfl⟩ : syracuseStep 1812211 = 2718317) B2718317
theorem B1812227 : Blo 1811607 1812227 := bstep (se 1 (by rfl) ⟨1359170, by rfl⟩ : syracuseStep 1812227 = 2718341) B2718341
theorem B1812243 : Blo 1811607 1812243 := bstep (se 1 (by rfl) ⟨1359182, by rfl⟩ : syracuseStep 1812243 = 2718365) B2718365
theorem B1812259 : Blo 1811607 1812259 := bstep (se 1 (by rfl) ⟨1359194, by rfl⟩ : syracuseStep 1812259 = 2718389) B2718389
theorem B1812275 : Blo 1811607 1812275 := bstep (se 1 (by rfl) ⟨1359206, by rfl⟩ : syracuseStep 1812275 = 2718413) B2718413
theorem B3057473 : Blo 1811607 3057473 := bstep (se 2 (by rfl) ⟨1146552, by rfl⟩ : syracuseStep 3057473 = 2293105) B2293105
theorem B1812291 : Blo 1811607 1812291 := bstep (se 1 (by rfl) ⟨1359218, by rfl⟩ : syracuseStep 1812291 = 2718437) B2718437
theorem B3442513 : Blo 1811607 3442513 := bstep (se 2 (by rfl) ⟨1290942, by rfl⟩ : syracuseStep 3442513 = 2581885) B2581885
theorem B1812307 : Blo 1811607 1812307 := bstep (se 1 (by rfl) ⟨1359230, by rfl⟩ : syracuseStep 1812307 = 2718461) B2718461
theorem B15476579 : Blo 1811607 15476579 := bstep (se 1 (by rfl) ⟨11607434, by rfl⟩ : syracuseStep 15476579 = 23214869) B23214869
theorem B1812323 : Blo 1811607 1812323 := bstep (se 1 (by rfl) ⟨1359242, by rfl⟩ : syracuseStep 1812323 = 2718485) B2718485
theorem B1812339 : Blo 1811607 1812339 := bstep (se 1 (by rfl) ⟨1359254, by rfl⟩ : syracuseStep 1812339 = 2718509) B2718509
theorem B1812355 : Blo 1811607 1812355 := bstep (se 1 (by rfl) ⟨1359266, by rfl⟩ : syracuseStep 1812355 = 2718533) B2718533
theorem B1812371 : Blo 1811607 1812371 := bstep (se 1 (by rfl) ⟨1359278, by rfl⟩ : syracuseStep 1812371 = 2718557) B2718557
theorem B1812387 : Blo 1811607 1812387 := bstep (se 1 (by rfl) ⟨1359290, by rfl⟩ : syracuseStep 1812387 = 2718581) B2718581
theorem B5162915 : Blo 1811607 5162915 := bstep (se 1 (by rfl) ⟨3872186, by rfl⟩ : syracuseStep 5162915 = 7744373) B7744373
theorem B1812403 : Blo 1811607 1812403 := bstep (se 1 (by rfl) ⟨1359302, by rfl⟩ : syracuseStep 1812403 = 2718605) B2718605
theorem B3057601 : Blo 1811607 3057601 := bstep (se 2 (by rfl) ⟨1146600, by rfl⟩ : syracuseStep 3057601 = 2293201) B2293201
theorem B1935299 : Blo 1811607 1935299 := bstep (se 1 (by rfl) ⟨1451474, by rfl⟩ : syracuseStep 1935299 = 2902949) B2902949
theorem B1812419 : Blo 1811607 1812419 := bstep (se 1 (by rfl) ⟨1359314, by rfl⟩ : syracuseStep 1812419 = 2718629) B2718629
theorem B1812435 : Blo 1811607 1812435 := bstep (se 1 (by rfl) ⟨1359326, by rfl⟩ : syracuseStep 1812435 = 2718653) B2718653
theorem B3057635 : Blo 1811607 3057635 := bstep (se 1 (by rfl) ⟨2293226, by rfl⟩ : syracuseStep 3057635 = 4586453) B4586453
theorem B1812451 : Blo 1811607 1812451 := bstep (se 1 (by rfl) ⟨1359338, by rfl⟩ : syracuseStep 1812451 = 2718677) B2718677
theorem B1812467 : Blo 1811607 1812467 := bstep (se 1 (by rfl) ⟨1359350, by rfl⟩ : syracuseStep 1812467 = 2718701) B2718701
theorem B1812483 : Blo 1811607 1812483 := bstep (se 1 (by rfl) ⟨1359362, by rfl⟩ : syracuseStep 1812483 = 2718725) B2718725
theorem B1812499 : Blo 1811607 1812499 := bstep (se 1 (by rfl) ⟨1359374, by rfl⟩ : syracuseStep 1812499 = 2718749) B2718749
theorem B1812515 : Blo 1811607 1812515 := bstep (se 1 (by rfl) ⟨1359386, by rfl⟩ : syracuseStep 1812515 = 2718773) B2718773
theorem B9177137 : Blo 1811607 9177137 := bstep (se 2 (by rfl) ⟨3441426, by rfl⟩ : syracuseStep 9177137 = 6882853) B6882853
theorem B1812531 : Blo 1811607 1812531 := bstep (se 1 (by rfl) ⟨1359398, by rfl⟩ : syracuseStep 1812531 = 2718797) B2718797
theorem B1812547 : Blo 1811607 1812547 := bstep (se 1 (by rfl) ⟨1359410, by rfl⟩ : syracuseStep 1812547 = 2718821) B2718821
theorem B2754641 : Blo 1811607 2754641 := bstep (se 2 (by rfl) ⟨1032990, by rfl⟩ : syracuseStep 2754641 = 2065981) B2065981
theorem B1812563 : Blo 1811607 1812563 := bstep (se 1 (by rfl) ⟨1359422, by rfl⟩ : syracuseStep 1812563 = 2718845) B2718845
theorem B2902115 : Blo 1811607 2902115 := bstep (se 1 (by rfl) ⟨2176586, by rfl⟩ : syracuseStep 2902115 = 4353173) B4353173
theorem B3057763 : Blo 1811607 3057763 := bstep (se 1 (by rfl) ⟨2293322, by rfl⟩ : syracuseStep 3057763 = 4586645) B4586645
theorem B1812579 : Blo 1811607 1812579 := bstep (se 1 (by rfl) ⟨1359434, by rfl⟩ : syracuseStep 1812579 = 2718869) B2718869
theorem B1812595 : Blo 1811607 1812595 := bstep (se 1 (by rfl) ⟨1359446, by rfl⟩ : syracuseStep 1812595 = 2718893) B2718893
theorem B1812611 : Blo 1811607 1812611 := bstep (se 1 (by rfl) ⟨1359458, by rfl⟩ : syracuseStep 1812611 = 2718917) B2718917
theorem B1812627 : Blo 1811607 1812627 := bstep (se 1 (by rfl) ⟨1359470, by rfl⟩ : syracuseStep 1812627 = 2718941) B2718941
theorem B1812643 : Blo 1811607 1812643 := bstep (se 1 (by rfl) ⟨1359482, by rfl⟩ : syracuseStep 1812643 = 2718965) B2718965
theorem B1812659 : Blo 1811607 1812659 := bstep (se 1 (by rfl) ⟨1359494, by rfl⟩ : syracuseStep 1812659 = 2718989) B2718989
theorem B1812675 : Blo 1811607 1812675 := bstep (se 1 (by rfl) ⟨1359506, by rfl⟩ : syracuseStep 1812675 = 2719013) B2719013
theorem B1812691 : Blo 1811607 1812691 := bstep (se 1 (by rfl) ⟨1359518, by rfl⟩ : syracuseStep 1812691 = 2719037) B2719037
theorem B1812707 : Blo 1811607 1812707 := bstep (se 1 (by rfl) ⟨1359530, by rfl⟩ : syracuseStep 1812707 = 2719061) B2719061
theorem B3442915 : Blo 1811607 3442915 := bstep (se 1 (by rfl) ⟨2582186, by rfl⟩ : syracuseStep 3442915 = 5164373) B5164373
theorem B3057905 : Blo 1811607 3057905 := bstep (se 2 (by rfl) ⟨1146714, by rfl⟩ : syracuseStep 3057905 = 2293429) B2293429
theorem B1812723 : Blo 1811607 1812723 := bstep (se 1 (by rfl) ⟨1359542, by rfl⟩ : syracuseStep 1812723 = 2719085) B2719085
theorem B1812739 : Blo 1811607 1812739 := bstep (se 1 (by rfl) ⟨1359554, by rfl⟩ : syracuseStep 1812739 = 2719109) B2719109
theorem B7743757 : Blo 1811607 7743757 := bstep (se 3 (by rfl) ⟨1451954, by rfl⟩ : syracuseStep 7743757 = 2903909) B2903909
theorem B3442961 : Blo 1811607 3442961 := bstep (se 2 (by rfl) ⟨1291110, by rfl⟩ : syracuseStep 3442961 = 2582221) B2582221
theorem B1812755 : Blo 1811607 1812755 := bstep (se 1 (by rfl) ⟨1359566, by rfl⟩ : syracuseStep 1812755 = 2719133) B2719133
theorem B10324259 : Blo 1811607 10324259 := bstep (se 1 (by rfl) ⟨7743194, by rfl⟩ : syracuseStep 10324259 = 15486389) B15486389
theorem B1812771 : Blo 1811607 1812771 := bstep (se 1 (by rfl) ⟨1359578, by rfl⟩ : syracuseStep 1812771 = 2719157) B2719157
theorem B1812787 : Blo 1811607 1812787 := bstep (se 1 (by rfl) ⟨1359590, by rfl⟩ : syracuseStep 1812787 = 2719181) B2719181
theorem B1812803 : Blo 1811607 1812803 := bstep (se 1 (by rfl) ⟨1359602, by rfl⟩ : syracuseStep 1812803 = 2719205) B2719205
theorem B12912965 : Blo 1811607 12912965 := bstep (se 4 (by rfl) ⟨1210590, by rfl⟩ : syracuseStep 12912965 = 2421181) B2421181
theorem B4589905 : Blo 1811607 4589905 := bstep (se 2 (by rfl) ⟨1721214, by rfl⟩ : syracuseStep 4589905 = 3442429) B3442429
theorem B1812819 : Blo 1811607 1812819 := bstep (se 1 (by rfl) ⟨1359614, by rfl⟩ : syracuseStep 1812819 = 2719229) B2719229
theorem B1812835 : Blo 1811607 1812835 := bstep (se 1 (by rfl) ⟨1359626, by rfl⟩ : syracuseStep 1812835 = 2719253) B2719253
theorem B2902385 : Blo 1811607 2902385 := bstep (se 2 (by rfl) ⟨1088394, by rfl⟩ : syracuseStep 2902385 = 2176789) B2176789
theorem B3058033 : Blo 1811607 3058033 := bstep (se 2 (by rfl) ⟨1146762, by rfl⟩ : syracuseStep 3058033 = 2293525) B2293525
theorem B13764977 : Blo 1811607 13764977 := bstep (se 2 (by rfl) ⟨5161866, by rfl⟩ : syracuseStep 13764977 = 10323733) B10323733
theorem B1812851 : Blo 1811607 1812851 := bstep (se 1 (by rfl) ⟨1359638, by rfl⟩ : syracuseStep 1812851 = 2719277) B2719277
theorem B1812867 : Blo 1811607 1812867 := bstep (se 1 (by rfl) ⟨1359650, by rfl⟩ : syracuseStep 1812867 = 2719301) B2719301
theorem B3058067 : Blo 1811607 3058067 := bstep (se 1 (by rfl) ⟨2293550, by rfl⟩ : syracuseStep 3058067 = 4587101) B4587101
theorem B1812883 : Blo 1811607 1812883 := bstep (se 1 (by rfl) ⟨1359662, by rfl⟩ : syracuseStep 1812883 = 2719325) B2719325
theorem B1812899 : Blo 1811607 1812899 := bstep (se 1 (by rfl) ⟨1359674, by rfl⟩ : syracuseStep 1812899 = 2719349) B2719349
theorem B1812915 : Blo 1811607 1812915 := bstep (se 1 (by rfl) ⟨1359686, by rfl⟩ : syracuseStep 1812915 = 2719373) B2719373
theorem B1812931 : Blo 1811607 1812931 := bstep (se 1 (by rfl) ⟨1359698, by rfl⟩ : syracuseStep 1812931 = 2719397) B2719397
theorem B3869137 : Blo 1811607 3869137 := bstep (se 2 (by rfl) ⟨1450926, by rfl⟩ : syracuseStep 3869137 = 2901853) B2901853
theorem B1812947 : Blo 1811607 1812947 := bstep (se 1 (by rfl) ⟨1359710, by rfl⟩ : syracuseStep 1812947 = 2719421) B2719421
theorem B1812963 : Blo 1811607 1812963 := bstep (se 1 (by rfl) ⟨1359722, by rfl⟩ : syracuseStep 1812963 = 2719445) B2719445
theorem B6883811 : Blo 1811607 6883811 := bstep (se 1 (by rfl) ⟨5162858, by rfl⟩ : syracuseStep 6883811 = 10325717) B10325717
theorem B6883825 : Blo 1811607 6883825 := bstep (se 2 (by rfl) ⟨2581434, by rfl⟩ : syracuseStep 6883825 = 5162869) B5162869
theorem B1812979 : Blo 1811607 1812979 := bstep (se 1 (by rfl) ⟨1359734, by rfl⟩ : syracuseStep 1812979 = 2719469) B2719469
theorem B1812995 : Blo 1811607 1812995 := bstep (se 1 (by rfl) ⟨1359746, by rfl⟩ : syracuseStep 1812995 = 2719493) B2719493
theorem B3058195 : Blo 1811607 3058195 := bstep (se 1 (by rfl) ⟨2293646, by rfl⟩ : syracuseStep 3058195 = 4587293) B4587293
theorem B1813011 : Blo 1811607 1813011 := bstep (se 1 (by rfl) ⟨1359758, by rfl⟩ : syracuseStep 1813011 = 2719517) B2719517
theorem B2943523 : Blo 1811607 2943523 := bstep (se 1 (by rfl) ⟨2207642, by rfl⟩ : syracuseStep 2943523 = 4415285) B4415285
theorem B1813027 : Blo 1811607 1813027 := bstep (se 1 (by rfl) ⟨1359770, by rfl⟩ : syracuseStep 1813027 = 2719541) B2719541
theorem B1813043 : Blo 1811607 1813043 := bstep (se 1 (by rfl) ⟨1359782, by rfl⟩ : syracuseStep 1813043 = 2719565) B2719565
theorem B1813059 : Blo 1811607 1813059 := bstep (se 1 (by rfl) ⟨1359794, by rfl⟩ : syracuseStep 1813059 = 2719589) B2719589
theorem B1813075 : Blo 1811607 1813075 := bstep (se 1 (by rfl) ⟨1359806, by rfl⟩ : syracuseStep 1813075 = 2719613) B2719613
theorem B7744099 : Blo 1811607 7744099 := bstep (se 1 (by rfl) ⟨5808074, by rfl⟩ : syracuseStep 7744099 = 11616149) B11616149
theorem B1813091 : Blo 1811607 1813091 := bstep (se 1 (by rfl) ⟨1359818, by rfl⟩ : syracuseStep 1813091 = 2719637) B2719637
theorem B4590179 : Blo 1811607 4590179 := bstep (se 1 (by rfl) ⟨3442634, by rfl⟩ : syracuseStep 4590179 = 6885269) B6885269
theorem B1813107 : Blo 1811607 1813107 := bstep (se 1 (by rfl) ⟨1359830, by rfl⟩ : syracuseStep 1813107 = 2719661) B2719661
theorem B1813123 : Blo 1811607 1813123 := bstep (se 1 (by rfl) ⟨1359842, by rfl⟩ : syracuseStep 1813123 = 2719685) B2719685
theorem B2902673 : Blo 1811607 2902673 := bstep (se 2 (by rfl) ⟨1088502, by rfl⟩ : syracuseStep 2902673 = 2177005) B2177005
theorem B1813139 : Blo 1811607 1813139 := bstep (se 1 (by rfl) ⟨1359854, by rfl⟩ : syracuseStep 1813139 = 2719709) B2719709
theorem B3058337 : Blo 1811607 3058337 := bstep (se 2 (by rfl) ⟨1146876, by rfl⟩ : syracuseStep 3058337 = 2293753) B2293753
theorem B1813155 : Blo 1811607 1813155 := bstep (se 1 (by rfl) ⟨1359866, by rfl⟩ : syracuseStep 1813155 = 2719733) B2719733
theorem B1813171 : Blo 1811607 1813171 := bstep (se 1 (by rfl) ⟨1359878, by rfl⟩ : syracuseStep 1813171 = 2719757) B2719757
theorem B1813187 : Blo 1811607 1813187 := bstep (se 1 (by rfl) ⟨1359890, by rfl⟩ : syracuseStep 1813187 = 2719781) B2719781
theorem B1813203 : Blo 1811607 1813203 := bstep (se 1 (by rfl) ⟨1359902, by rfl⟩ : syracuseStep 1813203 = 2719805) B2719805
theorem B1813219 : Blo 1811607 1813219 := bstep (se 1 (by rfl) ⟨1359914, by rfl⟩ : syracuseStep 1813219 = 2719829) B2719829
theorem B22055651 : Blo 1811607 22055651 := bstep (se 1 (by rfl) ⟨16541738, by rfl⟩ : syracuseStep 22055651 = 33083477) B33083477
theorem B1813235 : Blo 1811607 1813235 := bstep (se 1 (by rfl) ⟨1359926, by rfl⟩ : syracuseStep 1813235 = 2719853) B2719853
theorem B1813251 : Blo 1811607 1813251 := bstep (se 1 (by rfl) ⟨1359938, by rfl⟩ : syracuseStep 1813251 = 2719877) B2719877
theorem B1813267 : Blo 1811607 1813267 := bstep (se 1 (by rfl) ⟨1359950, by rfl⟩ : syracuseStep 1813267 = 2719901) B2719901
theorem B3058465 : Blo 1811607 3058465 := bstep (se 2 (by rfl) ⟨1146924, by rfl⟩ : syracuseStep 3058465 = 2293849) B2293849
theorem B1813283 : Blo 1811607 1813283 := bstep (se 1 (by rfl) ⟨1359962, by rfl⟩ : syracuseStep 1813283 = 2719925) B2719925
theorem B4590371 : Blo 1811607 4590371 := bstep (se 1 (by rfl) ⟨3442778, by rfl⟩ : syracuseStep 4590371 = 6885557) B6885557
theorem B11619121 : Blo 1811607 11619121 := bstep (se 2 (by rfl) ⟨4357170, by rfl⟩ : syracuseStep 11619121 = 8714341) B8714341
theorem B1813299 : Blo 1811607 1813299 := bstep (se 1 (by rfl) ⟨1359974, by rfl⟩ : syracuseStep 1813299 = 2719949) B2719949
theorem B3058499 : Blo 1811607 3058499 := bstep (se 1 (by rfl) ⟨2293874, by rfl⟩ : syracuseStep 3058499 = 4587749) B4587749
theorem B1813315 : Blo 1811607 1813315 := bstep (se 1 (by rfl) ⟨1359986, by rfl⟩ : syracuseStep 1813315 = 2719973) B2719973
theorem B1813331 : Blo 1811607 1813331 := bstep (se 1 (by rfl) ⟨1359998, by rfl⟩ : syracuseStep 1813331 = 2719997) B2719997
theorem B1813347 : Blo 1811607 1813347 := bstep (se 1 (by rfl) ⟨1360010, by rfl⟩ : syracuseStep 1813347 = 2720021) B2720021
theorem B1837939 : Blo 1811607 1837939 := bstep (se 1 (by rfl) ⟨1378454, by rfl⟩ : syracuseStep 1837939 = 2756909) B2756909
theorem B1813363 : Blo 1811607 1813363 := bstep (se 1 (by rfl) ⟨1360022, by rfl⟩ : syracuseStep 1813363 = 2720045) B2720045
theorem B1813379 : Blo 1811607 1813379 := bstep (se 1 (by rfl) ⟨1360034, by rfl⟩ : syracuseStep 1813379 = 2720069) B2720069
theorem B1813395 : Blo 1811607 1813395 := bstep (se 1 (by rfl) ⟨1360046, by rfl⟩ : syracuseStep 1813395 = 2720093) B2720093
theorem B1813411 : Blo 1811607 1813411 := bstep (se 1 (by rfl) ⟨1360058, by rfl⟩ : syracuseStep 1813411 = 2720117) B2720117
theorem B1813427 : Blo 1811607 1813427 := bstep (se 1 (by rfl) ⟨1360070, by rfl⟩ : syracuseStep 1813427 = 2720141) B2720141
theorem B3058627 : Blo 1811607 3058627 := bstep (se 1 (by rfl) ⟨2293970, by rfl⟩ : syracuseStep 3058627 = 4587941) B4587941
theorem B1813443 : Blo 1811607 1813443 := bstep (se 1 (by rfl) ⟨1360082, by rfl⟩ : syracuseStep 1813443 = 2720165) B2720165
theorem B6114257 : Blo 1811607 6114257 := bstep (se 2 (by rfl) ⟨2292846, by rfl⟩ : syracuseStep 6114257 = 4585693) B4585693
theorem B1813459 : Blo 1811607 1813459 := bstep (se 1 (by rfl) ⟨1360094, by rfl⟩ : syracuseStep 1813459 = 2720189) B2720189
theorem B1813475 : Blo 1811607 1813475 := bstep (se 1 (by rfl) ⟨1360106, by rfl⟩ : syracuseStep 1813475 = 2720213) B2720213
theorem B6204401 : Blo 1811607 6204401 := bstep (se 2 (by rfl) ⟨2326650, by rfl⟩ : syracuseStep 6204401 = 4653301) B4653301
theorem B1813491 : Blo 1811607 1813491 := bstep (se 1 (by rfl) ⟨1360118, by rfl⟩ : syracuseStep 1813491 = 2720237) B2720237
theorem B1813507 : Blo 1811607 1813507 := bstep (se 1 (by rfl) ⟨1360130, by rfl⟩ : syracuseStep 1813507 = 2720261) B2720261
theorem B1813523 : Blo 1811607 1813523 := bstep (se 1 (by rfl) ⟨1360142, by rfl⟩ : syracuseStep 1813523 = 2720285) B2720285
theorem B1813539 : Blo 1811607 1813539 := bstep (se 1 (by rfl) ⟨1360154, by rfl⟩ : syracuseStep 1813539 = 2720309) B2720309
theorem B2903089 : Blo 1811607 2903089 := bstep (se 2 (by rfl) ⟨1088658, by rfl⟩ : syracuseStep 2903089 = 2177317) B2177317
theorem B1936435 : Blo 1811607 1936435 := bstep (se 1 (by rfl) ⟨1452326, by rfl⟩ : syracuseStep 1936435 = 2904653) B2904653
theorem B1813555 : Blo 1811607 1813555 := bstep (se 1 (by rfl) ⟨1360166, by rfl⟩ : syracuseStep 1813555 = 2720333) B2720333
theorem B1813571 : Blo 1811607 1813571 := bstep (se 1 (by rfl) ⟨1360178, by rfl⟩ : syracuseStep 1813571 = 2720357) B2720357
theorem B3058769 : Blo 1811607 3058769 := bstep (se 2 (by rfl) ⟨1147038, by rfl⟩ : syracuseStep 3058769 = 2294077) B2294077
theorem B1813587 : Blo 1811607 1813587 := bstep (se 1 (by rfl) ⟨1360190, by rfl⟩ : syracuseStep 1813587 = 2720381) B2720381
theorem B3869795 : Blo 1811607 3869795 := bstep (se 1 (by rfl) ⟨2902346, by rfl⟩ : syracuseStep 3869795 = 5804693) B5804693
theorem B1813603 : Blo 1811607 1813603 := bstep (se 1 (by rfl) ⟨1360202, by rfl⟩ : syracuseStep 1813603 = 2720405) B2720405
theorem B5164145 : Blo 1811607 5164145 := bstep (se 2 (by rfl) ⟨1936554, by rfl⟩ : syracuseStep 5164145 = 3873109) B3873109
theorem B14699717 : Blo 1811607 14699717 := bstep (se 4 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 14699717 = 2756197) B2756197
theorem B23235781 : Blo 1811607 23235781 := bstep (se 4 (by rfl) ⟨2178354, by rfl⟩ : syracuseStep 23235781 = 4356709) B4356709
theorem B3058897 : Blo 1811607 3058897 := bstep (se 2 (by rfl) ⟨1147086, by rfl⟩ : syracuseStep 3058897 = 2294173) B2294173
theorem B3058931 : Blo 1811607 3058931 := bstep (se 1 (by rfl) ⟨2294198, by rfl⟩ : syracuseStep 3058931 = 4588397) B4588397
theorem B2616563 : Blo 1811607 2616563 := bstep (se 1 (by rfl) ⟨1962422, by rfl⟩ : syracuseStep 2616563 = 3924845) B3924845
theorem B3673379 : Blo 1811607 3673379 := bstep (se 1 (by rfl) ⟨2755034, by rfl⟩ : syracuseStep 3673379 = 5510069) B5510069
theorem B8711459 : Blo 1811607 8711459 := bstep (se 1 (by rfl) ⟨6533594, by rfl⟩ : syracuseStep 8711459 = 13067189) B13067189
theorem B10071373 : Blo 1811607 10071373 := bstep (se 3 (by rfl) ⟨1888382, by rfl⟩ : syracuseStep 10071373 = 3776765) B3776765
theorem B13069667 : Blo 1811607 13069667 := bstep (se 1 (by rfl) ⟨9802250, by rfl⟩ : syracuseStep 13069667 = 19604501) B19604501
theorem B3059059 : Blo 1811607 3059059 := bstep (se 1 (by rfl) ⟨2294294, by rfl⟩ : syracuseStep 3059059 = 4588589) B4588589
theorem B9178595 : Blo 1811607 9178595 := bstep (se 1 (by rfl) ⟨6883946, by rfl⟩ : syracuseStep 9178595 = 13767893) B13767893
theorem B6114797 : Blo 1811607 6114797 := bstep (se 3 (by rfl) ⟨1146524, by rfl⟩ : syracuseStep 6114797 = 2293049) B2293049
theorem B3059201 : Blo 1811607 3059201 := bstep (se 2 (by rfl) ⟨1147200, by rfl⟩ : syracuseStep 3059201 = 2294401) B2294401
theorem B6114851 : Blo 1811607 6114851 := bstep (se 1 (by rfl) ⟨4586138, by rfl⟩ : syracuseStep 6114851 = 9172277) B9172277
theorem B3681841 : Blo 1811607 3681841 := bstep (se 2 (by rfl) ⟨1380690, by rfl⟩ : syracuseStep 3681841 = 2761381) B2761381
theorem B17428067 : Blo 1811607 17428067 := bstep (se 1 (by rfl) ⟨13071050, by rfl⟩ : syracuseStep 17428067 = 26142101) B26142101
theorem B3059329 : Blo 1811607 3059329 := bstep (se 2 (by rfl) ⟨1147248, by rfl⟩ : syracuseStep 3059329 = 2294497) B2294497
theorem B3059363 : Blo 1811607 3059363 := bstep (se 1 (by rfl) ⟨2294522, by rfl⟩ : syracuseStep 3059363 = 4589045) B4589045
theorem B24792803 : Blo 1811607 24792803 := bstep (se 1 (by rfl) ⟨18594602, by rfl⟩ : syracuseStep 24792803 = 37189205) B37189205
theorem B3059491 : Blo 1811607 3059491 := bstep (se 1 (by rfl) ⟨2294618, by rfl⟩ : syracuseStep 3059491 = 4589237) B4589237
theorem B6115121 : Blo 1811607 6115121 := bstep (se 2 (by rfl) ⟨2293170, by rfl⟩ : syracuseStep 6115121 = 4586341) B4586341
theorem B6885283 : Blo 1811607 6885283 := bstep (se 1 (by rfl) ⟨5163962, by rfl⟩ : syracuseStep 6885283 = 10327925) B10327925
theorem B5803949 : Blo 1811607 5803949 := bstep (se 3 (by rfl) ⟨1088240, by rfl⟩ : syracuseStep 5803949 = 2176481) B2176481
theorem B3870641 : Blo 1811607 3870641 := bstep (se 2 (by rfl) ⟨1451490, by rfl⟩ : syracuseStep 3870641 = 2902981) B2902981
theorem B3059633 : Blo 1811607 3059633 := bstep (se 2 (by rfl) ⟨1147362, by rfl⟩ : syracuseStep 3059633 = 2294725) B2294725
theorem B2903987 : Blo 1811607 2903987 := bstep (se 1 (by rfl) ⟨2177990, by rfl⟩ : syracuseStep 2903987 = 4355981) B4355981
theorem B3059761 : Blo 1811607 3059761 := bstep (se 2 (by rfl) ⟨1147410, by rfl⟩ : syracuseStep 3059761 = 2294821) B2294821
theorem B10317901 : Blo 1811607 10317901 := bstep (se 3 (by rfl) ⟨1934606, by rfl⟩ : syracuseStep 10317901 = 3869213) B3869213
theorem B3059795 : Blo 1811607 3059795 := bstep (se 1 (by rfl) ⟨2294846, by rfl⟩ : syracuseStep 3059795 = 4589693) B4589693
theorem B6533219 : Blo 1811607 6533219 := bstep (se 1 (by rfl) ⟨4899914, by rfl⟩ : syracuseStep 6533219 = 9799829) B9799829
theorem B10326149 : Blo 1811607 10326149 := bstep (se 4 (by rfl) ⟨968076, by rfl⟩ : syracuseStep 10326149 = 1936153) B1936153
theorem B27914381 : Blo 1811607 27914381 := bstep (se 3 (by rfl) ⟨5233946, by rfl⟩ : syracuseStep 27914381 = 10467893) B10467893
theorem B2904211 : Blo 1811607 2904211 := bstep (se 1 (by rfl) ⟨2178158, by rfl⟩ : syracuseStep 2904211 = 4356317) B4356317
theorem B4354211 : Blo 1811607 4354211 := bstep (se 1 (by rfl) ⟨3265658, by rfl⟩ : syracuseStep 4354211 = 6531317) B6531317
theorem B3059923 : Blo 1811607 3059923 := bstep (se 1 (by rfl) ⟨2294942, by rfl⟩ : syracuseStep 3059923 = 4589885) B4589885
theorem B9179405 : Blo 1811607 9179405 := bstep (se 3 (by rfl) ⟨1721138, by rfl⟩ : syracuseStep 9179405 = 3442277) B3442277
theorem B6115661 : Blo 1811607 6115661 := bstep (se 3 (by rfl) ⟨1146686, by rfl⟩ : syracuseStep 6115661 = 2293373) B2293373
theorem B2756945 : Blo 1811607 2756945 := bstep (se 2 (by rfl) ⟨1033854, by rfl⟩ : syracuseStep 2756945 = 2067709) B2067709
theorem B3060065 : Blo 1811607 3060065 := bstep (se 2 (by rfl) ⟨1147524, by rfl⟩ : syracuseStep 3060065 = 2295049) B2295049
theorem B6115715 : Blo 1811607 6115715 := bstep (se 1 (by rfl) ⟨4586786, by rfl⟩ : syracuseStep 6115715 = 9173573) B9173573
theorem B19124677 : Blo 1811607 19124677 := bstep (se 4 (by rfl) ⟨1792938, by rfl⟩ : syracuseStep 19124677 = 3585877) B3585877
theorem B3060193 : Blo 1811607 3060193 := bstep (se 2 (by rfl) ⟨1147572, by rfl⟩ : syracuseStep 3060193 = 2295145) B2295145
theorem B3264995 : Blo 1811607 3264995 := bstep (se 1 (by rfl) ⟨2448746, by rfl⟩ : syracuseStep 3264995 = 4897493) B4897493
theorem B3060227 : Blo 1811607 3060227 := bstep (se 1 (by rfl) ⟨2295170, by rfl⟩ : syracuseStep 3060227 = 4590341) B4590341
theorem B4133393 : Blo 1811607 4133393 := bstep (se 2 (by rfl) ⟨1550022, by rfl⟩ : syracuseStep 4133393 = 3100045) B3100045
theorem B22049333 : Blo 1811607 22049333 := bstep (se 5 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 22049333 = 2067125) B2067125
theorem B8712803 : Blo 1811607 8712803 := bstep (se 1 (by rfl) ⟨6534602, by rfl⟩ : syracuseStep 8712803 = 13069205) B13069205
theorem B3060355 : Blo 1811607 3060355 := bstep (se 1 (by rfl) ⟨2295266, by rfl⟩ : syracuseStep 3060355 = 4590533) B4590533
theorem B5509777 : Blo 1811607 5509777 := bstep (se 2 (by rfl) ⟨2066166, by rfl⟩ : syracuseStep 5509777 = 4132333) B4132333
theorem B6115985 : Blo 1811607 6115985 := bstep (se 2 (by rfl) ⟨2293494, by rfl⟩ : syracuseStep 6115985 = 4586989) B4586989
theorem B4133521 : Blo 1811607 4133521 := bstep (se 2 (by rfl) ⟨1550070, by rfl⟩ : syracuseStep 4133521 = 3100141) B3100141
theorem B2355923 : Blo 1811607 2355923 := bstep (se 1 (by rfl) ⟨1766942, by rfl⟩ : syracuseStep 2355923 = 3533885) B3533885
theorem B7353101 : Blo 1811607 7353101 := bstep (se 3 (by rfl) ⟨1378706, by rfl⟩ : syracuseStep 7353101 = 2757413) B2757413
theorem B4076369 : Blo 1811607 4076369 := bstep (se 2 (by rfl) ⟨1528638, by rfl⟩ : syracuseStep 4076369 = 3057277) B3057277
theorem B4133713 : Blo 1811607 4133713 := bstep (se 2 (by rfl) ⟨1550142, by rfl⟩ : syracuseStep 4133713 = 3100285) B3100285
theorem B4076387 : Blo 1811607 4076387 := bstep (se 1 (by rfl) ⟨3057290, by rfl⟩ : syracuseStep 4076387 = 6114581) B6114581
theorem B3265393 : Blo 1811607 3265393 := bstep (se 2 (by rfl) ⟨1224522, by rfl⟩ : syracuseStep 3265393 = 2449045) B2449045
theorem B9171953 : Blo 1811607 9171953 := bstep (se 2 (by rfl) ⟨3439482, by rfl⟩ : syracuseStep 9171953 = 6878965) B6878965
theorem B19862597 : Blo 1811607 19862597 := bstep (se 4 (by rfl) ⟨1862118, by rfl⟩ : syracuseStep 19862597 = 3724237) B3724237
theorem B4076657 : Blo 1811607 4076657 := bstep (se 2 (by rfl) ⟨1528746, by rfl⟩ : syracuseStep 4076657 = 3057493) B3057493
theorem B2356339 : Blo 1811607 2356339 := bstep (se 1 (by rfl) ⟨1767254, by rfl⟩ : syracuseStep 2356339 = 3534509) B3534509
theorem B4076675 : Blo 1811607 4076675 := bstep (se 1 (by rfl) ⟨3057506, by rfl⟩ : syracuseStep 4076675 = 6115013) B6115013
theorem B6116525 : Blo 1811607 6116525 := bstep (se 3 (by rfl) ⟨1146848, by rfl⟩ : syracuseStep 6116525 = 2293697) B2293697
theorem B8606947 : Blo 1811607 8606947 := bstep (se 1 (by rfl) ⟨6455210, by rfl⟩ : syracuseStep 8606947 = 12910421) B12910421
theorem B6116579 : Blo 1811607 6116579 := bstep (se 1 (by rfl) ⟨4587434, by rfl⟩ : syracuseStep 6116579 = 9174869) B9174869
theorem B3487043 : Blo 1811607 3487043 := bstep (se 1 (by rfl) ⟨2615282, by rfl⟩ : syracuseStep 3487043 = 5230565) B5230565
theorem B4076945 : Blo 1811607 4076945 := bstep (se 2 (by rfl) ⟨1528854, by rfl⟩ : syracuseStep 4076945 = 3057709) B3057709
theorem B3102097 : Blo 1811607 3102097 := bstep (se 2 (by rfl) ⟨1163286, by rfl⟩ : syracuseStep 3102097 = 2326573) B2326573
theorem B4076963 : Blo 1811607 4076963 := bstep (se 1 (by rfl) ⟨3057722, by rfl⟩ : syracuseStep 4076963 = 6115445) B6115445
theorem B11023813 : Blo 1811607 11023813 := bstep (se 4 (by rfl) ⟨1033482, by rfl⟩ : syracuseStep 11023813 = 2066965) B2066965
theorem B5232109 : Blo 1811607 5232109 := bstep (se 3 (by rfl) ⟨981020, by rfl⟩ : syracuseStep 5232109 = 1962041) B1962041
theorem B6116849 : Blo 1811607 6116849 := bstep (se 2 (by rfl) ⟨2293818, by rfl⟩ : syracuseStep 6116849 = 4587637) B4587637
theorem B4355633 : Blo 1811607 4355633 := bstep (se 2 (by rfl) ⟨1633362, by rfl⟩ : syracuseStep 4355633 = 3266725) B3266725
theorem B3872323 : Blo 1811607 3872323 := bstep (se 1 (by rfl) ⟨2904242, by rfl⟩ : syracuseStep 3872323 = 5808485) B5808485
theorem B6624845 : Blo 1811607 6624845 := bstep (se 3 (by rfl) ⟨1242158, by rfl⟩ : syracuseStep 6624845 = 2484317) B2484317
theorem B8828557 : Blo 1811607 8828557 := bstep (se 3 (by rfl) ⟨1655354, by rfl⟩ : syracuseStep 8828557 = 3310709) B3310709
theorem B4077233 : Blo 1811607 4077233 := bstep (se 2 (by rfl) ⟨1528962, by rfl⟩ : syracuseStep 4077233 = 3057925) B3057925
theorem B20649653 : Blo 1811607 20649653 := bstep (se 5 (by rfl) ⟨967952, by rfl⟩ : syracuseStep 20649653 = 1935905) B1935905
theorem B4077251 : Blo 1811607 4077251 := bstep (se 1 (by rfl) ⟨3057938, by rfl⟩ : syracuseStep 4077251 = 6115877) B6115877
theorem B18863813 : Blo 1811607 18863813 := bstep (se 4 (by rfl) ⟨1768482, by rfl⟩ : syracuseStep 18863813 = 3536965) B3536965
theorem B2717411 : Blo 1811607 2717411 := bstep (se 1 (by rfl) ⟨2038058, by rfl⟩ : syracuseStep 2717411 = 4076117) B4076117
theorem B2717441 : Blo 1811607 2717441 := bstep (se 2 (by rfl) ⟨1019040, by rfl⟩ : syracuseStep 2717441 = 2038081) B2038081
theorem B2717459 : Blo 1811607 2717459 := bstep (se 1 (by rfl) ⟨2038094, by rfl⟩ : syracuseStep 2717459 = 4076189) B4076189
theorem B2717489 : Blo 1811607 2717489 := bstep (se 2 (by rfl) ⟨1019058, by rfl⟩ : syracuseStep 2717489 = 2038117) B2038117
theorem B2717507 : Blo 1811607 2717507 := bstep (se 1 (by rfl) ⟨2038130, by rfl⟩ : syracuseStep 2717507 = 4076261) B4076261
theorem B2717537 : Blo 1811607 2717537 := bstep (se 2 (by rfl) ⟨1019076, by rfl⟩ : syracuseStep 2717537 = 2038153) B2038153
theorem B6371185 : Blo 1811607 6371185 := bstep (se 2 (by rfl) ⟨2389194, by rfl⟩ : syracuseStep 6371185 = 4778389) B4778389
theorem B20936561 : Blo 1811607 20936561 := bstep (se 2 (by rfl) ⟨7851210, by rfl⟩ : syracuseStep 20936561 = 15702421) B15702421
theorem B2717555 : Blo 1811607 2717555 := bstep (se 1 (by rfl) ⟨2038166, by rfl⟩ : syracuseStep 2717555 = 4076333) B4076333
theorem B2717585 : Blo 1811607 2717585 := bstep (se 2 (by rfl) ⟨1019094, by rfl⟩ : syracuseStep 2717585 = 2038189) B2038189
theorem B2717603 : Blo 1811607 2717603 := bstep (se 1 (by rfl) ⟨2038202, by rfl⟩ : syracuseStep 2717603 = 4076405) B4076405
theorem B9795505 : Blo 1811607 9795505 := bstep (se 2 (by rfl) ⟨3673314, by rfl⟩ : syracuseStep 9795505 = 7346629) B7346629
theorem B2717633 : Blo 1811607 2717633 := bstep (se 2 (by rfl) ⟨1019112, by rfl⟩ : syracuseStep 2717633 = 2038225) B2038225
theorem B4077521 : Blo 1811607 4077521 := bstep (se 2 (by rfl) ⟨1529070, by rfl⟩ : syracuseStep 4077521 = 3058141) B3058141
theorem B2717651 : Blo 1811607 2717651 := bstep (se 1 (by rfl) ⟨2038238, by rfl⟩ : syracuseStep 2717651 = 4076477) B4076477
theorem B5158883 : Blo 1811607 5158883 := bstep (se 1 (by rfl) ⟨3869162, by rfl⟩ : syracuseStep 5158883 = 7738325) B7738325
theorem B4077539 : Blo 1811607 4077539 := bstep (se 1 (by rfl) ⟨3058154, by rfl⟩ : syracuseStep 4077539 = 6116309) B6116309
theorem B2717681 : Blo 1811607 2717681 := bstep (se 2 (by rfl) ⟨1019130, by rfl⟩ : syracuseStep 2717681 = 2038261) B2038261
theorem B2717699 : Blo 1811607 2717699 := bstep (se 1 (by rfl) ⟨2038274, by rfl⟩ : syracuseStep 2717699 = 4076549) B4076549
theorem B10319885 : Blo 1811607 10319885 := bstep (se 3 (by rfl) ⟨1934978, by rfl⟩ : syracuseStep 10319885 = 3869957) B3869957
theorem B6117389 : Blo 1811607 6117389 := bstep (se 3 (by rfl) ⟨1147010, by rfl⟩ : syracuseStep 6117389 = 2294021) B2294021
theorem B6535181 : Blo 1811607 6535181 := bstep (se 3 (by rfl) ⟨1225346, by rfl⟩ : syracuseStep 6535181 = 2450693) B2450693
theorem B3872785 : Blo 1811607 3872785 := bstep (se 2 (by rfl) ⟨1452294, by rfl⟩ : syracuseStep 3872785 = 2904589) B2904589
theorem B2717729 : Blo 1811607 2717729 := bstep (se 2 (by rfl) ⟨1019148, by rfl⟩ : syracuseStep 2717729 = 2038297) B2038297
theorem B2717747 : Blo 1811607 2717747 := bstep (se 1 (by rfl) ⟨2038310, by rfl⟩ : syracuseStep 2717747 = 4076621) B4076621
theorem B6117443 : Blo 1811607 6117443 := bstep (se 1 (by rfl) ⟨4588082, by rfl⟩ : syracuseStep 6117443 = 9176165) B9176165
theorem B2717777 : Blo 1811607 2717777 := bstep (se 2 (by rfl) ⟨1019166, by rfl⟩ : syracuseStep 2717777 = 2038333) B2038333
theorem B2717795 : Blo 1811607 2717795 := bstep (se 1 (by rfl) ⟨2038346, by rfl⟩ : syracuseStep 2717795 = 4076693) B4076693
theorem B2717825 : Blo 1811607 2717825 := bstep (se 2 (by rfl) ⟨1019184, by rfl⟩ : syracuseStep 2717825 = 2038369) B2038369
theorem B2717843 : Blo 1811607 2717843 := bstep (se 1 (by rfl) ⟨2038382, by rfl⟩ : syracuseStep 2717843 = 4076765) B4076765
theorem B2717873 : Blo 1811607 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B2717891 : Blo 1811607 2717891 := bstep (se 1 (by rfl) ⟨2038418, by rfl⟩ : syracuseStep 2717891 = 4076837) B4076837
theorem B6879437 : Blo 1811607 6879437 := bstep (se 3 (by rfl) ⟨1289894, by rfl⟩ : syracuseStep 6879437 = 2579789) B2579789
theorem B2717921 : Blo 1811607 2717921 := bstep (se 2 (by rfl) ⟨1019220, by rfl⟩ : syracuseStep 2717921 = 2038441) B2038441
theorem B4077809 : Blo 1811607 4077809 := bstep (se 2 (by rfl) ⟨1529178, by rfl⟩ : syracuseStep 4077809 = 3058357) B3058357
theorem B2717939 : Blo 1811607 2717939 := bstep (se 1 (by rfl) ⟨2038454, by rfl⟩ : syracuseStep 2717939 = 4076909) B4076909
theorem B4077827 : Blo 1811607 4077827 := bstep (se 1 (by rfl) ⟨3058370, by rfl⟩ : syracuseStep 4077827 = 6116741) B6116741
theorem B2717969 : Blo 1811607 2717969 := bstep (se 2 (by rfl) ⟨1019238, by rfl⟩ : syracuseStep 2717969 = 2038477) B2038477
theorem B2717987 : Blo 1811607 2717987 := bstep (se 1 (by rfl) ⟨2038490, by rfl⟩ : syracuseStep 2717987 = 4076981) B4076981
theorem B2718017 : Blo 1811607 2718017 := bstep (se 2 (by rfl) ⟨1019256, by rfl⟩ : syracuseStep 2718017 = 2038513) B2038513
theorem B7739725 : Blo 1811607 7739725 := bstep (se 3 (by rfl) ⟨1451198, by rfl⟩ : syracuseStep 7739725 = 2902397) B2902397
theorem B6117713 : Blo 1811607 6117713 := bstep (se 2 (by rfl) ⟨2294142, by rfl⟩ : syracuseStep 6117713 = 4588285) B4588285
theorem B2038099 : Blo 1811607 2038099 := bstep (se 1 (by rfl) ⟨1528574, by rfl⟩ : syracuseStep 2038099 = 3057149) B3057149
theorem B2718035 : Blo 1811607 2718035 := bstep (se 1 (by rfl) ⟨2038526, by rfl⟩ : syracuseStep 2718035 = 4077053) B4077053
theorem B8714573 : Blo 1811607 8714573 := bstep (se 3 (by rfl) ⟨1633982, by rfl⟩ : syracuseStep 8714573 = 3267965) B3267965
theorem B2718065 : Blo 1811607 2718065 := bstep (se 2 (by rfl) ⟨1019274, by rfl⟩ : syracuseStep 2718065 = 2038549) B2038549
theorem B2718083 : Blo 1811607 2718083 := bstep (se 1 (by rfl) ⟨2038562, by rfl⟩ : syracuseStep 2718083 = 4077125) B4077125
theorem B2718113 : Blo 1811607 2718113 := bstep (se 2 (by rfl) ⟨1019292, by rfl⟩ : syracuseStep 2718113 = 2038585) B2038585
theorem B9173411 : Blo 1811607 9173411 := bstep (se 1 (by rfl) ⟨6880058, by rfl⟩ : syracuseStep 9173411 = 13760117) B13760117
theorem B2718131 : Blo 1811607 2718131 := bstep (se 1 (by rfl) ⟨2038598, by rfl⟩ : syracuseStep 2718131 = 4077197) B4077197
theorem B2718161 : Blo 1811607 2718161 := bstep (se 2 (by rfl) ⟨1019310, by rfl⟩ : syracuseStep 2718161 = 2038621) B2038621
theorem B2038243 : Blo 1811607 2038243 := bstep (se 1 (by rfl) ⟨1528682, by rfl⟩ : syracuseStep 2038243 = 3057365) B3057365
theorem B2718179 : Blo 1811607 2718179 := bstep (se 1 (by rfl) ⟨2038634, by rfl⟩ : syracuseStep 2718179 = 4077269) B4077269
theorem B2718209 : Blo 1811607 2718209 := bstep (se 2 (by rfl) ⟨1019328, by rfl⟩ : syracuseStep 2718209 = 2038657) B2038657
theorem B4078097 : Blo 1811607 4078097 := bstep (se 2 (by rfl) ⟨1529286, by rfl⟩ : syracuseStep 4078097 = 3058573) B3058573
theorem B2718227 : Blo 1811607 2718227 := bstep (se 1 (by rfl) ⟨2038670, by rfl⟩ : syracuseStep 2718227 = 4077341) B4077341
theorem B4078115 : Blo 1811607 4078115 := bstep (se 1 (by rfl) ⟨3058586, by rfl⟩ : syracuseStep 4078115 = 6117173) B6117173
theorem B2718257 : Blo 1811607 2718257 := bstep (se 2 (by rfl) ⟨1019346, by rfl⟩ : syracuseStep 2718257 = 2038693) B2038693
theorem B2718275 : Blo 1811607 2718275 := bstep (se 1 (by rfl) ⟨2038706, by rfl⟩ : syracuseStep 2718275 = 4077413) B4077413
theorem B2718305 : Blo 1811607 2718305 := bstep (se 2 (by rfl) ⟨1019364, by rfl⟩ : syracuseStep 2718305 = 2038729) B2038729
theorem B5806691 : Blo 1811607 5806691 := bstep (se 1 (by rfl) ⟨4355018, by rfl⟩ : syracuseStep 5806691 = 8710037) B8710037
theorem B2038387 : Blo 1811607 2038387 := bstep (se 1 (by rfl) ⟨1528790, by rfl⟩ : syracuseStep 2038387 = 3057581) B3057581
theorem B2718323 : Blo 1811607 2718323 := bstep (se 1 (by rfl) ⟨2038742, by rfl⟩ : syracuseStep 2718323 = 4077485) B4077485
theorem B4586129 : Blo 1811607 4586129 := bstep (se 2 (by rfl) ⟨1719798, by rfl⟩ : syracuseStep 4586129 = 3439597) B3439597
theorem B2718353 : Blo 1811607 2718353 := bstep (se 2 (by rfl) ⟨1019382, by rfl⟩ : syracuseStep 2718353 = 2038765) B2038765
theorem B2718371 : Blo 1811607 2718371 := bstep (se 1 (by rfl) ⟨2038778, by rfl⟩ : syracuseStep 2718371 = 4077557) B4077557
theorem B2718401 : Blo 1811607 2718401 := bstep (se 2 (by rfl) ⟨1019400, by rfl⟩ : syracuseStep 2718401 = 2038801) B2038801
theorem B4586179 : Blo 1811607 4586179 := bstep (se 1 (by rfl) ⟨3439634, by rfl⟩ : syracuseStep 4586179 = 6879269) B6879269
theorem B2718419 : Blo 1811607 2718419 := bstep (se 1 (by rfl) ⟨2038814, by rfl⟩ : syracuseStep 2718419 = 4077629) B4077629
theorem B3439331 : Blo 1811607 3439331 := bstep (se 1 (by rfl) ⟨2579498, by rfl⟩ : syracuseStep 3439331 = 5158997) B5158997
theorem B5806819 : Blo 1811607 5806819 := bstep (se 1 (by rfl) ⟨4355114, by rfl⟩ : syracuseStep 5806819 = 8710229) B8710229
theorem B2718449 : Blo 1811607 2718449 := bstep (se 2 (by rfl) ⟨1019418, by rfl⟩ : syracuseStep 2718449 = 2038837) B2038837
theorem B2038531 : Blo 1811607 2038531 := bstep (se 1 (by rfl) ⟨1528898, by rfl⟩ : syracuseStep 2038531 = 3057797) B3057797
theorem B2718467 : Blo 1811607 2718467 := bstep (se 1 (by rfl) ⟨2038850, by rfl⟩ : syracuseStep 2718467 = 4077701) B4077701
theorem B9075469 : Blo 1811607 9075469 := bstep (se 3 (by rfl) ⟨1701650, by rfl⟩ : syracuseStep 9075469 = 3403301) B3403301
theorem B2718497 : Blo 1811607 2718497 := bstep (se 2 (by rfl) ⟨1019436, by rfl⟩ : syracuseStep 2718497 = 2038873) B2038873
theorem B4078385 : Blo 1811607 4078385 := bstep (se 2 (by rfl) ⟨1529394, by rfl⟩ : syracuseStep 4078385 = 3058789) B3058789
theorem B2718515 : Blo 1811607 2718515 := bstep (se 1 (by rfl) ⟨2038886, by rfl⟩ : syracuseStep 2718515 = 4077773) B4077773
theorem B4078403 : Blo 1811607 4078403 := bstep (se 1 (by rfl) ⟨3058802, by rfl⟩ : syracuseStep 4078403 = 6117605) B6117605
theorem B4586321 : Blo 1811607 4586321 := bstep (se 2 (by rfl) ⟨1719870, by rfl⟩ : syracuseStep 4586321 = 3439741) B3439741
theorem B2718545 : Blo 1811607 2718545 := bstep (se 2 (by rfl) ⟨1019454, by rfl⟩ : syracuseStep 2718545 = 2038909) B2038909
theorem B2718563 : Blo 1811607 2718563 := bstep (se 1 (by rfl) ⟨2038922, by rfl⟩ : syracuseStep 2718563 = 4077845) B4077845
theorem B11615075 : Blo 1811607 11615075 := bstep (se 1 (by rfl) ⟨8711306, by rfl⟩ : syracuseStep 11615075 = 17422613) B17422613
theorem B6118253 : Blo 1811607 6118253 := bstep (se 3 (by rfl) ⟨1147172, by rfl⟩ : syracuseStep 6118253 = 2294345) B2294345
theorem B2718593 : Blo 1811607 2718593 := bstep (se 2 (by rfl) ⟨1019472, by rfl⟩ : syracuseStep 2718593 = 2038945) B2038945
theorem B2038675 : Blo 1811607 2038675 := bstep (se 1 (by rfl) ⟨1529006, by rfl⟩ : syracuseStep 2038675 = 3058013) B3058013
theorem B2718611 : Blo 1811607 2718611 := bstep (se 1 (by rfl) ⟨2038958, by rfl⟩ : syracuseStep 2718611 = 4077917) B4077917
theorem B6118307 : Blo 1811607 6118307 := bstep (se 1 (by rfl) ⟨4588730, by rfl⟩ : syracuseStep 6118307 = 9177461) B9177461
theorem B10320817 : Blo 1811607 10320817 := bstep (se 2 (by rfl) ⟨3870306, by rfl⟩ : syracuseStep 10320817 = 7740613) B7740613
theorem B2718641 : Blo 1811607 2718641 := bstep (se 2 (by rfl) ⟨1019490, by rfl⟩ : syracuseStep 2718641 = 2038981) B2038981
theorem B2718659 : Blo 1811607 2718659 := bstep (se 1 (by rfl) ⟨2038994, by rfl⟩ : syracuseStep 2718659 = 4077989) B4077989
theorem B2718689 : Blo 1811607 2718689 := bstep (se 2 (by rfl) ⟨1019508, by rfl⟩ : syracuseStep 2718689 = 2039017) B2039017
theorem B2178019 : Blo 1811607 2178019 := bstep (se 1 (by rfl) ⟨1633514, by rfl⟩ : syracuseStep 2178019 = 3267029) B3267029
theorem B6880241 : Blo 1811607 6880241 := bstep (se 2 (by rfl) ⟨2580090, by rfl⟩ : syracuseStep 6880241 = 5160181) B5160181
theorem B2718707 : Blo 1811607 2718707 := bstep (se 1 (by rfl) ⟨2039030, by rfl⟩ : syracuseStep 2718707 = 4078061) B4078061
theorem B5159953 : Blo 1811607 5159953 := bstep (se 2 (by rfl) ⟨1934982, by rfl⟩ : syracuseStep 5159953 = 3869965) B3869965
theorem B2718737 : Blo 1811607 2718737 := bstep (se 2 (by rfl) ⟨1019526, by rfl⟩ : syracuseStep 2718737 = 2039053) B2039053
theorem B2038819 : Blo 1811607 2038819 := bstep (se 1 (by rfl) ⟨1529114, by rfl⟩ : syracuseStep 2038819 = 3058229) B3058229
theorem B2718755 : Blo 1811607 2718755 := bstep (se 1 (by rfl) ⟨2039066, by rfl⟩ : syracuseStep 2718755 = 4078133) B4078133
theorem B5807153 : Blo 1811607 5807153 := bstep (se 2 (by rfl) ⟨2177682, by rfl⟩ : syracuseStep 5807153 = 4355365) B4355365
theorem B2579521 : Blo 1811607 2579521 := bstep (se 2 (by rfl) ⟨967320, by rfl⟩ : syracuseStep 2579521 = 1934641) B1934641
theorem B2718785 : Blo 1811607 2718785 := bstep (se 2 (by rfl) ⟨1019544, by rfl⟩ : syracuseStep 2718785 = 2039089) B2039089
theorem B4078673 : Blo 1811607 4078673 := bstep (se 2 (by rfl) ⟨1529502, by rfl⟩ : syracuseStep 4078673 = 3059005) B3059005
theorem B2718803 : Blo 1811607 2718803 := bstep (se 1 (by rfl) ⟨2039102, by rfl⟩ : syracuseStep 2718803 = 4078205) B4078205
theorem B4078691 : Blo 1811607 4078691 := bstep (se 1 (by rfl) ⟨3059018, by rfl⟩ : syracuseStep 4078691 = 6118037) B6118037
theorem B2718833 : Blo 1811607 2718833 := bstep (se 2 (by rfl) ⟨1019562, by rfl⟩ : syracuseStep 2718833 = 2039125) B2039125
theorem B2718851 : Blo 1811607 2718851 := bstep (se 1 (by rfl) ⟨2039138, by rfl⟩ : syracuseStep 2718851 = 4078277) B4078277
theorem B2718881 : Blo 1811607 2718881 := bstep (se 2 (by rfl) ⟨1019580, by rfl⟩ : syracuseStep 2718881 = 2039161) B2039161
theorem B6118577 : Blo 1811607 6118577 := bstep (se 2 (by rfl) ⟨2294466, by rfl⟩ : syracuseStep 6118577 = 4588933) B4588933
theorem B2579635 : Blo 1811607 2579635 := bstep (se 1 (by rfl) ⟨1934726, by rfl⟩ : syracuseStep 2579635 = 3869453) B3869453
theorem B2038963 : Blo 1811607 2038963 := bstep (se 1 (by rfl) ⟨1529222, by rfl⟩ : syracuseStep 2038963 = 3058445) B3058445
theorem B2718899 : Blo 1811607 2718899 := bstep (se 1 (by rfl) ⟨2039174, by rfl⟩ : syracuseStep 2718899 = 4078349) B4078349
theorem B9174221 : Blo 1811607 9174221 := bstep (se 3 (by rfl) ⟨1720166, by rfl⟩ : syracuseStep 9174221 = 3440333) B3440333
theorem B2718929 : Blo 1811607 2718929 := bstep (se 2 (by rfl) ⟨1019598, by rfl⟩ : syracuseStep 2718929 = 2039197) B2039197
theorem B2718947 : Blo 1811607 2718947 := bstep (se 1 (by rfl) ⟨2039210, by rfl⟩ : syracuseStep 2718947 = 4078421) B4078421
theorem B2718977 : Blo 1811607 2718977 := bstep (se 2 (by rfl) ⟨1019616, by rfl⟩ : syracuseStep 2718977 = 2039233) B2039233
theorem B2718995 : Blo 1811607 2718995 := bstep (se 1 (by rfl) ⟨2039246, by rfl⟩ : syracuseStep 2718995 = 4078493) B4078493
theorem B2719025 : Blo 1811607 2719025 := bstep (se 2 (by rfl) ⟨1019634, by rfl⟩ : syracuseStep 2719025 = 2039269) B2039269
theorem B2039107 : Blo 1811607 2039107 := bstep (se 1 (by rfl) ⟨1529330, by rfl⟩ : syracuseStep 2039107 = 3058661) B3058661
theorem B2719043 : Blo 1811607 2719043 := bstep (se 1 (by rfl) ⟨2039282, by rfl⟩ : syracuseStep 2719043 = 4078565) B4078565
theorem B2719073 : Blo 1811607 2719073 := bstep (se 2 (by rfl) ⟨1019652, by rfl⟩ : syracuseStep 2719073 = 2039305) B2039305
theorem B7740785 : Blo 1811607 7740785 := bstep (se 2 (by rfl) ⟨2902794, by rfl⟩ : syracuseStep 7740785 = 5805589) B5805589
theorem B2719091 : Blo 1811607 2719091 := bstep (se 1 (by rfl) ⟨2039318, by rfl⟩ : syracuseStep 2719091 = 4078637) B4078637
theorem B4078961 : Blo 1811607 4078961 := bstep (se 2 (by rfl) ⟨1529610, by rfl⟩ : syracuseStep 4078961 = 3059221) B3059221
theorem B4078979 : Blo 1811607 4078979 := bstep (se 1 (by rfl) ⟨3059234, by rfl⟩ : syracuseStep 4078979 = 6118469) B6118469
theorem B2719121 : Blo 1811607 2719121 := bstep (se 2 (by rfl) ⟨1019670, by rfl⟩ : syracuseStep 2719121 = 2039341) B2039341
theorem B2719139 : Blo 1811607 2719139 := bstep (se 1 (by rfl) ⟨2039354, by rfl⟩ : syracuseStep 2719139 = 4078709) B4078709
theorem B2719169 : Blo 1811607 2719169 := bstep (se 2 (by rfl) ⟨1019688, by rfl⟩ : syracuseStep 2719169 = 2039377) B2039377
theorem B2039251 : Blo 1811607 2039251 := bstep (se 1 (by rfl) ⟨1529438, by rfl⟩ : syracuseStep 2039251 = 3058877) B3058877
theorem B2719187 : Blo 1811607 2719187 := bstep (se 1 (by rfl) ⟨2039390, by rfl⟩ : syracuseStep 2719187 = 4078781) B4078781
theorem B2719217 : Blo 1811607 2719217 := bstep (se 2 (by rfl) ⟨1019706, by rfl⟩ : syracuseStep 2719217 = 2039413) B2039413
theorem B2719235 : Blo 1811607 2719235 := bstep (se 1 (by rfl) ⟨2039426, by rfl⟩ : syracuseStep 2719235 = 4078853) B4078853
theorem B13762061 : Blo 1811607 13762061 := bstep (se 3 (by rfl) ⟨2580386, by rfl⟩ : syracuseStep 13762061 = 5160773) B5160773
theorem B2293267 : Blo 1811607 2293267 := bstep (se 1 (by rfl) ⟨1719950, by rfl⟩ : syracuseStep 2293267 = 3439901) B3439901
theorem B2719265 : Blo 1811607 2719265 := bstep (se 2 (by rfl) ⟨1019724, by rfl⟩ : syracuseStep 2719265 = 2039449) B2039449
theorem B2719283 : Blo 1811607 2719283 := bstep (se 1 (by rfl) ⟨2039462, by rfl⟩ : syracuseStep 2719283 = 4078925) B4078925
theorem B2719313 : Blo 1811607 2719313 := bstep (se 2 (by rfl) ⟨1019742, by rfl⟩ : syracuseStep 2719313 = 2039485) B2039485
theorem B3440227 : Blo 1811607 3440227 := bstep (se 1 (by rfl) ⟨2580170, by rfl⟩ : syracuseStep 3440227 = 5160341) B5160341
theorem B2039395 : Blo 1811607 2039395 := bstep (se 1 (by rfl) ⟨1529546, by rfl⟩ : syracuseStep 2039395 = 3059093) B3059093
theorem B2719331 : Blo 1811607 2719331 := bstep (se 1 (by rfl) ⟨2039498, by rfl⟩ : syracuseStep 2719331 = 4078997) B4078997
theorem B2293363 : Blo 1811607 2293363 := bstep (se 1 (by rfl) ⟨1720022, by rfl⟩ : syracuseStep 2293363 = 3440045) B3440045
theorem B2719361 : Blo 1811607 2719361 := bstep (se 2 (by rfl) ⟨1019760, by rfl⟩ : syracuseStep 2719361 = 2039521) B2039521
theorem B6200963 : Blo 1811607 6200963 := bstep (se 1 (by rfl) ⟨4650722, by rfl⟩ : syracuseStep 6200963 = 9301445) B9301445
theorem B6880909 : Blo 1811607 6880909 := bstep (se 3 (by rfl) ⟨1290170, by rfl⟩ : syracuseStep 6880909 = 2580341) B2580341
theorem B4079249 : Blo 1811607 4079249 := bstep (se 2 (by rfl) ⟨1529718, by rfl⟩ : syracuseStep 4079249 = 3059437) B3059437
theorem B2719379 : Blo 1811607 2719379 := bstep (se 1 (by rfl) ⟨2039534, by rfl⟩ : syracuseStep 2719379 = 4079069) B4079069
theorem B4079267 : Blo 1811607 4079267 := bstep (se 1 (by rfl) ⟨3059450, by rfl⟩ : syracuseStep 4079267 = 6118901) B6118901
theorem B2719409 : Blo 1811607 2719409 := bstep (se 2 (by rfl) ⟨1019778, by rfl⟩ : syracuseStep 2719409 = 2039557) B2039557
theorem B2719427 : Blo 1811607 2719427 := bstep (se 1 (by rfl) ⟨2039570, by rfl⟩ : syracuseStep 2719427 = 4079141) B4079141
theorem B6119117 : Blo 1811607 6119117 := bstep (se 3 (by rfl) ⟨1147334, by rfl⟩ : syracuseStep 6119117 = 2294669) B2294669
theorem B2719457 : Blo 1811607 2719457 := bstep (se 2 (by rfl) ⟨1019796, by rfl⟩ : syracuseStep 2719457 = 2039593) B2039593
theorem B2039539 : Blo 1811607 2039539 := bstep (se 1 (by rfl) ⟨1529654, by rfl⟩ : syracuseStep 2039539 = 3059309) B3059309
theorem B2719475 : Blo 1811607 2719475 := bstep (se 1 (by rfl) ⟨2039606, by rfl⟩ : syracuseStep 2719475 = 4079213) B4079213
theorem B3440387 : Blo 1811607 3440387 := bstep (se 1 (by rfl) ⟨2580290, by rfl⟩ : syracuseStep 3440387 = 5160581) B5160581
theorem B6119171 : Blo 1811607 6119171 := bstep (se 1 (by rfl) ⟨4589378, by rfl⟩ : syracuseStep 6119171 = 9178757) B9178757
theorem B2719505 : Blo 1811607 2719505 := bstep (se 2 (by rfl) ⟨1019814, by rfl⟩ : syracuseStep 2719505 = 2039629) B2039629
theorem B2719523 : Blo 1811607 2719523 := bstep (se 1 (by rfl) ⟨2039642, by rfl⟩ : syracuseStep 2719523 = 4079285) B4079285
theorem B2449201 : Blo 1811607 2449201 := bstep (se 2 (by rfl) ⟨918450, by rfl⟩ : syracuseStep 2449201 = 1836901) B1836901
theorem B4587313 : Blo 1811607 4587313 := bstep (se 2 (by rfl) ⟨1720242, by rfl⟩ : syracuseStep 4587313 = 3440485) B3440485
theorem B2719553 : Blo 1811607 2719553 := bstep (se 2 (by rfl) ⟨1019832, by rfl⟩ : syracuseStep 2719553 = 2039665) B2039665
theorem B6201155 : Blo 1811607 6201155 := bstep (se 1 (by rfl) ⟨4650866, by rfl⟩ : syracuseStep 6201155 = 9301733) B9301733
theorem B2719571 : Blo 1811607 2719571 := bstep (se 1 (by rfl) ⟨2039678, by rfl⟩ : syracuseStep 2719571 = 4079357) B4079357
theorem B35307377 : Blo 1811607 35307377 := bstep (se 2 (by rfl) ⟨13240266, by rfl⟩ : syracuseStep 35307377 = 26480533) B26480533
theorem B2449265 : Blo 1811607 2449265 := bstep (se 2 (by rfl) ⟨918474, by rfl⟩ : syracuseStep 2449265 = 1836949) B1836949
theorem B2719601 : Blo 1811607 2719601 := bstep (se 2 (by rfl) ⟨1019850, by rfl⟩ : syracuseStep 2719601 = 2039701) B2039701
theorem B2039683 : Blo 1811607 2039683 := bstep (se 1 (by rfl) ⟨1529762, by rfl⟩ : syracuseStep 2039683 = 3059525) B3059525
theorem B2719619 : Blo 1811607 2719619 := bstep (se 1 (by rfl) ⟨2039714, by rfl⟩ : syracuseStep 2719619 = 4079429) B4079429
theorem B2719649 : Blo 1811607 2719649 := bstep (se 2 (by rfl) ⟨1019868, by rfl⟩ : syracuseStep 2719649 = 2039737) B2039737
theorem B4079537 : Blo 1811607 4079537 := bstep (se 2 (by rfl) ⟨1529826, by rfl⟩ : syracuseStep 4079537 = 3059653) B3059653
theorem B2719667 : Blo 1811607 2719667 := bstep (se 1 (by rfl) ⟨2039750, by rfl⟩ : syracuseStep 2719667 = 4079501) B4079501
theorem B4079555 : Blo 1811607 4079555 := bstep (se 1 (by rfl) ⟨3059666, by rfl⟩ : syracuseStep 4079555 = 6119333) B6119333
theorem B2719697 : Blo 1811607 2719697 := bstep (se 2 (by rfl) ⟨1019886, by rfl⟩ : syracuseStep 2719697 = 2039773) B2039773
theorem B2719715 : Blo 1811607 2719715 := bstep (se 1 (by rfl) ⟨2039786, by rfl⟩ : syracuseStep 2719715 = 4079573) B4079573
theorem B11608049 : Blo 1811607 11608049 := bstep (se 2 (by rfl) ⟨4353018, by rfl⟩ : syracuseStep 11608049 = 8706037) B8706037
theorem B4079627 : Blo 1811607 4079627 := bstep (se 1 (by rfl) ⟨3059720, by rfl⟩ : syracuseStep 4079627 = 6119441) B6119441
theorem B2719769 : Blo 1811607 2719769 := bstep (se 2 (by rfl) ⟨1019913, by rfl⟩ : syracuseStep 2719769 = 2039827) B2039827
theorem B2039863 : Blo 1811607 2039863 := bstep (se 1 (by rfl) ⟨1529897, by rfl⟩ : syracuseStep 2039863 = 3059795) B3059795
theorem B4079681 : Blo 1811607 4079681 := bstep (se 2 (by rfl) ⟨1529880, by rfl⟩ : syracuseStep 4079681 = 3059761) B3059761
theorem B2719883 : Blo 1811607 2719883 := bstep (se 1 (by rfl) ⟨2039912, by rfl⟩ : syracuseStep 2719883 = 4079825) B4079825
theorem B17662103 : Blo 1811607 17662103 := bstep (se 1 (by rfl) ⟨13246577, by rfl⟩ : syracuseStep 17662103 = 26493155) B26493155
theorem B2719895 : Blo 1811607 2719895 := bstep (se 1 (by rfl) ⟨2039921, by rfl⟩ : syracuseStep 2719895 = 4079843) B4079843
theorem B6619315 : Blo 1811607 6619315 := bstep (se 1 (by rfl) ⟨4964486, by rfl⟩ : syracuseStep 6619315 = 9928973) B9928973
theorem B3440819 : Blo 1811607 3440819 := bstep (se 1 (by rfl) ⟨2580614, by rfl⟩ : syracuseStep 3440819 = 5161229) B5161229
theorem B6119603 : Blo 1811607 6119603 := bstep (se 1 (by rfl) ⟨4589702, by rfl⟩ : syracuseStep 6119603 = 9179405) B9179405
theorem B2719961 : Blo 1811607 2719961 := bstep (se 2 (by rfl) ⟨1019985, by rfl⟩ : syracuseStep 2719961 = 2039971) B2039971
theorem B2040043 : Blo 1811607 2040043 := bstep (se 1 (by rfl) ⟨1530032, by rfl⟩ : syracuseStep 2040043 = 3060065) B3060065
theorem B4587799 : Blo 1811607 4587799 := bstep (se 1 (by rfl) ⟨3440849, by rfl⟩ : syracuseStep 4587799 = 6881699) B6881699
theorem B4079897 : Blo 1811607 4079897 := bstep (se 2 (by rfl) ⟨1529961, by rfl⟩ : syracuseStep 4079897 = 3059923) B3059923
theorem B3440971 : Blo 1811607 3440971 := bstep (se 1 (by rfl) ⟨2580728, by rfl⟩ : syracuseStep 3440971 = 5161457) B5161457
theorem B2720075 : Blo 1811607 2720075 := bstep (se 1 (by rfl) ⟨2040056, by rfl⟩ : syracuseStep 2720075 = 4080113) B4080113
theorem B2720087 : Blo 1811607 2720087 := bstep (se 1 (by rfl) ⟨2040065, by rfl⟩ : syracuseStep 2720087 = 4080131) B4080131
theorem B2040151 : Blo 1811607 2040151 := bstep (se 1 (by rfl) ⟨1530113, by rfl⟩ : syracuseStep 2040151 = 3060227) B3060227
theorem B4079987 : Blo 1811607 4079987 := bstep (se 1 (by rfl) ⟨3059990, by rfl⟩ : syracuseStep 4079987 = 6119981) B6119981
theorem B4080023 : Blo 1811607 4080023 := bstep (se 1 (by rfl) ⟨3060017, by rfl⟩ : syracuseStep 4080023 = 6120035) B6120035
theorem B2720153 : Blo 1811607 2720153 := bstep (se 2 (by rfl) ⟨1020057, by rfl⟩ : syracuseStep 2720153 = 2040115) B2040115
theorem B6119873 : Blo 1811607 6119873 := bstep (se 2 (by rfl) ⟨2294952, by rfl⟩ : syracuseStep 6119873 = 4589905) B4589905
theorem B13763033 : Blo 1811607 13763033 := bstep (se 2 (by rfl) ⟨5161137, by rfl⟩ : syracuseStep 13763033 = 10322275) B10322275
theorem B2720267 : Blo 1811607 2720267 := bstep (se 1 (by rfl) ⟨2040200, by rfl⟩ : syracuseStep 2720267 = 4080401) B4080401
theorem B2720279 : Blo 1811607 2720279 := bstep (se 1 (by rfl) ⟨2040209, by rfl⟩ : syracuseStep 2720279 = 4080419) B4080419
theorem B6881867 : Blo 1811607 6881867 := bstep (se 1 (by rfl) ⟨5161400, by rfl⟩ : syracuseStep 6881867 = 10322801) B10322801
theorem B4080203 : Blo 1811607 4080203 := bstep (se 1 (by rfl) ⟨3060152, by rfl⟩ : syracuseStep 4080203 = 6120305) B6120305
theorem B6881881 : Blo 1811607 6881881 := bstep (se 2 (by rfl) ⟨2580705, by rfl⟩ : syracuseStep 6881881 = 5161411) B5161411
theorem B2720345 : Blo 1811607 2720345 := bstep (se 2 (by rfl) ⟨1020129, by rfl⟩ : syracuseStep 2720345 = 2040259) B2040259
theorem B4080257 : Blo 1811607 4080257 := bstep (se 2 (by rfl) ⟨1530096, by rfl⟩ : syracuseStep 4080257 = 3060193) B3060193
theorem B3441305 : Blo 1811607 3441305 := bstep (se 2 (by rfl) ⟨1290489, by rfl⟩ : syracuseStep 3441305 = 2580979) B2580979
theorem B4588235 : Blo 1811607 4588235 := bstep (se 1 (by rfl) ⟨3441176, by rfl⟩ : syracuseStep 4588235 = 6882353) B6882353
theorem B4080473 : Blo 1811607 4080473 := bstep (se 2 (by rfl) ⟨1530177, by rfl⟩ : syracuseStep 4080473 = 3060355) B3060355
theorem B4080563 : Blo 1811607 4080563 := bstep (se 1 (by rfl) ⟨3060422, by rfl⟩ : syracuseStep 4080563 = 6120845) B6120845
theorem B4080599 : Blo 1811607 4080599 := bstep (se 1 (by rfl) ⟨3060449, by rfl⟩ : syracuseStep 4080599 = 6120899) B6120899
theorem B7742425 : Blo 1811607 7742425 := bstep (se 2 (by rfl) ⟨2903409, by rfl⟩ : syracuseStep 7742425 = 5806819) B5806819
theorem B6120413 : Blo 1811607 6120413 := bstep (se 3 (by rfl) ⟨1147577, by rfl⟩ : syracuseStep 6120413 = 2295155) B2295155
theorem B13771781 : Blo 1811607 13771781 := bstep (se 4 (by rfl) ⟨1291104, by rfl⟩ : syracuseStep 13771781 = 2582209) B2582209
theorem B12100625 : Blo 1811607 12100625 := bstep (se 2 (by rfl) ⟨4537734, by rfl⟩ : syracuseStep 12100625 = 9075469) B9075469
theorem B4416563 : Blo 1811607 4416563 := bstep (se 1 (by rfl) ⟨3312422, by rfl⟩ : syracuseStep 4416563 = 6624845) B6624845
theorem B4588609 : Blo 1811607 4588609 := bstep (se 2 (by rfl) ⟨1720728, by rfl⟩ : syracuseStep 4588609 = 3441457) B3441457
theorem B15492161 : Blo 1811607 15492161 := bstep (se 2 (by rfl) ⟨5809560, by rfl⟩ : syracuseStep 15492161 = 11619121) B11619121
theorem B12575875 : Blo 1811607 12575875 := bstep (se 1 (by rfl) ⟨9431906, by rfl⟩ : syracuseStep 12575875 = 18863813) B18863813
theorem B1811607 : Blo 1811607 1811607 := bstep (se 1 (by rfl) ⟨1358705, by rfl⟩ : syracuseStep 1811607 = 2717411) B2717411
theorem B2450585 : Blo 1811607 2450585 := bstep (se 2 (by rfl) ⟨918969, by rfl⟩ : syracuseStep 2450585 = 1837939) B1837939
theorem B1811627 : Blo 1811607 1811627 := bstep (se 1 (by rfl) ⟨1358720, by rfl⟩ : syracuseStep 1811627 = 2717441) B2717441
theorem B223323317 : Blo 1811607 223323317 := bstep (se 5 (by rfl) ⟨10468280, by rfl⟩ : syracuseStep 223323317 = 20936561) B20936561
theorem B1811639 : Blo 1811607 1811639 := bstep (se 1 (by rfl) ⟨1358729, by rfl⟩ : syracuseStep 1811639 = 2717459) B2717459
theorem B1811659 : Blo 1811607 1811659 := bstep (se 1 (by rfl) ⟨1358744, by rfl⟩ : syracuseStep 1811659 = 2717489) B2717489
theorem B1811671 : Blo 1811607 1811671 := bstep (se 1 (by rfl) ⟨1358753, by rfl⟩ : syracuseStep 1811671 = 2717507) B2717507
theorem B1811691 : Blo 1811607 1811691 := bstep (se 1 (by rfl) ⟨1358768, by rfl⟩ : syracuseStep 1811691 = 2717537) B2717537
theorem B1811703 : Blo 1811607 1811703 := bstep (se 1 (by rfl) ⟨1358777, by rfl⟩ : syracuseStep 1811703 = 2717555) B2717555
theorem B1811723 : Blo 1811607 1811723 := bstep (se 1 (by rfl) ⟨1358792, by rfl⟩ : syracuseStep 1811723 = 2717585) B2717585
theorem B1811735 : Blo 1811607 1811735 := bstep (se 1 (by rfl) ⟨1358801, by rfl⟩ : syracuseStep 1811735 = 2717603) B2717603
theorem B3441943 : Blo 1811607 3441943 := bstep (se 1 (by rfl) ⟨2581457, by rfl⟩ : syracuseStep 3441943 = 5162915) B5162915
theorem B1811755 : Blo 1811607 1811755 := bstep (se 1 (by rfl) ⟨1358816, by rfl⟩ : syracuseStep 1811755 = 2717633) B2717633
theorem B1811767 : Blo 1811607 1811767 := bstep (se 1 (by rfl) ⟨1358825, by rfl⟩ : syracuseStep 1811767 = 2717651) B2717651
theorem B1811787 : Blo 1811607 1811787 := bstep (se 1 (by rfl) ⟨1358840, by rfl⟩ : syracuseStep 1811787 = 2717681) B2717681
theorem B1811799 : Blo 1811607 1811799 := bstep (se 1 (by rfl) ⟨1358849, by rfl⟩ : syracuseStep 1811799 = 2717699) B2717699
theorem B1811819 : Blo 1811607 1811819 := bstep (se 1 (by rfl) ⟨1358864, by rfl⟩ : syracuseStep 1811819 = 2717729) B2717729
theorem B1811831 : Blo 1811607 1811831 := bstep (se 1 (by rfl) ⟨1358873, by rfl⟩ : syracuseStep 1811831 = 2717747) B2717747
theorem B1836427 : Blo 1811607 1836427 := bstep (se 1 (by rfl) ⟨1377320, by rfl⟩ : syracuseStep 1836427 = 2754641) B2754641
theorem B1811851 : Blo 1811607 1811851 := bstep (se 1 (by rfl) ⟨1358888, by rfl⟩ : syracuseStep 1811851 = 2717777) B2717777
theorem B1811863 : Blo 1811607 1811863 := bstep (se 1 (by rfl) ⟨1358897, by rfl⟩ : syracuseStep 1811863 = 2717795) B2717795
theorem B2581913 : Blo 1811607 2581913 := bstep (se 2 (by rfl) ⟨968217, by rfl⟩ : syracuseStep 2581913 = 1936435) B1936435
theorem B1811883 : Blo 1811607 1811883 := bstep (se 1 (by rfl) ⟨1358912, by rfl⟩ : syracuseStep 1811883 = 2717825) B2717825
theorem B1811895 : Blo 1811607 1811895 := bstep (se 1 (by rfl) ⟨1358921, by rfl⟩ : syracuseStep 1811895 = 2717843) B2717843
theorem B1811915 : Blo 1811607 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B1811927 : Blo 1811607 1811927 := bstep (se 1 (by rfl) ⟨1358945, by rfl⟩ : syracuseStep 1811927 = 2717891) B2717891
theorem B1811947 : Blo 1811607 1811947 := bstep (se 1 (by rfl) ⟨1358960, by rfl⟩ : syracuseStep 1811947 = 2717921) B2717921
theorem B1811959 : Blo 1811607 1811959 := bstep (se 1 (by rfl) ⟨1358969, by rfl⟩ : syracuseStep 1811959 = 2717939) B2717939
theorem B1811979 : Blo 1811607 1811979 := bstep (se 1 (by rfl) ⟨1358984, by rfl⟩ : syracuseStep 1811979 = 2717969) B2717969
theorem B2295307 : Blo 1811607 2295307 := bstep (se 1 (by rfl) ⟨1721480, by rfl⟩ : syracuseStep 2295307 = 3442961) B3442961
theorem B1811991 : Blo 1811607 1811991 := bstep (se 1 (by rfl) ⟨1358993, by rfl⟩ : syracuseStep 1811991 = 2717987) B2717987
theorem B6882839 : Blo 1811607 6882839 := bstep (se 1 (by rfl) ⟨5162129, by rfl⟩ : syracuseStep 6882839 = 10324259) B10324259
theorem B1812011 : Blo 1811607 1812011 := bstep (se 1 (by rfl) ⟨1359008, by rfl⟩ : syracuseStep 1812011 = 2718017) B2718017
theorem B13067821 : Blo 1811607 13067821 := bstep (se 3 (by rfl) ⟨2450216, by rfl⟩ : syracuseStep 13067821 = 4900433) B4900433
theorem B5809715 : Blo 1811607 5809715 := bstep (se 1 (by rfl) ⟨4357286, by rfl⟩ : syracuseStep 5809715 = 8714573) B8714573
theorem B1812023 : Blo 1811607 1812023 := bstep (se 1 (by rfl) ⟨1359017, by rfl⟩ : syracuseStep 1812023 = 2718035) B2718035
theorem B1934923 : Blo 1811607 1934923 := bstep (se 1 (by rfl) ⟨1451192, by rfl⟩ : syracuseStep 1934923 = 2902385) B2902385
theorem B1812043 : Blo 1811607 1812043 := bstep (se 1 (by rfl) ⟨1359032, by rfl⟩ : syracuseStep 1812043 = 2718065) B2718065
theorem B9176651 : Blo 1811607 9176651 := bstep (se 1 (by rfl) ⟨6882488, by rfl⟩ : syracuseStep 9176651 = 13764977) B13764977
theorem B1812055 : Blo 1811607 1812055 := bstep (se 1 (by rfl) ⟨1359041, by rfl⟩ : syracuseStep 1812055 = 2718083) B2718083
theorem B23234141 : Blo 1811607 23234141 := bstep (se 3 (by rfl) ⟨4356401, by rfl⟩ : syracuseStep 23234141 = 8712803) B8712803
theorem B1812075 : Blo 1811607 1812075 := bstep (se 1 (by rfl) ⟨1359056, by rfl⟩ : syracuseStep 1812075 = 2718113) B2718113
theorem B1812087 : Blo 1811607 1812087 := bstep (se 1 (by rfl) ⟨1359065, by rfl⟩ : syracuseStep 1812087 = 2718131) B2718131
theorem B1812107 : Blo 1811607 1812107 := bstep (se 1 (by rfl) ⟨1359080, by rfl⟩ : syracuseStep 1812107 = 2718161) B2718161
theorem B1812119 : Blo 1811607 1812119 := bstep (se 1 (by rfl) ⟨1359089, by rfl⟩ : syracuseStep 1812119 = 2718179) B2718179
theorem B4589207 : Blo 1811607 4589207 := bstep (se 1 (by rfl) ⟨3441905, by rfl⟩ : syracuseStep 4589207 = 6883811) B6883811
theorem B1812139 : Blo 1811607 1812139 := bstep (se 1 (by rfl) ⟨1359104, by rfl⟩ : syracuseStep 1812139 = 2718209) B2718209
theorem B1812151 : Blo 1811607 1812151 := bstep (se 1 (by rfl) ⟨1359113, by rfl⟩ : syracuseStep 1812151 = 2718227) B2718227
theorem B1812171 : Blo 1811607 1812171 := bstep (se 1 (by rfl) ⟨1359128, by rfl⟩ : syracuseStep 1812171 = 2718257) B2718257
theorem B1812183 : Blo 1811607 1812183 := bstep (se 1 (by rfl) ⟨1359137, by rfl⟩ : syracuseStep 1812183 = 2718275) B2718275
theorem B1812203 : Blo 1811607 1812203 := bstep (se 1 (by rfl) ⟨1359152, by rfl⟩ : syracuseStep 1812203 = 2718305) B2718305
theorem B1812215 : Blo 1811607 1812215 := bstep (se 1 (by rfl) ⟨1359161, by rfl⟩ : syracuseStep 1812215 = 2718323) B2718323
theorem B3057419 : Blo 1811607 3057419 := bstep (se 1 (by rfl) ⟨2293064, by rfl⟩ : syracuseStep 3057419 = 4586129) B4586129
theorem B1812235 : Blo 1811607 1812235 := bstep (se 1 (by rfl) ⟨1359176, by rfl⟩ : syracuseStep 1812235 = 2718353) B2718353
theorem B13428497 : Blo 1811607 13428497 := bstep (se 2 (by rfl) ⟨5035686, by rfl⟩ : syracuseStep 13428497 = 10071373) B10071373
theorem B1812247 : Blo 1811607 1812247 := bstep (se 1 (by rfl) ⟨1359185, by rfl⟩ : syracuseStep 1812247 = 2718371) B2718371
theorem B1812267 : Blo 1811607 1812267 := bstep (se 1 (by rfl) ⟨1359200, by rfl⟩ : syracuseStep 1812267 = 2718401) B2718401
theorem B1812279 : Blo 1811607 1812279 := bstep (se 1 (by rfl) ⟨1359209, by rfl⟩ : syracuseStep 1812279 = 2718419) B2718419
theorem B1812299 : Blo 1811607 1812299 := bstep (se 1 (by rfl) ⟨1359224, by rfl⟩ : syracuseStep 1812299 = 2718449) B2718449
theorem B1812311 : Blo 1811607 1812311 := bstep (se 1 (by rfl) ⟨1359233, by rfl⟩ : syracuseStep 1812311 = 2718467) B2718467
theorem B1812331 : Blo 1811607 1812331 := bstep (se 1 (by rfl) ⟨1359248, by rfl⟩ : syracuseStep 1812331 = 2718497) B2718497
theorem B1812343 : Blo 1811607 1812343 := bstep (se 1 (by rfl) ⟨1359257, by rfl⟩ : syracuseStep 1812343 = 2718515) B2718515
theorem B3057547 : Blo 1811607 3057547 := bstep (se 1 (by rfl) ⟨2293160, by rfl⟩ : syracuseStep 3057547 = 4586321) B4586321
theorem B1812363 : Blo 1811607 1812363 := bstep (se 1 (by rfl) ⟨1359272, by rfl⟩ : syracuseStep 1812363 = 2718545) B2718545
theorem B1812375 : Blo 1811607 1812375 := bstep (se 1 (by rfl) ⟨1359281, by rfl⟩ : syracuseStep 1812375 = 2718563) B2718563
theorem B7743383 : Blo 1811607 7743383 := bstep (se 1 (by rfl) ⟨5807537, by rfl⟩ : syracuseStep 7743383 = 11615075) B11615075
theorem B1812395 : Blo 1811607 1812395 := bstep (se 1 (by rfl) ⟨1359296, by rfl⟩ : syracuseStep 1812395 = 2718593) B2718593
theorem B14698417 : Blo 1811607 14698417 := bstep (se 2 (by rfl) ⟨5511906, by rfl⟩ : syracuseStep 14698417 = 11023813) B11023813
theorem B1812407 : Blo 1811607 1812407 := bstep (se 1 (by rfl) ⟨1359305, by rfl⟩ : syracuseStep 1812407 = 2718611) B2718611
theorem B1812427 : Blo 1811607 1812427 := bstep (se 1 (by rfl) ⟨1359320, by rfl⟩ : syracuseStep 1812427 = 2718641) B2718641
theorem B1812439 : Blo 1811607 1812439 := bstep (se 1 (by rfl) ⟨1359329, by rfl⟩ : syracuseStep 1812439 = 2718659) B2718659
theorem B1812459 : Blo 1811607 1812459 := bstep (se 1 (by rfl) ⟨1359344, by rfl⟩ : syracuseStep 1812459 = 2718689) B2718689
theorem B1812471 : Blo 1811607 1812471 := bstep (se 1 (by rfl) ⟨1359353, by rfl⟩ : syracuseStep 1812471 = 2718707) B2718707
theorem B1812491 : Blo 1811607 1812491 := bstep (se 1 (by rfl) ⟨1359368, by rfl⟩ : syracuseStep 1812491 = 2718737) B2718737
theorem B1812503 : Blo 1811607 1812503 := bstep (se 1 (by rfl) ⟨1359377, by rfl⟩ : syracuseStep 1812503 = 2718755) B2718755
theorem B3057689 : Blo 1811607 3057689 := bstep (se 2 (by rfl) ⟨1146633, by rfl⟩ : syracuseStep 3057689 = 2293267) B2293267
theorem B1812523 : Blo 1811607 1812523 := bstep (se 1 (by rfl) ⟨1359392, by rfl⟩ : syracuseStep 1812523 = 2718785) B2718785
theorem B1812535 : Blo 1811607 1812535 := bstep (se 1 (by rfl) ⟨1359401, by rfl⟩ : syracuseStep 1812535 = 2718803) B2718803
theorem B4909121 : Blo 1811607 4909121 := bstep (se 2 (by rfl) ⟨1840920, by rfl⟩ : syracuseStep 4909121 = 3681841) B3681841
theorem B1812555 : Blo 1811607 1812555 := bstep (se 1 (by rfl) ⟨1359416, by rfl⟩ : syracuseStep 1812555 = 2718833) B2718833
theorem B3442763 : Blo 1811607 3442763 := bstep (se 1 (by rfl) ⟨2582072, by rfl⟩ : syracuseStep 3442763 = 5164145) B5164145
theorem B1812567 : Blo 1811607 1812567 := bstep (se 1 (by rfl) ⟨1359425, by rfl⟩ : syracuseStep 1812567 = 2718851) B2718851
theorem B5163097 : Blo 1811607 5163097 := bstep (se 2 (by rfl) ⟨1936161, by rfl⟩ : syracuseStep 5163097 = 3872323) B3872323
theorem B1812587 : Blo 1811607 1812587 := bstep (se 1 (by rfl) ⟨1359440, by rfl⟩ : syracuseStep 1812587 = 2718881) B2718881
theorem B1812599 : Blo 1811607 1812599 := bstep (se 1 (by rfl) ⟨1359449, by rfl⟩ : syracuseStep 1812599 = 2718899) B2718899
theorem B3442817 : Blo 1811607 3442817 := bstep (se 2 (by rfl) ⟨1291056, by rfl⟩ : syracuseStep 3442817 = 2582113) B2582113
theorem B9799811 : Blo 1811607 9799811 := bstep (se 1 (by rfl) ⟨7349858, by rfl⟩ : syracuseStep 9799811 = 14699717) B14699717
theorem B1812619 : Blo 1811607 1812619 := bstep (se 1 (by rfl) ⟨1359464, by rfl⟩ : syracuseStep 1812619 = 2718929) B2718929
theorem B1812631 : Blo 1811607 1812631 := bstep (se 1 (by rfl) ⟨1359473, by rfl⟩ : syracuseStep 1812631 = 2718947) B2718947
theorem B3057817 : Blo 1811607 3057817 := bstep (se 2 (by rfl) ⟨1146681, by rfl⟩ : syracuseStep 3057817 = 2293363) B2293363
theorem B1812651 : Blo 1811607 1812651 := bstep (se 1 (by rfl) ⟨1359488, by rfl⟩ : syracuseStep 1812651 = 2718977) B2718977
theorem B1812663 : Blo 1811607 1812663 := bstep (se 1 (by rfl) ⟨1359497, by rfl⟩ : syracuseStep 1812663 = 2718995) B2718995
theorem B1812683 : Blo 1811607 1812683 := bstep (se 1 (by rfl) ⟨1359512, by rfl⟩ : syracuseStep 1812683 = 2719025) B2719025
theorem B1812695 : Blo 1811607 1812695 := bstep (se 1 (by rfl) ⟨1359521, by rfl⟩ : syracuseStep 1812695 = 2719043) B2719043
theorem B1812715 : Blo 1811607 1812715 := bstep (se 1 (by rfl) ⟨1359536, by rfl⟩ : syracuseStep 1812715 = 2719073) B2719073
theorem B1812727 : Blo 1811607 1812727 := bstep (se 1 (by rfl) ⟨1359545, by rfl⟩ : syracuseStep 1812727 = 2719091) B2719091
theorem B1812747 : Blo 1811607 1812747 := bstep (se 1 (by rfl) ⟨1359560, by rfl⟩ : syracuseStep 1812747 = 2719121) B2719121
theorem B1812759 : Blo 1811607 1812759 := bstep (se 1 (by rfl) ⟨1359569, by rfl⟩ : syracuseStep 1812759 = 2719139) B2719139
theorem B1812779 : Blo 1811607 1812779 := bstep (se 1 (by rfl) ⟨1359584, by rfl⟩ : syracuseStep 1812779 = 2719169) B2719169
theorem B6531373 : Blo 1811607 6531373 := bstep (se 3 (by rfl) ⟨1224632, by rfl⟩ : syracuseStep 6531373 = 2449265) B2449265
theorem B1812791 : Blo 1811607 1812791 := bstep (se 1 (by rfl) ⟨1359593, by rfl⟩ : syracuseStep 1812791 = 2719187) B2719187
theorem B1812811 : Blo 1811607 1812811 := bstep (se 1 (by rfl) ⟨1359608, by rfl⟩ : syracuseStep 1812811 = 2719217) B2719217
theorem B1812823 : Blo 1811607 1812823 := bstep (se 1 (by rfl) ⟨1359617, by rfl⟩ : syracuseStep 1812823 = 2719235) B2719235
theorem B1812843 : Blo 1811607 1812843 := bstep (se 1 (by rfl) ⟨1359632, by rfl⟩ : syracuseStep 1812843 = 2719265) B2719265
theorem B1812855 : Blo 1811607 1812855 := bstep (se 1 (by rfl) ⟨1359641, by rfl⟩ : syracuseStep 1812855 = 2719283) B2719283
theorem B1812875 : Blo 1811607 1812875 := bstep (se 1 (by rfl) ⟨1359656, by rfl⟩ : syracuseStep 1812875 = 2719313) B2719313
theorem B1812887 : Blo 1811607 1812887 := bstep (se 1 (by rfl) ⟨1359665, by rfl⟩ : syracuseStep 1812887 = 2719331) B2719331
theorem B11618711 : Blo 1811607 11618711 := bstep (se 1 (by rfl) ⟨8714033, by rfl⟩ : syracuseStep 11618711 = 17428067) B17428067
theorem B1812907 : Blo 1811607 1812907 := bstep (se 1 (by rfl) ⟨1359680, by rfl⟩ : syracuseStep 1812907 = 2719361) B2719361
theorem B1812919 : Blo 1811607 1812919 := bstep (se 1 (by rfl) ⟨1359689, by rfl⟩ : syracuseStep 1812919 = 2719379) B2719379
theorem B4590017 : Blo 1811607 4590017 := bstep (se 2 (by rfl) ⟨1721256, by rfl⟩ : syracuseStep 4590017 = 3442513) B3442513
theorem B1812939 : Blo 1811607 1812939 := bstep (se 1 (by rfl) ⟨1359704, by rfl⟩ : syracuseStep 1812939 = 2719409) B2719409
theorem B1812951 : Blo 1811607 1812951 := bstep (se 1 (by rfl) ⟨1359713, by rfl⟩ : syracuseStep 1812951 = 2719427) B2719427
theorem B1812971 : Blo 1811607 1812971 := bstep (se 1 (by rfl) ⟨1359728, by rfl⟩ : syracuseStep 1812971 = 2719457) B2719457
theorem B1812983 : Blo 1811607 1812983 := bstep (se 1 (by rfl) ⟨1359737, by rfl⟩ : syracuseStep 1812983 = 2719475) B2719475
theorem B1813003 : Blo 1811607 1813003 := bstep (se 1 (by rfl) ⟨1359752, by rfl⟩ : syracuseStep 1813003 = 2719505) B2719505
theorem B1813015 : Blo 1811607 1813015 := bstep (se 1 (by rfl) ⟨1359761, by rfl⟩ : syracuseStep 1813015 = 2719523) B2719523
theorem B1813035 : Blo 1811607 1813035 := bstep (se 1 (by rfl) ⟨1359776, by rfl⟩ : syracuseStep 1813035 = 2719553) B2719553
theorem B1813047 : Blo 1811607 1813047 := bstep (se 1 (by rfl) ⟨1359785, by rfl⟩ : syracuseStep 1813047 = 2719571) B2719571
theorem B13060673 : Blo 1811607 13060673 := bstep (se 2 (by rfl) ⟨4897752, by rfl⟩ : syracuseStep 13060673 = 9795505) B9795505
theorem B23538251 : Blo 1811607 23538251 := bstep (se 1 (by rfl) ⟨17653688, by rfl⟩ : syracuseStep 23538251 = 35307377) B35307377
theorem B1813067 : Blo 1811607 1813067 := bstep (se 1 (by rfl) ⟨1359800, by rfl⟩ : syracuseStep 1813067 = 2719601) B2719601
theorem B1813079 : Blo 1811607 1813079 := bstep (se 1 (by rfl) ⟨1359809, by rfl⟩ : syracuseStep 1813079 = 2719619) B2719619
theorem B1813099 : Blo 1811607 1813099 := bstep (se 1 (by rfl) ⟨1359824, by rfl⟩ : syracuseStep 1813099 = 2719649) B2719649
theorem B3869299 : Blo 1811607 3869299 := bstep (se 1 (by rfl) ⟨2901974, by rfl⟩ : syracuseStep 3869299 = 5803949) B5803949
theorem B1935991 : Blo 1811607 1935991 := bstep (se 1 (by rfl) ⟨1451993, by rfl⟩ : syracuseStep 1935991 = 2903987) B2903987
theorem B1813111 : Blo 1811607 1813111 := bstep (se 1 (by rfl) ⟨1359833, by rfl⟩ : syracuseStep 1813111 = 2719667) B2719667
theorem B1813131 : Blo 1811607 1813131 := bstep (se 1 (by rfl) ⟨1359848, by rfl⟩ : syracuseStep 1813131 = 2719697) B2719697
theorem B1813143 : Blo 1811607 1813143 := bstep (se 1 (by rfl) ⟨1359857, by rfl⟩ : syracuseStep 1813143 = 2719715) B2719715
theorem B1813163 : Blo 1811607 1813163 := bstep (se 1 (by rfl) ⟨1359872, by rfl⟩ : syracuseStep 1813163 = 2719745) B2719745
theorem B1813175 : Blo 1811607 1813175 := bstep (se 1 (by rfl) ⟨1359881, by rfl⟩ : syracuseStep 1813175 = 2719763) B2719763
theorem B5163713 : Blo 1811607 5163713 := bstep (se 2 (by rfl) ⟨1936392, by rfl⟩ : syracuseStep 5163713 = 3872785) B3872785
theorem B1813195 : Blo 1811607 1813195 := bstep (se 1 (by rfl) ⟨1359896, by rfl⟩ : syracuseStep 1813195 = 2719793) B2719793
theorem B3058391 : Blo 1811607 3058391 := bstep (se 1 (by rfl) ⟨2293793, by rfl⟩ : syracuseStep 3058391 = 4587587) B4587587
theorem B1813207 : Blo 1811607 1813207 := bstep (se 1 (by rfl) ⟨1359905, by rfl⟩ : syracuseStep 1813207 = 2719811) B2719811
theorem B1813227 : Blo 1811607 1813227 := bstep (se 1 (by rfl) ⟨1359920, by rfl⟩ : syracuseStep 1813227 = 2719841) B2719841
theorem B1813239 : Blo 1811607 1813239 := bstep (se 1 (by rfl) ⟨1359929, by rfl⟩ : syracuseStep 1813239 = 2719859) B2719859
theorem B6884099 : Blo 1811607 6884099 := bstep (se 1 (by rfl) ⟨5163074, by rfl⟩ : syracuseStep 6884099 = 10326149) B10326149
theorem B1813259 : Blo 1811607 1813259 := bstep (se 1 (by rfl) ⟨1359944, by rfl⟩ : syracuseStep 1813259 = 2719889) B2719889
theorem B13757201 : Blo 1811607 13757201 := bstep (se 2 (by rfl) ⟨5158950, by rfl⟩ : syracuseStep 13757201 = 10317901) B10317901
theorem B2902807 : Blo 1811607 2902807 := bstep (se 1 (by rfl) ⟨2177105, by rfl⟩ : syracuseStep 2902807 = 4354211) B4354211
theorem B1813271 : Blo 1811607 1813271 := bstep (se 1 (by rfl) ⟨1359953, by rfl⟩ : syracuseStep 1813271 = 2719907) B2719907
theorem B1813291 : Blo 1811607 1813291 := bstep (se 1 (by rfl) ⟨1359968, by rfl⟩ : syracuseStep 1813291 = 2719937) B2719937
theorem B1813303 : Blo 1811607 1813303 := bstep (se 1 (by rfl) ⟨1359977, by rfl⟩ : syracuseStep 1813303 = 2719955) B2719955
theorem B1813323 : Blo 1811607 1813323 := bstep (se 1 (by rfl) ⟨1359992, by rfl⟩ : syracuseStep 1813323 = 2719985) B2719985
theorem B3058519 : Blo 1811607 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B1813335 : Blo 1811607 1813335 := bstep (se 1 (by rfl) ⟨1360001, by rfl⟩ : syracuseStep 1813335 = 2720003) B2720003
theorem B15698789 : Blo 1811607 15698789 := bstep (se 4 (by rfl) ⟨1471761, by rfl⟩ : syracuseStep 15698789 = 2943523) B2943523
theorem B1813355 : Blo 1811607 1813355 := bstep (se 1 (by rfl) ⟨1360016, by rfl⟩ : syracuseStep 1813355 = 2720033) B2720033
theorem B1813367 : Blo 1811607 1813367 := bstep (se 1 (by rfl) ⟨1360025, by rfl⟩ : syracuseStep 1813367 = 2720051) B2720051
theorem B1837963 : Blo 1811607 1837963 := bstep (se 1 (by rfl) ⟨1378472, by rfl⟩ : syracuseStep 1837963 = 2756945) B2756945
theorem B1813387 : Blo 1811607 1813387 := bstep (se 1 (by rfl) ⟨1360040, by rfl⟩ : syracuseStep 1813387 = 2720081) B2720081
theorem B1813399 : Blo 1811607 1813399 := bstep (se 1 (by rfl) ⟨1360049, by rfl⟩ : syracuseStep 1813399 = 2720099) B2720099
theorem B1813419 : Blo 1811607 1813419 := bstep (se 1 (by rfl) ⟨1360064, by rfl⟩ : syracuseStep 1813419 = 2720129) B2720129
theorem B1813431 : Blo 1811607 1813431 := bstep (se 1 (by rfl) ⟨1360073, by rfl⟩ : syracuseStep 1813431 = 2720147) B2720147
theorem B1813451 : Blo 1811607 1813451 := bstep (se 1 (by rfl) ⟨1360088, by rfl⟩ : syracuseStep 1813451 = 2720177) B2720177
theorem B1813463 : Blo 1811607 1813463 := bstep (se 1 (by rfl) ⟨1360097, by rfl⟩ : syracuseStep 1813463 = 2720195) B2720195
theorem B4590553 : Blo 1811607 4590553 := bstep (se 2 (by rfl) ⟨1721457, by rfl⟩ : syracuseStep 4590553 = 3442915) B3442915
theorem B1813483 : Blo 1811607 1813483 := bstep (se 1 (by rfl) ⟨1360112, by rfl⟩ : syracuseStep 1813483 = 2720225) B2720225
theorem B1813495 : Blo 1811607 1813495 := bstep (se 1 (by rfl) ⟨1360121, by rfl⟩ : syracuseStep 1813495 = 2720243) B2720243
theorem B2755595 : Blo 1811607 2755595 := bstep (se 1 (by rfl) ⟨2066696, by rfl⟩ : syracuseStep 2755595 = 4133393) B4133393
theorem B1813515 : Blo 1811607 1813515 := bstep (se 1 (by rfl) ⟨1360136, by rfl⟩ : syracuseStep 1813515 = 2720273) B2720273
theorem B10325009 : Blo 1811607 10325009 := bstep (se 2 (by rfl) ⟨3871878, by rfl⟩ : syracuseStep 10325009 = 7743757) B7743757
theorem B1813527 : Blo 1811607 1813527 := bstep (se 1 (by rfl) ⟨1360145, by rfl⟩ : syracuseStep 1813527 = 2720291) B2720291
theorem B14699555 : Blo 1811607 14699555 := bstep (se 1 (by rfl) ⟨11024666, by rfl⟩ : syracuseStep 14699555 = 22049333) B22049333
theorem B1813547 : Blo 1811607 1813547 := bstep (se 1 (by rfl) ⟨1360160, by rfl⟩ : syracuseStep 1813547 = 2720321) B2720321
theorem B1813559 : Blo 1811607 1813559 := bstep (se 1 (by rfl) ⟨1360169, by rfl⟩ : syracuseStep 1813559 = 2720339) B2720339
theorem B1813579 : Blo 1811607 1813579 := bstep (se 1 (by rfl) ⟨1360184, by rfl⟩ : syracuseStep 1813579 = 2720369) B2720369
theorem B1813591 : Blo 1811607 1813591 := bstep (se 1 (by rfl) ⟨1360193, by rfl⟩ : syracuseStep 1813591 = 2720387) B2720387
theorem B4902067 : Blo 1811607 4902067 := bstep (se 1 (by rfl) ⟨3676550, by rfl⟩ : syracuseStep 4902067 = 7353101) B7353101
theorem B21499181 : Blo 1811607 21499181 := bstep (se 3 (by rfl) ⟨4031096, by rfl⟩ : syracuseStep 21499181 = 8062193) B8062193
theorem B9178433 : Blo 1811607 9178433 := bstep (se 2 (by rfl) ⟨3441912, by rfl⟩ : syracuseStep 9178433 = 6883825) B6883825
theorem B6114635 : Blo 1811607 6114635 := bstep (se 1 (by rfl) ⟨4585976, by rfl⟩ : syracuseStep 6114635 = 9171953) B9171953
theorem B13241731 : Blo 1811607 13241731 := bstep (se 1 (by rfl) ⟨9931298, by rfl⟩ : syracuseStep 13241731 = 19862597) B19862597
theorem B3059147 : Blo 1811607 3059147 := bstep (se 1 (by rfl) ⟨2294360, by rfl⟩ : syracuseStep 3059147 = 4588721) B4588721
theorem B10325465 : Blo 1811607 10325465 := bstep (se 2 (by rfl) ⟨3872049, by rfl⟩ : syracuseStep 10325465 = 7744099) B7744099
theorem B15478289 : Blo 1811607 15478289 := bstep (se 2 (by rfl) ⟨5804358, by rfl⟩ : syracuseStep 15478289 = 11608717) B11608717
theorem B3059275 : Blo 1811607 3059275 := bstep (se 1 (by rfl) ⟨2294456, by rfl⟩ : syracuseStep 3059275 = 4588913) B4588913
theorem B6114905 : Blo 1811607 6114905 := bstep (se 2 (by rfl) ⟨2293089, by rfl⟩ : syracuseStep 6114905 = 4586179) B4586179
theorem B9072307 : Blo 1811607 9072307 := bstep (se 1 (by rfl) ⟨6804230, by rfl⟩ : syracuseStep 9072307 = 13608461) B13608461
theorem B3059417 : Blo 1811607 3059417 := bstep (se 2 (by rfl) ⟨1147281, by rfl⟩ : syracuseStep 3059417 = 2294563) B2294563
theorem B13766435 : Blo 1811607 13766435 := bstep (se 1 (by rfl) ⟨10324826, by rfl⟩ : syracuseStep 13766435 = 20649653) B20649653
theorem B4353857 : Blo 1811607 4353857 := bstep (se 2 (by rfl) ⟨1632696, by rfl⟩ : syracuseStep 4353857 = 3265393) B3265393
theorem B3059545 : Blo 1811607 3059545 := bstep (se 2 (by rfl) ⟨1147329, by rfl⟩ : syracuseStep 3059545 = 2294659) B2294659
theorem B10317719 : Blo 1811607 10317719 := bstep (se 1 (by rfl) ⟨7738289, by rfl⟩ : syracuseStep 10317719 = 15476579) B15476579
theorem B2904025 : Blo 1811607 2904025 := bstep (se 2 (by rfl) ⟨1089009, by rfl⟩ : syracuseStep 2904025 = 2178019) B2178019
theorem B3870785 : Blo 1811607 3870785 := bstep (se 2 (by rfl) ⟨1451544, by rfl⟩ : syracuseStep 3870785 = 2903089) B2903089
theorem B3141785 : Blo 1811607 3141785 := bstep (se 2 (by rfl) ⟨1178169, by rfl⟩ : syracuseStep 3141785 = 2356339) B2356339
theorem B6115607 : Blo 1811607 6115607 := bstep (se 1 (by rfl) ⟨4586705, by rfl⟩ : syracuseStep 6115607 = 9173411) B9173411
theorem B3871127 : Blo 1811607 3871127 := bstep (se 1 (by rfl) ⟨2903345, by rfl⟩ : syracuseStep 3871127 = 5806691) B5806691
theorem B3060119 : Blo 1811607 3060119 := bstep (se 1 (by rfl) ⟨2295089, by rfl⟩ : syracuseStep 3060119 = 4590179) B4590179
theorem B3060247 : Blo 1811607 3060247 := bstep (se 1 (by rfl) ⟨2295185, by rfl⟩ : syracuseStep 3060247 = 4590371) B4590371
theorem B4076171 : Blo 1811607 4076171 := bstep (se 1 (by rfl) ⟨3057128, by rfl⟩ : syracuseStep 4076171 = 6114257) B6114257
theorem B6976145 : Blo 1811607 6976145 := bstep (se 2 (by rfl) ⟨2616054, by rfl⟩ : syracuseStep 6976145 = 5232109) B5232109
theorem B4076225 : Blo 1811607 4076225 := bstep (se 2 (by rfl) ⟨1528584, by rfl⟩ : syracuseStep 4076225 = 3057169) B3057169
theorem B3871435 : Blo 1811607 3871435 := bstep (se 1 (by rfl) ⟨2903576, by rfl⟩ : syracuseStep 3871435 = 5807153) B5807153
theorem B6116147 : Blo 1811607 6116147 := bstep (se 1 (by rfl) ⟨4587110, by rfl⟩ : syracuseStep 6116147 = 9174221) B9174221
theorem B16536413 : Blo 1811607 16536413 := bstep (se 3 (by rfl) ⟨3100577, by rfl⟩ : syracuseStep 16536413 = 6201155) B6201155
theorem B8713111 : Blo 1811607 8713111 := bstep (se 1 (by rfl) ⟨6534833, by rfl⟩ : syracuseStep 8713111 = 13069667) B13069667
theorem B4076441 : Blo 1811607 4076441 := bstep (se 2 (by rfl) ⟨1528665, by rfl⟩ : syracuseStep 4076441 = 3057331) B3057331
theorem B4076531 : Blo 1811607 4076531 := bstep (se 1 (by rfl) ⟨3057398, by rfl⟩ : syracuseStep 4076531 = 6114797) B6114797
theorem B4076567 : Blo 1811607 4076567 := bstep (se 1 (by rfl) ⟨3057425, by rfl⟩ : syracuseStep 4076567 = 6114851) B6114851
theorem B3265601 : Blo 1811607 3265601 := bstep (se 2 (by rfl) ⟨1224600, by rfl⟩ : syracuseStep 3265601 = 2449201) B2449201
theorem B6116417 : Blo 1811607 6116417 := bstep (se 2 (by rfl) ⟨2293656, by rfl⟩ : syracuseStep 6116417 = 4587313) B4587313
theorem B4133975 : Blo 1811607 4133975 := bstep (se 1 (by rfl) ⟨3100481, by rfl⟩ : syracuseStep 4133975 = 6200963) B6200963
theorem B16528535 : Blo 1811607 16528535 := bstep (se 1 (by rfl) ⟨12396401, by rfl⟩ : syracuseStep 16528535 = 24792803) B24792803
theorem B4076747 : Blo 1811607 4076747 := bstep (se 1 (by rfl) ⟨3057560, by rfl⟩ : syracuseStep 4076747 = 6115121) B6115121
theorem B9180377 : Blo 1811607 9180377 := bstep (se 2 (by rfl) ⟨3442641, by rfl⟩ : syracuseStep 9180377 = 6885283) B6885283
theorem B4076801 : Blo 1811607 4076801 := bstep (se 2 (by rfl) ⟨1528800, by rfl⟩ : syracuseStep 4076801 = 3057601) B3057601
theorem B30954797 : Blo 1811607 30954797 := bstep (se 3 (by rfl) ⟨5804024, by rfl⟩ : syracuseStep 30954797 = 11608049) B11608049
theorem B3102041 : Blo 1811607 3102041 := bstep (se 2 (by rfl) ⟨1163265, by rfl⟩ : syracuseStep 3102041 = 2326531) B2326531
theorem B4355479 : Blo 1811607 4355479 := bstep (se 1 (by rfl) ⟨3266609, by rfl⟩ : syracuseStep 4355479 = 6533219) B6533219
theorem B18609587 : Blo 1811607 18609587 := bstep (se 1 (by rfl) ⟨13957190, by rfl⟩ : syracuseStep 18609587 = 27914381) B27914381
theorem B4077017 : Blo 1811607 4077017 := bstep (se 2 (by rfl) ⟨1528881, by rfl⟩ : syracuseStep 4077017 = 3057763) B3057763
theorem B3872281 : Blo 1811607 3872281 := bstep (se 2 (by rfl) ⟨1452105, by rfl⟩ : syracuseStep 3872281 = 2904211) B2904211
theorem B4077107 : Blo 1811607 4077107 := bstep (se 1 (by rfl) ⟨3057830, by rfl⟩ : syracuseStep 4077107 = 6115661) B6115661
theorem B4077143 : Blo 1811607 4077143 := bstep (se 1 (by rfl) ⟨3057857, by rfl⟩ : syracuseStep 4077143 = 6115715) B6115715
theorem B7738973 : Blo 1811607 7738973 := bstep (se 3 (by rfl) ⟨1451057, by rfl⟩ : syracuseStep 7738973 = 2902115) B2902115
theorem B6116957 : Blo 1811607 6116957 := bstep (se 3 (by rfl) ⟨1146929, by rfl⟩ : syracuseStep 6116957 = 2293859) B2293859
theorem B6534749 : Blo 1811607 6534749 := bstep (se 3 (by rfl) ⟨1225265, by rfl⟩ : syracuseStep 6534749 = 2450531) B2450531
theorem B4077323 : Blo 1811607 4077323 := bstep (se 1 (by rfl) ⟨3057992, by rfl⟩ : syracuseStep 4077323 = 6115985) B6115985
theorem B10319633 : Blo 1811607 10319633 := bstep (se 2 (by rfl) ⟨3869862, by rfl⟩ : syracuseStep 10319633 = 7739725) B7739725
theorem B2717465 : Blo 1811607 2717465 := bstep (se 2 (by rfl) ⟨1019049, by rfl⟩ : syracuseStep 2717465 = 2038099) B2038099
theorem B4077377 : Blo 1811607 4077377 := bstep (se 2 (by rfl) ⟨1529016, by rfl⟩ : syracuseStep 4077377 = 3058033) B3058033
theorem B2717579 : Blo 1811607 2717579 := bstep (se 1 (by rfl) ⟨2038184, by rfl⟩ : syracuseStep 2717579 = 4076369) B4076369
theorem B2717591 : Blo 1811607 2717591 := bstep (se 1 (by rfl) ⟨2038193, by rfl⟩ : syracuseStep 2717591 = 4076387) B4076387
theorem B25499569 : Blo 1811607 25499569 := bstep (se 2 (by rfl) ⟨9562338, by rfl⟩ : syracuseStep 25499569 = 19124677) B19124677
theorem B5158849 : Blo 1811607 5158849 := bstep (se 2 (by rfl) ⟨1934568, by rfl⟩ : syracuseStep 5158849 = 3869137) B3869137
theorem B2717657 : Blo 1811607 2717657 := bstep (se 2 (by rfl) ⟨1019121, by rfl⟩ : syracuseStep 2717657 = 2038243) B2038243
theorem B6977501 : Blo 1811607 6977501 := bstep (se 3 (by rfl) ⟨1308281, by rfl⟩ : syracuseStep 6977501 = 2616563) B2616563
theorem B4077593 : Blo 1811607 4077593 := bstep (se 2 (by rfl) ⟨1529097, by rfl⟩ : syracuseStep 4077593 = 3058195) B3058195
theorem B47085637 : Blo 1811607 47085637 := bstep (se 4 (by rfl) ⟨4414278, by rfl⟩ : syracuseStep 47085637 = 8828557) B8828557
theorem B52262981 : Blo 1811607 52262981 := bstep (se 4 (by rfl) ⟨4899654, by rfl⟩ : syracuseStep 52262981 = 9799309) B9799309
theorem B2717771 : Blo 1811607 2717771 := bstep (se 1 (by rfl) ⟨2038328, by rfl⟩ : syracuseStep 2717771 = 4076657) B4076657
theorem B2717783 : Blo 1811607 2717783 := bstep (se 1 (by rfl) ⟨2038337, by rfl⟩ : syracuseStep 2717783 = 4076675) B4076675
theorem B4077683 : Blo 1811607 4077683 := bstep (se 1 (by rfl) ⟨3058262, by rfl⟩ : syracuseStep 4077683 = 6116525) B6116525
theorem B4077719 : Blo 1811607 4077719 := bstep (se 1 (by rfl) ⟨3058289, by rfl⟩ : syracuseStep 4077719 = 6116579) B6116579
theorem B2717849 : Blo 1811607 2717849 := bstep (se 2 (by rfl) ⟨1019193, by rfl⟩ : syracuseStep 2717849 = 2038387) B2038387
theorem B7346369 : Blo 1811607 7346369 := bstep (se 2 (by rfl) ⟨2754888, by rfl⟩ : syracuseStep 7346369 = 5509777) B5509777
theorem B5511361 : Blo 1811607 5511361 := bstep (se 2 (by rfl) ⟨2066760, by rfl⟩ : syracuseStep 5511361 = 4133521) B4133521
theorem B2324695 : Blo 1811607 2324695 := bstep (se 1 (by rfl) ⟨1743521, by rfl⟩ : syracuseStep 2324695 = 3487043) B3487043
theorem B2717963 : Blo 1811607 2717963 := bstep (se 1 (by rfl) ⟨2038472, by rfl⟩ : syracuseStep 2717963 = 4076945) B4076945
theorem B2717975 : Blo 1811607 2717975 := bstep (se 1 (by rfl) ⟨2038481, by rfl⟩ : syracuseStep 2717975 = 4076963) B4076963
theorem B4077899 : Blo 1811607 4077899 := bstep (se 1 (by rfl) ⟨3058424, by rfl⟩ : syracuseStep 4077899 = 6116849) B6116849
theorem B2718041 : Blo 1811607 2718041 := bstep (se 2 (by rfl) ⟨1019265, by rfl⟩ : syracuseStep 2718041 = 2038531) B2038531
theorem B2038135 : Blo 1811607 2038135 := bstep (se 1 (by rfl) ⟨1528601, by rfl⟩ : syracuseStep 2038135 = 3057203) B3057203
theorem B4077953 : Blo 1811607 4077953 := bstep (se 2 (by rfl) ⟨1529232, by rfl⟩ : syracuseStep 4077953 = 3058465) B3058465
theorem B5511617 : Blo 1811607 5511617 := bstep (se 2 (by rfl) ⟨2066856, by rfl⟩ : syracuseStep 5511617 = 4133713) B4133713
theorem B2718155 : Blo 1811607 2718155 := bstep (se 1 (by rfl) ⟨2038616, by rfl⟩ : syracuseStep 2718155 = 4077233) B4077233
theorem B2718167 : Blo 1811607 2718167 := bstep (se 1 (by rfl) ⟨2038625, by rfl⟩ : syracuseStep 2718167 = 4077251) B4077251
theorem B2718233 : Blo 1811607 2718233 := bstep (se 2 (by rfl) ⟨1019337, by rfl⟩ : syracuseStep 2718233 = 2038675) B2038675
theorem B2038315 : Blo 1811607 2038315 := bstep (se 1 (by rfl) ⟨1528736, by rfl⟩ : syracuseStep 2038315 = 3057473) B3057473
theorem B13761089 : Blo 1811607 13761089 := bstep (se 2 (by rfl) ⟨5160408, by rfl⟩ : syracuseStep 13761089 = 10320817) B10320817
theorem B4078169 : Blo 1811607 4078169 := bstep (se 2 (by rfl) ⟨1529313, by rfl⟩ : syracuseStep 4078169 = 3058627) B3058627
theorem B8706653 : Blo 1811607 8706653 := bstep (se 3 (by rfl) ⟨1632497, by rfl⟩ : syracuseStep 8706653 = 3264995) B3264995
theorem B2718347 : Blo 1811607 2718347 := bstep (se 1 (by rfl) ⟨2038760, by rfl⟩ : syracuseStep 2718347 = 4077521) B4077521
theorem B3439255 : Blo 1811607 3439255 := bstep (se 1 (by rfl) ⟨2579441, by rfl⟩ : syracuseStep 3439255 = 5158883) B5158883
theorem B2038423 : Blo 1811607 2038423 := bstep (se 1 (by rfl) ⟨1528817, by rfl⟩ : syracuseStep 2038423 = 3057635) B3057635
theorem B2718359 : Blo 1811607 2718359 := bstep (se 1 (by rfl) ⟨2038769, by rfl⟩ : syracuseStep 2718359 = 4077539) B4077539
theorem B6879923 : Blo 1811607 6879923 := bstep (se 1 (by rfl) ⟨5159942, by rfl⟩ : syracuseStep 6879923 = 10319885) B10319885
theorem B4078259 : Blo 1811607 4078259 := bstep (se 1 (by rfl) ⟨3058694, by rfl⟩ : syracuseStep 4078259 = 6117389) B6117389
theorem B4356787 : Blo 1811607 4356787 := bstep (se 1 (by rfl) ⟨3267590, by rfl⟩ : syracuseStep 4356787 = 6535181) B6535181
theorem B6879937 : Blo 1811607 6879937 := bstep (se 2 (by rfl) ⟨2579976, by rfl⟩ : syracuseStep 6879937 = 5159953) B5159953
theorem B6118091 : Blo 1811607 6118091 := bstep (se 1 (by rfl) ⟨4588568, by rfl⟩ : syracuseStep 6118091 = 9177137) B9177137
theorem B4078295 : Blo 1811607 4078295 := bstep (se 1 (by rfl) ⟨3058721, by rfl⟩ : syracuseStep 4078295 = 6117443) B6117443
theorem B2718425 : Blo 1811607 2718425 := bstep (se 2 (by rfl) ⟨1019409, by rfl⟩ : syracuseStep 2718425 = 2038819) B2038819
theorem B3439361 : Blo 1811607 3439361 := bstep (se 2 (by rfl) ⟨1289760, by rfl⟩ : syracuseStep 3439361 = 2579521) B2579521
theorem B3267353 : Blo 1811607 3267353 := bstep (se 2 (by rfl) ⟨1225257, by rfl⟩ : syracuseStep 3267353 = 2450515) B2450515
theorem B11615021 : Blo 1811607 11615021 := bstep (se 3 (by rfl) ⟨2177816, by rfl⟩ : syracuseStep 11615021 = 4355633) B4355633
theorem B4586291 : Blo 1811607 4586291 := bstep (se 1 (by rfl) ⟨3439718, by rfl⟩ : syracuseStep 4586291 = 6879437) B6879437
theorem B2038603 : Blo 1811607 2038603 := bstep (se 1 (by rfl) ⟨1528952, by rfl⟩ : syracuseStep 2038603 = 3057905) B3057905
theorem B2718539 : Blo 1811607 2718539 := bstep (se 1 (by rfl) ⟨2038904, by rfl⟩ : syracuseStep 2718539 = 4077809) B4077809
theorem B2718551 : Blo 1811607 2718551 := bstep (se 1 (by rfl) ⟨2038913, by rfl⟩ : syracuseStep 2718551 = 4077827) B4077827
theorem B8608643 : Blo 1811607 8608643 := bstep (se 1 (by rfl) ⟨6456482, by rfl⟩ : syracuseStep 8608643 = 12912965) B12912965
theorem B4078475 : Blo 1811607 4078475 := bstep (se 1 (by rfl) ⟨3058856, by rfl⟩ : syracuseStep 4078475 = 6117713) B6117713
theorem B3439513 : Blo 1811607 3439513 := bstep (se 2 (by rfl) ⟨1289817, by rfl⟩ : syracuseStep 3439513 = 2579635) B2579635
theorem B2718617 : Blo 1811607 2718617 := bstep (se 2 (by rfl) ⟨1019481, by rfl⟩ : syracuseStep 2718617 = 2038963) B2038963
theorem B30981041 : Blo 1811607 30981041 := bstep (se 2 (by rfl) ⟨11617890, by rfl⟩ : syracuseStep 30981041 = 23235781) B23235781
theorem B2038711 : Blo 1811607 2038711 := bstep (se 1 (by rfl) ⟨1529033, by rfl⟩ : syracuseStep 2038711 = 3058067) B3058067
theorem B4078529 : Blo 1811607 4078529 := bstep (se 2 (by rfl) ⟨1529448, by rfl⟩ : syracuseStep 4078529 = 3058897) B3058897
theorem B11475929 : Blo 1811607 11475929 := bstep (se 2 (by rfl) ⟨4303473, by rfl⟩ : syracuseStep 11475929 = 8606947) B8606947
theorem B6118361 : Blo 1811607 6118361 := bstep (se 2 (by rfl) ⟨2294385, by rfl⟩ : syracuseStep 6118361 = 4588771) B4588771
theorem B2718731 : Blo 1811607 2718731 := bstep (se 1 (by rfl) ⟨2039048, by rfl⟩ : syracuseStep 2718731 = 4078097) B4078097
theorem B2718743 : Blo 1811607 2718743 := bstep (se 1 (by rfl) ⟨2039057, by rfl⟩ : syracuseStep 2718743 = 4078115) B4078115
theorem B7740461 : Blo 1811607 7740461 := bstep (se 3 (by rfl) ⟨1451336, by rfl⟩ : syracuseStep 7740461 = 2902673) B2902673
theorem B2718809 : Blo 1811607 2718809 := bstep (se 2 (by rfl) ⟨1019553, by rfl⟩ : syracuseStep 2718809 = 2039107) B2039107
theorem B2038891 : Blo 1811607 2038891 := bstep (se 1 (by rfl) ⟨1529168, by rfl⟩ : syracuseStep 2038891 = 3058337) B3058337
theorem B2292887 : Blo 1811607 2292887 := bstep (se 1 (by rfl) ⟨1719665, by rfl⟩ : syracuseStep 2292887 = 3439331) B3439331
theorem B14703767 : Blo 1811607 14703767 := bstep (se 1 (by rfl) ⟨11027825, by rfl⟩ : syracuseStep 14703767 = 22055651) B22055651
theorem B4078745 : Blo 1811607 4078745 := bstep (se 2 (by rfl) ⟨1529529, by rfl⟩ : syracuseStep 4078745 = 3059059) B3059059
theorem B4136129 : Blo 1811607 4136129 := bstep (se 2 (by rfl) ⟨1551048, by rfl⟩ : syracuseStep 4136129 = 3102097) B3102097
theorem B2718923 : Blo 1811607 2718923 := bstep (se 1 (by rfl) ⟨2039192, by rfl⟩ : syracuseStep 2718923 = 4078385) B4078385
theorem B2038999 : Blo 1811607 2038999 := bstep (se 1 (by rfl) ⟨1529249, by rfl⟩ : syracuseStep 2038999 = 3058499) B3058499
theorem B2718935 : Blo 1811607 2718935 := bstep (se 1 (by rfl) ⟨2039201, by rfl⟩ : syracuseStep 2718935 = 4078403) B4078403
theorem B6282461 : Blo 1811607 6282461 := bstep (se 3 (by rfl) ⟨1177961, by rfl⟩ : syracuseStep 6282461 = 2355923) B2355923
theorem B4078835 : Blo 1811607 4078835 := bstep (se 1 (by rfl) ⟨3059126, by rfl⟩ : syracuseStep 4078835 = 6118253) B6118253
theorem B4078871 : Blo 1811607 4078871 := bstep (se 1 (by rfl) ⟨3059153, by rfl⟩ : syracuseStep 4078871 = 6118307) B6118307
theorem B2719001 : Blo 1811607 2719001 := bstep (se 2 (by rfl) ⟨1019625, by rfl⟩ : syracuseStep 2719001 = 2039251) B2039251
theorem B4586827 : Blo 1811607 4586827 := bstep (se 1 (by rfl) ⟨3440120, by rfl⟩ : syracuseStep 4586827 = 6880241) B6880241
theorem B4136267 : Blo 1811607 4136267 := bstep (se 1 (by rfl) ⟨3102200, by rfl⟩ : syracuseStep 4136267 = 6204401) B6204401
theorem B2039179 : Blo 1811607 2039179 := bstep (se 1 (by rfl) ⟨1529384, by rfl⟩ : syracuseStep 2039179 = 3058769) B3058769
theorem B2719115 : Blo 1811607 2719115 := bstep (se 1 (by rfl) ⟨2039336, by rfl⟩ : syracuseStep 2719115 = 4078673) B4078673
theorem B2579863 : Blo 1811607 2579863 := bstep (se 1 (by rfl) ⟨1934897, by rfl⟩ : syracuseStep 2579863 = 3869795) B3869795
theorem B2719127 : Blo 1811607 2719127 := bstep (se 1 (by rfl) ⟨2039345, by rfl⟩ : syracuseStep 2719127 = 4078691) B4078691
theorem B4079051 : Blo 1811607 4079051 := bstep (se 1 (by rfl) ⟨3059288, by rfl⟩ : syracuseStep 4079051 = 6118577) B6118577
theorem B4586969 : Blo 1811607 4586969 := bstep (se 2 (by rfl) ⟨1720113, by rfl⟩ : syracuseStep 4586969 = 3440227) B3440227
theorem B2719193 : Blo 1811607 2719193 := bstep (se 2 (by rfl) ⟨1019697, by rfl⟩ : syracuseStep 2719193 = 2039395) B2039395
theorem B2039287 : Blo 1811607 2039287 := bstep (se 1 (by rfl) ⟨1529465, by rfl⟩ : syracuseStep 2039287 = 3058931) B3058931
theorem B4079105 : Blo 1811607 4079105 := bstep (se 2 (by rfl) ⟨1529664, by rfl⟩ : syracuseStep 4079105 = 3059329) B3059329
theorem B9174545 : Blo 1811607 9174545 := bstep (se 2 (by rfl) ⟨3440454, by rfl⟩ : syracuseStep 9174545 = 6880909) B6880909
theorem B2448919 : Blo 1811607 2448919 := bstep (se 1 (by rfl) ⟨1836689, by rfl⟩ : syracuseStep 2448919 = 3673379) B3673379
theorem B5807639 : Blo 1811607 5807639 := bstep (se 1 (by rfl) ⟨4355729, by rfl⟩ : syracuseStep 5807639 = 8711459) B8711459
theorem B5160523 : Blo 1811607 5160523 := bstep (se 1 (by rfl) ⟨3870392, by rfl⟩ : syracuseStep 5160523 = 7740785) B7740785
theorem B2719307 : Blo 1811607 2719307 := bstep (se 1 (by rfl) ⟨2039480, by rfl⟩ : syracuseStep 2719307 = 4078961) B4078961
theorem B2719319 : Blo 1811607 2719319 := bstep (se 1 (by rfl) ⟨2039489, by rfl⟩ : syracuseStep 2719319 = 4078979) B4078979
theorem B6119063 : Blo 1811607 6119063 := bstep (se 1 (by rfl) ⟨4589297, by rfl⟩ : syracuseStep 6119063 = 9178595) B9178595
theorem B2719385 : Blo 1811607 2719385 := bstep (se 2 (by rfl) ⟨1019769, by rfl⟩ : syracuseStep 2719385 = 2039539) B2039539
theorem B2039467 : Blo 1811607 2039467 := bstep (se 1 (by rfl) ⟨1529600, by rfl⟩ : syracuseStep 2039467 = 3059201) B3059201
theorem B9174707 : Blo 1811607 9174707 := bstep (se 1 (by rfl) ⟨6881030, by rfl⟩ : syracuseStep 9174707 = 13762061) B13762061
theorem B4079321 : Blo 1811607 4079321 := bstep (se 2 (by rfl) ⟨1529745, by rfl⟩ : syracuseStep 4079321 = 3059491) B3059491
theorem B2719499 : Blo 1811607 2719499 := bstep (se 1 (by rfl) ⟨2039624, by rfl⟩ : syracuseStep 2719499 = 4079249) B4079249
theorem B2039575 : Blo 1811607 2039575 := bstep (se 1 (by rfl) ⟨1529681, by rfl⟩ : syracuseStep 2039575 = 3059363) B3059363
theorem B2719511 : Blo 1811607 2719511 := bstep (se 1 (by rfl) ⟨2039633, by rfl⟩ : syracuseStep 2719511 = 4079267) B4079267
theorem B4079411 : Blo 1811607 4079411 := bstep (se 1 (by rfl) ⟨3059558, by rfl⟩ : syracuseStep 4079411 = 6119117) B6119117
theorem B8494913 : Blo 1811607 8494913 := bstep (se 2 (by rfl) ⟨3185592, by rfl⟩ : syracuseStep 8494913 = 6371185) B6371185
theorem B2293591 : Blo 1811607 2293591 := bstep (se 1 (by rfl) ⟨1720193, by rfl⟩ : syracuseStep 2293591 = 3440387) B3440387
theorem B4079447 : Blo 1811607 4079447 := bstep (se 1 (by rfl) ⟨3059585, by rfl⟩ : syracuseStep 4079447 = 6119171) B6119171
theorem B2719577 : Blo 1811607 2719577 := bstep (se 2 (by rfl) ⟨1019841, by rfl⟩ : syracuseStep 2719577 = 2039683) B2039683
theorem B5160797 : Blo 1811607 5160797 := bstep (se 3 (by rfl) ⟨967649, by rfl⟩ : syracuseStep 5160797 = 1935299) B1935299
theorem B2580427 : Blo 1811607 2580427 := bstep (se 1 (by rfl) ⟨1935320, by rfl⟩ : syracuseStep 2580427 = 3870641) B3870641
theorem B2039755 : Blo 1811607 2039755 := bstep (se 1 (by rfl) ⟨1529816, by rfl⟩ : syracuseStep 2039755 = 3059633) B3059633
theorem B2719691 : Blo 1811607 2719691 := bstep (se 1 (by rfl) ⟨2039768, by rfl⟩ : syracuseStep 2719691 = 4079537) B4079537
theorem B2719703 : Blo 1811607 2719703 := bstep (se 1 (by rfl) ⟨2039777, by rfl⟩ : syracuseStep 2719703 = 4079555) B4079555
theorem B2719751 : Blo 1811607 2719751 := bstep (se 1 (by rfl) ⟨2039813, by rfl⟩ : syracuseStep 2719751 = 4079627) B4079627
theorem B2719787 : Blo 1811607 2719787 := bstep (se 1 (by rfl) ⟨2039840, by rfl⟩ : syracuseStep 2719787 = 4079681) B4079681
theorem B2719817 : Blo 1811607 2719817 := bstep (se 2 (by rfl) ⟨1019931, by rfl⟩ : syracuseStep 2719817 = 2039863) B2039863
theorem B4079735 : Blo 1811607 4079735 := bstep (se 1 (by rfl) ⟨3059801, by rfl⟩ : syracuseStep 4079735 = 6119603) B6119603
theorem B8708269 : Blo 1811607 8708269 := bstep (se 3 (by rfl) ⟨1632800, by rfl⟩ : syracuseStep 8708269 = 3265601) B3265601
theorem B10322093 : Blo 1811607 10322093 := bstep (se 3 (by rfl) ⟨1935392, by rfl⟩ : syracuseStep 10322093 = 3870785) B3870785
theorem B2719931 : Blo 1811607 2719931 := bstep (se 1 (by rfl) ⟨2039948, by rfl⟩ : syracuseStep 2719931 = 4079897) B4079897
theorem B2719991 : Blo 1811607 2719991 := bstep (se 1 (by rfl) ⟨2039993, by rfl⟩ : syracuseStep 2719991 = 4079987) B4079987
theorem B7348481 : Blo 1811607 7348481 := bstep (se 2 (by rfl) ⟨2755680, by rfl⟩ : syracuseStep 7348481 = 5511361) B5511361
theorem B2580751 : Blo 1811607 2580751 := bstep (se 1 (by rfl) ⟨1935563, by rfl⟩ : syracuseStep 2580751 = 3871127) B3871127
theorem B2720015 : Blo 1811607 2720015 := bstep (se 1 (by rfl) ⟨2040011, by rfl⟩ : syracuseStep 2720015 = 4080023) B4080023
theorem B2040079 : Blo 1811607 2040079 := bstep (se 1 (by rfl) ⟨1530059, by rfl⟩ : syracuseStep 2040079 = 3060119) B3060119
theorem B4079915 : Blo 1811607 4079915 := bstep (se 1 (by rfl) ⟨3059936, by rfl⟩ : syracuseStep 4079915 = 6119873) B6119873
theorem B2720057 : Blo 1811607 2720057 := bstep (se 2 (by rfl) ⟨1020021, by rfl⟩ : syracuseStep 2720057 = 2040043) B2040043
theorem B9175355 : Blo 1811607 9175355 := bstep (se 1 (by rfl) ⟨6881516, by rfl⟩ : syracuseStep 9175355 = 13763033) B13763033
theorem B4587911 : Blo 1811607 4587911 := bstep (se 1 (by rfl) ⟨3440933, by rfl⟩ : syracuseStep 4587911 = 6881867) B6881867
theorem B2720135 : Blo 1811607 2720135 := bstep (se 1 (by rfl) ⟨2040101, by rfl⟩ : syracuseStep 2720135 = 4080203) B4080203
theorem B2720171 : Blo 1811607 2720171 := bstep (se 1 (by rfl) ⟨2040128, by rfl⟩ : syracuseStep 2720171 = 4080257) B4080257
theorem B4587961 : Blo 1811607 4587961 := bstep (se 2 (by rfl) ⟨1720485, by rfl⟩ : syracuseStep 4587961 = 3440971) B3440971
theorem B2720201 : Blo 1811607 2720201 := bstep (se 2 (by rfl) ⟨1020075, by rfl⟩ : syracuseStep 2720201 = 2040151) B2040151
theorem B9175517 : Blo 1811607 9175517 := bstep (se 3 (by rfl) ⟨1720409, by rfl⟩ : syracuseStep 9175517 = 3440819) B3440819
theorem B2720315 : Blo 1811607 2720315 := bstep (se 1 (by rfl) ⟨2040236, by rfl⟩ : syracuseStep 2720315 = 4080473) B4080473
theorem B2720375 : Blo 1811607 2720375 := bstep (se 1 (by rfl) ⟨2040281, by rfl⟩ : syracuseStep 2720375 = 4080563) B4080563
theorem B2720399 : Blo 1811607 2720399 := bstep (se 1 (by rfl) ⟨2040299, by rfl⟩ : syracuseStep 2720399 = 4080599) B4080599
theorem B4080275 : Blo 1811607 4080275 := bstep (se 1 (by rfl) ⟨3060206, by rfl⟩ : syracuseStep 4080275 = 6120413) B6120413
theorem B52363957 : Blo 1811607 52363957 := bstep (se 5 (by rfl) ⟨2454560, by rfl⟩ : syracuseStep 52363957 = 4909121) B4909121
theorem B4080329 : Blo 1811607 4080329 := bstep (se 2 (by rfl) ⟨1530123, by rfl⟩ : syracuseStep 4080329 = 3060247) B3060247
theorem B11019023 : Blo 1811607 11019023 := bstep (se 1 (by rfl) ⟨8264267, by rfl⟩ : syracuseStep 11019023 = 16528535) B16528535
theorem B9175841 : Blo 1811607 9175841 := bstep (se 2 (by rfl) ⟨3440940, by rfl⟩ : syracuseStep 9175841 = 6881881) B6881881
theorem B148882211 : Blo 1811607 148882211 := bstep (se 1 (by rfl) ⟨111661658, by rfl⟩ : syracuseStep 148882211 = 223323317) B223323317
theorem B6120251 : Blo 1811607 6120251 := bstep (se 1 (by rfl) ⟨4590188, by rfl⟩ : syracuseStep 6120251 = 9180377) B9180377
theorem B2581321 : Blo 1811607 2581321 := bstep (se 2 (by rfl) ⟨967995, by rfl⟩ : syracuseStep 2581321 = 1935991) B1935991
theorem B20636531 : Blo 1811607 20636531 := bstep (se 1 (by rfl) ⟨15477398, by rfl⟩ : syracuseStep 20636531 = 30954797) B30954797
theorem B5809049 : Blo 1811607 5809049 := bstep (se 2 (by rfl) ⟨2178393, by rfl⟩ : syracuseStep 5809049 = 4356787) B4356787
theorem B5161913 : Blo 1811607 5161913 := bstep (se 2 (by rfl) ⟨1935717, by rfl⟩ : syracuseStep 5161913 = 3871435) B3871435
theorem B4588559 : Blo 1811607 4588559 := bstep (se 1 (by rfl) ⟨3441419, by rfl⟩ : syracuseStep 4588559 = 6882839) B6882839
theorem B2450617 : Blo 1811607 2450617 := bstep (se 2 (by rfl) ⟨918981, by rfl⟩ : syracuseStep 2450617 = 1837963) B1837963
theorem B1811643 : Blo 1811607 1811643 := bstep (se 1 (by rfl) ⟨1358732, by rfl⟩ : syracuseStep 1811643 = 2717465) B2717465
theorem B11617481 : Blo 1811607 11617481 := bstep (se 2 (by rfl) ⟨4356555, by rfl⟩ : syracuseStep 11617481 = 8713111) B8713111
theorem B1811719 : Blo 1811607 1811719 := bstep (se 1 (by rfl) ⟨1358789, by rfl⟩ : syracuseStep 1811719 = 2717579) B2717579
theorem B1811727 : Blo 1811607 1811727 := bstep (se 1 (by rfl) ⟨1358795, by rfl⟩ : syracuseStep 1811727 = 2717591) B2717591
theorem B5162255 : Blo 1811607 5162255 := bstep (se 1 (by rfl) ⟨3871691, by rfl⟩ : syracuseStep 5162255 = 7743383) B7743383
theorem B10323233 : Blo 1811607 10323233 := bstep (se 2 (by rfl) ⟨3871212, by rfl⟩ : syracuseStep 10323233 = 7742425) B7742425
theorem B6120737 : Blo 1811607 6120737 := bstep (se 2 (by rfl) ⟨2295276, by rfl⟩ : syracuseStep 6120737 = 4590553) B4590553
theorem B1811771 : Blo 1811607 1811771 := bstep (se 1 (by rfl) ⟨1358828, by rfl⟩ : syracuseStep 1811771 = 2717657) B2717657
theorem B34841987 : Blo 1811607 34841987 := bstep (se 1 (by rfl) ⟨26131490, by rfl⟩ : syracuseStep 34841987 = 52262981) B52262981
theorem B1811847 : Blo 1811607 1811847 := bstep (se 1 (by rfl) ⟨1358885, by rfl⟩ : syracuseStep 1811847 = 2717771) B2717771
theorem B1811855 : Blo 1811607 1811855 := bstep (se 1 (by rfl) ⟨1358891, by rfl⟩ : syracuseStep 1811855 = 2717783) B2717783
theorem B2295211 : Blo 1811607 2295211 := bstep (se 1 (by rfl) ⟨1721408, by rfl⟩ : syracuseStep 2295211 = 3442817) B3442817
theorem B1811899 : Blo 1811607 1811899 := bstep (se 1 (by rfl) ⟨1358924, by rfl⟩ : syracuseStep 1811899 = 2717849) B2717849
theorem B1811975 : Blo 1811607 1811975 := bstep (se 1 (by rfl) ⟨1358981, by rfl⟩ : syracuseStep 1811975 = 2717963) B2717963
theorem B1811983 : Blo 1811607 1811983 := bstep (se 1 (by rfl) ⟨1358987, by rfl⟩ : syracuseStep 1811983 = 2717975) B2717975
theorem B1812027 : Blo 1811607 1812027 := bstep (se 1 (by rfl) ⟨1359020, by rfl⟩ : syracuseStep 1812027 = 2718041) B2718041
theorem B34833989 : Blo 1811607 34833989 := bstep (se 4 (by rfl) ⟨3265686, by rfl⟩ : syracuseStep 34833989 = 6531373) B6531373
theorem B1812103 : Blo 1811607 1812103 := bstep (se 1 (by rfl) ⟨1359077, by rfl⟩ : syracuseStep 1812103 = 2718155) B2718155
theorem B1812111 : Blo 1811607 1812111 := bstep (se 1 (by rfl) ⟨1359083, by rfl⟩ : syracuseStep 1812111 = 2718167) B2718167
theorem B1812155 : Blo 1811607 1812155 := bstep (se 1 (by rfl) ⟨1359116, by rfl⟩ : syracuseStep 1812155 = 2718233) B2718233
theorem B4589257 : Blo 1811607 4589257 := bstep (se 2 (by rfl) ⟨1720971, by rfl⟩ : syracuseStep 4589257 = 3441943) B3441943
theorem B9176813 : Blo 1811607 9176813 := bstep (se 3 (by rfl) ⟨1720652, by rfl⟩ : syracuseStep 9176813 = 3441305) B3441305
theorem B1812231 : Blo 1811607 1812231 := bstep (se 1 (by rfl) ⟨1359173, by rfl⟩ : syracuseStep 1812231 = 2718347) B2718347
theorem B1812239 : Blo 1811607 1812239 := bstep (se 1 (by rfl) ⟨1359179, by rfl⟩ : syracuseStep 1812239 = 2718359) B2718359
theorem B3442475 : Blo 1811607 3442475 := bstep (se 1 (by rfl) ⟨2581856, by rfl⟩ : syracuseStep 3442475 = 5163713) B5163713
theorem B1812283 : Blo 1811607 1812283 := bstep (se 1 (by rfl) ⟨1359212, by rfl⟩ : syracuseStep 1812283 = 2718425) B2718425
theorem B4589399 : Blo 1811607 4589399 := bstep (se 1 (by rfl) ⟨3442049, by rfl⟩ : syracuseStep 4589399 = 6884099) B6884099
theorem B17655641 : Blo 1811607 17655641 := bstep (se 2 (by rfl) ⟨6620865, by rfl⟩ : syracuseStep 17655641 = 13241731) B13241731
theorem B7743347 : Blo 1811607 7743347 := bstep (se 1 (by rfl) ⟨5807510, by rfl⟩ : syracuseStep 7743347 = 11615021) B11615021
theorem B3057527 : Blo 1811607 3057527 := bstep (se 1 (by rfl) ⟨2293145, by rfl⟩ : syracuseStep 3057527 = 4586291) B4586291
theorem B1812359 : Blo 1811607 1812359 := bstep (se 1 (by rfl) ⟨1359269, by rfl⟩ : syracuseStep 1812359 = 2718539) B2718539
theorem B1812367 : Blo 1811607 1812367 := bstep (se 1 (by rfl) ⟨1359275, by rfl⟩ : syracuseStep 1812367 = 2718551) B2718551
theorem B1812411 : Blo 1811607 1812411 := bstep (se 1 (by rfl) ⟨1359308, by rfl⟩ : syracuseStep 1812411 = 2718617) B2718617
theorem B20654027 : Blo 1811607 20654027 := bstep (se 1 (by rfl) ⟨15490520, by rfl⟩ : syracuseStep 20654027 = 30981041) B30981041
theorem B1837063 : Blo 1811607 1837063 := bstep (se 1 (by rfl) ⟨1377797, by rfl⟩ : syracuseStep 1837063 = 2755595) B2755595
theorem B1812487 : Blo 1811607 1812487 := bstep (se 1 (by rfl) ⟨1359365, by rfl⟩ : syracuseStep 1812487 = 2718731) B2718731
theorem B6883339 : Blo 1811607 6883339 := bstep (se 1 (by rfl) ⟨5162504, by rfl⟩ : syracuseStep 6883339 = 10325009) B10325009
theorem B1812495 : Blo 1811607 1812495 := bstep (se 1 (by rfl) ⟨1359371, by rfl⟩ : syracuseStep 1812495 = 2718743) B2718743
theorem B9799703 : Blo 1811607 9799703 := bstep (se 1 (by rfl) ⟨7349777, by rfl⟩ : syracuseStep 9799703 = 14699555) B14699555
theorem B5163041 : Blo 1811607 5163041 := bstep (se 2 (by rfl) ⟨1936140, by rfl⟩ : syracuseStep 5163041 = 3872281) B3872281
theorem B1812539 : Blo 1811607 1812539 := bstep (se 1 (by rfl) ⟨1359404, by rfl⟩ : syracuseStep 1812539 = 2718809) B2718809
theorem B1812615 : Blo 1811607 1812615 := bstep (se 1 (by rfl) ⟨1359461, by rfl⟩ : syracuseStep 1812615 = 2718923) B2718923
theorem B1812623 : Blo 1811607 1812623 := bstep (se 1 (by rfl) ⟨1359467, by rfl⟩ : syracuseStep 1812623 = 2718935) B2718935
theorem B4188307 : Blo 1811607 4188307 := bstep (se 1 (by rfl) ⟨3141230, by rfl⟩ : syracuseStep 4188307 = 6282461) B6282461
theorem B22653101 : Blo 1811607 22653101 := bstep (se 3 (by rfl) ⟨4247456, by rfl⟩ : syracuseStep 22653101 = 8494913) B8494913
theorem B1812667 : Blo 1811607 1812667 := bstep (se 1 (by rfl) ⟨1359500, by rfl⟩ : syracuseStep 1812667 = 2719001) B2719001
theorem B1812743 : Blo 1811607 1812743 := bstep (se 1 (by rfl) ⟨1359557, by rfl⟩ : syracuseStep 1812743 = 2719115) B2719115
theorem B1812751 : Blo 1811607 1812751 := bstep (se 1 (by rfl) ⟨1359563, by rfl⟩ : syracuseStep 1812751 = 2719127) B2719127
theorem B3057979 : Blo 1811607 3057979 := bstep (se 1 (by rfl) ⟨2293484, by rfl⟩ : syracuseStep 3057979 = 4586969) B4586969
theorem B1812795 : Blo 1811607 1812795 := bstep (se 1 (by rfl) ⟨1359596, by rfl⟩ : syracuseStep 1812795 = 2719193) B2719193
theorem B6883643 : Blo 1811607 6883643 := bstep (se 1 (by rfl) ⟨5162732, by rfl⟩ : syracuseStep 6883643 = 10325465) B10325465
theorem B1812871 : Blo 1811607 1812871 := bstep (se 1 (by rfl) ⟨1359653, by rfl⟩ : syracuseStep 1812871 = 2719307) B2719307
theorem B1812879 : Blo 1811607 1812879 := bstep (se 1 (by rfl) ⟨1359659, by rfl⟩ : syracuseStep 1812879 = 2719319) B2719319
theorem B1812923 : Blo 1811607 1812923 := bstep (se 1 (by rfl) ⟨1359692, by rfl⟩ : syracuseStep 1812923 = 2719385) B2719385
theorem B3058121 : Blo 1811607 3058121 := bstep (se 2 (by rfl) ⟨1146795, by rfl⟩ : syracuseStep 3058121 = 2293591) B2293591
theorem B1812999 : Blo 1811607 1812999 := bstep (se 1 (by rfl) ⟨1359749, by rfl⟩ : syracuseStep 1812999 = 2719499) B2719499
theorem B1813007 : Blo 1811607 1813007 := bstep (se 1 (by rfl) ⟨1359755, by rfl⟩ : syracuseStep 1813007 = 2719511) B2719511
theorem B9177623 : Blo 1811607 9177623 := bstep (se 1 (by rfl) ⟨6883217, by rfl⟩ : syracuseStep 9177623 = 13766435) B13766435
theorem B2902571 : Blo 1811607 2902571 := bstep (se 1 (by rfl) ⟨2176928, by rfl⟩ : syracuseStep 2902571 = 4353857) B4353857
theorem B1813051 : Blo 1811607 1813051 := bstep (se 1 (by rfl) ⟨1359788, by rfl⟩ : syracuseStep 1813051 = 2719577) B2719577
theorem B19597889 : Blo 1811607 19597889 := bstep (se 2 (by rfl) ⟨7349208, by rfl⟩ : syracuseStep 19597889 = 14698417) B14698417
theorem B33999425 : Blo 1811607 33999425 := bstep (se 2 (by rfl) ⟨12749784, by rfl⟩ : syracuseStep 33999425 = 25499569) B25499569
theorem B1813127 : Blo 1811607 1813127 := bstep (se 1 (by rfl) ⟨1359845, by rfl⟩ : syracuseStep 1813127 = 2719691) B2719691
theorem B1813135 : Blo 1811607 1813135 := bstep (se 1 (by rfl) ⟨1359851, by rfl⟩ : syracuseStep 1813135 = 2719703) B2719703
theorem B1813179 : Blo 1811607 1813179 := bstep (se 1 (by rfl) ⟨1359884, by rfl⟩ : syracuseStep 1813179 = 2719769) B2719769
theorem B1813255 : Blo 1811607 1813255 := bstep (se 1 (by rfl) ⟨1359941, by rfl⟩ : syracuseStep 1813255 = 2719883) B2719883
theorem B11774735 : Blo 1811607 11774735 := bstep (se 1 (by rfl) ⟨8831051, by rfl⟩ : syracuseStep 11774735 = 17662103) B17662103
theorem B1813263 : Blo 1811607 1813263 := bstep (se 1 (by rfl) ⟨1359947, by rfl⟩ : syracuseStep 1813263 = 2719895) B2719895
theorem B6884129 : Blo 1811607 6884129 := bstep (se 2 (by rfl) ⟨2581548, by rfl⟩ : syracuseStep 6884129 = 5163097) B5163097
theorem B13060901 : Blo 1811607 13060901 := bstep (se 4 (by rfl) ⟨1224459, by rfl⟩ : syracuseStep 13060901 = 2448919) B2448919
theorem B1813307 : Blo 1811607 1813307 := bstep (se 1 (by rfl) ⟨1359980, by rfl⟩ : syracuseStep 1813307 = 2719961) B2719961
theorem B1813383 : Blo 1811607 1813383 := bstep (se 1 (by rfl) ⟨1360037, by rfl⟩ : syracuseStep 1813383 = 2720075) B2720075
theorem B1813391 : Blo 1811607 1813391 := bstep (se 1 (by rfl) ⟨1360043, by rfl⟩ : syracuseStep 1813391 = 2720087) B2720087
theorem B8825753 : Blo 1811607 8825753 := bstep (se 2 (by rfl) ⟨3309657, by rfl⟩ : syracuseStep 8825753 = 6619315) B6619315
theorem B1813435 : Blo 1811607 1813435 := bstep (se 1 (by rfl) ⟨1360076, by rfl⟩ : syracuseStep 1813435 = 2720153) B2720153
theorem B3099593 : Blo 1811607 3099593 := bstep (se 2 (by rfl) ⟨1162347, by rfl⟩ : syracuseStep 3099593 = 2324695) B2324695
theorem B1813511 : Blo 1811607 1813511 := bstep (se 1 (by rfl) ⟨1360133, by rfl⟩ : syracuseStep 1813511 = 2720267) B2720267
theorem B1813519 : Blo 1811607 1813519 := bstep (se 1 (by rfl) ⟨1360139, by rfl⟩ : syracuseStep 1813519 = 2720279) B2720279
theorem B1813563 : Blo 1811607 1813563 := bstep (se 1 (by rfl) ⟨1360172, by rfl⟩ : syracuseStep 1813563 = 2720345) B2720345
theorem B6114365 : Blo 1811607 6114365 := bstep (se 3 (by rfl) ⟨1146443, by rfl⟩ : syracuseStep 6114365 = 2292887) B2292887
theorem B3058823 : Blo 1811607 3058823 := bstep (se 1 (by rfl) ⟨2294117, by rfl⟩ : syracuseStep 3058823 = 4588235) B4588235
theorem B2068027 : Blo 1811607 2068027 := bstep (se 1 (by rfl) ⟨1551020, by rfl⟩ : syracuseStep 2068027 = 3102041) B3102041
theorem B48385637 : Blo 1811607 48385637 := bstep (se 4 (by rfl) ⟨4536153, by rfl⟩ : syracuseStep 48385637 = 9072307) B9072307
theorem B12406391 : Blo 1811607 12406391 := bstep (se 1 (by rfl) ⟨9304793, by rfl⟩ : syracuseStep 12406391 = 18609587) B18609587
theorem B6885101 : Blo 1811607 6885101 := bstep (se 3 (by rfl) ⟨1290956, by rfl⟩ : syracuseStep 6885101 = 2581913) B2581913
theorem B3059471 : Blo 1811607 3059471 := bstep (se 1 (by rfl) ⟨2294603, by rfl⟩ : syracuseStep 3059471 = 4589207) B4589207
theorem B15487037 : Blo 1811607 15487037 := bstep (se 3 (by rfl) ⟨2903819, by rfl⟩ : syracuseStep 15487037 = 5807639) B5807639
theorem B6533207 : Blo 1811607 6533207 := bstep (se 1 (by rfl) ⟨4899905, by rfl⟩ : syracuseStep 6533207 = 9799811) B9799811
theorem B7745807 : Blo 1811607 7745807 := bstep (se 1 (by rfl) ⟨5809355, by rfl⟩ : syracuseStep 7745807 = 11618711) B11618711
theorem B3674411 : Blo 1811607 3674411 := bstep (se 1 (by rfl) ⟨2755808, by rfl⟩ : syracuseStep 3674411 = 5511617) B5511617
theorem B3060011 : Blo 1811607 3060011 := bstep (se 1 (by rfl) ⟨2295008, by rfl⟩ : syracuseStep 3060011 = 4590017) B4590017
theorem B15692167 : Blo 1811607 15692167 := bstep (se 1 (by rfl) ⟨11769125, by rfl⟩ : syracuseStep 15692167 = 23538251) B23538251
theorem B5804435 : Blo 1811607 5804435 := bstep (se 1 (by rfl) ⟨4353326, by rfl⟩ : syracuseStep 5804435 = 8706653) B8706653
theorem B6115769 : Blo 1811607 6115769 := bstep (se 2 (by rfl) ⟨2293413, by rfl⟩ : syracuseStep 6115769 = 4586827) B4586827
theorem B9171467 : Blo 1811607 9171467 := bstep (se 1 (by rfl) ⟨6878600, by rfl⟩ : syracuseStep 9171467 = 13757201) B13757201
theorem B10465859 : Blo 1811607 10465859 := bstep (se 1 (by rfl) ⟨7849394, by rfl⟩ : syracuseStep 10465859 = 15698789) B15698789
theorem B5739095 : Blo 1811607 5739095 := bstep (se 1 (by rfl) ⟨4304321, by rfl⟩ : syracuseStep 5739095 = 8608643) B8608643
theorem B9171629 : Blo 1811607 9171629 := bstep (se 3 (by rfl) ⟨1719680, by rfl⟩ : syracuseStep 9171629 = 3439361) B3439361
theorem B3060409 : Blo 1811607 3060409 := bstep (se 2 (by rfl) ⟨1147653, by rfl⟩ : syracuseStep 3060409 = 2295307) B2295307
theorem B9802511 : Blo 1811607 9802511 := bstep (se 1 (by rfl) ⟨7351883, by rfl⟩ : syracuseStep 9802511 = 14703767) B14703767
theorem B2757419 : Blo 1811607 2757419 := bstep (se 1 (by rfl) ⟨2068064, by rfl⟩ : syracuseStep 2757419 = 4136129) B4136129
theorem B14332787 : Blo 1811607 14332787 := bstep (se 1 (by rfl) ⟨10749590, by rfl⟩ : syracuseStep 14332787 = 21499181) B21499181
theorem B4076423 : Blo 1811607 4076423 := bstep (se 1 (by rfl) ⟨3057317, by rfl⟩ : syracuseStep 4076423 = 6114635) B6114635
theorem B2757511 : Blo 1811607 2757511 := bstep (se 1 (by rfl) ⟨2068133, by rfl⟩ : syracuseStep 2757511 = 4136267) B4136267
theorem B10318859 : Blo 1811607 10318859 := bstep (se 1 (by rfl) ⟨7739144, by rfl⟩ : syracuseStep 10318859 = 15478289) B15478289
theorem B6116363 : Blo 1811607 6116363 := bstep (se 1 (by rfl) ⟨4587272, by rfl⟩ : syracuseStep 6116363 = 9174545) B9174545
theorem B4076603 : Blo 1811607 4076603 := bstep (se 1 (by rfl) ⟨3057452, by rfl⟩ : syracuseStep 4076603 = 6114905) B6114905
theorem B6116471 : Blo 1811607 6116471 := bstep (se 1 (by rfl) ⟨4587353, by rfl⟩ : syracuseStep 6116471 = 9174707) B9174707
theorem B4076729 : Blo 1811607 4076729 := bstep (se 2 (by rfl) ⟨1528773, by rfl⟩ : syracuseStep 4076729 = 3057547) B3057547
theorem B30602477 : Blo 1811607 30602477 := bstep (se 3 (by rfl) ⟨5737964, by rfl⟩ : syracuseStep 30602477 = 11475929) B11475929
theorem B6878465 : Blo 1811607 6878465 := bstep (se 2 (by rfl) ⟨2579424, by rfl⟩ : syracuseStep 6878465 = 5158849) B5158849
theorem B6878479 : Blo 1811607 6878479 := bstep (se 1 (by rfl) ⟨5158859, by rfl⟩ : syracuseStep 6878479 = 10317719) B10317719
theorem B3872033 : Blo 1811607 3872033 := bstep (se 2 (by rfl) ⟨1452012, by rfl⟩ : syracuseStep 3872033 = 2904025) B2904025
theorem B62780849 : Blo 1811607 62780849 := bstep (se 2 (by rfl) ⟨23542818, by rfl⟩ : syracuseStep 62780849 = 47085637) B47085637
theorem B11777501 : Blo 1811607 11777501 := bstep (se 3 (by rfl) ⟨2208281, by rfl⟩ : syracuseStep 11777501 = 4416563) B4416563
theorem B4077071 : Blo 1811607 4077071 := bstep (se 1 (by rfl) ⟨3057803, by rfl⟩ : syracuseStep 4077071 = 6115607) B6115607
theorem B9180701 : Blo 1811607 9180701 := bstep (se 3 (by rfl) ⟨1721381, by rfl⟩ : syracuseStep 9180701 = 3442763) B3442763
theorem B4077089 : Blo 1811607 4077089 := bstep (se 2 (by rfl) ⟨1528908, by rfl⟩ : syracuseStep 4077089 = 3057817) B3057817
theorem B11023933 : Blo 1811607 11023933 := bstep (se 3 (by rfl) ⟨2066987, by rfl⟩ : syracuseStep 11023933 = 4133975) B4133975
theorem B6117065 : Blo 1811607 6117065 := bstep (se 2 (by rfl) ⟨2293899, by rfl⟩ : syracuseStep 6117065 = 4587799) B4587799
theorem B8378093 : Blo 1811607 8378093 := bstep (se 3 (by rfl) ⟨1570892, by rfl⟩ : syracuseStep 8378093 = 3141785) B3141785
theorem B6534893 : Blo 1811607 6534893 := bstep (se 3 (by rfl) ⟨1225292, by rfl⟩ : syracuseStep 6534893 = 2450585) B2450585
theorem B2717447 : Blo 1811607 2717447 := bstep (se 1 (by rfl) ⟨2038085, by rfl⟩ : syracuseStep 2717447 = 4076171) B4076171
theorem B4650763 : Blo 1811607 4650763 := bstep (se 1 (by rfl) ⟨3488072, by rfl⟩ : syracuseStep 4650763 = 6976145) B6976145
theorem B2717483 : Blo 1811607 2717483 := bstep (se 1 (by rfl) ⟨2038112, by rfl⟩ : syracuseStep 2717483 = 4076225) B4076225
theorem B2717513 : Blo 1811607 2717513 := bstep (se 2 (by rfl) ⟨1019067, by rfl⟩ : syracuseStep 2717513 = 2038135) B2038135
theorem B4077431 : Blo 1811607 4077431 := bstep (se 1 (by rfl) ⟨3058073, by rfl⟩ : syracuseStep 4077431 = 6116147) B6116147
theorem B11024275 : Blo 1811607 11024275 := bstep (se 1 (by rfl) ⟨8268206, by rfl⟩ : syracuseStep 11024275 = 16536413) B16536413
theorem B2717627 : Blo 1811607 2717627 := bstep (se 1 (by rfl) ⟨2038220, by rfl⟩ : syracuseStep 2717627 = 4076441) B4076441
theorem B2717687 : Blo 1811607 2717687 := bstep (se 1 (by rfl) ⟨2038265, by rfl⟩ : syracuseStep 2717687 = 4076531) B4076531
theorem B9181187 : Blo 1811607 9181187 := bstep (se 1 (by rfl) ⟨6885890, by rfl⟩ : syracuseStep 9181187 = 13771781) B13771781
theorem B8067083 : Blo 1811607 8067083 := bstep (se 1 (by rfl) ⟨6050312, by rfl⟩ : syracuseStep 8067083 = 12100625) B12100625
theorem B2717711 : Blo 1811607 2717711 := bstep (se 1 (by rfl) ⟨2038283, by rfl⟩ : syracuseStep 2717711 = 4076567) B4076567
theorem B4077611 : Blo 1811607 4077611 := bstep (se 1 (by rfl) ⟨3058208, by rfl⟩ : syracuseStep 4077611 = 6116417) B6116417
theorem B10328107 : Blo 1811607 10328107 := bstep (se 1 (by rfl) ⟨7746080, by rfl⟩ : syracuseStep 10328107 = 15492161) B15492161
theorem B2717753 : Blo 1811607 2717753 := bstep (se 2 (by rfl) ⟨1019157, by rfl⟩ : syracuseStep 2717753 = 2038315) B2038315
theorem B2717831 : Blo 1811607 2717831 := bstep (se 1 (by rfl) ⟨2038373, by rfl⟩ : syracuseStep 2717831 = 4076747) B4076747
theorem B5159065 : Blo 1811607 5159065 := bstep (se 2 (by rfl) ⟨1934649, by rfl⟩ : syracuseStep 5159065 = 3869299) B3869299
theorem B2717867 : Blo 1811607 2717867 := bstep (se 1 (by rfl) ⟨2038400, by rfl⟩ : syracuseStep 2717867 = 4076801) B4076801
theorem B4585673 : Blo 1811607 4585673 := bstep (se 2 (by rfl) ⟨1719627, by rfl⟩ : syracuseStep 4585673 = 3439255) B3439255
theorem B2717897 : Blo 1811607 2717897 := bstep (se 2 (by rfl) ⟨1019211, by rfl⟩ : syracuseStep 2717897 = 2038423) B2038423
theorem B9173249 : Blo 1811607 9173249 := bstep (se 2 (by rfl) ⟨3439968, by rfl⟩ : syracuseStep 9173249 = 6879937) B6879937
theorem B2718011 : Blo 1811607 2718011 := bstep (se 1 (by rfl) ⟨2038508, by rfl⟩ : syracuseStep 2718011 = 4077017) B4077017
theorem B2718071 : Blo 1811607 2718071 := bstep (se 1 (by rfl) ⟨2038553, by rfl⟩ : syracuseStep 2718071 = 4077107) B4077107
theorem B3873143 : Blo 1811607 3873143 := bstep (se 1 (by rfl) ⟨2904857, by rfl⟩ : syracuseStep 3873143 = 5809715) B5809715
theorem B6117767 : Blo 1811607 6117767 := bstep (se 1 (by rfl) ⟨4588325, by rfl⟩ : syracuseStep 6117767 = 9176651) B9176651
theorem B2718095 : Blo 1811607 2718095 := bstep (se 1 (by rfl) ⟨2038571, by rfl⟩ : syracuseStep 2718095 = 4077143) B4077143
theorem B5159315 : Blo 1811607 5159315 := bstep (se 1 (by rfl) ⟨3869486, by rfl⟩ : syracuseStep 5159315 = 7738973) B7738973
theorem B4077971 : Blo 1811607 4077971 := bstep (se 1 (by rfl) ⟨3058478, by rfl⟩ : syracuseStep 4077971 = 6116957) B6116957
theorem B15489427 : Blo 1811607 15489427 := bstep (se 1 (by rfl) ⟨11617070, by rfl⟩ : syracuseStep 15489427 = 23234141) B23234141
theorem B4356499 : Blo 1811607 4356499 := bstep (se 1 (by rfl) ⟨3267374, by rfl⟩ : syracuseStep 4356499 = 6534749) B6534749
theorem B2718137 : Blo 1811607 2718137 := bstep (se 2 (by rfl) ⟨1019301, by rfl⟩ : syracuseStep 2718137 = 2038603) B2038603
theorem B4078025 : Blo 1811607 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B2038279 : Blo 1811607 2038279 := bstep (se 1 (by rfl) ⟨1528709, by rfl⟩ : syracuseStep 2038279 = 3057419) B3057419
theorem B2718215 : Blo 1811607 2718215 := bstep (se 1 (by rfl) ⟨2038661, by rfl⟩ : syracuseStep 2718215 = 4077323) B4077323
theorem B6879755 : Blo 1811607 6879755 := bstep (se 1 (by rfl) ⟨5159816, by rfl⟩ : syracuseStep 6879755 = 10319633) B10319633
theorem B8952331 : Blo 1811607 8952331 := bstep (se 1 (by rfl) ⟨6714248, by rfl⟩ : syracuseStep 8952331 = 13428497) B13428497
theorem B4586017 : Blo 1811607 4586017 := bstep (se 2 (by rfl) ⟨1719756, by rfl⟩ : syracuseStep 4586017 = 3439513) B3439513
theorem B2718251 : Blo 1811607 2718251 := bstep (se 1 (by rfl) ⟨2038688, by rfl⟩ : syracuseStep 2718251 = 4077377) B4077377
theorem B2718281 : Blo 1811607 2718281 := bstep (se 2 (by rfl) ⟨1019355, by rfl⟩ : syracuseStep 2718281 = 2038711) B2038711
theorem B4651667 : Blo 1811607 4651667 := bstep (se 1 (by rfl) ⟨3488750, by rfl⟩ : syracuseStep 4651667 = 6977501) B6977501
theorem B2038459 : Blo 1811607 2038459 := bstep (se 1 (by rfl) ⟨1528844, by rfl⟩ : syracuseStep 2038459 = 3057689) B3057689
theorem B2718395 : Blo 1811607 2718395 := bstep (se 1 (by rfl) ⟨2038796, by rfl⟩ : syracuseStep 2718395 = 4077593) B4077593
theorem B2718455 : Blo 1811607 2718455 := bstep (se 1 (by rfl) ⟨2038841, by rfl⟩ : syracuseStep 2718455 = 4077683) B4077683
theorem B6118145 : Blo 1811607 6118145 := bstep (se 2 (by rfl) ⟨2294304, by rfl⟩ : syracuseStep 6118145 = 4588609) B4588609
theorem B2718479 : Blo 1811607 2718479 := bstep (se 1 (by rfl) ⟨2038859, by rfl⟩ : syracuseStep 2718479 = 4077719) B4077719
theorem B15481637 : Blo 1811607 15481637 := bstep (se 4 (by rfl) ⟨1451403, by rfl⟩ : syracuseStep 15481637 = 2902807) B2902807
theorem B4897579 : Blo 1811607 4897579 := bstep (se 1 (by rfl) ⟨3673184, by rfl⟩ : syracuseStep 4897579 = 7346369) B7346369
theorem B2718521 : Blo 1811607 2718521 := bstep (se 2 (by rfl) ⟨1019445, by rfl⟩ : syracuseStep 2718521 = 2038891) B2038891
theorem B16767833 : Blo 1811607 16767833 := bstep (se 2 (by rfl) ⟨6287937, by rfl⟩ : syracuseStep 16767833 = 12575875) B12575875
theorem B2718599 : Blo 1811607 2718599 := bstep (se 1 (by rfl) ⟨2038949, by rfl⟩ : syracuseStep 2718599 = 4077899) B4077899
theorem B6536089 : Blo 1811607 6536089 := bstep (se 2 (by rfl) ⟨2451033, by rfl⟩ : syracuseStep 6536089 = 4902067) B4902067
theorem B2718635 : Blo 1811607 2718635 := bstep (se 1 (by rfl) ⟨2038976, by rfl⟩ : syracuseStep 2718635 = 4077953) B4077953
theorem B2718665 : Blo 1811607 2718665 := bstep (se 2 (by rfl) ⟨1019499, by rfl⟩ : syracuseStep 2718665 = 2038999) B2038999
theorem B8707115 : Blo 1811607 8707115 := bstep (se 1 (by rfl) ⟨6530336, by rfl⟩ : syracuseStep 8707115 = 13060673) B13060673
theorem B9174059 : Blo 1811607 9174059 := bstep (se 1 (by rfl) ⟨6880544, by rfl⟩ : syracuseStep 9174059 = 13761089) B13761089
theorem B2718779 : Blo 1811607 2718779 := bstep (se 1 (by rfl) ⟨2039084, by rfl⟩ : syracuseStep 2718779 = 4078169) B4078169
theorem B4586615 : Blo 1811607 4586615 := bstep (se 1 (by rfl) ⟨3439961, by rfl⟩ : syracuseStep 4586615 = 6879923) B6879923
theorem B2718839 : Blo 1811607 2718839 := bstep (se 1 (by rfl) ⟨2039129, by rfl⟩ : syracuseStep 2718839 = 4078259) B4078259
theorem B4078727 : Blo 1811607 4078727 := bstep (se 1 (by rfl) ⟨3059045, by rfl⟩ : syracuseStep 4078727 = 6118091) B6118091
theorem B2038927 : Blo 1811607 2038927 := bstep (se 1 (by rfl) ⟨1529195, by rfl⟩ : syracuseStep 2038927 = 3058391) B3058391
theorem B2718863 : Blo 1811607 2718863 := bstep (se 1 (by rfl) ⟨2039147, by rfl⟩ : syracuseStep 2718863 = 4078295) B4078295
theorem B2448569 : Blo 1811607 2448569 := bstep (se 2 (by rfl) ⟨918213, by rfl⟩ : syracuseStep 2448569 = 1836427) B1836427
theorem B2718905 : Blo 1811607 2718905 := bstep (se 2 (by rfl) ⟨1019589, by rfl⟩ : syracuseStep 2718905 = 2039179) B2039179
theorem B2178235 : Blo 1811607 2178235 := bstep (se 1 (by rfl) ⟨1633676, by rfl⟩ : syracuseStep 2178235 = 3267353) B3267353
theorem B3439817 : Blo 1811607 3439817 := bstep (se 2 (by rfl) ⟨1289931, by rfl⟩ : syracuseStep 3439817 = 2579863) B2579863
theorem B5807305 : Blo 1811607 5807305 := bstep (se 2 (by rfl) ⟨2177739, by rfl⟩ : syracuseStep 5807305 = 4355479) B4355479
theorem B2718983 : Blo 1811607 2718983 := bstep (se 1 (by rfl) ⟨2039237, by rfl⟩ : syracuseStep 2718983 = 4078475) B4078475
theorem B2719019 : Blo 1811607 2719019 := bstep (se 1 (by rfl) ⟨2039264, by rfl⟩ : syracuseStep 2719019 = 4078529) B4078529
theorem B4078907 : Blo 1811607 4078907 := bstep (se 1 (by rfl) ⟨3059180, by rfl⟩ : syracuseStep 4078907 = 6118361) B6118361
theorem B2719049 : Blo 1811607 2719049 := bstep (se 2 (by rfl) ⟨1019643, by rfl⟩ : syracuseStep 2719049 = 2039287) B2039287
theorem B5160307 : Blo 1811607 5160307 := bstep (se 1 (by rfl) ⟨3870230, by rfl⟩ : syracuseStep 5160307 = 7740461) B7740461
theorem B17423761 : Blo 1811607 17423761 := bstep (se 2 (by rfl) ⟨6533910, by rfl⟩ : syracuseStep 17423761 = 13067821) B13067821
theorem B2579897 : Blo 1811607 2579897 := bstep (se 2 (by rfl) ⟨967461, by rfl⟩ : syracuseStep 2579897 = 1934923) B1934923
theorem B6880697 : Blo 1811607 6880697 := bstep (se 2 (by rfl) ⟨2580261, by rfl⟩ : syracuseStep 6880697 = 5160523) B5160523
theorem B2719163 : Blo 1811607 2719163 := bstep (se 1 (by rfl) ⟨2039372, by rfl⟩ : syracuseStep 2719163 = 4078745) B4078745
theorem B4079033 : Blo 1811607 4079033 := bstep (se 2 (by rfl) ⟨1529637, by rfl⟩ : syracuseStep 4079033 = 3059275) B3059275
theorem B2719223 : Blo 1811607 2719223 := bstep (se 1 (by rfl) ⟨2039417, by rfl⟩ : syracuseStep 2719223 = 4078835) B4078835
theorem B2719247 : Blo 1811607 2719247 := bstep (se 1 (by rfl) ⟨2039435, by rfl⟩ : syracuseStep 2719247 = 4078871) B4078871
theorem B6118955 : Blo 1811607 6118955 := bstep (se 1 (by rfl) ⟨4589216, by rfl⟩ : syracuseStep 6118955 = 9178433) B9178433
theorem B2719289 : Blo 1811607 2719289 := bstep (se 2 (by rfl) ⟨1019733, by rfl⟩ : syracuseStep 2719289 = 2039467) B2039467
theorem B2039431 : Blo 1811607 2039431 := bstep (se 1 (by rfl) ⟨1529573, by rfl⟩ : syracuseStep 2039431 = 3059147) B3059147
theorem B2719367 : Blo 1811607 2719367 := bstep (se 1 (by rfl) ⟨2039525, by rfl⟩ : syracuseStep 2719367 = 4079051) B4079051
theorem B2719403 : Blo 1811607 2719403 := bstep (se 1 (by rfl) ⟨2039552, by rfl⟩ : syracuseStep 2719403 = 4079105) B4079105
theorem B2719433 : Blo 1811607 2719433 := bstep (se 2 (by rfl) ⟨1019787, by rfl⟩ : syracuseStep 2719433 = 2039575) B2039575
theorem B4079375 : Blo 1811607 4079375 := bstep (se 1 (by rfl) ⟨3059531, by rfl⟩ : syracuseStep 4079375 = 6119063) B6119063
theorem B4079393 : Blo 1811607 4079393 := bstep (se 2 (by rfl) ⟨1529772, by rfl⟩ : syracuseStep 4079393 = 3059545) B3059545
theorem B2039611 : Blo 1811607 2039611 := bstep (se 1 (by rfl) ⟨1529708, by rfl⟩ : syracuseStep 2039611 = 3059417) B3059417
theorem B2719547 : Blo 1811607 2719547 := bstep (se 1 (by rfl) ⟨2039660, by rfl⟩ : syracuseStep 2719547 = 4079321) B4079321
theorem B2719607 : Blo 1811607 2719607 := bstep (se 1 (by rfl) ⟨2039705, by rfl⟩ : syracuseStep 2719607 = 4079411) B4079411
theorem B2719631 : Blo 1811607 2719631 := bstep (se 1 (by rfl) ⟨2039723, by rfl⟩ : syracuseStep 2719631 = 4079447) B4079447
theorem B3440531 : Blo 1811607 3440531 := bstep (se 1 (by rfl) ⟨2580398, by rfl⟩ : syracuseStep 3440531 = 5160797) B5160797
theorem B3440569 : Blo 1811607 3440569 := bstep (se 2 (by rfl) ⟨1290213, by rfl⟩ : syracuseStep 3440569 = 2580427) B2580427
theorem B2719673 : Blo 1811607 2719673 := bstep (se 2 (by rfl) ⟨1019877, by rfl⟩ : syracuseStep 2719673 = 2039755) B2039755
theorem B9797669 : Blo 1811607 9797669 := bstep (se 4 (by rfl) ⟨918531, by rfl⟩ : syracuseStep 9797669 = 1837063) B1837063
theorem B13770809 : Blo 1811607 13770809 := bstep (se 2 (by rfl) ⟨5164053, by rfl⟩ : syracuseStep 13770809 = 10328107) B10328107
theorem B2719823 : Blo 1811607 2719823 := bstep (se 1 (by rfl) ⟨2039867, by rfl⟩ : syracuseStep 2719823 = 4079735) B4079735
theorem B6881395 : Blo 1811607 6881395 := bstep (se 1 (by rfl) ⟨5161046, by rfl⟩ : syracuseStep 6881395 = 10322093) B10322093
theorem B86048885 : Blo 1811607 86048885 := bstep (se 5 (by rfl) ⟨4033541, by rfl⟩ : syracuseStep 86048885 = 8067083) B8067083
theorem B4898987 : Blo 1811607 4898987 := bstep (se 1 (by rfl) ⟨3674240, by rfl⟩ : syracuseStep 4898987 = 7348481) B7348481
theorem B2449607 : Blo 1811607 2449607 := bstep (se 1 (by rfl) ⟨1837205, by rfl⟩ : syracuseStep 2449607 = 3674411) B3674411
theorem B2719943 : Blo 1811607 2719943 := bstep (se 1 (by rfl) ⟨2039957, by rfl⟩ : syracuseStep 2719943 = 4079915) B4079915
theorem B2040007 : Blo 1811607 2040007 := bstep (se 1 (by rfl) ⟨1530005, by rfl⟩ : syracuseStep 2040007 = 3060011) B3060011
theorem B2720105 : Blo 1811607 2720105 := bstep (se 2 (by rfl) ⟨1020039, by rfl⟩ : syracuseStep 2720105 = 2040079) B2040079
theorem B3826063 : Blo 1811607 3826063 := bstep (se 1 (by rfl) ⟨2869547, by rfl⟩ : syracuseStep 3826063 = 5739095) B5739095
theorem B2720183 : Blo 1811607 2720183 := bstep (se 1 (by rfl) ⟨2040137, by rfl⟩ : syracuseStep 2720183 = 4080275) B4080275
theorem B2720219 : Blo 1811607 2720219 := bstep (se 1 (by rfl) ⟨2040164, by rfl⟩ : syracuseStep 2720219 = 4080329) B4080329
theorem B6529517 : Blo 1811607 6529517 := bstep (se 3 (by rfl) ⟨1224284, by rfl⟩ : syracuseStep 6529517 = 2448569) B2448569
theorem B20922889 : Blo 1811607 20922889 := bstep (se 2 (by rfl) ⟨7846083, by rfl⟩ : syracuseStep 20922889 = 15692167) B15692167
theorem B99254807 : Blo 1811607 99254807 := bstep (se 1 (by rfl) ⟨74441105, by rfl⟩ : syracuseStep 99254807 = 148882211) B148882211
theorem B20652569 : Blo 1811607 20652569 := bstep (se 2 (by rfl) ⟨7744713, by rfl⟩ : syracuseStep 20652569 = 15489427) B15489427
theorem B5808665 : Blo 1811607 5808665 := bstep (se 2 (by rfl) ⟨2178249, by rfl⟩ : syracuseStep 5808665 = 4356499) B4356499
theorem B4080167 : Blo 1811607 4080167 := bstep (se 1 (by rfl) ⟨3060125, by rfl⟩ : syracuseStep 4080167 = 6120251) B6120251
theorem B3441275 : Blo 1811607 3441275 := bstep (se 1 (by rfl) ⟨2580956, by rfl⟩ : syracuseStep 3441275 = 5161913) B5161913
theorem B11936441 : Blo 1811607 11936441 := bstep (se 2 (by rfl) ⟨4476165, by rfl⟩ : syracuseStep 11936441 = 8952331) B8952331
theorem B3441503 : Blo 1811607 3441503 := bstep (se 1 (by rfl) ⟨2581127, by rfl⟩ : syracuseStep 3441503 = 5162255) B5162255
theorem B6882155 : Blo 1811607 6882155 := bstep (se 1 (by rfl) ⟨5161616, by rfl⟩ : syracuseStep 6882155 = 10323233) B10323233
theorem B2581355 : Blo 1811607 2581355 := bstep (se 1 (by rfl) ⟨1936016, by rfl⟩ : syracuseStep 2581355 = 3872033) B3872033
theorem B4080491 : Blo 1811607 4080491 := bstep (se 1 (by rfl) ⟨3060368, by rfl⟩ : syracuseStep 4080491 = 6120737) B6120737
theorem B4080545 : Blo 1811607 4080545 := bstep (se 2 (by rfl) ⟨1530204, by rfl⟩ : syracuseStep 4080545 = 3060409) B3060409
theorem B178856885 : Blo 1811607 178856885 := bstep (se 5 (by rfl) ⟨8383916, by rfl⟩ : syracuseStep 178856885 = 16767833) B16767833
theorem B41853899 : Blo 1811607 41853899 := bstep (se 1 (by rfl) ⟨31390424, by rfl⟩ : syracuseStep 41853899 = 62780849) B62780849
theorem B11617253 : Blo 1811607 11617253 := bstep (se 4 (by rfl) ⟨1089117, by rfl⟩ : syracuseStep 11617253 = 2178235) B2178235
theorem B6120467 : Blo 1811607 6120467 := bstep (se 1 (by rfl) ⟨4590350, by rfl⟩ : syracuseStep 6120467 = 9180701) B9180701
theorem B6530105 : Blo 1811607 6530105 := bstep (se 2 (by rfl) ⟨2448789, by rfl⟩ : syracuseStep 6530105 = 4897579) B4897579
theorem B3441761 : Blo 1811607 3441761 := bstep (se 2 (by rfl) ⟨1290660, by rfl⟩ : syracuseStep 3441761 = 2581321) B2581321
theorem B1811631 : Blo 1811607 1811631 := bstep (se 1 (by rfl) ⟨1358723, by rfl⟩ : syracuseStep 1811631 = 2717447) B2717447
theorem B1811655 : Blo 1811607 1811655 := bstep (se 1 (by rfl) ⟨1358741, by rfl⟩ : syracuseStep 1811655 = 2717483) B2717483
theorem B2294983 : Blo 1811607 2294983 := bstep (se 1 (by rfl) ⟨1721237, by rfl⟩ : syracuseStep 2294983 = 3442475) B3442475
theorem B1811675 : Blo 1811607 1811675 := bstep (se 1 (by rfl) ⟨1358756, by rfl⟩ : syracuseStep 1811675 = 2717513) B2717513
theorem B5162231 : Blo 1811607 5162231 := bstep (se 1 (by rfl) ⟨3871673, by rfl⟩ : syracuseStep 5162231 = 7743347) B7743347
theorem B1811751 : Blo 1811607 1811751 := bstep (se 1 (by rfl) ⟨1358813, by rfl⟩ : syracuseStep 1811751 = 2717627) B2717627
theorem B1811791 : Blo 1811607 1811791 := bstep (se 1 (by rfl) ⟨1358843, by rfl⟩ : syracuseStep 1811791 = 2717687) B2717687
theorem B6120791 : Blo 1811607 6120791 := bstep (se 1 (by rfl) ⟨4590593, by rfl⟩ : syracuseStep 6120791 = 9181187) B9181187
theorem B1811807 : Blo 1811607 1811807 := bstep (se 1 (by rfl) ⟨1358855, by rfl⟩ : syracuseStep 1811807 = 2717711) B2717711
theorem B3442027 : Blo 1811607 3442027 := bstep (se 1 (by rfl) ⟨2581520, by rfl⟩ : syracuseStep 3442027 = 5163041) B5163041
theorem B1811835 : Blo 1811607 1811835 := bstep (se 1 (by rfl) ⟨1358876, by rfl⟩ : syracuseStep 1811835 = 2717753) B2717753
theorem B13764005 : Blo 1811607 13764005 := bstep (se 4 (by rfl) ⟨1290375, by rfl⟩ : syracuseStep 13764005 = 2580751) B2580751
theorem B1811887 : Blo 1811607 1811887 := bstep (se 1 (by rfl) ⟨1358915, by rfl⟩ : syracuseStep 1811887 = 2717831) B2717831
theorem B1811911 : Blo 1811607 1811911 := bstep (se 1 (by rfl) ⟨1358933, by rfl⟩ : syracuseStep 1811911 = 2717867) B2717867
theorem B3057115 : Blo 1811607 3057115 := bstep (se 1 (by rfl) ⟨2292836, by rfl⟩ : syracuseStep 3057115 = 4585673) B4585673
theorem B1811931 : Blo 1811607 1811931 := bstep (se 1 (by rfl) ⟨1358948, by rfl⟩ : syracuseStep 1811931 = 2717897) B2717897
theorem B1812007 : Blo 1811607 1812007 := bstep (se 1 (by rfl) ⟨1359005, by rfl⟩ : syracuseStep 1812007 = 2718011) B2718011
theorem B4589095 : Blo 1811607 4589095 := bstep (se 1 (by rfl) ⟨3441821, by rfl⟩ : syracuseStep 4589095 = 6883643) B6883643
theorem B1812047 : Blo 1811607 1812047 := bstep (se 1 (by rfl) ⟨1359035, by rfl⟩ : syracuseStep 1812047 = 2718071) B2718071
theorem B1812063 : Blo 1811607 1812063 := bstep (se 1 (by rfl) ⟨1359047, by rfl⟩ : syracuseStep 1812063 = 2718095) B2718095
theorem B1812091 : Blo 1811607 1812091 := bstep (se 1 (by rfl) ⟨1359068, by rfl⟩ : syracuseStep 1812091 = 2718137) B2718137
theorem B1812143 : Blo 1811607 1812143 := bstep (se 1 (by rfl) ⟨1359107, by rfl⟩ : syracuseStep 1812143 = 2718215) B2718215
theorem B1935047 : Blo 1811607 1935047 := bstep (se 1 (by rfl) ⟨1451285, by rfl⟩ : syracuseStep 1935047 = 2902571) B2902571
theorem B1812167 : Blo 1811607 1812167 := bstep (se 1 (by rfl) ⟨1359125, by rfl⟩ : syracuseStep 1812167 = 2718251) B2718251
theorem B1812187 : Blo 1811607 1812187 := bstep (se 1 (by rfl) ⟨1359140, by rfl⟩ : syracuseStep 1812187 = 2718281) B2718281
theorem B1812263 : Blo 1811607 1812263 := bstep (se 1 (by rfl) ⟨1359197, by rfl⟩ : syracuseStep 1812263 = 2718395) B2718395
theorem B1812303 : Blo 1811607 1812303 := bstep (se 1 (by rfl) ⟨1359227, by rfl⟩ : syracuseStep 1812303 = 2718455) B2718455
theorem B1812319 : Blo 1811607 1812319 := bstep (se 1 (by rfl) ⟨1359239, by rfl⟩ : syracuseStep 1812319 = 2718479) B2718479
theorem B7849823 : Blo 1811607 7849823 := bstep (se 1 (by rfl) ⟨5887367, by rfl⟩ : syracuseStep 7849823 = 11774735) B11774735
theorem B4589419 : Blo 1811607 4589419 := bstep (se 1 (by rfl) ⟨3442064, by rfl⟩ : syracuseStep 4589419 = 6884129) B6884129
theorem B1812347 : Blo 1811607 1812347 := bstep (se 1 (by rfl) ⟨1359260, by rfl⟩ : syracuseStep 1812347 = 2718521) B2718521
theorem B1812399 : Blo 1811607 1812399 := bstep (se 1 (by rfl) ⟨1359299, by rfl⟩ : syracuseStep 1812399 = 2718599) B2718599
theorem B5883835 : Blo 1811607 5883835 := bstep (se 1 (by rfl) ⟨4412876, by rfl⟩ : syracuseStep 5883835 = 8825753) B8825753
theorem B1812423 : Blo 1811607 1812423 := bstep (se 1 (by rfl) ⟨1359317, by rfl⟩ : syracuseStep 1812423 = 2718635) B2718635
theorem B22341581 : Blo 1811607 22341581 := bstep (se 3 (by rfl) ⟨4189046, by rfl⟩ : syracuseStep 22341581 = 8378093) B8378093
theorem B2066395 : Blo 1811607 2066395 := bstep (se 1 (by rfl) ⟨1549796, by rfl⟩ : syracuseStep 2066395 = 3099593) B3099593
theorem B1812443 : Blo 1811607 1812443 := bstep (se 1 (by rfl) ⟨1359332, by rfl⟩ : syracuseStep 1812443 = 2718665) B2718665
theorem B1812519 : Blo 1811607 1812519 := bstep (se 1 (by rfl) ⟨1359389, by rfl⟩ : syracuseStep 1812519 = 2718779) B2718779
theorem B3057743 : Blo 1811607 3057743 := bstep (se 1 (by rfl) ⟨2293307, by rfl⟩ : syracuseStep 3057743 = 4586615) B4586615
theorem B1812559 : Blo 1811607 1812559 := bstep (se 1 (by rfl) ⟨1359419, by rfl⟩ : syracuseStep 1812559 = 2718839) B2718839
theorem B14698577 : Blo 1811607 14698577 := bstep (se 2 (by rfl) ⟨5511966, by rfl⟩ : syracuseStep 14698577 = 11023933) B11023933
theorem B1812575 : Blo 1811607 1812575 := bstep (se 1 (by rfl) ⟨1359431, by rfl⟩ : syracuseStep 1812575 = 2718863) B2718863
theorem B1812603 : Blo 1811607 1812603 := bstep (se 1 (by rfl) ⟨1359452, by rfl⟩ : syracuseStep 1812603 = 2718905) B2718905
theorem B1812655 : Blo 1811607 1812655 := bstep (se 1 (by rfl) ⟨1359491, by rfl⟩ : syracuseStep 1812655 = 2718983) B2718983
theorem B1812679 : Blo 1811607 1812679 := bstep (se 1 (by rfl) ⟨1359509, by rfl⟩ : syracuseStep 1812679 = 2719019) B2719019
theorem B1812699 : Blo 1811607 1812699 := bstep (se 1 (by rfl) ⟨1359524, by rfl⟩ : syracuseStep 1812699 = 2719049) B2719049
theorem B1812775 : Blo 1811607 1812775 := bstep (se 1 (by rfl) ⟨1359581, by rfl⟩ : syracuseStep 1812775 = 2719163) B2719163
theorem B1812815 : Blo 1811607 1812815 := bstep (se 1 (by rfl) ⟨1359611, by rfl⟩ : syracuseStep 1812815 = 2719223) B2719223
theorem B1812831 : Blo 1811607 1812831 := bstep (se 1 (by rfl) ⟨1359623, by rfl⟩ : syracuseStep 1812831 = 2719247) B2719247
theorem B1812859 : Blo 1811607 1812859 := bstep (se 1 (by rfl) ⟨1359644, by rfl⟩ : syracuseStep 1812859 = 2719289) B2719289
theorem B1812911 : Blo 1811607 1812911 := bstep (se 1 (by rfl) ⟨1359683, by rfl⟩ : syracuseStep 1812911 = 2719367) B2719367
theorem B1812935 : Blo 1811607 1812935 := bstep (se 1 (by rfl) ⟨1359701, by rfl⟩ : syracuseStep 1812935 = 2719403) B2719403
theorem B1812955 : Blo 1811607 1812955 := bstep (se 1 (by rfl) ⟨1359716, by rfl⟩ : syracuseStep 1812955 = 2719433) B2719433
theorem B4590067 : Blo 1811607 4590067 := bstep (se 1 (by rfl) ⟨3442550, by rfl⟩ : syracuseStep 4590067 = 6885101) B6885101
theorem B14699033 : Blo 1811607 14699033 := bstep (se 2 (by rfl) ⟨5512137, by rfl⟩ : syracuseStep 14699033 = 11024275) B11024275
theorem B1813031 : Blo 1811607 1813031 := bstep (se 1 (by rfl) ⟨1359773, by rfl⟩ : syracuseStep 1813031 = 2719547) B2719547
theorem B1813071 : Blo 1811607 1813071 := bstep (se 1 (by rfl) ⟨1359803, by rfl⟩ : syracuseStep 1813071 = 2719607) B2719607
theorem B1813087 : Blo 1811607 1813087 := bstep (se 1 (by rfl) ⟨1359815, by rfl⟩ : syracuseStep 1813087 = 2719631) B2719631
theorem B1813115 : Blo 1811607 1813115 := bstep (se 1 (by rfl) ⟨1359836, by rfl⟩ : syracuseStep 1813115 = 2719673) B2719673
theorem B1813167 : Blo 1811607 1813167 := bstep (se 1 (by rfl) ⟨1359875, by rfl⟩ : syracuseStep 1813167 = 2719751) B2719751
theorem B9177785 : Blo 1811607 9177785 := bstep (se 2 (by rfl) ⟨3441669, by rfl⟩ : syracuseStep 9177785 = 6883339) B6883339
theorem B1813191 : Blo 1811607 1813191 := bstep (se 1 (by rfl) ⟨1359893, by rfl⟩ : syracuseStep 1813191 = 2719787) B2719787
theorem B10324691 : Blo 1811607 10324691 := bstep (se 1 (by rfl) ⟨7743518, by rfl⟩ : syracuseStep 10324691 = 15487037) B15487037
theorem B1813211 : Blo 1811607 1813211 := bstep (se 1 (by rfl) ⟨1359908, by rfl⟩ : syracuseStep 1813211 = 2719817) B2719817
theorem B1813287 : Blo 1811607 1813287 := bstep (se 1 (by rfl) ⟨1359965, by rfl⟩ : syracuseStep 1813287 = 2719931) B2719931
theorem B1813327 : Blo 1811607 1813327 := bstep (se 1 (by rfl) ⟨1359995, by rfl⟩ : syracuseStep 1813327 = 2719991) B2719991
theorem B1813343 : Blo 1811607 1813343 := bstep (se 1 (by rfl) ⟨1360007, by rfl⟩ : syracuseStep 1813343 = 2720015) B2720015
theorem B1813371 : Blo 1811607 1813371 := bstep (se 1 (by rfl) ⟨1360028, by rfl⟩ : syracuseStep 1813371 = 2720057) B2720057
theorem B11611025 : Blo 1811607 11611025 := bstep (se 2 (by rfl) ⟨4354134, by rfl⟩ : syracuseStep 11611025 = 8708269) B8708269
theorem B3058607 : Blo 1811607 3058607 := bstep (se 1 (by rfl) ⟨2293955, by rfl⟩ : syracuseStep 3058607 = 4587911) B4587911
theorem B1813423 : Blo 1811607 1813423 := bstep (se 1 (by rfl) ⟨1360067, by rfl⟩ : syracuseStep 1813423 = 2720135) B2720135
theorem B3869623 : Blo 1811607 3869623 := bstep (se 1 (by rfl) ⟨2902217, by rfl⟩ : syracuseStep 3869623 = 5804435) B5804435
theorem B1813447 : Blo 1811607 1813447 := bstep (se 1 (by rfl) ⟨1360085, by rfl⟩ : syracuseStep 1813447 = 2720171) B2720171
theorem B1813467 : Blo 1811607 1813467 := bstep (se 1 (by rfl) ⟨1360100, by rfl⟩ : syracuseStep 1813467 = 2720201) B2720201
theorem B11029477 : Blo 1811607 11029477 := bstep (se 4 (by rfl) ⟨1034013, by rfl⟩ : syracuseStep 11029477 = 2068027) B2068027
theorem B6114311 : Blo 1811607 6114311 := bstep (se 1 (by rfl) ⟨4585733, by rfl⟩ : syracuseStep 6114311 = 9171467) B9171467
theorem B1813543 : Blo 1811607 1813543 := bstep (se 1 (by rfl) ⟨1360157, by rfl⟩ : syracuseStep 1813543 = 2720315) B2720315
theorem B1813583 : Blo 1811607 1813583 := bstep (se 1 (by rfl) ⟨1360187, by rfl⟩ : syracuseStep 1813583 = 2720375) B2720375
theorem B1813599 : Blo 1811607 1813599 := bstep (se 1 (by rfl) ⟨1360199, by rfl⟩ : syracuseStep 1813599 = 2720399) B2720399
theorem B6114419 : Blo 1811607 6114419 := bstep (se 1 (by rfl) ⟨4585814, by rfl⟩ : syracuseStep 6114419 = 9171629) B9171629
theorem B1838279 : Blo 1811607 1838279 := bstep (se 1 (by rfl) ⟨1378709, by rfl⟩ : syracuseStep 1838279 = 2757419) B2757419
theorem B13757687 : Blo 1811607 13757687 := bstep (se 1 (by rfl) ⟨10318265, by rfl⟩ : syracuseStep 13757687 = 20636531) B20636531
theorem B9555191 : Blo 1811607 9555191 := bstep (se 1 (by rfl) ⟨7166393, by rfl⟩ : syracuseStep 9555191 = 14332787) B14332787
theorem B3059039 : Blo 1811607 3059039 := bstep (se 1 (by rfl) ⟨2294279, by rfl⟩ : syracuseStep 3059039 = 4588559) B4588559
theorem B20655485 : Blo 1811607 20655485 := bstep (se 3 (by rfl) ⟨3872903, by rfl⟩ : syracuseStep 20655485 = 7745807) B7745807
theorem B6114689 : Blo 1811607 6114689 := bstep (se 2 (by rfl) ⟨2293008, by rfl⟩ : syracuseStep 6114689 = 4586017) B4586017
theorem B7744987 : Blo 1811607 7744987 := bstep (se 1 (by rfl) ⟨5808740, by rfl⟩ : syracuseStep 7744987 = 11617481) B11617481
theorem B20401651 : Blo 1811607 20401651 := bstep (se 1 (by rfl) ⟨15301238, by rfl⟩ : syracuseStep 20401651 = 30602477) B30602477
theorem B23227991 : Blo 1811607 23227991 := bstep (se 1 (by rfl) ⟨17420993, by rfl⟩ : syracuseStep 23227991 = 34841987) B34841987
theorem B13069957 : Blo 1811607 13069957 := bstep (se 4 (by rfl) ⟨1225308, by rfl⟩ : syracuseStep 13069957 = 2450617) B2450617
theorem B7851667 : Blo 1811607 7851667 := bstep (se 1 (by rfl) ⟨5888750, by rfl⟩ : syracuseStep 7851667 = 11777501) B11777501
theorem B13758173 : Blo 1811607 13758173 := bstep (se 3 (by rfl) ⟨2579657, by rfl⟩ : syracuseStep 13758173 = 5159315) B5159315
theorem B3059599 : Blo 1811607 3059599 := bstep (se 1 (by rfl) ⟨2294699, by rfl⟩ : syracuseStep 3059599 = 4589399) B4589399
theorem B6533135 : Blo 1811607 6533135 := bstep (se 1 (by rfl) ⟨4899851, by rfl⟩ : syracuseStep 6533135 = 9799703) B9799703
theorem B15102067 : Blo 1811607 15102067 := bstep (se 1 (by rfl) ⟨11326550, by rfl⟩ : syracuseStep 15102067 = 22653101) B22653101
theorem B6115499 : Blo 1811607 6115499 := bstep (se 1 (by rfl) ⟨4586624, by rfl⟩ : syracuseStep 6115499 = 9173249) B9173249
theorem B9171305 : Blo 1811607 9171305 := bstep (se 2 (by rfl) ⟨3439239, by rfl⟩ : syracuseStep 9171305 = 6878479) B6878479
theorem B3101111 : Blo 1811607 3101111 := bstep (se 1 (by rfl) ⟨2325833, by rfl⟩ : syracuseStep 3101111 = 4651667) B4651667
theorem B3060281 : Blo 1811607 3060281 := bstep (se 2 (by rfl) ⟨1147605, by rfl⟩ : syracuseStep 3060281 = 2295211) B2295211
theorem B5804743 : Blo 1811607 5804743 := bstep (se 1 (by rfl) ⟨4353557, by rfl⟩ : syracuseStep 5804743 = 8707115) B8707115
theorem B6116039 : Blo 1811607 6116039 := bstep (se 1 (by rfl) ⟨4587029, by rfl⟩ : syracuseStep 6116039 = 9174059) B9174059
theorem B4076243 : Blo 1811607 4076243 := bstep (se 1 (by rfl) ⟨3057182, by rfl⟩ : syracuseStep 4076243 = 6114365) B6114365
theorem B32257091 : Blo 1811607 32257091 := bstep (se 1 (by rfl) ⟨24192818, by rfl⟩ : syracuseStep 32257091 = 48385637) B48385637
theorem B8270927 : Blo 1811607 8270927 := bstep (se 1 (by rfl) ⟨6203195, by rfl⟩ : syracuseStep 8270927 = 12406391) B12406391
theorem B4355471 : Blo 1811607 4355471 := bstep (se 1 (by rfl) ⟨3266603, by rfl⟩ : syracuseStep 4355471 = 6533207) B6533207
theorem B5584409 : Blo 1811607 5584409 := bstep (se 2 (by rfl) ⟨2094153, by rfl⟩ : syracuseStep 5584409 = 4188307) B4188307
theorem B6878753 : Blo 1811607 6878753 := bstep (se 2 (by rfl) ⟨2579532, by rfl⟩ : syracuseStep 6878753 = 5159065) B5159065
theorem B6116903 : Blo 1811607 6116903 := bstep (se 1 (by rfl) ⟨4587677, by rfl⟩ : syracuseStep 6116903 = 9175355) B9175355
theorem B4077179 : Blo 1811607 4077179 := bstep (se 1 (by rfl) ⟨3057884, by rfl⟩ : syracuseStep 4077179 = 6115769) B6115769
theorem B6117011 : Blo 1811607 6117011 := bstep (se 1 (by rfl) ⟨4587758, by rfl⟩ : syracuseStep 6117011 = 9175517) B9175517
theorem B4077305 : Blo 1811607 4077305 := bstep (se 2 (by rfl) ⟨1528989, by rfl⟩ : syracuseStep 4077305 = 3057979) B3057979
theorem B7346015 : Blo 1811607 7346015 := bstep (se 1 (by rfl) ⟨5509511, by rfl⟩ : syracuseStep 7346015 = 11019023) B11019023
theorem B6535007 : Blo 1811607 6535007 := bstep (se 1 (by rfl) ⟨4901255, by rfl⟩ : syracuseStep 6535007 = 9802511) B9802511
theorem B6117227 : Blo 1811607 6117227 := bstep (se 1 (by rfl) ⟨4587920, by rfl⟩ : syracuseStep 6117227 = 9175841) B9175841
theorem B6117281 : Blo 1811607 6117281 := bstep (se 2 (by rfl) ⟨2293980, by rfl⟩ : syracuseStep 6117281 = 4587961) B4587961
theorem B2717615 : Blo 1811607 2717615 := bstep (se 1 (by rfl) ⟨2038211, by rfl⟩ : syracuseStep 2717615 = 4076423) B4076423
theorem B3872699 : Blo 1811607 3872699 := bstep (se 1 (by rfl) ⟨2904524, by rfl⟩ : syracuseStep 3872699 = 5809049) B5809049
theorem B6879239 : Blo 1811607 6879239 := bstep (se 1 (by rfl) ⟨5159429, by rfl⟩ : syracuseStep 6879239 = 10318859) B10318859
theorem B4077575 : Blo 1811607 4077575 := bstep (se 1 (by rfl) ⟨3058181, by rfl⟩ : syracuseStep 4077575 = 6116363) B6116363
theorem B2717705 : Blo 1811607 2717705 := bstep (se 2 (by rfl) ⟨1019139, by rfl⟩ : syracuseStep 2717705 = 2038279) B2038279
theorem B2717735 : Blo 1811607 2717735 := bstep (se 1 (by rfl) ⟨2038301, by rfl⟩ : syracuseStep 2717735 = 4076603) B4076603
theorem B4077647 : Blo 1811607 4077647 := bstep (se 1 (by rfl) ⟨3058235, by rfl⟩ : syracuseStep 4077647 = 6116471) B6116471
theorem B2717819 : Blo 1811607 2717819 := bstep (se 1 (by rfl) ⟨2038364, by rfl⟩ : syracuseStep 2717819 = 4076729) B4076729
theorem B4585643 : Blo 1811607 4585643 := bstep (se 1 (by rfl) ⟨3439232, by rfl⟩ : syracuseStep 4585643 = 6878465) B6878465
theorem B69818609 : Blo 1811607 69818609 := bstep (se 2 (by rfl) ⟨26181978, by rfl⟩ : syracuseStep 69818609 = 52363957) B52363957
theorem B2717945 : Blo 1811607 2717945 := bstep (se 2 (by rfl) ⟨1019229, by rfl⟩ : syracuseStep 2717945 = 2038459) B2038459
theorem B10328381 : Blo 1811607 10328381 := bstep (se 3 (by rfl) ⟨1936571, by rfl⟩ : syracuseStep 10328381 = 3873143) B3873143
theorem B2718047 : Blo 1811607 2718047 := bstep (se 1 (by rfl) ⟨2038535, by rfl⟩ : syracuseStep 2718047 = 4077071) B4077071
theorem B2718059 : Blo 1811607 2718059 := bstep (se 1 (by rfl) ⟨2038544, by rfl⟩ : syracuseStep 2718059 = 4077089) B4077089
theorem B23222659 : Blo 1811607 23222659 := bstep (se 1 (by rfl) ⟨17416994, by rfl⟩ : syracuseStep 23222659 = 34833989) B34833989
theorem B30972293 : Blo 1811607 30972293 := bstep (se 4 (by rfl) ⟨2903652, by rfl⟩ : syracuseStep 30972293 = 5807305) B5807305
theorem B4078043 : Blo 1811607 4078043 := bstep (se 1 (by rfl) ⟨3058532, by rfl⟩ : syracuseStep 4078043 = 6117065) B6117065
theorem B6879725 : Blo 1811607 6879725 := bstep (se 3 (by rfl) ⟨1289948, by rfl⟩ : syracuseStep 6879725 = 2579897) B2579897
theorem B6117875 : Blo 1811607 6117875 := bstep (se 1 (by rfl) ⟨4588406, by rfl⟩ : syracuseStep 6117875 = 9176813) B9176813
theorem B4356595 : Blo 1811607 4356595 := bstep (se 1 (by rfl) ⟨3267446, by rfl⟩ : syracuseStep 4356595 = 6534893) B6534893
theorem B3676681 : Blo 1811607 3676681 := bstep (se 2 (by rfl) ⟨1378755, by rfl⟩ : syracuseStep 3676681 = 2757511) B2757511
theorem B8714785 : Blo 1811607 8714785 := bstep (se 2 (by rfl) ⟨3268044, by rfl⟩ : syracuseStep 8714785 = 6536089) B6536089
theorem B11770427 : Blo 1811607 11770427 := bstep (se 1 (by rfl) ⟨8827820, by rfl⟩ : syracuseStep 11770427 = 17655641) B17655641
theorem B2038351 : Blo 1811607 2038351 := bstep (se 1 (by rfl) ⟨1528763, by rfl⟩ : syracuseStep 2038351 = 3057527) B3057527
theorem B2718287 : Blo 1811607 2718287 := bstep (se 1 (by rfl) ⟨2038715, by rfl⟩ : syracuseStep 2718287 = 4077431) B4077431
theorem B13769351 : Blo 1811607 13769351 := bstep (se 1 (by rfl) ⟨10327013, by rfl⟩ : syracuseStep 13769351 = 20654027) B20654027
theorem B2718407 : Blo 1811607 2718407 := bstep (se 1 (by rfl) ⟨2038805, by rfl⟩ : syracuseStep 2718407 = 4077611) B4077611
theorem B27908957 : Blo 1811607 27908957 := bstep (se 3 (by rfl) ⟨5232929, by rfl⟩ : syracuseStep 27908957 = 10465859) B10465859
theorem B2718569 : Blo 1811607 2718569 := bstep (se 2 (by rfl) ⟨1019463, by rfl⟩ : syracuseStep 2718569 = 2038927) B2038927
theorem B4078511 : Blo 1811607 4078511 := bstep (se 1 (by rfl) ⟨3058883, by rfl⟩ : syracuseStep 4078511 = 6117767) B6117767
theorem B2718647 : Blo 1811607 2718647 := bstep (se 1 (by rfl) ⟨2038985, by rfl⟩ : syracuseStep 2718647 = 4077971) B4077971
theorem B2038747 : Blo 1811607 2038747 := bstep (se 1 (by rfl) ⟨1529060, by rfl⟩ : syracuseStep 2038747 = 3058121) B3058121
theorem B2718683 : Blo 1811607 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B4586503 : Blo 1811607 4586503 := bstep (se 1 (by rfl) ⟨3439877, by rfl⟩ : syracuseStep 4586503 = 6879755) B6879755
theorem B6118415 : Blo 1811607 6118415 := bstep (se 1 (by rfl) ⟨4588811, by rfl⟩ : syracuseStep 6118415 = 9177623) B9177623
theorem B13065259 : Blo 1811607 13065259 := bstep (se 1 (by rfl) ⟨9798944, by rfl⟩ : syracuseStep 13065259 = 19597889) B19597889
theorem B22666283 : Blo 1811607 22666283 := bstep (se 1 (by rfl) ⟨16999712, by rfl⟩ : syracuseStep 22666283 = 33999425) B33999425
theorem B6880409 : Blo 1811607 6880409 := bstep (se 2 (by rfl) ⟨2580153, by rfl⟩ : syracuseStep 6880409 = 5160307) B5160307
theorem B4078763 : Blo 1811607 4078763 := bstep (se 1 (by rfl) ⟨3059072, by rfl⟩ : syracuseStep 4078763 = 6118145) B6118145
theorem B23231681 : Blo 1811607 23231681 := bstep (se 2 (by rfl) ⟨8711880, by rfl⟩ : syracuseStep 23231681 = 17423761) B17423761
theorem B8707267 : Blo 1811607 8707267 := bstep (se 1 (by rfl) ⟨6530450, by rfl⟩ : syracuseStep 8707267 = 13060901) B13060901
theorem B10321091 : Blo 1811607 10321091 := bstep (se 1 (by rfl) ⟨7740818, by rfl⟩ : syracuseStep 10321091 = 15481637) B15481637
theorem B2039215 : Blo 1811607 2039215 := bstep (se 1 (by rfl) ⟨1529411, by rfl⟩ : syracuseStep 2039215 = 3058823) B3058823
theorem B2719151 : Blo 1811607 2719151 := bstep (se 1 (by rfl) ⟨2039363, by rfl⟩ : syracuseStep 2719151 = 4078727) B4078727
theorem B2293211 : Blo 1811607 2293211 := bstep (se 1 (by rfl) ⟨1719908, by rfl⟩ : syracuseStep 2293211 = 3439817) B3439817
theorem B2719241 : Blo 1811607 2719241 := bstep (se 2 (by rfl) ⟨1019715, by rfl⟩ : syracuseStep 2719241 = 2039431) B2039431
theorem B2719271 : Blo 1811607 2719271 := bstep (se 1 (by rfl) ⟨2039453, by rfl⟩ : syracuseStep 2719271 = 4078907) B4078907
theorem B6119009 : Blo 1811607 6119009 := bstep (se 2 (by rfl) ⟨2294628, by rfl⟩ : syracuseStep 6119009 = 4589257) B4589257
theorem B4587131 : Blo 1811607 4587131 := bstep (se 1 (by rfl) ⟨3440348, by rfl⟩ : syracuseStep 4587131 = 6880697) B6880697
theorem B2719355 : Blo 1811607 2719355 := bstep (se 1 (by rfl) ⟨2039516, by rfl⟩ : syracuseStep 2719355 = 4079033) B4079033
theorem B6201017 : Blo 1811607 6201017 := bstep (se 2 (by rfl) ⟨2325381, by rfl⟩ : syracuseStep 6201017 = 4650763) B4650763
theorem B4079303 : Blo 1811607 4079303 := bstep (se 1 (by rfl) ⟨3059477, by rfl⟩ : syracuseStep 4079303 = 6118955) B6118955
theorem B2719481 : Blo 1811607 2719481 := bstep (se 2 (by rfl) ⟨1019805, by rfl⟩ : syracuseStep 2719481 = 2039611) B2039611
theorem B2039647 : Blo 1811607 2039647 := bstep (se 1 (by rfl) ⟨1529735, by rfl⟩ : syracuseStep 2039647 = 3059471) B3059471
theorem B2719583 : Blo 1811607 2719583 := bstep (se 1 (by rfl) ⟨2039687, by rfl⟩ : syracuseStep 2719583 = 4079375) B4079375
theorem B2719595 : Blo 1811607 2719595 := bstep (se 1 (by rfl) ⟨2039696, by rfl⟩ : syracuseStep 2719595 = 4079393) B4079393
theorem B4587425 : Blo 1811607 4587425 := bstep (se 2 (by rfl) ⟨1720284, by rfl⟩ : syracuseStep 4587425 = 3440569) B3440569
theorem B2293687 : Blo 1811607 2293687 := bstep (se 1 (by rfl) ⟨1720265, by rfl⟩ : syracuseStep 2293687 = 3440531) B3440531
theorem B9175193 : Blo 1811607 9175193 := bstep (se 2 (by rfl) ⟨3440697, by rfl⟩ : syracuseStep 9175193 = 6881395) B6881395
theorem B20136089 : Blo 1811607 20136089 := bstep (se 2 (by rfl) ⟨7551033, by rfl⟩ : syracuseStep 20136089 = 15102067) B15102067
theorem B2720009 : Blo 1811607 2720009 := bstep (se 2 (by rfl) ⟨1020003, by rfl⟩ : syracuseStep 2720009 = 2040007) B2040007
theorem B2720111 : Blo 1811607 2720111 := bstep (se 1 (by rfl) ⟨2040083, by rfl⟩ : syracuseStep 2720111 = 4080167) B4080167
theorem B2040187 : Blo 1811607 2040187 := bstep (se 1 (by rfl) ⟨1530140, by rfl⟩ : syracuseStep 2040187 = 3060281) B3060281
theorem B2294183 : Blo 1811607 2294183 := bstep (se 1 (by rfl) ⟨1720637, by rfl⟩ : syracuseStep 2294183 = 3441275) B3441275
theorem B2294335 : Blo 1811607 2294335 := bstep (se 1 (by rfl) ⟨1720751, by rfl⟩ : syracuseStep 2294335 = 3441503) B3441503
theorem B4588103 : Blo 1811607 4588103 := bstep (se 1 (by rfl) ⟨3441077, by rfl⟩ : syracuseStep 4588103 = 6882155) B6882155
theorem B2720327 : Blo 1811607 2720327 := bstep (se 1 (by rfl) ⟨2040245, by rfl⟩ : syracuseStep 2720327 = 4080491) B4080491
theorem B2720363 : Blo 1811607 2720363 := bstep (se 1 (by rfl) ⟨2040272, by rfl⟩ : syracuseStep 2720363 = 4080545) B4080545
theorem B27902599 : Blo 1811607 27902599 := bstep (se 1 (by rfl) ⟨20926949, by rfl⟩ : syracuseStep 27902599 = 41853899) B41853899
theorem B5808793 : Blo 1811607 5808793 := bstep (se 2 (by rfl) ⟨2178297, by rfl⟩ : syracuseStep 5808793 = 4356595) B4356595
theorem B6120089 : Blo 1811607 6120089 := bstep (se 2 (by rfl) ⟨2295033, by rfl⟩ : syracuseStep 6120089 = 4590067) B4590067
theorem B4080311 : Blo 1811607 4080311 := bstep (se 1 (by rfl) ⟨3060233, by rfl⟩ : syracuseStep 4080311 = 6120467) B6120467
theorem B21504727 : Blo 1811607 21504727 := bstep (se 1 (by rfl) ⟨16128545, by rfl⟩ : syracuseStep 21504727 = 32257091) B32257091
theorem B5513951 : Blo 1811607 5513951 := bstep (se 1 (by rfl) ⟨4135463, by rfl⟩ : syracuseStep 5513951 = 8270927) B8270927
theorem B2294507 : Blo 1811607 2294507 := bstep (se 1 (by rfl) ⟨1720880, by rfl⟩ : syracuseStep 2294507 = 3441761) B3441761
theorem B4080527 : Blo 1811607 4080527 := bstep (se 1 (by rfl) ⟨3060395, by rfl⟩ : syracuseStep 4080527 = 6120791) B6120791
theorem B9176003 : Blo 1811607 9176003 := bstep (se 1 (by rfl) ⟨6882002, by rfl⟩ : syracuseStep 9176003 = 13764005) B13764005
theorem B83731445 : Blo 1811607 83731445 := bstep (se 5 (by rfl) ⟨3924911, by rfl⟩ : syracuseStep 83731445 = 7849823) B7849823
theorem B1811743 : Blo 1811607 1811743 := bstep (se 1 (by rfl) ⟨1358807, by rfl⟩ : syracuseStep 1811743 = 2717615) B2717615
theorem B2581799 : Blo 1811607 2581799 := bstep (se 1 (by rfl) ⟨1936349, by rfl⟩ : syracuseStep 2581799 = 3872699) B3872699
theorem B14705969 : Blo 1811607 14705969 := bstep (se 2 (by rfl) ⟨5514738, by rfl⟩ : syracuseStep 14705969 = 11029477) B11029477
theorem B14894387 : Blo 1811607 14894387 := bstep (se 1 (by rfl) ⟨11170790, by rfl⟩ : syracuseStep 14894387 = 22341581) B22341581
theorem B1811803 : Blo 1811607 1811803 := bstep (se 1 (by rfl) ⟨1358852, by rfl⟩ : syracuseStep 1811803 = 2717705) B2717705
theorem B1811823 : Blo 1811607 1811823 := bstep (se 1 (by rfl) ⟨1358867, by rfl⟩ : syracuseStep 1811823 = 2717735) B2717735
theorem B9799051 : Blo 1811607 9799051 := bstep (se 1 (by rfl) ⟨7349288, by rfl⟩ : syracuseStep 9799051 = 14698577) B14698577
theorem B1811879 : Blo 1811607 1811879 := bstep (se 1 (by rfl) ⟨1358909, by rfl⟩ : syracuseStep 1811879 = 2717819) B2717819
theorem B3057095 : Blo 1811607 3057095 := bstep (se 1 (by rfl) ⟨2292821, by rfl⟩ : syracuseStep 3057095 = 4585643) B4585643
theorem B1811963 : Blo 1811607 1811963 := bstep (se 1 (by rfl) ⟨1358972, by rfl⟩ : syracuseStep 1811963 = 2717945) B2717945
theorem B1812031 : Blo 1811607 1812031 := bstep (se 1 (by rfl) ⟨1359023, by rfl⟩ : syracuseStep 1812031 = 2718047) B2718047
theorem B1812039 : Blo 1811607 1812039 := bstep (se 1 (by rfl) ⟨1359029, by rfl⟩ : syracuseStep 1812039 = 2718059) B2718059
theorem B9799355 : Blo 1811607 9799355 := bstep (se 1 (by rfl) ⟨7349516, by rfl⟩ : syracuseStep 9799355 = 14699033) B14699033
theorem B1812191 : Blo 1811607 1812191 := bstep (se 1 (by rfl) ⟨1359143, by rfl⟩ : syracuseStep 1812191 = 2718287) B2718287
theorem B1812271 : Blo 1811607 1812271 := bstep (se 1 (by rfl) ⟨1359203, by rfl⟩ : syracuseStep 1812271 = 2718407) B2718407
theorem B6883127 : Blo 1811607 6883127 := bstep (se 1 (by rfl) ⟨5162345, by rfl⟩ : syracuseStep 6883127 = 10324691) B10324691
theorem B4589369 : Blo 1811607 4589369 := bstep (se 2 (by rfl) ⟨1721013, by rfl⟩ : syracuseStep 4589369 = 3442027) B3442027
theorem B18605971 : Blo 1811607 18605971 := bstep (se 1 (by rfl) ⟨13954478, by rfl⟩ : syracuseStep 18605971 = 27908957) B27908957
theorem B1812379 : Blo 1811607 1812379 := bstep (se 1 (by rfl) ⟨1359284, by rfl⟩ : syracuseStep 1812379 = 2718569) B2718569
theorem B1812431 : Blo 1811607 1812431 := bstep (se 1 (by rfl) ⟨1359323, by rfl⟩ : syracuseStep 1812431 = 2718647) B2718647
theorem B1812455 : Blo 1811607 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B17426609 : Blo 1811607 17426609 := bstep (se 2 (by rfl) ⟨6534978, by rfl⟩ : syracuseStep 17426609 = 13069957) B13069957
theorem B6883613 : Blo 1811607 6883613 := bstep (se 3 (by rfl) ⟨1290677, by rfl⟩ : syracuseStep 6883613 = 2581355) B2581355
theorem B1812767 : Blo 1811607 1812767 := bstep (se 1 (by rfl) ⟨1359575, by rfl⟩ : syracuseStep 1812767 = 2719151) B2719151
theorem B20637989 : Blo 1811607 20637989 := bstep (se 4 (by rfl) ⟨1934811, by rfl⟩ : syracuseStep 20637989 = 3869623) B3869623
theorem B1812827 : Blo 1811607 1812827 := bstep (se 1 (by rfl) ⟨1359620, by rfl⟩ : syracuseStep 1812827 = 2719241) B2719241
theorem B1812847 : Blo 1811607 1812847 := bstep (se 1 (by rfl) ⟨1359635, by rfl⟩ : syracuseStep 1812847 = 2719271) B2719271
theorem B15485327 : Blo 1811607 15485327 := bstep (se 1 (by rfl) ⟨11613995, by rfl⟩ : syracuseStep 15485327 = 23227991) B23227991
theorem B3058087 : Blo 1811607 3058087 := bstep (se 1 (by rfl) ⟨2293565, by rfl⟩ : syracuseStep 3058087 = 4587131) B4587131
theorem B1812903 : Blo 1811607 1812903 := bstep (se 1 (by rfl) ⟨1359677, by rfl⟩ : syracuseStep 1812903 = 2719355) B2719355
theorem B1812987 : Blo 1811607 1812987 := bstep (se 1 (by rfl) ⟨1359740, by rfl⟩ : syracuseStep 1812987 = 2719481) B2719481
theorem B1813055 : Blo 1811607 1813055 := bstep (se 1 (by rfl) ⟨1359791, by rfl⟩ : syracuseStep 1813055 = 2719583) B2719583
theorem B1813063 : Blo 1811607 1813063 := bstep (se 1 (by rfl) ⟨1359797, by rfl⟩ : syracuseStep 1813063 = 2719595) B2719595
theorem B3058249 : Blo 1811607 3058249 := bstep (se 2 (by rfl) ⟨1146843, by rfl⟩ : syracuseStep 3058249 = 2293687) B2293687
theorem B108808805 : Blo 1811607 108808805 := bstep (se 4 (by rfl) ⟨10200825, by rfl⟩ : syracuseStep 108808805 = 20401651) B20401651
theorem B3058283 : Blo 1811607 3058283 := bstep (se 1 (by rfl) ⟨2293712, by rfl⟩ : syracuseStep 3058283 = 4587425) B4587425
theorem B2755193 : Blo 1811607 2755193 := bstep (se 2 (by rfl) ⟨1033197, by rfl⟩ : syracuseStep 2755193 = 2066395) B2066395
theorem B6531779 : Blo 1811607 6531779 := bstep (se 1 (by rfl) ⟨4898834, by rfl⟩ : syracuseStep 6531779 = 9797669) B9797669
theorem B1813215 : Blo 1811607 1813215 := bstep (se 1 (by rfl) ⟨1359911, by rfl⟩ : syracuseStep 1813215 = 2719823) B2719823
theorem B1813295 : Blo 1811607 1813295 := bstep (se 1 (by rfl) ⟨1359971, by rfl⟩ : syracuseStep 1813295 = 2719943) B2719943
theorem B6114203 : Blo 1811607 6114203 := bstep (se 1 (by rfl) ⟨4585652, by rfl⟩ : syracuseStep 6114203 = 9171305) B9171305
theorem B1813403 : Blo 1811607 1813403 := bstep (se 1 (by rfl) ⟨1360052, by rfl⟩ : syracuseStep 1813403 = 2720105) B2720105
theorem B2067407 : Blo 1811607 2067407 := bstep (se 1 (by rfl) ⟨1550555, by rfl⟩ : syracuseStep 2067407 = 3101111) B3101111
theorem B1813455 : Blo 1811607 1813455 := bstep (se 1 (by rfl) ⟨1360091, by rfl⟩ : syracuseStep 1813455 = 2720183) B2720183
theorem B1813479 : Blo 1811607 1813479 := bstep (se 1 (by rfl) ⟨1360109, by rfl⟩ : syracuseStep 1813479 = 2720219) B2720219
theorem B4353011 : Blo 1811607 4353011 := bstep (se 1 (by rfl) ⟨3264758, by rfl⟩ : syracuseStep 4353011 = 6529517) B6529517
theorem B66169871 : Blo 1811607 66169871 := bstep (se 1 (by rfl) ⟨49627403, by rfl⟩ : syracuseStep 66169871 = 99254807) B99254807
theorem B6532285 : Blo 1811607 6532285 := bstep (se 3 (by rfl) ⟨1224803, by rfl⟩ : syracuseStep 6532285 = 2449607) B2449607
theorem B4902077 : Blo 1811607 4902077 := bstep (se 3 (by rfl) ⟨919139, by rfl⟩ : syracuseStep 4902077 = 1838279) B1838279
theorem B119237923 : Blo 1811607 119237923 := bstep (se 1 (by rfl) ⟨89428442, by rfl⟩ : syracuseStep 119237923 = 178856885) B178856885
theorem B186182957 : Blo 1811607 186182957 := bstep (se 3 (by rfl) ⟨34909304, by rfl⟩ : syracuseStep 186182957 = 69818609) B69818609
theorem B13765949 : Blo 1811607 13765949 := bstep (se 3 (by rfl) ⟨2581115, by rfl⟩ : syracuseStep 13765949 = 5162231) B5162231
theorem B7744835 : Blo 1811607 7744835 := bstep (se 1 (by rfl) ⟨5808626, by rfl⟩ : syracuseStep 7744835 = 11617253) B11617253
theorem B27897185 : Blo 1811607 27897185 := bstep (se 2 (by rfl) ⟨10461444, by rfl⟩ : syracuseStep 27897185 = 20922889) B20922889
theorem B4902241 : Blo 1811607 4902241 := bstep (se 2 (by rfl) ⟨1838340, by rfl⟩ : syracuseStep 4902241 = 3676681) B3676681
theorem B11619713 : Blo 1811607 11619713 := bstep (se 2 (by rfl) ⟨4357392, by rfl⟩ : syracuseStep 11619713 = 8714785) B8714785
theorem B3722939 : Blo 1811607 3722939 := bstep (se 1 (by rfl) ⟨2792204, by rfl⟩ : syracuseStep 3722939 = 5584409) B5584409
theorem B6115229 : Blo 1811607 6115229 := bstep (se 3 (by rfl) ⟨1146605, by rfl⟩ : syracuseStep 6115229 = 2293211) B2293211
theorem B6115337 : Blo 1811607 6115337 := bstep (se 2 (by rfl) ⟨2293251, by rfl⟩ : syracuseStep 6115337 = 4586503) B4586503
theorem B17420345 : Blo 1811607 17420345 := bstep (se 2 (by rfl) ⟨6532629, by rfl⟩ : syracuseStep 17420345 = 13065259) B13065259
theorem B6885587 : Blo 1811607 6885587 := bstep (se 1 (by rfl) ⟨5164190, by rfl⟩ : syracuseStep 6885587 = 10328381) B10328381
theorem B20648195 : Blo 1811607 20648195 := bstep (se 1 (by rfl) ⟨15486146, by rfl⟩ : syracuseStep 20648195 = 30972293) B30972293
theorem B3059977 : Blo 1811607 3059977 := bstep (se 2 (by rfl) ⟨1147491, by rfl⟩ : syracuseStep 3059977 = 2294983) B2294983
theorem B9179567 : Blo 1811607 9179567 := bstep (se 1 (by rfl) ⟨6884675, by rfl⟩ : syracuseStep 9179567 = 13769351) B13769351
theorem B31830509 : Blo 1811607 31830509 := bstep (se 3 (by rfl) ⟨5968220, by rfl⟩ : syracuseStep 31830509 = 11936441) B11936441
theorem B4076153 : Blo 1811607 4076153 := bstep (se 2 (by rfl) ⟨1528557, by rfl⟩ : syracuseStep 4076153 = 3057115) B3057115
theorem B10326649 : Blo 1811607 10326649 := bstep (se 2 (by rfl) ⟨3872493, by rfl⟩ : syracuseStep 10326649 = 7744987) B7744987
theorem B4076207 : Blo 1811607 4076207 := bstep (se 1 (by rfl) ⟨3057155, by rfl⟩ : syracuseStep 4076207 = 6114311) B6114311
theorem B15110855 : Blo 1811607 15110855 := bstep (se 1 (by rfl) ⟨11333141, by rfl⟩ : syracuseStep 15110855 = 22666283) B22666283
theorem B4076279 : Blo 1811607 4076279 := bstep (se 1 (by rfl) ⟨3057209, by rfl⟩ : syracuseStep 4076279 = 6114419) B6114419
theorem B15487787 : Blo 1811607 15487787 := bstep (se 1 (by rfl) ⟨11615840, by rfl⟩ : syracuseStep 15487787 = 23231681) B23231681
theorem B9171791 : Blo 1811607 9171791 := bstep (se 1 (by rfl) ⟨6878843, by rfl⟩ : syracuseStep 9171791 = 13757687) B13757687
theorem B6370127 : Blo 1811607 6370127 := bstep (se 1 (by rfl) ⟨4777595, by rfl⟩ : syracuseStep 6370127 = 9555191) B9555191
theorem B4076459 : Blo 1811607 4076459 := bstep (se 1 (by rfl) ⟨3057344, by rfl⟩ : syracuseStep 4076459 = 6114689) B6114689
theorem B4134011 : Blo 1811607 4134011 := bstep (se 1 (by rfl) ⟨3100508, by rfl⟩ : syracuseStep 4134011 = 6201017) B6201017
theorem B9172115 : Blo 1811607 9172115 := bstep (se 1 (by rfl) ⟨6879086, by rfl⟩ : syracuseStep 9172115 = 13758173) B13758173
theorem B7845113 : Blo 1811607 7845113 := bstep (se 2 (by rfl) ⟨2941917, by rfl⟩ : syracuseStep 7845113 = 5883835) B5883835
theorem B4355423 : Blo 1811607 4355423 := bstep (se 1 (by rfl) ⟨3266567, by rfl⟩ : syracuseStep 4355423 = 6533135) B6533135
theorem B9180539 : Blo 1811607 9180539 := bstep (se 1 (by rfl) ⟨6885404, by rfl⟩ : syracuseStep 9180539 = 13770809) B13770809
theorem B57365923 : Blo 1811607 57365923 := bstep (se 1 (by rfl) ⟨43024442, by rfl⟩ : syracuseStep 57365923 = 86048885) B86048885
theorem B4076999 : Blo 1811607 4076999 := bstep (se 1 (by rfl) ⟨3057749, by rfl⟩ : syracuseStep 4076999 = 6115499) B6115499
theorem B3265991 : Blo 1811607 3265991 := bstep (se 1 (by rfl) ⟨2449493, by rfl⟩ : syracuseStep 3265991 = 4898987) B4898987
theorem B17413613 : Blo 1811607 17413613 := bstep (se 3 (by rfl) ⟨3265052, by rfl⟩ : syracuseStep 17413613 = 6530105) B6530105
theorem B13768379 : Blo 1811607 13768379 := bstep (se 1 (by rfl) ⟨10326284, by rfl⟩ : syracuseStep 13768379 = 20652569) B20652569
theorem B3872443 : Blo 1811607 3872443 := bstep (se 1 (by rfl) ⟨2904332, by rfl⟩ : syracuseStep 3872443 = 5808665) B5808665
theorem B4077359 : Blo 1811607 4077359 := bstep (se 1 (by rfl) ⟨3058019, by rfl⟩ : syracuseStep 4077359 = 6116039) B6116039
theorem B2717495 : Blo 1811607 2717495 := bstep (se 1 (by rfl) ⟨2038121, by rfl⟩ : syracuseStep 2717495 = 4076243) B4076243
theorem B30963545 : Blo 1811607 30963545 := bstep (se 2 (by rfl) ⟨11611329, by rfl⟩ : syracuseStep 30963545 = 23222659) B23222659
theorem B5101417 : Blo 1811607 5101417 := bstep (se 2 (by rfl) ⟨1913031, by rfl⟩ : syracuseStep 5101417 = 3826063) B3826063
theorem B2717801 : Blo 1811607 2717801 := bstep (se 2 (by rfl) ⟨1019175, by rfl⟩ : syracuseStep 2717801 = 2038351) B2038351
theorem B7739657 : Blo 1811607 7739657 := bstep (se 2 (by rfl) ⟨2902371, by rfl⟩ : syracuseStep 7739657 = 5804743) B5804743
theorem B46438757 : Blo 1811607 46438757 := bstep (se 4 (by rfl) ⟨4353633, by rfl⟩ : syracuseStep 46438757 = 8707267) B8707267
theorem B4585835 : Blo 1811607 4585835 := bstep (se 1 (by rfl) ⟨3439376, by rfl⟩ : syracuseStep 4585835 = 6878753) B6878753
theorem B4077935 : Blo 1811607 4077935 := bstep (se 1 (by rfl) ⟨3058451, by rfl⟩ : syracuseStep 4077935 = 6116903) B6116903
theorem B11614589 : Blo 1811607 11614589 := bstep (se 3 (by rfl) ⟨2177735, by rfl⟩ : syracuseStep 11614589 = 4355471) B4355471
theorem B2718119 : Blo 1811607 2718119 := bstep (se 1 (by rfl) ⟨2038589, by rfl⟩ : syracuseStep 2718119 = 4077179) B4077179
theorem B4078007 : Blo 1811607 4078007 := bstep (se 1 (by rfl) ⟨3058505, by rfl⟩ : syracuseStep 4078007 = 6117011) B6117011
theorem B2718203 : Blo 1811607 2718203 := bstep (se 1 (by rfl) ⟨2038652, by rfl⟩ : syracuseStep 2718203 = 4077305) B4077305
theorem B4897343 : Blo 1811607 4897343 := bstep (se 1 (by rfl) ⟨3673007, by rfl⟩ : syracuseStep 4897343 = 7346015) B7346015
theorem B4356671 : Blo 1811607 4356671 := bstep (se 1 (by rfl) ⟨3267503, by rfl⟩ : syracuseStep 4356671 = 6535007) B6535007
theorem B4078151 : Blo 1811607 4078151 := bstep (se 1 (by rfl) ⟨3058613, by rfl⟩ : syracuseStep 4078151 = 6117227) B6117227
theorem B4078187 : Blo 1811607 4078187 := bstep (se 1 (by rfl) ⟨3058640, by rfl⟩ : syracuseStep 4078187 = 6117281) B6117281
theorem B2718329 : Blo 1811607 2718329 := bstep (se 2 (by rfl) ⟨1019373, by rfl⟩ : syracuseStep 2718329 = 2038747) B2038747
theorem B4586159 : Blo 1811607 4586159 := bstep (se 1 (by rfl) ⟨3439619, by rfl⟩ : syracuseStep 4586159 = 6879239) B6879239
theorem B2718383 : Blo 1811607 2718383 := bstep (se 1 (by rfl) ⟨2038787, by rfl⟩ : syracuseStep 2718383 = 4077575) B4077575
theorem B2038495 : Blo 1811607 2038495 := bstep (se 1 (by rfl) ⟨1528871, by rfl⟩ : syracuseStep 2038495 = 3057743) B3057743
theorem B2718431 : Blo 1811607 2718431 := bstep (se 1 (by rfl) ⟨2038823, by rfl⟩ : syracuseStep 2718431 = 4077647) B4077647
theorem B2718695 : Blo 1811607 2718695 := bstep (se 1 (by rfl) ⟨2039021, by rfl⟩ : syracuseStep 2718695 = 4078043) B4078043
theorem B4586483 : Blo 1811607 4586483 := bstep (se 1 (by rfl) ⟨3439862, by rfl⟩ : syracuseStep 4586483 = 6879725) B6879725
theorem B4078583 : Blo 1811607 4078583 := bstep (se 1 (by rfl) ⟨3058937, by rfl⟩ : syracuseStep 4078583 = 6117875) B6117875
theorem B7846951 : Blo 1811607 7846951 := bstep (se 1 (by rfl) ⟨5885213, by rfl⟩ : syracuseStep 7846951 = 11770427) B11770427
theorem B6118523 : Blo 1811607 6118523 := bstep (se 1 (by rfl) ⟨4588892, by rfl⟩ : syracuseStep 6118523 = 9177785) B9177785
theorem B5160125 : Blo 1811607 5160125 := bstep (se 3 (by rfl) ⟨967523, by rfl⟩ : syracuseStep 5160125 = 1935047) B1935047
theorem B2718953 : Blo 1811607 2718953 := bstep (se 2 (by rfl) ⟨1019607, by rfl⟩ : syracuseStep 2718953 = 2039215) B2039215
theorem B7740683 : Blo 1811607 7740683 := bstep (se 1 (by rfl) ⟨5805512, by rfl⟩ : syracuseStep 7740683 = 11611025) B11611025
theorem B2039071 : Blo 1811607 2039071 := bstep (se 1 (by rfl) ⟨1529303, by rfl⟩ : syracuseStep 2039071 = 3058607) B3058607
theorem B2719007 : Blo 1811607 2719007 := bstep (se 1 (by rfl) ⟨2039255, by rfl⟩ : syracuseStep 2719007 = 4078511) B4078511
theorem B4078943 : Blo 1811607 4078943 := bstep (se 1 (by rfl) ⟨3059207, by rfl⟩ : syracuseStep 4078943 = 6118415) B6118415
theorem B6118793 : Blo 1811607 6118793 := bstep (se 2 (by rfl) ⟨2294547, by rfl⟩ : syracuseStep 6118793 = 4589095) B4589095
theorem B4586939 : Blo 1811607 4586939 := bstep (se 1 (by rfl) ⟨3440204, by rfl⟩ : syracuseStep 4586939 = 6880409) B6880409
theorem B2719175 : Blo 1811607 2719175 := bstep (se 1 (by rfl) ⟨2039381, by rfl⟩ : syracuseStep 2719175 = 4078763) B4078763
theorem B6880727 : Blo 1811607 6880727 := bstep (se 1 (by rfl) ⟨5160545, by rfl⟩ : syracuseStep 6880727 = 10321091) B10321091
theorem B10468889 : Blo 1811607 10468889 := bstep (se 2 (by rfl) ⟨3925833, by rfl⟩ : syracuseStep 10468889 = 7851667) B7851667
theorem B2039359 : Blo 1811607 2039359 := bstep (se 1 (by rfl) ⟨1529519, by rfl⟩ : syracuseStep 2039359 = 3059039) B3059039
theorem B13770323 : Blo 1811607 13770323 := bstep (se 1 (by rfl) ⟨10327742, by rfl⟩ : syracuseStep 13770323 = 20655485) B20655485
theorem B4079339 : Blo 1811607 4079339 := bstep (se 1 (by rfl) ⟨3059504, by rfl⟩ : syracuseStep 4079339 = 6119009) B6119009
theorem B2719529 : Blo 1811607 2719529 := bstep (se 2 (by rfl) ⟨1019823, by rfl⟩ : syracuseStep 2719529 = 2039647) B2039647
theorem B2719535 : Blo 1811607 2719535 := bstep (se 1 (by rfl) ⟨2039651, by rfl⟩ : syracuseStep 2719535 = 4079303) B4079303
theorem B6119225 : Blo 1811607 6119225 := bstep (se 2 (by rfl) ⟨2294709, by rfl⟩ : syracuseStep 6119225 = 4589419) B4589419
theorem B4079465 : Blo 1811607 4079465 := bstep (se 2 (by rfl) ⟨1529799, by rfl⟩ : syracuseStep 4079465 = 3059599) B3059599
theorem B6119711 : Blo 1811607 6119711 := bstep (se 1 (by rfl) ⟨4589783, by rfl⟩ : syracuseStep 6119711 = 9179567) B9179567
theorem B4079969 : Blo 1811607 4079969 := bstep (se 2 (by rfl) ⟨1529988, by rfl⟩ : syracuseStep 4079969 = 3059977) B3059977
theorem B4080059 : Blo 1811607 4080059 := bstep (se 1 (by rfl) ⟨3060044, by rfl⟩ : syracuseStep 4080059 = 6120089) B6120089
theorem B2720207 : Blo 1811607 2720207 := bstep (se 1 (by rfl) ⟨2040155, by rfl⟩ : syracuseStep 2720207 = 4080311) B4080311
theorem B2720249 : Blo 1811607 2720249 := bstep (se 2 (by rfl) ⟨1020093, by rfl⟩ : syracuseStep 2720249 = 2040187) B2040187
theorem B2720351 : Blo 1811607 2720351 := bstep (se 1 (by rfl) ⟨2040263, by rfl⟩ : syracuseStep 2720351 = 4080527) B4080527
theorem B55820963 : Blo 1811607 55820963 := bstep (se 1 (by rfl) ⟨41865722, by rfl⟩ : syracuseStep 55820963 = 83731445) B83731445
theorem B39215917 : Blo 1811607 39215917 := bstep (se 3 (by rfl) ⟨7352984, by rfl⟩ : syracuseStep 39215917 = 14705969) B14705969
theorem B9929591 : Blo 1811607 9929591 := bstep (se 1 (by rfl) ⟨7447193, by rfl⟩ : syracuseStep 9929591 = 14894387) B14894387
theorem B6120359 : Blo 1811607 6120359 := bstep (se 1 (by rfl) ⟨4590269, by rfl⟩ : syracuseStep 6120359 = 9180539) B9180539
theorem B28672969 : Blo 1811607 28672969 := bstep (se 2 (by rfl) ⟨10752363, by rfl⟩ : syracuseStep 28672969 = 21504727) B21504727
theorem B11609075 : Blo 1811607 11609075 := bstep (se 1 (by rfl) ⟨8706806, by rfl⟩ : syracuseStep 11609075 = 17413613) B17413613
theorem B1811663 : Blo 1811607 1811663 := bstep (se 1 (by rfl) ⟨1358747, by rfl⟩ : syracuseStep 1811663 = 2717495) B2717495
theorem B4588751 : Blo 1811607 4588751 := bstep (se 1 (by rfl) ⟨3441563, by rfl⟩ : syracuseStep 4588751 = 6883127) B6883127
theorem B10462601 : Blo 1811607 10462601 := bstep (se 2 (by rfl) ⟨3923475, by rfl⟩ : syracuseStep 10462601 = 7846951) B7846951
theorem B1811867 : Blo 1811607 1811867 := bstep (se 1 (by rfl) ⟨1358900, by rfl⟩ : syracuseStep 1811867 = 2717801) B2717801
theorem B11617739 : Blo 1811607 11617739 := bstep (se 1 (by rfl) ⟨8713304, by rfl⟩ : syracuseStep 11617739 = 17426609) B17426609
theorem B11617789 : Blo 1811607 11617789 := bstep (se 3 (by rfl) ⟨2178335, by rfl⟩ : syracuseStep 11617789 = 4356671) B4356671
theorem B4589075 : Blo 1811607 4589075 := bstep (se 1 (by rfl) ⟨3441806, by rfl⟩ : syracuseStep 4589075 = 6883613) B6883613
theorem B30959171 : Blo 1811607 30959171 := bstep (se 1 (by rfl) ⟨23219378, by rfl⟩ : syracuseStep 30959171 = 46438757) B46438757
theorem B3057223 : Blo 1811607 3057223 := bstep (se 1 (by rfl) ⟨2292917, by rfl⟩ : syracuseStep 3057223 = 4585835) B4585835
theorem B8709713 : Blo 1811607 8709713 := bstep (se 2 (by rfl) ⟨3266142, by rfl⟩ : syracuseStep 8709713 = 6532285) B6532285
theorem B7743059 : Blo 1811607 7743059 := bstep (se 1 (by rfl) ⟨5807294, by rfl⟩ : syracuseStep 7743059 = 11614589) B11614589
theorem B10323551 : Blo 1811607 10323551 := bstep (se 1 (by rfl) ⟨7742663, by rfl⟩ : syracuseStep 10323551 = 15485327) B15485327
theorem B1812079 : Blo 1811607 1812079 := bstep (se 1 (by rfl) ⟨1359059, by rfl⟩ : syracuseStep 1812079 = 2718119) B2718119
theorem B1812135 : Blo 1811607 1812135 := bstep (se 1 (by rfl) ⟨1359101, by rfl⟩ : syracuseStep 1812135 = 2718203) B2718203
theorem B158983897 : Blo 1811607 158983897 := bstep (se 2 (by rfl) ⟨59618961, by rfl⟩ : syracuseStep 158983897 = 119237923) B119237923
theorem B1812219 : Blo 1811607 1812219 := bstep (se 1 (by rfl) ⟨1359164, by rfl⟩ : syracuseStep 1812219 = 2718329) B2718329
theorem B3057439 : Blo 1811607 3057439 := bstep (se 1 (by rfl) ⟨2293079, by rfl⟩ : syracuseStep 3057439 = 4586159) B4586159
theorem B1812255 : Blo 1811607 1812255 := bstep (se 1 (by rfl) ⟨1359191, by rfl⟩ : syracuseStep 1812255 = 2718383) B2718383
theorem B1812287 : Blo 1811607 1812287 := bstep (se 1 (by rfl) ⟨1359215, by rfl⟩ : syracuseStep 1812287 = 2718431) B2718431
theorem B1812463 : Blo 1811607 1812463 := bstep (se 1 (by rfl) ⟨1359347, by rfl⟩ : syracuseStep 1812463 = 2718695) B2718695
theorem B3057655 : Blo 1811607 3057655 := bstep (se 1 (by rfl) ⟨2293241, by rfl⟩ : syracuseStep 3057655 = 4586483) B4586483
theorem B2902007 : Blo 1811607 2902007 := bstep (se 1 (by rfl) ⟨2176505, by rfl⟩ : syracuseStep 2902007 = 4353011) B4353011
theorem B1812635 : Blo 1811607 1812635 := bstep (se 1 (by rfl) ⟨1359476, by rfl⟩ : syracuseStep 1812635 = 2718953) B2718953
theorem B1812671 : Blo 1811607 1812671 := bstep (se 1 (by rfl) ⟨1359503, by rfl⟩ : syracuseStep 1812671 = 2719007) B2719007
theorem B9177299 : Blo 1811607 9177299 := bstep (se 1 (by rfl) ⟨6882974, by rfl⟩ : syracuseStep 9177299 = 13765949) B13765949
theorem B5163223 : Blo 1811607 5163223 := bstep (se 1 (by rfl) ⟨3872417, by rfl⟩ : syracuseStep 5163223 = 7744835) B7744835
theorem B18598123 : Blo 1811607 18598123 := bstep (se 1 (by rfl) ⟨13948592, by rfl⟩ : syracuseStep 18598123 = 27897185) B27897185
theorem B5163257 : Blo 1811607 5163257 := bstep (se 2 (by rfl) ⟨1936221, by rfl⟩ : syracuseStep 5163257 = 3872443) B3872443
theorem B3057959 : Blo 1811607 3057959 := bstep (se 1 (by rfl) ⟨2293469, by rfl⟩ : syracuseStep 3057959 = 4586939) B4586939
theorem B1812783 : Blo 1811607 1812783 := bstep (se 1 (by rfl) ⟨1359587, by rfl⟩ : syracuseStep 1812783 = 2719175) B2719175
theorem B6801889 : Blo 1811607 6801889 := bstep (se 2 (by rfl) ⟨2550708, by rfl⟩ : syracuseStep 6801889 = 5101417) B5101417
theorem B24807961 : Blo 1811607 24807961 := bstep (se 2 (by rfl) ⟨9302985, by rfl⟩ : syracuseStep 24807961 = 18605971) B18605971
theorem B1813019 : Blo 1811607 1813019 := bstep (se 1 (by rfl) ⟨1359764, by rfl⟩ : syracuseStep 1813019 = 2719529) B2719529
theorem B1813023 : Blo 1811607 1813023 := bstep (se 1 (by rfl) ⟨1359767, by rfl⟩ : syracuseStep 1813023 = 2719535) B2719535
theorem B4590391 : Blo 1811607 4590391 := bstep (se 1 (by rfl) ⟨3442793, by rfl⟩ : syracuseStep 4590391 = 6885587) B6885587
theorem B13765463 : Blo 1811607 13765463 := bstep (se 1 (by rfl) ⟨10324097, by rfl⟩ : syracuseStep 13765463 = 20648195) B20648195
theorem B1813339 : Blo 1811607 1813339 := bstep (se 1 (by rfl) ⟨1360004, by rfl⟩ : syracuseStep 1813339 = 2720009) B2720009
theorem B1813407 : Blo 1811607 1813407 := bstep (se 1 (by rfl) ⟨1360055, by rfl⟩ : syracuseStep 1813407 = 2720111) B2720111
theorem B3058735 : Blo 1811607 3058735 := bstep (se 1 (by rfl) ⟨2294051, by rfl⟩ : syracuseStep 3058735 = 4588103) B4588103
theorem B1813551 : Blo 1811607 1813551 := bstep (se 1 (by rfl) ⟨1360163, by rfl⟩ : syracuseStep 1813551 = 2720327) B2720327
theorem B1813575 : Blo 1811607 1813575 := bstep (se 1 (by rfl) ⟨1360181, by rfl⟩ : syracuseStep 1813575 = 2720363) B2720363
theorem B10325191 : Blo 1811607 10325191 := bstep (se 1 (by rfl) ⟨7743893, by rfl⟩ : syracuseStep 10325191 = 15487787) B15487787
theorem B6114527 : Blo 1811607 6114527 := bstep (se 1 (by rfl) ⟨4585895, by rfl⟩ : syracuseStep 6114527 = 9171791) B9171791
theorem B4246751 : Blo 1811607 4246751 := bstep (se 1 (by rfl) ⟨3185063, by rfl⟩ : syracuseStep 4246751 = 6370127) B6370127
theorem B3059113 : Blo 1811607 3059113 := bstep (se 2 (by rfl) ⟨1147167, by rfl⟩ : syracuseStep 3059113 = 2294335) B2294335
theorem B6114743 : Blo 1811607 6114743 := bstep (se 1 (by rfl) ⟨4586057, by rfl⟩ : syracuseStep 6114743 = 9172115) B9172115
theorem B6884797 : Blo 1811607 6884797 := bstep (se 3 (by rfl) ⟨1290899, by rfl⟩ : syracuseStep 6884797 = 2581799) B2581799
theorem B496487885 : Blo 1811607 496487885 := bstep (se 3 (by rfl) ⟨93091478, by rfl⟩ : syracuseStep 496487885 = 186182957) B186182957
theorem B7745057 : Blo 1811607 7745057 := bstep (se 2 (by rfl) ⟨2904396, by rfl⟩ : syracuseStep 7745057 = 5808793) B5808793
theorem B2903615 : Blo 1811607 2903615 := bstep (se 1 (by rfl) ⟨2177711, by rfl⟩ : syracuseStep 2903615 = 4355423) B4355423
theorem B6532903 : Blo 1811607 6532903 := bstep (se 1 (by rfl) ⟨4899677, by rfl⟩ : syracuseStep 6532903 = 9799355) B9799355
theorem B9178919 : Blo 1811607 9178919 := bstep (se 1 (by rfl) ⟨6884189, by rfl⟩ : syracuseStep 9178919 = 13768379) B13768379
theorem B3059579 : Blo 1811607 3059579 := bstep (se 1 (by rfl) ⟨2294684, by rfl⟩ : syracuseStep 3059579 = 4589369) B4589369
theorem B84881357 : Blo 1811607 84881357 := bstep (se 3 (by rfl) ⟨15915254, by rfl⟩ : syracuseStep 84881357 = 31830509) B31830509
theorem B13758659 : Blo 1811607 13758659 := bstep (se 1 (by rfl) ⟨10318994, by rfl⟩ : syracuseStep 13758659 = 20637989) B20637989
theorem B290156813 : Blo 1811607 290156813 := bstep (se 3 (by rfl) ⟨54404402, by rfl⟩ : syracuseStep 290156813 = 108808805) B108808805
theorem B3264895 : Blo 1811607 3264895 := bstep (se 1 (by rfl) ⟨2448671, by rfl⟩ : syracuseStep 3264895 = 4897343) B4897343
theorem B4354519 : Blo 1811607 4354519 := bstep (se 1 (by rfl) ⟨3265889, by rfl⟩ : syracuseStep 4354519 = 6531779) B6531779
theorem B4076135 : Blo 1811607 4076135 := bstep (se 1 (by rfl) ⟨3057101, by rfl⟩ : syracuseStep 4076135 = 6114203) B6114203
theorem B7746475 : Blo 1811607 7746475 := bstep (se 1 (by rfl) ⟨5809856, by rfl⟩ : syracuseStep 7746475 = 11619713) B11619713
theorem B9180215 : Blo 1811607 9180215 := bstep (se 1 (by rfl) ⟨6885161, by rfl⟩ : syracuseStep 9180215 = 13770323) B13770323
theorem B4076819 : Blo 1811607 4076819 := bstep (se 1 (by rfl) ⟨3057614, by rfl⟩ : syracuseStep 4076819 = 6115229) B6115229
theorem B4076891 : Blo 1811607 4076891 := bstep (se 1 (by rfl) ⟨3057668, by rfl⟩ : syracuseStep 4076891 = 6115337) B6115337
theorem B11613563 : Blo 1811607 11613563 := bstep (se 1 (by rfl) ⟨8710172, by rfl⟩ : syracuseStep 11613563 = 17420345) B17420345
theorem B6116795 : Blo 1811607 6116795 := bstep (se 1 (by rfl) ⟨4587596, by rfl⟩ : syracuseStep 6116795 = 9175193) B9175193
theorem B13424059 : Blo 1811607 13424059 := bstep (se 1 (by rfl) ⟨10068044, by rfl⟩ : syracuseStep 13424059 = 20136089) B20136089
theorem B11024029 : Blo 1811607 11024029 := bstep (se 3 (by rfl) ⟨2067005, by rfl⟩ : syracuseStep 11024029 = 4134011) B4134011
theorem B2717435 : Blo 1811607 2717435 := bstep (se 1 (by rfl) ⟨2038076, by rfl⟩ : syracuseStep 2717435 = 4076153) B4076153
theorem B2717471 : Blo 1811607 2717471 := bstep (se 1 (by rfl) ⟨2038103, by rfl⟩ : syracuseStep 2717471 = 4076207) B4076207
theorem B10073903 : Blo 1811607 10073903 := bstep (se 1 (by rfl) ⟨7555427, by rfl⟩ : syracuseStep 10073903 = 15110855) B15110855
theorem B13072205 : Blo 1811607 13072205 := bstep (se 3 (by rfl) ⟨2451038, by rfl⟩ : syracuseStep 13072205 = 4902077) B4902077
theorem B2717519 : Blo 1811607 2717519 := bstep (se 1 (by rfl) ⟨2038139, by rfl⟩ : syracuseStep 2717519 = 4076279) B4076279
theorem B4077449 : Blo 1811607 4077449 := bstep (se 2 (by rfl) ⟨1529043, by rfl⟩ : syracuseStep 4077449 = 3058087) B3058087
theorem B2717639 : Blo 1811607 2717639 := bstep (se 1 (by rfl) ⟨2038229, by rfl⟩ : syracuseStep 2717639 = 4076459) B4076459
theorem B6117335 : Blo 1811607 6117335 := bstep (se 1 (by rfl) ⟨4588001, by rfl⟩ : syracuseStep 6117335 = 9176003) B9176003
theorem B20920301 : Blo 1811607 20920301 := bstep (se 3 (by rfl) ⟨3922556, by rfl⟩ : syracuseStep 20920301 = 7845113) B7845113
theorem B148813861 : Blo 1811607 148813861 := bstep (se 4 (by rfl) ⟨13951299, by rfl⟩ : syracuseStep 148813861 = 27902599) B27902599
theorem B4077665 : Blo 1811607 4077665 := bstep (se 2 (by rfl) ⟨1529124, by rfl⟩ : syracuseStep 4077665 = 3058249) B3058249
theorem B13768865 : Blo 1811607 13768865 := bstep (se 2 (by rfl) ⟨5163324, by rfl⟩ : syracuseStep 13768865 = 10326649) B10326649
theorem B2717993 : Blo 1811607 2717993 := bstep (se 2 (by rfl) ⟨1019247, by rfl⟩ : syracuseStep 2717993 = 2038495) B2038495
theorem B2038063 : Blo 1811607 2038063 := bstep (se 1 (by rfl) ⟨1528547, by rfl⟩ : syracuseStep 2038063 = 3057095) B3057095
theorem B2717999 : Blo 1811607 2717999 := bstep (se 1 (by rfl) ⟨2038499, by rfl⟩ : syracuseStep 2717999 = 4076999) B4076999
theorem B2177327 : Blo 1811607 2177327 := bstep (se 1 (by rfl) ⟨1632995, by rfl⟩ : syracuseStep 2177327 = 3265991) B3265991
theorem B6117821 : Blo 1811607 6117821 := bstep (se 3 (by rfl) ⟨1147091, by rfl⟩ : syracuseStep 6117821 = 2294183) B2294183
theorem B2718239 : Blo 1811607 2718239 := bstep (se 1 (by rfl) ⟨2038679, by rfl⟩ : syracuseStep 2718239 = 4077359) B4077359
theorem B20642363 : Blo 1811607 20642363 := bstep (se 1 (by rfl) ⟨15481772, by rfl⟩ : syracuseStep 20642363 = 30963545) B30963545
theorem B5159771 : Blo 1811607 5159771 := bstep (se 1 (by rfl) ⟨3869828, by rfl⟩ : syracuseStep 5159771 = 7739657) B7739657
theorem B2718623 : Blo 1811607 2718623 := bstep (se 1 (by rfl) ⟨2038967, by rfl⟩ : syracuseStep 2718623 = 4077935) B4077935
theorem B2718671 : Blo 1811607 2718671 := bstep (se 1 (by rfl) ⟨2039003, by rfl⟩ : syracuseStep 2718671 = 4078007) B4078007
theorem B7347181 : Blo 1811607 7347181 := bstep (se 3 (by rfl) ⟨1377596, by rfl⟩ : syracuseStep 7347181 = 2755193) B2755193
theorem B2718761 : Blo 1811607 2718761 := bstep (se 2 (by rfl) ⟨1019535, by rfl⟩ : syracuseStep 2718761 = 2039071) B2039071
theorem B2718767 : Blo 1811607 2718767 := bstep (se 1 (by rfl) ⟨2039075, by rfl⟩ : syracuseStep 2718767 = 4078151) B4078151
theorem B2038855 : Blo 1811607 2038855 := bstep (se 1 (by rfl) ⟨1529141, by rfl⟩ : syracuseStep 2038855 = 3058283) B3058283
theorem B2718791 : Blo 1811607 2718791 := bstep (se 1 (by rfl) ⟨2039093, by rfl⟩ : syracuseStep 2718791 = 4078187) B4078187
theorem B6536321 : Blo 1811607 6536321 := bstep (se 2 (by rfl) ⟨2451120, by rfl⟩ : syracuseStep 6536321 = 4902241) B4902241
theorem B13065401 : Blo 1811607 13065401 := bstep (se 2 (by rfl) ⟨4899525, by rfl⟩ : syracuseStep 13065401 = 9799051) B9799051
theorem B76487897 : Blo 1811607 76487897 := bstep (se 2 (by rfl) ⟨28682961, by rfl⟩ : syracuseStep 76487897 = 57365923) B57365923
theorem B14703869 : Blo 1811607 14703869 := bstep (se 3 (by rfl) ⟨2756975, by rfl⟩ : syracuseStep 14703869 = 5513951) B5513951
theorem B6118685 : Blo 1811607 6118685 := bstep (se 3 (by rfl) ⟨1147253, by rfl⟩ : syracuseStep 6118685 = 2294507) B2294507
theorem B2719055 : Blo 1811607 2719055 := bstep (se 1 (by rfl) ⟨2039291, by rfl⟩ : syracuseStep 2719055 = 4078583) B4078583
theorem B44113247 : Blo 1811607 44113247 := bstep (se 1 (by rfl) ⟨33084935, by rfl⟩ : syracuseStep 44113247 = 66169871) B66169871
theorem B4079015 : Blo 1811607 4079015 := bstep (se 1 (by rfl) ⟨3059261, by rfl⟩ : syracuseStep 4079015 = 6118523) B6118523
theorem B2719145 : Blo 1811607 2719145 := bstep (se 2 (by rfl) ⟨1019679, by rfl⟩ : syracuseStep 2719145 = 2039359) B2039359
theorem B3440083 : Blo 1811607 3440083 := bstep (se 1 (by rfl) ⟨2580062, by rfl⟩ : syracuseStep 3440083 = 5160125) B5160125
theorem B22052341 : Blo 1811607 22052341 := bstep (se 5 (by rfl) ⟨1033703, by rfl⟩ : syracuseStep 22052341 = 2067407) B2067407
theorem B5160455 : Blo 1811607 5160455 := bstep (se 1 (by rfl) ⟨3870341, by rfl⟩ : syracuseStep 5160455 = 7740683) B7740683
theorem B2719295 : Blo 1811607 2719295 := bstep (se 1 (by rfl) ⟨2039471, by rfl⟩ : syracuseStep 2719295 = 4078943) B4078943
theorem B4079195 : Blo 1811607 4079195 := bstep (se 1 (by rfl) ⟨3059396, by rfl⟩ : syracuseStep 4079195 = 6118793) B6118793
theorem B4587151 : Blo 1811607 4587151 := bstep (se 1 (by rfl) ⟨3440363, by rfl⟩ : syracuseStep 4587151 = 6880727) B6880727
theorem B6979259 : Blo 1811607 6979259 := bstep (se 1 (by rfl) ⟨5234444, by rfl⟩ : syracuseStep 6979259 = 10468889) B10468889
theorem B2481959 : Blo 1811607 2481959 := bstep (se 1 (by rfl) ⟨1861469, by rfl⟩ : syracuseStep 2481959 = 3722939) B3722939
theorem B2719559 : Blo 1811607 2719559 := bstep (se 1 (by rfl) ⟨2039669, by rfl⟩ : syracuseStep 2719559 = 4079339) B4079339
theorem B4079483 : Blo 1811607 4079483 := bstep (se 1 (by rfl) ⟨3059612, by rfl⟩ : syracuseStep 4079483 = 6119225) B6119225
theorem B2719643 : Blo 1811607 2719643 := bstep (se 1 (by rfl) ⟨2039732, by rfl⟩ : syracuseStep 2719643 = 4079465) B4079465
theorem B198418481 : Blo 1811607 198418481 := bstep (se 2 (by rfl) ⟨74406930, by rfl⟩ : syracuseStep 198418481 = 148813861) B148813861
theorem B193437875 : Blo 1811607 193437875 := bstep (se 1 (by rfl) ⟨145078406, by rfl⟩ : syracuseStep 193437875 = 290156813) B290156813
theorem B4079807 : Blo 1811607 4079807 := bstep (se 1 (by rfl) ⟨3059855, by rfl⟩ : syracuseStep 4079807 = 6119711) B6119711
theorem B2719979 : Blo 1811607 2719979 := bstep (se 1 (by rfl) ⟨2039984, by rfl⟩ : syracuseStep 2719979 = 4079969) B4079969
theorem B2720039 : Blo 1811607 2720039 := bstep (se 1 (by rfl) ⟨2040029, by rfl⟩ : syracuseStep 2720039 = 4080059) B4080059
theorem B24797497 : Blo 1811607 24797497 := bstep (se 2 (by rfl) ⟨9299061, by rfl⟩ : syracuseStep 24797497 = 18598123) B18598123
theorem B6619727 : Blo 1811607 6619727 := bstep (se 1 (by rfl) ⟨4964795, by rfl⟩ : syracuseStep 6619727 = 9929591) B9929591
theorem B4080239 : Blo 1811607 4080239 := bstep (se 1 (by rfl) ⟨3060179, by rfl⟩ : syracuseStep 4080239 = 6120359) B6120359
theorem B9069185 : Blo 1811607 9069185 := bstep (se 2 (by rfl) ⟨3400944, by rfl⟩ : syracuseStep 9069185 = 6801889) B6801889
theorem B6120143 : Blo 1811607 6120143 := bstep (se 1 (by rfl) ⟨4590107, by rfl⟩ : syracuseStep 6120143 = 9180215) B9180215
theorem B7742375 : Blo 1811607 7742375 := bstep (se 1 (by rfl) ⟨5806781, by rfl⟩ : syracuseStep 7742375 = 11613563) B11613563
theorem B5162039 : Blo 1811607 5162039 := bstep (se 1 (by rfl) ⟨3871529, by rfl⟩ : syracuseStep 5162039 = 7743059) B7743059
theorem B6882367 : Blo 1811607 6882367 := bstep (se 1 (by rfl) ⟨5161775, by rfl⟩ : syracuseStep 6882367 = 10323551) B10323551
theorem B6120521 : Blo 1811607 6120521 := bstep (se 2 (by rfl) ⟨2295195, by rfl⟩ : syracuseStep 6120521 = 4590391) B4590391
theorem B1811623 : Blo 1811607 1811623 := bstep (se 1 (by rfl) ⟨1358717, by rfl⟩ : syracuseStep 1811623 = 2717435) B2717435
theorem B1811647 : Blo 1811607 1811647 := bstep (se 1 (by rfl) ⟨1358735, by rfl⟩ : syracuseStep 1811647 = 2717471) B2717471
theorem B1323967693 : Blo 1811607 1323967693 := bstep (se 3 (by rfl) ⟨248243942, by rfl⟩ : syracuseStep 1323967693 = 496487885) B496487885
theorem B1811679 : Blo 1811607 1811679 := bstep (se 1 (by rfl) ⟨1358759, by rfl⟩ : syracuseStep 1811679 = 2717519) B2717519
theorem B1811759 : Blo 1811607 1811759 := bstep (se 1 (by rfl) ⟨1358819, by rfl⟩ : syracuseStep 1811759 = 2717639) B2717639
theorem B3442171 : Blo 1811607 3442171 := bstep (se 1 (by rfl) ⟨2581628, by rfl⟩ : syracuseStep 3442171 = 5163257) B5163257
theorem B1811995 : Blo 1811607 1811995 := bstep (se 1 (by rfl) ⟨1358996, by rfl⟩ : syracuseStep 1811995 = 2717993) B2717993
theorem B1811999 : Blo 1811607 1811999 := bstep (se 1 (by rfl) ⟨1358999, by rfl⟩ : syracuseStep 1811999 = 2717999) B2717999
theorem B1812159 : Blo 1811607 1812159 := bstep (se 1 (by rfl) ⟨1359119, by rfl⟩ : syracuseStep 1812159 = 2718239) B2718239
theorem B9176975 : Blo 1811607 9176975 := bstep (se 1 (by rfl) ⟨6882731, by rfl⟩ : syracuseStep 9176975 = 13765463) B13765463
theorem B1812415 : Blo 1811607 1812415 := bstep (se 1 (by rfl) ⟨1359311, by rfl⟩ : syracuseStep 1812415 = 2718623) B2718623
theorem B1812447 : Blo 1811607 1812447 := bstep (se 1 (by rfl) ⟨1359335, by rfl⟩ : syracuseStep 1812447 = 2718671) B2718671
theorem B29403121 : Blo 1811607 29403121 := bstep (se 2 (by rfl) ⟨11026170, by rfl⟩ : syracuseStep 29403121 = 22052341) B22052341
theorem B1812507 : Blo 1811607 1812507 := bstep (se 1 (by rfl) ⟨1359380, by rfl⟩ : syracuseStep 1812507 = 2718761) B2718761
theorem B1812511 : Blo 1811607 1812511 := bstep (se 1 (by rfl) ⟨1359383, by rfl⟩ : syracuseStep 1812511 = 2718767) B2718767
theorem B1812527 : Blo 1811607 1812527 := bstep (se 1 (by rfl) ⟨1359395, by rfl⟩ : syracuseStep 1812527 = 2718791) B2718791
theorem B8710267 : Blo 1811607 8710267 := bstep (se 1 (by rfl) ⟨6532700, by rfl⟩ : syracuseStep 8710267 = 13065401) B13065401
theorem B26863741 : Blo 1811607 26863741 := bstep (se 3 (by rfl) ⟨5036951, by rfl⟩ : syracuseStep 26863741 = 10073903) B10073903
theorem B14698705 : Blo 1811607 14698705 := bstep (se 2 (by rfl) ⟨5512014, by rfl⟩ : syracuseStep 14698705 = 11024029) B11024029
theorem B1812703 : Blo 1811607 1812703 := bstep (se 1 (by rfl) ⟨1359527, by rfl⟩ : syracuseStep 1812703 = 2719055) B2719055
theorem B1812763 : Blo 1811607 1812763 := bstep (se 1 (by rfl) ⟨1359572, by rfl⟩ : syracuseStep 1812763 = 2719145) B2719145
theorem B211978529 : Blo 1811607 211978529 := bstep (se 2 (by rfl) ⟨79491948, by rfl⟩ : syracuseStep 211978529 = 158983897) B158983897
theorem B5163371 : Blo 1811607 5163371 := bstep (se 1 (by rfl) ⟨3872528, by rfl⟩ : syracuseStep 5163371 = 7745057) B7745057
theorem B1935743 : Blo 1811607 1935743 := bstep (se 1 (by rfl) ⟨1451807, by rfl⟩ : syracuseStep 1935743 = 2903615) B2903615
theorem B1812863 : Blo 1811607 1812863 := bstep (se 1 (by rfl) ⟨1359647, by rfl⟩ : syracuseStep 1812863 = 2719295) B2719295
theorem B8710537 : Blo 1811607 8710537 := bstep (se 2 (by rfl) ⟨3266451, by rfl⟩ : syracuseStep 8710537 = 6532903) B6532903
theorem B1813039 : Blo 1811607 1813039 := bstep (se 1 (by rfl) ⟨1359779, by rfl⟩ : syracuseStep 1813039 = 2719559) B2719559
theorem B1813095 : Blo 1811607 1813095 := bstep (se 1 (by rfl) ⟨1359821, by rfl⟩ : syracuseStep 1813095 = 2719643) B2719643
theorem B6884297 : Blo 1811607 6884297 := bstep (se 2 (by rfl) ⟨2581611, by rfl⟩ : syracuseStep 6884297 = 5163223) B5163223
theorem B1813471 : Blo 1811607 1813471 := bstep (se 1 (by rfl) ⟨1360103, by rfl⟩ : syracuseStep 1813471 = 2720207) B2720207
theorem B1813499 : Blo 1811607 1813499 := bstep (se 1 (by rfl) ⟨1360124, by rfl⟩ : syracuseStep 1813499 = 2720249) B2720249
theorem B1813567 : Blo 1811607 1813567 := bstep (se 1 (by rfl) ⟨1360175, by rfl⟩ : syracuseStep 1813567 = 2720351) B2720351
theorem B4353193 : Blo 1811607 4353193 := bstep (se 2 (by rfl) ⟨1632447, by rfl⟩ : syracuseStep 4353193 = 3264895) B3264895
theorem B3059167 : Blo 1811607 3059167 := bstep (se 1 (by rfl) ⟨2294375, by rfl⟩ : syracuseStep 3059167 = 4588751) B4588751
theorem B6975067 : Blo 1811607 6975067 := bstep (se 1 (by rfl) ⟨5231300, by rfl⟩ : syracuseStep 6975067 = 10462601) B10462601
theorem B7745159 : Blo 1811607 7745159 := bstep (se 1 (by rfl) ⟨5808869, by rfl⟩ : syracuseStep 7745159 = 11617739) B11617739
theorem B3059383 : Blo 1811607 3059383 := bstep (se 1 (by rfl) ⟨2294537, by rfl⟩ : syracuseStep 3059383 = 4589075) B4589075
theorem B20639447 : Blo 1811607 20639447 := bstep (se 1 (by rfl) ⟨15479585, by rfl⟩ : syracuseStep 20639447 = 30959171) B30959171
theorem B13946867 : Blo 1811607 13946867 := bstep (se 1 (by rfl) ⟨10460150, by rfl⟩ : syracuseStep 13946867 = 20920301) B20920301
theorem B9179243 : Blo 1811607 9179243 := bstep (se 1 (by rfl) ⟨6884432, by rfl⟩ : syracuseStep 9179243 = 13768865) B13768865
theorem B13766921 : Blo 1811607 13766921 := bstep (se 2 (by rfl) ⟨5162595, by rfl⟩ : syracuseStep 13766921 = 10325191) B10325191
theorem B9179729 : Blo 1811607 9179729 := bstep (se 2 (by rfl) ⟨3442398, by rfl⟩ : syracuseStep 9179729 = 6884797) B6884797
theorem B4076297 : Blo 1811607 4076297 := bstep (se 2 (by rfl) ⟨1528611, by rfl⟩ : syracuseStep 4076297 = 3057223) B3057223
theorem B50991931 : Blo 1811607 50991931 := bstep (se 1 (by rfl) ⟨38243948, by rfl⟩ : syracuseStep 50991931 = 76487897) B76487897
theorem B4076351 : Blo 1811607 4076351 := bstep (se 1 (by rfl) ⟨3057263, by rfl⟩ : syracuseStep 4076351 = 6114527) B6114527
theorem B2831167 : Blo 1811607 2831167 := bstep (se 1 (by rfl) ⟨2123375, by rfl⟩ : syracuseStep 2831167 = 4246751) B4246751
theorem B9802579 : Blo 1811607 9802579 := bstep (se 1 (by rfl) ⟨7351934, by rfl⟩ : syracuseStep 9802579 = 14703869) B14703869
theorem B6116201 : Blo 1811607 6116201 := bstep (se 2 (by rfl) ⟨2293575, by rfl⟩ : syracuseStep 6116201 = 4587151) B4587151
theorem B4076495 : Blo 1811607 4076495 := bstep (se 1 (by rfl) ⟨3057371, by rfl⟩ : syracuseStep 4076495 = 6114743) B6114743
theorem B4076585 : Blo 1811607 4076585 := bstep (se 2 (by rfl) ⟨1528719, by rfl⟩ : syracuseStep 4076585 = 3057439) B3057439
theorem B56587571 : Blo 1811607 56587571 := bstep (se 1 (by rfl) ⟨42440678, by rfl⟩ : syracuseStep 56587571 = 84881357) B84881357
theorem B7738685 : Blo 1811607 7738685 := bstep (se 3 (by rfl) ⟨1451003, by rfl⟩ : syracuseStep 7738685 = 2902007) B2902007
theorem B4076873 : Blo 1811607 4076873 := bstep (se 2 (by rfl) ⟨1528827, by rfl⟩ : syracuseStep 4076873 = 3057655) B3057655
theorem B9172439 : Blo 1811607 9172439 := bstep (se 1 (by rfl) ⟨6879329, by rfl⟩ : syracuseStep 9172439 = 13758659) B13758659
theorem B2717417 : Blo 1811607 2717417 := bstep (se 2 (by rfl) ⟨1019031, by rfl⟩ : syracuseStep 2717417 = 2038063) B2038063
theorem B2717423 : Blo 1811607 2717423 := bstep (se 1 (by rfl) ⟨2038067, by rfl⟩ : syracuseStep 2717423 = 4076135) B4076135
theorem B37213975 : Blo 1811607 37213975 := bstep (se 1 (by rfl) ⟨27910481, by rfl⟩ : syracuseStep 37213975 = 55820963) B55820963
theorem B5806025 : Blo 1811607 5806025 := bstep (se 2 (by rfl) ⟨2177259, by rfl⟩ : syracuseStep 5806025 = 4354519) B4354519
theorem B7739383 : Blo 1811607 7739383 := bstep (se 1 (by rfl) ⟨5804537, by rfl⟩ : syracuseStep 7739383 = 11609075) B11609075
theorem B33077281 : Blo 1811607 33077281 := bstep (se 2 (by rfl) ⟨12403980, by rfl⟩ : syracuseStep 33077281 = 24807961) B24807961
theorem B5806205 : Blo 1811607 5806205 := bstep (se 3 (by rfl) ⟨1088663, by rfl⟩ : syracuseStep 5806205 = 2177327) B2177327
theorem B2717879 : Blo 1811607 2717879 := bstep (se 1 (by rfl) ⟨2038409, by rfl⟩ : syracuseStep 2717879 = 4076819) B4076819
theorem B2717927 : Blo 1811607 2717927 := bstep (se 1 (by rfl) ⟨2038445, by rfl⟩ : syracuseStep 2717927 = 4076891) B4076891
theorem B4077863 : Blo 1811607 4077863 := bstep (se 1 (by rfl) ⟨3058397, by rfl⟩ : syracuseStep 4077863 = 6116795) B6116795
theorem B5806475 : Blo 1811607 5806475 := bstep (se 1 (by rfl) ⟨4354856, by rfl⟩ : syracuseStep 5806475 = 8709713) B8709713
theorem B52287889 : Blo 1811607 52287889 := bstep (se 2 (by rfl) ⟨19607958, by rfl⟩ : syracuseStep 52287889 = 39215917) B39215917
theorem B8714803 : Blo 1811607 8714803 := bstep (se 1 (by rfl) ⟨6536102, by rfl⟩ : syracuseStep 8714803 = 13072205) B13072205
theorem B10328633 : Blo 1811607 10328633 := bstep (se 2 (by rfl) ⟨3873237, by rfl⟩ : syracuseStep 10328633 = 7746475) B7746475
theorem B2718299 : Blo 1811607 2718299 := bstep (se 1 (by rfl) ⟨2038724, by rfl⟩ : syracuseStep 2718299 = 4077449) B4077449
theorem B38230625 : Blo 1811607 38230625 := bstep (se 2 (by rfl) ⟨14336484, by rfl⟩ : syracuseStep 38230625 = 28672969) B28672969
theorem B4078223 : Blo 1811607 4078223 := bstep (se 1 (by rfl) ⟨3058667, by rfl⟩ : syracuseStep 4078223 = 6117335) B6117335
theorem B9796241 : Blo 1811607 9796241 := bstep (se 2 (by rfl) ⟨3673590, by rfl⟩ : syracuseStep 9796241 = 7347181) B7347181
theorem B4078313 : Blo 1811607 4078313 := bstep (se 2 (by rfl) ⟨1529367, by rfl⟩ : syracuseStep 4078313 = 3058735) B3058735
theorem B2718443 : Blo 1811607 2718443 := bstep (se 1 (by rfl) ⟨2038832, by rfl⟩ : syracuseStep 2718443 = 4077665) B4077665
theorem B2718473 : Blo 1811607 2718473 := bstep (se 2 (by rfl) ⟨1019427, by rfl⟩ : syracuseStep 2718473 = 2038855) B2038855
theorem B6118199 : Blo 1811607 6118199 := bstep (se 1 (by rfl) ⟨4588649, by rfl⟩ : syracuseStep 6118199 = 9177299) B9177299
theorem B2038639 : Blo 1811607 2038639 := bstep (se 1 (by rfl) ⟨1528979, by rfl⟩ : syracuseStep 2038639 = 3057959) B3057959
theorem B4078547 : Blo 1811607 4078547 := bstep (se 1 (by rfl) ⟨3058910, by rfl⟩ : syracuseStep 4078547 = 6117821) B6117821
theorem B13761575 : Blo 1811607 13761575 := bstep (se 1 (by rfl) ⟨10321181, by rfl⟩ : syracuseStep 13761575 = 20642363) B20642363
theorem B4078817 : Blo 1811607 4078817 := bstep (se 2 (by rfl) ⟨1529556, by rfl⟩ : syracuseStep 4078817 = 3059113) B3059113
theorem B3439847 : Blo 1811607 3439847 := bstep (se 1 (by rfl) ⟨2579885, by rfl⟩ : syracuseStep 3439847 = 5159771) B5159771
theorem B17898745 : Blo 1811607 17898745 := bstep (se 2 (by rfl) ⟨6712029, by rfl⟩ : syracuseStep 17898745 = 13424059) B13424059
theorem B4586777 : Blo 1811607 4586777 := bstep (se 2 (by rfl) ⟨1720041, by rfl⟩ : syracuseStep 4586777 = 3440083) B3440083
theorem B15490385 : Blo 1811607 15490385 := bstep (se 2 (by rfl) ⟨5808894, by rfl⟩ : syracuseStep 15490385 = 11617789) B11617789
theorem B4357547 : Blo 1811607 4357547 := bstep (se 1 (by rfl) ⟨3268160, by rfl⟩ : syracuseStep 4357547 = 6536321) B6536321
theorem B6618557 : Blo 1811607 6618557 := bstep (se 3 (by rfl) ⟨1240979, by rfl⟩ : syracuseStep 6618557 = 2481959) B2481959
theorem B4079123 : Blo 1811607 4079123 := bstep (se 1 (by rfl) ⟨3059342, by rfl⟩ : syracuseStep 4079123 = 6118685) B6118685
theorem B29408831 : Blo 1811607 29408831 := bstep (se 1 (by rfl) ⟨22056623, by rfl⟩ : syracuseStep 29408831 = 44113247) B44113247
theorem B2719343 : Blo 1811607 2719343 := bstep (se 1 (by rfl) ⟨2039507, by rfl⟩ : syracuseStep 2719343 = 4079015) B4079015
theorem B3440303 : Blo 1811607 3440303 := bstep (se 1 (by rfl) ⟨2580227, by rfl⟩ : syracuseStep 3440303 = 5160455) B5160455
theorem B2719463 : Blo 1811607 2719463 := bstep (se 1 (by rfl) ⟨2039597, by rfl⟩ : syracuseStep 2719463 = 4079195) B4079195
theorem B4652839 : Blo 1811607 4652839 := bstep (se 1 (by rfl) ⟨3489629, by rfl⟩ : syracuseStep 4652839 = 6979259) B6979259
theorem B6119279 : Blo 1811607 6119279 := bstep (se 1 (by rfl) ⟨4589459, by rfl⟩ : syracuseStep 6119279 = 9178919) B9178919
theorem B2039719 : Blo 1811607 2039719 := bstep (se 1 (by rfl) ⟨1529789, by rfl⟩ : syracuseStep 2039719 = 3059579) B3059579
theorem B2719655 : Blo 1811607 2719655 := bstep (se 1 (by rfl) ⟨2039741, by rfl⟩ : syracuseStep 2719655 = 4079483) B4079483
theorem B6119495 : Blo 1811607 6119495 := bstep (se 1 (by rfl) ⟨4589621, by rfl⟩ : syracuseStep 6119495 = 9179243) B9179243
theorem B128958583 : Blo 1811607 128958583 := bstep (se 1 (by rfl) ⟨96718937, by rfl⟩ : syracuseStep 128958583 = 193437875) B193437875
theorem B2719871 : Blo 1811607 2719871 := bstep (se 1 (by rfl) ⟨2039903, by rfl⟩ : syracuseStep 2719871 = 4079807) B4079807
theorem B6119819 : Blo 1811607 6119819 := bstep (se 1 (by rfl) ⟨4589864, by rfl⟩ : syracuseStep 6119819 = 9179729) B9179729
theorem B2720159 : Blo 1811607 2720159 := bstep (se 1 (by rfl) ⟨2040119, by rfl⟩ : syracuseStep 2720159 = 4080239) B4080239
theorem B33063329 : Blo 1811607 33063329 := bstep (se 2 (by rfl) ⟨12398748, by rfl⟩ : syracuseStep 33063329 = 24797497) B24797497
theorem B6046123 : Blo 1811607 6046123 := bstep (se 1 (by rfl) ⟨4534592, by rfl⟩ : syracuseStep 6046123 = 9069185) B9069185
theorem B4080095 : Blo 1811607 4080095 := bstep (se 1 (by rfl) ⟨3060071, by rfl⟩ : syracuseStep 4080095 = 6120143) B6120143
theorem B5161583 : Blo 1811607 5161583 := bstep (se 1 (by rfl) ⟨3871187, by rfl⟩ : syracuseStep 5161583 = 7742375) B7742375
theorem B3441359 : Blo 1811607 3441359 := bstep (se 1 (by rfl) ⟨2581019, by rfl⟩ : syracuseStep 3441359 = 5162039) B5162039
theorem B4080347 : Blo 1811607 4080347 := bstep (se 1 (by rfl) ⟨3060260, by rfl⟩ : syracuseStep 4080347 = 6120521) B6120521
theorem B37725047 : Blo 1811607 37725047 := bstep (se 1 (by rfl) ⟨28293785, by rfl⟩ : syracuseStep 37725047 = 56587571) B56587571
theorem B5161981 : Blo 1811607 5161981 := bstep (se 3 (by rfl) ⟨967871, by rfl⟩ : syracuseStep 5161981 = 1935743) B1935743
theorem B1811611 : Blo 1811607 1811611 := bstep (se 1 (by rfl) ⟨1358708, by rfl⟩ : syracuseStep 1811611 = 2717417) B2717417
theorem B1811615 : Blo 1811607 1811615 := bstep (se 1 (by rfl) ⟨1358711, by rfl⟩ : syracuseStep 1811615 = 2717423) B2717423
theorem B9176489 : Blo 1811607 9176489 := bstep (se 2 (by rfl) ⟨3441183, by rfl⟩ : syracuseStep 9176489 = 6882367) B6882367
theorem B1811919 : Blo 1811607 1811919 := bstep (se 1 (by rfl) ⟨1358939, by rfl⟩ : syracuseStep 1811919 = 2717879) B2717879
theorem B1811951 : Blo 1811607 1811951 := bstep (se 1 (by rfl) ⟨1358963, by rfl⟩ : syracuseStep 1811951 = 2717927) B2717927
theorem B3442247 : Blo 1811607 3442247 := bstep (se 1 (by rfl) ⟨2581685, by rfl⟩ : syracuseStep 3442247 = 5163371) B5163371
theorem B23864993 : Blo 1811607 23864993 := bstep (se 2 (by rfl) ⟨8949372, by rfl⟩ : syracuseStep 23864993 = 17898745) B17898745
theorem B1812199 : Blo 1811607 1812199 := bstep (se 1 (by rfl) ⟨1359149, by rfl⟩ : syracuseStep 1812199 = 2718299) B2718299
theorem B25487083 : Blo 1811607 25487083 := bstep (se 1 (by rfl) ⟨19115312, by rfl⟩ : syracuseStep 25487083 = 38230625) B38230625
theorem B6530827 : Blo 1811607 6530827 := bstep (se 1 (by rfl) ⟨4898120, by rfl⟩ : syracuseStep 6530827 = 9796241) B9796241
theorem B1812295 : Blo 1811607 1812295 := bstep (se 1 (by rfl) ⟨1359221, by rfl⟩ : syracuseStep 1812295 = 2718443) B2718443
theorem B1812315 : Blo 1811607 1812315 := bstep (se 1 (by rfl) ⟨1359236, by rfl⟩ : syracuseStep 1812315 = 2718473) B2718473
theorem B4589531 : Blo 1811607 4589531 := bstep (se 1 (by rfl) ⟨3442148, by rfl⟩ : syracuseStep 4589531 = 6884297) B6884297
theorem B4589561 : Blo 1811607 4589561 := bstep (se 2 (by rfl) ⟨1721085, by rfl⟩ : syracuseStep 4589561 = 3442171) B3442171
theorem B9300089 : Blo 1811607 9300089 := bstep (se 2 (by rfl) ⟨3487533, by rfl⟩ : syracuseStep 9300089 = 6975067) B6975067
theorem B3057851 : Blo 1811607 3057851 := bstep (se 1 (by rfl) ⟨2293388, by rfl⟩ : syracuseStep 3057851 = 4586777) B4586777
theorem B19605887 : Blo 1811607 19605887 := bstep (se 1 (by rfl) ⟨14704415, by rfl⟩ : syracuseStep 19605887 = 29408831) B29408831
theorem B6203785 : Blo 1811607 6203785 := bstep (se 2 (by rfl) ⟨2326419, by rfl⟩ : syracuseStep 6203785 = 4652839) B4652839
theorem B1812895 : Blo 1811607 1812895 := bstep (se 1 (by rfl) ⟨1359671, by rfl⟩ : syracuseStep 1812895 = 2719343) B2719343
theorem B5163439 : Blo 1811607 5163439 := bstep (se 1 (by rfl) ⟨3872579, by rfl⟩ : syracuseStep 5163439 = 7745159) B7745159
theorem B1812975 : Blo 1811607 1812975 := bstep (se 1 (by rfl) ⟨1359731, by rfl⟩ : syracuseStep 1812975 = 2719463) B2719463
theorem B1813103 : Blo 1811607 1813103 := bstep (se 1 (by rfl) ⟨1359827, by rfl⟩ : syracuseStep 1813103 = 2719655) B2719655
theorem B132278987 : Blo 1811607 132278987 := bstep (se 1 (by rfl) ⟨99209240, by rfl⟩ : syracuseStep 132278987 = 198418481) B198418481
theorem B1813319 : Blo 1811607 1813319 := bstep (se 1 (by rfl) ⟨1359989, by rfl⟩ : syracuseStep 1813319 = 2719979) B2719979
theorem B35818321 : Blo 1811607 35818321 := bstep (se 2 (by rfl) ⟨13431870, by rfl⟩ : syracuseStep 35818321 = 26863741) B26863741
theorem B9177947 : Blo 1811607 9177947 := bstep (se 1 (by rfl) ⟨6883460, by rfl⟩ : syracuseStep 9177947 = 13766921) B13766921
theorem B1813359 : Blo 1811607 1813359 := bstep (se 1 (by rfl) ⟨1360019, by rfl⟩ : syracuseStep 1813359 = 2720039) B2720039
theorem B19598273 : Blo 1811607 19598273 := bstep (se 2 (by rfl) ⟨7349352, by rfl⟩ : syracuseStep 19598273 = 14698705) B14698705
theorem B69717185 : Blo 1811607 69717185 := bstep (se 2 (by rfl) ⟨26143944, by rfl⟩ : syracuseStep 69717185 = 52287889) B52287889
theorem B11619737 : Blo 1811607 11619737 := bstep (se 2 (by rfl) ⟨4357401, by rfl⟩ : syracuseStep 11619737 = 8714803) B8714803
theorem B6114959 : Blo 1811607 6114959 := bstep (se 1 (by rfl) ⟨4586219, by rfl⟩ : syracuseStep 6114959 = 9172439) B9172439
theorem B67989241 : Blo 1811607 67989241 := bstep (se 2 (by rfl) ⟨25495965, by rfl⟩ : syracuseStep 67989241 = 50991931) B50991931
theorem B13070105 : Blo 1811607 13070105 := bstep (se 2 (by rfl) ⟨4901289, by rfl⟩ : syracuseStep 13070105 = 9802579) B9802579
theorem B17649485 : Blo 1811607 17649485 := bstep (se 3 (by rfl) ⟨3309278, by rfl⟩ : syracuseStep 17649485 = 6618557) B6618557
theorem B3870683 : Blo 1811607 3870683 := bstep (se 1 (by rfl) ⟨2903012, by rfl⟩ : syracuseStep 3870683 = 5806025) B5806025
theorem B3870803 : Blo 1811607 3870803 := bstep (se 1 (by rfl) ⟨2903102, by rfl⟩ : syracuseStep 3870803 = 5806205) B5806205
theorem B5804257 : Blo 1811607 5804257 := bstep (se 2 (by rfl) ⟨2176596, by rfl⟩ : syracuseStep 5804257 = 4353193) B4353193
theorem B3870983 : Blo 1811607 3870983 := bstep (se 1 (by rfl) ⟨2903237, by rfl⟩ : syracuseStep 3870983 = 5806475) B5806475
theorem B1765290257 : Blo 1811607 1765290257 := bstep (se 2 (by rfl) ⟨661983846, by rfl⟩ : syracuseStep 1765290257 = 1323967693) B1323967693
theorem B6885755 : Blo 1811607 6885755 := bstep (se 1 (by rfl) ⟨5164316, by rfl⟩ : syracuseStep 6885755 = 10328633) B10328633
theorem B10326923 : Blo 1811607 10326923 := bstep (se 1 (by rfl) ⟨7745192, by rfl⟩ : syracuseStep 10326923 = 15490385) B15490385
theorem B2905031 : Blo 1811607 2905031 := bstep (se 1 (by rfl) ⟨2178773, by rfl⟩ : syracuseStep 2905031 = 4357547) B4357547
theorem B13759631 : Blo 1811607 13759631 := bstep (se 1 (by rfl) ⟨10319723, by rfl⟩ : syracuseStep 13759631 = 20639447) B20639447
theorem B39204161 : Blo 1811607 39204161 := bstep (se 2 (by rfl) ⟨14701560, by rfl⟩ : syracuseStep 39204161 = 29403121) B29403121
theorem B10319177 : Blo 1811607 10319177 := bstep (se 2 (by rfl) ⟨3869691, by rfl⟩ : syracuseStep 10319177 = 7739383) B7739383
theorem B44103041 : Blo 1811607 44103041 := bstep (se 2 (by rfl) ⟨16538640, by rfl⟩ : syracuseStep 44103041 = 33077281) B33077281
theorem B11613689 : Blo 1811607 11613689 := bstep (se 2 (by rfl) ⟨4355133, by rfl⟩ : syracuseStep 11613689 = 8710267) B8710267
theorem B4413151 : Blo 1811607 4413151 := bstep (se 1 (by rfl) ⟨3309863, by rfl⟩ : syracuseStep 4413151 = 6619727) B6619727
theorem B2717531 : Blo 1811607 2717531 := bstep (se 1 (by rfl) ⟨2038148, by rfl⟩ : syracuseStep 2717531 = 4076297) B4076297
theorem B11614049 : Blo 1811607 11614049 := bstep (se 2 (by rfl) ⟨4355268, by rfl⟩ : syracuseStep 11614049 = 8710537) B8710537
theorem B2717567 : Blo 1811607 2717567 := bstep (se 1 (by rfl) ⟨2038175, by rfl⟩ : syracuseStep 2717567 = 4076351) B4076351
theorem B4077467 : Blo 1811607 4077467 := bstep (se 1 (by rfl) ⟨3058100, by rfl⟩ : syracuseStep 4077467 = 6116201) B6116201
theorem B9172925 : Blo 1811607 9172925 := bstep (se 3 (by rfl) ⟨1719923, by rfl⟩ : syracuseStep 9172925 = 3439847) B3439847
theorem B2717663 : Blo 1811607 2717663 := bstep (se 1 (by rfl) ⟨2038247, by rfl⟩ : syracuseStep 2717663 = 4076495) B4076495
theorem B2717723 : Blo 1811607 2717723 := bstep (se 1 (by rfl) ⟨2038292, by rfl⟩ : syracuseStep 2717723 = 4076585) B4076585
theorem B5159123 : Blo 1811607 5159123 := bstep (se 1 (by rfl) ⟨3869342, by rfl⟩ : syracuseStep 5159123 = 7738685) B7738685
theorem B2717915 : Blo 1811607 2717915 := bstep (se 1 (by rfl) ⟨2038436, by rfl⟩ : syracuseStep 2717915 = 4076873) B4076873
theorem B3774889 : Blo 1811607 3774889 := bstep (se 2 (by rfl) ⟨1415583, by rfl⟩ : syracuseStep 3774889 = 2831167) B2831167
theorem B2718185 : Blo 1811607 2718185 := bstep (se 2 (by rfl) ⟨1019319, by rfl⟩ : syracuseStep 2718185 = 2038639) B2038639
theorem B6117983 : Blo 1811607 6117983 := bstep (se 1 (by rfl) ⟨4588487, by rfl⟩ : syracuseStep 6117983 = 9176975) B9176975
theorem B198474533 : Blo 1811607 198474533 := bstep (se 4 (by rfl) ⟨18606987, by rfl⟩ : syracuseStep 198474533 = 37213975) B37213975
theorem B141319019 : Blo 1811607 141319019 := bstep (se 1 (by rfl) ⟨105989264, by rfl⟩ : syracuseStep 141319019 = 211978529) B211978529
theorem B2718575 : Blo 1811607 2718575 := bstep (se 1 (by rfl) ⟨2038931, by rfl⟩ : syracuseStep 2718575 = 4077863) B4077863
theorem B2718815 : Blo 1811607 2718815 := bstep (se 1 (by rfl) ⟨2039111, by rfl⟩ : syracuseStep 2718815 = 4078223) B4078223
theorem B2718875 : Blo 1811607 2718875 := bstep (se 1 (by rfl) ⟨2039156, by rfl⟩ : syracuseStep 2718875 = 4078313) B4078313
theorem B4078799 : Blo 1811607 4078799 := bstep (se 1 (by rfl) ⟨3059099, by rfl⟩ : syracuseStep 4078799 = 6118199) B6118199
theorem B4078889 : Blo 1811607 4078889 := bstep (se 2 (by rfl) ⟨1529583, by rfl⟩ : syracuseStep 4078889 = 3059167) B3059167
theorem B2719031 : Blo 1811607 2719031 := bstep (se 1 (by rfl) ⟨2039273, by rfl⟩ : syracuseStep 2719031 = 4078547) B4078547
theorem B9174383 : Blo 1811607 9174383 := bstep (se 1 (by rfl) ⟨6880787, by rfl⟩ : syracuseStep 9174383 = 13761575) B13761575
theorem B2719211 : Blo 1811607 2719211 := bstep (se 1 (by rfl) ⟨2039408, by rfl⟩ : syracuseStep 2719211 = 4078817) B4078817
theorem B4079177 : Blo 1811607 4079177 := bstep (se 2 (by rfl) ⟨1529691, by rfl⟩ : syracuseStep 4079177 = 3059383) B3059383
theorem B2719415 : Blo 1811607 2719415 := bstep (se 1 (by rfl) ⟨2039561, by rfl⟩ : syracuseStep 2719415 = 4079123) B4079123
theorem B2293535 : Blo 1811607 2293535 := bstep (se 1 (by rfl) ⟨1720151, by rfl⟩ : syracuseStep 2293535 = 3440303) B3440303
theorem B2719625 : Blo 1811607 2719625 := bstep (se 2 (by rfl) ⟨1019859, by rfl⟩ : syracuseStep 2719625 = 2039719) B2039719
theorem B4079519 : Blo 1811607 4079519 := bstep (se 1 (by rfl) ⟨3059639, by rfl⟩ : syracuseStep 4079519 = 6119279) B6119279
theorem B9297911 : Blo 1811607 9297911 := bstep (se 1 (by rfl) ⟨6973433, by rfl⟩ : syracuseStep 9297911 = 13946867) B13946867
theorem B4079663 : Blo 1811607 4079663 := bstep (se 1 (by rfl) ⟨3059747, by rfl⟩ : syracuseStep 4079663 = 6119495) B6119495
theorem B2580535 : Blo 1811607 2580535 := bstep (se 1 (by rfl) ⟨1935401, by rfl⟩ : syracuseStep 2580535 = 3870803) B3870803
theorem B2580655 : Blo 1811607 2580655 := bstep (se 1 (by rfl) ⟨1935491, by rfl⟩ : syracuseStep 2580655 = 3870983) B3870983
theorem B4079879 : Blo 1811607 4079879 := bstep (se 1 (by rfl) ⟨3059909, by rfl⟩ : syracuseStep 4079879 = 6119819) B6119819
theorem B2720063 : Blo 1811607 2720063 := bstep (se 1 (by rfl) ⟨2040047, by rfl⟩ : syracuseStep 2720063 = 4080095) B4080095
theorem B3441055 : Blo 1811607 3441055 := bstep (se 1 (by rfl) ⟨2580791, by rfl⟩ : syracuseStep 3441055 = 5161583) B5161583
theorem B2294239 : Blo 1811607 2294239 := bstep (se 1 (by rfl) ⟨1720679, by rfl⟩ : syracuseStep 2294239 = 3441359) B3441359
theorem B2720231 : Blo 1811607 2720231 := bstep (se 1 (by rfl) ⟨2040173, by rfl⟩ : syracuseStep 2720231 = 4080347) B4080347
theorem B8061497 : Blo 1811607 8061497 := bstep (se 2 (by rfl) ⟨3023061, by rfl⟩ : syracuseStep 8061497 = 6046123) B6046123
theorem B25150031 : Blo 1811607 25150031 := bstep (se 1 (by rfl) ⟨18862523, by rfl⟩ : syracuseStep 25150031 = 37725047) B37725047
theorem B29402027 : Blo 1811607 29402027 := bstep (se 1 (by rfl) ⟨22051520, by rfl⟩ : syracuseStep 29402027 = 44103041) B44103041
theorem B7742459 : Blo 1811607 7742459 := bstep (se 1 (by rfl) ⟨5806844, by rfl⟩ : syracuseStep 7742459 = 11613689) B11613689
theorem B2294831 : Blo 1811607 2294831 := bstep (se 1 (by rfl) ⟨1721123, by rfl⟩ : syracuseStep 2294831 = 3442247) B3442247
theorem B15909995 : Blo 1811607 15909995 := bstep (se 1 (by rfl) ⟨11932496, by rfl⟩ : syracuseStep 15909995 = 23864993) B23864993
theorem B1811687 : Blo 1811607 1811687 := bstep (se 1 (by rfl) ⟨1358765, by rfl⟩ : syracuseStep 1811687 = 2717531) B2717531
theorem B7742699 : Blo 1811607 7742699 := bstep (se 1 (by rfl) ⟨5807024, by rfl⟩ : syracuseStep 7742699 = 11614049) B11614049
theorem B1811711 : Blo 1811607 1811711 := bstep (se 1 (by rfl) ⟨1358783, by rfl⟩ : syracuseStep 1811711 = 2717567) B2717567
theorem B1811775 : Blo 1811607 1811775 := bstep (se 1 (by rfl) ⟨1358831, by rfl⟩ : syracuseStep 1811775 = 2717663) B2717663
theorem B6882641 : Blo 1811607 6882641 := bstep (se 2 (by rfl) ⟨2580990, by rfl⟩ : syracuseStep 6882641 = 5161981) B5161981
theorem B1811815 : Blo 1811607 1811815 := bstep (se 1 (by rfl) ⟨1358861, by rfl⟩ : syracuseStep 1811815 = 2717723) B2717723
theorem B1811943 : Blo 1811607 1811943 := bstep (se 1 (by rfl) ⟨1358957, by rfl⟩ : syracuseStep 1811943 = 2717915) B2717915
theorem B1812123 : Blo 1811607 1812123 := bstep (se 1 (by rfl) ⟨1359092, by rfl⟩ : syracuseStep 1812123 = 2718185) B2718185
theorem B1812383 : Blo 1811607 1812383 := bstep (se 1 (by rfl) ⟨1359287, by rfl⟩ : syracuseStep 1812383 = 2718575) B2718575
theorem B1812543 : Blo 1811607 1812543 := bstep (se 1 (by rfl) ⟨1359407, by rfl⟩ : syracuseStep 1812543 = 2718815) B2718815
theorem B1812583 : Blo 1811607 1812583 := bstep (se 1 (by rfl) ⟨1359437, by rfl⟩ : syracuseStep 1812583 = 2718875) B2718875
theorem B1812687 : Blo 1811607 1812687 := bstep (se 1 (by rfl) ⟨1359515, by rfl⟩ : syracuseStep 1812687 = 2719031) B2719031
theorem B5884201 : Blo 1811607 5884201 := bstep (se 2 (by rfl) ⟨2206575, by rfl⟩ : syracuseStep 5884201 = 4413151) B4413151
theorem B33982777 : Blo 1811607 33982777 := bstep (se 2 (by rfl) ⟨12743541, by rfl⟩ : syracuseStep 33982777 = 25487083) B25487083
theorem B1812807 : Blo 1811607 1812807 := bstep (se 1 (by rfl) ⟨1359605, by rfl⟩ : syracuseStep 1812807 = 2719211) B2719211
theorem B1812943 : Blo 1811607 1812943 := bstep (se 1 (by rfl) ⟨1359707, by rfl⟩ : syracuseStep 1812943 = 2719415) B2719415
theorem B11766323 : Blo 1811607 11766323 := bstep (se 1 (by rfl) ⟨8824742, by rfl⟩ : syracuseStep 11766323 = 17649485) B17649485
theorem B1813083 : Blo 1811607 1813083 := bstep (se 1 (by rfl) ⟨1359812, by rfl⟩ : syracuseStep 1813083 = 2719625) B2719625
theorem B1813247 : Blo 1811607 1813247 := bstep (se 1 (by rfl) ⟨1359935, by rfl⟩ : syracuseStep 1813247 = 2719871) B2719871
theorem B171944777 : Blo 1811607 171944777 := bstep (se 2 (by rfl) ⟨64479291, by rfl⟩ : syracuseStep 171944777 = 128958583) B128958583
theorem B4590503 : Blo 1811607 4590503 := bstep (se 1 (by rfl) ⟨3442877, by rfl⟩ : syracuseStep 4590503 = 6885755) B6885755
theorem B1813439 : Blo 1811607 1813439 := bstep (se 1 (by rfl) ⟨1360079, by rfl⟩ : syracuseStep 1813439 = 2720159) B2720159
theorem B5033185 : Blo 1811607 5033185 := bstep (se 2 (by rfl) ⟨1887444, by rfl⟩ : syracuseStep 5033185 = 3774889) B3774889
theorem B6884585 : Blo 1811607 6884585 := bstep (se 2 (by rfl) ⟨2581719, by rfl⟩ : syracuseStep 6884585 = 5163439) B5163439
theorem B6884615 : Blo 1811607 6884615 := bstep (se 1 (by rfl) ⟨5163461, by rfl⟩ : syracuseStep 6884615 = 10326923) B10326923
theorem B26136107 : Blo 1811607 26136107 := bstep (se 1 (by rfl) ⟨19602080, by rfl⟩ : syracuseStep 26136107 = 39204161) B39204161
theorem B6115283 : Blo 1811607 6115283 := bstep (se 1 (by rfl) ⟨4586462, by rfl⟩ : syracuseStep 6115283 = 9172925) B9172925
theorem B3059687 : Blo 1811607 3059687 := bstep (se 1 (by rfl) ⟨2294765, by rfl⟩ : syracuseStep 3059687 = 4589531) B4589531
theorem B3059707 : Blo 1811607 3059707 := bstep (se 1 (by rfl) ⟨2294780, by rfl⟩ : syracuseStep 3059707 = 4589561) B4589561
theorem B13070591 : Blo 1811607 13070591 := bstep (se 1 (by rfl) ⟨9802943, by rfl⟩ : syracuseStep 13070591 = 19605887) B19605887
theorem B94212679 : Blo 1811607 94212679 := bstep (se 1 (by rfl) ⟨70659509, by rfl⟩ : syracuseStep 94212679 = 141319019) B141319019
theorem B6116093 : Blo 1811607 6116093 := bstep (se 3 (by rfl) ⟨1146767, by rfl⟩ : syracuseStep 6116093 = 2293535) B2293535
theorem B46478123 : Blo 1811607 46478123 := bstep (se 1 (by rfl) ⟨34858592, by rfl⟩ : syracuseStep 46478123 = 69717185) B69717185
theorem B6116255 : Blo 1811607 6116255 := bstep (se 1 (by rfl) ⟨4587191, by rfl⟩ : syracuseStep 6116255 = 9174383) B9174383
theorem B7746491 : Blo 1811607 7746491 := bstep (se 1 (by rfl) ⟨5809868, by rfl⟩ : syracuseStep 7746491 = 11619737) B11619737
theorem B4076639 : Blo 1811607 4076639 := bstep (se 1 (by rfl) ⟨3057479, by rfl⟩ : syracuseStep 4076639 = 6114959) B6114959
theorem B8713403 : Blo 1811607 8713403 := bstep (se 1 (by rfl) ⟨6535052, by rfl⟩ : syracuseStep 8713403 = 13070105) B13070105
theorem B7746749 : Blo 1811607 7746749 := bstep (se 3 (by rfl) ⟨1452515, by rfl⟩ : syracuseStep 7746749 = 2905031) B2905031
theorem B24794429 : Blo 1811607 24794429 := bstep (se 3 (by rfl) ⟨4648955, by rfl⟩ : syracuseStep 24794429 = 9297911) B9297911
theorem B1176860171 : Blo 1811607 1176860171 := bstep (se 1 (by rfl) ⟨882645128, by rfl⟩ : syracuseStep 1176860171 = 1765290257) B1765290257
theorem B22042219 : Blo 1811607 22042219 := bstep (se 1 (by rfl) ⟨16531664, by rfl⟩ : syracuseStep 22042219 = 33063329) B33063329
theorem B7739009 : Blo 1811607 7739009 := bstep (se 2 (by rfl) ⟨2902128, by rfl⟩ : syracuseStep 7739009 = 5804257) B5804257
theorem B8271713 : Blo 1811607 8271713 := bstep (se 2 (by rfl) ⟨3101892, by rfl⟩ : syracuseStep 8271713 = 6203785) B6203785
theorem B9173087 : Blo 1811607 9173087 := bstep (se 1 (by rfl) ⟨6879815, by rfl⟩ : syracuseStep 9173087 = 13759631) B13759631
theorem B6879451 : Blo 1811607 6879451 := bstep (se 1 (by rfl) ⟨5159588, by rfl⟩ : syracuseStep 6879451 = 10319177) B10319177
theorem B6117659 : Blo 1811607 6117659 := bstep (se 1 (by rfl) ⟨4588244, by rfl⟩ : syracuseStep 6117659 = 9176489) B9176489
theorem B47757761 : Blo 1811607 47757761 := bstep (se 2 (by rfl) ⟨17909160, by rfl⟩ : syracuseStep 47757761 = 35818321) B35818321
theorem B2718311 : Blo 1811607 2718311 := bstep (se 1 (by rfl) ⟨2038733, by rfl⟩ : syracuseStep 2718311 = 4077467) B4077467
theorem B6200059 : Blo 1811607 6200059 := bstep (se 1 (by rfl) ⟨4650044, by rfl⟩ : syracuseStep 6200059 = 9300089) B9300089
theorem B2038567 : Blo 1811607 2038567 := bstep (se 1 (by rfl) ⟨1528925, by rfl⟩ : syracuseStep 2038567 = 3057851) B3057851
theorem B3439415 : Blo 1811607 3439415 := bstep (se 1 (by rfl) ⟨2579561, by rfl⟩ : syracuseStep 3439415 = 5159123) B5159123
theorem B4078655 : Blo 1811607 4078655 := bstep (se 1 (by rfl) ⟨3058991, by rfl⟩ : syracuseStep 4078655 = 6117983) B6117983
theorem B88185991 : Blo 1811607 88185991 := bstep (se 1 (by rfl) ⟨66139493, by rfl⟩ : syracuseStep 88185991 = 132278987) B132278987
theorem B132316355 : Blo 1811607 132316355 := bstep (se 1 (by rfl) ⟨99237266, by rfl⟩ : syracuseStep 132316355 = 198474533) B198474533
theorem B6118631 : Blo 1811607 6118631 := bstep (se 1 (by rfl) ⟨4588973, by rfl⟩ : syracuseStep 6118631 = 9177947) B9177947
theorem B13065515 : Blo 1811607 13065515 := bstep (se 1 (by rfl) ⟨9799136, by rfl⟩ : syracuseStep 13065515 = 19598273) B19598273
theorem B2719199 : Blo 1811607 2719199 := bstep (se 1 (by rfl) ⟨2039399, by rfl⟩ : syracuseStep 2719199 = 4078799) B4078799
theorem B2719259 : Blo 1811607 2719259 := bstep (se 1 (by rfl) ⟨2039444, by rfl⟩ : syracuseStep 2719259 = 4078889) B4078889
theorem B90652321 : Blo 1811607 90652321 := bstep (se 2 (by rfl) ⟨33994620, by rfl⟩ : syracuseStep 90652321 = 67989241) B67989241
theorem B8707769 : Blo 1811607 8707769 := bstep (se 2 (by rfl) ⟨3265413, by rfl⟩ : syracuseStep 8707769 = 6530827) B6530827
theorem B2719451 : Blo 1811607 2719451 := bstep (se 1 (by rfl) ⟨2039588, by rfl⟩ : syracuseStep 2719451 = 4079177) B4079177
theorem B2719679 : Blo 1811607 2719679 := bstep (se 1 (by rfl) ⟨2039759, by rfl⟩ : syracuseStep 2719679 = 4079519) B4079519
theorem B2580455 : Blo 1811607 2580455 := bstep (se 1 (by rfl) ⟨1935341, by rfl⟩ : syracuseStep 2580455 = 3870683) B3870683
theorem B2719775 : Blo 1811607 2719775 := bstep (se 1 (by rfl) ⟨2039831, by rfl⟩ : syracuseStep 2719775 = 4079663) B4079663
theorem B3440713 : Blo 1811607 3440713 := bstep (se 2 (by rfl) ⟨1290267, by rfl⟩ : syracuseStep 3440713 = 2580535) B2580535
theorem B6119549 : Blo 1811607 6119549 := bstep (se 3 (by rfl) ⟨1147415, by rfl⟩ : syracuseStep 6119549 = 2294831) B2294831
theorem B2719919 : Blo 1811607 2719919 := bstep (se 1 (by rfl) ⟨2039939, by rfl⟩ : syracuseStep 2719919 = 4079879) B4079879
theorem B3440873 : Blo 1811607 3440873 := bstep (se 2 (by rfl) ⟨1290327, by rfl⟩ : syracuseStep 3440873 = 2580655) B2580655
theorem B5374331 : Blo 1811607 5374331 := bstep (se 1 (by rfl) ⟨4030748, by rfl⟩ : syracuseStep 5374331 = 8061497) B8061497
theorem B45310369 : Blo 1811607 45310369 := bstep (se 2 (by rfl) ⟨16991388, by rfl⟩ : syracuseStep 45310369 = 33982777) B33982777
theorem B4588073 : Blo 1811607 4588073 := bstep (se 2 (by rfl) ⟨1720527, by rfl⟩ : syracuseStep 4588073 = 3441055) B3441055
theorem B5161639 : Blo 1811607 5161639 := bstep (se 1 (by rfl) ⟨3871229, by rfl⟩ : syracuseStep 5161639 = 7742459) B7742459
theorem B125616905 : Blo 1811607 125616905 := bstep (se 2 (by rfl) ⟨47106339, by rfl⟩ : syracuseStep 125616905 = 94212679) B94212679
theorem B5808935 : Blo 1811607 5808935 := bstep (se 1 (by rfl) ⟨4356701, by rfl⟩ : syracuseStep 5808935 = 8713403) B8713403
theorem B5161799 : Blo 1811607 5161799 := bstep (se 1 (by rfl) ⟨3871349, by rfl⟩ : syracuseStep 5161799 = 7742699) B7742699
theorem B4588427 : Blo 1811607 4588427 := bstep (se 1 (by rfl) ⟨3441320, by rfl⟩ : syracuseStep 4588427 = 6882641) B6882641
theorem B8266745 : Blo 1811607 8266745 := bstep (se 2 (by rfl) ⟨3100029, by rfl⟩ : syracuseStep 8266745 = 6200059) B6200059
theorem B784573447 : Blo 1811607 784573447 := bstep (se 1 (by rfl) ⟨588430085, by rfl⟩ : syracuseStep 784573447 = 1176860171) B1176860171
theorem B5514475 : Blo 1811607 5514475 := bstep (se 1 (by rfl) ⟨4135856, by rfl⟩ : syracuseStep 5514475 = 8271713) B8271713
theorem B117581321 : Blo 1811607 117581321 := bstep (se 2 (by rfl) ⟨44092995, by rfl⟩ : syracuseStep 117581321 = 88185991) B88185991
theorem B1812207 : Blo 1811607 1812207 := bstep (se 1 (by rfl) ⟨1359155, by rfl⟩ : syracuseStep 1812207 = 2718311) B2718311
theorem B4589723 : Blo 1811607 4589723 := bstep (se 1 (by rfl) ⟨3442292, by rfl⟩ : syracuseStep 4589723 = 6884585) B6884585
theorem B4589743 : Blo 1811607 4589743 := bstep (se 1 (by rfl) ⟨3442307, by rfl⟩ : syracuseStep 4589743 = 6884615) B6884615
theorem B8710343 : Blo 1811607 8710343 := bstep (se 1 (by rfl) ⟨6532757, by rfl⟩ : syracuseStep 8710343 = 13065515) B13065515
theorem B1812799 : Blo 1811607 1812799 := bstep (se 1 (by rfl) ⟨1359599, by rfl⟩ : syracuseStep 1812799 = 2719199) B2719199
theorem B1812839 : Blo 1811607 1812839 := bstep (se 1 (by rfl) ⟨1359629, by rfl⟩ : syracuseStep 1812839 = 2719259) B2719259
theorem B1812967 : Blo 1811607 1812967 := bstep (se 1 (by rfl) ⟨1359725, by rfl⟩ : syracuseStep 1812967 = 2719451) B2719451
theorem B1813119 : Blo 1811607 1813119 := bstep (se 1 (by rfl) ⟨1359839, by rfl⟩ : syracuseStep 1813119 = 2719679) B2719679
theorem B1813375 : Blo 1811607 1813375 := bstep (se 1 (by rfl) ⟨1360031, by rfl⟩ : syracuseStep 1813375 = 2720063) B2720063
theorem B1813487 : Blo 1811607 1813487 := bstep (se 1 (by rfl) ⟨1360115, by rfl⟩ : syracuseStep 1813487 = 2720231) B2720231
theorem B30985415 : Blo 1811607 30985415 := bstep (se 1 (by rfl) ⟨23239061, by rfl⟩ : syracuseStep 30985415 = 46478123) B46478123
theorem B5164327 : Blo 1811607 5164327 := bstep (se 1 (by rfl) ⟨3873245, by rfl⟩ : syracuseStep 5164327 = 7746491) B7746491
theorem B3058985 : Blo 1811607 3058985 := bstep (se 2 (by rfl) ⟨1147119, by rfl⟩ : syracuseStep 3058985 = 2294239) B2294239
theorem B264473909 : Blo 1811607 264473909 := bstep (se 5 (by rfl) ⟨12397214, by rfl⟩ : syracuseStep 264473909 = 24794429) B24794429
theorem B5164499 : Blo 1811607 5164499 := bstep (se 1 (by rfl) ⟨3873374, by rfl⟩ : syracuseStep 5164499 = 7746749) B7746749
theorem B6115391 : Blo 1811607 6115391 := bstep (se 1 (by rfl) ⟨4586543, by rfl⟩ : syracuseStep 6115391 = 9173087) B9173087
theorem B31838507 : Blo 1811607 31838507 := bstep (se 1 (by rfl) ⟨23878880, by rfl⟩ : syracuseStep 31838507 = 47757761) B47757761
theorem B7844215 : Blo 1811607 7844215 := bstep (se 1 (by rfl) ⟨5883161, by rfl⟩ : syracuseStep 7844215 = 11766323) B11766323
theorem B4079609 : Blo 1811607 4079609 := bstep (se 2 (by rfl) ⟨1529853, by rfl⟩ : syracuseStep 4079609 = 3059707) B3059707
theorem B3060335 : Blo 1811607 3060335 := bstep (se 1 (by rfl) ⟨2295251, by rfl⟩ : syracuseStep 3060335 = 4590503) B4590503
theorem B29389625 : Blo 1811607 29389625 := bstep (se 2 (by rfl) ⟨11021109, by rfl⟩ : syracuseStep 29389625 = 22042219) B22042219
theorem B120869761 : Blo 1811607 120869761 := bstep (se 2 (by rfl) ⟨45326160, by rfl⟩ : syracuseStep 120869761 = 90652321) B90652321
theorem B5805179 : Blo 1811607 5805179 := bstep (se 1 (by rfl) ⟨4353884, by rfl⟩ : syracuseStep 5805179 = 8707769) B8707769
theorem B4076855 : Blo 1811607 4076855 := bstep (se 1 (by rfl) ⟨3057641, by rfl⟩ : syracuseStep 4076855 = 6115283) B6115283
theorem B8713727 : Blo 1811607 8713727 := bstep (se 1 (by rfl) ⟨6535295, by rfl⟩ : syracuseStep 8713727 = 13070591) B13070591
theorem B9172601 : Blo 1811607 9172601 := bstep (se 2 (by rfl) ⟨3439725, by rfl⟩ : syracuseStep 9172601 = 6879451) B6879451
theorem B16766687 : Blo 1811607 16766687 := bstep (se 1 (by rfl) ⟨12575015, by rfl⟩ : syracuseStep 16766687 = 25150031) B25150031
theorem B7845601 : Blo 1811607 7845601 := bstep (se 2 (by rfl) ⟨2942100, by rfl⟩ : syracuseStep 7845601 = 5884201) B5884201
theorem B4077395 : Blo 1811607 4077395 := bstep (se 1 (by rfl) ⟨3058046, by rfl⟩ : syracuseStep 4077395 = 6116093) B6116093
theorem B4077503 : Blo 1811607 4077503 := bstep (se 1 (by rfl) ⟨3058127, by rfl⟩ : syracuseStep 4077503 = 6116255) B6116255
theorem B19601351 : Blo 1811607 19601351 := bstep (se 1 (by rfl) ⟨14701013, by rfl⟩ : syracuseStep 19601351 = 29402027) B29402027
theorem B2717759 : Blo 1811607 2717759 := bstep (se 1 (by rfl) ⟨2038319, by rfl⟩ : syracuseStep 2717759 = 4076639) B4076639
theorem B10606663 : Blo 1811607 10606663 := bstep (se 1 (by rfl) ⟨7954997, by rfl⟩ : syracuseStep 10606663 = 15909995) B15909995
theorem B2718089 : Blo 1811607 2718089 := bstep (se 2 (by rfl) ⟨1019283, by rfl⟩ : syracuseStep 2718089 = 2038567) B2038567
theorem B5159339 : Blo 1811607 5159339 := bstep (se 1 (by rfl) ⟨3869504, by rfl⟩ : syracuseStep 5159339 = 7739009) B7739009
theorem B26843653 : Blo 1811607 26843653 := bstep (se 4 (by rfl) ⟨2516592, by rfl⟩ : syracuseStep 26843653 = 5033185) B5033185
theorem B4078439 : Blo 1811607 4078439 := bstep (se 1 (by rfl) ⟨3058829, by rfl⟩ : syracuseStep 4078439 = 6117659) B6117659
theorem B2292943 : Blo 1811607 2292943 := bstep (se 1 (by rfl) ⟨1719707, by rfl⟩ : syracuseStep 2292943 = 3439415) B3439415
theorem B114629851 : Blo 1811607 114629851 := bstep (se 1 (by rfl) ⟨85972388, by rfl⟩ : syracuseStep 114629851 = 171944777) B171944777
theorem B2719103 : Blo 1811607 2719103 := bstep (se 1 (by rfl) ⟨2039327, by rfl⟩ : syracuseStep 2719103 = 4078655) B4078655
theorem B88210903 : Blo 1811607 88210903 := bstep (se 1 (by rfl) ⟨66158177, by rfl⟩ : syracuseStep 88210903 = 132316355) B132316355
theorem B4079087 : Blo 1811607 4079087 := bstep (se 1 (by rfl) ⟨3059315, by rfl⟩ : syracuseStep 4079087 = 6118631) B6118631
theorem B17424071 : Blo 1811607 17424071 := bstep (se 1 (by rfl) ⟨13068053, by rfl⟩ : syracuseStep 17424071 = 26136107) B26136107
theorem B6881213 : Blo 1811607 6881213 := bstep (se 3 (by rfl) ⟨1290227, by rfl⟩ : syracuseStep 6881213 = 2580455) B2580455
theorem B2039791 : Blo 1811607 2039791 := bstep (se 1 (by rfl) ⟨1529843, by rfl⟩ : syracuseStep 2039791 = 3059687) B3059687
theorem B4079699 : Blo 1811607 4079699 := bstep (se 1 (by rfl) ⟨3059774, by rfl⟩ : syracuseStep 4079699 = 6119549) B6119549
theorem B4587617 : Blo 1811607 4587617 := bstep (se 2 (by rfl) ⟨1720356, by rfl⟩ : syracuseStep 4587617 = 3440713) B3440713
theorem B2293915 : Blo 1811607 2293915 := bstep (se 1 (by rfl) ⟨1720436, by rfl⟩ : syracuseStep 2293915 = 3440873) B3440873
theorem B21225671 : Blo 1811607 21225671 := bstep (se 1 (by rfl) ⟨15919253, by rfl⟩ : syracuseStep 21225671 = 31838507) B31838507
theorem B6119657 : Blo 1811607 6119657 := bstep (se 2 (by rfl) ⟨2294871, by rfl⟩ : syracuseStep 6119657 = 4589743) B4589743
theorem B2040223 : Blo 1811607 2040223 := bstep (se 1 (by rfl) ⟨1530167, by rfl⟩ : syracuseStep 2040223 = 3060335) B3060335
theorem B3441199 : Blo 1811607 3441199 := bstep (se 1 (by rfl) ⟨2580899, by rfl⟩ : syracuseStep 3441199 = 5161799) B5161799
theorem B35791537 : Blo 1811607 35791537 := bstep (se 2 (by rfl) ⟨13421826, by rfl⟩ : syracuseStep 35791537 = 26843653) B26843653
theorem B6882185 : Blo 1811607 6882185 := bstep (se 2 (by rfl) ⟨2580819, by rfl⟩ : syracuseStep 6882185 = 5161639) B5161639
theorem B5809151 : Blo 1811607 5809151 := bstep (se 1 (by rfl) ⟨4356863, by rfl⟩ : syracuseStep 5809151 = 8713727) B8713727
theorem B13067567 : Blo 1811607 13067567 := bstep (se 1 (by rfl) ⟨9800675, by rfl⟩ : syracuseStep 13067567 = 19601351) B19601351
theorem B1811839 : Blo 1811607 1811839 := bstep (se 1 (by rfl) ⟨1358879, by rfl⟩ : syracuseStep 1811839 = 2717759) B2717759
theorem B1812059 : Blo 1811607 1812059 := bstep (se 1 (by rfl) ⟨1359044, by rfl⟩ : syracuseStep 1812059 = 2718089) B2718089
theorem B3057257 : Blo 1811607 3057257 := bstep (se 2 (by rfl) ⟨1146471, by rfl⟩ : syracuseStep 3057257 = 2292943) B2292943
theorem B152839801 : Blo 1811607 152839801 := bstep (se 2 (by rfl) ⟨57314925, by rfl⟩ : syracuseStep 152839801 = 114629851) B114629851
theorem B117614537 : Blo 1811607 117614537 := bstep (se 2 (by rfl) ⟨44105451, by rfl⟩ : syracuseStep 117614537 = 88210903) B88210903
theorem B1812735 : Blo 1811607 1812735 := bstep (se 1 (by rfl) ⟨1359551, by rfl⟩ : syracuseStep 1812735 = 2719103) B2719103
theorem B3442999 : Blo 1811607 3442999 := bstep (se 1 (by rfl) ⟨2582249, by rfl⟩ : syracuseStep 3442999 = 5164499) B5164499
theorem B1813183 : Blo 1811607 1813183 := bstep (se 1 (by rfl) ⟨1359887, by rfl⟩ : syracuseStep 1813183 = 2719775) B2719775
theorem B14142217 : Blo 1811607 14142217 := bstep (se 2 (by rfl) ⟨5303331, by rfl⟩ : syracuseStep 14142217 = 10606663) B10606663
theorem B1813279 : Blo 1811607 1813279 := bstep (se 1 (by rfl) ⟨1359959, by rfl⟩ : syracuseStep 1813279 = 2719919) B2719919
theorem B3582887 : Blo 1811607 3582887 := bstep (se 1 (by rfl) ⟨2687165, by rfl⟩ : syracuseStep 3582887 = 5374331) B5374331
theorem B3058715 : Blo 1811607 3058715 := bstep (se 1 (by rfl) ⟨2294036, by rfl⟩ : syracuseStep 3058715 = 4588073) B4588073
theorem B3058951 : Blo 1811607 3058951 := bstep (se 1 (by rfl) ⟨2294213, by rfl⟩ : syracuseStep 3058951 = 4588427) B4588427
theorem B3870119 : Blo 1811607 3870119 := bstep (se 1 (by rfl) ⟨2902589, by rfl⟩ : syracuseStep 3870119 = 5805179) B5805179
theorem B6115067 : Blo 1811607 6115067 := bstep (se 1 (by rfl) ⟨4586300, by rfl⟩ : syracuseStep 6115067 = 9172601) B9172601
theorem B1046097929 : Blo 1811607 1046097929 := bstep (se 2 (by rfl) ⟨392286723, by rfl⟩ : syracuseStep 1046097929 = 784573447) B784573447
theorem B3059815 : Blo 1811607 3059815 := bstep (se 1 (by rfl) ⟨2294861, by rfl⟩ : syracuseStep 3059815 = 4589723) B4589723
theorem B7352633 : Blo 1811607 7352633 := bstep (se 2 (by rfl) ⟨2757237, by rfl⟩ : syracuseStep 7352633 = 5514475) B5514475
theorem B6885769 : Blo 1811607 6885769 := bstep (se 2 (by rfl) ⟨2582163, by rfl⟩ : syracuseStep 6885769 = 5164327) B5164327
theorem B20656943 : Blo 1811607 20656943 := bstep (se 1 (by rfl) ⟨15492707, by rfl⟩ : syracuseStep 20656943 = 30985415) B30985415
theorem B4076927 : Blo 1811607 4076927 := bstep (se 1 (by rfl) ⟨3057695, by rfl⟩ : syracuseStep 4076927 = 6115391) B6115391
theorem B10458953 : Blo 1811607 10458953 := bstep (se 2 (by rfl) ⟨3922107, by rfl⟩ : syracuseStep 10458953 = 7844215) B7844215
theorem B83744603 : Blo 1811607 83744603 := bstep (se 1 (by rfl) ⟨62808452, by rfl⟩ : syracuseStep 83744603 = 125616905) B125616905
theorem B3872623 : Blo 1811607 3872623 := bstep (se 1 (by rfl) ⟨2904467, by rfl⟩ : syracuseStep 3872623 = 5808935) B5808935
theorem B19593083 : Blo 1811607 19593083 := bstep (se 1 (by rfl) ⟨14694812, by rfl⟩ : syracuseStep 19593083 = 29389625) B29389625
theorem B60413825 : Blo 1811607 60413825 := bstep (se 2 (by rfl) ⟨22655184, by rfl⟩ : syracuseStep 60413825 = 45310369) B45310369
theorem B2717903 : Blo 1811607 2717903 := bstep (se 1 (by rfl) ⟨2038427, by rfl⟩ : syracuseStep 2717903 = 4076855) B4076855
theorem B78387547 : Blo 1811607 78387547 := bstep (se 1 (by rfl) ⟨58790660, by rfl⟩ : syracuseStep 78387547 = 117581321) B117581321
theorem B161159681 : Blo 1811607 161159681 := bstep (se 2 (by rfl) ⟨60434880, by rfl⟩ : syracuseStep 161159681 = 120869761) B120869761
theorem B2718263 : Blo 1811607 2718263 := bstep (se 1 (by rfl) ⟨2038697, by rfl⟩ : syracuseStep 2718263 = 4077395) B4077395
theorem B2718335 : Blo 1811607 2718335 := bstep (se 1 (by rfl) ⟨2038751, by rfl⟩ : syracuseStep 2718335 = 4077503) B4077503
theorem B5806895 : Blo 1811607 5806895 := bstep (se 1 (by rfl) ⟨4355171, by rfl⟩ : syracuseStep 5806895 = 8710343) B8710343
theorem B3439559 : Blo 1811607 3439559 := bstep (se 1 (by rfl) ⟨2579669, by rfl⟩ : syracuseStep 3439559 = 5159339) B5159339
theorem B2718959 : Blo 1811607 2718959 := bstep (se 1 (by rfl) ⟨2039219, by rfl⟩ : syracuseStep 2718959 = 4078439) B4078439
theorem B44711165 : Blo 1811607 44711165 := bstep (se 3 (by rfl) ⟨8383343, by rfl⟩ : syracuseStep 44711165 = 16766687) B16766687
theorem B2039323 : Blo 1811607 2039323 := bstep (se 1 (by rfl) ⟨1529492, by rfl⟩ : syracuseStep 2039323 = 3058985) B3058985
theorem B176315939 : Blo 1811607 176315939 := bstep (se 1 (by rfl) ⟨132236954, by rfl⟩ : syracuseStep 176315939 = 264473909) B264473909
theorem B10460801 : Blo 1811607 10460801 := bstep (se 2 (by rfl) ⟨3922800, by rfl⟩ : syracuseStep 10460801 = 7845601) B7845601
theorem B2719391 : Blo 1811607 2719391 := bstep (se 1 (by rfl) ⟨2039543, by rfl⟩ : syracuseStep 2719391 = 4079087) B4079087
theorem B11616047 : Blo 1811607 11616047 := bstep (se 1 (by rfl) ⟨8712035, by rfl⟩ : syracuseStep 11616047 = 17424071) B17424071
theorem B4587475 : Blo 1811607 4587475 := bstep (se 1 (by rfl) ⟨3440606, by rfl⟩ : syracuseStep 4587475 = 6881213) B6881213
theorem B2719721 : Blo 1811607 2719721 := bstep (se 2 (by rfl) ⟨1019895, by rfl⟩ : syracuseStep 2719721 = 2039791) B2039791
theorem B22044653 : Blo 1811607 22044653 := bstep (se 3 (by rfl) ⟨4133372, by rfl⟩ : syracuseStep 22044653 = 8266745) B8266745
theorem B2719739 : Blo 1811607 2719739 := bstep (se 1 (by rfl) ⟨2039804, by rfl⟩ : syracuseStep 2719739 = 4079609) B4079609
theorem B2719799 : Blo 1811607 2719799 := bstep (se 1 (by rfl) ⟨2039849, by rfl⟩ : syracuseStep 2719799 = 4079699) B4079699
theorem B4079753 : Blo 1811607 4079753 := bstep (se 2 (by rfl) ⟨1529907, by rfl⟩ : syracuseStep 4079753 = 3059815) B3059815
theorem B4079771 : Blo 1811607 4079771 := bstep (se 1 (by rfl) ⟨3059828, by rfl⟩ : syracuseStep 4079771 = 6119657) B6119657
theorem B13771295 : Blo 1811607 13771295 := bstep (se 1 (by rfl) ⟨10328471, by rfl⟩ : syracuseStep 13771295 = 20656943) B20656943
theorem B2720297 : Blo 1811607 2720297 := bstep (se 2 (by rfl) ⟨1020111, by rfl⟩ : syracuseStep 2720297 = 2040223) B2040223
theorem B4588123 : Blo 1811607 4588123 := bstep (se 1 (by rfl) ⟨3441092, by rfl⟩ : syracuseStep 4588123 = 6882185) B6882185
theorem B4588265 : Blo 1811607 4588265 := bstep (se 2 (by rfl) ⟨1720599, by rfl⟩ : syracuseStep 4588265 = 3441199) B3441199
theorem B6972635 : Blo 1811607 6972635 := bstep (se 1 (by rfl) ⟨5229476, by rfl⟩ : syracuseStep 6972635 = 10458953) B10458953
theorem B55829735 : Blo 1811607 55829735 := bstep (se 1 (by rfl) ⟨41872301, by rfl⟩ : syracuseStep 55829735 = 83744603) B83744603
theorem B1811935 : Blo 1811607 1811935 := bstep (se 1 (by rfl) ⟨1358951, by rfl⟩ : syracuseStep 1811935 = 2717903) B2717903
theorem B107439787 : Blo 1811607 107439787 := bstep (se 1 (by rfl) ⟨80579840, by rfl⟩ : syracuseStep 107439787 = 161159681) B161159681
theorem B1812175 : Blo 1811607 1812175 := bstep (se 1 (by rfl) ⟨1359131, by rfl⟩ : syracuseStep 1812175 = 2718263) B2718263
theorem B1812223 : Blo 1811607 1812223 := bstep (se 1 (by rfl) ⟨1359167, by rfl⟩ : syracuseStep 1812223 = 2718335) B2718335
theorem B15485053 : Blo 1811607 15485053 := bstep (se 3 (by rfl) ⟨2903447, by rfl⟩ : syracuseStep 15485053 = 5806895) B5806895
theorem B1812639 : Blo 1811607 1812639 := bstep (se 1 (by rfl) ⟨1359479, by rfl⟩ : syracuseStep 1812639 = 2718959) B2718959
theorem B203786401 : Blo 1811607 203786401 := bstep (se 2 (by rfl) ⟨76419900, by rfl⟩ : syracuseStep 203786401 = 152839801) B152839801
theorem B6973867 : Blo 1811607 6973867 := bstep (se 1 (by rfl) ⟨5230400, by rfl⟩ : syracuseStep 6973867 = 10460801) B10460801
theorem B9554365 : Blo 1811607 9554365 := bstep (se 3 (by rfl) ⟨1791443, by rfl⟩ : syracuseStep 9554365 = 3582887) B3582887
theorem B1812927 : Blo 1811607 1812927 := bstep (se 1 (by rfl) ⟨1359695, by rfl⟩ : syracuseStep 1812927 = 2719391) B2719391
theorem B5163497 : Blo 1811607 5163497 := bstep (se 2 (by rfl) ⟨1936311, by rfl⟩ : syracuseStep 5163497 = 3872623) B3872623
theorem B7744031 : Blo 1811607 7744031 := bstep (se 1 (by rfl) ⟨5808023, by rfl⟩ : syracuseStep 7744031 = 11616047) B11616047
theorem B1813147 : Blo 1811607 1813147 := bstep (se 1 (by rfl) ⟨1359860, by rfl⟩ : syracuseStep 1813147 = 2719721) B2719721
theorem B1813159 : Blo 1811607 1813159 := bstep (se 1 (by rfl) ⟨1359869, by rfl⟩ : syracuseStep 1813159 = 2719739) B2719739
theorem B3058411 : Blo 1811607 3058411 := bstep (se 1 (by rfl) ⟨2293808, by rfl⟩ : syracuseStep 3058411 = 4587617) B4587617
theorem B14150447 : Blo 1811607 14150447 := bstep (se 1 (by rfl) ⟨10612835, by rfl⟩ : syracuseStep 14150447 = 21225671) B21225671
theorem B3058553 : Blo 1811607 3058553 := bstep (se 2 (by rfl) ⟨1146957, by rfl⟩ : syracuseStep 3058553 = 2293915) B2293915
theorem B4901755 : Blo 1811607 4901755 := bstep (se 1 (by rfl) ⟨3676316, by rfl⟩ : syracuseStep 4901755 = 7352633) B7352633
theorem B4590665 : Blo 1811607 4590665 := bstep (se 2 (by rfl) ⟨1721499, by rfl⟩ : syracuseStep 4590665 = 3442999) B3442999
theorem B104516729 : Blo 1811607 104516729 := bstep (se 2 (by rfl) ⟨39193773, by rfl⟩ : syracuseStep 104516729 = 78387547) B78387547
theorem B8711711 : Blo 1811607 8711711 := bstep (se 1 (by rfl) ⟨6533783, by rfl⟩ : syracuseStep 8711711 = 13067567) B13067567
theorem B47722049 : Blo 1811607 47722049 := bstep (se 2 (by rfl) ⟨17895768, by rfl⟩ : syracuseStep 47722049 = 35791537) B35791537
theorem B13062055 : Blo 1811607 13062055 := bstep (se 1 (by rfl) ⟨9796541, by rfl⟩ : syracuseStep 13062055 = 19593083) B19593083
theorem B40275883 : Blo 1811607 40275883 := bstep (se 1 (by rfl) ⟨30206912, by rfl⟩ : syracuseStep 40275883 = 60413825) B60413825
theorem B78409691 : Blo 1811607 78409691 := bstep (se 1 (by rfl) ⟨58807268, by rfl⟩ : syracuseStep 78409691 = 117614537) B117614537
theorem B29807443 : Blo 1811607 29807443 := bstep (se 1 (by rfl) ⟨22355582, by rfl⟩ : syracuseStep 29807443 = 44711165) B44711165
theorem B117543959 : Blo 1811607 117543959 := bstep (se 1 (by rfl) ⟨88157969, by rfl⟩ : syracuseStep 117543959 = 176315939) B176315939
theorem B4076711 : Blo 1811607 4076711 := bstep (se 1 (by rfl) ⟨3057533, by rfl⟩ : syracuseStep 4076711 = 6115067) B6115067
theorem B6116633 : Blo 1811607 6116633 := bstep (se 2 (by rfl) ⟨2293737, by rfl⟩ : syracuseStep 6116633 = 4587475) B4587475
theorem B2789594477 : Blo 1811607 2789594477 := bstep (se 3 (by rfl) ⟨523048964, by rfl⟩ : syracuseStep 2789594477 = 1046097929) B1046097929
theorem B9181025 : Blo 1811607 9181025 := bstep (se 2 (by rfl) ⟨3442884, by rfl⟩ : syracuseStep 9181025 = 6885769) B6885769
theorem B3872767 : Blo 1811607 3872767 := bstep (se 1 (by rfl) ⟨2904575, by rfl⟩ : syracuseStep 3872767 = 5809151) B5809151
theorem B2717951 : Blo 1811607 2717951 := bstep (se 1 (by rfl) ⟨2038463, by rfl⟩ : syracuseStep 2717951 = 4076927) B4076927
theorem B18856289 : Blo 1811607 18856289 := bstep (se 2 (by rfl) ⟨7071108, by rfl⟩ : syracuseStep 18856289 = 14142217) B14142217
theorem B2038171 : Blo 1811607 2038171 := bstep (se 1 (by rfl) ⟨1528628, by rfl⟩ : syracuseStep 2038171 = 3057257) B3057257
theorem B10320317 : Blo 1811607 10320317 := bstep (se 3 (by rfl) ⟨1935059, by rfl⟩ : syracuseStep 10320317 = 3870119) B3870119
theorem B4078601 : Blo 1811607 4078601 := bstep (se 2 (by rfl) ⟨1529475, by rfl⟩ : syracuseStep 4078601 = 3058951) B3058951
theorem B2293039 : Blo 1811607 2293039 := bstep (se 1 (by rfl) ⟨1719779, by rfl⟩ : syracuseStep 2293039 = 3439559) B3439559
theorem B2039143 : Blo 1811607 2039143 := bstep (se 1 (by rfl) ⟨1529357, by rfl⟩ : syracuseStep 2039143 = 3058715) B3058715
theorem B2719097 : Blo 1811607 2719097 := bstep (se 2 (by rfl) ⟨1019661, by rfl⟩ : syracuseStep 2719097 = 2039323) B2039323
theorem B14696435 : Blo 1811607 14696435 := bstep (se 1 (by rfl) ⟨11022326, by rfl⟩ : syracuseStep 14696435 = 22044653) B22044653
theorem B2719835 : Blo 1811607 2719835 := bstep (se 1 (by rfl) ⟨2039876, by rfl⟩ : syracuseStep 2719835 = 4079753) B4079753
theorem B2719847 : Blo 1811607 2719847 := bstep (se 1 (by rfl) ⟨2039885, by rfl⟩ : syracuseStep 2719847 = 4079771) B4079771
theorem B9298489 : Blo 1811607 9298489 := bstep (se 2 (by rfl) ⟨3486933, by rfl⟩ : syracuseStep 9298489 = 6973867) B6973867
theorem B12739153 : Blo 1811607 12739153 := bstep (se 2 (by rfl) ⟨4777182, by rfl⟩ : syracuseStep 12739153 = 9554365) B9554365
theorem B6120683 : Blo 1811607 6120683 := bstep (se 1 (by rfl) ⟨4590512, by rfl⟩ : syracuseStep 6120683 = 9181025) B9181025
theorem B1811967 : Blo 1811607 1811967 := bstep (se 1 (by rfl) ⟨1358975, by rfl⟩ : syracuseStep 1811967 = 2717951) B2717951
theorem B3442331 : Blo 1811607 3442331 := bstep (se 1 (by rfl) ⟨2581748, by rfl⟩ : syracuseStep 3442331 = 5163497) B5163497
theorem B5162687 : Blo 1811607 5162687 := bstep (se 1 (by rfl) ⟨3872015, by rfl⟩ : syracuseStep 5162687 = 7744031) B7744031
theorem B3057385 : Blo 1811607 3057385 := bstep (se 2 (by rfl) ⟨1146519, by rfl⟩ : syracuseStep 3057385 = 2293039) B2293039
theorem B1812731 : Blo 1811607 1812731 := bstep (se 1 (by rfl) ⟨1359548, by rfl⟩ : syracuseStep 1812731 = 2719097) B2719097
theorem B53701177 : Blo 1811607 53701177 := bstep (se 2 (by rfl) ⟨20137941, by rfl⟩ : syracuseStep 53701177 = 40275883) B40275883
theorem B5163689 : Blo 1811607 5163689 := bstep (se 2 (by rfl) ⟨1936383, by rfl⟩ : syracuseStep 5163689 = 3872767) B3872767
theorem B1813199 : Blo 1811607 1813199 := bstep (se 1 (by rfl) ⟨1359899, by rfl⟩ : syracuseStep 1813199 = 2719799) B2719799
theorem B20646737 : Blo 1811607 20646737 := bstep (se 2 (by rfl) ⟨7742526, by rfl⟩ : syracuseStep 20646737 = 15485053) B15485053
theorem B271715201 : Blo 1811607 271715201 := bstep (se 2 (by rfl) ⟨101893200, by rfl⟩ : syracuseStep 271715201 = 203786401) B203786401
theorem B1813531 : Blo 1811607 1813531 := bstep (se 1 (by rfl) ⟨1360148, by rfl⟩ : syracuseStep 1813531 = 2720297) B2720297
theorem B3058843 : Blo 1811607 3058843 := bstep (se 1 (by rfl) ⟨2294132, by rfl⟩ : syracuseStep 3058843 = 4588265) B4588265
theorem B4648423 : Blo 1811607 4648423 := bstep (se 1 (by rfl) ⟨3486317, by rfl⟩ : syracuseStep 4648423 = 6972635) B6972635
theorem B37219823 : Blo 1811607 37219823 := bstep (se 1 (by rfl) ⟨27914867, by rfl⟩ : syracuseStep 37219823 = 55829735) B55829735
theorem B39743257 : Blo 1811607 39743257 := bstep (se 2 (by rfl) ⟨14903721, by rfl⟩ : syracuseStep 39743257 = 29807443) B29807443
theorem B12570859 : Blo 1811607 12570859 := bstep (se 1 (by rfl) ⟨9428144, by rfl⟩ : syracuseStep 12570859 = 18856289) B18856289
theorem B9433631 : Blo 1811607 9433631 := bstep (se 1 (by rfl) ⟨7075223, by rfl⟩ : syracuseStep 9433631 = 14150447) B14150447
theorem B3060443 : Blo 1811607 3060443 := bstep (se 1 (by rfl) ⟨2295332, by rfl⟩ : syracuseStep 3060443 = 4590665) B4590665
theorem B69677819 : Blo 1811607 69677819 := bstep (se 1 (by rfl) ⟨52258364, by rfl⟩ : syracuseStep 69677819 = 104516729) B104516729
theorem B31814699 : Blo 1811607 31814699 := bstep (se 1 (by rfl) ⟨23861024, by rfl⟩ : syracuseStep 31814699 = 47722049) B47722049
theorem B9180863 : Blo 1811607 9180863 := bstep (se 1 (by rfl) ⟨6885647, by rfl⟩ : syracuseStep 9180863 = 13771295) B13771295
theorem B2717561 : Blo 1811607 2717561 := bstep (se 2 (by rfl) ⟨1019085, by rfl⟩ : syracuseStep 2717561 = 2038171) B2038171
theorem B78362639 : Blo 1811607 78362639 := bstep (se 1 (by rfl) ⟨58771979, by rfl⟩ : syracuseStep 78362639 = 117543959) B117543959
theorem B2717807 : Blo 1811607 2717807 := bstep (se 1 (by rfl) ⟨2038355, by rfl⟩ : syracuseStep 2717807 = 4076711) B4076711
theorem B6117497 : Blo 1811607 6117497 := bstep (se 2 (by rfl) ⟨2294061, by rfl⟩ : syracuseStep 6117497 = 4588123) B4588123
theorem B4077755 : Blo 1811607 4077755 := bstep (se 1 (by rfl) ⟨3058316, by rfl⟩ : syracuseStep 4077755 = 6116633) B6116633
theorem B1859729651 : Blo 1811607 1859729651 := bstep (se 1 (by rfl) ⟨1394797238, by rfl⟩ : syracuseStep 1859729651 = 2789594477) B2789594477
theorem B4077881 : Blo 1811607 4077881 := bstep (se 2 (by rfl) ⟨1529205, by rfl⟩ : syracuseStep 4077881 = 3058411) B3058411
theorem B6535673 : Blo 1811607 6535673 := bstep (se 2 (by rfl) ⟨2450877, by rfl⟩ : syracuseStep 6535673 = 4901755) B4901755
theorem B6880211 : Blo 1811607 6880211 := bstep (se 1 (by rfl) ⟨5160158, by rfl⟩ : syracuseStep 6880211 = 10320317) B10320317
theorem B2718857 : Blo 1811607 2718857 := bstep (se 2 (by rfl) ⟨1019571, by rfl⟩ : syracuseStep 2718857 = 2039143) B2039143
theorem B2039035 : Blo 1811607 2039035 := bstep (se 1 (by rfl) ⟨1529276, by rfl⟩ : syracuseStep 2039035 = 3058553) B3058553
theorem B2719067 : Blo 1811607 2719067 := bstep (se 1 (by rfl) ⟨2039300, by rfl⟩ : syracuseStep 2719067 = 4078601) B4078601
theorem B143253049 : Blo 1811607 143253049 := bstep (se 2 (by rfl) ⟨53719893, by rfl⟩ : syracuseStep 143253049 = 107439787) B107439787
theorem B5807807 : Blo 1811607 5807807 := bstep (se 1 (by rfl) ⟨4355855, by rfl⟩ : syracuseStep 5807807 = 8711711) B8711711
theorem B17416073 : Blo 1811607 17416073 := bstep (se 2 (by rfl) ⟨6531027, by rfl⟩ : syracuseStep 17416073 = 13062055) B13062055
theorem B39190493 : Blo 1811607 39190493 := bstep (se 3 (by rfl) ⟨7348217, by rfl⟩ : syracuseStep 39190493 = 14696435) B14696435
theorem B52273127 : Blo 1811607 52273127 := bstep (se 1 (by rfl) ⟨39204845, by rfl⟩ : syracuseStep 52273127 = 78409691) B78409691
theorem B2040295 : Blo 1811607 2040295 := bstep (se 1 (by rfl) ⟨1530221, by rfl⟩ : syracuseStep 2040295 = 3060443) B3060443
theorem B4080455 : Blo 1811607 4080455 := bstep (se 1 (by rfl) ⟨3060341, by rfl⟩ : syracuseStep 4080455 = 6120683) B6120683
theorem B2294887 : Blo 1811607 2294887 := bstep (se 1 (by rfl) ⟨1721165, by rfl⟩ : syracuseStep 2294887 = 3442331) B3442331
theorem B3441791 : Blo 1811607 3441791 := bstep (se 1 (by rfl) ⟨2581343, by rfl⟩ : syracuseStep 3441791 = 5162687) B5162687
theorem B6120575 : Blo 1811607 6120575 := bstep (se 1 (by rfl) ⟨4590431, by rfl⟩ : syracuseStep 6120575 = 9180863) B9180863
theorem B67044581 : Blo 1811607 67044581 := bstep (se 4 (by rfl) ⟨6285429, by rfl⟩ : syracuseStep 67044581 = 12570859) B12570859
theorem B1811707 : Blo 1811607 1811707 := bstep (se 1 (by rfl) ⟨1358780, by rfl⟩ : syracuseStep 1811707 = 2717561) B2717561
theorem B52241759 : Blo 1811607 52241759 := bstep (se 1 (by rfl) ⟨39181319, by rfl⟩ : syracuseStep 52241759 = 78362639) B78362639
theorem B1811871 : Blo 1811607 1811871 := bstep (se 1 (by rfl) ⟨1358903, by rfl⟩ : syracuseStep 1811871 = 2717807) B2717807
theorem B1239819767 : Blo 1811607 1239819767 := bstep (se 1 (by rfl) ⟨929864825, by rfl⟩ : syracuseStep 1239819767 = 1859729651) B1859729651
theorem B13764491 : Blo 1811607 13764491 := bstep (se 1 (by rfl) ⟨10323368, by rfl⟩ : syracuseStep 13764491 = 20646737) B20646737
theorem B181143467 : Blo 1811607 181143467 := bstep (se 1 (by rfl) ⟨135857600, by rfl⟩ : syracuseStep 181143467 = 271715201) B271715201
theorem B1812571 : Blo 1811607 1812571 := bstep (se 1 (by rfl) ⟨1359428, by rfl⟩ : syracuseStep 1812571 = 2718857) B2718857
theorem B1812711 : Blo 1811607 1812711 := bstep (se 1 (by rfl) ⟨1359533, by rfl⟩ : syracuseStep 1812711 = 2719067) B2719067
theorem B11610715 : Blo 1811607 11610715 := bstep (se 1 (by rfl) ⟨8708036, by rfl⟩ : syracuseStep 11610715 = 17416073) B17416073
theorem B26126995 : Blo 1811607 26126995 := bstep (se 1 (by rfl) ⟨19595246, by rfl⟩ : syracuseStep 26126995 = 39190493) B39190493
theorem B1813223 : Blo 1811607 1813223 := bstep (se 1 (by rfl) ⟨1359917, by rfl⟩ : syracuseStep 1813223 = 2719835) B2719835
theorem B1813231 : Blo 1811607 1813231 := bstep (se 1 (by rfl) ⟨1359923, by rfl⟩ : syracuseStep 1813231 = 2719847) B2719847
theorem B339356789 : Blo 1811607 339356789 := bstep (se 5 (by rfl) ⟨15907349, by rfl⟩ : syracuseStep 339356789 = 31814699) B31814699
theorem B46451879 : Blo 1811607 46451879 := bstep (se 1 (by rfl) ⟨34838909, by rfl⟩ : syracuseStep 46451879 = 69677819) B69677819
theorem B12397985 : Blo 1811607 12397985 := bstep (se 2 (by rfl) ⟨4649244, by rfl⟩ : syracuseStep 12397985 = 9298489) B9298489
theorem B71601569 : Blo 1811607 71601569 := bstep (se 2 (by rfl) ⟨26850588, by rfl⟩ : syracuseStep 71601569 = 53701177) B53701177
theorem B16985537 : Blo 1811607 16985537 := bstep (se 2 (by rfl) ⟨6369576, by rfl⟩ : syracuseStep 16985537 = 12739153) B12739153
theorem B6197897 : Blo 1811607 6197897 := bstep (se 2 (by rfl) ⟨2324211, by rfl⟩ : syracuseStep 6197897 = 4648423) B4648423
theorem B4076513 : Blo 1811607 4076513 := bstep (se 2 (by rfl) ⟨1528692, by rfl⟩ : syracuseStep 4076513 = 3057385) B3057385
theorem B52991009 : Blo 1811607 52991009 := bstep (se 2 (by rfl) ⟨19871628, by rfl⟩ : syracuseStep 52991009 = 39743257) B39743257
theorem B3871871 : Blo 1811607 3871871 := bstep (se 1 (by rfl) ⟨2903903, by rfl⟩ : syracuseStep 3871871 = 5807807) B5807807
theorem B4078331 : Blo 1811607 4078331 := bstep (se 1 (by rfl) ⟨3058748, by rfl⟩ : syracuseStep 4078331 = 6117497) B6117497
theorem B25156349 : Blo 1811607 25156349 := bstep (se 3 (by rfl) ⟨4716815, by rfl⟩ : syracuseStep 25156349 = 9433631) B9433631
theorem B2718503 : Blo 1811607 2718503 := bstep (se 1 (by rfl) ⟨2038877, by rfl⟩ : syracuseStep 2718503 = 4077755) B4077755
theorem B4078457 : Blo 1811607 4078457 := bstep (se 2 (by rfl) ⟨1529421, by rfl⟩ : syracuseStep 4078457 = 3058843) B3058843
theorem B2718587 : Blo 1811607 2718587 := bstep (se 1 (by rfl) ⟨2038940, by rfl⟩ : syracuseStep 2718587 = 4077881) B4077881
theorem B2718713 : Blo 1811607 2718713 := bstep (se 2 (by rfl) ⟨1019517, by rfl⟩ : syracuseStep 2718713 = 2039035) B2039035
theorem B4357115 : Blo 1811607 4357115 := bstep (se 1 (by rfl) ⟨3267836, by rfl⟩ : syracuseStep 4357115 = 6535673) B6535673
theorem B13769837 : Blo 1811607 13769837 := bstep (se 3 (by rfl) ⟨2581844, by rfl⟩ : syracuseStep 13769837 = 5163689) B5163689
theorem B4586807 : Blo 1811607 4586807 := bstep (se 1 (by rfl) ⟨3440105, by rfl⟩ : syracuseStep 4586807 = 6880211) B6880211
theorem B191004065 : Blo 1811607 191004065 := bstep (se 2 (by rfl) ⟨71626524, by rfl⟩ : syracuseStep 191004065 = 143253049) B143253049
theorem B24813215 : Blo 1811607 24813215 := bstep (se 1 (by rfl) ⟨18609911, by rfl⟩ : syracuseStep 24813215 = 37219823) B37219823
theorem B34848751 : Blo 1811607 34848751 := bstep (se 1 (by rfl) ⟨26136563, by rfl⟩ : syracuseStep 34848751 = 52273127) B52273127
theorem B2720303 : Blo 1811607 2720303 := bstep (se 1 (by rfl) ⟨2040227, by rfl⟩ : syracuseStep 2720303 = 4080455) B4080455
theorem B2720393 : Blo 1811607 2720393 := bstep (se 2 (by rfl) ⟨1020147, by rfl⟩ : syracuseStep 2720393 = 2040295) B2040295
theorem B2581247 : Blo 1811607 2581247 := bstep (se 1 (by rfl) ⟨1935935, by rfl⟩ : syracuseStep 2581247 = 3871871) B3871871
theorem B4080383 : Blo 1811607 4080383 := bstep (se 1 (by rfl) ⟨3060287, by rfl⟩ : syracuseStep 4080383 = 6120575) B6120575
theorem B44696387 : Blo 1811607 44696387 := bstep (se 1 (by rfl) ⟨33522290, by rfl⟩ : syracuseStep 44696387 = 67044581) B67044581
theorem B9176327 : Blo 1811607 9176327 := bstep (se 1 (by rfl) ⟨6882245, by rfl⟩ : syracuseStep 9176327 = 13764491) B13764491
theorem B16770899 : Blo 1811607 16770899 := bstep (se 1 (by rfl) ⟨12578174, by rfl⟩ : syracuseStep 16770899 = 25156349) B25156349
theorem B1812335 : Blo 1811607 1812335 := bstep (se 1 (by rfl) ⟨1359251, by rfl⟩ : syracuseStep 1812335 = 2718503) B2718503
theorem B1812391 : Blo 1811607 1812391 := bstep (se 1 (by rfl) ⟨1359293, by rfl⟩ : syracuseStep 1812391 = 2718587) B2718587
theorem B1812475 : Blo 1811607 1812475 := bstep (se 1 (by rfl) ⟨1359356, by rfl⟩ : syracuseStep 1812475 = 2718713) B2718713
theorem B30967919 : Blo 1811607 30967919 := bstep (se 1 (by rfl) ⟨23225939, by rfl⟩ : syracuseStep 30967919 = 46451879) B46451879
theorem B3057871 : Blo 1811607 3057871 := bstep (se 1 (by rfl) ⟨2293403, by rfl⟩ : syracuseStep 3057871 = 4586807) B4586807
theorem B11323691 : Blo 1811607 11323691 := bstep (se 1 (by rfl) ⟨8492768, by rfl⟩ : syracuseStep 11323691 = 16985537) B16985537
theorem B16542143 : Blo 1811607 16542143 := bstep (se 1 (by rfl) ⟨12406607, by rfl⟩ : syracuseStep 16542143 = 24813215) B24813215
theorem B9178109 : Blo 1811607 9178109 := bstep (se 3 (by rfl) ⟨1720895, by rfl⟩ : syracuseStep 9178109 = 3441791) B3441791
theorem B35327339 : Blo 1811607 35327339 := bstep (se 1 (by rfl) ⟨26495504, by rfl⟩ : syracuseStep 35327339 = 52991009) B52991009
theorem B34835993 : Blo 1811607 34835993 := bstep (se 2 (by rfl) ⟨13063497, by rfl⟩ : syracuseStep 34835993 = 26126995) B26126995
theorem B34827839 : Blo 1811607 34827839 := bstep (se 1 (by rfl) ⟨26120879, by rfl⟩ : syracuseStep 34827839 = 52241759) B52241759
theorem B120762311 : Blo 1811607 120762311 := bstep (se 1 (by rfl) ⟨90571733, by rfl⟩ : syracuseStep 120762311 = 181143467) B181143467
theorem B3059849 : Blo 1811607 3059849 := bstep (se 2 (by rfl) ⟨1147443, by rfl⟩ : syracuseStep 3059849 = 2294887) B2294887
theorem B16527725 : Blo 1811607 16527725 := bstep (se 3 (by rfl) ⟨3098948, by rfl⟩ : syracuseStep 16527725 = 6197897) B6197897
theorem B2904743 : Blo 1811607 2904743 := bstep (se 1 (by rfl) ⟨2178557, by rfl⟩ : syracuseStep 2904743 = 4357115) B4357115
theorem B9179891 : Blo 1811607 9179891 := bstep (se 1 (by rfl) ⟨6884918, by rfl⟩ : syracuseStep 9179891 = 13769837) B13769837
theorem B2717675 : Blo 1811607 2717675 := bstep (se 1 (by rfl) ⟨2038256, by rfl⟩ : syracuseStep 2717675 = 4076513) B4076513
theorem B15480953 : Blo 1811607 15480953 := bstep (se 2 (by rfl) ⟨5805357, by rfl⟩ : syracuseStep 15480953 = 11610715) B11610715
theorem B826546511 : Blo 1811607 826546511 := bstep (se 1 (by rfl) ⟨619909883, by rfl⟩ : syracuseStep 826546511 = 1239819767) B1239819767
theorem B2718887 : Blo 1811607 2718887 := bstep (se 1 (by rfl) ⟨2039165, by rfl⟩ : syracuseStep 2718887 = 4078331) B4078331
theorem B2718971 : Blo 1811607 2718971 := bstep (se 1 (by rfl) ⟨2039228, by rfl⟩ : syracuseStep 2718971 = 4078457) B4078457
theorem B226237859 : Blo 1811607 226237859 := bstep (se 1 (by rfl) ⟨169678394, by rfl⟩ : syracuseStep 226237859 = 339356789) B339356789
theorem B8265323 : Blo 1811607 8265323 := bstep (se 1 (by rfl) ⟨6198992, by rfl⟩ : syracuseStep 8265323 = 12397985) B12397985
theorem B47734379 : Blo 1811607 47734379 := bstep (se 1 (by rfl) ⟨35800784, by rfl⟩ : syracuseStep 47734379 = 71601569) B71601569
theorem B127336043 : Blo 1811607 127336043 := bstep (se 1 (by rfl) ⟨95502032, by rfl⟩ : syracuseStep 127336043 = 191004065) B191004065
theorem B46465001 : Blo 1811607 46465001 := bstep (se 2 (by rfl) ⟨17424375, by rfl⟩ : syracuseStep 46465001 = 34848751) B34848751
theorem B2039899 : Blo 1811607 2039899 := bstep (se 1 (by rfl) ⟨1529924, by rfl⟩ : syracuseStep 2039899 = 3059849) B3059849
theorem B11018483 : Blo 1811607 11018483 := bstep (se 1 (by rfl) ⟨8263862, by rfl⟩ : syracuseStep 11018483 = 16527725) B16527725
theorem B6119927 : Blo 1811607 6119927 := bstep (se 1 (by rfl) ⟨4589945, by rfl⟩ : syracuseStep 6119927 = 9179891) B9179891
theorem B2720255 : Blo 1811607 2720255 := bstep (se 1 (by rfl) ⟨2040191, by rfl⟩ : syracuseStep 2720255 = 4080383) B4080383
theorem B1811783 : Blo 1811607 1811783 := bstep (se 1 (by rfl) ⟨1358837, by rfl⟩ : syracuseStep 1811783 = 2717675) B2717675
theorem B20645279 : Blo 1811607 20645279 := bstep (se 1 (by rfl) ⟨15483959, by rfl⟩ : syracuseStep 20645279 = 30967919) B30967919
theorem B11028095 : Blo 1811607 11028095 := bstep (se 1 (by rfl) ⟨8271071, by rfl⟩ : syracuseStep 11028095 = 16542143) B16542143
theorem B6883325 : Blo 1811607 6883325 := bstep (se 3 (by rfl) ⟨1290623, by rfl⟩ : syracuseStep 6883325 = 2581247) B2581247
theorem B1812591 : Blo 1811607 1812591 := bstep (se 1 (by rfl) ⟨1359443, by rfl⟩ : syracuseStep 1812591 = 2718887) B2718887
theorem B1812647 : Blo 1811607 1812647 := bstep (se 1 (by rfl) ⟨1359485, by rfl⟩ : syracuseStep 1812647 = 2718971) B2718971
theorem B150825239 : Blo 1811607 150825239 := bstep (se 1 (by rfl) ⟨113118929, by rfl⟩ : syracuseStep 150825239 = 226237859) B226237859
theorem B23218559 : Blo 1811607 23218559 := bstep (se 1 (by rfl) ⟨17413919, by rfl⟩ : syracuseStep 23218559 = 34827839) B34827839
theorem B30976667 : Blo 1811607 30976667 := bstep (se 1 (by rfl) ⟨23232500, by rfl⟩ : syracuseStep 30976667 = 46465001) B46465001
theorem B1813535 : Blo 1811607 1813535 := bstep (se 1 (by rfl) ⟨1360151, by rfl⟩ : syracuseStep 1813535 = 2720303) B2720303
theorem B1813595 : Blo 1811607 1813595 := bstep (se 1 (by rfl) ⟨1360196, by rfl⟩ : syracuseStep 1813595 = 2720393) B2720393
theorem B1936495 : Blo 1811607 1936495 := bstep (se 1 (by rfl) ⟨1452371, by rfl⟩ : syracuseStep 1936495 = 2904743) B2904743
theorem B29797591 : Blo 1811607 29797591 := bstep (se 1 (by rfl) ⟨22348193, by rfl⟩ : syracuseStep 29797591 = 44696387) B44696387
theorem B7549127 : Blo 1811607 7549127 := bstep (se 1 (by rfl) ⟨5661845, by rfl⟩ : syracuseStep 7549127 = 11323691) B11323691
theorem B551031007 : Blo 1811607 551031007 := bstep (se 1 (by rfl) ⟨413273255, by rfl⟩ : syracuseStep 551031007 = 826546511) B826546511
theorem B5510215 : Blo 1811607 5510215 := bstep (se 1 (by rfl) ⟨4132661, by rfl⟩ : syracuseStep 5510215 = 8265323) B8265323
theorem B31822919 : Blo 1811607 31822919 := bstep (se 1 (by rfl) ⟨23867189, by rfl⟩ : syracuseStep 31822919 = 47734379) B47734379
theorem B84890695 : Blo 1811607 84890695 := bstep (se 1 (by rfl) ⟨63668021, by rfl⟩ : syracuseStep 84890695 = 127336043) B127336043
theorem B322032829 : Blo 1811607 322032829 := bstep (se 3 (by rfl) ⟨60381155, by rfl⟩ : syracuseStep 322032829 = 120762311) B120762311
theorem B4077161 : Blo 1811607 4077161 := bstep (se 2 (by rfl) ⟨1528935, by rfl⟩ : syracuseStep 4077161 = 3057871) B3057871
theorem B6117551 : Blo 1811607 6117551 := bstep (se 1 (by rfl) ⟨4588163, by rfl⟩ : syracuseStep 6117551 = 9176327) B9176327
theorem B11180599 : Blo 1811607 11180599 := bstep (se 1 (by rfl) ⟨8385449, by rfl⟩ : syracuseStep 11180599 = 16770899) B16770899
theorem B10320635 : Blo 1811607 10320635 := bstep (se 1 (by rfl) ⟨7740476, by rfl⟩ : syracuseStep 10320635 = 15480953) B15480953
theorem B6118739 : Blo 1811607 6118739 := bstep (se 1 (by rfl) ⟨4589054, by rfl⟩ : syracuseStep 6118739 = 9178109) B9178109
theorem B23551559 : Blo 1811607 23551559 := bstep (se 1 (by rfl) ⟨17663669, by rfl⟩ : syracuseStep 23551559 = 35327339) B35327339
theorem B23223995 : Blo 1811607 23223995 := bstep (se 1 (by rfl) ⟨17417996, by rfl⟩ : syracuseStep 23223995 = 34835993) B34835993
theorem B2719865 : Blo 1811607 2719865 := bstep (se 2 (by rfl) ⟨1019949, by rfl⟩ : syracuseStep 2719865 = 2039899) B2039899
theorem B59629861 : Blo 1811607 59629861 := bstep (se 4 (by rfl) ⟨5590299, by rfl⟩ : syracuseStep 59629861 = 11180599) B11180599
theorem B734708009 : Blo 1811607 734708009 := bstep (se 2 (by rfl) ⟨275515503, by rfl⟩ : syracuseStep 734708009 = 551031007) B551031007
theorem B4079951 : Blo 1811607 4079951 := bstep (se 1 (by rfl) ⟨3059963, by rfl⟩ : syracuseStep 4079951 = 6119927) B6119927
theorem B13763519 : Blo 1811607 13763519 := bstep (se 1 (by rfl) ⟨10322639, by rfl⟩ : syracuseStep 13763519 = 20645279) B20645279
theorem B4588883 : Blo 1811607 4588883 := bstep (se 1 (by rfl) ⟨3441662, by rfl⟩ : syracuseStep 4588883 = 6883325) B6883325
theorem B2581993 : Blo 1811607 2581993 := bstep (se 2 (by rfl) ⟨968247, by rfl⟩ : syracuseStep 2581993 = 1936495) B1936495
theorem B100550159 : Blo 1811607 100550159 := bstep (se 1 (by rfl) ⟨75412619, by rfl⟩ : syracuseStep 100550159 = 150825239) B150825239
theorem B429377105 : Blo 1811607 429377105 := bstep (se 2 (by rfl) ⟨161016414, by rfl⟩ : syracuseStep 429377105 = 322032829) B322032829
theorem B5032751 : Blo 1811607 5032751 := bstep (se 1 (by rfl) ⟨3774563, by rfl⟩ : syracuseStep 5032751 = 7549127) B7549127
theorem B1813503 : Blo 1811607 1813503 := bstep (se 1 (by rfl) ⟨1360127, by rfl⟩ : syracuseStep 1813503 = 2720255) B2720255
theorem B7352063 : Blo 1811607 7352063 := bstep (se 1 (by rfl) ⟨5514047, by rfl⟩ : syracuseStep 7352063 = 11028095) B11028095
theorem B15479039 : Blo 1811607 15479039 := bstep (se 1 (by rfl) ⟨11609279, by rfl⟩ : syracuseStep 15479039 = 23218559) B23218559
theorem B15701039 : Blo 1811607 15701039 := bstep (se 1 (by rfl) ⟨11775779, by rfl⟩ : syracuseStep 15701039 = 23551559) B23551559
theorem B7345655 : Blo 1811607 7345655 := bstep (se 1 (by rfl) ⟨5509241, by rfl⟩ : syracuseStep 7345655 = 11018483) B11018483
theorem B21215279 : Blo 1811607 21215279 := bstep (se 1 (by rfl) ⟨15911459, by rfl⟩ : syracuseStep 21215279 = 31822919) B31822919
theorem B2718107 : Blo 1811607 2718107 := bstep (se 1 (by rfl) ⟨2038580, by rfl⟩ : syracuseStep 2718107 = 4077161) B4077161
theorem B7346953 : Blo 1811607 7346953 := bstep (se 2 (by rfl) ⟨2755107, by rfl⟩ : syracuseStep 7346953 = 5510215) B5510215
theorem B113187593 : Blo 1811607 113187593 := bstep (se 2 (by rfl) ⟨42445347, by rfl⟩ : syracuseStep 113187593 = 84890695) B84890695
theorem B4078367 : Blo 1811607 4078367 := bstep (se 1 (by rfl) ⟨3058775, by rfl⟩ : syracuseStep 4078367 = 6117551) B6117551
theorem B39730121 : Blo 1811607 39730121 := bstep (se 2 (by rfl) ⟨14898795, by rfl⟩ : syracuseStep 39730121 = 29797591) B29797591
theorem B20651111 : Blo 1811607 20651111 := bstep (se 1 (by rfl) ⟨15488333, by rfl⟩ : syracuseStep 20651111 = 30976667) B30976667
theorem B6880423 : Blo 1811607 6880423 := bstep (se 1 (by rfl) ⟨5160317, by rfl⟩ : syracuseStep 6880423 = 10320635) B10320635
theorem B4079159 : Blo 1811607 4079159 := bstep (se 1 (by rfl) ⟨3059369, by rfl⟩ : syracuseStep 4079159 = 6118739) B6118739
theorem B15482663 : Blo 1811607 15482663 := bstep (se 1 (by rfl) ⟨11611997, by rfl⟩ : syracuseStep 15482663 = 23223995) B23223995
theorem B2719967 : Blo 1811607 2719967 := bstep (se 1 (by rfl) ⟨2039975, by rfl⟩ : syracuseStep 2719967 = 4079951) B4079951
theorem B9175679 : Blo 1811607 9175679 := bstep (se 1 (by rfl) ⟨6881759, by rfl⟩ : syracuseStep 9175679 = 13763519) B13763519
theorem B39183749 : Blo 1811607 39183749 := bstep (se 4 (by rfl) ⟨3673476, by rfl⟩ : syracuseStep 39183749 = 7346953) B7346953
theorem B1812071 : Blo 1811607 1812071 := bstep (se 1 (by rfl) ⟨1359053, by rfl⟩ : syracuseStep 1812071 = 2718107) B2718107
theorem B75458395 : Blo 1811607 75458395 := bstep (se 1 (by rfl) ⟨56593796, by rfl⟩ : syracuseStep 75458395 = 113187593) B113187593
theorem B26486747 : Blo 1811607 26486747 := bstep (se 1 (by rfl) ⟨19865060, by rfl⟩ : syracuseStep 26486747 = 39730121) B39730121
theorem B3442657 : Blo 1811607 3442657 := bstep (se 2 (by rfl) ⟨1290996, by rfl⟩ : syracuseStep 3442657 = 2581993) B2581993
theorem B13420669 : Blo 1811607 13420669 := bstep (se 3 (by rfl) ⟨2516375, by rfl⟩ : syracuseStep 13420669 = 5032751) B5032751
theorem B4901375 : Blo 1811607 4901375 := bstep (se 1 (by rfl) ⟨3676031, by rfl⟩ : syracuseStep 4901375 = 7352063) B7352063
theorem B1813243 : Blo 1811607 1813243 := bstep (se 1 (by rfl) ⟨1359932, by rfl⟩ : syracuseStep 1813243 = 2719865) B2719865
theorem B79506481 : Blo 1811607 79506481 := bstep (se 2 (by rfl) ⟨29814930, by rfl⟩ : syracuseStep 79506481 = 59629861) B59629861
theorem B3059255 : Blo 1811607 3059255 := bstep (se 1 (by rfl) ⟨2294441, by rfl⟩ : syracuseStep 3059255 = 4588883) B4588883
theorem B14143519 : Blo 1811607 14143519 := bstep (se 1 (by rfl) ⟨10607639, by rfl⟩ : syracuseStep 14143519 = 21215279) B21215279
theorem B13767407 : Blo 1811607 13767407 := bstep (se 1 (by rfl) ⟨10325555, by rfl⟩ : syracuseStep 13767407 = 20651111) B20651111
theorem B10319359 : Blo 1811607 10319359 := bstep (se 1 (by rfl) ⟨7739519, by rfl⟩ : syracuseStep 10319359 = 15479039) B15479039
theorem B489805339 : Blo 1811607 489805339 := bstep (se 1 (by rfl) ⟨367354004, by rfl⟩ : syracuseStep 489805339 = 734708009) B734708009
theorem B10467359 : Blo 1811607 10467359 := bstep (se 1 (by rfl) ⟨7850519, by rfl⟩ : syracuseStep 10467359 = 15701039) B15701039
theorem B4897103 : Blo 1811607 4897103 := bstep (se 1 (by rfl) ⟨3672827, by rfl⟩ : syracuseStep 4897103 = 7345655) B7345655
theorem B67033439 : Blo 1811607 67033439 := bstep (se 1 (by rfl) ⟨50275079, by rfl⟩ : syracuseStep 67033439 = 100550159) B100550159
theorem B286251403 : Blo 1811607 286251403 := bstep (se 1 (by rfl) ⟨214688552, by rfl⟩ : syracuseStep 286251403 = 429377105) B429377105
theorem B9173897 : Blo 1811607 9173897 := bstep (se 2 (by rfl) ⟨3440211, by rfl⟩ : syracuseStep 9173897 = 6880423) B6880423
theorem B2718911 : Blo 1811607 2718911 := bstep (se 1 (by rfl) ⟨2039183, by rfl⟩ : syracuseStep 2718911 = 4078367) B4078367
theorem B2719439 : Blo 1811607 2719439 := bstep (se 1 (by rfl) ⟨2039579, by rfl⟩ : syracuseStep 2719439 = 4079159) B4079159
theorem B10321775 : Blo 1811607 10321775 := bstep (se 1 (by rfl) ⟨7741331, by rfl⟩ : syracuseStep 10321775 = 15482663) B15482663
theorem B18858025 : Blo 1811607 18858025 := bstep (se 2 (by rfl) ⟨7071759, by rfl⟩ : syracuseStep 18858025 = 14143519) B14143519
theorem B44688959 : Blo 1811607 44688959 := bstep (se 1 (by rfl) ⟨33516719, by rfl⟩ : syracuseStep 44688959 = 67033439) B67033439
theorem B1812607 : Blo 1811607 1812607 := bstep (se 1 (by rfl) ⟨1359455, by rfl⟩ : syracuseStep 1812607 = 2718911) B2718911
theorem B1812959 : Blo 1811607 1812959 := bstep (se 1 (by rfl) ⟨1359719, by rfl⟩ : syracuseStep 1812959 = 2719439) B2719439
theorem B4590209 : Blo 1811607 4590209 := bstep (se 2 (by rfl) ⟨1721328, by rfl⟩ : syracuseStep 4590209 = 3442657) B3442657
theorem B1813311 : Blo 1811607 1813311 := bstep (se 1 (by rfl) ⟨1359983, by rfl⟩ : syracuseStep 1813311 = 2719967) B2719967
theorem B17894225 : Blo 1811607 17894225 := bstep (se 2 (by rfl) ⟨6710334, by rfl⟩ : syracuseStep 17894225 = 13420669) B13420669
theorem B9178271 : Blo 1811607 9178271 := bstep (se 1 (by rfl) ⟨6883703, by rfl⟩ : syracuseStep 9178271 = 13767407) B13767407
theorem B381668537 : Blo 1811607 381668537 := bstep (se 2 (by rfl) ⟨143125701, by rfl⟩ : syracuseStep 381668537 = 286251403) B286251403
theorem B52235765 : Blo 1811607 52235765 := bstep (se 5 (by rfl) ⟨2448551, by rfl⟩ : syracuseStep 52235765 = 4897103) B4897103
theorem B17657831 : Blo 1811607 17657831 := bstep (se 1 (by rfl) ⟨13243373, by rfl⟩ : syracuseStep 17657831 = 26486747) B26486747
theorem B106008641 : Blo 1811607 106008641 := bstep (se 2 (by rfl) ⟨39753240, by rfl⟩ : syracuseStep 106008641 = 79506481) B79506481
theorem B6115931 : Blo 1811607 6115931 := bstep (se 1 (by rfl) ⟨4586948, by rfl⟩ : syracuseStep 6115931 = 9173897) B9173897
theorem B13759145 : Blo 1811607 13759145 := bstep (se 2 (by rfl) ⟨5159679, by rfl⟩ : syracuseStep 13759145 = 10319359) B10319359
theorem B100611193 : Blo 1811607 100611193 := bstep (se 2 (by rfl) ⟨37729197, by rfl⟩ : syracuseStep 100611193 = 75458395) B75458395
theorem B6117119 : Blo 1811607 6117119 := bstep (se 1 (by rfl) ⟨4587839, by rfl⟩ : syracuseStep 6117119 = 9175679) B9175679
theorem B26122499 : Blo 1811607 26122499 := bstep (se 1 (by rfl) ⟨19591874, by rfl⟩ : syracuseStep 26122499 = 39183749) B39183749
theorem B6978239 : Blo 1811607 6978239 := bstep (se 1 (by rfl) ⟨5233679, by rfl⟩ : syracuseStep 6978239 = 10467359) B10467359
theorem B3267583 : Blo 1811607 3267583 := bstep (se 1 (by rfl) ⟨2450687, by rfl⟩ : syracuseStep 3267583 = 4901375) B4901375
theorem B653073785 : Blo 1811607 653073785 := bstep (se 2 (by rfl) ⟨244902669, by rfl⟩ : syracuseStep 653073785 = 489805339) B489805339
theorem B2039503 : Blo 1811607 2039503 := bstep (se 1 (by rfl) ⟨1529627, by rfl⟩ : syracuseStep 2039503 = 3059255) B3059255
theorem B6881183 : Blo 1811607 6881183 := bstep (se 1 (by rfl) ⟨5160887, by rfl⟩ : syracuseStep 6881183 = 10321775) B10321775
theorem B70672427 : Blo 1811607 70672427 := bstep (se 1 (by rfl) ⟨53004320, by rfl⟩ : syracuseStep 70672427 = 106008641) B106008641
theorem B1017782765 : Blo 1811607 1017782765 := bstep (se 3 (by rfl) ⟨190834268, by rfl⟩ : syracuseStep 1017782765 = 381668537) B381668537
theorem B11929483 : Blo 1811607 11929483 := bstep (se 1 (by rfl) ⟨8947112, by rfl⟩ : syracuseStep 11929483 = 17894225) B17894225
theorem B435382523 : Blo 1811607 435382523 := bstep (se 1 (by rfl) ⟨326536892, by rfl⟩ : syracuseStep 435382523 = 653073785) B653073785
theorem B17427109 : Blo 1811607 17427109 := bstep (se 4 (by rfl) ⟨1633791, by rfl⟩ : syracuseStep 17427109 = 3267583) B3267583
theorem B100576133 : Blo 1811607 100576133 := bstep (se 4 (by rfl) ⟨9429012, by rfl⟩ : syracuseStep 100576133 = 18858025) B18858025
theorem B134148257 : Blo 1811607 134148257 := bstep (se 2 (by rfl) ⟨50305596, by rfl⟩ : syracuseStep 134148257 = 100611193) B100611193
theorem B3060139 : Blo 1811607 3060139 := bstep (se 1 (by rfl) ⟨2295104, by rfl⟩ : syracuseStep 3060139 = 4590209) B4590209
theorem B4077287 : Blo 1811607 4077287 := bstep (se 1 (by rfl) ⟨3057965, by rfl⟩ : syracuseStep 4077287 = 6115931) B6115931
theorem B9172763 : Blo 1811607 9172763 := bstep (se 1 (by rfl) ⟨6879572, by rfl⟩ : syracuseStep 9172763 = 13759145) B13759145
theorem B29792639 : Blo 1811607 29792639 := bstep (se 1 (by rfl) ⟨22344479, by rfl⟩ : syracuseStep 29792639 = 44688959) B44688959
theorem B4078079 : Blo 1811607 4078079 := bstep (se 1 (by rfl) ⟨3058559, by rfl⟩ : syracuseStep 4078079 = 6117119) B6117119
theorem B17414999 : Blo 1811607 17414999 := bstep (se 1 (by rfl) ⟨13061249, by rfl⟩ : syracuseStep 17414999 = 26122499) B26122499
theorem B4652159 : Blo 1811607 4652159 := bstep (se 1 (by rfl) ⟨3489119, by rfl⟩ : syracuseStep 4652159 = 6978239) B6978239
theorem B6118847 : Blo 1811607 6118847 := bstep (se 1 (by rfl) ⟨4589135, by rfl⟩ : syracuseStep 6118847 = 9178271) B9178271
theorem B2719337 : Blo 1811607 2719337 := bstep (se 2 (by rfl) ⟨1019751, by rfl⟩ : syracuseStep 2719337 = 2039503) B2039503
theorem B34823843 : Blo 1811607 34823843 := bstep (se 1 (by rfl) ⟨26117882, by rfl⟩ : syracuseStep 34823843 = 52235765) B52235765
theorem B4587455 : Blo 1811607 4587455 := bstep (se 1 (by rfl) ⟨3440591, by rfl⟩ : syracuseStep 4587455 = 6881183) B6881183
theorem B11771887 : Blo 1811607 11771887 := bstep (se 1 (by rfl) ⟨8828915, by rfl⟩ : syracuseStep 11771887 = 17657831) B17657831
theorem B89432171 : Blo 1811607 89432171 := bstep (se 1 (by rfl) ⟨67074128, by rfl⟩ : syracuseStep 89432171 = 134148257) B134148257
theorem B4080185 : Blo 1811607 4080185 := bstep (se 2 (by rfl) ⟨1530069, by rfl⟩ : syracuseStep 4080185 = 3060139) B3060139
theorem B11609999 : Blo 1811607 11609999 := bstep (se 1 (by rfl) ⟨8707499, by rfl⟩ : syracuseStep 11609999 = 17414999) B17414999
theorem B1812891 : Blo 1811607 1812891 := bstep (se 1 (by rfl) ⟨1359668, by rfl⟩ : syracuseStep 1812891 = 2719337) B2719337
theorem B3058303 : Blo 1811607 3058303 := bstep (se 1 (by rfl) ⟨2293727, by rfl⟩ : syracuseStep 3058303 = 4587455) B4587455
theorem B47114951 : Blo 1811607 47114951 := bstep (se 1 (by rfl) ⟨35336213, by rfl⟩ : syracuseStep 47114951 = 70672427) B70672427
theorem B678521843 : Blo 1811607 678521843 := bstep (se 1 (by rfl) ⟨508891382, by rfl⟩ : syracuseStep 678521843 = 1017782765) B1017782765
theorem B23236145 : Blo 1811607 23236145 := bstep (se 2 (by rfl) ⟨8713554, by rfl⟩ : syracuseStep 23236145 = 17427109) B17427109
theorem B6115175 : Blo 1811607 6115175 := bstep (se 1 (by rfl) ⟨4586381, by rfl⟩ : syracuseStep 6115175 = 9172763) B9172763
theorem B49623029 : Blo 1811607 49623029 := bstep (se 5 (by rfl) ⟨2326079, by rfl⟩ : syracuseStep 49623029 = 4652159) B4652159
theorem B290255015 : Blo 1811607 290255015 := bstep (se 1 (by rfl) ⟨217691261, by rfl⟩ : syracuseStep 290255015 = 435382523) B435382523
theorem B19861759 : Blo 1811607 19861759 := bstep (se 1 (by rfl) ⟨14896319, by rfl⟩ : syracuseStep 19861759 = 29792639) B29792639
theorem B15905977 : Blo 1811607 15905977 := bstep (se 2 (by rfl) ⟨5964741, by rfl⟩ : syracuseStep 15905977 = 11929483) B11929483
theorem B2718191 : Blo 1811607 2718191 := bstep (se 1 (by rfl) ⟨2038643, by rfl⟩ : syracuseStep 2718191 = 4077287) B4077287
theorem B2718719 : Blo 1811607 2718719 := bstep (se 1 (by rfl) ⟨2039039, by rfl⟩ : syracuseStep 2718719 = 4078079) B4078079
theorem B67050755 : Blo 1811607 67050755 := bstep (se 1 (by rfl) ⟨50288066, by rfl⟩ : syracuseStep 67050755 = 100576133) B100576133
theorem B4079231 : Blo 1811607 4079231 := bstep (se 1 (by rfl) ⟨3059423, by rfl⟩ : syracuseStep 4079231 = 6118847) B6118847
theorem B23215895 : Blo 1811607 23215895 := bstep (se 1 (by rfl) ⟨17411921, by rfl⟩ : syracuseStep 23215895 = 34823843) B34823843
theorem B15695849 : Blo 1811607 15695849 := bstep (se 2 (by rfl) ⟨5885943, by rfl⟩ : syracuseStep 15695849 = 11771887) B11771887
theorem B59621447 : Blo 1811607 59621447 := bstep (se 1 (by rfl) ⟨44716085, by rfl⟩ : syracuseStep 59621447 = 89432171) B89432171
theorem B193503343 : Blo 1811607 193503343 := bstep (se 1 (by rfl) ⟨145127507, by rfl⟩ : syracuseStep 193503343 = 290255015) B290255015
theorem B2720123 : Blo 1811607 2720123 := bstep (se 1 (by rfl) ⟨2040092, by rfl⟩ : syracuseStep 2720123 = 4080185) B4080185
theorem B1812127 : Blo 1811607 1812127 := bstep (se 1 (by rfl) ⟨1359095, by rfl⟩ : syracuseStep 1812127 = 2718191) B2718191
theorem B452347895 : Blo 1811607 452347895 := bstep (se 1 (by rfl) ⟨339260921, by rfl⟩ : syracuseStep 452347895 = 678521843) B678521843
theorem B1812479 : Blo 1811607 1812479 := bstep (se 1 (by rfl) ⟨1359359, by rfl⟩ : syracuseStep 1812479 = 2718719) B2718719
theorem B15477263 : Blo 1811607 15477263 := bstep (se 1 (by rfl) ⟨11607947, by rfl⟩ : syracuseStep 15477263 = 23215895) B23215895
theorem B10463899 : Blo 1811607 10463899 := bstep (se 1 (by rfl) ⟨7847924, by rfl⟩ : syracuseStep 10463899 = 15695849) B15695849
theorem B33082019 : Blo 1811607 33082019 := bstep (se 1 (by rfl) ⟨24811514, by rfl⟩ : syracuseStep 33082019 = 49623029) B49623029
theorem B84831877 : Blo 1811607 84831877 := bstep (se 4 (by rfl) ⟨7952988, by rfl⟩ : syracuseStep 84831877 = 15905977) B15905977
theorem B502559477 : Blo 1811607 502559477 := bstep (se 5 (by rfl) ⟨23557475, by rfl⟩ : syracuseStep 502559477 = 47114951) B47114951
theorem B44700503 : Blo 1811607 44700503 := bstep (se 1 (by rfl) ⟨33525377, by rfl⟩ : syracuseStep 44700503 = 67050755) B67050755
theorem B4076783 : Blo 1811607 4076783 := bstep (se 1 (by rfl) ⟨3057587, by rfl⟩ : syracuseStep 4076783 = 6115175) B6115175
theorem B26482345 : Blo 1811607 26482345 := bstep (se 2 (by rfl) ⟨9930879, by rfl⟩ : syracuseStep 26482345 = 19861759) B19861759
theorem B4077737 : Blo 1811607 4077737 := bstep (se 2 (by rfl) ⟨1529151, by rfl⟩ : syracuseStep 4077737 = 3058303) B3058303
theorem B7739999 : Blo 1811607 7739999 := bstep (se 1 (by rfl) ⟨5804999, by rfl⟩ : syracuseStep 7739999 = 11609999) B11609999
theorem B15490763 : Blo 1811607 15490763 := bstep (se 1 (by rfl) ⟨11618072, by rfl⟩ : syracuseStep 15490763 = 23236145) B23236145
theorem B2719487 : Blo 1811607 2719487 := bstep (se 1 (by rfl) ⟨2039615, by rfl⟩ : syracuseStep 2719487 = 4079231) B4079231
theorem B158990525 : Blo 1811607 158990525 := bstep (se 3 (by rfl) ⟨29810723, by rfl⟩ : syracuseStep 158990525 = 59621447) B59621447
theorem B13951865 : Blo 1811607 13951865 := bstep (se 2 (by rfl) ⟨5231949, by rfl⟩ : syracuseStep 13951865 = 10463899) B10463899
theorem B301565263 : Blo 1811607 301565263 := bstep (se 1 (by rfl) ⟨226173947, by rfl⟩ : syracuseStep 301565263 = 452347895) B452347895
theorem B22054679 : Blo 1811607 22054679 := bstep (se 1 (by rfl) ⟨16541009, by rfl⟩ : syracuseStep 22054679 = 33082019) B33082019
theorem B113109169 : Blo 1811607 113109169 := bstep (se 2 (by rfl) ⟨42415938, by rfl⟩ : syracuseStep 113109169 = 84831877) B84831877
theorem B1812991 : Blo 1811607 1812991 := bstep (se 1 (by rfl) ⟨1359743, by rfl⟩ : syracuseStep 1812991 = 2719487) B2719487
theorem B1813415 : Blo 1811607 1813415 := bstep (se 1 (by rfl) ⟨1360061, by rfl⟩ : syracuseStep 1813415 = 2720123) B2720123
theorem B335039651 : Blo 1811607 335039651 := bstep (se 1 (by rfl) ⟨251279738, by rfl⟩ : syracuseStep 335039651 = 502559477) B502559477
theorem B564956693 : Blo 1811607 564956693 := bstep (se 6 (by rfl) ⟨13241172, by rfl⟩ : syracuseStep 564956693 = 26482345) B26482345
theorem B10318175 : Blo 1811607 10318175 := bstep (se 1 (by rfl) ⟨7738631, by rfl⟩ : syracuseStep 10318175 = 15477263) B15477263
theorem B10327175 : Blo 1811607 10327175 := bstep (se 1 (by rfl) ⟨7745381, by rfl⟩ : syracuseStep 10327175 = 15490763) B15490763
theorem B258004457 : Blo 1811607 258004457 := bstep (se 2 (by rfl) ⟨96751671, by rfl⟩ : syracuseStep 258004457 = 193503343) B193503343
theorem B2717855 : Blo 1811607 2717855 := bstep (se 1 (by rfl) ⟨2038391, by rfl⟩ : syracuseStep 2717855 = 4076783) B4076783
theorem B2718491 : Blo 1811607 2718491 := bstep (se 1 (by rfl) ⟨2038868, by rfl⟩ : syracuseStep 2718491 = 4077737) B4077737
theorem B5159999 : Blo 1811607 5159999 := bstep (se 1 (by rfl) ⟨3869999, by rfl⟩ : syracuseStep 5159999 = 7739999) B7739999
theorem B119201341 : Blo 1811607 119201341 := bstep (se 3 (by rfl) ⟨22350251, by rfl⟩ : syracuseStep 119201341 = 44700503) B44700503
theorem B1811903 : Blo 1811607 1811903 := bstep (se 1 (by rfl) ⟨1358927, by rfl⟩ : syracuseStep 1811903 = 2717855) B2717855
theorem B1812327 : Blo 1811607 1812327 := bstep (se 1 (by rfl) ⟨1359245, by rfl⟩ : syracuseStep 1812327 = 2718491) B2718491
theorem B158935121 : Blo 1811607 158935121 := bstep (se 2 (by rfl) ⟨59600670, by rfl⟩ : syracuseStep 158935121 = 119201341) B119201341
theorem B376637795 : Blo 1811607 376637795 := bstep (se 1 (by rfl) ⟨282478346, by rfl⟩ : syracuseStep 376637795 = 564956693) B564956693
theorem B9301243 : Blo 1811607 9301243 := bstep (se 1 (by rfl) ⟨6975932, by rfl⟩ : syracuseStep 9301243 = 13951865) B13951865
theorem B6884783 : Blo 1811607 6884783 := bstep (se 1 (by rfl) ⟨5163587, by rfl⟩ : syracuseStep 6884783 = 10327175) B10327175
theorem B172002971 : Blo 1811607 172002971 := bstep (se 1 (by rfl) ⟨129002228, by rfl⟩ : syracuseStep 172002971 = 258004457) B258004457
theorem B223359767 : Blo 1811607 223359767 := bstep (se 1 (by rfl) ⟨167519825, by rfl⟩ : syracuseStep 223359767 = 335039651) B335039651
theorem B105993683 : Blo 1811607 105993683 := bstep (se 1 (by rfl) ⟨79495262, by rfl⟩ : syracuseStep 105993683 = 158990525) B158990525
theorem B6878783 : Blo 1811607 6878783 := bstep (se 1 (by rfl) ⟨5159087, by rfl⟩ : syracuseStep 6878783 = 10318175) B10318175
theorem B150812225 : Blo 1811607 150812225 := bstep (se 2 (by rfl) ⟨56554584, by rfl⟩ : syracuseStep 150812225 = 113109169) B113109169
theorem B14703119 : Blo 1811607 14703119 := bstep (se 1 (by rfl) ⟨11027339, by rfl⟩ : syracuseStep 14703119 = 22054679) B22054679
theorem B402087017 : Blo 1811607 402087017 := bstep (se 2 (by rfl) ⟨150782631, by rfl⟩ : syracuseStep 402087017 = 301565263) B301565263
theorem B3439999 : Blo 1811607 3439999 := bstep (se 1 (by rfl) ⟨2579999, by rfl⟩ : syracuseStep 3439999 = 5159999) B5159999
theorem B148906511 : Blo 1811607 148906511 := bstep (se 1 (by rfl) ⟨111679883, by rfl⟩ : syracuseStep 148906511 = 223359767) B223359767
theorem B100541483 : Blo 1811607 100541483 := bstep (se 1 (by rfl) ⟨75406112, by rfl⟩ : syracuseStep 100541483 = 150812225) B150812225
theorem B105956747 : Blo 1811607 105956747 := bstep (se 1 (by rfl) ⟨79467560, by rfl⟩ : syracuseStep 105956747 = 158935121) B158935121
theorem B4589855 : Blo 1811607 4589855 := bstep (se 1 (by rfl) ⟨3442391, by rfl⟩ : syracuseStep 4589855 = 6884783) B6884783
theorem B9802079 : Blo 1811607 9802079 := bstep (se 1 (by rfl) ⟨7351559, by rfl⟩ : syracuseStep 9802079 = 14703119) B14703119
theorem B458674589 : Blo 1811607 458674589 := bstep (se 3 (by rfl) ⟨86001485, by rfl⟩ : syracuseStep 458674589 = 172002971) B172002971
theorem B70662455 : Blo 1811607 70662455 := bstep (se 1 (by rfl) ⟨52996841, by rfl⟩ : syracuseStep 70662455 = 105993683) B105993683
theorem B4585855 : Blo 1811607 4585855 := bstep (se 1 (by rfl) ⟨3439391, by rfl⟩ : syracuseStep 4585855 = 6878783) B6878783
theorem B251091863 : Blo 1811607 251091863 := bstep (se 1 (by rfl) ⟨188318897, by rfl⟩ : syracuseStep 251091863 = 376637795) B376637795
theorem B12401657 : Blo 1811607 12401657 := bstep (se 2 (by rfl) ⟨4650621, by rfl⟩ : syracuseStep 12401657 = 9301243) B9301243
theorem B4586665 : Blo 1811607 4586665 := bstep (se 2 (by rfl) ⟨1719999, by rfl⟩ : syracuseStep 4586665 = 3439999) B3439999
theorem B268058011 : Blo 1811607 268058011 := bstep (se 1 (by rfl) ⟨201043508, by rfl⟩ : syracuseStep 268058011 = 402087017) B402087017
theorem B305783059 : Blo 1811607 305783059 := bstep (se 1 (by rfl) ⟨229337294, by rfl⟩ : syracuseStep 305783059 = 458674589) B458674589
theorem B99271007 : Blo 1811607 99271007 := bstep (se 1 (by rfl) ⟨74453255, by rfl⟩ : syracuseStep 99271007 = 148906511) B148906511
theorem B67027655 : Blo 1811607 67027655 := bstep (se 1 (by rfl) ⟨50270741, by rfl⟩ : syracuseStep 67027655 = 100541483) B100541483
theorem B357410681 : Blo 1811607 357410681 := bstep (se 2 (by rfl) ⟨134029005, by rfl⟩ : syracuseStep 357410681 = 268058011) B268058011
theorem B8267771 : Blo 1811607 8267771 := bstep (se 1 (by rfl) ⟨6200828, by rfl⟩ : syracuseStep 8267771 = 12401657) B12401657
theorem B6114473 : Blo 1811607 6114473 := bstep (se 2 (by rfl) ⟨2292927, by rfl⟩ : syracuseStep 6114473 = 4585855) B4585855
theorem B3059903 : Blo 1811607 3059903 := bstep (se 1 (by rfl) ⟨2294927, by rfl⟩ : syracuseStep 3059903 = 4589855) B4589855
theorem B47108303 : Blo 1811607 47108303 := bstep (se 1 (by rfl) ⟨35331227, by rfl⟩ : syracuseStep 47108303 = 70662455) B70662455
theorem B6115553 : Blo 1811607 6115553 := bstep (se 2 (by rfl) ⟨2293332, by rfl⟩ : syracuseStep 6115553 = 4586665) B4586665
theorem B6534719 : Blo 1811607 6534719 := bstep (se 1 (by rfl) ⟨4901039, by rfl⟩ : syracuseStep 6534719 = 9802079) B9802079
theorem B70637831 : Blo 1811607 70637831 := bstep (se 1 (by rfl) ⟨52978373, by rfl⟩ : syracuseStep 70637831 = 105956747) B105956747
theorem B167394575 : Blo 1811607 167394575 := bstep (se 1 (by rfl) ⟨125545931, by rfl⟩ : syracuseStep 167394575 = 251091863) B251091863
theorem B2039935 : Blo 1811607 2039935 := bstep (se 1 (by rfl) ⟨1529951, by rfl⟩ : syracuseStep 2039935 = 3059903) B3059903
theorem B238273787 : Blo 1811607 238273787 := bstep (se 1 (by rfl) ⟨178705340, by rfl⟩ : syracuseStep 238273787 = 357410681) B357410681
theorem B22047389 : Blo 1811607 22047389 := bstep (se 3 (by rfl) ⟨4133885, by rfl⟩ : syracuseStep 22047389 = 8267771) B8267771
theorem B407710745 : Blo 1811607 407710745 := bstep (se 2 (by rfl) ⟨152891529, by rfl⟩ : syracuseStep 407710745 = 305783059) B305783059
theorem B47091887 : Blo 1811607 47091887 := bstep (se 1 (by rfl) ⟨35318915, by rfl⟩ : syracuseStep 47091887 = 70637831) B70637831
theorem B4076315 : Blo 1811607 4076315 := bstep (se 1 (by rfl) ⟨3057236, by rfl⟩ : syracuseStep 4076315 = 6114473) B6114473
theorem B111596383 : Blo 1811607 111596383 := bstep (se 1 (by rfl) ⟨83697287, by rfl⟩ : syracuseStep 111596383 = 167394575) B167394575
theorem B31405535 : Blo 1811607 31405535 := bstep (se 1 (by rfl) ⟨23554151, by rfl⟩ : syracuseStep 31405535 = 47108303) B47108303
theorem B4077035 : Blo 1811607 4077035 := bstep (se 1 (by rfl) ⟨3057776, by rfl⟩ : syracuseStep 4077035 = 6115553) B6115553
theorem B66180671 : Blo 1811607 66180671 := bstep (se 1 (by rfl) ⟨49635503, by rfl⟩ : syracuseStep 66180671 = 99271007) B99271007
theorem B44685103 : Blo 1811607 44685103 := bstep (se 1 (by rfl) ⟨33513827, by rfl⟩ : syracuseStep 44685103 = 67027655) B67027655
theorem B4356479 : Blo 1811607 4356479 := bstep (se 1 (by rfl) ⟨3267359, by rfl⟩ : syracuseStep 4356479 = 6534719) B6534719
theorem B2719913 : Blo 1811607 2719913 := bstep (se 2 (by rfl) ⟨1019967, by rfl⟩ : syracuseStep 2719913 = 2039935) B2039935
theorem B14698259 : Blo 1811607 14698259 := bstep (se 1 (by rfl) ⟨11023694, by rfl⟩ : syracuseStep 14698259 = 22047389) B22047389
theorem B31394591 : Blo 1811607 31394591 := bstep (se 1 (by rfl) ⟨23545943, by rfl⟩ : syracuseStep 31394591 = 47091887) B47091887
theorem B148795177 : Blo 1811607 148795177 := bstep (se 2 (by rfl) ⟨55798191, by rfl⟩ : syracuseStep 148795177 = 111596383) B111596383
theorem B2904319 : Blo 1811607 2904319 := bstep (se 1 (by rfl) ⟨2178239, by rfl⟩ : syracuseStep 2904319 = 4356479) B4356479
theorem B271807163 : Blo 1811607 271807163 := bstep (se 1 (by rfl) ⟨203855372, by rfl⟩ : syracuseStep 271807163 = 407710745) B407710745
theorem B2717543 : Blo 1811607 2717543 := bstep (se 1 (by rfl) ⟨2038157, by rfl⟩ : syracuseStep 2717543 = 4076315) B4076315
theorem B158849191 : Blo 1811607 158849191 := bstep (se 1 (by rfl) ⟨119136893, by rfl⟩ : syracuseStep 158849191 = 238273787) B238273787
theorem B20937023 : Blo 1811607 20937023 := bstep (se 1 (by rfl) ⟨15702767, by rfl⟩ : syracuseStep 20937023 = 31405535) B31405535
theorem B2718023 : Blo 1811607 2718023 := bstep (se 1 (by rfl) ⟨2038517, by rfl⟩ : syracuseStep 2718023 = 4077035) B4077035
theorem B44120447 : Blo 1811607 44120447 := bstep (se 1 (by rfl) ⟨33090335, by rfl⟩ : syracuseStep 44120447 = 66180671) B66180671
theorem B59580137 : Blo 1811607 59580137 := bstep (se 2 (by rfl) ⟨22342551, by rfl⟩ : syracuseStep 59580137 = 44685103) B44685103
theorem B9798839 : Blo 1811607 9798839 := bstep (se 1 (by rfl) ⟨7349129, by rfl⟩ : syracuseStep 9798839 = 14698259) B14698259
theorem B1811695 : Blo 1811607 1811695 := bstep (se 1 (by rfl) ⟨1358771, by rfl⟩ : syracuseStep 1811695 = 2717543) B2717543
theorem B1812015 : Blo 1811607 1812015 := bstep (se 1 (by rfl) ⟨1359011, by rfl⟩ : syracuseStep 1812015 = 2718023) B2718023
theorem B1813275 : Blo 1811607 1813275 := bstep (se 1 (by rfl) ⟨1359956, by rfl⟩ : syracuseStep 1813275 = 2719913) B2719913
theorem B847195685 : Blo 1811607 847195685 := bstep (se 4 (by rfl) ⟨79424595, by rfl⟩ : syracuseStep 847195685 = 158849191) B158849191
theorem B29413631 : Blo 1811607 29413631 := bstep (se 1 (by rfl) ⟨22060223, by rfl⟩ : syracuseStep 29413631 = 44120447) B44120447
theorem B158880365 : Blo 1811607 158880365 := bstep (se 3 (by rfl) ⟨29790068, by rfl⟩ : syracuseStep 158880365 = 59580137) B59580137
theorem B181204775 : Blo 1811607 181204775 := bstep (se 1 (by rfl) ⟨135903581, by rfl⟩ : syracuseStep 181204775 = 271807163) B271807163
theorem B15489701 : Blo 1811607 15489701 := bstep (se 4 (by rfl) ⟨1452159, by rfl⟩ : syracuseStep 15489701 = 2904319) B2904319
theorem B13958015 : Blo 1811607 13958015 := bstep (se 1 (by rfl) ⟨10468511, by rfl⟩ : syracuseStep 13958015 = 20937023) B20937023
theorem B20929727 : Blo 1811607 20929727 := bstep (se 1 (by rfl) ⟨15697295, by rfl⟩ : syracuseStep 20929727 = 31394591) B31394591
theorem B198393569 : Blo 1811607 198393569 := bstep (se 2 (by rfl) ⟨74397588, by rfl⟩ : syracuseStep 198393569 = 148795177) B148795177
theorem B13953151 : Blo 1811607 13953151 := bstep (se 1 (by rfl) ⟨10464863, by rfl⟩ : syracuseStep 13953151 = 20929727) B20929727
theorem B132262379 : Blo 1811607 132262379 := bstep (se 1 (by rfl) ⟨99196784, by rfl⟩ : syracuseStep 132262379 = 198393569) B198393569
theorem B6532559 : Blo 1811607 6532559 := bstep (se 1 (by rfl) ⟨4899419, by rfl⟩ : syracuseStep 6532559 = 9798839) B9798839
theorem B120803183 : Blo 1811607 120803183 := bstep (se 1 (by rfl) ⟨90602387, by rfl⟩ : syracuseStep 120803183 = 181204775) B181204775
theorem B10326467 : Blo 1811607 10326467 := bstep (se 1 (by rfl) ⟨7744850, by rfl⟩ : syracuseStep 10326467 = 15489701) B15489701
theorem B37221373 : Blo 1811607 37221373 := bstep (se 3 (by rfl) ⟨6979007, by rfl⟩ : syracuseStep 37221373 = 13958015) B13958015
theorem B19609087 : Blo 1811607 19609087 := bstep (se 1 (by rfl) ⟨14706815, by rfl⟩ : syracuseStep 19609087 = 29413631) B29413631
theorem B105920243 : Blo 1811607 105920243 := bstep (se 1 (by rfl) ⟨79440182, by rfl⟩ : syracuseStep 105920243 = 158880365) B158880365
theorem B564797123 : Blo 1811607 564797123 := bstep (se 1 (by rfl) ⟨423597842, by rfl⟩ : syracuseStep 564797123 = 847195685) B847195685
theorem B18604201 : Blo 1811607 18604201 := bstep (se 2 (by rfl) ⟨6976575, by rfl⟩ : syracuseStep 18604201 = 13953151) B13953151
theorem B49628497 : Blo 1811607 49628497 := bstep (se 2 (by rfl) ⟨18610686, by rfl⟩ : syracuseStep 49628497 = 37221373) B37221373
theorem B376531415 : Blo 1811607 376531415 := bstep (se 1 (by rfl) ⟨282398561, by rfl⟩ : syracuseStep 376531415 = 564797123) B564797123
theorem B6884311 : Blo 1811607 6884311 := bstep (se 1 (by rfl) ⟨5163233, by rfl⟩ : syracuseStep 6884311 = 10326467) B10326467
theorem B88174919 : Blo 1811607 88174919 := bstep (se 1 (by rfl) ⟨66131189, by rfl⟩ : syracuseStep 88174919 = 132262379) B132262379
theorem B26145449 : Blo 1811607 26145449 := bstep (se 2 (by rfl) ⟨9804543, by rfl⟩ : syracuseStep 26145449 = 19609087) B19609087
theorem B4355039 : Blo 1811607 4355039 := bstep (se 1 (by rfl) ⟨3266279, by rfl⟩ : syracuseStep 4355039 = 6532559) B6532559
theorem B70613495 : Blo 1811607 70613495 := bstep (se 1 (by rfl) ⟨52960121, by rfl⟩ : syracuseStep 70613495 = 105920243) B105920243
theorem B80535455 : Blo 1811607 80535455 := bstep (se 1 (by rfl) ⟨60401591, by rfl⟩ : syracuseStep 80535455 = 120803183) B120803183
theorem B24805601 : Blo 1811607 24805601 := bstep (se 2 (by rfl) ⟨9302100, by rfl⟩ : syracuseStep 24805601 = 18604201) B18604201
theorem B251020943 : Blo 1811607 251020943 := bstep (se 1 (by rfl) ⟨188265707, by rfl⟩ : syracuseStep 251020943 = 376531415) B376531415
theorem B2903359 : Blo 1811607 2903359 := bstep (se 1 (by rfl) ⟨2177519, by rfl⟩ : syracuseStep 2903359 = 4355039) B4355039
theorem B9179081 : Blo 1811607 9179081 := bstep (se 2 (by rfl) ⟨3442155, by rfl⟩ : syracuseStep 9179081 = 6884311) B6884311
theorem B47075663 : Blo 1811607 47075663 := bstep (se 1 (by rfl) ⟨35306747, by rfl⟩ : syracuseStep 47075663 = 70613495) B70613495
theorem B66171329 : Blo 1811607 66171329 := bstep (se 2 (by rfl) ⟨24814248, by rfl⟩ : syracuseStep 66171329 = 49628497) B49628497
theorem B58783279 : Blo 1811607 58783279 := bstep (se 1 (by rfl) ⟨44087459, by rfl⟩ : syracuseStep 58783279 = 88174919) B88174919
theorem B17430299 : Blo 1811607 17430299 := bstep (se 1 (by rfl) ⟨13072724, by rfl⟩ : syracuseStep 17430299 = 26145449) B26145449
theorem B53690303 : Blo 1811607 53690303 := bstep (se 1 (by rfl) ⟨40267727, by rfl⟩ : syracuseStep 53690303 = 80535455) B80535455
theorem B31383775 : Blo 1811607 31383775 := bstep (se 1 (by rfl) ⟨23537831, by rfl⟩ : syracuseStep 31383775 = 47075663) B47075663
theorem B44114219 : Blo 1811607 44114219 := bstep (se 1 (by rfl) ⟨33085664, by rfl⟩ : syracuseStep 44114219 = 66171329) B66171329
theorem B167347295 : Blo 1811607 167347295 := bstep (se 1 (by rfl) ⟨125510471, by rfl⟩ : syracuseStep 167347295 = 251020943) B251020943
theorem B35793535 : Blo 1811607 35793535 := bstep (se 1 (by rfl) ⟨26845151, by rfl⟩ : syracuseStep 35793535 = 53690303) B53690303
theorem B11620199 : Blo 1811607 11620199 := bstep (se 1 (by rfl) ⟨8715149, by rfl⟩ : syracuseStep 11620199 = 17430299) B17430299
theorem B3871145 : Blo 1811607 3871145 := bstep (se 2 (by rfl) ⟨1451679, by rfl⟩ : syracuseStep 3871145 = 2903359) B2903359
theorem B78377705 : Blo 1811607 78377705 := bstep (se 2 (by rfl) ⟨29391639, by rfl⟩ : syracuseStep 78377705 = 58783279) B58783279
theorem B16537067 : Blo 1811607 16537067 := bstep (se 1 (by rfl) ⟨12402800, by rfl⟩ : syracuseStep 16537067 = 24805601) B24805601
theorem B6119387 : Blo 1811607 6119387 := bstep (se 1 (by rfl) ⟨4589540, by rfl⟩ : syracuseStep 6119387 = 9179081) B9179081
theorem B29409479 : Blo 1811607 29409479 := bstep (se 1 (by rfl) ⟨22057109, by rfl⟩ : syracuseStep 29409479 = 44114219) B44114219
theorem B2580763 : Blo 1811607 2580763 := bstep (se 1 (by rfl) ⟨1935572, by rfl⟩ : syracuseStep 2580763 = 3871145) B3871145
theorem B41845033 : Blo 1811607 41845033 := bstep (se 2 (by rfl) ⟨15691887, by rfl⟩ : syracuseStep 41845033 = 31383775) B31383775
theorem B52251803 : Blo 1811607 52251803 := bstep (se 1 (by rfl) ⟨39188852, by rfl⟩ : syracuseStep 52251803 = 78377705) B78377705
theorem B7746799 : Blo 1811607 7746799 := bstep (se 1 (by rfl) ⟨5810099, by rfl⟩ : syracuseStep 7746799 = 11620199) B11620199
theorem B111564863 : Blo 1811607 111564863 := bstep (se 1 (by rfl) ⟨83673647, by rfl⟩ : syracuseStep 111564863 = 167347295) B167347295
theorem B47724713 : Blo 1811607 47724713 := bstep (se 2 (by rfl) ⟨17896767, by rfl⟩ : syracuseStep 47724713 = 35793535) B35793535
theorem B11024711 : Blo 1811607 11024711 := bstep (se 1 (by rfl) ⟨8268533, by rfl⟩ : syracuseStep 11024711 = 16537067) B16537067
theorem B4079591 : Blo 1811607 4079591 := bstep (se 1 (by rfl) ⟨3059693, by rfl⟩ : syracuseStep 4079591 = 6119387) B6119387
theorem B3441017 : Blo 1811607 3441017 := bstep (se 2 (by rfl) ⟨1290381, by rfl⟩ : syracuseStep 3441017 = 2580763) B2580763
theorem B74376575 : Blo 1811607 74376575 := bstep (se 1 (by rfl) ⟨55782431, by rfl⟩ : syracuseStep 74376575 = 111564863) B111564863
theorem B7349807 : Blo 1811607 7349807 := bstep (se 1 (by rfl) ⟨5512355, by rfl⟩ : syracuseStep 7349807 = 11024711) B11024711
theorem B34834535 : Blo 1811607 34834535 := bstep (se 1 (by rfl) ⟨26125901, by rfl⟩ : syracuseStep 34834535 = 52251803) B52251803
theorem B19606319 : Blo 1811607 19606319 := bstep (se 1 (by rfl) ⟨14704739, by rfl⟩ : syracuseStep 19606319 = 29409479) B29409479
theorem B55793377 : Blo 1811607 55793377 := bstep (se 2 (by rfl) ⟨20922516, by rfl⟩ : syracuseStep 55793377 = 41845033) B41845033
theorem B31816475 : Blo 1811607 31816475 := bstep (se 1 (by rfl) ⟨23862356, by rfl⟩ : syracuseStep 31816475 = 47724713) B47724713
theorem B10329065 : Blo 1811607 10329065 := bstep (se 2 (by rfl) ⟨3873399, by rfl⟩ : syracuseStep 10329065 = 7746799) B7746799
theorem B2719727 : Blo 1811607 2719727 := bstep (se 1 (by rfl) ⟨2039795, by rfl⟩ : syracuseStep 2719727 = 4079591) B4079591
theorem B2294011 : Blo 1811607 2294011 := bstep (se 1 (by rfl) ⟨1720508, by rfl⟩ : syracuseStep 2294011 = 3441017) B3441017
theorem B4899871 : Blo 1811607 4899871 := bstep (se 1 (by rfl) ⟨3674903, by rfl⟩ : syracuseStep 4899871 = 7349807) B7349807
theorem B21210983 : Blo 1811607 21210983 := bstep (se 1 (by rfl) ⟨15908237, by rfl⟩ : syracuseStep 21210983 = 31816475) B31816475
theorem B1813151 : Blo 1811607 1813151 := bstep (se 1 (by rfl) ⟨1359863, by rfl⟩ : syracuseStep 1813151 = 2719727) B2719727
theorem B13070879 : Blo 1811607 13070879 := bstep (se 1 (by rfl) ⟨9803159, by rfl⟩ : syracuseStep 13070879 = 19606319) B19606319
theorem B6886043 : Blo 1811607 6886043 := bstep (se 1 (by rfl) ⟨5164532, by rfl⟩ : syracuseStep 6886043 = 10329065) B10329065
theorem B49584383 : Blo 1811607 49584383 := bstep (se 1 (by rfl) ⟨37188287, by rfl⟩ : syracuseStep 49584383 = 74376575) B74376575
theorem B297564677 : Blo 1811607 297564677 := bstep (se 4 (by rfl) ⟨27896688, by rfl⟩ : syracuseStep 297564677 = 55793377) B55793377
theorem B23223023 : Blo 1811607 23223023 := bstep (se 1 (by rfl) ⟨17417267, by rfl⟩ : syracuseStep 23223023 = 34834535) B34834535
theorem B26132645 : Blo 1811607 26132645 := bstep (se 4 (by rfl) ⟨2449935, by rfl⟩ : syracuseStep 26132645 = 4899871) B4899871
theorem B14140655 : Blo 1811607 14140655 := bstep (se 1 (by rfl) ⟨10605491, by rfl⟩ : syracuseStep 14140655 = 21210983) B21210983
theorem B33056255 : Blo 1811607 33056255 := bstep (se 1 (by rfl) ⟨24792191, by rfl⟩ : syracuseStep 33056255 = 49584383) B49584383
theorem B3058681 : Blo 1811607 3058681 := bstep (se 2 (by rfl) ⟨1147005, by rfl⟩ : syracuseStep 3058681 = 2294011) B2294011
theorem B4590695 : Blo 1811607 4590695 := bstep (se 1 (by rfl) ⟨3443021, by rfl⟩ : syracuseStep 4590695 = 6886043) B6886043
theorem B8713919 : Blo 1811607 8713919 := bstep (se 1 (by rfl) ⟨6535439, by rfl⟩ : syracuseStep 8713919 = 13070879) B13070879
theorem B198376451 : Blo 1811607 198376451 := bstep (se 1 (by rfl) ⟨148782338, by rfl⟩ : syracuseStep 198376451 = 297564677) B297564677
theorem B15482015 : Blo 1811607 15482015 := bstep (se 1 (by rfl) ⟨11611511, by rfl⟩ : syracuseStep 15482015 = 23223023) B23223023
theorem B22037503 : Blo 1811607 22037503 := bstep (se 1 (by rfl) ⟨16528127, by rfl⟩ : syracuseStep 22037503 = 33056255) B33056255
theorem B23237117 : Blo 1811607 23237117 := bstep (se 3 (by rfl) ⟨4356959, by rfl⟩ : syracuseStep 23237117 = 8713919) B8713919
theorem B3060463 : Blo 1811607 3060463 := bstep (se 1 (by rfl) ⟨2295347, by rfl⟩ : syracuseStep 3060463 = 4590695) B4590695
theorem B17421763 : Blo 1811607 17421763 := bstep (se 1 (by rfl) ⟨13066322, by rfl⟩ : syracuseStep 17421763 = 26132645) B26132645
theorem B9427103 : Blo 1811607 9427103 := bstep (se 1 (by rfl) ⟨7070327, by rfl⟩ : syracuseStep 9427103 = 14140655) B14140655
theorem B4078241 : Blo 1811607 4078241 := bstep (se 2 (by rfl) ⟨1529340, by rfl⟩ : syracuseStep 4078241 = 3058681) B3058681
theorem B132250967 : Blo 1811607 132250967 := bstep (se 1 (by rfl) ⟨99188225, by rfl⟩ : syracuseStep 132250967 = 198376451) B198376451
theorem B10321343 : Blo 1811607 10321343 := bstep (se 1 (by rfl) ⟨7741007, by rfl⟩ : syracuseStep 10321343 = 15482015) B15482015
theorem B15491411 : Blo 1811607 15491411 := bstep (se 1 (by rfl) ⟨11618558, by rfl⟩ : syracuseStep 15491411 = 23237117) B23237117
theorem B4080617 : Blo 1811607 4080617 := bstep (se 2 (by rfl) ⟨1530231, by rfl⟩ : syracuseStep 4080617 = 3060463) B3060463
theorem B6284735 : Blo 1811607 6284735 := bstep (se 1 (by rfl) ⟨4713551, by rfl⟩ : syracuseStep 6284735 = 9427103) B9427103
theorem B23229017 : Blo 1811607 23229017 := bstep (se 2 (by rfl) ⟨8710881, by rfl⟩ : syracuseStep 23229017 = 17421763) B17421763
theorem B88167311 : Blo 1811607 88167311 := bstep (se 1 (by rfl) ⟨66125483, by rfl⟩ : syracuseStep 88167311 = 132250967) B132250967
theorem B29383337 : Blo 1811607 29383337 := bstep (se 2 (by rfl) ⟨11018751, by rfl⟩ : syracuseStep 29383337 = 22037503) B22037503
theorem B2718827 : Blo 1811607 2718827 := bstep (se 1 (by rfl) ⟨2039120, by rfl⟩ : syracuseStep 2718827 = 4078241) B4078241
theorem B6880895 : Blo 1811607 6880895 := bstep (se 1 (by rfl) ⟨5160671, by rfl⟩ : syracuseStep 6880895 = 10321343) B10321343
theorem B58778207 : Blo 1811607 58778207 := bstep (se 1 (by rfl) ⟨44083655, by rfl⟩ : syracuseStep 58778207 = 88167311) B88167311
theorem B2720411 : Blo 1811607 2720411 := bstep (se 1 (by rfl) ⟨2040308, by rfl⟩ : syracuseStep 2720411 = 4080617) B4080617
theorem B19588891 : Blo 1811607 19588891 := bstep (se 1 (by rfl) ⟨14691668, by rfl⟩ : syracuseStep 19588891 = 29383337) B29383337
theorem B1812551 : Blo 1811607 1812551 := bstep (se 1 (by rfl) ⟨1359413, by rfl⟩ : syracuseStep 1812551 = 2718827) B2718827
theorem B15486011 : Blo 1811607 15486011 := bstep (se 1 (by rfl) ⟨11614508, by rfl⟩ : syracuseStep 15486011 = 23229017) B23229017
theorem B4189823 : Blo 1811607 4189823 := bstep (se 1 (by rfl) ⟨3142367, by rfl⟩ : syracuseStep 4189823 = 6284735) B6284735
theorem B10327607 : Blo 1811607 10327607 := bstep (se 1 (by rfl) ⟨7745705, by rfl⟩ : syracuseStep 10327607 = 15491411) B15491411
theorem B4587263 : Blo 1811607 4587263 := bstep (se 1 (by rfl) ⟨3440447, by rfl⟩ : syracuseStep 4587263 = 6880895) B6880895
theorem B10324007 : Blo 1811607 10324007 := bstep (se 1 (by rfl) ⟨7743005, by rfl⟩ : syracuseStep 10324007 = 15486011) B15486011
theorem B26118521 : Blo 1811607 26118521 := bstep (se 2 (by rfl) ⟨9794445, by rfl⟩ : syracuseStep 26118521 = 19588891) B19588891
theorem B3058175 : Blo 1811607 3058175 := bstep (se 1 (by rfl) ⟨2293631, by rfl⟩ : syracuseStep 3058175 = 4587263) B4587263
theorem B39185471 : Blo 1811607 39185471 := bstep (se 1 (by rfl) ⟨29389103, by rfl⟩ : syracuseStep 39185471 = 58778207) B58778207
theorem B1813607 : Blo 1811607 1813607 := bstep (se 1 (by rfl) ⟨1360205, by rfl⟩ : syracuseStep 1813607 = 2720411) B2720411
theorem B6885071 : Blo 1811607 6885071 := bstep (se 1 (by rfl) ⟨5163803, by rfl⟩ : syracuseStep 6885071 = 10327607) B10327607
theorem B2793215 : Blo 1811607 2793215 := bstep (se 1 (by rfl) ⟨2094911, by rfl⟩ : syracuseStep 2793215 = 4189823) B4189823
theorem B6882671 : Blo 1811607 6882671 := bstep (se 1 (by rfl) ⟨5162003, by rfl⟩ : syracuseStep 6882671 = 10324007) B10324007
theorem B4590047 : Blo 1811607 4590047 := bstep (se 1 (by rfl) ⟨3442535, by rfl⟩ : syracuseStep 4590047 = 6885071) B6885071
theorem B1862143 : Blo 1811607 1862143 := bstep (se 1 (by rfl) ⟨1396607, by rfl⟩ : syracuseStep 1862143 = 2793215) B2793215
theorem B17412347 : Blo 1811607 17412347 := bstep (se 1 (by rfl) ⟨13059260, by rfl⟩ : syracuseStep 17412347 = 26118521) B26118521
theorem B2038783 : Blo 1811607 2038783 := bstep (se 1 (by rfl) ⟨1529087, by rfl⟩ : syracuseStep 2038783 = 3058175) B3058175
theorem B26123647 : Blo 1811607 26123647 := bstep (se 1 (by rfl) ⟨19592735, by rfl⟩ : syracuseStep 26123647 = 39185471) B39185471
theorem B11608231 : Blo 1811607 11608231 := bstep (se 1 (by rfl) ⟨8706173, by rfl⟩ : syracuseStep 11608231 = 17412347) B17412347
theorem B4588447 : Blo 1811607 4588447 := bstep (se 1 (by rfl) ⟨3441335, by rfl⟩ : syracuseStep 4588447 = 6882671) B6882671
theorem B9931429 : Blo 1811607 9931429 := bstep (se 4 (by rfl) ⟨931071, by rfl⟩ : syracuseStep 9931429 = 1862143) B1862143
theorem B3060031 : Blo 1811607 3060031 := bstep (se 1 (by rfl) ⟨2295023, by rfl⟩ : syracuseStep 3060031 = 4590047) B4590047
theorem B2718377 : Blo 1811607 2718377 := bstep (se 2 (by rfl) ⟨1019391, by rfl⟩ : syracuseStep 2718377 = 2038783) B2038783
theorem B34831529 : Blo 1811607 34831529 := bstep (se 2 (by rfl) ⟨13061823, by rfl⟩ : syracuseStep 34831529 = 26123647) B26123647
theorem B4080041 : Blo 1811607 4080041 := bstep (se 2 (by rfl) ⟨1530015, by rfl⟩ : syracuseStep 4080041 = 3060031) B3060031
theorem B1812251 : Blo 1811607 1812251 := bstep (se 1 (by rfl) ⟨1359188, by rfl⟩ : syracuseStep 1812251 = 2718377) B2718377
theorem B15477641 : Blo 1811607 15477641 := bstep (se 2 (by rfl) ⟨5804115, by rfl⟩ : syracuseStep 15477641 = 11608231) B11608231
theorem B23221019 : Blo 1811607 23221019 := bstep (se 1 (by rfl) ⟨17415764, by rfl⟩ : syracuseStep 23221019 = 34831529) B34831529
theorem B52967621 : Blo 1811607 52967621 := bstep (se 4 (by rfl) ⟨4965714, by rfl⟩ : syracuseStep 52967621 = 9931429) B9931429
theorem B6117929 : Blo 1811607 6117929 := bstep (se 2 (by rfl) ⟨2294223, by rfl⟩ : syracuseStep 6117929 = 4588447) B4588447
theorem B2720027 : Blo 1811607 2720027 := bstep (se 1 (by rfl) ⟨2040020, by rfl⟩ : syracuseStep 2720027 = 4080041) B4080041
theorem B35311747 : Blo 1811607 35311747 := bstep (se 1 (by rfl) ⟨26483810, by rfl⟩ : syracuseStep 35311747 = 52967621) B52967621
theorem B10318427 : Blo 1811607 10318427 := bstep (se 1 (by rfl) ⟨7738820, by rfl⟩ : syracuseStep 10318427 = 15477641) B15477641
theorem B15480679 : Blo 1811607 15480679 := bstep (se 1 (by rfl) ⟨11610509, by rfl⟩ : syracuseStep 15480679 = 23221019) B23221019
theorem B4078619 : Blo 1811607 4078619 := bstep (se 1 (by rfl) ⟨3058964, by rfl⟩ : syracuseStep 4078619 = 6117929) B6117929
theorem B47082329 : Blo 1811607 47082329 := bstep (se 2 (by rfl) ⟨17655873, by rfl⟩ : syracuseStep 47082329 = 35311747) B35311747
theorem B1813351 : Blo 1811607 1813351 := bstep (se 1 (by rfl) ⟨1360013, by rfl⟩ : syracuseStep 1813351 = 2720027) B2720027
theorem B20640905 : Blo 1811607 20640905 := bstep (se 2 (by rfl) ⟨7740339, by rfl⟩ : syracuseStep 20640905 = 15480679) B15480679
theorem B6878951 : Blo 1811607 6878951 := bstep (se 1 (by rfl) ⟨5159213, by rfl⟩ : syracuseStep 6878951 = 10318427) B10318427
theorem B2719079 : Blo 1811607 2719079 := bstep (se 1 (by rfl) ⟨2039309, by rfl⟩ : syracuseStep 2719079 = 4078619) B4078619
theorem B1812719 : Blo 1811607 1812719 := bstep (se 1 (by rfl) ⟨1359539, by rfl⟩ : syracuseStep 1812719 = 2719079) B2719079
theorem B31388219 : Blo 1811607 31388219 := bstep (se 1 (by rfl) ⟨23541164, by rfl⟩ : syracuseStep 31388219 = 47082329) B47082329
theorem B13760603 : Blo 1811607 13760603 := bstep (se 1 (by rfl) ⟨10320452, by rfl⟩ : syracuseStep 13760603 = 20640905) B20640905
theorem B4585967 : Blo 1811607 4585967 := bstep (se 1 (by rfl) ⟨3439475, by rfl⟩ : syracuseStep 4585967 = 6878951) B6878951
theorem B3057311 : Blo 1811607 3057311 := bstep (se 1 (by rfl) ⟨2292983, by rfl⟩ : syracuseStep 3057311 = 4585967) B4585967
theorem B20925479 : Blo 1811607 20925479 := bstep (se 1 (by rfl) ⟨15694109, by rfl⟩ : syracuseStep 20925479 = 31388219) B31388219
theorem B9173735 : Blo 1811607 9173735 := bstep (se 1 (by rfl) ⟨6880301, by rfl⟩ : syracuseStep 9173735 = 13760603) B13760603
theorem B6115823 : Blo 1811607 6115823 := bstep (se 1 (by rfl) ⟨4586867, by rfl⟩ : syracuseStep 6115823 = 9173735) B9173735
theorem B2038207 : Blo 1811607 2038207 := bstep (se 1 (by rfl) ⟨1528655, by rfl⟩ : syracuseStep 2038207 = 3057311) B3057311
theorem B13950319 : Blo 1811607 13950319 := bstep (se 1 (by rfl) ⟨10462739, by rfl⟩ : syracuseStep 13950319 = 20925479) B20925479
theorem B18600425 : Blo 1811607 18600425 := bstep (se 2 (by rfl) ⟨6975159, by rfl⟩ : syracuseStep 18600425 = 13950319) B13950319
theorem B4077215 : Blo 1811607 4077215 := bstep (se 1 (by rfl) ⟨3057911, by rfl⟩ : syracuseStep 4077215 = 6115823) B6115823
theorem B2717609 : Blo 1811607 2717609 := bstep (se 2 (by rfl) ⟨1019103, by rfl⟩ : syracuseStep 2717609 = 2038207) B2038207
theorem B1811739 : Blo 1811607 1811739 := bstep (se 1 (by rfl) ⟨1358804, by rfl⟩ : syracuseStep 1811739 = 2717609) B2717609
theorem B12400283 : Blo 1811607 12400283 := bstep (se 1 (by rfl) ⟨9300212, by rfl⟩ : syracuseStep 12400283 = 18600425) B18600425
theorem B2718143 : Blo 1811607 2718143 := bstep (se 1 (by rfl) ⟨2038607, by rfl⟩ : syracuseStep 2718143 = 4077215) B4077215
theorem B8266855 : Blo 1811607 8266855 := bstep (se 1 (by rfl) ⟨6200141, by rfl⟩ : syracuseStep 8266855 = 12400283) B12400283
theorem B1812095 : Blo 1811607 1812095 := bstep (se 1 (by rfl) ⟨1359071, by rfl⟩ : syracuseStep 1812095 = 2718143) B2718143
theorem B11022473 : Blo 1811607 11022473 := bstep (se 2 (by rfl) ⟨4133427, by rfl⟩ : syracuseStep 11022473 = 8266855) B8266855
theorem B7348315 : Blo 1811607 7348315 := bstep (se 1 (by rfl) ⟨5511236, by rfl⟩ : syracuseStep 7348315 = 11022473) B11022473
theorem B9797753 : Blo 1811607 9797753 := bstep (se 2 (by rfl) ⟨3674157, by rfl⟩ : syracuseStep 9797753 = 7348315) B7348315
theorem B6531835 : Blo 1811607 6531835 := bstep (se 1 (by rfl) ⟨4898876, by rfl⟩ : syracuseStep 6531835 = 9797753) B9797753
theorem B8709113 : Blo 1811607 8709113 := bstep (se 2 (by rfl) ⟨3265917, by rfl⟩ : syracuseStep 8709113 = 6531835) B6531835
theorem B5806075 : Blo 1811607 5806075 := bstep (se 1 (by rfl) ⟨4354556, by rfl⟩ : syracuseStep 5806075 = 8709113) B8709113
theorem B7741433 : Blo 1811607 7741433 := bstep (se 2 (by rfl) ⟨2903037, by rfl⟩ : syracuseStep 7741433 = 5806075) B5806075
theorem B20643821 : Blo 1811607 20643821 := bstep (se 3 (by rfl) ⟨3870716, by rfl⟩ : syracuseStep 20643821 = 7741433) B7741433
theorem B13762547 : Blo 1811607 13762547 := bstep (se 1 (by rfl) ⟨10321910, by rfl⟩ : syracuseStep 13762547 = 20643821) B20643821
theorem B9175031 : Blo 1811607 9175031 := bstep (se 1 (by rfl) ⟨6881273, by rfl⟩ : syracuseStep 9175031 = 13762547) B13762547
theorem B6116687 : Blo 1811607 6116687 := bstep (se 1 (by rfl) ⟨4587515, by rfl⟩ : syracuseStep 6116687 = 9175031) B9175031
theorem B4077791 : Blo 1811607 4077791 := bstep (se 1 (by rfl) ⟨3058343, by rfl⟩ : syracuseStep 4077791 = 6116687) B6116687
theorem B2718527 : Blo 1811607 2718527 := bstep (se 1 (by rfl) ⟨2038895, by rfl⟩ : syracuseStep 2718527 = 4077791) B4077791
theorem B1812351 : Blo 1811607 1812351 := bstep (se 1 (by rfl) ⟨1359263, by rfl⟩ : syracuseStep 1812351 = 2718527) B2718527

theorem C0 (j : ℕ) (h1 : 452901 ≤ j) (h2 : j ≤ 453401) : Blo 1811607 (4 * j + 3) := by
  interval_cases j
  · exact B1811607
  · exact B1811611
  · exact B1811615
  · exact B1811619
  · exact B1811623
  · exact B1811627
  · exact B1811631
  · exact B1811635
  · exact B1811639
  · exact B1811643
  · exact B1811647
  · exact B1811651
  · exact B1811655
  · exact B1811659
  · exact B1811663
  · exact B1811667
  · exact B1811671
  · exact B1811675
  · exact B1811679
  · exact B1811683
  · exact B1811687
  · exact B1811691
  · exact B1811695
  · exact B1811699
  · exact B1811703
  · exact B1811707
  · exact B1811711
  · exact B1811715
  · exact B1811719
  · exact B1811723
  · exact B1811727
  · exact B1811731
  · exact B1811735
  · exact B1811739
  · exact B1811743
  · exact B1811747
  · exact B1811751
  · exact B1811755
  · exact B1811759
  · exact B1811763
  · exact B1811767
  · exact B1811771
  · exact B1811775
  · exact B1811779
  · exact B1811783
  · exact B1811787
  · exact B1811791
  · exact B1811795
  · exact B1811799
  · exact B1811803
  · exact B1811807
  · exact B1811811
  · exact B1811815
  · exact B1811819
  · exact B1811823
  · exact B1811827
  · exact B1811831
  · exact B1811835
  · exact B1811839
  · exact B1811843
  · exact B1811847
  · exact B1811851
  · exact B1811855
  · exact B1811859
  · exact B1811863
  · exact B1811867
  · exact B1811871
  · exact B1811875
  · exact B1811879
  · exact B1811883
  · exact B1811887
  · exact B1811891
  · exact B1811895
  · exact B1811899
  · exact B1811903
  · exact B1811907
  · exact B1811911
  · exact B1811915
  · exact B1811919
  · exact B1811923
  · exact B1811927
  · exact B1811931
  · exact B1811935
  · exact B1811939
  · exact B1811943
  · exact B1811947
  · exact B1811951
  · exact B1811955
  · exact B1811959
  · exact B1811963
  · exact B1811967
  · exact B1811971
  · exact B1811975
  · exact B1811979
  · exact B1811983
  · exact B1811987
  · exact B1811991
  · exact B1811995
  · exact B1811999
  · exact B1812003
  · exact B1812007
  · exact B1812011
  · exact B1812015
  · exact B1812019
  · exact B1812023
  · exact B1812027
  · exact B1812031
  · exact B1812035
  · exact B1812039
  · exact B1812043
  · exact B1812047
  · exact B1812051
  · exact B1812055
  · exact B1812059
  · exact B1812063
  · exact B1812067
  · exact B1812071
  · exact B1812075
  · exact B1812079
  · exact B1812083
  · exact B1812087
  · exact B1812091
  · exact B1812095
  · exact B1812099
  · exact B1812103
  · exact B1812107
  · exact B1812111
  · exact B1812115
  · exact B1812119
  · exact B1812123
  · exact B1812127
  · exact B1812131
  · exact B1812135
  · exact B1812139
  · exact B1812143
  · exact B1812147
  · exact B1812151
  · exact B1812155
  · exact B1812159
  · exact B1812163
  · exact B1812167
  · exact B1812171
  · exact B1812175
  · exact B1812179
  · exact B1812183
  · exact B1812187
  · exact B1812191
  · exact B1812195
  · exact B1812199
  · exact B1812203
  · exact B1812207
  · exact B1812211
  · exact B1812215
  · exact B1812219
  · exact B1812223
  · exact B1812227
  · exact B1812231
  · exact B1812235
  · exact B1812239
  · exact B1812243
  · exact B1812247
  · exact B1812251
  · exact B1812255
  · exact B1812259
  · exact B1812263
  · exact B1812267
  · exact B1812271
  · exact B1812275
  · exact B1812279
  · exact B1812283
  · exact B1812287
  · exact B1812291
  · exact B1812295
  · exact B1812299
  · exact B1812303
  · exact B1812307
  · exact B1812311
  · exact B1812315
  · exact B1812319
  · exact B1812323
  · exact B1812327
  · exact B1812331
  · exact B1812335
  · exact B1812339
  · exact B1812343
  · exact B1812347
  · exact B1812351
  · exact B1812355
  · exact B1812359
  · exact B1812363
  · exact B1812367
  · exact B1812371
  · exact B1812375
  · exact B1812379
  · exact B1812383
  · exact B1812387
  · exact B1812391
  · exact B1812395
  · exact B1812399
  · exact B1812403
  · exact B1812407
  · exact B1812411
  · exact B1812415
  · exact B1812419
  · exact B1812423
  · exact B1812427
  · exact B1812431
  · exact B1812435
  · exact B1812439
  · exact B1812443
  · exact B1812447
  · exact B1812451
  · exact B1812455
  · exact B1812459
  · exact B1812463
  · exact B1812467
  · exact B1812471
  · exact B1812475
  · exact B1812479
  · exact B1812483
  · exact B1812487
  · exact B1812491
  · exact B1812495
  · exact B1812499
  · exact B1812503
  · exact B1812507
  · exact B1812511
  · exact B1812515
  · exact B1812519
  · exact B1812523
  · exact B1812527
  · exact B1812531
  · exact B1812535
  · exact B1812539
  · exact B1812543
  · exact B1812547
  · exact B1812551
  · exact B1812555
  · exact B1812559
  · exact B1812563
  · exact B1812567
  · exact B1812571
  · exact B1812575
  · exact B1812579
  · exact B1812583
  · exact B1812587
  · exact B1812591
  · exact B1812595
  · exact B1812599
  · exact B1812603
  · exact B1812607
  · exact B1812611
  · exact B1812615
  · exact B1812619
  · exact B1812623
  · exact B1812627
  · exact B1812631
  · exact B1812635
  · exact B1812639
  · exact B1812643
  · exact B1812647
  · exact B1812651
  · exact B1812655
  · exact B1812659
  · exact B1812663
  · exact B1812667
  · exact B1812671
  · exact B1812675
  · exact B1812679
  · exact B1812683
  · exact B1812687
  · exact B1812691
  · exact B1812695
  · exact B1812699
  · exact B1812703
  · exact B1812707
  · exact B1812711
  · exact B1812715
  · exact B1812719
  · exact B1812723
  · exact B1812727
  · exact B1812731
  · exact B1812735
  · exact B1812739
  · exact B1812743
  · exact B1812747
  · exact B1812751
  · exact B1812755
  · exact B1812759
  · exact B1812763
  · exact B1812767
  · exact B1812771
  · exact B1812775
  · exact B1812779
  · exact B1812783
  · exact B1812787
  · exact B1812791
  · exact B1812795
  · exact B1812799
  · exact B1812803
  · exact B1812807
  · exact B1812811
  · exact B1812815
  · exact B1812819
  · exact B1812823
  · exact B1812827
  · exact B1812831
  · exact B1812835
  · exact B1812839
  · exact B1812843
  · exact B1812847
  · exact B1812851
  · exact B1812855
  · exact B1812859
  · exact B1812863
  · exact B1812867
  · exact B1812871
  · exact B1812875
  · exact B1812879
  · exact B1812883
  · exact B1812887
  · exact B1812891
  · exact B1812895
  · exact B1812899
  · exact B1812903
  · exact B1812907
  · exact B1812911
  · exact B1812915
  · exact B1812919
  · exact B1812923
  · exact B1812927
  · exact B1812931
  · exact B1812935
  · exact B1812939
  · exact B1812943
  · exact B1812947
  · exact B1812951
  · exact B1812955
  · exact B1812959
  · exact B1812963
  · exact B1812967
  · exact B1812971
  · exact B1812975
  · exact B1812979
  · exact B1812983
  · exact B1812987
  · exact B1812991
  · exact B1812995
  · exact B1812999
  · exact B1813003
  · exact B1813007
  · exact B1813011
  · exact B1813015
  · exact B1813019
  · exact B1813023
  · exact B1813027
  · exact B1813031
  · exact B1813035
  · exact B1813039
  · exact B1813043
  · exact B1813047
  · exact B1813051
  · exact B1813055
  · exact B1813059
  · exact B1813063
  · exact B1813067
  · exact B1813071
  · exact B1813075
  · exact B1813079
  · exact B1813083
  · exact B1813087
  · exact B1813091
  · exact B1813095
  · exact B1813099
  · exact B1813103
  · exact B1813107
  · exact B1813111
  · exact B1813115
  · exact B1813119
  · exact B1813123
  · exact B1813127
  · exact B1813131
  · exact B1813135
  · exact B1813139
  · exact B1813143
  · exact B1813147
  · exact B1813151
  · exact B1813155
  · exact B1813159
  · exact B1813163
  · exact B1813167
  · exact B1813171
  · exact B1813175
  · exact B1813179
  · exact B1813183
  · exact B1813187
  · exact B1813191
  · exact B1813195
  · exact B1813199
  · exact B1813203
  · exact B1813207
  · exact B1813211
  · exact B1813215
  · exact B1813219
  · exact B1813223
  · exact B1813227
  · exact B1813231
  · exact B1813235
  · exact B1813239
  · exact B1813243
  · exact B1813247
  · exact B1813251
  · exact B1813255
  · exact B1813259
  · exact B1813263
  · exact B1813267
  · exact B1813271
  · exact B1813275
  · exact B1813279
  · exact B1813283
  · exact B1813287
  · exact B1813291
  · exact B1813295
  · exact B1813299
  · exact B1813303
  · exact B1813307
  · exact B1813311
  · exact B1813315
  · exact B1813319
  · exact B1813323
  · exact B1813327
  · exact B1813331
  · exact B1813335
  · exact B1813339
  · exact B1813343
  · exact B1813347
  · exact B1813351
  · exact B1813355
  · exact B1813359
  · exact B1813363
  · exact B1813367
  · exact B1813371
  · exact B1813375
  · exact B1813379
  · exact B1813383
  · exact B1813387
  · exact B1813391
  · exact B1813395
  · exact B1813399
  · exact B1813403
  · exact B1813407
  · exact B1813411
  · exact B1813415
  · exact B1813419
  · exact B1813423
  · exact B1813427
  · exact B1813431
  · exact B1813435
  · exact B1813439
  · exact B1813443
  · exact B1813447
  · exact B1813451
  · exact B1813455
  · exact B1813459
  · exact B1813463
  · exact B1813467
  · exact B1813471
  · exact B1813475
  · exact B1813479
  · exact B1813483
  · exact B1813487
  · exact B1813491
  · exact B1813495
  · exact B1813499
  · exact B1813503
  · exact B1813507
  · exact B1813511
  · exact B1813515
  · exact B1813519
  · exact B1813523
  · exact B1813527
  · exact B1813531
  · exact B1813535
  · exact B1813539
  · exact B1813543
  · exact B1813547
  · exact B1813551
  · exact B1813555
  · exact B1813559
  · exact B1813563
  · exact B1813567
  · exact B1813571
  · exact B1813575
  · exact B1813579
  · exact B1813583
  · exact B1813587
  · exact B1813591
  · exact B1813595
  · exact B1813599
  · exact B1813603
  · exact B1813607

theorem solution (m : ℕ) (hlo : 1811607 ≤ m) (hhi : m ≤ 1813607) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 452901 ≤ j := by omega
    have hj2 : j ≤ 453401 := by omega
    have hb : Blo 1811607 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
