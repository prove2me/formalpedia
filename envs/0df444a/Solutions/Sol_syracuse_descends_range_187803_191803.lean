-- Prove2me | solution 1 for syracuse_descends_range_187803_191803
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T16:43:49.267981+00:00
-- url     : https://prove2.me/submissions/b34a2030-233c-4934-a4d2-13e2c3571178

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


theorem B426005 : Blo 187803 426005 := bbase (se 6 (by rfl) ⟨9984, by rfl⟩ : syracuseStep 426005 = 19969) (by norm_num)
theorem B426077 : Blo 187803 426077 := bbase (se 3 (by rfl) ⟨79889, by rfl⟩ : syracuseStep 426077 = 159779) (by norm_num)
theorem B360605 : Blo 187803 360605 := bbase (se 3 (by rfl) ⟨67613, by rfl⟩ : syracuseStep 360605 = 135227) (by norm_num)
theorem B426149 : Blo 187803 426149 := bbase (se 4 (by rfl) ⟨39951, by rfl⟩ : syracuseStep 426149 = 79903) (by norm_num)
theorem B229565 : Blo 187803 229565 := bbase (se 3 (by rfl) ⟨43043, by rfl⟩ : syracuseStep 229565 = 86087) (by norm_num)
theorem B426221 : Blo 187803 426221 := bbase (se 3 (by rfl) ⟨79916, by rfl⟩ : syracuseStep 426221 = 159833) (by norm_num)
theorem B360749 : Blo 187803 360749 := bbase (se 3 (by rfl) ⟨67640, by rfl⟩ : syracuseStep 360749 = 135281) (by norm_num)
theorem B426293 : Blo 187803 426293 := bbase (se 5 (by rfl) ⟨19982, by rfl⟩ : syracuseStep 426293 = 39965) (by norm_num)
theorem B426365 : Blo 187803 426365 := bbase (se 3 (by rfl) ⟨79943, by rfl⟩ : syracuseStep 426365 = 159887) (by norm_num)
theorem B229825 : Blo 187803 229825 := bbase (se 2 (by rfl) ⟨86184, by rfl⟩ : syracuseStep 229825 = 172369) (by norm_num)
theorem B426437 : Blo 187803 426437 := bbase (se 4 (by rfl) ⟨39978, by rfl⟩ : syracuseStep 426437 = 79957) (by norm_num)
theorem B459245 : Blo 187803 459245 := bbase (se 3 (by rfl) ⟨86108, by rfl⟩ : syracuseStep 459245 = 172217) (by norm_num)
theorem B229873 : Blo 187803 229873 := bbase (se 2 (by rfl) ⟨86202, by rfl⟩ : syracuseStep 229873 = 172405) (by norm_num)
theorem B426509 : Blo 187803 426509 := bbase (se 3 (by rfl) ⟨79970, by rfl⟩ : syracuseStep 426509 = 159941) (by norm_num)
theorem B361037 : Blo 187803 361037 := bbase (se 3 (by rfl) ⟨67694, by rfl⟩ : syracuseStep 361037 = 135389) (by norm_num)
theorem B426581 : Blo 187803 426581 := bbase (se 8 (by rfl) ⟨2499, by rfl⟩ : syracuseStep 426581 = 4999) (by norm_num)
theorem B426653 : Blo 187803 426653 := bbase (se 3 (by rfl) ⟨79997, by rfl⟩ : syracuseStep 426653 = 159995) (by norm_num)
theorem B459437 : Blo 187803 459437 := bbase (se 3 (by rfl) ⟨86144, by rfl⟩ : syracuseStep 459437 = 172289) (by norm_num)
theorem B426725 : Blo 187803 426725 := bbase (se 4 (by rfl) ⟨40005, by rfl⟩ : syracuseStep 426725 = 80011) (by norm_num)
theorem B361189 : Blo 187803 361189 := bbase (se 4 (by rfl) ⟨33861, by rfl⟩ : syracuseStep 361189 = 67723) (by norm_num)
theorem B426797 : Blo 187803 426797 := bbase (se 3 (by rfl) ⟨80024, by rfl⟩ : syracuseStep 426797 = 160049) (by norm_num)
theorem B426869 : Blo 187803 426869 := bbase (se 5 (by rfl) ⟨20009, by rfl⟩ : syracuseStep 426869 = 40019) (by norm_num)
theorem B426941 : Blo 187803 426941 := bbase (se 3 (by rfl) ⟨80051, by rfl⟩ : syracuseStep 426941 = 160103) (by norm_num)
theorem B427013 : Blo 187803 427013 := bbase (se 4 (by rfl) ⟨40032, by rfl⟩ : syracuseStep 427013 = 80065) (by norm_num)
theorem B361493 : Blo 187803 361493 := bbase (se 6 (by rfl) ⟨8472, by rfl⟩ : syracuseStep 361493 = 16945) (by norm_num)
theorem B427085 : Blo 187803 427085 := bbase (se 3 (by rfl) ⟨80078, by rfl⟩ : syracuseStep 427085 = 160157) (by norm_num)
theorem B1442933 : Blo 187803 1442933 := bbase (se 5 (by rfl) ⟨67637, by rfl⟩ : syracuseStep 1442933 = 135275) (by norm_num)
theorem B427157 : Blo 187803 427157 := bbase (se 6 (by rfl) ⟨10011, by rfl⟩ : syracuseStep 427157 = 20023) (by norm_num)
theorem B427229 : Blo 187803 427229 := bbase (se 3 (by rfl) ⟨80105, by rfl⟩ : syracuseStep 427229 = 160211) (by norm_num)
theorem B427301 : Blo 187803 427301 := bbase (se 4 (by rfl) ⟨40059, by rfl⟩ : syracuseStep 427301 = 80119) (by norm_num)
theorem B427373 : Blo 187803 427373 := bbase (se 3 (by rfl) ⟨80132, by rfl⟩ : syracuseStep 427373 = 160265) (by norm_num)
theorem B427445 : Blo 187803 427445 := bbase (se 5 (by rfl) ⟨20036, by rfl⟩ : syracuseStep 427445 = 40073) (by norm_num)
theorem B951749 : Blo 187803 951749 := bbase (se 4 (by rfl) ⟨89226, by rfl⟩ : syracuseStep 951749 = 178453) (by norm_num)
theorem B427517 : Blo 187803 427517 := bbase (se 3 (by rfl) ⟨80159, by rfl⟩ : syracuseStep 427517 = 160319) (by norm_num)
theorem B1017365 : Blo 187803 1017365 := bbase (se 6 (by rfl) ⟨23844, by rfl⟩ : syracuseStep 1017365 = 47689) (by norm_num)
theorem B427589 : Blo 187803 427589 := bbase (se 4 (by rfl) ⟨40086, by rfl⟩ : syracuseStep 427589 = 80173) (by norm_num)
theorem B427661 : Blo 187803 427661 := bbase (se 3 (by rfl) ⟨80186, by rfl⟩ : syracuseStep 427661 = 160373) (by norm_num)
theorem B427733 : Blo 187803 427733 := bbase (se 7 (by rfl) ⟨5012, by rfl⟩ : syracuseStep 427733 = 10025) (by norm_num)
theorem B362245 : Blo 187803 362245 := bbase (se 4 (by rfl) ⟨33960, by rfl⟩ : syracuseStep 362245 = 67921) (by norm_num)
theorem B427805 : Blo 187803 427805 := bbase (se 3 (by rfl) ⟨80213, by rfl⟩ : syracuseStep 427805 = 160427) (by norm_num)
theorem B362285 : Blo 187803 362285 := bbase (se 3 (by rfl) ⟨67928, by rfl⟩ : syracuseStep 362285 = 135857) (by norm_num)
theorem B427877 : Blo 187803 427877 := bbase (se 4 (by rfl) ⟨40113, by rfl⟩ : syracuseStep 427877 = 80227) (by norm_num)
theorem B722789 : Blo 187803 722789 := bbase (se 4 (by rfl) ⟨67761, by rfl⟩ : syracuseStep 722789 = 135523) (by norm_num)
theorem B362389 : Blo 187803 362389 := bbase (se 6 (by rfl) ⟨8493, by rfl⟩ : syracuseStep 362389 = 16987) (by norm_num)
theorem B427949 : Blo 187803 427949 := bbase (se 3 (by rfl) ⟨80240, by rfl⟩ : syracuseStep 427949 = 160481) (by norm_num)
theorem B264173 : Blo 187803 264173 := bbase (se 3 (by rfl) ⟨49532, by rfl⟩ : syracuseStep 264173 = 99065) (by norm_num)
theorem B1214453 : Blo 187803 1214453 := bbase (se 5 (by rfl) ⟨56927, by rfl⟩ : syracuseStep 1214453 = 113855) (by norm_num)
theorem B428021 : Blo 187803 428021 := bbase (se 5 (by rfl) ⟨20063, by rfl⟩ : syracuseStep 428021 = 40127) (by norm_num)
theorem B362549 : Blo 187803 362549 := bbase (se 5 (by rfl) ⟨16994, by rfl⟩ : syracuseStep 362549 = 33989) (by norm_num)
theorem B428093 : Blo 187803 428093 := bbase (se 3 (by rfl) ⟨80267, by rfl⟩ : syracuseStep 428093 = 160535) (by norm_num)
theorem B362573 : Blo 187803 362573 := bbase (se 3 (by rfl) ⟨67982, by rfl⟩ : syracuseStep 362573 = 135965) (by norm_num)
theorem B428165 : Blo 187803 428165 := bbase (se 4 (by rfl) ⟨40140, by rfl⟩ : syracuseStep 428165 = 80281) (by norm_num)
theorem B723077 : Blo 187803 723077 := bbase (se 4 (by rfl) ⟨67788, by rfl⟩ : syracuseStep 723077 = 135577) (by norm_num)
theorem B362693 : Blo 187803 362693 := bbase (se 4 (by rfl) ⟨34002, by rfl⟩ : syracuseStep 362693 = 68005) (by norm_num)
theorem B428237 : Blo 187803 428237 := bbase (se 3 (by rfl) ⟨80294, by rfl⟩ : syracuseStep 428237 = 160589) (by norm_num)
theorem B428309 : Blo 187803 428309 := bbase (se 6 (by rfl) ⟨10038, by rfl⟩ : syracuseStep 428309 = 20077) (by norm_num)
theorem B428381 : Blo 187803 428381 := bbase (se 3 (by rfl) ⟨80321, by rfl⟩ : syracuseStep 428381 = 160643) (by norm_num)
theorem B428453 : Blo 187803 428453 := bbase (se 4 (by rfl) ⟨40167, by rfl⟩ : syracuseStep 428453 = 80335) (by norm_num)
theorem B362981 : Blo 187803 362981 := bbase (se 4 (by rfl) ⟨34029, by rfl⟩ : syracuseStep 362981 = 68059) (by norm_num)
theorem B428525 : Blo 187803 428525 := bbase (se 3 (by rfl) ⟨80348, by rfl⟩ : syracuseStep 428525 = 160697) (by norm_num)
theorem B428597 : Blo 187803 428597 := bbase (se 5 (by rfl) ⟨20090, by rfl⟩ : syracuseStep 428597 = 40181) (by norm_num)
theorem B428669 : Blo 187803 428669 := bbase (se 3 (by rfl) ⟨80375, by rfl⟩ : syracuseStep 428669 = 160751) (by norm_num)
theorem B363133 : Blo 187803 363133 := bbase (se 3 (by rfl) ⟨68087, by rfl⟩ : syracuseStep 363133 = 136175) (by norm_num)
theorem B428741 : Blo 187803 428741 := bbase (se 4 (by rfl) ⟨40194, by rfl⟩ : syracuseStep 428741 = 80389) (by norm_num)
theorem B953045 : Blo 187803 953045 := bbase (se 7 (by rfl) ⟨11168, by rfl⟩ : syracuseStep 953045 = 22337) (by norm_num)
theorem B428813 : Blo 187803 428813 := bbase (se 3 (by rfl) ⟨80402, by rfl⟩ : syracuseStep 428813 = 160805) (by norm_num)
theorem B428885 : Blo 187803 428885 := bbase (se 9 (by rfl) ⟨1256, by rfl⟩ : syracuseStep 428885 = 2513) (by norm_num)
theorem B428957 : Blo 187803 428957 := bbase (se 3 (by rfl) ⟨80429, by rfl⟩ : syracuseStep 428957 = 160859) (by norm_num)
theorem B363437 : Blo 187803 363437 := bbase (se 3 (by rfl) ⟨68144, by rfl⟩ : syracuseStep 363437 = 136289) (by norm_num)
theorem B429029 : Blo 187803 429029 := bbase (se 4 (by rfl) ⟨40221, by rfl⟩ : syracuseStep 429029 = 80443) (by norm_num)
theorem B429101 : Blo 187803 429101 := bbase (se 3 (by rfl) ⟨80456, by rfl⟩ : syracuseStep 429101 = 160913) (by norm_num)
theorem B429173 : Blo 187803 429173 := bbase (se 5 (by rfl) ⟨20117, by rfl⟩ : syracuseStep 429173 = 40235) (by norm_num)
theorem B2067605 : Blo 187803 2067605 := bbase (se 6 (by rfl) ⟨48459, by rfl⟩ : syracuseStep 2067605 = 96919) (by norm_num)
theorem B429245 : Blo 187803 429245 := bbase (se 3 (by rfl) ⟨80483, by rfl⟩ : syracuseStep 429245 = 160967) (by norm_num)
theorem B1084661 : Blo 187803 1084661 := bbase (se 5 (by rfl) ⟨50843, by rfl⟩ : syracuseStep 1084661 = 101687) (by norm_num)
theorem B429317 : Blo 187803 429317 := bbase (se 4 (by rfl) ⟨40248, by rfl⟩ : syracuseStep 429317 = 80497) (by norm_num)
theorem B724261 : Blo 187803 724261 := bbase (se 4 (by rfl) ⟨67899, by rfl⟩ : syracuseStep 724261 = 135799) (by norm_num)
theorem B429389 : Blo 187803 429389 := bbase (se 3 (by rfl) ⟨80510, by rfl⟩ : syracuseStep 429389 = 161021) (by norm_num)
theorem B920933 : Blo 187803 920933 := bbase (se 4 (by rfl) ⟨86337, by rfl⟩ : syracuseStep 920933 = 172675) (by norm_num)
theorem B429461 : Blo 187803 429461 := bbase (se 6 (by rfl) ⟨10065, by rfl⟩ : syracuseStep 429461 = 20131) (by norm_num)
theorem B429533 : Blo 187803 429533 := bbase (se 3 (by rfl) ⟨80537, by rfl⟩ : syracuseStep 429533 = 161075) (by norm_num)
theorem B429605 : Blo 187803 429605 := bbase (se 4 (by rfl) ⟨40275, by rfl⟩ : syracuseStep 429605 = 80551) (by norm_num)
theorem B724565 : Blo 187803 724565 := bbase (se 8 (by rfl) ⟨4245, by rfl⟩ : syracuseStep 724565 = 8491) (by norm_num)
theorem B429677 : Blo 187803 429677 := bbase (se 3 (by rfl) ⟨80564, by rfl⟩ : syracuseStep 429677 = 161129) (by norm_num)
theorem B429749 : Blo 187803 429749 := bbase (se 5 (by rfl) ⟨20144, by rfl⟩ : syracuseStep 429749 = 40289) (by norm_num)
theorem B429821 : Blo 187803 429821 := bbase (se 3 (by rfl) ⟨80591, by rfl⟩ : syracuseStep 429821 = 161183) (by norm_num)
theorem B429893 : Blo 187803 429893 := bbase (se 4 (by rfl) ⟨40302, by rfl⟩ : syracuseStep 429893 = 80605) (by norm_num)
theorem B429965 : Blo 187803 429965 := bbase (se 3 (by rfl) ⟨80618, by rfl⟩ : syracuseStep 429965 = 161237) (by norm_num)
theorem B430037 : Blo 187803 430037 := bbase (se 7 (by rfl) ⟨5039, by rfl⟩ : syracuseStep 430037 = 10079) (by norm_num)
theorem B954341 : Blo 187803 954341 := bbase (se 4 (by rfl) ⟨89469, by rfl⟩ : syracuseStep 954341 = 178939) (by norm_num)
theorem B430109 : Blo 187803 430109 := bbase (se 3 (by rfl) ⟨80645, by rfl⟩ : syracuseStep 430109 = 161291) (by norm_num)
theorem B200777 : Blo 187803 200777 := bbase (se 2 (by rfl) ⟨75291, by rfl⟩ : syracuseStep 200777 = 150583) (by norm_num)
theorem B462941 : Blo 187803 462941 := bbase (se 3 (by rfl) ⟨86801, by rfl⟩ : syracuseStep 462941 = 173603) (by norm_num)
theorem B430181 : Blo 187803 430181 := bbase (se 4 (by rfl) ⟨40329, by rfl⟩ : syracuseStep 430181 = 80659) (by norm_num)
theorem B200837 : Blo 187803 200837 := bbase (se 4 (by rfl) ⟨18828, by rfl⟩ : syracuseStep 200837 = 37657) (by norm_num)
theorem B430253 : Blo 187803 430253 := bbase (se 3 (by rfl) ⟨80672, by rfl⟩ : syracuseStep 430253 = 161345) (by norm_num)
theorem B430325 : Blo 187803 430325 := bbase (se 5 (by rfl) ⟨20171, by rfl⟩ : syracuseStep 430325 = 40343) (by norm_num)
theorem B200965 : Blo 187803 200965 := bbase (se 4 (by rfl) ⟨18840, by rfl⟩ : syracuseStep 200965 = 37681) (by norm_num)
theorem B430397 : Blo 187803 430397 := bbase (se 3 (by rfl) ⟨80699, by rfl⟩ : syracuseStep 430397 = 161399) (by norm_num)
theorem B430469 : Blo 187803 430469 := bbase (se 4 (by rfl) ⟨40356, by rfl⟩ : syracuseStep 430469 = 80713) (by norm_num)
theorem B1085845 : Blo 187803 1085845 := bbase (se 6 (by rfl) ⟨25449, by rfl⟩ : syracuseStep 1085845 = 50899) (by norm_num)
theorem B430541 : Blo 187803 430541 := bbase (se 3 (by rfl) ⟨80726, by rfl⟩ : syracuseStep 430541 = 161453) (by norm_num)
theorem B430613 : Blo 187803 430613 := bbase (se 6 (by rfl) ⟨10092, by rfl⟩ : syracuseStep 430613 = 20185) (by norm_num)
theorem B430685 : Blo 187803 430685 := bbase (se 3 (by rfl) ⟨80753, by rfl⟩ : syracuseStep 430685 = 161507) (by norm_num)
theorem B430757 : Blo 187803 430757 := bbase (se 4 (by rfl) ⟨40383, by rfl⟩ : syracuseStep 430757 = 80767) (by norm_num)
theorem B201409 : Blo 187803 201409 := bbase (se 2 (by rfl) ⟨75528, by rfl⟩ : syracuseStep 201409 = 151057) (by norm_num)
theorem B430829 : Blo 187803 430829 := bbase (se 3 (by rfl) ⟨80780, by rfl⟩ : syracuseStep 430829 = 161561) (by norm_num)
theorem B2036501 : Blo 187803 2036501 := bbase (se 6 (by rfl) ⟨47730, by rfl⟩ : syracuseStep 2036501 = 95461) (by norm_num)
theorem B430901 : Blo 187803 430901 := bbase (se 5 (by rfl) ⟨20198, by rfl⟩ : syracuseStep 430901 = 40397) (by norm_num)
theorem B201529 : Blo 187803 201529 := bbase (se 2 (by rfl) ⟨75573, by rfl⟩ : syracuseStep 201529 = 151147) (by norm_num)
theorem B430973 : Blo 187803 430973 := bbase (se 3 (by rfl) ⟨80807, by rfl⟩ : syracuseStep 430973 = 161615) (by norm_num)
theorem B431045 : Blo 187803 431045 := bbase (se 4 (by rfl) ⟨40410, by rfl⟩ : syracuseStep 431045 = 80821) (by norm_num)
theorem B1151957 : Blo 187803 1151957 := bbase (se 7 (by rfl) ⟨13499, by rfl⟩ : syracuseStep 1151957 = 26999) (by norm_num)
theorem B431117 : Blo 187803 431117 := bbase (se 3 (by rfl) ⟨80834, by rfl⟩ : syracuseStep 431117 = 161669) (by norm_num)
theorem B201781 : Blo 187803 201781 := bbase (se 5 (by rfl) ⟨9458, by rfl⟩ : syracuseStep 201781 = 18917) (by norm_num)
theorem B201785 : Blo 187803 201785 := bbase (se 2 (by rfl) ⟨75669, by rfl⟩ : syracuseStep 201785 = 151339) (by norm_num)
theorem B431189 : Blo 187803 431189 := bbase (se 8 (by rfl) ⟨2526, by rfl⟩ : syracuseStep 431189 = 5053) (by norm_num)
theorem B431261 : Blo 187803 431261 := bbase (se 3 (by rfl) ⟨80861, by rfl⟩ : syracuseStep 431261 = 161723) (by norm_num)
theorem B431333 : Blo 187803 431333 := bbase (se 4 (by rfl) ⟨40437, by rfl⟩ : syracuseStep 431333 = 80875) (by norm_num)
theorem B267509 : Blo 187803 267509 := bbase (se 5 (by rfl) ⟨12539, by rfl⟩ : syracuseStep 267509 = 25079) (by norm_num)
theorem B955637 : Blo 187803 955637 := bbase (se 5 (by rfl) ⟨44795, by rfl⟩ : syracuseStep 955637 = 89591) (by norm_num)
theorem B431405 : Blo 187803 431405 := bbase (se 3 (by rfl) ⟨80888, by rfl⟩ : syracuseStep 431405 = 161777) (by norm_num)
theorem B431477 : Blo 187803 431477 := bbase (se 5 (by rfl) ⟨20225, by rfl⟩ : syracuseStep 431477 = 40451) (by norm_num)
theorem B431549 : Blo 187803 431549 := bbase (se 3 (by rfl) ⟨80915, by rfl⟩ : syracuseStep 431549 = 161831) (by norm_num)
theorem B202349 : Blo 187803 202349 := bbase (se 3 (by rfl) ⟨37940, by rfl⟩ : syracuseStep 202349 = 75881) (by norm_num)
theorem B726677 : Blo 187803 726677 := bbase (se 6 (by rfl) ⟨17031, by rfl⟩ : syracuseStep 726677 = 34063) (by norm_num)
theorem B202537 : Blo 187803 202537 := bbase (se 2 (by rfl) ⟨75951, by rfl⟩ : syracuseStep 202537 = 151903) (by norm_num)
theorem B726965 : Blo 187803 726965 := bbase (se 5 (by rfl) ⟨34076, by rfl⟩ : syracuseStep 726965 = 68153) (by norm_num)
theorem B1087829 : Blo 187803 1087829 := bbase (se 10 (by rfl) ⟨1593, by rfl⟩ : syracuseStep 1087829 = 3187) (by norm_num)
theorem B956933 : Blo 187803 956933 := bbase (se 4 (by rfl) ⟨89712, by rfl⟩ : syracuseStep 956933 = 179425) (by norm_num)
theorem B203357 : Blo 187803 203357 := bbase (se 3 (by rfl) ⟨38129, by rfl⟩ : syracuseStep 203357 = 76259) (by norm_num)
theorem B268933 : Blo 187803 268933 := bbase (se 4 (by rfl) ⟨25212, by rfl⟩ : syracuseStep 268933 = 50425) (by norm_num)
theorem B301781 : Blo 187803 301781 := bbase (se 7 (by rfl) ⟨3536, by rfl⟩ : syracuseStep 301781 = 7073) (by norm_num)
theorem B301909 : Blo 187803 301909 := bbase (se 9 (by rfl) ⟨884, by rfl⟩ : syracuseStep 301909 = 1769) (by norm_num)
theorem B301973 : Blo 187803 301973 := bbase (se 6 (by rfl) ⟨7077, by rfl⟩ : syracuseStep 301973 = 14155) (by norm_num)
theorem B728021 : Blo 187803 728021 := bbase (se 7 (by rfl) ⟨8531, by rfl⟩ : syracuseStep 728021 = 17063) (by norm_num)
theorem B433117 : Blo 187803 433117 := bbase (se 3 (by rfl) ⟨81209, by rfl⟩ : syracuseStep 433117 = 162419) (by norm_num)
theorem B203801 : Blo 187803 203801 := bbase (se 2 (by rfl) ⟨76425, by rfl⟩ : syracuseStep 203801 = 152851) (by norm_num)
theorem B826453 : Blo 187803 826453 := bbase (se 8 (by rfl) ⟨4842, by rfl⟩ : syracuseStep 826453 = 9685) (by norm_num)
theorem B728149 : Blo 187803 728149 := bbase (se 8 (by rfl) ⟨4266, by rfl⟩ : syracuseStep 728149 = 8533) (by norm_num)
theorem B269525 : Blo 187803 269525 := bbase (se 7 (by rfl) ⟨3158, by rfl⟩ : syracuseStep 269525 = 6317) (by norm_num)
theorem B204049 : Blo 187803 204049 := bbase (se 2 (by rfl) ⟨76518, by rfl⟩ : syracuseStep 204049 = 153037) (by norm_num)
theorem B269605 : Blo 187803 269605 := bbase (se 4 (by rfl) ⟨25275, by rfl⟩ : syracuseStep 269605 = 50551) (by norm_num)
theorem B269725 : Blo 187803 269725 := bbase (se 3 (by rfl) ⟨50573, by rfl⟩ : syracuseStep 269725 = 101147) (by norm_num)
theorem B269821 : Blo 187803 269821 := bbase (se 3 (by rfl) ⟨50591, by rfl⟩ : syracuseStep 269821 = 101183) (by norm_num)
theorem B204481 : Blo 187803 204481 := bbase (se 2 (by rfl) ⟨76680, by rfl⟩ : syracuseStep 204481 = 153361) (by norm_num)
theorem B204553 : Blo 187803 204553 := bbase (se 2 (by rfl) ⟨76707, by rfl⟩ : syracuseStep 204553 = 153415) (by norm_num)
theorem B958229 : Blo 187803 958229 := bbase (se 6 (by rfl) ⟨22458, by rfl⟩ : syracuseStep 958229 = 44917) (by norm_num)
theorem B401213 : Blo 187803 401213 := bbase (se 3 (by rfl) ⟨75227, by rfl⟩ : syracuseStep 401213 = 150455) (by norm_num)
theorem B270317 : Blo 187803 270317 := bbase (se 3 (by rfl) ⟨50684, by rfl⟩ : syracuseStep 270317 = 101369) (by norm_num)
theorem B434173 : Blo 187803 434173 := bbase (se 3 (by rfl) ⟨81407, by rfl⟩ : syracuseStep 434173 = 162815) (by norm_num)
theorem B237745 : Blo 187803 237745 := bbase (se 2 (by rfl) ⟨89154, by rfl⟩ : syracuseStep 237745 = 178309) (by norm_num)
theorem B303293 : Blo 187803 303293 := bbase (se 3 (by rfl) ⟨56867, by rfl⟩ : syracuseStep 303293 = 113735) (by norm_num)
theorem B1515797 : Blo 187803 1515797 := bbase (se 6 (by rfl) ⟨35526, by rfl⟩ : syracuseStep 1515797 = 71053) (by norm_num)
theorem B303421 : Blo 187803 303421 := bbase (se 3 (by rfl) ⟨56891, by rfl⟩ : syracuseStep 303421 = 113783) (by norm_num)
theorem B237917 : Blo 187803 237917 := bbase (se 3 (by rfl) ⟨44609, by rfl⟩ : syracuseStep 237917 = 89219) (by norm_num)
theorem B237973 : Blo 187803 237973 := bbase (se 6 (by rfl) ⟨5577, by rfl⟩ : syracuseStep 237973 = 11155) (by norm_num)
theorem B238069 : Blo 187803 238069 := bbase (se 5 (by rfl) ⟨11159, by rfl⟩ : syracuseStep 238069 = 22319) (by norm_num)
theorem B1090037 : Blo 187803 1090037 := bbase (se 5 (by rfl) ⟨51095, by rfl⟩ : syracuseStep 1090037 = 102191) (by norm_num)
theorem B270869 : Blo 187803 270869 := bbase (se 6 (by rfl) ⟨6348, by rfl⟩ : syracuseStep 270869 = 12697) (by norm_num)
theorem B238241 : Blo 187803 238241 := bbase (se 2 (by rfl) ⟨89340, by rfl⟩ : syracuseStep 238241 = 178681) (by norm_num)
theorem B402101 : Blo 187803 402101 := bbase (se 5 (by rfl) ⟨18848, by rfl⟩ : syracuseStep 402101 = 37697) (by norm_num)
theorem B1450709 : Blo 187803 1450709 := bbase (se 7 (by rfl) ⟨17000, by rfl⟩ : syracuseStep 1450709 = 34001) (by norm_num)
theorem B238297 : Blo 187803 238297 := bbase (se 2 (by rfl) ⟨89361, by rfl⟩ : syracuseStep 238297 = 178723) (by norm_num)
theorem B1155829 : Blo 187803 1155829 := bbase (se 5 (by rfl) ⟨54179, by rfl⟩ : syracuseStep 1155829 = 108359) (by norm_num)
theorem B402221 : Blo 187803 402221 := bbase (se 3 (by rfl) ⟨75416, by rfl⟩ : syracuseStep 402221 = 150833) (by norm_num)
theorem B238393 : Blo 187803 238393 := bbase (se 2 (by rfl) ⟨89397, by rfl⟩ : syracuseStep 238393 = 178795) (by norm_num)
theorem B238565 : Blo 187803 238565 := bbase (se 4 (by rfl) ⟨22365, by rfl⟩ : syracuseStep 238565 = 44731) (by norm_num)
theorem B238621 : Blo 187803 238621 := bbase (se 3 (by rfl) ⟨44741, by rfl⟩ : syracuseStep 238621 = 89483) (by norm_num)
theorem B959525 : Blo 187803 959525 := bbase (se 4 (by rfl) ⟨89955, by rfl⟩ : syracuseStep 959525 = 179911) (by norm_num)
theorem B304229 : Blo 187803 304229 := bbase (se 4 (by rfl) ⟨28521, by rfl⟩ : syracuseStep 304229 = 57043) (by norm_num)
theorem B238717 : Blo 187803 238717 := bbase (se 3 (by rfl) ⟨44759, by rfl⟩ : syracuseStep 238717 = 89519) (by norm_num)
theorem B435413 : Blo 187803 435413 := bbase (se 7 (by rfl) ⟨5102, by rfl⟩ : syracuseStep 435413 = 10205) (by norm_num)
theorem B271621 : Blo 187803 271621 := bbase (se 4 (by rfl) ⟨25464, by rfl⟩ : syracuseStep 271621 = 50929) (by norm_num)
theorem B238889 : Blo 187803 238889 := bbase (se 2 (by rfl) ⟨89583, by rfl⟩ : syracuseStep 238889 = 179167) (by norm_num)
theorem B238945 : Blo 187803 238945 := bbase (se 2 (by rfl) ⟨89604, by rfl⟩ : syracuseStep 238945 = 179209) (by norm_num)
theorem B304517 : Blo 187803 304517 := bbase (se 4 (by rfl) ⟨28548, by rfl⟩ : syracuseStep 304517 = 57097) (by norm_num)
theorem B402853 : Blo 187803 402853 := bbase (se 4 (by rfl) ⟨37767, by rfl⟩ : syracuseStep 402853 = 75535) (by norm_num)
theorem B239041 : Blo 187803 239041 := bbase (se 2 (by rfl) ⟨89640, by rfl⟩ : syracuseStep 239041 = 179281) (by norm_num)
theorem B239213 : Blo 187803 239213 := bbase (se 3 (by rfl) ⟨44852, by rfl⟩ : syracuseStep 239213 = 89705) (by norm_num)
theorem B468629 : Blo 187803 468629 := bbase (se 6 (by rfl) ⟨10983, by rfl⟩ : syracuseStep 468629 = 21967) (by norm_num)
theorem B239269 : Blo 187803 239269 := bbase (se 4 (by rfl) ⟨22431, by rfl⟩ : syracuseStep 239269 = 44863) (by norm_num)
theorem B206513 : Blo 187803 206513 := bbase (se 2 (by rfl) ⟨77442, by rfl⟩ : syracuseStep 206513 = 154885) (by norm_num)
theorem B239365 : Blo 187803 239365 := bbase (se 4 (by rfl) ⟨22440, by rfl⟩ : syracuseStep 239365 = 44881) (by norm_num)
theorem B304933 : Blo 187803 304933 := bbase (se 4 (by rfl) ⟨28587, by rfl⟩ : syracuseStep 304933 = 57175) (by norm_num)
theorem B1025909 : Blo 187803 1025909 := bbase (se 5 (by rfl) ⟨48089, by rfl⟩ : syracuseStep 1025909 = 96179) (by norm_num)
theorem B239537 : Blo 187803 239537 := bbase (se 2 (by rfl) ⟨89826, by rfl⟩ : syracuseStep 239537 = 179653) (by norm_num)
theorem B305093 : Blo 187803 305093 := bbase (se 4 (by rfl) ⟨28602, by rfl⟩ : syracuseStep 305093 = 57205) (by norm_num)
theorem B239593 : Blo 187803 239593 := bbase (se 2 (by rfl) ⟨89847, by rfl⟩ : syracuseStep 239593 = 179695) (by norm_num)
theorem B272413 : Blo 187803 272413 := bbase (se 3 (by rfl) ⟨51077, by rfl⟩ : syracuseStep 272413 = 102155) (by norm_num)
theorem B239689 : Blo 187803 239689 := bbase (se 2 (by rfl) ⟨89883, by rfl⟩ : syracuseStep 239689 = 179767) (by norm_num)
theorem B436421 : Blo 187803 436421 := bbase (se 4 (by rfl) ⟨40914, by rfl⟩ : syracuseStep 436421 = 81829) (by norm_num)
theorem B239861 : Blo 187803 239861 := bbase (se 5 (by rfl) ⟨11243, by rfl⟩ : syracuseStep 239861 = 22487) (by norm_num)
theorem B3352853 : Blo 187803 3352853 := bbase (se 6 (by rfl) ⟨78582, by rfl⟩ : syracuseStep 3352853 = 157165) (by norm_num)
theorem B403741 : Blo 187803 403741 := bbase (se 3 (by rfl) ⟨75701, by rfl⟩ : syracuseStep 403741 = 151403) (by norm_num)
theorem B239917 : Blo 187803 239917 := bbase (se 3 (by rfl) ⟨44984, by rfl⟩ : syracuseStep 239917 = 89969) (by norm_num)
theorem B960821 : Blo 187803 960821 := bbase (se 5 (by rfl) ⟨45038, by rfl⟩ : syracuseStep 960821 = 90077) (by norm_num)
theorem B272749 : Blo 187803 272749 := bbase (se 3 (by rfl) ⟨51140, by rfl⟩ : syracuseStep 272749 = 102281) (by norm_num)
theorem B240013 : Blo 187803 240013 := bbase (se 3 (by rfl) ⟨45002, by rfl⟩ : syracuseStep 240013 = 90005) (by norm_num)
theorem B403861 : Blo 187803 403861 := bbase (se 6 (by rfl) ⟨9465, by rfl⟩ : syracuseStep 403861 = 18931) (by norm_num)
theorem B240185 : Blo 187803 240185 := bbase (se 2 (by rfl) ⟨90069, by rfl⟩ : syracuseStep 240185 = 180139) (by norm_num)
theorem B272965 : Blo 187803 272965 := bbase (se 4 (by rfl) ⟨25590, by rfl⟩ : syracuseStep 272965 = 51181) (by norm_num)
theorem B240241 : Blo 187803 240241 := bbase (se 2 (by rfl) ⟨90090, by rfl⟩ : syracuseStep 240241 = 180181) (by norm_num)
theorem B338581 : Blo 187803 338581 := bbase (se 6 (by rfl) ⟨7935, by rfl⟩ : syracuseStep 338581 = 15871) (by norm_num)
theorem B404117 : Blo 187803 404117 := bbase (se 6 (by rfl) ⟨9471, by rfl⟩ : syracuseStep 404117 = 18943) (by norm_num)
theorem B305869 : Blo 187803 305869 := bbase (se 3 (by rfl) ⟨57350, by rfl⟩ : syracuseStep 305869 = 114701) (by norm_num)
theorem B240337 : Blo 187803 240337 := bbase (se 2 (by rfl) ⟨90126, by rfl⟩ : syracuseStep 240337 = 180253) (by norm_num)
theorem B535349 : Blo 187803 535349 := bbase (se 5 (by rfl) ⟨25094, by rfl⟩ : syracuseStep 535349 = 50189) (by norm_num)
theorem B240509 : Blo 187803 240509 := bbase (se 3 (by rfl) ⟨45095, by rfl⟩ : syracuseStep 240509 = 90191) (by norm_num)
theorem B732053 : Blo 187803 732053 := bbase (se 6 (by rfl) ⟨17157, by rfl⟩ : syracuseStep 732053 = 34315) (by norm_num)
theorem B240565 : Blo 187803 240565 := bbase (se 5 (by rfl) ⟨11276, by rfl⟩ : syracuseStep 240565 = 22553) (by norm_num)
theorem B240661 : Blo 187803 240661 := bbase (se 6 (by rfl) ⟨5640, by rfl⟩ : syracuseStep 240661 = 11281) (by norm_num)
theorem B240833 : Blo 187803 240833 := bbase (se 2 (by rfl) ⟨90312, by rfl⟩ : syracuseStep 240833 = 180625) (by norm_num)
theorem B240889 : Blo 187803 240889 := bbase (se 2 (by rfl) ⟨90333, by rfl⟩ : syracuseStep 240889 = 180667) (by norm_num)
theorem B240985 : Blo 187803 240985 := bbase (se 2 (by rfl) ⟨90369, by rfl⟩ : syracuseStep 240985 = 180739) (by norm_num)
theorem B634229 : Blo 187803 634229 := bbase (se 5 (by rfl) ⟨29729, by rfl⟩ : syracuseStep 634229 = 59459) (by norm_num)
theorem B2174357 : Blo 187803 2174357 := bbase (se 6 (by rfl) ⟨50961, by rfl⟩ : syracuseStep 2174357 = 101923) (by norm_num)
theorem B536021 : Blo 187803 536021 := bbase (se 7 (by rfl) ⟨6281, by rfl⟩ : syracuseStep 536021 = 12563) (by norm_num)
theorem B241157 : Blo 187803 241157 := bbase (se 4 (by rfl) ⟨22608, by rfl⟩ : syracuseStep 241157 = 45217) (by norm_num)
theorem B405005 : Blo 187803 405005 := bbase (se 3 (by rfl) ⟨75938, by rfl⟩ : syracuseStep 405005 = 151877) (by norm_num)
theorem B241213 : Blo 187803 241213 := bbase (se 3 (by rfl) ⟨45227, by rfl⟩ : syracuseStep 241213 = 90455) (by norm_num)
theorem B962117 : Blo 187803 962117 := bbase (se 4 (by rfl) ⟨90198, by rfl⟩ : syracuseStep 962117 = 180397) (by norm_num)
theorem B241225 : Blo 187803 241225 := bbase (se 2 (by rfl) ⟨90459, by rfl⟩ : syracuseStep 241225 = 180919) (by norm_num)
theorem B241309 : Blo 187803 241309 := bbase (se 3 (by rfl) ⟨45245, by rfl⟩ : syracuseStep 241309 = 90491) (by norm_num)
theorem B1027765 : Blo 187803 1027765 := bbase (se 5 (by rfl) ⟨48176, by rfl⟩ : syracuseStep 1027765 = 96353) (by norm_num)
theorem B405245 : Blo 187803 405245 := bbase (se 3 (by rfl) ⟨75983, by rfl⟩ : syracuseStep 405245 = 151967) (by norm_num)
theorem B634661 : Blo 187803 634661 := bbase (se 4 (by rfl) ⟨59499, by rfl⟩ : syracuseStep 634661 = 118999) (by norm_num)
theorem B241481 : Blo 187803 241481 := bbase (se 2 (by rfl) ⟨90555, by rfl⟩ : syracuseStep 241481 = 181111) (by norm_num)
theorem B307061 : Blo 187803 307061 := bbase (se 5 (by rfl) ⟨14393, by rfl⟩ : syracuseStep 307061 = 28787) (by norm_num)
theorem B241537 : Blo 187803 241537 := bbase (se 2 (by rfl) ⟨90576, by rfl⟩ : syracuseStep 241537 = 181153) (by norm_num)
theorem B536453 : Blo 187803 536453 := bbase (se 4 (by rfl) ⟨50292, by rfl⟩ : syracuseStep 536453 = 100585) (by norm_num)
theorem B1224629 : Blo 187803 1224629 := bbase (se 5 (by rfl) ⟨57404, by rfl⟩ : syracuseStep 1224629 = 114809) (by norm_num)
theorem B241633 : Blo 187803 241633 := bbase (se 2 (by rfl) ⟨90612, by rfl⟩ : syracuseStep 241633 = 181225) (by norm_num)
theorem B339965 : Blo 187803 339965 := bbase (se 3 (by rfl) ⟨63743, by rfl⟩ : syracuseStep 339965 = 127487) (by norm_num)
theorem B3223637 : Blo 187803 3223637 := bbase (se 8 (by rfl) ⟨18888, by rfl⟩ : syracuseStep 3223637 = 37777) (by norm_num)
theorem B241805 : Blo 187803 241805 := bbase (se 3 (by rfl) ⟨45338, by rfl⟩ : syracuseStep 241805 = 90677) (by norm_num)
theorem B307381 : Blo 187803 307381 := bbase (se 5 (by rfl) ⟨14408, by rfl⟩ : syracuseStep 307381 = 28817) (by norm_num)
theorem B241861 : Blo 187803 241861 := bbase (se 4 (by rfl) ⟨22674, by rfl⟩ : syracuseStep 241861 = 45349) (by norm_num)
theorem B635093 : Blo 187803 635093 := bbase (se 7 (by rfl) ⟨7442, by rfl⟩ : syracuseStep 635093 = 14885) (by norm_num)
theorem B405749 : Blo 187803 405749 := bbase (se 5 (by rfl) ⟨19019, by rfl⟩ : syracuseStep 405749 = 38039) (by norm_num)
theorem B405757 : Blo 187803 405757 := bbase (se 3 (by rfl) ⟨76079, by rfl⟩ : syracuseStep 405757 = 152159) (by norm_num)
theorem B241957 : Blo 187803 241957 := bbase (se 4 (by rfl) ⟨22683, by rfl⟩ : syracuseStep 241957 = 45367) (by norm_num)
theorem B242129 : Blo 187803 242129 := bbase (se 2 (by rfl) ⟨90798, by rfl⟩ : syracuseStep 242129 = 181597) (by norm_num)
theorem B242185 : Blo 187803 242185 := bbase (se 2 (by rfl) ⟨90819, by rfl⟩ : syracuseStep 242185 = 181639) (by norm_num)
theorem B242281 : Blo 187803 242281 := bbase (se 2 (by rfl) ⟨90855, by rfl⟩ : syracuseStep 242281 = 181711) (by norm_num)
theorem B602741 : Blo 187803 602741 := bbase (se 5 (by rfl) ⟨28253, by rfl⟩ : syracuseStep 602741 = 56507) (by norm_num)
theorem B537205 : Blo 187803 537205 := bbase (se 5 (by rfl) ⟨25181, by rfl⟩ : syracuseStep 537205 = 50363) (by norm_num)
theorem B635525 : Blo 187803 635525 := bbase (se 4 (by rfl) ⟨59580, by rfl⟩ : syracuseStep 635525 = 119161) (by norm_num)
theorem B242437 : Blo 187803 242437 := bbase (se 4 (by rfl) ⟨22728, by rfl⟩ : syracuseStep 242437 = 45457) (by norm_num)
theorem B242453 : Blo 187803 242453 := bbase (se 6 (by rfl) ⟨5682, by rfl⟩ : syracuseStep 242453 = 11365) (by norm_num)
theorem B242509 : Blo 187803 242509 := bbase (se 3 (by rfl) ⟨45470, by rfl⟩ : syracuseStep 242509 = 90941) (by norm_num)
theorem B963413 : Blo 187803 963413 := bbase (se 9 (by rfl) ⟨2822, by rfl⟩ : syracuseStep 963413 = 5645) (by norm_num)
theorem B242605 : Blo 187803 242605 := bbase (se 3 (by rfl) ⟨45488, by rfl⟩ : syracuseStep 242605 = 90977) (by norm_num)
theorem B766997 : Blo 187803 766997 := bbase (se 6 (by rfl) ⟨17976, by rfl⟩ : syracuseStep 766997 = 35953) (by norm_num)
theorem B635957 : Blo 187803 635957 := bbase (se 5 (by rfl) ⟨29810, by rfl⟩ : syracuseStep 635957 = 59621) (by norm_num)
theorem B1815605 : Blo 187803 1815605 := bbase (se 5 (by rfl) ⟨85106, by rfl⟩ : syracuseStep 1815605 = 170213) (by norm_num)
theorem B865637 : Blo 187803 865637 := bbase (se 4 (by rfl) ⟨81153, by rfl⟩ : syracuseStep 865637 = 162307) (by norm_num)
theorem B406885 : Blo 187803 406885 := bbase (se 4 (by rfl) ⟨38145, by rfl⟩ : syracuseStep 406885 = 76291) (by norm_num)
theorem B1095029 : Blo 187803 1095029 := bbase (se 5 (by rfl) ⟨51329, by rfl⟩ : syracuseStep 1095029 = 102659) (by norm_num)
theorem B636389 : Blo 187803 636389 := bbase (se 4 (by rfl) ⟨59661, by rfl⟩ : syracuseStep 636389 = 119323) (by norm_num)
theorem B341509 : Blo 187803 341509 := bbase (se 4 (by rfl) ⟨32016, by rfl⟩ : syracuseStep 341509 = 64033) (by norm_num)
theorem B243361 : Blo 187803 243361 := bbase (se 2 (by rfl) ⟨91260, by rfl⟩ : syracuseStep 243361 = 182521) (by norm_num)
theorem B603845 : Blo 187803 603845 := bbase (se 4 (by rfl) ⟨56610, by rfl⟩ : syracuseStep 603845 = 113221) (by norm_num)
theorem B407261 : Blo 187803 407261 := bbase (se 3 (by rfl) ⟨76361, by rfl⟩ : syracuseStep 407261 = 152723) (by norm_num)
theorem B636821 : Blo 187803 636821 := bbase (se 6 (by rfl) ⟨14925, by rfl⟩ : syracuseStep 636821 = 29851) (by norm_num)
theorem B276517 : Blo 187803 276517 := bbase (se 4 (by rfl) ⟨25923, by rfl⟩ : syracuseStep 276517 = 51847) (by norm_num)
theorem B964709 : Blo 187803 964709 := bbase (se 4 (by rfl) ⟨90441, by rfl⟩ : syracuseStep 964709 = 180883) (by norm_num)
theorem B637253 : Blo 187803 637253 := bbase (se 4 (by rfl) ⟨59742, by rfl⟩ : syracuseStep 637253 = 119485) (by norm_num)
theorem B211297 : Blo 187803 211297 := bbase (se 2 (by rfl) ⟨79236, by rfl⟩ : syracuseStep 211297 = 158473) (by norm_num)
theorem B211333 : Blo 187803 211333 := bbase (se 4 (by rfl) ⟨19812, by rfl⟩ : syracuseStep 211333 = 39625) (by norm_num)
theorem B211369 : Blo 187803 211369 := bbase (se 2 (by rfl) ⟨79263, by rfl⟩ : syracuseStep 211369 = 158527) (by norm_num)
theorem B211405 : Blo 187803 211405 := bbase (se 3 (by rfl) ⟨39638, by rfl⟩ : syracuseStep 211405 = 79277) (by norm_num)
theorem B211441 : Blo 187803 211441 := bbase (se 2 (by rfl) ⟨79290, by rfl⟩ : syracuseStep 211441 = 158581) (by norm_num)
theorem B735749 : Blo 187803 735749 := bbase (se 4 (by rfl) ⟨68976, by rfl⟩ : syracuseStep 735749 = 137953) (by norm_num)
theorem B211477 : Blo 187803 211477 := bbase (se 6 (by rfl) ⟨4956, by rfl⟩ : syracuseStep 211477 = 9913) (by norm_num)
theorem B211513 : Blo 187803 211513 := bbase (se 2 (by rfl) ⟨79317, by rfl⟩ : syracuseStep 211513 = 158635) (by norm_num)
theorem B211549 : Blo 187803 211549 := bbase (se 3 (by rfl) ⟨39665, by rfl⟩ : syracuseStep 211549 = 79331) (by norm_num)
theorem B211585 : Blo 187803 211585 := bbase (se 2 (by rfl) ⟨79344, by rfl⟩ : syracuseStep 211585 = 158689) (by norm_num)
theorem B211621 : Blo 187803 211621 := bbase (se 4 (by rfl) ⟨19839, by rfl⟩ : syracuseStep 211621 = 39679) (by norm_num)
theorem B211657 : Blo 187803 211657 := bbase (se 2 (by rfl) ⟨79371, by rfl⟩ : syracuseStep 211657 = 158743) (by norm_num)
theorem B342733 : Blo 187803 342733 := bbase (se 3 (by rfl) ⟨64262, by rfl⟩ : syracuseStep 342733 = 128525) (by norm_num)
theorem B211693 : Blo 187803 211693 := bbase (se 3 (by rfl) ⟨39692, by rfl⟩ : syracuseStep 211693 = 79385) (by norm_num)
theorem B637685 : Blo 187803 637685 := bbase (se 5 (by rfl) ⟨29891, by rfl⟩ : syracuseStep 637685 = 59783) (by norm_num)
theorem B211729 : Blo 187803 211729 := bbase (se 2 (by rfl) ⟨79398, by rfl⟩ : syracuseStep 211729 = 158797) (by norm_num)
theorem B211765 : Blo 187803 211765 := bbase (se 5 (by rfl) ⟨9926, by rfl⟩ : syracuseStep 211765 = 19853) (by norm_num)
theorem B211801 : Blo 187803 211801 := bbase (se 2 (by rfl) ⟨79425, by rfl⟩ : syracuseStep 211801 = 158851) (by norm_num)
theorem B342893 : Blo 187803 342893 := bbase (se 3 (by rfl) ⟨64292, by rfl⟩ : syracuseStep 342893 = 128585) (by norm_num)
theorem B211837 : Blo 187803 211837 := bbase (se 3 (by rfl) ⟨39719, by rfl⟩ : syracuseStep 211837 = 79439) (by norm_num)
theorem B1096597 : Blo 187803 1096597 := bbase (se 6 (by rfl) ⟨25701, by rfl⟩ : syracuseStep 1096597 = 51403) (by norm_num)
theorem B211873 : Blo 187803 211873 := bbase (se 2 (by rfl) ⟨79452, by rfl⟩ : syracuseStep 211873 = 158905) (by norm_num)
theorem B211909 : Blo 187803 211909 := bbase (se 4 (by rfl) ⟨19866, by rfl⟩ : syracuseStep 211909 = 39733) (by norm_num)
theorem B211945 : Blo 187803 211945 := bbase (se 2 (by rfl) ⟨79479, by rfl⟩ : syracuseStep 211945 = 158959) (by norm_num)
theorem B211981 : Blo 187803 211981 := bbase (se 3 (by rfl) ⟨39746, by rfl⟩ : syracuseStep 211981 = 79493) (by norm_num)
theorem B212017 : Blo 187803 212017 := bbase (se 2 (by rfl) ⟨79506, by rfl⟩ : syracuseStep 212017 = 159013) (by norm_num)
theorem B212053 : Blo 187803 212053 := bbase (se 8 (by rfl) ⟨1242, by rfl⟩ : syracuseStep 212053 = 2485) (by norm_num)
theorem B212089 : Blo 187803 212089 := bbase (se 2 (by rfl) ⟨79533, by rfl⟩ : syracuseStep 212089 = 159067) (by norm_num)
theorem B212125 : Blo 187803 212125 := bbase (se 3 (by rfl) ⟨39773, by rfl⟩ : syracuseStep 212125 = 79547) (by norm_num)
theorem B638117 : Blo 187803 638117 := bbase (se 4 (by rfl) ⟨59823, by rfl⟩ : syracuseStep 638117 = 119647) (by norm_num)
theorem B212161 : Blo 187803 212161 := bbase (se 2 (by rfl) ⟨79560, by rfl⟩ : syracuseStep 212161 = 159121) (by norm_num)
theorem B212197 : Blo 187803 212197 := bbase (se 4 (by rfl) ⟨19893, by rfl⟩ : syracuseStep 212197 = 39787) (by norm_num)
theorem B212233 : Blo 187803 212233 := bbase (se 2 (by rfl) ⟨79587, by rfl⟩ : syracuseStep 212233 = 159175) (by norm_num)
theorem B212269 : Blo 187803 212269 := bbase (se 3 (by rfl) ⟨39800, by rfl⟩ : syracuseStep 212269 = 79601) (by norm_num)
theorem B408901 : Blo 187803 408901 := bbase (se 4 (by rfl) ⟨38334, by rfl⟩ : syracuseStep 408901 = 76669) (by norm_num)
theorem B212305 : Blo 187803 212305 := bbase (se 2 (by rfl) ⟨79614, by rfl⟩ : syracuseStep 212305 = 159229) (by norm_num)
theorem B212341 : Blo 187803 212341 := bbase (se 5 (by rfl) ⟨9953, by rfl⟩ : syracuseStep 212341 = 19907) (by norm_num)
theorem B966005 : Blo 187803 966005 := bbase (se 5 (by rfl) ⟨45281, by rfl⟩ : syracuseStep 966005 = 90563) (by norm_num)
theorem B540053 : Blo 187803 540053 := bbase (se 6 (by rfl) ⟨12657, by rfl⟩ : syracuseStep 540053 = 25315) (by norm_num)
theorem B212377 : Blo 187803 212377 := bbase (se 2 (by rfl) ⟨79641, by rfl⟩ : syracuseStep 212377 = 159283) (by norm_num)
theorem B212413 : Blo 187803 212413 := bbase (se 3 (by rfl) ⟨39827, by rfl⟩ : syracuseStep 212413 = 79655) (by norm_num)
theorem B212449 : Blo 187803 212449 := bbase (se 2 (by rfl) ⟨79668, by rfl⟩ : syracuseStep 212449 = 159337) (by norm_num)
theorem B212485 : Blo 187803 212485 := bbase (se 4 (by rfl) ⟨19920, by rfl⟩ : syracuseStep 212485 = 39841) (by norm_num)
theorem B212521 : Blo 187803 212521 := bbase (se 2 (by rfl) ⟨79695, by rfl⟩ : syracuseStep 212521 = 159391) (by norm_num)
theorem B605765 : Blo 187803 605765 := bbase (se 4 (by rfl) ⟨56790, by rfl⟩ : syracuseStep 605765 = 113581) (by norm_num)
theorem B212557 : Blo 187803 212557 := bbase (se 3 (by rfl) ⟨39854, by rfl⟩ : syracuseStep 212557 = 79709) (by norm_num)
theorem B638549 : Blo 187803 638549 := bbase (se 8 (by rfl) ⟨3741, by rfl⟩ : syracuseStep 638549 = 7483) (by norm_num)
theorem B212593 : Blo 187803 212593 := bbase (se 2 (by rfl) ⟨79722, by rfl⟩ : syracuseStep 212593 = 159445) (by norm_num)
theorem B212629 : Blo 187803 212629 := bbase (se 6 (by rfl) ⟨4983, by rfl⟩ : syracuseStep 212629 = 9967) (by norm_num)
theorem B245413 : Blo 187803 245413 := bbase (se 4 (by rfl) ⟨23007, by rfl⟩ : syracuseStep 245413 = 46015) (by norm_num)
theorem B212665 : Blo 187803 212665 := bbase (se 2 (by rfl) ⟨79749, by rfl⟩ : syracuseStep 212665 = 159499) (by norm_num)
theorem B212701 : Blo 187803 212701 := bbase (se 3 (by rfl) ⟨39881, by rfl⟩ : syracuseStep 212701 = 79763) (by norm_num)
theorem B212737 : Blo 187803 212737 := bbase (se 2 (by rfl) ⟨79776, by rfl⟩ : syracuseStep 212737 = 159553) (by norm_num)
theorem B409349 : Blo 187803 409349 := bbase (se 4 (by rfl) ⟨38376, by rfl⟩ : syracuseStep 409349 = 76753) (by norm_num)
theorem B212773 : Blo 187803 212773 := bbase (se 4 (by rfl) ⟨19947, by rfl⟩ : syracuseStep 212773 = 39895) (by norm_num)
theorem B212809 : Blo 187803 212809 := bbase (se 2 (by rfl) ⟨79803, by rfl⟩ : syracuseStep 212809 = 159607) (by norm_num)
theorem B212845 : Blo 187803 212845 := bbase (se 3 (by rfl) ⟨39908, by rfl⟩ : syracuseStep 212845 = 79817) (by norm_num)
theorem B212881 : Blo 187803 212881 := bbase (se 2 (by rfl) ⟨79830, by rfl⟩ : syracuseStep 212881 = 159661) (by norm_num)
theorem B343973 : Blo 187803 343973 := bbase (se 4 (by rfl) ⟨32247, by rfl⟩ : syracuseStep 343973 = 64495) (by norm_num)
theorem B507829 : Blo 187803 507829 := bbase (se 5 (by rfl) ⟨23804, by rfl⟩ : syracuseStep 507829 = 47609) (by norm_num)
theorem B212917 : Blo 187803 212917 := bbase (se 5 (by rfl) ⟨9980, by rfl⟩ : syracuseStep 212917 = 19961) (by norm_num)
theorem B212953 : Blo 187803 212953 := bbase (se 2 (by rfl) ⟨79857, by rfl⟩ : syracuseStep 212953 = 159715) (by norm_num)
theorem B212989 : Blo 187803 212989 := bbase (se 3 (by rfl) ⟨39935, by rfl⟩ : syracuseStep 212989 = 79871) (by norm_num)
theorem B638981 : Blo 187803 638981 := bbase (se 4 (by rfl) ⟨59904, by rfl⟩ : syracuseStep 638981 = 119809) (by norm_num)
theorem B213025 : Blo 187803 213025 := bbase (se 2 (by rfl) ⟨79884, by rfl⟩ : syracuseStep 213025 = 159769) (by norm_num)
theorem B344117 : Blo 187803 344117 := bbase (se 5 (by rfl) ⟨16130, by rfl⟩ : syracuseStep 344117 = 32261) (by norm_num)
theorem B213061 : Blo 187803 213061 := bbase (se 4 (by rfl) ⟨19974, by rfl⟩ : syracuseStep 213061 = 39949) (by norm_num)
theorem B213097 : Blo 187803 213097 := bbase (se 2 (by rfl) ⟨79911, by rfl⟩ : syracuseStep 213097 = 159823) (by norm_num)
theorem B213133 : Blo 187803 213133 := bbase (se 3 (by rfl) ⟨39962, by rfl⟩ : syracuseStep 213133 = 79925) (by norm_num)
theorem B213169 : Blo 187803 213169 := bbase (se 2 (by rfl) ⟨79938, by rfl⟩ : syracuseStep 213169 = 159877) (by norm_num)
theorem B213205 : Blo 187803 213205 := bbase (se 7 (by rfl) ⟨2498, by rfl⟩ : syracuseStep 213205 = 4997) (by norm_num)
theorem B213241 : Blo 187803 213241 := bbase (se 2 (by rfl) ⟨79965, by rfl⟩ : syracuseStep 213241 = 159931) (by norm_num)
theorem B1294613 : Blo 187803 1294613 := bbase (se 6 (by rfl) ⟨30342, by rfl⟩ : syracuseStep 1294613 = 60685) (by norm_num)
theorem B213277 : Blo 187803 213277 := bbase (se 3 (by rfl) ⟨39989, by rfl⟩ : syracuseStep 213277 = 79979) (by norm_num)
theorem B475429 : Blo 187803 475429 := bbase (se 4 (by rfl) ⟨44571, by rfl⟩ : syracuseStep 475429 = 89143) (by norm_num)
theorem B213313 : Blo 187803 213313 := bbase (se 2 (by rfl) ⟨79992, by rfl⟩ : syracuseStep 213313 = 159985) (by norm_num)
theorem B213349 : Blo 187803 213349 := bbase (se 4 (by rfl) ⟨20001, by rfl⟩ : syracuseStep 213349 = 40003) (by norm_num)
theorem B213385 : Blo 187803 213385 := bbase (se 2 (by rfl) ⟨80019, by rfl⟩ : syracuseStep 213385 = 160039) (by norm_num)
theorem B475541 : Blo 187803 475541 := bbase (se 6 (by rfl) ⟨11145, by rfl⟩ : syracuseStep 475541 = 22291) (by norm_num)
theorem B213421 : Blo 187803 213421 := bbase (se 3 (by rfl) ⟨40016, by rfl⟩ : syracuseStep 213421 = 80033) (by norm_num)
theorem B639413 : Blo 187803 639413 := bbase (se 5 (by rfl) ⟨29972, by rfl⟩ : syracuseStep 639413 = 59945) (by norm_num)
theorem B213457 : Blo 187803 213457 := bbase (se 2 (by rfl) ⟨80046, by rfl⟩ : syracuseStep 213457 = 160093) (by norm_num)
theorem B213493 : Blo 187803 213493 := bbase (se 5 (by rfl) ⟨10007, by rfl⟩ : syracuseStep 213493 = 20015) (by norm_num)
theorem B213529 : Blo 187803 213529 := bbase (se 2 (by rfl) ⟨80073, by rfl⟩ : syracuseStep 213529 = 160147) (by norm_num)
theorem B541237 : Blo 187803 541237 := bbase (se 5 (by rfl) ⟨25370, by rfl⟩ : syracuseStep 541237 = 50741) (by norm_num)
theorem B213565 : Blo 187803 213565 := bbase (se 3 (by rfl) ⟨40043, by rfl⟩ : syracuseStep 213565 = 80087) (by norm_num)
theorem B475733 : Blo 187803 475733 := bbase (se 8 (by rfl) ⟨2787, by rfl⟩ : syracuseStep 475733 = 5575) (by norm_num)
theorem B213601 : Blo 187803 213601 := bbase (se 2 (by rfl) ⟨80100, by rfl⟩ : syracuseStep 213601 = 160201) (by norm_num)
theorem B213637 : Blo 187803 213637 := bbase (se 4 (by rfl) ⟨20028, by rfl⟩ : syracuseStep 213637 = 40057) (by norm_num)
theorem B967301 : Blo 187803 967301 := bbase (se 4 (by rfl) ⟨90684, by rfl⟩ : syracuseStep 967301 = 181369) (by norm_num)
theorem B443029 : Blo 187803 443029 := bbase (se 6 (by rfl) ⟨10383, by rfl⟩ : syracuseStep 443029 = 20767) (by norm_num)
theorem B213673 : Blo 187803 213673 := bbase (se 2 (by rfl) ⟨80127, by rfl⟩ : syracuseStep 213673 = 160255) (by norm_num)
theorem B213709 : Blo 187803 213709 := bbase (se 3 (by rfl) ⟨40070, by rfl⟩ : syracuseStep 213709 = 80141) (by norm_num)
theorem B541397 : Blo 187803 541397 := bbase (se 7 (by rfl) ⟨6344, by rfl⟩ : syracuseStep 541397 = 12689) (by norm_num)
theorem B213745 : Blo 187803 213745 := bbase (se 2 (by rfl) ⟨80154, by rfl⟩ : syracuseStep 213745 = 160309) (by norm_num)
theorem B213781 : Blo 187803 213781 := bbase (se 6 (by rfl) ⟨5010, by rfl⟩ : syracuseStep 213781 = 10021) (by norm_num)
theorem B803621 : Blo 187803 803621 := bbase (se 4 (by rfl) ⟨75339, by rfl⟩ : syracuseStep 803621 = 150679) (by norm_num)
theorem B213817 : Blo 187803 213817 := bbase (se 2 (by rfl) ⟨80181, by rfl⟩ : syracuseStep 213817 = 160363) (by norm_num)
theorem B4146005 : Blo 187803 4146005 := bbase (se 9 (by rfl) ⟨12146, by rfl⟩ : syracuseStep 4146005 = 24293) (by norm_num)
theorem B213853 : Blo 187803 213853 := bbase (se 3 (by rfl) ⟨40097, by rfl⟩ : syracuseStep 213853 = 80195) (by norm_num)
theorem B639845 : Blo 187803 639845 := bbase (se 4 (by rfl) ⟨59985, by rfl⟩ : syracuseStep 639845 = 119971) (by norm_num)
theorem B213889 : Blo 187803 213889 := bbase (se 2 (by rfl) ⟨80208, by rfl⟩ : syracuseStep 213889 = 160417) (by norm_num)
theorem B213925 : Blo 187803 213925 := bbase (se 4 (by rfl) ⟨20055, by rfl⟩ : syracuseStep 213925 = 40111) (by norm_num)
theorem B476077 : Blo 187803 476077 := bbase (se 3 (by rfl) ⟨89264, by rfl⟩ : syracuseStep 476077 = 178529) (by norm_num)
theorem B1098677 : Blo 187803 1098677 := bbase (se 5 (by rfl) ⟨51500, by rfl⟩ : syracuseStep 1098677 = 103001) (by norm_num)
theorem B541637 : Blo 187803 541637 := bbase (se 4 (by rfl) ⟨50778, by rfl⟩ : syracuseStep 541637 = 101557) (by norm_num)
theorem B213961 : Blo 187803 213961 := bbase (se 2 (by rfl) ⟨80235, by rfl⟩ : syracuseStep 213961 = 160471) (by norm_num)
theorem B607189 : Blo 187803 607189 := bbase (se 7 (by rfl) ⟨7115, by rfl⟩ : syracuseStep 607189 = 14231) (by norm_num)
theorem B213997 : Blo 187803 213997 := bbase (se 3 (by rfl) ⟨40124, by rfl⟩ : syracuseStep 213997 = 80249) (by norm_num)
theorem B214033 : Blo 187803 214033 := bbase (se 2 (by rfl) ⟨80262, by rfl⟩ : syracuseStep 214033 = 160525) (by norm_num)
theorem B476189 : Blo 187803 476189 := bbase (se 3 (by rfl) ⟨89285, by rfl⟩ : syracuseStep 476189 = 178571) (by norm_num)
theorem B574517 : Blo 187803 574517 := bbase (se 5 (by rfl) ⟨26930, by rfl⟩ : syracuseStep 574517 = 53861) (by norm_num)
theorem B214069 : Blo 187803 214069 := bbase (se 5 (by rfl) ⟨10034, by rfl⟩ : syracuseStep 214069 = 20069) (by norm_num)
theorem B214105 : Blo 187803 214105 := bbase (se 2 (by rfl) ⟨80289, by rfl⟩ : syracuseStep 214105 = 160579) (by norm_num)
theorem B214141 : Blo 187803 214141 := bbase (se 3 (by rfl) ⟨40151, by rfl⟩ : syracuseStep 214141 = 80303) (by norm_num)
theorem B541829 : Blo 187803 541829 := bbase (se 4 (by rfl) ⟨50796, by rfl⟩ : syracuseStep 541829 = 101593) (by norm_num)
theorem B214177 : Blo 187803 214177 := bbase (se 2 (by rfl) ⟨80316, by rfl⟩ : syracuseStep 214177 = 160633) (by norm_num)
theorem B214213 : Blo 187803 214213 := bbase (se 4 (by rfl) ⟨20082, by rfl⟩ : syracuseStep 214213 = 40165) (by norm_num)
theorem B476381 : Blo 187803 476381 := bbase (se 3 (by rfl) ⟨89321, by rfl⟩ : syracuseStep 476381 = 178643) (by norm_num)
theorem B214249 : Blo 187803 214249 := bbase (se 2 (by rfl) ⟨80343, by rfl⟩ : syracuseStep 214249 = 160687) (by norm_num)
theorem B214285 : Blo 187803 214285 := bbase (se 3 (by rfl) ⟨40178, by rfl⟩ : syracuseStep 214285 = 80357) (by norm_num)
theorem B1525013 : Blo 187803 1525013 := bbase (se 6 (by rfl) ⟨35742, by rfl⟩ : syracuseStep 1525013 = 71485) (by norm_num)
theorem B640277 : Blo 187803 640277 := bbase (se 6 (by rfl) ⟨15006, by rfl⟩ : syracuseStep 640277 = 30013) (by norm_num)
theorem B214309 : Blo 187803 214309 := bbase (se 4 (by rfl) ⟨20091, by rfl⟩ : syracuseStep 214309 = 40183) (by norm_num)
theorem B214321 : Blo 187803 214321 := bbase (se 2 (by rfl) ⟨80370, by rfl⟩ : syracuseStep 214321 = 160741) (by norm_num)
theorem B214357 : Blo 187803 214357 := bbase (se 12 (by rfl) ⟨78, by rfl⟩ : syracuseStep 214357 = 157) (by norm_num)
theorem B214393 : Blo 187803 214393 := bbase (se 2 (by rfl) ⟨80397, by rfl⟩ : syracuseStep 214393 = 160795) (by norm_num)
theorem B607637 : Blo 187803 607637 := bbase (se 6 (by rfl) ⟨14241, by rfl⟩ : syracuseStep 607637 = 28483) (by norm_num)
theorem B214429 : Blo 187803 214429 := bbase (se 3 (by rfl) ⟨40205, by rfl⟩ : syracuseStep 214429 = 80411) (by norm_num)
theorem B214465 : Blo 187803 214465 := bbase (se 2 (by rfl) ⟨80424, by rfl⟩ : syracuseStep 214465 = 160849) (by norm_num)
theorem B476621 : Blo 187803 476621 := bbase (se 3 (by rfl) ⟨89366, by rfl⟩ : syracuseStep 476621 = 178733) (by norm_num)
theorem B214501 : Blo 187803 214501 := bbase (se 4 (by rfl) ⟨20109, by rfl⟩ : syracuseStep 214501 = 40219) (by norm_num)
theorem B509429 : Blo 187803 509429 := bbase (se 5 (by rfl) ⟨23879, by rfl⟩ : syracuseStep 509429 = 47759) (by norm_num)
theorem B214537 : Blo 187803 214537 := bbase (se 2 (by rfl) ⟨80451, by rfl⟩ : syracuseStep 214537 = 160903) (by norm_num)
theorem B214573 : Blo 187803 214573 := bbase (se 3 (by rfl) ⟨40232, by rfl⟩ : syracuseStep 214573 = 80465) (by norm_num)
theorem B1525301 : Blo 187803 1525301 := bbase (se 5 (by rfl) ⟨71498, by rfl⟩ : syracuseStep 1525301 = 142997) (by norm_num)
theorem B476725 : Blo 187803 476725 := bbase (se 5 (by rfl) ⟨22346, by rfl⟩ : syracuseStep 476725 = 44693) (by norm_num)
theorem B214609 : Blo 187803 214609 := bbase (se 2 (by rfl) ⟨80478, by rfl⟩ : syracuseStep 214609 = 160957) (by norm_num)
theorem B214645 : Blo 187803 214645 := bbase (se 5 (by rfl) ⟨10061, by rfl⟩ : syracuseStep 214645 = 20123) (by norm_num)
theorem B214681 : Blo 187803 214681 := bbase (se 2 (by rfl) ⟨80505, by rfl⟩ : syracuseStep 214681 = 161011) (by norm_num)
theorem B476837 : Blo 187803 476837 := bbase (se 4 (by rfl) ⟨44703, by rfl⟩ : syracuseStep 476837 = 89407) (by norm_num)
theorem B214717 : Blo 187803 214717 := bbase (se 3 (by rfl) ⟨40259, by rfl⟩ : syracuseStep 214717 = 80519) (by norm_num)
theorem B640709 : Blo 187803 640709 := bbase (se 4 (by rfl) ⟨60066, by rfl⟩ : syracuseStep 640709 = 120133) (by norm_num)
theorem B214753 : Blo 187803 214753 := bbase (se 2 (by rfl) ⟨80532, by rfl⟩ : syracuseStep 214753 = 161065) (by norm_num)
theorem B1033973 : Blo 187803 1033973 := bbase (se 5 (by rfl) ⟨48467, by rfl⟩ : syracuseStep 1033973 = 96935) (by norm_num)
theorem B214789 : Blo 187803 214789 := bbase (se 4 (by rfl) ⟨20136, by rfl⟩ : syracuseStep 214789 = 40273) (by norm_num)
theorem B214825 : Blo 187803 214825 := bbase (se 2 (by rfl) ⟨80559, by rfl⟩ : syracuseStep 214825 = 161119) (by norm_num)
theorem B214861 : Blo 187803 214861 := bbase (se 3 (by rfl) ⟨40286, by rfl⟩ : syracuseStep 214861 = 80573) (by norm_num)
theorem B477029 : Blo 187803 477029 := bbase (se 4 (by rfl) ⟨44721, by rfl⟩ : syracuseStep 477029 = 89443) (by norm_num)
theorem B214897 : Blo 187803 214897 := bbase (se 2 (by rfl) ⟨80586, by rfl⟩ : syracuseStep 214897 = 161173) (by norm_num)
theorem B214933 : Blo 187803 214933 := bbase (se 6 (by rfl) ⟨5037, by rfl⟩ : syracuseStep 214933 = 10075) (by norm_num)
theorem B968597 : Blo 187803 968597 := bbase (se 6 (by rfl) ⟨22701, by rfl⟩ : syracuseStep 968597 = 45403) (by norm_num)
theorem B1427381 : Blo 187803 1427381 := bbase (se 5 (by rfl) ⟨66908, by rfl⟩ : syracuseStep 1427381 = 133817) (by norm_num)
theorem B214969 : Blo 187803 214969 := bbase (se 2 (by rfl) ⟨80613, by rfl⟩ : syracuseStep 214969 = 161227) (by norm_num)
theorem B215005 : Blo 187803 215005 := bbase (se 3 (by rfl) ⟨40313, by rfl⟩ : syracuseStep 215005 = 80627) (by norm_num)
theorem B215041 : Blo 187803 215041 := bbase (se 2 (by rfl) ⟨80640, by rfl⟩ : syracuseStep 215041 = 161281) (by norm_num)
theorem B215077 : Blo 187803 215077 := bbase (se 4 (by rfl) ⟨20163, by rfl⟩ : syracuseStep 215077 = 40327) (by norm_num)
theorem B215113 : Blo 187803 215113 := bbase (se 2 (by rfl) ⟨80667, by rfl⟩ : syracuseStep 215113 = 161335) (by norm_num)
theorem B542821 : Blo 187803 542821 := bbase (se 4 (by rfl) ⟨50889, by rfl⟩ : syracuseStep 542821 = 101779) (by norm_num)
theorem B215149 : Blo 187803 215149 := bbase (se 3 (by rfl) ⟨40340, by rfl⟩ : syracuseStep 215149 = 80681) (by norm_num)
theorem B641141 : Blo 187803 641141 := bbase (se 5 (by rfl) ⟨30053, by rfl⟩ : syracuseStep 641141 = 60107) (by norm_num)
theorem B215185 : Blo 187803 215185 := bbase (se 2 (by rfl) ⟨80694, by rfl⟩ : syracuseStep 215185 = 161389) (by norm_num)
theorem B215221 : Blo 187803 215221 := bbase (se 5 (by rfl) ⟨10088, by rfl⟩ : syracuseStep 215221 = 20177) (by norm_num)
theorem B477373 : Blo 187803 477373 := bbase (se 3 (by rfl) ⟨89507, by rfl⟩ : syracuseStep 477373 = 179015) (by norm_num)
theorem B215257 : Blo 187803 215257 := bbase (se 2 (by rfl) ⟨80721, by rfl⟩ : syracuseStep 215257 = 161443) (by norm_num)
theorem B215293 : Blo 187803 215293 := bbase (se 3 (by rfl) ⟨40367, by rfl⟩ : syracuseStep 215293 = 80735) (by norm_num)
theorem B215329 : Blo 187803 215329 := bbase (se 2 (by rfl) ⟨80748, by rfl⟩ : syracuseStep 215329 = 161497) (by norm_num)
theorem B477485 : Blo 187803 477485 := bbase (se 3 (by rfl) ⟨89528, by rfl⟩ : syracuseStep 477485 = 179057) (by norm_num)
theorem B215365 : Blo 187803 215365 := bbase (se 4 (by rfl) ⟨20190, by rfl⟩ : syracuseStep 215365 = 40381) (by norm_num)
theorem B215401 : Blo 187803 215401 := bbase (se 2 (by rfl) ⟨80775, by rfl⟩ : syracuseStep 215401 = 161551) (by norm_num)
theorem B215437 : Blo 187803 215437 := bbase (se 3 (by rfl) ⟨40394, by rfl⟩ : syracuseStep 215437 = 80789) (by norm_num)
theorem B215473 : Blo 187803 215473 := bbase (se 2 (by rfl) ⟨80802, by rfl⟩ : syracuseStep 215473 = 161605) (by norm_num)
theorem B215509 : Blo 187803 215509 := bbase (se 7 (by rfl) ⟨2525, by rfl⟩ : syracuseStep 215509 = 5051) (by norm_num)
theorem B477677 : Blo 187803 477677 := bbase (se 3 (by rfl) ⟨89564, by rfl⟩ : syracuseStep 477677 = 179129) (by norm_num)
theorem B215545 : Blo 187803 215545 := bbase (se 2 (by rfl) ⟨80829, by rfl⟩ : syracuseStep 215545 = 161659) (by norm_num)
theorem B215581 : Blo 187803 215581 := bbase (se 3 (by rfl) ⟨40421, by rfl⟩ : syracuseStep 215581 = 80843) (by norm_num)
theorem B641573 : Blo 187803 641573 := bbase (se 4 (by rfl) ⟨60147, by rfl⟩ : syracuseStep 641573 = 120295) (by norm_num)
theorem B215617 : Blo 187803 215617 := bbase (se 2 (by rfl) ⟨80856, by rfl⟩ : syracuseStep 215617 = 161713) (by norm_num)
theorem B215653 : Blo 187803 215653 := bbase (se 4 (by rfl) ⟨20217, by rfl⟩ : syracuseStep 215653 = 40435) (by norm_num)
theorem B215689 : Blo 187803 215689 := bbase (se 2 (by rfl) ⟨80883, by rfl⟩ : syracuseStep 215689 = 161767) (by norm_num)
theorem B215725 : Blo 187803 215725 := bbase (se 3 (by rfl) ⟨40448, by rfl⟩ : syracuseStep 215725 = 80897) (by norm_num)
theorem B215761 : Blo 187803 215761 := bbase (se 2 (by rfl) ⟨80910, by rfl⟩ : syracuseStep 215761 = 161821) (by norm_num)
theorem B478021 : Blo 187803 478021 := bbase (se 4 (by rfl) ⟨44814, by rfl⟩ : syracuseStep 478021 = 89629) (by norm_num)
theorem B478133 : Blo 187803 478133 := bbase (se 5 (by rfl) ⟨22412, by rfl⟩ : syracuseStep 478133 = 44825) (by norm_num)
theorem B642005 : Blo 187803 642005 := bbase (se 7 (by rfl) ⟨7523, by rfl⟩ : syracuseStep 642005 = 15047) (by norm_num)
theorem B248845 : Blo 187803 248845 := bbase (se 3 (by rfl) ⟨46658, by rfl⟩ : syracuseStep 248845 = 93317) (by norm_num)
theorem B281717 : Blo 187803 281717 := bbase (se 5 (by rfl) ⟨13205, by rfl⟩ : syracuseStep 281717 = 26411) (by norm_num)
theorem B478325 : Blo 187803 478325 := bbase (se 5 (by rfl) ⟨22421, by rfl⟩ : syracuseStep 478325 = 44843) (by norm_num)
theorem B281741 : Blo 187803 281741 := bbase (se 3 (by rfl) ⟨52826, by rfl⟩ : syracuseStep 281741 = 105653) (by norm_num)
theorem B281765 : Blo 187803 281765 := bbase (se 4 (by rfl) ⟨26415, by rfl⟩ : syracuseStep 281765 = 52831) (by norm_num)
theorem B969893 : Blo 187803 969893 := bbase (se 4 (by rfl) ⟨90927, by rfl⟩ : syracuseStep 969893 = 181855) (by norm_num)
theorem B543925 : Blo 187803 543925 := bbase (se 5 (by rfl) ⟨25496, by rfl⟩ : syracuseStep 543925 = 50993) (by norm_num)
theorem B281789 : Blo 187803 281789 := bbase (se 3 (by rfl) ⟨52835, by rfl⟩ : syracuseStep 281789 = 105671) (by norm_num)
theorem B281813 : Blo 187803 281813 := bbase (se 7 (by rfl) ⟨3302, by rfl⟩ : syracuseStep 281813 = 6605) (by norm_num)
theorem B281837 : Blo 187803 281837 := bbase (se 3 (by rfl) ⟨52844, by rfl⟩ : syracuseStep 281837 = 105689) (by norm_num)
theorem B216317 : Blo 187803 216317 := bbase (se 3 (by rfl) ⟨40559, by rfl⟩ : syracuseStep 216317 = 81119) (by norm_num)
theorem B281861 : Blo 187803 281861 := bbase (se 4 (by rfl) ⟨26424, by rfl⟩ : syracuseStep 281861 = 52849) (by norm_num)
theorem B642325 : Blo 187803 642325 := bbase (se 6 (by rfl) ⟨15054, by rfl⟩ : syracuseStep 642325 = 30109) (by norm_num)
theorem B281885 : Blo 187803 281885 := bbase (se 3 (by rfl) ⟨52853, by rfl⟩ : syracuseStep 281885 = 105707) (by norm_num)
theorem B281909 : Blo 187803 281909 := bbase (se 5 (by rfl) ⟨13214, by rfl⟩ : syracuseStep 281909 = 26429) (by norm_num)
theorem B281933 : Blo 187803 281933 := bbase (se 3 (by rfl) ⟨52862, by rfl⟩ : syracuseStep 281933 = 105725) (by norm_num)
theorem B281957 : Blo 187803 281957 := bbase (se 4 (by rfl) ⟨26433, by rfl⟩ : syracuseStep 281957 = 52867) (by norm_num)
theorem B281981 : Blo 187803 281981 := bbase (se 3 (by rfl) ⟨52871, by rfl⟩ : syracuseStep 281981 = 105743) (by norm_num)
theorem B642437 : Blo 187803 642437 := bbase (se 4 (by rfl) ⟨60228, by rfl⟩ : syracuseStep 642437 = 120457) (by norm_num)
theorem B282005 : Blo 187803 282005 := bbase (se 6 (by rfl) ⟨6609, by rfl⟩ : syracuseStep 282005 = 13219) (by norm_num)
theorem B282029 : Blo 187803 282029 := bbase (se 3 (by rfl) ⟨52880, by rfl⟩ : syracuseStep 282029 = 105761) (by norm_num)
theorem B282053 : Blo 187803 282053 := bbase (se 4 (by rfl) ⟨26442, by rfl⟩ : syracuseStep 282053 = 52885) (by norm_num)
theorem B478669 : Blo 187803 478669 := bbase (se 3 (by rfl) ⟨89750, by rfl⟩ : syracuseStep 478669 = 179501) (by norm_num)
theorem B282077 : Blo 187803 282077 := bbase (se 3 (by rfl) ⟨52889, by rfl⟩ : syracuseStep 282077 = 105779) (by norm_num)
theorem B282101 : Blo 187803 282101 := bbase (se 5 (by rfl) ⟨13223, by rfl⟩ : syracuseStep 282101 = 26447) (by norm_num)
theorem B282125 : Blo 187803 282125 := bbase (se 3 (by rfl) ⟨52898, by rfl⟩ : syracuseStep 282125 = 105797) (by norm_num)
theorem B282149 : Blo 187803 282149 := bbase (se 4 (by rfl) ⟨26451, by rfl⟩ : syracuseStep 282149 = 52903) (by norm_num)
theorem B282173 : Blo 187803 282173 := bbase (se 3 (by rfl) ⟨52907, by rfl⟩ : syracuseStep 282173 = 105815) (by norm_num)
theorem B478781 : Blo 187803 478781 := bbase (se 3 (by rfl) ⟨89771, by rfl⟩ : syracuseStep 478781 = 179543) (by norm_num)
theorem B282197 : Blo 187803 282197 := bbase (se 8 (by rfl) ⟨1653, by rfl⟩ : syracuseStep 282197 = 3307) (by norm_num)
theorem B609893 : Blo 187803 609893 := bbase (se 4 (by rfl) ⟨57177, by rfl⟩ : syracuseStep 609893 = 114355) (by norm_num)
theorem B282221 : Blo 187803 282221 := bbase (se 3 (by rfl) ⟨52916, by rfl⟩ : syracuseStep 282221 = 105833) (by norm_num)
theorem B282245 : Blo 187803 282245 := bbase (se 4 (by rfl) ⟨26460, by rfl⟩ : syracuseStep 282245 = 52921) (by norm_num)
theorem B282269 : Blo 187803 282269 := bbase (se 3 (by rfl) ⟨52925, by rfl⟩ : syracuseStep 282269 = 105851) (by norm_num)
theorem B282293 : Blo 187803 282293 := bbase (se 5 (by rfl) ⟨13232, by rfl⟩ : syracuseStep 282293 = 26465) (by norm_num)
theorem B282317 : Blo 187803 282317 := bbase (se 3 (by rfl) ⟨52934, by rfl⟩ : syracuseStep 282317 = 105869) (by norm_num)
theorem B282341 : Blo 187803 282341 := bbase (se 4 (by rfl) ⟨26469, by rfl⟩ : syracuseStep 282341 = 52939) (by norm_num)
theorem B282365 : Blo 187803 282365 := bbase (se 3 (by rfl) ⟨52943, by rfl⟩ : syracuseStep 282365 = 105887) (by norm_num)
theorem B478973 : Blo 187803 478973 := bbase (se 3 (by rfl) ⟨89807, by rfl⟩ : syracuseStep 478973 = 179615) (by norm_num)
theorem B282389 : Blo 187803 282389 := bbase (se 6 (by rfl) ⟨6618, by rfl⟩ : syracuseStep 282389 = 13237) (by norm_num)
theorem B282413 : Blo 187803 282413 := bbase (se 3 (by rfl) ⟨52952, by rfl⟩ : syracuseStep 282413 = 105905) (by norm_num)
theorem B642869 : Blo 187803 642869 := bbase (se 5 (by rfl) ⟨30134, by rfl⟩ : syracuseStep 642869 = 60269) (by norm_num)
theorem B282437 : Blo 187803 282437 := bbase (se 4 (by rfl) ⟨26478, by rfl⟩ : syracuseStep 282437 = 52957) (by norm_num)
theorem B282461 : Blo 187803 282461 := bbase (se 3 (by rfl) ⟨52961, by rfl⟩ : syracuseStep 282461 = 105923) (by norm_num)
theorem B282485 : Blo 187803 282485 := bbase (se 5 (by rfl) ⟨13241, by rfl⟩ : syracuseStep 282485 = 26483) (by norm_num)
theorem B282509 : Blo 187803 282509 := bbase (se 3 (by rfl) ⟨52970, by rfl⟩ : syracuseStep 282509 = 105941) (by norm_num)
theorem B282533 : Blo 187803 282533 := bbase (se 4 (by rfl) ⟨26487, by rfl⟩ : syracuseStep 282533 = 52975) (by norm_num)
theorem B282557 : Blo 187803 282557 := bbase (se 3 (by rfl) ⟨52979, by rfl⟩ : syracuseStep 282557 = 105959) (by norm_num)
theorem B282581 : Blo 187803 282581 := bbase (se 7 (by rfl) ⟨3311, by rfl⟩ : syracuseStep 282581 = 6623) (by norm_num)
theorem B282605 : Blo 187803 282605 := bbase (se 3 (by rfl) ⟨52988, by rfl⟩ : syracuseStep 282605 = 105977) (by norm_num)
theorem B282629 : Blo 187803 282629 := bbase (se 4 (by rfl) ⟨26496, by rfl⟩ : syracuseStep 282629 = 52993) (by norm_num)
theorem B282653 : Blo 187803 282653 := bbase (se 3 (by rfl) ⟨52997, by rfl⟩ : syracuseStep 282653 = 105995) (by norm_num)
theorem B282677 : Blo 187803 282677 := bbase (se 5 (by rfl) ⟨13250, by rfl⟩ : syracuseStep 282677 = 26501) (by norm_num)
theorem B282701 : Blo 187803 282701 := bbase (se 3 (by rfl) ⟨53006, by rfl⟩ : syracuseStep 282701 = 106013) (by norm_num)
theorem B479317 : Blo 187803 479317 := bbase (se 8 (by rfl) ⟨2808, by rfl⟩ : syracuseStep 479317 = 5617) (by norm_num)
theorem B282725 : Blo 187803 282725 := bbase (se 4 (by rfl) ⟨26505, by rfl⟩ : syracuseStep 282725 = 53011) (by norm_num)
theorem B282749 : Blo 187803 282749 := bbase (se 3 (by rfl) ⟨53015, by rfl⟩ : syracuseStep 282749 = 106031) (by norm_num)
theorem B282773 : Blo 187803 282773 := bbase (se 6 (by rfl) ⟨6627, by rfl⟩ : syracuseStep 282773 = 13255) (by norm_num)
theorem B2150549 : Blo 187803 2150549 := bbase (se 6 (by rfl) ⟨50403, by rfl⟩ : syracuseStep 2150549 = 100807) (by norm_num)
theorem B282797 : Blo 187803 282797 := bbase (se 3 (by rfl) ⟨53024, by rfl⟩ : syracuseStep 282797 = 106049) (by norm_num)
theorem B282821 : Blo 187803 282821 := bbase (se 4 (by rfl) ⟨26514, by rfl⟩ : syracuseStep 282821 = 53029) (by norm_num)
theorem B479429 : Blo 187803 479429 := bbase (se 4 (by rfl) ⟨44946, by rfl⟩ : syracuseStep 479429 = 89893) (by norm_num)
theorem B282845 : Blo 187803 282845 := bbase (se 3 (by rfl) ⟨53033, by rfl⟩ : syracuseStep 282845 = 106067) (by norm_num)
theorem B643301 : Blo 187803 643301 := bbase (se 4 (by rfl) ⟨60309, by rfl⟩ : syracuseStep 643301 = 120619) (by norm_num)
theorem B282869 : Blo 187803 282869 := bbase (se 5 (by rfl) ⟨13259, by rfl⟩ : syracuseStep 282869 = 26519) (by norm_num)
theorem B282893 : Blo 187803 282893 := bbase (se 3 (by rfl) ⟨53042, by rfl⟩ : syracuseStep 282893 = 106085) (by norm_num)
theorem B282917 : Blo 187803 282917 := bbase (se 4 (by rfl) ⟨26523, by rfl⟩ : syracuseStep 282917 = 53047) (by norm_num)
theorem B282941 : Blo 187803 282941 := bbase (se 3 (by rfl) ⟨53051, by rfl⟩ : syracuseStep 282941 = 106103) (by norm_num)
theorem B282965 : Blo 187803 282965 := bbase (se 10 (by rfl) ⟨414, by rfl⟩ : syracuseStep 282965 = 829) (by norm_num)
theorem B905573 : Blo 187803 905573 := bbase (se 4 (by rfl) ⟨84897, by rfl⟩ : syracuseStep 905573 = 169795) (by norm_num)
theorem B282989 : Blo 187803 282989 := bbase (se 3 (by rfl) ⟨53060, by rfl⟩ : syracuseStep 282989 = 106121) (by norm_num)
theorem B283013 : Blo 187803 283013 := bbase (se 4 (by rfl) ⟨26532, by rfl⟩ : syracuseStep 283013 = 53065) (by norm_num)
theorem B479621 : Blo 187803 479621 := bbase (se 4 (by rfl) ⟨44964, by rfl⟩ : syracuseStep 479621 = 89929) (by norm_num)
theorem B283037 : Blo 187803 283037 := bbase (se 3 (by rfl) ⟨53069, by rfl⟩ : syracuseStep 283037 = 106139) (by norm_num)
theorem B283061 : Blo 187803 283061 := bbase (se 5 (by rfl) ⟨13268, by rfl⟩ : syracuseStep 283061 = 26537) (by norm_num)
theorem B971189 : Blo 187803 971189 := bbase (se 5 (by rfl) ⟨45524, by rfl⟩ : syracuseStep 971189 = 91049) (by norm_num)
theorem B283085 : Blo 187803 283085 := bbase (se 3 (by rfl) ⟨53078, by rfl⟩ : syracuseStep 283085 = 106157) (by norm_num)
theorem B1626581 : Blo 187803 1626581 := bbase (se 7 (by rfl) ⟨19061, by rfl⟩ : syracuseStep 1626581 = 38123) (by norm_num)
theorem B283109 : Blo 187803 283109 := bbase (se 4 (by rfl) ⟨26541, by rfl⟩ : syracuseStep 283109 = 53083) (by norm_num)
theorem B1102325 : Blo 187803 1102325 := bbase (se 5 (by rfl) ⟨51671, by rfl⟩ : syracuseStep 1102325 = 103343) (by norm_num)
theorem B283133 : Blo 187803 283133 := bbase (se 3 (by rfl) ⟨53087, by rfl⟩ : syracuseStep 283133 = 106175) (by norm_num)
theorem B283157 : Blo 187803 283157 := bbase (se 6 (by rfl) ⟨6636, by rfl⟩ : syracuseStep 283157 = 13273) (by norm_num)
theorem B283181 : Blo 187803 283181 := bbase (se 3 (by rfl) ⟨53096, by rfl⟩ : syracuseStep 283181 = 106193) (by norm_num)
theorem B283205 : Blo 187803 283205 := bbase (se 4 (by rfl) ⟨26550, by rfl⟩ : syracuseStep 283205 = 53101) (by norm_num)
theorem B283229 : Blo 187803 283229 := bbase (se 3 (by rfl) ⟨53105, by rfl⟩ : syracuseStep 283229 = 106211) (by norm_num)
theorem B971365 : Blo 187803 971365 := bbase (se 4 (by rfl) ⟨91065, by rfl⟩ : syracuseStep 971365 = 182131) (by norm_num)
theorem B283253 : Blo 187803 283253 := bbase (se 5 (by rfl) ⟨13277, by rfl⟩ : syracuseStep 283253 = 26555) (by norm_num)
theorem B283277 : Blo 187803 283277 := bbase (se 3 (by rfl) ⟨53114, by rfl⟩ : syracuseStep 283277 = 106229) (by norm_num)
theorem B643733 : Blo 187803 643733 := bbase (se 6 (by rfl) ⟨15087, by rfl⟩ : syracuseStep 643733 = 30175) (by norm_num)
theorem B545429 : Blo 187803 545429 := bbase (se 6 (by rfl) ⟨12783, by rfl⟩ : syracuseStep 545429 = 25567) (by norm_num)
theorem B283301 : Blo 187803 283301 := bbase (se 4 (by rfl) ⟨26559, by rfl⟩ : syracuseStep 283301 = 53119) (by norm_num)
theorem B283325 : Blo 187803 283325 := bbase (se 3 (by rfl) ⟨53123, by rfl⟩ : syracuseStep 283325 = 106247) (by norm_num)
theorem B840389 : Blo 187803 840389 := bbase (se 4 (by rfl) ⟨78786, by rfl⟩ : syracuseStep 840389 = 157573) (by norm_num)
theorem B283349 : Blo 187803 283349 := bbase (se 7 (by rfl) ⟨3320, by rfl⟩ : syracuseStep 283349 = 6641) (by norm_num)
theorem B479965 : Blo 187803 479965 := bbase (se 3 (by rfl) ⟨89993, by rfl⟩ : syracuseStep 479965 = 179987) (by norm_num)
theorem B217825 : Blo 187803 217825 := bbase (se 2 (by rfl) ⟨81684, by rfl⟩ : syracuseStep 217825 = 163369) (by norm_num)
theorem B283373 : Blo 187803 283373 := bbase (se 3 (by rfl) ⟨53132, by rfl⟩ : syracuseStep 283373 = 106265) (by norm_num)
theorem B283397 : Blo 187803 283397 := bbase (se 4 (by rfl) ⟨26568, by rfl⟩ : syracuseStep 283397 = 53137) (by norm_num)
theorem B283421 : Blo 187803 283421 := bbase (se 3 (by rfl) ⟨53141, by rfl⟩ : syracuseStep 283421 = 106283) (by norm_num)
theorem B283445 : Blo 187803 283445 := bbase (se 5 (by rfl) ⟨13286, by rfl⟩ : syracuseStep 283445 = 26573) (by norm_num)
theorem B283469 : Blo 187803 283469 := bbase (se 3 (by rfl) ⟨53150, by rfl⟩ : syracuseStep 283469 = 106301) (by norm_num)
theorem B480077 : Blo 187803 480077 := bbase (se 3 (by rfl) ⟨90014, by rfl⟩ : syracuseStep 480077 = 180029) (by norm_num)
theorem B283493 : Blo 187803 283493 := bbase (se 4 (by rfl) ⟨26577, by rfl⟩ : syracuseStep 283493 = 53155) (by norm_num)
theorem B283517 : Blo 187803 283517 := bbase (se 3 (by rfl) ⟨53159, by rfl⟩ : syracuseStep 283517 = 106319) (by norm_num)
theorem B283541 : Blo 187803 283541 := bbase (se 6 (by rfl) ⟨6645, by rfl⟩ : syracuseStep 283541 = 13291) (by norm_num)
theorem B283565 : Blo 187803 283565 := bbase (se 3 (by rfl) ⟨53168, by rfl⟩ : syracuseStep 283565 = 106337) (by norm_num)
theorem B283589 : Blo 187803 283589 := bbase (se 4 (by rfl) ⟨26586, by rfl⟩ : syracuseStep 283589 = 53173) (by norm_num)
theorem B807893 : Blo 187803 807893 := bbase (se 7 (by rfl) ⟨9467, by rfl⟩ : syracuseStep 807893 = 18935) (by norm_num)
theorem B283613 : Blo 187803 283613 := bbase (se 3 (by rfl) ⟨53177, by rfl⟩ : syracuseStep 283613 = 106355) (by norm_num)
theorem B283637 : Blo 187803 283637 := bbase (se 5 (by rfl) ⟨13295, by rfl⟩ : syracuseStep 283637 = 26591) (by norm_num)
theorem B283661 : Blo 187803 283661 := bbase (se 3 (by rfl) ⟨53186, by rfl⟩ : syracuseStep 283661 = 106373) (by norm_num)
theorem B480269 : Blo 187803 480269 := bbase (se 3 (by rfl) ⟨90050, by rfl⟩ : syracuseStep 480269 = 180101) (by norm_num)
theorem B283685 : Blo 187803 283685 := bbase (se 4 (by rfl) ⟨26595, by rfl⟩ : syracuseStep 283685 = 53191) (by norm_num)
theorem B283709 : Blo 187803 283709 := bbase (se 3 (by rfl) ⟨53195, by rfl⟩ : syracuseStep 283709 = 106391) (by norm_num)
theorem B644165 : Blo 187803 644165 := bbase (se 4 (by rfl) ⟨60390, by rfl⟩ : syracuseStep 644165 = 120781) (by norm_num)
theorem B283733 : Blo 187803 283733 := bbase (se 8 (by rfl) ⟨1662, by rfl⟩ : syracuseStep 283733 = 3325) (by norm_num)
theorem B283757 : Blo 187803 283757 := bbase (se 3 (by rfl) ⟨53204, by rfl⟩ : syracuseStep 283757 = 106409) (by norm_num)
theorem B283781 : Blo 187803 283781 := bbase (se 4 (by rfl) ⟨26604, by rfl⟩ : syracuseStep 283781 = 53209) (by norm_num)
theorem B283805 : Blo 187803 283805 := bbase (se 3 (by rfl) ⟨53213, by rfl⟩ : syracuseStep 283805 = 106427) (by norm_num)
theorem B283829 : Blo 187803 283829 := bbase (se 5 (by rfl) ⟨13304, by rfl⟩ : syracuseStep 283829 = 26609) (by norm_num)
theorem B283853 : Blo 187803 283853 := bbase (se 3 (by rfl) ⟨53222, by rfl⟩ : syracuseStep 283853 = 106445) (by norm_num)
theorem B283877 : Blo 187803 283877 := bbase (se 4 (by rfl) ⟨26613, by rfl⟩ : syracuseStep 283877 = 53227) (by norm_num)
theorem B283901 : Blo 187803 283901 := bbase (se 3 (by rfl) ⟨53231, by rfl⟩ : syracuseStep 283901 = 106463) (by norm_num)
theorem B283925 : Blo 187803 283925 := bbase (se 6 (by rfl) ⟨6654, by rfl⟩ : syracuseStep 283925 = 13309) (by norm_num)
theorem B283949 : Blo 187803 283949 := bbase (se 3 (by rfl) ⟨53240, by rfl⟩ : syracuseStep 283949 = 106481) (by norm_num)
theorem B283973 : Blo 187803 283973 := bbase (se 4 (by rfl) ⟨26622, by rfl⟩ : syracuseStep 283973 = 53245) (by norm_num)
theorem B283997 : Blo 187803 283997 := bbase (se 3 (by rfl) ⟨53249, by rfl⟩ : syracuseStep 283997 = 106499) (by norm_num)
theorem B480613 : Blo 187803 480613 := bbase (se 4 (by rfl) ⟨45057, by rfl⟩ : syracuseStep 480613 = 90115) (by norm_num)
theorem B284021 : Blo 187803 284021 := bbase (se 5 (by rfl) ⟨13313, by rfl⟩ : syracuseStep 284021 = 26627) (by norm_num)
theorem B284045 : Blo 187803 284045 := bbase (se 3 (by rfl) ⟨53258, by rfl⟩ : syracuseStep 284045 = 106517) (by norm_num)
theorem B284069 : Blo 187803 284069 := bbase (se 4 (by rfl) ⟨26631, by rfl⟩ : syracuseStep 284069 = 53263) (by norm_num)
theorem B284093 : Blo 187803 284093 := bbase (se 3 (by rfl) ⟨53267, by rfl⟩ : syracuseStep 284093 = 106535) (by norm_num)
theorem B284117 : Blo 187803 284117 := bbase (se 7 (by rfl) ⟨3329, by rfl⟩ : syracuseStep 284117 = 6659) (by norm_num)
theorem B480725 : Blo 187803 480725 := bbase (se 7 (by rfl) ⟨5633, by rfl⟩ : syracuseStep 480725 = 11267) (by norm_num)
theorem B382429 : Blo 187803 382429 := bbase (se 3 (by rfl) ⟨71705, by rfl⟩ : syracuseStep 382429 = 143411) (by norm_num)
theorem B284141 : Blo 187803 284141 := bbase (se 3 (by rfl) ⟨53276, by rfl⟩ : syracuseStep 284141 = 106553) (by norm_num)
theorem B644597 : Blo 187803 644597 := bbase (se 5 (by rfl) ⟨30215, by rfl⟩ : syracuseStep 644597 = 60431) (by norm_num)
theorem B284165 : Blo 187803 284165 := bbase (se 4 (by rfl) ⟨26640, by rfl⟩ : syracuseStep 284165 = 53281) (by norm_num)
theorem B218629 : Blo 187803 218629 := bbase (se 4 (by rfl) ⟨20496, by rfl⟩ : syracuseStep 218629 = 40993) (by norm_num)
theorem B284189 : Blo 187803 284189 := bbase (se 3 (by rfl) ⟨53285, by rfl⟩ : syracuseStep 284189 = 106571) (by norm_num)
theorem B316973 : Blo 187803 316973 := bbase (se 3 (by rfl) ⟨59432, by rfl⟩ : syracuseStep 316973 = 118865) (by norm_num)
theorem B284213 : Blo 187803 284213 := bbase (se 5 (by rfl) ⟨13322, by rfl⟩ : syracuseStep 284213 = 26645) (by norm_num)
theorem B874037 : Blo 187803 874037 := bbase (se 5 (by rfl) ⟨40970, by rfl⟩ : syracuseStep 874037 = 81941) (by norm_num)
theorem B284237 : Blo 187803 284237 := bbase (se 3 (by rfl) ⟨53294, by rfl⟩ : syracuseStep 284237 = 106589) (by norm_num)
theorem B284261 : Blo 187803 284261 := bbase (se 4 (by rfl) ⟨26649, by rfl⟩ : syracuseStep 284261 = 53299) (by norm_num)
theorem B284285 : Blo 187803 284285 := bbase (se 3 (by rfl) ⟨53303, by rfl⟩ : syracuseStep 284285 = 106607) (by norm_num)
theorem B284309 : Blo 187803 284309 := bbase (se 6 (by rfl) ⟨6663, by rfl⟩ : syracuseStep 284309 = 13327) (by norm_num)
theorem B480917 : Blo 187803 480917 := bbase (se 6 (by rfl) ⟨11271, by rfl⟩ : syracuseStep 480917 = 22543) (by norm_num)
theorem B317101 : Blo 187803 317101 := bbase (se 3 (by rfl) ⟨59456, by rfl⟩ : syracuseStep 317101 = 118913) (by norm_num)
theorem B284333 : Blo 187803 284333 := bbase (se 3 (by rfl) ⟨53312, by rfl⟩ : syracuseStep 284333 = 106625) (by norm_num)
theorem B218801 : Blo 187803 218801 := bbase (se 2 (by rfl) ⟨82050, by rfl⟩ : syracuseStep 218801 = 164101) (by norm_num)
theorem B284357 : Blo 187803 284357 := bbase (se 4 (by rfl) ⟨26658, by rfl⟩ : syracuseStep 284357 = 53317) (by norm_num)
theorem B284381 : Blo 187803 284381 := bbase (se 3 (by rfl) ⟨53321, by rfl⟩ : syracuseStep 284381 = 106643) (by norm_num)
theorem B906997 : Blo 187803 906997 := bbase (se 5 (by rfl) ⟨42515, by rfl⟩ : syracuseStep 906997 = 85031) (by norm_num)
theorem B284405 : Blo 187803 284405 := bbase (se 5 (by rfl) ⟨13331, by rfl⟩ : syracuseStep 284405 = 26663) (by norm_num)
theorem B317189 : Blo 187803 317189 := bbase (se 4 (by rfl) ⟨29736, by rfl⟩ : syracuseStep 317189 = 59473) (by norm_num)
theorem B284429 : Blo 187803 284429 := bbase (se 3 (by rfl) ⟨53330, by rfl⟩ : syracuseStep 284429 = 106661) (by norm_num)
theorem B284453 : Blo 187803 284453 := bbase (se 4 (by rfl) ⟨26667, by rfl⟩ : syracuseStep 284453 = 53335) (by norm_num)
theorem B284477 : Blo 187803 284477 := bbase (se 3 (by rfl) ⟨53339, by rfl⟩ : syracuseStep 284477 = 106679) (by norm_num)
theorem B284501 : Blo 187803 284501 := bbase (se 9 (by rfl) ⟨833, by rfl⟩ : syracuseStep 284501 = 1667) (by norm_num)
theorem B284525 : Blo 187803 284525 := bbase (se 3 (by rfl) ⟨53348, by rfl⟩ : syracuseStep 284525 = 106697) (by norm_num)
theorem B317317 : Blo 187803 317317 := bbase (se 4 (by rfl) ⟨29748, by rfl⟩ : syracuseStep 317317 = 59497) (by norm_num)
theorem B284549 : Blo 187803 284549 := bbase (se 4 (by rfl) ⟨26676, by rfl⟩ : syracuseStep 284549 = 53353) (by norm_num)
theorem B284573 : Blo 187803 284573 := bbase (se 3 (by rfl) ⟨53357, by rfl⟩ : syracuseStep 284573 = 106715) (by norm_num)
theorem B645029 : Blo 187803 645029 := bbase (se 4 (by rfl) ⟨60471, by rfl⟩ : syracuseStep 645029 = 120943) (by norm_num)
theorem B284597 : Blo 187803 284597 := bbase (se 5 (by rfl) ⟨13340, by rfl⟩ : syracuseStep 284597 = 26681) (by norm_num)
theorem B284621 : Blo 187803 284621 := bbase (se 3 (by rfl) ⟨53366, by rfl⟩ : syracuseStep 284621 = 106733) (by norm_num)
theorem B317405 : Blo 187803 317405 := bbase (se 3 (by rfl) ⟨59513, by rfl⟩ : syracuseStep 317405 = 119027) (by norm_num)
theorem B284645 : Blo 187803 284645 := bbase (se 4 (by rfl) ⟨26685, by rfl⟩ : syracuseStep 284645 = 53371) (by norm_num)
theorem B481261 : Blo 187803 481261 := bbase (se 3 (by rfl) ⟨90236, by rfl⟩ : syracuseStep 481261 = 180473) (by norm_num)
theorem B284669 : Blo 187803 284669 := bbase (se 3 (by rfl) ⟨53375, by rfl⟩ : syracuseStep 284669 = 106751) (by norm_num)
theorem B284693 : Blo 187803 284693 := bbase (se 6 (by rfl) ⟨6672, by rfl⟩ : syracuseStep 284693 = 13345) (by norm_num)
theorem B284717 : Blo 187803 284717 := bbase (se 3 (by rfl) ⟨53384, by rfl⟩ : syracuseStep 284717 = 106769) (by norm_num)
theorem B284741 : Blo 187803 284741 := bbase (se 4 (by rfl) ⟨26694, by rfl⟩ : syracuseStep 284741 = 53389) (by norm_num)
theorem B317533 : Blo 187803 317533 := bbase (se 3 (by rfl) ⟨59537, by rfl⟩ : syracuseStep 317533 = 119075) (by norm_num)
theorem B284765 : Blo 187803 284765 := bbase (se 3 (by rfl) ⟨53393, by rfl⟩ : syracuseStep 284765 = 106787) (by norm_num)
theorem B481373 : Blo 187803 481373 := bbase (se 3 (by rfl) ⟨90257, by rfl⟩ : syracuseStep 481373 = 180515) (by norm_num)
theorem B284789 : Blo 187803 284789 := bbase (se 5 (by rfl) ⟨13349, by rfl⟩ : syracuseStep 284789 = 26699) (by norm_num)
theorem B284813 : Blo 187803 284813 := bbase (se 3 (by rfl) ⟨53402, by rfl⟩ : syracuseStep 284813 = 106805) (by norm_num)
theorem B284837 : Blo 187803 284837 := bbase (se 4 (by rfl) ⟨26703, by rfl⟩ : syracuseStep 284837 = 53407) (by norm_num)
theorem B317621 : Blo 187803 317621 := bbase (se 5 (by rfl) ⟨14888, by rfl⟩ : syracuseStep 317621 = 29777) (by norm_num)
theorem B284861 : Blo 187803 284861 := bbase (se 3 (by rfl) ⟨53411, by rfl⟩ : syracuseStep 284861 = 106823) (by norm_num)
theorem B284885 : Blo 187803 284885 := bbase (se 7 (by rfl) ⟨3338, by rfl⟩ : syracuseStep 284885 = 6677) (by norm_num)
theorem B284909 : Blo 187803 284909 := bbase (se 3 (by rfl) ⟨53420, by rfl⟩ : syracuseStep 284909 = 106841) (by norm_num)
theorem B284933 : Blo 187803 284933 := bbase (se 4 (by rfl) ⟨26712, by rfl⟩ : syracuseStep 284933 = 53425) (by norm_num)
theorem B284957 : Blo 187803 284957 := bbase (se 3 (by rfl) ⟨53429, by rfl⟩ : syracuseStep 284957 = 106859) (by norm_num)
theorem B481565 : Blo 187803 481565 := bbase (se 3 (by rfl) ⟨90293, by rfl⟩ : syracuseStep 481565 = 180587) (by norm_num)
theorem B317749 : Blo 187803 317749 := bbase (se 5 (by rfl) ⟨14894, by rfl⟩ : syracuseStep 317749 = 29789) (by norm_num)
theorem B284981 : Blo 187803 284981 := bbase (se 5 (by rfl) ⟨13358, by rfl⟩ : syracuseStep 284981 = 26717) (by norm_num)
theorem B285005 : Blo 187803 285005 := bbase (se 3 (by rfl) ⟨53438, by rfl⟩ : syracuseStep 285005 = 106877) (by norm_num)
theorem B645461 : Blo 187803 645461 := bbase (se 10 (by rfl) ⟨945, by rfl⟩ : syracuseStep 645461 = 1891) (by norm_num)
theorem B285029 : Blo 187803 285029 := bbase (se 4 (by rfl) ⟨26721, by rfl⟩ : syracuseStep 285029 = 53443) (by norm_num)
theorem B285053 : Blo 187803 285053 := bbase (se 3 (by rfl) ⟨53447, by rfl⟩ : syracuseStep 285053 = 106895) (by norm_num)
theorem B317837 : Blo 187803 317837 := bbase (se 3 (by rfl) ⟨59594, by rfl⟩ : syracuseStep 317837 = 119189) (by norm_num)
theorem B285077 : Blo 187803 285077 := bbase (se 6 (by rfl) ⟨6681, by rfl⟩ : syracuseStep 285077 = 13363) (by norm_num)
theorem B285101 : Blo 187803 285101 := bbase (se 3 (by rfl) ⟨53456, by rfl⟩ : syracuseStep 285101 = 106913) (by norm_num)
theorem B285125 : Blo 187803 285125 := bbase (se 4 (by rfl) ⟨26730, by rfl⟩ : syracuseStep 285125 = 53461) (by norm_num)
theorem B285149 : Blo 187803 285149 := bbase (se 3 (by rfl) ⟨53465, by rfl⟩ : syracuseStep 285149 = 106931) (by norm_num)
theorem B285173 : Blo 187803 285173 := bbase (se 5 (by rfl) ⟨13367, by rfl⟩ : syracuseStep 285173 = 26735) (by norm_num)
theorem B317965 : Blo 187803 317965 := bbase (se 3 (by rfl) ⟨59618, by rfl⟩ : syracuseStep 317965 = 119237) (by norm_num)
theorem B285197 : Blo 187803 285197 := bbase (se 3 (by rfl) ⟨53474, by rfl⟩ : syracuseStep 285197 = 106949) (by norm_num)
theorem B383525 : Blo 187803 383525 := bbase (se 4 (by rfl) ⟨35955, by rfl⟩ : syracuseStep 383525 = 71911) (by norm_num)
theorem B285221 : Blo 187803 285221 := bbase (se 4 (by rfl) ⟨26739, by rfl⟩ : syracuseStep 285221 = 53479) (by norm_num)
theorem B285245 : Blo 187803 285245 := bbase (se 3 (by rfl) ⟨53483, by rfl⟩ : syracuseStep 285245 = 106967) (by norm_num)
theorem B481877 : Blo 187803 481877 := bbase (se 8 (by rfl) ⟨2823, by rfl⟩ : syracuseStep 481877 = 5647) (by norm_num)
theorem B285269 : Blo 187803 285269 := bbase (se 8 (by rfl) ⟨1671, by rfl⟩ : syracuseStep 285269 = 3343) (by norm_num)
theorem B318053 : Blo 187803 318053 := bbase (se 4 (by rfl) ⟨29817, by rfl⟩ : syracuseStep 318053 = 59635) (by norm_num)
theorem B285293 : Blo 187803 285293 := bbase (se 3 (by rfl) ⟨53492, by rfl⟩ : syracuseStep 285293 = 106985) (by norm_num)
theorem B481909 : Blo 187803 481909 := bbase (se 5 (by rfl) ⟨22589, by rfl⟩ : syracuseStep 481909 = 45179) (by norm_num)
theorem B285317 : Blo 187803 285317 := bbase (se 4 (by rfl) ⟨26748, by rfl⟩ : syracuseStep 285317 = 53497) (by norm_num)
theorem B285341 : Blo 187803 285341 := bbase (se 3 (by rfl) ⟨53501, by rfl⟩ : syracuseStep 285341 = 107003) (by norm_num)
theorem B285365 : Blo 187803 285365 := bbase (se 5 (by rfl) ⟨13376, by rfl⟩ : syracuseStep 285365 = 26753) (by norm_num)
theorem B809669 : Blo 187803 809669 := bbase (se 4 (by rfl) ⟨75906, by rfl⟩ : syracuseStep 809669 = 151813) (by norm_num)
theorem B285389 : Blo 187803 285389 := bbase (se 3 (by rfl) ⟨53510, by rfl⟩ : syracuseStep 285389 = 107021) (by norm_num)
theorem B318181 : Blo 187803 318181 := bbase (se 4 (by rfl) ⟨29829, by rfl⟩ : syracuseStep 318181 = 59659) (by norm_num)
theorem B285413 : Blo 187803 285413 := bbase (se 4 (by rfl) ⟨26757, by rfl⟩ : syracuseStep 285413 = 53515) (by norm_num)
theorem B482021 : Blo 187803 482021 := bbase (se 4 (by rfl) ⟨45189, by rfl⟩ : syracuseStep 482021 = 90379) (by norm_num)
theorem B285437 : Blo 187803 285437 := bbase (se 3 (by rfl) ⟨53519, by rfl⟩ : syracuseStep 285437 = 107039) (by norm_num)
theorem B645893 : Blo 187803 645893 := bbase (se 4 (by rfl) ⟨60552, by rfl⟩ : syracuseStep 645893 = 121105) (by norm_num)
theorem B285461 : Blo 187803 285461 := bbase (se 6 (by rfl) ⟨6690, by rfl⟩ : syracuseStep 285461 = 13381) (by norm_num)
theorem B285485 : Blo 187803 285485 := bbase (se 3 (by rfl) ⟨53528, by rfl⟩ : syracuseStep 285485 = 107057) (by norm_num)
theorem B318269 : Blo 187803 318269 := bbase (se 3 (by rfl) ⟨59675, by rfl⟩ : syracuseStep 318269 = 119351) (by norm_num)
theorem B285509 : Blo 187803 285509 := bbase (se 4 (by rfl) ⟨26766, by rfl⟩ : syracuseStep 285509 = 53533) (by norm_num)
theorem B285533 : Blo 187803 285533 := bbase (se 3 (by rfl) ⟨53537, by rfl⟩ : syracuseStep 285533 = 107075) (by norm_num)
theorem B285557 : Blo 187803 285557 := bbase (se 5 (by rfl) ⟨13385, by rfl⟩ : syracuseStep 285557 = 26771) (by norm_num)
theorem B285581 : Blo 187803 285581 := bbase (se 3 (by rfl) ⟨53546, by rfl⟩ : syracuseStep 285581 = 107093) (by norm_num)
theorem B285605 : Blo 187803 285605 := bbase (se 4 (by rfl) ⟨26775, by rfl⟩ : syracuseStep 285605 = 53551) (by norm_num)
theorem B482213 : Blo 187803 482213 := bbase (se 4 (by rfl) ⟨45207, by rfl⟩ : syracuseStep 482213 = 90415) (by norm_num)
theorem B809909 : Blo 187803 809909 := bbase (se 5 (by rfl) ⟨37964, by rfl⟩ : syracuseStep 809909 = 75929) (by norm_num)
theorem B318397 : Blo 187803 318397 := bbase (se 3 (by rfl) ⟨59699, by rfl⟩ : syracuseStep 318397 = 119399) (by norm_num)
theorem B285629 : Blo 187803 285629 := bbase (se 3 (by rfl) ⟨53555, by rfl⟩ : syracuseStep 285629 = 107111) (by norm_num)
theorem B285653 : Blo 187803 285653 := bbase (se 7 (by rfl) ⟨3347, by rfl⟩ : syracuseStep 285653 = 6695) (by norm_num)
theorem B285677 : Blo 187803 285677 := bbase (se 3 (by rfl) ⟨53564, by rfl⟩ : syracuseStep 285677 = 107129) (by norm_num)
theorem B285701 : Blo 187803 285701 := bbase (se 4 (by rfl) ⟨26784, by rfl⟩ : syracuseStep 285701 = 53569) (by norm_num)
theorem B318485 : Blo 187803 318485 := bbase (se 6 (by rfl) ⟨7464, by rfl⟩ : syracuseStep 318485 = 14929) (by norm_num)
theorem B285725 : Blo 187803 285725 := bbase (se 3 (by rfl) ⟨53573, by rfl⟩ : syracuseStep 285725 = 107147) (by norm_num)
theorem B220205 : Blo 187803 220205 := bbase (se 3 (by rfl) ⟨41288, by rfl⟩ : syracuseStep 220205 = 82577) (by norm_num)
theorem B777269 : Blo 187803 777269 := bbase (se 5 (by rfl) ⟨36434, by rfl⟩ : syracuseStep 777269 = 72869) (by norm_num)
theorem B285749 : Blo 187803 285749 := bbase (se 5 (by rfl) ⟨13394, by rfl⟩ : syracuseStep 285749 = 26789) (by norm_num)
theorem B285773 : Blo 187803 285773 := bbase (se 3 (by rfl) ⟨53582, by rfl⟩ : syracuseStep 285773 = 107165) (by norm_num)
theorem B285797 : Blo 187803 285797 := bbase (se 4 (by rfl) ⟨26793, by rfl⟩ : syracuseStep 285797 = 53587) (by norm_num)
theorem B285821 : Blo 187803 285821 := bbase (se 3 (by rfl) ⟨53591, by rfl⟩ : syracuseStep 285821 = 107183) (by norm_num)
theorem B318613 : Blo 187803 318613 := bbase (se 6 (by rfl) ⟨7467, by rfl⟩ : syracuseStep 318613 = 14935) (by norm_num)
theorem B285845 : Blo 187803 285845 := bbase (se 6 (by rfl) ⟨6699, by rfl⟩ : syracuseStep 285845 = 13399) (by norm_num)
theorem B285869 : Blo 187803 285869 := bbase (se 3 (by rfl) ⟨53600, by rfl⟩ : syracuseStep 285869 = 107201) (by norm_num)
theorem B646325 : Blo 187803 646325 := bbase (se 5 (by rfl) ⟨30296, by rfl⟩ : syracuseStep 646325 = 60593) (by norm_num)
theorem B285893 : Blo 187803 285893 := bbase (se 4 (by rfl) ⟨26802, by rfl⟩ : syracuseStep 285893 = 53605) (by norm_num)
theorem B515285 : Blo 187803 515285 := bbase (se 7 (by rfl) ⟨6038, by rfl⟩ : syracuseStep 515285 = 12077) (by norm_num)
theorem B285917 : Blo 187803 285917 := bbase (se 3 (by rfl) ⟨53609, by rfl⟩ : syracuseStep 285917 = 107219) (by norm_num)
theorem B318701 : Blo 187803 318701 := bbase (se 3 (by rfl) ⟨59756, by rfl⟩ : syracuseStep 318701 = 119513) (by norm_num)
theorem B285941 : Blo 187803 285941 := bbase (se 5 (by rfl) ⟨13403, by rfl⟩ : syracuseStep 285941 = 26807) (by norm_num)
theorem B482557 : Blo 187803 482557 := bbase (se 3 (by rfl) ⟨90479, by rfl⟩ : syracuseStep 482557 = 180959) (by norm_num)
theorem B285965 : Blo 187803 285965 := bbase (se 3 (by rfl) ⟨53618, by rfl⟩ : syracuseStep 285965 = 107237) (by norm_num)
theorem B285989 : Blo 187803 285989 := bbase (se 4 (by rfl) ⟨26811, by rfl⟩ : syracuseStep 285989 = 53623) (by norm_num)
theorem B286013 : Blo 187803 286013 := bbase (se 3 (by rfl) ⟨53627, by rfl⟩ : syracuseStep 286013 = 107255) (by norm_num)
theorem B286037 : Blo 187803 286037 := bbase (se 11 (by rfl) ⟨209, by rfl⟩ : syracuseStep 286037 = 419) (by norm_num)
theorem B318829 : Blo 187803 318829 := bbase (se 3 (by rfl) ⟨59780, by rfl⟩ : syracuseStep 318829 = 119561) (by norm_num)
theorem B482669 : Blo 187803 482669 := bbase (se 3 (by rfl) ⟨90500, by rfl⟩ : syracuseStep 482669 = 181001) (by norm_num)
theorem B286061 : Blo 187803 286061 := bbase (se 3 (by rfl) ⟨53636, by rfl⟩ : syracuseStep 286061 = 107273) (by norm_num)
theorem B1629557 : Blo 187803 1629557 := bbase (se 5 (by rfl) ⟨76385, by rfl⟩ : syracuseStep 1629557 = 152771) (by norm_num)
theorem B286085 : Blo 187803 286085 := bbase (se 4 (by rfl) ⟨26820, by rfl⟩ : syracuseStep 286085 = 53641) (by norm_num)
theorem B286109 : Blo 187803 286109 := bbase (se 3 (by rfl) ⟨53645, by rfl⟩ : syracuseStep 286109 = 107291) (by norm_num)
theorem B286133 : Blo 187803 286133 := bbase (se 5 (by rfl) ⟨13412, by rfl⟩ : syracuseStep 286133 = 26825) (by norm_num)
theorem B613813 : Blo 187803 613813 := bbase (se 5 (by rfl) ⟨28772, by rfl⟩ : syracuseStep 613813 = 57545) (by norm_num)
theorem B318917 : Blo 187803 318917 := bbase (se 4 (by rfl) ⟨29898, by rfl⟩ : syracuseStep 318917 = 59797) (by norm_num)
theorem B286157 : Blo 187803 286157 := bbase (se 3 (by rfl) ⟨53654, by rfl⟩ : syracuseStep 286157 = 107309) (by norm_num)
theorem B482773 : Blo 187803 482773 := bbase (se 7 (by rfl) ⟨5657, by rfl⟩ : syracuseStep 482773 = 11315) (by norm_num)
theorem B286181 : Blo 187803 286181 := bbase (se 4 (by rfl) ⟨26829, by rfl⟩ : syracuseStep 286181 = 53659) (by norm_num)
theorem B286205 : Blo 187803 286205 := bbase (se 3 (by rfl) ⟨53663, by rfl⟩ : syracuseStep 286205 = 107327) (by norm_num)
theorem B286229 : Blo 187803 286229 := bbase (se 6 (by rfl) ⟨6708, by rfl⟩ : syracuseStep 286229 = 13417) (by norm_num)
theorem B482861 : Blo 187803 482861 := bbase (se 3 (by rfl) ⟨90536, by rfl⟩ : syracuseStep 482861 = 181073) (by norm_num)
theorem B286253 : Blo 187803 286253 := bbase (se 3 (by rfl) ⟨53672, by rfl⟩ : syracuseStep 286253 = 107345) (by norm_num)
theorem B319045 : Blo 187803 319045 := bbase (se 4 (by rfl) ⟨29910, by rfl⟩ : syracuseStep 319045 = 59821) (by norm_num)
theorem B286277 : Blo 187803 286277 := bbase (se 4 (by rfl) ⟨26838, by rfl⟩ : syracuseStep 286277 = 53677) (by norm_num)
theorem B286301 : Blo 187803 286301 := bbase (se 3 (by rfl) ⟨53681, by rfl⟩ : syracuseStep 286301 = 107363) (by norm_num)
theorem B646757 : Blo 187803 646757 := bbase (se 4 (by rfl) ⟨60633, by rfl⟩ : syracuseStep 646757 = 121267) (by norm_num)
theorem B286325 : Blo 187803 286325 := bbase (se 5 (by rfl) ⟨13421, by rfl⟩ : syracuseStep 286325 = 26843) (by norm_num)
theorem B286349 : Blo 187803 286349 := bbase (se 3 (by rfl) ⟨53690, by rfl⟩ : syracuseStep 286349 = 107381) (by norm_num)
theorem B319133 : Blo 187803 319133 := bbase (se 3 (by rfl) ⟨59837, by rfl⟩ : syracuseStep 319133 = 119675) (by norm_num)
theorem B286373 : Blo 187803 286373 := bbase (se 4 (by rfl) ⟨26847, by rfl⟩ : syracuseStep 286373 = 53695) (by norm_num)
theorem B614069 : Blo 187803 614069 := bbase (se 5 (by rfl) ⟨28784, by rfl⟩ : syracuseStep 614069 = 57569) (by norm_num)
theorem B286397 : Blo 187803 286397 := bbase (se 3 (by rfl) ⟨53699, by rfl⟩ : syracuseStep 286397 = 107399) (by norm_num)
theorem B286421 : Blo 187803 286421 := bbase (se 7 (by rfl) ⟨3356, by rfl⟩ : syracuseStep 286421 = 6713) (by norm_num)
theorem B286445 : Blo 187803 286445 := bbase (se 3 (by rfl) ⟨53708, by rfl⟩ : syracuseStep 286445 = 107417) (by norm_num)
theorem B286469 : Blo 187803 286469 := bbase (se 4 (by rfl) ⟨26856, by rfl⟩ : syracuseStep 286469 = 53713) (by norm_num)
theorem B581381 : Blo 187803 581381 := bbase (se 4 (by rfl) ⟨54504, by rfl⟩ : syracuseStep 581381 = 109009) (by norm_num)
theorem B319261 : Blo 187803 319261 := bbase (se 3 (by rfl) ⟨59861, by rfl⟩ : syracuseStep 319261 = 119723) (by norm_num)
theorem B286493 : Blo 187803 286493 := bbase (se 3 (by rfl) ⟨53717, by rfl⟩ : syracuseStep 286493 = 107435) (by norm_num)
theorem B286517 : Blo 187803 286517 := bbase (se 5 (by rfl) ⟨13430, by rfl⟩ : syracuseStep 286517 = 26861) (by norm_num)
theorem B286541 : Blo 187803 286541 := bbase (se 3 (by rfl) ⟨53726, by rfl⟩ : syracuseStep 286541 = 107453) (by norm_num)
theorem B286565 : Blo 187803 286565 := bbase (se 4 (by rfl) ⟨26865, by rfl⟩ : syracuseStep 286565 = 53731) (by norm_num)
theorem B319349 : Blo 187803 319349 := bbase (se 5 (by rfl) ⟨14969, by rfl⟩ : syracuseStep 319349 = 29939) (by norm_num)
theorem B286589 : Blo 187803 286589 := bbase (se 3 (by rfl) ⟨53735, by rfl⟩ : syracuseStep 286589 = 107471) (by norm_num)
theorem B483205 : Blo 187803 483205 := bbase (se 4 (by rfl) ⟨45300, by rfl⟩ : syracuseStep 483205 = 90601) (by norm_num)
theorem B286613 : Blo 187803 286613 := bbase (se 6 (by rfl) ⟨6717, by rfl⟩ : syracuseStep 286613 = 13435) (by norm_num)
theorem B581525 : Blo 187803 581525 := bbase (se 6 (by rfl) ⟨13629, by rfl⟩ : syracuseStep 581525 = 27259) (by norm_num)
theorem B286621 : Blo 187803 286621 := bbase (se 3 (by rfl) ⟨53741, by rfl⟩ : syracuseStep 286621 = 107483) (by norm_num)
theorem B286637 : Blo 187803 286637 := bbase (se 3 (by rfl) ⟨53744, by rfl⟩ : syracuseStep 286637 = 107489) (by norm_num)
theorem B286661 : Blo 187803 286661 := bbase (se 4 (by rfl) ⟨26874, by rfl⟩ : syracuseStep 286661 = 53749) (by norm_num)
theorem B286685 : Blo 187803 286685 := bbase (se 3 (by rfl) ⟨53753, by rfl⟩ : syracuseStep 286685 = 107507) (by norm_num)
theorem B319477 : Blo 187803 319477 := bbase (se 5 (by rfl) ⟨14975, by rfl⟩ : syracuseStep 319477 = 29951) (by norm_num)
theorem B483317 : Blo 187803 483317 := bbase (se 5 (by rfl) ⟨22655, by rfl⟩ : syracuseStep 483317 = 45311) (by norm_num)
theorem B286709 : Blo 187803 286709 := bbase (se 5 (by rfl) ⟨13439, by rfl⟩ : syracuseStep 286709 = 26879) (by norm_num)
theorem B286733 : Blo 187803 286733 := bbase (se 3 (by rfl) ⟨53762, by rfl⟩ : syracuseStep 286733 = 107525) (by norm_num)
theorem B647189 : Blo 187803 647189 := bbase (se 6 (by rfl) ⟨15168, by rfl⟩ : syracuseStep 647189 = 30337) (by norm_num)
theorem B286757 : Blo 187803 286757 := bbase (se 4 (by rfl) ⟨26883, by rfl⟩ : syracuseStep 286757 = 53767) (by norm_num)
theorem B286781 : Blo 187803 286781 := bbase (se 3 (by rfl) ⟨53771, by rfl⟩ : syracuseStep 286781 = 107543) (by norm_num)
theorem B319565 : Blo 187803 319565 := bbase (se 3 (by rfl) ⟨59918, by rfl⟩ : syracuseStep 319565 = 119837) (by norm_num)
theorem B286805 : Blo 187803 286805 := bbase (se 8 (by rfl) ⟨1680, by rfl⟩ : syracuseStep 286805 = 3361) (by norm_num)
theorem B286829 : Blo 187803 286829 := bbase (se 3 (by rfl) ⟨53780, by rfl⟩ : syracuseStep 286829 = 107561) (by norm_num)
theorem B286853 : Blo 187803 286853 := bbase (se 4 (by rfl) ⟨26892, by rfl⟩ : syracuseStep 286853 = 53785) (by norm_num)
theorem B286877 : Blo 187803 286877 := bbase (se 3 (by rfl) ⟨53789, by rfl⟩ : syracuseStep 286877 = 107579) (by norm_num)
theorem B483509 : Blo 187803 483509 := bbase (se 5 (by rfl) ⟨22664, by rfl⟩ : syracuseStep 483509 = 45329) (by norm_num)
theorem B286901 : Blo 187803 286901 := bbase (se 5 (by rfl) ⟨13448, by rfl⟩ : syracuseStep 286901 = 26897) (by norm_num)
theorem B319693 : Blo 187803 319693 := bbase (se 3 (by rfl) ⟨59942, by rfl⟩ : syracuseStep 319693 = 119885) (by norm_num)
theorem B286925 : Blo 187803 286925 := bbase (se 3 (by rfl) ⟨53798, by rfl⟩ : syracuseStep 286925 = 107597) (by norm_num)
theorem B286949 : Blo 187803 286949 := bbase (se 4 (by rfl) ⟨26901, by rfl⟩ : syracuseStep 286949 = 53803) (by norm_num)
theorem B286973 : Blo 187803 286973 := bbase (se 3 (by rfl) ⟨53807, by rfl⟩ : syracuseStep 286973 = 107615) (by norm_num)
theorem B286997 : Blo 187803 286997 := bbase (se 6 (by rfl) ⟨6726, by rfl⟩ : syracuseStep 286997 = 13453) (by norm_num)
theorem B319781 : Blo 187803 319781 := bbase (se 4 (by rfl) ⟨29979, by rfl⟩ : syracuseStep 319781 = 59959) (by norm_num)
theorem B287021 : Blo 187803 287021 := bbase (se 3 (by rfl) ⟨53816, by rfl⟩ : syracuseStep 287021 = 107633) (by norm_num)
theorem B287045 : Blo 187803 287045 := bbase (se 4 (by rfl) ⟨26910, by rfl⟩ : syracuseStep 287045 = 53821) (by norm_num)
theorem B287069 : Blo 187803 287069 := bbase (se 3 (by rfl) ⟨53825, by rfl⟩ : syracuseStep 287069 = 107651) (by norm_num)
theorem B516469 : Blo 187803 516469 := bbase (se 5 (by rfl) ⟨24209, by rfl⟩ : syracuseStep 516469 = 48419) (by norm_num)
theorem B287093 : Blo 187803 287093 := bbase (se 5 (by rfl) ⟨13457, by rfl⟩ : syracuseStep 287093 = 26915) (by norm_num)
theorem B483725 : Blo 187803 483725 := bbase (se 3 (by rfl) ⟨90698, by rfl⟩ : syracuseStep 483725 = 181397) (by norm_num)
theorem B287117 : Blo 187803 287117 := bbase (se 3 (by rfl) ⟨53834, by rfl⟩ : syracuseStep 287117 = 107669) (by norm_num)
theorem B319909 : Blo 187803 319909 := bbase (se 4 (by rfl) ⟨29991, by rfl⟩ : syracuseStep 319909 = 59983) (by norm_num)
theorem B287141 : Blo 187803 287141 := bbase (se 4 (by rfl) ⟨26919, by rfl⟩ : syracuseStep 287141 = 53839) (by norm_num)
theorem B287165 : Blo 187803 287165 := bbase (se 3 (by rfl) ⟨53843, by rfl⟩ : syracuseStep 287165 = 107687) (by norm_num)
theorem B287189 : Blo 187803 287189 := bbase (se 7 (by rfl) ⟨3365, by rfl⟩ : syracuseStep 287189 = 6731) (by norm_num)
theorem B1106389 : Blo 187803 1106389 := bbase (se 7 (by rfl) ⟨12965, by rfl⟩ : syracuseStep 1106389 = 25931) (by norm_num)
theorem B287213 : Blo 187803 287213 := bbase (se 3 (by rfl) ⟨53852, by rfl⟩ : syracuseStep 287213 = 107705) (by norm_num)
theorem B319997 : Blo 187803 319997 := bbase (se 3 (by rfl) ⟨59999, by rfl⟩ : syracuseStep 319997 = 119999) (by norm_num)
theorem B287237 : Blo 187803 287237 := bbase (se 4 (by rfl) ⟨26928, by rfl⟩ : syracuseStep 287237 = 53857) (by norm_num)
theorem B483853 : Blo 187803 483853 := bbase (se 3 (by rfl) ⟨90722, by rfl⟩ : syracuseStep 483853 = 181445) (by norm_num)
theorem B287261 : Blo 187803 287261 := bbase (se 3 (by rfl) ⟨53861, by rfl⟩ : syracuseStep 287261 = 107723) (by norm_num)
theorem B287285 : Blo 187803 287285 := bbase (se 5 (by rfl) ⟨13466, by rfl⟩ : syracuseStep 287285 = 26933) (by norm_num)
theorem B287309 : Blo 187803 287309 := bbase (se 3 (by rfl) ⟨53870, by rfl⟩ : syracuseStep 287309 = 107741) (by norm_num)
theorem B516709 : Blo 187803 516709 := bbase (se 4 (by rfl) ⟨48441, by rfl⟩ : syracuseStep 516709 = 96883) (by norm_num)
theorem B287333 : Blo 187803 287333 := bbase (se 4 (by rfl) ⟨26937, by rfl⟩ : syracuseStep 287333 = 53875) (by norm_num)
theorem B320125 : Blo 187803 320125 := bbase (se 3 (by rfl) ⟨60023, by rfl⟩ : syracuseStep 320125 = 120047) (by norm_num)
theorem B483965 : Blo 187803 483965 := bbase (se 3 (by rfl) ⟨90743, by rfl⟩ : syracuseStep 483965 = 181487) (by norm_num)
theorem B287357 : Blo 187803 287357 := bbase (se 3 (by rfl) ⟨53879, by rfl⟩ : syracuseStep 287357 = 107759) (by norm_num)
theorem B287381 : Blo 187803 287381 := bbase (se 6 (by rfl) ⟨6735, by rfl⟩ : syracuseStep 287381 = 13471) (by norm_num)
theorem B287405 : Blo 187803 287405 := bbase (se 3 (by rfl) ⟨53888, by rfl⟩ : syracuseStep 287405 = 107777) (by norm_num)
theorem B287429 : Blo 187803 287429 := bbase (se 4 (by rfl) ⟨26946, by rfl⟩ : syracuseStep 287429 = 53893) (by norm_num)
theorem B320213 : Blo 187803 320213 := bbase (se 7 (by rfl) ⟨3752, by rfl⟩ : syracuseStep 320213 = 7505) (by norm_num)
theorem B287453 : Blo 187803 287453 := bbase (se 3 (by rfl) ⟨53897, by rfl⟩ : syracuseStep 287453 = 107795) (by norm_num)
theorem B287477 : Blo 187803 287477 := bbase (se 5 (by rfl) ⟨13475, by rfl⟩ : syracuseStep 287477 = 26951) (by norm_num)
theorem B287501 : Blo 187803 287501 := bbase (se 3 (by rfl) ⟨53906, by rfl⟩ : syracuseStep 287501 = 107813) (by norm_num)
theorem B287525 : Blo 187803 287525 := bbase (se 4 (by rfl) ⟨26955, by rfl⟩ : syracuseStep 287525 = 53911) (by norm_num)
theorem B484157 : Blo 187803 484157 := bbase (se 3 (by rfl) ⟨90779, by rfl⟩ : syracuseStep 484157 = 181559) (by norm_num)
theorem B287549 : Blo 187803 287549 := bbase (se 3 (by rfl) ⟨53915, by rfl⟩ : syracuseStep 287549 = 107831) (by norm_num)
theorem B320341 : Blo 187803 320341 := bbase (se 9 (by rfl) ⟨938, by rfl⟩ : syracuseStep 320341 = 1877) (by norm_num)
theorem B287573 : Blo 187803 287573 := bbase (se 9 (by rfl) ⟨842, by rfl⟩ : syracuseStep 287573 = 1685) (by norm_num)
theorem B615269 : Blo 187803 615269 := bbase (se 4 (by rfl) ⟨57681, by rfl⟩ : syracuseStep 615269 = 115363) (by norm_num)
theorem B287597 : Blo 187803 287597 := bbase (se 3 (by rfl) ⟨53924, by rfl⟩ : syracuseStep 287597 = 107849) (by norm_num)
theorem B287621 : Blo 187803 287621 := bbase (se 4 (by rfl) ⟨26964, by rfl⟩ : syracuseStep 287621 = 53929) (by norm_num)
theorem B3072917 : Blo 187803 3072917 := bbase (se 6 (by rfl) ⟨72021, by rfl⟩ : syracuseStep 3072917 = 144043) (by norm_num)
theorem B287645 : Blo 187803 287645 := bbase (se 3 (by rfl) ⟨53933, by rfl⟩ : syracuseStep 287645 = 107867) (by norm_num)
theorem B320429 : Blo 187803 320429 := bbase (se 3 (by rfl) ⟨60080, by rfl⟩ : syracuseStep 320429 = 120161) (by norm_num)
theorem B287669 : Blo 187803 287669 := bbase (se 5 (by rfl) ⟨13484, by rfl⟩ : syracuseStep 287669 = 26969) (by norm_num)
theorem B287693 : Blo 187803 287693 := bbase (se 3 (by rfl) ⟨53942, by rfl⟩ : syracuseStep 287693 = 107885) (by norm_num)
theorem B320557 : Blo 187803 320557 := bbase (se 3 (by rfl) ⟨60104, by rfl⟩ : syracuseStep 320557 = 120209) (by norm_num)
theorem B320645 : Blo 187803 320645 := bbase (se 4 (by rfl) ⟨30060, by rfl⟩ : syracuseStep 320645 = 60121) (by norm_num)
theorem B484501 : Blo 187803 484501 := bbase (se 6 (by rfl) ⟨11355, by rfl⟩ : syracuseStep 484501 = 22711) (by norm_num)
theorem B812197 : Blo 187803 812197 := bbase (se 4 (by rfl) ⟨76143, by rfl⟩ : syracuseStep 812197 = 152287) (by norm_num)
theorem B320773 : Blo 187803 320773 := bbase (se 4 (by rfl) ⟨30072, by rfl⟩ : syracuseStep 320773 = 60145) (by norm_num)
theorem B484613 : Blo 187803 484613 := bbase (se 4 (by rfl) ⟨45432, by rfl⟩ : syracuseStep 484613 = 90865) (by norm_num)
theorem B517429 : Blo 187803 517429 := bbase (se 5 (by rfl) ⟨24254, by rfl⟩ : syracuseStep 517429 = 48509) (by norm_num)
theorem B3106133 : Blo 187803 3106133 := bbase (se 12 (by rfl) ⟨1137, by rfl⟩ : syracuseStep 3106133 = 2275) (by norm_num)
theorem B320861 : Blo 187803 320861 := bbase (se 3 (by rfl) ⟨60161, by rfl⟩ : syracuseStep 320861 = 120323) (by norm_num)
theorem B484805 : Blo 187803 484805 := bbase (se 4 (by rfl) ⟨45450, by rfl⟩ : syracuseStep 484805 = 90901) (by norm_num)
theorem B320989 : Blo 187803 320989 := bbase (se 3 (by rfl) ⟨60185, by rfl⟩ : syracuseStep 320989 = 120371) (by norm_num)
theorem B386549 : Blo 187803 386549 := bbase (se 5 (by rfl) ⟨18119, by rfl⟩ : syracuseStep 386549 = 36239) (by norm_num)
theorem B1435157 : Blo 187803 1435157 := bbase (se 6 (by rfl) ⟨33636, by rfl⟩ : syracuseStep 1435157 = 67273) (by norm_num)
theorem B321077 : Blo 187803 321077 := bbase (se 5 (by rfl) ⟨15050, by rfl⟩ : syracuseStep 321077 = 30101) (by norm_num)
theorem B321205 : Blo 187803 321205 := bbase (se 5 (by rfl) ⟨15056, by rfl⟩ : syracuseStep 321205 = 30113) (by norm_num)
theorem B452317 : Blo 187803 452317 := bbase (se 3 (by rfl) ⟨84809, by rfl⟩ : syracuseStep 452317 = 169619) (by norm_num)
theorem B321293 : Blo 187803 321293 := bbase (se 3 (by rfl) ⟨60242, by rfl⟩ : syracuseStep 321293 = 120485) (by norm_num)
theorem B485149 : Blo 187803 485149 := bbase (se 3 (by rfl) ⟨90965, by rfl⟩ : syracuseStep 485149 = 181931) (by norm_num)
theorem B321421 : Blo 187803 321421 := bbase (se 3 (by rfl) ⟨60266, by rfl⟩ : syracuseStep 321421 = 120533) (by norm_num)
theorem B485261 : Blo 187803 485261 := bbase (se 3 (by rfl) ⟨90986, by rfl⟩ : syracuseStep 485261 = 181973) (by norm_num)
theorem B321509 : Blo 187803 321509 := bbase (se 4 (by rfl) ⟨30141, by rfl⟩ : syracuseStep 321509 = 60283) (by norm_num)
theorem B780293 : Blo 187803 780293 := bbase (se 4 (by rfl) ⟨73152, by rfl⟩ : syracuseStep 780293 = 146305) (by norm_num)
theorem B190517 : Blo 187803 190517 := bbase (se 5 (by rfl) ⟨8930, by rfl⟩ : syracuseStep 190517 = 17861) (by norm_num)
theorem B485453 : Blo 187803 485453 := bbase (se 3 (by rfl) ⟨91022, by rfl⟩ : syracuseStep 485453 = 182045) (by norm_num)
theorem B321637 : Blo 187803 321637 := bbase (se 4 (by rfl) ⟨30153, by rfl⟩ : syracuseStep 321637 = 60307) (by norm_num)
theorem B321725 : Blo 187803 321725 := bbase (se 3 (by rfl) ⟨60323, by rfl⟩ : syracuseStep 321725 = 120647) (by norm_num)
theorem B715013 : Blo 187803 715013 := bbase (se 4 (by rfl) ⟨67032, by rfl⟩ : syracuseStep 715013 = 134065) (by norm_num)
theorem B321853 : Blo 187803 321853 := bbase (se 3 (by rfl) ⟨60347, by rfl⟩ : syracuseStep 321853 = 120695) (by norm_num)
theorem B190793 : Blo 187803 190793 := bbase (se 2 (by rfl) ⟨71547, by rfl⟩ : syracuseStep 190793 = 143095) (by norm_num)
theorem B223585 : Blo 187803 223585 := bbase (se 2 (by rfl) ⟨83844, by rfl⟩ : syracuseStep 223585 = 167689) (by norm_num)
theorem B321941 : Blo 187803 321941 := bbase (se 6 (by rfl) ⟨7545, by rfl⟩ : syracuseStep 321941 = 15091) (by norm_num)
theorem B322069 : Blo 187803 322069 := bbase (se 6 (by rfl) ⟨7548, by rfl⟩ : syracuseStep 322069 = 15097) (by norm_num)
theorem B715301 : Blo 187803 715301 := bbase (se 4 (by rfl) ⟨67059, by rfl⟩ : syracuseStep 715301 = 134119) (by norm_num)
theorem B616997 : Blo 187803 616997 := bbase (se 4 (by rfl) ⟨57843, by rfl⟩ : syracuseStep 616997 = 115687) (by norm_num)
theorem B322157 : Blo 187803 322157 := bbase (se 3 (by rfl) ⟨60404, by rfl⟩ : syracuseStep 322157 = 120809) (by norm_num)
theorem B813685 : Blo 187803 813685 := bbase (se 5 (by rfl) ⟨38141, by rfl⟩ : syracuseStep 813685 = 76283) (by norm_num)
theorem B813701 : Blo 187803 813701 := bbase (se 4 (by rfl) ⟨76284, by rfl⟩ : syracuseStep 813701 = 152569) (by norm_num)
theorem B191117 : Blo 187803 191117 := bbase (se 3 (by rfl) ⟨35834, by rfl⟩ : syracuseStep 191117 = 71669) (by norm_num)
theorem B387749 : Blo 187803 387749 := bbase (se 4 (by rfl) ⟨36351, by rfl⟩ : syracuseStep 387749 = 72703) (by norm_num)
theorem B191149 : Blo 187803 191149 := bbase (se 3 (by rfl) ⟨35840, by rfl⟩ : syracuseStep 191149 = 71681) (by norm_num)
theorem B322285 : Blo 187803 322285 := bbase (se 3 (by rfl) ⟨60428, by rfl⟩ : syracuseStep 322285 = 120857) (by norm_num)
theorem B879349 : Blo 187803 879349 := bbase (se 5 (by rfl) ⟨41219, by rfl⟩ : syracuseStep 879349 = 82439) (by norm_num)
theorem B322373 : Blo 187803 322373 := bbase (se 4 (by rfl) ⟨30222, by rfl⟩ : syracuseStep 322373 = 60445) (by norm_num)
theorem B322501 : Blo 187803 322501 := bbase (se 4 (by rfl) ⟨30234, by rfl⟩ : syracuseStep 322501 = 60469) (by norm_num)
theorem B191441 : Blo 187803 191441 := bbase (se 2 (by rfl) ⟨71790, by rfl⟩ : syracuseStep 191441 = 143581) (by norm_num)
theorem B289765 : Blo 187803 289765 := bbase (se 4 (by rfl) ⟨27165, by rfl⟩ : syracuseStep 289765 = 54331) (by norm_num)
theorem B322589 : Blo 187803 322589 := bbase (se 3 (by rfl) ⟨60485, by rfl⟩ : syracuseStep 322589 = 120971) (by norm_num)
theorem B453701 : Blo 187803 453701 := bbase (se 4 (by rfl) ⟨42534, by rfl⟩ : syracuseStep 453701 = 85069) (by norm_num)
theorem B453709 : Blo 187803 453709 := bbase (se 3 (by rfl) ⟨85070, by rfl⟩ : syracuseStep 453709 = 170141) (by norm_num)
theorem B322717 : Blo 187803 322717 := bbase (se 3 (by rfl) ⟨60509, by rfl⟩ : syracuseStep 322717 = 121019) (by norm_num)
theorem B257197 : Blo 187803 257197 := bbase (se 3 (by rfl) ⟨48224, by rfl⟩ : syracuseStep 257197 = 96449) (by norm_num)
theorem B2616533 : Blo 187803 2616533 := bbase (se 7 (by rfl) ⟨30662, by rfl⟩ : syracuseStep 2616533 = 61325) (by norm_num)
theorem B322805 : Blo 187803 322805 := bbase (se 5 (by rfl) ⟨15131, by rfl⟩ : syracuseStep 322805 = 30263) (by norm_num)
theorem B3665173 : Blo 187803 3665173 := bbase (se 6 (by rfl) ⟨85902, by rfl⟩ : syracuseStep 3665173 = 171805) (by norm_num)
theorem B650549 : Blo 187803 650549 := bbase (se 5 (by rfl) ⟨30494, by rfl⟩ : syracuseStep 650549 = 60989) (by norm_num)
theorem B1076597 : Blo 187803 1076597 := bbase (se 5 (by rfl) ⟨50465, by rfl⟩ : syracuseStep 1076597 = 100931) (by norm_num)
theorem B322933 : Blo 187803 322933 := bbase (se 5 (by rfl) ⟨15137, by rfl⟩ : syracuseStep 322933 = 30275) (by norm_num)
theorem B257413 : Blo 187803 257413 := bbase (se 4 (by rfl) ⟨24132, by rfl⟩ : syracuseStep 257413 = 48265) (by norm_num)
theorem B224689 : Blo 187803 224689 := bbase (se 2 (by rfl) ⟨84258, by rfl⟩ : syracuseStep 224689 = 168517) (by norm_num)
theorem B945605 : Blo 187803 945605 := bbase (se 4 (by rfl) ⟨88650, by rfl⟩ : syracuseStep 945605 = 177301) (by norm_num)
theorem B323021 : Blo 187803 323021 := bbase (se 3 (by rfl) ⟨60566, by rfl⟩ : syracuseStep 323021 = 121133) (by norm_num)
theorem B192025 : Blo 187803 192025 := bbase (se 2 (by rfl) ⟨72009, by rfl⟩ : syracuseStep 192025 = 144019) (by norm_num)
theorem B323149 : Blo 187803 323149 := bbase (se 3 (by rfl) ⟨60590, by rfl⟩ : syracuseStep 323149 = 121181) (by norm_num)
theorem B323237 : Blo 187803 323237 := bbase (se 4 (by rfl) ⟨30303, by rfl⟩ : syracuseStep 323237 = 60607) (by norm_num)
theorem B716485 : Blo 187803 716485 := bbase (se 4 (by rfl) ⟨67170, by rfl⟩ : syracuseStep 716485 = 134341) (by norm_num)
theorem B1732309 : Blo 187803 1732309 := bbase (se 7 (by rfl) ⟨20300, by rfl⟩ : syracuseStep 1732309 = 40601) (by norm_num)
theorem B257773 : Blo 187803 257773 := bbase (se 3 (by rfl) ⟨48332, by rfl⟩ : syracuseStep 257773 = 96665) (by norm_num)
theorem B323365 : Blo 187803 323365 := bbase (se 4 (by rfl) ⟨30315, by rfl⟩ : syracuseStep 323365 = 60631) (by norm_num)
theorem B192313 : Blo 187803 192313 := bbase (se 2 (by rfl) ⟨72117, by rfl⟩ : syracuseStep 192313 = 144235) (by norm_num)
theorem B257861 : Blo 187803 257861 := bbase (se 4 (by rfl) ⟨24174, by rfl⟩ : syracuseStep 257861 = 48349) (by norm_num)
theorem B323453 : Blo 187803 323453 := bbase (se 3 (by rfl) ⟨60647, by rfl⟩ : syracuseStep 323453 = 121295) (by norm_num)
theorem B683909 : Blo 187803 683909 := bbase (se 4 (by rfl) ⟨64116, by rfl⟩ : syracuseStep 683909 = 128233) (by norm_num)
theorem B913301 : Blo 187803 913301 := bbase (se 6 (by rfl) ⟨21405, by rfl⟩ : syracuseStep 913301 = 42811) (by norm_num)
theorem B716789 : Blo 187803 716789 := bbase (se 5 (by rfl) ⟨33599, by rfl⟩ : syracuseStep 716789 = 67199) (by norm_num)
theorem B323581 : Blo 187803 323581 := bbase (se 3 (by rfl) ⟨60671, by rfl⟩ : syracuseStep 323581 = 121343) (by norm_num)
theorem B684053 : Blo 187803 684053 := bbase (se 6 (by rfl) ⟨16032, by rfl⟩ : syracuseStep 684053 = 32065) (by norm_num)
theorem B454709 : Blo 187803 454709 := bbase (se 5 (by rfl) ⟨21314, by rfl⟩ : syracuseStep 454709 = 42629) (by norm_num)
theorem B323669 : Blo 187803 323669 := bbase (se 8 (by rfl) ⟨1896, by rfl⟩ : syracuseStep 323669 = 3793) (by norm_num)
theorem B356557 : Blo 187803 356557 := bbase (se 3 (by rfl) ⟨66854, by rfl⟩ : syracuseStep 356557 = 133709) (by norm_num)
theorem B356717 : Blo 187803 356717 := bbase (se 3 (by rfl) ⟨66884, by rfl⟩ : syracuseStep 356717 = 133769) (by norm_num)
theorem B291293 : Blo 187803 291293 := bbase (se 3 (by rfl) ⟨54617, by rfl⟩ : syracuseStep 291293 = 109235) (by norm_num)
theorem B356861 : Blo 187803 356861 := bbase (se 3 (by rfl) ⟨66911, by rfl⟩ : syracuseStep 356861 = 133823) (by norm_num)
theorem B1470997 : Blo 187803 1470997 := bbase (se 6 (by rfl) ⟨34476, by rfl⟩ : syracuseStep 1470997 = 68953) (by norm_num)
theorem B225865 : Blo 187803 225865 := bbase (se 2 (by rfl) ⟨84699, by rfl⟩ : syracuseStep 225865 = 169399) (by norm_num)
theorem B291541 : Blo 187803 291541 := bbase (se 7 (by rfl) ⟨3416, by rfl⟩ : syracuseStep 291541 = 6833) (by norm_num)
theorem B422621 : Blo 187803 422621 := bbase (se 3 (by rfl) ⟨79241, by rfl⟩ : syracuseStep 422621 = 158483) (by norm_num)
theorem B357149 : Blo 187803 357149 := bbase (se 3 (by rfl) ⟨66965, by rfl⟩ : syracuseStep 357149 = 133931) (by norm_num)
theorem B422693 : Blo 187803 422693 := bbase (se 4 (by rfl) ⟨39627, by rfl⟩ : syracuseStep 422693 = 79255) (by norm_num)
theorem B455477 : Blo 187803 455477 := bbase (se 5 (by rfl) ⟨21350, by rfl⟩ : syracuseStep 455477 = 42701) (by norm_num)
theorem B815957 : Blo 187803 815957 := bbase (se 9 (by rfl) ⟨2390, by rfl⟩ : syracuseStep 815957 = 4781) (by norm_num)
theorem B422765 : Blo 187803 422765 := bbase (se 3 (by rfl) ⟨79268, by rfl⟩ : syracuseStep 422765 = 158537) (by norm_num)
theorem B226201 : Blo 187803 226201 := bbase (se 2 (by rfl) ⟨84825, by rfl⟩ : syracuseStep 226201 = 169651) (by norm_num)
theorem B422837 : Blo 187803 422837 := bbase (se 5 (by rfl) ⟨19820, by rfl⟩ : syracuseStep 422837 = 39641) (by norm_num)
theorem B357301 : Blo 187803 357301 := bbase (se 5 (by rfl) ⟨16748, by rfl⟩ : syracuseStep 357301 = 33497) (by norm_num)
theorem B422909 : Blo 187803 422909 := bbase (se 3 (by rfl) ⟨79295, by rfl⟩ : syracuseStep 422909 = 158591) (by norm_num)
theorem B422981 : Blo 187803 422981 := bbase (se 4 (by rfl) ⟨39654, by rfl⟩ : syracuseStep 422981 = 79309) (by norm_num)
theorem B423053 : Blo 187803 423053 := bbase (se 3 (by rfl) ⟨79322, by rfl⟩ : syracuseStep 423053 = 158645) (by norm_num)
theorem B259213 : Blo 187803 259213 := bbase (se 3 (by rfl) ⟨48602, by rfl⟩ : syracuseStep 259213 = 97205) (by norm_num)
theorem B423125 : Blo 187803 423125 := bbase (se 7 (by rfl) ⟨4958, by rfl⟩ : syracuseStep 423125 = 9917) (by norm_num)
theorem B914645 : Blo 187803 914645 := bbase (se 7 (by rfl) ⟨10718, by rfl⟩ : syracuseStep 914645 = 21437) (by norm_num)
theorem B193753 : Blo 187803 193753 := bbase (se 2 (by rfl) ⟨72657, by rfl⟩ : syracuseStep 193753 = 145315) (by norm_num)
theorem B357605 : Blo 187803 357605 := bbase (se 4 (by rfl) ⟨33525, by rfl⟩ : syracuseStep 357605 = 67051) (by norm_num)
theorem B423197 : Blo 187803 423197 := bbase (se 3 (by rfl) ⟨79349, by rfl⟩ : syracuseStep 423197 = 158699) (by norm_num)
theorem B423269 : Blo 187803 423269 := bbase (se 4 (by rfl) ⟨39681, by rfl⟩ : syracuseStep 423269 = 79363) (by norm_num)
theorem B1373557 : Blo 187803 1373557 := bbase (se 5 (by rfl) ⟨64385, by rfl⟩ : syracuseStep 1373557 = 128771) (by norm_num)
theorem B423341 : Blo 187803 423341 := bbase (se 3 (by rfl) ⟨79376, by rfl⟩ : syracuseStep 423341 = 158753) (by norm_num)
theorem B423413 : Blo 187803 423413 := bbase (se 5 (by rfl) ⟨19847, by rfl⟩ : syracuseStep 423413 = 39695) (by norm_num)
theorem B423485 : Blo 187803 423485 := bbase (se 3 (by rfl) ⟨79403, by rfl⟩ : syracuseStep 423485 = 158807) (by norm_num)
theorem B1373813 : Blo 187803 1373813 := bbase (se 5 (by rfl) ⟨64397, by rfl⟩ : syracuseStep 1373813 = 128795) (by norm_num)
theorem B423557 : Blo 187803 423557 := bbase (se 4 (by rfl) ⟨39708, by rfl⟩ : syracuseStep 423557 = 79417) (by norm_num)
theorem B423629 : Blo 187803 423629 := bbase (se 3 (by rfl) ⟨79430, by rfl⟩ : syracuseStep 423629 = 158861) (by norm_num)
theorem B227081 : Blo 187803 227081 := bbase (se 2 (by rfl) ⟨85155, by rfl⟩ : syracuseStep 227081 = 170311) (by norm_num)
theorem B423701 : Blo 187803 423701 := bbase (se 6 (by rfl) ⟨9930, by rfl⟩ : syracuseStep 423701 = 19861) (by norm_num)
theorem B194357 : Blo 187803 194357 := bbase (se 5 (by rfl) ⟨9110, by rfl⟩ : syracuseStep 194357 = 18221) (by norm_num)
theorem B194389 : Blo 187803 194389 := bbase (se 9 (by rfl) ⟨569, by rfl⟩ : syracuseStep 194389 = 1139) (by norm_num)
theorem B423773 : Blo 187803 423773 := bbase (se 3 (by rfl) ⟨79457, by rfl⟩ : syracuseStep 423773 = 158915) (by norm_num)
theorem B423845 : Blo 187803 423845 := bbase (se 4 (by rfl) ⟨39735, by rfl⟩ : syracuseStep 423845 = 79471) (by norm_num)
theorem B358357 : Blo 187803 358357 := bbase (se 7 (by rfl) ⟨4199, by rfl⟩ : syracuseStep 358357 = 8399) (by norm_num)
theorem B423917 : Blo 187803 423917 := bbase (se 3 (by rfl) ⟨79484, by rfl⟩ : syracuseStep 423917 = 158969) (by norm_num)
theorem B423989 : Blo 187803 423989 := bbase (se 5 (by rfl) ⟨19874, by rfl⟩ : syracuseStep 423989 = 39749) (by norm_num)
theorem B718901 : Blo 187803 718901 := bbase (se 5 (by rfl) ⟨33698, by rfl⟩ : syracuseStep 718901 = 67397) (by norm_num)
theorem B227389 : Blo 187803 227389 := bbase (se 3 (by rfl) ⟨42635, by rfl⟩ : syracuseStep 227389 = 85271) (by norm_num)
theorem B358501 : Blo 187803 358501 := bbase (se 4 (by rfl) ⟨33609, by rfl⟩ : syracuseStep 358501 = 67219) (by norm_num)
theorem B424061 : Blo 187803 424061 := bbase (se 3 (by rfl) ⟨79511, by rfl⟩ : syracuseStep 424061 = 159023) (by norm_num)
theorem B424133 : Blo 187803 424133 := bbase (se 4 (by rfl) ⟨39762, by rfl⟩ : syracuseStep 424133 = 79525) (by norm_num)
theorem B358661 : Blo 187803 358661 := bbase (se 4 (by rfl) ⟨33624, by rfl⟩ : syracuseStep 358661 = 67249) (by norm_num)
theorem B424205 : Blo 187803 424205 := bbase (se 3 (by rfl) ⟨79538, by rfl⟩ : syracuseStep 424205 = 159077) (by norm_num)
theorem B522517 : Blo 187803 522517 := bbase (se 6 (by rfl) ⟨12246, by rfl⟩ : syracuseStep 522517 = 24493) (by norm_num)
theorem B424277 : Blo 187803 424277 := bbase (se 10 (by rfl) ⟨621, by rfl⟩ : syracuseStep 424277 = 1243) (by norm_num)
theorem B719189 : Blo 187803 719189 := bbase (se 10 (by rfl) ⟨1053, by rfl⟩ : syracuseStep 719189 = 2107) (by norm_num)
theorem B358805 : Blo 187803 358805 := bbase (se 6 (by rfl) ⟨8409, by rfl⟩ : syracuseStep 358805 = 16819) (by norm_num)
theorem B424349 : Blo 187803 424349 := bbase (se 3 (by rfl) ⟨79565, by rfl⟩ : syracuseStep 424349 = 159131) (by norm_num)
theorem B227773 : Blo 187803 227773 := bbase (se 3 (by rfl) ⟨42707, by rfl⟩ : syracuseStep 227773 = 85415) (by norm_num)
theorem B227777 : Blo 187803 227777 := bbase (se 2 (by rfl) ⟨85416, by rfl⟩ : syracuseStep 227777 = 170833) (by norm_num)
theorem B424421 : Blo 187803 424421 := bbase (se 4 (by rfl) ⟨39789, by rfl⟩ : syracuseStep 424421 = 79579) (by norm_num)
theorem B424493 : Blo 187803 424493 := bbase (se 3 (by rfl) ⟨79592, by rfl⟩ : syracuseStep 424493 = 159185) (by norm_num)
theorem B457285 : Blo 187803 457285 := bbase (se 4 (by rfl) ⟨42870, by rfl⟩ : syracuseStep 457285 = 85741) (by norm_num)
theorem B686677 : Blo 187803 686677 := bbase (se 8 (by rfl) ⟨4023, by rfl⟩ : syracuseStep 686677 = 8047) (by norm_num)
theorem B916069 : Blo 187803 916069 := bbase (se 4 (by rfl) ⟨85881, by rfl⟩ : syracuseStep 916069 = 171763) (by norm_num)
theorem B424565 : Blo 187803 424565 := bbase (se 5 (by rfl) ⟨19901, by rfl⟩ : syracuseStep 424565 = 39803) (by norm_num)
theorem B359093 : Blo 187803 359093 := bbase (se 5 (by rfl) ⟨16832, by rfl⟩ : syracuseStep 359093 = 33665) (by norm_num)
theorem B424637 : Blo 187803 424637 := bbase (se 3 (by rfl) ⟨79619, by rfl⟩ : syracuseStep 424637 = 159239) (by norm_num)
theorem B686821 : Blo 187803 686821 := bbase (se 4 (by rfl) ⟨64389, by rfl⟩ : syracuseStep 686821 = 128779) (by norm_num)
theorem B424709 : Blo 187803 424709 := bbase (se 4 (by rfl) ⟨39816, by rfl⟩ : syracuseStep 424709 = 79633) (by norm_num)
theorem B1178389 : Blo 187803 1178389 := bbase (se 6 (by rfl) ⟨27618, by rfl⟩ : syracuseStep 1178389 = 55237) (by norm_num)
theorem B424781 : Blo 187803 424781 := bbase (se 3 (by rfl) ⟨79646, by rfl⟩ : syracuseStep 424781 = 159293) (by norm_num)
theorem B359245 : Blo 187803 359245 := bbase (se 3 (by rfl) ⟨67358, by rfl⟩ : syracuseStep 359245 = 134717) (by norm_num)
theorem B228181 : Blo 187803 228181 := bbase (se 9 (by rfl) ⟨668, by rfl⟩ : syracuseStep 228181 = 1337) (by norm_num)
theorem B424853 : Blo 187803 424853 := bbase (se 6 (by rfl) ⟨9957, by rfl⟩ : syracuseStep 424853 = 19915) (by norm_num)
theorem B424925 : Blo 187803 424925 := bbase (se 3 (by rfl) ⟨79673, by rfl⟩ : syracuseStep 424925 = 159347) (by norm_num)
theorem B326669 : Blo 187803 326669 := bbase (se 3 (by rfl) ⟨61250, by rfl⟩ : syracuseStep 326669 = 122501) (by norm_num)
theorem B261149 : Blo 187803 261149 := bbase (se 3 (by rfl) ⟨48965, by rfl⟩ : syracuseStep 261149 = 97931) (by norm_num)
theorem B424997 : Blo 187803 424997 := bbase (se 4 (by rfl) ⟨39843, by rfl⟩ : syracuseStep 424997 = 79687) (by norm_num)
theorem B457805 : Blo 187803 457805 := bbase (se 3 (by rfl) ⟨85838, by rfl⟩ : syracuseStep 457805 = 171677) (by norm_num)
theorem B425069 : Blo 187803 425069 := bbase (se 3 (by rfl) ⟨79700, by rfl⟩ : syracuseStep 425069 = 159401) (by norm_num)
theorem B359549 : Blo 187803 359549 := bbase (se 3 (by rfl) ⟨67415, by rfl⟩ : syracuseStep 359549 = 134831) (by norm_num)
theorem B425141 : Blo 187803 425141 := bbase (se 5 (by rfl) ⟨19928, by rfl⟩ : syracuseStep 425141 = 39857) (by norm_num)
theorem B1965269 : Blo 187803 1965269 := bbase (se 7 (by rfl) ⟨23030, by rfl⟩ : syracuseStep 1965269 = 46061) (by norm_num)
theorem B425213 : Blo 187803 425213 := bbase (se 3 (by rfl) ⟨79727, by rfl⟩ : syracuseStep 425213 = 159455) (by norm_num)
theorem B752933 : Blo 187803 752933 := bbase (se 4 (by rfl) ⟨70587, by rfl⟩ : syracuseStep 752933 = 141175) (by norm_num)
theorem B425285 : Blo 187803 425285 := bbase (se 4 (by rfl) ⟨39870, by rfl⟩ : syracuseStep 425285 = 79741) (by norm_num)
theorem B425357 : Blo 187803 425357 := bbase (se 3 (by rfl) ⟨79754, by rfl⟩ : syracuseStep 425357 = 159509) (by norm_num)
theorem B458189 : Blo 187803 458189 := bbase (se 3 (by rfl) ⟨85910, by rfl⟩ : syracuseStep 458189 = 171821) (by norm_num)
theorem B425429 : Blo 187803 425429 := bbase (se 7 (by rfl) ⟨4985, by rfl⟩ : syracuseStep 425429 = 9971) (by norm_num)
theorem B720373 : Blo 187803 720373 := bbase (se 5 (by rfl) ⟨33767, by rfl⟩ : syracuseStep 720373 = 67535) (by norm_num)
theorem B458237 : Blo 187803 458237 := bbase (se 3 (by rfl) ⟨85919, by rfl⟩ : syracuseStep 458237 = 171839) (by norm_num)
theorem B458245 : Blo 187803 458245 := bbase (se 4 (by rfl) ⟨42960, by rfl⟩ : syracuseStep 458245 = 85921) (by norm_num)
theorem B425501 : Blo 187803 425501 := bbase (se 3 (by rfl) ⟨79781, by rfl⟩ : syracuseStep 425501 = 159563) (by norm_num)
theorem B425573 : Blo 187803 425573 := bbase (se 4 (by rfl) ⟨39897, by rfl⟩ : syracuseStep 425573 = 79795) (by norm_num)
theorem B1638005 : Blo 187803 1638005 := bbase (se 5 (by rfl) ⟨76781, by rfl⟩ : syracuseStep 1638005 = 153563) (by norm_num)
theorem B425645 : Blo 187803 425645 := bbase (se 3 (by rfl) ⟨79808, by rfl⟩ : syracuseStep 425645 = 159617) (by norm_num)
theorem B327397 : Blo 187803 327397 := bbase (se 4 (by rfl) ⟨30693, by rfl⟩ : syracuseStep 327397 = 61387) (by norm_num)
theorem B425717 : Blo 187803 425717 := bbase (se 5 (by rfl) ⟨19955, by rfl⟩ : syracuseStep 425717 = 39911) (by norm_num)
theorem B491285 : Blo 187803 491285 := bbase (se 6 (by rfl) ⟨11514, by rfl⟩ : syracuseStep 491285 = 23029) (by norm_num)
theorem B720677 : Blo 187803 720677 := bbase (se 4 (by rfl) ⟨67563, by rfl⟩ : syracuseStep 720677 = 135127) (by norm_num)
theorem B425789 : Blo 187803 425789 := bbase (se 3 (by rfl) ⟨79835, by rfl⟩ : syracuseStep 425789 = 159671) (by norm_num)
theorem B360301 : Blo 187803 360301 := bbase (se 3 (by rfl) ⟨67556, by rfl⟩ : syracuseStep 360301 = 135113) (by norm_num)
theorem B425861 : Blo 187803 425861 := bbase (se 4 (by rfl) ⟨39924, by rfl⟩ : syracuseStep 425861 = 79849) (by norm_num)
theorem B425933 : Blo 187803 425933 := bbase (se 3 (by rfl) ⟨79862, by rfl⟩ : syracuseStep 425933 = 159725) (by norm_num)
theorem B360445 : Blo 187803 360445 := bbase (se 3 (by rfl) ⟨67583, by rfl⟩ : syracuseStep 360445 = 135167) (by norm_num)
theorem B425987 : Blo 187803 425987 := bstep (se 1 (by rfl) ⟨319490, by rfl⟩ : syracuseStep 425987 = 638981) B638981
theorem B229411 : Blo 187803 229411 := bstep (se 1 (by rfl) ⟨172058, by rfl⟩ : syracuseStep 229411 = 344117) B344117
theorem B1474757 : Blo 187803 1474757 := bstep (se 4 (by rfl) ⟨138258, by rfl⟩ : syracuseStep 1474757 = 276517) B276517
theorem B426257 : Blo 187803 426257 := bstep (se 2 (by rfl) ⟨159846, by rfl⟩ : syracuseStep 426257 = 319693) B319693
theorem B426275 : Blo 187803 426275 := bstep (se 1 (by rfl) ⟨319706, by rfl⟩ : syracuseStep 426275 = 639413) B639413
theorem B360931 : Blo 187803 360931 := bstep (se 1 (by rfl) ⟨270698, by rfl⟩ : syracuseStep 360931 = 541397) B541397
theorem B688625 : Blo 187803 688625 := bstep (se 2 (by rfl) ⟨258234, by rfl⟩ : syracuseStep 688625 = 516469) B516469
theorem B426545 : Blo 187803 426545 := bstep (se 2 (by rfl) ⟨159954, by rfl⟩ : syracuseStep 426545 = 319909) B319909
theorem B426563 : Blo 187803 426563 := bstep (se 1 (by rfl) ⟨319922, by rfl⟩ : syracuseStep 426563 = 639845) B639845
theorem B1475185 : Blo 187803 1475185 := bstep (se 2 (by rfl) ⟨553194, by rfl⟩ : syracuseStep 1475185 = 1106389) B1106389
theorem B361091 : Blo 187803 361091 := bstep (se 1 (by rfl) ⟨270818, by rfl⟩ : syracuseStep 361091 = 541637) B541637
theorem B1081997 : Blo 187803 1081997 := bstep (se 3 (by rfl) ⟨202874, by rfl⟩ : syracuseStep 1081997 = 405749) B405749
theorem B721649 : Blo 187803 721649 := bstep (se 2 (by rfl) ⟨270618, by rfl⟩ : syracuseStep 721649 = 541237) B541237
theorem B426833 : Blo 187803 426833 := bstep (se 2 (by rfl) ⟨160062, by rfl⟩ : syracuseStep 426833 = 320125) B320125
theorem B1016675 : Blo 187803 1016675 := bstep (se 1 (by rfl) ⟨762506, by rfl⟩ : syracuseStep 1016675 = 1525013) B1525013
theorem B426851 : Blo 187803 426851 := bstep (se 1 (by rfl) ⟨320138, by rfl⟩ : syracuseStep 426851 = 640277) B640277
theorem B590705 : Blo 187803 590705 := bstep (se 2 (by rfl) ⟨221514, by rfl⟩ : syracuseStep 590705 = 443029) B443029
theorem B1541105 : Blo 187803 1541105 := bstep (se 2 (by rfl) ⟨577914, by rfl⟩ : syracuseStep 1541105 = 1155829) B1155829
theorem B1016867 : Blo 187803 1016867 := bstep (se 1 (by rfl) ⟨762650, by rfl⟩ : syracuseStep 1016867 = 1525301) B1525301
theorem B427121 : Blo 187803 427121 := bstep (se 2 (by rfl) ⟨160170, by rfl⟩ : syracuseStep 427121 = 320341) B320341
theorem B427139 : Blo 187803 427139 := bstep (se 1 (by rfl) ⟨320354, by rfl⟩ : syracuseStep 427139 = 640709) B640709
theorem B689315 : Blo 187803 689315 := bstep (se 1 (by rfl) ⟨516986, by rfl⟩ : syracuseStep 689315 = 1033973) B1033973
theorem B951587 : Blo 187803 951587 := bstep (se 1 (by rfl) ⟨713690, by rfl⟩ : syracuseStep 951587 = 1427381) B1427381
theorem B755021 : Blo 187803 755021 := bstep (se 3 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 755021 = 283133) B283133
theorem B722317 : Blo 187803 722317 := bstep (se 3 (by rfl) ⟨135434, by rfl⟩ : syracuseStep 722317 = 270869) B270869
theorem B427409 : Blo 187803 427409 := bstep (se 2 (by rfl) ⟨160278, by rfl⟩ : syracuseStep 427409 = 320557) B320557
theorem B427427 : Blo 187803 427427 := bstep (se 1 (by rfl) ⟨320570, by rfl⟩ : syracuseStep 427427 = 641141) B641141
theorem B1082929 : Blo 187803 1082929 := bstep (se 2 (by rfl) ⟨406098, by rfl⟩ : syracuseStep 1082929 = 812197) B812197
theorem B1607309 : Blo 187803 1607309 := bstep (se 3 (by rfl) ⟨301370, by rfl⟩ : syracuseStep 1607309 = 602741) B602741
theorem B427697 : Blo 187803 427697 := bstep (se 2 (by rfl) ⟨160386, by rfl⟩ : syracuseStep 427697 = 320773) B320773
theorem B362161 : Blo 187803 362161 := bstep (se 2 (by rfl) ⟨135810, by rfl⟩ : syracuseStep 362161 = 271621) B271621
theorem B427715 : Blo 187803 427715 := bstep (se 1 (by rfl) ⟨320786, by rfl⟩ : syracuseStep 427715 = 641573) B641573
theorem B689905 : Blo 187803 689905 := bstep (se 2 (by rfl) ⟨258714, by rfl⟩ : syracuseStep 689905 = 517429) B517429
theorem B427985 : Blo 187803 427985 := bstep (se 2 (by rfl) ⟨160494, by rfl⟩ : syracuseStep 427985 = 320989) B320989
theorem B428003 : Blo 187803 428003 := bstep (se 1 (by rfl) ⟨321002, by rfl⟩ : syracuseStep 428003 = 642005) B642005
theorem B952397 : Blo 187803 952397 := bstep (se 3 (by rfl) ⟨178574, by rfl⟩ : syracuseStep 952397 = 357149) B357149
theorem B1378403 : Blo 187803 1378403 := bstep (se 1 (by rfl) ⟨1033802, by rfl⟩ : syracuseStep 1378403 = 2067605) B2067605
theorem B1214605 : Blo 187803 1214605 := bstep (se 3 (by rfl) ⟨227738, by rfl⟩ : syracuseStep 1214605 = 455477) B455477
theorem B723107 : Blo 187803 723107 := bstep (se 1 (by rfl) ⟨542330, by rfl⟩ : syracuseStep 723107 = 1084661) B1084661
theorem B428273 : Blo 187803 428273 := bstep (se 2 (by rfl) ⟨160602, by rfl⟩ : syracuseStep 428273 = 321205) B321205
theorem B428291 : Blo 187803 428291 := bstep (se 1 (by rfl) ⟨321218, by rfl⟩ : syracuseStep 428291 = 642437) B642437
theorem B428561 : Blo 187803 428561 := bstep (se 2 (by rfl) ⟨160710, by rfl⟩ : syracuseStep 428561 = 321421) B321421
theorem B428579 : Blo 187803 428579 := bstep (se 1 (by rfl) ⟨321434, by rfl⟩ : syracuseStep 428579 = 642869) B642869
theorem B363217 : Blo 187803 363217 := bstep (se 2 (by rfl) ⟨136206, by rfl⟩ : syracuseStep 363217 = 272413) B272413
theorem B428849 : Blo 187803 428849 := bstep (se 2 (by rfl) ⟨160818, by rfl⟩ : syracuseStep 428849 = 321637) B321637
theorem B723761 : Blo 187803 723761 := bstep (se 2 (by rfl) ⟨271410, by rfl⟩ : syracuseStep 723761 = 542821) B542821
theorem B428867 : Blo 187803 428867 := bstep (se 1 (by rfl) ⟨321650, by rfl⟩ : syracuseStep 428867 = 643301) B643301
theorem B1084387 : Blo 187803 1084387 := bstep (se 1 (by rfl) ⟨813290, by rfl⟩ : syracuseStep 1084387 = 1626581) B1626581
theorem B1444877 : Blo 187803 1444877 := bstep (se 3 (by rfl) ⟨270914, by rfl⟩ : syracuseStep 1444877 = 541829) B541829
theorem B429137 : Blo 187803 429137 := bstep (se 2 (by rfl) ⟨160926, by rfl⟩ : syracuseStep 429137 = 321853) B321853
theorem B429155 : Blo 187803 429155 := bstep (se 1 (by rfl) ⟨321866, by rfl⟩ : syracuseStep 429155 = 643733) B643733
theorem B363619 : Blo 187803 363619 := bstep (se 1 (by rfl) ⟨272714, by rfl⟩ : syracuseStep 363619 = 545429) B545429
theorem B363665 : Blo 187803 363665 := bstep (se 2 (by rfl) ⟨136374, by rfl⟩ : syracuseStep 363665 = 272749) B272749
theorem B2755781 : Blo 187803 2755781 := bstep (se 4 (by rfl) ⟨258354, by rfl⟩ : syracuseStep 2755781 = 516709) B516709
theorem B429425 : Blo 187803 429425 := bstep (se 2 (by rfl) ⟨161034, by rfl⟩ : syracuseStep 429425 = 322069) B322069
theorem B429443 : Blo 187803 429443 := bstep (se 1 (by rfl) ⟨322082, by rfl⟩ : syracuseStep 429443 = 644165) B644165
theorem B363953 : Blo 187803 363953 := bstep (se 2 (by rfl) ⟨136482, by rfl⟩ : syracuseStep 363953 = 272965) B272965
theorem B1084913 : Blo 187803 1084913 := bstep (se 2 (by rfl) ⟨406842, by rfl⟩ : syracuseStep 1084913 = 813685) B813685
theorem B1019461 : Blo 187803 1019461 := bstep (se 4 (by rfl) ⟨95574, by rfl⟩ : syracuseStep 1019461 = 191149) B191149
theorem B429713 : Blo 187803 429713 := bstep (se 2 (by rfl) ⟨161142, by rfl⟩ : syracuseStep 429713 = 322285) B322285
theorem B429731 : Blo 187803 429731 := bstep (se 1 (by rfl) ⟨322298, by rfl⟩ : syracuseStep 429731 = 644597) B644597
theorem B430001 : Blo 187803 430001 := bstep (se 2 (by rfl) ⟨161250, by rfl⟩ : syracuseStep 430001 = 322501) B322501
theorem B430019 : Blo 187803 430019 := bstep (se 1 (by rfl) ⟨322514, by rfl⟩ : syracuseStep 430019 = 645029) B645029
theorem B331793 : Blo 187803 331793 := bstep (se 2 (by rfl) ⟨124422, by rfl⟩ : syracuseStep 331793 = 248845) B248845
theorem B2330765 : Blo 187803 2330765 := bstep (se 3 (by rfl) ⟨437018, by rfl⟩ : syracuseStep 2330765 = 874037) B874037
theorem B430289 : Blo 187803 430289 := bstep (se 2 (by rfl) ⟨161358, by rfl⟩ : syracuseStep 430289 = 322717) B322717
theorem B725219 : Blo 187803 725219 := bstep (se 1 (by rfl) ⟨543914, by rfl⟩ : syracuseStep 725219 = 1087829) B1087829
theorem B430307 : Blo 187803 430307 := bstep (se 1 (by rfl) ⟨322730, by rfl⟩ : syracuseStep 430307 = 645461) B645461
theorem B725233 : Blo 187803 725233 := bstep (se 2 (by rfl) ⟨271962, by rfl⟩ : syracuseStep 725233 = 543925) B543925
theorem B4886897 : Blo 187803 4886897 := bstep (se 2 (by rfl) ⟨1832586, by rfl⟩ : syracuseStep 4886897 = 3665173) B3665173
theorem B856433 : Blo 187803 856433 := bstep (se 2 (by rfl) ⟨321162, by rfl⟩ : syracuseStep 856433 = 642325) B642325
theorem B201187 : Blo 187803 201187 := bstep (se 1 (by rfl) ⟨150890, by rfl⟩ : syracuseStep 201187 = 301781) B301781
theorem B430577 : Blo 187803 430577 := bstep (se 2 (by rfl) ⟨161466, by rfl⟩ : syracuseStep 430577 = 322933) B322933
theorem B430595 : Blo 187803 430595 := bstep (se 1 (by rfl) ⟨322946, by rfl⟩ : syracuseStep 430595 = 645893) B645893
theorem B299585 : Blo 187803 299585 := bstep (se 2 (by rfl) ⟨112344, by rfl⟩ : syracuseStep 299585 = 224689) B224689
theorem B2429621 : Blo 187803 2429621 := bstep (se 5 (by rfl) ⟨113888, by rfl⟩ : syracuseStep 2429621 = 227777) B227777
theorem B430865 : Blo 187803 430865 := bstep (se 2 (by rfl) ⟨161574, by rfl⟩ : syracuseStep 430865 = 323149) B323149
theorem B430883 : Blo 187803 430883 := bstep (se 1 (by rfl) ⟨323162, by rfl⟩ : syracuseStep 430883 = 646325) B646325
theorem B1086371 : Blo 187803 1086371 := bstep (se 1 (by rfl) ⟨814778, by rfl⟩ : syracuseStep 1086371 = 1629557) B1629557
theorem B955313 : Blo 187803 955313 := bstep (se 2 (by rfl) ⟨358242, by rfl⟩ : syracuseStep 955313 = 716485) B716485
theorem B431153 : Blo 187803 431153 := bstep (se 2 (by rfl) ⟨161682, by rfl⟩ : syracuseStep 431153 = 323365) B323365
theorem B431171 : Blo 187803 431171 := bstep (se 1 (by rfl) ⟨323378, by rfl⟩ : syracuseStep 431171 = 646757) B646757
theorem B267475 : Blo 187803 267475 := bstep (se 1 (by rfl) ⟨200606, by rfl⟩ : syracuseStep 267475 = 401213) B401213
theorem B431441 : Blo 187803 431441 := bstep (se 2 (by rfl) ⟨161790, by rfl⟩ : syracuseStep 431441 = 323581) B323581
theorem B431459 : Blo 187803 431459 := bstep (se 1 (by rfl) ⟨323594, by rfl⟩ : syracuseStep 431459 = 647189) B647189
theorem B202195 : Blo 187803 202195 := bstep (se 1 (by rfl) ⟨151646, by rfl⟩ : syracuseStep 202195 = 303293) B303293
theorem B726691 : Blo 187803 726691 := bstep (se 1 (by rfl) ⟨545018, by rfl⟩ : syracuseStep 726691 = 1090037) B1090037
theorem B267953 : Blo 187803 267953 := bstep (se 2 (by rfl) ⟨100482, by rfl⟩ : syracuseStep 267953 = 200965) B200965
theorem B268067 : Blo 187803 268067 := bstep (se 1 (by rfl) ⟨201050, by rfl⟩ : syracuseStep 268067 = 402101) B402101
theorem B1447793 : Blo 187803 1447793 := bstep (se 2 (by rfl) ⟨542922, by rfl⟩ : syracuseStep 1447793 = 1085845) B1085845
theorem B268147 : Blo 187803 268147 := bstep (se 1 (by rfl) ⟨201110, by rfl⟩ : syracuseStep 268147 = 402221) B402221
theorem B202819 : Blo 187803 202819 := bstep (se 1 (by rfl) ⟨152114, by rfl⟩ : syracuseStep 202819 = 304229) B304229
theorem B301153 : Blo 187803 301153 := bstep (se 2 (by rfl) ⟨112932, by rfl⟩ : syracuseStep 301153 = 225865) B225865
theorem B2070755 : Blo 187803 2070755 := bstep (se 1 (by rfl) ⟨1553066, by rfl⟩ : syracuseStep 2070755 = 3106133) B3106133
theorem B956771 : Blo 187803 956771 := bstep (se 1 (by rfl) ⟨717578, by rfl⟩ : syracuseStep 956771 = 1435157) B1435157
theorem B268705 : Blo 187803 268705 := bstep (se 2 (by rfl) ⟨100764, by rfl⟩ : syracuseStep 268705 = 201529) B201529
theorem B301601 : Blo 187803 301601 := bstep (se 2 (by rfl) ⟨113100, by rfl⟩ : syracuseStep 301601 = 226201) B226201
theorem B1088261 : Blo 187803 1088261 := bstep (se 4 (by rfl) ⟨102024, by rfl⟩ : syracuseStep 1088261 = 204049) B204049
theorem B2235235 : Blo 187803 2235235 := bstep (se 1 (by rfl) ⟨1676426, by rfl⟩ : syracuseStep 2235235 = 3352853) B3352853
theorem B269411 : Blo 187803 269411 := bstep (se 1 (by rfl) ⟨202058, by rfl⟩ : syracuseStep 269411 = 404117) B404117
theorem B957581 : Blo 187803 957581 := bstep (se 3 (by rfl) ⟨179546, by rfl⟩ : syracuseStep 957581 = 359093) B359093
theorem B2202805 : Blo 187803 2202805 := bstep (se 5 (by rfl) ⟨103256, by rfl⟩ : syracuseStep 2202805 = 206513) B206513
theorem B302467 : Blo 187803 302467 := bstep (se 1 (by rfl) ⟨226850, by rfl⟩ : syracuseStep 302467 = 453701) B453701
theorem B1744355 : Blo 187803 1744355 := bstep (se 1 (by rfl) ⟨1308266, by rfl⟩ : syracuseStep 1744355 = 2616533) B2616533
theorem B1449571 : Blo 187803 1449571 := bstep (se 1 (by rfl) ⟨1087178, by rfl⟩ : syracuseStep 1449571 = 2174357) B2174357
theorem B270049 : Blo 187803 270049 := bstep (se 2 (by rfl) ⟨101268, by rfl⟩ : syracuseStep 270049 = 202537) B202537
theorem B270163 : Blo 187803 270163 := bstep (se 1 (by rfl) ⟨202622, by rfl⟩ : syracuseStep 270163 = 405245) B405245
theorem B204707 : Blo 187803 204707 := bstep (se 1 (by rfl) ⟨153530, by rfl⟩ : syracuseStep 204707 = 307061) B307061
theorem B303139 : Blo 187803 303139 := bstep (se 1 (by rfl) ⟨227354, by rfl⟩ : syracuseStep 303139 = 454709) B454709
theorem B696397 : Blo 187803 696397 := bstep (se 3 (by rfl) ⟨130574, by rfl⟩ : syracuseStep 696397 = 261149) B261149
theorem B303185 : Blo 187803 303185 := bstep (se 2 (by rfl) ⟨113694, by rfl⟩ : syracuseStep 303185 = 227389) B227389
theorem B237811 : Blo 187803 237811 := bstep (se 1 (by rfl) ⟨178358, by rfl⟩ : syracuseStep 237811 = 356717) B356717
theorem B237907 : Blo 187803 237907 := bstep (se 1 (by rfl) ⟨178430, by rfl⟩ : syracuseStep 237907 = 356861) B356861
theorem B696689 : Blo 187803 696689 := bstep (se 2 (by rfl) ⟨261258, by rfl⟩ : syracuseStep 696689 = 522517) B522517
theorem B1286533 : Blo 187803 1286533 := bstep (se 4 (by rfl) ⟨120612, by rfl⟩ : syracuseStep 1286533 = 241225) B241225
theorem B303697 : Blo 187803 303697 := bstep (se 2 (by rfl) ⟨113886, by rfl⟩ : syracuseStep 303697 = 227773) B227773
theorem B1221425 : Blo 187803 1221425 := bstep (se 2 (by rfl) ⟨458034, by rfl⟩ : syracuseStep 1221425 = 916069) B916069
theorem B238403 : Blo 187803 238403 := bstep (se 1 (by rfl) ⟨178802, by rfl⟩ : syracuseStep 238403 = 357605) B357605
theorem B730019 : Blo 187803 730019 := bstep (se 1 (by rfl) ⟨547514, by rfl⟩ : syracuseStep 730019 = 1095029) B1095029
theorem B402545 : Blo 187803 402545 := bstep (se 2 (by rfl) ⟨150954, by rfl⟩ : syracuseStep 402545 = 301909) B301909
theorem B304241 : Blo 187803 304241 := bstep (se 2 (by rfl) ⟨114090, by rfl⟩ : syracuseStep 304241 = 228181) B228181
theorem B402563 : Blo 187803 402563 := bstep (se 1 (by rfl) ⟨301922, by rfl⟩ : syracuseStep 402563 = 603845) B603845
theorem B271507 : Blo 187803 271507 := bstep (se 1 (by rfl) ⟨203630, by rfl⟩ : syracuseStep 271507 = 407261) B407261
theorem B1221965 : Blo 187803 1221965 := bstep (se 3 (by rfl) ⟨229118, by rfl⟩ : syracuseStep 1221965 = 458237) B458237
theorem B239107 : Blo 187803 239107 := bstep (se 1 (by rfl) ⟨179330, by rfl⟩ : syracuseStep 239107 = 358661) B358661
theorem B1615373 : Blo 187803 1615373 := bstep (se 3 (by rfl) ⟨302882, by rfl⟩ : syracuseStep 1615373 = 605765) B605765
theorem B239203 : Blo 187803 239203 := bstep (se 1 (by rfl) ⟨179402, by rfl⟩ : syracuseStep 239203 = 358805) B358805
theorem B1025669 : Blo 187803 1025669 := bstep (se 4 (by rfl) ⟨96156, by rfl⟩ : syracuseStep 1025669 = 192313) B192313
theorem B4368013 : Blo 187803 4368013 := bstep (se 3 (by rfl) ⟨819002, by rfl⟩ : syracuseStep 4368013 = 1638005) B1638005
theorem B960497 : Blo 187803 960497 := bstep (se 2 (by rfl) ⟨360186, by rfl⟩ : syracuseStep 960497 = 720373) B720373
theorem B305203 : Blo 187803 305203 := bstep (se 1 (by rfl) ⟨228902, by rfl⟩ : syracuseStep 305203 = 457805) B457805
theorem B239699 : Blo 187803 239699 := bstep (se 1 (by rfl) ⟨179774, by rfl⟩ : syracuseStep 239699 = 359549) B359549
theorem B501955 : Blo 187803 501955 := bstep (se 1 (by rfl) ⟨376466, by rfl⟩ : syracuseStep 501955 = 752933) B752933
theorem B272641 : Blo 187803 272641 := bstep (se 2 (by rfl) ⟨102240, by rfl⟩ : syracuseStep 272641 = 204481) B204481
theorem B436529 : Blo 187803 436529 := bstep (se 2 (by rfl) ⟨163698, by rfl⟩ : syracuseStep 436529 = 327397) B327397
theorem B305459 : Blo 187803 305459 := bstep (se 1 (by rfl) ⟨229094, by rfl⟩ : syracuseStep 305459 = 458189) B458189
theorem B272737 : Blo 187803 272737 := bstep (se 2 (by rfl) ⟨102276, by rfl⟩ : syracuseStep 272737 = 204553) B204553
theorem B272899 : Blo 187803 272899 := bstep (se 1 (by rfl) ⟨204674, by rfl⟩ : syracuseStep 272899 = 409349) B409349
theorem B240403 : Blo 187803 240403 := bstep (se 1 (by rfl) ⟨180302, by rfl⟩ : syracuseStep 240403 = 360605) B360605
theorem B863075 : Blo 187803 863075 := bstep (se 1 (by rfl) ⟨647306, by rfl⟩ : syracuseStep 863075 = 1294613) B1294613
theorem B535405 : Blo 187803 535405 := bstep (se 3 (by rfl) ⟨100388, by rfl⟩ : syracuseStep 535405 = 200777) B200777
theorem B240499 : Blo 187803 240499 := bstep (se 1 (by rfl) ⟨180374, by rfl⟩ : syracuseStep 240499 = 360749) B360749
theorem B2173877 : Blo 187803 2173877 := bstep (se 5 (by rfl) ⟨101900, by rfl⟩ : syracuseStep 2173877 = 203801) B203801
theorem B306163 : Blo 187803 306163 := bstep (se 1 (by rfl) ⟨229622, by rfl⟩ : syracuseStep 306163 = 459245) B459245
theorem B535565 : Blo 187803 535565 := bstep (se 3 (by rfl) ⟨100418, by rfl⟩ : syracuseStep 535565 = 200837) B200837
theorem B633905 : Blo 187803 633905 := bstep (se 2 (by rfl) ⟨237714, by rfl⟩ : syracuseStep 633905 = 475429) B475429
theorem B404561 : Blo 187803 404561 := bstep (se 2 (by rfl) ⟨151710, by rfl⟩ : syracuseStep 404561 = 303421) B303421
theorem B535747 : Blo 187803 535747 := bstep (se 1 (by rfl) ⟨401810, by rfl⟩ : syracuseStep 535747 = 803621) B803621
theorem B2764003 : Blo 187803 2764003 := bstep (se 1 (by rfl) ⟨2073002, by rfl⟩ : syracuseStep 2764003 = 4146005) B4146005
theorem B306433 : Blo 187803 306433 := bstep (se 2 (by rfl) ⟨114912, by rfl⟩ : syracuseStep 306433 = 229825) B229825
theorem B732451 : Blo 187803 732451 := bstep (se 1 (by rfl) ⟨549338, by rfl⟩ : syracuseStep 732451 = 1098677) B1098677
theorem B306497 : Blo 187803 306497 := bstep (se 2 (by rfl) ⟨114936, by rfl⟩ : syracuseStep 306497 = 229873) B229873
theorem B240995 : Blo 187803 240995 := bstep (se 1 (by rfl) ⟨180746, by rfl⟩ : syracuseStep 240995 = 361493) B361493
theorem B961955 : Blo 187803 961955 := bstep (se 1 (by rfl) ⟨721466, by rfl⟩ : syracuseStep 961955 = 1442933) B1442933
theorem B634445 : Blo 187803 634445 := bstep (se 3 (by rfl) ⟨118958, by rfl⟩ : syracuseStep 634445 = 237917) B237917
theorem B405091 : Blo 187803 405091 := bstep (se 1 (by rfl) ⟨303818, by rfl⟩ : syracuseStep 405091 = 607637) B607637
theorem B634499 : Blo 187803 634499 := bstep (se 1 (by rfl) ⟨475874, by rfl⟩ : syracuseStep 634499 = 951749) B951749
theorem B241523 : Blo 187803 241523 := bstep (se 1 (by rfl) ⟨181142, by rfl⟩ : syracuseStep 241523 = 362285) B362285
theorem B634769 : Blo 187803 634769 := bstep (se 2 (by rfl) ⟨238038, by rfl⟩ : syracuseStep 634769 = 476077) B476077
theorem B241699 : Blo 187803 241699 := bstep (se 1 (by rfl) ⟨181274, by rfl⟩ : syracuseStep 241699 = 362549) B362549
theorem B241715 : Blo 187803 241715 := bstep (se 1 (by rfl) ⟨181286, by rfl⟩ : syracuseStep 241715 = 362573) B362573
theorem B241795 : Blo 187803 241795 := bstep (se 1 (by rfl) ⟨181346, by rfl⟩ : syracuseStep 241795 = 362693) B362693
theorem B962765 : Blo 187803 962765 := bstep (se 3 (by rfl) ⟨180518, by rfl⟩ : syracuseStep 962765 = 361037) B361037
theorem B635309 : Blo 187803 635309 := bstep (se 3 (by rfl) ⟨119120, by rfl⟩ : syracuseStep 635309 = 238241) B238241
theorem B1225165 : Blo 187803 1225165 := bstep (se 3 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 1225165 = 459437) B459437
theorem B635363 : Blo 187803 635363 := bstep (se 1 (by rfl) ⟨476522, by rfl⟩ : syracuseStep 635363 = 953045) B953045
theorem B2241037 : Blo 187803 2241037 := bstep (se 3 (by rfl) ⟨420194, by rfl⟩ : syracuseStep 2241037 = 840389) B840389
theorem B537137 : Blo 187803 537137 := bstep (se 2 (by rfl) ⟨201426, by rfl⟩ : syracuseStep 537137 = 402853) B402853
theorem B242291 : Blo 187803 242291 := bstep (se 1 (by rfl) ⟨181718, by rfl⟩ : syracuseStep 242291 = 363437) B363437
theorem B635633 : Blo 187803 635633 := bstep (se 2 (by rfl) ⟨238362, by rfl⟩ : syracuseStep 635633 = 476725) B476725
theorem B603089 : Blo 187803 603089 := bstep (se 2 (by rfl) ⟨226158, by rfl⟩ : syracuseStep 603089 = 452317) B452317
theorem B406577 : Blo 187803 406577 := bstep (se 2 (by rfl) ⟨152466, by rfl⟩ : syracuseStep 406577 = 304933) B304933
theorem B406595 : Blo 187803 406595 := bstep (se 1 (by rfl) ⟨304946, by rfl⟩ : syracuseStep 406595 = 609893) B609893
theorem B636173 : Blo 187803 636173 := bstep (se 3 (by rfl) ⟨119282, by rfl⟩ : syracuseStep 636173 = 238565) B238565
theorem B636227 : Blo 187803 636227 := bstep (se 1 (by rfl) ⟨477170, by rfl⟩ : syracuseStep 636227 = 954341) B954341
theorem B308627 : Blo 187803 308627 := bstep (se 1 (by rfl) ⟨231470, by rfl⟩ : syracuseStep 308627 = 462941) B462941
theorem B538093 : Blo 187803 538093 := bstep (se 3 (by rfl) ⟨100892, by rfl⟩ : syracuseStep 538093 = 201785) B201785
theorem B603715 : Blo 187803 603715 := bstep (se 1 (by rfl) ⟨452786, by rfl⟩ : syracuseStep 603715 = 905573) B905573
theorem B636497 : Blo 187803 636497 := bstep (se 2 (by rfl) ⟨238686, by rfl⟩ : syracuseStep 636497 = 477373) B477373
theorem B538321 : Blo 187803 538321 := bstep (se 2 (by rfl) ⟨201870, by rfl⟩ : syracuseStep 538321 = 403741) B403741
theorem B1357667 : Blo 187803 1357667 := bstep (se 1 (by rfl) ⟨1018250, by rfl⟩ : syracuseStep 1357667 = 2036501) B2036501
theorem B538481 : Blo 187803 538481 := bstep (se 2 (by rfl) ⟨201930, by rfl⟩ : syracuseStep 538481 = 403861) B403861
theorem B1161101 : Blo 187803 1161101 := bstep (se 3 (by rfl) ⟨217706, by rfl⟩ : syracuseStep 1161101 = 435413) B435413
theorem B538595 : Blo 187803 538595 := bstep (se 1 (by rfl) ⟨403946, by rfl⟩ : syracuseStep 538595 = 807893) B807893
theorem B767971 : Blo 187803 767971 := bstep (se 1 (by rfl) ⟨575978, by rfl⟩ : syracuseStep 767971 = 1151957) B1151957
theorem B637037 : Blo 187803 637037 := bstep (se 3 (by rfl) ⟨119444, by rfl⟩ : syracuseStep 637037 = 238889) B238889
theorem B637091 : Blo 187803 637091 := bstep (se 1 (by rfl) ⟨477818, by rfl⟩ : syracuseStep 637091 = 955637) B955637
theorem B407825 : Blo 187803 407825 := bstep (se 2 (by rfl) ⟨152934, by rfl⟩ : syracuseStep 407825 = 305869) B305869
theorem B211315 : Blo 187803 211315 := bstep (se 1 (by rfl) ⟨158486, by rfl⟩ : syracuseStep 211315 = 316973) B316973
theorem B637361 : Blo 187803 637361 := bstep (se 2 (by rfl) ⟨239010, by rfl⟩ : syracuseStep 637361 = 478021) B478021
theorem B211459 : Blo 187803 211459 := bstep (se 1 (by rfl) ⟨158594, by rfl⟩ : syracuseStep 211459 = 317189) B317189
theorem B1161733 : Blo 187803 1161733 := bstep (se 4 (by rfl) ⟨108912, by rfl⟩ : syracuseStep 1161733 = 217825) B217825
theorem B1358477 : Blo 187803 1358477 := bstep (se 3 (by rfl) ⟨254714, by rfl⟩ : syracuseStep 1358477 = 509429) B509429
theorem B211603 : Blo 187803 211603 := bstep (se 1 (by rfl) ⟨158702, by rfl⟩ : syracuseStep 211603 = 317405) B317405
theorem B604945 : Blo 187803 604945 := bstep (se 2 (by rfl) ⟨226854, by rfl⟩ : syracuseStep 604945 = 453709) B453709
theorem B211747 : Blo 187803 211747 := bstep (se 1 (by rfl) ⟨158810, by rfl⟩ : syracuseStep 211747 = 317621) B317621
theorem B342929 : Blo 187803 342929 := bstep (se 2 (by rfl) ⟨128598, by rfl⟩ : syracuseStep 342929 = 257197) B257197
theorem B211891 : Blo 187803 211891 := bstep (se 1 (by rfl) ⟨158918, by rfl⟩ : syracuseStep 211891 = 317837) B317837
theorem B637901 : Blo 187803 637901 := bstep (se 3 (by rfl) ⟨119606, by rfl⟩ : syracuseStep 637901 = 239213) B239213
theorem B539597 : Blo 187803 539597 := bstep (se 3 (by rfl) ⟨101174, by rfl⟩ : syracuseStep 539597 = 202349) B202349
theorem B637955 : Blo 187803 637955 := bstep (se 1 (by rfl) ⟨478466, by rfl⟩ : syracuseStep 637955 = 956933) B956933
theorem B965681 : Blo 187803 965681 := bstep (se 2 (by rfl) ⟨362130, by rfl⟩ : syracuseStep 965681 = 724261) B724261
theorem B212035 : Blo 187803 212035 := bstep (se 1 (by rfl) ⟨159026, by rfl⟩ : syracuseStep 212035 = 318053) B318053
theorem B539779 : Blo 187803 539779 := bstep (se 1 (by rfl) ⟨404834, by rfl⟩ : syracuseStep 539779 = 809669) B809669
theorem B343217 : Blo 187803 343217 := bstep (se 2 (by rfl) ⟨128706, by rfl⟩ : syracuseStep 343217 = 257413) B257413
theorem B212179 : Blo 187803 212179 := bstep (se 1 (by rfl) ⟨159134, by rfl⟩ : syracuseStep 212179 = 318269) B318269
theorem B638225 : Blo 187803 638225 := bstep (se 2 (by rfl) ⟨239334, by rfl⟩ : syracuseStep 638225 = 478669) B478669
theorem B539939 : Blo 187803 539939 := bstep (se 1 (by rfl) ⟨404954, by rfl⟩ : syracuseStep 539939 = 809909) B809909
theorem B212323 : Blo 187803 212323 := bstep (se 1 (by rfl) ⟨159242, by rfl⟩ : syracuseStep 212323 = 318485) B318485
theorem B605549 : Blo 187803 605549 := bstep (se 3 (by rfl) ⟨113540, by rfl⟩ : syracuseStep 605549 = 227081) B227081
theorem B5848517 : Blo 187803 5848517 := bstep (se 4 (by rfl) ⟨548298, by rfl⟩ : syracuseStep 5848517 = 1096597) B1096597
theorem B343523 : Blo 187803 343523 := bstep (se 1 (by rfl) ⟨257642, by rfl⟩ : syracuseStep 343523 = 515285) B515285
theorem B212467 : Blo 187803 212467 := bstep (se 1 (by rfl) ⟨159350, by rfl⟩ : syracuseStep 212467 = 318701) B318701
theorem B212611 : Blo 187803 212611 := bstep (se 1 (by rfl) ⟨159458, by rfl⟩ : syracuseStep 212611 = 318917) B318917
theorem B343697 : Blo 187803 343697 := bstep (se 2 (by rfl) ⟨128886, by rfl⟩ : syracuseStep 343697 = 257773) B257773
theorem B212755 : Blo 187803 212755 := bstep (se 1 (by rfl) ⟨159566, by rfl⟩ : syracuseStep 212755 = 319133) B319133
theorem B409379 : Blo 187803 409379 := bstep (se 1 (by rfl) ⟨307034, by rfl⟩ : syracuseStep 409379 = 614069) B614069
theorem B638765 : Blo 187803 638765 := bstep (se 3 (by rfl) ⟨119768, by rfl⟩ : syracuseStep 638765 = 239537) B239537
theorem B638819 : Blo 187803 638819 := bstep (se 1 (by rfl) ⟨479114, by rfl⟩ : syracuseStep 638819 = 958229) B958229
theorem B212899 : Blo 187803 212899 := bstep (se 1 (by rfl) ⟨159674, by rfl⟩ : syracuseStep 212899 = 319349) B319349
theorem B213043 : Blo 187803 213043 := bstep (se 1 (by rfl) ⟨159782, by rfl⟩ : syracuseStep 213043 = 319565) B319565
theorem B639089 : Blo 187803 639089 := bstep (se 2 (by rfl) ⟨239658, by rfl⟩ : syracuseStep 639089 = 479317) B479317
theorem B508045 : Blo 187803 508045 := bstep (se 3 (by rfl) ⟨95258, by rfl⟩ : syracuseStep 508045 = 190517) B190517
theorem B213187 : Blo 187803 213187 := bstep (se 1 (by rfl) ⟨159890, by rfl⟩ : syracuseStep 213187 = 319781) B319781
theorem B409841 : Blo 187803 409841 := bstep (se 2 (by rfl) ⟨153690, by rfl⟩ : syracuseStep 409841 = 307381) B307381
theorem B475409 : Blo 187803 475409 := bstep (se 2 (by rfl) ⟨178278, by rfl⟩ : syracuseStep 475409 = 356557) B356557
theorem B541009 : Blo 187803 541009 := bstep (se 2 (by rfl) ⟨202878, by rfl⟩ : syracuseStep 541009 = 405757) B405757
theorem B213331 : Blo 187803 213331 := bstep (se 1 (by rfl) ⟨159998, by rfl⟩ : syracuseStep 213331 = 319997) B319997
theorem B213475 : Blo 187803 213475 := bstep (se 1 (by rfl) ⟨160106, by rfl⟩ : syracuseStep 213475 = 320213) B320213
theorem B967139 : Blo 187803 967139 := bstep (se 1 (by rfl) ⟨725354, by rfl⟩ : syracuseStep 967139 = 1450709) B1450709
theorem B410179 : Blo 187803 410179 := bstep (se 1 (by rfl) ⟨307634, by rfl⟩ : syracuseStep 410179 = 615269) B615269
theorem B2048611 : Blo 187803 2048611 := bstep (se 1 (by rfl) ⟨1536458, by rfl⟩ : syracuseStep 2048611 = 3072917) B3072917
theorem B213619 : Blo 187803 213619 := bstep (se 1 (by rfl) ⟨160214, by rfl⟩ : syracuseStep 213619 = 320429) B320429
theorem B639629 : Blo 187803 639629 := bstep (se 3 (by rfl) ⟨119930, by rfl⟩ : syracuseStep 639629 = 239861) B239861
theorem B639683 : Blo 187803 639683 := bstep (se 1 (by rfl) ⟨479762, by rfl⟩ : syracuseStep 639683 = 959525) B959525
theorem B213763 : Blo 187803 213763 := bstep (se 1 (by rfl) ⟨160322, by rfl⟩ : syracuseStep 213763 = 320645) B320645
theorem B1295153 : Blo 187803 1295153 := bstep (se 2 (by rfl) ⟨485682, by rfl⟩ : syracuseStep 1295153 = 971365) B971365
theorem B508781 : Blo 187803 508781 := bstep (se 3 (by rfl) ⟨95396, by rfl⟩ : syracuseStep 508781 = 190793) B190793
theorem B213907 : Blo 187803 213907 := bstep (se 1 (by rfl) ⟨160430, by rfl⟩ : syracuseStep 213907 = 320861) B320861
theorem B639953 : Blo 187803 639953 := bstep (se 2 (by rfl) ⟨239982, by rfl⟩ : syracuseStep 639953 = 479965) B479965
theorem B214051 : Blo 187803 214051 := bstep (se 1 (by rfl) ⟨160538, by rfl⟩ : syracuseStep 214051 = 321077) B321077
theorem B312419 : Blo 187803 312419 := bstep (se 1 (by rfl) ⟨234314, by rfl⟩ : syracuseStep 312419 = 468629) B468629
theorem B214195 : Blo 187803 214195 := bstep (se 1 (by rfl) ⟨160646, by rfl⟩ : syracuseStep 214195 = 321293) B321293
theorem B476401 : Blo 187803 476401 := bstep (se 2 (by rfl) ⟨178650, by rfl⟩ : syracuseStep 476401 = 357301) B357301
theorem B967949 : Blo 187803 967949 := bstep (se 3 (by rfl) ⟨181490, by rfl⟩ : syracuseStep 967949 = 362981) B362981
theorem B214339 : Blo 187803 214339 := bstep (se 1 (by rfl) ⟨160754, by rfl⟩ : syracuseStep 214339 = 321509) B321509
theorem B214483 : Blo 187803 214483 := bstep (se 1 (by rfl) ⟨160862, by rfl⟩ : syracuseStep 214483 = 321725) B321725
theorem B640493 : Blo 187803 640493 := bstep (se 3 (by rfl) ⟨120092, by rfl⟩ : syracuseStep 640493 = 240185) B240185
theorem B476675 : Blo 187803 476675 := bstep (se 1 (by rfl) ⟨357506, by rfl⟩ : syracuseStep 476675 = 715013) B715013
theorem B345617 : Blo 187803 345617 := bstep (se 2 (by rfl) ⟨129606, by rfl⟩ : syracuseStep 345617 = 259213) B259213
theorem B640547 : Blo 187803 640547 := bstep (se 1 (by rfl) ⟨480410, by rfl⟩ : syracuseStep 640547 = 960821) B960821
theorem B542285 : Blo 187803 542285 := bstep (se 3 (by rfl) ⟨101678, by rfl⟩ : syracuseStep 542285 = 203357) B203357
theorem B214627 : Blo 187803 214627 := bstep (se 1 (by rfl) ⟨160970, by rfl⟩ : syracuseStep 214627 = 321941) B321941
theorem B476867 : Blo 187803 476867 := bstep (se 1 (by rfl) ⟨357650, by rfl⟩ : syracuseStep 476867 = 715301) B715301
theorem B411331 : Blo 187803 411331 := bstep (se 1 (by rfl) ⟨308498, by rfl⟩ : syracuseStep 411331 = 616997) B616997
theorem B509645 : Blo 187803 509645 := bstep (se 3 (by rfl) ⟨95558, by rfl⟩ : syracuseStep 509645 = 191117) B191117
theorem B214771 : Blo 187803 214771 := bstep (se 1 (by rfl) ⟨161078, by rfl⟩ : syracuseStep 214771 = 322157) B322157
theorem B542467 : Blo 187803 542467 := bstep (se 1 (by rfl) ⟨406850, by rfl⟩ : syracuseStep 542467 = 813701) B813701
theorem B640817 : Blo 187803 640817 := bstep (se 2 (by rfl) ⟨240306, by rfl⟩ : syracuseStep 640817 = 480613) B480613
theorem B542513 : Blo 187803 542513 := bstep (se 2 (by rfl) ⟨203442, by rfl⟩ : syracuseStep 542513 = 406885) B406885
theorem B214915 : Blo 187803 214915 := bstep (se 1 (by rfl) ⟨161186, by rfl⟩ : syracuseStep 214915 = 322373) B322373
theorem B509905 : Blo 187803 509905 := bstep (se 2 (by rfl) ⟨191214, by rfl⟩ : syracuseStep 509905 = 382429) B382429
theorem B215059 : Blo 187803 215059 := bstep (se 1 (by rfl) ⟨161294, by rfl⟩ : syracuseStep 215059 = 322589) B322589
theorem B4769813 : Blo 187803 4769813 := bstep (se 6 (by rfl) ⟨111792, by rfl⟩ : syracuseStep 4769813 = 223585) B223585
theorem B215203 : Blo 187803 215203 := bstep (se 1 (by rfl) ⟨161402, by rfl⟩ : syracuseStep 215203 = 322805) B322805
theorem B215347 : Blo 187803 215347 := bstep (se 1 (by rfl) ⟨161510, by rfl⟩ : syracuseStep 215347 = 323021) B323021
theorem B641357 : Blo 187803 641357 := bstep (se 3 (by rfl) ⟨120254, by rfl⟩ : syracuseStep 641357 = 240509) B240509
theorem B641411 : Blo 187803 641411 := bstep (se 1 (by rfl) ⟨481058, by rfl⟩ : syracuseStep 641411 = 962117) B962117
theorem B805261 : Blo 187803 805261 := bstep (se 3 (by rfl) ⟨150986, by rfl⟩ : syracuseStep 805261 = 301973) B301973
theorem B215491 : Blo 187803 215491 := bstep (se 1 (by rfl) ⟨161618, by rfl⟩ : syracuseStep 215491 = 323237) B323237
theorem B510509 : Blo 187803 510509 := bstep (se 3 (by rfl) ⟨95720, by rfl⟩ : syracuseStep 510509 = 191441) B191441
theorem B215635 : Blo 187803 215635 := bstep (se 1 (by rfl) ⟨161726, by rfl⟩ : syracuseStep 215635 = 323453) B323453
theorem B608867 : Blo 187803 608867 := bstep (se 1 (by rfl) ⟨456650, by rfl⟩ : syracuseStep 608867 = 913301) B913301
theorem B477809 : Blo 187803 477809 := bstep (se 2 (by rfl) ⟨179178, by rfl⟩ : syracuseStep 477809 = 358357) B358357
theorem B641681 : Blo 187803 641681 := bstep (se 2 (by rfl) ⟨240630, by rfl⟩ : syracuseStep 641681 = 481261) B481261
theorem B477859 : Blo 187803 477859 := bstep (se 1 (by rfl) ⟨358394, by rfl⟩ : syracuseStep 477859 = 716789) B716789
theorem B1166021 : Blo 187803 1166021 := bstep (se 4 (by rfl) ⟨109314, by rfl⟩ : syracuseStep 1166021 = 218629) B218629
theorem B871117 : Blo 187803 871117 := bstep (se 3 (by rfl) ⟨163334, by rfl⟩ : syracuseStep 871117 = 326669) B326669
theorem B2149091 : Blo 187803 2149091 := bstep (se 1 (by rfl) ⟨1611818, by rfl⟩ : syracuseStep 2149091 = 3223637) B3223637
theorem B215779 : Blo 187803 215779 := bstep (se 1 (by rfl) ⟨161834, by rfl⟩ : syracuseStep 215779 = 323669) B323669
theorem B478001 : Blo 187803 478001 := bstep (se 2 (by rfl) ⟨179250, by rfl⟩ : syracuseStep 478001 = 358501) B358501
theorem B281729 : Blo 187803 281729 := bstep (se 2 (by rfl) ⟨105648, by rfl⟩ : syracuseStep 281729 = 211297) B211297
theorem B281747 : Blo 187803 281747 := bstep (se 1 (by rfl) ⟨211310, by rfl⟩ : syracuseStep 281747 = 422621) B422621
theorem B642221 : Blo 187803 642221 := bstep (se 3 (by rfl) ⟨120416, by rfl⟩ : syracuseStep 642221 = 240833) B240833
theorem B281777 : Blo 187803 281777 := bstep (se 2 (by rfl) ⟨105666, by rfl⟩ : syracuseStep 281777 = 211333) B211333
theorem B281795 : Blo 187803 281795 := bstep (se 1 (by rfl) ⟨211346, by rfl⟩ : syracuseStep 281795 = 422693) B422693
theorem B281825 : Blo 187803 281825 := bstep (se 2 (by rfl) ⟨105684, by rfl⟩ : syracuseStep 281825 = 211369) B211369
theorem B642275 : Blo 187803 642275 := bstep (se 1 (by rfl) ⟨481706, by rfl⟩ : syracuseStep 642275 = 963413) B963413
theorem B543971 : Blo 187803 543971 := bstep (se 1 (by rfl) ⟨407978, by rfl⟩ : syracuseStep 543971 = 815957) B815957
theorem B281843 : Blo 187803 281843 := bstep (se 1 (by rfl) ⟨211382, by rfl⟩ : syracuseStep 281843 = 422765) B422765
theorem B281873 : Blo 187803 281873 := bstep (se 2 (by rfl) ⟨105702, by rfl⟩ : syracuseStep 281873 = 211405) B211405
theorem B281891 : Blo 187803 281891 := bstep (se 1 (by rfl) ⟨211418, by rfl⟩ : syracuseStep 281891 = 422837) B422837
theorem B281921 : Blo 187803 281921 := bstep (se 2 (by rfl) ⟨105720, by rfl⟩ : syracuseStep 281921 = 211441) B211441
theorem B576845 : Blo 187803 576845 := bstep (se 3 (by rfl) ⟨108158, by rfl⟩ : syracuseStep 576845 = 216317) B216317
theorem B281939 : Blo 187803 281939 := bstep (se 1 (by rfl) ⟨211454, by rfl⟩ : syracuseStep 281939 = 422909) B422909
theorem B511331 : Blo 187803 511331 := bstep (se 1 (by rfl) ⟨383498, by rfl⟩ : syracuseStep 511331 = 766997) B766997
theorem B281969 : Blo 187803 281969 := bstep (se 2 (by rfl) ⟨105738, by rfl⟩ : syracuseStep 281969 = 211477) B211477
theorem B281987 : Blo 187803 281987 := bstep (se 1 (by rfl) ⟨211490, by rfl⟩ : syracuseStep 281987 = 422981) B422981
theorem B282017 : Blo 187803 282017 := bstep (se 2 (by rfl) ⟨105756, by rfl⟩ : syracuseStep 282017 = 211513) B211513
theorem B609713 : Blo 187803 609713 := bstep (se 2 (by rfl) ⟨228642, by rfl⟩ : syracuseStep 609713 = 457285) B457285
theorem B282035 : Blo 187803 282035 := bstep (se 1 (by rfl) ⟨211526, by rfl⟩ : syracuseStep 282035 = 423053) B423053
theorem B282065 : Blo 187803 282065 := bstep (se 2 (by rfl) ⟨105774, by rfl⟩ : syracuseStep 282065 = 211549) B211549
theorem B282083 : Blo 187803 282083 := bstep (se 1 (by rfl) ⟨211562, by rfl⟩ : syracuseStep 282083 = 423125) B423125
theorem B609763 : Blo 187803 609763 := bstep (se 1 (by rfl) ⟨457322, by rfl⟩ : syracuseStep 609763 = 914645) B914645
theorem B642545 : Blo 187803 642545 := bstep (se 2 (by rfl) ⟨240954, by rfl⟩ : syracuseStep 642545 = 481909) B481909
theorem B282113 : Blo 187803 282113 := bstep (se 2 (by rfl) ⟨105792, by rfl⟩ : syracuseStep 282113 = 211585) B211585
theorem B282131 : Blo 187803 282131 := bstep (se 1 (by rfl) ⟨211598, by rfl⟩ : syracuseStep 282131 = 423197) B423197
theorem B282161 : Blo 187803 282161 := bstep (se 2 (by rfl) ⟨105810, by rfl⟩ : syracuseStep 282161 = 211621) B211621
theorem B282179 : Blo 187803 282179 := bstep (se 1 (by rfl) ⟨211634, by rfl⟩ : syracuseStep 282179 = 423269) B423269
theorem B577091 : Blo 187803 577091 := bstep (se 1 (by rfl) ⟨432818, by rfl⟩ : syracuseStep 577091 = 865637) B865637
theorem B282209 : Blo 187803 282209 := bstep (se 2 (by rfl) ⟨105828, by rfl⟩ : syracuseStep 282209 = 211657) B211657
theorem B282227 : Blo 187803 282227 := bstep (se 1 (by rfl) ⟨211670, by rfl⟩ : syracuseStep 282227 = 423341) B423341
theorem B282257 : Blo 187803 282257 := bstep (se 2 (by rfl) ⟨105846, by rfl⟩ : syracuseStep 282257 = 211693) B211693
theorem B282275 : Blo 187803 282275 := bstep (se 1 (by rfl) ⟨211706, by rfl⟩ : syracuseStep 282275 = 423413) B423413
theorem B282305 : Blo 187803 282305 := bstep (se 2 (by rfl) ⟨105864, by rfl⟩ : syracuseStep 282305 = 211729) B211729
theorem B282323 : Blo 187803 282323 := bstep (se 1 (by rfl) ⟨211742, by rfl⟩ : syracuseStep 282323 = 423485) B423485
theorem B282353 : Blo 187803 282353 := bstep (se 2 (by rfl) ⟨105882, by rfl⟩ : syracuseStep 282353 = 211765) B211765
theorem B282371 : Blo 187803 282371 := bstep (se 1 (by rfl) ⟨211778, by rfl⟩ : syracuseStep 282371 = 423557) B423557
theorem B478993 : Blo 187803 478993 := bstep (se 2 (by rfl) ⟨179622, by rfl⟩ : syracuseStep 478993 = 359245) B359245
theorem B282401 : Blo 187803 282401 := bstep (se 2 (by rfl) ⟨105900, by rfl⟩ : syracuseStep 282401 = 211801) B211801
theorem B282419 : Blo 187803 282419 := bstep (se 1 (by rfl) ⟨211814, by rfl⟩ : syracuseStep 282419 = 423629) B423629
theorem B282449 : Blo 187803 282449 := bstep (se 2 (by rfl) ⟨105918, by rfl⟩ : syracuseStep 282449 = 211837) B211837
theorem B282467 : Blo 187803 282467 := bstep (se 1 (by rfl) ⟨211850, by rfl⟩ : syracuseStep 282467 = 423701) B423701
theorem B282497 : Blo 187803 282497 := bstep (se 2 (by rfl) ⟨105936, by rfl⟩ : syracuseStep 282497 = 211873) B211873
theorem B282515 : Blo 187803 282515 := bstep (se 1 (by rfl) ⟨211886, by rfl⟩ : syracuseStep 282515 = 423773) B423773
theorem B282545 : Blo 187803 282545 := bstep (se 2 (by rfl) ⟨105954, by rfl⟩ : syracuseStep 282545 = 211909) B211909
theorem B282563 : Blo 187803 282563 := bstep (se 1 (by rfl) ⟨211922, by rfl⟩ : syracuseStep 282563 = 423845) B423845
theorem B577489 : Blo 187803 577489 := bstep (se 2 (by rfl) ⟨216558, by rfl⟩ : syracuseStep 577489 = 433117) B433117
theorem B282593 : Blo 187803 282593 := bstep (se 2 (by rfl) ⟨105972, by rfl⟩ : syracuseStep 282593 = 211945) B211945
theorem B282611 : Blo 187803 282611 := bstep (se 1 (by rfl) ⟨211958, by rfl⟩ : syracuseStep 282611 = 423917) B423917
theorem B643085 : Blo 187803 643085 := bstep (se 3 (by rfl) ⟨120578, by rfl⟩ : syracuseStep 643085 = 241157) B241157
theorem B282641 : Blo 187803 282641 := bstep (se 2 (by rfl) ⟨105990, by rfl⟩ : syracuseStep 282641 = 211981) B211981
theorem B282659 : Blo 187803 282659 := bstep (se 1 (by rfl) ⟨211994, by rfl⟩ : syracuseStep 282659 = 423989) B423989
theorem B479267 : Blo 187803 479267 := bstep (se 1 (by rfl) ⟨359450, by rfl⟩ : syracuseStep 479267 = 718901) B718901
theorem B282689 : Blo 187803 282689 := bstep (se 2 (by rfl) ⟨106008, by rfl⟩ : syracuseStep 282689 = 212017) B212017
theorem B643139 : Blo 187803 643139 := bstep (se 1 (by rfl) ⟨482354, by rfl⟩ : syracuseStep 643139 = 964709) B964709
theorem B282707 : Blo 187803 282707 := bstep (se 1 (by rfl) ⟨212030, by rfl⟩ : syracuseStep 282707 = 424061) B424061
theorem B282737 : Blo 187803 282737 := bstep (se 2 (by rfl) ⟨106026, by rfl⟩ : syracuseStep 282737 = 212053) B212053
theorem B1101937 : Blo 187803 1101937 := bstep (se 2 (by rfl) ⟨413226, by rfl⟩ : syracuseStep 1101937 = 826453) B826453
theorem B970865 : Blo 187803 970865 := bstep (se 2 (by rfl) ⟨364074, by rfl⟩ : syracuseStep 970865 = 728149) B728149
theorem B282755 : Blo 187803 282755 := bstep (se 1 (by rfl) ⟨212066, by rfl⟩ : syracuseStep 282755 = 424133) B424133
theorem B282785 : Blo 187803 282785 := bstep (se 2 (by rfl) ⟨106044, by rfl⟩ : syracuseStep 282785 = 212089) B212089
theorem B282803 : Blo 187803 282803 := bstep (se 1 (by rfl) ⟨212102, by rfl⟩ : syracuseStep 282803 = 424205) B424205
theorem B282833 : Blo 187803 282833 := bstep (se 2 (by rfl) ⟨106062, by rfl⟩ : syracuseStep 282833 = 212125) B212125
theorem B282851 : Blo 187803 282851 := bstep (se 1 (by rfl) ⟨212138, by rfl⟩ : syracuseStep 282851 = 424277) B424277
theorem B479459 : Blo 187803 479459 := bstep (se 1 (by rfl) ⟨359594, by rfl⟩ : syracuseStep 479459 = 719189) B719189
theorem B282881 : Blo 187803 282881 := bstep (se 2 (by rfl) ⟨106080, by rfl⟩ : syracuseStep 282881 = 212161) B212161
theorem B282899 : Blo 187803 282899 := bstep (se 1 (by rfl) ⟨212174, by rfl⟩ : syracuseStep 282899 = 424349) B424349
theorem B282929 : Blo 187803 282929 := bstep (se 2 (by rfl) ⟨106098, by rfl⟩ : syracuseStep 282929 = 212197) B212197
theorem B282947 : Blo 187803 282947 := bstep (se 1 (by rfl) ⟨212210, by rfl⟩ : syracuseStep 282947 = 424421) B424421
theorem B643409 : Blo 187803 643409 := bstep (se 2 (by rfl) ⟨241278, by rfl⟩ : syracuseStep 643409 = 482557) B482557
theorem B282977 : Blo 187803 282977 := bstep (se 2 (by rfl) ⟨106116, by rfl⟩ : syracuseStep 282977 = 212233) B212233
theorem B282995 : Blo 187803 282995 := bstep (se 1 (by rfl) ⟨212246, by rfl⟩ : syracuseStep 282995 = 424493) B424493
theorem B283025 : Blo 187803 283025 := bstep (se 2 (by rfl) ⟨106134, by rfl⟩ : syracuseStep 283025 = 212269) B212269
theorem B283043 : Blo 187803 283043 := bstep (se 1 (by rfl) ⟨212282, by rfl⟩ : syracuseStep 283043 = 424565) B424565
theorem B545201 : Blo 187803 545201 := bstep (se 2 (by rfl) ⟨204450, by rfl⟩ : syracuseStep 545201 = 408901) B408901
theorem B283073 : Blo 187803 283073 := bstep (se 2 (by rfl) ⟨106152, by rfl⟩ : syracuseStep 283073 = 212305) B212305
theorem B1036741 : Blo 187803 1036741 := bstep (se 4 (by rfl) ⟨97194, by rfl⟩ : syracuseStep 1036741 = 194389) B194389
theorem B283091 : Blo 187803 283091 := bstep (se 1 (by rfl) ⟨212318, by rfl⟩ : syracuseStep 283091 = 424637) B424637
theorem B283121 : Blo 187803 283121 := bstep (se 2 (by rfl) ⟨106170, by rfl⟩ : syracuseStep 283121 = 212341) B212341
theorem B283139 : Blo 187803 283139 := bstep (se 1 (by rfl) ⟨212354, by rfl⟩ : syracuseStep 283139 = 424709) B424709
theorem B283169 : Blo 187803 283169 := bstep (se 2 (by rfl) ⟨106188, by rfl⟩ : syracuseStep 283169 = 212377) B212377
theorem B283187 : Blo 187803 283187 := bstep (se 1 (by rfl) ⟨212390, by rfl⟩ : syracuseStep 283187 = 424781) B424781
theorem B283217 : Blo 187803 283217 := bstep (se 2 (by rfl) ⟨106206, by rfl⟩ : syracuseStep 283217 = 212413) B212413
theorem B283235 : Blo 187803 283235 := bstep (se 1 (by rfl) ⟨212426, by rfl⟩ : syracuseStep 283235 = 424853) B424853
theorem B643697 : Blo 187803 643697 := bstep (se 2 (by rfl) ⟨241386, by rfl⟩ : syracuseStep 643697 = 482773) B482773
theorem B283265 : Blo 187803 283265 := bstep (se 2 (by rfl) ⟨106224, by rfl⟩ : syracuseStep 283265 = 212449) B212449
theorem B283283 : Blo 187803 283283 := bstep (se 1 (by rfl) ⟨212462, by rfl⟩ : syracuseStep 283283 = 424925) B424925
theorem B283313 : Blo 187803 283313 := bstep (se 2 (by rfl) ⟨106242, by rfl⟩ : syracuseStep 283313 = 212485) B212485
theorem B610993 : Blo 187803 610993 := bstep (se 2 (by rfl) ⟨229122, by rfl⟩ : syracuseStep 610993 = 458245) B458245
theorem B283331 : Blo 187803 283331 := bstep (se 1 (by rfl) ⟨212498, by rfl⟩ : syracuseStep 283331 = 424997) B424997
theorem B283361 : Blo 187803 283361 := bstep (se 2 (by rfl) ⟨106260, by rfl⟩ : syracuseStep 283361 = 212521) B212521
theorem B283379 : Blo 187803 283379 := bstep (se 1 (by rfl) ⟨212534, by rfl⟩ : syracuseStep 283379 = 425069) B425069
theorem B283409 : Blo 187803 283409 := bstep (se 2 (by rfl) ⟨106278, by rfl⟩ : syracuseStep 283409 = 212557) B212557
theorem B283427 : Blo 187803 283427 := bstep (se 1 (by rfl) ⟨212570, by rfl⟩ : syracuseStep 283427 = 425141) B425141
theorem B283457 : Blo 187803 283457 := bstep (se 2 (by rfl) ⟨106296, by rfl⟩ : syracuseStep 283457 = 212593) B212593
theorem B1528645 : Blo 187803 1528645 := bstep (se 4 (by rfl) ⟨143310, by rfl⟩ : syracuseStep 1528645 = 286621) B286621
theorem B283475 : Blo 187803 283475 := bstep (se 1 (by rfl) ⟨212606, by rfl⟩ : syracuseStep 283475 = 425213) B425213
theorem B643949 : Blo 187803 643949 := bstep (se 3 (by rfl) ⟨120740, by rfl⟩ : syracuseStep 643949 = 241481) B241481
theorem B283505 : Blo 187803 283505 := bstep (se 2 (by rfl) ⟨106314, by rfl⟩ : syracuseStep 283505 = 212629) B212629
theorem B283523 : Blo 187803 283523 := bstep (se 1 (by rfl) ⟨212642, by rfl⟩ : syracuseStep 283523 = 425285) B425285
theorem B283553 : Blo 187803 283553 := bstep (se 2 (by rfl) ⟨106332, by rfl⟩ : syracuseStep 283553 = 212665) B212665
theorem B644003 : Blo 187803 644003 := bstep (se 1 (by rfl) ⟨483002, by rfl⟩ : syracuseStep 644003 = 966005) B966005
theorem B283571 : Blo 187803 283571 := bstep (se 1 (by rfl) ⟨212678, by rfl⟩ : syracuseStep 283571 = 425357) B425357
theorem B283601 : Blo 187803 283601 := bstep (se 2 (by rfl) ⟨106350, by rfl⟩ : syracuseStep 283601 = 212701) B212701
theorem B283619 : Blo 187803 283619 := bstep (se 1 (by rfl) ⟨212714, by rfl⟩ : syracuseStep 283619 = 425429) B425429
theorem B283649 : Blo 187803 283649 := bstep (se 2 (by rfl) ⟨106368, by rfl⟩ : syracuseStep 283649 = 212737) B212737
theorem B283667 : Blo 187803 283667 := bstep (se 1 (by rfl) ⟨212750, by rfl⟩ : syracuseStep 283667 = 425501) B425501
theorem B283697 : Blo 187803 283697 := bstep (se 2 (by rfl) ⟨106386, by rfl⟩ : syracuseStep 283697 = 212773) B212773
theorem B283715 : Blo 187803 283715 := bstep (se 1 (by rfl) ⟨212786, by rfl⟩ : syracuseStep 283715 = 425573) B425573
theorem B283745 : Blo 187803 283745 := bstep (se 2 (by rfl) ⟨106404, by rfl⟩ : syracuseStep 283745 = 212809) B212809
theorem B283763 : Blo 187803 283763 := bstep (se 1 (by rfl) ⟨212822, by rfl⟩ : syracuseStep 283763 = 425645) B425645
theorem B283793 : Blo 187803 283793 := bstep (se 2 (by rfl) ⟨106422, by rfl⟩ : syracuseStep 283793 = 212845) B212845
theorem B480401 : Blo 187803 480401 := bstep (se 2 (by rfl) ⟨180150, by rfl⟩ : syracuseStep 480401 = 360301) B360301
theorem B283811 : Blo 187803 283811 := bstep (se 1 (by rfl) ⟨212858, by rfl⟩ : syracuseStep 283811 = 425717) B425717
theorem B644273 : Blo 187803 644273 := bstep (se 2 (by rfl) ⟨241602, by rfl⟩ : syracuseStep 644273 = 483205) B483205
theorem B283841 : Blo 187803 283841 := bstep (se 2 (by rfl) ⟨106440, by rfl⟩ : syracuseStep 283841 = 212881) B212881
theorem B480451 : Blo 187803 480451 := bstep (se 1 (by rfl) ⟨360338, by rfl⟩ : syracuseStep 480451 = 720677) B720677
theorem B283859 : Blo 187803 283859 := bstep (se 1 (by rfl) ⟨212894, by rfl⟩ : syracuseStep 283859 = 425789) B425789
theorem B677105 : Blo 187803 677105 := bstep (se 2 (by rfl) ⟨253914, by rfl⟩ : syracuseStep 677105 = 507829) B507829
theorem B283889 : Blo 187803 283889 := bstep (se 2 (by rfl) ⟨106458, by rfl⟩ : syracuseStep 283889 = 212917) B212917
theorem B283907 : Blo 187803 283907 := bstep (se 1 (by rfl) ⟨212930, by rfl⟩ : syracuseStep 283907 = 425861) B425861
theorem B283937 : Blo 187803 283937 := bstep (se 2 (by rfl) ⟨106476, by rfl⟩ : syracuseStep 283937 = 212953) B212953
theorem B283955 : Blo 187803 283955 := bstep (se 1 (by rfl) ⟨212966, by rfl⟩ : syracuseStep 283955 = 425933) B425933
theorem B578897 : Blo 187803 578897 := bstep (se 2 (by rfl) ⟨217086, by rfl⟩ : syracuseStep 578897 = 434173) B434173
theorem B283985 : Blo 187803 283985 := bstep (se 2 (by rfl) ⟨106494, by rfl⟩ : syracuseStep 283985 = 212989) B212989
theorem B480593 : Blo 187803 480593 := bstep (se 2 (by rfl) ⟨180222, by rfl⟩ : syracuseStep 480593 = 360445) B360445
theorem B284003 : Blo 187803 284003 := bstep (se 1 (by rfl) ⟨213002, by rfl⟩ : syracuseStep 284003 = 426005) B426005
theorem B284033 : Blo 187803 284033 := bstep (se 2 (by rfl) ⟨106512, by rfl⟩ : syracuseStep 284033 = 213025) B213025
theorem B284051 : Blo 187803 284051 := bstep (se 1 (by rfl) ⟨213038, by rfl⟩ : syracuseStep 284051 = 426077) B426077
theorem B284081 : Blo 187803 284081 := bstep (se 2 (by rfl) ⟨106530, by rfl⟩ : syracuseStep 284081 = 213061) B213061
theorem B284099 : Blo 187803 284099 := bstep (se 1 (by rfl) ⟨213074, by rfl⟩ : syracuseStep 284099 = 426149) B426149
theorem B284129 : Blo 187803 284129 := bstep (se 2 (by rfl) ⟨106548, by rfl⟩ : syracuseStep 284129 = 213097) B213097
theorem B284147 : Blo 187803 284147 := bstep (se 1 (by rfl) ⟨213110, by rfl⟩ : syracuseStep 284147 = 426221) B426221
theorem B284177 : Blo 187803 284177 := bstep (se 2 (by rfl) ⟨106566, by rfl⟩ : syracuseStep 284177 = 213133) B213133
theorem B284195 : Blo 187803 284195 := bstep (se 1 (by rfl) ⟨213146, by rfl⟩ : syracuseStep 284195 = 426293) B426293
theorem B316993 : Blo 187803 316993 := bstep (se 2 (by rfl) ⟨118872, by rfl⟩ : syracuseStep 316993 = 237745) B237745
theorem B284225 : Blo 187803 284225 := bstep (se 2 (by rfl) ⟨106584, by rfl⟩ : syracuseStep 284225 = 213169) B213169
theorem B284243 : Blo 187803 284243 := bstep (se 1 (by rfl) ⟨213182, by rfl⟩ : syracuseStep 284243 = 426365) B426365
theorem B317027 : Blo 187803 317027 := bstep (se 1 (by rfl) ⟨237770, by rfl⟩ : syracuseStep 317027 = 475541) B475541
theorem B284273 : Blo 187803 284273 := bstep (se 2 (by rfl) ⟨106602, by rfl⟩ : syracuseStep 284273 = 213205) B213205
theorem B284291 : Blo 187803 284291 := bstep (se 1 (by rfl) ⟨213218, by rfl⟩ : syracuseStep 284291 = 426437) B426437
theorem B284321 : Blo 187803 284321 := bstep (se 2 (by rfl) ⟨106620, by rfl⟩ : syracuseStep 284321 = 213241) B213241
theorem B284339 : Blo 187803 284339 := bstep (se 1 (by rfl) ⟨213254, by rfl⟩ : syracuseStep 284339 = 426509) B426509
theorem B644813 : Blo 187803 644813 := bstep (se 3 (by rfl) ⟨120902, by rfl⟩ : syracuseStep 644813 = 241805) B241805
theorem B284369 : Blo 187803 284369 := bstep (se 2 (by rfl) ⟨106638, by rfl⟩ : syracuseStep 284369 = 213277) B213277
theorem B317155 : Blo 187803 317155 := bstep (se 1 (by rfl) ⟨237866, by rfl⟩ : syracuseStep 317155 = 475733) B475733
theorem B284387 : Blo 187803 284387 := bstep (se 1 (by rfl) ⟨213290, by rfl⟩ : syracuseStep 284387 = 426581) B426581
theorem B284417 : Blo 187803 284417 := bstep (se 2 (by rfl) ⟨106656, by rfl⟩ : syracuseStep 284417 = 213313) B213313
theorem B644867 : Blo 187803 644867 := bstep (se 1 (by rfl) ⟨483650, by rfl⟩ : syracuseStep 644867 = 967301) B967301
theorem B284435 : Blo 187803 284435 := bstep (se 1 (by rfl) ⟨213326, by rfl⟩ : syracuseStep 284435 = 426653) B426653
theorem B284465 : Blo 187803 284465 := bstep (se 2 (by rfl) ⟨106674, by rfl⟩ : syracuseStep 284465 = 213349) B213349
theorem B284483 : Blo 187803 284483 := bstep (se 1 (by rfl) ⟨213362, by rfl⟩ : syracuseStep 284483 = 426725) B426725
theorem B612173 : Blo 187803 612173 := bstep (se 3 (by rfl) ⟨114782, by rfl⟩ : syracuseStep 612173 = 229565) B229565
theorem B284513 : Blo 187803 284513 := bstep (se 2 (by rfl) ⟨106692, by rfl⟩ : syracuseStep 284513 = 213385) B213385
theorem B317297 : Blo 187803 317297 := bstep (se 2 (by rfl) ⟨118986, by rfl⟩ : syracuseStep 317297 = 237973) B237973
theorem B284531 : Blo 187803 284531 := bstep (se 1 (by rfl) ⟨213398, by rfl⟩ : syracuseStep 284531 = 426797) B426797
theorem B284561 : Blo 187803 284561 := bstep (se 2 (by rfl) ⟨106710, by rfl⟩ : syracuseStep 284561 = 213421) B213421
theorem B284579 : Blo 187803 284579 := bstep (se 1 (by rfl) ⟨213434, by rfl⟩ : syracuseStep 284579 = 426869) B426869
theorem B284609 : Blo 187803 284609 := bstep (se 2 (by rfl) ⟨106728, by rfl⟩ : syracuseStep 284609 = 213457) B213457
theorem B284627 : Blo 187803 284627 := bstep (se 1 (by rfl) ⟨213470, by rfl⟩ : syracuseStep 284627 = 426941) B426941
theorem B317425 : Blo 187803 317425 := bstep (se 2 (by rfl) ⟨119034, by rfl⟩ : syracuseStep 317425 = 238069) B238069
theorem B284657 : Blo 187803 284657 := bstep (se 2 (by rfl) ⟨106746, by rfl⟩ : syracuseStep 284657 = 213493) B213493
theorem B284675 : Blo 187803 284675 := bstep (se 1 (by rfl) ⟨213506, by rfl⟩ : syracuseStep 284675 = 427013) B427013
theorem B645137 : Blo 187803 645137 := bstep (se 2 (by rfl) ⟨241926, by rfl⟩ : syracuseStep 645137 = 483853) B483853
theorem B317459 : Blo 187803 317459 := bstep (se 1 (by rfl) ⟨238094, by rfl⟩ : syracuseStep 317459 = 476189) B476189
theorem B284705 : Blo 187803 284705 := bstep (se 2 (by rfl) ⟨106764, by rfl⟩ : syracuseStep 284705 = 213529) B213529
theorem B284723 : Blo 187803 284723 := bstep (se 1 (by rfl) ⟨213542, by rfl⟩ : syracuseStep 284723 = 427085) B427085
theorem B284753 : Blo 187803 284753 := bstep (se 2 (by rfl) ⟨106782, by rfl⟩ : syracuseStep 284753 = 213565) B213565
theorem B284771 : Blo 187803 284771 := bstep (se 1 (by rfl) ⟨213578, by rfl⟩ : syracuseStep 284771 = 427157) B427157
theorem B284801 : Blo 187803 284801 := bstep (se 2 (by rfl) ⟨106800, by rfl⟩ : syracuseStep 284801 = 213601) B213601
theorem B317587 : Blo 187803 317587 := bstep (se 1 (by rfl) ⟨238190, by rfl⟩ : syracuseStep 317587 = 476381) B476381
theorem B284819 : Blo 187803 284819 := bstep (se 1 (by rfl) ⟨213614, by rfl⟩ : syracuseStep 284819 = 427229) B427229
theorem B284849 : Blo 187803 284849 := bstep (se 2 (by rfl) ⟨106818, by rfl⟩ : syracuseStep 284849 = 213637) B213637
theorem B284867 : Blo 187803 284867 := bstep (se 1 (by rfl) ⟨213650, by rfl⟩ : syracuseStep 284867 = 427301) B427301
theorem B284897 : Blo 187803 284897 := bstep (se 2 (by rfl) ⟨106836, by rfl⟩ : syracuseStep 284897 = 213673) B213673
theorem B284915 : Blo 187803 284915 := bstep (se 1 (by rfl) ⟨213686, by rfl⟩ : syracuseStep 284915 = 427373) B427373
theorem B284945 : Blo 187803 284945 := bstep (se 2 (by rfl) ⟨106854, by rfl⟩ : syracuseStep 284945 = 213709) B213709
theorem B317729 : Blo 187803 317729 := bstep (se 2 (by rfl) ⟨119148, by rfl⟩ : syracuseStep 317729 = 238297) B238297
theorem B284963 : Blo 187803 284963 := bstep (se 1 (by rfl) ⟨213722, by rfl⟩ : syracuseStep 284963 = 427445) B427445
theorem B481585 : Blo 187803 481585 := bstep (se 2 (by rfl) ⟨180594, by rfl⟩ : syracuseStep 481585 = 361189) B361189
theorem B317747 : Blo 187803 317747 := bstep (se 1 (by rfl) ⟨238310, by rfl⟩ : syracuseStep 317747 = 476621) B476621
theorem B284993 : Blo 187803 284993 := bstep (se 2 (by rfl) ⟨106872, by rfl⟩ : syracuseStep 284993 = 213745) B213745
theorem B285011 : Blo 187803 285011 := bstep (se 1 (by rfl) ⟨213758, by rfl⟩ : syracuseStep 285011 = 427517) B427517
theorem B285041 : Blo 187803 285041 := bstep (se 2 (by rfl) ⟨106890, by rfl⟩ : syracuseStep 285041 = 213781) B213781
theorem B285059 : Blo 187803 285059 := bstep (se 1 (by rfl) ⟨213794, by rfl⟩ : syracuseStep 285059 = 427589) B427589
theorem B317857 : Blo 187803 317857 := bstep (se 2 (by rfl) ⟨119196, by rfl⟩ : syracuseStep 317857 = 238393) B238393
theorem B285089 : Blo 187803 285089 := bstep (se 2 (by rfl) ⟨106908, by rfl⟩ : syracuseStep 285089 = 213817) B213817
theorem B285107 : Blo 187803 285107 := bstep (se 1 (by rfl) ⟨213830, by rfl⟩ : syracuseStep 285107 = 427661) B427661
theorem B317891 : Blo 187803 317891 := bstep (se 1 (by rfl) ⟨238418, by rfl⟩ : syracuseStep 317891 = 476837) B476837
theorem B285137 : Blo 187803 285137 := bstep (se 2 (by rfl) ⟨106926, by rfl⟩ : syracuseStep 285137 = 213853) B213853
theorem B285155 : Blo 187803 285155 := bstep (se 1 (by rfl) ⟨213866, by rfl⟩ : syracuseStep 285155 = 427733) B427733
theorem B285185 : Blo 187803 285185 := bstep (se 2 (by rfl) ⟨106944, by rfl⟩ : syracuseStep 285185 = 213889) B213889
theorem B285203 : Blo 187803 285203 := bstep (se 1 (by rfl) ⟨213902, by rfl⟩ : syracuseStep 285203 = 427805) B427805
theorem B645677 : Blo 187803 645677 := bstep (se 3 (by rfl) ⟨121064, by rfl⟩ : syracuseStep 645677 = 242129) B242129
theorem B285233 : Blo 187803 285233 := bstep (se 2 (by rfl) ⟨106962, by rfl⟩ : syracuseStep 285233 = 213925) B213925
theorem B318019 : Blo 187803 318019 := bstep (se 1 (by rfl) ⟨238514, by rfl⟩ : syracuseStep 318019 = 477029) B477029
theorem B285251 : Blo 187803 285251 := bstep (se 1 (by rfl) ⟨213938, by rfl⟩ : syracuseStep 285251 = 427877) B427877
theorem B481859 : Blo 187803 481859 := bstep (se 1 (by rfl) ⟨361394, by rfl⟩ : syracuseStep 481859 = 722789) B722789
theorem B285281 : Blo 187803 285281 := bstep (se 2 (by rfl) ⟨106980, by rfl⟩ : syracuseStep 285281 = 213961) B213961
theorem B645731 : Blo 187803 645731 := bstep (se 1 (by rfl) ⟨484298, by rfl⟩ : syracuseStep 645731 = 968597) B968597
theorem B809585 : Blo 187803 809585 := bstep (se 2 (by rfl) ⟨303594, by rfl⟩ : syracuseStep 809585 = 607189) B607189
theorem B285299 : Blo 187803 285299 := bstep (se 1 (by rfl) ⟨213974, by rfl⟩ : syracuseStep 285299 = 427949) B427949
theorem B2939533 : Blo 187803 2939533 := bstep (se 3 (by rfl) ⟨551162, by rfl⟩ : syracuseStep 2939533 = 1102325) B1102325
theorem B285329 : Blo 187803 285329 := bstep (se 2 (by rfl) ⟨106998, by rfl⟩ : syracuseStep 285329 = 213997) B213997
theorem B809635 : Blo 187803 809635 := bstep (se 1 (by rfl) ⟨607226, by rfl⟩ : syracuseStep 809635 = 1214453) B1214453
theorem B285347 : Blo 187803 285347 := bstep (se 1 (by rfl) ⟨214010, by rfl⟩ : syracuseStep 285347 = 428021) B428021
theorem B285377 : Blo 187803 285377 := bstep (se 2 (by rfl) ⟨107016, by rfl⟩ : syracuseStep 285377 = 214033) B214033
theorem B318161 : Blo 187803 318161 := bstep (se 2 (by rfl) ⟨119310, by rfl⟩ : syracuseStep 318161 = 238621) B238621
theorem B285395 : Blo 187803 285395 := bstep (se 1 (by rfl) ⟨214046, by rfl⟩ : syracuseStep 285395 = 428093) B428093
theorem B285425 : Blo 187803 285425 := bstep (se 2 (by rfl) ⟨107034, by rfl⟩ : syracuseStep 285425 = 214069) B214069
theorem B285443 : Blo 187803 285443 := bstep (se 1 (by rfl) ⟨214082, by rfl⟩ : syracuseStep 285443 = 428165) B428165
theorem B482051 : Blo 187803 482051 := bstep (se 1 (by rfl) ⟨361538, by rfl⟩ : syracuseStep 482051 = 723077) B723077
theorem B285473 : Blo 187803 285473 := bstep (se 2 (by rfl) ⟨107052, by rfl⟩ : syracuseStep 285473 = 214105) B214105
theorem B285491 : Blo 187803 285491 := bstep (se 1 (by rfl) ⟨214118, by rfl⟩ : syracuseStep 285491 = 428237) B428237
theorem B318289 : Blo 187803 318289 := bstep (se 2 (by rfl) ⟨119358, by rfl⟩ : syracuseStep 318289 = 238717) B238717
theorem B285521 : Blo 187803 285521 := bstep (se 2 (by rfl) ⟨107070, by rfl⟩ : syracuseStep 285521 = 214141) B214141
theorem B285539 : Blo 187803 285539 := bstep (se 1 (by rfl) ⟨214154, by rfl⟩ : syracuseStep 285539 = 428309) B428309
theorem B646001 : Blo 187803 646001 := bstep (se 2 (by rfl) ⟨242250, by rfl⟩ : syracuseStep 646001 = 484501) B484501
theorem B318323 : Blo 187803 318323 := bstep (se 1 (by rfl) ⟨238742, by rfl⟩ : syracuseStep 318323 = 477485) B477485
theorem B285569 : Blo 187803 285569 := bstep (se 2 (by rfl) ⟨107088, by rfl⟩ : syracuseStep 285569 = 214177) B214177
theorem B285587 : Blo 187803 285587 := bstep (se 1 (by rfl) ⟨214190, by rfl⟩ : syracuseStep 285587 = 428381) B428381
theorem B285617 : Blo 187803 285617 := bstep (se 2 (by rfl) ⟨107106, by rfl⟩ : syracuseStep 285617 = 214213) B214213
theorem B285635 : Blo 187803 285635 := bstep (se 1 (by rfl) ⟨214226, by rfl⟩ : syracuseStep 285635 = 428453) B428453
theorem B285665 : Blo 187803 285665 := bstep (se 2 (by rfl) ⟨107124, by rfl⟩ : syracuseStep 285665 = 214249) B214249
theorem B318451 : Blo 187803 318451 := bstep (se 1 (by rfl) ⟨238838, by rfl⟩ : syracuseStep 318451 = 477677) B477677
theorem B285683 : Blo 187803 285683 := bstep (se 1 (by rfl) ⟨214262, by rfl⟩ : syracuseStep 285683 = 428525) B428525
theorem B285713 : Blo 187803 285713 := bstep (se 2 (by rfl) ⟨107142, by rfl⟩ : syracuseStep 285713 = 214285) B214285
theorem B285731 : Blo 187803 285731 := bstep (se 1 (by rfl) ⟨214298, by rfl⟩ : syracuseStep 285731 = 428597) B428597
theorem B285761 : Blo 187803 285761 := bstep (se 2 (by rfl) ⟨107160, by rfl⟩ : syracuseStep 285761 = 214321) B214321
theorem B285779 : Blo 187803 285779 := bstep (se 1 (by rfl) ⟨214334, by rfl⟩ : syracuseStep 285779 = 428669) B428669
theorem B285809 : Blo 187803 285809 := bstep (se 2 (by rfl) ⟨107178, by rfl⟩ : syracuseStep 285809 = 214357) B214357
theorem B318593 : Blo 187803 318593 := bstep (se 2 (by rfl) ⟨119472, by rfl⟩ : syracuseStep 318593 = 238945) B238945
theorem B285827 : Blo 187803 285827 := bstep (se 1 (by rfl) ⟨214370, by rfl⟩ : syracuseStep 285827 = 428741) B428741
theorem B285857 : Blo 187803 285857 := bstep (se 2 (by rfl) ⟨107196, by rfl⟩ : syracuseStep 285857 = 214393) B214393
theorem B285875 : Blo 187803 285875 := bstep (se 1 (by rfl) ⟨214406, by rfl⟩ : syracuseStep 285875 = 428813) B428813
theorem B285905 : Blo 187803 285905 := bstep (se 2 (by rfl) ⟨107214, by rfl⟩ : syracuseStep 285905 = 214429) B214429
theorem B285923 : Blo 187803 285923 := bstep (se 1 (by rfl) ⟨214442, by rfl⟩ : syracuseStep 285923 = 428885) B428885
theorem B318721 : Blo 187803 318721 := bstep (se 2 (by rfl) ⟨119520, by rfl⟩ : syracuseStep 318721 = 239041) B239041
theorem B285953 : Blo 187803 285953 := bstep (se 2 (by rfl) ⟨107232, by rfl⟩ : syracuseStep 285953 = 214465) B214465
theorem B285971 : Blo 187803 285971 := bstep (se 1 (by rfl) ⟨214478, by rfl⟩ : syracuseStep 285971 = 428957) B428957
theorem B318755 : Blo 187803 318755 := bstep (se 1 (by rfl) ⟨239066, by rfl⟩ : syracuseStep 318755 = 478133) B478133
theorem B286001 : Blo 187803 286001 := bstep (se 2 (by rfl) ⟨107250, by rfl⟩ : syracuseStep 286001 = 214501) B214501
theorem B286019 : Blo 187803 286019 := bstep (se 1 (by rfl) ⟨214514, by rfl⟩ : syracuseStep 286019 = 429029) B429029
theorem B286049 : Blo 187803 286049 := bstep (se 2 (by rfl) ⟨107268, by rfl⟩ : syracuseStep 286049 = 214537) B214537
theorem B286067 : Blo 187803 286067 := bstep (se 1 (by rfl) ⟨214550, by rfl⟩ : syracuseStep 286067 = 429101) B429101
theorem B646541 : Blo 187803 646541 := bstep (se 3 (by rfl) ⟨121226, by rfl⟩ : syracuseStep 646541 = 242453) B242453
theorem B286097 : Blo 187803 286097 := bstep (se 2 (by rfl) ⟨107286, by rfl⟩ : syracuseStep 286097 = 214573) B214573
theorem B187811 : Blo 187803 187811 := bstep (se 1 (by rfl) ⟨140858, by rfl⟩ : syracuseStep 187811 = 281717) B281717
theorem B318883 : Blo 187803 318883 := bstep (se 1 (by rfl) ⟨239162, by rfl⟩ : syracuseStep 318883 = 478325) B478325
theorem B286115 : Blo 187803 286115 := bstep (se 1 (by rfl) ⟨214586, by rfl⟩ : syracuseStep 286115 = 429173) B429173
theorem B187827 : Blo 187803 187827 := bstep (se 1 (by rfl) ⟨140870, by rfl⟩ : syracuseStep 187827 = 281741) B281741
theorem B286145 : Blo 187803 286145 := bstep (se 2 (by rfl) ⟨107304, by rfl⟩ : syracuseStep 286145 = 214609) B214609
theorem B187843 : Blo 187803 187843 := bstep (se 1 (by rfl) ⟨140882, by rfl⟩ : syracuseStep 187843 = 281765) B281765
theorem B646595 : Blo 187803 646595 := bstep (se 1 (by rfl) ⟨484946, by rfl⟩ : syracuseStep 646595 = 969893) B969893
theorem B187859 : Blo 187803 187859 := bstep (se 1 (by rfl) ⟨140894, by rfl⟩ : syracuseStep 187859 = 281789) B281789
theorem B286163 : Blo 187803 286163 := bstep (se 1 (by rfl) ⟨214622, by rfl⟩ : syracuseStep 286163 = 429245) B429245
theorem B187875 : Blo 187803 187875 := bstep (se 1 (by rfl) ⟨140906, by rfl⟩ : syracuseStep 187875 = 281813) B281813
theorem B286193 : Blo 187803 286193 := bstep (se 2 (by rfl) ⟨107322, by rfl⟩ : syracuseStep 286193 = 214645) B214645
theorem B187891 : Blo 187803 187891 := bstep (se 1 (by rfl) ⟨140918, by rfl⟩ : syracuseStep 187891 = 281837) B281837
theorem B187907 : Blo 187803 187907 := bstep (se 1 (by rfl) ⟨140930, by rfl⟩ : syracuseStep 187907 = 281861) B281861
theorem B286211 : Blo 187803 286211 := bstep (se 1 (by rfl) ⟨214658, by rfl⟩ : syracuseStep 286211 = 429317) B429317
theorem B187923 : Blo 187803 187923 := bstep (se 1 (by rfl) ⟨140942, by rfl⟩ : syracuseStep 187923 = 281885) B281885
theorem B286241 : Blo 187803 286241 := bstep (se 2 (by rfl) ⟨107340, by rfl⟩ : syracuseStep 286241 = 214681) B214681
theorem B187939 : Blo 187803 187939 := bstep (se 1 (by rfl) ⟨140954, by rfl⟩ : syracuseStep 187939 = 281909) B281909
theorem B319025 : Blo 187803 319025 := bstep (se 2 (by rfl) ⟨119634, by rfl⟩ : syracuseStep 319025 = 239269) B239269
theorem B187955 : Blo 187803 187955 := bstep (se 1 (by rfl) ⟨140966, by rfl⟩ : syracuseStep 187955 = 281933) B281933
theorem B286259 : Blo 187803 286259 := bstep (se 1 (by rfl) ⟨214694, by rfl⟩ : syracuseStep 286259 = 429389) B429389
theorem B187971 : Blo 187803 187971 := bstep (se 1 (by rfl) ⟨140978, by rfl⟩ : syracuseStep 187971 = 281957) B281957
theorem B613955 : Blo 187803 613955 := bstep (se 1 (by rfl) ⟨460466, by rfl⟩ : syracuseStep 613955 = 920933) B920933
theorem B286289 : Blo 187803 286289 := bstep (se 2 (by rfl) ⟨107358, by rfl⟩ : syracuseStep 286289 = 214717) B214717
theorem B187987 : Blo 187803 187987 := bstep (se 1 (by rfl) ⟨140990, by rfl⟩ : syracuseStep 187987 = 281981) B281981
theorem B188003 : Blo 187803 188003 := bstep (se 1 (by rfl) ⟨141002, by rfl⟩ : syracuseStep 188003 = 282005) B282005
theorem B286307 : Blo 187803 286307 := bstep (se 1 (by rfl) ⟨214730, by rfl⟩ : syracuseStep 286307 = 429461) B429461
theorem B188019 : Blo 187803 188019 := bstep (se 1 (by rfl) ⟨141014, by rfl⟩ : syracuseStep 188019 = 282029) B282029
theorem B286337 : Blo 187803 286337 := bstep (se 2 (by rfl) ⟨107376, by rfl⟩ : syracuseStep 286337 = 214753) B214753
theorem B188035 : Blo 187803 188035 := bstep (se 1 (by rfl) ⟨141026, by rfl⟩ : syracuseStep 188035 = 282053) B282053
theorem B188051 : Blo 187803 188051 := bstep (se 1 (by rfl) ⟨141038, by rfl⟩ : syracuseStep 188051 = 282077) B282077
theorem B286355 : Blo 187803 286355 := bstep (se 1 (by rfl) ⟨214766, by rfl⟩ : syracuseStep 286355 = 429533) B429533
theorem B188067 : Blo 187803 188067 := bstep (se 1 (by rfl) ⟨141050, by rfl⟩ : syracuseStep 188067 = 282101) B282101
theorem B319153 : Blo 187803 319153 := bstep (se 2 (by rfl) ⟨119682, by rfl⟩ : syracuseStep 319153 = 239365) B239365
theorem B482993 : Blo 187803 482993 := bstep (se 2 (by rfl) ⟨181122, by rfl⟩ : syracuseStep 482993 = 362245) B362245
theorem B188083 : Blo 187803 188083 := bstep (se 1 (by rfl) ⟨141062, by rfl⟩ : syracuseStep 188083 = 282125) B282125
theorem B286385 : Blo 187803 286385 := bstep (se 2 (by rfl) ⟨107394, by rfl⟩ : syracuseStep 286385 = 214789) B214789
theorem B188099 : Blo 187803 188099 := bstep (se 1 (by rfl) ⟨141074, by rfl⟩ : syracuseStep 188099 = 282149) B282149
theorem B286403 : Blo 187803 286403 := bstep (se 1 (by rfl) ⟨214802, by rfl⟩ : syracuseStep 286403 = 429605) B429605
theorem B188115 : Blo 187803 188115 := bstep (se 1 (by rfl) ⟨141086, by rfl⟩ : syracuseStep 188115 = 282173) B282173
theorem B319187 : Blo 187803 319187 := bstep (se 1 (by rfl) ⟨239390, by rfl⟩ : syracuseStep 319187 = 478781) B478781
theorem B646865 : Blo 187803 646865 := bstep (se 2 (by rfl) ⟨242574, by rfl⟩ : syracuseStep 646865 = 485149) B485149
theorem B286433 : Blo 187803 286433 := bstep (se 2 (by rfl) ⟨107412, by rfl⟩ : syracuseStep 286433 = 214825) B214825
theorem B188131 : Blo 187803 188131 := bstep (se 1 (by rfl) ⟨141098, by rfl⟩ : syracuseStep 188131 = 282197) B282197
theorem B483043 : Blo 187803 483043 := bstep (se 1 (by rfl) ⟨362282, by rfl⟩ : syracuseStep 483043 = 724565) B724565
theorem B188147 : Blo 187803 188147 := bstep (se 1 (by rfl) ⟨141110, by rfl⟩ : syracuseStep 188147 = 282221) B282221
theorem B286451 : Blo 187803 286451 := bstep (se 1 (by rfl) ⟨214838, by rfl⟩ : syracuseStep 286451 = 429677) B429677
theorem B188163 : Blo 187803 188163 := bstep (se 1 (by rfl) ⟨141122, by rfl⟩ : syracuseStep 188163 = 282245) B282245
theorem B286481 : Blo 187803 286481 := bstep (se 2 (by rfl) ⟨107430, by rfl⟩ : syracuseStep 286481 = 214861) B214861
theorem B188179 : Blo 187803 188179 := bstep (se 1 (by rfl) ⟨141134, by rfl⟩ : syracuseStep 188179 = 282269) B282269
theorem B188195 : Blo 187803 188195 := bstep (se 1 (by rfl) ⟨141146, by rfl⟩ : syracuseStep 188195 = 282293) B282293
theorem B286499 : Blo 187803 286499 := bstep (se 1 (by rfl) ⟨214874, by rfl⟩ : syracuseStep 286499 = 429749) B429749
theorem B188211 : Blo 187803 188211 := bstep (se 1 (by rfl) ⟨141158, by rfl⟩ : syracuseStep 188211 = 282317) B282317
theorem B286529 : Blo 187803 286529 := bstep (se 2 (by rfl) ⟨107448, by rfl⟩ : syracuseStep 286529 = 214897) B214897
theorem B188227 : Blo 187803 188227 := bstep (se 1 (by rfl) ⟨141170, by rfl⟩ : syracuseStep 188227 = 282341) B282341
theorem B188243 : Blo 187803 188243 := bstep (se 1 (by rfl) ⟨141182, by rfl⟩ : syracuseStep 188243 = 282365) B282365
theorem B319315 : Blo 187803 319315 := bstep (se 1 (by rfl) ⟨239486, by rfl⟩ : syracuseStep 319315 = 478973) B478973
theorem B286547 : Blo 187803 286547 := bstep (se 1 (by rfl) ⟨214910, by rfl⟩ : syracuseStep 286547 = 429821) B429821
theorem B188259 : Blo 187803 188259 := bstep (se 1 (by rfl) ⟨141194, by rfl⟩ : syracuseStep 188259 = 282389) B282389
theorem B483185 : Blo 187803 483185 := bstep (se 2 (by rfl) ⟨181194, by rfl⟩ : syracuseStep 483185 = 362389) B362389
theorem B286577 : Blo 187803 286577 := bstep (se 2 (by rfl) ⟨107466, by rfl⟩ : syracuseStep 286577 = 214933) B214933
theorem B188275 : Blo 187803 188275 := bstep (se 1 (by rfl) ⟨141206, by rfl⟩ : syracuseStep 188275 = 282413) B282413
theorem B188291 : Blo 187803 188291 := bstep (se 1 (by rfl) ⟨141218, by rfl⟩ : syracuseStep 188291 = 282437) B282437
theorem B286595 : Blo 187803 286595 := bstep (se 1 (by rfl) ⟨214946, by rfl⟩ : syracuseStep 286595 = 429893) B429893
theorem B188307 : Blo 187803 188307 := bstep (se 1 (by rfl) ⟨141230, by rfl⟩ : syracuseStep 188307 = 282461) B282461
theorem B286625 : Blo 187803 286625 := bstep (se 2 (by rfl) ⟨107484, by rfl⟩ : syracuseStep 286625 = 214969) B214969
theorem B188323 : Blo 187803 188323 := bstep (se 1 (by rfl) ⟨141242, by rfl⟩ : syracuseStep 188323 = 282485) B282485
theorem B188339 : Blo 187803 188339 := bstep (se 1 (by rfl) ⟨141254, by rfl⟩ : syracuseStep 188339 = 282509) B282509
theorem B286643 : Blo 187803 286643 := bstep (se 1 (by rfl) ⟨214982, by rfl⟩ : syracuseStep 286643 = 429965) B429965
theorem B188355 : Blo 187803 188355 := bstep (se 1 (by rfl) ⟨141266, by rfl⟩ : syracuseStep 188355 = 282533) B282533
theorem B286673 : Blo 187803 286673 := bstep (se 2 (by rfl) ⟨107502, by rfl⟩ : syracuseStep 286673 = 215005) B215005
theorem B188371 : Blo 187803 188371 := bstep (se 1 (by rfl) ⟨141278, by rfl⟩ : syracuseStep 188371 = 282557) B282557
theorem B319457 : Blo 187803 319457 := bstep (se 2 (by rfl) ⟨119796, by rfl⟩ : syracuseStep 319457 = 239593) B239593
theorem B188387 : Blo 187803 188387 := bstep (se 1 (by rfl) ⟨141290, by rfl⟩ : syracuseStep 188387 = 282581) B282581
theorem B286691 : Blo 187803 286691 := bstep (se 1 (by rfl) ⟨215018, by rfl⟩ : syracuseStep 286691 = 430037) B430037
theorem B188403 : Blo 187803 188403 := bstep (se 1 (by rfl) ⟨141302, by rfl⟩ : syracuseStep 188403 = 282605) B282605
theorem B286721 : Blo 187803 286721 := bstep (se 2 (by rfl) ⟨107520, by rfl⟩ : syracuseStep 286721 = 215041) B215041
theorem B188419 : Blo 187803 188419 := bstep (se 1 (by rfl) ⟨141314, by rfl⟩ : syracuseStep 188419 = 282629) B282629
theorem B188435 : Blo 187803 188435 := bstep (se 1 (by rfl) ⟨141326, by rfl⟩ : syracuseStep 188435 = 282653) B282653
theorem B286739 : Blo 187803 286739 := bstep (se 1 (by rfl) ⟨215054, by rfl⟩ : syracuseStep 286739 = 430109) B430109
theorem B188451 : Blo 187803 188451 := bstep (se 1 (by rfl) ⟨141338, by rfl⟩ : syracuseStep 188451 = 282677) B282677
theorem B286769 : Blo 187803 286769 := bstep (se 2 (by rfl) ⟨107538, by rfl⟩ : syracuseStep 286769 = 215077) B215077
theorem B188467 : Blo 187803 188467 := bstep (se 1 (by rfl) ⟨141350, by rfl⟩ : syracuseStep 188467 = 282701) B282701
theorem B188483 : Blo 187803 188483 := bstep (se 1 (by rfl) ⟨141362, by rfl⟩ : syracuseStep 188483 = 282725) B282725
theorem B286787 : Blo 187803 286787 := bstep (se 1 (by rfl) ⟨215090, by rfl⟩ : syracuseStep 286787 = 430181) B430181
theorem B188499 : Blo 187803 188499 := bstep (se 1 (by rfl) ⟨141374, by rfl⟩ : syracuseStep 188499 = 282749) B282749
theorem B319585 : Blo 187803 319585 := bstep (se 2 (by rfl) ⟨119844, by rfl⟩ : syracuseStep 319585 = 239689) B239689
theorem B188515 : Blo 187803 188515 := bstep (se 1 (by rfl) ⟨141386, by rfl⟩ : syracuseStep 188515 = 282773) B282773
theorem B1433699 : Blo 187803 1433699 := bstep (se 1 (by rfl) ⟨1075274, by rfl⟩ : syracuseStep 1433699 = 2150549) B2150549
theorem B286817 : Blo 187803 286817 := bstep (se 2 (by rfl) ⟨107556, by rfl⟩ : syracuseStep 286817 = 215113) B215113
theorem B188531 : Blo 187803 188531 := bstep (se 1 (by rfl) ⟨141398, by rfl⟩ : syracuseStep 188531 = 282797) B282797
theorem B286835 : Blo 187803 286835 := bstep (se 1 (by rfl) ⟨215126, by rfl⟩ : syracuseStep 286835 = 430253) B430253
theorem B188547 : Blo 187803 188547 := bstep (se 1 (by rfl) ⟨141410, by rfl⟩ : syracuseStep 188547 = 282821) B282821
theorem B319619 : Blo 187803 319619 := bstep (se 1 (by rfl) ⟨239714, by rfl⟩ : syracuseStep 319619 = 479429) B479429
theorem B1532045 : Blo 187803 1532045 := bstep (se 3 (by rfl) ⟨287258, by rfl⟩ : syracuseStep 1532045 = 574517) B574517
theorem B286865 : Blo 187803 286865 := bstep (se 2 (by rfl) ⟨107574, by rfl⟩ : syracuseStep 286865 = 215149) B215149
theorem B188563 : Blo 187803 188563 := bstep (se 1 (by rfl) ⟨141422, by rfl⟩ : syracuseStep 188563 = 282845) B282845
theorem B188579 : Blo 187803 188579 := bstep (se 1 (by rfl) ⟨141434, by rfl⟩ : syracuseStep 188579 = 282869) B282869
theorem B286883 : Blo 187803 286883 := bstep (se 1 (by rfl) ⟨215162, by rfl⟩ : syracuseStep 286883 = 430325) B430325
theorem B188595 : Blo 187803 188595 := bstep (se 1 (by rfl) ⟨141446, by rfl⟩ : syracuseStep 188595 = 282893) B282893
theorem B286913 : Blo 187803 286913 := bstep (se 2 (by rfl) ⟨107592, by rfl⟩ : syracuseStep 286913 = 215185) B215185
theorem B188611 : Blo 187803 188611 := bstep (se 1 (by rfl) ⟨141458, by rfl⟩ : syracuseStep 188611 = 282917) B282917
theorem B188627 : Blo 187803 188627 := bstep (se 1 (by rfl) ⟨141470, by rfl⟩ : syracuseStep 188627 = 282941) B282941
theorem B286931 : Blo 187803 286931 := bstep (se 1 (by rfl) ⟨215198, by rfl⟩ : syracuseStep 286931 = 430397) B430397
theorem B188643 : Blo 187803 188643 := bstep (se 1 (by rfl) ⟨141482, by rfl⟩ : syracuseStep 188643 = 282965) B282965
theorem B286961 : Blo 187803 286961 := bstep (se 2 (by rfl) ⟨107610, by rfl⟩ : syracuseStep 286961 = 215221) B215221
theorem B188659 : Blo 187803 188659 := bstep (se 1 (by rfl) ⟨141494, by rfl⟩ : syracuseStep 188659 = 282989) B282989
theorem B188675 : Blo 187803 188675 := bstep (se 1 (by rfl) ⟨141506, by rfl⟩ : syracuseStep 188675 = 283013) B283013
theorem B319747 : Blo 187803 319747 := bstep (se 1 (by rfl) ⟨239810, by rfl⟩ : syracuseStep 319747 = 479621) B479621
theorem B286979 : Blo 187803 286979 := bstep (se 1 (by rfl) ⟨215234, by rfl⟩ : syracuseStep 286979 = 430469) B430469
theorem B188691 : Blo 187803 188691 := bstep (se 1 (by rfl) ⟨141518, by rfl⟩ : syracuseStep 188691 = 283037) B283037
theorem B287009 : Blo 187803 287009 := bstep (se 2 (by rfl) ⟨107628, by rfl⟩ : syracuseStep 287009 = 215257) B215257
theorem B188707 : Blo 187803 188707 := bstep (se 1 (by rfl) ⟨141530, by rfl⟩ : syracuseStep 188707 = 283061) B283061
theorem B647459 : Blo 187803 647459 := bstep (se 1 (by rfl) ⟨485594, by rfl⟩ : syracuseStep 647459 = 971189) B971189
theorem B188723 : Blo 187803 188723 := bstep (se 1 (by rfl) ⟨141542, by rfl⟩ : syracuseStep 188723 = 283085) B283085
theorem B287027 : Blo 187803 287027 := bstep (se 1 (by rfl) ⟨215270, by rfl⟩ : syracuseStep 287027 = 430541) B430541
theorem B188739 : Blo 187803 188739 := bstep (se 1 (by rfl) ⟨141554, by rfl⟩ : syracuseStep 188739 = 283109) B283109
theorem B287057 : Blo 187803 287057 := bstep (se 2 (by rfl) ⟨107646, by rfl⟩ : syracuseStep 287057 = 215293) B215293
theorem B188755 : Blo 187803 188755 := bstep (se 1 (by rfl) ⟨141566, by rfl⟩ : syracuseStep 188755 = 283133) B283133
theorem B188771 : Blo 187803 188771 := bstep (se 1 (by rfl) ⟨141578, by rfl⟩ : syracuseStep 188771 = 283157) B283157
theorem B287075 : Blo 187803 287075 := bstep (se 1 (by rfl) ⟨215306, by rfl⟩ : syracuseStep 287075 = 430613) B430613
theorem B188787 : Blo 187803 188787 := bstep (se 1 (by rfl) ⟨141590, by rfl⟩ : syracuseStep 188787 = 283181) B283181
theorem B287105 : Blo 187803 287105 := bstep (se 2 (by rfl) ⟨107664, by rfl⟩ : syracuseStep 287105 = 215329) B215329
theorem B188803 : Blo 187803 188803 := bstep (se 1 (by rfl) ⟨141602, by rfl⟩ : syracuseStep 188803 = 283205) B283205
theorem B319889 : Blo 187803 319889 := bstep (se 2 (by rfl) ⟨119958, by rfl⟩ : syracuseStep 319889 = 239917) B239917
theorem B188819 : Blo 187803 188819 := bstep (se 1 (by rfl) ⟨141614, by rfl⟩ : syracuseStep 188819 = 283229) B283229
theorem B287123 : Blo 187803 287123 := bstep (se 1 (by rfl) ⟨215342, by rfl⟩ : syracuseStep 287123 = 430685) B430685
theorem B188835 : Blo 187803 188835 := bstep (se 1 (by rfl) ⟨141626, by rfl⟩ : syracuseStep 188835 = 283253) B283253
theorem B287153 : Blo 187803 287153 := bstep (se 2 (by rfl) ⟨107682, by rfl⟩ : syracuseStep 287153 = 215365) B215365
theorem B188851 : Blo 187803 188851 := bstep (se 1 (by rfl) ⟨141638, by rfl⟩ : syracuseStep 188851 = 283277) B283277
theorem B188867 : Blo 187803 188867 := bstep (se 1 (by rfl) ⟨141650, by rfl⟩ : syracuseStep 188867 = 283301) B283301
theorem B287171 : Blo 187803 287171 := bstep (se 1 (by rfl) ⟨215378, by rfl⟩ : syracuseStep 287171 = 430757) B430757
theorem B188883 : Blo 187803 188883 := bstep (se 1 (by rfl) ⟨141662, by rfl⟩ : syracuseStep 188883 = 283325) B283325
theorem B287201 : Blo 187803 287201 := bstep (se 2 (by rfl) ⟨107700, by rfl⟩ : syracuseStep 287201 = 215401) B215401
theorem B188899 : Blo 187803 188899 := bstep (se 1 (by rfl) ⟨141674, by rfl⟩ : syracuseStep 188899 = 283349) B283349
theorem B188915 : Blo 187803 188915 := bstep (se 1 (by rfl) ⟨141686, by rfl⟩ : syracuseStep 188915 = 283373) B283373
theorem B287219 : Blo 187803 287219 := bstep (se 1 (by rfl) ⟨215414, by rfl⟩ : syracuseStep 287219 = 430829) B430829
theorem B188931 : Blo 187803 188931 := bstep (se 1 (by rfl) ⟨141698, by rfl⟩ : syracuseStep 188931 = 283397) B283397
theorem B320017 : Blo 187803 320017 := bstep (se 2 (by rfl) ⟨120006, by rfl⟩ : syracuseStep 320017 = 240013) B240013
theorem B188947 : Blo 187803 188947 := bstep (se 1 (by rfl) ⟨141710, by rfl⟩ : syracuseStep 188947 = 283421) B283421
theorem B287249 : Blo 187803 287249 := bstep (se 2 (by rfl) ⟨107718, by rfl⟩ : syracuseStep 287249 = 215437) B215437
theorem B188963 : Blo 187803 188963 := bstep (se 1 (by rfl) ⟨141722, by rfl⟩ : syracuseStep 188963 = 283445) B283445
theorem B287267 : Blo 187803 287267 := bstep (se 1 (by rfl) ⟨215450, by rfl⟩ : syracuseStep 287267 = 430901) B430901
theorem B188979 : Blo 187803 188979 := bstep (se 1 (by rfl) ⟨141734, by rfl⟩ : syracuseStep 188979 = 283469) B283469
theorem B320051 : Blo 187803 320051 := bstep (se 1 (by rfl) ⟨240038, by rfl⟩ : syracuseStep 320051 = 480077) B480077
theorem B287297 : Blo 187803 287297 := bstep (se 2 (by rfl) ⟨107736, by rfl⟩ : syracuseStep 287297 = 215473) B215473
theorem B188995 : Blo 187803 188995 := bstep (se 1 (by rfl) ⟨141746, by rfl⟩ : syracuseStep 188995 = 283493) B283493
theorem B189011 : Blo 187803 189011 := bstep (se 1 (by rfl) ⟨141758, by rfl⟩ : syracuseStep 189011 = 283517) B283517
theorem B287315 : Blo 187803 287315 := bstep (se 1 (by rfl) ⟨215486, by rfl⟩ : syracuseStep 287315 = 430973) B430973
theorem B189027 : Blo 187803 189027 := bstep (se 1 (by rfl) ⟨141770, by rfl⟩ : syracuseStep 189027 = 283541) B283541
theorem B287345 : Blo 187803 287345 := bstep (se 2 (by rfl) ⟨107754, by rfl⟩ : syracuseStep 287345 = 215509) B215509
theorem B189043 : Blo 187803 189043 := bstep (se 1 (by rfl) ⟨141782, by rfl⟩ : syracuseStep 189043 = 283565) B283565
theorem B189059 : Blo 187803 189059 := bstep (se 1 (by rfl) ⟨141794, by rfl⟩ : syracuseStep 189059 = 283589) B283589
theorem B287363 : Blo 187803 287363 := bstep (se 1 (by rfl) ⟨215522, by rfl⟩ : syracuseStep 287363 = 431045) B431045
theorem B713357 : Blo 187803 713357 := bstep (se 3 (by rfl) ⟨133754, by rfl⟩ : syracuseStep 713357 = 267509) B267509
theorem B189075 : Blo 187803 189075 := bstep (se 1 (by rfl) ⟨141806, by rfl⟩ : syracuseStep 189075 = 283613) B283613
theorem B287393 : Blo 187803 287393 := bstep (se 2 (by rfl) ⟨107772, by rfl⟩ : syracuseStep 287393 = 215545) B215545
theorem B189091 : Blo 187803 189091 := bstep (se 1 (by rfl) ⟨141818, by rfl⟩ : syracuseStep 189091 = 283637) B283637
theorem B189107 : Blo 187803 189107 := bstep (se 1 (by rfl) ⟨141830, by rfl⟩ : syracuseStep 189107 = 283661) B283661
theorem B320179 : Blo 187803 320179 := bstep (se 1 (by rfl) ⟨240134, by rfl⟩ : syracuseStep 320179 = 480269) B480269
theorem B287411 : Blo 187803 287411 := bstep (se 1 (by rfl) ⟨215558, by rfl⟩ : syracuseStep 287411 = 431117) B431117
theorem B189123 : Blo 187803 189123 := bstep (se 1 (by rfl) ⟨141842, by rfl⟩ : syracuseStep 189123 = 283685) B283685
theorem B287441 : Blo 187803 287441 := bstep (se 2 (by rfl) ⟨107790, by rfl⟩ : syracuseStep 287441 = 215581) B215581
theorem B189139 : Blo 187803 189139 := bstep (se 1 (by rfl) ⟨141854, by rfl⟩ : syracuseStep 189139 = 283709) B283709
theorem B189155 : Blo 187803 189155 := bstep (se 1 (by rfl) ⟨141866, by rfl⟩ : syracuseStep 189155 = 283733) B283733
theorem B287459 : Blo 187803 287459 := bstep (se 1 (by rfl) ⟨215594, by rfl⟩ : syracuseStep 287459 = 431189) B431189
theorem B189171 : Blo 187803 189171 := bstep (se 1 (by rfl) ⟨141878, by rfl⟩ : syracuseStep 189171 = 283757) B283757
theorem B287489 : Blo 187803 287489 := bstep (se 2 (by rfl) ⟨107808, by rfl⟩ : syracuseStep 287489 = 215617) B215617
theorem B189187 : Blo 187803 189187 := bstep (se 1 (by rfl) ⟨141890, by rfl⟩ : syracuseStep 189187 = 283781) B283781
theorem B189203 : Blo 187803 189203 := bstep (se 1 (by rfl) ⟨141902, by rfl⟩ : syracuseStep 189203 = 283805) B283805
theorem B287507 : Blo 187803 287507 := bstep (se 1 (by rfl) ⟨215630, by rfl⟩ : syracuseStep 287507 = 431261) B431261
theorem B189219 : Blo 187803 189219 := bstep (se 1 (by rfl) ⟨141914, by rfl⟩ : syracuseStep 189219 = 283829) B283829
theorem B287537 : Blo 187803 287537 := bstep (se 2 (by rfl) ⟨107826, by rfl⟩ : syracuseStep 287537 = 215653) B215653
theorem B189235 : Blo 187803 189235 := bstep (se 1 (by rfl) ⟨141926, by rfl⟩ : syracuseStep 189235 = 283853) B283853
theorem B320321 : Blo 187803 320321 := bstep (se 2 (by rfl) ⟨120120, by rfl⟩ : syracuseStep 320321 = 240241) B240241
theorem B189251 : Blo 187803 189251 := bstep (se 1 (by rfl) ⟨141938, by rfl⟩ : syracuseStep 189251 = 283877) B283877
theorem B287555 : Blo 187803 287555 := bstep (se 1 (by rfl) ⟨215666, by rfl⟩ : syracuseStep 287555 = 431333) B431333
theorem B484177 : Blo 187803 484177 := bstep (se 2 (by rfl) ⟨181566, by rfl⟩ : syracuseStep 484177 = 363133) B363133
theorem B189267 : Blo 187803 189267 := bstep (se 1 (by rfl) ⟨141950, by rfl⟩ : syracuseStep 189267 = 283901) B283901
theorem B287585 : Blo 187803 287585 := bstep (se 2 (by rfl) ⟨107844, by rfl⟩ : syracuseStep 287585 = 215689) B215689
theorem B189283 : Blo 187803 189283 := bstep (se 1 (by rfl) ⟨141962, by rfl⟩ : syracuseStep 189283 = 283925) B283925
theorem B451441 : Blo 187803 451441 := bstep (se 2 (by rfl) ⟨169290, by rfl⟩ : syracuseStep 451441 = 338581) B338581
theorem B189299 : Blo 187803 189299 := bstep (se 1 (by rfl) ⟨141974, by rfl⟩ : syracuseStep 189299 = 283949) B283949
theorem B287603 : Blo 187803 287603 := bstep (se 1 (by rfl) ⟨215702, by rfl⟩ : syracuseStep 287603 = 431405) B431405
theorem B189315 : Blo 187803 189315 := bstep (se 1 (by rfl) ⟨141986, by rfl⟩ : syracuseStep 189315 = 283973) B283973
theorem B287633 : Blo 187803 287633 := bstep (se 2 (by rfl) ⟨107862, by rfl⟩ : syracuseStep 287633 = 215725) B215725
theorem B189331 : Blo 187803 189331 := bstep (se 1 (by rfl) ⟨141998, by rfl⟩ : syracuseStep 189331 = 283997) B283997
theorem B189347 : Blo 187803 189347 := bstep (se 1 (by rfl) ⟨142010, by rfl⟩ : syracuseStep 189347 = 284021) B284021
theorem B287651 : Blo 187803 287651 := bstep (se 1 (by rfl) ⟨215738, by rfl⟩ : syracuseStep 287651 = 431477) B431477
theorem B189363 : Blo 187803 189363 := bstep (se 1 (by rfl) ⟨142022, by rfl⟩ : syracuseStep 189363 = 284045) B284045
theorem B320449 : Blo 187803 320449 := bstep (se 2 (by rfl) ⟨120168, by rfl⟩ : syracuseStep 320449 = 240337) B240337
theorem B189379 : Blo 187803 189379 := bstep (se 1 (by rfl) ⟨142034, by rfl⟩ : syracuseStep 189379 = 284069) B284069
theorem B287681 : Blo 187803 287681 := bstep (se 2 (by rfl) ⟨107880, by rfl⟩ : syracuseStep 287681 = 215761) B215761
theorem B189395 : Blo 187803 189395 := bstep (se 1 (by rfl) ⟨142046, by rfl⟩ : syracuseStep 189395 = 284093) B284093
theorem B287699 : Blo 187803 287699 := bstep (se 1 (by rfl) ⟨215774, by rfl⟩ : syracuseStep 287699 = 431549) B431549
theorem B189411 : Blo 187803 189411 := bstep (se 1 (by rfl) ⟨142058, by rfl⟩ : syracuseStep 189411 = 284117) B284117
theorem B320483 : Blo 187803 320483 := bstep (se 1 (by rfl) ⟨240362, by rfl⟩ : syracuseStep 320483 = 480725) B480725
theorem B1172465 : Blo 187803 1172465 := bstep (se 2 (by rfl) ⟨439674, by rfl⟩ : syracuseStep 1172465 = 879349) B879349
theorem B189427 : Blo 187803 189427 := bstep (se 1 (by rfl) ⟨142070, by rfl⟩ : syracuseStep 189427 = 284141) B284141
theorem B189443 : Blo 187803 189443 := bstep (se 1 (by rfl) ⟨142082, by rfl⟩ : syracuseStep 189443 = 284165) B284165
theorem B1074181 : Blo 187803 1074181 := bstep (se 4 (by rfl) ⟨100704, by rfl⟩ : syracuseStep 1074181 = 201409) B201409
theorem B812045 : Blo 187803 812045 := bstep (se 3 (by rfl) ⟨152258, by rfl⟩ : syracuseStep 812045 = 304517) B304517
theorem B189459 : Blo 187803 189459 := bstep (se 1 (by rfl) ⟨142094, by rfl⟩ : syracuseStep 189459 = 284189) B284189
theorem B189475 : Blo 187803 189475 := bstep (se 1 (by rfl) ⟨142106, by rfl⟩ : syracuseStep 189475 = 284213) B284213
theorem B189491 : Blo 187803 189491 := bstep (se 1 (by rfl) ⟨142118, by rfl⟩ : syracuseStep 189491 = 284237) B284237
theorem B189507 : Blo 187803 189507 := bstep (se 1 (by rfl) ⟨142130, by rfl⟩ : syracuseStep 189507 = 284261) B284261
theorem B189523 : Blo 187803 189523 := bstep (se 1 (by rfl) ⟨142142, by rfl⟩ : syracuseStep 189523 = 284285) B284285
theorem B189539 : Blo 187803 189539 := bstep (se 1 (by rfl) ⟨142154, by rfl⟩ : syracuseStep 189539 = 284309) B284309
theorem B320611 : Blo 187803 320611 := bstep (se 1 (by rfl) ⟨240458, by rfl⟩ : syracuseStep 320611 = 480917) B480917
theorem B484451 : Blo 187803 484451 := bstep (se 1 (by rfl) ⟨363338, by rfl⟩ : syracuseStep 484451 = 726677) B726677
theorem B189555 : Blo 187803 189555 := bstep (se 1 (by rfl) ⟨142166, by rfl⟩ : syracuseStep 189555 = 284333) B284333
theorem B189571 : Blo 187803 189571 := bstep (se 1 (by rfl) ⟨142178, by rfl⟩ : syracuseStep 189571 = 284357) B284357
theorem B189587 : Blo 187803 189587 := bstep (se 1 (by rfl) ⟨142190, by rfl⟩ : syracuseStep 189587 = 284381) B284381
theorem B189603 : Blo 187803 189603 := bstep (se 1 (by rfl) ⟨142202, by rfl⟩ : syracuseStep 189603 = 284405) B284405
theorem B189619 : Blo 187803 189619 := bstep (se 1 (by rfl) ⟨142214, by rfl⟩ : syracuseStep 189619 = 284429) B284429
theorem B189635 : Blo 187803 189635 := bstep (se 1 (by rfl) ⟨142226, by rfl⟩ : syracuseStep 189635 = 284453) B284453
theorem B189651 : Blo 187803 189651 := bstep (se 1 (by rfl) ⟨142238, by rfl⟩ : syracuseStep 189651 = 284477) B284477
theorem B189667 : Blo 187803 189667 := bstep (se 1 (by rfl) ⟨142250, by rfl⟩ : syracuseStep 189667 = 284501) B284501
theorem B320753 : Blo 187803 320753 := bstep (se 2 (by rfl) ⟨120282, by rfl⟩ : syracuseStep 320753 = 240565) B240565
theorem B189683 : Blo 187803 189683 := bstep (se 1 (by rfl) ⟨142262, by rfl⟩ : syracuseStep 189683 = 284525) B284525
theorem B189699 : Blo 187803 189699 := bstep (se 1 (by rfl) ⟨142274, by rfl⟩ : syracuseStep 189699 = 284549) B284549
theorem B189715 : Blo 187803 189715 := bstep (se 1 (by rfl) ⟨142286, by rfl⟩ : syracuseStep 189715 = 284573) B284573
theorem B189731 : Blo 187803 189731 := bstep (se 1 (by rfl) ⟨142298, by rfl⟩ : syracuseStep 189731 = 284597) B284597
theorem B484643 : Blo 187803 484643 := bstep (se 1 (by rfl) ⟨363482, by rfl⟩ : syracuseStep 484643 = 726965) B726965
theorem B386353 : Blo 187803 386353 := bstep (se 2 (by rfl) ⟨144882, by rfl⟩ : syracuseStep 386353 = 289765) B289765
theorem B189747 : Blo 187803 189747 := bstep (se 1 (by rfl) ⟨142310, by rfl⟩ : syracuseStep 189747 = 284621) B284621
theorem B189763 : Blo 187803 189763 := bstep (se 1 (by rfl) ⟨142322, by rfl⟩ : syracuseStep 189763 = 284645) B284645
theorem B189779 : Blo 187803 189779 := bstep (se 1 (by rfl) ⟨142334, by rfl⟩ : syracuseStep 189779 = 284669) B284669
theorem B189795 : Blo 187803 189795 := bstep (se 1 (by rfl) ⟨142346, by rfl⟩ : syracuseStep 189795 = 284693) B284693
theorem B320881 : Blo 187803 320881 := bstep (se 2 (by rfl) ⟨120330, by rfl⟩ : syracuseStep 320881 = 240661) B240661
theorem B189811 : Blo 187803 189811 := bstep (se 1 (by rfl) ⟨142358, by rfl⟩ : syracuseStep 189811 = 284717) B284717
theorem B189827 : Blo 187803 189827 := bstep (se 1 (by rfl) ⟨142370, by rfl⟩ : syracuseStep 189827 = 284741) B284741
theorem B2712973 : Blo 187803 2712973 := bstep (se 3 (by rfl) ⟨508682, by rfl⟩ : syracuseStep 2712973 = 1017365) B1017365
theorem B189843 : Blo 187803 189843 := bstep (se 1 (by rfl) ⟨142382, by rfl⟩ : syracuseStep 189843 = 284765) B284765
theorem B320915 : Blo 187803 320915 := bstep (se 1 (by rfl) ⟨240686, by rfl⟩ : syracuseStep 320915 = 481373) B481373
theorem B189859 : Blo 187803 189859 := bstep (se 1 (by rfl) ⟨142394, by rfl⟩ : syracuseStep 189859 = 284789) B284789
theorem B189875 : Blo 187803 189875 := bstep (se 1 (by rfl) ⟨142406, by rfl⟩ : syracuseStep 189875 = 284813) B284813
theorem B189891 : Blo 187803 189891 := bstep (se 1 (by rfl) ⟨142418, by rfl⟩ : syracuseStep 189891 = 284837) B284837
theorem B189907 : Blo 187803 189907 := bstep (se 1 (by rfl) ⟨142430, by rfl⟩ : syracuseStep 189907 = 284861) B284861
theorem B189923 : Blo 187803 189923 := bstep (se 1 (by rfl) ⟨142442, by rfl⟩ : syracuseStep 189923 = 284885) B284885
theorem B189939 : Blo 187803 189939 := bstep (se 1 (by rfl) ⟨142454, by rfl⟩ : syracuseStep 189939 = 284909) B284909
theorem B189955 : Blo 187803 189955 := bstep (se 1 (by rfl) ⟨142466, by rfl⟩ : syracuseStep 189955 = 284933) B284933
theorem B189971 : Blo 187803 189971 := bstep (se 1 (by rfl) ⟨142478, by rfl⟩ : syracuseStep 189971 = 284957) B284957
theorem B321043 : Blo 187803 321043 := bstep (se 1 (by rfl) ⟨240782, by rfl⟩ : syracuseStep 321043 = 481565) B481565
theorem B189987 : Blo 187803 189987 := bstep (se 1 (by rfl) ⟨142490, by rfl⟩ : syracuseStep 189987 = 284981) B284981
theorem B190003 : Blo 187803 190003 := bstep (se 1 (by rfl) ⟨142502, by rfl⟩ : syracuseStep 190003 = 285005) B285005
theorem B190019 : Blo 187803 190019 := bstep (se 1 (by rfl) ⟨142514, by rfl⟩ : syracuseStep 190019 = 285029) B285029
theorem B190035 : Blo 187803 190035 := bstep (se 1 (by rfl) ⟨142526, by rfl⟩ : syracuseStep 190035 = 285053) B285053
theorem B190051 : Blo 187803 190051 := bstep (se 1 (by rfl) ⟨142538, by rfl⟩ : syracuseStep 190051 = 285077) B285077
theorem B190067 : Blo 187803 190067 := bstep (se 1 (by rfl) ⟨142550, by rfl⟩ : syracuseStep 190067 = 285101) B285101
theorem B190083 : Blo 187803 190083 := bstep (se 1 (by rfl) ⟨142562, by rfl⟩ : syracuseStep 190083 = 285125) B285125
theorem B190099 : Blo 187803 190099 := bstep (se 1 (by rfl) ⟨142574, by rfl⟩ : syracuseStep 190099 = 285149) B285149
theorem B321185 : Blo 187803 321185 := bstep (se 2 (by rfl) ⟨120444, by rfl⟩ : syracuseStep 321185 = 240889) B240889
theorem B190115 : Blo 187803 190115 := bstep (se 1 (by rfl) ⟨142586, by rfl⟩ : syracuseStep 190115 = 285173) B285173
theorem B190131 : Blo 187803 190131 := bstep (se 1 (by rfl) ⟨142598, by rfl⟩ : syracuseStep 190131 = 285197) B285197
theorem B255683 : Blo 187803 255683 := bstep (se 1 (by rfl) ⟨191762, by rfl⟩ : syracuseStep 255683 = 383525) B383525
theorem B190147 : Blo 187803 190147 := bstep (se 1 (by rfl) ⟨142610, by rfl⟩ : syracuseStep 190147 = 285221) B285221
theorem B190163 : Blo 187803 190163 := bstep (se 1 (by rfl) ⟨142622, by rfl⟩ : syracuseStep 190163 = 285245) B285245
theorem B321251 : Blo 187803 321251 := bstep (se 1 (by rfl) ⟨240938, by rfl⟩ : syracuseStep 321251 = 481877) B481877
theorem B190179 : Blo 187803 190179 := bstep (se 1 (by rfl) ⟨142634, by rfl⟩ : syracuseStep 190179 = 285269) B285269
theorem B190195 : Blo 187803 190195 := bstep (se 1 (by rfl) ⟨142646, by rfl⟩ : syracuseStep 190195 = 285293) B285293
theorem B190211 : Blo 187803 190211 := bstep (se 1 (by rfl) ⟨142658, by rfl⟩ : syracuseStep 190211 = 285317) B285317
theorem B190227 : Blo 187803 190227 := bstep (se 1 (by rfl) ⟨142670, by rfl⟩ : syracuseStep 190227 = 285341) B285341
theorem B321313 : Blo 187803 321313 := bstep (se 2 (by rfl) ⟨120492, by rfl⟩ : syracuseStep 321313 = 240985) B240985
theorem B190243 : Blo 187803 190243 := bstep (se 1 (by rfl) ⟨142682, by rfl⟩ : syracuseStep 190243 = 285365) B285365
theorem B583469 : Blo 187803 583469 := bstep (se 3 (by rfl) ⟨109400, by rfl⟩ : syracuseStep 583469 = 218801) B218801
theorem B190259 : Blo 187803 190259 := bstep (se 1 (by rfl) ⟨142694, by rfl⟩ : syracuseStep 190259 = 285389) B285389
theorem B190275 : Blo 187803 190275 := bstep (se 1 (by rfl) ⟨142706, by rfl⟩ : syracuseStep 190275 = 285413) B285413
theorem B321347 : Blo 187803 321347 := bstep (se 1 (by rfl) ⟨241010, by rfl⟩ : syracuseStep 321347 = 482021) B482021
theorem B190291 : Blo 187803 190291 := bstep (se 1 (by rfl) ⟨142718, by rfl⟩ : syracuseStep 190291 = 285437) B285437
theorem B190307 : Blo 187803 190307 := bstep (se 1 (by rfl) ⟨142730, by rfl⟩ : syracuseStep 190307 = 285461) B285461
theorem B190323 : Blo 187803 190323 := bstep (se 1 (by rfl) ⟨142742, by rfl⟩ : syracuseStep 190323 = 285485) B285485
theorem B190339 : Blo 187803 190339 := bstep (se 1 (by rfl) ⟨142754, by rfl⟩ : syracuseStep 190339 = 285509) B285509
theorem B190355 : Blo 187803 190355 := bstep (se 1 (by rfl) ⟨142766, by rfl⟩ : syracuseStep 190355 = 285533) B285533
theorem B190371 : Blo 187803 190371 := bstep (se 1 (by rfl) ⟨142778, by rfl⟩ : syracuseStep 190371 = 285557) B285557
theorem B190387 : Blo 187803 190387 := bstep (se 1 (by rfl) ⟨142790, by rfl⟩ : syracuseStep 190387 = 285581) B285581
theorem B190403 : Blo 187803 190403 := bstep (se 1 (by rfl) ⟨142802, by rfl⟩ : syracuseStep 190403 = 285605) B285605
theorem B321475 : Blo 187803 321475 := bstep (se 1 (by rfl) ⟨241106, by rfl⟩ : syracuseStep 321475 = 482213) B482213
theorem B190419 : Blo 187803 190419 := bstep (se 1 (by rfl) ⟨142814, by rfl⟩ : syracuseStep 190419 = 285629) B285629
theorem B485347 : Blo 187803 485347 := bstep (se 1 (by rfl) ⟨364010, by rfl⟩ : syracuseStep 485347 = 728021) B728021
theorem B190435 : Blo 187803 190435 := bstep (se 1 (by rfl) ⟨142826, by rfl⟩ : syracuseStep 190435 = 285653) B285653
theorem B190451 : Blo 187803 190451 := bstep (se 1 (by rfl) ⟨142838, by rfl⟩ : syracuseStep 190451 = 285677) B285677
theorem B190467 : Blo 187803 190467 := bstep (se 1 (by rfl) ⟨142850, by rfl⟩ : syracuseStep 190467 = 285701) B285701
theorem B190483 : Blo 187803 190483 := bstep (se 1 (by rfl) ⟨142862, by rfl⟩ : syracuseStep 190483 = 285725) B285725
theorem B256033 : Blo 187803 256033 := bstep (se 2 (by rfl) ⟨96012, by rfl⟩ : syracuseStep 256033 = 192025) B192025
theorem B518179 : Blo 187803 518179 := bstep (se 1 (by rfl) ⟨388634, by rfl⟩ : syracuseStep 518179 = 777269) B777269
theorem B190499 : Blo 187803 190499 := bstep (se 1 (by rfl) ⟨142874, by rfl⟩ : syracuseStep 190499 = 285749) B285749
theorem B190515 : Blo 187803 190515 := bstep (se 1 (by rfl) ⟨142886, by rfl⟩ : syracuseStep 190515 = 285773) B285773
theorem B190531 : Blo 187803 190531 := bstep (se 1 (by rfl) ⟨142898, by rfl⟩ : syracuseStep 190531 = 285797) B285797
theorem B321617 : Blo 187803 321617 := bstep (se 2 (by rfl) ⟨120606, by rfl⟩ : syracuseStep 321617 = 241213) B241213
theorem B190547 : Blo 187803 190547 := bstep (se 1 (by rfl) ⟨142910, by rfl⟩ : syracuseStep 190547 = 285821) B285821
theorem B190563 : Blo 187803 190563 := bstep (se 1 (by rfl) ⟨142922, by rfl⟩ : syracuseStep 190563 = 285845) B285845
theorem B190579 : Blo 187803 190579 := bstep (se 1 (by rfl) ⟨142934, by rfl⟩ : syracuseStep 190579 = 285869) B285869
theorem B190595 : Blo 187803 190595 := bstep (se 1 (by rfl) ⟨142946, by rfl⟩ : syracuseStep 190595 = 285893) B285893
theorem B518285 : Blo 187803 518285 := bstep (se 3 (by rfl) ⟨97178, by rfl⟩ : syracuseStep 518285 = 194357) B194357
theorem B190611 : Blo 187803 190611 := bstep (se 1 (by rfl) ⟨142958, by rfl⟩ : syracuseStep 190611 = 285917) B285917
theorem B190627 : Blo 187803 190627 := bstep (se 1 (by rfl) ⟨142970, by rfl⟩ : syracuseStep 190627 = 285941) B285941
theorem B190643 : Blo 187803 190643 := bstep (se 1 (by rfl) ⟨142982, by rfl⟩ : syracuseStep 190643 = 285965) B285965
theorem B190659 : Blo 187803 190659 := bstep (se 1 (by rfl) ⟨142994, by rfl⟩ : syracuseStep 190659 = 285989) B285989
theorem B321745 : Blo 187803 321745 := bstep (se 2 (by rfl) ⟨120654, by rfl⟩ : syracuseStep 321745 = 241309) B241309
theorem B190675 : Blo 187803 190675 := bstep (se 1 (by rfl) ⟨143006, by rfl⟩ : syracuseStep 190675 = 286013) B286013
theorem B190691 : Blo 187803 190691 := bstep (se 1 (by rfl) ⟨143018, by rfl⟩ : syracuseStep 190691 = 286037) B286037
theorem B1370353 : Blo 187803 1370353 := bstep (se 2 (by rfl) ⟨513882, by rfl⟩ : syracuseStep 1370353 = 1027765) B1027765
theorem B321779 : Blo 187803 321779 := bstep (se 1 (by rfl) ⟨241334, by rfl⟩ : syracuseStep 321779 = 482669) B482669
theorem B190707 : Blo 187803 190707 := bstep (se 1 (by rfl) ⟨143030, by rfl⟩ : syracuseStep 190707 = 286061) B286061
theorem B190723 : Blo 187803 190723 := bstep (se 1 (by rfl) ⟨143042, by rfl⟩ : syracuseStep 190723 = 286085) B286085
theorem B190739 : Blo 187803 190739 := bstep (se 1 (by rfl) ⟨143054, by rfl⟩ : syracuseStep 190739 = 286109) B286109
theorem B190755 : Blo 187803 190755 := bstep (se 1 (by rfl) ⟨143066, by rfl⟩ : syracuseStep 190755 = 286133) B286133
theorem B190771 : Blo 187803 190771 := bstep (se 1 (by rfl) ⟨143078, by rfl⟩ : syracuseStep 190771 = 286157) B286157
theorem B190787 : Blo 187803 190787 := bstep (se 1 (by rfl) ⟨143090, by rfl⟩ : syracuseStep 190787 = 286181) B286181
theorem B190803 : Blo 187803 190803 := bstep (se 1 (by rfl) ⟨143102, by rfl⟩ : syracuseStep 190803 = 286205) B286205
theorem B190819 : Blo 187803 190819 := bstep (se 1 (by rfl) ⟨143114, by rfl⟩ : syracuseStep 190819 = 286229) B286229
theorem B321907 : Blo 187803 321907 := bstep (se 1 (by rfl) ⟨241430, by rfl⟩ : syracuseStep 321907 = 482861) B482861
theorem B190835 : Blo 187803 190835 := bstep (se 1 (by rfl) ⟨143126, by rfl⟩ : syracuseStep 190835 = 286253) B286253
theorem B190851 : Blo 187803 190851 := bstep (se 1 (by rfl) ⟨143138, by rfl⟩ : syracuseStep 190851 = 286277) B286277
theorem B190867 : Blo 187803 190867 := bstep (se 1 (by rfl) ⟨143150, by rfl⟩ : syracuseStep 190867 = 286301) B286301
theorem B190883 : Blo 187803 190883 := bstep (se 1 (by rfl) ⟨143162, by rfl⟩ : syracuseStep 190883 = 286325) B286325
theorem B190899 : Blo 187803 190899 := bstep (se 1 (by rfl) ⟨143174, by rfl⟩ : syracuseStep 190899 = 286349) B286349
theorem B190915 : Blo 187803 190915 := bstep (se 1 (by rfl) ⟨143186, by rfl⟩ : syracuseStep 190915 = 286373) B286373
theorem B190931 : Blo 187803 190931 := bstep (se 1 (by rfl) ⟨143198, by rfl⟩ : syracuseStep 190931 = 286397) B286397
theorem B190947 : Blo 187803 190947 := bstep (se 1 (by rfl) ⟨143210, by rfl⟩ : syracuseStep 190947 = 286421) B286421
theorem B190963 : Blo 187803 190963 := bstep (se 1 (by rfl) ⟨143222, by rfl⟩ : syracuseStep 190963 = 286445) B286445
theorem B322049 : Blo 187803 322049 := bstep (se 2 (by rfl) ⟨120768, by rfl⟩ : syracuseStep 322049 = 241537) B241537
theorem B190979 : Blo 187803 190979 := bstep (se 1 (by rfl) ⟨143234, by rfl⟩ : syracuseStep 190979 = 286469) B286469
theorem B387587 : Blo 187803 387587 := bstep (se 1 (by rfl) ⟨290690, by rfl⟩ : syracuseStep 387587 = 581381) B581381
theorem B813581 : Blo 187803 813581 := bstep (se 3 (by rfl) ⟨152546, by rfl⟩ : syracuseStep 813581 = 305093) B305093
theorem B190995 : Blo 187803 190995 := bstep (se 1 (by rfl) ⟨143246, by rfl⟩ : syracuseStep 190995 = 286493) B286493
theorem B191011 : Blo 187803 191011 := bstep (se 1 (by rfl) ⟨143258, by rfl⟩ : syracuseStep 191011 = 286517) B286517
theorem B191027 : Blo 187803 191027 := bstep (se 1 (by rfl) ⟨143270, by rfl⟩ : syracuseStep 191027 = 286541) B286541
theorem B191043 : Blo 187803 191043 := bstep (se 1 (by rfl) ⟨143282, by rfl⟩ : syracuseStep 191043 = 286565) B286565
theorem B191059 : Blo 187803 191059 := bstep (se 1 (by rfl) ⟨143294, by rfl⟩ : syracuseStep 191059 = 286589) B286589
theorem B191075 : Blo 187803 191075 := bstep (se 1 (by rfl) ⟨143306, by rfl⟩ : syracuseStep 191075 = 286613) B286613
theorem B387683 : Blo 187803 387683 := bstep (se 1 (by rfl) ⟨290762, by rfl⟩ : syracuseStep 387683 = 581525) B581525
theorem B191091 : Blo 187803 191091 := bstep (se 1 (by rfl) ⟨143318, by rfl⟩ : syracuseStep 191091 = 286637) B286637
theorem B322177 : Blo 187803 322177 := bstep (se 2 (by rfl) ⟨120816, by rfl⟩ : syracuseStep 322177 = 241633) B241633
theorem B191107 : Blo 187803 191107 := bstep (se 1 (by rfl) ⟨143330, by rfl⟩ : syracuseStep 191107 = 286661) B286661
theorem B191123 : Blo 187803 191123 := bstep (se 1 (by rfl) ⟨143342, by rfl⟩ : syracuseStep 191123 = 286685) B286685
theorem B322211 : Blo 187803 322211 := bstep (se 1 (by rfl) ⟨241658, by rfl⟩ : syracuseStep 322211 = 483317) B483317
theorem B191139 : Blo 187803 191139 := bstep (se 1 (by rfl) ⟨143354, by rfl⟩ : syracuseStep 191139 = 286709) B286709
theorem B191155 : Blo 187803 191155 := bstep (se 1 (by rfl) ⟨143366, by rfl⟩ : syracuseStep 191155 = 286733) B286733
theorem B191171 : Blo 187803 191171 := bstep (se 1 (by rfl) ⟨143378, by rfl⟩ : syracuseStep 191171 = 286757) B286757
theorem B191187 : Blo 187803 191187 := bstep (se 1 (by rfl) ⟨143390, by rfl⟩ : syracuseStep 191187 = 286781) B286781
theorem B191203 : Blo 187803 191203 := bstep (se 1 (by rfl) ⟨143402, by rfl⟩ : syracuseStep 191203 = 286805) B286805
theorem B191219 : Blo 187803 191219 := bstep (se 1 (by rfl) ⟨143414, by rfl⟩ : syracuseStep 191219 = 286829) B286829
theorem B191235 : Blo 187803 191235 := bstep (se 1 (by rfl) ⟨143426, by rfl⟩ : syracuseStep 191235 = 286853) B286853
theorem B191251 : Blo 187803 191251 := bstep (se 1 (by rfl) ⟨143438, by rfl⟩ : syracuseStep 191251 = 286877) B286877
theorem B322339 : Blo 187803 322339 := bstep (se 1 (by rfl) ⟨241754, by rfl⟩ : syracuseStep 322339 = 483509) B483509
theorem B191267 : Blo 187803 191267 := bstep (se 1 (by rfl) ⟨143450, by rfl⟩ : syracuseStep 191267 = 286901) B286901
theorem B191283 : Blo 187803 191283 := bstep (se 1 (by rfl) ⟨143462, by rfl⟩ : syracuseStep 191283 = 286925) B286925
theorem B191299 : Blo 187803 191299 := bstep (se 1 (by rfl) ⟨143474, by rfl⟩ : syracuseStep 191299 = 286949) B286949
theorem B191315 : Blo 187803 191315 := bstep (se 1 (by rfl) ⟨143486, by rfl⟩ : syracuseStep 191315 = 286973) B286973
theorem B191331 : Blo 187803 191331 := bstep (se 1 (by rfl) ⟨143498, by rfl⟩ : syracuseStep 191331 = 286997) B286997
theorem B1010531 : Blo 187803 1010531 := bstep (se 1 (by rfl) ⟨757898, by rfl⟩ : syracuseStep 1010531 = 1515797) B1515797
theorem B191347 : Blo 187803 191347 := bstep (se 1 (by rfl) ⟨143510, by rfl⟩ : syracuseStep 191347 = 287021) B287021
theorem B191363 : Blo 187803 191363 := bstep (se 1 (by rfl) ⟨143522, by rfl⟩ : syracuseStep 191363 = 287045) B287045
theorem B191379 : Blo 187803 191379 := bstep (se 1 (by rfl) ⟨143534, by rfl⟩ : syracuseStep 191379 = 287069) B287069
theorem B191395 : Blo 187803 191395 := bstep (se 1 (by rfl) ⟨143546, by rfl⟩ : syracuseStep 191395 = 287093) B287093
theorem B322481 : Blo 187803 322481 := bstep (se 2 (by rfl) ⟨120930, by rfl⟩ : syracuseStep 322481 = 241861) B241861
theorem B322483 : Blo 187803 322483 := bstep (se 1 (by rfl) ⟨241862, by rfl⟩ : syracuseStep 322483 = 483725) B483725
theorem B191411 : Blo 187803 191411 := bstep (se 1 (by rfl) ⟨143558, by rfl⟩ : syracuseStep 191411 = 287117) B287117
theorem B191427 : Blo 187803 191427 := bstep (se 1 (by rfl) ⟨143570, by rfl⟩ : syracuseStep 191427 = 287141) B287141
theorem B1076165 : Blo 187803 1076165 := bstep (se 4 (by rfl) ⟨100890, by rfl⟩ : syracuseStep 1076165 = 201781) B201781
theorem B191443 : Blo 187803 191443 := bstep (se 1 (by rfl) ⟨143582, by rfl⟩ : syracuseStep 191443 = 287165) B287165
theorem B191459 : Blo 187803 191459 := bstep (se 1 (by rfl) ⟨143594, by rfl⟩ : syracuseStep 191459 = 287189) B287189
theorem B191475 : Blo 187803 191475 := bstep (se 1 (by rfl) ⟨143606, by rfl⟩ : syracuseStep 191475 = 287213) B287213
theorem B191491 : Blo 187803 191491 := bstep (se 1 (by rfl) ⟨143618, by rfl⟩ : syracuseStep 191491 = 287237) B287237
theorem B191507 : Blo 187803 191507 := bstep (se 1 (by rfl) ⟨143630, by rfl⟩ : syracuseStep 191507 = 287261) B287261
theorem B191523 : Blo 187803 191523 := bstep (se 1 (by rfl) ⟨143642, by rfl⟩ : syracuseStep 191523 = 287285) B287285
theorem B322609 : Blo 187803 322609 := bstep (se 2 (by rfl) ⟨120978, by rfl⟩ : syracuseStep 322609 = 241957) B241957
theorem B191539 : Blo 187803 191539 := bstep (se 1 (by rfl) ⟨143654, by rfl⟩ : syracuseStep 191539 = 287309) B287309
theorem B191555 : Blo 187803 191555 := bstep (se 1 (by rfl) ⟨143666, by rfl⟩ : syracuseStep 191555 = 287333) B287333
theorem B322643 : Blo 187803 322643 := bstep (se 1 (by rfl) ⟨241982, by rfl⟩ : syracuseStep 322643 = 483965) B483965
theorem B191571 : Blo 187803 191571 := bstep (se 1 (by rfl) ⟨143678, by rfl⟩ : syracuseStep 191571 = 287357) B287357
theorem B191587 : Blo 187803 191587 := bstep (se 1 (by rfl) ⟨143690, by rfl⟩ : syracuseStep 191587 = 287381) B287381
theorem B191603 : Blo 187803 191603 := bstep (se 1 (by rfl) ⟨143702, by rfl⟩ : syracuseStep 191603 = 287405) B287405
theorem B191619 : Blo 187803 191619 := bstep (se 1 (by rfl) ⟨143714, by rfl⟩ : syracuseStep 191619 = 287429) B287429
theorem B191635 : Blo 187803 191635 := bstep (se 1 (by rfl) ⟨143726, by rfl⟩ : syracuseStep 191635 = 287453) B287453
theorem B191651 : Blo 187803 191651 := bstep (se 1 (by rfl) ⟨143738, by rfl⟩ : syracuseStep 191651 = 287477) B287477
theorem B191667 : Blo 187803 191667 := bstep (se 1 (by rfl) ⟨143750, by rfl⟩ : syracuseStep 191667 = 287501) B287501
theorem B191683 : Blo 187803 191683 := bstep (se 1 (by rfl) ⟨143762, by rfl⟩ : syracuseStep 191683 = 287525) B287525
theorem B322771 : Blo 187803 322771 := bstep (se 1 (by rfl) ⟨242078, by rfl⟩ : syracuseStep 322771 = 484157) B484157
theorem B191699 : Blo 187803 191699 := bstep (se 1 (by rfl) ⟨143774, by rfl⟩ : syracuseStep 191699 = 287549) B287549
theorem B191715 : Blo 187803 191715 := bstep (se 1 (by rfl) ⟨143786, by rfl⟩ : syracuseStep 191715 = 287573) B287573
theorem B191731 : Blo 187803 191731 := bstep (se 1 (by rfl) ⟨143798, by rfl⟩ : syracuseStep 191731 = 287597) B287597
theorem B191747 : Blo 187803 191747 := bstep (se 1 (by rfl) ⟨143810, by rfl⟩ : syracuseStep 191747 = 287621) B287621
theorem B191763 : Blo 187803 191763 := bstep (se 1 (by rfl) ⟨143822, by rfl⟩ : syracuseStep 191763 = 287645) B287645
theorem B191779 : Blo 187803 191779 := bstep (se 1 (by rfl) ⟨143834, by rfl⟩ : syracuseStep 191779 = 287669) B287669
theorem B191795 : Blo 187803 191795 := bstep (se 1 (by rfl) ⟨143846, by rfl⟩ : syracuseStep 191795 = 287693) B287693
theorem B322913 : Blo 187803 322913 := bstep (se 2 (by rfl) ⟨121092, by rfl⟩ : syracuseStep 322913 = 242185) B242185
theorem B1961329 : Blo 187803 1961329 := bstep (se 2 (by rfl) ⟨735498, by rfl⟩ : syracuseStep 1961329 = 1470997) B1470997
theorem B323041 : Blo 187803 323041 := bstep (se 2 (by rfl) ⟨121140, by rfl⟩ : syracuseStep 323041 = 242281) B242281
theorem B716273 : Blo 187803 716273 := bstep (se 2 (by rfl) ⟨268602, by rfl⟩ : syracuseStep 716273 = 537205) B537205
theorem B323075 : Blo 187803 323075 := bstep (se 1 (by rfl) ⟨242306, by rfl⟩ : syracuseStep 323075 = 484613) B484613
theorem B388721 : Blo 187803 388721 := bstep (se 2 (by rfl) ⟨145770, by rfl⟩ : syracuseStep 388721 = 291541) B291541
theorem B323203 : Blo 187803 323203 := bstep (se 1 (by rfl) ⟨242402, by rfl⟩ : syracuseStep 323203 = 484805) B484805
theorem B257699 : Blo 187803 257699 := bstep (se 1 (by rfl) ⟨193274, by rfl⟩ : syracuseStep 257699 = 386549) B386549
theorem B323249 : Blo 187803 323249 := bstep (se 2 (by rfl) ⟨121218, by rfl⟩ : syracuseStep 323249 = 242437) B242437
theorem B323345 : Blo 187803 323345 := bstep (se 2 (by rfl) ⟨121254, by rfl⟩ : syracuseStep 323345 = 242509) B242509
theorem B323473 : Blo 187803 323473 := bstep (se 2 (by rfl) ⟨121302, by rfl⟩ : syracuseStep 323473 = 242605) B242605
theorem B683939 : Blo 187803 683939 := bstep (se 1 (by rfl) ⟨512954, by rfl⟩ : syracuseStep 683939 = 1025909) B1025909
theorem B323507 : Blo 187803 323507 := bstep (se 1 (by rfl) ⟨242630, by rfl⟩ : syracuseStep 323507 = 485261) B485261
theorem B520195 : Blo 187803 520195 := bstep (se 1 (by rfl) ⟨390146, by rfl⟩ : syracuseStep 520195 = 780293) B780293
theorem B323635 : Blo 187803 323635 := bstep (se 1 (by rfl) ⟨242726, by rfl⟩ : syracuseStep 323635 = 485453) B485453
theorem B290947 : Blo 187803 290947 := bstep (se 1 (by rfl) ⟨218210, by rfl⟩ : syracuseStep 290947 = 436421) B436421
theorem B1142981 : Blo 187803 1142981 := bstep (se 4 (by rfl) ⟨107154, by rfl⟩ : syracuseStep 1142981 = 214309) B214309
theorem B258337 : Blo 187803 258337 := bstep (se 2 (by rfl) ⟨96876, by rfl⟩ : syracuseStep 258337 = 193753) B193753
theorem B258499 : Blo 187803 258499 := bstep (se 1 (by rfl) ⟨193874, by rfl⟩ : syracuseStep 258499 = 387749) B387749
theorem B1831409 : Blo 187803 1831409 := bstep (se 2 (by rfl) ⟨686778, by rfl⟩ : syracuseStep 1831409 = 1373557) B1373557
theorem B356899 : Blo 187803 356899 := bstep (se 1 (by rfl) ⟨267674, by rfl⟩ : syracuseStep 356899 = 535349) B535349
theorem B488035 : Blo 187803 488035 := bstep (se 1 (by rfl) ⟨366026, by rfl⟩ : syracuseStep 488035 = 732053) B732053
theorem B455345 : Blo 187803 455345 := bstep (se 2 (by rfl) ⟨170754, by rfl⟩ : syracuseStep 455345 = 341509) B341509
theorem B324481 : Blo 187803 324481 := bstep (se 2 (by rfl) ⟨121680, by rfl⟩ : syracuseStep 324481 = 243361) B243361
theorem B422801 : Blo 187803 422801 := bstep (se 2 (by rfl) ⟨158550, by rfl⟩ : syracuseStep 422801 = 317101) B317101
theorem B422819 : Blo 187803 422819 := bstep (se 1 (by rfl) ⟨317114, by rfl⟩ : syracuseStep 422819 = 634229) B634229
theorem B717731 : Blo 187803 717731 := bstep (se 1 (by rfl) ⟨538298, by rfl⟩ : syracuseStep 717731 = 1076597) B1076597
theorem B357347 : Blo 187803 357347 := bstep (se 1 (by rfl) ⟨268010, by rfl⟩ : syracuseStep 357347 = 536021) B536021
theorem B1209329 : Blo 187803 1209329 := bstep (se 2 (by rfl) ⟨453498, by rfl⟩ : syracuseStep 1209329 = 906997) B906997
theorem B423089 : Blo 187803 423089 := bstep (se 2 (by rfl) ⟨158658, by rfl⟩ : syracuseStep 423089 = 317317) B317317
theorem B423107 : Blo 187803 423107 := bstep (se 1 (by rfl) ⟨317330, by rfl⟩ : syracuseStep 423107 = 634661) B634661
theorem B357635 : Blo 187803 357635 := bstep (se 1 (by rfl) ⟨268226, by rfl⟩ : syracuseStep 357635 = 536453) B536453
theorem B455939 : Blo 187803 455939 := bstep (se 1 (by rfl) ⟨341954, by rfl⟩ : syracuseStep 455939 = 683909) B683909
theorem B816419 : Blo 187803 816419 := bstep (se 1 (by rfl) ⟨612314, by rfl⟩ : syracuseStep 816419 = 1224629) B1224629
theorem B1439045 : Blo 187803 1439045 := bstep (se 4 (by rfl) ⟨134910, by rfl⟩ : syracuseStep 1439045 = 269821) B269821
theorem B226643 : Blo 187803 226643 := bstep (se 1 (by rfl) ⟨169982, by rfl⟩ : syracuseStep 226643 = 339965) B339965
theorem B456035 : Blo 187803 456035 := bstep (se 1 (by rfl) ⟨342026, by rfl⟩ : syracuseStep 456035 = 684053) B684053
theorem B587213 : Blo 187803 587213 := bstep (se 3 (by rfl) ⟨110102, by rfl⟩ : syracuseStep 587213 = 220205) B220205
theorem B423377 : Blo 187803 423377 := bstep (se 2 (by rfl) ⟨158766, by rfl⟩ : syracuseStep 423377 = 317533) B317533
theorem B423395 : Blo 187803 423395 := bstep (se 1 (by rfl) ⟨317546, by rfl⟩ : syracuseStep 423395 = 635093) B635093
theorem B194195 : Blo 187803 194195 := bstep (se 1 (by rfl) ⟨145646, by rfl⟩ : syracuseStep 194195 = 291293) B291293
theorem B423665 : Blo 187803 423665 := bstep (se 2 (by rfl) ⟨158874, by rfl⟩ : syracuseStep 423665 = 317749) B317749
theorem B423683 : Blo 187803 423683 := bstep (se 1 (by rfl) ⟨317762, by rfl⟩ : syracuseStep 423683 = 635525) B635525
theorem B718733 : Blo 187803 718733 := bstep (se 3 (by rfl) ⟨134762, by rfl⟩ : syracuseStep 718733 = 269525) B269525
theorem B423953 : Blo 187803 423953 := bstep (se 2 (by rfl) ⟨158982, by rfl⟩ : syracuseStep 423953 = 317965) B317965
theorem B423971 : Blo 187803 423971 := bstep (se 1 (by rfl) ⟨317978, by rfl⟩ : syracuseStep 423971 = 635957) B635957
theorem B1210403 : Blo 187803 1210403 := bstep (se 1 (by rfl) ⟨907802, by rfl⟩ : syracuseStep 1210403 = 1815605) B1815605
theorem B915569 : Blo 187803 915569 := bstep (se 2 (by rfl) ⟨343338, by rfl⟩ : syracuseStep 915569 = 686677) B686677
theorem B1734797 : Blo 187803 1734797 := bstep (se 3 (by rfl) ⟨325274, by rfl⟩ : syracuseStep 1734797 = 650549) B650549
theorem B358577 : Blo 187803 358577 := bstep (se 2 (by rfl) ⟨134466, by rfl⟩ : syracuseStep 358577 = 268933) B268933
theorem B1308869 : Blo 187803 1308869 := bstep (se 4 (by rfl) ⟨122706, by rfl⟩ : syracuseStep 1308869 = 245413) B245413
theorem B456977 : Blo 187803 456977 := bstep (se 2 (by rfl) ⟨171366, by rfl⟩ : syracuseStep 456977 = 342733) B342733
theorem B424241 : Blo 187803 424241 := bstep (se 2 (by rfl) ⟨159090, by rfl⟩ : syracuseStep 424241 = 318181) B318181
theorem B915761 : Blo 187803 915761 := bstep (se 2 (by rfl) ⟨343410, by rfl⟩ : syracuseStep 915761 = 686821) B686821
theorem B424259 : Blo 187803 424259 := bstep (se 1 (by rfl) ⟨318194, by rfl⟩ : syracuseStep 424259 = 636389) B636389
theorem B1571185 : Blo 187803 1571185 := bstep (se 2 (by rfl) ⟨589194, by rfl⟩ : syracuseStep 1571185 = 1178389) B1178389
theorem B915875 : Blo 187803 915875 := bstep (se 1 (by rfl) ⟨686906, by rfl⟩ : syracuseStep 915875 = 1373813) B1373813
theorem B9238981 : Blo 187803 9238981 := bstep (se 4 (by rfl) ⟨866154, by rfl⟩ : syracuseStep 9238981 = 1732309) B1732309
theorem B2521613 : Blo 187803 2521613 := bstep (se 3 (by rfl) ⟨472802, by rfl⟩ : syracuseStep 2521613 = 945605) B945605
theorem B424529 : Blo 187803 424529 := bstep (se 2 (by rfl) ⟨159198, by rfl⟩ : syracuseStep 424529 = 318397) B318397
theorem B424547 : Blo 187803 424547 := bstep (se 1 (by rfl) ⟨318410, by rfl⟩ : syracuseStep 424547 = 636821) B636821
theorem B1080013 : Blo 187803 1080013 := bstep (se 3 (by rfl) ⟨202502, by rfl⟩ : syracuseStep 1080013 = 405005) B405005
theorem B424817 : Blo 187803 424817 := bstep (se 2 (by rfl) ⟨159306, by rfl⟩ : syracuseStep 424817 = 318613) B318613
theorem B424835 : Blo 187803 424835 := bstep (se 1 (by rfl) ⟨318626, by rfl⟩ : syracuseStep 424835 = 637253) B637253
theorem B490499 : Blo 187803 490499 := bstep (se 1 (by rfl) ⟨367874, by rfl⟩ : syracuseStep 490499 = 735749) B735749
theorem B359473 : Blo 187803 359473 := bstep (se 2 (by rfl) ⟨134802, by rfl⟩ : syracuseStep 359473 = 269605) B269605
theorem B425105 : Blo 187803 425105 := bstep (se 2 (by rfl) ⟨159414, by rfl⟩ : syracuseStep 425105 = 318829) B318829
theorem B425123 : Blo 187803 425123 := bstep (se 1 (by rfl) ⟨318842, by rfl⟩ : syracuseStep 425123 = 637685) B637685
theorem B359633 : Blo 187803 359633 := bstep (se 2 (by rfl) ⟨134862, by rfl⟩ : syracuseStep 359633 = 269725) B269725
theorem B818417 : Blo 187803 818417 := bstep (se 2 (by rfl) ⟨306906, by rfl⟩ : syracuseStep 818417 = 613813) B613813
theorem B228595 : Blo 187803 228595 := bstep (se 1 (by rfl) ⟨171446, by rfl⟩ : syracuseStep 228595 = 342893) B342893
theorem B425393 : Blo 187803 425393 := bstep (se 2 (by rfl) ⟨159522, by rfl⟩ : syracuseStep 425393 = 319045) B319045
theorem B425411 : Blo 187803 425411 := bstep (se 1 (by rfl) ⟨319058, by rfl⟩ : syracuseStep 425411 = 638117) B638117
theorem B1310179 : Blo 187803 1310179 := bstep (se 1 (by rfl) ⟨982634, by rfl⟩ : syracuseStep 1310179 = 1965269) B1965269
theorem B687629 : Blo 187803 687629 := bstep (se 3 (by rfl) ⟨128930, by rfl⟩ : syracuseStep 687629 = 257861) B257861
theorem B360035 : Blo 187803 360035 := bstep (se 1 (by rfl) ⟨270026, by rfl⟩ : syracuseStep 360035 = 540053) B540053
theorem B425681 : Blo 187803 425681 := bstep (se 2 (by rfl) ⟨159630, by rfl⟩ : syracuseStep 425681 = 319261) B319261
theorem B425699 : Blo 187803 425699 := bstep (se 1 (by rfl) ⟨319274, by rfl⟩ : syracuseStep 425699 = 638549) B638549
theorem B2817845 : Blo 187803 2817845 := bstep (se 5 (by rfl) ⟨132086, by rfl⟩ : syracuseStep 2817845 = 264173) B264173
theorem B327523 : Blo 187803 327523 := bstep (se 1 (by rfl) ⟨245642, by rfl⟩ : syracuseStep 327523 = 491285) B491285
theorem B229315 : Blo 187803 229315 := bstep (se 1 (by rfl) ⟨171986, by rfl⟩ : syracuseStep 229315 = 343973) B343973
theorem B720845 : Blo 187803 720845 := bstep (se 3 (by rfl) ⟨135158, by rfl⟩ : syracuseStep 720845 = 270317) B270317
theorem B425969 : Blo 187803 425969 := bstep (se 2 (by rfl) ⟨159738, by rfl⟩ : syracuseStep 425969 = 319477) B319477
theorem B426059 : Blo 187803 426059 := bstep (se 1 (by rfl) ⟨319544, by rfl⟩ : syracuseStep 426059 = 639089) B639089
theorem B426113 : Blo 187803 426113 := bstep (se 2 (by rfl) ⟨159792, by rfl⟩ : syracuseStep 426113 = 319585) B319585
theorem B983171 : Blo 187803 983171 := bstep (se 1 (by rfl) ⟨737378, by rfl⟩ : syracuseStep 983171 = 1474757) B1474757
theorem B459083 : Blo 187803 459083 := bstep (se 1 (by rfl) ⟨344312, by rfl⟩ : syracuseStep 459083 = 688625) B688625
theorem B426329 : Blo 187803 426329 := bstep (se 2 (by rfl) ⟨159873, by rfl⟩ : syracuseStep 426329 = 319747) B319747
theorem B426419 : Blo 187803 426419 := bstep (se 1 (by rfl) ⟨319814, by rfl⟩ : syracuseStep 426419 = 639629) B639629
theorem B721331 : Blo 187803 721331 := bstep (se 1 (by rfl) ⟨540998, by rfl⟩ : syracuseStep 721331 = 1081997) B1081997
theorem B721345 : Blo 187803 721345 := bstep (se 2 (by rfl) ⟨270504, by rfl⟩ : syracuseStep 721345 = 541009) B541009
theorem B426455 : Blo 187803 426455 := bstep (se 1 (by rfl) ⟨319841, by rfl⟩ : syracuseStep 426455 = 639683) B639683
theorem B393803 : Blo 187803 393803 := bstep (se 1 (by rfl) ⟨295352, by rfl⟩ : syracuseStep 393803 = 590705) B590705
theorem B426635 : Blo 187803 426635 := bstep (se 1 (by rfl) ⟨319976, by rfl⟩ : syracuseStep 426635 = 639953) B639953
theorem B426689 : Blo 187803 426689 := bstep (se 2 (by rfl) ⟨160008, by rfl⟩ : syracuseStep 426689 = 320017) B320017
theorem B1966913 : Blo 187803 1966913 := bstep (se 2 (by rfl) ⟨737592, by rfl⟩ : syracuseStep 1966913 = 1475185) B1475185
theorem B426905 : Blo 187803 426905 := bstep (se 2 (by rfl) ⟨160089, by rfl⟩ : syracuseStep 426905 = 320179) B320179
theorem B426995 : Blo 187803 426995 := bstep (se 1 (by rfl) ⟨320246, by rfl⟩ : syracuseStep 426995 = 640493) B640493
theorem B230411 : Blo 187803 230411 := bstep (se 1 (by rfl) ⟨172808, by rfl⟩ : syracuseStep 230411 = 345617) B345617
theorem B427031 : Blo 187803 427031 := bstep (se 1 (by rfl) ⟨320273, by rfl⟩ : syracuseStep 427031 = 640547) B640547
theorem B361523 : Blo 187803 361523 := bstep (se 1 (by rfl) ⟨271142, by rfl⟩ : syracuseStep 361523 = 542285) B542285
theorem B427211 : Blo 187803 427211 := bstep (se 1 (by rfl) ⟨320408, by rfl⟩ : syracuseStep 427211 = 640817) B640817
theorem B361675 : Blo 187803 361675 := bstep (se 1 (by rfl) ⟨271256, by rfl⟩ : syracuseStep 361675 = 542513) B542513
theorem B427265 : Blo 187803 427265 := bstep (se 2 (by rfl) ⟨160224, by rfl⟩ : syracuseStep 427265 = 320449) B320449
theorem B918935 : Blo 187803 918935 := bstep (se 1 (by rfl) ⟨689201, by rfl⟩ : syracuseStep 918935 = 1378403) B1378403
theorem B427481 : Blo 187803 427481 := bstep (se 2 (by rfl) ⟨160305, by rfl⟩ : syracuseStep 427481 = 320611) B320611
theorem B362009 : Blo 187803 362009 := bstep (se 2 (by rfl) ⟨135753, by rfl⟩ : syracuseStep 362009 = 271507) B271507
theorem B427571 : Blo 187803 427571 := bstep (se 1 (by rfl) ⟨320678, by rfl⟩ : syracuseStep 427571 = 641357) B641357
theorem B427607 : Blo 187803 427607 := bstep (se 1 (by rfl) ⟨320705, by rfl⟩ : syracuseStep 427607 = 641411) B641411
theorem B427787 : Blo 187803 427787 := bstep (se 1 (by rfl) ⟨320840, by rfl⟩ : syracuseStep 427787 = 641681) B641681
theorem B427841 : Blo 187803 427841 := bstep (se 2 (by rfl) ⟨160440, by rfl⟩ : syracuseStep 427841 = 320881) B320881
theorem B428057 : Blo 187803 428057 := bstep (se 2 (by rfl) ⟨160521, by rfl⟩ : syracuseStep 428057 = 321043) B321043
theorem B1443905 : Blo 187803 1443905 := bstep (se 2 (by rfl) ⟨541464, by rfl⟩ : syracuseStep 1443905 = 1082929) B1082929
theorem B428147 : Blo 187803 428147 := bstep (se 1 (by rfl) ⟨321110, by rfl⟩ : syracuseStep 428147 = 642221) B642221
theorem B1837187 : Blo 187803 1837187 := bstep (se 1 (by rfl) ⟨1377890, by rfl⟩ : syracuseStep 1837187 = 2755781) B2755781
theorem B428183 : Blo 187803 428183 := bstep (se 1 (by rfl) ⟨321137, by rfl⟩ : syracuseStep 428183 = 642275) B642275
theorem B362647 : Blo 187803 362647 := bstep (se 1 (by rfl) ⟨271985, by rfl⟩ : syracuseStep 362647 = 543971) B543971
theorem B919873 : Blo 187803 919873 := bstep (se 2 (by rfl) ⟨344952, by rfl⟩ : syracuseStep 919873 = 689905) B689905
theorem B428363 : Blo 187803 428363 := bstep (se 1 (by rfl) ⟨321272, by rfl⟩ : syracuseStep 428363 = 642545) B642545
theorem B723275 : Blo 187803 723275 := bstep (se 1 (by rfl) ⟨542456, by rfl⟩ : syracuseStep 723275 = 1084913) B1084913
theorem B723289 : Blo 187803 723289 := bstep (se 2 (by rfl) ⟨271233, by rfl⟩ : syracuseStep 723289 = 542467) B542467
theorem B428417 : Blo 187803 428417 := bstep (se 2 (by rfl) ⟨160656, by rfl⟩ : syracuseStep 428417 = 321313) B321313
theorem B428633 : Blo 187803 428633 := bstep (se 2 (by rfl) ⟨160737, by rfl⟩ : syracuseStep 428633 = 321475) B321475
theorem B428723 : Blo 187803 428723 := bstep (se 1 (by rfl) ⟨321542, by rfl⟩ : syracuseStep 428723 = 643085) B643085
theorem B428759 : Blo 187803 428759 := bstep (se 1 (by rfl) ⟨321569, by rfl⟩ : syracuseStep 428759 = 643139) B643139
theorem B690905 : Blo 187803 690905 := bstep (se 2 (by rfl) ⟨259089, by rfl⟩ : syracuseStep 690905 = 518179) B518179
theorem B1084205 : Blo 187803 1084205 := bstep (se 3 (by rfl) ⟨203288, by rfl⟩ : syracuseStep 1084205 = 406577) B406577
theorem B428939 : Blo 187803 428939 := bstep (se 1 (by rfl) ⟨321704, by rfl⟩ : syracuseStep 428939 = 643409) B643409
theorem B428993 : Blo 187803 428993 := bstep (se 2 (by rfl) ⟨160872, by rfl⟩ : syracuseStep 428993 = 321745) B321745
theorem B363467 : Blo 187803 363467 := bstep (se 1 (by rfl) ⟨272600, by rfl⟩ : syracuseStep 363467 = 545201) B545201
theorem B363521 : Blo 187803 363521 := bstep (se 2 (by rfl) ⟨136320, by rfl⟩ : syracuseStep 363521 = 272641) B272641
theorem B429131 : Blo 187803 429131 := bstep (se 1 (by rfl) ⟨321848, by rfl⟩ : syracuseStep 429131 = 643697) B643697
theorem B1838173 : Blo 187803 1838173 := bstep (se 3 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 1838173 = 689315) B689315
theorem B429209 : Blo 187803 429209 := bstep (se 2 (by rfl) ⟨160953, by rfl⟩ : syracuseStep 429209 = 321907) B321907
theorem B429299 : Blo 187803 429299 := bstep (se 1 (by rfl) ⟨321974, by rfl⟩ : syracuseStep 429299 = 643949) B643949
theorem B724247 : Blo 187803 724247 := bstep (se 1 (by rfl) ⟨543185, by rfl⟩ : syracuseStep 724247 = 1086371) B1086371
theorem B429335 : Blo 187803 429335 := bstep (se 1 (by rfl) ⟨322001, by rfl⟩ : syracuseStep 429335 = 644003) B644003
theorem B363865 : Blo 187803 363865 := bstep (se 2 (by rfl) ⟨136449, by rfl⟩ : syracuseStep 363865 = 272899) B272899
theorem B953693 : Blo 187803 953693 := bstep (se 3 (by rfl) ⟨178817, by rfl⟩ : syracuseStep 953693 = 357635) B357635
theorem B429515 : Blo 187803 429515 := bstep (se 1 (by rfl) ⟨322136, by rfl⟩ : syracuseStep 429515 = 644273) B644273
theorem B429569 : Blo 187803 429569 := bstep (se 2 (by rfl) ⟨161088, by rfl⟩ : syracuseStep 429569 = 322177) B322177
theorem B1216093 : Blo 187803 1216093 := bstep (se 3 (by rfl) ⟨228017, by rfl⟩ : syracuseStep 1216093 = 456035) B456035
theorem B429785 : Blo 187803 429785 := bstep (se 2 (by rfl) ⟨161169, by rfl⟩ : syracuseStep 429785 = 322339) B322339
theorem B429875 : Blo 187803 429875 := bstep (se 1 (by rfl) ⟨322406, by rfl⟩ : syracuseStep 429875 = 644813) B644813
theorem B429911 : Blo 187803 429911 := bstep (se 1 (by rfl) ⟨322433, by rfl⟩ : syracuseStep 429911 = 644867) B644867
theorem B429977 : Blo 187803 429977 := bstep (se 2 (by rfl) ⟨161241, by rfl⟩ : syracuseStep 429977 = 322483) B322483
theorem B1445849 : Blo 187803 1445849 := bstep (se 2 (by rfl) ⟨542193, by rfl⟩ : syracuseStep 1445849 = 1084387) B1084387
theorem B430091 : Blo 187803 430091 := bstep (se 1 (by rfl) ⟨322568, by rfl⟩ : syracuseStep 430091 = 645137) B645137
theorem B430145 : Blo 187803 430145 := bstep (se 2 (by rfl) ⟨161304, by rfl⟩ : syracuseStep 430145 = 322609) B322609
theorem B1380503 : Blo 187803 1380503 := bstep (se 1 (by rfl) ⟨1035377, by rfl⟩ : syracuseStep 1380503 = 2070755) B2070755
theorem B18583829 : Blo 187803 18583829 := bstep (se 6 (by rfl) ⟨435558, by rfl⟩ : syracuseStep 18583829 = 871117) B871117
theorem B430361 : Blo 187803 430361 := bstep (se 2 (by rfl) ⟨161385, by rfl⟩ : syracuseStep 430361 = 322771) B322771
theorem B430451 : Blo 187803 430451 := bstep (se 1 (by rfl) ⟨322838, by rfl⟩ : syracuseStep 430451 = 645677) B645677
theorem B430487 : Blo 187803 430487 := bstep (se 1 (by rfl) ⟨322865, by rfl⟩ : syracuseStep 430487 = 645731) B645731
theorem B725507 : Blo 187803 725507 := bstep (se 1 (by rfl) ⟨544130, by rfl⟩ : syracuseStep 725507 = 1088261) B1088261
theorem B430667 : Blo 187803 430667 := bstep (se 1 (by rfl) ⟨323000, by rfl⟩ : syracuseStep 430667 = 646001) B646001
theorem B856669 : Blo 187803 856669 := bstep (se 3 (by rfl) ⟨160625, by rfl⟩ : syracuseStep 856669 = 321251) B321251
theorem B430721 : Blo 187803 430721 := bstep (se 2 (by rfl) ⟨161520, by rfl⟩ : syracuseStep 430721 = 323041) B323041
theorem B430937 : Blo 187803 430937 := bstep (se 2 (by rfl) ⟨161601, by rfl⟩ : syracuseStep 430937 = 323203) B323203
theorem B431027 : Blo 187803 431027 := bstep (se 1 (by rfl) ⟨323270, by rfl⟩ : syracuseStep 431027 = 646541) B646541
theorem B431063 : Blo 187803 431063 := bstep (se 1 (by rfl) ⟨323297, by rfl⟩ : syracuseStep 431063 = 646595) B646595
theorem B431243 : Blo 187803 431243 := bstep (se 1 (by rfl) ⟨323432, by rfl⟩ : syracuseStep 431243 = 646865) B646865
theorem B431297 : Blo 187803 431297 := bstep (se 2 (by rfl) ⟨161736, by rfl⟩ : syracuseStep 431297 = 323473) B323473
theorem B693593 : Blo 187803 693593 := bstep (se 2 (by rfl) ⟨260097, by rfl⟩ : syracuseStep 693593 = 520195) B520195
theorem B202123 : Blo 187803 202123 := bstep (se 1 (by rfl) ⟨151592, by rfl⟩ : syracuseStep 202123 = 303185) B303185
theorem B12719501 : Blo 187803 12719501 := bstep (se 3 (by rfl) ⟨2384906, by rfl⟩ : syracuseStep 12719501 = 4769813) B4769813
theorem B955799 : Blo 187803 955799 := bstep (se 1 (by rfl) ⟨716849, by rfl⟩ : syracuseStep 955799 = 1433699) B1433699
theorem B431513 : Blo 187803 431513 := bstep (se 2 (by rfl) ⟨161817, by rfl⟩ : syracuseStep 431513 = 323635) B323635
theorem B431639 : Blo 187803 431639 := bstep (se 1 (by rfl) ⟨323729, by rfl⟩ : syracuseStep 431639 = 647459) B647459
theorem B464459 : Blo 187803 464459 := bstep (se 1 (by rfl) ⟨348344, by rfl⟩ : syracuseStep 464459 = 696689) B696689
theorem B1382093 : Blo 187803 1382093 := bstep (se 3 (by rfl) ⟨259142, by rfl⟩ : syracuseStep 1382093 = 518285) B518285
theorem B1382321 : Blo 187803 1382321 := bstep (se 2 (by rfl) ⟨518370, by rfl⟩ : syracuseStep 1382321 = 1036741) B1036741
theorem B268363 : Blo 187803 268363 := bstep (se 1 (by rfl) ⟨201272, by rfl⟩ : syracuseStep 268363 = 402545) B402545
theorem B268375 : Blo 187803 268375 := bstep (se 1 (by rfl) ⟨201281, by rfl⟩ : syracuseStep 268375 = 402563) B402563
theorem B2038193 : Blo 187803 2038193 := bstep (se 2 (by rfl) ⟨764322, by rfl⟩ : syracuseStep 2038193 = 1528645) B1528645
theorem B432641 : Blo 187803 432641 := bstep (se 2 (by rfl) ⟨162240, by rfl⟩ : syracuseStep 432641 = 324481) B324481
theorem B203639 : Blo 187803 203639 := bstep (se 1 (by rfl) ⟨152729, by rfl⟩ : syracuseStep 203639 = 305459) B305459
theorem B1449251 : Blo 187803 1449251 := bstep (se 1 (by rfl) ⟨1086938, by rfl⟩ : syracuseStep 1449251 = 2173877) B2173877
theorem B204331 : Blo 187803 204331 := bstep (se 1 (by rfl) ⟨153248, by rfl⟩ : syracuseStep 204331 = 306497) B306497
theorem B1023961 : Blo 187803 1023961 := bstep (se 2 (by rfl) ⟨383985, by rfl⟩ : syracuseStep 1023961 = 767971) B767971
theorem B270425 : Blo 187803 270425 := bstep (se 2 (by rfl) ⟨101409, by rfl⟩ : syracuseStep 270425 = 202819) B202819
theorem B401537 : Blo 187803 401537 := bstep (se 2 (by rfl) ⟨150576, by rfl⟩ : syracuseStep 401537 = 301153) B301153
theorem B761987 : Blo 187803 761987 := bstep (se 1 (by rfl) ⟨571490, by rfl⟩ : syracuseStep 761987 = 1142981) B1142981
theorem B1220939 : Blo 187803 1220939 := bstep (se 1 (by rfl) ⟨915704, by rfl⟩ : syracuseStep 1220939 = 1831409) B1831409
theorem B303563 : Blo 187803 303563 := bstep (se 1 (by rfl) ⟨227672, by rfl⟩ : syracuseStep 303563 = 455345) B455345
theorem B402059 : Blo 187803 402059 := bstep (se 1 (by rfl) ⟨301544, by rfl⟩ : syracuseStep 402059 = 603089) B603089
theorem B238231 : Blo 187803 238231 := bstep (se 1 (by rfl) ⟨178673, by rfl⟩ : syracuseStep 238231 = 357347) B357347
theorem B1548977 : Blo 187803 1548977 := bstep (se 2 (by rfl) ⟨580866, by rfl⟩ : syracuseStep 1548977 = 1161733) B1161733
theorem B271063 : Blo 187803 271063 := bstep (se 1 (by rfl) ⟨203297, by rfl⟩ : syracuseStep 271063 = 406595) B406595
theorem B303959 : Blo 187803 303959 := bstep (se 1 (by rfl) ⟨227969, by rfl⟩ : syracuseStep 303959 = 455939) B455939
theorem B959363 : Blo 187803 959363 := bstep (se 1 (by rfl) ⟨719522, by rfl⟩ : syracuseStep 959363 = 1439045) B1439045
theorem B205751 : Blo 187803 205751 := bstep (se 1 (by rfl) ⟨154313, by rfl⟩ : syracuseStep 205751 = 308627) B308627
theorem B1156531 : Blo 187803 1156531 := bstep (se 1 (by rfl) ⟨867398, by rfl⟩ : syracuseStep 1156531 = 1734797) B1734797
theorem B239051 : Blo 187803 239051 := bstep (se 1 (by rfl) ⟨179288, by rfl⟩ : syracuseStep 239051 = 358577) B358577
theorem B304651 : Blo 187803 304651 := bstep (se 1 (by rfl) ⟨228488, by rfl⟩ : syracuseStep 304651 = 456977) B456977
theorem B271883 : Blo 187803 271883 := bstep (se 1 (by rfl) ⟨203912, by rfl⟩ : syracuseStep 271883 = 407825) B407825
theorem B304793 : Blo 187803 304793 := bstep (se 2 (by rfl) ⟨114297, by rfl⟩ : syracuseStep 304793 = 228595) B228595
theorem B1681075 : Blo 187803 1681075 := bstep (se 1 (by rfl) ⟨1260806, by rfl⟩ : syracuseStep 1681075 = 2521613) B2521613
theorem B861997 : Blo 187803 861997 := bstep (se 3 (by rfl) ⟨161624, by rfl⟩ : syracuseStep 861997 = 323249) B323249
theorem B403289 : Blo 187803 403289 := bstep (se 2 (by rfl) ⟨151233, by rfl⟩ : syracuseStep 403289 = 302467) B302467
theorem B1746905 : Blo 187803 1746905 := bstep (se 2 (by rfl) ⟨655089, by rfl⟩ : syracuseStep 1746905 = 1310179) B1310179
theorem B1091677 : Blo 187803 1091677 := bstep (se 3 (by rfl) ⟨204689, by rfl⟩ : syracuseStep 1091677 = 409379) B409379
theorem B239755 : Blo 187803 239755 := bstep (se 1 (by rfl) ⟨179816, by rfl⟩ : syracuseStep 239755 = 359633) B359633
theorem B403699 : Blo 187803 403699 := bstep (se 1 (by rfl) ⟨302774, by rfl⟩ : syracuseStep 403699 = 605549) B605549
theorem B240023 : Blo 187803 240023 := bstep (se 1 (by rfl) ⟨180017, by rfl⟩ : syracuseStep 240023 = 360035) B360035
theorem B436697 : Blo 187803 436697 := bstep (se 2 (by rfl) ⟨163761, by rfl⟩ : syracuseStep 436697 = 327523) B327523
theorem B1878563 : Blo 187803 1878563 := bstep (se 1 (by rfl) ⟨1408922, by rfl⟩ : syracuseStep 1878563 = 2817845) B2817845
theorem B305753 : Blo 187803 305753 := bstep (se 2 (by rfl) ⟨114657, by rfl⟩ : syracuseStep 305753 = 229315) B229315
theorem B404185 : Blo 187803 404185 := bstep (se 2 (by rfl) ⟨151569, by rfl⟩ : syracuseStep 404185 = 303139) B303139
theorem B928529 : Blo 187803 928529 := bstep (se 2 (by rfl) ⟨348198, by rfl⟩ : syracuseStep 928529 = 696397) B696397
theorem B273227 : Blo 187803 273227 := bstep (se 1 (by rfl) ⟨204920, by rfl⟩ : syracuseStep 273227 = 409841) B409841
theorem B1223525 : Blo 187803 1223525 := bstep (se 4 (by rfl) ⟨114705, by rfl⟩ : syracuseStep 1223525 = 229411) B229411
theorem B240727 : Blo 187803 240727 := bstep (se 1 (by rfl) ⟨180545, by rfl⟩ : syracuseStep 240727 = 361091) B361091
theorem B765101 : Blo 187803 765101 := bstep (se 3 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 765101 = 286913) B286913
theorem B863435 : Blo 187803 863435 := bstep (se 1 (by rfl) ⟨647576, by rfl⟩ : syracuseStep 863435 = 1295153) B1295153
theorem B339187 : Blo 187803 339187 := bstep (se 1 (by rfl) ⟨254390, by rfl⟩ : syracuseStep 339187 = 508781) B508781
theorem B1027403 : Blo 187803 1027403 := bstep (se 1 (by rfl) ⟨770552, by rfl⟩ : syracuseStep 1027403 = 1541105) B1541105
theorem B208279 : Blo 187803 208279 := bstep (se 1 (by rfl) ⟨156209, by rfl⟩ : syracuseStep 208279 = 312419) B312419
theorem B404929 : Blo 187803 404929 := bstep (se 2 (by rfl) ⟨151848, by rfl⟩ : syracuseStep 404929 = 303697) B303697
theorem B2731481 : Blo 187803 2731481 := bstep (se 2 (by rfl) ⟨1024305, by rfl⟩ : syracuseStep 2731481 = 2048611) B2048611
theorem B634391 : Blo 187803 634391 := bstep (se 1 (by rfl) ⟨475793, by rfl⟩ : syracuseStep 634391 = 951587) B951587
theorem B503347 : Blo 187803 503347 := bstep (se 1 (by rfl) ⟨377510, by rfl⟩ : syracuseStep 503347 = 755021) B755021
theorem B339763 : Blo 187803 339763 := bstep (se 1 (by rfl) ⟨254822, by rfl⟩ : syracuseStep 339763 = 509645) B509645
theorem B601921 : Blo 187803 601921 := bstep (se 2 (by rfl) ⟨225720, by rfl⟩ : syracuseStep 601921 = 451441) B451441
theorem B634931 : Blo 187803 634931 := bstep (se 1 (by rfl) ⟨476198, by rfl⟩ : syracuseStep 634931 = 952397) B952397
theorem B798893 : Blo 187803 798893 := bstep (se 3 (by rfl) ⟨149792, by rfl⟩ : syracuseStep 798893 = 299585) B299585
theorem B635201 : Blo 187803 635201 := bstep (se 2 (by rfl) ⟨238200, by rfl⟩ : syracuseStep 635201 = 476401) B476401
theorem B405911 : Blo 187803 405911 := bstep (se 1 (by rfl) ⟨304433, by rfl⟩ : syracuseStep 405911 = 608867) B608867
theorem B1454597 : Blo 187803 1454597 := bstep (se 4 (by rfl) ⟨136368, by rfl⟩ : syracuseStep 1454597 = 272737) B272737
theorem B3617297 : Blo 187803 3617297 := bstep (se 2 (by rfl) ⟨1356486, by rfl⟩ : syracuseStep 3617297 = 2712973) B2712973
theorem B963089 : Blo 187803 963089 := bstep (se 2 (by rfl) ⟨361158, by rfl⟩ : syracuseStep 963089 = 722317) B722317
theorem B963251 : Blo 187803 963251 := bstep (se 1 (by rfl) ⟨722438, by rfl⟩ : syracuseStep 963251 = 1444877) B1444877
theorem B6861509 : Blo 187803 6861509 := bstep (se 4 (by rfl) ⟨643266, by rfl⟩ : syracuseStep 6861509 = 1286533) B1286533
theorem B242443 : Blo 187803 242443 := bstep (se 1 (by rfl) ⟨181832, by rfl⟩ : syracuseStep 242443 = 363665) B363665
theorem B635741 : Blo 187803 635741 := bstep (se 3 (by rfl) ⟨119201, by rfl⟩ : syracuseStep 635741 = 238403) B238403
theorem B406475 : Blo 187803 406475 := bstep (se 1 (by rfl) ⟨304856, by rfl⟩ : syracuseStep 406475 = 609713) B609713
theorem B341377 : Blo 187803 341377 := bstep (se 2 (by rfl) ⟨128016, by rfl⟩ : syracuseStep 341377 = 256033) B256033
theorem B406937 : Blo 187803 406937 := bstep (se 2 (by rfl) ⟨152601, by rfl⟩ : syracuseStep 406937 = 305203) B305203
theorem B1553843 : Blo 187803 1553843 := bstep (se 1 (by rfl) ⟨1165382, by rfl⟩ : syracuseStep 1553843 = 2330765) B2330765
theorem B1619473 : Blo 187803 1619473 := bstep (se 2 (by rfl) ⟨607302, by rfl⟩ : syracuseStep 1619473 = 1214605) B1214605
theorem B1619747 : Blo 187803 1619747 := bstep (se 1 (by rfl) ⟨1214810, by rfl⟩ : syracuseStep 1619747 = 2429621) B2429621
theorem B636875 : Blo 187803 636875 := bstep (se 1 (by rfl) ⟨477656, by rfl⟩ : syracuseStep 636875 = 955313) B955313
theorem B15677509 : Blo 187803 15677509 := bstep (se 4 (by rfl) ⟨1469766, by rfl⟩ : syracuseStep 15677509 = 2939533) B2939533
theorem B637145 : Blo 187803 637145 := bstep (se 2 (by rfl) ⟨238929, by rfl⟩ : syracuseStep 637145 = 477859) B477859
theorem B3258629 : Blo 187803 3258629 := bstep (se 4 (by rfl) ⟨305496, by rfl⟩ : syracuseStep 3258629 = 610993) B610993
theorem B211351 : Blo 187803 211351 := bstep (se 1 (by rfl) ⟨158513, by rfl⟩ : syracuseStep 211351 = 317027) B317027
theorem B408115 : Blo 187803 408115 := bstep (se 1 (by rfl) ⟨306086, by rfl⟩ : syracuseStep 408115 = 612173) B612173
theorem B211531 : Blo 187803 211531 := bstep (se 1 (by rfl) ⟨158648, by rfl⟩ : syracuseStep 211531 = 317297) B317297
theorem B965195 : Blo 187803 965195 := bstep (se 1 (by rfl) ⟨723896, by rfl⟩ : syracuseStep 965195 = 1447793) B1447793
theorem B211639 : Blo 187803 211639 := bstep (se 1 (by rfl) ⟨158729, by rfl⟩ : syracuseStep 211639 = 317459) B317459
theorem B211819 : Blo 187803 211819 := bstep (se 1 (by rfl) ⟨158864, by rfl⟩ : syracuseStep 211819 = 317729) B317729
theorem B637847 : Blo 187803 637847 := bstep (se 1 (by rfl) ⟨478385, by rfl⟩ : syracuseStep 637847 = 956771) B956771
theorem B211927 : Blo 187803 211927 := bstep (se 1 (by rfl) ⟨158945, by rfl⟩ : syracuseStep 211927 = 317891) B317891
theorem B3685337 : Blo 187803 3685337 := bstep (se 2 (by rfl) ⟨1382001, by rfl⟩ : syracuseStep 3685337 = 2764003) B2764003
theorem B408577 : Blo 187803 408577 := bstep (se 2 (by rfl) ⟨153216, by rfl⟩ : syracuseStep 408577 = 306433) B306433
theorem B2735117 : Blo 187803 2735117 := bstep (se 3 (by rfl) ⟨512834, by rfl⟩ : syracuseStep 2735117 = 1025669) B1025669
theorem B539723 : Blo 187803 539723 := bstep (se 1 (by rfl) ⟨404792, by rfl⟩ : syracuseStep 539723 = 809585) B809585
theorem B212107 : Blo 187803 212107 := bstep (se 1 (by rfl) ⟨159080, by rfl⟩ : syracuseStep 212107 = 318161) B318161
theorem B212215 : Blo 187803 212215 := bstep (se 1 (by rfl) ⟨159161, by rfl⟩ : syracuseStep 212215 = 318323) B318323
theorem B212395 : Blo 187803 212395 := bstep (se 1 (by rfl) ⟨159296, by rfl⟩ : syracuseStep 212395 = 318593) B318593
theorem B1359281 : Blo 187803 1359281 := bstep (se 2 (by rfl) ⟨509730, by rfl⟩ : syracuseStep 1359281 = 1019461) B1019461
theorem B638387 : Blo 187803 638387 := bstep (se 1 (by rfl) ⟨478790, by rfl⟩ : syracuseStep 638387 = 957581) B957581
theorem B540121 : Blo 187803 540121 := bstep (se 2 (by rfl) ⟨202545, by rfl⟩ : syracuseStep 540121 = 405091) B405091
theorem B212503 : Blo 187803 212503 := bstep (se 1 (by rfl) ⟨159377, by rfl⟩ : syracuseStep 212503 = 318755) B318755
theorem B638657 : Blo 187803 638657 := bstep (se 2 (by rfl) ⟨239496, by rfl⟩ : syracuseStep 638657 = 478993) B478993
theorem B212683 : Blo 187803 212683 := bstep (se 1 (by rfl) ⟨159512, by rfl⟩ : syracuseStep 212683 = 319025) B319025
theorem B3096269 : Blo 187803 3096269 := bstep (se 3 (by rfl) ⟨580550, by rfl⟩ : syracuseStep 3096269 = 1161101) B1161101
theorem B409303 : Blo 187803 409303 := bstep (se 1 (by rfl) ⟨306977, by rfl⟩ : syracuseStep 409303 = 613955) B613955
theorem B212791 : Blo 187803 212791 := bstep (se 1 (by rfl) ⟨159593, by rfl⟩ : syracuseStep 212791 = 319187) B319187
theorem B769985 : Blo 187803 769985 := bstep (se 2 (by rfl) ⟨288744, by rfl⟩ : syracuseStep 769985 = 577489) B577489
theorem B212971 : Blo 187803 212971 := bstep (se 1 (by rfl) ⟨159728, by rfl⟩ : syracuseStep 212971 = 319457) B319457
theorem B213079 : Blo 187803 213079 := bstep (se 1 (by rfl) ⟨159809, by rfl⟩ : syracuseStep 213079 = 319619) B319619
theorem B639197 : Blo 187803 639197 := bstep (se 3 (by rfl) ⟨119849, by rfl⟩ : syracuseStep 639197 = 239699) B239699
theorem B213259 : Blo 187803 213259 := bstep (se 1 (by rfl) ⟨159944, by rfl⟩ : syracuseStep 213259 = 319889) B319889
theorem B966977 : Blo 187803 966977 := bstep (se 2 (by rfl) ⟨362616, by rfl⟩ : syracuseStep 966977 = 725233) B725233
theorem B213367 : Blo 187803 213367 := bstep (se 1 (by rfl) ⟨160025, by rfl⟩ : syracuseStep 213367 = 320051) B320051
theorem B344449 : Blo 187803 344449 := bstep (se 2 (by rfl) ⟨129168, by rfl⟩ : syracuseStep 344449 = 258337) B258337
theorem B475571 : Blo 187803 475571 := bstep (se 1 (by rfl) ⟨356678, by rfl⟩ : syracuseStep 475571 = 713357) B713357
theorem B213547 : Blo 187803 213547 := bstep (se 1 (by rfl) ⟨160160, by rfl⟩ : syracuseStep 213547 = 320321) B320321
theorem B344665 : Blo 187803 344665 := bstep (se 2 (by rfl) ⟨129249, by rfl⟩ : syracuseStep 344665 = 258499) B258499
theorem B213655 : Blo 187803 213655 := bstep (se 1 (by rfl) ⟨160241, by rfl⟩ : syracuseStep 213655 = 320483) B320483
theorem B541363 : Blo 187803 541363 := bstep (se 1 (by rfl) ⟨406022, by rfl⟩ : syracuseStep 541363 = 812045) B812045
theorem B475865 : Blo 187803 475865 := bstep (se 2 (by rfl) ⟨178449, by rfl⟩ : syracuseStep 475865 = 356899) B356899
theorem B1164077 : Blo 187803 1164077 := bstep (se 3 (by rfl) ⟨218264, by rfl⟩ : syracuseStep 1164077 = 436529) B436529
theorem B213835 : Blo 187803 213835 := bstep (se 1 (by rfl) ⟨160376, by rfl⟩ : syracuseStep 213835 = 320753) B320753
theorem B213943 : Blo 187803 213943 := bstep (se 1 (by rfl) ⟨160457, by rfl⟩ : syracuseStep 213943 = 320915) B320915
theorem B214123 : Blo 187803 214123 := bstep (se 1 (by rfl) ⟨160592, by rfl⟩ : syracuseStep 214123 = 321185) B321185
theorem B214231 : Blo 187803 214231 := bstep (se 1 (by rfl) ⟨160673, by rfl⟩ : syracuseStep 214231 = 321347) B321347
theorem B640331 : Blo 187803 640331 := bstep (se 1 (by rfl) ⟨480248, by rfl⟩ : syracuseStep 640331 = 960497) B960497
theorem B214411 : Blo 187803 214411 := bstep (se 1 (by rfl) ⟨160808, by rfl⟩ : syracuseStep 214411 = 321617) B321617
theorem B804269 : Blo 187803 804269 := bstep (se 3 (by rfl) ⟨150800, by rfl⟩ : syracuseStep 804269 = 301601) B301601
theorem B1361357 : Blo 187803 1361357 := bstep (se 3 (by rfl) ⟨255254, by rfl⟩ : syracuseStep 1361357 = 510509) B510509
theorem B214519 : Blo 187803 214519 := bstep (se 1 (by rfl) ⟨160889, by rfl⟩ : syracuseStep 214519 = 321779) B321779
theorem B640601 : Blo 187803 640601 := bstep (se 2 (by rfl) ⟨240225, by rfl⟩ : syracuseStep 640601 = 480451) B480451
theorem B214699 : Blo 187803 214699 := bstep (se 1 (by rfl) ⟨161024, by rfl⟩ : syracuseStep 214699 = 322049) B322049
theorem B542387 : Blo 187803 542387 := bstep (se 1 (by rfl) ⟨406790, by rfl⟩ : syracuseStep 542387 = 813581) B813581
theorem B214807 : Blo 187803 214807 := bstep (se 1 (by rfl) ⟨161105, by rfl⟩ : syracuseStep 214807 = 322211) B322211
theorem B575383 : Blo 187803 575383 := bstep (se 1 (by rfl) ⟨431537, by rfl⟩ : syracuseStep 575383 = 863075) B863075
theorem B673687 : Blo 187803 673687 := bstep (se 1 (by rfl) ⟨505265, by rfl⟩ : syracuseStep 673687 = 1010531) B1010531
theorem B214987 : Blo 187803 214987 := bstep (se 1 (by rfl) ⟨161240, by rfl⟩ : syracuseStep 214987 = 322481) B322481
theorem B215095 : Blo 187803 215095 := bstep (se 1 (by rfl) ⟨161321, by rfl⟩ : syracuseStep 215095 = 322643) B322643
theorem B804953 : Blo 187803 804953 := bstep (se 2 (by rfl) ⟨301857, by rfl⟩ : syracuseStep 804953 = 603715) B603715
theorem B968921 : Blo 187803 968921 := bstep (se 2 (by rfl) ⟨363345, by rfl⟩ : syracuseStep 968921 = 726691) B726691
theorem B215275 : Blo 187803 215275 := bstep (se 1 (by rfl) ⟨161456, by rfl⟩ : syracuseStep 215275 = 322913) B322913
theorem B641303 : Blo 187803 641303 := bstep (se 1 (by rfl) ⟨480977, by rfl⟩ : syracuseStep 641303 = 961955) B961955
theorem B477515 : Blo 187803 477515 := bstep (se 1 (by rfl) ⟨358136, by rfl⟩ : syracuseStep 477515 = 716273) B716273
theorem B215383 : Blo 187803 215383 := bstep (se 1 (by rfl) ⟨161537, by rfl⟩ : syracuseStep 215383 = 323075) B323075
theorem B215563 : Blo 187803 215563 := bstep (se 1 (by rfl) ⟨161672, by rfl⟩ : syracuseStep 215563 = 323345) B323345
theorem B215671 : Blo 187803 215671 := bstep (se 1 (by rfl) ⟨161753, by rfl⟩ : syracuseStep 215671 = 323507) B323507
theorem B641843 : Blo 187803 641843 := bstep (se 1 (by rfl) ⟨481382, by rfl⟩ : syracuseStep 641843 = 962765) B962765
theorem B642113 : Blo 187803 642113 := bstep (se 2 (by rfl) ⟨240792, by rfl⟩ : syracuseStep 642113 = 481585) B481585
theorem B281753 : Blo 187803 281753 := bstep (se 2 (by rfl) ⟨105657, by rfl⟩ : syracuseStep 281753 = 211315) B211315
theorem B281867 : Blo 187803 281867 := bstep (se 1 (by rfl) ⟨211400, by rfl⟩ : syracuseStep 281867 = 422801) B422801
theorem B281879 : Blo 187803 281879 := bstep (se 1 (by rfl) ⟨211409, by rfl⟩ : syracuseStep 281879 = 422819) B422819
theorem B478487 : Blo 187803 478487 := bstep (se 1 (by rfl) ⟨358865, by rfl⟩ : syracuseStep 478487 = 717731) B717731
theorem B806219 : Blo 187803 806219 := bstep (se 1 (by rfl) ⟨604664, by rfl⟩ : syracuseStep 806219 = 1209329) B1209329
theorem B281945 : Blo 187803 281945 := bstep (se 2 (by rfl) ⟨105729, by rfl⟩ : syracuseStep 281945 = 211459) B211459
theorem B282059 : Blo 187803 282059 := bstep (se 1 (by rfl) ⟨211544, by rfl⟩ : syracuseStep 282059 = 423089) B423089
theorem B282071 : Blo 187803 282071 := bstep (se 1 (by rfl) ⟨211553, by rfl⟩ : syracuseStep 282071 = 423107) B423107
theorem B544279 : Blo 187803 544279 := bstep (se 1 (by rfl) ⟨408209, by rfl⟩ : syracuseStep 544279 = 816419) B816419
theorem B282137 : Blo 187803 282137 := bstep (se 2 (by rfl) ⟨105801, by rfl⟩ : syracuseStep 282137 = 211603) B211603
theorem B1363549 : Blo 187803 1363549 := bstep (se 3 (by rfl) ⟨255665, by rfl⟩ : syracuseStep 1363549 = 511331) B511331
theorem B642653 : Blo 187803 642653 := bstep (se 3 (by rfl) ⟨120497, by rfl⟩ : syracuseStep 642653 = 240995) B240995
theorem B282251 : Blo 187803 282251 := bstep (se 1 (by rfl) ⟨211688, by rfl⟩ : syracuseStep 282251 = 423377) B423377
theorem B282263 : Blo 187803 282263 := bstep (se 1 (by rfl) ⟨211697, by rfl⟩ : syracuseStep 282263 = 423395) B423395
theorem B806593 : Blo 187803 806593 := bstep (se 2 (by rfl) ⟨302472, by rfl⟩ : syracuseStep 806593 = 604945) B604945
theorem B282329 : Blo 187803 282329 := bstep (se 2 (by rfl) ⟨105873, by rfl⟩ : syracuseStep 282329 = 211747) B211747
theorem B970541 : Blo 187803 970541 := bstep (se 3 (by rfl) ⟨181976, by rfl⟩ : syracuseStep 970541 = 363953) B363953
theorem B282443 : Blo 187803 282443 := bstep (se 1 (by rfl) ⟨211832, by rfl⟩ : syracuseStep 282443 = 423665) B423665
theorem B282455 : Blo 187803 282455 := bstep (se 1 (by rfl) ⟨211841, by rfl⟩ : syracuseStep 282455 = 423683) B423683
theorem B2576245 : Blo 187803 2576245 := bstep (se 5 (by rfl) ⟨120761, by rfl⟩ : syracuseStep 2576245 = 241523) B241523
theorem B905111 : Blo 187803 905111 := bstep (se 1 (by rfl) ⟨678833, by rfl⟩ : syracuseStep 905111 = 1357667) B1357667
theorem B282521 : Blo 187803 282521 := bstep (se 2 (by rfl) ⟨105945, by rfl⟩ : syracuseStep 282521 = 211891) B211891
theorem B479155 : Blo 187803 479155 := bstep (se 1 (by rfl) ⟨359366, by rfl⟩ : syracuseStep 479155 = 718733) B718733
theorem B282635 : Blo 187803 282635 := bstep (se 1 (by rfl) ⟨211976, by rfl⟩ : syracuseStep 282635 = 423953) B423953
theorem B282647 : Blo 187803 282647 := bstep (se 1 (by rfl) ⟨211985, by rfl⟩ : syracuseStep 282647 = 423971) B423971
theorem B806935 : Blo 187803 806935 := bstep (se 1 (by rfl) ⟨605201, by rfl⟩ : syracuseStep 806935 = 1210403) B1210403
theorem B479297 : Blo 187803 479297 := bstep (se 2 (by rfl) ⟨179736, by rfl⟩ : syracuseStep 479297 = 359473) B359473
theorem B610379 : Blo 187803 610379 := bstep (se 1 (by rfl) ⟨457784, by rfl⟩ : syracuseStep 610379 = 915569) B915569
theorem B282713 : Blo 187803 282713 := bstep (se 2 (by rfl) ⟨106017, by rfl⟩ : syracuseStep 282713 = 212035) B212035
theorem B872579 : Blo 187803 872579 := bstep (se 1 (by rfl) ⟨654434, by rfl⟩ : syracuseStep 872579 = 1308869) B1308869
theorem B282827 : Blo 187803 282827 := bstep (se 1 (by rfl) ⟨212120, by rfl⟩ : syracuseStep 282827 = 424241) B424241
theorem B610507 : Blo 187803 610507 := bstep (se 1 (by rfl) ⟨457880, by rfl⟩ : syracuseStep 610507 = 915761) B915761
theorem B282839 : Blo 187803 282839 := bstep (se 1 (by rfl) ⟨212129, by rfl⟩ : syracuseStep 282839 = 424259) B424259
theorem B2937073 : Blo 187803 2937073 := bstep (se 2 (by rfl) ⟨1101402, by rfl⟩ : syracuseStep 2937073 = 2202805) B2202805
theorem B610583 : Blo 187803 610583 := bstep (se 1 (by rfl) ⟨457937, by rfl⟩ : syracuseStep 610583 = 915875) B915875
theorem B282905 : Blo 187803 282905 := bstep (se 2 (by rfl) ⟨106089, by rfl⟩ : syracuseStep 282905 = 212179) B212179
theorem B283019 : Blo 187803 283019 := bstep (se 1 (by rfl) ⟨212264, by rfl⟩ : syracuseStep 283019 = 424529) B424529
theorem B283031 : Blo 187803 283031 := bstep (se 1 (by rfl) ⟨212273, by rfl⟩ : syracuseStep 283031 = 424547) B424547
theorem B905651 : Blo 187803 905651 := bstep (se 1 (by rfl) ⟨679238, by rfl⟩ : syracuseStep 905651 = 1358477) B1358477
theorem B283097 : Blo 187803 283097 := bstep (se 2 (by rfl) ⟨106161, by rfl⟩ : syracuseStep 283097 = 212323) B212323
theorem B283211 : Blo 187803 283211 := bstep (se 1 (by rfl) ⟨212408, by rfl⟩ : syracuseStep 283211 = 424817) B424817
theorem B283223 : Blo 187803 283223 := bstep (se 1 (by rfl) ⟨212417, by rfl⟩ : syracuseStep 283223 = 424835) B424835
theorem B283289 : Blo 187803 283289 := bstep (se 2 (by rfl) ⟨106233, by rfl⟩ : syracuseStep 283289 = 212467) B212467
theorem B643787 : Blo 187803 643787 := bstep (se 1 (by rfl) ⟨482840, by rfl⟩ : syracuseStep 643787 = 965681) B965681
theorem B283403 : Blo 187803 283403 := bstep (se 1 (by rfl) ⟨212552, by rfl⟩ : syracuseStep 283403 = 425105) B425105
theorem B283415 : Blo 187803 283415 := bstep (se 1 (by rfl) ⟨212561, by rfl⟩ : syracuseStep 283415 = 425123) B425123
theorem B545611 : Blo 187803 545611 := bstep (se 1 (by rfl) ⟨409208, by rfl⟩ : syracuseStep 545611 = 818417) B818417
theorem B283481 : Blo 187803 283481 := bstep (se 2 (by rfl) ⟨106305, by rfl⟩ : syracuseStep 283481 = 212611) B212611
theorem B283595 : Blo 187803 283595 := bstep (se 1 (by rfl) ⟨212696, by rfl⟩ : syracuseStep 283595 = 425393) B425393
theorem B283607 : Blo 187803 283607 := bstep (se 1 (by rfl) ⟨212705, by rfl⟩ : syracuseStep 283607 = 425411) B425411
theorem B644057 : Blo 187803 644057 := bstep (se 2 (by rfl) ⟨241521, by rfl⟩ : syracuseStep 644057 = 483043) B483043
theorem B283673 : Blo 187803 283673 := bstep (se 2 (by rfl) ⟨106377, by rfl⟩ : syracuseStep 283673 = 212755) B212755
theorem B545885 : Blo 187803 545885 := bstep (se 3 (by rfl) ⟨102353, by rfl⟩ : syracuseStep 545885 = 204707) B204707
theorem B283787 : Blo 187803 283787 := bstep (se 1 (by rfl) ⟨212840, by rfl⟩ : syracuseStep 283787 = 425681) B425681
theorem B283799 : Blo 187803 283799 := bstep (se 1 (by rfl) ⟨212849, by rfl⟩ : syracuseStep 283799 = 425699) B425699
theorem B283865 : Blo 187803 283865 := bstep (se 2 (by rfl) ⟨106449, by rfl⟩ : syracuseStep 283865 = 212899) B212899
theorem B480563 : Blo 187803 480563 := bstep (se 1 (by rfl) ⟨360422, by rfl⟩ : syracuseStep 480563 = 720845) B720845
theorem B283979 : Blo 187803 283979 := bstep (se 1 (by rfl) ⟨212984, by rfl⟩ : syracuseStep 283979 = 425969) B425969
theorem B283991 : Blo 187803 283991 := bstep (se 1 (by rfl) ⟨212993, by rfl⟩ : syracuseStep 283991 = 425987) B425987
theorem B284057 : Blo 187803 284057 := bstep (se 2 (by rfl) ⟨106521, by rfl⟩ : syracuseStep 284057 = 213043) B213043
theorem B644573 : Blo 187803 644573 := bstep (se 3 (by rfl) ⟨120857, by rfl⟩ : syracuseStep 644573 = 241715) B241715
theorem B316939 : Blo 187803 316939 := bstep (se 1 (by rfl) ⟨237704, by rfl⟩ : syracuseStep 316939 = 475409) B475409
theorem B284171 : Blo 187803 284171 := bstep (se 1 (by rfl) ⟨213128, by rfl⟩ : syracuseStep 284171 = 426257) B426257
theorem B677393 : Blo 187803 677393 := bstep (se 2 (by rfl) ⟨254022, by rfl⟩ : syracuseStep 677393 = 508045) B508045
theorem B284183 : Blo 187803 284183 := bstep (se 1 (by rfl) ⟨213137, by rfl⟩ : syracuseStep 284183 = 426275) B426275
theorem B284249 : Blo 187803 284249 := bstep (se 2 (by rfl) ⟨106593, by rfl⟩ : syracuseStep 284249 = 213187) B213187
theorem B644759 : Blo 187803 644759 := bstep (se 1 (by rfl) ⟨483569, by rfl⟩ : syracuseStep 644759 = 967139) B967139
theorem B317081 : Blo 187803 317081 := bstep (se 2 (by rfl) ⟨118905, by rfl⟩ : syracuseStep 317081 = 237811) B237811
theorem B284363 : Blo 187803 284363 := bstep (se 1 (by rfl) ⟨213272, by rfl⟩ : syracuseStep 284363 = 426545) B426545
theorem B4085453 : Blo 187803 4085453 := bstep (se 3 (by rfl) ⟨766022, by rfl⟩ : syracuseStep 4085453 = 1532045) B1532045
theorem B284375 : Blo 187803 284375 := bstep (se 1 (by rfl) ⟨213281, by rfl⟩ : syracuseStep 284375 = 426563) B426563
theorem B317209 : Blo 187803 317209 := bstep (se 2 (by rfl) ⟨118953, by rfl⟩ : syracuseStep 317209 = 237907) B237907
theorem B284441 : Blo 187803 284441 := bstep (se 2 (by rfl) ⟨106665, by rfl⟩ : syracuseStep 284441 = 213331) B213331
theorem B481099 : Blo 187803 481099 := bstep (se 1 (by rfl) ⟨360824, by rfl⟩ : syracuseStep 481099 = 721649) B721649
theorem B284555 : Blo 187803 284555 := bstep (se 1 (by rfl) ⟨213416, by rfl⟩ : syracuseStep 284555 = 426833) B426833
theorem B677783 : Blo 187803 677783 := bstep (se 1 (by rfl) ⟨508337, by rfl⟩ : syracuseStep 677783 = 1016675) B1016675
theorem B284567 : Blo 187803 284567 := bstep (se 1 (by rfl) ⟨213425, by rfl⟩ : syracuseStep 284567 = 426851) B426851
theorem B284633 : Blo 187803 284633 := bstep (se 2 (by rfl) ⟨106737, by rfl⟩ : syracuseStep 284633 = 213475) B213475
theorem B481241 : Blo 187803 481241 := bstep (se 2 (by rfl) ⟨180465, by rfl⟩ : syracuseStep 481241 = 360931) B360931
theorem B677911 : Blo 187803 677911 := bstep (se 1 (by rfl) ⟨508433, by rfl⟩ : syracuseStep 677911 = 1016867) B1016867
theorem B284747 : Blo 187803 284747 := bstep (se 1 (by rfl) ⟨213560, by rfl⟩ : syracuseStep 284747 = 427121) B427121
theorem B284759 : Blo 187803 284759 := bstep (se 1 (by rfl) ⟨213569, by rfl⟩ : syracuseStep 284759 = 427139) B427139
theorem B546905 : Blo 187803 546905 := bstep (se 2 (by rfl) ⟨205089, by rfl⟩ : syracuseStep 546905 = 410179) B410179
theorem B284825 : Blo 187803 284825 := bstep (se 2 (by rfl) ⟨106809, by rfl⟩ : syracuseStep 284825 = 213619) B213619
theorem B645299 : Blo 187803 645299 := bstep (se 1 (by rfl) ⟨483974, by rfl⟩ : syracuseStep 645299 = 967949) B967949
theorem B284939 : Blo 187803 284939 := bstep (se 1 (by rfl) ⟨213704, by rfl⟩ : syracuseStep 284939 = 427409) B427409
theorem B284951 : Blo 187803 284951 := bstep (se 1 (by rfl) ⟨213713, by rfl⟩ : syracuseStep 284951 = 427427) B427427
theorem B13031725 : Blo 187803 13031725 := bstep (se 3 (by rfl) ⟨2443448, by rfl⟩ : syracuseStep 13031725 = 4886897) B4886897
theorem B2283821 : Blo 187803 2283821 := bstep (se 3 (by rfl) ⟨428216, by rfl⟩ : syracuseStep 2283821 = 856433) B856433
theorem B317783 : Blo 187803 317783 := bstep (se 1 (by rfl) ⟨238337, by rfl⟩ : syracuseStep 317783 = 476675) B476675
theorem B285017 : Blo 187803 285017 := bstep (se 2 (by rfl) ⟨106881, by rfl⟩ : syracuseStep 285017 = 213763) B213763
theorem B2677093 : Blo 187803 2677093 := bstep (se 4 (by rfl) ⟨250977, by rfl⟩ : syracuseStep 2677093 = 501955) B501955
theorem B1071539 : Blo 187803 1071539 := bstep (se 1 (by rfl) ⟨803654, by rfl⟩ : syracuseStep 1071539 = 1607309) B1607309
theorem B645569 : Blo 187803 645569 := bstep (se 2 (by rfl) ⟨242088, by rfl⟩ : syracuseStep 645569 = 484177) B484177
theorem B285131 : Blo 187803 285131 := bstep (se 1 (by rfl) ⟨213848, by rfl⟩ : syracuseStep 285131 = 427697) B427697
theorem B317911 : Blo 187803 317911 := bstep (se 1 (by rfl) ⟨238433, by rfl⟩ : syracuseStep 317911 = 476867) B476867
theorem B285143 : Blo 187803 285143 := bstep (se 1 (by rfl) ⟨213857, by rfl⟩ : syracuseStep 285143 = 427715) B427715
theorem B285209 : Blo 187803 285209 := bstep (se 2 (by rfl) ⟨106953, by rfl⟩ : syracuseStep 285209 = 213907) B213907
theorem B285323 : Blo 187803 285323 := bstep (se 1 (by rfl) ⟨213992, by rfl⟩ : syracuseStep 285323 = 427985) B427985
theorem B285335 : Blo 187803 285335 := bstep (se 1 (by rfl) ⟨214001, by rfl⟩ : syracuseStep 285335 = 428003) B428003
theorem B1432241 : Blo 187803 1432241 := bstep (se 2 (by rfl) ⟨537090, by rfl⟩ : syracuseStep 1432241 = 1074181) B1074181
theorem B285401 : Blo 187803 285401 := bstep (se 2 (by rfl) ⟨107025, by rfl⟩ : syracuseStep 285401 = 214051) B214051
theorem B482071 : Blo 187803 482071 := bstep (se 1 (by rfl) ⟨361553, by rfl⟩ : syracuseStep 482071 = 723107) B723107
theorem B285515 : Blo 187803 285515 := bstep (se 1 (by rfl) ⟨214136, by rfl⟩ : syracuseStep 285515 = 428273) B428273
theorem B285527 : Blo 187803 285527 := bstep (se 1 (by rfl) ⟨214145, by rfl⟩ : syracuseStep 285527 = 428291) B428291
theorem B285593 : Blo 187803 285593 := bstep (se 2 (by rfl) ⟨107097, by rfl⟩ : syracuseStep 285593 = 214195) B214195
theorem B646109 : Blo 187803 646109 := bstep (se 3 (by rfl) ⟨121145, by rfl⟩ : syracuseStep 646109 = 242291) B242291
theorem B285707 : Blo 187803 285707 := bstep (se 1 (by rfl) ⟨214280, by rfl⟩ : syracuseStep 285707 = 428561) B428561
theorem B285719 : Blo 187803 285719 := bstep (se 1 (by rfl) ⟨214289, by rfl⟩ : syracuseStep 285719 = 428579) B428579
theorem B318539 : Blo 187803 318539 := bstep (se 1 (by rfl) ⟨238904, by rfl⟩ : syracuseStep 318539 = 477809) B477809
theorem B285785 : Blo 187803 285785 := bstep (se 2 (by rfl) ⟨107169, by rfl⟩ : syracuseStep 285785 = 214339) B214339
theorem B777347 : Blo 187803 777347 := bstep (se 1 (by rfl) ⟨583010, by rfl⟩ : syracuseStep 777347 = 1166021) B1166021
theorem B1432727 : Blo 187803 1432727 := bstep (se 1 (by rfl) ⟨1074545, by rfl⟩ : syracuseStep 1432727 = 2149091) B2149091
theorem B318667 : Blo 187803 318667 := bstep (se 1 (by rfl) ⟨239000, by rfl⟩ : syracuseStep 318667 = 478001) B478001
theorem B285899 : Blo 187803 285899 := bstep (se 1 (by rfl) ⟨214424, by rfl⟩ : syracuseStep 285899 = 428849) B428849
theorem B482507 : Blo 187803 482507 := bstep (se 1 (by rfl) ⟨361880, by rfl⟩ : syracuseStep 482507 = 723761) B723761
theorem B285911 : Blo 187803 285911 := bstep (se 1 (by rfl) ⟨214433, by rfl⟩ : syracuseStep 285911 = 428867) B428867
theorem B285977 : Blo 187803 285977 := bstep (se 2 (by rfl) ⟨107241, by rfl⟩ : syracuseStep 285977 = 214483) B214483
theorem B318809 : Blo 187803 318809 := bstep (se 2 (by rfl) ⟨119553, by rfl⟩ : syracuseStep 318809 = 239107) B239107
theorem B286091 : Blo 187803 286091 := bstep (se 1 (by rfl) ⟨214568, by rfl⟩ : syracuseStep 286091 = 429137) B429137
theorem B286103 : Blo 187803 286103 := bstep (se 1 (by rfl) ⟨214577, by rfl⟩ : syracuseStep 286103 = 429155) B429155
theorem B187819 : Blo 187803 187819 := bstep (se 1 (by rfl) ⟨140864, by rfl⟩ : syracuseStep 187819 = 281729) B281729
theorem B187831 : Blo 187803 187831 := bstep (se 1 (by rfl) ⟨140873, by rfl⟩ : syracuseStep 187831 = 281747) B281747
theorem B187851 : Blo 187803 187851 := bstep (se 1 (by rfl) ⟨140888, by rfl⟩ : syracuseStep 187851 = 281777) B281777
theorem B187863 : Blo 187803 187863 := bstep (se 1 (by rfl) ⟨140897, by rfl⟩ : syracuseStep 187863 = 281795) B281795
theorem B318937 : Blo 187803 318937 := bstep (se 2 (by rfl) ⟨119601, by rfl⟩ : syracuseStep 318937 = 239203) B239203
theorem B286169 : Blo 187803 286169 := bstep (se 2 (by rfl) ⟨107313, by rfl⟩ : syracuseStep 286169 = 214627) B214627
theorem B187883 : Blo 187803 187883 := bstep (se 1 (by rfl) ⟨140912, by rfl⟩ : syracuseStep 187883 = 281825) B281825
theorem B187895 : Blo 187803 187895 := bstep (se 1 (by rfl) ⟨140921, by rfl⟩ : syracuseStep 187895 = 281843) B281843
theorem B187915 : Blo 187803 187915 := bstep (se 1 (by rfl) ⟨140936, by rfl⟩ : syracuseStep 187915 = 281873) B281873
theorem B187927 : Blo 187803 187927 := bstep (se 1 (by rfl) ⟨140945, by rfl⟩ : syracuseStep 187927 = 281891) B281891
theorem B187947 : Blo 187803 187947 := bstep (se 1 (by rfl) ⟨140960, by rfl⟩ : syracuseStep 187947 = 281921) B281921
theorem B384563 : Blo 187803 384563 := bstep (se 1 (by rfl) ⟨288422, by rfl⟩ : syracuseStep 384563 = 576845) B576845
theorem B187959 : Blo 187803 187959 := bstep (se 1 (by rfl) ⟨140969, by rfl⟩ : syracuseStep 187959 = 281939) B281939
theorem B482881 : Blo 187803 482881 := bstep (se 2 (by rfl) ⟨181080, by rfl⟩ : syracuseStep 482881 = 362161) B362161
theorem B187979 : Blo 187803 187979 := bstep (se 1 (by rfl) ⟨140984, by rfl⟩ : syracuseStep 187979 = 281969) B281969
theorem B286283 : Blo 187803 286283 := bstep (se 1 (by rfl) ⟨214712, by rfl⟩ : syracuseStep 286283 = 429425) B429425
theorem B187991 : Blo 187803 187991 := bstep (se 1 (by rfl) ⟨140993, by rfl⟩ : syracuseStep 187991 = 281987) B281987
theorem B286295 : Blo 187803 286295 := bstep (se 1 (by rfl) ⟨214721, by rfl⟩ : syracuseStep 286295 = 429443) B429443
theorem B548441 : Blo 187803 548441 := bstep (se 2 (by rfl) ⟨205665, by rfl⟩ : syracuseStep 548441 = 411331) B411331
theorem B188011 : Blo 187803 188011 := bstep (se 1 (by rfl) ⟨141008, by rfl⟩ : syracuseStep 188011 = 282017) B282017
theorem B188023 : Blo 187803 188023 := bstep (se 1 (by rfl) ⟨141017, by rfl⟩ : syracuseStep 188023 = 282035) B282035
theorem B188043 : Blo 187803 188043 := bstep (se 1 (by rfl) ⟨141032, by rfl⟩ : syracuseStep 188043 = 282065) B282065
theorem B188055 : Blo 187803 188055 := bstep (se 1 (by rfl) ⟨141041, by rfl⟩ : syracuseStep 188055 = 282083) B282083
theorem B286361 : Blo 187803 286361 := bstep (se 2 (by rfl) ⟨107385, by rfl⟩ : syracuseStep 286361 = 214771) B214771
theorem B188075 : Blo 187803 188075 := bstep (se 1 (by rfl) ⟨141056, by rfl⟩ : syracuseStep 188075 = 282113) B282113
theorem B188087 : Blo 187803 188087 := bstep (se 1 (by rfl) ⟨141065, by rfl⟩ : syracuseStep 188087 = 282131) B282131
theorem B188107 : Blo 187803 188107 := bstep (se 1 (by rfl) ⟨141080, by rfl⟩ : syracuseStep 188107 = 282161) B282161
theorem B188119 : Blo 187803 188119 := bstep (se 1 (by rfl) ⟨141089, by rfl⟩ : syracuseStep 188119 = 282179) B282179
theorem B188139 : Blo 187803 188139 := bstep (se 1 (by rfl) ⟨141104, by rfl⟩ : syracuseStep 188139 = 282209) B282209
theorem B188151 : Blo 187803 188151 := bstep (se 1 (by rfl) ⟨141113, by rfl⟩ : syracuseStep 188151 = 282227) B282227
theorem B188171 : Blo 187803 188171 := bstep (se 1 (by rfl) ⟨141128, by rfl⟩ : syracuseStep 188171 = 282257) B282257
theorem B286475 : Blo 187803 286475 := bstep (se 1 (by rfl) ⟨214856, by rfl⟩ : syracuseStep 286475 = 429713) B429713
theorem B188183 : Blo 187803 188183 := bstep (se 1 (by rfl) ⟨141137, by rfl⟩ : syracuseStep 188183 = 282275) B282275
theorem B286487 : Blo 187803 286487 := bstep (se 1 (by rfl) ⟨214865, by rfl⟩ : syracuseStep 286487 = 429731) B429731
theorem B188203 : Blo 187803 188203 := bstep (se 1 (by rfl) ⟨141152, by rfl⟩ : syracuseStep 188203 = 282305) B282305
theorem B188215 : Blo 187803 188215 := bstep (se 1 (by rfl) ⟨141161, by rfl⟩ : syracuseStep 188215 = 282323) B282323
theorem B188235 : Blo 187803 188235 := bstep (se 1 (by rfl) ⟨141176, by rfl⟩ : syracuseStep 188235 = 282353) B282353
theorem B188247 : Blo 187803 188247 := bstep (se 1 (by rfl) ⟨141185, by rfl⟩ : syracuseStep 188247 = 282371) B282371
theorem B286553 : Blo 187803 286553 := bstep (se 2 (by rfl) ⟨107457, by rfl⟩ : syracuseStep 286553 = 214915) B214915
theorem B1072997 : Blo 187803 1072997 := bstep (se 4 (by rfl) ⟨100593, by rfl⟩ : syracuseStep 1072997 = 201187) B201187
theorem B188267 : Blo 187803 188267 := bstep (se 1 (by rfl) ⟨141200, by rfl⟩ : syracuseStep 188267 = 282401) B282401
theorem B188279 : Blo 187803 188279 := bstep (se 1 (by rfl) ⟨141209, by rfl⟩ : syracuseStep 188279 = 282419) B282419
theorem B188299 : Blo 187803 188299 := bstep (se 1 (by rfl) ⟨141224, by rfl⟩ : syracuseStep 188299 = 282449) B282449
theorem B188311 : Blo 187803 188311 := bstep (se 1 (by rfl) ⟨141233, by rfl⟩ : syracuseStep 188311 = 282467) B282467
theorem B188331 : Blo 187803 188331 := bstep (se 1 (by rfl) ⟨141248, by rfl⟩ : syracuseStep 188331 = 282497) B282497
theorem B188343 : Blo 187803 188343 := bstep (se 1 (by rfl) ⟨141257, by rfl⟩ : syracuseStep 188343 = 282515) B282515
theorem B679873 : Blo 187803 679873 := bstep (se 2 (by rfl) ⟨254952, by rfl⟩ : syracuseStep 679873 = 509905) B509905
theorem B188363 : Blo 187803 188363 := bstep (se 1 (by rfl) ⟨141272, by rfl⟩ : syracuseStep 188363 = 282545) B282545
theorem B286667 : Blo 187803 286667 := bstep (se 1 (by rfl) ⟨215000, by rfl⟩ : syracuseStep 286667 = 430001) B430001
theorem B188375 : Blo 187803 188375 := bstep (se 1 (by rfl) ⟨141281, by rfl⟩ : syracuseStep 188375 = 282563) B282563
theorem B647129 : Blo 187803 647129 := bstep (se 2 (by rfl) ⟨242673, by rfl⟩ : syracuseStep 647129 = 485347) B485347
theorem B286679 : Blo 187803 286679 := bstep (se 1 (by rfl) ⟨215009, by rfl⟩ : syracuseStep 286679 = 430019) B430019
theorem B188395 : Blo 187803 188395 := bstep (se 1 (by rfl) ⟨141296, by rfl⟩ : syracuseStep 188395 = 282593) B282593
theorem B188407 : Blo 187803 188407 := bstep (se 1 (by rfl) ⟨141305, by rfl⟩ : syracuseStep 188407 = 282611) B282611
theorem B188427 : Blo 187803 188427 := bstep (se 1 (by rfl) ⟨141320, by rfl⟩ : syracuseStep 188427 = 282641) B282641
theorem B221195 : Blo 187803 221195 := bstep (se 1 (by rfl) ⟨165896, by rfl⟩ : syracuseStep 221195 = 331793) B331793
theorem B188439 : Blo 187803 188439 := bstep (se 1 (by rfl) ⟨141329, by rfl⟩ : syracuseStep 188439 = 282659) B282659
theorem B319511 : Blo 187803 319511 := bstep (se 1 (by rfl) ⟨239633, by rfl⟩ : syracuseStep 319511 = 479267) B479267
theorem B286745 : Blo 187803 286745 := bstep (se 2 (by rfl) ⟨107529, by rfl⟩ : syracuseStep 286745 = 215059) B215059
theorem B188459 : Blo 187803 188459 := bstep (se 1 (by rfl) ⟨141344, by rfl⟩ : syracuseStep 188459 = 282689) B282689
theorem B188471 : Blo 187803 188471 := bstep (se 1 (by rfl) ⟨141353, by rfl⟩ : syracuseStep 188471 = 282707) B282707
theorem B11952197 : Blo 187803 11952197 := bstep (se 4 (by rfl) ⟨1120518, by rfl⟩ : syracuseStep 11952197 = 2241037) B2241037
theorem B188491 : Blo 187803 188491 := bstep (se 1 (by rfl) ⟨141368, by rfl⟩ : syracuseStep 188491 = 282737) B282737
theorem B647243 : Blo 187803 647243 := bstep (se 1 (by rfl) ⟨485432, by rfl⟩ : syracuseStep 647243 = 970865) B970865
theorem B188503 : Blo 187803 188503 := bstep (se 1 (by rfl) ⟨141377, by rfl⟩ : syracuseStep 188503 = 282755) B282755
theorem B188523 : Blo 187803 188523 := bstep (se 1 (by rfl) ⟨141392, by rfl⟩ : syracuseStep 188523 = 282785) B282785
theorem B188535 : Blo 187803 188535 := bstep (se 1 (by rfl) ⟨141401, by rfl⟩ : syracuseStep 188535 = 282803) B282803
theorem B188555 : Blo 187803 188555 := bstep (se 1 (by rfl) ⟨141416, by rfl⟩ : syracuseStep 188555 = 282833) B282833
theorem B286859 : Blo 187803 286859 := bstep (se 1 (by rfl) ⟨215144, by rfl⟩ : syracuseStep 286859 = 430289) B430289
theorem B188567 : Blo 187803 188567 := bstep (se 1 (by rfl) ⟨141425, by rfl⟩ : syracuseStep 188567 = 282851) B282851
theorem B319639 : Blo 187803 319639 := bstep (se 1 (by rfl) ⟨239729, by rfl⟩ : syracuseStep 319639 = 479459) B479459
theorem B483479 : Blo 187803 483479 := bstep (se 1 (by rfl) ⟨362609, by rfl⟩ : syracuseStep 483479 = 725219) B725219
theorem B286871 : Blo 187803 286871 := bstep (se 1 (by rfl) ⟨215153, by rfl⟩ : syracuseStep 286871 = 430307) B430307
theorem B188587 : Blo 187803 188587 := bstep (se 1 (by rfl) ⟨141440, by rfl⟩ : syracuseStep 188587 = 282881) B282881
theorem B188599 : Blo 187803 188599 := bstep (se 1 (by rfl) ⟨141449, by rfl⟩ : syracuseStep 188599 = 282899) B282899
theorem B188619 : Blo 187803 188619 := bstep (se 1 (by rfl) ⟨141464, by rfl⟩ : syracuseStep 188619 = 282929) B282929
theorem B188631 : Blo 187803 188631 := bstep (se 1 (by rfl) ⟨141473, by rfl⟩ : syracuseStep 188631 = 282947) B282947
theorem B286937 : Blo 187803 286937 := bstep (se 2 (by rfl) ⟨107601, by rfl⟩ : syracuseStep 286937 = 215203) B215203
theorem B188651 : Blo 187803 188651 := bstep (se 1 (by rfl) ⟨141488, by rfl⟩ : syracuseStep 188651 = 282977) B282977
theorem B188663 : Blo 187803 188663 := bstep (se 1 (by rfl) ⟨141497, by rfl⟩ : syracuseStep 188663 = 282995) B282995
theorem B188683 : Blo 187803 188683 := bstep (se 1 (by rfl) ⟨141512, by rfl⟩ : syracuseStep 188683 = 283025) B283025
theorem B93184277 : Blo 187803 93184277 := bstep (se 6 (by rfl) ⟨2184006, by rfl⟩ : syracuseStep 93184277 = 4368013) B4368013
theorem B188695 : Blo 187803 188695 := bstep (se 1 (by rfl) ⟨141521, by rfl⟩ : syracuseStep 188695 = 283043) B283043
theorem B188715 : Blo 187803 188715 := bstep (se 1 (by rfl) ⟨141536, by rfl⟩ : syracuseStep 188715 = 283073) B283073
theorem B811309 : Blo 187803 811309 := bstep (se 3 (by rfl) ⟨152120, by rfl⟩ : syracuseStep 811309 = 304241) B304241
theorem B188727 : Blo 187803 188727 := bstep (se 1 (by rfl) ⟨141545, by rfl⟩ : syracuseStep 188727 = 283091) B283091
theorem B1827137 : Blo 187803 1827137 := bstep (se 2 (by rfl) ⟨685176, by rfl⟩ : syracuseStep 1827137 = 1370353) B1370353
theorem B188747 : Blo 187803 188747 := bstep (se 1 (by rfl) ⟨141560, by rfl⟩ : syracuseStep 188747 = 283121) B283121
theorem B287051 : Blo 187803 287051 := bstep (se 1 (by rfl) ⟨215288, by rfl⟩ : syracuseStep 287051 = 430577) B430577
theorem B188759 : Blo 187803 188759 := bstep (se 1 (by rfl) ⟨141569, by rfl⟩ : syracuseStep 188759 = 283139) B283139
theorem B287063 : Blo 187803 287063 := bstep (se 1 (by rfl) ⟨215297, by rfl⟩ : syracuseStep 287063 = 430595) B430595
theorem B188779 : Blo 187803 188779 := bstep (se 1 (by rfl) ⟨141584, by rfl⟩ : syracuseStep 188779 = 283169) B283169
theorem B188791 : Blo 187803 188791 := bstep (se 1 (by rfl) ⟨141593, by rfl⟩ : syracuseStep 188791 = 283187) B283187
theorem B188811 : Blo 187803 188811 := bstep (se 1 (by rfl) ⟨141608, by rfl⟩ : syracuseStep 188811 = 283217) B283217
theorem B188823 : Blo 187803 188823 := bstep (se 1 (by rfl) ⟨141617, by rfl⟩ : syracuseStep 188823 = 283235) B283235
theorem B287129 : Blo 187803 287129 := bstep (se 2 (by rfl) ⟨107673, by rfl⟩ : syracuseStep 287129 = 215347) B215347
theorem B188843 : Blo 187803 188843 := bstep (se 1 (by rfl) ⟨141632, by rfl⟩ : syracuseStep 188843 = 283265) B283265
theorem B188855 : Blo 187803 188855 := bstep (se 1 (by rfl) ⟨141641, by rfl⟩ : syracuseStep 188855 = 283283) B283283
theorem B188875 : Blo 187803 188875 := bstep (se 1 (by rfl) ⟨141656, by rfl⟩ : syracuseStep 188875 = 283313) B283313
theorem B188887 : Blo 187803 188887 := bstep (se 1 (by rfl) ⟨141665, by rfl⟩ : syracuseStep 188887 = 283331) B283331
theorem B188907 : Blo 187803 188907 := bstep (se 1 (by rfl) ⟨141680, by rfl⟩ : syracuseStep 188907 = 283361) B283361
theorem B188919 : Blo 187803 188919 := bstep (se 1 (by rfl) ⟨141689, by rfl⟩ : syracuseStep 188919 = 283379) B283379
theorem B188939 : Blo 187803 188939 := bstep (se 1 (by rfl) ⟨141704, by rfl⟩ : syracuseStep 188939 = 283409) B283409
theorem B287243 : Blo 187803 287243 := bstep (se 1 (by rfl) ⟨215432, by rfl⟩ : syracuseStep 287243 = 430865) B430865
theorem B1073681 : Blo 187803 1073681 := bstep (se 2 (by rfl) ⟨402630, by rfl⟩ : syracuseStep 1073681 = 805261) B805261
theorem B188951 : Blo 187803 188951 := bstep (se 1 (by rfl) ⟨141713, by rfl⟩ : syracuseStep 188951 = 283427) B283427
theorem B287255 : Blo 187803 287255 := bstep (se 1 (by rfl) ⟨215441, by rfl⟩ : syracuseStep 287255 = 430883) B430883
theorem B188971 : Blo 187803 188971 := bstep (se 1 (by rfl) ⟨141728, by rfl⟩ : syracuseStep 188971 = 283457) B283457
theorem B188983 : Blo 187803 188983 := bstep (se 1 (by rfl) ⟨141737, by rfl⟩ : syracuseStep 188983 = 283475) B283475
theorem B189003 : Blo 187803 189003 := bstep (se 1 (by rfl) ⟨141752, by rfl⟩ : syracuseStep 189003 = 283505) B283505
theorem B189015 : Blo 187803 189015 := bstep (se 1 (by rfl) ⟨141761, by rfl⟩ : syracuseStep 189015 = 283523) B283523
theorem B287321 : Blo 187803 287321 := bstep (se 2 (by rfl) ⟨107745, by rfl⟩ : syracuseStep 287321 = 215491) B215491
theorem B189035 : Blo 187803 189035 := bstep (se 1 (by rfl) ⟨141776, by rfl⟩ : syracuseStep 189035 = 283553) B283553
theorem B189047 : Blo 187803 189047 := bstep (se 1 (by rfl) ⟨141785, by rfl⟩ : syracuseStep 189047 = 283571) B283571
theorem B189067 : Blo 187803 189067 := bstep (se 1 (by rfl) ⟨141800, by rfl⟩ : syracuseStep 189067 = 283601) B283601
theorem B189079 : Blo 187803 189079 := bstep (se 1 (by rfl) ⟨141809, by rfl⟩ : syracuseStep 189079 = 283619) B283619
theorem B189099 : Blo 187803 189099 := bstep (se 1 (by rfl) ⟨141824, by rfl⟩ : syracuseStep 189099 = 283649) B283649
theorem B189111 : Blo 187803 189111 := bstep (se 1 (by rfl) ⟨141833, by rfl⟩ : syracuseStep 189111 = 283667) B283667
theorem B189131 : Blo 187803 189131 := bstep (se 1 (by rfl) ⟨141848, by rfl⟩ : syracuseStep 189131 = 283697) B283697
theorem B287435 : Blo 187803 287435 := bstep (se 1 (by rfl) ⟨215576, by rfl⟩ : syracuseStep 287435 = 431153) B431153
theorem B189143 : Blo 187803 189143 := bstep (se 1 (by rfl) ⟨141857, by rfl⟩ : syracuseStep 189143 = 283715) B283715
theorem B287447 : Blo 187803 287447 := bstep (se 1 (by rfl) ⟨215585, by rfl⟩ : syracuseStep 287447 = 431171) B431171
theorem B189163 : Blo 187803 189163 := bstep (se 1 (by rfl) ⟨141872, by rfl⟩ : syracuseStep 189163 = 283745) B283745
theorem B189175 : Blo 187803 189175 := bstep (se 1 (by rfl) ⟨141881, by rfl⟩ : syracuseStep 189175 = 283763) B283763
theorem B189195 : Blo 187803 189195 := bstep (se 1 (by rfl) ⟨141896, by rfl⟩ : syracuseStep 189195 = 283793) B283793
theorem B320267 : Blo 187803 320267 := bstep (se 1 (by rfl) ⟨240200, by rfl⟩ : syracuseStep 320267 = 480401) B480401
theorem B189207 : Blo 187803 189207 := bstep (se 1 (by rfl) ⟨141905, by rfl⟩ : syracuseStep 189207 = 283811) B283811
theorem B287513 : Blo 187803 287513 := bstep (se 2 (by rfl) ⟨107817, by rfl⟩ : syracuseStep 287513 = 215635) B215635
theorem B189227 : Blo 187803 189227 := bstep (se 1 (by rfl) ⟨141920, by rfl⟩ : syracuseStep 189227 = 283841) B283841
theorem B189239 : Blo 187803 189239 := bstep (se 1 (by rfl) ⟨141929, by rfl⟩ : syracuseStep 189239 = 283859) B283859
theorem B451403 : Blo 187803 451403 := bstep (se 1 (by rfl) ⟨338552, by rfl⟩ : syracuseStep 451403 = 677105) B677105
theorem B189259 : Blo 187803 189259 := bstep (se 1 (by rfl) ⟨141944, by rfl⟩ : syracuseStep 189259 = 283889) B283889
theorem B189271 : Blo 187803 189271 := bstep (se 1 (by rfl) ⟨141953, by rfl⟩ : syracuseStep 189271 = 283907) B283907
theorem B189291 : Blo 187803 189291 := bstep (se 1 (by rfl) ⟨141968, by rfl⟩ : syracuseStep 189291 = 283937) B283937
theorem B2417525 : Blo 187803 2417525 := bstep (se 5 (by rfl) ⟨113321, by rfl⟩ : syracuseStep 2417525 = 226643) B226643
theorem B189303 : Blo 187803 189303 := bstep (se 1 (by rfl) ⟨141977, by rfl⟩ : syracuseStep 189303 = 283955) B283955
theorem B385931 : Blo 187803 385931 := bstep (se 1 (by rfl) ⟨289448, by rfl⟩ : syracuseStep 385931 = 578897) B578897
theorem B189323 : Blo 187803 189323 := bstep (se 1 (by rfl) ⟨141992, by rfl⟩ : syracuseStep 189323 = 283985) B283985
theorem B320395 : Blo 187803 320395 := bstep (se 1 (by rfl) ⟨240296, by rfl⟩ : syracuseStep 320395 = 480593) B480593
theorem B287627 : Blo 187803 287627 := bstep (se 1 (by rfl) ⟨215720, by rfl⟩ : syracuseStep 287627 = 431441) B431441
theorem B189335 : Blo 187803 189335 := bstep (se 1 (by rfl) ⟨142001, by rfl⟩ : syracuseStep 189335 = 284003) B284003
theorem B287639 : Blo 187803 287639 := bstep (se 1 (by rfl) ⟨215729, by rfl⟩ : syracuseStep 287639 = 431459) B431459
theorem B189355 : Blo 187803 189355 := bstep (se 1 (by rfl) ⟨142016, by rfl⟩ : syracuseStep 189355 = 284033) B284033
theorem B189367 : Blo 187803 189367 := bstep (se 1 (by rfl) ⟨142025, by rfl⟩ : syracuseStep 189367 = 284051) B284051
theorem B484289 : Blo 187803 484289 := bstep (se 2 (by rfl) ⟨181608, by rfl⟩ : syracuseStep 484289 = 363217) B363217
theorem B189387 : Blo 187803 189387 := bstep (se 1 (by rfl) ⟨142040, by rfl⟩ : syracuseStep 189387 = 284081) B284081
theorem B189399 : Blo 187803 189399 := bstep (se 1 (by rfl) ⟨142049, by rfl⟩ : syracuseStep 189399 = 284099) B284099
theorem B287705 : Blo 187803 287705 := bstep (se 2 (by rfl) ⟨107889, by rfl⟩ : syracuseStep 287705 = 215779) B215779
theorem B189419 : Blo 187803 189419 := bstep (se 1 (by rfl) ⟨142064, by rfl⟩ : syracuseStep 189419 = 284129) B284129
theorem B189431 : Blo 187803 189431 := bstep (se 1 (by rfl) ⟨142073, by rfl⟩ : syracuseStep 189431 = 284147) B284147
theorem B189451 : Blo 187803 189451 := bstep (se 1 (by rfl) ⟨142088, by rfl⟩ : syracuseStep 189451 = 284177) B284177
theorem B189463 : Blo 187803 189463 := bstep (se 1 (by rfl) ⟨142097, by rfl⟩ : syracuseStep 189463 = 284195) B284195
theorem B320537 : Blo 187803 320537 := bstep (se 2 (by rfl) ⟨120201, by rfl⟩ : syracuseStep 320537 = 240403) B240403
theorem B189483 : Blo 187803 189483 := bstep (se 1 (by rfl) ⟨142112, by rfl⟩ : syracuseStep 189483 = 284225) B284225
theorem B189495 : Blo 187803 189495 := bstep (se 1 (by rfl) ⟨142121, by rfl⟩ : syracuseStep 189495 = 284243) B284243
theorem B189515 : Blo 187803 189515 := bstep (se 1 (by rfl) ⟨142136, by rfl⟩ : syracuseStep 189515 = 284273) B284273
theorem B189527 : Blo 187803 189527 := bstep (se 1 (by rfl) ⟨142145, by rfl⟩ : syracuseStep 189527 = 284291) B284291
theorem B189547 : Blo 187803 189547 := bstep (se 1 (by rfl) ⟨142160, by rfl⟩ : syracuseStep 189547 = 284321) B284321
theorem B189559 : Blo 187803 189559 := bstep (se 1 (by rfl) ⟨142169, by rfl⟩ : syracuseStep 189559 = 284339) B284339
theorem B189579 : Blo 187803 189579 := bstep (se 1 (by rfl) ⟨142184, by rfl⟩ : syracuseStep 189579 = 284369) B284369
theorem B713873 : Blo 187803 713873 := bstep (se 2 (by rfl) ⟨267702, by rfl⟩ : syracuseStep 713873 = 535405) B535405
theorem B189591 : Blo 187803 189591 := bstep (se 1 (by rfl) ⟨142193, by rfl⟩ : syracuseStep 189591 = 284387) B284387
theorem B320665 : Blo 187803 320665 := bstep (se 2 (by rfl) ⟨120249, by rfl⟩ : syracuseStep 320665 = 240499) B240499
theorem B189611 : Blo 187803 189611 := bstep (se 1 (by rfl) ⟨142208, by rfl⟩ : syracuseStep 189611 = 284417) B284417
theorem B189623 : Blo 187803 189623 := bstep (se 1 (by rfl) ⟨142217, by rfl⟩ : syracuseStep 189623 = 284435) B284435
theorem B189643 : Blo 187803 189643 := bstep (se 1 (by rfl) ⟨142232, by rfl⟩ : syracuseStep 189643 = 284465) B284465
theorem B189655 : Blo 187803 189655 := bstep (se 1 (by rfl) ⟨142241, by rfl⟩ : syracuseStep 189655 = 284483) B284483
theorem B189675 : Blo 187803 189675 := bstep (se 1 (by rfl) ⟨142256, by rfl⟩ : syracuseStep 189675 = 284513) B284513
theorem B189687 : Blo 187803 189687 := bstep (se 1 (by rfl) ⟨142265, by rfl⟩ : syracuseStep 189687 = 284531) B284531
theorem B189707 : Blo 187803 189707 := bstep (se 1 (by rfl) ⟨142280, by rfl⟩ : syracuseStep 189707 = 284561) B284561
theorem B189719 : Blo 187803 189719 := bstep (se 1 (by rfl) ⟨142289, by rfl⟩ : syracuseStep 189719 = 284579) B284579
theorem B189739 : Blo 187803 189739 := bstep (se 1 (by rfl) ⟨142304, by rfl⟩ : syracuseStep 189739 = 284609) B284609
theorem B189751 : Blo 187803 189751 := bstep (se 1 (by rfl) ⟨142313, by rfl⟩ : syracuseStep 189751 = 284627) B284627
theorem B189771 : Blo 187803 189771 := bstep (se 1 (by rfl) ⟨142328, by rfl⟩ : syracuseStep 189771 = 284657) B284657
theorem B189783 : Blo 187803 189783 := bstep (se 1 (by rfl) ⟨142337, by rfl⟩ : syracuseStep 189783 = 284675) B284675
theorem B189803 : Blo 187803 189803 := bstep (se 1 (by rfl) ⟨142352, by rfl⟩ : syracuseStep 189803 = 284705) B284705
theorem B189815 : Blo 187803 189815 := bstep (se 1 (by rfl) ⟨142361, by rfl⟩ : syracuseStep 189815 = 284723) B284723
theorem B189835 : Blo 187803 189835 := bstep (se 1 (by rfl) ⟨142376, by rfl⟩ : syracuseStep 189835 = 284753) B284753
theorem B189847 : Blo 187803 189847 := bstep (se 1 (by rfl) ⟨142385, by rfl⟩ : syracuseStep 189847 = 284771) B284771
theorem B189867 : Blo 187803 189867 := bstep (se 1 (by rfl) ⟨142400, by rfl⟩ : syracuseStep 189867 = 284801) B284801
theorem B189879 : Blo 187803 189879 := bstep (se 1 (by rfl) ⟨142409, by rfl⟩ : syracuseStep 189879 = 284819) B284819
theorem B189899 : Blo 187803 189899 := bstep (se 1 (by rfl) ⟨142424, by rfl⟩ : syracuseStep 189899 = 284849) B284849
theorem B189911 : Blo 187803 189911 := bstep (se 1 (by rfl) ⟨142433, by rfl⟩ : syracuseStep 189911 = 284867) B284867
theorem B484825 : Blo 187803 484825 := bstep (se 2 (by rfl) ⟨181809, by rfl⟩ : syracuseStep 484825 = 363619) B363619
theorem B189931 : Blo 187803 189931 := bstep (se 1 (by rfl) ⟨142448, by rfl⟩ : syracuseStep 189931 = 284897) B284897
theorem B189943 : Blo 187803 189943 := bstep (se 1 (by rfl) ⟨142457, by rfl⟩ : syracuseStep 189943 = 284915) B284915
theorem B189963 : Blo 187803 189963 := bstep (se 1 (by rfl) ⟨142472, by rfl⟩ : syracuseStep 189963 = 284945) B284945
theorem B189975 : Blo 187803 189975 := bstep (se 1 (by rfl) ⟨142481, by rfl⟩ : syracuseStep 189975 = 284963) B284963
theorem B189995 : Blo 187803 189995 := bstep (se 1 (by rfl) ⟨142496, by rfl⟩ : syracuseStep 189995 = 284993) B284993
theorem B190007 : Blo 187803 190007 := bstep (se 1 (by rfl) ⟨142505, by rfl⟩ : syracuseStep 190007 = 285011) B285011
theorem B190027 : Blo 187803 190027 := bstep (se 1 (by rfl) ⟨142520, by rfl⟩ : syracuseStep 190027 = 285041) B285041
theorem B190039 : Blo 187803 190039 := bstep (se 1 (by rfl) ⟨142529, by rfl⟩ : syracuseStep 190039 = 285059) B285059
theorem B714329 : Blo 187803 714329 := bstep (se 2 (by rfl) ⟨267873, by rfl⟩ : syracuseStep 714329 = 535747) B535747
theorem B190059 : Blo 187803 190059 := bstep (se 1 (by rfl) ⟨142544, by rfl⟩ : syracuseStep 190059 = 285089) B285089
theorem B190071 : Blo 187803 190071 := bstep (se 1 (by rfl) ⟨142553, by rfl⟩ : syracuseStep 190071 = 285107) B285107
theorem B190091 : Blo 187803 190091 := bstep (se 1 (by rfl) ⟨142568, by rfl⟩ : syracuseStep 190091 = 285137) B285137
theorem B190103 : Blo 187803 190103 := bstep (se 1 (by rfl) ⟨142577, by rfl⟩ : syracuseStep 190103 = 285155) B285155
theorem B190123 : Blo 187803 190123 := bstep (se 1 (by rfl) ⟨142592, by rfl⟩ : syracuseStep 190123 = 285185) B285185
theorem B190135 : Blo 187803 190135 := bstep (se 1 (by rfl) ⟨142601, by rfl⟩ : syracuseStep 190135 = 285203) B285203
theorem B190155 : Blo 187803 190155 := bstep (se 1 (by rfl) ⟨142616, by rfl⟩ : syracuseStep 190155 = 285233) B285233
theorem B190167 : Blo 187803 190167 := bstep (se 1 (by rfl) ⟨142625, by rfl⟩ : syracuseStep 190167 = 285251) B285251
theorem B321239 : Blo 187803 321239 := bstep (se 1 (by rfl) ⟨240929, by rfl⟩ : syracuseStep 321239 = 481859) B481859
theorem B976601 : Blo 187803 976601 := bstep (se 2 (by rfl) ⟨366225, by rfl⟩ : syracuseStep 976601 = 732451) B732451
theorem B517853 : Blo 187803 517853 := bstep (se 3 (by rfl) ⟨97097, by rfl⟩ : syracuseStep 517853 = 194195) B194195
theorem B190187 : Blo 187803 190187 := bstep (se 1 (by rfl) ⟨142640, by rfl⟩ : syracuseStep 190187 = 285281) B285281
theorem B190199 : Blo 187803 190199 := bstep (se 1 (by rfl) ⟨142649, by rfl⟩ : syracuseStep 190199 = 285299) B285299
theorem B190219 : Blo 187803 190219 := bstep (se 1 (by rfl) ⟨142664, by rfl⟩ : syracuseStep 190219 = 285329) B285329
theorem B190231 : Blo 187803 190231 := bstep (se 1 (by rfl) ⟨142673, by rfl⟩ : syracuseStep 190231 = 285347) B285347
theorem B190251 : Blo 187803 190251 := bstep (se 1 (by rfl) ⟨142688, by rfl⟩ : syracuseStep 190251 = 285377) B285377
theorem B714541 : Blo 187803 714541 := bstep (se 3 (by rfl) ⟨133976, by rfl⟩ : syracuseStep 714541 = 267953) B267953
theorem B190263 : Blo 187803 190263 := bstep (se 1 (by rfl) ⟨142697, by rfl⟩ : syracuseStep 190263 = 285395) B285395
theorem B2615105 : Blo 187803 2615105 := bstep (se 2 (by rfl) ⟨980664, by rfl⟩ : syracuseStep 2615105 = 1961329) B1961329
theorem B190283 : Blo 187803 190283 := bstep (se 1 (by rfl) ⟨142712, by rfl⟩ : syracuseStep 190283 = 285425) B285425
theorem B190295 : Blo 187803 190295 := bstep (se 1 (by rfl) ⟨142721, by rfl⟩ : syracuseStep 190295 = 285443) B285443
theorem B321367 : Blo 187803 321367 := bstep (se 1 (by rfl) ⟨241025, by rfl⟩ : syracuseStep 321367 = 482051) B482051
theorem B681821 : Blo 187803 681821 := bstep (se 3 (by rfl) ⟨127841, by rfl⟩ : syracuseStep 681821 = 255683) B255683
theorem B190315 : Blo 187803 190315 := bstep (se 1 (by rfl) ⟨142736, by rfl⟩ : syracuseStep 190315 = 285473) B285473
theorem B190327 : Blo 187803 190327 := bstep (se 1 (by rfl) ⟨142745, by rfl⟩ : syracuseStep 190327 = 285491) B285491
theorem B190347 : Blo 187803 190347 := bstep (se 1 (by rfl) ⟨142760, by rfl⟩ : syracuseStep 190347 = 285521) B285521
theorem B190359 : Blo 187803 190359 := bstep (se 1 (by rfl) ⟨142769, by rfl⟩ : syracuseStep 190359 = 285539) B285539
theorem B190379 : Blo 187803 190379 := bstep (se 1 (by rfl) ⟨142784, by rfl⟩ : syracuseStep 190379 = 285569) B285569
theorem B190391 : Blo 187803 190391 := bstep (se 1 (by rfl) ⟨142793, by rfl⟩ : syracuseStep 190391 = 285587) B285587
theorem B190411 : Blo 187803 190411 := bstep (se 1 (by rfl) ⟨142808, by rfl⟩ : syracuseStep 190411 = 285617) B285617
theorem B190423 : Blo 187803 190423 := bstep (se 1 (by rfl) ⟨142817, by rfl⟩ : syracuseStep 190423 = 285635) B285635
theorem B813017 : Blo 187803 813017 := bstep (se 2 (by rfl) ⟨304881, by rfl⟩ : syracuseStep 813017 = 609763) B609763
theorem B190443 : Blo 187803 190443 := bstep (se 1 (by rfl) ⟨142832, by rfl⟩ : syracuseStep 190443 = 285665) B285665
theorem B190455 : Blo 187803 190455 := bstep (se 1 (by rfl) ⟨142841, by rfl⟩ : syracuseStep 190455 = 285683) B285683
theorem B190475 : Blo 187803 190475 := bstep (se 1 (by rfl) ⟨142856, by rfl⟩ : syracuseStep 190475 = 285713) B285713
theorem B190487 : Blo 187803 190487 := bstep (se 1 (by rfl) ⟨142865, by rfl⟩ : syracuseStep 190487 = 285731) B285731
theorem B190507 : Blo 187803 190507 := bstep (se 1 (by rfl) ⟨142880, by rfl⟩ : syracuseStep 190507 = 285761) B285761
theorem B190519 : Blo 187803 190519 := bstep (se 1 (by rfl) ⟨142889, by rfl⟩ : syracuseStep 190519 = 285779) B285779
theorem B190539 : Blo 187803 190539 := bstep (se 1 (by rfl) ⟨142904, by rfl⟩ : syracuseStep 190539 = 285809) B285809
theorem B190551 : Blo 187803 190551 := bstep (se 1 (by rfl) ⟨142913, by rfl⟩ : syracuseStep 190551 = 285827) B285827
theorem B714845 : Blo 187803 714845 := bstep (se 3 (by rfl) ⟨134033, by rfl⟩ : syracuseStep 714845 = 268067) B268067
theorem B190571 : Blo 187803 190571 := bstep (se 1 (by rfl) ⟨142928, by rfl⟩ : syracuseStep 190571 = 285857) B285857
theorem B190583 : Blo 187803 190583 := bstep (se 1 (by rfl) ⟨142937, by rfl⟩ : syracuseStep 190583 = 285875) B285875
theorem B190603 : Blo 187803 190603 := bstep (se 1 (by rfl) ⟨142952, by rfl⟩ : syracuseStep 190603 = 285905) B285905
theorem B190615 : Blo 187803 190615 := bstep (se 1 (by rfl) ⟨142961, by rfl⟩ : syracuseStep 190615 = 285923) B285923
theorem B190635 : Blo 187803 190635 := bstep (se 1 (by rfl) ⟨142976, by rfl⟩ : syracuseStep 190635 = 285953) B285953
theorem B190647 : Blo 187803 190647 := bstep (se 1 (by rfl) ⟨142985, by rfl⟩ : syracuseStep 190647 = 285971) B285971
theorem B190667 : Blo 187803 190667 := bstep (se 1 (by rfl) ⟨143000, by rfl⟩ : syracuseStep 190667 = 286001) B286001
theorem B190679 : Blo 187803 190679 := bstep (se 1 (by rfl) ⟨143009, by rfl⟩ : syracuseStep 190679 = 286019) B286019
theorem B190699 : Blo 187803 190699 := bstep (se 1 (by rfl) ⟨143024, by rfl⟩ : syracuseStep 190699 = 286049) B286049
theorem B190711 : Blo 187803 190711 := bstep (se 1 (by rfl) ⟨143033, by rfl⟩ : syracuseStep 190711 = 286067) B286067
theorem B190731 : Blo 187803 190731 := bstep (se 1 (by rfl) ⟨143048, by rfl⟩ : syracuseStep 190731 = 286097) B286097
theorem B190743 : Blo 187803 190743 := bstep (se 1 (by rfl) ⟨143057, by rfl⟩ : syracuseStep 190743 = 286115) B286115
theorem B190763 : Blo 187803 190763 := bstep (se 1 (by rfl) ⟨143072, by rfl⟩ : syracuseStep 190763 = 286145) B286145
theorem B190775 : Blo 187803 190775 := bstep (se 1 (by rfl) ⟨143081, by rfl⟩ : syracuseStep 190775 = 286163) B286163
theorem B190795 : Blo 187803 190795 := bstep (se 1 (by rfl) ⟨143096, by rfl⟩ : syracuseStep 190795 = 286193) B286193
theorem B190807 : Blo 187803 190807 := bstep (se 1 (by rfl) ⟨143105, by rfl⟩ : syracuseStep 190807 = 286211) B286211
theorem B190827 : Blo 187803 190827 := bstep (se 1 (by rfl) ⟨143120, by rfl⟩ : syracuseStep 190827 = 286241) B286241
theorem B190839 : Blo 187803 190839 := bstep (se 1 (by rfl) ⟨143129, by rfl⟩ : syracuseStep 190839 = 286259) B286259
theorem B190859 : Blo 187803 190859 := bstep (se 1 (by rfl) ⟨143144, by rfl⟩ : syracuseStep 190859 = 286289) B286289
theorem B190871 : Blo 187803 190871 := bstep (se 1 (by rfl) ⟨143153, by rfl⟩ : syracuseStep 190871 = 286307) B286307
theorem B190891 : Blo 187803 190891 := bstep (se 1 (by rfl) ⟨143168, by rfl⟩ : syracuseStep 190891 = 286337) B286337
theorem B190903 : Blo 187803 190903 := bstep (se 1 (by rfl) ⟨143177, by rfl⟩ : syracuseStep 190903 = 286355) B286355
theorem B321995 : Blo 187803 321995 := bstep (se 1 (by rfl) ⟨241496, by rfl⟩ : syracuseStep 321995 = 482993) B482993
theorem B190923 : Blo 187803 190923 := bstep (se 1 (by rfl) ⟨143192, by rfl⟩ : syracuseStep 190923 = 286385) B286385
theorem B190935 : Blo 187803 190935 := bstep (se 1 (by rfl) ⟨143201, by rfl⟩ : syracuseStep 190935 = 286403) B286403
theorem B190955 : Blo 187803 190955 := bstep (se 1 (by rfl) ⟨143216, by rfl⟩ : syracuseStep 190955 = 286433) B286433
theorem B190967 : Blo 187803 190967 := bstep (se 1 (by rfl) ⟨143225, by rfl⟩ : syracuseStep 190967 = 286451) B286451
theorem B190987 : Blo 187803 190987 := bstep (se 1 (by rfl) ⟨143240, by rfl⟩ : syracuseStep 190987 = 286481) B286481
theorem B190999 : Blo 187803 190999 := bstep (se 1 (by rfl) ⟨143249, by rfl⟩ : syracuseStep 190999 = 286499) B286499
theorem B191019 : Blo 187803 191019 := bstep (se 1 (by rfl) ⟨143264, by rfl⟩ : syracuseStep 191019 = 286529) B286529
theorem B191031 : Blo 187803 191031 := bstep (se 1 (by rfl) ⟨143273, by rfl⟩ : syracuseStep 191031 = 286547) B286547
theorem B322123 : Blo 187803 322123 := bstep (se 1 (by rfl) ⟨241592, by rfl⟩ : syracuseStep 322123 = 483185) B483185
theorem B191051 : Blo 187803 191051 := bstep (se 1 (by rfl) ⟨143288, by rfl⟩ : syracuseStep 191051 = 286577) B286577
theorem B191063 : Blo 187803 191063 := bstep (se 1 (by rfl) ⟨143297, by rfl⟩ : syracuseStep 191063 = 286595) B286595
theorem B1632869 : Blo 187803 1632869 := bstep (se 4 (by rfl) ⟨153081, by rfl⟩ : syracuseStep 1632869 = 306163) B306163
theorem B191083 : Blo 187803 191083 := bstep (se 1 (by rfl) ⟨143312, by rfl⟩ : syracuseStep 191083 = 286625) B286625
theorem B191095 : Blo 187803 191095 := bstep (se 1 (by rfl) ⟨143321, by rfl⟩ : syracuseStep 191095 = 286643) B286643
theorem B191115 : Blo 187803 191115 := bstep (se 1 (by rfl) ⟨143336, by rfl⟩ : syracuseStep 191115 = 286673) B286673
theorem B191127 : Blo 187803 191127 := bstep (se 1 (by rfl) ⟨143345, by rfl⟩ : syracuseStep 191127 = 286691) B286691
theorem B191147 : Blo 187803 191147 := bstep (se 1 (by rfl) ⟨143360, by rfl⟩ : syracuseStep 191147 = 286721) B286721
theorem B191159 : Blo 187803 191159 := bstep (se 1 (by rfl) ⟨143369, by rfl⟩ : syracuseStep 191159 = 286739) B286739
theorem B191179 : Blo 187803 191179 := bstep (se 1 (by rfl) ⟨143384, by rfl⟩ : syracuseStep 191179 = 286769) B286769
theorem B191191 : Blo 187803 191191 := bstep (se 1 (by rfl) ⟨143393, by rfl⟩ : syracuseStep 191191 = 286787) B286787
theorem B322265 : Blo 187803 322265 := bstep (se 2 (by rfl) ⟨120849, by rfl⟩ : syracuseStep 322265 = 241699) B241699
theorem B191211 : Blo 187803 191211 := bstep (se 1 (by rfl) ⟨143408, by rfl⟩ : syracuseStep 191211 = 286817) B286817
theorem B191223 : Blo 187803 191223 := bstep (se 1 (by rfl) ⟨143417, by rfl⟩ : syracuseStep 191223 = 286835) B286835
theorem B191243 : Blo 187803 191243 := bstep (se 1 (by rfl) ⟨143432, by rfl⟩ : syracuseStep 191243 = 286865) B286865
theorem B191255 : Blo 187803 191255 := bstep (se 1 (by rfl) ⟨143441, by rfl⟩ : syracuseStep 191255 = 286883) B286883
theorem B191275 : Blo 187803 191275 := bstep (se 1 (by rfl) ⟨143456, by rfl⟩ : syracuseStep 191275 = 286913) B286913
theorem B191287 : Blo 187803 191287 := bstep (se 1 (by rfl) ⟨143465, by rfl⟩ : syracuseStep 191287 = 286931) B286931
theorem B1469249 : Blo 187803 1469249 := bstep (se 2 (by rfl) ⟨550968, by rfl⟩ : syracuseStep 1469249 = 1101937) B1101937
theorem B191307 : Blo 187803 191307 := bstep (se 1 (by rfl) ⟨143480, by rfl⟩ : syracuseStep 191307 = 286961) B286961
theorem B191319 : Blo 187803 191319 := bstep (se 1 (by rfl) ⟨143489, by rfl⟩ : syracuseStep 191319 = 286979) B286979
theorem B387929 : Blo 187803 387929 := bstep (se 2 (by rfl) ⟨145473, by rfl⟩ : syracuseStep 387929 = 290947) B290947
theorem B322393 : Blo 187803 322393 := bstep (se 2 (by rfl) ⟨120897, by rfl⟩ : syracuseStep 322393 = 241795) B241795
theorem B191339 : Blo 187803 191339 := bstep (se 1 (by rfl) ⟨143504, by rfl⟩ : syracuseStep 191339 = 287009) B287009
theorem B191351 : Blo 187803 191351 := bstep (se 1 (by rfl) ⟨143513, by rfl⟩ : syracuseStep 191351 = 287027) B287027
theorem B191371 : Blo 187803 191371 := bstep (se 1 (by rfl) ⟨143528, by rfl⟩ : syracuseStep 191371 = 287057) B287057
theorem B191383 : Blo 187803 191383 := bstep (se 1 (by rfl) ⟨143537, by rfl⟩ : syracuseStep 191383 = 287075) B287075
theorem B191403 : Blo 187803 191403 := bstep (se 1 (by rfl) ⟨143552, by rfl⟩ : syracuseStep 191403 = 287105) B287105
theorem B191415 : Blo 187803 191415 := bstep (se 1 (by rfl) ⟨143561, by rfl⟩ : syracuseStep 191415 = 287123) B287123
theorem B191435 : Blo 187803 191435 := bstep (se 1 (by rfl) ⟨143576, by rfl⟩ : syracuseStep 191435 = 287153) B287153
theorem B191447 : Blo 187803 191447 := bstep (se 1 (by rfl) ⟨143585, by rfl⟩ : syracuseStep 191447 = 287171) B287171
theorem B191467 : Blo 187803 191467 := bstep (se 1 (by rfl) ⟨143600, by rfl⟩ : syracuseStep 191467 = 287201) B287201
theorem B191479 : Blo 187803 191479 := bstep (se 1 (by rfl) ⟨143609, by rfl⟩ : syracuseStep 191479 = 287219) B287219
theorem B191499 : Blo 187803 191499 := bstep (se 1 (by rfl) ⟨143624, by rfl⟩ : syracuseStep 191499 = 287249) B287249
theorem B191511 : Blo 187803 191511 := bstep (se 1 (by rfl) ⟨143633, by rfl⟩ : syracuseStep 191511 = 287267) B287267
theorem B191531 : Blo 187803 191531 := bstep (se 1 (by rfl) ⟨143648, by rfl⟩ : syracuseStep 191531 = 287297) B287297
theorem B191543 : Blo 187803 191543 := bstep (se 1 (by rfl) ⟨143657, by rfl⟩ : syracuseStep 191543 = 287315) B287315
theorem B191563 : Blo 187803 191563 := bstep (se 1 (by rfl) ⟨143672, by rfl⟩ : syracuseStep 191563 = 287345) B287345
theorem B191575 : Blo 187803 191575 := bstep (se 1 (by rfl) ⟨143681, by rfl⟩ : syracuseStep 191575 = 287363) B287363
theorem B191595 : Blo 187803 191595 := bstep (se 1 (by rfl) ⟨143696, by rfl⟩ : syracuseStep 191595 = 287393) B287393
theorem B191607 : Blo 187803 191607 := bstep (se 1 (by rfl) ⟨143705, by rfl⟩ : syracuseStep 191607 = 287411) B287411
theorem B191627 : Blo 187803 191627 := bstep (se 1 (by rfl) ⟨143720, by rfl⟩ : syracuseStep 191627 = 287441) B287441
theorem B191639 : Blo 187803 191639 := bstep (se 1 (by rfl) ⟨143729, by rfl⟩ : syracuseStep 191639 = 287459) B287459
theorem B191659 : Blo 187803 191659 := bstep (se 1 (by rfl) ⟨143744, by rfl⟩ : syracuseStep 191659 = 287489) B287489
theorem B191671 : Blo 187803 191671 := bstep (se 1 (by rfl) ⟨143753, by rfl⟩ : syracuseStep 191671 = 287507) B287507
theorem B814283 : Blo 187803 814283 := bstep (se 1 (by rfl) ⟨610712, by rfl⟩ : syracuseStep 814283 = 1221425) B1221425
theorem B191691 : Blo 187803 191691 := bstep (se 1 (by rfl) ⟨143768, by rfl⟩ : syracuseStep 191691 = 287537) B287537
theorem B191703 : Blo 187803 191703 := bstep (se 1 (by rfl) ⟨143777, by rfl⟩ : syracuseStep 191703 = 287555) B287555
theorem B191723 : Blo 187803 191723 := bstep (se 1 (by rfl) ⟨143792, by rfl⟩ : syracuseStep 191723 = 287585) B287585
theorem B191735 : Blo 187803 191735 := bstep (se 1 (by rfl) ⟨143801, by rfl⟩ : syracuseStep 191735 = 287603) B287603
theorem B191755 : Blo 187803 191755 := bstep (se 1 (by rfl) ⟨143816, by rfl⟩ : syracuseStep 191755 = 287633) B287633
theorem B1633553 : Blo 187803 1633553 := bstep (se 2 (by rfl) ⟨612582, by rfl⟩ : syracuseStep 1633553 = 1225165) B1225165
theorem B486679 : Blo 187803 486679 := bstep (se 1 (by rfl) ⟨365009, by rfl⟩ : syracuseStep 486679 = 730019) B730019
theorem B191767 : Blo 187803 191767 := bstep (se 1 (by rfl) ⟨143825, by rfl⟩ : syracuseStep 191767 = 287651) B287651
theorem B191787 : Blo 187803 191787 := bstep (se 1 (by rfl) ⟨143840, by rfl⟩ : syracuseStep 191787 = 287681) B287681
theorem B191799 : Blo 187803 191799 := bstep (se 1 (by rfl) ⟨143849, by rfl⟩ : syracuseStep 191799 = 287699) B287699
theorem B781643 : Blo 187803 781643 := bstep (se 1 (by rfl) ⟨586232, by rfl⟩ : syracuseStep 781643 = 1172465) B1172465
theorem B322967 : Blo 187803 322967 := bstep (se 1 (by rfl) ⟨242225, by rfl⟩ : syracuseStep 322967 = 484451) B484451
theorem B650713 : Blo 187803 650713 := bstep (se 2 (by rfl) ⟨244017, by rfl⟩ : syracuseStep 650713 = 488035) B488035
theorem B847325 : Blo 187803 847325 := bstep (se 3 (by rfl) ⟨158873, by rfl⟩ : syracuseStep 847325 = 317747) B317747
theorem B323095 : Blo 187803 323095 := bstep (se 1 (by rfl) ⟨242321, by rfl⟩ : syracuseStep 323095 = 484643) B484643
theorem B814643 : Blo 187803 814643 := bstep (se 1 (by rfl) ⟨610982, by rfl⟩ : syracuseStep 814643 = 1221965) B1221965
theorem B1076915 : Blo 187803 1076915 := bstep (se 1 (by rfl) ⟨807686, by rfl⟩ : syracuseStep 1076915 = 1615373) B1615373
theorem B388979 : Blo 187803 388979 := bstep (se 1 (by rfl) ⟨291734, by rfl⟩ : syracuseStep 388979 = 583469) B583469
theorem B2060549 : Blo 187803 2060549 := bstep (se 4 (by rfl) ⟨193176, by rfl⟩ : syracuseStep 2060549 = 386353) B386353
theorem B356633 : Blo 187803 356633 := bstep (se 2 (by rfl) ⟨133737, by rfl⟩ : syracuseStep 356633 = 267475) B267475
theorem B258391 : Blo 187803 258391 := bstep (se 1 (by rfl) ⟨193793, by rfl⟩ : syracuseStep 258391 = 387587) B387587
theorem B258455 : Blo 187803 258455 := bstep (se 1 (by rfl) ⟨193841, by rfl⟩ : syracuseStep 258455 = 387683) B387683
theorem B717443 : Blo 187803 717443 := bstep (se 1 (by rfl) ⟨538082, by rfl⟩ : syracuseStep 717443 = 1076165) B1076165
theorem B717457 : Blo 187803 717457 := bstep (se 2 (by rfl) ⟨269046, by rfl⟩ : syracuseStep 717457 = 538093) B538093
theorem B357043 : Blo 187803 357043 := bstep (se 1 (by rfl) ⟨267782, by rfl⟩ : syracuseStep 357043 = 535565) B535565
theorem B422603 : Blo 187803 422603 := bstep (se 1 (by rfl) ⟨316952, by rfl⟩ : syracuseStep 422603 = 633905) B633905
theorem B422657 : Blo 187803 422657 := bstep (se 2 (by rfl) ⟨158496, by rfl⟩ : syracuseStep 422657 = 316993) B316993
theorem B717761 : Blo 187803 717761 := bstep (se 2 (by rfl) ⟨269160, by rfl⟩ : syracuseStep 717761 = 538321) B538321
theorem B422873 : Blo 187803 422873 := bstep (se 2 (by rfl) ⟨158577, by rfl⟩ : syracuseStep 422873 = 317155) B317155
theorem B422963 : Blo 187803 422963 := bstep (se 1 (by rfl) ⟨317222, by rfl⟩ : syracuseStep 422963 = 634445) B634445
theorem B259147 : Blo 187803 259147 := bstep (se 1 (by rfl) ⟨194360, by rfl⟩ : syracuseStep 259147 = 388721) B388721
theorem B422999 : Blo 187803 422999 := bstep (se 1 (by rfl) ⟨317249, by rfl⟩ : syracuseStep 422999 = 634499) B634499
theorem B1078373 : Blo 187803 1078373 := bstep (se 4 (by rfl) ⟨101097, by rfl⟩ : syracuseStep 1078373 = 202195) B202195
theorem B357529 : Blo 187803 357529 := bstep (se 2 (by rfl) ⟨134073, by rfl⟩ : syracuseStep 357529 = 268147) B268147
theorem B423179 : Blo 187803 423179 := bstep (se 1 (by rfl) ⟨317384, by rfl⟩ : syracuseStep 423179 = 634769) B634769
theorem B455959 : Blo 187803 455959 := bstep (se 1 (by rfl) ⟨341969, by rfl⟩ : syracuseStep 455959 = 683939) B683939
theorem B423233 : Blo 187803 423233 := bstep (se 2 (by rfl) ⟨158712, by rfl⟩ : syracuseStep 423233 = 317425) B317425
theorem B423449 : Blo 187803 423449 := bstep (se 2 (by rfl) ⟨158793, by rfl⟩ : syracuseStep 423449 = 317587) B317587
theorem B1078829 : Blo 187803 1078829 := bstep (se 3 (by rfl) ⟨202280, by rfl⟩ : syracuseStep 1078829 = 404561) B404561
theorem B718429 : Blo 187803 718429 := bstep (se 3 (by rfl) ⟨134705, by rfl⟩ : syracuseStep 718429 = 269411) B269411
theorem B423539 : Blo 187803 423539 := bstep (se 1 (by rfl) ⟨317654, by rfl⟩ : syracuseStep 423539 = 635309) B635309
theorem B423575 : Blo 187803 423575 := bstep (se 1 (by rfl) ⟨317681, by rfl⟩ : syracuseStep 423575 = 635363) B635363
theorem B358091 : Blo 187803 358091 := bstep (se 1 (by rfl) ⟨268568, by rfl⟩ : syracuseStep 358091 = 537137) B537137
theorem B915245 : Blo 187803 915245 := bstep (se 3 (by rfl) ⟨171608, by rfl⟩ : syracuseStep 915245 = 343217) B343217
theorem B2094913 : Blo 187803 2094913 := bstep (se 2 (by rfl) ⟨785592, by rfl⟩ : syracuseStep 2094913 = 1571185) B1571185
theorem B423755 : Blo 187803 423755 := bstep (se 1 (by rfl) ⟨317816, by rfl⟩ : syracuseStep 423755 = 635633) B635633
theorem B423809 : Blo 187803 423809 := bstep (se 2 (by rfl) ⟨158928, by rfl⟩ : syracuseStep 423809 = 317857) B317857
theorem B358273 : Blo 187803 358273 := bstep (se 2 (by rfl) ⟨134352, by rfl⟩ : syracuseStep 358273 = 268705) B268705
theorem B12318641 : Blo 187803 12318641 := bstep (se 2 (by rfl) ⟨4619490, by rfl⟩ : syracuseStep 12318641 = 9238981) B9238981
theorem B424025 : Blo 187803 424025 := bstep (se 2 (by rfl) ⟨159009, by rfl⟩ : syracuseStep 424025 = 318019) B318019
theorem B424115 : Blo 187803 424115 := bstep (se 1 (by rfl) ⟨318086, by rfl⟩ : syracuseStep 424115 = 636173) B636173
theorem B424151 : Blo 187803 424151 := bstep (se 1 (by rfl) ⟨318113, by rfl⟩ : syracuseStep 424151 = 636227) B636227
theorem B1079513 : Blo 187803 1079513 := bstep (se 2 (by rfl) ⟨404817, by rfl⟩ : syracuseStep 1079513 = 809635) B809635
theorem B1440017 : Blo 187803 1440017 := bstep (se 2 (by rfl) ⟨540006, by rfl⟩ : syracuseStep 1440017 = 1080013) B1080013
theorem B391475 : Blo 187803 391475 := bstep (se 1 (by rfl) ⟨293606, by rfl⟩ : syracuseStep 391475 = 587213) B587213
theorem B424331 : Blo 187803 424331 := bstep (se 1 (by rfl) ⟨318248, by rfl⟩ : syracuseStep 424331 = 636497) B636497
theorem B424385 : Blo 187803 424385 := bstep (se 2 (by rfl) ⟨159144, by rfl⟩ : syracuseStep 424385 = 318289) B318289
theorem B2980313 : Blo 187803 2980313 := bstep (se 2 (by rfl) ⟨1117617, by rfl⟩ : syracuseStep 2980313 = 2235235) B2235235
theorem B358987 : Blo 187803 358987 := bstep (se 1 (by rfl) ⟨269240, by rfl⟩ : syracuseStep 358987 = 538481) B538481
theorem B4651613 : Blo 187803 4651613 := bstep (se 3 (by rfl) ⟨872177, by rfl⟩ : syracuseStep 4651613 = 1744355) B1744355
theorem B359063 : Blo 187803 359063 := bstep (se 1 (by rfl) ⟨269297, by rfl⟩ : syracuseStep 359063 = 538595) B538595
theorem B424601 : Blo 187803 424601 := bstep (se 2 (by rfl) ⟨159225, by rfl⟩ : syracuseStep 424601 = 318451) B318451
theorem B1833677 : Blo 187803 1833677 := bstep (se 3 (by rfl) ⟨343814, by rfl⟩ : syracuseStep 1833677 = 687629) B687629
theorem B424691 : Blo 187803 424691 := bstep (se 1 (by rfl) ⟨318518, by rfl⟩ : syracuseStep 424691 = 637037) B637037
theorem B424727 : Blo 187803 424727 := bstep (se 1 (by rfl) ⟨318545, by rfl⟩ : syracuseStep 424727 = 637091) B637091
theorem B719705 : Blo 187803 719705 := bstep (se 2 (by rfl) ⟨269889, by rfl⟩ : syracuseStep 719705 = 539779) B539779
theorem B1538909 : Blo 187803 1538909 := bstep (se 3 (by rfl) ⟨288545, by rfl⟩ : syracuseStep 1538909 = 577091) B577091
theorem B424907 : Blo 187803 424907 := bstep (se 1 (by rfl) ⟨318680, by rfl⟩ : syracuseStep 424907 = 637361) B637361
theorem B424961 : Blo 187803 424961 := bstep (se 2 (by rfl) ⟨159360, by rfl⟩ : syracuseStep 424961 = 318721) B318721
theorem B916525 : Blo 187803 916525 := bstep (se 3 (by rfl) ⟨171848, by rfl⟩ : syracuseStep 916525 = 343697) B343697
theorem B687197 : Blo 187803 687197 := bstep (se 3 (by rfl) ⟨128849, by rfl⟩ : syracuseStep 687197 = 257699) B257699
theorem B425177 : Blo 187803 425177 := bstep (se 2 (by rfl) ⟨159441, by rfl⟩ : syracuseStep 425177 = 318883) B318883
theorem B228619 : Blo 187803 228619 := bstep (se 1 (by rfl) ⟨171464, by rfl⟩ : syracuseStep 228619 = 342929) B342929
theorem B425267 : Blo 187803 425267 := bstep (se 1 (by rfl) ⟨318950, by rfl⟩ : syracuseStep 425267 = 637901) B637901
theorem B359731 : Blo 187803 359731 := bstep (se 1 (by rfl) ⟨269798, by rfl⟩ : syracuseStep 359731 = 539597) B539597
theorem B425303 : Blo 187803 425303 := bstep (se 1 (by rfl) ⟨318977, by rfl⟩ : syracuseStep 425303 = 637955) B637955
theorem B326999 : Blo 187803 326999 := bstep (se 1 (by rfl) ⟨245249, by rfl⟩ : syracuseStep 326999 = 490499) B490499
theorem B1932761 : Blo 187803 1932761 := bstep (se 2 (by rfl) ⟨724785, by rfl⟩ : syracuseStep 1932761 = 1449571) B1449571
theorem B425483 : Blo 187803 425483 := bstep (se 1 (by rfl) ⟨319112, by rfl⟩ : syracuseStep 425483 = 638225) B638225
theorem B359959 : Blo 187803 359959 := bstep (se 1 (by rfl) ⟨269969, by rfl⟩ : syracuseStep 359959 = 539939) B539939
theorem B425537 : Blo 187803 425537 := bstep (se 2 (by rfl) ⟨159576, by rfl⟩ : syracuseStep 425537 = 319153) B319153
theorem B360065 : Blo 187803 360065 := bstep (se 2 (by rfl) ⟨135024, by rfl⟩ : syracuseStep 360065 = 270049) B270049
theorem B3899011 : Blo 187803 3899011 := bstep (se 1 (by rfl) ⟨2924258, by rfl⟩ : syracuseStep 3899011 = 5848517) B5848517
theorem B229015 : Blo 187803 229015 := bstep (se 1 (by rfl) ⟨171761, by rfl⟩ : syracuseStep 229015 = 343523) B343523
theorem B425753 : Blo 187803 425753 := bstep (se 2 (by rfl) ⟨159657, by rfl⟩ : syracuseStep 425753 = 319315) B319315
theorem B360217 : Blo 187803 360217 := bstep (se 2 (by rfl) ⟨135081, by rfl⟩ : syracuseStep 360217 = 270163) B270163
theorem B425843 : Blo 187803 425843 := bstep (se 1 (by rfl) ⟨319382, by rfl⟩ : syracuseStep 425843 = 638765) B638765
theorem B425879 : Blo 187803 425879 := bstep (se 1 (by rfl) ⟨319409, by rfl⟩ : syracuseStep 425879 = 638819) B638819
theorem B589853 : Blo 187803 589853 := bstep (se 3 (by rfl) ⟨110597, by rfl⟩ : syracuseStep 589853 = 221195) B221195
theorem B655447 : Blo 187803 655447 := bstep (se 1 (by rfl) ⟨491585, by rfl⟩ : syracuseStep 655447 = 983171) B983171
theorem B426131 : Blo 187803 426131 := bstep (se 1 (by rfl) ⟨319598, by rfl⟩ : syracuseStep 426131 = 639197) B639197
theorem B426185 : Blo 187803 426185 := bstep (se 2 (by rfl) ⟨159819, by rfl⟩ : syracuseStep 426185 = 319639) B319639
theorem B721133 : Blo 187803 721133 := bstep (se 3 (by rfl) ⟨135212, by rfl⟩ : syracuseStep 721133 = 270425) B270425
theorem B2031965 : Blo 187803 2031965 := bstep (se 3 (by rfl) ⟨380993, by rfl⟩ : syracuseStep 2031965 = 761987) B761987
theorem B2326877 : Blo 187803 2326877 := bstep (se 3 (by rfl) ⟨436289, by rfl⟩ : syracuseStep 2326877 = 872579) B872579
theorem B262535 : Blo 187803 262535 := bstep (se 1 (by rfl) ⟨196901, by rfl⟩ : syracuseStep 262535 = 393803) B393803
theorem B1081745 : Blo 187803 1081745 := bstep (se 2 (by rfl) ⟨405654, by rfl⟩ : syracuseStep 1081745 = 811309) B811309
theorem B459265 : Blo 187803 459265 := bstep (se 2 (by rfl) ⟨172224, by rfl⟩ : syracuseStep 459265 = 344449) B344449
theorem B1311275 : Blo 187803 1311275 := bstep (se 1 (by rfl) ⟨983456, by rfl⟩ : syracuseStep 1311275 = 1966913) B1966913
theorem B459553 : Blo 187803 459553 := bstep (se 2 (by rfl) ⟨172332, by rfl⟩ : syracuseStep 459553 = 344665) B344665
theorem B426887 : Blo 187803 426887 := bstep (se 1 (by rfl) ⟨320165, by rfl⟩ : syracuseStep 426887 = 640331) B640331
theorem B721817 : Blo 187803 721817 := bstep (se 2 (by rfl) ⟨270681, by rfl⟩ : syracuseStep 721817 = 541363) B541363
theorem B361417 : Blo 187803 361417 := bstep (se 2 (by rfl) ⟨135531, by rfl⟩ : syracuseStep 361417 = 271063) B271063
theorem B427067 : Blo 187803 427067 := bstep (se 1 (by rfl) ⟨320300, by rfl⟩ : syracuseStep 427067 = 640601) B640601
theorem B1082429 : Blo 187803 1082429 := bstep (se 3 (by rfl) ⟨202955, by rfl⟩ : syracuseStep 1082429 = 405911) B405911
theorem B689213 : Blo 187803 689213 := bstep (se 3 (by rfl) ⟨129227, by rfl⟩ : syracuseStep 689213 = 258455) B258455
theorem B427193 : Blo 187803 427193 := bstep (se 2 (by rfl) ⟨160197, by rfl⟩ : syracuseStep 427193 = 320395) B320395
theorem B427535 : Blo 187803 427535 := bstep (se 1 (by rfl) ⟨320651, by rfl⟩ : syracuseStep 427535 = 641303) B641303
theorem B427553 : Blo 187803 427553 := bstep (se 2 (by rfl) ⟨160332, by rfl⟩ : syracuseStep 427553 = 320665) B320665
theorem B4130605 : Blo 187803 4130605 := bstep (se 3 (by rfl) ⟨774488, by rfl⟩ : syracuseStep 4130605 = 1548977) B1548977
theorem B460603 : Blo 187803 460603 := bstep (se 1 (by rfl) ⟨345452, by rfl⟩ : syracuseStep 460603 = 690905) B690905
theorem B722803 : Blo 187803 722803 := bstep (se 1 (by rfl) ⟨542102, by rfl⟩ : syracuseStep 722803 = 1084205) B1084205
theorem B427895 : Blo 187803 427895 := bstep (se 1 (by rfl) ⟨320921, by rfl⟩ : syracuseStep 427895 = 641843) B641843
theorem B1542041 : Blo 187803 1542041 := bstep (se 2 (by rfl) ⟨578265, by rfl⟩ : syracuseStep 1542041 = 1156531) B1156531
theorem B428075 : Blo 187803 428075 := bstep (se 1 (by rfl) ⟨321056, by rfl⟩ : syracuseStep 428075 = 642113) B642113
theorem B952721 : Blo 187803 952721 := bstep (se 2 (by rfl) ⟨357270, by rfl⟩ : syracuseStep 952721 = 714541) B714541
theorem B1149329 : Blo 187803 1149329 := bstep (se 2 (by rfl) ⟨430998, by rfl⟩ : syracuseStep 1149329 = 861997) B861997
theorem B428435 : Blo 187803 428435 := bstep (se 1 (by rfl) ⟨321326, by rfl⟩ : syracuseStep 428435 = 642653) B642653
theorem B428489 : Blo 187803 428489 := bstep (se 2 (by rfl) ⟨160683, by rfl⟩ : syracuseStep 428489 = 321367) B321367
theorem B920335 : Blo 187803 920335 := bstep (se 1 (by rfl) ⟨690251, by rfl⟩ : syracuseStep 920335 = 1380503) B1380503
theorem B12389219 : Blo 187803 12389219 := bstep (se 1 (by rfl) ⟨9291914, by rfl⟩ : syracuseStep 12389219 = 18583829) B18583829
theorem B429191 : Blo 187803 429191 := bstep (se 1 (by rfl) ⟨321893, by rfl⟩ : syracuseStep 429191 = 643787) B643787
theorem B429371 : Blo 187803 429371 := bstep (se 1 (by rfl) ⟨322028, by rfl⟩ : syracuseStep 429371 = 644057) B644057
theorem B363923 : Blo 187803 363923 := bstep (se 1 (by rfl) ⟨272942, by rfl⟩ : syracuseStep 363923 = 545885) B545885
theorem B429497 : Blo 187803 429497 := bstep (se 2 (by rfl) ⟨161061, by rfl⟩ : syracuseStep 429497 = 322123) B322123
theorem B462395 : Blo 187803 462395 := bstep (se 1 (by rfl) ⟨346796, by rfl⟩ : syracuseStep 462395 = 693593) B693593
theorem B429715 : Blo 187803 429715 := bstep (se 1 (by rfl) ⟨322286, by rfl⟩ : syracuseStep 429715 = 644573) B644573
theorem B429839 : Blo 187803 429839 := bstep (se 1 (by rfl) ⟨322379, by rfl⟩ : syracuseStep 429839 = 644759) B644759
theorem B429857 : Blo 187803 429857 := bstep (se 2 (by rfl) ⟨161196, by rfl⟩ : syracuseStep 429857 = 322393) B322393
theorem B2723635 : Blo 187803 2723635 := bstep (se 1 (by rfl) ⟨2042726, by rfl⟩ : syracuseStep 2723635 = 4085453) B4085453
theorem B921395 : Blo 187803 921395 := bstep (se 1 (by rfl) ⟨691046, by rfl⟩ : syracuseStep 921395 = 1382093) B1382093
theorem B921547 : Blo 187803 921547 := bstep (se 1 (by rfl) ⟨691160, by rfl⟩ : syracuseStep 921547 = 1382321) B1382321
theorem B725021 : Blo 187803 725021 := bstep (se 3 (by rfl) ⟨135941, by rfl⟩ : syracuseStep 725021 = 271883) B271883
theorem B364603 : Blo 187803 364603 := bstep (se 1 (by rfl) ⟨273452, by rfl⟩ : syracuseStep 364603 = 546905) B546905
theorem B430199 : Blo 187803 430199 := bstep (se 1 (by rfl) ⟨322649, by rfl⟩ : syracuseStep 430199 = 645299) B645299
theorem B430379 : Blo 187803 430379 := bstep (se 1 (by rfl) ⟨322784, by rfl⟩ : syracuseStep 430379 = 645569) B645569
theorem B954827 : Blo 187803 954827 := bstep (se 1 (by rfl) ⟨716120, by rfl⟩ : syracuseStep 954827 = 1432241) B1432241
theorem B1446365 : Blo 187803 1446365 := bstep (se 3 (by rfl) ⟨271193, by rfl⟩ : syracuseStep 1446365 = 542387) B542387
theorem B430739 : Blo 187803 430739 := bstep (se 1 (by rfl) ⟨323054, by rfl⟩ : syracuseStep 430739 = 646109) B646109
theorem B725705 : Blo 187803 725705 := bstep (se 2 (by rfl) ⟨272139, by rfl⟩ : syracuseStep 725705 = 544279) B544279
theorem B430793 : Blo 187803 430793 := bstep (se 2 (by rfl) ⟨161547, by rfl⟩ : syracuseStep 430793 = 323095) B323095
theorem B955151 : Blo 187803 955151 := bstep (se 1 (by rfl) ⟨716363, by rfl⟩ : syracuseStep 955151 = 1432727) B1432727
theorem B365627 : Blo 187803 365627 := bstep (se 1 (by rfl) ⟨274220, by rfl⟩ : syracuseStep 365627 = 548441) B548441
theorem B2168045 : Blo 187803 2168045 := bstep (se 3 (by rfl) ⟨406508, by rfl⟩ : syracuseStep 2168045 = 813017) B813017
theorem B4658413 : Blo 187803 4658413 := bstep (se 3 (by rfl) ⟨873452, by rfl⟩ : syracuseStep 4658413 = 1746905) B1746905
theorem B431419 : Blo 187803 431419 := bstep (se 1 (by rfl) ⟨323564, by rfl⟩ : syracuseStep 431419 = 647129) B647129
theorem B7968131 : Blo 187803 7968131 := bstep (se 1 (by rfl) ⟨5976098, by rfl⟩ : syracuseStep 7968131 = 11952197) B11952197
theorem B431495 : Blo 187803 431495 := bstep (se 1 (by rfl) ⟨323621, by rfl⟩ : syracuseStep 431495 = 647243) B647243
theorem B1218091 : Blo 187803 1218091 := bstep (se 1 (by rfl) ⟨913568, by rfl⟩ : syracuseStep 1218091 = 1827137) B1827137
theorem B202375 : Blo 187803 202375 := bstep (se 1 (by rfl) ⟨151781, by rfl⟩ : syracuseStep 202375 = 303563) B303563
theorem B268039 : Blo 187803 268039 := bstep (se 1 (by rfl) ⟨201029, by rfl⟩ : syracuseStep 268039 = 402059) B402059
theorem B300935 : Blo 187803 300935 := bstep (se 1 (by rfl) ⟨225701, by rfl⟩ : syracuseStep 300935 = 451403) B451403
theorem B1611683 : Blo 187803 1611683 := bstep (se 1 (by rfl) ⟨1208762, by rfl⟩ : syracuseStep 1611683 = 2417525) B2417525
theorem B4954229 : Blo 187803 4954229 := bstep (se 5 (by rfl) ⟨232229, by rfl⟩ : syracuseStep 4954229 = 464459) B464459
theorem B956609 : Blo 187803 956609 := bstep (se 2 (by rfl) ⟨358728, by rfl⟩ : syracuseStep 956609 = 717457) B717457
theorem B727481 : Blo 187803 727481 := bstep (se 2 (by rfl) ⟨272805, by rfl⟩ : syracuseStep 727481 = 545611) B545611
theorem B203195 : Blo 187803 203195 := bstep (se 1 (by rfl) ⟨152396, by rfl⟩ : syracuseStep 203195 = 304793) B304793
theorem B268859 : Blo 187803 268859 := bstep (se 1 (by rfl) ⟨201644, by rfl⟩ : syracuseStep 268859 = 403289) B403289
theorem B1088579 : Blo 187803 1088579 := bstep (se 1 (by rfl) ⟨816434, by rfl⟩ : syracuseStep 1088579 = 1632869) B1632869
theorem B269497 : Blo 187803 269497 := bstep (se 2 (by rfl) ⟨101061, by rfl⟩ : syracuseStep 269497 = 202123) B202123
theorem B957905 : Blo 187803 957905 := bstep (se 2 (by rfl) ⟨359214, by rfl⟩ : syracuseStep 957905 = 718429) B718429
theorem B1089035 : Blo 187803 1089035 := bstep (se 1 (by rfl) ⟨816776, by rfl⟩ : syracuseStep 1089035 = 1633553) B1633553
theorem B728605 : Blo 187803 728605 := bstep (se 3 (by rfl) ⟨136613, by rfl⟩ : syracuseStep 728605 = 273227) B273227
theorem B2793217 : Blo 187803 2793217 := bstep (se 2 (by rfl) ⟨1047456, by rfl⟩ : syracuseStep 2793217 = 2094913) B2094913
theorem B7282709 : Blo 187803 7282709 := bstep (se 6 (by rfl) ⟨170688, by rfl⟩ : syracuseStep 7282709 = 341377) B341377
theorem B532595 : Blo 187803 532595 := bstep (se 1 (by rfl) ⟨399446, by rfl⟩ : syracuseStep 532595 = 798893) B798893
theorem B237755 : Blo 187803 237755 := bstep (se 1 (by rfl) ⟨178316, by rfl⟩ : syracuseStep 237755 = 356633) B356633
theorem B17375633 : Blo 187803 17375633 := bstep (se 2 (by rfl) ⟨6515862, by rfl⟩ : syracuseStep 17375633 = 13031725) B13031725
theorem B270983 : Blo 187803 270983 := bstep (se 1 (by rfl) ⟨203237, by rfl⟩ : syracuseStep 270983 = 406475) B406475
theorem B271291 : Blo 187803 271291 := bstep (se 1 (by rfl) ⟨203468, by rfl⟩ : syracuseStep 271291 = 406937) B406937
theorem B238727 : Blo 187803 238727 := bstep (se 1 (by rfl) ⟨179045, by rfl⟩ : syracuseStep 238727 = 358091) B358091
theorem B5154029 : Blo 187803 5154029 := bstep (se 3 (by rfl) ⟨966380, by rfl⟩ : syracuseStep 5154029 = 1932761) B1932761
theorem B1222033 : Blo 187803 1222033 := bstep (se 2 (by rfl) ⟨458262, by rfl⟩ : syracuseStep 1222033 = 916525) B916525
theorem B2172419 : Blo 187803 2172419 := bstep (se 1 (by rfl) ⟨1629314, by rfl⟩ : syracuseStep 2172419 = 3258629) B3258629
theorem B960011 : Blo 187803 960011 := bstep (se 1 (by rfl) ⟨720008, by rfl⟩ : syracuseStep 960011 = 1440017) B1440017
theorem B960173 : Blo 187803 960173 := bstep (se 3 (by rfl) ⟨180032, by rfl⟩ : syracuseStep 960173 = 360065) B360065
theorem B304825 : Blo 187803 304825 := bstep (se 2 (by rfl) ⟨114309, by rfl⟩ : syracuseStep 304825 = 228619) B228619
theorem B239375 : Blo 187803 239375 := bstep (se 1 (by rfl) ⟨179531, by rfl⟩ : syracuseStep 239375 = 359063) B359063
theorem B1222451 : Blo 187803 1222451 := bstep (se 1 (by rfl) ⟨916838, by rfl⟩ : syracuseStep 1222451 = 1833677) B1833677
theorem B1025939 : Blo 187803 1025939 := bstep (se 1 (by rfl) ⟨769454, by rfl⟩ : syracuseStep 1025939 = 1538909) B1538909
theorem B272441 : Blo 187803 272441 := bstep (se 2 (by rfl) ⟨102165, by rfl⟩ : syracuseStep 272441 = 204331) B204331
theorem B305353 : Blo 187803 305353 := bstep (se 2 (by rfl) ⟨114507, by rfl⟩ : syracuseStep 305353 = 229015) B229015
theorem B306055 : Blo 187803 306055 := bstep (se 1 (by rfl) ⟨229541, by rfl⟩ : syracuseStep 306055 = 459083) B459083
theorem B961793 : Blo 187803 961793 := bstep (se 2 (by rfl) ⟨360672, by rfl⟩ : syracuseStep 961793 = 721345) B721345
theorem B248491405 : Blo 187803 248491405 := bstep (se 3 (by rfl) ⟨46592138, by rfl⟩ : syracuseStep 248491405 = 93184277) B93184277
theorem B962603 : Blo 187803 962603 := bstep (se 1 (by rfl) ⟨721952, by rfl⟩ : syracuseStep 962603 = 1443905) B1443905
theorem B536635 : Blo 187803 536635 := bstep (se 1 (by rfl) ⟨402476, by rfl⟩ : syracuseStep 536635 = 804953) B804953
theorem B1224791 : Blo 187803 1224791 := bstep (se 1 (by rfl) ⟨918593, by rfl⟩ : syracuseStep 1224791 = 1837187) B1837187
theorem B242347 : Blo 187803 242347 := bstep (se 1 (by rfl) ⟨181760, by rfl⟩ : syracuseStep 242347 = 363521) B363521
theorem B537479 : Blo 187803 537479 := bstep (se 1 (by rfl) ⟨403109, by rfl⟩ : syracuseStep 537479 = 806219) B806219
theorem B635795 : Blo 187803 635795 := bstep (se 1 (by rfl) ⟨476846, by rfl⟩ : syracuseStep 635795 = 953693) B953693
theorem B2241433 : Blo 187803 2241433 := bstep (se 2 (by rfl) ⟨840537, by rfl⟩ : syracuseStep 2241433 = 1681075) B1681075
theorem B767177 : Blo 187803 767177 := bstep (se 2 (by rfl) ⟨287691, by rfl⟩ : syracuseStep 767177 = 575383) B575383
theorem B898249 : Blo 187803 898249 := bstep (se 2 (by rfl) ⟨336843, by rfl⟩ : syracuseStep 898249 = 673687) B673687
theorem B603407 : Blo 187803 603407 := bstep (se 1 (by rfl) ⟨452555, by rfl⟩ : syracuseStep 603407 = 905111) B905111
theorem B963899 : Blo 187803 963899 := bstep (se 1 (by rfl) ⟨722924, by rfl⟩ : syracuseStep 963899 = 1445849) B1445849
theorem B406919 : Blo 187803 406919 := bstep (se 1 (by rfl) ⟨305189, by rfl⟩ : syracuseStep 406919 = 610379) B610379
theorem B1455569 : Blo 187803 1455569 := bstep (se 2 (by rfl) ⟨545838, by rfl⟩ : syracuseStep 1455569 = 1091677) B1091677
theorem B964061 : Blo 187803 964061 := bstep (se 3 (by rfl) ⟨180761, by rfl⟩ : syracuseStep 964061 = 361523) B361523
theorem B603767 : Blo 187803 603767 := bstep (se 1 (by rfl) ⟨452825, by rfl⟩ : syracuseStep 603767 = 905651) B905651
theorem B538265 : Blo 187803 538265 := bstep (se 2 (by rfl) ⟨201849, by rfl⟩ : syracuseStep 538265 = 403699) B403699
theorem B1226497 : Blo 187803 1226497 := bstep (se 2 (by rfl) ⟨459936, by rfl⟩ : syracuseStep 1226497 = 919873) B919873
theorem B964385 : Blo 187803 964385 := bstep (se 2 (by rfl) ⟨361644, by rfl⟩ : syracuseStep 964385 = 723289) B723289
theorem B637199 : Blo 187803 637199 := bstep (se 1 (by rfl) ⟨477899, by rfl⟩ : syracuseStep 637199 = 955799) B955799
theorem B538913 : Blo 187803 538913 := bstep (se 2 (by rfl) ⟨202092, by rfl⟩ : syracuseStep 538913 = 404185) B404185
theorem B211387 : Blo 187803 211387 := bstep (se 1 (by rfl) ⟨158540, by rfl⟩ : syracuseStep 211387 = 317081) B317081
theorem B2144717 : Blo 187803 2144717 := bstep (se 3 (by rfl) ⟨402134, by rfl⟩ : syracuseStep 2144717 = 804269) B804269
theorem B4143581 : Blo 187803 4143581 := bstep (se 3 (by rfl) ⟨776921, by rfl⟩ : syracuseStep 4143581 = 1553843) B1553843
theorem B637469 : Blo 187803 637469 := bstep (se 3 (by rfl) ⟨119525, by rfl⟩ : syracuseStep 637469 = 239051) B239051
theorem B965357 : Blo 187803 965357 := bstep (se 3 (by rfl) ⟨181004, by rfl⟩ : syracuseStep 965357 = 362009) B362009
theorem B1522547 : Blo 187803 1522547 := bstep (se 1 (by rfl) ⟨1141910, by rfl⟩ : syracuseStep 1522547 = 2283821) B2283821
theorem B211855 : Blo 187803 211855 := bstep (se 1 (by rfl) ⟨158891, by rfl⟩ : syracuseStep 211855 = 317783) B317783
theorem B1358795 : Blo 187803 1358795 := bstep (se 1 (by rfl) ⟨1019096, by rfl⟩ : syracuseStep 1358795 = 2038193) B2038193
theorem B277705 : Blo 187803 277705 := bstep (se 2 (by rfl) ⟨104139, by rfl⟩ : syracuseStep 277705 = 208279) B208279
theorem B2604269 : Blo 187803 2604269 := bstep (se 3 (by rfl) ⟨488300, by rfl⟩ : syracuseStep 2604269 = 976601) B976601
theorem B539905 : Blo 187803 539905 := bstep (se 2 (by rfl) ⟨202464, by rfl⟩ : syracuseStep 539905 = 404929) B404929
theorem B867617 : Blo 187803 867617 := bstep (se 2 (by rfl) ⟨325356, by rfl⟩ : syracuseStep 867617 = 650713) B650713
theorem B212359 : Blo 187803 212359 := bstep (se 1 (by rfl) ⟨159269, by rfl⟩ : syracuseStep 212359 = 318539) B318539
theorem B671129 : Blo 187803 671129 := bstep (se 2 (by rfl) ⟨251673, by rfl⟩ : syracuseStep 671129 = 503347) B503347
theorem B1818065 : Blo 187803 1818065 := bstep (se 2 (by rfl) ⟨681774, by rfl⟩ : syracuseStep 1818065 = 1363549) B1363549
theorem B1621457 : Blo 187803 1621457 := bstep (se 2 (by rfl) ⟨608046, by rfl⟩ : syracuseStep 1621457 = 1216093) B1216093
theorem B966167 : Blo 187803 966167 := bstep (se 1 (by rfl) ⟨724625, by rfl⟩ : syracuseStep 966167 = 1449251) B1449251
theorem B212539 : Blo 187803 212539 := bstep (se 1 (by rfl) ⟨159404, by rfl⟩ : syracuseStep 212539 = 318809) B318809
theorem B802561 : Blo 187803 802561 := bstep (se 2 (by rfl) ⟨300960, by rfl⟩ : syracuseStep 802561 = 601921) B601921
theorem B638873 : Blo 187803 638873 := bstep (se 2 (by rfl) ⟨239577, by rfl⟩ : syracuseStep 638873 = 479155) B479155
theorem B213007 : Blo 187803 213007 := bstep (se 1 (by rfl) ⟨159755, by rfl⟩ : syracuseStep 213007 = 319511) B319511
theorem B3916097 : Blo 187803 3916097 := bstep (se 2 (by rfl) ⟨1468536, by rfl⟩ : syracuseStep 3916097 = 2937073) B2937073
theorem B344521 : Blo 187803 344521 := bstep (se 2 (by rfl) ⟨129195, by rfl⟩ : syracuseStep 344521 = 258391) B258391
theorem B213511 : Blo 187803 213511 := bstep (se 1 (by rfl) ⟨160133, by rfl⟩ : syracuseStep 213511 = 320267) B320267
theorem B639575 : Blo 187803 639575 := bstep (se 1 (by rfl) ⟨479681, by rfl⟩ : syracuseStep 639575 = 959363) B959363
theorem B213691 : Blo 187803 213691 := bstep (se 1 (by rfl) ⟨160268, by rfl⟩ : syracuseStep 213691 = 320537) B320537
theorem B475915 : Blo 187803 475915 := bstep (se 1 (by rfl) ⟨356936, by rfl⟩ : syracuseStep 475915 = 713873) B713873
theorem B476057 : Blo 187803 476057 := bstep (se 2 (by rfl) ⟨178521, by rfl⟩ : syracuseStep 476057 = 357043) B357043
theorem B476219 : Blo 187803 476219 := bstep (se 1 (by rfl) ⟨357164, by rfl⟩ : syracuseStep 476219 = 714329) B714329
theorem B640061 : Blo 187803 640061 := bstep (se 3 (by rfl) ⟨120011, by rfl⟩ : syracuseStep 640061 = 240023) B240023
theorem B214159 : Blo 187803 214159 := bstep (se 1 (by rfl) ⟨160619, by rfl⟩ : syracuseStep 214159 = 321239) B321239
theorem B345235 : Blo 187803 345235 := bstep (se 1 (by rfl) ⟨258926, by rfl⟩ : syracuseStep 345235 = 517853) B517853
theorem B476563 : Blo 187803 476563 := bstep (se 1 (by rfl) ⟨357422, by rfl⟩ : syracuseStep 476563 = 714845) B714845
theorem B345529 : Blo 187803 345529 := bstep (se 2 (by rfl) ⟨129573, by rfl⟩ : syracuseStep 345529 = 259147) B259147
theorem B476705 : Blo 187803 476705 := bstep (se 2 (by rfl) ⟨178764, by rfl⟩ : syracuseStep 476705 = 357529) B357529
theorem B214663 : Blo 187803 214663 := bstep (se 1 (by rfl) ⟨160997, by rfl⟩ : syracuseStep 214663 = 321995) B321995
theorem B607945 : Blo 187803 607945 := bstep (se 2 (by rfl) ⟨227979, by rfl⟩ : syracuseStep 607945 = 455959) B455959
theorem B214843 : Blo 187803 214843 := bstep (se 1 (by rfl) ⟨161132, by rfl⟩ : syracuseStep 214843 = 322265) B322265
theorem B509981 : Blo 187803 509981 := bstep (se 3 (by rfl) ⟨95621, by rfl⟩ : syracuseStep 509981 = 191243) B191243
theorem B510067 : Blo 187803 510067 := bstep (se 1 (by rfl) ⟨382550, by rfl⟩ : syracuseStep 510067 = 765101) B765101
theorem B542855 : Blo 187803 542855 := bstep (se 1 (by rfl) ⟨407141, by rfl⟩ : syracuseStep 542855 = 814283) B814283
theorem B575623 : Blo 187803 575623 := bstep (se 1 (by rfl) ⟨431717, by rfl⟩ : syracuseStep 575623 = 863435) B863435
theorem B215311 : Blo 187803 215311 := bstep (se 1 (by rfl) ⟨161483, by rfl⟩ : syracuseStep 215311 = 322967) B322967
theorem B1820987 : Blo 187803 1820987 := bstep (se 1 (by rfl) ⟨1365740, by rfl⟩ : syracuseStep 1820987 = 2731481) B2731481
theorem B543037 : Blo 187803 543037 := bstep (se 3 (by rfl) ⟨101819, by rfl⟩ : syracuseStep 543037 = 203639) B203639
theorem B543095 : Blo 187803 543095 := bstep (se 1 (by rfl) ⟨407321, by rfl⟩ : syracuseStep 543095 = 814643) B814643
theorem B641465 : Blo 187803 641465 := bstep (se 2 (by rfl) ⟨240549, by rfl⟩ : syracuseStep 641465 = 481099) B481099
theorem B477697 : Blo 187803 477697 := bstep (se 2 (by rfl) ⟨179136, by rfl⟩ : syracuseStep 477697 = 358273) B358273
theorem B969245 : Blo 187803 969245 := bstep (se 3 (by rfl) ⟨181733, by rfl⟩ : syracuseStep 969245 = 363467) B363467
theorem B903881 : Blo 187803 903881 := bstep (se 2 (by rfl) ⟨338955, by rfl⟩ : syracuseStep 903881 = 677911) B677911
theorem B1624805 : Blo 187803 1624805 := bstep (se 4 (by rfl) ⟨152325, by rfl⟩ : syracuseStep 1624805 = 304651) B304651
theorem B969731 : Blo 187803 969731 := bstep (se 1 (by rfl) ⟨727298, by rfl⟩ : syracuseStep 969731 = 1454597) B1454597
theorem B2411531 : Blo 187803 2411531 := bstep (se 1 (by rfl) ⟨1808648, by rfl⟩ : syracuseStep 2411531 = 3617297) B3617297
theorem B642059 : Blo 187803 642059 := bstep (se 1 (by rfl) ⟨481544, by rfl⟩ : syracuseStep 642059 = 963089) B963089
theorem B478295 : Blo 187803 478295 := bstep (se 1 (by rfl) ⟨358721, by rfl⟩ : syracuseStep 478295 = 717443) B717443
theorem B642167 : Blo 187803 642167 := bstep (se 1 (by rfl) ⟨481625, by rfl⟩ : syracuseStep 642167 = 963251) B963251
theorem B4574339 : Blo 187803 4574339 := bstep (se 1 (by rfl) ⟨3430754, by rfl⟩ : syracuseStep 4574339 = 6861509) B6861509
theorem B281735 : Blo 187803 281735 := bstep (se 1 (by rfl) ⟨211301, by rfl⟩ : syracuseStep 281735 = 422603) B422603
theorem B281771 : Blo 187803 281771 := bstep (se 1 (by rfl) ⟨211328, by rfl⟩ : syracuseStep 281771 = 422657) B422657
theorem B281801 : Blo 187803 281801 := bstep (se 2 (by rfl) ⟨105675, by rfl⟩ : syracuseStep 281801 = 211351) B211351
theorem B478507 : Blo 187803 478507 := bstep (se 1 (by rfl) ⟨358880, by rfl⟩ : syracuseStep 478507 = 717761) B717761
theorem B281915 : Blo 187803 281915 := bstep (se 1 (by rfl) ⟨211436, by rfl⟩ : syracuseStep 281915 = 422873) B422873
theorem B281975 : Blo 187803 281975 := bstep (se 1 (by rfl) ⟨211481, by rfl⟩ : syracuseStep 281975 = 422963) B422963
theorem B281999 : Blo 187803 281999 := bstep (se 1 (by rfl) ⟨211499, by rfl⟩ : syracuseStep 281999 = 422999) B422999
theorem B544153 : Blo 187803 544153 := bstep (se 2 (by rfl) ⟨204057, by rfl⟩ : syracuseStep 544153 = 408115) B408115
theorem B282041 : Blo 187803 282041 := bstep (se 2 (by rfl) ⟨105765, by rfl⟩ : syracuseStep 282041 = 211531) B211531
theorem B478649 : Blo 187803 478649 := bstep (se 2 (by rfl) ⟨179493, by rfl⟩ : syracuseStep 478649 = 358987) B358987
theorem B282119 : Blo 187803 282119 := bstep (se 1 (by rfl) ⟨211589, by rfl⟩ : syracuseStep 282119 = 423179) B423179
theorem B282155 : Blo 187803 282155 := bstep (se 1 (by rfl) ⟨211616, by rfl⟩ : syracuseStep 282155 = 423233) B423233
theorem B282185 : Blo 187803 282185 := bstep (se 2 (by rfl) ⟨105819, by rfl⟩ : syracuseStep 282185 = 211639) B211639
theorem B282299 : Blo 187803 282299 := bstep (se 1 (by rfl) ⟨211724, by rfl⟩ : syracuseStep 282299 = 423449) B423449
theorem B642761 : Blo 187803 642761 := bstep (se 2 (by rfl) ⟨241035, by rfl⟩ : syracuseStep 642761 = 482071) B482071
theorem B282359 : Blo 187803 282359 := bstep (se 1 (by rfl) ⟨211769, by rfl⟩ : syracuseStep 282359 = 423539) B423539
theorem B282383 : Blo 187803 282383 := bstep (se 1 (by rfl) ⟨211787, by rfl⟩ : syracuseStep 282383 = 423575) B423575
theorem B3624749 : Blo 187803 3624749 := bstep (se 3 (by rfl) ⟨679640, by rfl⟩ : syracuseStep 3624749 = 1359281) B1359281
theorem B282425 : Blo 187803 282425 := bstep (se 2 (by rfl) ⟨105909, by rfl⟩ : syracuseStep 282425 = 211819) B211819
theorem B610163 : Blo 187803 610163 := bstep (se 1 (by rfl) ⟨457622, by rfl⟩ : syracuseStep 610163 = 915245) B915245
theorem B282503 : Blo 187803 282503 := bstep (se 1 (by rfl) ⟨211877, by rfl⟩ : syracuseStep 282503 = 423755) B423755
theorem B282539 : Blo 187803 282539 := bstep (se 1 (by rfl) ⟨211904, by rfl⟩ : syracuseStep 282539 = 423809) B423809
theorem B282569 : Blo 187803 282569 := bstep (se 2 (by rfl) ⟨105963, by rfl⟩ : syracuseStep 282569 = 211927) B211927
theorem B8212427 : Blo 187803 8212427 := bstep (se 1 (by rfl) ⟨6159320, by rfl⟩ : syracuseStep 8212427 = 12318641) B12318641
theorem B544769 : Blo 187803 544769 := bstep (se 2 (by rfl) ⟨204288, by rfl⟩ : syracuseStep 544769 = 408577) B408577
theorem B282683 : Blo 187803 282683 := bstep (se 1 (by rfl) ⟨212012, by rfl⟩ : syracuseStep 282683 = 424025) B424025
theorem B282743 : Blo 187803 282743 := bstep (se 1 (by rfl) ⟨212057, by rfl⟩ : syracuseStep 282743 = 424115) B424115
theorem B282767 : Blo 187803 282767 := bstep (se 1 (by rfl) ⟨212075, by rfl⟩ : syracuseStep 282767 = 424151) B424151
theorem B282809 : Blo 187803 282809 := bstep (se 2 (by rfl) ⟨106053, by rfl⟩ : syracuseStep 282809 = 212107) B212107
theorem B282887 : Blo 187803 282887 := bstep (se 1 (by rfl) ⟨212165, by rfl⟩ : syracuseStep 282887 = 424331) B424331
theorem B282923 : Blo 187803 282923 := bstep (se 1 (by rfl) ⟨212192, by rfl⟩ : syracuseStep 282923 = 424385) B424385
theorem B1986875 : Blo 187803 1986875 := bstep (se 1 (by rfl) ⟨1490156, by rfl⟩ : syracuseStep 1986875 = 2980313) B2980313
theorem B282953 : Blo 187803 282953 := bstep (se 2 (by rfl) ⟨106107, by rfl⟩ : syracuseStep 282953 = 212215) B212215
theorem B643463 : Blo 187803 643463 := bstep (se 1 (by rfl) ⟨482597, by rfl⟩ : syracuseStep 643463 = 965195) B965195
theorem B3101075 : Blo 187803 3101075 := bstep (se 1 (by rfl) ⟨2325806, by rfl⟩ : syracuseStep 3101075 = 4651613) B4651613
theorem B479641 : Blo 187803 479641 := bstep (se 2 (by rfl) ⟨179865, by rfl⟩ : syracuseStep 479641 = 359731) B359731
theorem B283067 : Blo 187803 283067 := bstep (se 1 (by rfl) ⟨212300, by rfl⟩ : syracuseStep 283067 = 424601) B424601
theorem B283127 : Blo 187803 283127 := bstep (se 1 (by rfl) ⟨212345, by rfl⟩ : syracuseStep 283127 = 424691) B424691
theorem B283151 : Blo 187803 283151 := bstep (se 1 (by rfl) ⟨212363, by rfl⟩ : syracuseStep 283151 = 424727) B424727
theorem B283193 : Blo 187803 283193 := bstep (se 2 (by rfl) ⟨106197, by rfl⟩ : syracuseStep 283193 = 212395) B212395
theorem B479803 : Blo 187803 479803 := bstep (se 1 (by rfl) ⟨359852, by rfl⟩ : syracuseStep 479803 = 719705) B719705
theorem B283271 : Blo 187803 283271 := bstep (se 1 (by rfl) ⟨212453, by rfl⟩ : syracuseStep 283271 = 424907) B424907
theorem B283307 : Blo 187803 283307 := bstep (se 1 (by rfl) ⟨212480, by rfl⟩ : syracuseStep 283307 = 424961) B424961
theorem B1823411 : Blo 187803 1823411 := bstep (se 1 (by rfl) ⟨1367558, by rfl⟩ : syracuseStep 1823411 = 2735117) B2735117
theorem B283337 : Blo 187803 283337 := bstep (se 2 (by rfl) ⟨106251, by rfl⟩ : syracuseStep 283337 = 212503) B212503
theorem B479945 : Blo 187803 479945 := bstep (se 2 (by rfl) ⟨179979, by rfl⟩ : syracuseStep 479945 = 359959) B359959
theorem B643841 : Blo 187803 643841 := bstep (se 2 (by rfl) ⟨241440, by rfl⟩ : syracuseStep 643841 = 482881) B482881
theorem B283451 : Blo 187803 283451 := bstep (se 1 (by rfl) ⟨212588, by rfl⟩ : syracuseStep 283451 = 425177) B425177
theorem B5198681 : Blo 187803 5198681 := bstep (se 2 (by rfl) ⟨1949505, by rfl⟩ : syracuseStep 5198681 = 3899011) B3899011
theorem B283511 : Blo 187803 283511 := bstep (se 1 (by rfl) ⟨212633, by rfl⟩ : syracuseStep 283511 = 425267) B425267
theorem B283535 : Blo 187803 283535 := bstep (se 1 (by rfl) ⟨212651, by rfl⟩ : syracuseStep 283535 = 425303) B425303
theorem B217999 : Blo 187803 217999 := bstep (se 1 (by rfl) ⟨163499, by rfl⟩ : syracuseStep 217999 = 326999) B326999
theorem B283577 : Blo 187803 283577 := bstep (se 2 (by rfl) ⟨106341, by rfl⟩ : syracuseStep 283577 = 212683) B212683
theorem B545737 : Blo 187803 545737 := bstep (se 2 (by rfl) ⟨204651, by rfl⟩ : syracuseStep 545737 = 409303) B409303
theorem B283655 : Blo 187803 283655 := bstep (se 1 (by rfl) ⟨212741, by rfl⟩ : syracuseStep 283655 = 425483) B425483
theorem B480289 : Blo 187803 480289 := bstep (se 2 (by rfl) ⟨180108, by rfl⟩ : syracuseStep 480289 = 360217) B360217
theorem B283691 : Blo 187803 283691 := bstep (se 1 (by rfl) ⟨212768, by rfl⟩ : syracuseStep 283691 = 425537) B425537
theorem B283721 : Blo 187803 283721 := bstep (se 2 (by rfl) ⟨106395, by rfl⟩ : syracuseStep 283721 = 212791) B212791
theorem B283835 : Blo 187803 283835 := bstep (se 1 (by rfl) ⟨212876, by rfl⟩ : syracuseStep 283835 = 425753) B425753
theorem B283895 : Blo 187803 283895 := bstep (se 1 (by rfl) ⟨212921, by rfl⟩ : syracuseStep 283895 = 425843) B425843
theorem B906497 : Blo 187803 906497 := bstep (se 2 (by rfl) ⟨339936, by rfl⟩ : syracuseStep 906497 = 679873) B679873
theorem B283919 : Blo 187803 283919 := bstep (se 1 (by rfl) ⟨212939, by rfl⟩ : syracuseStep 283919 = 425879) B425879
theorem B1365281 : Blo 187803 1365281 := bstep (se 2 (by rfl) ⟨511980, by rfl⟩ : syracuseStep 1365281 = 1023961) B1023961
theorem B513323 : Blo 187803 513323 := bstep (se 1 (by rfl) ⟨384992, by rfl⟩ : syracuseStep 513323 = 769985) B769985
theorem B283961 : Blo 187803 283961 := bstep (se 2 (by rfl) ⟨106485, by rfl⟩ : syracuseStep 283961 = 212971) B212971
theorem B284039 : Blo 187803 284039 := bstep (se 1 (by rfl) ⟨213029, by rfl⟩ : syracuseStep 284039 = 426059) B426059
theorem B284075 : Blo 187803 284075 := bstep (se 1 (by rfl) ⟨213056, by rfl⟩ : syracuseStep 284075 = 426113) B426113
theorem B284105 : Blo 187803 284105 := bstep (se 2 (by rfl) ⟨106539, by rfl⟩ : syracuseStep 284105 = 213079) B213079
theorem B644651 : Blo 187803 644651 := bstep (se 1 (by rfl) ⟨483488, by rfl⟩ : syracuseStep 644651 = 966977) B966977
theorem B284219 : Blo 187803 284219 := bstep (se 1 (by rfl) ⟨213164, by rfl⟩ : syracuseStep 284219 = 426329) B426329
theorem B317047 : Blo 187803 317047 := bstep (se 1 (by rfl) ⟨237785, by rfl⟩ : syracuseStep 317047 = 475571) B475571
theorem B284279 : Blo 187803 284279 := bstep (se 1 (by rfl) ⟨213209, by rfl⟩ : syracuseStep 284279 = 426419) B426419
theorem B480887 : Blo 187803 480887 := bstep (se 1 (by rfl) ⟨360665, by rfl⟩ : syracuseStep 480887 = 721331) B721331
theorem B284303 : Blo 187803 284303 := bstep (se 1 (by rfl) ⟨213227, by rfl⟩ : syracuseStep 284303 = 426455) B426455
theorem B1070765 : Blo 187803 1070765 := bstep (se 3 (by rfl) ⟨200768, by rfl⟩ : syracuseStep 1070765 = 401537) B401537
theorem B284345 : Blo 187803 284345 := bstep (se 2 (by rfl) ⟨106629, by rfl⟩ : syracuseStep 284345 = 213259) B213259
theorem B1431269 : Blo 187803 1431269 := bstep (se 4 (by rfl) ⟨134181, by rfl⟩ : syracuseStep 1431269 = 268363) B268363
theorem B284423 : Blo 187803 284423 := bstep (se 1 (by rfl) ⟨213317, by rfl⟩ : syracuseStep 284423 = 426635) B426635
theorem B284459 : Blo 187803 284459 := bstep (se 1 (by rfl) ⟨213344, by rfl⟩ : syracuseStep 284459 = 426689) B426689
theorem B317243 : Blo 187803 317243 := bstep (se 1 (by rfl) ⟨237932, by rfl⟩ : syracuseStep 317243 = 475865) B475865
theorem B284489 : Blo 187803 284489 := bstep (se 2 (by rfl) ⟨106683, by rfl⟩ : syracuseStep 284489 = 213367) B213367
theorem B776051 : Blo 187803 776051 := bstep (se 1 (by rfl) ⟨582038, by rfl⟩ : syracuseStep 776051 = 1164077) B1164077
theorem B284603 : Blo 187803 284603 := bstep (se 1 (by rfl) ⟨213452, by rfl⟩ : syracuseStep 284603 = 426905) B426905
theorem B284663 : Blo 187803 284663 := bstep (se 1 (by rfl) ⟨213497, by rfl⟩ : syracuseStep 284663 = 426995) B426995
theorem B284687 : Blo 187803 284687 := bstep (se 1 (by rfl) ⟨213515, by rfl⟩ : syracuseStep 284687 = 427031) B427031
theorem B284729 : Blo 187803 284729 := bstep (se 2 (by rfl) ⟨106773, by rfl⟩ : syracuseStep 284729 = 213547) B213547
theorem B1628221 : Blo 187803 1628221 := bstep (se 3 (by rfl) ⟨305291, by rfl⟩ : syracuseStep 1628221 = 610583) B610583
theorem B284807 : Blo 187803 284807 := bstep (se 1 (by rfl) ⟨213605, by rfl⟩ : syracuseStep 284807 = 427211) B427211
theorem B284843 : Blo 187803 284843 := bstep (se 1 (by rfl) ⟨213632, by rfl⟩ : syracuseStep 284843 = 427265) B427265
theorem B317641 : Blo 187803 317641 := bstep (se 2 (by rfl) ⟨119115, by rfl⟩ : syracuseStep 317641 = 238231) B238231
theorem B284873 : Blo 187803 284873 := bstep (se 2 (by rfl) ⟨106827, by rfl⟩ : syracuseStep 284873 = 213655) B213655
theorem B612623 : Blo 187803 612623 := bstep (se 1 (by rfl) ⟨459467, by rfl⟩ : syracuseStep 612623 = 918935) B918935
theorem B907571 : Blo 187803 907571 := bstep (se 1 (by rfl) ⟨680678, by rfl⟩ : syracuseStep 907571 = 1361357) B1361357
theorem B284987 : Blo 187803 284987 := bstep (se 1 (by rfl) ⟨213740, by rfl⟩ : syracuseStep 284987 = 427481) B427481
theorem B285047 : Blo 187803 285047 := bstep (se 1 (by rfl) ⟨213785, by rfl⟩ : syracuseStep 285047 = 427571) B427571
theorem B285071 : Blo 187803 285071 := bstep (se 1 (by rfl) ⟨213803, by rfl⟩ : syracuseStep 285071 = 427607) B427607
theorem B285113 : Blo 187803 285113 := bstep (se 2 (by rfl) ⟨106917, by rfl⟩ : syracuseStep 285113 = 213835) B213835
theorem B285191 : Blo 187803 285191 := bstep (se 1 (by rfl) ⟨213893, by rfl⟩ : syracuseStep 285191 = 427787) B427787
theorem B285227 : Blo 187803 285227 := bstep (se 1 (by rfl) ⟨213920, by rfl⟩ : syracuseStep 285227 = 427841) B427841
theorem B285257 : Blo 187803 285257 := bstep (se 2 (by rfl) ⟨106971, by rfl⟩ : syracuseStep 285257 = 213943) B213943
theorem B285371 : Blo 187803 285371 := bstep (se 1 (by rfl) ⟨214028, by rfl⟩ : syracuseStep 285371 = 428057) B428057
theorem B285431 : Blo 187803 285431 := bstep (se 1 (by rfl) ⟨214073, by rfl⟩ : syracuseStep 285431 = 428147) B428147
theorem B285455 : Blo 187803 285455 := bstep (se 1 (by rfl) ⟨214091, by rfl⟩ : syracuseStep 285455 = 428183) B428183
theorem B285497 : Blo 187803 285497 := bstep (se 2 (by rfl) ⟨107061, by rfl⟩ : syracuseStep 285497 = 214123) B214123
theorem B645947 : Blo 187803 645947 := bstep (se 1 (by rfl) ⟨484460, by rfl⟩ : syracuseStep 645947 = 968921) B968921
theorem B318343 : Blo 187803 318343 := bstep (se 1 (by rfl) ⟨238757, by rfl⟩ : syracuseStep 318343 = 477515) B477515
theorem B285575 : Blo 187803 285575 := bstep (se 1 (by rfl) ⟨214181, by rfl⟩ : syracuseStep 285575 = 428363) B428363
theorem B482183 : Blo 187803 482183 := bstep (se 1 (by rfl) ⟨361637, by rfl⟩ : syracuseStep 482183 = 723275) B723275
theorem B285611 : Blo 187803 285611 := bstep (se 1 (by rfl) ⟨214208, by rfl⟩ : syracuseStep 285611 = 428417) B428417
theorem B482233 : Blo 187803 482233 := bstep (se 2 (by rfl) ⟨180837, by rfl⟩ : syracuseStep 482233 = 361675) B361675
theorem B285641 : Blo 187803 285641 := bstep (se 2 (by rfl) ⟨107115, by rfl⟩ : syracuseStep 285641 = 214231) B214231
theorem B285755 : Blo 187803 285755 := bstep (se 1 (by rfl) ⟨214316, by rfl⟩ : syracuseStep 285755 = 428633) B428633
theorem B285815 : Blo 187803 285815 := bstep (se 1 (by rfl) ⟨214361, by rfl⟩ : syracuseStep 285815 = 428723) B428723
theorem B285839 : Blo 187803 285839 := bstep (se 1 (by rfl) ⟨214379, by rfl⟩ : syracuseStep 285839 = 428759) B428759
theorem B285881 : Blo 187803 285881 := bstep (se 2 (by rfl) ⟨107205, by rfl⟩ : syracuseStep 285881 = 214411) B214411
theorem B14277829 : Blo 187803 14277829 := bstep (se 4 (by rfl) ⟨1338546, by rfl⟩ : syracuseStep 14277829 = 2677093) B2677093
theorem B285959 : Blo 187803 285959 := bstep (se 1 (by rfl) ⟨214469, by rfl⟩ : syracuseStep 285959 = 428939) B428939
theorem B646433 : Blo 187803 646433 := bstep (se 2 (by rfl) ⟨242412, by rfl⟩ : syracuseStep 646433 = 484825) B484825
theorem B285995 : Blo 187803 285995 := bstep (se 1 (by rfl) ⟨214496, by rfl⟩ : syracuseStep 285995 = 428993) B428993
theorem B286025 : Blo 187803 286025 := bstep (se 2 (by rfl) ⟨107259, by rfl⟩ : syracuseStep 286025 = 214519) B214519
theorem B286087 : Blo 187803 286087 := bstep (se 1 (by rfl) ⟨214565, by rfl⟩ : syracuseStep 286087 = 429131) B429131
theorem B187835 : Blo 187803 187835 := bstep (se 1 (by rfl) ⟨140876, by rfl⟩ : syracuseStep 187835 = 281753) B281753
theorem B286139 : Blo 187803 286139 := bstep (se 1 (by rfl) ⟨214604, by rfl⟩ : syracuseStep 286139 = 429209) B429209
theorem B286199 : Blo 187803 286199 := bstep (se 1 (by rfl) ⟨214649, by rfl⟩ : syracuseStep 286199 = 429299) B429299
theorem B187911 : Blo 187803 187911 := bstep (se 1 (by rfl) ⟨140933, by rfl⟩ : syracuseStep 187911 = 281867) B281867
theorem B187919 : Blo 187803 187919 := bstep (se 1 (by rfl) ⟨140939, by rfl⟩ : syracuseStep 187919 = 281879) B281879
theorem B318991 : Blo 187803 318991 := bstep (se 1 (by rfl) ⟨239243, by rfl⟩ : syracuseStep 318991 = 478487) B478487
theorem B482831 : Blo 187803 482831 := bstep (se 1 (by rfl) ⟨362123, by rfl⟩ : syracuseStep 482831 = 724247) B724247
theorem B286223 : Blo 187803 286223 := bstep (se 1 (by rfl) ⟨214667, by rfl⟩ : syracuseStep 286223 = 429335) B429335
theorem B286265 : Blo 187803 286265 := bstep (se 2 (by rfl) ⟨107349, by rfl⟩ : syracuseStep 286265 = 214699) B214699
theorem B187963 : Blo 187803 187963 := bstep (se 1 (by rfl) ⟨140972, by rfl⟩ : syracuseStep 187963 = 281945) B281945
theorem B810557 : Blo 187803 810557 := bstep (se 3 (by rfl) ⟨151979, by rfl⟩ : syracuseStep 810557 = 303959) B303959
theorem B188039 : Blo 187803 188039 := bstep (se 1 (by rfl) ⟨141029, by rfl⟩ : syracuseStep 188039 = 282059) B282059
theorem B286343 : Blo 187803 286343 := bstep (se 1 (by rfl) ⟨214757, by rfl⟩ : syracuseStep 286343 = 429515) B429515
theorem B188047 : Blo 187803 188047 := bstep (se 1 (by rfl) ⟨141035, by rfl⟩ : syracuseStep 188047 = 282071) B282071
theorem B286379 : Blo 187803 286379 := bstep (se 1 (by rfl) ⟨214784, by rfl⟩ : syracuseStep 286379 = 429569) B429569
theorem B188091 : Blo 187803 188091 := bstep (se 1 (by rfl) ⟨141068, by rfl⟩ : syracuseStep 188091 = 282137) B282137
theorem B286409 : Blo 187803 286409 := bstep (se 2 (by rfl) ⟨107403, by rfl⟩ : syracuseStep 286409 = 214807) B214807
theorem B188167 : Blo 187803 188167 := bstep (se 1 (by rfl) ⟨141125, by rfl⟩ : syracuseStep 188167 = 282251) B282251
theorem B188175 : Blo 187803 188175 := bstep (se 1 (by rfl) ⟨141131, by rfl⟩ : syracuseStep 188175 = 282263) B282263
theorem B188219 : Blo 187803 188219 := bstep (se 1 (by rfl) ⟨141164, by rfl⟩ : syracuseStep 188219 = 282329) B282329
theorem B286523 : Blo 187803 286523 := bstep (se 1 (by rfl) ⟨214892, by rfl⟩ : syracuseStep 286523 = 429785) B429785
theorem B548669 : Blo 187803 548669 := bstep (se 3 (by rfl) ⟨102875, by rfl⟩ : syracuseStep 548669 = 205751) B205751
theorem B647027 : Blo 187803 647027 := bstep (se 1 (by rfl) ⟨485270, by rfl⟩ : syracuseStep 647027 = 970541) B970541
theorem B286583 : Blo 187803 286583 := bstep (se 1 (by rfl) ⟨214937, by rfl⟩ : syracuseStep 286583 = 429875) B429875
theorem B188295 : Blo 187803 188295 := bstep (se 1 (by rfl) ⟨141221, by rfl⟩ : syracuseStep 188295 = 282443) B282443
theorem B188303 : Blo 187803 188303 := bstep (se 1 (by rfl) ⟨141227, by rfl⟩ : syracuseStep 188303 = 282455) B282455
theorem B286607 : Blo 187803 286607 := bstep (se 1 (by rfl) ⟨214955, by rfl⟩ : syracuseStep 286607 = 429911) B429911
theorem B286649 : Blo 187803 286649 := bstep (se 2 (by rfl) ⟨107493, by rfl⟩ : syracuseStep 286649 = 214987) B214987
theorem B188347 : Blo 187803 188347 := bstep (se 1 (by rfl) ⟨141260, by rfl⟩ : syracuseStep 188347 = 282521) B282521
theorem B286651 : Blo 187803 286651 := bstep (se 1 (by rfl) ⟨214988, by rfl⟩ : syracuseStep 286651 = 429977) B429977
theorem B188423 : Blo 187803 188423 := bstep (se 1 (by rfl) ⟨141317, by rfl⟩ : syracuseStep 188423 = 282635) B282635
theorem B286727 : Blo 187803 286727 := bstep (se 1 (by rfl) ⟨215045, by rfl⟩ : syracuseStep 286727 = 430091) B430091
theorem B188431 : Blo 187803 188431 := bstep (se 1 (by rfl) ⟨141323, by rfl⟩ : syracuseStep 188431 = 282647) B282647
theorem B614429 : Blo 187803 614429 := bstep (se 3 (by rfl) ⟨115205, by rfl⟩ : syracuseStep 614429 = 230411) B230411
theorem B319531 : Blo 187803 319531 := bstep (se 1 (by rfl) ⟨239648, by rfl⟩ : syracuseStep 319531 = 479297) B479297
theorem B286763 : Blo 187803 286763 := bstep (se 1 (by rfl) ⟨215072, by rfl⟩ : syracuseStep 286763 = 430145) B430145
theorem B188475 : Blo 187803 188475 := bstep (se 1 (by rfl) ⟨141356, by rfl⟩ : syracuseStep 188475 = 282713) B282713
theorem B286793 : Blo 187803 286793 := bstep (se 2 (by rfl) ⟨107547, by rfl⟩ : syracuseStep 286793 = 215095) B215095
theorem B188551 : Blo 187803 188551 := bstep (se 1 (by rfl) ⟨141413, by rfl⟩ : syracuseStep 188551 = 282827) B282827
theorem B188559 : Blo 187803 188559 := bstep (se 1 (by rfl) ⟨141419, by rfl⟩ : syracuseStep 188559 = 282839) B282839
theorem B319673 : Blo 187803 319673 := bstep (se 2 (by rfl) ⟨119877, by rfl⟩ : syracuseStep 319673 = 239755) B239755
theorem B188603 : Blo 187803 188603 := bstep (se 1 (by rfl) ⟨141452, by rfl⟩ : syracuseStep 188603 = 282905) B282905
theorem B286907 : Blo 187803 286907 := bstep (se 1 (by rfl) ⟨215180, by rfl⟩ : syracuseStep 286907 = 430361) B430361
theorem B483529 : Blo 187803 483529 := bstep (se 2 (by rfl) ⟨181323, by rfl⟩ : syracuseStep 483529 = 362647) B362647
theorem B286967 : Blo 187803 286967 := bstep (se 1 (by rfl) ⟨215225, by rfl⟩ : syracuseStep 286967 = 430451) B430451
theorem B188679 : Blo 187803 188679 := bstep (se 1 (by rfl) ⟨141509, by rfl⟩ : syracuseStep 188679 = 283019) B283019
theorem B188687 : Blo 187803 188687 := bstep (se 1 (by rfl) ⟨141515, by rfl⟩ : syracuseStep 188687 = 283031) B283031
theorem B286991 : Blo 187803 286991 := bstep (se 1 (by rfl) ⟨215243, by rfl⟩ : syracuseStep 286991 = 430487) B430487
theorem B188731 : Blo 187803 188731 := bstep (se 1 (by rfl) ⟨141548, by rfl⟩ : syracuseStep 188731 = 283097) B283097
theorem B287033 : Blo 187803 287033 := bstep (se 2 (by rfl) ⟨107637, by rfl⟩ : syracuseStep 287033 = 215275) B215275
theorem B483671 : Blo 187803 483671 := bstep (se 1 (by rfl) ⟨362753, by rfl⟩ : syracuseStep 483671 = 725507) B725507
theorem B188807 : Blo 187803 188807 := bstep (se 1 (by rfl) ⟨141605, by rfl⟩ : syracuseStep 188807 = 283211) B283211
theorem B287111 : Blo 187803 287111 := bstep (se 1 (by rfl) ⟨215333, by rfl⟩ : syracuseStep 287111 = 430667) B430667
theorem B188815 : Blo 187803 188815 := bstep (se 1 (by rfl) ⟨141611, by rfl⟩ : syracuseStep 188815 = 283223) B283223
theorem B287147 : Blo 187803 287147 := bstep (se 1 (by rfl) ⟨215360, by rfl⟩ : syracuseStep 287147 = 430721) B430721
theorem B188859 : Blo 187803 188859 := bstep (se 1 (by rfl) ⟨141644, by rfl⟩ : syracuseStep 188859 = 283289) B283289
theorem B287177 : Blo 187803 287177 := bstep (se 2 (by rfl) ⟨107691, by rfl⟩ : syracuseStep 287177 = 215383) B215383
theorem B188935 : Blo 187803 188935 := bstep (se 1 (by rfl) ⟨141701, by rfl⟩ : syracuseStep 188935 = 283403) B283403
theorem B188943 : Blo 187803 188943 := bstep (se 1 (by rfl) ⟨141707, by rfl⟩ : syracuseStep 188943 = 283415) B283415
theorem B188987 : Blo 187803 188987 := bstep (se 1 (by rfl) ⟨141740, by rfl⟩ : syracuseStep 188987 = 283481) B283481
theorem B287291 : Blo 187803 287291 := bstep (se 1 (by rfl) ⟨215468, by rfl⟩ : syracuseStep 287291 = 430937) B430937
theorem B287351 : Blo 187803 287351 := bstep (se 1 (by rfl) ⟨215513, by rfl⟩ : syracuseStep 287351 = 431027) B431027
theorem B189063 : Blo 187803 189063 := bstep (se 1 (by rfl) ⟨141797, by rfl⟩ : syracuseStep 189063 = 283595) B283595
theorem B189071 : Blo 187803 189071 := bstep (se 1 (by rfl) ⟨141803, by rfl⟩ : syracuseStep 189071 = 283607) B283607
theorem B287375 : Blo 187803 287375 := bstep (se 1 (by rfl) ⟨215531, by rfl⟩ : syracuseStep 287375 = 431063) B431063
theorem B287417 : Blo 187803 287417 := bstep (se 2 (by rfl) ⟨107781, by rfl⟩ : syracuseStep 287417 = 215563) B215563
theorem B189115 : Blo 187803 189115 := bstep (se 1 (by rfl) ⟨141836, by rfl⟩ : syracuseStep 189115 = 283673) B283673
theorem B189191 : Blo 187803 189191 := bstep (se 1 (by rfl) ⟨141893, by rfl⟩ : syracuseStep 189191 = 283787) B283787
theorem B287495 : Blo 187803 287495 := bstep (se 1 (by rfl) ⟨215621, by rfl⟩ : syracuseStep 287495 = 431243) B431243
theorem B189199 : Blo 187803 189199 := bstep (se 1 (by rfl) ⟨141899, by rfl⟩ : syracuseStep 189199 = 283799) B283799
theorem B287531 : Blo 187803 287531 := bstep (se 1 (by rfl) ⟨215648, by rfl⟩ : syracuseStep 287531 = 431297) B431297
theorem B189243 : Blo 187803 189243 := bstep (se 1 (by rfl) ⟨141932, by rfl⟩ : syracuseStep 189243 = 283865) B283865
theorem B287561 : Blo 187803 287561 := bstep (se 2 (by rfl) ⟨107835, by rfl⟩ : syracuseStep 287561 = 215671) B215671
theorem B320375 : Blo 187803 320375 := bstep (se 1 (by rfl) ⟨240281, by rfl⟩ : syracuseStep 320375 = 480563) B480563
theorem B189319 : Blo 187803 189319 := bstep (se 1 (by rfl) ⟨141989, by rfl⟩ : syracuseStep 189319 = 283979) B283979
theorem B189327 : Blo 187803 189327 := bstep (se 1 (by rfl) ⟨141995, by rfl⟩ : syracuseStep 189327 = 283991) B283991
theorem B8479667 : Blo 187803 8479667 := bstep (se 1 (by rfl) ⟨6359750, by rfl⟩ : syracuseStep 8479667 = 12719501) B12719501
theorem B189371 : Blo 187803 189371 := bstep (se 1 (by rfl) ⟨142028, by rfl⟩ : syracuseStep 189371 = 284057) B284057
theorem B287675 : Blo 187803 287675 := bstep (se 1 (by rfl) ⟨215756, by rfl⟩ : syracuseStep 287675 = 431513) B431513
theorem B189447 : Blo 187803 189447 := bstep (se 1 (by rfl) ⟨142085, by rfl⟩ : syracuseStep 189447 = 284171) B284171
theorem B451595 : Blo 187803 451595 := bstep (se 1 (by rfl) ⟨338696, by rfl⟩ : syracuseStep 451595 = 677393) B677393
theorem B287759 : Blo 187803 287759 := bstep (se 1 (by rfl) ⟨215819, by rfl⟩ : syracuseStep 287759 = 431639) B431639
theorem B189455 : Blo 187803 189455 := bstep (se 1 (by rfl) ⟨142091, by rfl⟩ : syracuseStep 189455 = 284183) B284183
theorem B189499 : Blo 187803 189499 := bstep (se 1 (by rfl) ⟨142124, by rfl⟩ : syracuseStep 189499 = 284249) B284249
theorem B189575 : Blo 187803 189575 := bstep (se 1 (by rfl) ⟨142181, by rfl⟩ : syracuseStep 189575 = 284363) B284363
theorem B189583 : Blo 187803 189583 := bstep (se 1 (by rfl) ⟨142187, by rfl⟩ : syracuseStep 189583 = 284375) B284375
theorem B189627 : Blo 187803 189627 := bstep (se 1 (by rfl) ⟨142220, by rfl⟩ : syracuseStep 189627 = 284441) B284441
theorem B189703 : Blo 187803 189703 := bstep (se 1 (by rfl) ⟨142277, by rfl⟩ : syracuseStep 189703 = 284555) B284555
theorem B451855 : Blo 187803 451855 := bstep (se 1 (by rfl) ⟨338891, by rfl⟩ : syracuseStep 451855 = 677783) B677783
theorem B189711 : Blo 187803 189711 := bstep (se 1 (by rfl) ⟨142283, by rfl⟩ : syracuseStep 189711 = 284567) B284567
theorem B189755 : Blo 187803 189755 := bstep (se 1 (by rfl) ⟨142316, by rfl⟩ : syracuseStep 189755 = 284633) B284633
theorem B320827 : Blo 187803 320827 := bstep (se 1 (by rfl) ⟨240620, by rfl⟩ : syracuseStep 320827 = 481241) B481241
theorem B189831 : Blo 187803 189831 := bstep (se 1 (by rfl) ⟨142373, by rfl⟩ : syracuseStep 189831 = 284747) B284747
theorem B189839 : Blo 187803 189839 := bstep (se 1 (by rfl) ⟨142379, by rfl⟩ : syracuseStep 189839 = 284759) B284759
theorem B189883 : Blo 187803 189883 := bstep (se 1 (by rfl) ⟨142412, by rfl⟩ : syracuseStep 189883 = 284825) B284825
theorem B320969 : Blo 187803 320969 := bstep (se 2 (by rfl) ⟨120363, by rfl⟩ : syracuseStep 320969 = 240727) B240727
theorem B2450897 : Blo 187803 2450897 := bstep (se 2 (by rfl) ⟨919086, by rfl⟩ : syracuseStep 2450897 = 1838173) B1838173
theorem B189959 : Blo 187803 189959 := bstep (se 1 (by rfl) ⟨142469, by rfl⟩ : syracuseStep 189959 = 284939) B284939
theorem B189967 : Blo 187803 189967 := bstep (se 1 (by rfl) ⟨142475, by rfl⟩ : syracuseStep 189967 = 284951) B284951
theorem B190011 : Blo 187803 190011 := bstep (se 1 (by rfl) ⟨142508, by rfl⟩ : syracuseStep 190011 = 285017) B285017
theorem B714359 : Blo 187803 714359 := bstep (se 1 (by rfl) ⟨535769, by rfl⟩ : syracuseStep 714359 = 1071539) B1071539
theorem B190087 : Blo 187803 190087 := bstep (se 1 (by rfl) ⟨142565, by rfl⟩ : syracuseStep 190087 = 285131) B285131
theorem B190095 : Blo 187803 190095 := bstep (se 1 (by rfl) ⟨142571, by rfl⟩ : syracuseStep 190095 = 285143) B285143
theorem B452249 : Blo 187803 452249 := bstep (se 2 (by rfl) ⟨169593, by rfl⟩ : syracuseStep 452249 = 339187) B339187
theorem B288427 : Blo 187803 288427 := bstep (se 1 (by rfl) ⟨216320, by rfl⟩ : syracuseStep 288427 = 432641) B432641
theorem B190139 : Blo 187803 190139 := bstep (se 1 (by rfl) ⟨142604, by rfl⟩ : syracuseStep 190139 = 285209) B285209
theorem B648905 : Blo 187803 648905 := bstep (se 2 (by rfl) ⟨243339, by rfl⟩ : syracuseStep 648905 = 486679) B486679
theorem B190215 : Blo 187803 190215 := bstep (se 1 (by rfl) ⟨142661, by rfl⟩ : syracuseStep 190215 = 285323) B285323
theorem B190223 : Blo 187803 190223 := bstep (se 1 (by rfl) ⟨142667, by rfl⟩ : syracuseStep 190223 = 285335) B285335
theorem B485153 : Blo 187803 485153 := bstep (se 2 (by rfl) ⟨181932, by rfl⟩ : syracuseStep 485153 = 363865) B363865
theorem B190267 : Blo 187803 190267 := bstep (se 1 (by rfl) ⟨142700, by rfl⟩ : syracuseStep 190267 = 285401) B285401
theorem B190343 : Blo 187803 190343 := bstep (se 1 (by rfl) ⟨142757, by rfl⟩ : syracuseStep 190343 = 285515) B285515
theorem B190351 : Blo 187803 190351 := bstep (se 1 (by rfl) ⟨142763, by rfl⟩ : syracuseStep 190351 = 285527) B285527
theorem B190395 : Blo 187803 190395 := bstep (se 1 (by rfl) ⟨142796, by rfl⟩ : syracuseStep 190395 = 285593) B285593
theorem B190471 : Blo 187803 190471 := bstep (se 1 (by rfl) ⟨142853, by rfl⟩ : syracuseStep 190471 = 285707) B285707
theorem B190479 : Blo 187803 190479 := bstep (se 1 (by rfl) ⟨142859, by rfl⟩ : syracuseStep 190479 = 285719) B285719
theorem B190523 : Blo 187803 190523 := bstep (se 1 (by rfl) ⟨142892, by rfl⟩ : syracuseStep 190523 = 285785) B285785
theorem B518231 : Blo 187803 518231 := bstep (se 1 (by rfl) ⟨388673, by rfl⟩ : syracuseStep 518231 = 777347) B777347
theorem B190599 : Blo 187803 190599 := bstep (se 1 (by rfl) ⟨142949, by rfl⟩ : syracuseStep 190599 = 285899) B285899
theorem B321671 : Blo 187803 321671 := bstep (se 1 (by rfl) ⟨241253, by rfl⟩ : syracuseStep 321671 = 482507) B482507
theorem B190607 : Blo 187803 190607 := bstep (se 1 (by rfl) ⟨142955, by rfl⟩ : syracuseStep 190607 = 285911) B285911
theorem B6973613 : Blo 187803 6973613 := bstep (se 3 (by rfl) ⟨1307552, by rfl⟩ : syracuseStep 6973613 = 2615105) B2615105
theorem B190651 : Blo 187803 190651 := bstep (se 1 (by rfl) ⟨142988, by rfl⟩ : syracuseStep 190651 = 285977) B285977
theorem B1075457 : Blo 187803 1075457 := bstep (se 2 (by rfl) ⟨403296, by rfl⟩ : syracuseStep 1075457 = 806593) B806593
theorem B190727 : Blo 187803 190727 := bstep (se 1 (by rfl) ⟨143045, by rfl⟩ : syracuseStep 190727 = 286091) B286091
theorem B190735 : Blo 187803 190735 := bstep (se 1 (by rfl) ⟨143051, by rfl⟩ : syracuseStep 190735 = 286103) B286103
theorem B190779 : Blo 187803 190779 := bstep (se 1 (by rfl) ⟨143084, by rfl⟩ : syracuseStep 190779 = 286169) B286169
theorem B256375 : Blo 187803 256375 := bstep (se 1 (by rfl) ⟨192281, by rfl⟩ : syracuseStep 256375 = 384563) B384563
theorem B190855 : Blo 187803 190855 := bstep (se 1 (by rfl) ⟨143141, by rfl⟩ : syracuseStep 190855 = 286283) B286283
theorem B190863 : Blo 187803 190863 := bstep (se 1 (by rfl) ⟨143147, by rfl⟩ : syracuseStep 190863 = 286295) B286295
theorem B453017 : Blo 187803 453017 := bstep (se 2 (by rfl) ⟨169881, by rfl⟩ : syracuseStep 453017 = 339763) B339763
theorem B190907 : Blo 187803 190907 := bstep (se 1 (by rfl) ⟨143180, by rfl⟩ : syracuseStep 190907 = 286361) B286361
theorem B3434993 : Blo 187803 3434993 := bstep (se 2 (by rfl) ⟨1288122, by rfl⟩ : syracuseStep 3434993 = 2576245) B2576245
theorem B190983 : Blo 187803 190983 := bstep (se 1 (by rfl) ⟨143237, by rfl⟩ : syracuseStep 190983 = 286475) B286475
theorem B190991 : Blo 187803 190991 := bstep (se 1 (by rfl) ⟨143243, by rfl⟩ : syracuseStep 190991 = 286487) B286487
theorem B191035 : Blo 187803 191035 := bstep (se 1 (by rfl) ⟨143276, by rfl⟩ : syracuseStep 191035 = 286553) B286553
theorem B715331 : Blo 187803 715331 := bstep (se 1 (by rfl) ⟨536498, by rfl⟩ : syracuseStep 715331 = 1072997) B1072997
theorem B191111 : Blo 187803 191111 := bstep (se 1 (by rfl) ⟨143333, by rfl⟩ : syracuseStep 191111 = 286667) B286667
theorem B191119 : Blo 187803 191119 := bstep (se 1 (by rfl) ⟨143339, by rfl⟩ : syracuseStep 191119 = 286679) B286679
theorem B191163 : Blo 187803 191163 := bstep (se 1 (by rfl) ⟨143372, by rfl⟩ : syracuseStep 191163 = 286745) B286745
theorem B1075913 : Blo 187803 1075913 := bstep (se 2 (by rfl) ⟨403467, by rfl⟩ : syracuseStep 1075913 = 806935) B806935
theorem B191239 : Blo 187803 191239 := bstep (se 1 (by rfl) ⟨143429, by rfl⟩ : syracuseStep 191239 = 286859) B286859
theorem B322319 : Blo 187803 322319 := bstep (se 1 (by rfl) ⟨241739, by rfl⟩ : syracuseStep 322319 = 483479) B483479
theorem B191247 : Blo 187803 191247 := bstep (se 1 (by rfl) ⟨143435, by rfl⟩ : syracuseStep 191247 = 286871) B286871
theorem B191291 : Blo 187803 191291 := bstep (se 1 (by rfl) ⟨143468, by rfl⟩ : syracuseStep 191291 = 286937) B286937
theorem B813959 : Blo 187803 813959 := bstep (se 1 (by rfl) ⟨610469, by rfl⟩ : syracuseStep 813959 = 1220939) B1220939
theorem B191367 : Blo 187803 191367 := bstep (se 1 (by rfl) ⟨143525, by rfl⟩ : syracuseStep 191367 = 287051) B287051
theorem B191375 : Blo 187803 191375 := bstep (se 1 (by rfl) ⟨143531, by rfl⟩ : syracuseStep 191375 = 287063) B287063
theorem B814009 : Blo 187803 814009 := bstep (se 2 (by rfl) ⟨305253, by rfl⟩ : syracuseStep 814009 = 610507) B610507
theorem B191419 : Blo 187803 191419 := bstep (se 1 (by rfl) ⟨143564, by rfl⟩ : syracuseStep 191419 = 287129) B287129
theorem B191495 : Blo 187803 191495 := bstep (se 1 (by rfl) ⟨143621, by rfl⟩ : syracuseStep 191495 = 287243) B287243
theorem B715787 : Blo 187803 715787 := bstep (se 1 (by rfl) ⟨536840, by rfl⟩ : syracuseStep 715787 = 1073681) B1073681
theorem B191503 : Blo 187803 191503 := bstep (se 1 (by rfl) ⟨143627, by rfl⟩ : syracuseStep 191503 = 287255) B287255
theorem B191547 : Blo 187803 191547 := bstep (se 1 (by rfl) ⟨143660, by rfl⟩ : syracuseStep 191547 = 287321) B287321
theorem B191623 : Blo 187803 191623 := bstep (se 1 (by rfl) ⟨143717, by rfl⟩ : syracuseStep 191623 = 287435) B287435
theorem B191631 : Blo 187803 191631 := bstep (se 1 (by rfl) ⟨143723, by rfl⟩ : syracuseStep 191631 = 287447) B287447
theorem B191675 : Blo 187803 191675 := bstep (se 1 (by rfl) ⟨143756, by rfl⟩ : syracuseStep 191675 = 287513) B287513
theorem B257287 : Blo 187803 257287 := bstep (se 1 (by rfl) ⟨192965, by rfl⟩ : syracuseStep 257287 = 385931) B385931
theorem B191751 : Blo 187803 191751 := bstep (se 1 (by rfl) ⟨143813, by rfl⟩ : syracuseStep 191751 = 287627) B287627
theorem B191759 : Blo 187803 191759 := bstep (se 1 (by rfl) ⟨143819, by rfl⟩ : syracuseStep 191759 = 287639) B287639
theorem B322859 : Blo 187803 322859 := bstep (se 1 (by rfl) ⟨242144, by rfl⟩ : syracuseStep 322859 = 484289) B484289
theorem B191803 : Blo 187803 191803 := bstep (se 1 (by rfl) ⟨143852, by rfl⟩ : syracuseStep 191803 = 287705) B287705
theorem B1142225 : Blo 187803 1142225 := bstep (se 2 (by rfl) ⟨428334, by rfl⟩ : syracuseStep 1142225 = 856669) B856669
theorem B323257 : Blo 187803 323257 := bstep (se 2 (by rfl) ⟨121221, by rfl⟩ : syracuseStep 323257 = 242443) B242443
theorem B454547 : Blo 187803 454547 := bstep (se 1 (by rfl) ⟨340910, by rfl⟩ : syracuseStep 454547 = 681821) B681821
theorem B5009501 : Blo 187803 5009501 := bstep (se 3 (by rfl) ⟨939281, by rfl⟩ : syracuseStep 5009501 = 1878563) B1878563
theorem B815341 : Blo 187803 815341 := bstep (se 3 (by rfl) ⟨152876, by rfl⟩ : syracuseStep 815341 = 305753) B305753
theorem B291131 : Blo 187803 291131 := bstep (se 1 (by rfl) ⟨218348, by rfl⟩ : syracuseStep 291131 = 436697) B436697
theorem B619019 : Blo 187803 619019 := bstep (se 1 (by rfl) ⟨464264, by rfl⟩ : syracuseStep 619019 = 928529) B928529
theorem B979499 : Blo 187803 979499 := bstep (se 1 (by rfl) ⟨734624, by rfl⟩ : syracuseStep 979499 = 1469249) B1469249
theorem B258619 : Blo 187803 258619 := bstep (se 1 (by rfl) ⟨193964, by rfl⟩ : syracuseStep 258619 = 387929) B387929
theorem B815683 : Blo 187803 815683 := bstep (se 1 (by rfl) ⟨611762, by rfl⟩ : syracuseStep 815683 = 1223525) B1223525
theorem B422585 : Blo 187803 422585 := bstep (se 2 (by rfl) ⟨158469, by rfl⟩ : syracuseStep 422585 = 316939) B316939
theorem B2159297 : Blo 187803 2159297 := bstep (se 2 (by rfl) ⟨809736, by rfl⟩ : syracuseStep 2159297 = 1619473) B1619473
theorem B684935 : Blo 187803 684935 := bstep (se 1 (by rfl) ⟨513701, by rfl⟩ : syracuseStep 684935 = 1027403) B1027403
theorem B521095 : Blo 187803 521095 := bstep (se 1 (by rfl) ⟨390821, by rfl⟩ : syracuseStep 521095 = 781643) B781643
theorem B422927 : Blo 187803 422927 := bstep (se 1 (by rfl) ⟨317195, by rfl⟩ : syracuseStep 422927 = 634391) B634391
theorem B422945 : Blo 187803 422945 := bstep (se 2 (by rfl) ⟨158604, by rfl⟩ : syracuseStep 422945 = 317209) B317209
theorem B717943 : Blo 187803 717943 := bstep (se 1 (by rfl) ⟨538457, by rfl⟩ : syracuseStep 717943 = 1076915) B1076915
theorem B259319 : Blo 187803 259319 := bstep (se 1 (by rfl) ⟨194489, by rfl⟩ : syracuseStep 259319 = 388979) B388979
theorem B423287 : Blo 187803 423287 := bstep (se 1 (by rfl) ⟨317465, by rfl⟩ : syracuseStep 423287 = 634931) B634931
theorem B20903345 : Blo 187803 20903345 := bstep (se 2 (by rfl) ⟨7838754, by rfl⟩ : syracuseStep 20903345 = 15677509) B15677509
theorem B357833 : Blo 187803 357833 := bstep (se 2 (by rfl) ⟨134187, by rfl⟩ : syracuseStep 357833 = 268375) B268375
theorem B1373699 : Blo 187803 1373699 := bstep (se 1 (by rfl) ⟨1030274, by rfl⟩ : syracuseStep 1373699 = 2060549) B2060549
theorem B423467 : Blo 187803 423467 := bstep (se 1 (by rfl) ⟨317600, by rfl⟩ : syracuseStep 423467 = 635201) B635201
theorem B423827 : Blo 187803 423827 := bstep (se 1 (by rfl) ⟨317870, by rfl⟩ : syracuseStep 423827 = 635741) B635741
theorem B423881 : Blo 187803 423881 := bstep (se 2 (by rfl) ⟨158955, by rfl⟩ : syracuseStep 423881 = 317911) B317911
theorem B718915 : Blo 187803 718915 := bstep (se 1 (by rfl) ⟨539186, by rfl⟩ : syracuseStep 718915 = 1078373) B1078373
theorem B719219 : Blo 187803 719219 := bstep (se 1 (by rfl) ⟨539414, by rfl⟩ : syracuseStep 719219 = 1078829) B1078829
theorem B1079831 : Blo 187803 1079831 := bstep (se 1 (by rfl) ⟨809873, by rfl⟩ : syracuseStep 1079831 = 1619747) B1619747
theorem B2259533 : Blo 187803 2259533 := bstep (se 3 (by rfl) ⟨423662, by rfl⟩ : syracuseStep 2259533 = 847325) B847325
theorem B424583 : Blo 187803 424583 := bstep (se 1 (by rfl) ⟨318437, by rfl⟩ : syracuseStep 424583 = 636875) B636875
theorem B424763 : Blo 187803 424763 := bstep (se 1 (by rfl) ⟨318572, by rfl⟩ : syracuseStep 424763 = 637145) B637145
theorem B719675 : Blo 187803 719675 := bstep (se 1 (by rfl) ⟨539756, by rfl⟩ : syracuseStep 719675 = 1079513) B1079513
theorem B260983 : Blo 187803 260983 := bstep (se 1 (by rfl) ⟨195737, by rfl⟩ : syracuseStep 260983 = 391475) B391475
theorem B424889 : Blo 187803 424889 := bstep (se 2 (by rfl) ⟨159333, by rfl⟩ : syracuseStep 424889 = 318667) B318667
theorem B425231 : Blo 187803 425231 := bstep (se 1 (by rfl) ⟨318923, by rfl⟩ : syracuseStep 425231 = 637847) B637847
theorem B425249 : Blo 187803 425249 := bstep (se 2 (by rfl) ⟨159468, by rfl⟩ : syracuseStep 425249 = 318937) B318937
theorem B720161 : Blo 187803 720161 := bstep (se 2 (by rfl) ⟨270060, by rfl⟩ : syracuseStep 720161 = 540121) B540121
theorem B2456891 : Blo 187803 2456891 := bstep (se 1 (by rfl) ⟨1842668, by rfl⟩ : syracuseStep 2456891 = 3685337) B3685337
theorem B359815 : Blo 187803 359815 := bstep (se 1 (by rfl) ⟨269861, by rfl⟩ : syracuseStep 359815 = 539723) B539723
theorem B458131 : Blo 187803 458131 := bstep (se 1 (by rfl) ⟨343598, by rfl⟩ : syracuseStep 458131 = 687197) B687197
theorem B425591 : Blo 187803 425591 := bstep (se 1 (by rfl) ⟨319193, by rfl⟩ : syracuseStep 425591 = 638387) B638387
theorem B425771 : Blo 187803 425771 := bstep (se 1 (by rfl) ⟨319328, by rfl⟩ : syracuseStep 425771 = 638657) B638657
theorem B2064179 : Blo 187803 2064179 := bstep (se 1 (by rfl) ⟨1548134, by rfl⟩ : syracuseStep 2064179 = 3096269) B3096269
theorem B426041 : Blo 187803 426041 := bstep (se 2 (by rfl) ⟨159765, by rfl⟩ : syracuseStep 426041 = 319531) B319531
theorem B1572941 : Blo 187803 1572941 := bstep (se 3 (by rfl) ⟨294926, by rfl⟩ : syracuseStep 1572941 = 589853) B589853
theorem B721163 : Blo 187803 721163 := bstep (se 1 (by rfl) ⟨540872, by rfl⟩ : syracuseStep 721163 = 1081745) B1081745
theorem B426383 : Blo 187803 426383 := bstep (se 1 (by rfl) ⟨319787, by rfl⟩ : syracuseStep 426383 = 639575) B639575
theorem B21955157 : Blo 187803 21955157 := bstep (se 8 (by rfl) ⟨128643, by rfl⟩ : syracuseStep 21955157 = 257287) B257287
theorem B459361 : Blo 187803 459361 := bstep (se 2 (by rfl) ⟨172260, by rfl⟩ : syracuseStep 459361 = 344521) B344521
theorem B426707 : Blo 187803 426707 := bstep (se 1 (by rfl) ⟨320030, by rfl⟩ : syracuseStep 426707 = 640061) B640061
theorem B721619 : Blo 187803 721619 := bstep (se 1 (by rfl) ⟨541214, by rfl⟩ : syracuseStep 721619 = 1082429) B1082429
theorem B459475 : Blo 187803 459475 := bstep (se 1 (by rfl) ⟨344606, by rfl⟩ : syracuseStep 459475 = 689213) B689213
theorem B361721 : Blo 187803 361721 := bstep (se 2 (by rfl) ⟨135645, by rfl⟩ : syracuseStep 361721 = 271291) B271291
theorem B361903 : Blo 187803 361903 := bstep (se 1 (by rfl) ⟨271427, by rfl⟩ : syracuseStep 361903 = 542855) B542855
theorem B460313 : Blo 187803 460313 := bstep (se 2 (by rfl) ⟨172617, by rfl⟩ : syracuseStep 460313 = 345235) B345235
theorem B1213991 : Blo 187803 1213991 := bstep (se 1 (by rfl) ⟨910493, by rfl⟩ : syracuseStep 1213991 = 1820987) B1820987
theorem B362063 : Blo 187803 362063 := bstep (se 1 (by rfl) ⟨271547, by rfl⟩ : syracuseStep 362063 = 543095) B543095
theorem B427643 : Blo 187803 427643 := bstep (se 1 (by rfl) ⟨320732, by rfl⟩ : syracuseStep 427643 = 641465) B641465
theorem B722621 : Blo 187803 722621 := bstep (se 3 (by rfl) ⟨135491, by rfl⟩ : syracuseStep 722621 = 270983) B270983
theorem B427769 : Blo 187803 427769 := bstep (se 2 (by rfl) ⟨160413, by rfl⟩ : syracuseStep 427769 = 320827) B320827
theorem B1083203 : Blo 187803 1083203 := bstep (se 1 (by rfl) ⟨812402, by rfl⟩ : syracuseStep 1083203 = 1624805) B1624805
theorem B8259479 : Blo 187803 8259479 := bstep (se 1 (by rfl) ⟨6194609, by rfl⟩ : syracuseStep 8259479 = 12389219) B12389219
theorem B1607687 : Blo 187803 1607687 := bstep (se 1 (by rfl) ⟨1205765, by rfl⟩ : syracuseStep 1607687 = 2411531) B2411531
theorem B428039 : Blo 187803 428039 := bstep (se 1 (by rfl) ⟨321029, by rfl⟩ : syracuseStep 428039 = 642059) B642059
theorem B428111 : Blo 187803 428111 := bstep (se 1 (by rfl) ⟨321083, by rfl⟩ : syracuseStep 428111 = 642167) B642167
theorem B3049559 : Blo 187803 3049559 := bstep (se 1 (by rfl) ⟨2287169, by rfl⟩ : syracuseStep 3049559 = 4574339) B4574339
theorem B428507 : Blo 187803 428507 := bstep (se 1 (by rfl) ⟨321380, by rfl⟩ : syracuseStep 428507 = 642761) B642761
theorem B5474951 : Blo 187803 5474951 := bstep (se 1 (by rfl) ⟨4106213, by rfl⟩ : syracuseStep 5474951 = 8212427) B8212427
theorem B363179 : Blo 187803 363179 := bstep (se 1 (by rfl) ⟨272384, by rfl⟩ : syracuseStep 363179 = 544769) B544769
theorem B428975 : Blo 187803 428975 := bstep (se 1 (by rfl) ⟨321731, by rfl⟩ : syracuseStep 428975 = 643463) B643463
theorem B2067383 : Blo 187803 2067383 := bstep (se 1 (by rfl) ⟨1550537, by rfl⟩ : syracuseStep 2067383 = 3101075) B3101075
theorem B724049 : Blo 187803 724049 := bstep (se 2 (by rfl) ⟨271518, by rfl⟩ : syracuseStep 724049 = 543037) B543037
theorem B1215607 : Blo 187803 1215607 := bstep (se 1 (by rfl) ⟨911705, by rfl⟩ : syracuseStep 1215607 = 1823411) B1823411
theorem B429227 : Blo 187803 429227 := bstep (se 1 (by rfl) ⟨321920, by rfl⟩ : syracuseStep 429227 = 643841) B643841
theorem B691517 : Blo 187803 691517 := bstep (se 3 (by rfl) ⟨129659, by rfl⟩ : syracuseStep 691517 = 259319) B259319
theorem B1609085 : Blo 187803 1609085 := bstep (se 3 (by rfl) ⟨301703, by rfl⟩ : syracuseStep 1609085 = 603407) B603407
theorem B1445363 : Blo 187803 1445363 := bstep (se 1 (by rfl) ⟨1084022, by rfl⟩ : syracuseStep 1445363 = 2168045) B2168045
theorem B5312087 : Blo 187803 5312087 := bstep (se 1 (by rfl) ⟨3984065, by rfl⟩ : syracuseStep 5312087 = 7968131) B7968131
theorem B429767 : Blo 187803 429767 := bstep (se 1 (by rfl) ⟨322325, by rfl⟩ : syracuseStep 429767 = 644651) B644651
theorem B954179 : Blo 187803 954179 := bstep (se 1 (by rfl) ⟨715634, by rfl⟩ : syracuseStep 954179 = 1431269) B1431269
theorem B1085345 : Blo 187803 1085345 := bstep (se 2 (by rfl) ⟨407004, by rfl⟩ : syracuseStep 1085345 = 814009) B814009
theorem B331321873 : Blo 187803 331321873 := bstep (se 2 (by rfl) ⟨124245702, by rfl⟩ : syracuseStep 331321873 = 248491405) B248491405
theorem B725537 : Blo 187803 725537 := bstep (se 2 (by rfl) ⟨272076, by rfl⟩ : syracuseStep 725537 = 544153) B544153
theorem B430631 : Blo 187803 430631 := bstep (se 1 (by rfl) ⟨322973, by rfl⟩ : syracuseStep 430631 = 645947) B645947
theorem B725719 : Blo 187803 725719 := bstep (se 1 (by rfl) ⟨544289, by rfl⟩ : syracuseStep 725719 = 1088579) B1088579
theorem B430955 : Blo 187803 430955 := bstep (se 1 (by rfl) ⟨323216, by rfl⟩ : syracuseStep 430955 = 646433) B646433
theorem B431009 : Blo 187803 431009 := bstep (se 2 (by rfl) ⟨161628, by rfl⟩ : syracuseStep 431009 = 323257) B323257
theorem B726023 : Blo 187803 726023 := bstep (se 1 (by rfl) ⟨544517, by rfl⟩ : syracuseStep 726023 = 1089035) B1089035
theorem B365779 : Blo 187803 365779 := bstep (se 1 (by rfl) ⟨274334, by rfl⟩ : syracuseStep 365779 = 548669) B548669
theorem B431351 : Blo 187803 431351 := bstep (se 1 (by rfl) ⟨323513, by rfl⟩ : syracuseStep 431351 = 647027) B647027
theorem B4855139 : Blo 187803 4855139 := bstep (se 1 (by rfl) ⟨3641354, by rfl⟩ : syracuseStep 4855139 = 7282709) B7282709
theorem B726509 : Blo 187803 726509 := bstep (se 3 (by rfl) ⟨136220, by rfl⟩ : syracuseStep 726509 = 272441) B272441
theorem B1087121 : Blo 187803 1087121 := bstep (se 2 (by rfl) ⟨407670, by rfl⟩ : syracuseStep 1087121 = 815341) B815341
theorem B1087577 : Blo 187803 1087577 := bstep (se 2 (by rfl) ⟨407841, by rfl⟩ : syracuseStep 1087577 = 815683) B815683
theorem B1448279 : Blo 187803 1448279 := bstep (se 1 (by rfl) ⟨1086209, by rfl⟩ : syracuseStep 1448279 = 2172419) B2172419
theorem B301499 : Blo 187803 301499 := bstep (se 1 (by rfl) ⟨226124, by rfl⟩ : syracuseStep 301499 = 452249) B452249
theorem B694793 : Blo 187803 694793 := bstep (se 2 (by rfl) ⟨260547, by rfl⟩ : syracuseStep 694793 = 521095) B521095
theorem B727649 : Blo 187803 727649 := bstep (se 2 (by rfl) ⟨272868, by rfl⟩ : syracuseStep 727649 = 545737) B545737
theorem B957257 : Blo 187803 957257 := bstep (se 2 (by rfl) ⟨358971, by rfl⟩ : syracuseStep 957257 = 717943) B717943
theorem B302011 : Blo 187803 302011 := bstep (se 1 (by rfl) ⟨226508, by rfl⟩ : syracuseStep 302011 = 453017) B453017
theorem B269833 : Blo 187803 269833 := bstep (se 2 (by rfl) ⟨101187, by rfl⟩ : syracuseStep 269833 = 202375) B202375
theorem B1842821 : Blo 187803 1842821 := bstep (se 4 (by rfl) ⟨172764, by rfl⟩ : syracuseStep 1842821 = 345529) B345529
theorem B761483 : Blo 187803 761483 := bstep (se 1 (by rfl) ⟨571112, by rfl⟩ : syracuseStep 761483 = 1142225) B1142225
theorem B303031 : Blo 187803 303031 := bstep (se 1 (by rfl) ⟨227273, by rfl⟩ : syracuseStep 303031 = 454547) B454547
theorem B2170961 : Blo 187803 2170961 := bstep (se 2 (by rfl) ⟨814110, by rfl⟩ : syracuseStep 2170961 = 1628221) B1628221
theorem B958553 : Blo 187803 958553 := bstep (se 2 (by rfl) ⟨359457, by rfl⟩ : syracuseStep 958553 = 718915) B718915
theorem B271279 : Blo 187803 271279 := bstep (se 1 (by rfl) ⟨203459, by rfl⟩ : syracuseStep 271279 = 406919) B406919
theorem B13935563 : Blo 187803 13935563 := bstep (se 1 (by rfl) ⟨10451672, by rfl⟩ : syracuseStep 13935563 = 20903345) B20903345
theorem B238555 : Blo 187803 238555 := bstep (se 1 (by rfl) ⟨178916, by rfl⟩ : syracuseStep 238555 = 357833) B357833
theorem B402511 : Blo 187803 402511 := bstep (se 1 (by rfl) ⟨301883, by rfl⟩ : syracuseStep 402511 = 603767) B603767
theorem B22029893 : Blo 187803 22029893 := bstep (se 4 (by rfl) ⟨2065302, by rfl⟩ : syracuseStep 22029893 = 4130605) B4130605
theorem B370273 : Blo 187803 370273 := bstep (se 2 (by rfl) ⟨138852, by rfl⟩ : syracuseStep 370273 = 277705) B277705
theorem B2762387 : Blo 187803 2762387 := bstep (se 1 (by rfl) ⟨2071790, by rfl⟩ : syracuseStep 2762387 = 4143581) B4143581
theorem B1354643 : Blo 187803 1354643 := bstep (se 1 (by rfl) ⟨1015982, by rfl⟩ : syracuseStep 1354643 = 2031965) B2031965
theorem B1551251 : Blo 187803 1551251 := bstep (se 1 (by rfl) ⟨1163438, by rfl⟩ : syracuseStep 1551251 = 2326877) B2326877
theorem B634013 : Blo 187803 634013 := bstep (se 3 (by rfl) ⟨118877, by rfl⟩ : syracuseStep 634013 = 237755) B237755
theorem B765245 : Blo 187803 765245 := bstep (se 3 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 765245 = 286967) B286967
theorem B634553 : Blo 187803 634553 := bstep (se 2 (by rfl) ⟨237957, by rfl⟩ : syracuseStep 634553 = 475915) B475915
theorem B700093 : Blo 187803 700093 := bstep (se 3 (by rfl) ⟨131267, by rfl⟩ : syracuseStep 700093 = 262535) B262535
theorem B1028027 : Blo 187803 1028027 := bstep (se 1 (by rfl) ⟨771020, by rfl⟩ : syracuseStep 1028027 = 1542041) B1542041
theorem B635147 : Blo 187803 635147 := bstep (se 1 (by rfl) ⟨476360, by rfl⟩ : syracuseStep 635147 = 952721) B952721
theorem B602473 : Blo 187803 602473 := bstep (se 2 (by rfl) ⟨225927, by rfl⟩ : syracuseStep 602473 = 451855) B451855
theorem B602587 : Blo 187803 602587 := bstep (se 1 (by rfl) ⟨451940, by rfl⟩ : syracuseStep 602587 = 903881) B903881
theorem B635417 : Blo 187803 635417 := bstep (se 2 (by rfl) ⟨238281, by rfl⟩ : syracuseStep 635417 = 476563) B476563
theorem B406433 : Blo 187803 406433 := bstep (se 2 (by rfl) ⟨152412, by rfl⟩ : syracuseStep 406433 = 304825) B304825
theorem B242615 : Blo 187803 242615 := bstep (se 1 (by rfl) ⟨181961, by rfl⟩ : syracuseStep 242615 = 363923) B363923
theorem B963737 : Blo 187803 963737 := bstep (se 2 (by rfl) ⟨361401, by rfl⟩ : syracuseStep 963737 = 722803) B722803
theorem B406775 : Blo 187803 406775 := bstep (se 1 (by rfl) ⟨305081, by rfl⟩ : syracuseStep 406775 = 610163) B610163
theorem B767357 : Blo 187803 767357 := bstep (se 3 (by rfl) ⟨143879, by rfl⟩ : syracuseStep 767357 = 287759) B287759
theorem B767497 : Blo 187803 767497 := bstep (se 2 (by rfl) ⟨287811, by rfl⟩ : syracuseStep 767497 = 575623) B575623
theorem B1324583 : Blo 187803 1324583 := bstep (se 1 (by rfl) ⟨993437, by rfl⟩ : syracuseStep 1324583 = 1986875) B1986875
theorem B636551 : Blo 187803 636551 := bstep (se 1 (by rfl) ⟨477413, by rfl⟩ : syracuseStep 636551 = 954827) B954827
theorem B964243 : Blo 187803 964243 := bstep (se 1 (by rfl) ⟨723182, by rfl⟩ : syracuseStep 964243 = 1446365) B1446365
theorem B636605 : Blo 187803 636605 := bstep (se 3 (by rfl) ⟨119363, by rfl⟩ : syracuseStep 636605 = 238727) B238727
theorem B341833 : Blo 187803 341833 := bstep (se 2 (by rfl) ⟨128187, by rfl⟩ : syracuseStep 341833 = 256375) B256375
theorem B636767 : Blo 187803 636767 := bstep (se 1 (by rfl) ⟨477575, by rfl⟩ : syracuseStep 636767 = 955151) B955151
theorem B636929 : Blo 187803 636929 := bstep (se 2 (by rfl) ⟨238848, by rfl⟩ : syracuseStep 636929 = 477697) B477697
theorem B243751 : Blo 187803 243751 := bstep (se 1 (by rfl) ⟨182813, by rfl⟩ : syracuseStep 243751 = 365627) B365627
theorem B604331 : Blo 187803 604331 := bstep (se 1 (by rfl) ⟨453248, by rfl⟩ : syracuseStep 604331 = 906497) B906497
theorem B342215 : Blo 187803 342215 := bstep (se 1 (by rfl) ⟨256661, by rfl⟩ : syracuseStep 342215 = 513323) B513323
theorem B1227113 : Blo 187803 1227113 := bstep (se 2 (by rfl) ⟨460167, by rfl⟩ : syracuseStep 1227113 = 920335) B920335
theorem B408073 : Blo 187803 408073 := bstep (se 2 (by rfl) ⟨153027, by rfl⟩ : syracuseStep 408073 = 306055) B306055
theorem B211495 : Blo 187803 211495 := bstep (se 1 (by rfl) ⟨158621, by rfl⟩ : syracuseStep 211495 = 317243) B317243
theorem B637739 : Blo 187803 637739 := bstep (se 1 (by rfl) ⟨478304, by rfl⟩ : syracuseStep 637739 = 956609) B956609
theorem B408415 : Blo 187803 408415 := bstep (se 1 (by rfl) ⟨306311, by rfl⟩ : syracuseStep 408415 = 612623) B612623
theorem B638009 : Blo 187803 638009 := bstep (se 2 (by rfl) ⟨239253, by rfl⟩ : syracuseStep 638009 = 478507) B478507
theorem B638333 : Blo 187803 638333 := bstep (se 3 (by rfl) ⟨119687, by rfl⟩ : syracuseStep 638333 = 239375) B239375
theorem B572953 : Blo 187803 572953 := bstep (se 2 (by rfl) ⟨214857, by rfl⟩ : syracuseStep 572953 = 429715) B429715
theorem B638603 : Blo 187803 638603 := bstep (se 1 (by rfl) ⟨478952, by rfl⟩ : syracuseStep 638603 = 957905) B957905
theorem B802493 : Blo 187803 802493 := bstep (se 3 (by rfl) ⟨150467, by rfl⟩ : syracuseStep 802493 = 300935) B300935
theorem B540371 : Blo 187803 540371 := bstep (se 1 (by rfl) ⟨405278, by rfl⟩ : syracuseStep 540371 = 810557) B810557
theorem B1228729 : Blo 187803 1228729 := bstep (se 2 (by rfl) ⟨460773, by rfl⟩ : syracuseStep 1228729 = 921547) B921547
theorem B409619 : Blo 187803 409619 := bstep (se 1 (by rfl) ⟨307214, by rfl⟩ : syracuseStep 409619 = 614429) B614429
theorem B1359949 : Blo 187803 1359949 := bstep (se 3 (by rfl) ⟨254990, by rfl⟩ : syracuseStep 1359949 = 509981) B509981
theorem B213115 : Blo 187803 213115 := bstep (se 1 (by rfl) ⟨159836, by rfl⟩ : syracuseStep 213115 = 319673) B319673
theorem B11583755 : Blo 187803 11583755 := bstep (se 1 (by rfl) ⟨8687816, by rfl⟩ : syracuseStep 11583755 = 17375633) B17375633
theorem B639521 : Blo 187803 639521 := bstep (se 2 (by rfl) ⟨239820, by rfl⟩ : syracuseStep 639521 = 479641) B479641
theorem B213583 : Blo 187803 213583 := bstep (se 1 (by rfl) ⟨160187, by rfl⟩ : syracuseStep 213583 = 320375) B320375
theorem B5653111 : Blo 187803 5653111 := bstep (se 1 (by rfl) ⟨4239833, by rfl⟩ : syracuseStep 5653111 = 8479667) B8479667
theorem B344825 : Blo 187803 344825 := bstep (se 2 (by rfl) ⟨129309, by rfl⟩ : syracuseStep 344825 = 258619) B258619
theorem B639737 : Blo 187803 639737 := bstep (se 2 (by rfl) ⟨239901, by rfl⟩ : syracuseStep 639737 = 479803) B479803
theorem B213979 : Blo 187803 213979 := bstep (se 1 (by rfl) ⟨160484, by rfl⟩ : syracuseStep 213979 = 320969) B320969
theorem B640007 : Blo 187803 640007 := bstep (se 1 (by rfl) ⟨480005, by rfl⟩ : syracuseStep 640007 = 960011) B960011
theorem B3064877 : Blo 187803 3064877 := bstep (se 3 (by rfl) ⟨574664, by rfl⟩ : syracuseStep 3064877 = 1149329) B1149329
theorem B476239 : Blo 187803 476239 := bstep (se 1 (by rfl) ⟨357179, by rfl⟩ : syracuseStep 476239 = 714359) B714359
theorem B640115 : Blo 187803 640115 := bstep (se 1 (by rfl) ⟨480086, by rfl⟩ : syracuseStep 640115 = 960173) B960173
theorem B541853 : Blo 187803 541853 := bstep (se 3 (by rfl) ⟨101597, by rfl⟩ : syracuseStep 541853 = 203195) B203195
theorem B640385 : Blo 187803 640385 := bstep (se 2 (by rfl) ⟨240144, by rfl⟩ : syracuseStep 640385 = 480289) B480289
theorem B345487 : Blo 187803 345487 := bstep (se 1 (by rfl) ⟨259115, by rfl⟩ : syracuseStep 345487 = 518231) B518231
theorem B214447 : Blo 187803 214447 := bstep (se 1 (by rfl) ⟨160835, by rfl⟩ : syracuseStep 214447 = 321671) B321671
theorem B1197665 : Blo 187803 1197665 := bstep (se 2 (by rfl) ⟨449124, by rfl⟩ : syracuseStep 1197665 = 898249) B898249
theorem B6211217 : Blo 187803 6211217 := bstep (se 2 (by rfl) ⟨2329206, by rfl⟩ : syracuseStep 6211217 = 4658413) B4658413
theorem B476887 : Blo 187803 476887 := bstep (se 1 (by rfl) ⟨357665, by rfl⟩ : syracuseStep 476887 = 715331) B715331
theorem B575225 : Blo 187803 575225 := bstep (se 2 (by rfl) ⟨215709, by rfl⟩ : syracuseStep 575225 = 431419) B431419
theorem B214879 : Blo 187803 214879 := bstep (se 1 (by rfl) ⟨161159, by rfl⟩ : syracuseStep 214879 = 322319) B322319
theorem B542639 : Blo 187803 542639 := bstep (se 1 (by rfl) ⟨406979, by rfl⟩ : syracuseStep 542639 = 813959) B813959
theorem B477191 : Blo 187803 477191 := bstep (se 1 (by rfl) ⟨357893, by rfl⟩ : syracuseStep 477191 = 715787) B715787
theorem B1624121 : Blo 187803 1624121 := bstep (se 2 (by rfl) ⟨609045, by rfl⟩ : syracuseStep 1624121 = 1218091) B1218091
theorem B641195 : Blo 187803 641195 := bstep (se 1 (by rfl) ⟨480896, by rfl⟩ : syracuseStep 641195 = 961793) B961793
theorem B215239 : Blo 187803 215239 := bstep (se 1 (by rfl) ⟨161429, by rfl⟩ : syracuseStep 215239 = 322859) B322859
theorem B641735 : Blo 187803 641735 := bstep (se 1 (by rfl) ⟨481301, by rfl⟩ : syracuseStep 641735 = 962603) B962603
theorem B412679 : Blo 187803 412679 := bstep (se 1 (by rfl) ⟨309509, by rfl⟩ : syracuseStep 412679 = 619019) B619019
theorem B281723 : Blo 187803 281723 := bstep (se 1 (by rfl) ⟨211292, by rfl⟩ : syracuseStep 281723 = 422585) B422585
theorem B281849 : Blo 187803 281849 := bstep (se 2 (by rfl) ⟨105693, by rfl⟩ : syracuseStep 281849 = 211387) B211387
theorem B281951 : Blo 187803 281951 := bstep (se 1 (by rfl) ⟨211463, by rfl⟩ : syracuseStep 281951 = 422927) B422927
theorem B281963 : Blo 187803 281963 := bstep (se 1 (by rfl) ⟨211472, by rfl⟩ : syracuseStep 281963 = 422945) B422945
theorem B511451 : Blo 187803 511451 := bstep (se 1 (by rfl) ⟨383588, by rfl⟩ : syracuseStep 511451 = 767177) B767177
theorem B642599 : Blo 187803 642599 := bstep (se 1 (by rfl) ⟨481949, by rfl⟩ : syracuseStep 642599 = 963899) B963899
theorem B282191 : Blo 187803 282191 := bstep (se 1 (by rfl) ⟨211643, by rfl⟩ : syracuseStep 282191 = 423287) B423287
theorem B970379 : Blo 187803 970379 := bstep (se 1 (by rfl) ⟨727784, by rfl⟩ : syracuseStep 970379 = 1455569) B1455569
theorem B642707 : Blo 187803 642707 := bstep (se 1 (by rfl) ⟨482030, by rfl⟩ : syracuseStep 642707 = 964061) B964061
theorem B282311 : Blo 187803 282311 := bstep (se 1 (by rfl) ⟨211733, by rfl⟩ : syracuseStep 282311 = 423467) B423467
theorem B347977 : Blo 187803 347977 := bstep (se 2 (by rfl) ⟨130491, by rfl⟩ : syracuseStep 347977 = 260983) B260983
theorem B282473 : Blo 187803 282473 := bstep (se 2 (by rfl) ⟨105927, by rfl⟩ : syracuseStep 282473 = 211855) B211855
theorem B642923 : Blo 187803 642923 := bstep (se 1 (by rfl) ⟨482192, by rfl⟩ : syracuseStep 642923 = 964385) B964385
theorem B642977 : Blo 187803 642977 := bstep (se 2 (by rfl) ⟨241116, by rfl⟩ : syracuseStep 642977 = 482233) B482233
theorem B282551 : Blo 187803 282551 := bstep (se 1 (by rfl) ⟨211913, by rfl⟩ : syracuseStep 282551 = 423827) B423827
theorem B282587 : Blo 187803 282587 := bstep (se 1 (by rfl) ⟨211940, by rfl⟩ : syracuseStep 282587 = 423881) B423881
theorem B1233053 : Blo 187803 1233053 := bstep (se 3 (by rfl) ⟨231197, by rfl⟩ : syracuseStep 1233053 = 462395) B462395
theorem B479479 : Blo 187803 479479 := bstep (se 1 (by rfl) ⟨359609, by rfl⟩ : syracuseStep 479479 = 719219) B719219
theorem B1429811 : Blo 187803 1429811 := bstep (se 1 (by rfl) ⟨1072358, by rfl⟩ : syracuseStep 1429811 = 2144717) B2144717
theorem B283055 : Blo 187803 283055 := bstep (se 1 (by rfl) ⟨212291, by rfl⟩ : syracuseStep 283055 = 424583) B424583
theorem B643571 : Blo 187803 643571 := bstep (se 1 (by rfl) ⟨482678, by rfl⟩ : syracuseStep 643571 = 965357) B965357
theorem B381449 : Blo 187803 381449 := bstep (se 2 (by rfl) ⟨143043, by rfl⟩ : syracuseStep 381449 = 286087) B286087
theorem B283145 : Blo 187803 283145 := bstep (se 2 (by rfl) ⟨106179, by rfl⟩ : syracuseStep 283145 = 212359) B212359
theorem B479753 : Blo 187803 479753 := bstep (se 2 (by rfl) ⟨179907, by rfl⟩ : syracuseStep 479753 = 359815) B359815
theorem B610841 : Blo 187803 610841 := bstep (se 2 (by rfl) ⟨229065, by rfl⟩ : syracuseStep 610841 = 458131) B458131
theorem B283175 : Blo 187803 283175 := bstep (se 1 (by rfl) ⟨212381, by rfl⟩ : syracuseStep 283175 = 424763) B424763
theorem B479783 : Blo 187803 479783 := bstep (se 1 (by rfl) ⟨359837, by rfl⟩ : syracuseStep 479783 = 719675) B719675
theorem B283259 : Blo 187803 283259 := bstep (se 1 (by rfl) ⟨212444, by rfl⟩ : syracuseStep 283259 = 424889) B424889
theorem B905863 : Blo 187803 905863 := bstep (se 1 (by rfl) ⟨679397, by rfl⟩ : syracuseStep 905863 = 1358795) B1358795
theorem B971473 : Blo 187803 971473 := bstep (se 2 (by rfl) ⟨364302, by rfl⟩ : syracuseStep 971473 = 728605) B728605
theorem B283385 : Blo 187803 283385 := bstep (se 2 (by rfl) ⟨106269, by rfl⟩ : syracuseStep 283385 = 212539) B212539
theorem B283487 : Blo 187803 283487 := bstep (se 1 (by rfl) ⟨212615, by rfl⟩ : syracuseStep 283487 = 425231) B425231
theorem B283499 : Blo 187803 283499 := bstep (se 1 (by rfl) ⟨212624, by rfl⟩ : syracuseStep 283499 = 425249) B425249
theorem B480107 : Blo 187803 480107 := bstep (se 1 (by rfl) ⟨360080, by rfl⟩ : syracuseStep 480107 = 720161) B720161
theorem B578411 : Blo 187803 578411 := bstep (se 1 (by rfl) ⟨433808, by rfl⟩ : syracuseStep 578411 = 867617) B867617
theorem B447419 : Blo 187803 447419 := bstep (se 1 (by rfl) ⟨335564, by rfl⟩ : syracuseStep 447419 = 671129) B671129
theorem B1070081 : Blo 187803 1070081 := bstep (se 2 (by rfl) ⟨401280, by rfl⟩ : syracuseStep 1070081 = 802561) B802561
theorem B3724289 : Blo 187803 3724289 := bstep (se 2 (by rfl) ⟨1396608, by rfl⟩ : syracuseStep 3724289 = 2793217) B2793217
theorem B644111 : Blo 187803 644111 := bstep (se 1 (by rfl) ⟨483083, by rfl⟩ : syracuseStep 644111 = 966167) B966167
theorem B283727 : Blo 187803 283727 := bstep (se 1 (by rfl) ⟨212795, by rfl⟩ : syracuseStep 283727 = 425591) B425591
theorem B283847 : Blo 187803 283847 := bstep (se 1 (by rfl) ⟨212885, by rfl⟩ : syracuseStep 283847 = 425771) B425771
theorem B382201 : Blo 187803 382201 := bstep (se 2 (by rfl) ⟨143325, by rfl⟩ : syracuseStep 382201 = 286651) B286651
theorem B284009 : Blo 187803 284009 := bstep (se 2 (by rfl) ⟨106503, by rfl⟩ : syracuseStep 284009 = 213007) B213007
theorem B284087 : Blo 187803 284087 := bstep (se 1 (by rfl) ⟨213065, by rfl⟩ : syracuseStep 284087 = 426131) B426131
theorem B873929 : Blo 187803 873929 := bstep (se 2 (by rfl) ⟨327723, by rfl⟩ : syracuseStep 873929 = 655447) B655447
theorem B284123 : Blo 187803 284123 := bstep (se 1 (by rfl) ⟨213092, by rfl⟩ : syracuseStep 284123 = 426185) B426185
theorem B480755 : Blo 187803 480755 := bstep (se 1 (by rfl) ⟨360566, by rfl⟩ : syracuseStep 480755 = 721133) B721133
theorem B2610731 : Blo 187803 2610731 := bstep (se 1 (by rfl) ⟨1958048, by rfl⟩ : syracuseStep 2610731 = 3916097) B3916097
theorem B644705 : Blo 187803 644705 := bstep (se 2 (by rfl) ⟨241764, by rfl⟩ : syracuseStep 644705 = 483529) B483529
theorem B284591 : Blo 187803 284591 := bstep (se 1 (by rfl) ⟨213443, by rfl⟩ : syracuseStep 284591 = 426887) B426887
theorem B317371 : Blo 187803 317371 := bstep (se 1 (by rfl) ⟨238028, by rfl⟩ : syracuseStep 317371 = 476057) B476057
theorem B481211 : Blo 187803 481211 := bstep (se 1 (by rfl) ⟨360908, by rfl⟩ : syracuseStep 481211 = 721817) B721817
theorem B612353 : Blo 187803 612353 := bstep (se 2 (by rfl) ⟨229632, by rfl⟩ : syracuseStep 612353 = 459265) B459265
theorem B284681 : Blo 187803 284681 := bstep (se 2 (by rfl) ⟨106755, by rfl⟩ : syracuseStep 284681 = 213511) B213511
theorem B317479 : Blo 187803 317479 := bstep (se 1 (by rfl) ⟨238109, by rfl⟩ : syracuseStep 317479 = 476219) B476219
theorem B284711 : Blo 187803 284711 := bstep (se 1 (by rfl) ⟨213533, by rfl⟩ : syracuseStep 284711 = 427067) B427067
theorem B284795 : Blo 187803 284795 := bstep (se 1 (by rfl) ⟨213596, by rfl⟩ : syracuseStep 284795 = 427193) B427193
theorem B284921 : Blo 187803 284921 := bstep (se 2 (by rfl) ⟨106845, by rfl⟩ : syracuseStep 284921 = 213691) B213691
theorem B285023 : Blo 187803 285023 := bstep (se 1 (by rfl) ⟨213767, by rfl⟩ : syracuseStep 285023 = 427535) B427535
theorem B317803 : Blo 187803 317803 := bstep (se 1 (by rfl) ⟨238352, by rfl⟩ : syracuseStep 317803 = 476705) B476705
theorem B285035 : Blo 187803 285035 := bstep (se 1 (by rfl) ⟨213776, by rfl⟩ : syracuseStep 285035 = 427553) B427553
theorem B612737 : Blo 187803 612737 := bstep (se 2 (by rfl) ⟨229776, by rfl⟩ : syracuseStep 612737 = 459553) B459553
theorem B1628549 : Blo 187803 1628549 := bstep (se 4 (by rfl) ⟨152676, by rfl⟩ : syracuseStep 1628549 = 305353) B305353
theorem B285263 : Blo 187803 285263 := bstep (se 1 (by rfl) ⟨213947, by rfl⟩ : syracuseStep 285263 = 427895) B427895
theorem B481889 : Blo 187803 481889 := bstep (se 2 (by rfl) ⟨180708, by rfl⟩ : syracuseStep 481889 = 361417) B361417
theorem B285383 : Blo 187803 285383 := bstep (se 1 (by rfl) ⟨214037, by rfl⟩ : syracuseStep 285383 = 428075) B428075
theorem B2611997 : Blo 187803 2611997 := bstep (se 3 (by rfl) ⟨489749, by rfl⟩ : syracuseStep 2611997 = 979499) B979499
theorem B3496733 : Blo 187803 3496733 := bstep (se 3 (by rfl) ⟨655637, by rfl⟩ : syracuseStep 3496733 = 1311275) B1311275
theorem B285545 : Blo 187803 285545 := bstep (se 2 (by rfl) ⟨107079, by rfl⟩ : syracuseStep 285545 = 214159) B214159
theorem B285623 : Blo 187803 285623 := bstep (se 1 (by rfl) ⟨214217, by rfl⟩ : syracuseStep 285623 = 428435) B428435
theorem B285659 : Blo 187803 285659 := bstep (se 1 (by rfl) ⟨214244, by rfl⟩ : syracuseStep 285659 = 428489) B428489
theorem B646163 : Blo 187803 646163 := bstep (se 1 (by rfl) ⟨484622, by rfl⟩ : syracuseStep 646163 = 969245) B969245
theorem B1629377 : Blo 187803 1629377 := bstep (se 2 (by rfl) ⟨611016, by rfl⟩ : syracuseStep 1629377 = 1222033) B1222033
theorem B646487 : Blo 187803 646487 := bstep (se 1 (by rfl) ⟨484865, by rfl⟩ : syracuseStep 646487 = 969731) B969731
theorem B318863 : Blo 187803 318863 := bstep (se 1 (by rfl) ⟨239147, by rfl⟩ : syracuseStep 318863 = 478295) B478295
theorem B187823 : Blo 187803 187823 := bstep (se 1 (by rfl) ⟨140867, by rfl⟩ : syracuseStep 187823 = 281735) B281735
theorem B286127 : Blo 187803 286127 := bstep (se 1 (by rfl) ⟨214595, by rfl⟩ : syracuseStep 286127 = 429191) B429191
theorem B187847 : Blo 187803 187847 := bstep (se 1 (by rfl) ⟨140885, by rfl⟩ : syracuseStep 187847 = 281771) B281771
theorem B187867 : Blo 187803 187867 := bstep (se 1 (by rfl) ⟨140900, by rfl⟩ : syracuseStep 187867 = 281801) B281801
theorem B286217 : Blo 187803 286217 := bstep (se 2 (by rfl) ⟨107331, by rfl⟩ : syracuseStep 286217 = 214663) B214663
theorem B187943 : Blo 187803 187943 := bstep (se 1 (by rfl) ⟨140957, by rfl⟩ : syracuseStep 187943 = 281915) B281915
theorem B286247 : Blo 187803 286247 := bstep (se 1 (by rfl) ⟨214685, by rfl⟩ : syracuseStep 286247 = 429371) B429371
theorem B384569 : Blo 187803 384569 := bstep (se 2 (by rfl) ⟨144213, by rfl⟩ : syracuseStep 384569 = 288427) B288427
theorem B187983 : Blo 187803 187983 := bstep (se 1 (by rfl) ⟨140987, by rfl⟩ : syracuseStep 187983 = 281975) B281975
theorem B187999 : Blo 187803 187999 := bstep (se 1 (by rfl) ⟨140999, by rfl⟩ : syracuseStep 187999 = 281999) B281999
theorem B810593 : Blo 187803 810593 := bstep (se 2 (by rfl) ⟨303972, by rfl⟩ : syracuseStep 810593 = 607945) B607945
theorem B188027 : Blo 187803 188027 := bstep (se 1 (by rfl) ⟨141020, by rfl⟩ : syracuseStep 188027 = 282041) B282041
theorem B319099 : Blo 187803 319099 := bstep (se 1 (by rfl) ⟨239324, by rfl⟩ : syracuseStep 319099 = 478649) B478649
theorem B286331 : Blo 187803 286331 := bstep (se 1 (by rfl) ⟨214748, by rfl⟩ : syracuseStep 286331 = 429497) B429497
theorem B188079 : Blo 187803 188079 := bstep (se 1 (by rfl) ⟨141059, by rfl⟩ : syracuseStep 188079 = 282119) B282119
theorem B188103 : Blo 187803 188103 := bstep (se 1 (by rfl) ⟨141077, by rfl⟩ : syracuseStep 188103 = 282155) B282155
theorem B188123 : Blo 187803 188123 := bstep (se 1 (by rfl) ⟨141092, by rfl⟩ : syracuseStep 188123 = 282185) B282185
theorem B614137 : Blo 187803 614137 := bstep (se 2 (by rfl) ⟨230301, by rfl⟩ : syracuseStep 614137 = 460603) B460603
theorem B286457 : Blo 187803 286457 := bstep (se 2 (by rfl) ⟨107421, by rfl⟩ : syracuseStep 286457 = 214843) B214843
theorem B188199 : Blo 187803 188199 := bstep (se 1 (by rfl) ⟨141149, by rfl⟩ : syracuseStep 188199 = 282299) B282299
theorem B188239 : Blo 187803 188239 := bstep (se 1 (by rfl) ⟨141179, by rfl⟩ : syracuseStep 188239 = 282359) B282359
theorem B188255 : Blo 187803 188255 := bstep (se 1 (by rfl) ⟨141191, by rfl⟩ : syracuseStep 188255 = 282383) B282383
theorem B286559 : Blo 187803 286559 := bstep (se 1 (by rfl) ⟨214919, by rfl⟩ : syracuseStep 286559 = 429839) B429839
theorem B286571 : Blo 187803 286571 := bstep (se 1 (by rfl) ⟨214928, by rfl⟩ : syracuseStep 286571 = 429857) B429857
theorem B2416499 : Blo 187803 2416499 := bstep (se 1 (by rfl) ⟨1812374, by rfl⟩ : syracuseStep 2416499 = 3624749) B3624749
theorem B614263 : Blo 187803 614263 := bstep (se 1 (by rfl) ⟨460697, by rfl⟩ : syracuseStep 614263 = 921395) B921395
theorem B188283 : Blo 187803 188283 := bstep (se 1 (by rfl) ⟨141212, by rfl⟩ : syracuseStep 188283 = 282425) B282425
theorem B188335 : Blo 187803 188335 := bstep (se 1 (by rfl) ⟨141251, by rfl⟩ : syracuseStep 188335 = 282503) B282503
theorem B188359 : Blo 187803 188359 := bstep (se 1 (by rfl) ⟨141269, by rfl⟩ : syracuseStep 188359 = 282539) B282539
theorem B188379 : Blo 187803 188379 := bstep (se 1 (by rfl) ⟨141284, by rfl⟩ : syracuseStep 188379 = 282569) B282569
theorem B483347 : Blo 187803 483347 := bstep (se 1 (by rfl) ⟨362510, by rfl⟩ : syracuseStep 483347 = 725021) B725021
theorem B1204253 : Blo 187803 1204253 := bstep (se 3 (by rfl) ⟨225797, by rfl⟩ : syracuseStep 1204253 = 451595) B451595
theorem B188455 : Blo 187803 188455 := bstep (se 1 (by rfl) ⟨141341, by rfl⟩ : syracuseStep 188455 = 282683) B282683
theorem B188495 : Blo 187803 188495 := bstep (se 1 (by rfl) ⟨141371, by rfl⟩ : syracuseStep 188495 = 282743) B282743
theorem B286799 : Blo 187803 286799 := bstep (se 1 (by rfl) ⟨215099, by rfl⟩ : syracuseStep 286799 = 430199) B430199
theorem B188511 : Blo 187803 188511 := bstep (se 1 (by rfl) ⟨141383, by rfl⟩ : syracuseStep 188511 = 282767) B282767
theorem B188539 : Blo 187803 188539 := bstep (se 1 (by rfl) ⟨141404, by rfl⟩ : syracuseStep 188539 = 282809) B282809
theorem B680089 : Blo 187803 680089 := bstep (se 2 (by rfl) ⟨255033, by rfl⟩ : syracuseStep 680089 = 510067) B510067
theorem B188591 : Blo 187803 188591 := bstep (se 1 (by rfl) ⟨141443, by rfl⟩ : syracuseStep 188591 = 282887) B282887
theorem B188615 : Blo 187803 188615 := bstep (se 1 (by rfl) ⟨141461, by rfl⟩ : syracuseStep 188615 = 282923) B282923
theorem B286919 : Blo 187803 286919 := bstep (se 1 (by rfl) ⟨215189, by rfl⟩ : syracuseStep 286919 = 430379) B430379
theorem B188635 : Blo 187803 188635 := bstep (se 1 (by rfl) ⟨141476, by rfl⟩ : syracuseStep 188635 = 282953) B282953
theorem B188711 : Blo 187803 188711 := bstep (se 1 (by rfl) ⟨141533, by rfl⟩ : syracuseStep 188711 = 283067) B283067
theorem B188751 : Blo 187803 188751 := bstep (se 1 (by rfl) ⟨141563, by rfl⟩ : syracuseStep 188751 = 283127) B283127
theorem B188767 : Blo 187803 188767 := bstep (se 1 (by rfl) ⟨141575, by rfl⟩ : syracuseStep 188767 = 283151) B283151
theorem B287081 : Blo 187803 287081 := bstep (se 2 (by rfl) ⟨107655, by rfl⟩ : syracuseStep 287081 = 215311) B215311
theorem B188795 : Blo 187803 188795 := bstep (se 1 (by rfl) ⟨141596, by rfl⟩ : syracuseStep 188795 = 283193) B283193
theorem B188847 : Blo 187803 188847 := bstep (se 1 (by rfl) ⟨141635, by rfl⟩ : syracuseStep 188847 = 283271) B283271
theorem B287159 : Blo 187803 287159 := bstep (se 1 (by rfl) ⟨215369, by rfl⟩ : syracuseStep 287159 = 430739) B430739
theorem B188871 : Blo 187803 188871 := bstep (se 1 (by rfl) ⟨141653, by rfl⟩ : syracuseStep 188871 = 283307) B283307
theorem B188891 : Blo 187803 188891 := bstep (se 1 (by rfl) ⟨141668, by rfl⟩ : syracuseStep 188891 = 283337) B283337
theorem B319963 : Blo 187803 319963 := bstep (se 1 (by rfl) ⟨239972, by rfl⟩ : syracuseStep 319963 = 479945) B479945
theorem B483803 : Blo 187803 483803 := bstep (se 1 (by rfl) ⟨362852, by rfl⟩ : syracuseStep 483803 = 725705) B725705
theorem B287195 : Blo 187803 287195 := bstep (se 1 (by rfl) ⟨215396, by rfl⟩ : syracuseStep 287195 = 430793) B430793
theorem B188967 : Blo 187803 188967 := bstep (se 1 (by rfl) ⟨141725, by rfl⟩ : syracuseStep 188967 = 283451) B283451
theorem B3465787 : Blo 187803 3465787 := bstep (se 1 (by rfl) ⟨2599340, by rfl⟩ : syracuseStep 3465787 = 5198681) B5198681
theorem B189007 : Blo 187803 189007 := bstep (se 1 (by rfl) ⟨141755, by rfl⟩ : syracuseStep 189007 = 283511) B283511
theorem B189023 : Blo 187803 189023 := bstep (se 1 (by rfl) ⟨141767, by rfl⟩ : syracuseStep 189023 = 283535) B283535
theorem B189051 : Blo 187803 189051 := bstep (se 1 (by rfl) ⟨141788, by rfl⟩ : syracuseStep 189051 = 283577) B283577
theorem B189103 : Blo 187803 189103 := bstep (se 1 (by rfl) ⟨141827, by rfl⟩ : syracuseStep 189103 = 283655) B283655
theorem B189127 : Blo 187803 189127 := bstep (se 1 (by rfl) ⟨141845, by rfl⟩ : syracuseStep 189127 = 283691) B283691
theorem B189147 : Blo 187803 189147 := bstep (se 1 (by rfl) ⟨141860, by rfl⟩ : syracuseStep 189147 = 283721) B283721
theorem B189223 : Blo 187803 189223 := bstep (se 1 (by rfl) ⟨141917, by rfl⟩ : syracuseStep 189223 = 283835) B283835
theorem B189263 : Blo 187803 189263 := bstep (se 1 (by rfl) ⟨141947, by rfl⟩ : syracuseStep 189263 = 283895) B283895
theorem B189279 : Blo 187803 189279 := bstep (se 1 (by rfl) ⟨141959, by rfl⟩ : syracuseStep 189279 = 283919) B283919
theorem B910187 : Blo 187803 910187 := bstep (se 1 (by rfl) ⟨682640, by rfl⟩ : syracuseStep 910187 = 1365281) B1365281
theorem B189307 : Blo 187803 189307 := bstep (se 1 (by rfl) ⟨141980, by rfl⟩ : syracuseStep 189307 = 283961) B283961
theorem B189359 : Blo 187803 189359 := bstep (se 1 (by rfl) ⟨142019, by rfl⟩ : syracuseStep 189359 = 284039) B284039
theorem B287663 : Blo 187803 287663 := bstep (se 1 (by rfl) ⟨215747, by rfl⟩ : syracuseStep 287663 = 431495) B431495
theorem B189383 : Blo 187803 189383 := bstep (se 1 (by rfl) ⟨142037, by rfl⟩ : syracuseStep 189383 = 284075) B284075
theorem B189403 : Blo 187803 189403 := bstep (se 1 (by rfl) ⟨142052, by rfl⟩ : syracuseStep 189403 = 284105) B284105
theorem B189479 : Blo 187803 189479 := bstep (se 1 (by rfl) ⟨142109, by rfl⟩ : syracuseStep 189479 = 284219) B284219
theorem B189519 : Blo 187803 189519 := bstep (se 1 (by rfl) ⟨142139, by rfl⟩ : syracuseStep 189519 = 284279) B284279
theorem B320591 : Blo 187803 320591 := bstep (se 1 (by rfl) ⟨240443, by rfl⟩ : syracuseStep 320591 = 480887) B480887
theorem B189535 : Blo 187803 189535 := bstep (se 1 (by rfl) ⟨142151, by rfl⟩ : syracuseStep 189535 = 284303) B284303
theorem B713843 : Blo 187803 713843 := bstep (se 1 (by rfl) ⟨535382, by rfl⟩ : syracuseStep 713843 = 1070765) B1070765
theorem B189563 : Blo 187803 189563 := bstep (se 1 (by rfl) ⟨142172, by rfl⟩ : syracuseStep 189563 = 284345) B284345
theorem B189615 : Blo 187803 189615 := bstep (se 1 (by rfl) ⟨142211, by rfl⟩ : syracuseStep 189615 = 284423) B284423
theorem B189639 : Blo 187803 189639 := bstep (se 1 (by rfl) ⟨142229, by rfl⟩ : syracuseStep 189639 = 284459) B284459
theorem B189659 : Blo 187803 189659 := bstep (se 1 (by rfl) ⟨142244, by rfl⟩ : syracuseStep 189659 = 284489) B284489
theorem B517367 : Blo 187803 517367 := bstep (se 1 (by rfl) ⟨388025, by rfl⟩ : syracuseStep 517367 = 776051) B776051
theorem B1074455 : Blo 187803 1074455 := bstep (se 1 (by rfl) ⟨805841, by rfl⟩ : syracuseStep 1074455 = 1611683) B1611683
theorem B189735 : Blo 187803 189735 := bstep (se 1 (by rfl) ⟨142301, by rfl⟩ : syracuseStep 189735 = 284603) B284603
theorem B189775 : Blo 187803 189775 := bstep (se 1 (by rfl) ⟨142331, by rfl⟩ : syracuseStep 189775 = 284663) B284663
theorem B189791 : Blo 187803 189791 := bstep (se 1 (by rfl) ⟨142343, by rfl⟩ : syracuseStep 189791 = 284687) B284687
theorem B189819 : Blo 187803 189819 := bstep (se 1 (by rfl) ⟨142364, by rfl⟩ : syracuseStep 189819 = 284729) B284729
theorem B3302819 : Blo 187803 3302819 := bstep (se 1 (by rfl) ⟨2477114, by rfl⟩ : syracuseStep 3302819 = 4954229) B4954229
theorem B189871 : Blo 187803 189871 := bstep (se 1 (by rfl) ⟨142403, by rfl⟩ : syracuseStep 189871 = 284807) B284807
theorem B189895 : Blo 187803 189895 := bstep (se 1 (by rfl) ⟨142421, by rfl⟩ : syracuseStep 189895 = 284843) B284843
theorem B189915 : Blo 187803 189915 := bstep (se 1 (by rfl) ⟨142436, by rfl⟩ : syracuseStep 189915 = 284873) B284873
theorem B189991 : Blo 187803 189991 := bstep (se 1 (by rfl) ⟨142493, by rfl⟩ : syracuseStep 189991 = 284987) B284987
theorem B190031 : Blo 187803 190031 := bstep (se 1 (by rfl) ⟨142523, by rfl⟩ : syracuseStep 190031 = 285047) B285047
theorem B190047 : Blo 187803 190047 := bstep (se 1 (by rfl) ⟨142535, by rfl⟩ : syracuseStep 190047 = 285071) B285071
theorem B190075 : Blo 187803 190075 := bstep (se 1 (by rfl) ⟨142556, by rfl⟩ : syracuseStep 190075 = 285113) B285113
theorem B484987 : Blo 187803 484987 := bstep (se 1 (by rfl) ⟨363740, by rfl⟩ : syracuseStep 484987 = 727481) B727481
theorem B190127 : Blo 187803 190127 := bstep (se 1 (by rfl) ⟨142595, by rfl⟩ : syracuseStep 190127 = 285191) B285191
theorem B190151 : Blo 187803 190151 := bstep (se 1 (by rfl) ⟨142613, by rfl⟩ : syracuseStep 190151 = 285227) B285227
theorem B190171 : Blo 187803 190171 := bstep (se 1 (by rfl) ⟨142628, by rfl⟩ : syracuseStep 190171 = 285257) B285257
theorem B190247 : Blo 187803 190247 := bstep (se 1 (by rfl) ⟨142685, by rfl⟩ : syracuseStep 190247 = 285371) B285371
theorem B190287 : Blo 187803 190287 := bstep (se 1 (by rfl) ⟨142715, by rfl⟩ : syracuseStep 190287 = 285431) B285431
theorem B190303 : Blo 187803 190303 := bstep (se 1 (by rfl) ⟨142727, by rfl⟩ : syracuseStep 190303 = 285455) B285455
theorem B1730413 : Blo 187803 1730413 := bstep (se 3 (by rfl) ⟨324452, by rfl⟩ : syracuseStep 1730413 = 648905) B648905
theorem B190331 : Blo 187803 190331 := bstep (se 1 (by rfl) ⟨142748, by rfl⟩ : syracuseStep 190331 = 285497) B285497
theorem B190383 : Blo 187803 190383 := bstep (se 1 (by rfl) ⟨142787, by rfl⟩ : syracuseStep 190383 = 285575) B285575
theorem B321455 : Blo 187803 321455 := bstep (se 1 (by rfl) ⟨241091, by rfl⟩ : syracuseStep 321455 = 482183) B482183
theorem B190407 : Blo 187803 190407 := bstep (se 1 (by rfl) ⟨142805, by rfl⟩ : syracuseStep 190407 = 285611) B285611
theorem B190427 : Blo 187803 190427 := bstep (se 1 (by rfl) ⟨142820, by rfl⟩ : syracuseStep 190427 = 285641) B285641
theorem B190503 : Blo 187803 190503 := bstep (se 1 (by rfl) ⟨142877, by rfl⟩ : syracuseStep 190503 = 285755) B285755
theorem B190543 : Blo 187803 190543 := bstep (se 1 (by rfl) ⟨142907, by rfl⟩ : syracuseStep 190543 = 285815) B285815
theorem B190559 : Blo 187803 190559 := bstep (se 1 (by rfl) ⟨142919, by rfl⟩ : syracuseStep 190559 = 285839) B285839
theorem B190587 : Blo 187803 190587 := bstep (se 1 (by rfl) ⟨142940, by rfl⟩ : syracuseStep 190587 = 285881) B285881
theorem B11954309 : Blo 187803 11954309 := bstep (se 4 (by rfl) ⟨1120716, by rfl⟩ : syracuseStep 11954309 = 2241433) B2241433
theorem B190639 : Blo 187803 190639 := bstep (se 1 (by rfl) ⟨142979, by rfl⟩ : syracuseStep 190639 = 285959) B285959
theorem B190663 : Blo 187803 190663 := bstep (se 1 (by rfl) ⟨142997, by rfl⟩ : syracuseStep 190663 = 285995) B285995
theorem B190683 : Blo 187803 190683 := bstep (se 1 (by rfl) ⟨143012, by rfl⟩ : syracuseStep 190683 = 286025) B286025
theorem B190759 : Blo 187803 190759 := bstep (se 1 (by rfl) ⟨143069, by rfl⟩ : syracuseStep 190759 = 286139) B286139
theorem B190799 : Blo 187803 190799 := bstep (se 1 (by rfl) ⟨143099, by rfl⟩ : syracuseStep 190799 = 286199) B286199
theorem B321887 : Blo 187803 321887 := bstep (se 1 (by rfl) ⟨241415, by rfl⟩ : syracuseStep 321887 = 482831) B482831
theorem B190815 : Blo 187803 190815 := bstep (se 1 (by rfl) ⟨143111, by rfl⟩ : syracuseStep 190815 = 286223) B286223
theorem B190843 : Blo 187803 190843 := bstep (se 1 (by rfl) ⟨143132, by rfl⟩ : syracuseStep 190843 = 286265) B286265
theorem B3631513 : Blo 187803 3631513 := bstep (se 2 (by rfl) ⟨1361817, by rfl⟩ : syracuseStep 3631513 = 2723635) B2723635
theorem B190895 : Blo 187803 190895 := bstep (se 1 (by rfl) ⟨143171, by rfl⟩ : syracuseStep 190895 = 286343) B286343
theorem B190919 : Blo 187803 190919 := bstep (se 1 (by rfl) ⟨143189, by rfl⟩ : syracuseStep 190919 = 286379) B286379
theorem B190939 : Blo 187803 190939 := bstep (se 1 (by rfl) ⟨143204, by rfl⟩ : syracuseStep 190939 = 286409) B286409
theorem B191015 : Blo 187803 191015 := bstep (se 1 (by rfl) ⟨143261, by rfl⟩ : syracuseStep 191015 = 286523) B286523
theorem B191055 : Blo 187803 191055 := bstep (se 1 (by rfl) ⟨143291, by rfl⟩ : syracuseStep 191055 = 286583) B286583
theorem B191071 : Blo 187803 191071 := bstep (se 1 (by rfl) ⟨143303, by rfl⟩ : syracuseStep 191071 = 286607) B286607
theorem B191099 : Blo 187803 191099 := bstep (se 1 (by rfl) ⟨143324, by rfl⟩ : syracuseStep 191099 = 286649) B286649
theorem B191151 : Blo 187803 191151 := bstep (se 1 (by rfl) ⟨143363, by rfl⟩ : syracuseStep 191151 = 286727) B286727
theorem B191175 : Blo 187803 191175 := bstep (se 1 (by rfl) ⟨143381, by rfl⟩ : syracuseStep 191175 = 286763) B286763
theorem B191195 : Blo 187803 191195 := bstep (se 1 (by rfl) ⟨143396, by rfl⟩ : syracuseStep 191195 = 286793) B286793
theorem B355063 : Blo 187803 355063 := bstep (se 1 (by rfl) ⟨266297, by rfl⟩ : syracuseStep 355063 = 532595) B532595
theorem B715513 : Blo 187803 715513 := bstep (se 2 (by rfl) ⟨268317, by rfl⟩ : syracuseStep 715513 = 536635) B536635
theorem B486137 : Blo 187803 486137 := bstep (se 2 (by rfl) ⟨182301, by rfl⟩ : syracuseStep 486137 = 364603) B364603
theorem B191271 : Blo 187803 191271 := bstep (se 1 (by rfl) ⟨143453, by rfl⟩ : syracuseStep 191271 = 286907) B286907
theorem B191311 : Blo 187803 191311 := bstep (se 1 (by rfl) ⟨143483, by rfl⟩ : syracuseStep 191311 = 286967) B286967
theorem B191327 : Blo 187803 191327 := bstep (se 1 (by rfl) ⟨143495, by rfl⟩ : syracuseStep 191327 = 286991) B286991
theorem B191355 : Blo 187803 191355 := bstep (se 1 (by rfl) ⟨143516, by rfl⟩ : syracuseStep 191355 = 287033) B287033
theorem B322447 : Blo 187803 322447 := bstep (se 1 (by rfl) ⟨241835, by rfl⟩ : syracuseStep 322447 = 483671) B483671
theorem B191407 : Blo 187803 191407 := bstep (se 1 (by rfl) ⟨143555, by rfl⟩ : syracuseStep 191407 = 287111) B287111
theorem B191431 : Blo 187803 191431 := bstep (se 1 (by rfl) ⟨143573, by rfl⟩ : syracuseStep 191431 = 287147) B287147
theorem B191451 : Blo 187803 191451 := bstep (se 1 (by rfl) ⟨143588, by rfl⟩ : syracuseStep 191451 = 287177) B287177
theorem B191527 : Blo 187803 191527 := bstep (se 1 (by rfl) ⟨143645, by rfl⟩ : syracuseStep 191527 = 287291) B287291
theorem B191567 : Blo 187803 191567 := bstep (se 1 (by rfl) ⟨143675, by rfl⟩ : syracuseStep 191567 = 287351) B287351
theorem B191583 : Blo 187803 191583 := bstep (se 1 (by rfl) ⟨143687, by rfl⟩ : syracuseStep 191583 = 287375) B287375
theorem B191611 : Blo 187803 191611 := bstep (se 1 (by rfl) ⟨143708, by rfl⟩ : syracuseStep 191611 = 287417) B287417
theorem B191663 : Blo 187803 191663 := bstep (se 1 (by rfl) ⟨143747, by rfl⟩ : syracuseStep 191663 = 287495) B287495
theorem B191687 : Blo 187803 191687 := bstep (se 1 (by rfl) ⟨143765, by rfl⟩ : syracuseStep 191687 = 287531) B287531
theorem B191707 : Blo 187803 191707 := bstep (se 1 (by rfl) ⟨143780, by rfl⟩ : syracuseStep 191707 = 287561) B287561
theorem B191783 : Blo 187803 191783 := bstep (se 1 (by rfl) ⟨143837, by rfl⟩ : syracuseStep 191783 = 287675) B287675
theorem B1437101 : Blo 187803 1437101 := bstep (se 3 (by rfl) ⟨269456, by rfl⟩ : syracuseStep 1437101 = 538913) B538913
theorem B2420189 : Blo 187803 2420189 := bstep (se 3 (by rfl) ⟨453785, by rfl⟩ : syracuseStep 2420189 = 907571) B907571
theorem B3436019 : Blo 187803 3436019 := bstep (se 1 (by rfl) ⟨2577014, by rfl⟩ : syracuseStep 3436019 = 5154029) B5154029
theorem B323129 : Blo 187803 323129 := bstep (se 2 (by rfl) ⟨121173, by rfl⟩ : syracuseStep 323129 = 242347) B242347
theorem B1633931 : Blo 187803 1633931 := bstep (se 1 (by rfl) ⟨1225448, by rfl⟩ : syracuseStep 1633931 = 2450897) B2450897
theorem B290665 : Blo 187803 290665 := bstep (se 2 (by rfl) ⟨108999, by rfl⟩ : syracuseStep 290665 = 217999) B217999
theorem B323435 : Blo 187803 323435 := bstep (se 1 (by rfl) ⟨242576, by rfl⟩ : syracuseStep 323435 = 485153) B485153
theorem B814967 : Blo 187803 814967 := bstep (se 1 (by rfl) ⟨611225, by rfl⟩ : syracuseStep 814967 = 1222451) B1222451
theorem B683959 : Blo 187803 683959 := bstep (se 1 (by rfl) ⟨512969, by rfl⟩ : syracuseStep 683959 = 1025939) B1025939
theorem B4649075 : Blo 187803 4649075 := bstep (se 1 (by rfl) ⟨3486806, by rfl⟩ : syracuseStep 4649075 = 6973613) B6973613
theorem B716957 : Blo 187803 716957 := bstep (se 3 (by rfl) ⟨134429, by rfl⟩ : syracuseStep 716957 = 268859) B268859
theorem B716971 : Blo 187803 716971 := bstep (se 1 (by rfl) ⟨537728, by rfl⟩ : syracuseStep 716971 = 1075457) B1075457
theorem B6025421 : Blo 187803 6025421 := bstep (se 3 (by rfl) ⟨1129766, by rfl⟩ : syracuseStep 6025421 = 2259533) B2259533
theorem B2289995 : Blo 187803 2289995 := bstep (se 1 (by rfl) ⟨1717496, by rfl⟩ : syracuseStep 2289995 = 3434993) B3434993
theorem B717275 : Blo 187803 717275 := bstep (se 1 (by rfl) ⟨537956, by rfl⟩ : syracuseStep 717275 = 1075913) B1075913
theorem B422729 : Blo 187803 422729 := bstep (se 2 (by rfl) ⟨158523, by rfl⟩ : syracuseStep 422729 = 317047) B317047
theorem B1635329 : Blo 187803 1635329 := bstep (se 2 (by rfl) ⟨613248, by rfl⟩ : syracuseStep 1635329 = 1226497) B1226497
theorem B357385 : Blo 187803 357385 := bstep (se 2 (by rfl) ⟨134019, by rfl⟩ : syracuseStep 357385 = 268039) B268039
theorem B816527 : Blo 187803 816527 := bstep (se 1 (by rfl) ⟨612395, by rfl⟩ : syracuseStep 816527 = 1224791) B1224791
theorem B3339667 : Blo 187803 3339667 := bstep (se 1 (by rfl) ⟨2504750, by rfl⟩ : syracuseStep 3339667 = 5009501) B5009501
theorem B194087 : Blo 187803 194087 := bstep (se 1 (by rfl) ⟨145565, by rfl⟩ : syracuseStep 194087 = 291131) B291131
theorem B423521 : Blo 187803 423521 := bstep (se 2 (by rfl) ⟨158820, by rfl⟩ : syracuseStep 423521 = 317641) B317641
theorem B1439531 : Blo 187803 1439531 := bstep (se 1 (by rfl) ⟨1079648, by rfl⟩ : syracuseStep 1439531 = 2159297) B2159297
theorem B358319 : Blo 187803 358319 := bstep (se 1 (by rfl) ⟨268739, by rfl⟩ : syracuseStep 358319 = 537479) B537479
theorem B456623 : Blo 187803 456623 := bstep (se 1 (by rfl) ⟨342467, by rfl⟩ : syracuseStep 456623 = 684935) B684935
theorem B423863 : Blo 187803 423863 := bstep (se 1 (by rfl) ⟨317897, by rfl⟩ : syracuseStep 423863 = 635795) B635795
theorem B6944717 : Blo 187803 6944717 := bstep (se 3 (by rfl) ⟨1302134, by rfl⟩ : syracuseStep 6944717 = 2604269) B2604269
theorem B915799 : Blo 187803 915799 := bstep (se 1 (by rfl) ⟨686849, by rfl⟩ : syracuseStep 915799 = 1373699) B1373699
theorem B358843 : Blo 187803 358843 := bstep (se 1 (by rfl) ⟨269132, by rfl⟩ : syracuseStep 358843 = 538265) B538265
theorem B424457 : Blo 187803 424457 := bstep (se 2 (by rfl) ⟨159171, by rfl⟩ : syracuseStep 424457 = 318343) B318343
theorem B424799 : Blo 187803 424799 := bstep (se 1 (by rfl) ⟨318599, by rfl⟩ : syracuseStep 424799 = 637199) B637199
theorem B359329 : Blo 187803 359329 := bstep (se 2 (by rfl) ⟨134748, by rfl⟩ : syracuseStep 359329 = 269497) B269497
theorem B19037105 : Blo 187803 19037105 := bstep (se 2 (by rfl) ⟨7138914, by rfl⟩ : syracuseStep 19037105 = 14277829) B14277829
theorem B719873 : Blo 187803 719873 := bstep (se 2 (by rfl) ⟨269952, by rfl⟩ : syracuseStep 719873 = 539905) B539905
theorem B719887 : Blo 187803 719887 := bstep (se 1 (by rfl) ⟨539915, by rfl⟩ : syracuseStep 719887 = 1079831) B1079831
theorem B424979 : Blo 187803 424979 := bstep (se 1 (by rfl) ⟨318734, by rfl⟩ : syracuseStep 424979 = 637469) B637469
theorem B1015031 : Blo 187803 1015031 := bstep (se 1 (by rfl) ⟨761273, by rfl⟩ : syracuseStep 1015031 = 1522547) B1522547
theorem B425321 : Blo 187803 425321 := bstep (se 2 (by rfl) ⟨159495, by rfl⟩ : syracuseStep 425321 = 318991) B318991
theorem B1637927 : Blo 187803 1637927 := bstep (se 1 (by rfl) ⟨1228445, by rfl⟩ : syracuseStep 1637927 = 2456891) B2456891
theorem B1212043 : Blo 187803 1212043 := bstep (se 1 (by rfl) ⟨909032, by rfl⟩ : syracuseStep 1212043 = 1818065) B1818065
theorem B1080971 : Blo 187803 1080971 := bstep (se 1 (by rfl) ⟨810728, by rfl⟩ : syracuseStep 1080971 = 1621457) B1621457
theorem B1376119 : Blo 187803 1376119 := bstep (se 1 (by rfl) ⟨1032089, by rfl⟩ : syracuseStep 1376119 = 2064179) B2064179
theorem B425915 : Blo 187803 425915 := bstep (se 1 (by rfl) ⟨319436, by rfl⟩ : syracuseStep 425915 = 638873) B638873
theorem B1048627 : Blo 187803 1048627 := bstep (se 1 (by rfl) ⟨786470, by rfl⟩ : syracuseStep 1048627 = 1572941) B1572941
theorem B426347 : Blo 187803 426347 := bstep (se 1 (by rfl) ⟨319760, by rfl⟩ : syracuseStep 426347 = 639521) B639521
theorem B229883 : Blo 187803 229883 := bstep (se 1 (by rfl) ⟨172412, by rfl⟩ : syracuseStep 229883 = 344825) B344825
theorem B426491 : Blo 187803 426491 := bstep (se 1 (by rfl) ⟨319868, by rfl⟩ : syracuseStep 426491 = 639737) B639737
theorem B426617 : Blo 187803 426617 := bstep (se 2 (by rfl) ⟨159981, by rfl⟩ : syracuseStep 426617 = 319963) B319963
theorem B426671 : Blo 187803 426671 := bstep (se 1 (by rfl) ⟨320003, by rfl⟩ : syracuseStep 426671 = 640007) B640007
theorem B426743 : Blo 187803 426743 := bstep (se 1 (by rfl) ⟨320057, by rfl⟩ : syracuseStep 426743 = 640115) B640115
theorem B4621049 : Blo 187803 4621049 := bstep (se 2 (by rfl) ⟨1732893, by rfl⟩ : syracuseStep 4621049 = 3465787) B3465787
theorem B361235 : Blo 187803 361235 := bstep (se 1 (by rfl) ⟨270926, by rfl⟩ : syracuseStep 361235 = 541853) B541853
theorem B7537481 : Blo 187803 7537481 := bstep (se 2 (by rfl) ⟨2826555, by rfl⟩ : syracuseStep 7537481 = 5653111) B5653111
theorem B426923 : Blo 187803 426923 := bstep (se 1 (by rfl) ⟨320192, by rfl⟩ : syracuseStep 426923 = 640385) B640385
theorem B722135 : Blo 187803 722135 := bstep (se 1 (by rfl) ⟨541601, by rfl⟩ : syracuseStep 722135 = 1083203) B1083203
theorem B5506319 : Blo 187803 5506319 := bstep (se 1 (by rfl) ⟨4129739, by rfl⟩ : syracuseStep 5506319 = 8259479) B8259479
theorem B361759 : Blo 187803 361759 := bstep (se 1 (by rfl) ⟨271319, by rfl⟩ : syracuseStep 361759 = 542639) B542639
theorem B1017197 : Blo 187803 1017197 := bstep (se 3 (by rfl) ⟨190724, by rfl⟩ : syracuseStep 1017197 = 381449) B381449
theorem B1082747 : Blo 187803 1082747 := bstep (se 1 (by rfl) ⟨812060, by rfl⟩ : syracuseStep 1082747 = 1624121) B1624121
theorem B2033039 : Blo 187803 2033039 := bstep (se 1 (by rfl) ⟨1524779, by rfl⟩ : syracuseStep 2033039 = 3049559) B3049559
theorem B427463 : Blo 187803 427463 := bstep (se 1 (by rfl) ⟨320597, by rfl⟩ : syracuseStep 427463 = 641195) B641195
theorem B427823 : Blo 187803 427823 := bstep (se 1 (by rfl) ⟨320867, by rfl⟩ : syracuseStep 427823 = 641735) B641735
theorem B460649 : Blo 187803 460649 := bstep (se 2 (by rfl) ⟨172743, by rfl⟩ : syracuseStep 460649 = 345487) B345487
theorem B1378255 : Blo 187803 1378255 := bstep (se 1 (by rfl) ⟨1033691, by rfl⟩ : syracuseStep 1378255 = 2067383) B2067383
theorem B493697 : Blo 187803 493697 := bstep (se 2 (by rfl) ⟨185136, by rfl⟩ : syracuseStep 493697 = 370273) B370273
theorem B428399 : Blo 187803 428399 := bstep (se 1 (by rfl) ⟨321299, by rfl⟩ : syracuseStep 428399 = 642599) B642599
theorem B3541391 : Blo 187803 3541391 := bstep (se 1 (by rfl) ⟨2656043, by rfl⟩ : syracuseStep 3541391 = 5312087) B5312087
theorem B428471 : Blo 187803 428471 := bstep (se 1 (by rfl) ⟨321353, by rfl⟩ : syracuseStep 428471 = 642707) B642707
theorem B428615 : Blo 187803 428615 := bstep (se 1 (by rfl) ⟨321461, by rfl⟩ : syracuseStep 428615 = 642923) B642923
theorem B428651 : Blo 187803 428651 := bstep (se 1 (by rfl) ⟨321488, by rfl⟩ : syracuseStep 428651 = 642977) B642977
theorem B723563 : Blo 187803 723563 := bstep (se 1 (by rfl) ⟨542672, by rfl⟩ : syracuseStep 723563 = 1085345) B1085345
theorem B822035 : Blo 187803 822035 := bstep (se 1 (by rfl) ⟨616526, by rfl⟩ : syracuseStep 822035 = 1233053) B1233053
theorem B953207 : Blo 187803 953207 := bstep (se 1 (by rfl) ⟨714905, by rfl⟩ : syracuseStep 953207 = 1429811) B1429811
theorem B429047 : Blo 187803 429047 := bstep (se 1 (by rfl) ⟨321785, by rfl⟩ : syracuseStep 429047 = 643571) B643571
theorem B298279 : Blo 187803 298279 := bstep (se 1 (by rfl) ⟨223709, by rfl⟩ : syracuseStep 298279 = 447419) B447419
theorem B429407 : Blo 187803 429407 := bstep (se 1 (by rfl) ⟨322055, by rfl⟩ : syracuseStep 429407 = 644111) B644111
theorem B954017 : Blo 187803 954017 := bstep (se 2 (by rfl) ⟨357756, by rfl⟩ : syracuseStep 954017 = 715513) B715513
theorem B1740487 : Blo 187803 1740487 := bstep (se 1 (by rfl) ⟨1305365, by rfl⟩ : syracuseStep 1740487 = 2610731) B2610731
theorem B429803 : Blo 187803 429803 := bstep (se 1 (by rfl) ⟨322352, by rfl⟩ : syracuseStep 429803 = 644705) B644705
theorem B724747 : Blo 187803 724747 := bstep (se 1 (by rfl) ⟨543560, by rfl⟩ : syracuseStep 724747 = 1087121) B1087121
theorem B429929 : Blo 187803 429929 := bstep (se 2 (by rfl) ⟨161223, by rfl⟩ : syracuseStep 429929 = 322447) B322447
theorem B2330477 : Blo 187803 2330477 := bstep (se 3 (by rfl) ⟨436964, by rfl⟩ : syracuseStep 2330477 = 873929) B873929
theorem B725051 : Blo 187803 725051 := bstep (se 1 (by rfl) ⟨543788, by rfl⟩ : syracuseStep 725051 = 1087577) B1087577
theorem B1085699 : Blo 187803 1085699 := bstep (se 1 (by rfl) ⟨814274, by rfl⟩ : syracuseStep 1085699 = 1628549) B1628549
theorem B200999 : Blo 187803 200999 := bstep (se 1 (by rfl) ⟨150749, by rfl⟩ : syracuseStep 200999 = 301499) B301499
theorem B463195 : Blo 187803 463195 := bstep (se 1 (by rfl) ⟨347396, by rfl⟩ : syracuseStep 463195 = 694793) B694793
theorem B1741331 : Blo 187803 1741331 := bstep (se 1 (by rfl) ⟨1305998, by rfl⟩ : syracuseStep 1741331 = 2611997) B2611997
theorem B2331155 : Blo 187803 2331155 := bstep (se 1 (by rfl) ⟨1748366, by rfl⟩ : syracuseStep 2331155 = 3496733) B3496733
theorem B430775 : Blo 187803 430775 := bstep (se 1 (by rfl) ⟨323081, by rfl⟩ : syracuseStep 430775 = 646163) B646163
theorem B1086251 : Blo 187803 1086251 := bstep (se 1 (by rfl) ⟨814688, by rfl⟩ : syracuseStep 1086251 = 1629377) B1629377
theorem B430991 : Blo 187803 430991 := bstep (se 1 (by rfl) ⟨323243, by rfl⟩ : syracuseStep 430991 = 646487) B646487
theorem B1446821 : Blo 187803 1446821 := bstep (se 4 (by rfl) ⟨135639, by rfl⟩ : syracuseStep 1446821 = 271279) B271279
theorem B1610725 : Blo 187803 1610725 := bstep (se 4 (by rfl) ⟨151005, by rfl⟩ : syracuseStep 1610725 = 302011) B302011
theorem B463969 : Blo 187803 463969 := bstep (se 2 (by rfl) ⟨173988, by rfl⟩ : syracuseStep 463969 = 347977) B347977
theorem B1610999 : Blo 187803 1610999 := bstep (se 1 (by rfl) ⟨1208249, by rfl⟩ : syracuseStep 1610999 = 2416499) B2416499
theorem B1447307 : Blo 187803 1447307 := bstep (se 1 (by rfl) ⟨1085480, by rfl⟩ : syracuseStep 1447307 = 2170961) B2170961
theorem B955961 : Blo 187803 955961 := bstep (se 2 (by rfl) ⟨358485, by rfl⟩ : syracuseStep 955961 = 716971) B716971
theorem B2201879 : Blo 187803 2201879 := bstep (se 1 (by rfl) ⟨1651409, by rfl⟩ : syracuseStep 2201879 = 3302819) B3302819
theorem B14686595 : Blo 187803 14686595 := bstep (se 1 (by rfl) ⟨11014946, by rfl⟩ : syracuseStep 14686595 = 22029893) B22029893
theorem B1841591 : Blo 187803 1841591 := bstep (se 1 (by rfl) ⟨1381193, by rfl⟩ : syracuseStep 1841591 = 2762387) B2762387
theorem B2038405 : Blo 187803 2038405 := bstep (se 4 (by rfl) ⟨191100, by rfl⟩ : syracuseStep 2038405 = 382201) B382201
theorem B1023329 : Blo 187803 1023329 := bstep (se 2 (by rfl) ⟨383748, by rfl⟩ : syracuseStep 1023329 = 767497) B767497
theorem B958067 : Blo 187803 958067 := bstep (se 1 (by rfl) ⟨718550, by rfl⟩ : syracuseStep 958067 = 1437101) B1437101
theorem B1613459 : Blo 187803 1613459 := bstep (se 1 (by rfl) ⟨1210094, by rfl⟩ : syracuseStep 1613459 = 2420189) B2420189
theorem B1089287 : Blo 187803 1089287 := bstep (se 1 (by rfl) ⟨816965, by rfl⟩ : syracuseStep 1089287 = 1633931) B1633931
theorem B1221065 : Blo 187803 1221065 := bstep (se 2 (by rfl) ⟨457899, by rfl⟩ : syracuseStep 1221065 = 915799) B915799
theorem B270955 : Blo 187803 270955 := bstep (se 1 (by rfl) ⟨203216, by rfl⟩ : syracuseStep 270955 = 406433) B406433
theorem B1090219 : Blo 187803 1090219 := bstep (se 1 (by rfl) ⟨817664, by rfl⟩ : syracuseStep 1090219 = 1635329) B1635329
theorem B2040653 : Blo 187803 2040653 := bstep (se 3 (by rfl) ⟨382622, by rfl⟩ : syracuseStep 2040653 = 765245) B765245
theorem B1844045 : Blo 187803 1844045 := bstep (se 3 (by rfl) ⟨345758, by rfl⟩ : syracuseStep 1844045 = 691517) B691517
theorem B271183 : Blo 187803 271183 := bstep (se 1 (by rfl) ⟨203387, by rfl⟩ : syracuseStep 271183 = 406775) B406775
theorem B959687 : Blo 187803 959687 := bstep (se 1 (by rfl) ⟨719765, by rfl⟩ : syracuseStep 959687 = 1439531) B1439531
theorem B238879 : Blo 187803 238879 := bstep (se 1 (by rfl) ⟨179159, by rfl⟩ : syracuseStep 238879 = 358319) B358319
theorem B304415 : Blo 187803 304415 := bstep (se 1 (by rfl) ⟨228311, by rfl⟩ : syracuseStep 304415 = 456623) B456623
theorem B4629811 : Blo 187803 4629811 := bstep (se 1 (by rfl) ⟨3472358, by rfl⟩ : syracuseStep 4629811 = 6944717) B6944717
theorem B959849 : Blo 187803 959849 := bstep (se 2 (by rfl) ⟨359943, by rfl⟩ : syracuseStep 959849 = 719887) B719887
theorem B402887 : Blo 187803 402887 := bstep (se 1 (by rfl) ⟨302165, by rfl⟩ : syracuseStep 402887 = 604331) B604331
theorem B12691403 : Blo 187803 12691403 := bstep (se 1 (by rfl) ⟨9518552, by rfl⟩ : syracuseStep 12691403 = 19037105) B19037105
theorem B763937 : Blo 187803 763937 := bstep (se 2 (by rfl) ⟨286476, by rfl⟩ : syracuseStep 763937 = 572953) B572953
theorem B1616057 : Blo 187803 1616057 := bstep (se 2 (by rfl) ⟨606021, by rfl⟩ : syracuseStep 1616057 = 1212043) B1212043
theorem B1091951 : Blo 187803 1091951 := bstep (se 1 (by rfl) ⟨818963, by rfl⟩ : syracuseStep 1091951 = 1637927) B1637927
theorem B534995 : Blo 187803 534995 := bstep (se 1 (by rfl) ⟨401246, by rfl⟩ : syracuseStep 534995 = 802493) B802493
theorem B404041 : Blo 187803 404041 := bstep (se 2 (by rfl) ⟨151515, by rfl⟩ : syracuseStep 404041 = 303031) B303031
theorem B273079 : Blo 187803 273079 := bstep (se 1 (by rfl) ⟨204809, by rfl⟩ : syracuseStep 273079 = 409619) B409619
theorem B1813265 : Blo 187803 1813265 := bstep (se 2 (by rfl) ⟨679974, by rfl⟩ : syracuseStep 1813265 = 1359949) B1359949
theorem B2043251 : Blo 187803 2043251 := bstep (se 1 (by rfl) ⟨1532438, by rfl⟩ : syracuseStep 2043251 = 3064877) B3064877
theorem B241147 : Blo 187803 241147 := bstep (se 1 (by rfl) ⟨180860, by rfl⟩ : syracuseStep 241147 = 361721) B361721
theorem B306875 : Blo 187803 306875 := bstep (se 1 (by rfl) ⟨230156, by rfl⟩ : syracuseStep 306875 = 460313) B460313
theorem B241375 : Blo 187803 241375 := bstep (se 1 (by rfl) ⟨181031, by rfl⟩ : syracuseStep 241375 = 362063) B362063
theorem B798443 : Blo 187803 798443 := bstep (se 1 (by rfl) ⟨598832, by rfl⟩ : syracuseStep 798443 = 1197665) B1197665
theorem B4140811 : Blo 187803 4140811 := bstep (se 1 (by rfl) ⟨3105608, by rfl⟩ : syracuseStep 4140811 = 6211217) B6211217
theorem B634985 : Blo 187803 634985 := bstep (se 2 (by rfl) ⟨238119, by rfl⟩ : syracuseStep 634985 = 476239) B476239
theorem B536681 : Blo 187803 536681 := bstep (se 2 (by rfl) ⟨201255, by rfl⟩ : syracuseStep 536681 = 402511) B402511
theorem B3649967 : Blo 187803 3649967 := bstep (se 1 (by rfl) ⟨2737475, by rfl⟩ : syracuseStep 3649967 = 5474951) B5474951
theorem B242119 : Blo 187803 242119 := bstep (se 1 (by rfl) ⟨181589, by rfl⟩ : syracuseStep 242119 = 363179) B363179
theorem B635849 : Blo 187803 635849 := bstep (se 2 (by rfl) ⟨238443, by rfl⟩ : syracuseStep 635849 = 476887) B476887
theorem B340967 : Blo 187803 340967 := bstep (se 1 (by rfl) ⟨255725, by rfl⟩ : syracuseStep 340967 = 511451) B511451
theorem B963575 : Blo 187803 963575 := bstep (se 1 (by rfl) ⟨722681, by rfl⟩ : syracuseStep 963575 = 1445363) B1445363
theorem B2307217 : Blo 187803 2307217 := bstep (se 2 (by rfl) ⟨865206, by rfl⟩ : syracuseStep 2307217 = 1730413) B1730413
theorem B636119 : Blo 187803 636119 := bstep (se 1 (by rfl) ⟨477089, by rfl⟩ : syracuseStep 636119 = 954179) B954179
theorem B407227 : Blo 187803 407227 := bstep (se 1 (by rfl) ⟨305420, by rfl⟩ : syracuseStep 407227 = 610841) B610841
theorem B473417 : Blo 187803 473417 := bstep (se 2 (by rfl) ⟨177531, by rfl⟩ : syracuseStep 473417 = 355063) B355063
theorem B2177405 : Blo 187803 2177405 := bstep (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) B816527
theorem B408235 : Blo 187803 408235 := bstep (se 1 (by rfl) ⟨306176, by rfl⟩ : syracuseStep 408235 = 612353) B612353
theorem B1620809 : Blo 187803 1620809 := bstep (se 2 (by rfl) ⟨607803, by rfl⟩ : syracuseStep 1620809 = 1215607) B1215607
theorem B965519 : Blo 187803 965519 := bstep (se 1 (by rfl) ⟨724139, by rfl⟩ : syracuseStep 965519 = 1448279) B1448279
theorem B408491 : Blo 187803 408491 := bstep (se 1 (by rfl) ⟨306368, by rfl⟩ : syracuseStep 408491 = 612737) B612737
theorem B638171 : Blo 187803 638171 := bstep (se 1 (by rfl) ⟨478628, by rfl⟩ : syracuseStep 638171 = 957257) B957257
theorem B933457 : Blo 187803 933457 := bstep (se 2 (by rfl) ⟨350046, by rfl⟩ : syracuseStep 933457 = 700093) B700093
theorem B212575 : Blo 187803 212575 := bstep (se 1 (by rfl) ⟨159431, by rfl⟩ : syracuseStep 212575 = 318863) B318863
theorem B540395 : Blo 187803 540395 := bstep (se 1 (by rfl) ⟨405296, by rfl⟩ : syracuseStep 540395 = 810593) B810593
theorem B1228547 : Blo 187803 1228547 := bstep (se 1 (by rfl) ⟨921410, by rfl⟩ : syracuseStep 1228547 = 1842821) B1842821
theorem B507655 : Blo 187803 507655 := bstep (se 1 (by rfl) ⟨380741, by rfl⟩ : syracuseStep 507655 = 761483) B761483
theorem B802835 : Blo 187803 802835 := bstep (se 1 (by rfl) ⟨602126, by rfl⟩ : syracuseStep 802835 = 1204253) B1204253
theorem B639035 : Blo 187803 639035 := bstep (se 1 (by rfl) ⟨479276, by rfl⟩ : syracuseStep 639035 = 958553) B958553
theorem B639305 : Blo 187803 639305 := bstep (se 2 (by rfl) ⟨239739, by rfl⟩ : syracuseStep 639305 = 479479) B479479
theorem B803297 : Blo 187803 803297 := bstep (se 2 (by rfl) ⟨301236, by rfl⟩ : syracuseStep 803297 = 602473) B602473
theorem B606791 : Blo 187803 606791 := bstep (se 1 (by rfl) ⟨455093, by rfl⟩ : syracuseStep 606791 = 910187) B910187
theorem B803449 : Blo 187803 803449 := bstep (se 2 (by rfl) ⟨301293, by rfl⟩ : syracuseStep 803449 = 602587) B602587
theorem B9290375 : Blo 187803 9290375 := bstep (se 1 (by rfl) ⟨6967781, by rfl⟩ : syracuseStep 9290375 = 13935563) B13935563
theorem B441762497 : Blo 187803 441762497 := bstep (se 2 (by rfl) ⟨165660936, by rfl⟩ : syracuseStep 441762497 = 331321873) B331321873
theorem B213727 : Blo 187803 213727 := bstep (se 1 (by rfl) ⟨160295, by rfl⟩ : syracuseStep 213727 = 320591) B320591
theorem B475895 : Blo 187803 475895 := bstep (se 1 (by rfl) ⟨356921, by rfl⟩ : syracuseStep 475895 = 713843) B713843
theorem B344911 : Blo 187803 344911 := bstep (se 1 (by rfl) ⟨258683, by rfl⟩ : syracuseStep 344911 = 517367) B517367
theorem B1295297 : Blo 187803 1295297 := bstep (se 2 (by rfl) ⟨485736, by rfl⟩ : syracuseStep 1295297 = 971473) B971473
theorem B967625 : Blo 187803 967625 := bstep (se 2 (by rfl) ⟨362859, by rfl⟩ : syracuseStep 967625 = 725719) B725719
theorem B214303 : Blo 187803 214303 := bstep (se 1 (by rfl) ⟨160727, by rfl⟩ : syracuseStep 214303 = 321455) B321455
theorem B476513 : Blo 187803 476513 := bstep (se 2 (by rfl) ⟨178692, by rfl⟩ : syracuseStep 476513 = 357385) B357385
theorem B214591 : Blo 187803 214591 := bstep (se 1 (by rfl) ⟨160943, by rfl⟩ : syracuseStep 214591 = 321887) B321887
theorem B903095 : Blo 187803 903095 := bstep (se 1 (by rfl) ⟨677321, by rfl⟩ : syracuseStep 903095 = 1354643) B1354643
theorem B1034167 : Blo 187803 1034167 := bstep (se 1 (by rfl) ⟨775625, by rfl⟩ : syracuseStep 1034167 = 1551251) B1551251
theorem B215419 : Blo 187803 215419 := bstep (se 1 (by rfl) ⟨161564, by rfl⟩ : syracuseStep 215419 = 323129) B323129
theorem B215623 : Blo 187803 215623 := bstep (se 1 (by rfl) ⟨161717, by rfl⟩ : syracuseStep 215623 = 323435) B323435
theorem B543311 : Blo 187803 543311 := bstep (se 1 (by rfl) ⟨407483, by rfl⟩ : syracuseStep 543311 = 814967) B814967
theorem B1100477 : Blo 187803 1100477 := bstep (se 3 (by rfl) ⟨206339, by rfl⟩ : syracuseStep 1100477 = 412679) B412679
theorem B3099383 : Blo 187803 3099383 := bstep (se 1 (by rfl) ⟨2324537, by rfl⟩ : syracuseStep 3099383 = 4649075) B4649075
theorem B477971 : Blo 187803 477971 := bstep (se 1 (by rfl) ⟨358478, by rfl⟩ : syracuseStep 477971 = 716957) B716957
theorem B4016947 : Blo 187803 4016947 := bstep (se 1 (by rfl) ⟨3012710, by rfl⟩ : syracuseStep 4016947 = 6025421) B6025421
theorem B1526663 : Blo 187803 1526663 := bstep (se 1 (by rfl) ⟨1144997, by rfl⟩ : syracuseStep 1526663 = 2289995) B2289995
theorem B478183 : Blo 187803 478183 := bstep (se 1 (by rfl) ⟨358637, by rfl⟩ : syracuseStep 478183 = 717275) B717275
theorem B281819 : Blo 187803 281819 := bstep (se 1 (by rfl) ⟨211364, by rfl⟩ : syracuseStep 281819 = 422729) B422729
theorem B478457 : Blo 187803 478457 := bstep (se 2 (by rfl) ⟨179421, by rfl⟩ : syracuseStep 478457 = 358843) B358843
theorem B544097 : Blo 187803 544097 := bstep (se 2 (by rfl) ⟨204036, by rfl⟩ : syracuseStep 544097 = 408073) B408073
theorem B281993 : Blo 187803 281993 := bstep (se 2 (by rfl) ⟨105747, by rfl⟩ : syracuseStep 281993 = 211495) B211495
theorem B642491 : Blo 187803 642491 := bstep (se 1 (by rfl) ⟨481868, by rfl⟩ : syracuseStep 642491 = 963737) B963737
theorem B511571 : Blo 187803 511571 := bstep (se 1 (by rfl) ⟨383678, by rfl⟩ : syracuseStep 511571 = 767357) B767357
theorem B282347 : Blo 187803 282347 := bstep (se 1 (by rfl) ⟨211760, by rfl⟩ : syracuseStep 282347 = 423521) B423521
theorem B544553 : Blo 187803 544553 := bstep (se 2 (by rfl) ⟨204207, by rfl⟩ : syracuseStep 544553 = 408415) B408415
theorem B479105 : Blo 187803 479105 := bstep (se 2 (by rfl) ⟨179664, by rfl⟩ : syracuseStep 479105 = 359329) B359329
theorem B282575 : Blo 187803 282575 := bstep (se 1 (by rfl) ⟨211931, by rfl⟩ : syracuseStep 282575 = 423863) B423863
theorem B282971 : Blo 187803 282971 := bstep (se 1 (by rfl) ⟨212228, by rfl⟩ : syracuseStep 282971 = 424457) B424457
theorem B283199 : Blo 187803 283199 := bstep (se 1 (by rfl) ⟨212399, by rfl⟩ : syracuseStep 283199 = 424799) B424799
theorem B479915 : Blo 187803 479915 := bstep (se 1 (by rfl) ⟨359936, by rfl⟩ : syracuseStep 479915 = 719873) B719873
theorem B283319 : Blo 187803 283319 := bstep (se 1 (by rfl) ⟨212489, by rfl⟩ : syracuseStep 283319 = 424979) B424979
theorem B676687 : Blo 187803 676687 := bstep (se 1 (by rfl) ⟨507515, by rfl⟩ : syracuseStep 676687 = 1015031) B1015031
theorem B283547 : Blo 187803 283547 := bstep (se 1 (by rfl) ⟨212660, by rfl⟩ : syracuseStep 283547 = 425321) B425321
theorem B283943 : Blo 187803 283943 := bstep (se 1 (by rfl) ⟨212957, by rfl⟩ : syracuseStep 283943 = 425915) B425915
theorem B284027 : Blo 187803 284027 := bstep (se 1 (by rfl) ⟨213020, by rfl⟩ : syracuseStep 284027 = 426041) B426041
theorem B284153 : Blo 187803 284153 := bstep (se 2 (by rfl) ⟨106557, by rfl⟩ : syracuseStep 284153 = 213115) B213115
theorem B7722503 : Blo 187803 7722503 := bstep (se 1 (by rfl) ⟨5791877, by rfl⟩ : syracuseStep 7722503 = 11583755) B11583755
theorem B480775 : Blo 187803 480775 := bstep (se 1 (by rfl) ⟨360581, by rfl⟩ : syracuseStep 480775 = 721163) B721163
theorem B906785 : Blo 187803 906785 := bstep (se 2 (by rfl) ⟨340044, by rfl⟩ : syracuseStep 906785 = 680089) B680089
theorem B284255 : Blo 187803 284255 := bstep (se 1 (by rfl) ⟨213191, by rfl⟩ : syracuseStep 284255 = 426383) B426383
theorem B14636771 : Blo 187803 14636771 := bstep (se 1 (by rfl) ⟨10977578, by rfl⟩ : syracuseStep 14636771 = 21955157) B21955157
theorem B284471 : Blo 187803 284471 := bstep (se 1 (by rfl) ⟨213353, by rfl⟩ : syracuseStep 284471 = 426707) B426707
theorem B481079 : Blo 187803 481079 := bstep (se 1 (by rfl) ⟨360809, by rfl⟩ : syracuseStep 481079 = 721619) B721619
theorem B284777 : Blo 187803 284777 := bstep (se 2 (by rfl) ⟨106791, by rfl⟩ : syracuseStep 284777 = 213583) B213583
theorem B612481 : Blo 187803 612481 := bstep (se 2 (by rfl) ⟨229680, by rfl⟩ : syracuseStep 612481 = 459361) B459361
theorem B809327 : Blo 187803 809327 := bstep (se 1 (by rfl) ⟨606995, by rfl⟩ : syracuseStep 809327 = 1213991) B1213991
theorem B285095 : Blo 187803 285095 := bstep (se 1 (by rfl) ⟨213821, by rfl⟩ : syracuseStep 285095 = 427643) B427643
theorem B481747 : Blo 187803 481747 := bstep (se 1 (by rfl) ⟨361310, by rfl⟩ : syracuseStep 481747 = 722621) B722621
theorem B383483 : Blo 187803 383483 := bstep (se 1 (by rfl) ⟨287612, by rfl⟩ : syracuseStep 383483 = 575225) B575225
theorem B285179 : Blo 187803 285179 := bstep (se 1 (by rfl) ⟨213884, by rfl⟩ : syracuseStep 285179 = 427769) B427769
theorem B318073 : Blo 187803 318073 := bstep (se 2 (by rfl) ⟨119277, by rfl⟩ : syracuseStep 318073 = 238555) B238555
theorem B285305 : Blo 187803 285305 := bstep (se 2 (by rfl) ⟨106989, by rfl⟩ : syracuseStep 285305 = 213979) B213979
theorem B1071791 : Blo 187803 1071791 := bstep (se 1 (by rfl) ⟨803843, by rfl⟩ : syracuseStep 1071791 = 1607687) B1607687
theorem B318127 : Blo 187803 318127 := bstep (se 1 (by rfl) ⟨238595, by rfl⟩ : syracuseStep 318127 = 477191) B477191
theorem B285359 : Blo 187803 285359 := bstep (se 1 (by rfl) ⟨214019, by rfl⟩ : syracuseStep 285359 = 428039) B428039
theorem B285407 : Blo 187803 285407 := bstep (se 1 (by rfl) ⟨214055, by rfl⟩ : syracuseStep 285407 = 428111) B428111
theorem B285671 : Blo 187803 285671 := bstep (se 1 (by rfl) ⟨214253, by rfl⟩ : syracuseStep 285671 = 428507) B428507
theorem B285929 : Blo 187803 285929 := bstep (se 2 (by rfl) ⟨107223, by rfl⟩ : syracuseStep 285929 = 214447) B214447
theorem B482537 : Blo 187803 482537 := bstep (se 2 (by rfl) ⟨180951, by rfl⟩ : syracuseStep 482537 = 361903) B361903
theorem B285983 : Blo 187803 285983 := bstep (se 1 (by rfl) ⟨214487, by rfl⟩ : syracuseStep 285983 = 428975) B428975
theorem B482699 : Blo 187803 482699 := bstep (se 1 (by rfl) ⟨362024, by rfl⟩ : syracuseStep 482699 = 724049) B724049
theorem B187815 : Blo 187803 187815 := bstep (se 1 (by rfl) ⟨140861, by rfl⟩ : syracuseStep 187815 = 281723) B281723
theorem B286151 : Blo 187803 286151 := bstep (se 1 (by rfl) ⟨214613, by rfl⟩ : syracuseStep 286151 = 429227) B429227
theorem B646649 : Blo 187803 646649 := bstep (se 2 (by rfl) ⟨242493, by rfl⟩ : syracuseStep 646649 = 484987) B484987
theorem B187899 : Blo 187803 187899 := bstep (se 1 (by rfl) ⟨140924, by rfl⟩ : syracuseStep 187899 = 281849) B281849
theorem B187967 : Blo 187803 187967 := bstep (se 1 (by rfl) ⟨140975, by rfl⟩ : syracuseStep 187967 = 281951) B281951
theorem B187975 : Blo 187803 187975 := bstep (se 1 (by rfl) ⟨140981, by rfl⟩ : syracuseStep 187975 = 281963) B281963
theorem B1072723 : Blo 187803 1072723 := bstep (se 1 (by rfl) ⟨804542, by rfl⟩ : syracuseStep 1072723 = 1609085) B1609085
theorem B188127 : Blo 187803 188127 := bstep (se 1 (by rfl) ⟨141095, by rfl⟩ : syracuseStep 188127 = 282191) B282191
theorem B646919 : Blo 187803 646919 := bstep (se 1 (by rfl) ⟨485189, by rfl⟩ : syracuseStep 646919 = 970379) B970379
theorem B286505 : Blo 187803 286505 := bstep (se 2 (by rfl) ⟨107439, by rfl⟩ : syracuseStep 286505 = 214879) B214879
theorem B188207 : Blo 187803 188207 := bstep (se 1 (by rfl) ⟨141155, by rfl⟩ : syracuseStep 188207 = 282311) B282311
theorem B286511 : Blo 187803 286511 := bstep (se 1 (by rfl) ⟨214883, by rfl⟩ : syracuseStep 286511 = 429767) B429767
theorem B646973 : Blo 187803 646973 := bstep (se 3 (by rfl) ⟨121307, by rfl⟩ : syracuseStep 646973 = 242615) B242615
theorem B188315 : Blo 187803 188315 := bstep (se 1 (by rfl) ⟨141236, by rfl⟩ : syracuseStep 188315 = 282473) B282473
theorem B188367 : Blo 187803 188367 := bstep (se 1 (by rfl) ⟨141275, by rfl⟩ : syracuseStep 188367 = 282551) B282551
theorem B188391 : Blo 187803 188391 := bstep (se 1 (by rfl) ⟨141293, by rfl⟩ : syracuseStep 188391 = 282587) B282587
theorem B286985 : Blo 187803 286985 := bstep (se 2 (by rfl) ⟨107619, by rfl⟩ : syracuseStep 286985 = 215239) B215239
theorem B188703 : Blo 187803 188703 := bstep (se 1 (by rfl) ⟨141527, by rfl⟩ : syracuseStep 188703 = 283055) B283055
theorem B188763 : Blo 187803 188763 := bstep (se 1 (by rfl) ⟨141572, by rfl⟩ : syracuseStep 188763 = 283145) B283145
theorem B319835 : Blo 187803 319835 := bstep (se 1 (by rfl) ⟨239876, by rfl⟩ : syracuseStep 319835 = 479753) B479753
theorem B483691 : Blo 187803 483691 := bstep (se 1 (by rfl) ⟨362768, by rfl⟩ : syracuseStep 483691 = 725537) B725537
theorem B188783 : Blo 187803 188783 := bstep (se 1 (by rfl) ⟨141587, by rfl⟩ : syracuseStep 188783 = 283175) B283175
theorem B319855 : Blo 187803 319855 := bstep (se 1 (by rfl) ⟨239891, by rfl⟩ : syracuseStep 319855 = 479783) B479783
theorem B287087 : Blo 187803 287087 := bstep (se 1 (by rfl) ⟨215315, by rfl⟩ : syracuseStep 287087 = 430631) B430631
theorem B188839 : Blo 187803 188839 := bstep (se 1 (by rfl) ⟨141629, by rfl⟩ : syracuseStep 188839 = 283259) B283259
theorem B188923 : Blo 187803 188923 := bstep (se 1 (by rfl) ⟨141692, by rfl⟩ : syracuseStep 188923 = 283385) B283385
theorem B4842017 : Blo 187803 4842017 := bstep (se 2 (by rfl) ⟨1815756, by rfl⟩ : syracuseStep 4842017 = 3631513) B3631513
theorem B188991 : Blo 187803 188991 := bstep (se 1 (by rfl) ⟨141743, by rfl⟩ : syracuseStep 188991 = 283487) B283487
theorem B188999 : Blo 187803 188999 := bstep (se 1 (by rfl) ⟨141749, by rfl⟩ : syracuseStep 188999 = 283499) B283499
theorem B320071 : Blo 187803 320071 := bstep (se 1 (by rfl) ⟨240053, by rfl⟩ : syracuseStep 320071 = 480107) B480107
theorem B385607 : Blo 187803 385607 := bstep (se 1 (by rfl) ⟨289205, by rfl⟩ : syracuseStep 385607 = 578411) B578411
theorem B287303 : Blo 187803 287303 := bstep (se 1 (by rfl) ⟨215477, by rfl⟩ : syracuseStep 287303 = 430955) B430955
theorem B287339 : Blo 187803 287339 := bstep (se 1 (by rfl) ⟨215504, by rfl⟩ : syracuseStep 287339 = 431009) B431009
theorem B713387 : Blo 187803 713387 := bstep (se 1 (by rfl) ⟨535040, by rfl⟩ : syracuseStep 713387 = 1070081) B1070081
theorem B2482859 : Blo 187803 2482859 := bstep (se 1 (by rfl) ⟨1862144, by rfl⟩ : syracuseStep 2482859 = 3724289) B3724289
theorem B484015 : Blo 187803 484015 := bstep (se 1 (by rfl) ⟨363011, by rfl⟩ : syracuseStep 484015 = 726023) B726023
theorem B189151 : Blo 187803 189151 := bstep (se 1 (by rfl) ⟨141863, by rfl⟩ : syracuseStep 189151 = 283727) B283727
theorem B189231 : Blo 187803 189231 := bstep (se 1 (by rfl) ⟨141923, by rfl⟩ : syracuseStep 189231 = 283847) B283847
theorem B287567 : Blo 187803 287567 := bstep (se 1 (by rfl) ⟨215675, by rfl⟩ : syracuseStep 287567 = 431351) B431351
theorem B3236759 : Blo 187803 3236759 := bstep (se 1 (by rfl) ⟨2427569, by rfl⟩ : syracuseStep 3236759 = 4855139) B4855139
theorem B189339 : Blo 187803 189339 := bstep (se 1 (by rfl) ⟨142004, by rfl⟩ : syracuseStep 189339 = 284009) B284009
theorem B189391 : Blo 187803 189391 := bstep (se 1 (by rfl) ⟨142043, by rfl⟩ : syracuseStep 189391 = 284087) B284087
theorem B189415 : Blo 187803 189415 := bstep (se 1 (by rfl) ⟨142061, by rfl⟩ : syracuseStep 189415 = 284123) B284123
theorem B484339 : Blo 187803 484339 := bstep (se 1 (by rfl) ⟨363254, by rfl⟩ : syracuseStep 484339 = 726509) B726509
theorem B320503 : Blo 187803 320503 := bstep (se 1 (by rfl) ⟨240377, by rfl⟩ : syracuseStep 320503 = 480755) B480755
theorem B2450533 : Blo 187803 2450533 := bstep (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) B459475
theorem B189727 : Blo 187803 189727 := bstep (se 1 (by rfl) ⟨142295, by rfl⟩ : syracuseStep 189727 = 284591) B284591
theorem B320807 : Blo 187803 320807 := bstep (se 1 (by rfl) ⟨240605, by rfl⟩ : syracuseStep 320807 = 481211) B481211
theorem B189787 : Blo 187803 189787 := bstep (se 1 (by rfl) ⟨142340, by rfl⟩ : syracuseStep 189787 = 284681) B284681
theorem B189807 : Blo 187803 189807 := bstep (se 1 (by rfl) ⟨142355, by rfl⟩ : syracuseStep 189807 = 284711) B284711
theorem B189863 : Blo 187803 189863 := bstep (se 1 (by rfl) ⟨142397, by rfl⟩ : syracuseStep 189863 = 284795) B284795
theorem B517565 : Blo 187803 517565 := bstep (se 3 (by rfl) ⟨97043, by rfl⟩ : syracuseStep 517565 = 194087) B194087
theorem B189947 : Blo 187803 189947 := bstep (se 1 (by rfl) ⟨142460, by rfl⟩ : syracuseStep 189947 = 284921) B284921
theorem B190015 : Blo 187803 190015 := bstep (se 1 (by rfl) ⟨142511, by rfl⟩ : syracuseStep 190015 = 285023) B285023
theorem B190023 : Blo 187803 190023 := bstep (se 1 (by rfl) ⟨142517, by rfl⟩ : syracuseStep 190023 = 285035) B285035
theorem B190175 : Blo 187803 190175 := bstep (se 1 (by rfl) ⟨142631, by rfl⟩ : syracuseStep 190175 = 285263) B285263
theorem B321259 : Blo 187803 321259 := bstep (se 1 (by rfl) ⟨240944, by rfl⟩ : syracuseStep 321259 = 481889) B481889
theorem B485099 : Blo 187803 485099 := bstep (se 1 (by rfl) ⟨363824, by rfl⟩ : syracuseStep 485099 = 727649) B727649
theorem B190255 : Blo 187803 190255 := bstep (se 1 (by rfl) ⟨142691, by rfl⟩ : syracuseStep 190255 = 285383) B285383
theorem B190363 : Blo 187803 190363 := bstep (se 1 (by rfl) ⟨142772, by rfl⟩ : syracuseStep 190363 = 285545) B285545
theorem B190415 : Blo 187803 190415 := bstep (se 1 (by rfl) ⟨142811, by rfl⟩ : syracuseStep 190415 = 285623) B285623
theorem B190439 : Blo 187803 190439 := bstep (se 1 (by rfl) ⟨142829, by rfl⟩ : syracuseStep 190439 = 285659) B285659
theorem B190751 : Blo 187803 190751 := bstep (se 1 (by rfl) ⟨143063, by rfl⟩ : syracuseStep 190751 = 286127) B286127
theorem B190811 : Blo 187803 190811 := bstep (se 1 (by rfl) ⟨143108, by rfl⟩ : syracuseStep 190811 = 286217) B286217
theorem B190831 : Blo 187803 190831 := bstep (se 1 (by rfl) ⟨143123, by rfl⟩ : syracuseStep 190831 = 286247) B286247
theorem B256379 : Blo 187803 256379 := bstep (se 1 (by rfl) ⟨192284, by rfl⟩ : syracuseStep 256379 = 384569) B384569
theorem B190887 : Blo 187803 190887 := bstep (se 1 (by rfl) ⟨143165, by rfl⟩ : syracuseStep 190887 = 286331) B286331
theorem B387553 : Blo 187803 387553 := bstep (se 2 (by rfl) ⟨145332, by rfl⟩ : syracuseStep 387553 = 290665) B290665
theorem B190971 : Blo 187803 190971 := bstep (se 1 (by rfl) ⟨143228, by rfl⟩ : syracuseStep 190971 = 286457) B286457
theorem B191039 : Blo 187803 191039 := bstep (se 1 (by rfl) ⟨143279, by rfl⟩ : syracuseStep 191039 = 286559) B286559
theorem B191047 : Blo 187803 191047 := bstep (se 1 (by rfl) ⟨143285, by rfl⟩ : syracuseStep 191047 = 286571) B286571
theorem B911945 : Blo 187803 911945 := bstep (se 2 (by rfl) ⟨341979, by rfl⟩ : syracuseStep 911945 = 683959) B683959
theorem B322231 : Blo 187803 322231 := bstep (se 1 (by rfl) ⟨241673, by rfl⟩ : syracuseStep 322231 = 483347) B483347
theorem B191199 : Blo 187803 191199 := bstep (se 1 (by rfl) ⟨143399, by rfl⟩ : syracuseStep 191199 = 286799) B286799
theorem B191279 : Blo 187803 191279 := bstep (se 1 (by rfl) ⟨143459, by rfl⟩ : syracuseStep 191279 = 286919) B286919
theorem B191387 : Blo 187803 191387 := bstep (se 1 (by rfl) ⟨143540, by rfl⟩ : syracuseStep 191387 = 287081) B287081
theorem B191439 : Blo 187803 191439 := bstep (se 1 (by rfl) ⟨143579, by rfl⟩ : syracuseStep 191439 = 287159) B287159
theorem B322535 : Blo 187803 322535 := bstep (se 1 (by rfl) ⟨241901, by rfl⟩ : syracuseStep 322535 = 483803) B483803
theorem B191463 : Blo 187803 191463 := bstep (se 1 (by rfl) ⟨143597, by rfl⟩ : syracuseStep 191463 = 287195) B287195
theorem B31878157 : Blo 187803 31878157 := bstep (se 3 (by rfl) ⟨5977154, by rfl⟩ : syracuseStep 31878157 = 11954309) B11954309
theorem B191775 : Blo 187803 191775 := bstep (se 1 (by rfl) ⟨143831, by rfl⟩ : syracuseStep 191775 = 287663) B287663
theorem B1207817 : Blo 187803 1207817 := bstep (se 2 (by rfl) ⟨452931, by rfl⟩ : syracuseStep 1207817 = 905863) B905863
theorem B716303 : Blo 187803 716303 := bstep (se 1 (by rfl) ⟨537227, by rfl⟩ : syracuseStep 716303 = 1074455) B1074455
theorem B487705 : Blo 187803 487705 := bstep (se 2 (by rfl) ⟨182889, by rfl⟩ : syracuseStep 487705 = 365779) B365779
theorem B324091 : Blo 187803 324091 := bstep (se 1 (by rfl) ⟨243068, by rfl⟩ : syracuseStep 324091 = 486137) B486137
theorem B4452889 : Blo 187803 4452889 := bstep (se 2 (by rfl) ⟨1669833, by rfl⟩ : syracuseStep 4452889 = 3339667) B3339667
theorem B422675 : Blo 187803 422675 := bstep (se 1 (by rfl) ⟨317006, by rfl⟩ : syracuseStep 422675 = 634013) B634013
theorem B2290679 : Blo 187803 2290679 := bstep (se 1 (by rfl) ⟨1718009, by rfl⟩ : syracuseStep 2290679 = 3436019) B3436019
theorem B455777 : Blo 187803 455777 := bstep (se 2 (by rfl) ⟨170916, by rfl⟩ : syracuseStep 455777 = 341833) B341833
theorem B423035 : Blo 187803 423035 := bstep (se 1 (by rfl) ⟨317276, by rfl⟩ : syracuseStep 423035 = 634553) B634553
theorem B423161 : Blo 187803 423161 := bstep (se 2 (by rfl) ⟨158685, by rfl⟩ : syracuseStep 423161 = 317371) B317371
theorem B685351 : Blo 187803 685351 := bstep (se 1 (by rfl) ⟨514013, by rfl⟩ : syracuseStep 685351 = 1028027) B1028027
theorem B423305 : Blo 187803 423305 := bstep (se 2 (by rfl) ⟨158739, by rfl⟩ : syracuseStep 423305 = 317479) B317479
theorem B325001 : Blo 187803 325001 := bstep (se 2 (by rfl) ⟨121875, by rfl⟩ : syracuseStep 325001 = 243751) B243751
theorem B423431 : Blo 187803 423431 := bstep (se 1 (by rfl) ⟨317573, by rfl⟩ : syracuseStep 423431 = 635147) B635147
theorem B423611 : Blo 187803 423611 := bstep (se 1 (by rfl) ⟨317708, by rfl⟩ : syracuseStep 423611 = 635417) B635417
theorem B423737 : Blo 187803 423737 := bstep (se 2 (by rfl) ⟨158901, by rfl⟩ : syracuseStep 423737 = 317803) B317803
theorem B5142629 : Blo 187803 5142629 := bstep (se 4 (by rfl) ⟨482121, by rfl⟩ : syracuseStep 5142629 = 964243) B964243
theorem B883055 : Blo 187803 883055 := bstep (se 1 (by rfl) ⟨662291, by rfl⟩ : syracuseStep 883055 = 1324583) B1324583
theorem B424367 : Blo 187803 424367 := bstep (se 1 (by rfl) ⟨318275, by rfl⟩ : syracuseStep 424367 = 636551) B636551
theorem B424403 : Blo 187803 424403 := bstep (se 1 (by rfl) ⟨318302, by rfl⟩ : syracuseStep 424403 = 636605) B636605
theorem B424511 : Blo 187803 424511 := bstep (se 1 (by rfl) ⟨318383, by rfl⟩ : syracuseStep 424511 = 636767) B636767
theorem B424619 : Blo 187803 424619 := bstep (se 1 (by rfl) ⟨318464, by rfl⟩ : syracuseStep 424619 = 636929) B636929
theorem B228143 : Blo 187803 228143 := bstep (se 1 (by rfl) ⟨171107, by rfl⟩ : syracuseStep 228143 = 342215) B342215
theorem B818075 : Blo 187803 818075 := bstep (se 1 (by rfl) ⟨613556, by rfl⟩ : syracuseStep 818075 = 1227113) B1227113
theorem B425159 : Blo 187803 425159 := bstep (se 1 (by rfl) ⟨318869, by rfl⟩ : syracuseStep 425159 = 637739) B637739
theorem B1440989 : Blo 187803 1440989 := bstep (se 3 (by rfl) ⟨270185, by rfl⟩ : syracuseStep 1440989 = 540371) B540371
theorem B359777 : Blo 187803 359777 := bstep (se 2 (by rfl) ⟨134916, by rfl⟩ : syracuseStep 359777 = 269833) B269833
theorem B425339 : Blo 187803 425339 := bstep (se 1 (by rfl) ⟨319004, by rfl⟩ : syracuseStep 425339 = 638009) B638009
theorem B425465 : Blo 187803 425465 := bstep (se 2 (by rfl) ⟨159549, by rfl⟩ : syracuseStep 425465 = 319099) B319099
theorem B425555 : Blo 187803 425555 := bstep (se 1 (by rfl) ⟨319166, by rfl⟩ : syracuseStep 425555 = 638333) B638333
theorem B818849 : Blo 187803 818849 := bstep (se 2 (by rfl) ⟨307068, by rfl⟩ : syracuseStep 818849 = 614137) B614137
theorem B425735 : Blo 187803 425735 := bstep (se 1 (by rfl) ⟨319301, by rfl⟩ : syracuseStep 425735 = 638603) B638603
theorem B720647 : Blo 187803 720647 := bstep (se 1 (by rfl) ⟨540485, by rfl⟩ : syracuseStep 720647 = 1080971) B1080971
theorem B1834825 : Blo 187803 1834825 := bstep (se 2 (by rfl) ⟨688059, by rfl⟩ : syracuseStep 1834825 = 1376119) B1376119
theorem B819017 : Blo 187803 819017 := bstep (se 2 (by rfl) ⟨307131, by rfl⟩ : syracuseStep 819017 = 614263) B614263
theorem B1638305 : Blo 187803 1638305 := bstep (se 2 (by rfl) ⟨614364, by rfl⟩ : syracuseStep 1638305 = 1228729) B1228729
theorem B426023 : Blo 187803 426023 := bstep (se 1 (by rfl) ⟨319517, by rfl⟩ : syracuseStep 426023 = 639035) B639035
theorem B426203 : Blo 187803 426203 := bstep (se 1 (by rfl) ⟨319652, by rfl⟩ : syracuseStep 426203 = 639305) B639305
theorem B6193583 : Blo 187803 6193583 := bstep (se 1 (by rfl) ⟨4645187, by rfl⟩ : syracuseStep 6193583 = 9290375) B9290375
theorem B426473 : Blo 187803 426473 := bstep (se 2 (by rfl) ⟨159927, by rfl⟩ : syracuseStep 426473 = 319855) B319855
theorem B3080699 : Blo 187803 3080699 := bstep (se 1 (by rfl) ⟨2310524, by rfl⟩ : syracuseStep 3080699 = 4621049) B4621049
theorem B426761 : Blo 187803 426761 := bstep (se 2 (by rfl) ⟨160035, by rfl⟩ : syracuseStep 426761 = 320071) B320071
theorem B361273 : Blo 187803 361273 := bstep (se 2 (by rfl) ⟨135477, by rfl⟩ : syracuseStep 361273 = 270955) B270955
theorem B3670879 : Blo 187803 3670879 := bstep (se 1 (by rfl) ⟨2753159, by rfl⟩ : syracuseStep 3670879 = 5506319) B5506319
theorem B721831 : Blo 187803 721831 := bstep (se 1 (by rfl) ⟨541373, by rfl⟩ : syracuseStep 721831 = 1082747) B1082747
theorem B361577 : Blo 187803 361577 := bstep (se 2 (by rfl) ⟨135591, by rfl⟩ : syracuseStep 361577 = 271183) B271183
theorem B459881 : Blo 187803 459881 := bstep (se 2 (by rfl) ⟨172455, by rfl⟩ : syracuseStep 459881 = 344911) B344911
theorem B427337 : Blo 187803 427337 := bstep (se 2 (by rfl) ⟨160251, by rfl⟩ : syracuseStep 427337 = 320503) B320503
theorem B329131 : Blo 187803 329131 := bstep (se 1 (by rfl) ⟨246848, by rfl⟩ : syracuseStep 329131 = 493697) B493697
theorem B2360927 : Blo 187803 2360927 := bstep (se 1 (by rfl) ⟨1770695, by rfl⟩ : syracuseStep 2360927 = 3541391) B3541391
theorem B362207 : Blo 187803 362207 := bstep (se 1 (by rfl) ⟨271655, by rfl⟩ : syracuseStep 362207 = 543311) B543311
theorem B6620957 : Blo 187803 6620957 := bstep (se 3 (by rfl) ⟨1241429, by rfl⟩ : syracuseStep 6620957 = 2482859) B2482859
theorem B2066255 : Blo 187803 2066255 := bstep (se 1 (by rfl) ⟨1549691, by rfl⟩ : syracuseStep 2066255 = 3099383) B3099383
theorem B1017775 : Blo 187803 1017775 := bstep (se 1 (by rfl) ⟨763331, by rfl⟩ : syracuseStep 1017775 = 1526663) B1526663
theorem B362731 : Blo 187803 362731 := bstep (se 1 (by rfl) ⟨272048, by rfl⟩ : syracuseStep 362731 = 544097) B544097
theorem B428327 : Blo 187803 428327 := bstep (se 1 (by rfl) ⟨321245, by rfl⟩ : syracuseStep 428327 = 642491) B642491
theorem B428345 : Blo 187803 428345 := bstep (se 2 (by rfl) ⟨160629, by rfl⟩ : syracuseStep 428345 = 321259) B321259
theorem B363035 : Blo 187803 363035 := bstep (se 1 (by rfl) ⟨272276, by rfl⟩ : syracuseStep 363035 = 544553) B544553
theorem B1378889 : Blo 187803 1378889 := bstep (se 2 (by rfl) ⟨517083, by rfl⟩ : syracuseStep 1378889 = 1034167) B1034167
theorem B1837673 : Blo 187803 1837673 := bstep (se 2 (by rfl) ⟨689127, by rfl⟩ : syracuseStep 1837673 = 1378255) B1378255
theorem B723799 : Blo 187803 723799 := bstep (se 1 (by rfl) ⟨542849, by rfl⟩ : syracuseStep 723799 = 1085699) B1085699
theorem B429641 : Blo 187803 429641 := bstep (se 2 (by rfl) ⟨161115, by rfl⟩ : syracuseStep 429641 = 322231) B322231
theorem B364105 : Blo 187803 364105 := bstep (se 2 (by rfl) ⟨136539, by rfl⟩ : syracuseStep 364105 = 273079) B273079
theorem B5148335 : Blo 187803 5148335 := bstep (se 1 (by rfl) ⟨3861251, by rfl⟩ : syracuseStep 5148335 = 7722503) B7722503
theorem B42504209 : Blo 187803 42504209 := bstep (se 2 (by rfl) ⟨15939078, by rfl⟩ : syracuseStep 42504209 = 31878157) B31878157
theorem B431099 : Blo 187803 431099 := bstep (se 1 (by rfl) ⟨323324, by rfl⟩ : syracuseStep 431099 = 646649) B646649
theorem B726191 : Blo 187803 726191 := bstep (se 1 (by rfl) ⟨544643, by rfl⟩ : syracuseStep 726191 = 1089287) B1089287
theorem B431279 : Blo 187803 431279 := bstep (se 1 (by rfl) ⟨323459, by rfl⟩ : syracuseStep 431279 = 646919) B646919
theorem B431315 : Blo 187803 431315 := bstep (se 1 (by rfl) ⟨323486, by rfl⟩ : syracuseStep 431315 = 646973) B646973
theorem B432121 : Blo 187803 432121 := bstep (se 2 (by rfl) ⟨162045, by rfl⟩ : syracuseStep 432121 = 324091) B324091
theorem B5937185 : Blo 187803 5937185 := bstep (se 2 (by rfl) ⟨2226444, by rfl⟩ : syracuseStep 5937185 = 4452889) B4452889
theorem B202943 : Blo 187803 202943 := bstep (se 1 (by rfl) ⟨152207, by rfl⟩ : syracuseStep 202943 = 304415) B304415
theorem B268591 : Blo 187803 268591 := bstep (se 1 (by rfl) ⟨201443, by rfl⟩ : syracuseStep 268591 = 402887) B402887
theorem B8460935 : Blo 187803 8460935 := bstep (se 1 (by rfl) ⟨6345701, by rfl⟩ : syracuseStep 8460935 = 12691403) B12691403
theorem B2431853 : Blo 187803 2431853 := bstep (se 3 (by rfl) ⟨455972, by rfl⟩ : syracuseStep 2431853 = 911945) B911945
theorem B727967 : Blo 187803 727967 := bstep (se 1 (by rfl) ⟨545975, by rfl⟩ : syracuseStep 727967 = 1091951) B1091951
theorem B532295 : Blo 187803 532295 := bstep (se 1 (by rfl) ⟨399221, by rfl⟩ : syracuseStep 532295 = 798443) B798443
theorem B2433311 : Blo 187803 2433311 := bstep (se 1 (by rfl) ⟨1824983, by rfl⟩ : syracuseStep 2433311 = 3649967) B3649967
theorem B303851 : Blo 187803 303851 := bstep (se 1 (by rfl) ⟨227888, by rfl⟩ : syracuseStep 303851 = 455777) B455777
theorem B1451603 : Blo 187803 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B272327 : Blo 187803 272327 := bstep (se 1 (by rfl) ⟨204245, by rfl⟩ : syracuseStep 272327 = 408491) B408491
theorem B960659 : Blo 187803 960659 := bstep (se 1 (by rfl) ⟨720494, by rfl⟩ : syracuseStep 960659 = 1440989) B1440989
theorem B239851 : Blo 187803 239851 := bstep (se 1 (by rfl) ⟨179888, by rfl⟩ : syracuseStep 239851 = 359777) B359777
theorem B1092203 : Blo 187803 1092203 := bstep (se 1 (by rfl) ⟨819152, by rfl⟩ : syracuseStep 1092203 = 1638305) B1638305
theorem B535223 : Blo 187803 535223 := bstep (se 1 (by rfl) ⟨401417, by rfl⟩ : syracuseStep 535223 = 802835) B802835
theorem B535531 : Blo 187803 535531 := bstep (se 1 (by rfl) ⟨401648, by rfl⟩ : syracuseStep 535531 = 803297) B803297
theorem B404527 : Blo 187803 404527 := bstep (se 1 (by rfl) ⟨303395, by rfl⟩ : syracuseStep 404527 = 606791) B606791
theorem B240823 : Blo 187803 240823 := bstep (se 1 (by rfl) ⟨180617, by rfl⟩ : syracuseStep 240823 = 361235) B361235
theorem B5024987 : Blo 187803 5024987 := bstep (se 1 (by rfl) ⟨3768740, by rfl⟩ : syracuseStep 5024987 = 7537481) B7537481
theorem B863531 : Blo 187803 863531 := bstep (se 1 (by rfl) ⟨647648, by rfl⟩ : syracuseStep 863531 = 1295297) B1295297
theorem B535997 : Blo 187803 535997 := bstep (se 3 (by rfl) ⟨100499, by rfl⟩ : syracuseStep 535997 = 200999) B200999
theorem B1453625 : Blo 187803 1453625 := bstep (se 2 (by rfl) ⟨545109, by rfl⟩ : syracuseStep 1453625 = 1090219) B1090219
theorem B307099 : Blo 187803 307099 := bstep (se 1 (by rfl) ⟨230324, by rfl⟩ : syracuseStep 307099 = 460649) B460649
theorem B602063 : Blo 187803 602063 := bstep (se 1 (by rfl) ⟨451547, by rfl⟩ : syracuseStep 602063 = 903095) B903095
theorem B6173081 : Blo 187803 6173081 := bstep (se 2 (by rfl) ⟨2314905, by rfl⟩ : syracuseStep 6173081 = 4629811) B4629811
theorem B635471 : Blo 187803 635471 := bstep (se 1 (by rfl) ⟨476603, by rfl⟩ : syracuseStep 635471 = 953207) B953207
theorem B2896669 : Blo 187803 2896669 := bstep (se 3 (by rfl) ⟨543125, by rfl⟩ : syracuseStep 2896669 = 1086251) B1086251
theorem B341047 : Blo 187803 341047 := bstep (se 1 (by rfl) ⟨255785, by rfl⟩ : syracuseStep 341047 = 511571) B511571
theorem B636011 : Blo 187803 636011 := bstep (se 1 (by rfl) ⟨477008, by rfl⟩ : syracuseStep 636011 = 954017) B954017
theorem B1553651 : Blo 187803 1553651 := bstep (se 1 (by rfl) ⟨1165238, by rfl⟩ : syracuseStep 1553651 = 2330477) B2330477
theorem B1160887 : Blo 187803 1160887 := bstep (se 1 (by rfl) ⟨870665, by rfl⟩ : syracuseStep 1160887 = 1741331) B1741331
theorem B1554103 : Blo 187803 1554103 := bstep (se 1 (by rfl) ⟨1165577, by rfl⟩ : syracuseStep 1554103 = 2331155) B2331155
theorem B964547 : Blo 187803 964547 := bstep (se 1 (by rfl) ⟨723410, by rfl⟩ : syracuseStep 964547 = 1446821) B1446821
theorem B538721 : Blo 187803 538721 := bstep (se 2 (by rfl) ⟨202020, by rfl⟩ : syracuseStep 538721 = 404041) B404041
theorem B964871 : Blo 187803 964871 := bstep (se 1 (by rfl) ⟨723653, by rfl⟩ : syracuseStep 964871 = 1447307) B1447307
theorem B604523 : Blo 187803 604523 := bstep (se 1 (by rfl) ⟨453392, by rfl⟩ : syracuseStep 604523 = 906785) B906785
theorem B637307 : Blo 187803 637307 := bstep (se 1 (by rfl) ⟨477980, by rfl⟩ : syracuseStep 637307 = 955961) B955961
theorem B5421437 : Blo 187803 5421437 := bstep (se 3 (by rfl) ⟨1016519, by rfl⟩ : syracuseStep 5421437 = 2033039) B2033039
theorem B5355929 : Blo 187803 5355929 := bstep (se 2 (by rfl) ⟨2008473, by rfl⟩ : syracuseStep 5355929 = 4016947) B4016947
theorem B637577 : Blo 187803 637577 := bstep (se 2 (by rfl) ⟨239091, by rfl⟩ : syracuseStep 637577 = 478183) B478183
theorem B539551 : Blo 187803 539551 := bstep (se 1 (by rfl) ⟨404663, by rfl⟩ : syracuseStep 539551 = 809327) B809327
theorem B1227727 : Blo 187803 1227727 := bstep (se 1 (by rfl) ⟨920795, by rfl⟩ : syracuseStep 1227727 = 1841591) B1841591
theorem B966329 : Blo 187803 966329 := bstep (se 2 (by rfl) ⟨362373, by rfl⟩ : syracuseStep 966329 = 724747) B724747
theorem B5521081 : Blo 187803 5521081 := bstep (se 2 (by rfl) ⟨2070405, by rfl⟩ : syracuseStep 5521081 = 4140811) B4140811
theorem B638711 : Blo 187803 638711 := bstep (se 1 (by rfl) ⟨479033, by rfl⟩ : syracuseStep 638711 = 958067) B958067
theorem B213223 : Blo 187803 213223 := bstep (se 1 (by rfl) ⟨159917, by rfl⟩ : syracuseStep 213223 = 319835) B319835
theorem B3228011 : Blo 187803 3228011 := bstep (se 1 (by rfl) ⟨2421008, by rfl⟩ : syracuseStep 3228011 = 4842017) B4842017
theorem B475591 : Blo 187803 475591 := bstep (se 1 (by rfl) ⟨356693, by rfl⟩ : syracuseStep 475591 = 713387) B713387
theorem B1360435 : Blo 187803 1360435 := bstep (se 1 (by rfl) ⟨1020326, by rfl⟩ : syracuseStep 1360435 = 2040653) B2040653
theorem B1229363 : Blo 187803 1229363 := bstep (se 1 (by rfl) ⟨922022, by rfl⟩ : syracuseStep 1229363 = 1844045) B1844045
theorem B639791 : Blo 187803 639791 := bstep (se 1 (by rfl) ⟨479843, by rfl⟩ : syracuseStep 639791 = 959687) B959687
theorem B213871 : Blo 187803 213871 := bstep (se 1 (by rfl) ⟨160403, by rfl⟩ : syracuseStep 213871 = 320807) B320807
theorem B639899 : Blo 187803 639899 := bstep (se 1 (by rfl) ⟨479924, by rfl⟩ : syracuseStep 639899 = 959849) B959849
theorem B345043 : Blo 187803 345043 := bstep (se 1 (by rfl) ⟨258782, by rfl⟩ : syracuseStep 345043 = 517565) B517565
theorem B902249 : Blo 187803 902249 := bstep (se 2 (by rfl) ⟨338343, by rfl⟩ : syracuseStep 902249 = 676687) B676687
theorem B2147633 : Blo 187803 2147633 := bstep (se 2 (by rfl) ⟨805362, by rfl⟩ : syracuseStep 2147633 = 1610725) B1610725
theorem B509291 : Blo 187803 509291 := bstep (se 1 (by rfl) ⟨381968, by rfl⟩ : syracuseStep 509291 = 763937) B763937
theorem B1590821 : Blo 187803 1590821 := bstep (se 4 (by rfl) ⟨149139, by rfl⟩ : syracuseStep 1590821 = 298279) B298279
theorem B2934605 : Blo 187803 2934605 := bstep (se 3 (by rfl) ⟨550238, by rfl⟩ : syracuseStep 2934605 = 1100477) B1100477
theorem B215023 : Blo 187803 215023 := bstep (se 1 (by rfl) ⟨161267, by rfl⟩ : syracuseStep 215023 = 322535) B322535
theorem B641033 : Blo 187803 641033 := bstep (se 2 (by rfl) ⟨240387, by rfl⟩ : syracuseStep 641033 = 480775) B480775
theorem B608381 : Blo 187803 608381 := bstep (se 3 (by rfl) ⟨114071, by rfl⟩ : syracuseStep 608381 = 228143) B228143
theorem B1362167 : Blo 187803 1362167 := bstep (se 1 (by rfl) ⟨1021625, by rfl⟩ : syracuseStep 1362167 = 2043251) B2043251
theorem B542969 : Blo 187803 542969 := bstep (se 2 (by rfl) ⟨203613, by rfl⟩ : syracuseStep 542969 = 407227) B407227
theorem B805211 : Blo 187803 805211 := bstep (se 1 (by rfl) ⟨603908, by rfl⟩ : syracuseStep 805211 = 1207817) B1207817
theorem B477535 : Blo 187803 477535 := bstep (se 1 (by rfl) ⟨358151, by rfl⟩ : syracuseStep 477535 = 716303) B716303
theorem B281783 : Blo 187803 281783 := bstep (se 1 (by rfl) ⟨211337, by rfl⟩ : syracuseStep 281783 = 422675) B422675
theorem B642329 : Blo 187803 642329 := bstep (se 2 (by rfl) ⟨240873, by rfl⟩ : syracuseStep 642329 = 481747) B481747
theorem B1527119 : Blo 187803 1527119 := bstep (se 1 (by rfl) ⟨1145339, by rfl⟩ : syracuseStep 1527119 = 2290679) B2290679
theorem B642383 : Blo 187803 642383 := bstep (se 1 (by rfl) ⟨481787, by rfl⟩ : syracuseStep 642383 = 963575) B963575
theorem B282023 : Blo 187803 282023 := bstep (se 1 (by rfl) ⟨211517, by rfl⟩ : syracuseStep 282023 = 423035) B423035
theorem B282107 : Blo 187803 282107 := bstep (se 1 (by rfl) ⟨211580, by rfl⟩ : syracuseStep 282107 = 423161) B423161
theorem B544313 : Blo 187803 544313 := bstep (se 2 (by rfl) ⟨204117, by rfl⟩ : syracuseStep 544313 = 408235) B408235
theorem B282203 : Blo 187803 282203 := bstep (se 1 (by rfl) ⟨211652, by rfl⟩ : syracuseStep 282203 = 423305) B423305
theorem B216667 : Blo 187803 216667 := bstep (se 1 (by rfl) ⟨162500, by rfl⟩ : syracuseStep 216667 = 325001) B325001
theorem B282287 : Blo 187803 282287 := bstep (se 1 (by rfl) ⟨211715, by rfl⟩ : syracuseStep 282287 = 423431) B423431
theorem B282407 : Blo 187803 282407 := bstep (se 1 (by rfl) ⟨211805, by rfl⟩ : syracuseStep 282407 = 423611) B423611
theorem B282491 : Blo 187803 282491 := bstep (se 1 (by rfl) ⟨211868, by rfl⟩ : syracuseStep 282491 = 423737) B423737
theorem B3428419 : Blo 187803 3428419 := bstep (se 1 (by rfl) ⟨2571314, by rfl⟩ : syracuseStep 3428419 = 5142629) B5142629
theorem B315611 : Blo 187803 315611 := bstep (se 1 (by rfl) ⟨236708, by rfl⟩ : syracuseStep 315611 = 473417) B473417
theorem B282911 : Blo 187803 282911 := bstep (se 1 (by rfl) ⟨212183, by rfl⟩ : syracuseStep 282911 = 424367) B424367
theorem B282935 : Blo 187803 282935 := bstep (se 1 (by rfl) ⟨212201, by rfl⟩ : syracuseStep 282935 = 424403) B424403
theorem B283007 : Blo 187803 283007 := bstep (se 1 (by rfl) ⟨212255, by rfl⟩ : syracuseStep 283007 = 424511) B424511
theorem B2183597 : Blo 187803 2183597 := bstep (se 3 (by rfl) ⟨409424, by rfl⟩ : syracuseStep 2183597 = 818849) B818849
theorem B283079 : Blo 187803 283079 := bstep (se 1 (by rfl) ⟨212309, by rfl⟩ : syracuseStep 283079 = 424619) B424619
theorem B643679 : Blo 187803 643679 := bstep (se 1 (by rfl) ⟨482759, by rfl⟩ : syracuseStep 643679 = 965519) B965519
theorem B545383 : Blo 187803 545383 := bstep (se 1 (by rfl) ⟨409037, by rfl⟩ : syracuseStep 545383 = 818075) B818075
theorem B1430297 : Blo 187803 1430297 := bstep (se 2 (by rfl) ⟨536361, by rfl⟩ : syracuseStep 1430297 = 1072723) B1072723
theorem B283433 : Blo 187803 283433 := bstep (se 2 (by rfl) ⟨106287, by rfl⟩ : syracuseStep 283433 = 212575) B212575
theorem B283439 : Blo 187803 283439 := bstep (se 1 (by rfl) ⟨212579, by rfl⟩ : syracuseStep 283439 = 425159) B425159
theorem B283559 : Blo 187803 283559 := bstep (se 1 (by rfl) ⟨212669, by rfl⟩ : syracuseStep 283559 = 425339) B425339
theorem B283643 : Blo 187803 283643 := bstep (se 1 (by rfl) ⟨212732, by rfl⟩ : syracuseStep 283643 = 425465) B425465
theorem B676873 : Blo 187803 676873 := bstep (se 2 (by rfl) ⟨253827, by rfl⟩ : syracuseStep 676873 = 507655) B507655
theorem B283703 : Blo 187803 283703 := bstep (se 1 (by rfl) ⟨212777, by rfl⟩ : syracuseStep 283703 = 425555) B425555
theorem B2446433 : Blo 187803 2446433 := bstep (se 2 (by rfl) ⟨917412, by rfl⟩ : syracuseStep 2446433 = 1834825) B1834825
theorem B283823 : Blo 187803 283823 := bstep (se 1 (by rfl) ⟨212867, by rfl⟩ : syracuseStep 283823 = 425735) B425735
theorem B480431 : Blo 187803 480431 := bstep (se 1 (by rfl) ⟨360323, by rfl⟩ : syracuseStep 480431 = 720647) B720647
theorem B546011 : Blo 187803 546011 := bstep (se 1 (by rfl) ⟨409508, by rfl⟩ : syracuseStep 546011 = 819017) B819017
theorem B1398169 : Blo 187803 1398169 := bstep (se 2 (by rfl) ⟨524313, by rfl⟩ : syracuseStep 1398169 = 1048627) B1048627
theorem B284231 : Blo 187803 284231 := bstep (se 1 (by rfl) ⟨213173, by rfl⟩ : syracuseStep 284231 = 426347) B426347
theorem B284327 : Blo 187803 284327 := bstep (se 1 (by rfl) ⟨213245, by rfl⟩ : syracuseStep 284327 = 426491) B426491
theorem B284411 : Blo 187803 284411 := bstep (se 1 (by rfl) ⟨213308, by rfl⟩ : syracuseStep 284411 = 426617) B426617
theorem B284447 : Blo 187803 284447 := bstep (se 1 (by rfl) ⟨213335, by rfl⟩ : syracuseStep 284447 = 426671) B426671
theorem B294508331 : Blo 187803 294508331 := bstep (se 1 (by rfl) ⟨220881248, by rfl⟩ : syracuseStep 294508331 = 441762497) B441762497
theorem B644921 : Blo 187803 644921 := bstep (se 2 (by rfl) ⟨241845, by rfl⟩ : syracuseStep 644921 = 483691) B483691
theorem B317263 : Blo 187803 317263 := bstep (se 1 (by rfl) ⟨237947, by rfl⟩ : syracuseStep 317263 = 475895) B475895
theorem B284495 : Blo 187803 284495 := bstep (se 1 (by rfl) ⟨213371, by rfl⟩ : syracuseStep 284495 = 426743) B426743
theorem B284615 : Blo 187803 284615 := bstep (se 1 (by rfl) ⟨213461, by rfl⟩ : syracuseStep 284615 = 426923) B426923
theorem B645083 : Blo 187803 645083 := bstep (se 1 (by rfl) ⟨483812, by rfl⟩ : syracuseStep 645083 = 967625) B967625
theorem B481423 : Blo 187803 481423 := bstep (se 1 (by rfl) ⟨361067, by rfl⟩ : syracuseStep 481423 = 722135) B722135
theorem B1071265 : Blo 187803 1071265 := bstep (se 2 (by rfl) ⟨401724, by rfl⟩ : syracuseStep 1071265 = 803449) B803449
theorem B645353 : Blo 187803 645353 := bstep (se 2 (by rfl) ⟨242007, by rfl⟩ : syracuseStep 645353 = 484015) B484015
theorem B317675 : Blo 187803 317675 := bstep (se 1 (by rfl) ⟨238256, by rfl⟩ : syracuseStep 317675 = 476513) B476513
theorem B678131 : Blo 187803 678131 := bstep (se 1 (by rfl) ⟨508598, by rfl⟩ : syracuseStep 678131 = 1017197) B1017197
theorem B284969 : Blo 187803 284969 := bstep (se 2 (by rfl) ⟨106863, by rfl⟩ : syracuseStep 284969 = 213727) B213727
theorem B284975 : Blo 187803 284975 := bstep (se 1 (by rfl) ⟨213731, by rfl⟩ : syracuseStep 284975 = 427463) B427463
theorem B285215 : Blo 187803 285215 := bstep (se 1 (by rfl) ⟨213911, by rfl⟩ : syracuseStep 285215 = 427823) B427823
theorem B645785 : Blo 187803 645785 := bstep (se 2 (by rfl) ⟨242169, by rfl⟩ : syracuseStep 645785 = 484339) B484339
theorem B613021 : Blo 187803 613021 := bstep (se 3 (by rfl) ⟨114941, by rfl⟩ : syracuseStep 613021 = 229883) B229883
theorem B3267377 : Blo 187803 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B285599 : Blo 187803 285599 := bstep (se 1 (by rfl) ⟨214199, by rfl⟩ : syracuseStep 285599 = 428399) B428399
theorem B285647 : Blo 187803 285647 := bstep (se 1 (by rfl) ⟨214235, by rfl⟩ : syracuseStep 285647 = 428471) B428471
theorem B318505 : Blo 187803 318505 := bstep (se 2 (by rfl) ⟨119439, by rfl⟩ : syracuseStep 318505 = 238879) B238879
theorem B285737 : Blo 187803 285737 := bstep (se 2 (by rfl) ⟨107151, by rfl⟩ : syracuseStep 285737 = 214303) B214303
theorem B482345 : Blo 187803 482345 := bstep (se 2 (by rfl) ⟨180879, by rfl⟩ : syracuseStep 482345 = 361759) B361759
theorem B285743 : Blo 187803 285743 := bstep (se 1 (by rfl) ⟨214307, by rfl⟩ : syracuseStep 285743 = 428615) B428615
theorem B285767 : Blo 187803 285767 := bstep (se 1 (by rfl) ⟨214325, by rfl⟩ : syracuseStep 285767 = 428651) B428651
theorem B482375 : Blo 187803 482375 := bstep (se 1 (by rfl) ⟨361781, by rfl⟩ : syracuseStep 482375 = 723563) B723563
theorem B318647 : Blo 187803 318647 := bstep (se 1 (by rfl) ⟨238985, by rfl⟩ : syracuseStep 318647 = 477971) B477971
theorem B286031 : Blo 187803 286031 := bstep (se 1 (by rfl) ⟨214523, by rfl⟩ : syracuseStep 286031 = 429047) B429047
theorem B286121 : Blo 187803 286121 := bstep (se 2 (by rfl) ⟨107295, by rfl⟩ : syracuseStep 286121 = 214591) B214591
theorem B187879 : Blo 187803 187879 := bstep (se 1 (by rfl) ⟨140909, by rfl⟩ : syracuseStep 187879 = 281819) B281819
theorem B318971 : Blo 187803 318971 := bstep (se 1 (by rfl) ⟨239228, by rfl⟩ : syracuseStep 318971 = 478457) B478457
theorem B286271 : Blo 187803 286271 := bstep (se 1 (by rfl) ⟨214703, by rfl⟩ : syracuseStep 286271 = 429407) B429407
theorem B187995 : Blo 187803 187995 := bstep (se 1 (by rfl) ⟨140996, by rfl⟩ : syracuseStep 187995 = 281993) B281993
theorem B188231 : Blo 187803 188231 := bstep (se 1 (by rfl) ⟨141173, by rfl⟩ : syracuseStep 188231 = 282347) B282347
theorem B286535 : Blo 187803 286535 := bstep (se 1 (by rfl) ⟨214901, by rfl⟩ : syracuseStep 286535 = 429803) B429803
theorem B286619 : Blo 187803 286619 := bstep (se 1 (by rfl) ⟨214964, by rfl⟩ : syracuseStep 286619 = 429929) B429929
theorem B319403 : Blo 187803 319403 := bstep (se 1 (by rfl) ⟨239552, by rfl⟩ : syracuseStep 319403 = 479105) B479105
theorem B909245 : Blo 187803 909245 := bstep (se 3 (by rfl) ⟨170483, by rfl⟩ : syracuseStep 909245 = 340967) B340967
theorem B188383 : Blo 187803 188383 := bstep (se 1 (by rfl) ⟨141287, by rfl⟩ : syracuseStep 188383 = 282575) B282575
theorem B483367 : Blo 187803 483367 := bstep (se 1 (by rfl) ⟨362525, by rfl⟩ : syracuseStep 483367 = 725051) B725051
theorem B188647 : Blo 187803 188647 := bstep (se 1 (by rfl) ⟨141485, by rfl⟩ : syracuseStep 188647 = 282971) B282971
theorem B188799 : Blo 187803 188799 := bstep (se 1 (by rfl) ⟨141599, by rfl⟩ : syracuseStep 188799 = 283199) B283199
theorem B319943 : Blo 187803 319943 := bstep (se 1 (by rfl) ⟨239957, by rfl⟩ : syracuseStep 319943 = 479915) B479915
theorem B188879 : Blo 187803 188879 := bstep (se 1 (by rfl) ⟨141659, by rfl⟩ : syracuseStep 188879 = 283319) B283319
theorem B287183 : Blo 187803 287183 := bstep (se 1 (by rfl) ⟨215387, by rfl⟩ : syracuseStep 287183 = 430775) B430775
theorem B287225 : Blo 187803 287225 := bstep (se 2 (by rfl) ⟨107709, by rfl⟩ : syracuseStep 287225 = 215419) B215419
theorem B287327 : Blo 187803 287327 := bstep (se 1 (by rfl) ⟨215495, by rfl⟩ : syracuseStep 287327 = 430991) B430991
theorem B189031 : Blo 187803 189031 := bstep (se 1 (by rfl) ⟨141773, by rfl⟩ : syracuseStep 189031 = 283547) B283547
theorem B516737 : Blo 187803 516737 := bstep (se 2 (by rfl) ⟨193776, by rfl⟩ : syracuseStep 516737 = 387553) B387553
theorem B287497 : Blo 187803 287497 := bstep (se 2 (by rfl) ⟨107811, by rfl⟩ : syracuseStep 287497 = 215623) B215623
theorem B1073999 : Blo 187803 1073999 := bstep (se 1 (by rfl) ⟨805499, by rfl⟩ : syracuseStep 1073999 = 1610999) B1610999
theorem B189295 : Blo 187803 189295 := bstep (se 1 (by rfl) ⟨141971, by rfl⟩ : syracuseStep 189295 = 283943) B283943
theorem B189351 : Blo 187803 189351 := bstep (se 1 (by rfl) ⟨142013, by rfl⟩ : syracuseStep 189351 = 284027) B284027
theorem B189435 : Blo 187803 189435 := bstep (se 1 (by rfl) ⟨142076, by rfl⟩ : syracuseStep 189435 = 284153) B284153
theorem B189503 : Blo 187803 189503 := bstep (se 1 (by rfl) ⟨142127, by rfl⟩ : syracuseStep 189503 = 284255) B284255
theorem B9757847 : Blo 187803 9757847 := bstep (se 1 (by rfl) ⟨7318385, by rfl⟩ : syracuseStep 9757847 = 14636771) B14636771
theorem B189647 : Blo 187803 189647 := bstep (se 1 (by rfl) ⟨142235, by rfl⟩ : syracuseStep 189647 = 284471) B284471
theorem B320719 : Blo 187803 320719 := bstep (se 1 (by rfl) ⟨240539, by rfl⟩ : syracuseStep 320719 = 481079) B481079
theorem B189851 : Blo 187803 189851 := bstep (se 1 (by rfl) ⟨142388, by rfl⟩ : syracuseStep 189851 = 284777) B284777
theorem B1467919 : Blo 187803 1467919 := bstep (se 1 (by rfl) ⟨1100939, by rfl⟩ : syracuseStep 1467919 = 2201879) B2201879
theorem B9791063 : Blo 187803 9791063 := bstep (se 1 (by rfl) ⟨7343297, by rfl⟩ : syracuseStep 9791063 = 14686595) B14686595
theorem B190063 : Blo 187803 190063 := bstep (se 1 (by rfl) ⟨142547, by rfl⟩ : syracuseStep 190063 = 285095) B285095
theorem B255655 : Blo 187803 255655 := bstep (se 1 (by rfl) ⟨191741, by rfl⟩ : syracuseStep 255655 = 383483) B383483
theorem B190119 : Blo 187803 190119 := bstep (se 1 (by rfl) ⟨142589, by rfl⟩ : syracuseStep 190119 = 285179) B285179
theorem B190203 : Blo 187803 190203 := bstep (se 1 (by rfl) ⟨142652, by rfl⟩ : syracuseStep 190203 = 285305) B285305
theorem B714527 : Blo 187803 714527 := bstep (se 1 (by rfl) ⟨535895, by rfl⟩ : syracuseStep 714527 = 1071791) B1071791
theorem B190239 : Blo 187803 190239 := bstep (se 1 (by rfl) ⟨142679, by rfl⟩ : syracuseStep 190239 = 285359) B285359
theorem B190271 : Blo 187803 190271 := bstep (se 1 (by rfl) ⟨142703, by rfl⟩ : syracuseStep 190271 = 285407) B285407
theorem B190447 : Blo 187803 190447 := bstep (se 1 (by rfl) ⟨142835, by rfl⟩ : syracuseStep 190447 = 285671) B285671
theorem B321529 : Blo 187803 321529 := bstep (se 2 (by rfl) ⟨120573, by rfl⟩ : syracuseStep 321529 = 241147) B241147
theorem B190619 : Blo 187803 190619 := bstep (se 1 (by rfl) ⟨142964, by rfl⟩ : syracuseStep 190619 = 285929) B285929
theorem B321691 : Blo 187803 321691 := bstep (se 1 (by rfl) ⟨241268, by rfl⟩ : syracuseStep 321691 = 482537) B482537
theorem B190655 : Blo 187803 190655 := bstep (se 1 (by rfl) ⟨142991, by rfl⟩ : syracuseStep 190655 = 285983) B285983
theorem B682219 : Blo 187803 682219 := bstep (se 1 (by rfl) ⟨511664, by rfl⟩ : syracuseStep 682219 = 1023329) B1023329
theorem B321799 : Blo 187803 321799 := bstep (se 1 (by rfl) ⟨241349, by rfl⟩ : syracuseStep 321799 = 482699) B482699
theorem B2320649 : Blo 187803 2320649 := bstep (se 2 (by rfl) ⟨870243, by rfl⟩ : syracuseStep 2320649 = 1740487) B1740487
theorem B321833 : Blo 187803 321833 := bstep (se 2 (by rfl) ⟨120687, by rfl⟩ : syracuseStep 321833 = 241375) B241375
theorem B190767 : Blo 187803 190767 := bstep (se 1 (by rfl) ⟨143075, by rfl⟩ : syracuseStep 190767 = 286151) B286151
theorem B1075639 : Blo 187803 1075639 := bstep (se 1 (by rfl) ⟨806729, by rfl⟩ : syracuseStep 1075639 = 1613459) B1613459
theorem B191003 : Blo 187803 191003 := bstep (se 1 (by rfl) ⟨143252, by rfl⟩ : syracuseStep 191003 = 286505) B286505
theorem B191007 : Blo 187803 191007 := bstep (se 1 (by rfl) ⟨143255, by rfl⟩ : syracuseStep 191007 = 286511) B286511
theorem B191323 : Blo 187803 191323 := bstep (se 1 (by rfl) ⟨143492, by rfl⟩ : syracuseStep 191323 = 286985) B286985
theorem B191391 : Blo 187803 191391 := bstep (se 1 (by rfl) ⟨143543, by rfl⟩ : syracuseStep 191391 = 287087) B287087
theorem B814043 : Blo 187803 814043 := bstep (se 1 (by rfl) ⟨610532, by rfl⟩ : syracuseStep 814043 = 1221065) B1221065
theorem B650273 : Blo 187803 650273 := bstep (se 2 (by rfl) ⟨243852, by rfl⟩ : syracuseStep 650273 = 487705) B487705
theorem B257071 : Blo 187803 257071 := bstep (se 1 (by rfl) ⟨192803, by rfl⟩ : syracuseStep 257071 = 385607) B385607
theorem B191535 : Blo 187803 191535 := bstep (se 1 (by rfl) ⟨143651, by rfl⟩ : syracuseStep 191535 = 287303) B287303
theorem B191559 : Blo 187803 191559 := bstep (se 1 (by rfl) ⟨143669, by rfl⟩ : syracuseStep 191559 = 287339) B287339
theorem B617593 : Blo 187803 617593 := bstep (se 2 (by rfl) ⟨231597, by rfl⟩ : syracuseStep 617593 = 463195) B463195
theorem B191711 : Blo 187803 191711 := bstep (se 1 (by rfl) ⟨143783, by rfl⟩ : syracuseStep 191711 = 287567) B287567
theorem B322825 : Blo 187803 322825 := bstep (se 2 (by rfl) ⟨121059, by rfl⟩ : syracuseStep 322825 = 242119) B242119
theorem B2157839 : Blo 187803 2157839 := bstep (se 1 (by rfl) ⟨1618379, by rfl⟩ : syracuseStep 2157839 = 3236759) B3236759
theorem B683677 : Blo 187803 683677 := bstep (se 3 (by rfl) ⟨128189, by rfl⟩ : syracuseStep 683677 = 256379) B256379
theorem B323399 : Blo 187803 323399 := bstep (se 1 (by rfl) ⟨242549, by rfl⟩ : syracuseStep 323399 = 485099) B485099
theorem B1077371 : Blo 187803 1077371 := bstep (se 1 (by rfl) ⟨808028, by rfl⟩ : syracuseStep 1077371 = 1616057) B1616057
theorem B618625 : Blo 187803 618625 := bstep (se 2 (by rfl) ⟨231984, by rfl⟩ : syracuseStep 618625 = 463969) B463969
theorem B3076289 : Blo 187803 3076289 := bstep (se 2 (by rfl) ⟨1153608, by rfl⟩ : syracuseStep 3076289 = 2307217) B2307217
theorem B356663 : Blo 187803 356663 := bstep (se 1 (by rfl) ⟨267497, by rfl⟩ : syracuseStep 356663 = 534995) B534995
theorem B913801 : Blo 187803 913801 := bstep (se 2 (by rfl) ⟨342675, by rfl⟩ : syracuseStep 913801 = 685351) B685351
theorem B1208843 : Blo 187803 1208843 := bstep (se 1 (by rfl) ⟨906632, by rfl⟩ : syracuseStep 1208843 = 1813265) B1813265
theorem B2192093 : Blo 187803 2192093 := bstep (se 3 (by rfl) ⟨411017, by rfl⟩ : syracuseStep 2192093 = 822035) B822035
theorem B423323 : Blo 187803 423323 := bstep (se 1 (by rfl) ⟨317492, by rfl⟩ : syracuseStep 423323 = 634985) B634985
theorem B357787 : Blo 187803 357787 := bstep (se 1 (by rfl) ⟨268340, by rfl⟩ : syracuseStep 357787 = 536681) B536681
theorem B816641 : Blo 187803 816641 := bstep (se 2 (by rfl) ⟨306240, by rfl⟩ : syracuseStep 816641 = 612481) B612481
theorem B423899 : Blo 187803 423899 := bstep (se 1 (by rfl) ⟨317924, by rfl⟩ : syracuseStep 423899 = 635849) B635849
theorem B424079 : Blo 187803 424079 := bstep (se 1 (by rfl) ⟨318059, by rfl⟩ : syracuseStep 424079 = 636119) B636119
theorem B424097 : Blo 187803 424097 := bstep (se 2 (by rfl) ⟨159036, by rfl⟩ : syracuseStep 424097 = 318073) B318073
theorem B2717873 : Blo 187803 2717873 := bstep (se 2 (by rfl) ⟨1019202, by rfl⟩ : syracuseStep 2717873 = 2038405) B2038405
theorem B424169 : Blo 187803 424169 := bstep (se 2 (by rfl) ⟨159063, by rfl⟩ : syracuseStep 424169 = 318127) B318127
theorem B588703 : Blo 187803 588703 := bstep (se 1 (by rfl) ⟨441527, by rfl⟩ : syracuseStep 588703 = 883055) B883055
theorem B818333 : Blo 187803 818333 := bstep (se 3 (by rfl) ⟨153437, by rfl⟩ : syracuseStep 818333 = 306875) B306875
theorem B1080539 : Blo 187803 1080539 := bstep (se 1 (by rfl) ⟨810404, by rfl⟩ : syracuseStep 1080539 = 1620809) B1620809
theorem B3276125 : Blo 187803 3276125 := bstep (se 3 (by rfl) ⟨614273, by rfl⟩ : syracuseStep 3276125 = 1228547) B1228547
theorem B1244609 : Blo 187803 1244609 := bstep (se 2 (by rfl) ⟨466728, by rfl⟩ : syracuseStep 1244609 = 933457) B933457
theorem B425447 : Blo 187803 425447 := bstep (se 1 (by rfl) ⟨319085, by rfl⟩ : syracuseStep 425447 = 638171) B638171
theorem B360263 : Blo 187803 360263 := bstep (se 1 (by rfl) ⟨270197, by rfl⟩ : syracuseStep 360263 = 540395) B540395
theorem B4129055 : Blo 187803 4129055 := bstep (se 1 (by rfl) ⟨3096791, by rfl⟩ : syracuseStep 4129055 = 6193583) B6193583
theorem B819575 : Blo 187803 819575 := bstep (se 1 (by rfl) ⟨614681, by rfl⟩ : syracuseStep 819575 = 1229363) B1229363
theorem B426527 : Blo 187803 426527 := bstep (se 1 (by rfl) ⟨319895, by rfl⟩ : syracuseStep 426527 = 639791) B639791
theorem B426599 : Blo 187803 426599 := bstep (se 1 (by rfl) ⟨319949, by rfl⟩ : syracuseStep 426599 = 639899) B639899
theorem B951101 : Blo 187803 951101 := bstep (se 3 (by rfl) ⟨178331, by rfl⟩ : syracuseStep 951101 = 356663) B356663
theorem B1377503 : Blo 187803 1377503 := bstep (se 1 (by rfl) ⟨1033127, by rfl⟩ : syracuseStep 1377503 = 2066255) B2066255
theorem B427355 : Blo 187803 427355 := bstep (se 1 (by rfl) ⟨320516, by rfl⟩ : syracuseStep 427355 = 641033) B641033
theorem B361979 : Blo 187803 361979 := bstep (se 1 (by rfl) ⟨271484, by rfl⟩ : syracuseStep 361979 = 542969) B542969
theorem B427625 : Blo 187803 427625 := bstep (se 2 (by rfl) ⟨160359, by rfl⟩ : syracuseStep 427625 = 320719) B320719
theorem B1377965 : Blo 187803 1377965 := bstep (se 3 (by rfl) ⟨258368, by rfl⟩ : syracuseStep 1377965 = 516737) B516737
theorem B919259 : Blo 187803 919259 := bstep (se 1 (by rfl) ⟨689444, by rfl⟩ : syracuseStep 919259 = 1378889) B1378889
theorem B428219 : Blo 187803 428219 := bstep (se 1 (by rfl) ⟨321164, by rfl⟩ : syracuseStep 428219 = 642329) B642329
theorem B1018079 : Blo 187803 1018079 := bstep (se 1 (by rfl) ⟨763559, by rfl⟩ : syracuseStep 1018079 = 1527119) B1527119
theorem B428255 : Blo 187803 428255 := bstep (se 1 (by rfl) ⟨321191, by rfl⟩ : syracuseStep 428255 = 642383) B642383
theorem B362875 : Blo 187803 362875 := bstep (se 1 (by rfl) ⟨272156, by rfl⟩ : syracuseStep 362875 = 544313) B544313
theorem B428705 : Blo 187803 428705 := bstep (se 2 (by rfl) ⟨160764, by rfl⟩ : syracuseStep 428705 = 321529) B321529
theorem B428921 : Blo 187803 428921 := bstep (se 2 (by rfl) ⟨160845, by rfl⟩ : syracuseStep 428921 = 321691) B321691
theorem B429065 : Blo 187803 429065 := bstep (se 2 (by rfl) ⟨160899, by rfl⟩ : syracuseStep 429065 = 321799) B321799
theorem B429119 : Blo 187803 429119 := bstep (se 1 (by rfl) ⟨321839, by rfl⟩ : syracuseStep 429119 = 643679) B643679
theorem B953531 : Blo 187803 953531 := bstep (se 1 (by rfl) ⟨715148, by rfl⟩ : syracuseStep 953531 = 1430297) B1430297
theorem B364007 : Blo 187803 364007 := bstep (se 1 (by rfl) ⟨273005, by rfl⟩ : syracuseStep 364007 = 546011) B546011
theorem B429947 : Blo 187803 429947 := bstep (se 1 (by rfl) ⟨322460, by rfl⟩ : syracuseStep 429947 = 644921) B644921
theorem B430055 : Blo 187803 430055 := bstep (se 1 (by rfl) ⟨322541, by rfl⟩ : syracuseStep 430055 = 645083) B645083
theorem B430235 : Blo 187803 430235 := bstep (se 1 (by rfl) ⟨322676, by rfl⟩ : syracuseStep 430235 = 645353) B645353
theorem B823457 : Blo 187803 823457 := bstep (se 2 (by rfl) ⟨308796, by rfl⟩ : syracuseStep 823457 = 617593) B617593
theorem B6295805 : Blo 187803 6295805 := bstep (se 3 (by rfl) ⟨1180463, by rfl⟩ : syracuseStep 6295805 = 2360927) B2360927
theorem B430433 : Blo 187803 430433 := bstep (se 2 (by rfl) ⟨161412, by rfl⟩ : syracuseStep 430433 = 322825) B322825
theorem B5640623 : Blo 187803 5640623 := bstep (se 1 (by rfl) ⟨4230467, by rfl⟩ : syracuseStep 5640623 = 8460935) B8460935
theorem B430523 : Blo 187803 430523 := bstep (se 1 (by rfl) ⟨322892, by rfl⟩ : syracuseStep 430523 = 645785) B645785
theorem B1840229 : Blo 187803 1840229 := bstep (se 4 (by rfl) ⟨172521, by rfl⟩ : syracuseStep 1840229 = 345043) B345043
theorem B726205 : Blo 187803 726205 := bstep (se 3 (by rfl) ⟨136163, by rfl⟩ : syracuseStep 726205 = 272327) B272327
theorem B15832493 : Blo 187803 15832493 := bstep (se 3 (by rfl) ⟨2968592, by rfl⟩ : syracuseStep 15832493 = 5937185) B5937185
theorem B824833 : Blo 187803 824833 := bstep (se 2 (by rfl) ⟨309312, by rfl⟩ : syracuseStep 824833 = 618625) B618625
theorem B1218401 : Blo 187803 1218401 := bstep (se 2 (by rfl) ⟨456900, by rfl⟩ : syracuseStep 1218401 = 913801) B913801
theorem B727177 : Blo 187803 727177 := bstep (se 2 (by rfl) ⟨272691, by rfl⟩ : syracuseStep 727177 = 545383) B545383
theorem B1612061 : Blo 187803 1612061 := bstep (se 3 (by rfl) ⟨302261, by rfl⟩ : syracuseStep 1612061 = 604523) B604523
theorem B6527375 : Blo 187803 6527375 := bstep (se 1 (by rfl) ⟨4895531, by rfl⟩ : syracuseStep 6527375 = 9791063) B9791063
theorem B1547099 : Blo 187803 1547099 := bstep (se 1 (by rfl) ⟨1160324, by rfl⟩ : syracuseStep 1547099 = 2320649) B2320649
theorem B728135 : Blo 187803 728135 := bstep (se 1 (by rfl) ⟨546101, by rfl⟩ : syracuseStep 728135 = 1092203) B1092203
theorem B3349991 : Blo 187803 3349991 := bstep (se 1 (by rfl) ⟨2512493, by rfl⟩ : syracuseStep 3349991 = 5024987) B5024987
theorem B1547849 : Blo 187803 1547849 := bstep (se 2 (by rfl) ⟨580443, by rfl⟩ : syracuseStep 1547849 = 1160887) B1160887
theorem B2072137 : Blo 187803 2072137 := bstep (se 2 (by rfl) ⟨777051, by rfl⟩ : syracuseStep 2072137 = 1554103) B1554103
theorem B401375 : Blo 187803 401375 := bstep (se 1 (by rfl) ⟨301031, by rfl⟩ : syracuseStep 401375 = 602063) B602063
theorem B1811915 : Blo 187803 1811915 := bstep (se 1 (by rfl) ⟨1358936, by rfl⟩ : syracuseStep 1811915 = 2717873) B2717873
theorem B3614291 : Blo 187803 3614291 := bstep (se 1 (by rfl) ⟨2710718, by rfl⟩ : syracuseStep 3614291 = 5421437) B5421437
theorem B829739 : Blo 187803 829739 := bstep (se 1 (by rfl) ⟨622304, by rfl⟩ : syracuseStep 829739 = 1244609) B1244609
theorem B240175 : Blo 187803 240175 := bstep (se 1 (by rfl) ⟨180131, by rfl⟩ : syracuseStep 240175 = 360263) B360263
theorem B634121 : Blo 187803 634121 := bstep (se 2 (by rfl) ⟨237795, by rfl⟩ : syracuseStep 634121 = 475591) B475591
theorem B1813913 : Blo 187803 1813913 := bstep (se 2 (by rfl) ⟨680217, by rfl⟩ : syracuseStep 1813913 = 1360435) B1360435
theorem B601499 : Blo 187803 601499 := bstep (se 1 (by rfl) ⟨451124, by rfl⟩ : syracuseStep 601499 = 902249) B902249
theorem B241051 : Blo 187803 241051 := bstep (se 1 (by rfl) ⟨180788, by rfl⟩ : syracuseStep 241051 = 361577) B361577
theorem B306587 : Blo 187803 306587 := bstep (se 1 (by rfl) ⟨229940, by rfl⟩ : syracuseStep 306587 = 459881) B459881
theorem B339527 : Blo 187803 339527 := bstep (se 1 (by rfl) ⟨254645, by rfl⟩ : syracuseStep 339527 = 509291) B509291
theorem B1060547 : Blo 187803 1060547 := bstep (se 1 (by rfl) ⟨795410, by rfl⟩ : syracuseStep 1060547 = 1590821) B1590821
theorem B4894505 : Blo 187803 4894505 := bstep (se 2 (by rfl) ⟨1835439, by rfl⟩ : syracuseStep 4894505 = 3670879) B3670879
theorem B241471 : Blo 187803 241471 := bstep (se 1 (by rfl) ⟨181103, by rfl⟩ : syracuseStep 241471 = 362207) B362207
theorem B962441 : Blo 187803 962441 := bstep (se 2 (by rfl) ⟨360915, by rfl⟩ : syracuseStep 962441 = 721831) B721831
theorem B405587 : Blo 187803 405587 := bstep (se 1 (by rfl) ⟨304190, by rfl⟩ : syracuseStep 405587 = 608381) B608381
theorem B536807 : Blo 187803 536807 := bstep (se 1 (by rfl) ⟨402605, by rfl⟩ : syracuseStep 536807 = 805211) B805211
theorem B242023 : Blo 187803 242023 := bstep (se 1 (by rfl) ⟨181517, by rfl⟩ : syracuseStep 242023 = 363035) B363035
theorem B1225115 : Blo 187803 1225115 := bstep (se 1 (by rfl) ⟨918836, by rfl⟩ : syracuseStep 1225115 = 1837673) B1837673
theorem B438841 : Blo 187803 438841 := bstep (se 2 (by rfl) ⟨164565, by rfl⟩ : syracuseStep 438841 = 329131) B329131
theorem B210407 : Blo 187803 210407 := bstep (se 1 (by rfl) ⟨157805, by rfl⟩ : syracuseStep 210407 = 315611) B315611
theorem B1455731 : Blo 187803 1455731 := bstep (se 1 (by rfl) ⟨1091798, by rfl⟩ : syracuseStep 1455731 = 2183597) B2183597
theorem B636713 : Blo 187803 636713 := bstep (se 2 (by rfl) ⟨238767, by rfl⟩ : syracuseStep 636713 = 477535) B477535
theorem B539369 : Blo 187803 539369 := bstep (se 2 (by rfl) ⟨202263, by rfl⟩ : syracuseStep 539369 = 404527) B404527
theorem B342761 : Blo 187803 342761 := bstep (se 2 (by rfl) ⟨128535, by rfl⟩ : syracuseStep 342761 = 257071) B257071
theorem B211783 : Blo 187803 211783 := bstep (se 1 (by rfl) ⟨158837, by rfl⟩ : syracuseStep 211783 = 317675) B317675
theorem B2178251 : Blo 187803 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B1621235 : Blo 187803 1621235 := bstep (se 1 (by rfl) ⟨1215926, by rfl⟩ : syracuseStep 1621235 = 2431853) B2431853
theorem B212431 : Blo 187803 212431 := bstep (se 1 (by rfl) ⟨159323, by rfl⟩ : syracuseStep 212431 = 318647) B318647
theorem B212647 : Blo 187803 212647 := bstep (se 1 (by rfl) ⟨159485, by rfl⟩ : syracuseStep 212647 = 318971) B318971
theorem B409465 : Blo 187803 409465 := bstep (se 2 (by rfl) ⟨153549, by rfl⟩ : syracuseStep 409465 = 307099) B307099
theorem B212935 : Blo 187803 212935 := bstep (se 1 (by rfl) ⟨159701, by rfl⟩ : syracuseStep 212935 = 319403) B319403
theorem B4571225 : Blo 187803 4571225 := bstep (se 2 (by rfl) ⟨1714209, by rfl⟩ : syracuseStep 4571225 = 3428419) B3428419
theorem B1622207 : Blo 187803 1622207 := bstep (se 1 (by rfl) ⟨1216655, by rfl⟩ : syracuseStep 1622207 = 2433311) B2433311
theorem B213295 : Blo 187803 213295 := bstep (se 1 (by rfl) ⟨159971, by rfl⟩ : syracuseStep 213295 = 319943) B319943
theorem B541181 : Blo 187803 541181 := bstep (se 3 (by rfl) ⟨101471, by rfl⟩ : syracuseStep 541181 = 202943) B202943
theorem B6505231 : Blo 187803 6505231 := bstep (se 1 (by rfl) ⟨4878923, by rfl⟩ : syracuseStep 6505231 = 9757847) B9757847
theorem B967735 : Blo 187803 967735 := bstep (se 1 (by rfl) ⟨725801, by rfl⟩ : syracuseStep 967735 = 1451603) B1451603
theorem B476351 : Blo 187803 476351 := bstep (se 1 (by rfl) ⟨357263, by rfl⟩ : syracuseStep 476351 = 714527) B714527
theorem B902497 : Blo 187803 902497 := bstep (se 2 (by rfl) ⟨338436, by rfl⟩ : syracuseStep 902497 = 676873) B676873
theorem B640439 : Blo 187803 640439 := bstep (se 1 (by rfl) ⟨480329, by rfl⟩ : syracuseStep 640439 = 960659) B960659
theorem B214555 : Blo 187803 214555 := bstep (se 1 (by rfl) ⟨160916, by rfl⟩ : syracuseStep 214555 = 321833) B321833
theorem B477049 : Blo 187803 477049 := bstep (se 2 (by rfl) ⟨178893, by rfl⟩ : syracuseStep 477049 = 357787) B357787
theorem B542695 : Blo 187803 542695 := bstep (se 1 (by rfl) ⟨407021, by rfl⟩ : syracuseStep 542695 = 814043) B814043
theorem B575687 : Blo 187803 575687 := bstep (se 1 (by rfl) ⟨431765, by rfl⟩ : syracuseStep 575687 = 863531) B863531
theorem B969083 : Blo 187803 969083 := bstep (se 1 (by rfl) ⟨726812, by rfl⟩ : syracuseStep 969083 = 1453625) B1453625
theorem B215599 : Blo 187803 215599 := bstep (se 1 (by rfl) ⟨161699, by rfl⟩ : syracuseStep 215599 = 323399) B323399
theorem B576161 : Blo 187803 576161 := bstep (se 2 (by rfl) ⟨216060, by rfl⟩ : syracuseStep 576161 = 432121) B432121
theorem B2050859 : Blo 187803 2050859 := bstep (se 1 (by rfl) ⟨1538144, by rfl⟩ : syracuseStep 2050859 = 3076289) B3076289
theorem B641897 : Blo 187803 641897 := bstep (se 2 (by rfl) ⟨240711, by rfl⟩ : syracuseStep 641897 = 481423) B481423
theorem B1428353 : Blo 187803 1428353 := bstep (se 2 (by rfl) ⟨535632, by rfl⟩ : syracuseStep 1428353 = 1071265) B1071265
theorem B4115387 : Blo 187803 4115387 := bstep (se 1 (by rfl) ⟨3086540, by rfl⟩ : syracuseStep 4115387 = 6173081) B6173081
theorem B805895 : Blo 187803 805895 := bstep (se 1 (by rfl) ⟨604421, by rfl⟩ : syracuseStep 805895 = 1208843) B1208843
theorem B1461395 : Blo 187803 1461395 := bstep (se 1 (by rfl) ⟨1096046, by rfl⟩ : syracuseStep 1461395 = 2192093) B2192093
theorem B1035767 : Blo 187803 1035767 := bstep (se 1 (by rfl) ⟨776825, by rfl⟩ : syracuseStep 1035767 = 1553651) B1553651
theorem B1363493 : Blo 187803 1363493 := bstep (se 4 (by rfl) ⟨127827, by rfl⟩ : syracuseStep 1363493 = 255655) B255655
theorem B282215 : Blo 187803 282215 := bstep (se 1 (by rfl) ⟨211661, by rfl⟩ : syracuseStep 282215 = 423323) B423323
theorem B544427 : Blo 187803 544427 := bstep (se 1 (by rfl) ⟨408320, by rfl⟩ : syracuseStep 544427 = 816641) B816641
theorem B1429325 : Blo 187803 1429325 := bstep (se 3 (by rfl) ⟨267998, by rfl⟩ : syracuseStep 1429325 = 535997) B535997
theorem B643031 : Blo 187803 643031 := bstep (se 1 (by rfl) ⟨482273, by rfl⟩ : syracuseStep 643031 = 964547) B964547
theorem B282599 : Blo 187803 282599 := bstep (se 1 (by rfl) ⟨211949, by rfl⟩ : syracuseStep 282599 = 423899) B423899
theorem B282719 : Blo 187803 282719 := bstep (se 1 (by rfl) ⟨212039, by rfl⟩ : syracuseStep 282719 = 424079) B424079
theorem B282731 : Blo 187803 282731 := bstep (se 1 (by rfl) ⟨212048, by rfl⟩ : syracuseStep 282731 = 424097) B424097
theorem B282779 : Blo 187803 282779 := bstep (se 1 (by rfl) ⟨212084, by rfl⟩ : syracuseStep 282779 = 424169) B424169
theorem B643247 : Blo 187803 643247 := bstep (se 1 (by rfl) ⟨482435, by rfl⟩ : syracuseStep 643247 = 964871) B964871
theorem B545555 : Blo 187803 545555 := bstep (se 1 (by rfl) ⟨409166, by rfl⟩ : syracuseStep 545555 = 818333) B818333
theorem B2184083 : Blo 187803 2184083 := bstep (se 1 (by rfl) ⟨1638062, by rfl⟩ : syracuseStep 2184083 = 3276125) B3276125
theorem B7361441 : Blo 187803 7361441 := bstep (se 2 (by rfl) ⟨2760540, by rfl⟩ : syracuseStep 7361441 = 5521081) B5521081
theorem B5428133 : Blo 187803 5428133 := bstep (se 4 (by rfl) ⟨508887, by rfl⟩ : syracuseStep 5428133 = 1017775) B1017775
theorem B283631 : Blo 187803 283631 := bstep (se 1 (by rfl) ⟨212723, by rfl⟩ : syracuseStep 283631 = 425447) B425447
theorem B644219 : Blo 187803 644219 := bstep (se 1 (by rfl) ⟨483164, by rfl⟩ : syracuseStep 644219 = 966329) B966329
theorem B284015 : Blo 187803 284015 := bstep (se 1 (by rfl) ⟨213011, by rfl⟩ : syracuseStep 284015 = 426023) B426023
theorem B644489 : Blo 187803 644489 := bstep (se 2 (by rfl) ⟨241683, by rfl⟩ : syracuseStep 644489 = 483367) B483367
theorem B284135 : Blo 187803 284135 := bstep (se 1 (by rfl) ⟨213101, by rfl⟩ : syracuseStep 284135 = 426203) B426203
theorem B2152007 : Blo 187803 2152007 := bstep (se 1 (by rfl) ⟨1614005, by rfl⟩ : syracuseStep 2152007 = 3228011) B3228011
theorem B284297 : Blo 187803 284297 := bstep (se 2 (by rfl) ⟨106611, by rfl⟩ : syracuseStep 284297 = 213223) B213223
theorem B284315 : Blo 187803 284315 := bstep (se 1 (by rfl) ⟨213236, by rfl⟩ : syracuseStep 284315 = 426473) B426473
theorem B2053799 : Blo 187803 2053799 := bstep (se 1 (by rfl) ⟨1540349, by rfl⟩ : syracuseStep 2053799 = 3080699) B3080699
theorem B284507 : Blo 187803 284507 := bstep (se 1 (by rfl) ⟨213380, by rfl⟩ : syracuseStep 284507 = 426761) B426761
theorem B1431755 : Blo 187803 1431755 := bstep (se 1 (by rfl) ⟨1073816, by rfl⟩ : syracuseStep 1431755 = 2147633) B2147633
theorem B284891 : Blo 187803 284891 := bstep (se 1 (by rfl) ⟨213668, by rfl⟩ : syracuseStep 284891 = 427337) B427337
theorem B383329 : Blo 187803 383329 := bstep (se 2 (by rfl) ⟨143748, by rfl⟩ : syracuseStep 383329 = 287497) B287497
theorem B481697 : Blo 187803 481697 := bstep (se 2 (by rfl) ⟨180636, by rfl⟩ : syracuseStep 481697 = 361273) B361273
theorem B285161 : Blo 187803 285161 := bstep (se 2 (by rfl) ⟨106935, by rfl⟩ : syracuseStep 285161 = 213871) B213871
theorem B4413971 : Blo 187803 4413971 := bstep (se 1 (by rfl) ⟨3310478, by rfl⟩ : syracuseStep 4413971 = 6620957) B6620957
theorem B1956403 : Blo 187803 1956403 := bstep (se 1 (by rfl) ⟨1467302, by rfl⟩ : syracuseStep 1956403 = 2934605) B2934605
theorem B908111 : Blo 187803 908111 := bstep (se 1 (by rfl) ⟨681083, by rfl⟩ : syracuseStep 908111 = 1362167) B1362167
theorem B285551 : Blo 187803 285551 := bstep (se 1 (by rfl) ⟨214163, by rfl⟩ : syracuseStep 285551 = 428327) B428327
theorem B285563 : Blo 187803 285563 := bstep (se 1 (by rfl) ⟨214172, by rfl⟩ : syracuseStep 285563 = 428345) B428345
theorem B810269 : Blo 187803 810269 := bstep (se 3 (by rfl) ⟨151925, by rfl⟩ : syracuseStep 810269 = 303851) B303851
theorem B1957225 : Blo 187803 1957225 := bstep (se 2 (by rfl) ⟨733959, by rfl⟩ : syracuseStep 1957225 = 1467919) B1467919
theorem B187855 : Blo 187803 187855 := bstep (se 1 (by rfl) ⟨140891, by rfl⟩ : syracuseStep 187855 = 281783) B281783
theorem B188015 : Blo 187803 188015 := bstep (se 1 (by rfl) ⟨141011, by rfl⟩ : syracuseStep 188015 = 282023) B282023
theorem B188071 : Blo 187803 188071 := bstep (se 1 (by rfl) ⟨141053, by rfl⟩ : syracuseStep 188071 = 282107) B282107
theorem B286427 : Blo 187803 286427 := bstep (se 1 (by rfl) ⟨214820, by rfl⟩ : syracuseStep 286427 = 429641) B429641
theorem B188135 : Blo 187803 188135 := bstep (se 1 (by rfl) ⟨141101, by rfl⟩ : syracuseStep 188135 = 282203) B282203
theorem B3432223 : Blo 187803 3432223 := bstep (se 1 (by rfl) ⟨2574167, by rfl⟩ : syracuseStep 3432223 = 5148335) B5148335
theorem B188191 : Blo 187803 188191 := bstep (se 1 (by rfl) ⟨141143, by rfl⟩ : syracuseStep 188191 = 282287) B282287
theorem B188271 : Blo 187803 188271 := bstep (se 1 (by rfl) ⟨141203, by rfl⟩ : syracuseStep 188271 = 282407) B282407
theorem B188327 : Blo 187803 188327 := bstep (se 1 (by rfl) ⟨141245, by rfl⟩ : syracuseStep 188327 = 282491) B282491
theorem B286697 : Blo 187803 286697 := bstep (se 2 (by rfl) ⟨107511, by rfl⟩ : syracuseStep 286697 = 215023) B215023
theorem B28336139 : Blo 187803 28336139 := bstep (se 1 (by rfl) ⟨21252104, by rfl⟩ : syracuseStep 28336139 = 42504209) B42504209
theorem B188607 : Blo 187803 188607 := bstep (se 1 (by rfl) ⟨141455, by rfl⟩ : syracuseStep 188607 = 282911) B282911
theorem B188623 : Blo 187803 188623 := bstep (se 1 (by rfl) ⟨141467, by rfl⟩ : syracuseStep 188623 = 282935) B282935
theorem B188671 : Blo 187803 188671 := bstep (se 1 (by rfl) ⟨141503, by rfl⟩ : syracuseStep 188671 = 283007) B283007
theorem B188719 : Blo 187803 188719 := bstep (se 1 (by rfl) ⟨141539, by rfl⟩ : syracuseStep 188719 = 283079) B283079
theorem B319801 : Blo 187803 319801 := bstep (se 2 (by rfl) ⟨119925, by rfl⟩ : syracuseStep 319801 = 239851) B239851
theorem B483641 : Blo 187803 483641 := bstep (se 2 (by rfl) ⟨181365, by rfl⟩ : syracuseStep 483641 = 362731) B362731
theorem B909625 : Blo 187803 909625 := bstep (se 2 (by rfl) ⟨341109, by rfl⟩ : syracuseStep 909625 = 682219) B682219
theorem B188955 : Blo 187803 188955 := bstep (se 1 (by rfl) ⟨141716, by rfl⟩ : syracuseStep 188955 = 283433) B283433
theorem B188959 : Blo 187803 188959 := bstep (se 1 (by rfl) ⟨141719, by rfl⟩ : syracuseStep 188959 = 283439) B283439
theorem B1434185 : Blo 187803 1434185 := bstep (se 2 (by rfl) ⟨537819, by rfl⟩ : syracuseStep 1434185 = 1075639) B1075639
theorem B189039 : Blo 187803 189039 := bstep (se 1 (by rfl) ⟨141779, by rfl⟩ : syracuseStep 189039 = 283559) B283559
theorem B189095 : Blo 187803 189095 := bstep (se 1 (by rfl) ⟨141821, by rfl⟩ : syracuseStep 189095 = 283643) B283643
theorem B287399 : Blo 187803 287399 := bstep (se 1 (by rfl) ⟨215549, by rfl⟩ : syracuseStep 287399 = 431099) B431099
theorem B189135 : Blo 187803 189135 := bstep (se 1 (by rfl) ⟨141851, by rfl⟩ : syracuseStep 189135 = 283703) B283703
theorem B1630955 : Blo 187803 1630955 := bstep (se 1 (by rfl) ⟨1223216, by rfl⟩ : syracuseStep 1630955 = 2446433) B2446433
theorem B189215 : Blo 187803 189215 := bstep (se 1 (by rfl) ⟨141911, by rfl⟩ : syracuseStep 189215 = 283823) B283823
theorem B320287 : Blo 187803 320287 := bstep (se 1 (by rfl) ⟨240215, by rfl⟩ : syracuseStep 320287 = 480431) B480431
theorem B484127 : Blo 187803 484127 := bstep (se 1 (by rfl) ⟨363095, by rfl⟩ : syracuseStep 484127 = 726191) B726191
theorem B287519 : Blo 187803 287519 := bstep (se 1 (by rfl) ⟨215639, by rfl⟩ : syracuseStep 287519 = 431279) B431279
theorem B287543 : Blo 187803 287543 := bstep (se 1 (by rfl) ⟨215657, by rfl⟩ : syracuseStep 287543 = 431315) B431315
theorem B189487 : Blo 187803 189487 := bstep (se 1 (by rfl) ⟨142115, by rfl⟩ : syracuseStep 189487 = 284231) B284231
theorem B189551 : Blo 187803 189551 := bstep (se 1 (by rfl) ⟨142163, by rfl⟩ : syracuseStep 189551 = 284327) B284327
theorem B189607 : Blo 187803 189607 := bstep (se 1 (by rfl) ⟨142205, by rfl⟩ : syracuseStep 189607 = 284411) B284411
theorem B189631 : Blo 187803 189631 := bstep (se 1 (by rfl) ⟨142223, by rfl⟩ : syracuseStep 189631 = 284447) B284447
theorem B196338887 : Blo 187803 196338887 := bstep (se 1 (by rfl) ⟨147254165, by rfl⟩ : syracuseStep 196338887 = 294508331) B294508331
theorem B189663 : Blo 187803 189663 := bstep (se 1 (by rfl) ⟨142247, by rfl⟩ : syracuseStep 189663 = 284495) B284495
theorem B189743 : Blo 187803 189743 := bstep (se 1 (by rfl) ⟨142307, by rfl⟩ : syracuseStep 189743 = 284615) B284615
theorem B714041 : Blo 187803 714041 := bstep (se 2 (by rfl) ⟨267765, by rfl⟩ : syracuseStep 714041 = 535531) B535531
theorem B452087 : Blo 187803 452087 := bstep (se 1 (by rfl) ⟨339065, by rfl⟩ : syracuseStep 452087 = 678131) B678131
theorem B189979 : Blo 187803 189979 := bstep (se 1 (by rfl) ⟨142484, by rfl⟩ : syracuseStep 189979 = 284969) B284969
theorem B189983 : Blo 187803 189983 := bstep (se 1 (by rfl) ⟨142487, by rfl⟩ : syracuseStep 189983 = 284975) B284975
theorem B321097 : Blo 187803 321097 := bstep (se 2 (by rfl) ⟨120411, by rfl⟩ : syracuseStep 321097 = 240823) B240823
theorem B190143 : Blo 187803 190143 := bstep (se 1 (by rfl) ⟨142607, by rfl⟩ : syracuseStep 190143 = 285215) B285215
theorem B3860261 : Blo 187803 3860261 := bstep (se 4 (by rfl) ⟨361899, by rfl⟩ : syracuseStep 3860261 = 723799) B723799
theorem B190399 : Blo 187803 190399 := bstep (se 1 (by rfl) ⟨142799, by rfl⟩ : syracuseStep 190399 = 285599) B285599
theorem B485311 : Blo 187803 485311 := bstep (se 1 (by rfl) ⟨363983, by rfl⟩ : syracuseStep 485311 = 727967) B727967
theorem B190431 : Blo 187803 190431 := bstep (se 1 (by rfl) ⟨142823, by rfl⟩ : syracuseStep 190431 = 285647) B285647
theorem B190491 : Blo 187803 190491 := bstep (se 1 (by rfl) ⟨142868, by rfl⟩ : syracuseStep 190491 = 285737) B285737
theorem B321563 : Blo 187803 321563 := bstep (se 1 (by rfl) ⟨241172, by rfl⟩ : syracuseStep 321563 = 482345) B482345
theorem B190495 : Blo 187803 190495 := bstep (se 1 (by rfl) ⟨142871, by rfl⟩ : syracuseStep 190495 = 285743) B285743
theorem B190511 : Blo 187803 190511 := bstep (se 1 (by rfl) ⟨142883, by rfl⟩ : syracuseStep 190511 = 285767) B285767
theorem B321583 : Blo 187803 321583 := bstep (se 1 (by rfl) ⟨241187, by rfl⟩ : syracuseStep 321583 = 482375) B482375
theorem B485473 : Blo 187803 485473 := bstep (se 2 (by rfl) ⟨182052, by rfl⟩ : syracuseStep 485473 = 364105) B364105
theorem B288889 : Blo 187803 288889 := bstep (se 2 (by rfl) ⟨108333, by rfl⟩ : syracuseStep 288889 = 216667) B216667
theorem B911569 : Blo 187803 911569 := bstep (se 2 (by rfl) ⟨341838, by rfl⟩ : syracuseStep 911569 = 683677) B683677
theorem B190687 : Blo 187803 190687 := bstep (se 1 (by rfl) ⟨143015, by rfl⟩ : syracuseStep 190687 = 286031) B286031
theorem B190747 : Blo 187803 190747 := bstep (se 1 (by rfl) ⟨143060, by rfl⟩ : syracuseStep 190747 = 286121) B286121
theorem B190847 : Blo 187803 190847 := bstep (se 1 (by rfl) ⟨143135, by rfl⟩ : syracuseStep 190847 = 286271) B286271
theorem B191023 : Blo 187803 191023 := bstep (se 1 (by rfl) ⟨143267, by rfl⟩ : syracuseStep 191023 = 286535) B286535
theorem B354863 : Blo 187803 354863 := bstep (se 1 (by rfl) ⟨266147, by rfl⟩ : syracuseStep 354863 = 532295) B532295
theorem B191079 : Blo 187803 191079 := bstep (se 1 (by rfl) ⟨143309, by rfl⟩ : syracuseStep 191079 = 286619) B286619
theorem B191455 : Blo 187803 191455 := bstep (se 1 (by rfl) ⟨143591, by rfl⟩ : syracuseStep 191455 = 287183) B287183
theorem B191483 : Blo 187803 191483 := bstep (se 1 (by rfl) ⟨143612, by rfl⟩ : syracuseStep 191483 = 287225) B287225
theorem B191551 : Blo 187803 191551 := bstep (se 1 (by rfl) ⟨143663, by rfl⟩ : syracuseStep 191551 = 287327) B287327
theorem B715999 : Blo 187803 715999 := bstep (se 1 (by rfl) ⟨536999, by rfl⟩ : syracuseStep 715999 = 1073999) B1073999
theorem B3862225 : Blo 187803 3862225 := bstep (se 2 (by rfl) ⟨1448334, by rfl⟩ : syracuseStep 3862225 = 2896669) B2896669
theorem B14282477 : Blo 187803 14282477 := bstep (se 3 (by rfl) ⟨2677964, by rfl⟩ : syracuseStep 14282477 = 5355929) B5355929
theorem B454729 : Blo 187803 454729 := bstep (se 2 (by rfl) ⟨170523, by rfl⟩ : syracuseStep 454729 = 341047) B341047
theorem B356815 : Blo 187803 356815 := bstep (se 1 (by rfl) ⟨267611, by rfl⟩ : syracuseStep 356815 = 535223) B535223
theorem B1864225 : Blo 187803 1864225 := bstep (se 2 (by rfl) ⟨699084, by rfl⟩ : syracuseStep 1864225 = 1398169) B1398169
theorem B1438559 : Blo 187803 1438559 := bstep (se 1 (by rfl) ⟨1078919, by rfl⟩ : syracuseStep 1438559 = 2157839) B2157839
theorem B423017 : Blo 187803 423017 := bstep (se 2 (by rfl) ⟨158631, by rfl⟩ : syracuseStep 423017 = 317263) B317263
theorem B718247 : Blo 187803 718247 := bstep (se 1 (by rfl) ⟨538685, by rfl⟩ : syracuseStep 718247 = 1077371) B1077371
theorem B1734061 : Blo 187803 1734061 := bstep (se 3 (by rfl) ⟨325136, by rfl⟩ : syracuseStep 1734061 = 650273) B650273
theorem B423647 : Blo 187803 423647 := bstep (se 1 (by rfl) ⟨317735, by rfl⟩ : syracuseStep 423647 = 635471) B635471
theorem B358121 : Blo 187803 358121 := bstep (se 2 (by rfl) ⟨134295, by rfl⟩ : syracuseStep 358121 = 268591) B268591
theorem B424007 : Blo 187803 424007 := bstep (se 1 (by rfl) ⟨318005, by rfl⟩ : syracuseStep 424007 = 636011) B636011
theorem B817361 : Blo 187803 817361 := bstep (se 2 (by rfl) ⟨306510, by rfl⟩ : syracuseStep 817361 = 613021) B613021
theorem B784937 : Blo 187803 784937 := bstep (se 2 (by rfl) ⟨294351, by rfl⟩ : syracuseStep 784937 = 588703) B588703
theorem B719401 : Blo 187803 719401 := bstep (se 2 (by rfl) ⟨269775, by rfl⟩ : syracuseStep 719401 = 539551) B539551
theorem B1636969 : Blo 187803 1636969 := bstep (se 2 (by rfl) ⟨613863, by rfl⟩ : syracuseStep 1636969 = 1227727) B1227727
theorem B424673 : Blo 187803 424673 := bstep (se 2 (by rfl) ⟨159252, by rfl⟩ : syracuseStep 424673 = 318505) B318505
theorem B359147 : Blo 187803 359147 := bstep (se 1 (by rfl) ⟨269360, by rfl⟩ : syracuseStep 359147 = 538721) B538721
theorem B424871 : Blo 187803 424871 := bstep (se 1 (by rfl) ⟨318653, by rfl⟩ : syracuseStep 424871 = 637307) B637307
theorem B425051 : Blo 187803 425051 := bstep (se 1 (by rfl) ⟨318788, by rfl⟩ : syracuseStep 425051 = 637577) B637577
theorem B720359 : Blo 187803 720359 := bstep (se 1 (by rfl) ⟨540269, by rfl⟩ : syracuseStep 720359 = 1080539) B1080539
theorem B2424653 : Blo 187803 2424653 := bstep (se 3 (by rfl) ⟨454622, by rfl⟩ : syracuseStep 2424653 = 909245) B909245
theorem B425807 : Blo 187803 425807 := bstep (se 1 (by rfl) ⟨319355, by rfl⟩ : syracuseStep 425807 = 638711) B638711
theorem B3047483 : Blo 187803 3047483 := bstep (se 1 (by rfl) ⟨2285612, by rfl⟩ : syracuseStep 3047483 = 4571225) B4571225
theorem B1081471 : Blo 187803 1081471 := bstep (se 1 (by rfl) ⟨811103, by rfl⟩ : syracuseStep 1081471 = 1622207) B1622207
theorem B2752703 : Blo 187803 2752703 := bstep (se 1 (by rfl) ⟨2064527, by rfl⟩ : syracuseStep 2752703 = 4129055) B4129055
theorem B360787 : Blo 187803 360787 := bstep (se 1 (by rfl) ⟨270590, by rfl⟩ : syracuseStep 360787 = 541181) B541181
theorem B426401 : Blo 187803 426401 := bstep (se 2 (by rfl) ⟨159900, by rfl⟩ : syracuseStep 426401 = 319801) B319801
theorem B1212833 : Blo 187803 1212833 := bstep (se 2 (by rfl) ⟨454812, by rfl⟩ : syracuseStep 1212833 = 909625) B909625
theorem B2195885 : Blo 187803 2195885 := bstep (se 3 (by rfl) ⟨411728, by rfl⟩ : syracuseStep 2195885 = 823457) B823457
theorem B918335 : Blo 187803 918335 := bstep (se 1 (by rfl) ⟨688751, by rfl⟩ : syracuseStep 918335 = 1377503) B1377503
theorem B426959 : Blo 187803 426959 := bstep (se 1 (by rfl) ⟨320219, by rfl⟩ : syracuseStep 426959 = 640439) B640439
theorem B427049 : Blo 187803 427049 := bstep (se 2 (by rfl) ⟨160143, by rfl⟩ : syracuseStep 427049 = 320287) B320287
theorem B918643 : Blo 187803 918643 := bstep (se 1 (by rfl) ⟨688982, by rfl⟩ : syracuseStep 918643 = 1377965) B1377965
theorem B427931 : Blo 187803 427931 := bstep (se 1 (by rfl) ⟨320948, by rfl⟩ : syracuseStep 427931 = 641897) B641897
theorem B952235 : Blo 187803 952235 := bstep (se 1 (by rfl) ⟨714176, by rfl⟩ : syracuseStep 952235 = 1428353) B1428353
theorem B428129 : Blo 187803 428129 := bstep (se 2 (by rfl) ⟨160548, by rfl⟩ : syracuseStep 428129 = 321097) B321097
theorem B362951 : Blo 187803 362951 := bstep (se 1 (by rfl) ⟨272213, by rfl⟩ : syracuseStep 362951 = 544427) B544427
theorem B6162965 : Blo 187803 6162965 := bstep (se 6 (by rfl) ⟨144444, by rfl⟩ : syracuseStep 6162965 = 288889) B288889
theorem B952883 : Blo 187803 952883 := bstep (se 1 (by rfl) ⟨714662, by rfl⟩ : syracuseStep 952883 = 1429325) B1429325
theorem B723593 : Blo 187803 723593 := bstep (se 2 (by rfl) ⟨271347, by rfl⟩ : syracuseStep 723593 = 542695) B542695
theorem B428687 : Blo 187803 428687 := bstep (se 1 (by rfl) ⟨321515, by rfl⟩ : syracuseStep 428687 = 643031) B643031
theorem B428777 : Blo 187803 428777 := bstep (se 2 (by rfl) ⟨160791, by rfl⟩ : syracuseStep 428777 = 321583) B321583
theorem B428831 : Blo 187803 428831 := bstep (se 1 (by rfl) ⟨321623, by rfl⟩ : syracuseStep 428831 = 643247) B643247
theorem B4197203 : Blo 187803 4197203 := bstep (se 1 (by rfl) ⟨3147902, by rfl⟩ : syracuseStep 4197203 = 6295805) B6295805
theorem B1215425 : Blo 187803 1215425 := bstep (se 2 (by rfl) ⟨455784, by rfl⟩ : syracuseStep 1215425 = 911569) B911569
theorem B363703 : Blo 187803 363703 := bstep (se 1 (by rfl) ⟨272777, by rfl⟩ : syracuseStep 363703 = 545555) B545555
theorem B429479 : Blo 187803 429479 := bstep (se 1 (by rfl) ⟨322109, by rfl⟩ : syracuseStep 429479 = 644219) B644219
theorem B429659 : Blo 187803 429659 := bstep (se 1 (by rfl) ⟨322244, by rfl⟩ : syracuseStep 429659 = 644489) B644489
theorem B10554995 : Blo 187803 10554995 := bstep (se 1 (by rfl) ⟨7916246, by rfl⟩ : syracuseStep 10554995 = 15832493) B15832493
theorem B954503 : Blo 187803 954503 := bstep (se 1 (by rfl) ⟨715877, by rfl⟩ : syracuseStep 954503 = 1431755) B1431755
theorem B954665 : Blo 187803 954665 := bstep (se 2 (by rfl) ⟨357999, by rfl⟩ : syracuseStep 954665 = 715999) B715999
theorem B954989 : Blo 187803 954989 := bstep (se 3 (by rfl) ⟨179060, by rfl⟩ : syracuseStep 954989 = 358121) B358121
theorem B2233327 : Blo 187803 2233327 := bstep (se 1 (by rfl) ⟨1674995, by rfl⟩ : syracuseStep 2233327 = 3349991) B3349991
theorem B956123 : Blo 187803 956123 := bstep (se 1 (by rfl) ⟨717092, by rfl⟩ : syracuseStep 956123 = 1434185) B1434185
theorem B1087303 : Blo 187803 1087303 := bstep (se 1 (by rfl) ⟨815477, by rfl⟩ : syracuseStep 1087303 = 1630955) B1630955
theorem B301391 : Blo 187803 301391 := bstep (se 1 (by rfl) ⟨226043, by rfl⟩ : syracuseStep 301391 = 452087) B452087
theorem B236575 : Blo 187803 236575 := bstep (se 1 (by rfl) ⟨177431, by rfl⟩ : syracuseStep 236575 = 354863) B354863
theorem B204391 : Blo 187803 204391 := bstep (se 1 (by rfl) ⟨153293, by rfl⟩ : syracuseStep 204391 = 306587) B306587
theorem B270391 : Blo 187803 270391 := bstep (se 1 (by rfl) ⟨202793, by rfl⟩ : syracuseStep 270391 = 405587) B405587
theorem B959039 : Blo 187803 959039 := bstep (se 1 (by rfl) ⟨719279, by rfl⟩ : syracuseStep 959039 = 1438559) B1438559
theorem B959201 : Blo 187803 959201 := bstep (se 2 (by rfl) ⟨359700, by rfl⟩ : syracuseStep 959201 = 719401) B719401
theorem B2762045 : Blo 187803 2762045 := bstep (se 3 (by rfl) ⟨517883, by rfl⟩ : syracuseStep 2762045 = 1035767) B1035767
theorem B239431 : Blo 187803 239431 := bstep (se 1 (by rfl) ⟨179573, by rfl⟩ : syracuseStep 239431 = 359147) B359147
theorem B2828125 : Blo 187803 2828125 := bstep (se 3 (by rfl) ⟨530273, by rfl⟩ : syracuseStep 2828125 = 1060547) B1060547
theorem B2762849 : Blo 187803 2762849 := bstep (se 2 (by rfl) ⟨1036068, by rfl⟩ : syracuseStep 2762849 = 2072137) B2072137
theorem B1452167 : Blo 187803 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B1616435 : Blo 187803 1616435 := bstep (se 1 (by rfl) ⟨1212326, by rfl⟩ : syracuseStep 1616435 = 2424653) B2424653
theorem B634067 : Blo 187803 634067 := bstep (se 1 (by rfl) ⟨475550, by rfl⟩ : syracuseStep 634067 = 951101) B951101
theorem B241319 : Blo 187803 241319 := bstep (se 1 (by rfl) ⟨180989, by rfl⟩ : syracuseStep 241319 = 361979) B361979
theorem B1290313 : Blo 187803 1290313 := bstep (se 2 (by rfl) ⟨483867, by rfl⟩ : syracuseStep 1290313 = 967735) B967735
theorem B537263 : Blo 187803 537263 := bstep (se 1 (by rfl) ⟨402947, by rfl⟩ : syracuseStep 537263 = 805895) B805895
theorem B635687 : Blo 187803 635687 := bstep (se 1 (by rfl) ⟨476765, by rfl⟩ : syracuseStep 635687 = 953531) B953531
theorem B242671 : Blo 187803 242671 := bstep (se 1 (by rfl) ⟨182003, by rfl⟩ : syracuseStep 242671 = 364007) B364007
theorem B636065 : Blo 187803 636065 := bstep (se 2 (by rfl) ⟨238524, by rfl⟩ : syracuseStep 636065 = 477049) B477049
theorem B2340485 : Blo 187803 2340485 := bstep (se 4 (by rfl) ⟨219420, by rfl⟩ : syracuseStep 2340485 = 438841) B438841
theorem B1456055 : Blo 187803 1456055 := bstep (se 1 (by rfl) ⟨1092041, by rfl⟩ : syracuseStep 1456055 = 2184083) B2184083
theorem B3618755 : Blo 187803 3618755 := bstep (se 1 (by rfl) ⟨2714066, by rfl⟩ : syracuseStep 3618755 = 5428133) B5428133
theorem B1226819 : Blo 187803 1226819 := bstep (se 1 (by rfl) ⟨920114, by rfl⟩ : syracuseStep 1226819 = 1840229) B1840229
theorem B605407 : Blo 187803 605407 := bstep (se 1 (by rfl) ⟨454055, by rfl⟩ : syracuseStep 605407 = 908111) B908111
theorem B1031399 : Blo 187803 1031399 := bstep (se 1 (by rfl) ⟨773549, by rfl⟩ : syracuseStep 1031399 = 1547099) B1547099
theorem B540179 : Blo 187803 540179 := bstep (se 1 (by rfl) ⟨405134, by rfl⟩ : syracuseStep 540179 = 810269) B810269
theorem B1031899 : Blo 187803 1031899 := bstep (se 1 (by rfl) ⟨773924, by rfl⟩ : syracuseStep 1031899 = 1547849) B1547849
theorem B2244341 : Blo 187803 2244341 := bstep (se 5 (by rfl) ⟨105203, by rfl⟩ : syracuseStep 2244341 = 210407) B210407
theorem B18890759 : Blo 187803 18890759 := bstep (se 1 (by rfl) ⟨14168069, by rfl⟩ : syracuseStep 18890759 = 28336139) B28336139
theorem B606305 : Blo 187803 606305 := bstep (se 2 (by rfl) ⟨227364, by rfl⟩ : syracuseStep 606305 = 454729) B454729
theorem B475753 : Blo 187803 475753 := bstep (se 2 (by rfl) ⟨178407, by rfl⟩ : syracuseStep 475753 = 356815) B356815
theorem B130892591 : Blo 187803 130892591 := bstep (se 1 (by rfl) ⟨98169443, by rfl⟩ : syracuseStep 130892591 = 196338887) B196338887
theorem B476027 : Blo 187803 476027 := bstep (se 1 (by rfl) ⟨357020, by rfl⟩ : syracuseStep 476027 = 714041) B714041
theorem B2409527 : Blo 187803 2409527 := bstep (se 1 (by rfl) ⟨1807145, by rfl⟩ : syracuseStep 2409527 = 3614291) B3614291
theorem B2573507 : Blo 187803 2573507 := bstep (se 1 (by rfl) ⟨1930130, by rfl⟩ : syracuseStep 2573507 = 3860261) B3860261
theorem B214375 : Blo 187803 214375 := bstep (se 1 (by rfl) ⟨160781, by rfl⟩ : syracuseStep 214375 = 321563) B321563
theorem B968273 : Blo 187803 968273 := bstep (se 2 (by rfl) ⟨363102, by rfl⟩ : syracuseStep 968273 = 726205) B726205
theorem B2312081 : Blo 187803 2312081 := bstep (se 2 (by rfl) ⟨867030, by rfl⟩ : syracuseStep 2312081 = 1734061) B1734061
theorem B1099777 : Blo 187803 1099777 := bstep (se 2 (by rfl) ⟨412416, by rfl⟩ : syracuseStep 1099777 = 824833) B824833
theorem B3656117 : Blo 187803 3656117 := bstep (se 5 (by rfl) ⟨171380, by rfl⟩ : syracuseStep 3656117 = 342761) B342761
theorem B9521651 : Blo 187803 9521651 := bstep (se 1 (by rfl) ⟨7141238, by rfl⟩ : syracuseStep 9521651 = 14282477) B14282477
theorem B3263003 : Blo 187803 3263003 := bstep (se 1 (by rfl) ⟨2447252, by rfl⟩ : syracuseStep 3263003 = 4894505) B4894505
theorem B641627 : Blo 187803 641627 := bstep (se 1 (by rfl) ⟨481220, by rfl⟩ : syracuseStep 641627 = 962441) B962441
theorem B969569 : Blo 187803 969569 := bstep (se 2 (by rfl) ⟨363588, by rfl⟩ : syracuseStep 969569 = 727177) B727177
theorem B511105 : Blo 187803 511105 := bstep (se 2 (by rfl) ⟨191664, by rfl⟩ : syracuseStep 511105 = 383329) B383329
theorem B2608537 : Blo 187803 2608537 := bstep (se 2 (by rfl) ⟨978201, by rfl⟩ : syracuseStep 2608537 = 1956403) B1956403
theorem B282011 : Blo 187803 282011 := bstep (se 1 (by rfl) ⟨211508, by rfl⟩ : syracuseStep 282011 = 423017) B423017
theorem B2182625 : Blo 187803 2182625 := bstep (se 2 (by rfl) ⟨818484, by rfl⟩ : syracuseStep 2182625 = 1636969) B1636969
theorem B478831 : Blo 187803 478831 := bstep (se 1 (by rfl) ⟨359123, by rfl⟩ : syracuseStep 478831 = 718247) B718247
theorem B970487 : Blo 187803 970487 := bstep (se 1 (by rfl) ⟨727865, by rfl⟩ : syracuseStep 970487 = 1455731) B1455731
theorem B20598533 : Blo 187803 20598533 := bstep (se 4 (by rfl) ⟨1931112, by rfl⟩ : syracuseStep 20598533 = 3862225) B3862225
theorem B282377 : Blo 187803 282377 := bstep (se 2 (by rfl) ⟨105891, by rfl⟩ : syracuseStep 282377 = 211783) B211783
theorem B282431 : Blo 187803 282431 := bstep (se 1 (by rfl) ⟨211823, by rfl⟩ : syracuseStep 282431 = 423647) B423647
theorem B282671 : Blo 187803 282671 := bstep (se 1 (by rfl) ⟨212003, by rfl⟩ : syracuseStep 282671 = 424007) B424007
theorem B544907 : Blo 187803 544907 := bstep (se 1 (by rfl) ⟨408680, by rfl⟩ : syracuseStep 544907 = 817361) B817361
theorem B2609633 : Blo 187803 2609633 := bstep (se 2 (by rfl) ⟨978612, by rfl⟩ : syracuseStep 2609633 = 1957225) B1957225
theorem B283115 : Blo 187803 283115 := bstep (se 1 (by rfl) ⟨212336, by rfl⟩ : syracuseStep 283115 = 424673) B424673
theorem B283241 : Blo 187803 283241 := bstep (se 2 (by rfl) ⟨106215, by rfl⟩ : syracuseStep 283241 = 212431) B212431
theorem B283247 : Blo 187803 283247 := bstep (se 1 (by rfl) ⟨212435, by rfl⟩ : syracuseStep 283247 = 424871) B424871
theorem B283367 : Blo 187803 283367 := bstep (se 1 (by rfl) ⟨212525, by rfl⟩ : syracuseStep 283367 = 425051) B425051
theorem B283529 : Blo 187803 283529 := bstep (se 2 (by rfl) ⟨106323, by rfl⟩ : syracuseStep 283529 = 212647) B212647
theorem B480239 : Blo 187803 480239 := bstep (se 1 (by rfl) ⟨360179, by rfl⟩ : syracuseStep 480239 = 720359) B720359
theorem B4576297 : Blo 187803 4576297 := bstep (se 2 (by rfl) ⟨1716111, by rfl⟩ : syracuseStep 4576297 = 3432223) B3432223
theorem B545953 : Blo 187803 545953 := bstep (se 2 (by rfl) ⟨204732, by rfl⟩ : syracuseStep 545953 = 409465) B409465
theorem B283871 : Blo 187803 283871 := bstep (se 1 (by rfl) ⟨212903, by rfl⟩ : syracuseStep 283871 = 425807) B425807
theorem B1070333 : Blo 187803 1070333 := bstep (se 3 (by rfl) ⟨200687, by rfl⟩ : syracuseStep 1070333 = 401375) B401375
theorem B283913 : Blo 187803 283913 := bstep (se 2 (by rfl) ⟨106467, by rfl⟩ : syracuseStep 283913 = 212935) B212935
theorem B546383 : Blo 187803 546383 := bstep (se 1 (by rfl) ⟨409787, by rfl⟩ : syracuseStep 546383 = 819575) B819575
theorem B284351 : Blo 187803 284351 := bstep (se 1 (by rfl) ⟨213263, by rfl⟩ : syracuseStep 284351 = 426527) B426527
theorem B284393 : Blo 187803 284393 := bstep (se 2 (by rfl) ⟨106647, by rfl⟩ : syracuseStep 284393 = 213295) B213295
theorem B284399 : Blo 187803 284399 := bstep (se 1 (by rfl) ⟨213299, by rfl⟩ : syracuseStep 284399 = 426599) B426599
theorem B317567 : Blo 187803 317567 := bstep (se 1 (by rfl) ⟨238175, by rfl⟩ : syracuseStep 317567 = 476351) B476351
theorem B284903 : Blo 187803 284903 := bstep (se 1 (by rfl) ⟨213677, by rfl⟩ : syracuseStep 284903 = 427355) B427355
theorem B8673641 : Blo 187803 8673641 := bstep (se 2 (by rfl) ⟨3252615, by rfl⟩ : syracuseStep 8673641 = 6505231) B6505231
theorem B285083 : Blo 187803 285083 := bstep (se 1 (by rfl) ⟨213812, by rfl⟩ : syracuseStep 285083 = 427625) B427625
theorem B612839 : Blo 187803 612839 := bstep (se 1 (by rfl) ⟨459629, by rfl⟩ : syracuseStep 612839 = 919259) B919259
theorem B285479 : Blo 187803 285479 := bstep (se 1 (by rfl) ⟨214109, by rfl⟩ : syracuseStep 285479 = 428219) B428219
theorem B383791 : Blo 187803 383791 := bstep (se 1 (by rfl) ⟨287843, by rfl⟩ : syracuseStep 383791 = 575687) B575687
theorem B678719 : Blo 187803 678719 := bstep (se 1 (by rfl) ⟨509039, by rfl⟩ : syracuseStep 678719 = 1018079) B1018079
theorem B285503 : Blo 187803 285503 := bstep (se 1 (by rfl) ⟨214127, by rfl⟩ : syracuseStep 285503 = 428255) B428255
theorem B646055 : Blo 187803 646055 := bstep (se 1 (by rfl) ⟨484541, by rfl⟩ : syracuseStep 646055 = 969083) B969083
theorem B384107 : Blo 187803 384107 := bstep (se 1 (by rfl) ⟨288080, by rfl⟩ : syracuseStep 384107 = 576161) B576161
theorem B285803 : Blo 187803 285803 := bstep (se 1 (by rfl) ⟨214352, by rfl⟩ : syracuseStep 285803 = 428705) B428705
theorem B1203329 : Blo 187803 1203329 := bstep (se 2 (by rfl) ⟨451248, by rfl⟩ : syracuseStep 1203329 = 902497) B902497
theorem B285947 : Blo 187803 285947 := bstep (se 1 (by rfl) ⟨214460, by rfl⟩ : syracuseStep 285947 = 428921) B428921
theorem B2743591 : Blo 187803 2743591 := bstep (se 1 (by rfl) ⟨2057693, by rfl⟩ : syracuseStep 2743591 = 4115387) B4115387
theorem B286043 : Blo 187803 286043 := bstep (se 1 (by rfl) ⟨214532, by rfl⟩ : syracuseStep 286043 = 429065) B429065
theorem B286073 : Blo 187803 286073 := bstep (se 2 (by rfl) ⟨107277, by rfl⟩ : syracuseStep 286073 = 214555) B214555
theorem B286079 : Blo 187803 286079 := bstep (se 1 (by rfl) ⟨214559, by rfl⟩ : syracuseStep 286079 = 429119) B429119
theorem B974263 : Blo 187803 974263 := bstep (se 1 (by rfl) ⟨730697, by rfl⟩ : syracuseStep 974263 = 1461395) B1461395
theorem B908995 : Blo 187803 908995 := bstep (se 1 (by rfl) ⟨681746, by rfl⟩ : syracuseStep 908995 = 1363493) B1363493
theorem B188143 : Blo 187803 188143 := bstep (se 1 (by rfl) ⟨141107, by rfl⟩ : syracuseStep 188143 = 282215) B282215
theorem B286631 : Blo 187803 286631 := bstep (se 1 (by rfl) ⟨214973, by rfl⟩ : syracuseStep 286631 = 429947) B429947
theorem B647081 : Blo 187803 647081 := bstep (se 2 (by rfl) ⟨242655, by rfl⟩ : syracuseStep 647081 = 485311) B485311
theorem B188399 : Blo 187803 188399 := bstep (se 1 (by rfl) ⟨141299, by rfl⟩ : syracuseStep 188399 = 282599) B282599
theorem B286703 : Blo 187803 286703 := bstep (se 1 (by rfl) ⟨215027, by rfl⟩ : syracuseStep 286703 = 430055) B430055
theorem B188479 : Blo 187803 188479 := bstep (se 1 (by rfl) ⟨141359, by rfl⟩ : syracuseStep 188479 = 282719) B282719
theorem B188487 : Blo 187803 188487 := bstep (se 1 (by rfl) ⟨141365, by rfl⟩ : syracuseStep 188487 = 282731) B282731
theorem B188519 : Blo 187803 188519 := bstep (se 1 (by rfl) ⟨141389, by rfl⟩ : syracuseStep 188519 = 282779) B282779
theorem B286823 : Blo 187803 286823 := bstep (se 1 (by rfl) ⟨215117, by rfl⟩ : syracuseStep 286823 = 430235) B430235
theorem B647297 : Blo 187803 647297 := bstep (se 2 (by rfl) ⟨242736, by rfl⟩ : syracuseStep 647297 = 485473) B485473
theorem B286955 : Blo 187803 286955 := bstep (se 1 (by rfl) ⟨215216, by rfl⟩ : syracuseStep 286955 = 430433) B430433
theorem B3760415 : Blo 187803 3760415 := bstep (se 1 (by rfl) ⟨2820311, by rfl⟩ : syracuseStep 3760415 = 5640623) B5640623
theorem B287015 : Blo 187803 287015 := bstep (se 1 (by rfl) ⟨215261, by rfl⟩ : syracuseStep 287015 = 430523) B430523
theorem B483833 : Blo 187803 483833 := bstep (se 2 (by rfl) ⟨181437, by rfl⟩ : syracuseStep 483833 = 362875) B362875
theorem B4907627 : Blo 187803 4907627 := bstep (se 1 (by rfl) ⟨3680720, by rfl⟩ : syracuseStep 4907627 = 7361441) B7361441
theorem B189087 : Blo 187803 189087 := bstep (se 1 (by rfl) ⟨141815, by rfl⟩ : syracuseStep 189087 = 283631) B283631
theorem B320233 : Blo 187803 320233 := bstep (se 2 (by rfl) ⟨120087, by rfl⟩ : syracuseStep 320233 = 240175) B240175
theorem B287465 : Blo 187803 287465 := bstep (se 2 (by rfl) ⟨107799, by rfl⟩ : syracuseStep 287465 = 215599) B215599
theorem B189343 : Blo 187803 189343 := bstep (se 1 (by rfl) ⟨142007, by rfl⟩ : syracuseStep 189343 = 284015) B284015
theorem B189423 : Blo 187803 189423 := bstep (se 1 (by rfl) ⟨142067, by rfl⟩ : syracuseStep 189423 = 284135) B284135
theorem B1434671 : Blo 187803 1434671 := bstep (se 1 (by rfl) ⟨1076003, by rfl⟩ : syracuseStep 1434671 = 2152007) B2152007
theorem B189531 : Blo 187803 189531 := bstep (se 1 (by rfl) ⟨142148, by rfl⟩ : syracuseStep 189531 = 284297) B284297
theorem B189543 : Blo 187803 189543 := bstep (se 1 (by rfl) ⟨142157, by rfl⟩ : syracuseStep 189543 = 284315) B284315
theorem B1369199 : Blo 187803 1369199 := bstep (se 1 (by rfl) ⟨1026899, by rfl⟩ : syracuseStep 1369199 = 2053799) B2053799
theorem B189671 : Blo 187803 189671 := bstep (se 1 (by rfl) ⟨142253, by rfl⟩ : syracuseStep 189671 = 284507) B284507
theorem B812267 : Blo 187803 812267 := bstep (se 1 (by rfl) ⟨609200, by rfl⟩ : syracuseStep 812267 = 1218401) B1218401
theorem B189927 : Blo 187803 189927 := bstep (se 1 (by rfl) ⟨142445, by rfl⟩ : syracuseStep 189927 = 284891) B284891
theorem B1074707 : Blo 187803 1074707 := bstep (se 1 (by rfl) ⟨806030, by rfl⟩ : syracuseStep 1074707 = 1612061) B1612061
theorem B4351583 : Blo 187803 4351583 := bstep (se 1 (by rfl) ⟨3263687, by rfl⟩ : syracuseStep 4351583 = 6527375) B6527375
theorem B321131 : Blo 187803 321131 := bstep (se 1 (by rfl) ⟨240848, by rfl⟩ : syracuseStep 321131 = 481697) B481697
theorem B190107 : Blo 187803 190107 := bstep (se 1 (by rfl) ⟨142580, by rfl⟩ : syracuseStep 190107 = 285161) B285161
theorem B2942647 : Blo 187803 2942647 := bstep (se 1 (by rfl) ⟨2206985, by rfl⟩ : syracuseStep 2942647 = 4413971) B4413971
theorem B321401 : Blo 187803 321401 := bstep (se 2 (by rfl) ⟨120525, by rfl⟩ : syracuseStep 321401 = 241051) B241051
theorem B190367 : Blo 187803 190367 := bstep (se 1 (by rfl) ⟨142775, by rfl⟩ : syracuseStep 190367 = 285551) B285551
theorem B190375 : Blo 187803 190375 := bstep (se 1 (by rfl) ⟨142781, by rfl⟩ : syracuseStep 190375 = 285563) B285563
theorem B485423 : Blo 187803 485423 := bstep (se 1 (by rfl) ⟨364067, by rfl⟩ : syracuseStep 485423 = 728135) B728135
theorem B321961 : Blo 187803 321961 := bstep (se 2 (by rfl) ⟨120735, by rfl⟩ : syracuseStep 321961 = 241471) B241471
theorem B190951 : Blo 187803 190951 := bstep (se 1 (by rfl) ⟨143213, by rfl⟩ : syracuseStep 190951 = 286427) B286427
theorem B191131 : Blo 187803 191131 := bstep (se 1 (by rfl) ⟨143348, by rfl⟩ : syracuseStep 191131 = 286697) B286697
theorem B322427 : Blo 187803 322427 := bstep (se 1 (by rfl) ⟨241820, by rfl⟩ : syracuseStep 322427 = 483641) B483641
theorem B191599 : Blo 187803 191599 := bstep (se 1 (by rfl) ⟨143699, by rfl⟩ : syracuseStep 191599 = 287399) B287399
theorem B322697 : Blo 187803 322697 := bstep (se 2 (by rfl) ⟨121011, by rfl⟩ : syracuseStep 322697 = 242023) B242023
theorem B322751 : Blo 187803 322751 := bstep (se 1 (by rfl) ⟨242063, by rfl⟩ : syracuseStep 322751 = 484127) B484127
theorem B191679 : Blo 187803 191679 := bstep (se 1 (by rfl) ⟨143759, by rfl⟩ : syracuseStep 191679 = 287519) B287519
theorem B191695 : Blo 187803 191695 := bstep (se 1 (by rfl) ⟨143771, by rfl⟩ : syracuseStep 191695 = 287543) B287543
theorem B2485633 : Blo 187803 2485633 := bstep (se 2 (by rfl) ⟨932112, by rfl⟩ : syracuseStep 2485633 = 1864225) B1864225
theorem B1207943 : Blo 187803 1207943 := bstep (se 1 (by rfl) ⟨905957, by rfl⟩ : syracuseStep 1207943 = 1811915) B1811915
theorem B2093165 : Blo 187803 2093165 := bstep (se 3 (by rfl) ⟨392468, by rfl⟩ : syracuseStep 2093165 = 784937) B784937
theorem B553159 : Blo 187803 553159 := bstep (se 1 (by rfl) ⟨414869, by rfl⟩ : syracuseStep 553159 = 829739) B829739
theorem B5468957 : Blo 187803 5468957 := bstep (se 3 (by rfl) ⟨1025429, by rfl⟩ : syracuseStep 5468957 = 2050859) B2050859
theorem B422747 : Blo 187803 422747 := bstep (se 1 (by rfl) ⟨317060, by rfl⟩ : syracuseStep 422747 = 634121) B634121
theorem B1209275 : Blo 187803 1209275 := bstep (se 1 (by rfl) ⟨906956, by rfl⟩ : syracuseStep 1209275 = 1813913) B1813913
theorem B226351 : Blo 187803 226351 := bstep (se 1 (by rfl) ⟨169763, by rfl⟩ : syracuseStep 226351 = 339527) B339527
theorem B357871 : Blo 187803 357871 := bstep (se 1 (by rfl) ⟨268403, by rfl⟩ : syracuseStep 357871 = 536807) B536807
theorem B816743 : Blo 187803 816743 := bstep (se 1 (by rfl) ⟨612557, by rfl⟩ : syracuseStep 816743 = 1225115) B1225115
theorem B1603997 : Blo 187803 1603997 := bstep (se 3 (by rfl) ⟨300749, by rfl⟩ : syracuseStep 1603997 = 601499) B601499
theorem B424475 : Blo 187803 424475 := bstep (se 1 (by rfl) ⟨318356, by rfl⟩ : syracuseStep 424475 = 636713) B636713
theorem B359579 : Blo 187803 359579 := bstep (se 1 (by rfl) ⟨269684, by rfl⟩ : syracuseStep 359579 = 539369) B539369
theorem B1080823 : Blo 187803 1080823 := bstep (se 1 (by rfl) ⟨810617, by rfl⟩ : syracuseStep 1080823 = 1621235) B1621235
theorem B2031655 : Blo 187803 2031655 := bstep (se 1 (by rfl) ⟨1523741, by rfl⟩ : syracuseStep 2031655 = 3047483) B3047483
theorem B360521 : Blo 187803 360521 := bstep (se 2 (by rfl) ⟨135195, by rfl⟩ : syracuseStep 360521 = 270391) B270391
theorem B1835135 : Blo 187803 1835135 := bstep (se 1 (by rfl) ⟨1376351, by rfl⟩ : syracuseStep 1835135 = 2752703) B2752703
theorem B1441961 : Blo 187803 1441961 := bstep (se 2 (by rfl) ⟨540735, by rfl⟩ : syracuseStep 1441961 = 1081471) B1081471
theorem B6881669 : Blo 187803 6881669 := bstep (se 4 (by rfl) ⟨645156, by rfl⟩ : syracuseStep 6881669 = 1290313) B1290313
theorem B1606351 : Blo 187803 1606351 := bstep (se 1 (by rfl) ⟨1204763, by rfl⟩ : syracuseStep 1606351 = 2409527) B2409527
theorem B426977 : Blo 187803 426977 := bstep (se 2 (by rfl) ⟨160116, by rfl⟩ : syracuseStep 426977 = 320233) B320233
theorem B2950181 : Blo 187803 2950181 := bstep (se 4 (by rfl) ⟨276579, by rfl⟩ : syracuseStep 2950181 = 553159) B553159
theorem B4097141 : Blo 187803 4097141 := bstep (se 5 (by rfl) ⟨192053, by rfl⟩ : syracuseStep 4097141 = 384107) B384107
theorem B1541387 : Blo 187803 1541387 := bstep (se 1 (by rfl) ⟨1156040, by rfl⟩ : syracuseStep 1541387 = 2312081) B2312081
theorem B427751 : Blo 187803 427751 := bstep (se 1 (by rfl) ⟨320813, by rfl⟩ : syracuseStep 427751 = 641627) B641627
theorem B349046909 : Blo 187803 349046909 := bstep (se 3 (by rfl) ⟨65446295, by rfl⟩ : syracuseStep 349046909 = 130892591) B130892591
theorem B3770833 : Blo 187803 3770833 := bstep (se 2 (by rfl) ⟨1414062, by rfl⟩ : syracuseStep 3770833 = 2828125) B2828125
theorem B13732355 : Blo 187803 13732355 := bstep (se 1 (by rfl) ⟨10299266, by rfl⟩ : syracuseStep 13732355 = 20598533) B20598533
theorem B1739755 : Blo 187803 1739755 := bstep (se 1 (by rfl) ⟨1304816, by rfl⟩ : syracuseStep 1739755 = 2609633) B2609633
theorem B429281 : Blo 187803 429281 := bstep (se 2 (by rfl) ⟨160980, by rfl⟩ : syracuseStep 429281 = 321961) B321961
theorem B200927 : Blo 187803 200927 := bstep (se 1 (by rfl) ⟨150695, by rfl⟩ : syracuseStep 200927 = 301391) B301391
theorem B3314177 : Blo 187803 3314177 := bstep (se 2 (by rfl) ⟨1242816, by rfl⟩ : syracuseStep 3314177 = 2485633) B2485633
theorem B3478049 : Blo 187803 3478049 := bstep (se 2 (by rfl) ⟨1304268, by rfl⟩ : syracuseStep 3478049 = 2608537) B2608537
theorem B430703 : Blo 187803 430703 := bstep (se 1 (by rfl) ⟨323027, by rfl⟩ : syracuseStep 430703 = 646055) B646055
theorem B431387 : Blo 187803 431387 := bstep (se 1 (by rfl) ⟨323540, by rfl⟩ : syracuseStep 431387 = 647081) B647081
theorem B431531 : Blo 187803 431531 := bstep (se 1 (by rfl) ⟨323648, by rfl⟩ : syracuseStep 431531 = 647297) B647297
theorem B956447 : Blo 187803 956447 := bstep (se 1 (by rfl) ⟨717335, by rfl⟩ : syracuseStep 956447 = 1434671) B1434671
theorem B1841363 : Blo 187803 1841363 := bstep (se 1 (by rfl) ⟨1381022, by rfl⟩ : syracuseStep 1841363 = 2762045) B2762045
theorem B6101729 : Blo 187803 6101729 := bstep (se 2 (by rfl) ⟨2288148, by rfl⟩ : syracuseStep 6101729 = 4576297) B4576297
theorem B301801 : Blo 187803 301801 := bstep (se 2 (by rfl) ⟨113175, by rfl⟩ : syracuseStep 301801 = 226351) B226351
theorem B1841899 : Blo 187803 1841899 := bstep (se 1 (by rfl) ⟨1381424, by rfl⟩ : syracuseStep 1841899 = 2762849) B2762849
theorem B727937 : Blo 187803 727937 := bstep (se 2 (by rfl) ⟨272976, by rfl⟩ : syracuseStep 727937 = 545953) B545953
theorem B1449737 : Blo 187803 1449737 := bstep (se 2 (by rfl) ⟨543651, by rfl⟩ : syracuseStep 1449737 = 1087303) B1087303
theorem B958877 : Blo 187803 958877 := bstep (se 3 (by rfl) ⟨179789, by rfl⟩ : syracuseStep 958877 = 359579) B359579
theorem B3645971 : Blo 187803 3645971 := bstep (se 1 (by rfl) ⟨2734478, by rfl⟩ : syracuseStep 3645971 = 5468957) B5468957
theorem B272521 : Blo 187803 272521 := bstep (se 2 (by rfl) ⟨102195, by rfl⟩ : syracuseStep 272521 = 204391) B204391
theorem B12593839 : Blo 187803 12593839 := bstep (se 1 (by rfl) ⟨9445379, by rfl⟩ : syracuseStep 12593839 = 18890759) B18890759
theorem B404203 : Blo 187803 404203 := bstep (se 1 (by rfl) ⟨303152, by rfl⟩ : syracuseStep 404203 = 606305) B606305
theorem B1453085 : Blo 187803 1453085 := bstep (se 3 (by rfl) ⟨272453, by rfl⟩ : syracuseStep 1453085 = 544907) B544907
theorem B1715671 : Blo 187803 1715671 := bstep (se 1 (by rfl) ⟨1286753, by rfl⟩ : syracuseStep 1715671 = 2573507) B2573507
theorem B634337 : Blo 187803 634337 := bstep (se 2 (by rfl) ⟨237876, by rfl⟩ : syracuseStep 634337 = 475753) B475753
theorem B634823 : Blo 187803 634823 := bstep (se 1 (by rfl) ⟨476117, by rfl⟩ : syracuseStep 634823 = 952235) B952235
theorem B1224857 : Blo 187803 1224857 := bstep (se 2 (by rfl) ⟨459321, by rfl⟩ : syracuseStep 1224857 = 918643) B918643
theorem B2437411 : Blo 187803 2437411 := bstep (se 1 (by rfl) ⟨1828058, by rfl⟩ : syracuseStep 2437411 = 3656117) B3656117
theorem B241967 : Blo 187803 241967 := bstep (se 1 (by rfl) ⟨181475, by rfl⟩ : syracuseStep 241967 = 362951) B362951
theorem B4108643 : Blo 187803 4108643 := bstep (se 1 (by rfl) ⟨3081482, by rfl⟩ : syracuseStep 4108643 = 6162965) B6162965
theorem B2175335 : Blo 187803 2175335 := bstep (se 1 (by rfl) ⟨1631501, by rfl⟩ : syracuseStep 2175335 = 3263003) B3263003
theorem B635255 : Blo 187803 635255 := bstep (se 1 (by rfl) ⟨476441, by rfl⟩ : syracuseStep 635255 = 952883) B952883
theorem B2798135 : Blo 187803 2798135 := bstep (se 1 (by rfl) ⟨2098601, by rfl⟩ : syracuseStep 2798135 = 4197203) B4197203
theorem B1455083 : Blo 187803 1455083 := bstep (se 1 (by rfl) ⟨1091312, by rfl⟩ : syracuseStep 1455083 = 2182625) B2182625
theorem B636335 : Blo 187803 636335 := bstep (se 1 (by rfl) ⟨477251, by rfl⟩ : syracuseStep 636335 = 954503) B954503
theorem B636443 : Blo 187803 636443 := bstep (se 1 (by rfl) ⟨477332, by rfl⟩ : syracuseStep 636443 = 954665) B954665
theorem B636659 : Blo 187803 636659 := bstep (se 1 (by rfl) ⟨477494, by rfl⟩ : syracuseStep 636659 = 954989) B954989
theorem B637415 : Blo 187803 637415 := bstep (se 1 (by rfl) ⟨478061, by rfl⟩ : syracuseStep 637415 = 956123) B956123
theorem B211711 : Blo 187803 211711 := bstep (se 1 (by rfl) ⟨158783, by rfl⟩ : syracuseStep 211711 = 317567) B317567
theorem B1457021 : Blo 187803 1457021 := bstep (se 3 (by rfl) ⟨273191, by rfl⟩ : syracuseStep 1457021 = 546383) B546383
theorem B5782427 : Blo 187803 5782427 := bstep (se 1 (by rfl) ⟨4336820, by rfl⟩ : syracuseStep 5782427 = 8673641) B8673641
theorem B408559 : Blo 187803 408559 := bstep (se 1 (by rfl) ⟨306419, by rfl⟩ : syracuseStep 408559 = 612839) B612839
theorem B802219 : Blo 187803 802219 := bstep (se 1 (by rfl) ⟨601664, by rfl⟩ : syracuseStep 802219 = 1203329) B1203329
theorem B638441 : Blo 187803 638441 := bstep (se 2 (by rfl) ⟨239415, by rfl⟩ : syracuseStep 638441 = 478831) B478831
theorem B2506943 : Blo 187803 2506943 := bstep (se 1 (by rfl) ⟨1880207, by rfl⟩ : syracuseStep 2506943 = 3760415) B3760415
theorem B639359 : Blo 187803 639359 := bstep (se 1 (by rfl) ⟨479519, by rfl⟩ : syracuseStep 639359 = 959039) B959039
theorem B639467 : Blo 187803 639467 := bstep (se 1 (by rfl) ⟨479600, by rfl⟩ : syracuseStep 639467 = 959201) B959201
theorem B541511 : Blo 187803 541511 := bstep (se 1 (by rfl) ⟨406133, by rfl⟩ : syracuseStep 541511 = 812267) B812267
theorem B2901055 : Blo 187803 2901055 := bstep (se 1 (by rfl) ⟨2175791, by rfl⟩ : syracuseStep 2901055 = 4351583) B4351583
theorem B214087 : Blo 187803 214087 := bstep (se 1 (by rfl) ⟨160565, by rfl⟩ : syracuseStep 214087 = 321131) B321131
theorem B214267 : Blo 187803 214267 := bstep (se 1 (by rfl) ⟨160700, by rfl⟩ : syracuseStep 214267 = 321401) B321401
theorem B968111 : Blo 187803 968111 := bstep (se 1 (by rfl) ⟨726083, by rfl⟩ : syracuseStep 968111 = 1452167) B1452167
theorem B214951 : Blo 187803 214951 := bstep (se 1 (by rfl) ⟨161213, by rfl⟩ : syracuseStep 214951 = 322427) B322427
theorem B477161 : Blo 187803 477161 := bstep (se 2 (by rfl) ⟨178935, by rfl⟩ : syracuseStep 477161 = 357871) B357871
theorem B215131 : Blo 187803 215131 := bstep (se 1 (by rfl) ⟨161348, by rfl⟩ : syracuseStep 215131 = 322697) B322697
theorem B215167 : Blo 187803 215167 := bstep (se 1 (by rfl) ⟨161375, by rfl⟩ : syracuseStep 215167 = 322751) B322751
theorem B805295 : Blo 187803 805295 := bstep (se 1 (by rfl) ⟨603971, by rfl⟩ : syracuseStep 805295 = 1207943) B1207943
theorem B1395443 : Blo 187803 1395443 := bstep (se 1 (by rfl) ⟨1046582, by rfl⟩ : syracuseStep 1395443 = 2093165) B2093165
theorem B281831 : Blo 187803 281831 := bstep (se 1 (by rfl) ⟨211373, by rfl⟩ : syracuseStep 281831 = 422747) B422747
theorem B806183 : Blo 187803 806183 := bstep (se 1 (by rfl) ⟨604637, by rfl⟩ : syracuseStep 806183 = 1209275) B1209275
theorem B511721 : Blo 187803 511721 := bstep (se 2 (by rfl) ⟨191895, by rfl⟩ : syracuseStep 511721 = 383791) B383791
theorem B544495 : Blo 187803 544495 := bstep (se 1 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 544495 = 816743) B816743
theorem B1560323 : Blo 187803 1560323 := bstep (se 1 (by rfl) ⟨1170242, by rfl⟩ : syracuseStep 1560323 = 2340485) B2340485
theorem B970703 : Blo 187803 970703 := bstep (se 1 (by rfl) ⟨728027, by rfl⟩ : syracuseStep 970703 = 1456055) B1456055
theorem B2412503 : Blo 187803 2412503 := bstep (se 1 (by rfl) ⟨1809377, by rfl⟩ : syracuseStep 2412503 = 3618755) B3618755
theorem B315433 : Blo 187803 315433 := bstep (se 2 (by rfl) ⟨118287, by rfl⟩ : syracuseStep 315433 = 236575) B236575
theorem B1069331 : Blo 187803 1069331 := bstep (se 1 (by rfl) ⟨801998, by rfl⟩ : syracuseStep 1069331 = 1603997) B1603997
theorem B807209 : Blo 187803 807209 := bstep (se 2 (by rfl) ⟨302703, by rfl⟩ : syracuseStep 807209 = 605407) B605407
theorem B282983 : Blo 187803 282983 := bstep (se 1 (by rfl) ⟨212237, by rfl⟩ : syracuseStep 282983 = 424475) B424475
theorem B3658121 : Blo 187803 3658121 := bstep (se 2 (by rfl) ⟨1371795, by rfl⟩ : syracuseStep 3658121 = 2743591) B2743591
theorem B643517 : Blo 187803 643517 := bstep (se 3 (by rfl) ⟨120659, by rfl⟩ : syracuseStep 643517 = 241319) B241319
theorem B1299017 : Blo 187803 1299017 := bstep (se 2 (by rfl) ⟨487131, by rfl⟩ : syracuseStep 1299017 = 974263) B974263
theorem B1496227 : Blo 187803 1496227 := bstep (se 1 (by rfl) ⟨1122170, by rfl⟩ : syracuseStep 1496227 = 2244341) B2244341
theorem B284267 : Blo 187803 284267 := bstep (se 1 (by rfl) ⟨213200, by rfl⟩ : syracuseStep 284267 = 426401) B426401
theorem B808555 : Blo 187803 808555 := bstep (se 1 (by rfl) ⟨606416, by rfl⟩ : syracuseStep 808555 = 1212833) B1212833
theorem B1463923 : Blo 187803 1463923 := bstep (se 1 (by rfl) ⟨1097942, by rfl⟩ : syracuseStep 1463923 = 2195885) B2195885
theorem B481049 : Blo 187803 481049 := bstep (se 2 (by rfl) ⟨180393, by rfl⟩ : syracuseStep 481049 = 360787) B360787
theorem B317351 : Blo 187803 317351 := bstep (se 1 (by rfl) ⟨238013, by rfl⟩ : syracuseStep 317351 = 476027) B476027
theorem B284639 : Blo 187803 284639 := bstep (se 1 (by rfl) ⟨213479, by rfl⟩ : syracuseStep 284639 = 426959) B426959
theorem B284699 : Blo 187803 284699 := bstep (se 1 (by rfl) ⟨213524, by rfl⟩ : syracuseStep 284699 = 427049) B427049
theorem B645515 : Blo 187803 645515 := bstep (se 1 (by rfl) ⟨484136, by rfl⟩ : syracuseStep 645515 = 968273) B968273
theorem B285287 : Blo 187803 285287 := bstep (se 1 (by rfl) ⟨213965, by rfl⟩ : syracuseStep 285287 = 427931) B427931
theorem B285419 : Blo 187803 285419 := bstep (se 1 (by rfl) ⟨214064, by rfl⟩ : syracuseStep 285419 = 428129) B428129
theorem B6347767 : Blo 187803 6347767 := bstep (se 1 (by rfl) ⟨4760825, by rfl⟩ : syracuseStep 6347767 = 9521651) B9521651
theorem B482395 : Blo 187803 482395 := bstep (se 1 (by rfl) ⟨361796, by rfl⟩ : syracuseStep 482395 = 723593) B723593
theorem B285791 : Blo 187803 285791 := bstep (se 1 (by rfl) ⟨214343, by rfl⟩ : syracuseStep 285791 = 428687) B428687
theorem B285833 : Blo 187803 285833 := bstep (se 2 (by rfl) ⟨107187, by rfl⟩ : syracuseStep 285833 = 214375) B214375
theorem B285851 : Blo 187803 285851 := bstep (se 1 (by rfl) ⟨214388, by rfl⟩ : syracuseStep 285851 = 428777) B428777
theorem B285887 : Blo 187803 285887 := bstep (se 1 (by rfl) ⟨214415, by rfl⟩ : syracuseStep 285887 = 428831) B428831
theorem B646379 : Blo 187803 646379 := bstep (se 1 (by rfl) ⟨484784, by rfl⟩ : syracuseStep 646379 = 969569) B969569
theorem B2448893 : Blo 187803 2448893 := bstep (se 3 (by rfl) ⟨459167, by rfl⟩ : syracuseStep 2448893 = 918335) B918335
theorem B188007 : Blo 187803 188007 := bstep (se 1 (by rfl) ⟨141005, by rfl⟩ : syracuseStep 188007 = 282011) B282011
theorem B286319 : Blo 187803 286319 := bstep (se 1 (by rfl) ⟨214739, by rfl⟩ : syracuseStep 286319 = 429479) B429479
theorem B286439 : Blo 187803 286439 := bstep (se 1 (by rfl) ⟨214829, by rfl⟩ : syracuseStep 286439 = 429659) B429659
theorem B319241 : Blo 187803 319241 := bstep (se 2 (by rfl) ⟨119715, by rfl⟩ : syracuseStep 319241 = 239431) B239431
theorem B646991 : Blo 187803 646991 := bstep (se 1 (by rfl) ⟨485243, by rfl⟩ : syracuseStep 646991 = 970487) B970487
theorem B188251 : Blo 187803 188251 := bstep (se 1 (by rfl) ⟨141188, by rfl⟩ : syracuseStep 188251 = 282377) B282377
theorem B188287 : Blo 187803 188287 := bstep (se 1 (by rfl) ⟨141215, by rfl⟩ : syracuseStep 188287 = 282431) B282431
theorem B1466369 : Blo 187803 1466369 := bstep (se 2 (by rfl) ⟨549888, by rfl⟩ : syracuseStep 1466369 = 1099777) B1099777
theorem B188447 : Blo 187803 188447 := bstep (se 1 (by rfl) ⟨141335, by rfl⟩ : syracuseStep 188447 = 282671) B282671
theorem B188743 : Blo 187803 188743 := bstep (se 1 (by rfl) ⟨141557, by rfl⟩ : syracuseStep 188743 = 283115) B283115
theorem B188827 : Blo 187803 188827 := bstep (se 1 (by rfl) ⟨141620, by rfl⟩ : syracuseStep 188827 = 283241) B283241
theorem B188831 : Blo 187803 188831 := bstep (se 1 (by rfl) ⟨141623, by rfl⟩ : syracuseStep 188831 = 283247) B283247
theorem B188911 : Blo 187803 188911 := bstep (se 1 (by rfl) ⟨141683, by rfl⟩ : syracuseStep 188911 = 283367) B283367
theorem B189019 : Blo 187803 189019 := bstep (se 1 (by rfl) ⟨141764, by rfl⟩ : syracuseStep 189019 = 283529) B283529
theorem B320159 : Blo 187803 320159 := bstep (se 1 (by rfl) ⟨240119, by rfl⟩ : syracuseStep 320159 = 480239) B480239
theorem B189247 : Blo 187803 189247 := bstep (se 1 (by rfl) ⟨141935, by rfl⟩ : syracuseStep 189247 = 283871) B283871
theorem B713555 : Blo 187803 713555 := bstep (se 1 (by rfl) ⟨535166, by rfl⟩ : syracuseStep 713555 = 1070333) B1070333
theorem B189275 : Blo 187803 189275 := bstep (se 1 (by rfl) ⟨141956, by rfl⟩ : syracuseStep 189275 = 283913) B283913
theorem B189567 : Blo 187803 189567 := bstep (se 1 (by rfl) ⟨142175, by rfl⟩ : syracuseStep 189567 = 284351) B284351
theorem B189595 : Blo 187803 189595 := bstep (se 1 (by rfl) ⟨142196, by rfl⟩ : syracuseStep 189595 = 284393) B284393
theorem B189599 : Blo 187803 189599 := bstep (se 1 (by rfl) ⟨142199, by rfl⟩ : syracuseStep 189599 = 284399) B284399
theorem B189935 : Blo 187803 189935 := bstep (se 1 (by rfl) ⟨142451, by rfl⟩ : syracuseStep 189935 = 284903) B284903
theorem B681473 : Blo 187803 681473 := bstep (se 2 (by rfl) ⟨255552, by rfl⟩ : syracuseStep 681473 = 511105) B511105
theorem B484937 : Blo 187803 484937 := bstep (se 2 (by rfl) ⟨181851, by rfl⟩ : syracuseStep 484937 = 363703) B363703
theorem B190055 : Blo 187803 190055 := bstep (se 1 (by rfl) ⟨142541, by rfl⟩ : syracuseStep 190055 = 285083) B285083
theorem B190319 : Blo 187803 190319 := bstep (se 1 (by rfl) ⟨142739, by rfl⟩ : syracuseStep 190319 = 285479) B285479
theorem B452479 : Blo 187803 452479 := bstep (se 1 (by rfl) ⟨339359, by rfl⟩ : syracuseStep 452479 = 678719) B678719
theorem B190335 : Blo 187803 190335 := bstep (se 1 (by rfl) ⟨142751, by rfl⟩ : syracuseStep 190335 = 285503) B285503
theorem B190535 : Blo 187803 190535 := bstep (se 1 (by rfl) ⟨142901, by rfl⟩ : syracuseStep 190535 = 285803) B285803
theorem B190631 : Blo 187803 190631 := bstep (se 1 (by rfl) ⟨142973, by rfl⟩ : syracuseStep 190631 = 285947) B285947
theorem B190695 : Blo 187803 190695 := bstep (se 1 (by rfl) ⟨143021, by rfl⟩ : syracuseStep 190695 = 286043) B286043
theorem B190715 : Blo 187803 190715 := bstep (se 1 (by rfl) ⟨143036, by rfl⟩ : syracuseStep 190715 = 286073) B286073
theorem B190719 : Blo 187803 190719 := bstep (se 1 (by rfl) ⟨143039, by rfl⟩ : syracuseStep 190719 = 286079) B286079
theorem B191087 : Blo 187803 191087 := bstep (se 1 (by rfl) ⟨143315, by rfl⟩ : syracuseStep 191087 = 286631) B286631
theorem B191135 : Blo 187803 191135 := bstep (se 1 (by rfl) ⟨143351, by rfl⟩ : syracuseStep 191135 = 286703) B286703
theorem B191215 : Blo 187803 191215 := bstep (se 1 (by rfl) ⟨143411, by rfl⟩ : syracuseStep 191215 = 286823) B286823
theorem B191303 : Blo 187803 191303 := bstep (se 1 (by rfl) ⟨143477, by rfl⟩ : syracuseStep 191303 = 286955) B286955
theorem B191343 : Blo 187803 191343 := bstep (se 1 (by rfl) ⟨143507, by rfl⟩ : syracuseStep 191343 = 287015) B287015
theorem B322555 : Blo 187803 322555 := bstep (se 1 (by rfl) ⟨241916, by rfl⟩ : syracuseStep 322555 = 483833) B483833
theorem B3271751 : Blo 187803 3271751 := bstep (se 1 (by rfl) ⟨2453813, by rfl⟩ : syracuseStep 3271751 = 4907627) B4907627
theorem B191643 : Blo 187803 191643 := bstep (se 1 (by rfl) ⟨143732, by rfl⟩ : syracuseStep 191643 = 287465) B287465
theorem B912799 : Blo 187803 912799 := bstep (se 1 (by rfl) ⟨684599, by rfl⟩ : syracuseStep 912799 = 1369199) B1369199
theorem B716471 : Blo 187803 716471 := bstep (se 1 (by rfl) ⟨537353, by rfl⟩ : syracuseStep 716471 = 1074707) B1074707
theorem B2977769 : Blo 187803 2977769 := bstep (se 2 (by rfl) ⟨1116663, by rfl⟩ : syracuseStep 2977769 = 2233327) B2233327
theorem B323561 : Blo 187803 323561 := bstep (se 2 (by rfl) ⟨121335, by rfl⟩ : syracuseStep 323561 = 242671) B242671
theorem B323615 : Blo 187803 323615 := bstep (se 1 (by rfl) ⟨242711, by rfl⟩ : syracuseStep 323615 = 485423) B485423
theorem B1077623 : Blo 187803 1077623 := bstep (se 1 (by rfl) ⟨808217, by rfl⟩ : syracuseStep 1077623 = 1616435) B1616435
theorem B422711 : Blo 187803 422711 := bstep (se 1 (by rfl) ⟨317033, by rfl⟩ : syracuseStep 422711 = 634067) B634067
theorem B3241133 : Blo 187803 3241133 := bstep (se 3 (by rfl) ⟨607712, by rfl⟩ : syracuseStep 3241133 = 1215425) B1215425
theorem B358175 : Blo 187803 358175 := bstep (se 1 (by rfl) ⟨268631, by rfl⟩ : syracuseStep 358175 = 537263) B537263
theorem B423791 : Blo 187803 423791 := bstep (se 1 (by rfl) ⟨317843, by rfl⟩ : syracuseStep 423791 = 635687) B635687
theorem B424043 : Blo 187803 424043 := bstep (se 1 (by rfl) ⟨318032, by rfl⟩ : syracuseStep 424043 = 636065) B636065
theorem B15694117 : Blo 187803 15694117 := bstep (se 4 (by rfl) ⟨1471323, by rfl⟩ : syracuseStep 15694117 = 2942647) B2942647
theorem B817879 : Blo 187803 817879 := bstep (se 1 (by rfl) ⟨613409, by rfl⟩ : syracuseStep 817879 = 1226819) B1226819
theorem B28146653 : Blo 187803 28146653 := bstep (se 3 (by rfl) ⟨5277497, by rfl⟩ : syracuseStep 28146653 = 10554995) B10554995
theorem B1441097 : Blo 187803 1441097 := bstep (se 2 (by rfl) ⟨540411, by rfl⟩ : syracuseStep 1441097 = 1080823) B1080823
theorem B687599 : Blo 187803 687599 := bstep (se 1 (by rfl) ⟨515699, by rfl⟩ : syracuseStep 687599 = 1031399) B1031399
theorem B1211993 : Blo 187803 1211993 := bstep (se 2 (by rfl) ⟨454497, by rfl⟩ : syracuseStep 1211993 = 908995) B908995
theorem B1375865 : Blo 187803 1375865 := bstep (se 2 (by rfl) ⟨515949, by rfl⟩ : syracuseStep 1375865 = 1031899) B1031899
theorem B360119 : Blo 187803 360119 := bstep (se 1 (by rfl) ⟨270089, by rfl⟩ : syracuseStep 360119 = 540179) B540179
theorem B426239 : Blo 187803 426239 := bstep (se 1 (by rfl) ⟨319679, by rfl⟩ : syracuseStep 426239 = 639359) B639359
theorem B4587779 : Blo 187803 4587779 := bstep (se 1 (by rfl) ⟨3440834, by rfl⟩ : syracuseStep 4587779 = 6881669) B6881669
theorem B426311 : Blo 187803 426311 := bstep (se 1 (by rfl) ⟨319733, by rfl⟩ : syracuseStep 426311 = 639467) B639467
theorem B6685181 : Blo 187803 6685181 := bstep (se 3 (by rfl) ⟨1253471, by rfl⟩ : syracuseStep 6685181 = 2506943) B2506943
theorem B361007 : Blo 187803 361007 := bstep (se 1 (by rfl) ⟨270755, by rfl⟩ : syracuseStep 361007 = 541511) B541511
theorem B1966787 : Blo 187803 1966787 := bstep (se 1 (by rfl) ⟨1475090, by rfl⟩ : syracuseStep 1966787 = 2950181) B2950181
theorem B2851549 : Blo 187803 2851549 := bstep (se 3 (by rfl) ⟨534665, by rfl⟩ : syracuseStep 2851549 = 1069331) B1069331
theorem B3868073 : Blo 187803 3868073 := bstep (se 2 (by rfl) ⟨1450527, by rfl⟩ : syracuseStep 3868073 = 2901055) B2901055
theorem B1608335 : Blo 187803 1608335 := bstep (se 1 (by rfl) ⟨1206251, by rfl⟩ : syracuseStep 1608335 = 2412503) B2412503
theorem B363361 : Blo 187803 363361 := bstep (se 2 (by rfl) ⟨136260, by rfl⟩ : syracuseStep 363361 = 272521) B272521
theorem B429011 : Blo 187803 429011 := bstep (se 1 (by rfl) ⟨321758, by rfl⟩ : syracuseStep 429011 = 643517) B643517
theorem B430073 : Blo 187803 430073 := bstep (se 2 (by rfl) ⟨161277, by rfl⟩ : syracuseStep 430073 = 322555) B322555
theorem B430343 : Blo 187803 430343 := bstep (se 1 (by rfl) ⟨322757, by rfl⟩ : syracuseStep 430343 = 645515) B645515
theorem B4067819 : Blo 187803 4067819 := bstep (se 1 (by rfl) ⟨3050864, by rfl⟩ : syracuseStep 4067819 = 6101729) B6101729
theorem B430919 : Blo 187803 430919 := bstep (se 1 (by rfl) ⟨323189, by rfl⟩ : syracuseStep 430919 = 646379) B646379
theorem B725993 : Blo 187803 725993 := bstep (se 2 (by rfl) ⟨272247, by rfl⟩ : syracuseStep 725993 = 544495) B544495
theorem B431327 : Blo 187803 431327 := bstep (se 1 (by rfl) ⟨323495, by rfl⟩ : syracuseStep 431327 = 646991) B646991
theorem B2430647 : Blo 187803 2430647 := bstep (se 1 (by rfl) ⟨1822985, by rfl⟩ : syracuseStep 2430647 = 3645971) B3645971
theorem B3249881 : Blo 187803 3249881 := bstep (se 2 (by rfl) ⟨1218705, by rfl⟩ : syracuseStep 3249881 = 2437411) B2437411
theorem B1450223 : Blo 187803 1450223 := bstep (se 1 (by rfl) ⟨1087667, by rfl⟩ : syracuseStep 1450223 = 2175335) B2175335
theorem B1090505 : Blo 187803 1090505 := bstep (se 2 (by rfl) ⟨408939, by rfl⟩ : syracuseStep 1090505 = 817879) B817879
theorem B402401 : Blo 187803 402401 := bstep (se 2 (by rfl) ⟨150900, by rfl⟩ : syracuseStep 402401 = 301801) B301801
theorem B238783 : Blo 187803 238783 := bstep (se 1 (by rfl) ⟨179087, by rfl⟩ : syracuseStep 238783 = 358175) B358175
theorem B8463689 : Blo 187803 8463689 := bstep (se 2 (by rfl) ⟨3173883, by rfl⟩ : syracuseStep 8463689 = 6347767) B6347767
theorem B960731 : Blo 187803 960731 := bstep (se 1 (by rfl) ⟨720548, by rfl⟩ : syracuseStep 960731 = 1441097) B1441097
theorem B240079 : Blo 187803 240079 := bstep (se 1 (by rfl) ⟨180059, by rfl⟩ : syracuseStep 240079 = 360119) B360119
theorem B7940717 : Blo 187803 7940717 := bstep (se 3 (by rfl) ⟨1488884, by rfl⟩ : syracuseStep 7940717 = 2977769) B2977769
theorem B240347 : Blo 187803 240347 := bstep (se 1 (by rfl) ⟨180260, by rfl⟩ : syracuseStep 240347 = 360521) B360521
theorem B1223423 : Blo 187803 1223423 := bstep (se 1 (by rfl) ⟨917567, by rfl⟩ : syracuseStep 1223423 = 1835135) B1835135
theorem B961307 : Blo 187803 961307 := bstep (se 1 (by rfl) ⟨720980, by rfl⟩ : syracuseStep 961307 = 1441961) B1441961
theorem B1682309 : Blo 187803 1682309 := bstep (se 4 (by rfl) ⟨157716, by rfl⟩ : syracuseStep 1682309 = 315433) B315433
theorem B535805 : Blo 187803 535805 := bstep (se 3 (by rfl) ⟨100463, by rfl⟩ : syracuseStep 535805 = 200927) B200927
theorem B2731427 : Blo 187803 2731427 := bstep (se 1 (by rfl) ⟨2048570, by rfl⟩ : syracuseStep 2731427 = 4097141) B4097141
theorem B2141801 : Blo 187803 2141801 := bstep (se 2 (by rfl) ⟨803175, by rfl⟩ : syracuseStep 2141801 = 1606351) B1606351
theorem B232697939 : Blo 187803 232697939 := bstep (se 1 (by rfl) ⟨174523454, by rfl⟩ : syracuseStep 232697939 = 349046909) B349046909
theorem B83701957 : Blo 187803 83701957 := bstep (se 4 (by rfl) ⟨7847058, by rfl⟩ : syracuseStep 83701957 = 15694117) B15694117
theorem B536863 : Blo 187803 536863 := bstep (se 1 (by rfl) ⟨402647, by rfl⟩ : syracuseStep 536863 = 805295) B805295
theorem B9154903 : Blo 187803 9154903 := bstep (se 1 (by rfl) ⟨6866177, by rfl⟩ : syracuseStep 9154903 = 13732355) B13732355
theorem B930295 : Blo 187803 930295 := bstep (se 1 (by rfl) ⟨697721, by rfl⟩ : syracuseStep 930295 = 1395443) B1395443
theorem B537455 : Blo 187803 537455 := bstep (se 1 (by rfl) ⟨403091, by rfl⟩ : syracuseStep 537455 = 806183) B806183
theorem B341147 : Blo 187803 341147 := bstep (se 1 (by rfl) ⟨255860, by rfl⟩ : syracuseStep 341147 = 511721) B511721
theorem B603305 : Blo 187803 603305 := bstep (se 2 (by rfl) ⟨226239, by rfl⟩ : syracuseStep 603305 = 452479) B452479
theorem B538139 : Blo 187803 538139 := bstep (se 1 (by rfl) ⟨403604, by rfl⟩ : syracuseStep 538139 = 807209) B807209
theorem B2438747 : Blo 187803 2438747 := bstep (se 1 (by rfl) ⟨1829060, by rfl⟩ : syracuseStep 2438747 = 3658121) B3658121
theorem B2209451 : Blo 187803 2209451 := bstep (se 1 (by rfl) ⟨1657088, by rfl⟩ : syracuseStep 2209451 = 3314177) B3314177
theorem B866011 : Blo 187803 866011 := bstep (se 1 (by rfl) ⟨649508, by rfl⟩ : syracuseStep 866011 = 1299017) B1299017
theorem B5027777 : Blo 187803 5027777 := bstep (se 2 (by rfl) ⟨1885416, by rfl⟩ : syracuseStep 5027777 = 3770833) B3770833
theorem B4110365 : Blo 187803 4110365 := bstep (se 3 (by rfl) ⟨770693, by rfl⟩ : syracuseStep 4110365 = 1541387) B1541387
theorem B16791785 : Blo 187803 16791785 := bstep (se 2 (by rfl) ⟨6296919, by rfl⟩ : syracuseStep 16791785 = 12593839) B12593839
theorem B538937 : Blo 187803 538937 := bstep (se 2 (by rfl) ⟨202101, by rfl⟩ : syracuseStep 538937 = 404203) B404203
theorem B211567 : Blo 187803 211567 := bstep (se 1 (by rfl) ⟨158675, by rfl⟩ : syracuseStep 211567 = 317351) B317351
theorem B1817261 : Blo 187803 1817261 := bstep (se 3 (by rfl) ⟨340736, by rfl⟩ : syracuseStep 1817261 = 681473) B681473
theorem B637631 : Blo 187803 637631 := bstep (se 1 (by rfl) ⟨478223, by rfl⟩ : syracuseStep 637631 = 956447) B956447
theorem B1227575 : Blo 187803 1227575 := bstep (se 1 (by rfl) ⟨920681, by rfl⟩ : syracuseStep 1227575 = 1841363) B1841363
theorem B212827 : Blo 187803 212827 := bstep (se 1 (by rfl) ⟨159620, by rfl⟩ : syracuseStep 212827 = 319241) B319241
theorem B966491 : Blo 187803 966491 := bstep (se 1 (by rfl) ⟨724868, by rfl⟩ : syracuseStep 966491 = 1449737) B1449737
theorem B639251 : Blo 187803 639251 := bstep (se 1 (by rfl) ⟨479438, by rfl⟩ : syracuseStep 639251 = 958877) B958877
theorem B213439 : Blo 187803 213439 := bstep (se 1 (by rfl) ⟨160079, by rfl⟩ : syracuseStep 213439 = 320159) B320159
theorem B475703 : Blo 187803 475703 := bstep (se 1 (by rfl) ⟨356777, by rfl⟩ : syracuseStep 475703 = 713555) B713555
theorem B968723 : Blo 187803 968723 := bstep (se 1 (by rfl) ⟨726542, by rfl⟩ : syracuseStep 968723 = 1453085) B1453085
theorem B2181167 : Blo 187803 2181167 := bstep (se 1 (by rfl) ⟨1635875, by rfl⟩ : syracuseStep 2181167 = 3271751) B3271751
theorem B1951897 : Blo 187803 1951897 := bstep (se 2 (by rfl) ⟨731961, by rfl⟩ : syracuseStep 1951897 = 1463923) B1463923
theorem B4868261 : Blo 187803 4868261 := bstep (se 4 (by rfl) ⟨456399, by rfl⟩ : syracuseStep 4868261 = 912799) B912799
theorem B477647 : Blo 187803 477647 := bstep (se 1 (by rfl) ⟨358235, by rfl⟩ : syracuseStep 477647 = 716471) B716471
theorem B215707 : Blo 187803 215707 := bstep (se 1 (by rfl) ⟨161780, by rfl⟩ : syracuseStep 215707 = 323561) B323561
theorem B215743 : Blo 187803 215743 := bstep (se 1 (by rfl) ⟨161807, by rfl⟩ : syracuseStep 215743 = 323615) B323615
theorem B2739095 : Blo 187803 2739095 := bstep (se 1 (by rfl) ⟨2054321, by rfl⟩ : syracuseStep 2739095 = 4108643) B4108643
theorem B281807 : Blo 187803 281807 := bstep (se 1 (by rfl) ⟨211355, by rfl⟩ : syracuseStep 281807 = 422711) B422711
theorem B970055 : Blo 187803 970055 := bstep (se 1 (by rfl) ⟨727541, by rfl⟩ : syracuseStep 970055 = 1455083) B1455083
theorem B282281 : Blo 187803 282281 := bstep (se 2 (by rfl) ⟨105855, by rfl⟩ : syracuseStep 282281 = 211711) B211711
theorem B282527 : Blo 187803 282527 := bstep (se 1 (by rfl) ⟨211895, by rfl⟩ : syracuseStep 282527 = 423791) B423791
theorem B544745 : Blo 187803 544745 := bstep (se 2 (by rfl) ⟨204279, by rfl⟩ : syracuseStep 544745 = 408559) B408559
theorem B282695 : Blo 187803 282695 := bstep (se 1 (by rfl) ⟨212021, by rfl⟩ : syracuseStep 282695 = 424043) B424043
theorem B643193 : Blo 187803 643193 := bstep (se 2 (by rfl) ⟨241197, by rfl⟩ : syracuseStep 643193 = 482395) B482395
theorem B1069625 : Blo 187803 1069625 := bstep (se 2 (by rfl) ⟨401109, by rfl⟩ : syracuseStep 1069625 = 802219) B802219
theorem B971347 : Blo 187803 971347 := bstep (se 1 (by rfl) ⟨728510, by rfl⟩ : syracuseStep 971347 = 1457021) B1457021
theorem B3854951 : Blo 187803 3854951 := bstep (se 1 (by rfl) ⟨2891213, by rfl⟩ : syracuseStep 3854951 = 5782427) B5782427
theorem B18764435 : Blo 187803 18764435 := bstep (se 1 (by rfl) ⟨14073326, by rfl⟩ : syracuseStep 18764435 = 28146653) B28146653
theorem B807995 : Blo 187803 807995 := bstep (se 1 (by rfl) ⟨605996, by rfl⟩ : syracuseStep 807995 = 1211993) B1211993
theorem B2708873 : Blo 187803 2708873 := bstep (se 2 (by rfl) ⟨1015827, by rfl⟩ : syracuseStep 2708873 = 2031655) B2031655
theorem B284651 : Blo 187803 284651 := bstep (se 1 (by rfl) ⟨213488, by rfl⟩ : syracuseStep 284651 = 426977) B426977
theorem B645245 : Blo 187803 645245 := bstep (se 3 (by rfl) ⟨120983, by rfl⟩ : syracuseStep 645245 = 241967) B241967
theorem B645407 : Blo 187803 645407 := bstep (se 1 (by rfl) ⟨484055, by rfl⟩ : syracuseStep 645407 = 968111) B968111
theorem B285167 : Blo 187803 285167 := bstep (se 1 (by rfl) ⟨213875, by rfl⟩ : syracuseStep 285167 = 427751) B427751
theorem B318107 : Blo 187803 318107 := bstep (se 1 (by rfl) ⟨238580, by rfl⟩ : syracuseStep 318107 = 477161) B477161
theorem B285449 : Blo 187803 285449 := bstep (se 2 (by rfl) ⟨107043, by rfl⟩ : syracuseStep 285449 = 214087) B214087
theorem B285689 : Blo 187803 285689 := bstep (se 2 (by rfl) ⟨107133, by rfl⟩ : syracuseStep 285689 = 214267) B214267
theorem B286187 : Blo 187803 286187 := bstep (se 1 (by rfl) ⟨214640, by rfl⟩ : syracuseStep 286187 = 429281) B429281
theorem B187887 : Blo 187803 187887 := bstep (se 1 (by rfl) ⟨140915, by rfl⟩ : syracuseStep 187887 = 281831) B281831
theorem B1040215 : Blo 187803 1040215 := bstep (se 1 (by rfl) ⟨780161, by rfl⟩ : syracuseStep 1040215 = 1560323) B1560323
theorem B286601 : Blo 187803 286601 := bstep (se 2 (by rfl) ⟨107475, by rfl⟩ : syracuseStep 286601 = 214951) B214951
theorem B647135 : Blo 187803 647135 := bstep (se 1 (by rfl) ⟨485351, by rfl⟩ : syracuseStep 647135 = 970703) B970703
theorem B286841 : Blo 187803 286841 := bstep (se 2 (by rfl) ⟨107565, by rfl⟩ : syracuseStep 286841 = 215131) B215131
theorem B286889 : Blo 187803 286889 := bstep (se 2 (by rfl) ⟨107583, by rfl⟩ : syracuseStep 286889 = 215167) B215167
theorem B188655 : Blo 187803 188655 := bstep (se 1 (by rfl) ⟨141491, by rfl⟩ : syracuseStep 188655 = 282983) B282983
theorem B2318699 : Blo 187803 2318699 := bstep (se 1 (by rfl) ⟨1739024, by rfl⟩ : syracuseStep 2318699 = 3478049) B3478049
theorem B287135 : Blo 187803 287135 := bstep (se 1 (by rfl) ⟨215351, by rfl⟩ : syracuseStep 287135 = 430703) B430703
theorem B287591 : Blo 187803 287591 := bstep (se 1 (by rfl) ⟨215693, by rfl⟩ : syracuseStep 287591 = 431387) B431387
theorem B287687 : Blo 187803 287687 := bstep (se 1 (by rfl) ⟨215765, by rfl⟩ : syracuseStep 287687 = 431531) B431531
theorem B189511 : Blo 187803 189511 := bstep (se 1 (by rfl) ⟨142133, by rfl⟩ : syracuseStep 189511 = 284267) B284267
theorem B320699 : Blo 187803 320699 := bstep (se 1 (by rfl) ⟨240524, by rfl⟩ : syracuseStep 320699 = 481049) B481049
theorem B2319673 : Blo 187803 2319673 := bstep (se 2 (by rfl) ⟨869877, by rfl⟩ : syracuseStep 2319673 = 1739755) B1739755
theorem B189759 : Blo 187803 189759 := bstep (se 1 (by rfl) ⟨142319, by rfl⟩ : syracuseStep 189759 = 284639) B284639
theorem B189799 : Blo 187803 189799 := bstep (se 1 (by rfl) ⟨142349, by rfl⟩ : syracuseStep 189799 = 284699) B284699
theorem B190191 : Blo 187803 190191 := bstep (se 1 (by rfl) ⟨142643, by rfl⟩ : syracuseStep 190191 = 285287) B285287
theorem B190279 : Blo 187803 190279 := bstep (se 1 (by rfl) ⟨142709, by rfl⟩ : syracuseStep 190279 = 285419) B285419
theorem B485291 : Blo 187803 485291 := bstep (se 1 (by rfl) ⟨363968, by rfl⟩ : syracuseStep 485291 = 727937) B727937
theorem B2287561 : Blo 187803 2287561 := bstep (se 2 (by rfl) ⟨857835, by rfl⟩ : syracuseStep 2287561 = 1715671) B1715671
theorem B190527 : Blo 187803 190527 := bstep (se 1 (by rfl) ⟨142895, by rfl⟩ : syracuseStep 190527 = 285791) B285791
theorem B190555 : Blo 187803 190555 := bstep (se 1 (by rfl) ⟨142916, by rfl⟩ : syracuseStep 190555 = 285833) B285833
theorem B190567 : Blo 187803 190567 := bstep (se 1 (by rfl) ⟨142925, by rfl⟩ : syracuseStep 190567 = 285851) B285851
theorem B190591 : Blo 187803 190591 := bstep (se 1 (by rfl) ⟨142943, by rfl⟩ : syracuseStep 190591 = 285887) B285887
theorem B1632595 : Blo 187803 1632595 := bstep (se 1 (by rfl) ⟨1224446, by rfl⟩ : syracuseStep 1632595 = 2448893) B2448893
theorem B190879 : Blo 187803 190879 := bstep (se 1 (by rfl) ⟨143159, by rfl⟩ : syracuseStep 190879 = 286319) B286319
theorem B190959 : Blo 187803 190959 := bstep (se 1 (by rfl) ⟨143219, by rfl⟩ : syracuseStep 190959 = 286439) B286439
theorem B977579 : Blo 187803 977579 := bstep (se 1 (by rfl) ⟨733184, by rfl⟩ : syracuseStep 977579 = 1466369) B1466369
theorem B323291 : Blo 187803 323291 := bstep (se 1 (by rfl) ⟨242468, by rfl⟩ : syracuseStep 323291 = 484937) B484937
theorem B1994969 : Blo 187803 1994969 := bstep (se 2 (by rfl) ⟨748113, by rfl⟩ : syracuseStep 1994969 = 1496227) B1496227
theorem B1078073 : Blo 187803 1078073 := bstep (se 2 (by rfl) ⟨404277, by rfl⟩ : syracuseStep 1078073 = 808555) B808555
theorem B422891 : Blo 187803 422891 := bstep (se 1 (by rfl) ⟨317168, by rfl⟩ : syracuseStep 422891 = 634337) B634337
theorem B423215 : Blo 187803 423215 := bstep (se 1 (by rfl) ⟨317411, by rfl⟩ : syracuseStep 423215 = 634823) B634823
theorem B816571 : Blo 187803 816571 := bstep (se 1 (by rfl) ⟨612428, by rfl⟩ : syracuseStep 816571 = 1224857) B1224857
theorem B423503 : Blo 187803 423503 := bstep (se 1 (by rfl) ⟨317627, by rfl⟩ : syracuseStep 423503 = 635255) B635255
theorem B718415 : Blo 187803 718415 := bstep (se 1 (by rfl) ⟨538811, by rfl⟩ : syracuseStep 718415 = 1077623) B1077623
theorem B1865423 : Blo 187803 1865423 := bstep (se 1 (by rfl) ⟨1399067, by rfl⟩ : syracuseStep 1865423 = 2798135) B2798135
theorem B2160755 : Blo 187803 2160755 := bstep (se 1 (by rfl) ⟨1620566, by rfl⟩ : syracuseStep 2160755 = 3241133) B3241133
theorem B424223 : Blo 187803 424223 := bstep (se 1 (by rfl) ⟨318167, by rfl⟩ : syracuseStep 424223 = 636335) B636335
theorem B2455865 : Blo 187803 2455865 := bstep (se 2 (by rfl) ⟨920949, by rfl⟩ : syracuseStep 2455865 = 1841899) B1841899
theorem B424295 : Blo 187803 424295 := bstep (se 1 (by rfl) ⟨318221, by rfl⟩ : syracuseStep 424295 = 636443) B636443
theorem B424439 : Blo 187803 424439 := bstep (se 1 (by rfl) ⟨318329, by rfl⟩ : syracuseStep 424439 = 636659) B636659
theorem B424943 : Blo 187803 424943 := bstep (se 1 (by rfl) ⟨318707, by rfl⟩ : syracuseStep 424943 = 637415) B637415
theorem B425627 : Blo 187803 425627 := bstep (se 1 (by rfl) ⟨319220, by rfl⟩ : syracuseStep 425627 = 638441) B638441
theorem B458399 : Blo 187803 458399 := bstep (se 1 (by rfl) ⟨343799, by rfl⟩ : syracuseStep 458399 = 687599) B687599
theorem B917243 : Blo 187803 917243 := bstep (se 1 (by rfl) ⟨687932, by rfl⟩ : syracuseStep 917243 = 1375865) B1375865
theorem B426167 : Blo 187803 426167 := bstep (se 1 (by rfl) ⟨319625, by rfl⟩ : syracuseStep 426167 = 639251) B639251
theorem B620527837 : Blo 187803 620527837 := bstep (se 3 (by rfl) ⟨116348969, by rfl⟩ : syracuseStep 620527837 = 232697939) B232697939
theorem B4456787 : Blo 187803 4456787 := bstep (se 1 (by rfl) ⟨3342590, by rfl⟩ : syracuseStep 4456787 = 6685181) B6685181
theorem B1311191 : Blo 187803 1311191 := bstep (se 1 (by rfl) ⟨983393, by rfl⟩ : syracuseStep 1311191 = 1966787) B1966787
theorem B3245507 : Blo 187803 3245507 := bstep (se 1 (by rfl) ⟨2434130, by rfl⟩ : syracuseStep 3245507 = 4868261) B4868261
theorem B3050081 : Blo 187803 3050081 := bstep (se 2 (by rfl) ⟨1143780, by rfl⟩ : syracuseStep 3050081 = 2287561) B2287561
theorem B428795 : Blo 187803 428795 := bstep (se 1 (by rfl) ⟨321596, by rfl⟩ : syracuseStep 428795 = 643193) B643193
theorem B1805915 : Blo 187803 1805915 := bstep (se 1 (by rfl) ⟨1354436, by rfl⟩ : syracuseStep 1805915 = 2708873) B2708873
theorem B2166587 : Blo 187803 2166587 := bstep (se 1 (by rfl) ⟨1624940, by rfl⟩ : syracuseStep 2166587 = 3249881) B3249881
theorem B430163 : Blo 187803 430163 := bstep (se 1 (by rfl) ⟨322622, by rfl⟩ : syracuseStep 430163 = 645245) B645245
theorem B430271 : Blo 187803 430271 := bstep (se 1 (by rfl) ⟨322703, by rfl⟩ : syracuseStep 430271 = 645407) B645407
theorem B431423 : Blo 187803 431423 := bstep (se 1 (by rfl) ⟨323567, by rfl⟩ : syracuseStep 431423 = 647135) B647135
theorem B1545799 : Blo 187803 1545799 := bstep (se 1 (by rfl) ⟨1159349, by rfl⟩ : syracuseStep 1545799 = 2318699) B2318699
theorem B727003 : Blo 187803 727003 := bstep (se 1 (by rfl) ⟨545252, by rfl⟩ : syracuseStep 727003 = 1090505) B1090505
theorem B268267 : Blo 187803 268267 := bstep (se 1 (by rfl) ⟨201200, by rfl⟩ : syracuseStep 268267 = 402401) B402401
theorem B5642459 : Blo 187803 5642459 := bstep (se 1 (by rfl) ⟨4231844, by rfl⟩ : syracuseStep 5642459 = 8463689) B8463689
theorem B1088761 : Blo 187803 1088761 := bstep (se 2 (by rfl) ⟨408285, by rfl⟩ : syracuseStep 1088761 = 816571) B816571
theorem B1121539 : Blo 187803 1121539 := bstep (se 1 (by rfl) ⟨841154, by rfl⟩ : syracuseStep 1121539 = 1682309) B1682309
theorem B1154681 : Blo 187803 1154681 := bstep (se 2 (by rfl) ⟨433005, by rfl⟩ : syracuseStep 1154681 = 866011) B866011
theorem B402203 : Blo 187803 402203 := bstep (se 1 (by rfl) ⟨301652, by rfl⟩ : syracuseStep 402203 = 603305) B603305
theorem B3351851 : Blo 187803 3351851 := bstep (se 1 (by rfl) ⟨2513888, by rfl⟩ : syracuseStep 3351851 = 5027777) B5027777
theorem B1222397 : Blo 187803 1222397 := bstep (se 3 (by rfl) ⟨229199, by rfl⟩ : syracuseStep 1222397 = 458399) B458399
theorem B1386953 : Blo 187803 1386953 := bstep (se 2 (by rfl) ⟨520107, by rfl⟩ : syracuseStep 1386953 = 1040215) B1040215
theorem B1452653 : Blo 187803 1452653 := bstep (se 3 (by rfl) ⟨272372, by rfl⟩ : syracuseStep 1452653 = 544745) B544745
theorem B3058519 : Blo 187803 3058519 := bstep (se 1 (by rfl) ⟨2293889, by rfl⟩ : syracuseStep 3058519 = 4587779) B4587779
theorem B240671 : Blo 187803 240671 := bstep (se 1 (by rfl) ⟨180503, by rfl⟩ : syracuseStep 240671 = 361007) B361007
theorem B1454111 : Blo 187803 1454111 := bstep (se 1 (by rfl) ⟨1090583, by rfl⟩ : syracuseStep 1454111 = 2181167) B2181167
theorem B3092897 : Blo 187803 3092897 := bstep (se 2 (by rfl) ⟨1159836, by rfl⟩ : syracuseStep 3092897 = 2319673) B2319673
theorem B4961573 : Blo 187803 4961573 := bstep (se 4 (by rfl) ⟨465147, by rfl⟩ : syracuseStep 4961573 = 930295) B930295
theorem B2602529 : Blo 187803 2602529 := bstep (se 2 (by rfl) ⟨975948, by rfl⟩ : syracuseStep 2602529 = 1951897) B1951897
theorem B2569967 : Blo 187803 2569967 := bstep (se 1 (by rfl) ⟨1927475, by rfl⟩ : syracuseStep 2569967 = 3854951) B3854951
theorem B2176793 : Blo 187803 2176793 := bstep (se 2 (by rfl) ⟨816297, by rfl⟩ : syracuseStep 2176793 = 1632595) B1632595
theorem B538663 : Blo 187803 538663 := bstep (se 1 (by rfl) ⟨403997, by rfl⟩ : syracuseStep 538663 = 807995) B807995
theorem B1620431 : Blo 187803 1620431 := bstep (se 1 (by rfl) ⟨1215323, by rfl⟩ : syracuseStep 1620431 = 2430647) B2430647
theorem B212071 : Blo 187803 212071 := bstep (se 1 (by rfl) ⟨159053, by rfl⟩ : syracuseStep 212071 = 318107) B318107
theorem B60833045 : Blo 187803 60833045 := bstep (se 6 (by rfl) ⟨1425774, by rfl⟩ : syracuseStep 60833045 = 2851549) B2851549
theorem B966815 : Blo 187803 966815 := bstep (se 1 (by rfl) ⟨725111, by rfl⟩ : syracuseStep 966815 = 1450223) B1450223
theorem B12206537 : Blo 187803 12206537 := bstep (se 2 (by rfl) ⟨4577451, by rfl⟩ : syracuseStep 12206537 = 9154903) B9154903
theorem B1295129 : Blo 187803 1295129 := bstep (se 2 (by rfl) ⟨485673, by rfl⟩ : syracuseStep 1295129 = 971347) B971347
theorem B213799 : Blo 187803 213799 := bstep (se 1 (by rfl) ⟨160349, by rfl⟩ : syracuseStep 213799 = 320699) B320699
theorem B640487 : Blo 187803 640487 := bstep (se 1 (by rfl) ⟨480365, by rfl⟩ : syracuseStep 640487 = 960731) B960731
theorem B5293811 : Blo 187803 5293811 := bstep (se 1 (by rfl) ⟨3970358, by rfl⟩ : syracuseStep 5293811 = 7940717) B7940717
theorem B640871 : Blo 187803 640871 := bstep (se 1 (by rfl) ⟨480653, by rfl⟩ : syracuseStep 640871 = 961307) B961307
theorem B640925 : Blo 187803 640925 := bstep (se 3 (by rfl) ⟨120173, by rfl⟩ : syracuseStep 640925 = 240347) B240347
theorem B1820951 : Blo 187803 1820951 := bstep (se 1 (by rfl) ⟨1365713, by rfl⟩ : syracuseStep 1820951 = 2731427) B2731427
theorem B1427867 : Blo 187803 1427867 := bstep (se 1 (by rfl) ⟨1070900, by rfl⟩ : syracuseStep 1427867 = 2141801) B2141801
theorem B215527 : Blo 187803 215527 := bstep (se 1 (by rfl) ⟨161645, by rfl⟩ : syracuseStep 215527 = 323291) B323291
theorem B1329979 : Blo 187803 1329979 := bstep (se 1 (by rfl) ⟨997484, by rfl⟩ : syracuseStep 1329979 = 1994969) B1994969
theorem B281927 : Blo 187803 281927 := bstep (se 1 (by rfl) ⟨211445, by rfl⟩ : syracuseStep 281927 = 422891) B422891
theorem B282089 : Blo 187803 282089 := bstep (se 2 (by rfl) ⟨105783, by rfl⟩ : syracuseStep 282089 = 211567) B211567
theorem B282143 : Blo 187803 282143 := bstep (se 1 (by rfl) ⟨211607, by rfl⟩ : syracuseStep 282143 = 423215) B423215
theorem B282335 : Blo 187803 282335 := bstep (se 1 (by rfl) ⟨211751, by rfl⟩ : syracuseStep 282335 = 423503) B423503
theorem B478943 : Blo 187803 478943 := bstep (se 1 (by rfl) ⟨359207, by rfl⟩ : syracuseStep 478943 = 718415) B718415
theorem B1625831 : Blo 187803 1625831 := bstep (se 1 (by rfl) ⟨1219373, by rfl⟩ : syracuseStep 1625831 = 2438747) B2438747
theorem B2740243 : Blo 187803 2740243 := bstep (se 1 (by rfl) ⟨2055182, by rfl⟩ : syracuseStep 2740243 = 4110365) B4110365
theorem B11194523 : Blo 187803 11194523 := bstep (se 1 (by rfl) ⟨8395892, by rfl⟩ : syracuseStep 11194523 = 16791785) B16791785
theorem B282815 : Blo 187803 282815 := bstep (se 1 (by rfl) ⟨212111, by rfl⟩ : syracuseStep 282815 = 424223) B424223
theorem B282863 : Blo 187803 282863 := bstep (se 1 (by rfl) ⟨212147, by rfl⟩ : syracuseStep 282863 = 424295) B424295
theorem B282959 : Blo 187803 282959 := bstep (se 1 (by rfl) ⟨212219, by rfl⟩ : syracuseStep 282959 = 424439) B424439
theorem B283295 : Blo 187803 283295 := bstep (se 1 (by rfl) ⟨212471, by rfl⟩ : syracuseStep 283295 = 424943) B424943
theorem B283751 : Blo 187803 283751 := bstep (se 1 (by rfl) ⟨212813, by rfl⟩ : syracuseStep 283751 = 425627) B425627
theorem B283769 : Blo 187803 283769 := bstep (se 2 (by rfl) ⟨106413, by rfl⟩ : syracuseStep 283769 = 212827) B212827
theorem B611495 : Blo 187803 611495 := bstep (se 1 (by rfl) ⟨458621, by rfl⟩ : syracuseStep 611495 = 917243) B917243
theorem B644327 : Blo 187803 644327 := bstep (se 1 (by rfl) ⟨483245, by rfl⟩ : syracuseStep 644327 = 966491) B966491
theorem B284159 : Blo 187803 284159 := bstep (se 1 (by rfl) ⟨213119, by rfl⟩ : syracuseStep 284159 = 426239) B426239
theorem B284207 : Blo 187803 284207 := bstep (se 1 (by rfl) ⟨213155, by rfl⟩ : syracuseStep 284207 = 426311) B426311
theorem B317135 : Blo 187803 317135 := bstep (se 1 (by rfl) ⟨237851, by rfl⟩ : syracuseStep 317135 = 475703) B475703
theorem B284585 : Blo 187803 284585 := bstep (se 2 (by rfl) ⟨106719, by rfl⟩ : syracuseStep 284585 = 213439) B213439
theorem B2578715 : Blo 187803 2578715 := bstep (se 1 (by rfl) ⟨1934036, by rfl⟩ : syracuseStep 2578715 = 3868073) B3868073
theorem B645815 : Blo 187803 645815 := bstep (se 1 (by rfl) ⟨484361, by rfl⟩ : syracuseStep 645815 = 968723) B968723
theorem B318377 : Blo 187803 318377 := bstep (se 2 (by rfl) ⟨119391, by rfl⟩ : syracuseStep 318377 = 238783) B238783
theorem B318431 : Blo 187803 318431 := bstep (se 1 (by rfl) ⟨238823, by rfl⟩ : syracuseStep 318431 = 477647) B477647
theorem B1072223 : Blo 187803 1072223 := bstep (se 1 (by rfl) ⟨804167, by rfl⟩ : syracuseStep 1072223 = 1608335) B1608335
theorem B1826063 : Blo 187803 1826063 := bstep (se 1 (by rfl) ⟨1369547, by rfl⟩ : syracuseStep 1826063 = 2739095) B2739095
theorem B286007 : Blo 187803 286007 := bstep (se 1 (by rfl) ⟨214505, by rfl⟩ : syracuseStep 286007 = 429011) B429011
theorem B187871 : Blo 187803 187871 := bstep (se 1 (by rfl) ⟨140903, by rfl⟩ : syracuseStep 187871 = 281807) B281807
theorem B646703 : Blo 187803 646703 := bstep (se 1 (by rfl) ⟨485027, by rfl⟩ : syracuseStep 646703 = 970055) B970055
theorem B1433213 : Blo 187803 1433213 := bstep (se 3 (by rfl) ⟨268727, by rfl⟩ : syracuseStep 1433213 = 537455) B537455
theorem B188187 : Blo 187803 188187 := bstep (se 1 (by rfl) ⟨141140, by rfl⟩ : syracuseStep 188187 = 282281) B282281
theorem B188351 : Blo 187803 188351 := bstep (se 1 (by rfl) ⟨141263, by rfl⟩ : syracuseStep 188351 = 282527) B282527
theorem B286715 : Blo 187803 286715 := bstep (se 1 (by rfl) ⟨215036, by rfl⟩ : syracuseStep 286715 = 430073) B430073
theorem B188463 : Blo 187803 188463 := bstep (se 1 (by rfl) ⟨141347, by rfl⟩ : syracuseStep 188463 = 282695) B282695
theorem B286895 : Blo 187803 286895 := bstep (se 1 (by rfl) ⟨215171, by rfl⟩ : syracuseStep 286895 = 430343) B430343
theorem B2711879 : Blo 187803 2711879 := bstep (se 1 (by rfl) ⟨2033909, by rfl⟩ : syracuseStep 2711879 = 4067819) B4067819
theorem B713083 : Blo 187803 713083 := bstep (se 1 (by rfl) ⟨534812, by rfl⟩ : syracuseStep 713083 = 1069625) B1069625
theorem B12509623 : Blo 187803 12509623 := bstep (se 1 (by rfl) ⟨9382217, by rfl⟩ : syracuseStep 12509623 = 18764435) B18764435
theorem B287279 : Blo 187803 287279 := bstep (se 1 (by rfl) ⟨215459, by rfl⟩ : syracuseStep 287279 = 430919) B430919
theorem B320105 : Blo 187803 320105 := bstep (se 2 (by rfl) ⟨120039, by rfl⟩ : syracuseStep 320105 = 240079) B240079
theorem B483995 : Blo 187803 483995 := bstep (se 1 (by rfl) ⟨362996, by rfl⟩ : syracuseStep 483995 = 725993) B725993
theorem B287551 : Blo 187803 287551 := bstep (se 1 (by rfl) ⟨215663, by rfl⟩ : syracuseStep 287551 = 431327) B431327
theorem B287609 : Blo 187803 287609 := bstep (se 2 (by rfl) ⟨107853, by rfl⟩ : syracuseStep 287609 = 215707) B215707
theorem B287657 : Blo 187803 287657 := bstep (se 2 (by rfl) ⟨107871, by rfl⟩ : syracuseStep 287657 = 215743) B215743
theorem B484481 : Blo 187803 484481 := bstep (se 2 (by rfl) ⟨181680, by rfl⟩ : syracuseStep 484481 = 363361) B363361
theorem B189767 : Blo 187803 189767 := bstep (se 1 (by rfl) ⟨142325, by rfl⟩ : syracuseStep 189767 = 284651) B284651
theorem B190111 : Blo 187803 190111 := bstep (se 1 (by rfl) ⟨142583, by rfl⟩ : syracuseStep 190111 = 285167) B285167
theorem B5891869 : Blo 187803 5891869 := bstep (se 3 (by rfl) ⟨1104725, by rfl⟩ : syracuseStep 5891869 = 2209451) B2209451
theorem B190299 : Blo 187803 190299 := bstep (se 1 (by rfl) ⟨142724, by rfl⟩ : syracuseStep 190299 = 285449) B285449
theorem B190459 : Blo 187803 190459 := bstep (se 1 (by rfl) ⟨142844, by rfl⟩ : syracuseStep 190459 = 285689) B285689
theorem B190791 : Blo 187803 190791 := bstep (se 1 (by rfl) ⟨143093, by rfl⟩ : syracuseStep 190791 = 286187) B286187
theorem B191067 : Blo 187803 191067 := bstep (se 1 (by rfl) ⟨143300, by rfl⟩ : syracuseStep 191067 = 286601) B286601
theorem B191227 : Blo 187803 191227 := bstep (se 1 (by rfl) ⟨143420, by rfl⟩ : syracuseStep 191227 = 286841) B286841
theorem B191259 : Blo 187803 191259 := bstep (se 1 (by rfl) ⟨143444, by rfl⟩ : syracuseStep 191259 = 286889) B286889
theorem B111602609 : Blo 187803 111602609 := bstep (se 2 (by rfl) ⟨41850978, by rfl⟩ : syracuseStep 111602609 = 83701957) B83701957
theorem B191423 : Blo 187803 191423 := bstep (se 1 (by rfl) ⟨143567, by rfl⟩ : syracuseStep 191423 = 287135) B287135
theorem B715817 : Blo 187803 715817 := bstep (se 2 (by rfl) ⟨268431, by rfl⟩ : syracuseStep 715817 = 536863) B536863
theorem B191727 : Blo 187803 191727 := bstep (se 1 (by rfl) ⟨143795, by rfl⟩ : syracuseStep 191727 = 287591) B287591
theorem B191791 : Blo 187803 191791 := bstep (se 1 (by rfl) ⟨143843, by rfl⟩ : syracuseStep 191791 = 287687) B287687
theorem B323527 : Blo 187803 323527 := bstep (se 1 (by rfl) ⟨242645, by rfl⟩ : syracuseStep 323527 = 485291) B485291
theorem B651719 : Blo 187803 651719 := bstep (se 1 (by rfl) ⟨488789, by rfl⟩ : syracuseStep 651719 = 977579) B977579
theorem B815615 : Blo 187803 815615 := bstep (se 1 (by rfl) ⟨611711, by rfl⟩ : syracuseStep 815615 = 1223423) B1223423
theorem B357203 : Blo 187803 357203 := bstep (se 1 (by rfl) ⟨267902, by rfl⟩ : syracuseStep 357203 = 535805) B535805
theorem B718715 : Blo 187803 718715 := bstep (se 1 (by rfl) ⟨539036, by rfl⟩ : syracuseStep 718715 = 1078073) B1078073
theorem B227431 : Blo 187803 227431 := bstep (se 1 (by rfl) ⟨170573, by rfl⟩ : syracuseStep 227431 = 341147) B341147
theorem B358759 : Blo 187803 358759 := bstep (se 1 (by rfl) ⟨269069, by rfl⟩ : syracuseStep 358759 = 538139) B538139
theorem B1243615 : Blo 187803 1243615 := bstep (se 1 (by rfl) ⟨932711, by rfl⟩ : syracuseStep 1243615 = 1865423) B1865423
theorem B1440503 : Blo 187803 1440503 := bstep (se 1 (by rfl) ⟨1080377, by rfl⟩ : syracuseStep 1440503 = 2160755) B2160755
theorem B359291 : Blo 187803 359291 := bstep (se 1 (by rfl) ⟨269468, by rfl⟩ : syracuseStep 359291 = 538937) B538937
theorem B1637243 : Blo 187803 1637243 := bstep (se 1 (by rfl) ⟨1227932, by rfl⟩ : syracuseStep 1637243 = 2455865) B2455865
theorem B1211507 : Blo 187803 1211507 := bstep (se 1 (by rfl) ⟨908630, by rfl⟩ : syracuseStep 1211507 = 1817261) B1817261
theorem B425087 : Blo 187803 425087 := bstep (se 1 (by rfl) ⟨318815, by rfl⟩ : syracuseStep 425087 = 637631) B637631
theorem B818383 : Blo 187803 818383 := bstep (se 1 (by rfl) ⟨613787, by rfl⟩ : syracuseStep 818383 = 1227575) B1227575
theorem B950777 : Blo 187803 950777 := bstep (se 2 (by rfl) ⟨356541, by rfl⟩ : syracuseStep 950777 = 713083) B713083
theorem B1212965 : Blo 187803 1212965 := bstep (se 4 (by rfl) ⟨113715, by rfl⟩ : syracuseStep 1212965 = 227431) B227431
theorem B2163671 : Blo 187803 2163671 := bstep (se 1 (by rfl) ⟨1622753, by rfl⟩ : syracuseStep 2163671 = 3245507) B3245507
theorem B427247 : Blo 187803 427247 := bstep (se 1 (by rfl) ⟨320435, by rfl⟩ : syracuseStep 427247 = 640871) B640871
theorem B427283 : Blo 187803 427283 := bstep (se 1 (by rfl) ⟨320462, by rfl⟩ : syracuseStep 427283 = 640925) B640925
theorem B1213967 : Blo 187803 1213967 := bstep (se 1 (by rfl) ⟨910475, by rfl⟩ : syracuseStep 1213967 = 1820951) B1820951
theorem B951911 : Blo 187803 951911 := bstep (se 1 (by rfl) ⟨713933, by rfl⟩ : syracuseStep 951911 = 1427867) B1427867
theorem B2033387 : Blo 187803 2033387 := bstep (se 1 (by rfl) ⟨1525040, by rfl⟩ : syracuseStep 2033387 = 3050081) B3050081
theorem B66717989 : Blo 187803 66717989 := bstep (se 4 (by rfl) ⟨6254811, by rfl⟩ : syracuseStep 66717989 = 12509623) B12509623
theorem B1083887 : Blo 187803 1083887 := bstep (se 1 (by rfl) ⟨812915, by rfl⟩ : syracuseStep 1083887 = 1625831) B1625831
theorem B1444391 : Blo 187803 1444391 := bstep (se 1 (by rfl) ⟨1083293, by rfl⟩ : syracuseStep 1444391 = 2166587) B2166587
theorem B429551 : Blo 187803 429551 := bstep (se 1 (by rfl) ⟨322163, by rfl⟩ : syracuseStep 429551 = 644327) B644327
theorem B1773305 : Blo 187803 1773305 := bstep (se 2 (by rfl) ⟨664989, by rfl⟩ : syracuseStep 1773305 = 1329979) B1329979
theorem B1707965 : Blo 187803 1707965 := bstep (se 3 (by rfl) ⟨320243, by rfl⟩ : syracuseStep 1707965 = 640487) B640487
theorem B430543 : Blo 187803 430543 := bstep (se 1 (by rfl) ⟨322907, by rfl⟩ : syracuseStep 430543 = 645815) B645815
theorem B1217375 : Blo 187803 1217375 := bstep (se 1 (by rfl) ⟨913031, by rfl⟩ : syracuseStep 1217375 = 1826063) B1826063
theorem B431135 : Blo 187803 431135 := bstep (se 1 (by rfl) ⟨323351, by rfl⟩ : syracuseStep 431135 = 646703) B646703
theorem B955475 : Blo 187803 955475 := bstep (se 1 (by rfl) ⟨716606, by rfl⟩ : syracuseStep 955475 = 1433213) B1433213
theorem B431369 : Blo 187803 431369 := bstep (se 2 (by rfl) ⟨161763, by rfl⟩ : syracuseStep 431369 = 323527) B323527
theorem B1807919 : Blo 187803 1807919 := bstep (se 1 (by rfl) ⟨1355939, by rfl⟩ : syracuseStep 1807919 = 2711879) B2711879
theorem B2234567 : Blo 187803 2234567 := bstep (se 1 (by rfl) ⟨1675925, by rfl⟩ : syracuseStep 2234567 = 3351851) B3351851
theorem B924635 : Blo 187803 924635 := bstep (se 1 (by rfl) ⟨693476, by rfl⟩ : syracuseStep 924635 = 1386953) B1386953
theorem B434479 : Blo 187803 434479 := bstep (se 1 (by rfl) ⟨325859, by rfl⟩ : syracuseStep 434479 = 651719) B651719
theorem B238135 : Blo 187803 238135 := bstep (se 1 (by rfl) ⟨178601, by rfl⟩ : syracuseStep 238135 = 357203) B357203
theorem B1713311 : Blo 187803 1713311 := bstep (se 1 (by rfl) ⟨1284983, by rfl⟩ : syracuseStep 1713311 = 2569967) B2569967
theorem B1451195 : Blo 187803 1451195 := bstep (se 1 (by rfl) ⟨1088396, by rfl⟩ : syracuseStep 1451195 = 2176793) B2176793
theorem B1091177 : Blo 187803 1091177 := bstep (se 2 (by rfl) ⟨409191, by rfl⟩ : syracuseStep 1091177 = 818383) B818383
theorem B1451681 : Blo 187803 1451681 := bstep (se 2 (by rfl) ⟨544380, by rfl⟩ : syracuseStep 1451681 = 1088761) B1088761
theorem B960335 : Blo 187803 960335 := bstep (se 1 (by rfl) ⟨720251, by rfl⟩ : syracuseStep 960335 = 1440503) B1440503
theorem B239527 : Blo 187803 239527 := bstep (se 1 (by rfl) ⟨179645, by rfl⟩ : syracuseStep 239527 = 359291) B359291
theorem B1091495 : Blo 187803 1091495 := bstep (se 1 (by rfl) ⟨818621, by rfl⟩ : syracuseStep 1091495 = 1637243) B1637243
theorem B827370449 : Blo 187803 827370449 := bstep (se 2 (by rfl) ⟨310263918, by rfl⟩ : syracuseStep 827370449 = 620527837) B620527837
theorem B8137691 : Blo 187803 8137691 := bstep (se 1 (by rfl) ⟨6103268, by rfl⟩ : syracuseStep 8137691 = 12206537) B12206537
theorem B3453677 : Blo 187803 3453677 := bstep (se 3 (by rfl) ⟨647564, by rfl⟩ : syracuseStep 3453677 = 1295129) B1295129
theorem B407663 : Blo 187803 407663 := bstep (se 1 (by rfl) ⟨305747, by rfl⟩ : syracuseStep 407663 = 611495) B611495
theorem B4078025 : Blo 187803 4078025 := bstep (se 2 (by rfl) ⟨1529259, by rfl⟩ : syracuseStep 4078025 = 3058519) B3058519
theorem B211423 : Blo 187803 211423 := bstep (se 1 (by rfl) ⟨158567, by rfl⟩ : syracuseStep 211423 = 317135) B317135
theorem B1719143 : Blo 187803 1719143 := bstep (se 1 (by rfl) ⟨1289357, by rfl⟩ : syracuseStep 1719143 = 2578715) B2578715
theorem B212251 : Blo 187803 212251 := bstep (se 1 (by rfl) ⟨159188, by rfl⟩ : syracuseStep 212251 = 318377) B318377
theorem B212287 : Blo 187803 212287 := bstep (se 1 (by rfl) ⟨159215, by rfl⟩ : syracuseStep 212287 = 318431) B318431
theorem B769787 : Blo 187803 769787 := bstep (se 1 (by rfl) ⟨577340, by rfl⟩ : syracuseStep 769787 = 1154681) B1154681
theorem B3653657 : Blo 187803 3653657 := bstep (se 2 (by rfl) ⟨1370121, by rfl⟩ : syracuseStep 3653657 = 2740243) B2740243
theorem B213403 : Blo 187803 213403 := bstep (se 1 (by rfl) ⟨160052, by rfl⟩ : syracuseStep 213403 = 320105) B320105
theorem B968435 : Blo 187803 968435 := bstep (se 1 (by rfl) ⟨726326, by rfl⟩ : syracuseStep 968435 = 1452653) B1452653
theorem B74401739 : Blo 187803 74401739 := bstep (se 1 (by rfl) ⟨55801304, by rfl⟩ : syracuseStep 74401739 = 111602609) B111602609
theorem B477211 : Blo 187803 477211 := bstep (se 1 (by rfl) ⟨357908, by rfl⟩ : syracuseStep 477211 = 715817) B715817
theorem B969337 : Blo 187803 969337 := bstep (se 2 (by rfl) ⟨363501, by rfl⟩ : syracuseStep 969337 = 727003) B727003
theorem B969407 : Blo 187803 969407 := bstep (se 1 (by rfl) ⟨727055, by rfl⟩ : syracuseStep 969407 = 1454111) B1454111
theorem B641789 : Blo 187803 641789 := bstep (se 3 (by rfl) ⟨120335, by rfl⟩ : syracuseStep 641789 = 240671) B240671
theorem B543743 : Blo 187803 543743 := bstep (se 1 (by rfl) ⟨407807, by rfl⟩ : syracuseStep 543743 = 815615) B815615
theorem B478345 : Blo 187803 478345 := bstep (se 2 (by rfl) ⟨179379, by rfl⟩ : syracuseStep 478345 = 358759) B358759
theorem B1658153 : Blo 187803 1658153 := bstep (se 2 (by rfl) ⟨621807, by rfl⟩ : syracuseStep 1658153 = 1243615) B1243615
theorem B479143 : Blo 187803 479143 := bstep (se 1 (by rfl) ⟨359357, by rfl⟩ : syracuseStep 479143 = 718715) B718715
theorem B282761 : Blo 187803 282761 := bstep (se 2 (by rfl) ⟨106035, by rfl⟩ : syracuseStep 282761 = 212071) B212071
theorem B1495385 : Blo 187803 1495385 := bstep (se 2 (by rfl) ⟨560769, by rfl⟩ : syracuseStep 1495385 = 1121539) B1121539
theorem B807671 : Blo 187803 807671 := bstep (se 1 (by rfl) ⟨605753, by rfl⟩ : syracuseStep 807671 = 1211507) B1211507
theorem B283391 : Blo 187803 283391 := bstep (se 1 (by rfl) ⟨212543, by rfl⟩ : syracuseStep 283391 = 425087) B425087
theorem B40555363 : Blo 187803 40555363 := bstep (se 1 (by rfl) ⟨30416522, by rfl⟩ : syracuseStep 40555363 = 60833045) B60833045
theorem B644543 : Blo 187803 644543 := bstep (se 1 (by rfl) ⟨483407, by rfl⟩ : syracuseStep 644543 = 966815) B966815
theorem B284111 : Blo 187803 284111 := bstep (se 1 (by rfl) ⟨213083, by rfl⟩ : syracuseStep 284111 = 426167) B426167
theorem B874127 : Blo 187803 874127 := bstep (se 1 (by rfl) ⟨655595, by rfl⟩ : syracuseStep 874127 = 1311191) B1311191
theorem B285065 : Blo 187803 285065 := bstep (se 2 (by rfl) ⟨106899, by rfl⟩ : syracuseStep 285065 = 213799) B213799
theorem B383401 : Blo 187803 383401 := bstep (se 2 (by rfl) ⟨143775, by rfl⟩ : syracuseStep 383401 = 287551) B287551
theorem B3529207 : Blo 187803 3529207 := bstep (se 1 (by rfl) ⟨2646905, by rfl⟩ : syracuseStep 3529207 = 5293811) B5293811
theorem B285863 : Blo 187803 285863 := bstep (se 1 (by rfl) ⟨214397, by rfl⟩ : syracuseStep 285863 = 428795) B428795
theorem B1072541 : Blo 187803 1072541 := bstep (se 3 (by rfl) ⟨201101, by rfl⟩ : syracuseStep 1072541 = 402203) B402203
theorem B187951 : Blo 187803 187951 := bstep (se 1 (by rfl) ⟨140963, by rfl⟩ : syracuseStep 187951 = 281927) B281927
theorem B188059 : Blo 187803 188059 := bstep (se 1 (by rfl) ⟨141044, by rfl⟩ : syracuseStep 188059 = 282089) B282089
theorem B188095 : Blo 187803 188095 := bstep (se 1 (by rfl) ⟨141071, by rfl⟩ : syracuseStep 188095 = 282143) B282143
theorem B7855825 : Blo 187803 7855825 := bstep (se 2 (by rfl) ⟨2945934, by rfl⟩ : syracuseStep 7855825 = 5891869) B5891869
theorem B188223 : Blo 187803 188223 := bstep (se 1 (by rfl) ⟨141167, by rfl⟩ : syracuseStep 188223 = 282335) B282335
theorem B319295 : Blo 187803 319295 := bstep (se 1 (by rfl) ⟨239471, by rfl⟩ : syracuseStep 319295 = 478943) B478943
theorem B286775 : Blo 187803 286775 := bstep (se 1 (by rfl) ⟨215081, by rfl⟩ : syracuseStep 286775 = 430163) B430163
theorem B7463015 : Blo 187803 7463015 := bstep (se 1 (by rfl) ⟨5597261, by rfl⟩ : syracuseStep 7463015 = 11194523) B11194523
theorem B188543 : Blo 187803 188543 := bstep (se 1 (by rfl) ⟨141407, by rfl⟩ : syracuseStep 188543 = 282815) B282815
theorem B286847 : Blo 187803 286847 := bstep (se 1 (by rfl) ⟨215135, by rfl⟩ : syracuseStep 286847 = 430271) B430271
theorem B188575 : Blo 187803 188575 := bstep (se 1 (by rfl) ⟨141431, by rfl⟩ : syracuseStep 188575 = 282863) B282863
theorem B188639 : Blo 187803 188639 := bstep (se 1 (by rfl) ⟨141479, by rfl⟩ : syracuseStep 188639 = 282959) B282959
theorem B188863 : Blo 187803 188863 := bstep (se 1 (by rfl) ⟨141647, by rfl⟩ : syracuseStep 188863 = 283295) B283295
theorem B287369 : Blo 187803 287369 := bstep (se 2 (by rfl) ⟨107763, by rfl⟩ : syracuseStep 287369 = 215527) B215527
theorem B189167 : Blo 187803 189167 := bstep (se 1 (by rfl) ⟨141875, by rfl⟩ : syracuseStep 189167 = 283751) B283751
theorem B189179 : Blo 187803 189179 := bstep (se 1 (by rfl) ⟨141884, by rfl⟩ : syracuseStep 189179 = 283769) B283769
theorem B47539061 : Blo 187803 47539061 := bstep (se 5 (by rfl) ⟨2228393, by rfl⟩ : syracuseStep 47539061 = 4456787) B4456787
theorem B287615 : Blo 187803 287615 := bstep (se 1 (by rfl) ⟨215711, by rfl⟩ : syracuseStep 287615 = 431423) B431423
theorem B189439 : Blo 187803 189439 := bstep (se 1 (by rfl) ⟨142079, by rfl⟩ : syracuseStep 189439 = 284159) B284159
theorem B189471 : Blo 187803 189471 := bstep (se 1 (by rfl) ⟨142103, by rfl⟩ : syracuseStep 189471 = 284207) B284207
theorem B189723 : Blo 187803 189723 := bstep (se 1 (by rfl) ⟨142292, by rfl⟩ : syracuseStep 189723 = 284585) B284585
theorem B3761639 : Blo 187803 3761639 := bstep (se 1 (by rfl) ⟨2821229, by rfl⟩ : syracuseStep 3761639 = 5642459) B5642459
theorem B714815 : Blo 187803 714815 := bstep (se 1 (by rfl) ⟨536111, by rfl⟩ : syracuseStep 714815 = 1072223) B1072223
theorem B190671 : Blo 187803 190671 := bstep (se 1 (by rfl) ⟨143003, by rfl⟩ : syracuseStep 190671 = 286007) B286007
theorem B191143 : Blo 187803 191143 := bstep (se 1 (by rfl) ⟨143357, by rfl⟩ : syracuseStep 191143 = 286715) B286715
theorem B191263 : Blo 187803 191263 := bstep (se 1 (by rfl) ⟨143447, by rfl⟩ : syracuseStep 191263 = 286895) B286895
theorem B191519 : Blo 187803 191519 := bstep (se 1 (by rfl) ⟨143639, by rfl⟩ : syracuseStep 191519 = 287279) B287279
theorem B322663 : Blo 187803 322663 := bstep (se 1 (by rfl) ⟨241997, by rfl⟩ : syracuseStep 322663 = 483995) B483995
theorem B191739 : Blo 187803 191739 := bstep (se 1 (by rfl) ⟨143804, by rfl⟩ : syracuseStep 191739 = 287609) B287609
theorem B191771 : Blo 187803 191771 := bstep (se 1 (by rfl) ⟨143828, by rfl⟩ : syracuseStep 191771 = 287657) B287657
theorem B322987 : Blo 187803 322987 := bstep (se 1 (by rfl) ⟨242240, by rfl⟩ : syracuseStep 322987 = 484481) B484481
theorem B814931 : Blo 187803 814931 := bstep (se 1 (by rfl) ⟨611198, by rfl⟩ : syracuseStep 814931 = 1222397) B1222397
theorem B2061065 : Blo 187803 2061065 := bstep (se 2 (by rfl) ⟨772899, by rfl⟩ : syracuseStep 2061065 = 1545799) B1545799
theorem B357689 : Blo 187803 357689 := bstep (se 2 (by rfl) ⟨134133, by rfl⟩ : syracuseStep 357689 = 268267) B268267
theorem B718217 : Blo 187803 718217 := bstep (se 2 (by rfl) ⟨269331, by rfl⟩ : syracuseStep 718217 = 538663) B538663
theorem B2061931 : Blo 187803 2061931 := bstep (se 1 (by rfl) ⟨1546448, by rfl⟩ : syracuseStep 2061931 = 3092897) B3092897
theorem B3307715 : Blo 187803 3307715 := bstep (se 1 (by rfl) ⟨2480786, by rfl⟩ : syracuseStep 3307715 = 4961573) B4961573
theorem B1735019 : Blo 187803 1735019 := bstep (se 1 (by rfl) ⟨1301264, by rfl⟩ : syracuseStep 1735019 = 2602529) B2602529
theorem B4815773 : Blo 187803 4815773 := bstep (se 3 (by rfl) ⟨902957, by rfl⟩ : syracuseStep 4815773 = 1805915) B1805915
theorem B1080287 : Blo 187803 1080287 := bstep (se 1 (by rfl) ⟨810215, by rfl⟩ : syracuseStep 1080287 = 1620431) B1620431
theorem B1442447 : Blo 187803 1442447 := bstep (se 1 (by rfl) ⟨1081835, by rfl⟩ : syracuseStep 1442447 = 2163671) B2163671
theorem B722591 : Blo 187803 722591 := bstep (se 1 (by rfl) ⟨541943, by rfl⟩ : syracuseStep 722591 = 1083887) B1083887
theorem B427859 : Blo 187803 427859 := bstep (se 1 (by rfl) ⟨320894, by rfl⟩ : syracuseStep 427859 = 641789) B641789
theorem B362495 : Blo 187803 362495 := bstep (se 1 (by rfl) ⟨271871, by rfl⟩ : syracuseStep 362495 = 543743) B543743
theorem B1182203 : Blo 187803 1182203 := bstep (se 1 (by rfl) ⟨886652, by rfl⟩ : syracuseStep 1182203 = 1773305) B1773305
theorem B429695 : Blo 187803 429695 := bstep (se 1 (by rfl) ⟨322271, by rfl⟩ : syracuseStep 429695 = 644543) B644543
theorem B430217 : Blo 187803 430217 := bstep (se 2 (by rfl) ⟨161331, by rfl⟩ : syracuseStep 430217 = 322663) B322663
theorem B430649 : Blo 187803 430649 := bstep (se 2 (by rfl) ⟨161493, by rfl⟩ : syracuseStep 430649 = 322987) B322987
theorem B31692707 : Blo 187803 31692707 := bstep (se 1 (by rfl) ⟨23769530, by rfl⟩ : syracuseStep 31692707 = 47539061) B47539061
theorem B727451 : Blo 187803 727451 := bstep (se 1 (by rfl) ⟨545588, by rfl⟩ : syracuseStep 727451 = 1091177) B1091177
theorem B54073817 : Blo 187803 54073817 := bstep (se 2 (by rfl) ⟨20277681, by rfl⟩ : syracuseStep 54073817 = 40555363) B40555363
theorem B727663 : Blo 187803 727663 := bstep (se 1 (by rfl) ⟨545747, by rfl⟩ : syracuseStep 727663 = 1091495) B1091495
theorem B2302451 : Blo 187803 2302451 := bstep (se 1 (by rfl) ⟨1726838, by rfl⟩ : syracuseStep 2302451 = 3453677) B3453677
theorem B238459 : Blo 187803 238459 := bstep (se 1 (by rfl) ⟨178844, by rfl⟩ : syracuseStep 238459 = 357689) B357689
theorem B271775 : Blo 187803 271775 := bstep (se 1 (by rfl) ⟨203831, by rfl⟩ : syracuseStep 271775 = 407663) B407663
theorem B2205143 : Blo 187803 2205143 := bstep (se 1 (by rfl) ⟨1653857, by rfl⟩ : syracuseStep 2205143 = 3307715) B3307715
theorem B1156679 : Blo 187803 1156679 := bstep (se 1 (by rfl) ⟨867509, by rfl⟩ : syracuseStep 1156679 = 1735019) B1735019
theorem B2435771 : Blo 187803 2435771 := bstep (se 1 (by rfl) ⟨1826828, by rfl⟩ : syracuseStep 2435771 = 3653657) B3653657
theorem B633851 : Blo 187803 633851 := bstep (se 1 (by rfl) ⟨475388, by rfl⟩ : syracuseStep 633851 = 950777) B950777
theorem B634607 : Blo 187803 634607 := bstep (se 1 (by rfl) ⟨475955, by rfl⟩ : syracuseStep 634607 = 951911) B951911
theorem B1355591 : Blo 187803 1355591 := bstep (se 1 (by rfl) ⟨1016693, by rfl⟩ : syracuseStep 1355591 = 2033387) B2033387
theorem B44478659 : Blo 187803 44478659 := bstep (se 1 (by rfl) ⟨33358994, by rfl⟩ : syracuseStep 44478659 = 66717989) B66717989
theorem B962927 : Blo 187803 962927 := bstep (se 1 (by rfl) ⟨722195, by rfl⟩ : syracuseStep 962927 = 1444391) B1444391
theorem B636281 : Blo 187803 636281 := bstep (se 2 (by rfl) ⟨238605, by rfl⟩ : syracuseStep 636281 = 477211) B477211
theorem B996923 : Blo 187803 996923 := bstep (se 1 (by rfl) ⟨747692, by rfl⟩ : syracuseStep 996923 = 1495385) B1495385
theorem B538447 : Blo 187803 538447 := bstep (se 1 (by rfl) ⟨403835, by rfl⟩ : syracuseStep 538447 = 807671) B807671
theorem B636983 : Blo 187803 636983 := bstep (se 1 (by rfl) ⟨477737, by rfl⟩ : syracuseStep 636983 = 955475) B955475
theorem B1292449 : Blo 187803 1292449 := bstep (se 2 (by rfl) ⟨484668, by rfl⟩ : syracuseStep 1292449 = 969337) B969337
theorem B637793 : Blo 187803 637793 := bstep (se 2 (by rfl) ⟨239172, by rfl⟩ : syracuseStep 637793 = 478345) B478345
theorem B212863 : Blo 187803 212863 := bstep (se 1 (by rfl) ⟨159647, by rfl⟩ : syracuseStep 212863 = 319295) B319295
theorem B638857 : Blo 187803 638857 := bstep (se 2 (by rfl) ⟨239571, by rfl⟩ : syracuseStep 638857 = 479143) B479143
theorem B574057 : Blo 187803 574057 := bstep (se 2 (by rfl) ⟨215271, by rfl⟩ : syracuseStep 574057 = 430543) B430543
theorem B967463 : Blo 187803 967463 := bstep (se 1 (by rfl) ⟨725597, by rfl⟩ : syracuseStep 967463 = 1451195) B1451195
theorem B2507759 : Blo 187803 2507759 := bstep (se 1 (by rfl) ⟨1880819, by rfl⟩ : syracuseStep 2507759 = 3761639) B3761639
theorem B967787 : Blo 187803 967787 := bstep (se 1 (by rfl) ⟨725840, by rfl⟩ : syracuseStep 967787 = 1451681) B1451681
theorem B640223 : Blo 187803 640223 := bstep (se 1 (by rfl) ⟨480167, by rfl⟩ : syracuseStep 640223 = 960335) B960335
theorem B476543 : Blo 187803 476543 := bstep (se 1 (by rfl) ⟨357407, by rfl⟩ : syracuseStep 476543 = 714815) B714815
theorem B5425127 : Blo 187803 5425127 := bstep (se 1 (by rfl) ⟨4068845, by rfl⟩ : syracuseStep 5425127 = 8137691) B8137691
theorem B543287 : Blo 187803 543287 := bstep (se 1 (by rfl) ⟨407465, by rfl⟩ : syracuseStep 543287 = 814931) B814931
theorem B511201 : Blo 187803 511201 := bstep (se 2 (by rfl) ⟨191700, by rfl⟩ : syracuseStep 511201 = 383401) B383401
theorem B281897 : Blo 187803 281897 := bstep (se 2 (by rfl) ⟨105711, by rfl⟩ : syracuseStep 281897 = 211423) B211423
theorem B4705609 : Blo 187803 4705609 := bstep (se 2 (by rfl) ⟨1764603, by rfl⟩ : syracuseStep 4705609 = 3529207) B3529207
theorem B478811 : Blo 187803 478811 := bstep (se 1 (by rfl) ⟨359108, by rfl⟩ : syracuseStep 478811 = 718217) B718217
theorem B283001 : Blo 187803 283001 := bstep (se 2 (by rfl) ⟨106125, by rfl⟩ : syracuseStep 283001 = 212251) B212251
theorem B283049 : Blo 187803 283049 := bstep (se 2 (by rfl) ⟨106143, by rfl⟩ : syracuseStep 283049 = 212287) B212287
theorem B10474433 : Blo 187803 10474433 := bstep (se 2 (by rfl) ⟨3927912, by rfl⟩ : syracuseStep 10474433 = 7855825) B7855825
theorem B513191 : Blo 187803 513191 := bstep (se 1 (by rfl) ⟨384893, by rfl⟩ : syracuseStep 513191 = 769787) B769787
theorem B808643 : Blo 187803 808643 := bstep (se 1 (by rfl) ⟨606482, by rfl⟩ : syracuseStep 808643 = 1212965) B1212965
theorem B579305 : Blo 187803 579305 := bstep (se 2 (by rfl) ⟨217239, by rfl⟩ : syracuseStep 579305 = 434479) B434479
theorem B284537 : Blo 187803 284537 := bstep (se 2 (by rfl) ⟨106701, by rfl⟩ : syracuseStep 284537 = 213403) B213403
theorem B317513 : Blo 187803 317513 := bstep (se 2 (by rfl) ⟨119067, by rfl⟩ : syracuseStep 317513 = 238135) B238135
theorem B284831 : Blo 187803 284831 := bstep (se 1 (by rfl) ⟨213623, by rfl⟩ : syracuseStep 284831 = 427247) B427247
theorem B284855 : Blo 187803 284855 := bstep (se 1 (by rfl) ⟨213641, by rfl⟩ : syracuseStep 284855 = 427283) B427283
theorem B809311 : Blo 187803 809311 := bstep (se 1 (by rfl) ⟨606983, by rfl⟩ : syracuseStep 809311 = 1213967) B1213967
theorem B645623 : Blo 187803 645623 := bstep (se 1 (by rfl) ⟨484217, by rfl⟩ : syracuseStep 645623 = 968435) B968435
theorem B49601159 : Blo 187803 49601159 := bstep (se 1 (by rfl) ⟨37200869, by rfl⟩ : syracuseStep 49601159 = 74401739) B74401739
theorem B646271 : Blo 187803 646271 := bstep (se 1 (by rfl) ⟨484703, by rfl⟩ : syracuseStep 646271 = 969407) B969407
theorem B5496173 : Blo 187803 5496173 := bstep (se 3 (by rfl) ⟨1030532, by rfl⟩ : syracuseStep 5496173 = 2061065) B2061065
theorem B1105435 : Blo 187803 1105435 := bstep (se 1 (by rfl) ⟨829076, by rfl⟩ : syracuseStep 1105435 = 1658153) B1658153
theorem B286367 : Blo 187803 286367 := bstep (se 1 (by rfl) ⟨214775, by rfl⟩ : syracuseStep 286367 = 429551) B429551
theorem B319369 : Blo 187803 319369 := bstep (se 2 (by rfl) ⟨119763, by rfl⟩ : syracuseStep 319369 = 239527) B239527
theorem B1138643 : Blo 187803 1138643 := bstep (se 1 (by rfl) ⟨853982, by rfl⟩ : syracuseStep 1138643 = 1707965) B1707965
theorem B188507 : Blo 187803 188507 := bstep (se 1 (by rfl) ⟨141380, by rfl⟩ : syracuseStep 188507 = 282761) B282761
theorem B188927 : Blo 187803 188927 := bstep (se 1 (by rfl) ⟨141695, by rfl⟩ : syracuseStep 188927 = 283391) B283391
theorem B811583 : Blo 187803 811583 := bstep (se 1 (by rfl) ⟨608687, by rfl⟩ : syracuseStep 811583 = 1217375) B1217375
theorem B287423 : Blo 187803 287423 := bstep (se 1 (by rfl) ⟨215567, by rfl⟩ : syracuseStep 287423 = 431135) B431135
theorem B287579 : Blo 187803 287579 := bstep (se 1 (by rfl) ⟨215684, by rfl⟩ : syracuseStep 287579 = 431369) B431369
theorem B189407 : Blo 187803 189407 := bstep (se 1 (by rfl) ⟨142055, by rfl⟩ : syracuseStep 189407 = 284111) B284111
theorem B1205279 : Blo 187803 1205279 := bstep (se 1 (by rfl) ⟨903959, by rfl⟩ : syracuseStep 1205279 = 1807919) B1807919
theorem B582751 : Blo 187803 582751 := bstep (se 1 (by rfl) ⟨437063, by rfl⟩ : syracuseStep 582751 = 874127) B874127
theorem B190043 : Blo 187803 190043 := bstep (se 1 (by rfl) ⟨142532, by rfl⟩ : syracuseStep 190043 = 285065) B285065
theorem B616423 : Blo 187803 616423 := bstep (se 1 (by rfl) ⟨462317, by rfl⟩ : syracuseStep 616423 = 924635) B924635
theorem B190575 : Blo 187803 190575 := bstep (se 1 (by rfl) ⟨142931, by rfl⟩ : syracuseStep 190575 = 285863) B285863
theorem B715027 : Blo 187803 715027 := bstep (se 1 (by rfl) ⟨536270, by rfl⟩ : syracuseStep 715027 = 1072541) B1072541
theorem B191183 : Blo 187803 191183 := bstep (se 1 (by rfl) ⟨143387, by rfl⟩ : syracuseStep 191183 = 286775) B286775
theorem B4975343 : Blo 187803 4975343 := bstep (se 1 (by rfl) ⟨3731507, by rfl⟩ : syracuseStep 4975343 = 7463015) B7463015
theorem B191231 : Blo 187803 191231 := bstep (se 1 (by rfl) ⟨143423, by rfl⟩ : syracuseStep 191231 = 286847) B286847
theorem B191579 : Blo 187803 191579 := bstep (se 1 (by rfl) ⟨143684, by rfl⟩ : syracuseStep 191579 = 287369) B287369
theorem B5958845 : Blo 187803 5958845 := bstep (se 3 (by rfl) ⟨1117283, by rfl⟩ : syracuseStep 5958845 = 2234567) B2234567
theorem B191743 : Blo 187803 191743 := bstep (se 1 (by rfl) ⟨143807, by rfl⟩ : syracuseStep 191743 = 287615) B287615
theorem B1142207 : Blo 187803 1142207 := bstep (se 1 (by rfl) ⟨856655, by rfl⟩ : syracuseStep 1142207 = 1713311) B1713311
theorem B551580299 : Blo 187803 551580299 := bstep (se 1 (by rfl) ⟨413685224, by rfl⟩ : syracuseStep 551580299 = 827370449) B827370449
theorem B2749241 : Blo 187803 2749241 := bstep (se 2 (by rfl) ⟨1030965, by rfl⟩ : syracuseStep 2749241 = 2061931) B2061931
theorem B2718683 : Blo 187803 2718683 := bstep (se 1 (by rfl) ⟨2039012, by rfl⟩ : syracuseStep 2718683 = 4078025) B4078025
theorem B1146095 : Blo 187803 1146095 := bstep (se 1 (by rfl) ⟨859571, by rfl⟩ : syracuseStep 1146095 = 1719143) B1719143
theorem B3210515 : Blo 187803 3210515 := bstep (se 1 (by rfl) ⟨2407886, by rfl⟩ : syracuseStep 3210515 = 4815773) B4815773
theorem B720191 : Blo 187803 720191 := bstep (se 1 (by rfl) ⟨540143, by rfl⟩ : syracuseStep 720191 = 1080287) B1080287
theorem B1671839 : Blo 187803 1671839 := bstep (se 1 (by rfl) ⟨1253879, by rfl⟩ : syracuseStep 1671839 = 2507759) B2507759
theorem B426815 : Blo 187803 426815 := bstep (se 1 (by rfl) ⟨320111, by rfl⟩ : syracuseStep 426815 = 640223) B640223
theorem B788135 : Blo 187803 788135 := bstep (se 1 (by rfl) ⟨591101, by rfl⟩ : syracuseStep 788135 = 1182203) B1182203
theorem B821897 : Blo 187803 821897 := bstep (se 2 (by rfl) ⟨308211, by rfl⟩ : syracuseStep 821897 = 616423) B616423
theorem B953369 : Blo 187803 953369 := bstep (se 2 (by rfl) ⟨357513, by rfl⟩ : syracuseStep 953369 = 715027) B715027
theorem B6982955 : Blo 187803 6982955 := bstep (se 1 (by rfl) ⟨5237216, by rfl⟩ : syracuseStep 6982955 = 10474433) B10474433
theorem B724733 : Blo 187803 724733 := bstep (se 3 (by rfl) ⟨135887, by rfl⟩ : syracuseStep 724733 = 271775) B271775
theorem B36049211 : Blo 187803 36049211 := bstep (se 1 (by rfl) ⟨27036908, by rfl⟩ : syracuseStep 36049211 = 54073817) B54073817
theorem B430415 : Blo 187803 430415 := bstep (se 1 (by rfl) ⟨322811, by rfl⟩ : syracuseStep 430415 = 645623) B645623
theorem B33067439 : Blo 187803 33067439 := bstep (se 1 (by rfl) ⟨24800579, by rfl⟩ : syracuseStep 33067439 = 49601159) B49601159
theorem B430847 : Blo 187803 430847 := bstep (se 1 (by rfl) ⟨323135, by rfl⟩ : syracuseStep 430847 = 646271) B646271
theorem B759095 : Blo 187803 759095 := bstep (se 1 (by rfl) ⟨569321, by rfl⟩ : syracuseStep 759095 = 1138643) B1138643
theorem B2726405 : Blo 187803 2726405 := bstep (se 4 (by rfl) ⟨255600, by rfl⟩ : syracuseStep 2726405 = 511201) B511201
theorem B1448765 : Blo 187803 1448765 := bstep (se 3 (by rfl) ⟨271643, by rfl⟩ : syracuseStep 1448765 = 543287) B543287
theorem B3316895 : Blo 187803 3316895 := bstep (se 1 (by rfl) ⟨2487671, by rfl⟩ : syracuseStep 3316895 = 4975343) B4975343
theorem B3972563 : Blo 187803 3972563 := bstep (se 1 (by rfl) ⟨2979422, by rfl⟩ : syracuseStep 3972563 = 5958845) B5958845
theorem B761471 : Blo 187803 761471 := bstep (se 1 (by rfl) ⟨571103, by rfl⟩ : syracuseStep 761471 = 1142207) B1142207
theorem B664615 : Blo 187803 664615 := bstep (se 1 (by rfl) ⟨498461, by rfl⟩ : syracuseStep 664615 = 996923) B996923
theorem B1812455 : Blo 187803 1812455 := bstep (se 1 (by rfl) ⟨1359341, by rfl⟩ : syracuseStep 1812455 = 2718683) B2718683
theorem B764063 : Blo 187803 764063 := bstep (se 1 (by rfl) ⟨573047, by rfl⟩ : syracuseStep 764063 = 1146095) B1146095
theorem B2140343 : Blo 187803 2140343 := bstep (se 1 (by rfl) ⟨1605257, by rfl⟩ : syracuseStep 2140343 = 3210515) B3210515
theorem B961631 : Blo 187803 961631 := bstep (se 1 (by rfl) ⟨721223, by rfl⟩ : syracuseStep 961631 = 1442447) B1442447
theorem B765409 : Blo 187803 765409 := bstep (se 2 (by rfl) ⟨287028, by rfl⟩ : syracuseStep 765409 = 574057) B574057
theorem B3616751 : Blo 187803 3616751 := bstep (se 1 (by rfl) ⟨2712563, by rfl⟩ : syracuseStep 3616751 = 5425127) B5425127
theorem B342127 : Blo 187803 342127 := bstep (se 1 (by rfl) ⟨256595, by rfl⟩ : syracuseStep 342127 = 513191) B513191
theorem B211675 : Blo 187803 211675 := bstep (se 1 (by rfl) ⟨158756, by rfl⟩ : syracuseStep 211675 = 317513) B317513
theorem B6274145 : Blo 187803 6274145 := bstep (se 2 (by rfl) ⟨2352804, by rfl⟩ : syracuseStep 6274145 = 4705609) B4705609
theorem B966653 : Blo 187803 966653 := bstep (se 3 (by rfl) ⟨181247, by rfl⟩ : syracuseStep 966653 = 362495) B362495
theorem B541055 : Blo 187803 541055 := bstep (se 1 (by rfl) ⟨405791, by rfl⟩ : syracuseStep 541055 = 811583) B811583
theorem B803519 : Blo 187803 803519 := bstep (se 1 (by rfl) ⟨602639, by rfl⟩ : syracuseStep 803519 = 1205279) B1205279
theorem B771119 : Blo 187803 771119 := bstep (se 1 (by rfl) ⟨578339, by rfl⟩ : syracuseStep 771119 = 1156679) B1156679
theorem B1623847 : Blo 187803 1623847 := bstep (se 1 (by rfl) ⟨1217885, by rfl⟩ : syracuseStep 1623847 = 2435771) B2435771
theorem B903727 : Blo 187803 903727 := bstep (se 1 (by rfl) ⟨677795, by rfl⟩ : syracuseStep 903727 = 1355591) B1355591
theorem B1723265 : Blo 187803 1723265 := bstep (se 2 (by rfl) ⟨646224, by rfl⟩ : syracuseStep 1723265 = 1292449) B1292449
theorem B641951 : Blo 187803 641951 := bstep (se 1 (by rfl) ⟨481463, by rfl⟩ : syracuseStep 641951 = 962927) B962927
theorem B970217 : Blo 187803 970217 := bstep (se 2 (by rfl) ⟨363831, by rfl⟩ : syracuseStep 970217 = 727663) B727663
theorem B480127 : Blo 187803 480127 := bstep (se 1 (by rfl) ⟨360095, by rfl⟩ : syracuseStep 480127 = 720191) B720191
theorem B283817 : Blo 187803 283817 := bstep (se 2 (by rfl) ⟨106431, by rfl⟩ : syracuseStep 283817 = 212863) B212863
theorem B644975 : Blo 187803 644975 := bstep (se 1 (by rfl) ⟨483731, by rfl⟩ : syracuseStep 644975 = 967463) B967463
theorem B645191 : Blo 187803 645191 := bstep (se 1 (by rfl) ⟨483893, by rfl⟩ : syracuseStep 645191 = 967787) B967787
theorem B317695 : Blo 187803 317695 := bstep (se 1 (by rfl) ⟨238271, by rfl⟩ : syracuseStep 317695 = 476543) B476543
theorem B481727 : Blo 187803 481727 := bstep (se 1 (by rfl) ⟨361295, by rfl⟩ : syracuseStep 481727 = 722591) B722591
theorem B317945 : Blo 187803 317945 := bstep (se 2 (by rfl) ⟨119229, by rfl⟩ : syracuseStep 317945 = 238459) B238459
theorem B285239 : Blo 187803 285239 := bstep (se 1 (by rfl) ⟨213929, by rfl⟩ : syracuseStep 285239 = 427859) B427859
theorem B777001 : Blo 187803 777001 := bstep (se 2 (by rfl) ⟨291375, by rfl⟩ : syracuseStep 777001 = 582751) B582751
theorem B187931 : Blo 187803 187931 := bstep (se 1 (by rfl) ⟨140948, by rfl⟩ : syracuseStep 187931 = 281897) B281897
theorem B319207 : Blo 187803 319207 := bstep (se 1 (by rfl) ⟨239405, by rfl⟩ : syracuseStep 319207 = 478811) B478811
theorem B286463 : Blo 187803 286463 := bstep (se 1 (by rfl) ⟨214847, by rfl⟩ : syracuseStep 286463 = 429695) B429695
theorem B286811 : Blo 187803 286811 := bstep (se 1 (by rfl) ⟨215108, by rfl⟩ : syracuseStep 286811 = 430217) B430217
theorem B188667 : Blo 187803 188667 := bstep (se 1 (by rfl) ⟨141500, by rfl⟩ : syracuseStep 188667 = 283001) B283001
theorem B188699 : Blo 187803 188699 := bstep (se 1 (by rfl) ⟨141524, by rfl⟩ : syracuseStep 188699 = 283049) B283049
theorem B287099 : Blo 187803 287099 := bstep (se 1 (by rfl) ⟨215324, by rfl⟩ : syracuseStep 287099 = 430649) B430649
theorem B386203 : Blo 187803 386203 := bstep (se 1 (by rfl) ⟨289652, by rfl⟩ : syracuseStep 386203 = 579305) B579305
theorem B189691 : Blo 187803 189691 := bstep (se 1 (by rfl) ⟨142268, by rfl⟩ : syracuseStep 189691 = 284537) B284537
theorem B21128471 : Blo 187803 21128471 := bstep (se 1 (by rfl) ⟨15846353, by rfl⟩ : syracuseStep 21128471 = 31692707) B31692707
theorem B189887 : Blo 187803 189887 := bstep (se 1 (by rfl) ⟨142415, by rfl⟩ : syracuseStep 189887 = 284831) B284831
theorem B189903 : Blo 187803 189903 := bstep (se 1 (by rfl) ⟨142427, by rfl⟩ : syracuseStep 189903 = 284855) B284855
theorem B484967 : Blo 187803 484967 := bstep (se 1 (by rfl) ⟨363725, by rfl⟩ : syracuseStep 484967 = 727451) B727451
theorem B2156381 : Blo 187803 2156381 := bstep (se 3 (by rfl) ⟨404321, by rfl⟩ : syracuseStep 2156381 = 808643) B808643
theorem B3664115 : Blo 187803 3664115 := bstep (se 1 (by rfl) ⟨2748086, by rfl⟩ : syracuseStep 3664115 = 5496173) B5496173
theorem B190911 : Blo 187803 190911 := bstep (se 1 (by rfl) ⟨143183, by rfl⟩ : syracuseStep 190911 = 286367) B286367
theorem B1534967 : Blo 187803 1534967 := bstep (se 1 (by rfl) ⟨1151225, by rfl⟩ : syracuseStep 1534967 = 2302451) B2302451
theorem B191615 : Blo 187803 191615 := bstep (se 1 (by rfl) ⟨143711, by rfl⟩ : syracuseStep 191615 = 287423) B287423
theorem B191719 : Blo 187803 191719 := bstep (se 1 (by rfl) ⟨143789, by rfl⟩ : syracuseStep 191719 = 287579) B287579
theorem B1470095 : Blo 187803 1470095 := bstep (se 1 (by rfl) ⟨1102571, by rfl⟩ : syracuseStep 1470095 = 2205143) B2205143
theorem B422567 : Blo 187803 422567 := bstep (se 1 (by rfl) ⟨316925, by rfl⟩ : syracuseStep 422567 = 633851) B633851
theorem B717929 : Blo 187803 717929 := bstep (se 2 (by rfl) ⟨269223, by rfl⟩ : syracuseStep 717929 = 538447) B538447
theorem B423071 : Blo 187803 423071 := bstep (se 1 (by rfl) ⟨317303, by rfl⟩ : syracuseStep 423071 = 634607) B634607
theorem B29652439 : Blo 187803 29652439 := bstep (se 1 (by rfl) ⟨22239329, by rfl⟩ : syracuseStep 29652439 = 44478659) B44478659
theorem B367720199 : Blo 187803 367720199 := bstep (se 1 (by rfl) ⟨275790149, by rfl⟩ : syracuseStep 367720199 = 551580299) B551580299
theorem B1079081 : Blo 187803 1079081 := bstep (se 2 (by rfl) ⟨404655, by rfl⟩ : syracuseStep 1079081 = 809311) B809311
theorem B1832827 : Blo 187803 1832827 := bstep (se 1 (by rfl) ⟨1374620, by rfl⟩ : syracuseStep 1832827 = 2749241) B2749241
theorem B424187 : Blo 187803 424187 := bstep (se 1 (by rfl) ⟨318140, by rfl⟩ : syracuseStep 424187 = 636281) B636281
theorem B424655 : Blo 187803 424655 := bstep (se 1 (by rfl) ⟨318491, by rfl⟩ : syracuseStep 424655 = 636983) B636983
theorem B425195 : Blo 187803 425195 := bstep (se 1 (by rfl) ⟨318896, by rfl⟩ : syracuseStep 425195 = 637793) B637793
theorem B1473913 : Blo 187803 1473913 := bstep (se 2 (by rfl) ⟨552717, by rfl⟩ : syracuseStep 1473913 = 1105435) B1105435
theorem B425825 : Blo 187803 425825 := bstep (se 2 (by rfl) ⟨159684, by rfl⟩ : syracuseStep 425825 = 319369) B319369
theorem B851809 : Blo 187803 851809 := bstep (se 2 (by rfl) ⟨319428, by rfl⟩ : syracuseStep 851809 = 638857) B638857
theorem B360703 : Blo 187803 360703 := bstep (se 1 (by rfl) ⟨270527, by rfl⟩ : syracuseStep 360703 = 541055) B541055
theorem B1114559 : Blo 187803 1114559 := bstep (se 1 (by rfl) ⟨835919, by rfl⟩ : syracuseStep 1114559 = 1671839) B1671839
theorem B886153 : Blo 187803 886153 := bstep (se 2 (by rfl) ⟨332307, by rfl⟩ : syracuseStep 886153 = 664615) B664615
theorem B1148843 : Blo 187803 1148843 := bstep (se 1 (by rfl) ⟨861632, by rfl⟩ : syracuseStep 1148843 = 1723265) B1723265
theorem B427967 : Blo 187803 427967 := bstep (se 1 (by rfl) ⟨320975, by rfl⟩ : syracuseStep 427967 = 641951) B641951
theorem B4655303 : Blo 187803 4655303 := bstep (se 1 (by rfl) ⟨3491477, by rfl⟩ : syracuseStep 4655303 = 6982955) B6982955
theorem B2165129 : Blo 187803 2165129 := bstep (se 2 (by rfl) ⟨811923, by rfl⟩ : syracuseStep 2165129 = 1623847) B1623847
theorem B429983 : Blo 187803 429983 := bstep (se 1 (by rfl) ⟨322487, by rfl⟩ : syracuseStep 429983 = 644975) B644975
theorem B430127 : Blo 187803 430127 := bstep (se 1 (by rfl) ⟨322595, by rfl⟩ : syracuseStep 430127 = 645191) B645191
theorem B1020545 : Blo 187803 1020545 := bstep (se 2 (by rfl) ⟨382704, by rfl⟩ : syracuseStep 1020545 = 765409) B765409
theorem B1023311 : Blo 187803 1023311 := bstep (se 1 (by rfl) ⟨767483, by rfl⟩ : syracuseStep 1023311 = 1534967) B1534967
theorem B245146799 : Blo 187803 245146799 := bstep (se 1 (by rfl) ⟨183860099, by rfl⟩ : syracuseStep 245146799 = 367720199) B367720199
theorem B535679 : Blo 187803 535679 := bstep (se 1 (by rfl) ⟨401759, by rfl⟩ : syracuseStep 535679 = 803519) B803519
theorem B635579 : Blo 187803 635579 := bstep (se 1 (by rfl) ⟨476684, by rfl⟩ : syracuseStep 635579 = 953369) B953369
theorem B24032807 : Blo 187803 24032807 := bstep (se 1 (by rfl) ⟨18024605, by rfl⟩ : syracuseStep 24032807 = 36049211) B36049211
theorem B506063 : Blo 187803 506063 := bstep (se 1 (by rfl) ⟨379547, by rfl⟩ : syracuseStep 506063 = 759095) B759095
theorem B211963 : Blo 187803 211963 := bstep (se 1 (by rfl) ⟨158972, by rfl⟩ : syracuseStep 211963 = 317945) B317945
theorem B1817603 : Blo 187803 1817603 := bstep (se 1 (by rfl) ⟨1363202, by rfl⟩ : syracuseStep 1817603 = 2726405) B2726405
theorem B965843 : Blo 187803 965843 := bstep (se 1 (by rfl) ⟨724382, by rfl⟩ : syracuseStep 965843 = 1448765) B1448765
theorem B2211263 : Blo 187803 2211263 := bstep (se 1 (by rfl) ⟨1658447, by rfl⟩ : syracuseStep 2211263 = 3316895) B3316895
theorem B507647 : Blo 187803 507647 := bstep (se 1 (by rfl) ⟨380735, by rfl⟩ : syracuseStep 507647 = 761471) B761471
theorem B640169 : Blo 187803 640169 := bstep (se 2 (by rfl) ⟨240063, by rfl⟩ : syracuseStep 640169 = 480127) B480127
theorem B509375 : Blo 187803 509375 := bstep (se 1 (by rfl) ⟨382031, by rfl⟩ : syracuseStep 509375 = 764063) B764063
theorem B1426895 : Blo 187803 1426895 := bstep (se 1 (by rfl) ⟨1070171, by rfl⟩ : syracuseStep 1426895 = 2140343) B2140343
theorem B2442743 : Blo 187803 2442743 := bstep (se 1 (by rfl) ⟨1832057, by rfl⟩ : syracuseStep 2442743 = 3664115) B3664115
theorem B8406773 : Blo 187803 8406773 := bstep (se 5 (by rfl) ⟨394067, by rfl⟩ : syracuseStep 8406773 = 788135) B788135
theorem B39536585 : Blo 187803 39536585 := bstep (se 2 (by rfl) ⟨14826219, by rfl⟩ : syracuseStep 39536585 = 29652439) B29652439
theorem B641087 : Blo 187803 641087 := bstep (se 1 (by rfl) ⟨480815, by rfl⟩ : syracuseStep 641087 = 961631) B961631
theorem B2443769 : Blo 187803 2443769 := bstep (se 2 (by rfl) ⟨916413, by rfl⟩ : syracuseStep 2443769 = 1832827) B1832827
theorem B2411167 : Blo 187803 2411167 := bstep (se 1 (by rfl) ⟨1808375, by rfl⟩ : syracuseStep 2411167 = 3616751) B3616751
theorem B281711 : Blo 187803 281711 := bstep (se 1 (by rfl) ⟨211283, by rfl⟩ : syracuseStep 281711 = 422567) B422567
theorem B478619 : Blo 187803 478619 := bstep (se 1 (by rfl) ⟨358964, by rfl⟩ : syracuseStep 478619 = 717929) B717929
theorem B282047 : Blo 187803 282047 := bstep (se 1 (by rfl) ⟨211535, by rfl⟩ : syracuseStep 282047 = 423071) B423071
theorem B282233 : Blo 187803 282233 := bstep (se 2 (by rfl) ⟨105837, by rfl⟩ : syracuseStep 282233 = 211675) B211675
theorem B1036001 : Blo 187803 1036001 := bstep (se 2 (by rfl) ⟨388500, by rfl⟩ : syracuseStep 1036001 = 777001) B777001
theorem B282791 : Blo 187803 282791 := bstep (se 1 (by rfl) ⟨212093, by rfl⟩ : syracuseStep 282791 = 424187) B424187
theorem B283103 : Blo 187803 283103 := bstep (se 1 (by rfl) ⟨212327, by rfl⟩ : syracuseStep 283103 = 424655) B424655
theorem B4182763 : Blo 187803 4182763 := bstep (se 1 (by rfl) ⟨3137072, by rfl⟩ : syracuseStep 4182763 = 6274145) B6274145
theorem B283463 : Blo 187803 283463 := bstep (se 1 (by rfl) ⟨212597, by rfl⟩ : syracuseStep 283463 = 425195) B425195
theorem B1135745 : Blo 187803 1135745 := bstep (se 2 (by rfl) ⟨425904, by rfl⟩ : syracuseStep 1135745 = 851809) B851809
theorem B283883 : Blo 187803 283883 := bstep (se 1 (by rfl) ⟨212912, by rfl⟩ : syracuseStep 283883 = 425825) B425825
theorem B644435 : Blo 187803 644435 := bstep (se 1 (by rfl) ⟨483326, by rfl⟩ : syracuseStep 644435 = 966653) B966653
theorem B284543 : Blo 187803 284543 := bstep (se 1 (by rfl) ⟨213407, by rfl⟩ : syracuseStep 284543 = 426815) B426815
theorem B1824677 : Blo 187803 1824677 := bstep (se 4 (by rfl) ⟨171063, by rfl⟩ : syracuseStep 1824677 = 342127) B342127
theorem B514079 : Blo 187803 514079 := bstep (se 1 (by rfl) ⟨385559, by rfl⟩ : syracuseStep 514079 = 771119) B771119
theorem B514937 : Blo 187803 514937 := bstep (se 2 (by rfl) ⟨193101, by rfl⟩ : syracuseStep 514937 = 386203) B386203
theorem B547931 : Blo 187803 547931 := bstep (se 1 (by rfl) ⟨410948, by rfl⟩ : syracuseStep 547931 = 821897) B821897
theorem B646811 : Blo 187803 646811 := bstep (se 1 (by rfl) ⟨485108, by rfl⟩ : syracuseStep 646811 = 970217) B970217
theorem B483155 : Blo 187803 483155 := bstep (se 1 (by rfl) ⟨362366, by rfl⟩ : syracuseStep 483155 = 724733) B724733
theorem B286943 : Blo 187803 286943 := bstep (se 1 (by rfl) ⟨215207, by rfl⟩ : syracuseStep 286943 = 430415) B430415
theorem B22044959 : Blo 187803 22044959 := bstep (se 1 (by rfl) ⟨16533719, by rfl⟩ : syracuseStep 22044959 = 33067439) B33067439
theorem B287231 : Blo 187803 287231 := bstep (se 1 (by rfl) ⟨215423, by rfl⟩ : syracuseStep 287231 = 430847) B430847
theorem B1204969 : Blo 187803 1204969 := bstep (se 2 (by rfl) ⟨451863, by rfl⟩ : syracuseStep 1204969 = 903727) B903727
theorem B189211 : Blo 187803 189211 := bstep (se 1 (by rfl) ⟨141908, by rfl⟩ : syracuseStep 189211 = 283817) B283817
theorem B321151 : Blo 187803 321151 := bstep (se 1 (by rfl) ⟨240863, by rfl⟩ : syracuseStep 321151 = 481727) B481727
theorem B190159 : Blo 187803 190159 := bstep (se 1 (by rfl) ⟨142619, by rfl⟩ : syracuseStep 190159 = 285239) B285239
theorem B2648375 : Blo 187803 2648375 := bstep (se 1 (by rfl) ⟨1986281, by rfl⟩ : syracuseStep 2648375 = 3972563) B3972563
theorem B190975 : Blo 187803 190975 := bstep (se 1 (by rfl) ⟨143231, by rfl⟩ : syracuseStep 190975 = 286463) B286463
theorem B191207 : Blo 187803 191207 := bstep (se 1 (by rfl) ⟨143405, by rfl⟩ : syracuseStep 191207 = 286811) B286811
theorem B191399 : Blo 187803 191399 := bstep (se 1 (by rfl) ⟨143549, by rfl⟩ : syracuseStep 191399 = 287099) B287099
theorem B14085647 : Blo 187803 14085647 := bstep (se 1 (by rfl) ⟨10564235, by rfl⟩ : syracuseStep 14085647 = 21128471) B21128471
theorem B323311 : Blo 187803 323311 := bstep (se 1 (by rfl) ⟨242483, by rfl⟩ : syracuseStep 323311 = 484967) B484967
theorem B1437587 : Blo 187803 1437587 := bstep (se 1 (by rfl) ⟨1078190, by rfl⟩ : syracuseStep 1437587 = 2156381) B2156381
theorem B1208303 : Blo 187803 1208303 := bstep (se 1 (by rfl) ⟨906227, by rfl⟩ : syracuseStep 1208303 = 1812455) B1812455
theorem B980063 : Blo 187803 980063 := bstep (se 1 (by rfl) ⟨735047, by rfl⟩ : syracuseStep 980063 = 1470095) B1470095
theorem B423593 : Blo 187803 423593 := bstep (se 2 (by rfl) ⟨158847, by rfl⟩ : syracuseStep 423593 = 317695) B317695
theorem B719387 : Blo 187803 719387 := bstep (se 1 (by rfl) ⟨539540, by rfl⟩ : syracuseStep 719387 = 1079081) B1079081
theorem B1965217 : Blo 187803 1965217 := bstep (se 2 (by rfl) ⟨736956, by rfl⟩ : syracuseStep 1965217 = 1473913) B1473913
theorem B425609 : Blo 187803 425609 := bstep (se 2 (by rfl) ⟨159603, by rfl⟩ : syracuseStep 425609 = 319207) B319207
theorem B426779 : Blo 187803 426779 := bstep (se 1 (by rfl) ⟨320084, by rfl⟩ : syracuseStep 426779 = 640169) B640169
theorem B951263 : Blo 187803 951263 := bstep (se 1 (by rfl) ⟨713447, by rfl⟩ : syracuseStep 951263 = 1426895) B1426895
theorem B1606625 : Blo 187803 1606625 := bstep (se 2 (by rfl) ⟨602484, by rfl⟩ : syracuseStep 1606625 = 1204969) B1204969
theorem B5604515 : Blo 187803 5604515 := bstep (se 1 (by rfl) ⟨4203386, by rfl⟩ : syracuseStep 5604515 = 8406773) B8406773
theorem B427391 : Blo 187803 427391 := bstep (se 1 (by rfl) ⟨320543, by rfl⟩ : syracuseStep 427391 = 641087) B641087
theorem B1443419 : Blo 187803 1443419 := bstep (se 1 (by rfl) ⟨1082564, by rfl⟩ : syracuseStep 1443419 = 2165129) B2165129
theorem B1181537 : Blo 187803 1181537 := bstep (se 2 (by rfl) ⟨443076, by rfl⟩ : syracuseStep 1181537 = 886153) B886153
theorem B428201 : Blo 187803 428201 := bstep (se 2 (by rfl) ⟨160575, by rfl⟩ : syracuseStep 428201 = 321151) B321151
theorem B3214889 : Blo 187803 3214889 := bstep (se 2 (by rfl) ⟨1205583, by rfl⟩ : syracuseStep 3214889 = 2411167) B2411167
theorem B429623 : Blo 187803 429623 := bstep (se 1 (by rfl) ⟨322217, by rfl⟩ : syracuseStep 429623 = 644435) B644435
theorem B1216451 : Blo 187803 1216451 := bstep (se 1 (by rfl) ⟨912338, by rfl⟩ : syracuseStep 1216451 = 1824677) B1824677
theorem B431081 : Blo 187803 431081 := bstep (se 2 (by rfl) ⟨161655, by rfl⟩ : syracuseStep 431081 = 323311) B323311
theorem B431207 : Blo 187803 431207 := bstep (se 1 (by rfl) ⟨323405, by rfl⟩ : syracuseStep 431207 = 646811) B646811
theorem B5577017 : Blo 187803 5577017 := bstep (se 2 (by rfl) ⟨2091381, by rfl⟩ : syracuseStep 5577017 = 4182763) B4182763
theorem B958391 : Blo 187803 958391 := bstep (se 1 (by rfl) ⟨718793, by rfl⟩ : syracuseStep 958391 = 1437587) B1437587
theorem B2728829 : Blo 187803 2728829 := bstep (se 3 (by rfl) ⟨511655, by rfl⟩ : syracuseStep 2728829 = 1023311) B1023311
theorem B337375 : Blo 187803 337375 := bstep (se 1 (by rfl) ⟨253031, by rfl⟩ : syracuseStep 337375 = 506063) B506063
theorem B2762669 : Blo 187803 2762669 := bstep (se 3 (by rfl) ⟨518000, by rfl⟩ : syracuseStep 2762669 = 1036001) B1036001
theorem B338431 : Blo 187803 338431 := bstep (se 1 (by rfl) ⟨253823, by rfl⟩ : syracuseStep 338431 = 507647) B507647
theorem B765895 : Blo 187803 765895 := bstep (se 1 (by rfl) ⟨574421, by rfl⟩ : syracuseStep 765895 = 1148843) B1148843
theorem B26357723 : Blo 187803 26357723 := bstep (se 1 (by rfl) ⟨19768292, by rfl⟩ : syracuseStep 26357723 = 39536585) B39536585
theorem B1358333 : Blo 187803 1358333 := bstep (se 3 (by rfl) ⟨254687, by rfl⟩ : syracuseStep 1358333 = 509375) B509375
theorem B342719 : Blo 187803 342719 := bstep (se 1 (by rfl) ⟨257039, by rfl⟩ : syracuseStep 342719 = 514079) B514079
theorem B343291 : Blo 187803 343291 := bstep (se 1 (by rfl) ⟨257468, by rfl⟩ : syracuseStep 343291 = 514937) B514937
theorem B14696639 : Blo 187803 14696639 := bstep (se 1 (by rfl) ⟨11022479, by rfl⟩ : syracuseStep 14696639 = 22044959) B22044959
theorem B163431199 : Blo 187803 163431199 := bstep (se 1 (by rfl) ⟨122573399, by rfl⟩ : syracuseStep 163431199 = 245146799) B245146799
theorem B9390431 : Blo 187803 9390431 := bstep (se 1 (by rfl) ⟨7042823, by rfl⟩ : syracuseStep 9390431 = 14085647) B14085647
theorem B805535 : Blo 187803 805535 := bstep (se 1 (by rfl) ⟨604151, by rfl⟩ : syracuseStep 805535 = 1208303) B1208303
theorem B1461149 : Blo 187803 1461149 := bstep (se 3 (by rfl) ⟨273965, by rfl⟩ : syracuseStep 1461149 = 547931) B547931
theorem B282395 : Blo 187803 282395 := bstep (se 1 (by rfl) ⟨211796, by rfl⟩ : syracuseStep 282395 = 423593) B423593
theorem B282617 : Blo 187803 282617 := bstep (se 2 (by rfl) ⟨105981, by rfl⟩ : syracuseStep 282617 = 211963) B211963
theorem B479591 : Blo 187803 479591 := bstep (se 1 (by rfl) ⟨359693, by rfl⟩ : syracuseStep 479591 = 719387) B719387
theorem B643895 : Blo 187803 643895 := bstep (se 1 (by rfl) ⟨482921, by rfl⟩ : syracuseStep 643895 = 965843) B965843
theorem B283739 : Blo 187803 283739 := bstep (se 1 (by rfl) ⟨212804, by rfl⟩ : syracuseStep 283739 = 425609) B425609
theorem B743039 : Blo 187803 743039 := bstep (se 1 (by rfl) ⟨557279, by rfl⟩ : syracuseStep 743039 = 1114559) B1114559
theorem B480937 : Blo 187803 480937 := bstep (se 2 (by rfl) ⟨180351, by rfl⟩ : syracuseStep 480937 = 360703) B360703
theorem B1628495 : Blo 187803 1628495 := bstep (se 1 (by rfl) ⟨1221371, by rfl⟩ : syracuseStep 1628495 = 2442743) B2442743
theorem B285311 : Blo 187803 285311 := bstep (se 1 (by rfl) ⟨213983, by rfl⟩ : syracuseStep 285311 = 427967) B427967
theorem B12114613 : Blo 187803 12114613 := bstep (se 5 (by rfl) ⟨567872, by rfl⟩ : syracuseStep 12114613 = 1135745) B1135745
theorem B3103535 : Blo 187803 3103535 := bstep (se 1 (by rfl) ⟨2327651, by rfl⟩ : syracuseStep 3103535 = 4655303) B4655303
theorem B1629179 : Blo 187803 1629179 := bstep (se 1 (by rfl) ⟨1221884, by rfl⟩ : syracuseStep 1629179 = 2443769) B2443769
theorem B187807 : Blo 187803 187807 := bstep (se 1 (by rfl) ⟨140855, by rfl⟩ : syracuseStep 187807 = 281711) B281711
theorem B319079 : Blo 187803 319079 := bstep (se 1 (by rfl) ⟨239309, by rfl⟩ : syracuseStep 319079 = 478619) B478619
theorem B188031 : Blo 187803 188031 := bstep (se 1 (by rfl) ⟨141023, by rfl⟩ : syracuseStep 188031 = 282047) B282047
theorem B188155 : Blo 187803 188155 := bstep (se 1 (by rfl) ⟨141116, by rfl⟩ : syracuseStep 188155 = 282233) B282233
theorem B286655 : Blo 187803 286655 := bstep (se 1 (by rfl) ⟨214991, by rfl⟩ : syracuseStep 286655 = 429983) B429983
theorem B286751 : Blo 187803 286751 := bstep (se 1 (by rfl) ⟨215063, by rfl⟩ : syracuseStep 286751 = 430127) B430127
theorem B188527 : Blo 187803 188527 := bstep (se 1 (by rfl) ⟨141395, by rfl⟩ : syracuseStep 188527 = 282791) B282791
theorem B188735 : Blo 187803 188735 := bstep (se 1 (by rfl) ⟨141551, by rfl⟩ : syracuseStep 188735 = 283103) B283103
theorem B680363 : Blo 187803 680363 := bstep (se 1 (by rfl) ⟨510272, by rfl⟩ : syracuseStep 680363 = 1020545) B1020545
theorem B188975 : Blo 187803 188975 := bstep (se 1 (by rfl) ⟨141731, by rfl⟩ : syracuseStep 188975 = 283463) B283463
theorem B189255 : Blo 187803 189255 := bstep (se 1 (by rfl) ⟨141941, by rfl⟩ : syracuseStep 189255 = 283883) B283883
theorem B189695 : Blo 187803 189695 := bstep (se 1 (by rfl) ⟨142271, by rfl⟩ : syracuseStep 189695 = 284543) B284543
theorem B322103 : Blo 187803 322103 := bstep (se 1 (by rfl) ⟨241577, by rfl⟩ : syracuseStep 322103 = 483155) B483155
theorem B191295 : Blo 187803 191295 := bstep (se 1 (by rfl) ⟨143471, by rfl⟩ : syracuseStep 191295 = 286943) B286943
theorem B191487 : Blo 187803 191487 := bstep (se 1 (by rfl) ⟨143615, by rfl⟩ : syracuseStep 191487 = 287231) B287231
theorem B1765583 : Blo 187803 1765583 := bstep (se 1 (by rfl) ⟨1324187, by rfl⟩ : syracuseStep 1765583 = 2648375) B2648375
theorem B357119 : Blo 187803 357119 := bstep (se 1 (by rfl) ⟨267839, by rfl⟩ : syracuseStep 357119 = 535679) B535679
theorem B423719 : Blo 187803 423719 := bstep (se 1 (by rfl) ⟨317789, by rfl⟩ : syracuseStep 423719 = 635579) B635579
theorem B653375 : Blo 187803 653375 := bstep (se 1 (by rfl) ⟨490031, by rfl⟩ : syracuseStep 653375 = 980063) B980063
theorem B16021871 : Blo 187803 16021871 := bstep (se 1 (by rfl) ⟨12016403, by rfl⟩ : syracuseStep 16021871 = 24032807) B24032807
theorem B2620289 : Blo 187803 2620289 := bstep (se 2 (by rfl) ⟨982608, by rfl⟩ : syracuseStep 2620289 = 1965217) B1965217
theorem B1211735 : Blo 187803 1211735 := bstep (se 1 (by rfl) ⟨908801, by rfl⟩ : syracuseStep 1211735 = 1817603) B1817603
theorem B1474175 : Blo 187803 1474175 := bstep (se 1 (by rfl) ⟨1105631, by rfl⟩ : syracuseStep 1474175 = 2211263) B2211263
theorem B9797759 : Blo 187803 9797759 := bstep (se 1 (by rfl) ⟨7348319, by rfl⟩ : syracuseStep 9797759 = 14696639) B14696639
theorem B3736343 : Blo 187803 3736343 := bstep (se 1 (by rfl) ⟨2802257, by rfl⟩ : syracuseStep 3736343 = 5604515) B5604515
theorem B217908265 : Blo 187803 217908265 := bstep (se 2 (by rfl) ⟨81715599, by rfl⟩ : syracuseStep 217908265 = 163431199) B163431199
theorem B787691 : Blo 187803 787691 := bstep (se 1 (by rfl) ⟨590768, by rfl⟩ : syracuseStep 787691 = 1181537) B1181537
theorem B6260287 : Blo 187803 6260287 := bstep (se 1 (by rfl) ⟨4695215, by rfl⟩ : syracuseStep 6260287 = 9390431) B9390431
theorem B429263 : Blo 187803 429263 := bstep (se 1 (by rfl) ⟨321947, by rfl⟩ : syracuseStep 429263 = 643895) B643895
theorem B495359 : Blo 187803 495359 := bstep (se 1 (by rfl) ⟨371519, by rfl⟩ : syracuseStep 495359 = 743039) B743039
theorem B1085663 : Blo 187803 1085663 := bstep (se 1 (by rfl) ⟨814247, by rfl⟩ : syracuseStep 1085663 = 1628495) B1628495
theorem B2069023 : Blo 187803 2069023 := bstep (se 1 (by rfl) ⟨1551767, by rfl⟩ : syracuseStep 2069023 = 3103535) B3103535
theorem B1086119 : Blo 187803 1086119 := bstep (se 1 (by rfl) ⟨814589, by rfl⟩ : syracuseStep 1086119 = 1629179) B1629179
theorem B1021193 : Blo 187803 1021193 := bstep (se 2 (by rfl) ⟨382947, by rfl⟩ : syracuseStep 1021193 = 765895) B765895
theorem B1841779 : Blo 187803 1841779 := bstep (se 1 (by rfl) ⟨1381334, by rfl⟩ : syracuseStep 1841779 = 2762669) B2762669
theorem B17571815 : Blo 187803 17571815 := bstep (se 1 (by rfl) ⟨13178861, by rfl⟩ : syracuseStep 17571815 = 26357723) B26357723
theorem B238079 : Blo 187803 238079 := bstep (se 1 (by rfl) ⟨178559, by rfl⟩ : syracuseStep 238079 = 357119) B357119
theorem B435583 : Blo 187803 435583 := bstep (se 1 (by rfl) ⟨326687, by rfl⟩ : syracuseStep 435583 = 653375) B653375
theorem B1746859 : Blo 187803 1746859 := bstep (se 1 (by rfl) ⟨1310144, by rfl⟩ : syracuseStep 1746859 = 2620289) B2620289
theorem B634175 : Blo 187803 634175 := bstep (se 1 (by rfl) ⟨475631, by rfl⟩ : syracuseStep 634175 = 951263) B951263
theorem B962279 : Blo 187803 962279 := bstep (se 1 (by rfl) ⟨721709, by rfl⟩ : syracuseStep 962279 = 1443419) B1443419
theorem B537023 : Blo 187803 537023 := bstep (se 1 (by rfl) ⟨402767, by rfl⟩ : syracuseStep 537023 = 805535) B805535
theorem B2143259 : Blo 187803 2143259 := bstep (se 1 (by rfl) ⟨1607444, by rfl⟩ : syracuseStep 2143259 = 3214889) B3214889
theorem B212719 : Blo 187803 212719 := bstep (se 1 (by rfl) ⟨159539, by rfl⟩ : syracuseStep 212719 = 319079) B319079
theorem B638927 : Blo 187803 638927 := bstep (se 1 (by rfl) ⟨479195, by rfl⟩ : syracuseStep 638927 = 958391) B958391
theorem B1819219 : Blo 187803 1819219 := bstep (se 1 (by rfl) ⟨1364414, by rfl⟩ : syracuseStep 1819219 = 2728829) B2728829
theorem B214735 : Blo 187803 214735 := bstep (se 1 (by rfl) ⟨161051, by rfl⟩ : syracuseStep 214735 = 322103) B322103
theorem B641249 : Blo 187803 641249 := bstep (se 2 (by rfl) ⟨240468, by rfl⟩ : syracuseStep 641249 = 480937) B480937
theorem B282479 : Blo 187803 282479 := bstep (se 1 (by rfl) ⟨211859, by rfl⟩ : syracuseStep 282479 = 423719) B423719
theorem B905555 : Blo 187803 905555 := bstep (se 1 (by rfl) ⟨679166, by rfl⟩ : syracuseStep 905555 = 1358333) B1358333
theorem B807823 : Blo 187803 807823 := bstep (se 1 (by rfl) ⟨605867, by rfl⟩ : syracuseStep 807823 = 1211735) B1211735
theorem B284519 : Blo 187803 284519 := bstep (se 1 (by rfl) ⟨213389, by rfl⟩ : syracuseStep 284519 = 426779) B426779
theorem B1071083 : Blo 187803 1071083 := bstep (se 1 (by rfl) ⟨803312, by rfl⟩ : syracuseStep 1071083 = 1606625) B1606625
theorem B284927 : Blo 187803 284927 := bstep (se 1 (by rfl) ⟨213695, by rfl⟩ : syracuseStep 284927 = 427391) B427391
theorem B285467 : Blo 187803 285467 := bstep (se 1 (by rfl) ⟨214100, by rfl⟩ : syracuseStep 285467 = 428201) B428201
theorem B974099 : Blo 187803 974099 := bstep (se 1 (by rfl) ⟨730574, by rfl⟩ : syracuseStep 974099 = 1461149) B1461149
theorem B286415 : Blo 187803 286415 := bstep (se 1 (by rfl) ⟨214811, by rfl⟩ : syracuseStep 286415 = 429623) B429623
theorem B188263 : Blo 187803 188263 := bstep (se 1 (by rfl) ⟨141197, by rfl⟩ : syracuseStep 188263 = 282395) B282395
theorem B810967 : Blo 187803 810967 := bstep (se 1 (by rfl) ⟨608225, by rfl⟩ : syracuseStep 810967 = 1216451) B1216451
theorem B188411 : Blo 187803 188411 := bstep (se 1 (by rfl) ⟨141308, by rfl⟩ : syracuseStep 188411 = 282617) B282617
theorem B319727 : Blo 187803 319727 := bstep (se 1 (by rfl) ⟨239795, by rfl⟩ : syracuseStep 319727 = 479591) B479591
theorem B287387 : Blo 187803 287387 := bstep (se 1 (by rfl) ⟨215540, by rfl⟩ : syracuseStep 287387 = 431081) B431081
theorem B451241 : Blo 187803 451241 := bstep (se 2 (by rfl) ⟨169215, by rfl⟩ : syracuseStep 451241 = 338431) B338431
theorem B189159 : Blo 187803 189159 := bstep (se 1 (by rfl) ⟨141869, by rfl⟩ : syracuseStep 189159 = 283739) B283739
theorem B287471 : Blo 187803 287471 := bstep (se 1 (by rfl) ⟨215603, by rfl⟩ : syracuseStep 287471 = 431207) B431207
theorem B190207 : Blo 187803 190207 := bstep (se 1 (by rfl) ⟨142655, by rfl⟩ : syracuseStep 190207 = 285311) B285311
theorem B191103 : Blo 187803 191103 := bstep (se 1 (by rfl) ⟨143327, by rfl⟩ : syracuseStep 191103 = 286655) B286655
theorem B191167 : Blo 187803 191167 := bstep (se 1 (by rfl) ⟨143375, by rfl⟩ : syracuseStep 191167 = 286751) B286751
theorem B453575 : Blo 187803 453575 := bstep (se 1 (by rfl) ⟨340181, by rfl⟩ : syracuseStep 453575 = 680363) B680363
theorem B14872045 : Blo 187803 14872045 := bstep (se 3 (by rfl) ⟨2788508, by rfl⟩ : syracuseStep 14872045 = 5577017) B5577017
theorem B1799333 : Blo 187803 1799333 := bstep (se 4 (by rfl) ⟨168687, by rfl⟩ : syracuseStep 1799333 = 337375) B337375
theorem B1177055 : Blo 187803 1177055 := bstep (se 1 (by rfl) ⟨882791, by rfl⟩ : syracuseStep 1177055 = 1765583) B1765583
theorem B16152817 : Blo 187803 16152817 := bstep (se 2 (by rfl) ⟨6057306, by rfl⟩ : syracuseStep 16152817 = 12114613) B12114613
theorem B10681247 : Blo 187803 10681247 := bstep (se 1 (by rfl) ⟨8010935, by rfl⟩ : syracuseStep 10681247 = 16021871) B16021871
theorem B457721 : Blo 187803 457721 := bstep (se 2 (by rfl) ⟨171645, by rfl⟩ : syracuseStep 457721 = 343291) B343291
theorem B228479 : Blo 187803 228479 := bstep (se 1 (by rfl) ⟨171359, by rfl⟩ : syracuseStep 228479 = 342719) B342719
theorem B982783 : Blo 187803 982783 := bstep (se 1 (by rfl) ⟨737087, by rfl⟩ : syracuseStep 982783 = 1474175) B1474175
theorem B2490895 : Blo 187803 2490895 := bstep (se 1 (by rfl) ⟨1868171, by rfl⟩ : syracuseStep 2490895 = 3736343) B3736343
theorem B2425625 : Blo 187803 2425625 := bstep (se 2 (by rfl) ⟨909609, by rfl⟩ : syracuseStep 2425625 = 1819219) B1819219
theorem B525127 : Blo 187803 525127 := bstep (se 1 (by rfl) ⟨393845, by rfl⟩ : syracuseStep 525127 = 787691) B787691
theorem B427499 : Blo 187803 427499 := bstep (se 1 (by rfl) ⟨320624, by rfl⟩ : syracuseStep 427499 = 641249) B641249
theorem B330239 : Blo 187803 330239 := bstep (se 1 (by rfl) ⟨247679, by rfl⟩ : syracuseStep 330239 = 495359) B495359
theorem B2329145 : Blo 187803 2329145 := bstep (se 2 (by rfl) ⟨873429, by rfl⟩ : syracuseStep 2329145 = 1746859) B1746859
theorem B723775 : Blo 187803 723775 := bstep (se 1 (by rfl) ⟨542831, by rfl⟩ : syracuseStep 723775 = 1085663) B1085663
theorem B724079 : Blo 187803 724079 := bstep (se 1 (by rfl) ⟨543059, by rfl⟩ : syracuseStep 724079 = 1086119) B1086119
theorem B19829393 : Blo 187803 19829393 := bstep (se 2 (by rfl) ⟨7436022, by rfl⟩ : syracuseStep 19829393 = 14872045) B14872045
theorem B300827 : Blo 187803 300827 := bstep (se 1 (by rfl) ⟨225620, by rfl⟩ : syracuseStep 300827 = 451241) B451241
theorem B2758697 : Blo 187803 2758697 := bstep (se 2 (by rfl) ⟨1034511, by rfl⟩ : syracuseStep 2758697 = 2069023) B2069023
theorem B302383 : Blo 187803 302383 := bstep (se 1 (by rfl) ⟨226787, by rfl⟩ : syracuseStep 302383 = 453575) B453575
theorem B21537089 : Blo 187803 21537089 := bstep (se 2 (by rfl) ⟨8076408, by rfl⟩ : syracuseStep 21537089 = 16152817) B16152817
theorem B7120831 : Blo 187803 7120831 := bstep (se 1 (by rfl) ⟨5340623, by rfl⟩ : syracuseStep 7120831 = 10681247) B10681247
theorem B305147 : Blo 187803 305147 := bstep (se 1 (by rfl) ⟨228860, by rfl⟩ : syracuseStep 305147 = 457721) B457721
theorem B6531839 : Blo 187803 6531839 := bstep (se 1 (by rfl) ⟨4898879, by rfl⟩ : syracuseStep 6531839 = 9797759) B9797759
theorem B634877 : Blo 187803 634877 := bstep (se 3 (by rfl) ⟨119039, by rfl⟩ : syracuseStep 634877 = 238079) B238079
theorem B603703 : Blo 187803 603703 := bstep (se 1 (by rfl) ⟨452777, by rfl⟩ : syracuseStep 603703 = 905555) B905555
theorem B11714543 : Blo 187803 11714543 := bstep (se 1 (by rfl) ⟨8785907, by rfl⟩ : syracuseStep 11714543 = 17571815) B17571815
theorem B213151 : Blo 187803 213151 := bstep (se 1 (by rfl) ⟨159863, by rfl⟩ : syracuseStep 213151 = 319727) B319727
theorem B641519 : Blo 187803 641519 := bstep (se 1 (by rfl) ⟨481139, by rfl⟩ : syracuseStep 641519 = 962279) B962279
theorem B609277 : Blo 187803 609277 := bstep (se 3 (by rfl) ⟨114239, by rfl⟩ : syracuseStep 609277 = 228479) B228479
theorem B1428839 : Blo 187803 1428839 := bstep (se 1 (by rfl) ⟨1071629, by rfl⟩ : syracuseStep 1428839 = 2143259) B2143259
theorem B1199555 : Blo 187803 1199555 := bstep (se 1 (by rfl) ⟨899666, by rfl⟩ : syracuseStep 1199555 = 1799333) B1799333
theorem B283625 : Blo 187803 283625 := bstep (se 2 (by rfl) ⟨106359, by rfl⟩ : syracuseStep 283625 = 212719) B212719
theorem B290544353 : Blo 187803 290544353 := bstep (se 2 (by rfl) ⟨108954132, by rfl⟩ : syracuseStep 290544353 = 217908265) B217908265
theorem B8347049 : Blo 187803 8347049 := bstep (se 2 (by rfl) ⟨3130143, by rfl⟩ : syracuseStep 8347049 = 6260287) B6260287
theorem B286175 : Blo 187803 286175 := bstep (se 1 (by rfl) ⟨214631, by rfl⟩ : syracuseStep 286175 = 429263) B429263
theorem B286313 : Blo 187803 286313 := bstep (se 2 (by rfl) ⟨107367, by rfl⟩ : syracuseStep 286313 = 214735) B214735
theorem B188319 : Blo 187803 188319 := bstep (se 1 (by rfl) ⟨141239, by rfl⟩ : syracuseStep 188319 = 282479) B282479
theorem B680795 : Blo 187803 680795 := bstep (se 1 (by rfl) ⟨510596, by rfl⟩ : syracuseStep 680795 = 1021193) B1021193
theorem B189679 : Blo 187803 189679 := bstep (se 1 (by rfl) ⟨142259, by rfl⟩ : syracuseStep 189679 = 284519) B284519
theorem B714055 : Blo 187803 714055 := bstep (se 1 (by rfl) ⟨535541, by rfl⟩ : syracuseStep 714055 = 1071083) B1071083
theorem B189951 : Blo 187803 189951 := bstep (se 1 (by rfl) ⟨142463, by rfl⟩ : syracuseStep 189951 = 284927) B284927
theorem B190311 : Blo 187803 190311 := bstep (se 1 (by rfl) ⟨142733, by rfl⟩ : syracuseStep 190311 = 285467) B285467
theorem B649399 : Blo 187803 649399 := bstep (se 1 (by rfl) ⟨487049, by rfl⟩ : syracuseStep 649399 = 974099) B974099
theorem B190943 : Blo 187803 190943 := bstep (se 1 (by rfl) ⟨143207, by rfl⟩ : syracuseStep 190943 = 286415) B286415
theorem B191591 : Blo 187803 191591 := bstep (se 1 (by rfl) ⟨143693, by rfl⟩ : syracuseStep 191591 = 287387) B287387
theorem B191647 : Blo 187803 191647 := bstep (se 1 (by rfl) ⟨143735, by rfl⟩ : syracuseStep 191647 = 287471) B287471
theorem B1077097 : Blo 187803 1077097 := bstep (se 2 (by rfl) ⟨403911, by rfl⟩ : syracuseStep 1077097 = 807823) B807823
theorem B2323109 : Blo 187803 2323109 := bstep (se 4 (by rfl) ⟨217791, by rfl⟩ : syracuseStep 2323109 = 435583) B435583
theorem B422783 : Blo 187803 422783 := bstep (se 1 (by rfl) ⟨317087, by rfl⟩ : syracuseStep 422783 = 634175) B634175
theorem B358015 : Blo 187803 358015 := bstep (se 1 (by rfl) ⟨268511, by rfl⟩ : syracuseStep 358015 = 537023) B537023
theorem B2455705 : Blo 187803 2455705 := bstep (se 2 (by rfl) ⟨920889, by rfl⟩ : syracuseStep 2455705 = 1841779) B1841779
theorem B784703 : Blo 187803 784703 := bstep (se 1 (by rfl) ⟨588527, by rfl⟩ : syracuseStep 784703 = 1177055) B1177055
theorem B1310377 : Blo 187803 1310377 := bstep (se 2 (by rfl) ⟨491391, by rfl⟩ : syracuseStep 1310377 = 982783) B982783
theorem B1081289 : Blo 187803 1081289 := bstep (se 2 (by rfl) ⟨405483, by rfl⟩ : syracuseStep 1081289 = 810967) B810967
theorem B425951 : Blo 187803 425951 := bstep (se 1 (by rfl) ⟨319463, by rfl⟩ : syracuseStep 425951 = 638927) B638927
theorem B427679 : Blo 187803 427679 := bstep (se 1 (by rfl) ⟨320759, by rfl⟩ : syracuseStep 427679 = 641519) B641519
theorem B952073 : Blo 187803 952073 := bstep (se 2 (by rfl) ⟨357027, by rfl⟩ : syracuseStep 952073 = 714055) B714055
theorem B952559 : Blo 187803 952559 := bstep (se 1 (by rfl) ⟨714419, by rfl⟩ : syracuseStep 952559 = 1428839) B1428839
theorem B200551 : Blo 187803 200551 := bstep (se 1 (by rfl) ⟨150413, by rfl⟩ : syracuseStep 200551 = 300827) B300827
theorem B1839131 : Blo 187803 1839131 := bstep (se 1 (by rfl) ⟨1379348, by rfl⟩ : syracuseStep 1839131 = 2758697) B2758697
theorem B193696235 : Blo 187803 193696235 := bstep (se 1 (by rfl) ⟨145272176, by rfl⟩ : syracuseStep 193696235 = 290544353) B290544353
theorem B14358059 : Blo 187803 14358059 := bstep (se 1 (by rfl) ⟨10768544, by rfl⟩ : syracuseStep 14358059 = 21537089) B21537089
theorem B1612709 : Blo 187803 1612709 := bstep (se 4 (by rfl) ⟨151191, by rfl⟩ : syracuseStep 1612709 = 302383) B302383
theorem B1548739 : Blo 187803 1548739 := bstep (se 1 (by rfl) ⟨1161554, by rfl⟩ : syracuseStep 1548739 = 2323109) B2323109
theorem B1747169 : Blo 187803 1747169 := bstep (se 2 (by rfl) ⟨655188, by rfl⟩ : syracuseStep 1747169 = 1310377) B1310377
theorem B7809695 : Blo 187803 7809695 := bstep (se 1 (by rfl) ⟨5857271, by rfl⟩ : syracuseStep 7809695 = 11714543) B11714543
theorem B1617083 : Blo 187803 1617083 := bstep (se 1 (by rfl) ⟨1212812, by rfl⟩ : syracuseStep 1617083 = 2425625) B2425625
theorem B700169 : Blo 187803 700169 := bstep (se 2 (by rfl) ⟨262563, by rfl⟩ : syracuseStep 700169 = 525127) B525127
theorem B1552763 : Blo 187803 1552763 := bstep (se 1 (by rfl) ⟨1164572, by rfl⟩ : syracuseStep 1552763 = 2329145) B2329145
theorem B799703 : Blo 187803 799703 := bstep (se 1 (by rfl) ⟨599777, by rfl⟩ : syracuseStep 799703 = 1199555) B1199555
theorem B13284773 : Blo 187803 13284773 := bstep (se 4 (by rfl) ⟨1245447, by rfl⟩ : syracuseStep 13284773 = 2490895) B2490895
theorem B865865 : Blo 187803 865865 := bstep (se 2 (by rfl) ⟨324699, by rfl⟩ : syracuseStep 865865 = 649399) B649399
theorem B13219595 : Blo 187803 13219595 := bstep (se 1 (by rfl) ⟨9914696, by rfl⟩ : syracuseStep 13219595 = 19829393) B19829393
theorem B965033 : Blo 187803 965033 := bstep (se 2 (by rfl) ⟨361887, by rfl⟩ : syracuseStep 965033 = 723775) B723775
theorem B804937 : Blo 187803 804937 := bstep (se 2 (by rfl) ⟨301851, by rfl⟩ : syracuseStep 804937 = 603703) B603703
theorem B477353 : Blo 187803 477353 := bstep (se 2 (by rfl) ⟨179007, by rfl⟩ : syracuseStep 477353 = 358015) B358015
theorem B281855 : Blo 187803 281855 := bstep (se 1 (by rfl) ⟨211391, by rfl⟩ : syracuseStep 281855 = 422783) B422783
theorem B283967 : Blo 187803 283967 := bstep (se 1 (by rfl) ⟨212975, by rfl⟩ : syracuseStep 283967 = 425951) B425951
theorem B284201 : Blo 187803 284201 := bstep (se 2 (by rfl) ⟨106575, by rfl⟩ : syracuseStep 284201 = 213151) B213151
theorem B284999 : Blo 187803 284999 := bstep (se 1 (by rfl) ⟨213749, by rfl⟩ : syracuseStep 284999 = 427499) B427499
theorem B220159 : Blo 187803 220159 := bstep (se 1 (by rfl) ⟨165119, by rfl⟩ : syracuseStep 220159 = 330239) B330239
theorem B482719 : Blo 187803 482719 := bstep (se 1 (by rfl) ⟨362039, by rfl⟩ : syracuseStep 482719 = 724079) B724079
theorem B9494441 : Blo 187803 9494441 := bstep (se 2 (by rfl) ⟨3560415, by rfl⟩ : syracuseStep 9494441 = 7120831) B7120831
theorem B189083 : Blo 187803 189083 := bstep (se 1 (by rfl) ⟨141812, by rfl⟩ : syracuseStep 189083 = 283625) B283625
theorem B812369 : Blo 187803 812369 := bstep (se 2 (by rfl) ⟨304638, by rfl⟩ : syracuseStep 812369 = 609277) B609277
theorem B5564699 : Blo 187803 5564699 := bstep (se 1 (by rfl) ⟨4173524, by rfl⟩ : syracuseStep 5564699 = 8347049) B8347049
theorem B190783 : Blo 187803 190783 := bstep (se 1 (by rfl) ⟨143087, by rfl⟩ : syracuseStep 190783 = 286175) B286175
theorem B190875 : Blo 187803 190875 := bstep (se 1 (by rfl) ⟨143156, by rfl⟩ : syracuseStep 190875 = 286313) B286313
theorem B1436129 : Blo 187803 1436129 := bstep (se 2 (by rfl) ⟨538548, by rfl⟩ : syracuseStep 1436129 = 1077097) B1077097
theorem B813725 : Blo 187803 813725 := bstep (se 3 (by rfl) ⟨152573, by rfl⟩ : syracuseStep 813725 = 305147) B305147
theorem B453863 : Blo 187803 453863 := bstep (se 1 (by rfl) ⟨340397, by rfl⟩ : syracuseStep 453863 = 680795) B680795
theorem B4354559 : Blo 187803 4354559 := bstep (se 1 (by rfl) ⟨3265919, by rfl⟩ : syracuseStep 4354559 = 6531839) B6531839
theorem B423251 : Blo 187803 423251 := bstep (se 1 (by rfl) ⟨317438, by rfl⟩ : syracuseStep 423251 = 634877) B634877
theorem B3274273 : Blo 187803 3274273 := bstep (se 2 (by rfl) ⟨1227852, by rfl⟩ : syracuseStep 3274273 = 2455705) B2455705
theorem B523135 : Blo 187803 523135 := bstep (se 1 (by rfl) ⟨392351, by rfl⟩ : syracuseStep 523135 = 784703) B784703
theorem B720859 : Blo 187803 720859 := bstep (se 1 (by rfl) ⟨540644, by rfl⟩ : syracuseStep 720859 = 1081289) B1081289
theorem B8259941 : Blo 187803 8259941 := bstep (se 4 (by rfl) ⟨774369, by rfl⟩ : syracuseStep 8259941 = 1548739) B1548739
theorem B9572039 : Blo 187803 9572039 := bstep (se 1 (by rfl) ⟨7179029, by rfl⟩ : syracuseStep 9572039 = 14358059) B14358059
theorem B267401 : Blo 187803 267401 := bstep (se 2 (by rfl) ⟨100275, by rfl⟩ : syracuseStep 267401 = 200551) B200551
theorem B6329627 : Blo 187803 6329627 := bstep (se 1 (by rfl) ⟨4747220, by rfl⟩ : syracuseStep 6329627 = 9494441) B9494441
theorem B3709799 : Blo 187803 3709799 := bstep (se 1 (by rfl) ⟨2782349, by rfl⟩ : syracuseStep 3709799 = 5564699) B5564699
theorem B957419 : Blo 187803 957419 := bstep (se 1 (by rfl) ⟨718064, by rfl⟩ : syracuseStep 957419 = 1436129) B1436129
theorem B4365697 : Blo 187803 4365697 := bstep (se 2 (by rfl) ⟨1637136, by rfl⟩ : syracuseStep 4365697 = 3274273) B3274273
theorem B533135 : Blo 187803 533135 := bstep (se 1 (by rfl) ⟨399851, by rfl⟩ : syracuseStep 533135 = 799703) B799703
theorem B8856515 : Blo 187803 8856515 := bstep (se 1 (by rfl) ⟨6642386, by rfl⟩ : syracuseStep 8856515 = 13284773) B13284773
theorem B697513 : Blo 187803 697513 := bstep (se 2 (by rfl) ⟨261567, by rfl⟩ : syracuseStep 697513 = 523135) B523135
theorem B961145 : Blo 187803 961145 := bstep (se 2 (by rfl) ⟨360429, by rfl⟩ : syracuseStep 961145 = 720859) B720859
theorem B634715 : Blo 187803 634715 := bstep (se 1 (by rfl) ⟨476036, by rfl⟩ : syracuseStep 634715 = 952073) B952073
theorem B635039 : Blo 187803 635039 := bstep (se 1 (by rfl) ⟨476279, by rfl⟩ : syracuseStep 635039 = 952559) B952559
theorem B1226087 : Blo 187803 1226087 := bstep (se 1 (by rfl) ⟨919565, by rfl⟩ : syracuseStep 1226087 = 1839131) B1839131
theorem B541579 : Blo 187803 541579 := bstep (se 1 (by rfl) ⟨406184, by rfl⟩ : syracuseStep 541579 = 812369) B812369
theorem B1164779 : Blo 187803 1164779 := bstep (se 1 (by rfl) ⟨873584, by rfl⟩ : syracuseStep 1164779 = 1747169) B1747169
theorem B542483 : Blo 187803 542483 := bstep (se 1 (by rfl) ⟨406862, by rfl⟩ : syracuseStep 542483 = 813725) B813725
theorem B1035175 : Blo 187803 1035175 := bstep (se 1 (by rfl) ⟨776381, by rfl⟩ : syracuseStep 1035175 = 1552763) B1552763
theorem B2903039 : Blo 187803 2903039 := bstep (se 1 (by rfl) ⟨2177279, by rfl⟩ : syracuseStep 2903039 = 4354559) B4354559
theorem B282167 : Blo 187803 282167 := bstep (se 1 (by rfl) ⟨211625, by rfl⟩ : syracuseStep 282167 = 423251) B423251
theorem B577243 : Blo 187803 577243 := bstep (se 1 (by rfl) ⟨432932, by rfl⟩ : syracuseStep 577243 = 865865) B865865
theorem B643355 : Blo 187803 643355 := bstep (se 1 (by rfl) ⟨482516, by rfl⟩ : syracuseStep 643355 = 965033) B965033
theorem B643625 : Blo 187803 643625 := bstep (se 2 (by rfl) ⟨241359, by rfl⟩ : syracuseStep 643625 = 482719) B482719
theorem B285119 : Blo 187803 285119 := bstep (se 1 (by rfl) ⟨213839, by rfl⟩ : syracuseStep 285119 = 427679) B427679
theorem B318235 : Blo 187803 318235 := bstep (se 1 (by rfl) ⟨238676, by rfl⟩ : syracuseStep 318235 = 477353) B477353
theorem B187903 : Blo 187803 187903 := bstep (se 1 (by rfl) ⟨140927, by rfl⟩ : syracuseStep 187903 = 281855) B281855
theorem B1073249 : Blo 187803 1073249 := bstep (se 2 (by rfl) ⟨402468, by rfl⟩ : syracuseStep 1073249 = 804937) B804937
theorem B129130823 : Blo 187803 129130823 := bstep (se 1 (by rfl) ⟨96848117, by rfl⟩ : syracuseStep 129130823 = 193696235) B193696235
theorem B189311 : Blo 187803 189311 := bstep (se 1 (by rfl) ⟨141983, by rfl⟩ : syracuseStep 189311 = 283967) B283967
theorem B189467 : Blo 187803 189467 := bstep (se 1 (by rfl) ⟨142100, by rfl⟩ : syracuseStep 189467 = 284201) B284201
theorem B189999 : Blo 187803 189999 := bstep (se 1 (by rfl) ⟨142499, by rfl⟩ : syracuseStep 189999 = 284999) B284999
theorem B1075139 : Blo 187803 1075139 := bstep (se 1 (by rfl) ⟨806354, by rfl⟩ : syracuseStep 1075139 = 1612709) B1612709
theorem B1174181 : Blo 187803 1174181 := bstep (se 4 (by rfl) ⟨110079, by rfl⟩ : syracuseStep 1174181 = 220159) B220159
theorem B5206463 : Blo 187803 5206463 := bstep (se 1 (by rfl) ⟨3904847, by rfl⟩ : syracuseStep 5206463 = 7809695) B7809695
theorem B1078055 : Blo 187803 1078055 := bstep (se 1 (by rfl) ⟨808541, by rfl⟩ : syracuseStep 1078055 = 1617083) B1617083
theorem B7468469 : Blo 187803 7468469 := bstep (se 5 (by rfl) ⟨350084, by rfl⟩ : syracuseStep 7468469 = 700169) B700169
theorem B1210301 : Blo 187803 1210301 := bstep (se 3 (by rfl) ⟨226931, by rfl⟩ : syracuseStep 1210301 = 453863) B453863
theorem B8813063 : Blo 187803 8813063 := bstep (se 1 (by rfl) ⟨6609797, by rfl⟩ : syracuseStep 8813063 = 13219595) B13219595
theorem B361655 : Blo 187803 361655 := bstep (se 1 (by rfl) ⟨271241, by rfl⟩ : syracuseStep 361655 = 542483) B542483
theorem B722105 : Blo 187803 722105 := bstep (se 2 (by rfl) ⟨270789, by rfl⟩ : syracuseStep 722105 = 541579) B541579
theorem B5506627 : Blo 187803 5506627 := bstep (se 1 (by rfl) ⟨4129970, by rfl⟩ : syracuseStep 5506627 = 8259941) B8259941
theorem B1935359 : Blo 187803 1935359 := bstep (se 1 (by rfl) ⟨1451519, by rfl⟩ : syracuseStep 1935359 = 2903039) B2903039
theorem B428903 : Blo 187803 428903 := bstep (se 1 (by rfl) ⟨321677, by rfl⟩ : syracuseStep 428903 = 643355) B643355
theorem B429083 : Blo 187803 429083 := bstep (se 1 (by rfl) ⟨321812, by rfl⟩ : syracuseStep 429083 = 643625) B643625
theorem B1380233 : Blo 187803 1380233 := bstep (se 2 (by rfl) ⟨517587, by rfl⟩ : syracuseStep 1380233 = 1035175) B1035175
theorem B86087215 : Blo 187803 86087215 := bstep (se 1 (by rfl) ⟨64565411, by rfl⟩ : syracuseStep 86087215 = 129130823) B129130823
theorem B5904343 : Blo 187803 5904343 := bstep (se 1 (by rfl) ⟨4428257, by rfl⟩ : syracuseStep 5904343 = 8856515) B8856515
theorem B23501501 : Blo 187803 23501501 := bstep (se 3 (by rfl) ⟨4406531, by rfl⟩ : syracuseStep 23501501 = 8813063) B8813063
theorem B930017 : Blo 187803 930017 := bstep (se 2 (by rfl) ⟨348756, by rfl⟩ : syracuseStep 930017 = 697513) B697513
theorem B2473199 : Blo 187803 2473199 := bstep (se 1 (by rfl) ⟨1854899, by rfl⟩ : syracuseStep 2473199 = 3709799) B3709799
theorem B638279 : Blo 187803 638279 := bstep (se 1 (by rfl) ⟨478709, by rfl⟩ : syracuseStep 638279 = 957419) B957419
theorem B769657 : Blo 187803 769657 := bstep (se 2 (by rfl) ⟨288621, by rfl⟩ : syracuseStep 769657 = 577243) B577243
theorem B640763 : Blo 187803 640763 := bstep (se 1 (by rfl) ⟨480572, by rfl⟩ : syracuseStep 640763 = 961145) B961145
theorem B3131149 : Blo 187803 3131149 := bstep (se 3 (by rfl) ⟨587090, by rfl⟩ : syracuseStep 3131149 = 1174181) B1174181
theorem B806867 : Blo 187803 806867 := bstep (se 1 (by rfl) ⟨605150, by rfl⟩ : syracuseStep 806867 = 1210301) B1210301
theorem B5820929 : Blo 187803 5820929 := bstep (se 2 (by rfl) ⟨2182848, by rfl⟩ : syracuseStep 5820929 = 4365697) B4365697
theorem B776519 : Blo 187803 776519 := bstep (se 1 (by rfl) ⟨582389, by rfl⟩ : syracuseStep 776519 = 1164779) B1164779
theorem B188111 : Blo 187803 188111 := bstep (se 1 (by rfl) ⟨141083, by rfl⟩ : syracuseStep 188111 = 282167) B282167
theorem B6381359 : Blo 187803 6381359 := bstep (se 1 (by rfl) ⟨4786019, by rfl⟩ : syracuseStep 6381359 = 9572039) B9572039
theorem B713069 : Blo 187803 713069 := bstep (se 3 (by rfl) ⟨133700, by rfl⟩ : syracuseStep 713069 = 267401) B267401
theorem B4219751 : Blo 187803 4219751 := bstep (se 1 (by rfl) ⟨3164813, by rfl⟩ : syracuseStep 4219751 = 6329627) B6329627
theorem B190079 : Blo 187803 190079 := bstep (se 1 (by rfl) ⟨142559, by rfl⟩ : syracuseStep 190079 = 285119) B285119
theorem B715499 : Blo 187803 715499 := bstep (se 1 (by rfl) ⟨536624, by rfl⟩ : syracuseStep 715499 = 1073249) B1073249
theorem B355423 : Blo 187803 355423 := bstep (se 1 (by rfl) ⟨266567, by rfl⟩ : syracuseStep 355423 = 533135) B533135
theorem B716759 : Blo 187803 716759 := bstep (se 1 (by rfl) ⟨537569, by rfl⟩ : syracuseStep 716759 = 1075139) B1075139
theorem B423143 : Blo 187803 423143 := bstep (se 1 (by rfl) ⟨317357, by rfl⟩ : syracuseStep 423143 = 634715) B634715
theorem B423359 : Blo 187803 423359 := bstep (se 1 (by rfl) ⟨317519, by rfl⟩ : syracuseStep 423359 = 635039) B635039
theorem B3470975 : Blo 187803 3470975 := bstep (se 1 (by rfl) ⟨2603231, by rfl⟩ : syracuseStep 3470975 = 5206463) B5206463
theorem B718703 : Blo 187803 718703 := bstep (se 1 (by rfl) ⟨539027, by rfl⟩ : syracuseStep 718703 = 1078055) B1078055
theorem B817391 : Blo 187803 817391 := bstep (se 1 (by rfl) ⟨613043, by rfl⟩ : syracuseStep 817391 = 1226087) B1226087
theorem B4978979 : Blo 187803 4978979 := bstep (se 1 (by rfl) ⟨3734234, by rfl⟩ : syracuseStep 4978979 = 7468469) B7468469
theorem B424313 : Blo 187803 424313 := bstep (se 2 (by rfl) ⟨159117, by rfl⟩ : syracuseStep 424313 = 318235) B318235
theorem B427175 : Blo 187803 427175 := bstep (se 1 (by rfl) ⟨320381, by rfl⟩ : syracuseStep 427175 = 640763) B640763
theorem B7342169 : Blo 187803 7342169 := bstep (se 2 (by rfl) ⟨2753313, by rfl⟩ : syracuseStep 7342169 = 5506627) B5506627
theorem B920155 : Blo 187803 920155 := bstep (se 1 (by rfl) ⟨690116, by rfl⟩ : syracuseStep 920155 = 1380233) B1380233
theorem B15667667 : Blo 187803 15667667 := bstep (se 1 (by rfl) ⟨11750750, by rfl⟩ : syracuseStep 15667667 = 23501501) B23501501
theorem B3319319 : Blo 187803 3319319 := bstep (se 1 (by rfl) ⟨2489489, by rfl⟩ : syracuseStep 3319319 = 4978979) B4978979
theorem B1648799 : Blo 187803 1648799 := bstep (se 1 (by rfl) ⟨1236599, by rfl⟩ : syracuseStep 1648799 = 2473199) B2473199
theorem B1026209 : Blo 187803 1026209 := bstep (se 2 (by rfl) ⟨384828, by rfl⟩ : syracuseStep 1026209 = 769657) B769657
theorem B241103 : Blo 187803 241103 := bstep (se 1 (by rfl) ⟨180827, by rfl⟩ : syracuseStep 241103 = 361655) B361655
theorem B1290239 : Blo 187803 1290239 := bstep (se 1 (by rfl) ⟨967679, by rfl⟩ : syracuseStep 1290239 = 1935359) B1935359
theorem B4174865 : Blo 187803 4174865 := bstep (se 2 (by rfl) ⟨1565574, by rfl⟩ : syracuseStep 4174865 = 3131149) B3131149
theorem B537911 : Blo 187803 537911 := bstep (se 1 (by rfl) ⟨403433, by rfl⟩ : syracuseStep 537911 = 806867) B806867
theorem B3880619 : Blo 187803 3880619 := bstep (se 1 (by rfl) ⟨2910464, by rfl⟩ : syracuseStep 3880619 = 5820929) B5820929
theorem B473897 : Blo 187803 473897 := bstep (se 2 (by rfl) ⟨177711, by rfl⟩ : syracuseStep 473897 = 355423) B355423
theorem B180042709 : Blo 187803 180042709 := bstep (se 7 (by rfl) ⟨2109875, by rfl⟩ : syracuseStep 180042709 = 4219751) B4219751
theorem B475379 : Blo 187803 475379 := bstep (se 1 (by rfl) ⟨356534, by rfl⟩ : syracuseStep 475379 = 713069) B713069
theorem B2179709 : Blo 187803 2179709 := bstep (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) B817391
theorem B476999 : Blo 187803 476999 := bstep (se 1 (by rfl) ⟨357749, by rfl⟩ : syracuseStep 476999 = 715499) B715499
theorem B477839 : Blo 187803 477839 := bstep (se 1 (by rfl) ⟨358379, by rfl⟩ : syracuseStep 477839 = 716759) B716759
theorem B282095 : Blo 187803 282095 := bstep (se 1 (by rfl) ⟨211571, by rfl⟩ : syracuseStep 282095 = 423143) B423143
theorem B282239 : Blo 187803 282239 := bstep (se 1 (by rfl) ⟨211679, by rfl⟩ : syracuseStep 282239 = 423359) B423359
theorem B2313983 : Blo 187803 2313983 := bstep (se 1 (by rfl) ⟨1735487, by rfl⟩ : syracuseStep 2313983 = 3470975) B3470975
theorem B479135 : Blo 187803 479135 := bstep (se 1 (by rfl) ⟨359351, by rfl⟩ : syracuseStep 479135 = 718703) B718703
theorem B282875 : Blo 187803 282875 := bstep (se 1 (by rfl) ⟨212156, by rfl⟩ : syracuseStep 282875 = 424313) B424313
theorem B481403 : Blo 187803 481403 := bstep (se 1 (by rfl) ⟨361052, by rfl⟩ : syracuseStep 481403 = 722105) B722105
theorem B285935 : Blo 187803 285935 := bstep (se 1 (by rfl) ⟨214451, by rfl⟩ : syracuseStep 285935 = 428903) B428903
theorem B286055 : Blo 187803 286055 := bstep (se 1 (by rfl) ⟨214541, by rfl⟩ : syracuseStep 286055 = 429083) B429083
theorem B517679 : Blo 187803 517679 := bstep (se 1 (by rfl) ⟨388259, by rfl⟩ : syracuseStep 517679 = 776519) B776519
theorem B4254239 : Blo 187803 4254239 := bstep (se 1 (by rfl) ⟨3190679, by rfl⟩ : syracuseStep 4254239 = 6381359) B6381359
theorem B114782953 : Blo 187803 114782953 := bstep (se 2 (by rfl) ⟨43043607, by rfl⟩ : syracuseStep 114782953 = 86087215) B86087215
theorem B620011 : Blo 187803 620011 := bstep (se 1 (by rfl) ⟨465008, by rfl⟩ : syracuseStep 620011 = 930017) B930017
theorem B425519 : Blo 187803 425519 := bstep (se 1 (by rfl) ⟨319139, by rfl⟩ : syracuseStep 425519 = 638279) B638279
theorem B31489829 : Blo 187803 31489829 := bstep (se 4 (by rfl) ⟨2952171, by rfl⟩ : syracuseStep 31489829 = 5904343) B5904343
theorem B1542655 : Blo 187803 1542655 := bstep (se 1 (by rfl) ⟨1156991, by rfl⟩ : syracuseStep 1542655 = 2313983) B2313983
theorem B11344637 : Blo 187803 11344637 := bstep (se 3 (by rfl) ⟨2127119, by rfl⟩ : syracuseStep 11344637 = 4254239) B4254239
theorem B826681 : Blo 187803 826681 := bstep (se 2 (by rfl) ⟨310005, by rfl⟩ : syracuseStep 826681 = 620011) B620011
theorem B860159 : Blo 187803 860159 := bstep (se 1 (by rfl) ⟨645119, by rfl⟩ : syracuseStep 860159 = 1290239) B1290239
theorem B1453139 : Blo 187803 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B1226873 : Blo 187803 1226873 := bstep (se 2 (by rfl) ⟨460077, by rfl⟩ : syracuseStep 1226873 = 920155) B920155
theorem B19579117 : Blo 187803 19579117 := bstep (se 3 (by rfl) ⟨3671084, by rfl⟩ : syracuseStep 19579117 = 7342169) B7342169
theorem B153043937 : Blo 187803 153043937 := bstep (se 2 (by rfl) ⟨57391476, by rfl⟩ : syracuseStep 153043937 = 114782953) B114782953
theorem B2212879 : Blo 187803 2212879 := bstep (se 1 (by rfl) ⟨1659659, by rfl⟩ : syracuseStep 2212879 = 3319319) B3319319
theorem B345119 : Blo 187803 345119 := bstep (se 1 (by rfl) ⟨258839, by rfl⟩ : syracuseStep 345119 = 517679) B517679
theorem B1099199 : Blo 187803 1099199 := bstep (se 1 (by rfl) ⟨824399, by rfl⟩ : syracuseStep 1099199 = 1648799) B1648799
theorem B1263725 : Blo 187803 1263725 := bstep (se 3 (by rfl) ⟨236948, by rfl⟩ : syracuseStep 1263725 = 473897) B473897
theorem B642941 : Blo 187803 642941 := bstep (se 3 (by rfl) ⟨120551, by rfl⟩ : syracuseStep 642941 = 241103) B241103
theorem B283679 : Blo 187803 283679 := bstep (se 1 (by rfl) ⟨212759, by rfl⟩ : syracuseStep 283679 = 425519) B425519
theorem B20993219 : Blo 187803 20993219 := bstep (se 1 (by rfl) ⟨15744914, by rfl⟩ : syracuseStep 20993219 = 31489829) B31489829
theorem B316919 : Blo 187803 316919 := bstep (se 1 (by rfl) ⟨237689, by rfl⟩ : syracuseStep 316919 = 475379) B475379
theorem B284783 : Blo 187803 284783 := bstep (se 1 (by rfl) ⟨213587, by rfl⟩ : syracuseStep 284783 = 427175) B427175
theorem B317999 : Blo 187803 317999 := bstep (se 1 (by rfl) ⟨238499, by rfl⟩ : syracuseStep 317999 = 476999) B476999
theorem B318559 : Blo 187803 318559 := bstep (se 1 (by rfl) ⟨238919, by rfl⟩ : syracuseStep 318559 = 477839) B477839
theorem B188063 : Blo 187803 188063 := bstep (se 1 (by rfl) ⟨141047, by rfl⟩ : syracuseStep 188063 = 282095) B282095
theorem B188159 : Blo 187803 188159 := bstep (se 1 (by rfl) ⟨141119, by rfl⟩ : syracuseStep 188159 = 282239) B282239
theorem B319423 : Blo 187803 319423 := bstep (se 1 (by rfl) ⟨239567, by rfl⟩ : syracuseStep 319423 = 479135) B479135
theorem B188583 : Blo 187803 188583 := bstep (se 1 (by rfl) ⟨141437, by rfl⟩ : syracuseStep 188583 = 282875) B282875
theorem B10445111 : Blo 187803 10445111 := bstep (se 1 (by rfl) ⟨7833833, by rfl⟩ : syracuseStep 10445111 = 15667667) B15667667
theorem B320935 : Blo 187803 320935 := bstep (se 1 (by rfl) ⟨240701, by rfl⟩ : syracuseStep 320935 = 481403) B481403
theorem B190623 : Blo 187803 190623 := bstep (se 1 (by rfl) ⟨142967, by rfl⟩ : syracuseStep 190623 = 285935) B285935
theorem B190703 : Blo 187803 190703 := bstep (se 1 (by rfl) ⟨143027, by rfl⟩ : syracuseStep 190703 = 286055) B286055
theorem B684139 : Blo 187803 684139 := bstep (se 1 (by rfl) ⟨513104, by rfl⟩ : syracuseStep 684139 = 1026209) B1026209
theorem B2783243 : Blo 187803 2783243 := bstep (se 1 (by rfl) ⟨2087432, by rfl⟩ : syracuseStep 2783243 = 4174865) B4174865
theorem B358607 : Blo 187803 358607 := bstep (se 1 (by rfl) ⟨268955, by rfl⟩ : syracuseStep 358607 = 537911) B537911
theorem B2587079 : Blo 187803 2587079 := bstep (se 1 (by rfl) ⟨1940309, by rfl⟩ : syracuseStep 2587079 = 3880619) B3880619
theorem B240056945 : Blo 187803 240056945 := bstep (se 2 (by rfl) ⟨90021354, by rfl⟩ : syracuseStep 240056945 = 180042709) B180042709
theorem B2950505 : Blo 187803 2950505 := bstep (se 2 (by rfl) ⟨1106439, by rfl⟩ : syracuseStep 2950505 = 2212879) B2212879
theorem B427913 : Blo 187803 427913 := bstep (se 2 (by rfl) ⟨160467, by rfl⟩ : syracuseStep 427913 = 320935) B320935
theorem B428627 : Blo 187803 428627 := bstep (se 1 (by rfl) ⟨321470, by rfl⟩ : syracuseStep 428627 = 642941) B642941
theorem B8227493 : Blo 187803 8227493 := bstep (se 4 (by rfl) ⟨771327, by rfl⟩ : syracuseStep 8227493 = 1542655) B1542655
theorem B920317 : Blo 187803 920317 := bstep (se 3 (by rfl) ⟨172559, by rfl⟩ : syracuseStep 920317 = 345119) B345119
theorem B13995479 : Blo 187803 13995479 := bstep (se 1 (by rfl) ⟨10496609, by rfl⟩ : syracuseStep 13995479 = 20993219) B20993219
theorem B956285 : Blo 187803 956285 := bstep (se 3 (by rfl) ⟨179303, by rfl⟩ : syracuseStep 956285 = 358607) B358607
theorem B211279 : Blo 187803 211279 := bstep (se 1 (by rfl) ⟨158459, by rfl⟩ : syracuseStep 211279 = 316919) B316919
theorem B2931197 : Blo 187803 2931197 := bstep (se 3 (by rfl) ⟨549599, by rfl⟩ : syracuseStep 2931197 = 1099199) B1099199
theorem B211999 : Blo 187803 211999 := bstep (se 1 (by rfl) ⟨158999, by rfl⟩ : syracuseStep 211999 = 317999) B317999
theorem B573439 : Blo 187803 573439 := bstep (se 1 (by rfl) ⟨430079, by rfl⟩ : syracuseStep 573439 = 860159) B860159
theorem B6963407 : Blo 187803 6963407 := bstep (se 1 (by rfl) ⟨5222555, by rfl⟩ : syracuseStep 6963407 = 10445111) B10445111
theorem B6898877 : Blo 187803 6898877 := bstep (se 3 (by rfl) ⟨1293539, by rfl⟩ : syracuseStep 6898877 = 2587079) B2587079
theorem B968759 : Blo 187803 968759 := bstep (se 1 (by rfl) ⟨726569, by rfl⟩ : syracuseStep 968759 = 1453139) B1453139
theorem B1855495 : Blo 187803 1855495 := bstep (se 1 (by rfl) ⟨1391621, by rfl⟩ : syracuseStep 1855495 = 2783243) B2783243
theorem B1102241 : Blo 187803 1102241 := bstep (se 2 (by rfl) ⟨413340, by rfl⟩ : syracuseStep 1102241 = 826681) B826681
theorem B26105489 : Blo 187803 26105489 := bstep (se 2 (by rfl) ⟨9789558, by rfl⟩ : syracuseStep 26105489 = 19579117) B19579117
theorem B102029291 : Blo 187803 102029291 := bstep (se 1 (by rfl) ⟨76521968, by rfl⟩ : syracuseStep 102029291 = 153043937) B153043937
theorem B842483 : Blo 187803 842483 := bstep (se 1 (by rfl) ⟨631862, by rfl⟩ : syracuseStep 842483 = 1263725) B1263725
theorem B189119 : Blo 187803 189119 := bstep (se 1 (by rfl) ⟨141839, by rfl⟩ : syracuseStep 189119 = 283679) B283679
theorem B189855 : Blo 187803 189855 := bstep (se 1 (by rfl) ⟨142391, by rfl⟩ : syracuseStep 189855 = 284783) B284783
theorem B7563091 : Blo 187803 7563091 := bstep (se 1 (by rfl) ⟨5672318, by rfl⟩ : syracuseStep 7563091 = 11344637) B11344637
theorem B912185 : Blo 187803 912185 := bstep (se 2 (by rfl) ⟨342069, by rfl⟩ : syracuseStep 912185 = 684139) B684139
theorem B3271661 : Blo 187803 3271661 := bstep (se 3 (by rfl) ⟨613436, by rfl⟩ : syracuseStep 3271661 = 1226873) B1226873
theorem B424745 : Blo 187803 424745 := bstep (se 2 (by rfl) ⟨159279, by rfl⟩ : syracuseStep 424745 = 318559) B318559
theorem B160037963 : Blo 187803 160037963 := bstep (se 1 (by rfl) ⟨120028472, by rfl⟩ : syracuseStep 160037963 = 240056945) B240056945
theorem B425897 : Blo 187803 425897 := bstep (se 2 (by rfl) ⟨159711, by rfl⟩ : syracuseStep 425897 = 319423) B319423
theorem B1967003 : Blo 187803 1967003 := bstep (se 1 (by rfl) ⟨1475252, by rfl⟩ : syracuseStep 1967003 = 2950505) B2950505
theorem B17403659 : Blo 187803 17403659 := bstep (se 1 (by rfl) ⟨13052744, by rfl⟩ : syracuseStep 17403659 = 26105489) B26105489
theorem B561655 : Blo 187803 561655 := bstep (se 1 (by rfl) ⟨421241, by rfl⟩ : syracuseStep 561655 = 842483) B842483
theorem B31266101 : Blo 187803 31266101 := bstep (se 5 (by rfl) ⟨1465598, by rfl⟩ : syracuseStep 31266101 = 2931197) B2931197
theorem B764585 : Blo 187803 764585 := bstep (se 2 (by rfl) ⟨286719, by rfl⟩ : syracuseStep 764585 = 573439) B573439
theorem B4599251 : Blo 187803 4599251 := bstep (se 1 (by rfl) ⟨3449438, by rfl⟩ : syracuseStep 4599251 = 6898877) B6898877
theorem B5484995 : Blo 187803 5484995 := bstep (se 1 (by rfl) ⟨4113746, by rfl⟩ : syracuseStep 5484995 = 8227493) B8227493
theorem B734827 : Blo 187803 734827 := bstep (se 1 (by rfl) ⟨551120, by rfl⟩ : syracuseStep 734827 = 1102241) B1102241
theorem B1227089 : Blo 187803 1227089 := bstep (se 2 (by rfl) ⟨460158, by rfl⟩ : syracuseStep 1227089 = 920317) B920317
theorem B637523 : Blo 187803 637523 := bstep (se 1 (by rfl) ⟨478142, by rfl⟩ : syracuseStep 637523 = 956285) B956285
theorem B2473993 : Blo 187803 2473993 := bstep (se 2 (by rfl) ⟨927747, by rfl⟩ : syracuseStep 2473993 = 1855495) B1855495
theorem B608123 : Blo 187803 608123 := bstep (se 1 (by rfl) ⟨456092, by rfl⟩ : syracuseStep 608123 = 912185) B912185
theorem B2181107 : Blo 187803 2181107 := bstep (se 1 (by rfl) ⟨1635830, by rfl⟩ : syracuseStep 2181107 = 3271661) B3271661
theorem B281705 : Blo 187803 281705 := bstep (se 2 (by rfl) ⟨105639, by rfl⟩ : syracuseStep 281705 = 211279) B211279
theorem B282665 : Blo 187803 282665 := bstep (se 2 (by rfl) ⟨105999, by rfl⟩ : syracuseStep 282665 = 211999) B211999
theorem B283163 : Blo 187803 283163 := bstep (se 1 (by rfl) ⟨212372, by rfl⟩ : syracuseStep 283163 = 424745) B424745
theorem B283931 : Blo 187803 283931 := bstep (se 1 (by rfl) ⟨212948, by rfl⟩ : syracuseStep 283931 = 425897) B425897
theorem B4642271 : Blo 187803 4642271 := bstep (se 1 (by rfl) ⟨3481703, by rfl⟩ : syracuseStep 4642271 = 6963407) B6963407
theorem B285275 : Blo 187803 285275 := bstep (se 1 (by rfl) ⟨213956, by rfl⟩ : syracuseStep 285275 = 427913) B427913
theorem B645839 : Blo 187803 645839 := bstep (se 1 (by rfl) ⟨484379, by rfl⟩ : syracuseStep 645839 = 968759) B968759
theorem B285751 : Blo 187803 285751 := bstep (se 1 (by rfl) ⟨214313, by rfl⟩ : syracuseStep 285751 = 428627) B428627
theorem B9330319 : Blo 187803 9330319 := bstep (se 1 (by rfl) ⟨6997739, by rfl⟩ : syracuseStep 9330319 = 13995479) B13995479
theorem B10084121 : Blo 187803 10084121 := bstep (se 2 (by rfl) ⟨3781545, by rfl⟩ : syracuseStep 10084121 = 7563091) B7563091
theorem B68019527 : Blo 187803 68019527 := bstep (se 1 (by rfl) ⟨51014645, by rfl⟩ : syracuseStep 68019527 = 102029291) B102029291
theorem B106691975 : Blo 187803 106691975 := bstep (se 1 (by rfl) ⟨80018981, by rfl⟩ : syracuseStep 106691975 = 160037963) B160037963
theorem B1311335 : Blo 187803 1311335 := bstep (se 1 (by rfl) ⟨983501, by rfl⟩ : syracuseStep 1311335 = 1967003) B1967003
theorem B11602439 : Blo 187803 11602439 := bstep (se 1 (by rfl) ⟨8701829, by rfl⟩ : syracuseStep 11602439 = 17403659) B17403659
theorem B20844067 : Blo 187803 20844067 := bstep (se 1 (by rfl) ⟨15633050, by rfl⟩ : syracuseStep 20844067 = 31266101) B31266101
theorem B430559 : Blo 187803 430559 := bstep (se 1 (by rfl) ⟨322919, by rfl⟩ : syracuseStep 430559 = 645839) B645839
theorem B6722747 : Blo 187803 6722747 := bstep (se 1 (by rfl) ⟨5042060, by rfl⟩ : syracuseStep 6722747 = 10084121) B10084121
theorem B405415 : Blo 187803 405415 := bstep (se 1 (by rfl) ⟨304061, by rfl⟩ : syracuseStep 405415 = 608123) B608123
theorem B1454071 : Blo 187803 1454071 := bstep (se 1 (by rfl) ⟨1090553, by rfl⟩ : syracuseStep 1454071 = 2181107) B2181107
theorem B3094847 : Blo 187803 3094847 := bstep (se 1 (by rfl) ⟨2321135, by rfl⟩ : syracuseStep 3094847 = 4642271) B4642271
theorem B1524005 : Blo 187803 1524005 := bstep (se 4 (by rfl) ⟨142875, by rfl⟩ : syracuseStep 1524005 = 285751) B285751
theorem B509723 : Blo 187803 509723 := bstep (se 1 (by rfl) ⟨382292, by rfl⟩ : syracuseStep 509723 = 764585) B764585
theorem B3066167 : Blo 187803 3066167 := bstep (se 1 (by rfl) ⟨2299625, by rfl⟩ : syracuseStep 3066167 = 4599251) B4599251
theorem B3656663 : Blo 187803 3656663 := bstep (se 1 (by rfl) ⟨2742497, by rfl⟩ : syracuseStep 3656663 = 5484995) B5484995
theorem B49761701 : Blo 187803 49761701 := bstep (se 4 (by rfl) ⟨4665159, by rfl⟩ : syracuseStep 49761701 = 9330319) B9330319
theorem B71127983 : Blo 187803 71127983 := bstep (se 1 (by rfl) ⟨53345987, by rfl⟩ : syracuseStep 71127983 = 106691975) B106691975
theorem B3298657 : Blo 187803 3298657 := bstep (se 2 (by rfl) ⟨1236996, by rfl⟩ : syracuseStep 3298657 = 2473993) B2473993
theorem B187803 : Blo 187803 187803 := bstep (se 1 (by rfl) ⟨140852, by rfl⟩ : syracuseStep 187803 = 281705) B281705
theorem B188443 : Blo 187803 188443 := bstep (se 1 (by rfl) ⟨141332, by rfl⟩ : syracuseStep 188443 = 282665) B282665
theorem B188775 : Blo 187803 188775 := bstep (se 1 (by rfl) ⟨141581, by rfl⟩ : syracuseStep 188775 = 283163) B283163
theorem B189287 : Blo 187803 189287 := bstep (se 1 (by rfl) ⟨141965, by rfl⟩ : syracuseStep 189287 = 283931) B283931
theorem B190183 : Blo 187803 190183 := bstep (se 1 (by rfl) ⟨142637, by rfl⟩ : syracuseStep 190183 = 285275) B285275
theorem B748873 : Blo 187803 748873 := bstep (se 2 (by rfl) ⟨280827, by rfl⟩ : syracuseStep 748873 = 561655) B561655
theorem B45346351 : Blo 187803 45346351 := bstep (se 1 (by rfl) ⟨34009763, by rfl⟩ : syracuseStep 45346351 = 68019527) B68019527
theorem B979769 : Blo 187803 979769 := bstep (se 2 (by rfl) ⟨367413, by rfl⟩ : syracuseStep 979769 = 734827) B734827
theorem B818059 : Blo 187803 818059 := bstep (se 1 (by rfl) ⟨613544, by rfl⟩ : syracuseStep 818059 = 1227089) B1227089
theorem B425015 : Blo 187803 425015 := bstep (se 1 (by rfl) ⟨318761, by rfl⟩ : syracuseStep 425015 = 637523) B637523
theorem B1016003 : Blo 187803 1016003 := bstep (se 1 (by rfl) ⟨762002, by rfl⟩ : syracuseStep 1016003 = 1524005) B1524005
theorem B7734959 : Blo 187803 7734959 := bstep (se 1 (by rfl) ⟨5801219, by rfl⟩ : syracuseStep 7734959 = 11602439) B11602439
theorem B47418655 : Blo 187803 47418655 := bstep (se 1 (by rfl) ⟨35563991, by rfl⟩ : syracuseStep 47418655 = 71127983) B71127983
theorem B27792089 : Blo 187803 27792089 := bstep (se 2 (by rfl) ⟨10422033, by rfl⟩ : syracuseStep 27792089 = 20844067) B20844067
theorem B60461801 : Blo 187803 60461801 := bstep (se 2 (by rfl) ⟨22673175, by rfl⟩ : syracuseStep 60461801 = 45346351) B45346351
theorem B1938761 : Blo 187803 1938761 := bstep (se 2 (by rfl) ⟨727035, by rfl⟩ : syracuseStep 1938761 = 1454071) B1454071
theorem B4398209 : Blo 187803 4398209 := bstep (se 2 (by rfl) ⟨1649328, by rfl⟩ : syracuseStep 4398209 = 3298657) B3298657
theorem B1090745 : Blo 187803 1090745 := bstep (se 2 (by rfl) ⟨409029, by rfl⟩ : syracuseStep 1090745 = 818059) B818059
theorem B339815 : Blo 187803 339815 := bstep (se 1 (by rfl) ⟨254861, by rfl⟩ : syracuseStep 339815 = 509723) B509723
theorem B2044111 : Blo 187803 2044111 := bstep (se 1 (by rfl) ⟨1533083, by rfl⟩ : syracuseStep 2044111 = 3066167) B3066167
theorem B2437775 : Blo 187803 2437775 := bstep (se 1 (by rfl) ⟨1828331, by rfl⟩ : syracuseStep 2437775 = 3656663) B3656663
theorem B33174467 : Blo 187803 33174467 := bstep (se 1 (by rfl) ⟨24880850, by rfl⟩ : syracuseStep 33174467 = 49761701) B49761701
theorem B998497 : Blo 187803 998497 := bstep (se 2 (by rfl) ⟨374436, by rfl⟩ : syracuseStep 998497 = 748873) B748873
theorem B283343 : Blo 187803 283343 := bstep (se 1 (by rfl) ⟨212507, by rfl⟩ : syracuseStep 283343 = 425015) B425015
theorem B874223 : Blo 187803 874223 := bstep (se 1 (by rfl) ⟨655667, by rfl⟩ : syracuseStep 874223 = 1311335) B1311335
theorem B287039 : Blo 187803 287039 := bstep (se 1 (by rfl) ⟨215279, by rfl⟩ : syracuseStep 287039 = 430559) B430559
theorem B4481831 : Blo 187803 4481831 := bstep (se 1 (by rfl) ⟨3361373, by rfl⟩ : syracuseStep 4481831 = 6722747) B6722747
theorem B653179 : Blo 187803 653179 := bstep (se 1 (by rfl) ⟨489884, by rfl⟩ : syracuseStep 653179 = 979769) B979769
theorem B2063231 : Blo 187803 2063231 := bstep (se 1 (by rfl) ⟨1547423, by rfl⟩ : syracuseStep 2063231 = 3094847) B3094847
theorem B2162213 : Blo 187803 2162213 := bstep (se 4 (by rfl) ⟨202707, by rfl⟩ : syracuseStep 2162213 = 405415) B405415
theorem B40307867 : Blo 187803 40307867 := bstep (se 1 (by rfl) ⟨30230900, by rfl⟩ : syracuseStep 40307867 = 60461801) B60461801
theorem B2725481 : Blo 187803 2725481 := bstep (se 2 (by rfl) ⟨1022055, by rfl⟩ : syracuseStep 2725481 = 2044111) B2044111
theorem B2987887 : Blo 187803 2987887 := bstep (se 1 (by rfl) ⟨2240915, by rfl⟩ : syracuseStep 2987887 = 4481831) B4481831
theorem B727163 : Blo 187803 727163 := bstep (se 1 (by rfl) ⟨545372, by rfl⟩ : syracuseStep 727163 = 1090745) B1090745
theorem B5156639 : Blo 187803 5156639 := bstep (se 1 (by rfl) ⟨3867479, by rfl⟩ : syracuseStep 5156639 = 7734959) B7734959
theorem B18528059 : Blo 187803 18528059 := bstep (se 1 (by rfl) ⟨13896044, by rfl⟩ : syracuseStep 18528059 = 27792089) B27792089
theorem B1292507 : Blo 187803 1292507 := bstep (se 1 (by rfl) ⟨969380, by rfl⟩ : syracuseStep 1292507 = 1938761) B1938761
theorem B63224873 : Blo 187803 63224873 := bstep (se 2 (by rfl) ⟨23709327, by rfl⟩ : syracuseStep 63224873 = 47418655) B47418655
theorem B2932139 : Blo 187803 2932139 := bstep (se 1 (by rfl) ⟨2199104, by rfl⟩ : syracuseStep 2932139 = 4398209) B4398209
theorem B870905 : Blo 187803 870905 := bstep (se 2 (by rfl) ⟨326589, by rfl⟩ : syracuseStep 870905 = 653179) B653179
theorem B1625183 : Blo 187803 1625183 := bstep (se 1 (by rfl) ⟨1218887, by rfl⟩ : syracuseStep 1625183 = 2437775) B2437775
theorem B1331329 : Blo 187803 1331329 := bstep (se 2 (by rfl) ⟨499248, by rfl⟩ : syracuseStep 1331329 = 998497) B998497
theorem B677335 : Blo 187803 677335 := bstep (se 1 (by rfl) ⟨508001, by rfl⟩ : syracuseStep 677335 = 1016003) B1016003
theorem B188895 : Blo 187803 188895 := bstep (se 1 (by rfl) ⟨141671, by rfl⟩ : syracuseStep 188895 = 283343) B283343
theorem B582815 : Blo 187803 582815 := bstep (se 1 (by rfl) ⟨437111, by rfl⟩ : syracuseStep 582815 = 874223) B874223
theorem B191359 : Blo 187803 191359 := bstep (se 1 (by rfl) ⟨143519, by rfl⟩ : syracuseStep 191359 = 287039) B287039
theorem B226543 : Blo 187803 226543 := bstep (se 1 (by rfl) ⟨169907, by rfl⟩ : syracuseStep 226543 = 339815) B339815
theorem B22116311 : Blo 187803 22116311 := bstep (se 1 (by rfl) ⟨16587233, by rfl⟩ : syracuseStep 22116311 = 33174467) B33174467
theorem B1375487 : Blo 187803 1375487 := bstep (se 1 (by rfl) ⟨1031615, by rfl⟩ : syracuseStep 1375487 = 2063231) B2063231
theorem B1441475 : Blo 187803 1441475 := bstep (se 1 (by rfl) ⟨1081106, by rfl⟩ : syracuseStep 1441475 = 2162213) B2162213
theorem B1083455 : Blo 187803 1083455 := bstep (se 1 (by rfl) ⟨812591, by rfl⟩ : syracuseStep 1083455 = 1625183) B1625183
theorem B26871911 : Blo 187803 26871911 := bstep (se 1 (by rfl) ⟨20153933, by rfl⟩ : syracuseStep 26871911 = 40307867) B40307867
theorem B1775105 : Blo 187803 1775105 := bstep (se 2 (by rfl) ⟨665664, by rfl⟩ : syracuseStep 1775105 = 1331329) B1331329
theorem B302057 : Blo 187803 302057 := bstep (se 2 (by rfl) ⟨113271, by rfl⟩ : syracuseStep 302057 = 226543) B226543
theorem B861671 : Blo 187803 861671 := bstep (se 1 (by rfl) ⟨646253, by rfl⟩ : syracuseStep 861671 = 1292507) B1292507
theorem B42149915 : Blo 187803 42149915 := bstep (se 1 (by rfl) ⟨31612436, by rfl⟩ : syracuseStep 42149915 = 63224873) B63224873
theorem B960983 : Blo 187803 960983 := bstep (se 1 (by rfl) ⟨720737, by rfl⟩ : syracuseStep 960983 = 1441475) B1441475
theorem B1554173 : Blo 187803 1554173 := bstep (se 3 (by rfl) ⟨291407, by rfl⟩ : syracuseStep 1554173 = 582815) B582815
theorem B1816987 : Blo 187803 1816987 := bstep (se 1 (by rfl) ⟨1362740, by rfl⟩ : syracuseStep 1816987 = 2725481) B2725481
theorem B903113 : Blo 187803 903113 := bstep (se 2 (by rfl) ⟨338667, by rfl⟩ : syracuseStep 903113 = 677335) B677335
theorem B3983849 : Blo 187803 3983849 := bstep (se 2 (by rfl) ⟨1493943, by rfl⟩ : syracuseStep 3983849 = 2987887) B2987887
theorem B1954759 : Blo 187803 1954759 := bstep (se 1 (by rfl) ⟨1466069, by rfl⟩ : syracuseStep 1954759 = 2932139) B2932139
theorem B580603 : Blo 187803 580603 := bstep (se 1 (by rfl) ⟨435452, by rfl⟩ : syracuseStep 580603 = 870905) B870905
theorem B484775 : Blo 187803 484775 := bstep (se 1 (by rfl) ⟨363581, by rfl⟩ : syracuseStep 484775 = 727163) B727163
theorem B49408157 : Blo 187803 49408157 := bstep (se 3 (by rfl) ⟨9264029, by rfl⟩ : syracuseStep 49408157 = 18528059) B18528059
theorem B3437759 : Blo 187803 3437759 := bstep (se 1 (by rfl) ⟨2578319, by rfl⟩ : syracuseStep 3437759 = 5156639) B5156639
theorem B14744207 : Blo 187803 14744207 := bstep (se 1 (by rfl) ⟨11058155, by rfl⟩ : syracuseStep 14744207 = 22116311) B22116311
theorem B916991 : Blo 187803 916991 := bstep (se 1 (by rfl) ⟨687743, by rfl⟩ : syracuseStep 916991 = 1375487) B1375487
theorem B722303 : Blo 187803 722303 := bstep (se 1 (by rfl) ⟨541727, by rfl⟩ : syracuseStep 722303 = 1083455) B1083455
theorem B2655899 : Blo 187803 2655899 := bstep (se 1 (by rfl) ⟨1991924, by rfl⟩ : syracuseStep 2655899 = 3983849) B3983849
theorem B1183403 : Blo 187803 1183403 := bstep (se 1 (by rfl) ⟨887552, by rfl⟩ : syracuseStep 1183403 = 1775105) B1775105
theorem B201371 : Blo 187803 201371 := bstep (se 1 (by rfl) ⟨151028, by rfl⟩ : syracuseStep 201371 = 302057) B302057
theorem B602075 : Blo 187803 602075 := bstep (se 1 (by rfl) ⟨451556, by rfl⟩ : syracuseStep 602075 = 903113) B903113
theorem B574447 : Blo 187803 574447 := bstep (se 1 (by rfl) ⟨430835, by rfl⟩ : syracuseStep 574447 = 861671) B861671
theorem B2606345 : Blo 187803 2606345 := bstep (se 2 (by rfl) ⟨977379, by rfl⟩ : syracuseStep 2606345 = 1954759) B1954759
theorem B28099943 : Blo 187803 28099943 := bstep (se 1 (by rfl) ⟨21074957, by rfl⟩ : syracuseStep 28099943 = 42149915) B42149915
theorem B640655 : Blo 187803 640655 := bstep (se 1 (by rfl) ⟨480491, by rfl⟩ : syracuseStep 640655 = 960983) B960983
theorem B1036115 : Blo 187803 1036115 := bstep (se 1 (by rfl) ⟨777086, by rfl⟩ : syracuseStep 1036115 = 1554173) B1554173
theorem B774137 : Blo 187803 774137 := bstep (se 2 (by rfl) ⟨290301, by rfl⟩ : syracuseStep 774137 = 580603) B580603
theorem B611327 : Blo 187803 611327 := bstep (se 1 (by rfl) ⟨458495, by rfl⟩ : syracuseStep 611327 = 916991) B916991
theorem B17914607 : Blo 187803 17914607 := bstep (se 1 (by rfl) ⟨13435955, by rfl⟩ : syracuseStep 17914607 = 26871911) B26871911
theorem B9167357 : Blo 187803 9167357 := bstep (se 3 (by rfl) ⟨1718879, by rfl⟩ : syracuseStep 9167357 = 3437759) B3437759
theorem B131755085 : Blo 187803 131755085 := bstep (se 3 (by rfl) ⟨24704078, by rfl⟩ : syracuseStep 131755085 = 49408157) B49408157
theorem B323183 : Blo 187803 323183 := bstep (se 1 (by rfl) ⟨242387, by rfl⟩ : syracuseStep 323183 = 484775) B484775
theorem B2422649 : Blo 187803 2422649 := bstep (se 2 (by rfl) ⟨908493, by rfl⟩ : syracuseStep 2422649 = 1816987) B1816987
theorem B9829471 : Blo 187803 9829471 := bstep (se 1 (by rfl) ⟨7372103, by rfl⟩ : syracuseStep 9829471 = 14744207) B14744207
theorem B1737563 : Blo 187803 1737563 := bstep (se 1 (by rfl) ⟨1303172, by rfl⟩ : syracuseStep 1737563 = 2606345) B2606345
theorem B427103 : Blo 187803 427103 := bstep (se 1 (by rfl) ⟨320327, by rfl⟩ : syracuseStep 427103 = 640655) B640655
theorem B1770599 : Blo 187803 1770599 := bstep (se 1 (by rfl) ⟨1327949, by rfl⟩ : syracuseStep 1770599 = 2655899) B2655899
theorem B24446285 : Blo 187803 24446285 := bstep (se 3 (by rfl) ⟨4583678, by rfl⟩ : syracuseStep 24446285 = 9167357) B9167357
theorem B788935 : Blo 187803 788935 := bstep (se 1 (by rfl) ⟨591701, by rfl⟩ : syracuseStep 788935 = 1183403) B1183403
theorem B690743 : Blo 187803 690743 := bstep (se 1 (by rfl) ⟨518057, by rfl⟩ : syracuseStep 690743 = 1036115) B1036115
theorem B401383 : Blo 187803 401383 := bstep (se 1 (by rfl) ⟨301037, by rfl⟩ : syracuseStep 401383 = 602075) B602075
theorem B1615099 : Blo 187803 1615099 := bstep (se 1 (by rfl) ⟨1211324, by rfl⟩ : syracuseStep 1615099 = 2422649) B2422649
theorem B765929 : Blo 187803 765929 := bstep (se 2 (by rfl) ⟨287223, by rfl⟩ : syracuseStep 765929 = 574447) B574447
theorem B536989 : Blo 187803 536989 := bstep (se 3 (by rfl) ⟨100685, by rfl⟩ : syracuseStep 536989 = 201371) B201371
theorem B11943071 : Blo 187803 11943071 := bstep (se 1 (by rfl) ⟨8957303, by rfl⟩ : syracuseStep 11943071 = 17914607) B17914607
theorem B87836723 : Blo 187803 87836723 := bstep (se 1 (by rfl) ⟨65877542, by rfl⟩ : syracuseStep 87836723 = 131755085) B131755085
theorem B215455 : Blo 187803 215455 := bstep (se 1 (by rfl) ⟨161591, by rfl⟩ : syracuseStep 215455 = 323183) B323183
theorem B18733295 : Blo 187803 18733295 := bstep (se 1 (by rfl) ⟨14049971, by rfl⟩ : syracuseStep 18733295 = 28099943) B28099943
theorem B481535 : Blo 187803 481535 := bstep (se 1 (by rfl) ⟨361151, by rfl⟩ : syracuseStep 481535 = 722303) B722303
theorem B516091 : Blo 187803 516091 := bstep (se 1 (by rfl) ⟨387068, by rfl⟩ : syracuseStep 516091 = 774137) B774137
theorem B1630205 : Blo 187803 1630205 := bstep (se 3 (by rfl) ⟨305663, by rfl⟩ : syracuseStep 1630205 = 611327) B611327
theorem B13105961 : Blo 187803 13105961 := bstep (se 2 (by rfl) ⟨4914735, by rfl⟩ : syracuseStep 13105961 = 9829471) B9829471
theorem B58557815 : Blo 187803 58557815 := bstep (se 1 (by rfl) ⟨43918361, by rfl⟩ : syracuseStep 58557815 = 87836723) B87836723
theorem B460495 : Blo 187803 460495 := bstep (se 1 (by rfl) ⟨345371, by rfl⟩ : syracuseStep 460495 = 690743) B690743
theorem B4721597 : Blo 187803 4721597 := bstep (se 3 (by rfl) ⟨885299, by rfl⟩ : syracuseStep 4721597 = 1770599) B1770599
theorem B1051913 : Blo 187803 1051913 := bstep (se 2 (by rfl) ⟨394467, by rfl⟩ : syracuseStep 1051913 = 788935) B788935
theorem B1086803 : Blo 187803 1086803 := bstep (se 1 (by rfl) ⟨815102, by rfl⟩ : syracuseStep 1086803 = 1630205) B1630205
theorem B535177 : Blo 187803 535177 := bstep (se 2 (by rfl) ⟨200691, by rfl⟩ : syracuseStep 535177 = 401383) B401383
theorem B16297523 : Blo 187803 16297523 := bstep (se 1 (by rfl) ⟨12223142, by rfl⟩ : syracuseStep 16297523 = 24446285) B24446285
theorem B49955453 : Blo 187803 49955453 := bstep (se 3 (by rfl) ⟨9366647, by rfl⟩ : syracuseStep 49955453 = 18733295) B18733295
theorem B510619 : Blo 187803 510619 := bstep (se 1 (by rfl) ⟨382964, by rfl⟩ : syracuseStep 510619 = 765929) B765929
theorem B18534005 : Blo 187803 18534005 := bstep (se 5 (by rfl) ⟨868781, by rfl⟩ : syracuseStep 18534005 = 1737563) B1737563
theorem B8737307 : Blo 187803 8737307 := bstep (se 1 (by rfl) ⟨6552980, by rfl⟩ : syracuseStep 8737307 = 13105961) B13105961
theorem B284735 : Blo 187803 284735 := bstep (se 1 (by rfl) ⟨213551, by rfl⟩ : syracuseStep 284735 = 427103) B427103
theorem B2153465 : Blo 187803 2153465 := bstep (se 2 (by rfl) ⟨807549, by rfl⟩ : syracuseStep 2153465 = 1615099) B1615099
theorem B287273 : Blo 187803 287273 := bstep (se 2 (by rfl) ⟨107727, by rfl⟩ : syracuseStep 287273 = 215455) B215455
theorem B321023 : Blo 187803 321023 := bstep (se 1 (by rfl) ⟨240767, by rfl⟩ : syracuseStep 321023 = 481535) B481535
theorem B715985 : Blo 187803 715985 := bstep (se 2 (by rfl) ⟨268494, by rfl⟩ : syracuseStep 715985 = 536989) B536989
theorem B7962047 : Blo 187803 7962047 := bstep (se 1 (by rfl) ⟨5971535, by rfl⟩ : syracuseStep 7962047 = 11943071) B11943071
theorem B688121 : Blo 187803 688121 := bstep (se 2 (by rfl) ⟨258045, by rfl⟩ : syracuseStep 688121 = 516091) B516091
theorem B3147731 : Blo 187803 3147731 := bstep (se 1 (by rfl) ⟨2360798, by rfl⟩ : syracuseStep 3147731 = 4721597) B4721597
theorem B12356003 : Blo 187803 12356003 := bstep (se 1 (by rfl) ⟨9267002, by rfl⟩ : syracuseStep 12356003 = 18534005) B18534005
theorem B724535 : Blo 187803 724535 := bstep (se 1 (by rfl) ⟨543401, by rfl⟩ : syracuseStep 724535 = 1086803) B1086803
theorem B33303635 : Blo 187803 33303635 := bstep (se 1 (by rfl) ⟨24977726, by rfl⟩ : syracuseStep 33303635 = 49955453) B49955453
theorem B39038543 : Blo 187803 39038543 := bstep (se 1 (by rfl) ⟨29278907, by rfl⟩ : syracuseStep 39038543 = 58557815) B58557815
theorem B214015 : Blo 187803 214015 := bstep (se 1 (by rfl) ⟨160511, by rfl⟩ : syracuseStep 214015 = 321023) B321023
theorem B477323 : Blo 187803 477323 := bstep (se 1 (by rfl) ⟨357992, by rfl⟩ : syracuseStep 477323 = 715985) B715985
theorem B10865015 : Blo 187803 10865015 := bstep (se 1 (by rfl) ⟨8148761, by rfl⟩ : syracuseStep 10865015 = 16297523) B16297523
theorem B2805101 : Blo 187803 2805101 := bstep (se 3 (by rfl) ⟨525956, by rfl⟩ : syracuseStep 2805101 = 1051913) B1051913
theorem B613993 : Blo 187803 613993 := bstep (se 2 (by rfl) ⟨230247, by rfl⟩ : syracuseStep 613993 = 460495) B460495
theorem B5824871 : Blo 187803 5824871 := bstep (se 1 (by rfl) ⟨4368653, by rfl⟩ : syracuseStep 5824871 = 8737307) B8737307
theorem B713569 : Blo 187803 713569 := bstep (se 2 (by rfl) ⟨267588, by rfl⟩ : syracuseStep 713569 = 535177) B535177
theorem B680825 : Blo 187803 680825 := bstep (se 2 (by rfl) ⟨255309, by rfl⟩ : syracuseStep 680825 = 510619) B510619
theorem B189823 : Blo 187803 189823 := bstep (se 1 (by rfl) ⟨142367, by rfl⟩ : syracuseStep 189823 = 284735) B284735
theorem B1435643 : Blo 187803 1435643 := bstep (se 1 (by rfl) ⟨1076732, by rfl⟩ : syracuseStep 1435643 = 2153465) B2153465
theorem B191515 : Blo 187803 191515 := bstep (se 1 (by rfl) ⟨143636, by rfl⟩ : syracuseStep 191515 = 287273) B287273
theorem B5308031 : Blo 187803 5308031 := bstep (se 1 (by rfl) ⟨3981023, by rfl⟩ : syracuseStep 5308031 = 7962047) B7962047
theorem B458747 : Blo 187803 458747 := bstep (se 1 (by rfl) ⟨344060, by rfl⟩ : syracuseStep 458747 = 688121) B688121
theorem B951425 : Blo 187803 951425 := bstep (se 2 (by rfl) ⟨356784, by rfl⟩ : syracuseStep 951425 = 713569) B713569
theorem B2098487 : Blo 187803 2098487 := bstep (se 1 (by rfl) ⟨1573865, by rfl⟩ : syracuseStep 2098487 = 3147731) B3147731
theorem B7243343 : Blo 187803 7243343 := bstep (se 1 (by rfl) ⟨5432507, by rfl⟩ : syracuseStep 7243343 = 10865015) B10865015
theorem B1870067 : Blo 187803 1870067 := bstep (se 1 (by rfl) ⟨1402550, by rfl⟩ : syracuseStep 1870067 = 2805101) B2805101
theorem B957095 : Blo 187803 957095 := bstep (se 1 (by rfl) ⟨717821, by rfl⟩ : syracuseStep 957095 = 1435643) B1435643
theorem B26025695 : Blo 187803 26025695 := bstep (se 1 (by rfl) ⟨19519271, by rfl⟩ : syracuseStep 26025695 = 39038543) B39038543
theorem B305831 : Blo 187803 305831 := bstep (se 1 (by rfl) ⟨229373, by rfl⟩ : syracuseStep 305831 = 458747) B458747
theorem B8237335 : Blo 187803 8237335 := bstep (se 1 (by rfl) ⟨6178001, by rfl⟩ : syracuseStep 8237335 = 12356003) B12356003
theorem B3883247 : Blo 187803 3883247 := bstep (se 1 (by rfl) ⟨2912435, by rfl⟩ : syracuseStep 3883247 = 5824871) B5824871
theorem B22202423 : Blo 187803 22202423 := bstep (se 1 (by rfl) ⟨16651817, by rfl⟩ : syracuseStep 22202423 = 33303635) B33303635
theorem B285353 : Blo 187803 285353 := bstep (se 2 (by rfl) ⟨107007, by rfl⟩ : syracuseStep 285353 = 214015) B214015
theorem B318215 : Blo 187803 318215 := bstep (se 1 (by rfl) ⟨238661, by rfl⟩ : syracuseStep 318215 = 477323) B477323
theorem B483023 : Blo 187803 483023 := bstep (se 1 (by rfl) ⟨362267, by rfl⟩ : syracuseStep 483023 = 724535) B724535
theorem B453883 : Blo 187803 453883 := bstep (se 1 (by rfl) ⟨340412, by rfl⟩ : syracuseStep 453883 = 680825) B680825
theorem B818657 : Blo 187803 818657 := bstep (se 2 (by rfl) ⟨306996, by rfl⟩ : syracuseStep 818657 = 613993) B613993
theorem B3538687 : Blo 187803 3538687 := bstep (se 1 (by rfl) ⟨2654015, by rfl⟩ : syracuseStep 3538687 = 5308031) B5308031
theorem B2588831 : Blo 187803 2588831 := bstep (se 1 (by rfl) ⟨1941623, by rfl⟩ : syracuseStep 2588831 = 3883247) B3883247
theorem B10983113 : Blo 187803 10983113 := bstep (se 2 (by rfl) ⟨4118667, by rfl⟩ : syracuseStep 10983113 = 8237335) B8237335
theorem B4986845 : Blo 187803 4986845 := bstep (se 3 (by rfl) ⟨935033, by rfl⟩ : syracuseStep 4986845 = 1870067) B1870067
theorem B203887 : Blo 187803 203887 := bstep (se 1 (by rfl) ⟨152915, by rfl⟩ : syracuseStep 203887 = 305831) B305831
theorem B634283 : Blo 187803 634283 := bstep (se 1 (by rfl) ⟨475712, by rfl⟩ : syracuseStep 634283 = 951425) B951425
theorem B4828895 : Blo 187803 4828895 := bstep (se 1 (by rfl) ⟨3621671, by rfl⟩ : syracuseStep 4828895 = 7243343) B7243343
theorem B605177 : Blo 187803 605177 := bstep (se 2 (by rfl) ⟨226941, by rfl⟩ : syracuseStep 605177 = 453883) B453883
theorem B638063 : Blo 187803 638063 := bstep (se 1 (by rfl) ⟨478547, by rfl⟩ : syracuseStep 638063 = 957095) B957095
theorem B212143 : Blo 187803 212143 := bstep (se 1 (by rfl) ⟨159107, by rfl⟩ : syracuseStep 212143 = 318215) B318215
theorem B17350463 : Blo 187803 17350463 := bstep (se 1 (by rfl) ⟨13012847, by rfl⟩ : syracuseStep 17350463 = 26025695) B26025695
theorem B545771 : Blo 187803 545771 := bstep (se 1 (by rfl) ⟨409328, by rfl⟩ : syracuseStep 545771 = 818657) B818657
theorem B14801615 : Blo 187803 14801615 := bstep (se 1 (by rfl) ⟨11101211, by rfl⟩ : syracuseStep 14801615 = 22202423) B22202423
theorem B5595965 : Blo 187803 5595965 := bstep (se 3 (by rfl) ⟨1049243, by rfl⟩ : syracuseStep 5595965 = 2098487) B2098487
theorem B190235 : Blo 187803 190235 := bstep (se 1 (by rfl) ⟨142676, by rfl⟩ : syracuseStep 190235 = 285353) B285353
theorem B322015 : Blo 187803 322015 := bstep (se 1 (by rfl) ⟨241511, by rfl⟩ : syracuseStep 322015 = 483023) B483023
theorem B4718249 : Blo 187803 4718249 := bstep (se 2 (by rfl) ⟨1769343, by rfl⟩ : syracuseStep 4718249 = 3538687) B3538687
theorem B429353 : Blo 187803 429353 := bstep (se 2 (by rfl) ⟨161007, by rfl⟩ : syracuseStep 429353 = 322015) B322015
theorem B363847 : Blo 187803 363847 := bstep (se 1 (by rfl) ⟨272885, by rfl⟩ : syracuseStep 363847 = 545771) B545771
theorem B9867743 : Blo 187803 9867743 := bstep (se 1 (by rfl) ⟨7400807, by rfl⟩ : syracuseStep 9867743 = 14801615) B14801615
theorem B3219263 : Blo 187803 3219263 := bstep (se 1 (by rfl) ⟨2414447, by rfl⟩ : syracuseStep 3219263 = 4828895) B4828895
theorem B271849 : Blo 187803 271849 := bstep (se 2 (by rfl) ⟨101943, by rfl⟩ : syracuseStep 271849 = 203887) B203887
theorem B403451 : Blo 187803 403451 := bstep (se 1 (by rfl) ⟨302588, by rfl⟩ : syracuseStep 403451 = 605177) B605177
theorem B7322075 : Blo 187803 7322075 := bstep (se 1 (by rfl) ⟨5491556, by rfl⟩ : syracuseStep 7322075 = 10983113) B10983113
theorem B3324563 : Blo 187803 3324563 := bstep (se 1 (by rfl) ⟨2493422, by rfl⟩ : syracuseStep 3324563 = 4986845) B4986845
theorem B282857 : Blo 187803 282857 := bstep (se 2 (by rfl) ⟨106071, by rfl⟩ : syracuseStep 282857 = 212143) B212143
theorem B1725887 : Blo 187803 1725887 := bstep (se 1 (by rfl) ⟨1294415, by rfl⟩ : syracuseStep 1725887 = 2588831) B2588831
theorem B3730643 : Blo 187803 3730643 := bstep (se 1 (by rfl) ⟨2797982, by rfl⟩ : syracuseStep 3730643 = 5595965) B5595965
theorem B422855 : Blo 187803 422855 := bstep (se 1 (by rfl) ⟨317141, by rfl⟩ : syracuseStep 422855 = 634283) B634283
theorem B425375 : Blo 187803 425375 := bstep (se 1 (by rfl) ⟨319031, by rfl⟩ : syracuseStep 425375 = 638063) B638063
theorem B3145499 : Blo 187803 3145499 := bstep (se 1 (by rfl) ⟨2359124, by rfl⟩ : syracuseStep 3145499 = 4718249) B4718249
theorem B11566975 : Blo 187803 11566975 := bstep (se 1 (by rfl) ⟨8675231, by rfl⟩ : syracuseStep 11566975 = 17350463) B17350463
theorem B362465 : Blo 187803 362465 := bstep (se 2 (by rfl) ⟨135924, by rfl⟩ : syracuseStep 362465 = 271849) B271849
theorem B268967 : Blo 187803 268967 := bstep (se 1 (by rfl) ⟨201725, by rfl⟩ : syracuseStep 268967 = 403451) B403451
theorem B4602365 : Blo 187803 4602365 := bstep (se 3 (by rfl) ⟨862943, by rfl⟩ : syracuseStep 4602365 = 1725887) B1725887
theorem B2146175 : Blo 187803 2146175 := bstep (se 1 (by rfl) ⟨1609631, by rfl⟩ : syracuseStep 2146175 = 3219263) B3219263
theorem B281903 : Blo 187803 281903 := bstep (se 1 (by rfl) ⟨211427, by rfl⟩ : syracuseStep 281903 = 422855) B422855
theorem B2216375 : Blo 187803 2216375 := bstep (se 1 (by rfl) ⟨1662281, by rfl⟩ : syracuseStep 2216375 = 3324563) B3324563
theorem B283583 : Blo 187803 283583 := bstep (se 1 (by rfl) ⟨212687, by rfl⟩ : syracuseStep 283583 = 425375) B425375
theorem B15422633 : Blo 187803 15422633 := bstep (se 2 (by rfl) ⟨5783487, by rfl⟩ : syracuseStep 15422633 = 11566975) B11566975
theorem B286235 : Blo 187803 286235 := bstep (se 1 (by rfl) ⟨214676, by rfl⟩ : syracuseStep 286235 = 429353) B429353
theorem B188571 : Blo 187803 188571 := bstep (se 1 (by rfl) ⟨141428, by rfl⟩ : syracuseStep 188571 = 282857) B282857
theorem B6578495 : Blo 187803 6578495 := bstep (se 1 (by rfl) ⟨4933871, by rfl⟩ : syracuseStep 6578495 = 9867743) B9867743
theorem B485129 : Blo 187803 485129 := bstep (se 2 (by rfl) ⟨181923, by rfl⟩ : syracuseStep 485129 = 363847) B363847
theorem B2487095 : Blo 187803 2487095 := bstep (se 1 (by rfl) ⟨1865321, by rfl⟩ : syracuseStep 2487095 = 3730643) B3730643
theorem B4881383 : Blo 187803 4881383 := bstep (se 1 (by rfl) ⟨3661037, by rfl⟩ : syracuseStep 4881383 = 7322075) B7322075
theorem B2096999 : Blo 187803 2096999 := bstep (se 1 (by rfl) ⟨1572749, by rfl⟩ : syracuseStep 2096999 = 3145499) B3145499
theorem B3254255 : Blo 187803 3254255 := bstep (se 1 (by rfl) ⟨2440691, by rfl⟩ : syracuseStep 3254255 = 4881383) B4881383
theorem B241643 : Blo 187803 241643 := bstep (se 1 (by rfl) ⟨181232, by rfl⟩ : syracuseStep 241643 = 362465) B362465
theorem B1658063 : Blo 187803 1658063 := bstep (se 1 (by rfl) ⟨1243547, by rfl⟩ : syracuseStep 1658063 = 2487095) B2487095
theorem B3068243 : Blo 187803 3068243 := bstep (se 1 (by rfl) ⟨2301182, by rfl⟩ : syracuseStep 3068243 = 4602365) B4602365
theorem B1397999 : Blo 187803 1397999 := bstep (se 1 (by rfl) ⟨1048499, by rfl⟩ : syracuseStep 1397999 = 2096999) B2096999
theorem B1430783 : Blo 187803 1430783 := bstep (se 1 (by rfl) ⟨1073087, by rfl⟩ : syracuseStep 1430783 = 2146175) B2146175
theorem B187935 : Blo 187803 187935 := bstep (se 1 (by rfl) ⟨140951, by rfl⟩ : syracuseStep 187935 = 281903) B281903
theorem B189055 : Blo 187803 189055 := bstep (se 1 (by rfl) ⟨141791, by rfl⟩ : syracuseStep 189055 = 283583) B283583
theorem B10281755 : Blo 187803 10281755 := bstep (se 1 (by rfl) ⟨7711316, by rfl⟩ : syracuseStep 10281755 = 15422633) B15422633
theorem B190823 : Blo 187803 190823 := bstep (se 1 (by rfl) ⟨143117, by rfl⟩ : syracuseStep 190823 = 286235) B286235
theorem B4385663 : Blo 187803 4385663 := bstep (se 1 (by rfl) ⟨3289247, by rfl⟩ : syracuseStep 4385663 = 6578495) B6578495
theorem B323419 : Blo 187803 323419 := bstep (se 1 (by rfl) ⟨242564, by rfl⟩ : syracuseStep 323419 = 485129) B485129
theorem B717245 : Blo 187803 717245 := bstep (se 3 (by rfl) ⟨134483, by rfl⟩ : syracuseStep 717245 = 268967) B268967
theorem B94565333 : Blo 187803 94565333 := bstep (se 7 (by rfl) ⟨1108187, by rfl⟩ : syracuseStep 94565333 = 2216375) B2216375
theorem B953855 : Blo 187803 953855 := bstep (se 1 (by rfl) ⟨715391, by rfl⟩ : syracuseStep 953855 = 1430783) B1430783
theorem B431225 : Blo 187803 431225 := bstep (se 2 (by rfl) ⟨161709, by rfl⟩ : syracuseStep 431225 = 323419) B323419
theorem B6854503 : Blo 187803 6854503 := bstep (se 1 (by rfl) ⟨5140877, by rfl⟩ : syracuseStep 6854503 = 10281755) B10281755
theorem B2169503 : Blo 187803 2169503 := bstep (se 1 (by rfl) ⟨1627127, by rfl⟩ : syracuseStep 2169503 = 3254255) B3254255
theorem B2923775 : Blo 187803 2923775 := bstep (se 1 (by rfl) ⟨2192831, by rfl⟩ : syracuseStep 2923775 = 4385663) B4385663
theorem B2045495 : Blo 187803 2045495 := bstep (se 1 (by rfl) ⟨1534121, by rfl⟩ : syracuseStep 2045495 = 3068243) B3068243
theorem B931999 : Blo 187803 931999 := bstep (se 1 (by rfl) ⟨698999, by rfl⟩ : syracuseStep 931999 = 1397999) B1397999
theorem B478163 : Blo 187803 478163 := bstep (se 1 (by rfl) ⟨358622, by rfl⟩ : syracuseStep 478163 = 717245) B717245
theorem B644381 : Blo 187803 644381 := bstep (se 3 (by rfl) ⟨120821, by rfl⟩ : syracuseStep 644381 = 241643) B241643
theorem B1105375 : Blo 187803 1105375 := bstep (se 1 (by rfl) ⟨829031, by rfl⟩ : syracuseStep 1105375 = 1658063) B1658063
theorem B252174221 : Blo 187803 252174221 := bstep (se 3 (by rfl) ⟨47282666, by rfl⟩ : syracuseStep 252174221 = 94565333) B94565333
theorem B429587 : Blo 187803 429587 := bstep (se 1 (by rfl) ⟨322190, by rfl⟩ : syracuseStep 429587 = 644381) B644381
theorem B1446335 : Blo 187803 1446335 := bstep (se 1 (by rfl) ⟨1084751, by rfl⟩ : syracuseStep 1446335 = 2169503) B2169503
theorem B635903 : Blo 187803 635903 := bstep (se 1 (by rfl) ⟨476927, by rfl⟩ : syracuseStep 635903 = 953855) B953855
theorem B1949183 : Blo 187803 1949183 := bstep (se 1 (by rfl) ⟨1461887, by rfl⟩ : syracuseStep 1949183 = 2923775) B2923775
theorem B168116147 : Blo 187803 168116147 := bstep (se 1 (by rfl) ⟨126087110, by rfl⟩ : syracuseStep 168116147 = 252174221) B252174221
theorem B1363663 : Blo 187803 1363663 := bstep (se 1 (by rfl) ⟨1022747, by rfl⟩ : syracuseStep 1363663 = 2045495) B2045495
theorem B318775 : Blo 187803 318775 := bstep (se 1 (by rfl) ⟨239081, by rfl⟩ : syracuseStep 318775 = 478163) B478163
theorem B287483 : Blo 187803 287483 := bstep (se 1 (by rfl) ⟨215612, by rfl⟩ : syracuseStep 287483 = 431225) B431225
theorem B9139337 : Blo 187803 9139337 := bstep (se 2 (by rfl) ⟨3427251, by rfl⟩ : syracuseStep 9139337 = 6854503) B6854503
theorem B1242665 : Blo 187803 1242665 := bstep (se 2 (by rfl) ⟨465999, by rfl⟩ : syracuseStep 1242665 = 931999) B931999
theorem B1473833 : Blo 187803 1473833 := bstep (se 2 (by rfl) ⟨552687, by rfl⟩ : syracuseStep 1473833 = 1105375) B1105375
theorem B828443 : Blo 187803 828443 := bstep (se 1 (by rfl) ⟨621332, by rfl⟩ : syracuseStep 828443 = 1242665) B1242665
theorem B112077431 : Blo 187803 112077431 := bstep (se 1 (by rfl) ⟨84058073, by rfl⟩ : syracuseStep 112077431 = 168116147) B168116147
theorem B964223 : Blo 187803 964223 := bstep (se 1 (by rfl) ⟨723167, by rfl⟩ : syracuseStep 964223 = 1446335) B1446335
theorem B1818217 : Blo 187803 1818217 := bstep (se 2 (by rfl) ⟨681831, by rfl⟩ : syracuseStep 1818217 = 1363663) B1363663
theorem B1299455 : Blo 187803 1299455 := bstep (se 1 (by rfl) ⟨974591, by rfl⟩ : syracuseStep 1299455 = 1949183) B1949183
theorem B286391 : Blo 187803 286391 := bstep (se 1 (by rfl) ⟨214793, by rfl⟩ : syracuseStep 286391 = 429587) B429587
theorem B191655 : Blo 187803 191655 := bstep (se 1 (by rfl) ⟨143741, by rfl⟩ : syracuseStep 191655 = 287483) B287483
theorem B423935 : Blo 187803 423935 := bstep (se 1 (by rfl) ⟨317951, by rfl⟩ : syracuseStep 423935 = 635903) B635903
theorem B6092891 : Blo 187803 6092891 := bstep (se 1 (by rfl) ⟨4569668, by rfl⟩ : syracuseStep 6092891 = 9139337) B9139337
theorem B3930221 : Blo 187803 3930221 := bstep (se 3 (by rfl) ⟨736916, by rfl⟩ : syracuseStep 3930221 = 1473833) B1473833
theorem B425033 : Blo 187803 425033 := bstep (se 2 (by rfl) ⟨159387, by rfl⟩ : syracuseStep 425033 = 318775) B318775
theorem B74718287 : Blo 187803 74718287 := bstep (se 1 (by rfl) ⟨56038715, by rfl⟩ : syracuseStep 74718287 = 112077431) B112077431
theorem B866303 : Blo 187803 866303 := bstep (se 1 (by rfl) ⟨649727, by rfl⟩ : syracuseStep 866303 = 1299455) B1299455
theorem B642815 : Blo 187803 642815 := bstep (se 1 (by rfl) ⟨482111, by rfl⟩ : syracuseStep 642815 = 964223) B964223
theorem B282623 : Blo 187803 282623 := bstep (se 1 (by rfl) ⟨211967, by rfl⟩ : syracuseStep 282623 = 423935) B423935
theorem B283355 : Blo 187803 283355 := bstep (se 1 (by rfl) ⟨212516, by rfl⟩ : syracuseStep 283355 = 425033) B425033
theorem B190927 : Blo 187803 190927 := bstep (se 1 (by rfl) ⟨143195, by rfl⟩ : syracuseStep 190927 = 286391) B286391
theorem B552295 : Blo 187803 552295 := bstep (se 1 (by rfl) ⟨414221, by rfl⟩ : syracuseStep 552295 = 828443) B828443
theorem B4061927 : Blo 187803 4061927 := bstep (se 1 (by rfl) ⟨3046445, by rfl⟩ : syracuseStep 4061927 = 6092891) B6092891
theorem B2620147 : Blo 187803 2620147 := bstep (se 1 (by rfl) ⟨1965110, by rfl⟩ : syracuseStep 2620147 = 3930221) B3930221
theorem B2424289 : Blo 187803 2424289 := bstep (se 2 (by rfl) ⟨909108, by rfl⟩ : syracuseStep 2424289 = 1818217) B1818217
theorem B428543 : Blo 187803 428543 := bstep (se 1 (by rfl) ⟨321407, by rfl⟩ : syracuseStep 428543 = 642815) B642815
theorem B49812191 : Blo 187803 49812191 := bstep (se 1 (by rfl) ⟨37359143, by rfl⟩ : syracuseStep 49812191 = 74718287) B74718287
theorem B736393 : Blo 187803 736393 := bstep (se 2 (by rfl) ⟨276147, by rfl⟩ : syracuseStep 736393 = 552295) B552295
theorem B3493529 : Blo 187803 3493529 := bstep (se 2 (by rfl) ⟨1310073, by rfl⟩ : syracuseStep 3493529 = 2620147) B2620147
theorem B577535 : Blo 187803 577535 := bstep (se 1 (by rfl) ⟨433151, by rfl⟩ : syracuseStep 577535 = 866303) B866303
theorem B2707951 : Blo 187803 2707951 := bstep (se 1 (by rfl) ⟨2030963, by rfl⟩ : syracuseStep 2707951 = 4061927) B4061927
theorem B3232385 : Blo 187803 3232385 := bstep (se 2 (by rfl) ⟨1212144, by rfl⟩ : syracuseStep 3232385 = 2424289) B2424289
theorem B188415 : Blo 187803 188415 := bstep (se 1 (by rfl) ⟨141311, by rfl⟩ : syracuseStep 188415 = 282623) B282623
theorem B188903 : Blo 187803 188903 := bstep (se 1 (by rfl) ⟨141677, by rfl⟩ : syracuseStep 188903 = 283355) B283355
theorem B2329019 : Blo 187803 2329019 := bstep (se 1 (by rfl) ⟨1746764, by rfl⟩ : syracuseStep 2329019 = 3493529) B3493529
theorem B3610601 : Blo 187803 3610601 := bstep (se 2 (by rfl) ⟨1353975, by rfl⟩ : syracuseStep 3610601 = 2707951) B2707951
theorem B33208127 : Blo 187803 33208127 := bstep (se 1 (by rfl) ⟨24906095, by rfl⟩ : syracuseStep 33208127 = 49812191) B49812191
theorem B1540093 : Blo 187803 1540093 := bstep (se 3 (by rfl) ⟨288767, by rfl⟩ : syracuseStep 1540093 = 577535) B577535
theorem B285695 : Blo 187803 285695 := bstep (se 1 (by rfl) ⟨214271, by rfl⟩ : syracuseStep 285695 = 428543) B428543
theorem B2154923 : Blo 187803 2154923 := bstep (se 1 (by rfl) ⟨1616192, by rfl⟩ : syracuseStep 2154923 = 3232385) B3232385
theorem B981857 : Blo 187803 981857 := bstep (se 2 (by rfl) ⟨368196, by rfl⟩ : syracuseStep 981857 = 736393) B736393
theorem B1552679 : Blo 187803 1552679 := bstep (se 1 (by rfl) ⟨1164509, by rfl⟩ : syracuseStep 1552679 = 2329019) B2329019
theorem B2407067 : Blo 187803 2407067 := bstep (se 1 (by rfl) ⟨1805300, by rfl⟩ : syracuseStep 2407067 = 3610601) B3610601
theorem B22138751 : Blo 187803 22138751 := bstep (se 1 (by rfl) ⟨16604063, by rfl⟩ : syracuseStep 22138751 = 33208127) B33208127
theorem B2053457 : Blo 187803 2053457 := bstep (se 2 (by rfl) ⟨770046, by rfl⟩ : syracuseStep 2053457 = 1540093) B1540093
theorem B190463 : Blo 187803 190463 := bstep (se 1 (by rfl) ⟨142847, by rfl⟩ : syracuseStep 190463 = 285695) B285695
theorem B1436615 : Blo 187803 1436615 := bstep (se 1 (by rfl) ⟨1077461, by rfl⟩ : syracuseStep 1436615 = 2154923) B2154923
theorem B654571 : Blo 187803 654571 := bstep (se 1 (by rfl) ⟨490928, by rfl⟩ : syracuseStep 654571 = 981857) B981857
theorem B957743 : Blo 187803 957743 := bstep (se 1 (by rfl) ⟨718307, by rfl⟩ : syracuseStep 957743 = 1436615) B1436615
theorem B14759167 : Blo 187803 14759167 := bstep (se 1 (by rfl) ⟨11069375, by rfl⟩ : syracuseStep 14759167 = 22138751) B22138751
theorem B3491045 : Blo 187803 3491045 := bstep (se 4 (by rfl) ⟨327285, by rfl⟩ : syracuseStep 3491045 = 654571) B654571
theorem B1035119 : Blo 187803 1035119 := bstep (se 1 (by rfl) ⟨776339, by rfl⟩ : syracuseStep 1035119 = 1552679) B1552679
theorem B1368971 : Blo 187803 1368971 := bstep (se 1 (by rfl) ⟨1026728, by rfl⟩ : syracuseStep 1368971 = 2053457) B2053457
theorem B1604711 : Blo 187803 1604711 := bstep (se 1 (by rfl) ⟨1203533, by rfl⟩ : syracuseStep 1604711 = 2407067) B2407067
theorem B2327363 : Blo 187803 2327363 := bstep (se 1 (by rfl) ⟨1745522, by rfl⟩ : syracuseStep 2327363 = 3491045) B3491045
theorem B690079 : Blo 187803 690079 := bstep (se 1 (by rfl) ⟨517559, by rfl⟩ : syracuseStep 690079 = 1035119) B1035119
theorem B638495 : Blo 187803 638495 := bstep (se 1 (by rfl) ⟨478871, by rfl⟩ : syracuseStep 638495 = 957743) B957743
theorem B19678889 : Blo 187803 19678889 := bstep (se 2 (by rfl) ⟨7379583, by rfl⟩ : syracuseStep 19678889 = 14759167) B14759167
theorem B1069807 : Blo 187803 1069807 := bstep (se 1 (by rfl) ⟨802355, by rfl⟩ : syracuseStep 1069807 = 1604711) B1604711
theorem B912647 : Blo 187803 912647 := bstep (se 1 (by rfl) ⟨684485, by rfl⟩ : syracuseStep 912647 = 1368971) B1368971
theorem B920105 : Blo 187803 920105 := bstep (se 2 (by rfl) ⟨345039, by rfl⟩ : syracuseStep 920105 = 690079) B690079
theorem B1551575 : Blo 187803 1551575 := bstep (se 1 (by rfl) ⟨1163681, by rfl⟩ : syracuseStep 1551575 = 2327363) B2327363
theorem B13119259 : Blo 187803 13119259 := bstep (se 1 (by rfl) ⟨9839444, by rfl⟩ : syracuseStep 13119259 = 19678889) B19678889
theorem B1426409 : Blo 187803 1426409 := bstep (se 2 (by rfl) ⟨534903, by rfl⟩ : syracuseStep 1426409 = 1069807) B1069807
theorem B608431 : Blo 187803 608431 := bstep (se 1 (by rfl) ⟨456323, by rfl⟩ : syracuseStep 608431 = 912647) B912647
theorem B425663 : Blo 187803 425663 := bstep (se 1 (by rfl) ⟨319247, by rfl⟩ : syracuseStep 425663 = 638495) B638495
theorem B950939 : Blo 187803 950939 := bstep (se 1 (by rfl) ⟨713204, by rfl⟩ : syracuseStep 950939 = 1426409) B1426409
theorem B1034383 : Blo 187803 1034383 := bstep (se 1 (by rfl) ⟨775787, by rfl⟩ : syracuseStep 1034383 = 1551575) B1551575
theorem B283775 : Blo 187803 283775 := bstep (se 1 (by rfl) ⟨212831, by rfl⟩ : syracuseStep 283775 = 425663) B425663
theorem B613403 : Blo 187803 613403 := bstep (se 1 (by rfl) ⟨460052, by rfl⟩ : syracuseStep 613403 = 920105) B920105
theorem B811241 : Blo 187803 811241 := bstep (se 2 (by rfl) ⟨304215, by rfl⟩ : syracuseStep 811241 = 608431) B608431
theorem B17492345 : Blo 187803 17492345 := bstep (se 2 (by rfl) ⟨6559629, by rfl⟩ : syracuseStep 17492345 = 13119259) B13119259
theorem B1379177 : Blo 187803 1379177 := bstep (se 2 (by rfl) ⟨517191, by rfl⟩ : syracuseStep 1379177 = 1034383) B1034383
theorem B633959 : Blo 187803 633959 := bstep (se 1 (by rfl) ⟨475469, by rfl⟩ : syracuseStep 633959 = 950939) B950939
theorem B408935 : Blo 187803 408935 := bstep (se 1 (by rfl) ⟨306701, by rfl⟩ : syracuseStep 408935 = 613403) B613403
theorem B540827 : Blo 187803 540827 := bstep (se 1 (by rfl) ⟨405620, by rfl⟩ : syracuseStep 540827 = 811241) B811241
theorem B189183 : Blo 187803 189183 := bstep (se 1 (by rfl) ⟨141887, by rfl⟩ : syracuseStep 189183 = 283775) B283775
theorem B11661563 : Blo 187803 11661563 := bstep (se 1 (by rfl) ⟨8746172, by rfl⟩ : syracuseStep 11661563 = 17492345) B17492345
theorem B360551 : Blo 187803 360551 := bstep (se 1 (by rfl) ⟨270413, by rfl⟩ : syracuseStep 360551 = 540827) B540827
theorem B919451 : Blo 187803 919451 := bstep (se 1 (by rfl) ⟨689588, by rfl⟩ : syracuseStep 919451 = 1379177) B1379177
theorem B7774375 : Blo 187803 7774375 := bstep (se 1 (by rfl) ⟨5830781, by rfl⟩ : syracuseStep 7774375 = 11661563) B11661563
theorem B1090493 : Blo 187803 1090493 := bstep (se 3 (by rfl) ⟨204467, by rfl⟩ : syracuseStep 1090493 = 408935) B408935
theorem B422639 : Blo 187803 422639 := bstep (se 1 (by rfl) ⟨316979, by rfl⟩ : syracuseStep 422639 = 633959) B633959
theorem B726995 : Blo 187803 726995 := bstep (se 1 (by rfl) ⟨545246, by rfl⟩ : syracuseStep 726995 = 1090493) B1090493
theorem B10365833 : Blo 187803 10365833 := bstep (se 2 (by rfl) ⟨3887187, by rfl⟩ : syracuseStep 10365833 = 7774375) B7774375
theorem B961469 : Blo 187803 961469 := bstep (se 3 (by rfl) ⟨180275, by rfl⟩ : syracuseStep 961469 = 360551) B360551
theorem B281759 : Blo 187803 281759 := bstep (se 1 (by rfl) ⟨211319, by rfl⟩ : syracuseStep 281759 = 422639) B422639
theorem B2451869 : Blo 187803 2451869 := bstep (se 3 (by rfl) ⟨459725, by rfl⟩ : syracuseStep 2451869 = 919451) B919451
theorem B640979 : Blo 187803 640979 := bstep (se 1 (by rfl) ⟨480734, by rfl⟩ : syracuseStep 640979 = 961469) B961469
theorem B187839 : Blo 187803 187839 := bstep (se 1 (by rfl) ⟨140879, by rfl⟩ : syracuseStep 187839 = 281759) B281759
theorem B484663 : Blo 187803 484663 := bstep (se 1 (by rfl) ⟨363497, by rfl⟩ : syracuseStep 484663 = 726995) B726995
theorem B1634579 : Blo 187803 1634579 := bstep (se 1 (by rfl) ⟨1225934, by rfl⟩ : syracuseStep 1634579 = 2451869) B2451869
theorem B6910555 : Blo 187803 6910555 := bstep (se 1 (by rfl) ⟨5182916, by rfl⟩ : syracuseStep 6910555 = 10365833) B10365833
theorem B427319 : Blo 187803 427319 := bstep (se 1 (by rfl) ⟨320489, by rfl⟩ : syracuseStep 427319 = 640979) B640979
theorem B9214073 : Blo 187803 9214073 := bstep (se 2 (by rfl) ⟨3455277, by rfl⟩ : syracuseStep 9214073 = 6910555) B6910555
theorem B1089719 : Blo 187803 1089719 := bstep (se 1 (by rfl) ⟨817289, by rfl⟩ : syracuseStep 1089719 = 1634579) B1634579
theorem B646217 : Blo 187803 646217 := bstep (se 2 (by rfl) ⟨242331, by rfl⟩ : syracuseStep 646217 = 484663) B484663
theorem B430811 : Blo 187803 430811 := bstep (se 1 (by rfl) ⟨323108, by rfl⟩ : syracuseStep 430811 = 646217) B646217
theorem B726479 : Blo 187803 726479 := bstep (se 1 (by rfl) ⟨544859, by rfl⟩ : syracuseStep 726479 = 1089719) B1089719
theorem B6142715 : Blo 187803 6142715 := bstep (se 1 (by rfl) ⟨4607036, by rfl⟩ : syracuseStep 6142715 = 9214073) B9214073
theorem B284879 : Blo 187803 284879 := bstep (se 1 (by rfl) ⟨213659, by rfl⟩ : syracuseStep 284879 = 427319) B427319
theorem B287207 : Blo 187803 287207 := bstep (se 1 (by rfl) ⟨215405, by rfl⟩ : syracuseStep 287207 = 430811) B430811
theorem B484319 : Blo 187803 484319 := bstep (se 1 (by rfl) ⟨363239, by rfl⟩ : syracuseStep 484319 = 726479) B726479
theorem B189919 : Blo 187803 189919 := bstep (se 1 (by rfl) ⟨142439, by rfl⟩ : syracuseStep 189919 = 284879) B284879
theorem B4095143 : Blo 187803 4095143 := bstep (se 1 (by rfl) ⟨3071357, by rfl⟩ : syracuseStep 4095143 = 6142715) B6142715
theorem B2730095 : Blo 187803 2730095 := bstep (se 1 (by rfl) ⟨2047571, by rfl⟩ : syracuseStep 2730095 = 4095143) B4095143
theorem B191471 : Blo 187803 191471 := bstep (se 1 (by rfl) ⟨143603, by rfl⟩ : syracuseStep 191471 = 287207) B287207
theorem B322879 : Blo 187803 322879 := bstep (se 1 (by rfl) ⟨242159, by rfl⟩ : syracuseStep 322879 = 484319) B484319
theorem B430505 : Blo 187803 430505 := bstep (se 2 (by rfl) ⟨161439, by rfl⟩ : syracuseStep 430505 = 322879) B322879
theorem B1820063 : Blo 187803 1820063 := bstep (se 1 (by rfl) ⟨1365047, by rfl⟩ : syracuseStep 1820063 = 2730095) B2730095
theorem B1213375 : Blo 187803 1213375 := bstep (se 1 (by rfl) ⟨910031, by rfl⟩ : syracuseStep 1213375 = 1820063) B1820063
theorem B287003 : Blo 187803 287003 := bstep (se 1 (by rfl) ⟨215252, by rfl⟩ : syracuseStep 287003 = 430505) B430505
theorem B1617833 : Blo 187803 1617833 := bstep (se 2 (by rfl) ⟨606687, by rfl⟩ : syracuseStep 1617833 = 1213375) B1213375
theorem B191335 : Blo 187803 191335 := bstep (se 1 (by rfl) ⟨143501, by rfl⟩ : syracuseStep 191335 = 287003) B287003
theorem B1078555 : Blo 187803 1078555 := bstep (se 1 (by rfl) ⟨808916, by rfl⟩ : syracuseStep 1078555 = 1617833) B1617833
theorem B1438073 : Blo 187803 1438073 := bstep (se 2 (by rfl) ⟨539277, by rfl⟩ : syracuseStep 1438073 = 1078555) B1078555
theorem B958715 : Blo 187803 958715 := bstep (se 1 (by rfl) ⟨719036, by rfl⟩ : syracuseStep 958715 = 1438073) B1438073
theorem B639143 : Blo 187803 639143 := bstep (se 1 (by rfl) ⟨479357, by rfl⟩ : syracuseStep 639143 = 958715) B958715
theorem B426095 : Blo 187803 426095 := bstep (se 1 (by rfl) ⟨319571, by rfl⟩ : syracuseStep 426095 = 639143) B639143
theorem B284063 : Blo 187803 284063 := bstep (se 1 (by rfl) ⟨213047, by rfl⟩ : syracuseStep 284063 = 426095) B426095
theorem B189375 : Blo 187803 189375 := bstep (se 1 (by rfl) ⟨142031, by rfl⟩ : syracuseStep 189375 = 284063) B284063

theorem C0 (j : ℕ) (h1 : 46950 ≤ j) (h2 : j ≤ 47649) : Blo 187803 (4 * j + 3) := by
  interval_cases j
  · exact B187803
  · exact B187807
  · exact B187811
  · exact B187815
  · exact B187819
  · exact B187823
  · exact B187827
  · exact B187831
  · exact B187835
  · exact B187839
  · exact B187843
  · exact B187847
  · exact B187851
  · exact B187855
  · exact B187859
  · exact B187863
  · exact B187867
  · exact B187871
  · exact B187875
  · exact B187879
  · exact B187883
  · exact B187887
  · exact B187891
  · exact B187895
  · exact B187899
  · exact B187903
  · exact B187907
  · exact B187911
  · exact B187915
  · exact B187919
  · exact B187923
  · exact B187927
  · exact B187931
  · exact B187935
  · exact B187939
  · exact B187943
  · exact B187947
  · exact B187951
  · exact B187955
  · exact B187959
  · exact B187963
  · exact B187967
  · exact B187971
  · exact B187975
  · exact B187979
  · exact B187983
  · exact B187987
  · exact B187991
  · exact B187995
  · exact B187999
  · exact B188003
  · exact B188007
  · exact B188011
  · exact B188015
  · exact B188019
  · exact B188023
  · exact B188027
  · exact B188031
  · exact B188035
  · exact B188039
  · exact B188043
  · exact B188047
  · exact B188051
  · exact B188055
  · exact B188059
  · exact B188063
  · exact B188067
  · exact B188071
  · exact B188075
  · exact B188079
  · exact B188083
  · exact B188087
  · exact B188091
  · exact B188095
  · exact B188099
  · exact B188103
  · exact B188107
  · exact B188111
  · exact B188115
  · exact B188119
  · exact B188123
  · exact B188127
  · exact B188131
  · exact B188135
  · exact B188139
  · exact B188143
  · exact B188147
  · exact B188151
  · exact B188155
  · exact B188159
  · exact B188163
  · exact B188167
  · exact B188171
  · exact B188175
  · exact B188179
  · exact B188183
  · exact B188187
  · exact B188191
  · exact B188195
  · exact B188199
  · exact B188203
  · exact B188207
  · exact B188211
  · exact B188215
  · exact B188219
  · exact B188223
  · exact B188227
  · exact B188231
  · exact B188235
  · exact B188239
  · exact B188243
  · exact B188247
  · exact B188251
  · exact B188255
  · exact B188259
  · exact B188263
  · exact B188267
  · exact B188271
  · exact B188275
  · exact B188279
  · exact B188283
  · exact B188287
  · exact B188291
  · exact B188295
  · exact B188299
  · exact B188303
  · exact B188307
  · exact B188311
  · exact B188315
  · exact B188319
  · exact B188323
  · exact B188327
  · exact B188331
  · exact B188335
  · exact B188339
  · exact B188343
  · exact B188347
  · exact B188351
  · exact B188355
  · exact B188359
  · exact B188363
  · exact B188367
  · exact B188371
  · exact B188375
  · exact B188379
  · exact B188383
  · exact B188387
  · exact B188391
  · exact B188395
  · exact B188399
  · exact B188403
  · exact B188407
  · exact B188411
  · exact B188415
  · exact B188419
  · exact B188423
  · exact B188427
  · exact B188431
  · exact B188435
  · exact B188439
  · exact B188443
  · exact B188447
  · exact B188451
  · exact B188455
  · exact B188459
  · exact B188463
  · exact B188467
  · exact B188471
  · exact B188475
  · exact B188479
  · exact B188483
  · exact B188487
  · exact B188491
  · exact B188495
  · exact B188499
  · exact B188503
  · exact B188507
  · exact B188511
  · exact B188515
  · exact B188519
  · exact B188523
  · exact B188527
  · exact B188531
  · exact B188535
  · exact B188539
  · exact B188543
  · exact B188547
  · exact B188551
  · exact B188555
  · exact B188559
  · exact B188563
  · exact B188567
  · exact B188571
  · exact B188575
  · exact B188579
  · exact B188583
  · exact B188587
  · exact B188591
  · exact B188595
  · exact B188599
  · exact B188603
  · exact B188607
  · exact B188611
  · exact B188615
  · exact B188619
  · exact B188623
  · exact B188627
  · exact B188631
  · exact B188635
  · exact B188639
  · exact B188643
  · exact B188647
  · exact B188651
  · exact B188655
  · exact B188659
  · exact B188663
  · exact B188667
  · exact B188671
  · exact B188675
  · exact B188679
  · exact B188683
  · exact B188687
  · exact B188691
  · exact B188695
  · exact B188699
  · exact B188703
  · exact B188707
  · exact B188711
  · exact B188715
  · exact B188719
  · exact B188723
  · exact B188727
  · exact B188731
  · exact B188735
  · exact B188739
  · exact B188743
  · exact B188747
  · exact B188751
  · exact B188755
  · exact B188759
  · exact B188763
  · exact B188767
  · exact B188771
  · exact B188775
  · exact B188779
  · exact B188783
  · exact B188787
  · exact B188791
  · exact B188795
  · exact B188799
  · exact B188803
  · exact B188807
  · exact B188811
  · exact B188815
  · exact B188819
  · exact B188823
  · exact B188827
  · exact B188831
  · exact B188835
  · exact B188839
  · exact B188843
  · exact B188847
  · exact B188851
  · exact B188855
  · exact B188859
  · exact B188863
  · exact B188867
  · exact B188871
  · exact B188875
  · exact B188879
  · exact B188883
  · exact B188887
  · exact B188891
  · exact B188895
  · exact B188899
  · exact B188903
  · exact B188907
  · exact B188911
  · exact B188915
  · exact B188919
  · exact B188923
  · exact B188927
  · exact B188931
  · exact B188935
  · exact B188939
  · exact B188943
  · exact B188947
  · exact B188951
  · exact B188955
  · exact B188959
  · exact B188963
  · exact B188967
  · exact B188971
  · exact B188975
  · exact B188979
  · exact B188983
  · exact B188987
  · exact B188991
  · exact B188995
  · exact B188999
  · exact B189003
  · exact B189007
  · exact B189011
  · exact B189015
  · exact B189019
  · exact B189023
  · exact B189027
  · exact B189031
  · exact B189035
  · exact B189039
  · exact B189043
  · exact B189047
  · exact B189051
  · exact B189055
  · exact B189059
  · exact B189063
  · exact B189067
  · exact B189071
  · exact B189075
  · exact B189079
  · exact B189083
  · exact B189087
  · exact B189091
  · exact B189095
  · exact B189099
  · exact B189103
  · exact B189107
  · exact B189111
  · exact B189115
  · exact B189119
  · exact B189123
  · exact B189127
  · exact B189131
  · exact B189135
  · exact B189139
  · exact B189143
  · exact B189147
  · exact B189151
  · exact B189155
  · exact B189159
  · exact B189163
  · exact B189167
  · exact B189171
  · exact B189175
  · exact B189179
  · exact B189183
  · exact B189187
  · exact B189191
  · exact B189195
  · exact B189199
  · exact B189203
  · exact B189207
  · exact B189211
  · exact B189215
  · exact B189219
  · exact B189223
  · exact B189227
  · exact B189231
  · exact B189235
  · exact B189239
  · exact B189243
  · exact B189247
  · exact B189251
  · exact B189255
  · exact B189259
  · exact B189263
  · exact B189267
  · exact B189271
  · exact B189275
  · exact B189279
  · exact B189283
  · exact B189287
  · exact B189291
  · exact B189295
  · exact B189299
  · exact B189303
  · exact B189307
  · exact B189311
  · exact B189315
  · exact B189319
  · exact B189323
  · exact B189327
  · exact B189331
  · exact B189335
  · exact B189339
  · exact B189343
  · exact B189347
  · exact B189351
  · exact B189355
  · exact B189359
  · exact B189363
  · exact B189367
  · exact B189371
  · exact B189375
  · exact B189379
  · exact B189383
  · exact B189387
  · exact B189391
  · exact B189395
  · exact B189399
  · exact B189403
  · exact B189407
  · exact B189411
  · exact B189415
  · exact B189419
  · exact B189423
  · exact B189427
  · exact B189431
  · exact B189435
  · exact B189439
  · exact B189443
  · exact B189447
  · exact B189451
  · exact B189455
  · exact B189459
  · exact B189463
  · exact B189467
  · exact B189471
  · exact B189475
  · exact B189479
  · exact B189483
  · exact B189487
  · exact B189491
  · exact B189495
  · exact B189499
  · exact B189503
  · exact B189507
  · exact B189511
  · exact B189515
  · exact B189519
  · exact B189523
  · exact B189527
  · exact B189531
  · exact B189535
  · exact B189539
  · exact B189543
  · exact B189547
  · exact B189551
  · exact B189555
  · exact B189559
  · exact B189563
  · exact B189567
  · exact B189571
  · exact B189575
  · exact B189579
  · exact B189583
  · exact B189587
  · exact B189591
  · exact B189595
  · exact B189599
  · exact B189603
  · exact B189607
  · exact B189611
  · exact B189615
  · exact B189619
  · exact B189623
  · exact B189627
  · exact B189631
  · exact B189635
  · exact B189639
  · exact B189643
  · exact B189647
  · exact B189651
  · exact B189655
  · exact B189659
  · exact B189663
  · exact B189667
  · exact B189671
  · exact B189675
  · exact B189679
  · exact B189683
  · exact B189687
  · exact B189691
  · exact B189695
  · exact B189699
  · exact B189703
  · exact B189707
  · exact B189711
  · exact B189715
  · exact B189719
  · exact B189723
  · exact B189727
  · exact B189731
  · exact B189735
  · exact B189739
  · exact B189743
  · exact B189747
  · exact B189751
  · exact B189755
  · exact B189759
  · exact B189763
  · exact B189767
  · exact B189771
  · exact B189775
  · exact B189779
  · exact B189783
  · exact B189787
  · exact B189791
  · exact B189795
  · exact B189799
  · exact B189803
  · exact B189807
  · exact B189811
  · exact B189815
  · exact B189819
  · exact B189823
  · exact B189827
  · exact B189831
  · exact B189835
  · exact B189839
  · exact B189843
  · exact B189847
  · exact B189851
  · exact B189855
  · exact B189859
  · exact B189863
  · exact B189867
  · exact B189871
  · exact B189875
  · exact B189879
  · exact B189883
  · exact B189887
  · exact B189891
  · exact B189895
  · exact B189899
  · exact B189903
  · exact B189907
  · exact B189911
  · exact B189915
  · exact B189919
  · exact B189923
  · exact B189927
  · exact B189931
  · exact B189935
  · exact B189939
  · exact B189943
  · exact B189947
  · exact B189951
  · exact B189955
  · exact B189959
  · exact B189963
  · exact B189967
  · exact B189971
  · exact B189975
  · exact B189979
  · exact B189983
  · exact B189987
  · exact B189991
  · exact B189995
  · exact B189999
  · exact B190003
  · exact B190007
  · exact B190011
  · exact B190015
  · exact B190019
  · exact B190023
  · exact B190027
  · exact B190031
  · exact B190035
  · exact B190039
  · exact B190043
  · exact B190047
  · exact B190051
  · exact B190055
  · exact B190059
  · exact B190063
  · exact B190067
  · exact B190071
  · exact B190075
  · exact B190079
  · exact B190083
  · exact B190087
  · exact B190091
  · exact B190095
  · exact B190099
  · exact B190103
  · exact B190107
  · exact B190111
  · exact B190115
  · exact B190119
  · exact B190123
  · exact B190127
  · exact B190131
  · exact B190135
  · exact B190139
  · exact B190143
  · exact B190147
  · exact B190151
  · exact B190155
  · exact B190159
  · exact B190163
  · exact B190167
  · exact B190171
  · exact B190175
  · exact B190179
  · exact B190183
  · exact B190187
  · exact B190191
  · exact B190195
  · exact B190199
  · exact B190203
  · exact B190207
  · exact B190211
  · exact B190215
  · exact B190219
  · exact B190223
  · exact B190227
  · exact B190231
  · exact B190235
  · exact B190239
  · exact B190243
  · exact B190247
  · exact B190251
  · exact B190255
  · exact B190259
  · exact B190263
  · exact B190267
  · exact B190271
  · exact B190275
  · exact B190279
  · exact B190283
  · exact B190287
  · exact B190291
  · exact B190295
  · exact B190299
  · exact B190303
  · exact B190307
  · exact B190311
  · exact B190315
  · exact B190319
  · exact B190323
  · exact B190327
  · exact B190331
  · exact B190335
  · exact B190339
  · exact B190343
  · exact B190347
  · exact B190351
  · exact B190355
  · exact B190359
  · exact B190363
  · exact B190367
  · exact B190371
  · exact B190375
  · exact B190379
  · exact B190383
  · exact B190387
  · exact B190391
  · exact B190395
  · exact B190399
  · exact B190403
  · exact B190407
  · exact B190411
  · exact B190415
  · exact B190419
  · exact B190423
  · exact B190427
  · exact B190431
  · exact B190435
  · exact B190439
  · exact B190443
  · exact B190447
  · exact B190451
  · exact B190455
  · exact B190459
  · exact B190463
  · exact B190467
  · exact B190471
  · exact B190475
  · exact B190479
  · exact B190483
  · exact B190487
  · exact B190491
  · exact B190495
  · exact B190499
  · exact B190503
  · exact B190507
  · exact B190511
  · exact B190515
  · exact B190519
  · exact B190523
  · exact B190527
  · exact B190531
  · exact B190535
  · exact B190539
  · exact B190543
  · exact B190547
  · exact B190551
  · exact B190555
  · exact B190559
  · exact B190563
  · exact B190567
  · exact B190571
  · exact B190575
  · exact B190579
  · exact B190583
  · exact B190587
  · exact B190591
  · exact B190595
  · exact B190599

theorem C1 (j : ℕ) (h1 : 47650 ≤ j) (h2 : j ≤ 47950) : Blo 187803 (4 * j + 3) := by
  interval_cases j
  · exact B190603
  · exact B190607
  · exact B190611
  · exact B190615
  · exact B190619
  · exact B190623
  · exact B190627
  · exact B190631
  · exact B190635
  · exact B190639
  · exact B190643
  · exact B190647
  · exact B190651
  · exact B190655
  · exact B190659
  · exact B190663
  · exact B190667
  · exact B190671
  · exact B190675
  · exact B190679
  · exact B190683
  · exact B190687
  · exact B190691
  · exact B190695
  · exact B190699
  · exact B190703
  · exact B190707
  · exact B190711
  · exact B190715
  · exact B190719
  · exact B190723
  · exact B190727
  · exact B190731
  · exact B190735
  · exact B190739
  · exact B190743
  · exact B190747
  · exact B190751
  · exact B190755
  · exact B190759
  · exact B190763
  · exact B190767
  · exact B190771
  · exact B190775
  · exact B190779
  · exact B190783
  · exact B190787
  · exact B190791
  · exact B190795
  · exact B190799
  · exact B190803
  · exact B190807
  · exact B190811
  · exact B190815
  · exact B190819
  · exact B190823
  · exact B190827
  · exact B190831
  · exact B190835
  · exact B190839
  · exact B190843
  · exact B190847
  · exact B190851
  · exact B190855
  · exact B190859
  · exact B190863
  · exact B190867
  · exact B190871
  · exact B190875
  · exact B190879
  · exact B190883
  · exact B190887
  · exact B190891
  · exact B190895
  · exact B190899
  · exact B190903
  · exact B190907
  · exact B190911
  · exact B190915
  · exact B190919
  · exact B190923
  · exact B190927
  · exact B190931
  · exact B190935
  · exact B190939
  · exact B190943
  · exact B190947
  · exact B190951
  · exact B190955
  · exact B190959
  · exact B190963
  · exact B190967
  · exact B190971
  · exact B190975
  · exact B190979
  · exact B190983
  · exact B190987
  · exact B190991
  · exact B190995
  · exact B190999
  · exact B191003
  · exact B191007
  · exact B191011
  · exact B191015
  · exact B191019
  · exact B191023
  · exact B191027
  · exact B191031
  · exact B191035
  · exact B191039
  · exact B191043
  · exact B191047
  · exact B191051
  · exact B191055
  · exact B191059
  · exact B191063
  · exact B191067
  · exact B191071
  · exact B191075
  · exact B191079
  · exact B191083
  · exact B191087
  · exact B191091
  · exact B191095
  · exact B191099
  · exact B191103
  · exact B191107
  · exact B191111
  · exact B191115
  · exact B191119
  · exact B191123
  · exact B191127
  · exact B191131
  · exact B191135
  · exact B191139
  · exact B191143
  · exact B191147
  · exact B191151
  · exact B191155
  · exact B191159
  · exact B191163
  · exact B191167
  · exact B191171
  · exact B191175
  · exact B191179
  · exact B191183
  · exact B191187
  · exact B191191
  · exact B191195
  · exact B191199
  · exact B191203
  · exact B191207
  · exact B191211
  · exact B191215
  · exact B191219
  · exact B191223
  · exact B191227
  · exact B191231
  · exact B191235
  · exact B191239
  · exact B191243
  · exact B191247
  · exact B191251
  · exact B191255
  · exact B191259
  · exact B191263
  · exact B191267
  · exact B191271
  · exact B191275
  · exact B191279
  · exact B191283
  · exact B191287
  · exact B191291
  · exact B191295
  · exact B191299
  · exact B191303
  · exact B191307
  · exact B191311
  · exact B191315
  · exact B191319
  · exact B191323
  · exact B191327
  · exact B191331
  · exact B191335
  · exact B191339
  · exact B191343
  · exact B191347
  · exact B191351
  · exact B191355
  · exact B191359
  · exact B191363
  · exact B191367
  · exact B191371
  · exact B191375
  · exact B191379
  · exact B191383
  · exact B191387
  · exact B191391
  · exact B191395
  · exact B191399
  · exact B191403
  · exact B191407
  · exact B191411
  · exact B191415
  · exact B191419
  · exact B191423
  · exact B191427
  · exact B191431
  · exact B191435
  · exact B191439
  · exact B191443
  · exact B191447
  · exact B191451
  · exact B191455
  · exact B191459
  · exact B191463
  · exact B191467
  · exact B191471
  · exact B191475
  · exact B191479
  · exact B191483
  · exact B191487
  · exact B191491
  · exact B191495
  · exact B191499
  · exact B191503
  · exact B191507
  · exact B191511
  · exact B191515
  · exact B191519
  · exact B191523
  · exact B191527
  · exact B191531
  · exact B191535
  · exact B191539
  · exact B191543
  · exact B191547
  · exact B191551
  · exact B191555
  · exact B191559
  · exact B191563
  · exact B191567
  · exact B191571
  · exact B191575
  · exact B191579
  · exact B191583
  · exact B191587
  · exact B191591
  · exact B191595
  · exact B191599
  · exact B191603
  · exact B191607
  · exact B191611
  · exact B191615
  · exact B191619
  · exact B191623
  · exact B191627
  · exact B191631
  · exact B191635
  · exact B191639
  · exact B191643
  · exact B191647
  · exact B191651
  · exact B191655
  · exact B191659
  · exact B191663
  · exact B191667
  · exact B191671
  · exact B191675
  · exact B191679
  · exact B191683
  · exact B191687
  · exact B191691
  · exact B191695
  · exact B191699
  · exact B191703
  · exact B191707
  · exact B191711
  · exact B191715
  · exact B191719
  · exact B191723
  · exact B191727
  · exact B191731
  · exact B191735
  · exact B191739
  · exact B191743
  · exact B191747
  · exact B191751
  · exact B191755
  · exact B191759
  · exact B191763
  · exact B191767
  · exact B191771
  · exact B191775
  · exact B191779
  · exact B191783
  · exact B191787
  · exact B191791
  · exact B191795
  · exact B191799
  · exact B191803

theorem solution (m : ℕ) (hlo : 187803 ≤ m) (hhi : m ≤ 191803) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 46950 ≤ j := by omega
    have hj2 : j ≤ 47950 := by omega
    have hb : Blo 187803 (4 * j + 3) := by
      rcases Nat.lt_or_ge j 47650 with hc0 | hc0
      · exact C0 j (by omega) (by omega)
      exact C1 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
