-- Prove2me | solution 1 for syracuse_descends_range_1451545_1453545
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-09T22:43:32.806465+00:00
-- url     : https://prove2.me/submissions/90840817-49d3-4478-9b6a-f59a62f9f49c

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


theorem B2326541 : Blo 1451545 2326541 := bbase (se 3 (by rfl) ⟨436226, by rfl⟩ : syracuseStep 2326541 = 872453) (by norm_num)
theorem B2179085 : Blo 1451545 2179085 := bbase (se 3 (by rfl) ⟨408578, by rfl⟩ : syracuseStep 2179085 = 817157) (by norm_num)
theorem B3268637 : Blo 1451545 3268637 := bbase (se 3 (by rfl) ⟨612869, by rfl⟩ : syracuseStep 3268637 = 1225739) (by norm_num)
theorem B2179109 : Blo 1451545 2179109 := bbase (se 4 (by rfl) ⟨204291, by rfl⟩ : syracuseStep 2179109 = 408583) (by norm_num)
theorem B2179133 : Blo 1451545 2179133 := bbase (se 3 (by rfl) ⟨408587, by rfl⟩ : syracuseStep 2179133 = 817175) (by norm_num)
theorem B2179157 : Blo 1451545 2179157 := bbase (se 8 (by rfl) ⟨12768, by rfl⟩ : syracuseStep 2179157 = 25537) (by norm_num)
theorem B1744993 : Blo 1451545 1744993 := bbase (se 2 (by rfl) ⟨654372, by rfl⟩ : syracuseStep 1744993 = 1308745) (by norm_num)
theorem B3268709 : Blo 1451545 3268709 := bbase (se 4 (by rfl) ⟨306441, by rfl⟩ : syracuseStep 3268709 = 612883) (by norm_num)
theorem B2179181 : Blo 1451545 2179181 := bbase (se 3 (by rfl) ⟨408596, by rfl⟩ : syracuseStep 2179181 = 817193) (by norm_num)
theorem B2449541 : Blo 1451545 2449541 := bbase (se 4 (by rfl) ⟨229644, by rfl⟩ : syracuseStep 2449541 = 459289) (by norm_num)
theorem B2179205 : Blo 1451545 2179205 := bbase (se 4 (by rfl) ⟨204300, by rfl⟩ : syracuseStep 2179205 = 408601) (by norm_num)
theorem B2179229 : Blo 1451545 2179229 := bbase (se 3 (by rfl) ⟨408605, by rfl⟩ : syracuseStep 2179229 = 817211) (by norm_num)
theorem B7356581 : Blo 1451545 7356581 := bbase (se 4 (by rfl) ⟨689679, by rfl⟩ : syracuseStep 7356581 = 1379359) (by norm_num)
theorem B3268781 : Blo 1451545 3268781 := bbase (se 3 (by rfl) ⟨612896, by rfl⟩ : syracuseStep 3268781 = 1225793) (by norm_num)
theorem B2179253 : Blo 1451545 2179253 := bbase (se 5 (by rfl) ⟨102152, by rfl⟩ : syracuseStep 2179253 = 204305) (by norm_num)
theorem B2179277 : Blo 1451545 2179277 := bbase (se 3 (by rfl) ⟨408614, by rfl⟩ : syracuseStep 2179277 = 817229) (by norm_num)
theorem B2179301 : Blo 1451545 2179301 := bbase (se 4 (by rfl) ⟨204309, by rfl⟩ : syracuseStep 2179301 = 408619) (by norm_num)
theorem B2793709 : Blo 1451545 2793709 := bbase (se 3 (by rfl) ⟨523820, by rfl⟩ : syracuseStep 2793709 = 1047641) (by norm_num)
theorem B3268853 : Blo 1451545 3268853 := bbase (se 5 (by rfl) ⟨153227, by rfl⟩ : syracuseStep 3268853 = 306455) (by norm_num)
theorem B3776765 : Blo 1451545 3776765 := bbase (se 3 (by rfl) ⟨708143, by rfl⟩ : syracuseStep 3776765 = 1416287) (by norm_num)
theorem B2179325 : Blo 1451545 2179325 := bbase (se 3 (by rfl) ⟨408623, by rfl⟩ : syracuseStep 2179325 = 817247) (by norm_num)
theorem B2449669 : Blo 1451545 2449669 := bbase (se 4 (by rfl) ⟨229656, by rfl⟩ : syracuseStep 2449669 = 459313) (by norm_num)
theorem B2179349 : Blo 1451545 2179349 := bbase (se 6 (by rfl) ⟨51078, by rfl⟩ : syracuseStep 2179349 = 102157) (by norm_num)
theorem B3678493 : Blo 1451545 3678493 := bbase (se 3 (by rfl) ⟨689717, by rfl⟩ : syracuseStep 3678493 = 1379435) (by norm_num)
theorem B2179373 : Blo 1451545 2179373 := bbase (se 3 (by rfl) ⟨408632, by rfl⟩ : syracuseStep 2179373 = 817265) (by norm_num)
theorem B1745209 : Blo 1451545 1745209 := bbase (se 2 (by rfl) ⟨654453, by rfl⟩ : syracuseStep 1745209 = 1308907) (by norm_num)
theorem B3268925 : Blo 1451545 3268925 := bbase (se 3 (by rfl) ⟨612923, by rfl⟩ : syracuseStep 3268925 = 1225847) (by norm_num)
theorem B2179397 : Blo 1451545 2179397 := bbase (se 4 (by rfl) ⟨204318, by rfl⟩ : syracuseStep 2179397 = 408637) (by norm_num)
theorem B37749077 : Blo 1451545 37749077 := bbase (se 10 (by rfl) ⟨55296, by rfl⟩ : syracuseStep 37749077 = 110593) (by norm_num)
theorem B2449757 : Blo 1451545 2449757 := bbase (se 3 (by rfl) ⟨459329, by rfl⟩ : syracuseStep 2449757 = 918659) (by norm_num)
theorem B2179421 : Blo 1451545 2179421 := bbase (se 3 (by rfl) ⟨408641, by rfl⟩ : syracuseStep 2179421 = 817283) (by norm_num)
theorem B5890421 : Blo 1451545 5890421 := bbase (se 5 (by rfl) ⟨276113, by rfl⟩ : syracuseStep 5890421 = 552227) (by norm_num)
theorem B2179445 : Blo 1451545 2179445 := bbase (se 5 (by rfl) ⟨102161, by rfl⟩ : syracuseStep 2179445 = 204323) (by norm_num)
theorem B1573237 : Blo 1451545 1573237 := bbase (se 5 (by rfl) ⟨73745, by rfl⟩ : syracuseStep 1573237 = 147491) (by norm_num)
theorem B3268997 : Blo 1451545 3268997 := bbase (se 4 (by rfl) ⟨306468, by rfl⟩ : syracuseStep 3268997 = 612937) (by norm_num)
theorem B2179469 : Blo 1451545 2179469 := bbase (se 3 (by rfl) ⟨408650, by rfl⟩ : syracuseStep 2179469 = 817301) (by norm_num)
theorem B3678605 : Blo 1451545 3678605 := bbase (se 3 (by rfl) ⟨689738, by rfl⟩ : syracuseStep 3678605 = 1379477) (by norm_num)
theorem B2179493 : Blo 1451545 2179493 := bbase (se 4 (by rfl) ⟨204327, by rfl⟩ : syracuseStep 2179493 = 408655) (by norm_num)
theorem B2179517 : Blo 1451545 2179517 := bbase (se 3 (by rfl) ⟨408659, by rfl⟩ : syracuseStep 2179517 = 817319) (by norm_num)
theorem B3269069 : Blo 1451545 3269069 := bbase (se 3 (by rfl) ⟨612950, by rfl⟩ : syracuseStep 3269069 = 1225901) (by norm_num)
theorem B2179541 : Blo 1451545 2179541 := bbase (se 7 (by rfl) ⟨25541, by rfl⟩ : syracuseStep 2179541 = 51083) (by norm_num)
theorem B2449885 : Blo 1451545 2449885 := bbase (se 3 (by rfl) ⟨459353, by rfl⟩ : syracuseStep 2449885 = 918707) (by norm_num)
theorem B2179565 : Blo 1451545 2179565 := bbase (se 3 (by rfl) ⟨408668, by rfl⟩ : syracuseStep 2179565 = 817337) (by norm_num)
theorem B2179589 : Blo 1451545 2179589 := bbase (se 4 (by rfl) ⟨204336, by rfl⟩ : syracuseStep 2179589 = 408673) (by norm_num)
theorem B3269141 : Blo 1451545 3269141 := bbase (se 6 (by rfl) ⟨76620, by rfl⟩ : syracuseStep 3269141 = 153241) (by norm_num)
theorem B3727901 : Blo 1451545 3727901 := bbase (se 3 (by rfl) ⟨698981, by rfl⟩ : syracuseStep 3727901 = 1397963) (by norm_num)
theorem B2179613 : Blo 1451545 2179613 := bbase (se 3 (by rfl) ⟨408677, by rfl⟩ : syracuseStep 2179613 = 817355) (by norm_num)
theorem B4899365 : Blo 1451545 4899365 := bbase (se 4 (by rfl) ⟨459315, by rfl⟩ : syracuseStep 4899365 = 918631) (by norm_num)
theorem B2449973 : Blo 1451545 2449973 := bbase (se 5 (by rfl) ⟨114842, by rfl⟩ : syracuseStep 2449973 = 229685) (by norm_num)
theorem B9306677 : Blo 1451545 9306677 := bbase (se 5 (by rfl) ⟨436250, by rfl⟩ : syracuseStep 9306677 = 872501) (by norm_num)
theorem B2179637 : Blo 1451545 2179637 := bbase (se 5 (by rfl) ⟨102170, by rfl⟩ : syracuseStep 2179637 = 204341) (by norm_num)
theorem B7348805 : Blo 1451545 7348805 := bbase (se 4 (by rfl) ⟨688950, by rfl⟩ : syracuseStep 7348805 = 1377901) (by norm_num)
theorem B5972549 : Blo 1451545 5972549 := bbase (se 4 (by rfl) ⟨559926, by rfl⟩ : syracuseStep 5972549 = 1119853) (by norm_num)
theorem B2179661 : Blo 1451545 2179661 := bbase (se 3 (by rfl) ⟨408686, by rfl⟩ : syracuseStep 2179661 = 817373) (by norm_num)
theorem B3678797 : Blo 1451545 3678797 := bbase (se 3 (by rfl) ⟨689774, by rfl⟩ : syracuseStep 3678797 = 1379549) (by norm_num)
theorem B3269213 : Blo 1451545 3269213 := bbase (se 3 (by rfl) ⟨612977, by rfl⟩ : syracuseStep 3269213 = 1225955) (by norm_num)
theorem B2179685 : Blo 1451545 2179685 := bbase (se 4 (by rfl) ⟨204345, by rfl⟩ : syracuseStep 2179685 = 408691) (by norm_num)
theorem B2179709 : Blo 1451545 2179709 := bbase (se 3 (by rfl) ⟨408695, by rfl⟩ : syracuseStep 2179709 = 817391) (by norm_num)
theorem B2179733 : Blo 1451545 2179733 := bbase (se 6 (by rfl) ⟨51087, by rfl⟩ : syracuseStep 2179733 = 102175) (by norm_num)
theorem B3981973 : Blo 1451545 3981973 := bbase (se 6 (by rfl) ⟨93327, by rfl⟩ : syracuseStep 3981973 = 186655) (by norm_num)
theorem B3269285 : Blo 1451545 3269285 := bbase (se 4 (by rfl) ⟨306495, by rfl⟩ : syracuseStep 3269285 = 612991) (by norm_num)
theorem B2179757 : Blo 1451545 2179757 := bbase (se 3 (by rfl) ⟨408704, by rfl⟩ : syracuseStep 2179757 = 817409) (by norm_num)
theorem B2450101 : Blo 1451545 2450101 := bbase (se 5 (by rfl) ⟨114848, by rfl⟩ : syracuseStep 2450101 = 229697) (by norm_num)
theorem B4653749 : Blo 1451545 4653749 := bbase (se 5 (by rfl) ⟨218144, by rfl⟩ : syracuseStep 4653749 = 436289) (by norm_num)
theorem B2327221 : Blo 1451545 2327221 := bbase (se 5 (by rfl) ⟨109088, by rfl⟩ : syracuseStep 2327221 = 218177) (by norm_num)
theorem B2179781 : Blo 1451545 2179781 := bbase (se 4 (by rfl) ⟨204354, by rfl⟩ : syracuseStep 2179781 = 408709) (by norm_num)
theorem B2179805 : Blo 1451545 2179805 := bbase (se 3 (by rfl) ⟨408713, by rfl⟩ : syracuseStep 2179805 = 817427) (by norm_num)
theorem B3269357 : Blo 1451545 3269357 := bbase (se 3 (by rfl) ⟨613004, by rfl⟩ : syracuseStep 3269357 = 1226009) (by norm_num)
theorem B2327285 : Blo 1451545 2327285 := bbase (se 5 (by rfl) ⟨109091, by rfl⟩ : syracuseStep 2327285 = 218183) (by norm_num)
theorem B2179829 : Blo 1451545 2179829 := bbase (se 5 (by rfl) ⟨102179, by rfl⟩ : syracuseStep 2179829 = 204359) (by norm_num)
theorem B2450189 : Blo 1451545 2450189 := bbase (se 3 (by rfl) ⟨459410, by rfl⟩ : syracuseStep 2450189 = 918821) (by norm_num)
theorem B2179853 : Blo 1451545 2179853 := bbase (se 3 (by rfl) ⟨408722, by rfl⟩ : syracuseStep 2179853 = 817445) (by norm_num)
theorem B2179877 : Blo 1451545 2179877 := bbase (se 4 (by rfl) ⟨204363, by rfl⟩ : syracuseStep 2179877 = 408727) (by norm_num)
theorem B3269429 : Blo 1451545 3269429 := bbase (se 5 (by rfl) ⟨153254, by rfl⟩ : syracuseStep 3269429 = 306509) (by norm_num)
theorem B2179901 : Blo 1451545 2179901 := bbase (se 3 (by rfl) ⟨408731, by rfl⟩ : syracuseStep 2179901 = 817463) (by norm_num)
theorem B2179925 : Blo 1451545 2179925 := bbase (se 9 (by rfl) ⟨6386, by rfl⟩ : syracuseStep 2179925 = 12773) (by norm_num)
theorem B2179949 : Blo 1451545 2179949 := bbase (se 3 (by rfl) ⟨408740, by rfl⟩ : syracuseStep 2179949 = 817481) (by norm_num)
theorem B3269501 : Blo 1451545 3269501 := bbase (se 3 (by rfl) ⟨613031, by rfl⟩ : syracuseStep 3269501 = 1226063) (by norm_num)
theorem B2179973 : Blo 1451545 2179973 := bbase (se 4 (by rfl) ⟨204372, by rfl⟩ : syracuseStep 2179973 = 408745) (by norm_num)
theorem B2450317 : Blo 1451545 2450317 := bbase (se 3 (by rfl) ⟨459434, by rfl⟩ : syracuseStep 2450317 = 918869) (by norm_num)
theorem B2179997 : Blo 1451545 2179997 := bbase (se 3 (by rfl) ⟨408749, by rfl⟩ : syracuseStep 2179997 = 817499) (by norm_num)
theorem B3679141 : Blo 1451545 3679141 := bbase (se 4 (by rfl) ⟨344919, by rfl⟩ : syracuseStep 3679141 = 689839) (by norm_num)
theorem B2180021 : Blo 1451545 2180021 := bbase (se 5 (by rfl) ⟨102188, by rfl⟩ : syracuseStep 2180021 = 204377) (by norm_num)
theorem B3269573 : Blo 1451545 3269573 := bbase (se 4 (by rfl) ⟨306522, by rfl⟩ : syracuseStep 3269573 = 613045) (by norm_num)
theorem B2180045 : Blo 1451545 2180045 := bbase (se 3 (by rfl) ⟨408758, by rfl⟩ : syracuseStep 2180045 = 817517) (by norm_num)
theorem B4899797 : Blo 1451545 4899797 := bbase (se 7 (by rfl) ⟨57419, by rfl⟩ : syracuseStep 4899797 = 114839) (by norm_num)
theorem B4137941 : Blo 1451545 4137941 := bbase (se 7 (by rfl) ⟨48491, by rfl⟩ : syracuseStep 4137941 = 96983) (by norm_num)
theorem B2450405 : Blo 1451545 2450405 := bbase (se 4 (by rfl) ⟨229725, by rfl⟩ : syracuseStep 2450405 = 459451) (by norm_num)
theorem B2180069 : Blo 1451545 2180069 := bbase (se 4 (by rfl) ⟨204381, by rfl⟩ : syracuseStep 2180069 = 408763) (by norm_num)
theorem B2180093 : Blo 1451545 2180093 := bbase (se 3 (by rfl) ⟨408767, by rfl⟩ : syracuseStep 2180093 = 817535) (by norm_num)
theorem B3269645 : Blo 1451545 3269645 := bbase (se 3 (by rfl) ⟨613058, by rfl⟩ : syracuseStep 3269645 = 1226117) (by norm_num)
theorem B2180117 : Blo 1451545 2180117 := bbase (se 6 (by rfl) ⟨51096, by rfl⟩ : syracuseStep 2180117 = 102193) (by norm_num)
theorem B3679253 : Blo 1451545 3679253 := bbase (se 6 (by rfl) ⟨86232, by rfl⟩ : syracuseStep 3679253 = 172465) (by norm_num)
theorem B5514277 : Blo 1451545 5514277 := bbase (se 4 (by rfl) ⟨516963, by rfl⟩ : syracuseStep 5514277 = 1033927) (by norm_num)
theorem B2180141 : Blo 1451545 2180141 := bbase (se 3 (by rfl) ⟨408776, by rfl⟩ : syracuseStep 2180141 = 817553) (by norm_num)
theorem B2180165 : Blo 1451545 2180165 := bbase (se 4 (by rfl) ⟨204390, by rfl⟩ : syracuseStep 2180165 = 408781) (by norm_num)
theorem B6202453 : Blo 1451545 6202453 := bbase (se 8 (by rfl) ⟨36342, by rfl⟩ : syracuseStep 6202453 = 72685) (by norm_num)
theorem B3269717 : Blo 1451545 3269717 := bbase (se 8 (by rfl) ⟨19158, by rfl⟩ : syracuseStep 3269717 = 38317) (by norm_num)
theorem B2180189 : Blo 1451545 2180189 := bbase (se 3 (by rfl) ⟨408785, by rfl⟩ : syracuseStep 2180189 = 817571) (by norm_num)
theorem B6202469 : Blo 1451545 6202469 := bbase (se 4 (by rfl) ⟨581481, by rfl⟩ : syracuseStep 6202469 = 1162963) (by norm_num)
theorem B2450533 : Blo 1451545 2450533 := bbase (se 4 (by rfl) ⟨229737, by rfl⟩ : syracuseStep 2450533 = 459475) (by norm_num)
theorem B8275061 : Blo 1451545 8275061 := bbase (se 5 (by rfl) ⟨387893, by rfl⟩ : syracuseStep 8275061 = 775787) (by norm_num)
theorem B2180213 : Blo 1451545 2180213 := bbase (se 5 (by rfl) ⟨102197, by rfl⟩ : syracuseStep 2180213 = 204395) (by norm_num)
theorem B2180237 : Blo 1451545 2180237 := bbase (se 3 (by rfl) ⟨408794, by rfl⟩ : syracuseStep 2180237 = 817589) (by norm_num)
theorem B3269789 : Blo 1451545 3269789 := bbase (se 3 (by rfl) ⟨613085, by rfl⟩ : syracuseStep 3269789 = 1226171) (by norm_num)
theorem B2180261 : Blo 1451545 2180261 := bbase (se 4 (by rfl) ⟨204399, by rfl⟩ : syracuseStep 2180261 = 408799) (by norm_num)
theorem B2450621 : Blo 1451545 2450621 := bbase (se 3 (by rfl) ⟨459491, by rfl⟩ : syracuseStep 2450621 = 918983) (by norm_num)
theorem B2180285 : Blo 1451545 2180285 := bbase (se 3 (by rfl) ⟨408803, by rfl⟩ : syracuseStep 2180285 = 817607) (by norm_num)
theorem B2180309 : Blo 1451545 2180309 := bbase (se 7 (by rfl) ⟨25550, by rfl⟩ : syracuseStep 2180309 = 51101) (by norm_num)
theorem B3269861 : Blo 1451545 3269861 := bbase (se 4 (by rfl) ⟨306549, by rfl⟩ : syracuseStep 3269861 = 613099) (by norm_num)
theorem B3269933 : Blo 1451545 3269933 := bbase (se 3 (by rfl) ⟨613112, by rfl⟩ : syracuseStep 3269933 = 1226225) (by norm_num)
theorem B2450749 : Blo 1451545 2450749 := bbase (se 3 (by rfl) ⟨459515, by rfl⟩ : syracuseStep 2450749 = 919031) (by norm_num)
theorem B5514581 : Blo 1451545 5514581 := bbase (se 12 (by rfl) ⟨2019, by rfl⟩ : syracuseStep 5514581 = 4039) (by norm_num)
theorem B3270005 : Blo 1451545 3270005 := bbase (se 5 (by rfl) ⟨153281, by rfl⟩ : syracuseStep 3270005 = 306563) (by norm_num)
theorem B4900229 : Blo 1451545 4900229 := bbase (se 4 (by rfl) ⟨459396, by rfl⟩ : syracuseStep 4900229 = 918793) (by norm_num)
theorem B12404117 : Blo 1451545 12404117 := bbase (se 6 (by rfl) ⟨290721, by rfl⟩ : syracuseStep 12404117 = 581443) (by norm_num)
theorem B2450837 : Blo 1451545 2450837 := bbase (se 6 (by rfl) ⟨57441, by rfl⟩ : syracuseStep 2450837 = 114883) (by norm_num)
theorem B7357877 : Blo 1451545 7357877 := bbase (se 5 (by rfl) ⟨344900, by rfl⟩ : syracuseStep 7357877 = 689801) (by norm_num)
theorem B3270077 : Blo 1451545 3270077 := bbase (se 3 (by rfl) ⟨613139, by rfl⟩ : syracuseStep 3270077 = 1226279) (by norm_num)
theorem B3270149 : Blo 1451545 3270149 := bbase (se 4 (by rfl) ⟨306576, by rfl⟩ : syracuseStep 3270149 = 613153) (by norm_num)
theorem B2450965 : Blo 1451545 2450965 := bbase (se 6 (by rfl) ⟨57444, by rfl⟩ : syracuseStep 2450965 = 114889) (by norm_num)
theorem B5891653 : Blo 1451545 5891653 := bbase (se 4 (by rfl) ⟨552342, by rfl⟩ : syracuseStep 5891653 = 1104685) (by norm_num)
theorem B3270221 : Blo 1451545 3270221 := bbase (se 3 (by rfl) ⟨613166, by rfl⟩ : syracuseStep 3270221 = 1226333) (by norm_num)
theorem B23881301 : Blo 1451545 23881301 := bbase (se 8 (by rfl) ⟨139929, by rfl⟩ : syracuseStep 23881301 = 279859) (by norm_num)
theorem B2451053 : Blo 1451545 2451053 := bbase (se 3 (by rfl) ⟨459572, by rfl⟩ : syracuseStep 2451053 = 919145) (by norm_num)
theorem B3270293 : Blo 1451545 3270293 := bbase (se 6 (by rfl) ⟨76647, by rfl⟩ : syracuseStep 3270293 = 153295) (by norm_num)
theorem B11175637 : Blo 1451545 11175637 := bbase (se 7 (by rfl) ⟨130964, by rfl⟩ : syracuseStep 11175637 = 261929) (by norm_num)
theorem B3270365 : Blo 1451545 3270365 := bbase (se 3 (by rfl) ⟨613193, by rfl⟩ : syracuseStep 3270365 = 1226387) (by norm_num)
theorem B2451181 : Blo 1451545 2451181 := bbase (se 3 (by rfl) ⟨459596, by rfl⟩ : syracuseStep 2451181 = 919193) (by norm_num)
theorem B3270437 : Blo 1451545 3270437 := bbase (se 4 (by rfl) ⟨306603, by rfl⟩ : syracuseStep 3270437 = 613207) (by norm_num)
theorem B4900661 : Blo 1451545 4900661 := bbase (se 5 (by rfl) ⟨229718, by rfl⟩ : syracuseStep 4900661 = 459437) (by norm_num)
theorem B2451269 : Blo 1451545 2451269 := bbase (se 4 (by rfl) ⟨229806, by rfl⟩ : syracuseStep 2451269 = 459613) (by norm_num)
theorem B7350101 : Blo 1451545 7350101 := bbase (se 9 (by rfl) ⟨21533, by rfl⟩ : syracuseStep 7350101 = 43067) (by norm_num)
theorem B3491677 : Blo 1451545 3491677 := bbase (se 3 (by rfl) ⟨654689, by rfl⟩ : syracuseStep 3491677 = 1309379) (by norm_num)
theorem B2451397 : Blo 1451545 2451397 := bbase (se 4 (by rfl) ⟨229818, by rfl⟩ : syracuseStep 2451397 = 459637) (by norm_num)
theorem B2451485 : Blo 1451545 2451485 := bbase (se 3 (by rfl) ⟨459653, by rfl⟩ : syracuseStep 2451485 = 919307) (by norm_num)
theorem B4417573 : Blo 1451545 4417573 := bbase (se 4 (by rfl) ⟨414147, by rfl⟩ : syracuseStep 4417573 = 828295) (by norm_num)
theorem B1837181 : Blo 1451545 1837181 := bbase (se 3 (by rfl) ⟨344471, by rfl⟩ : syracuseStep 1837181 = 688943) (by norm_num)
theorem B4417669 : Blo 1451545 4417669 := bbase (se 4 (by rfl) ⟨414156, by rfl⟩ : syracuseStep 4417669 = 828313) (by norm_num)
theorem B5376149 : Blo 1451545 5376149 := bbase (se 6 (by rfl) ⟨126003, by rfl⟩ : syracuseStep 5376149 = 252007) (by norm_num)
theorem B2451613 : Blo 1451545 2451613 := bbase (se 3 (by rfl) ⟨459677, by rfl⟩ : syracuseStep 2451613 = 919355) (by norm_num)
theorem B1837237 : Blo 1451545 1837237 := bbase (se 5 (by rfl) ⟨86120, by rfl⟩ : syracuseStep 1837237 = 172241) (by norm_num)
theorem B3311813 : Blo 1451545 3311813 := bbase (se 4 (by rfl) ⟨310482, by rfl⟩ : syracuseStep 3311813 = 620965) (by norm_num)
theorem B1550549 : Blo 1451545 1550549 := bbase (se 7 (by rfl) ⟨18170, by rfl⟩ : syracuseStep 1550549 = 36341) (by norm_num)
theorem B4901093 : Blo 1451545 4901093 := bbase (se 4 (by rfl) ⟨459477, by rfl⟩ : syracuseStep 4901093 = 918955) (by norm_num)
theorem B2451701 : Blo 1451545 2451701 := bbase (se 5 (by rfl) ⟨114923, by rfl⟩ : syracuseStep 2451701 = 229847) (by norm_num)
theorem B1837333 : Blo 1451545 1837333 := bbase (se 6 (by rfl) ⟨43062, by rfl⟩ : syracuseStep 1837333 = 86125) (by norm_num)
theorem B2451829 : Blo 1451545 2451829 := bbase (se 5 (by rfl) ⟨114929, by rfl⟩ : syracuseStep 2451829 = 229859) (by norm_num)
theorem B4778389 : Blo 1451545 4778389 := bbase (se 6 (by rfl) ⟨111993, by rfl⟩ : syracuseStep 4778389 = 223987) (by norm_num)
theorem B1837505 : Blo 1451545 1837505 := bbase (se 2 (by rfl) ⟨689064, by rfl⟩ : syracuseStep 1837505 = 1378129) (by norm_num)
theorem B2451917 : Blo 1451545 2451917 := bbase (se 3 (by rfl) ⟨459734, by rfl⟩ : syracuseStep 2451917 = 919469) (by norm_num)
theorem B1837561 : Blo 1451545 1837561 := bbase (se 2 (by rfl) ⟨689085, by rfl⟩ : syracuseStep 1837561 = 1378171) (by norm_num)
theorem B3926549 : Blo 1451545 3926549 := bbase (se 6 (by rfl) ⟨92028, by rfl⟩ : syracuseStep 3926549 = 184057) (by norm_num)
theorem B3492389 : Blo 1451545 3492389 := bbase (se 4 (by rfl) ⟨327411, by rfl⟩ : syracuseStep 3492389 = 654823) (by norm_num)
theorem B2452045 : Blo 1451545 2452045 := bbase (se 3 (by rfl) ⟨459758, by rfl⟩ : syracuseStep 2452045 = 919517) (by norm_num)
theorem B1837657 : Blo 1451545 1837657 := bbase (se 2 (by rfl) ⟨689121, by rfl⟩ : syracuseStep 1837657 = 1378243) (by norm_num)
theorem B1550993 : Blo 1451545 1550993 := bbase (se 2 (by rfl) ⟨581622, by rfl⟩ : syracuseStep 1550993 = 1163245) (by norm_num)
theorem B4901525 : Blo 1451545 4901525 := bbase (se 6 (by rfl) ⟨114879, by rfl⟩ : syracuseStep 4901525 = 229759) (by norm_num)
theorem B2452133 : Blo 1451545 2452133 := bbase (se 4 (by rfl) ⟨229887, by rfl⟩ : syracuseStep 2452133 = 459775) (by norm_num)
theorem B2067125 : Blo 1451545 2067125 := bbase (se 5 (by rfl) ⟨96896, by rfl⟩ : syracuseStep 2067125 = 193793) (by norm_num)
theorem B53005013 : Blo 1451545 53005013 := bbase (se 7 (by rfl) ⟨621152, by rfl⟩ : syracuseStep 53005013 = 1242305) (by norm_num)
theorem B5892821 : Blo 1451545 5892821 := bbase (se 7 (by rfl) ⟨69056, by rfl⟩ : syracuseStep 5892821 = 138113) (by norm_num)
theorem B1633009 : Blo 1451545 1633009 := bbase (se 2 (by rfl) ⟨612378, by rfl⟩ : syracuseStep 1633009 = 1224757) (by norm_num)
theorem B5966581 : Blo 1451545 5966581 := bbase (se 5 (by rfl) ⟨279683, by rfl⟩ : syracuseStep 5966581 = 559367) (by norm_num)
theorem B8833781 : Blo 1451545 8833781 := bbase (se 5 (by rfl) ⟨414083, by rfl⟩ : syracuseStep 8833781 = 828167) (by norm_num)
theorem B1837829 : Blo 1451545 1837829 := bbase (se 4 (by rfl) ⟨172296, by rfl⟩ : syracuseStep 1837829 = 344593) (by norm_num)
theorem B1633045 : Blo 1451545 1633045 := bbase (se 6 (by rfl) ⟨38274, by rfl⟩ : syracuseStep 1633045 = 76549) (by norm_num)
theorem B2452261 : Blo 1451545 2452261 := bbase (se 4 (by rfl) ⟨229899, by rfl⟩ : syracuseStep 2452261 = 459799) (by norm_num)
theorem B1633081 : Blo 1451545 1633081 := bbase (se 2 (by rfl) ⟨612405, by rfl⟩ : syracuseStep 1633081 = 1224811) (by norm_num)
theorem B1837885 : Blo 1451545 1837885 := bbase (se 3 (by rfl) ⟨344603, by rfl⟩ : syracuseStep 1837885 = 689207) (by norm_num)
theorem B6982469 : Blo 1451545 6982469 := bbase (se 4 (by rfl) ⟨654606, by rfl⟩ : syracuseStep 6982469 = 1309213) (by norm_num)
theorem B2796373 : Blo 1451545 2796373 := bbase (se 9 (by rfl) ⟨8192, by rfl⟩ : syracuseStep 2796373 = 16385) (by norm_num)
theorem B1633117 : Blo 1451545 1633117 := bbase (se 3 (by rfl) ⟨306209, by rfl⟩ : syracuseStep 1633117 = 612419) (by norm_num)
theorem B2452349 : Blo 1451545 2452349 := bbase (se 3 (by rfl) ⟨459815, by rfl⟩ : syracuseStep 2452349 = 919631) (by norm_num)
theorem B1633153 : Blo 1451545 1633153 := bbase (se 2 (by rfl) ⟨612432, by rfl⟩ : syracuseStep 1633153 = 1224865) (by norm_num)
theorem B4656005 : Blo 1451545 4656005 := bbase (se 4 (by rfl) ⟨436500, by rfl⟩ : syracuseStep 4656005 = 873001) (by norm_num)
theorem B1551241 : Blo 1451545 1551241 := bbase (se 2 (by rfl) ⟨581715, by rfl⟩ : syracuseStep 1551241 = 1163431) (by norm_num)
theorem B1837981 : Blo 1451545 1837981 := bbase (se 3 (by rfl) ⟨344621, by rfl⟩ : syracuseStep 1837981 = 689243) (by norm_num)
theorem B1633189 : Blo 1451545 1633189 := bbase (se 4 (by rfl) ⟨153111, by rfl⟩ : syracuseStep 1633189 = 306223) (by norm_num)
theorem B3926981 : Blo 1451545 3926981 := bbase (se 4 (by rfl) ⟨368154, by rfl⟩ : syracuseStep 3926981 = 736309) (by norm_num)
theorem B1633225 : Blo 1451545 1633225 := bbase (se 2 (by rfl) ⟨612459, by rfl⟩ : syracuseStep 1633225 = 1224919) (by norm_num)
theorem B1633261 : Blo 1451545 1633261 := bbase (se 3 (by rfl) ⟨306236, by rfl⟩ : syracuseStep 1633261 = 612473) (by norm_num)
theorem B2452477 : Blo 1451545 2452477 := bbase (se 3 (by rfl) ⟨459839, by rfl⟩ : syracuseStep 2452477 = 919679) (by norm_num)
theorem B1633297 : Blo 1451545 1633297 := bbase (se 2 (by rfl) ⟨612486, by rfl⟩ : syracuseStep 1633297 = 1224973) (by norm_num)
theorem B1633333 : Blo 1451545 1633333 := bbase (se 5 (by rfl) ⟨76562, by rfl⟩ : syracuseStep 1633333 = 153125) (by norm_num)
theorem B4901957 : Blo 1451545 4901957 := bbase (se 4 (by rfl) ⟨459558, by rfl⟩ : syracuseStep 4901957 = 919117) (by norm_num)
theorem B1838153 : Blo 1451545 1838153 := bbase (se 2 (by rfl) ⟨689307, by rfl⟩ : syracuseStep 1838153 = 1378615) (by norm_num)
theorem B2452565 : Blo 1451545 2452565 := bbase (se 8 (by rfl) ⟨14370, by rfl⟩ : syracuseStep 2452565 = 28741) (by norm_num)
theorem B1633369 : Blo 1451545 1633369 := bbase (se 2 (by rfl) ⟨612513, by rfl⟩ : syracuseStep 1633369 = 1225027) (by norm_num)
theorem B7351397 : Blo 1451545 7351397 := bbase (se 4 (by rfl) ⟨689193, by rfl⟩ : syracuseStep 7351397 = 1378387) (by norm_num)
theorem B2944109 : Blo 1451545 2944109 := bbase (se 3 (by rfl) ⟨552020, by rfl⟩ : syracuseStep 2944109 = 1104041) (by norm_num)
theorem B2616437 : Blo 1451545 2616437 := bbase (se 5 (by rfl) ⟨122645, by rfl⟩ : syracuseStep 2616437 = 245291) (by norm_num)
theorem B7851125 : Blo 1451545 7851125 := bbase (se 5 (by rfl) ⟨368021, by rfl⟩ : syracuseStep 7851125 = 736043) (by norm_num)
theorem B1633405 : Blo 1451545 1633405 := bbase (se 3 (by rfl) ⟨306263, by rfl⟩ : syracuseStep 1633405 = 612527) (by norm_num)
theorem B1838209 : Blo 1451545 1838209 := bbase (se 2 (by rfl) ⟨689328, by rfl⟩ : syracuseStep 1838209 = 1378657) (by norm_num)
theorem B1633441 : Blo 1451545 1633441 := bbase (se 2 (by rfl) ⟨612540, by rfl⟩ : syracuseStep 1633441 = 1225081) (by norm_num)
theorem B2755757 : Blo 1451545 2755757 := bbase (se 3 (by rfl) ⟨516704, by rfl⟩ : syracuseStep 2755757 = 1033409) (by norm_num)
theorem B2239661 : Blo 1451545 2239661 := bbase (se 3 (by rfl) ⟨419936, by rfl⟩ : syracuseStep 2239661 = 839873) (by norm_num)
theorem B1633477 : Blo 1451545 1633477 := bbase (se 4 (by rfl) ⟨153138, by rfl⟩ : syracuseStep 1633477 = 306277) (by norm_num)
theorem B2944205 : Blo 1451545 2944205 := bbase (se 3 (by rfl) ⟨552038, by rfl⟩ : syracuseStep 2944205 = 1104077) (by norm_num)
theorem B2452693 : Blo 1451545 2452693 := bbase (se 7 (by rfl) ⟨28742, by rfl⟩ : syracuseStep 2452693 = 57485) (by norm_num)
theorem B1838305 : Blo 1451545 1838305 := bbase (se 2 (by rfl) ⟨689364, by rfl⟩ : syracuseStep 1838305 = 1378729) (by norm_num)
theorem B1633513 : Blo 1451545 1633513 := bbase (se 2 (by rfl) ⟨612567, by rfl⟩ : syracuseStep 1633513 = 1225135) (by norm_num)
theorem B1633549 : Blo 1451545 1633549 := bbase (se 3 (by rfl) ⟨306290, by rfl⟩ : syracuseStep 1633549 = 612581) (by norm_num)
theorem B2452781 : Blo 1451545 2452781 := bbase (se 3 (by rfl) ⟨459896, by rfl⟩ : syracuseStep 2452781 = 919793) (by norm_num)
theorem B1633585 : Blo 1451545 1633585 := bbase (se 2 (by rfl) ⟨612594, by rfl⟩ : syracuseStep 1633585 = 1225189) (by norm_num)
theorem B6204725 : Blo 1451545 6204725 := bbase (se 5 (by rfl) ⟨290846, by rfl⟩ : syracuseStep 6204725 = 581693) (by norm_num)
theorem B1551673 : Blo 1451545 1551673 := bbase (se 2 (by rfl) ⟨581877, by rfl⟩ : syracuseStep 1551673 = 1163755) (by norm_num)
theorem B5107013 : Blo 1451545 5107013 := bbase (se 4 (by rfl) ⟨478782, by rfl⟩ : syracuseStep 5107013 = 957565) (by norm_num)
theorem B1633621 : Blo 1451545 1633621 := bbase (se 11 (by rfl) ⟨1196, by rfl⟩ : syracuseStep 1633621 = 2393) (by norm_num)
theorem B7458149 : Blo 1451545 7458149 := bbase (se 4 (by rfl) ⟨699201, by rfl⟩ : syracuseStep 7458149 = 1398403) (by norm_num)
theorem B1633657 : Blo 1451545 1633657 := bbase (se 2 (by rfl) ⟨612621, by rfl⟩ : syracuseStep 1633657 = 1225243) (by norm_num)
theorem B1551745 : Blo 1451545 1551745 := bbase (se 2 (by rfl) ⟨581904, by rfl⟩ : syracuseStep 1551745 = 1163809) (by norm_num)
theorem B4476293 : Blo 1451545 4476293 := bbase (se 4 (by rfl) ⟨419652, by rfl⟩ : syracuseStep 4476293 = 839305) (by norm_num)
theorem B1838477 : Blo 1451545 1838477 := bbase (se 3 (by rfl) ⟨344714, by rfl⟩ : syracuseStep 1838477 = 689429) (by norm_num)
theorem B2616725 : Blo 1451545 2616725 := bbase (se 6 (by rfl) ⟨61329, by rfl⟩ : syracuseStep 2616725 = 122659) (by norm_num)
theorem B5516693 : Blo 1451545 5516693 := bbase (se 6 (by rfl) ⟨129297, by rfl⟩ : syracuseStep 5516693 = 258595) (by norm_num)
theorem B1633693 : Blo 1451545 1633693 := bbase (se 3 (by rfl) ⟨306317, by rfl⟩ : syracuseStep 1633693 = 612635) (by norm_num)
theorem B2067877 : Blo 1451545 2067877 := bbase (se 4 (by rfl) ⟨193863, by rfl⟩ : syracuseStep 2067877 = 387727) (by norm_num)
theorem B1633729 : Blo 1451545 1633729 := bbase (se 2 (by rfl) ⟨612648, by rfl⟩ : syracuseStep 1633729 = 1225297) (by norm_num)
theorem B1838533 : Blo 1451545 1838533 := bbase (se 4 (by rfl) ⟨172362, by rfl⟩ : syracuseStep 1838533 = 344725) (by norm_num)
theorem B2756045 : Blo 1451545 2756045 := bbase (se 3 (by rfl) ⟨516758, by rfl⟩ : syracuseStep 2756045 = 1033517) (by norm_num)
theorem B3927509 : Blo 1451545 3927509 := bbase (se 7 (by rfl) ⟨46025, by rfl⟩ : syracuseStep 3927509 = 92051) (by norm_num)
theorem B2616797 : Blo 1451545 2616797 := bbase (se 3 (by rfl) ⟨490649, by rfl⟩ : syracuseStep 2616797 = 981299) (by norm_num)
theorem B3100133 : Blo 1451545 3100133 := bbase (se 4 (by rfl) ⟨290637, by rfl⟩ : syracuseStep 3100133 = 581275) (by norm_num)
theorem B1633765 : Blo 1451545 1633765 := bbase (se 4 (by rfl) ⟨153165, by rfl⟩ : syracuseStep 1633765 = 306331) (by norm_num)
theorem B3100141 : Blo 1451545 3100141 := bbase (se 3 (by rfl) ⟨581276, by rfl⟩ : syracuseStep 3100141 = 1162553) (by norm_num)
theorem B4902389 : Blo 1451545 4902389 := bbase (se 5 (by rfl) ⟨229799, by rfl⟩ : syracuseStep 4902389 = 459599) (by norm_num)
theorem B1633801 : Blo 1451545 1633801 := bbase (se 2 (by rfl) ⟨612675, by rfl⟩ : syracuseStep 1633801 = 1225351) (by norm_num)
theorem B1838629 : Blo 1451545 1838629 := bbase (se 4 (by rfl) ⟨172371, by rfl⟩ : syracuseStep 1838629 = 344743) (by norm_num)
theorem B1633837 : Blo 1451545 1633837 := bbase (se 3 (by rfl) ⟨306344, by rfl⟩ : syracuseStep 1633837 = 612689) (by norm_num)
theorem B1633873 : Blo 1451545 1633873 := bbase (se 2 (by rfl) ⟨612702, by rfl⟩ : syracuseStep 1633873 = 1225405) (by norm_num)
theorem B2756197 : Blo 1451545 2756197 := bbase (se 4 (by rfl) ⟨258393, by rfl⟩ : syracuseStep 2756197 = 516787) (by norm_num)
theorem B1633909 : Blo 1451545 1633909 := bbase (se 5 (by rfl) ⟨76589, by rfl⟩ : syracuseStep 1633909 = 153179) (by norm_num)
theorem B2485885 : Blo 1451545 2485885 := bbase (se 3 (by rfl) ⟨466103, by rfl⟩ : syracuseStep 2485885 = 932207) (by norm_num)
theorem B13962901 : Blo 1451545 13962901 := bbase (se 6 (by rfl) ⟨327255, by rfl⟩ : syracuseStep 13962901 = 654511) (by norm_num)
theorem B1633945 : Blo 1451545 1633945 := bbase (se 2 (by rfl) ⟨612729, by rfl⟩ : syracuseStep 1633945 = 1225459) (by norm_num)
theorem B5516981 : Blo 1451545 5516981 := bbase (se 5 (by rfl) ⟨258608, by rfl⟩ : syracuseStep 5516981 = 517217) (by norm_num)
theorem B1633981 : Blo 1451545 1633981 := bbase (se 3 (by rfl) ⟨306371, by rfl⟩ : syracuseStep 1633981 = 612743) (by norm_num)
theorem B1838801 : Blo 1451545 1838801 := bbase (se 2 (by rfl) ⟨689550, by rfl⟩ : syracuseStep 1838801 = 1379101) (by norm_num)
theorem B1634017 : Blo 1451545 1634017 := bbase (se 2 (by rfl) ⟨612756, by rfl⟩ : syracuseStep 1634017 = 1225513) (by norm_num)
theorem B1552117 : Blo 1451545 1552117 := bbase (se 5 (by rfl) ⟨72755, by rfl⟩ : syracuseStep 1552117 = 145511) (by norm_num)
theorem B1634053 : Blo 1451545 1634053 := bbase (se 4 (by rfl) ⟨153192, by rfl⟩ : syracuseStep 1634053 = 306385) (by norm_num)
theorem B1838857 : Blo 1451545 1838857 := bbase (se 2 (by rfl) ⟨689571, by rfl⟩ : syracuseStep 1838857 = 1379143) (by norm_num)
theorem B1634089 : Blo 1451545 1634089 := bbase (se 2 (by rfl) ⟨612783, by rfl⟩ : syracuseStep 1634089 = 1225567) (by norm_num)
theorem B1634125 : Blo 1451545 1634125 := bbase (se 3 (by rfl) ⟨306398, by rfl⟩ : syracuseStep 1634125 = 612797) (by norm_num)
theorem B1838953 : Blo 1451545 1838953 := bbase (se 2 (by rfl) ⟨689607, by rfl⟩ : syracuseStep 1838953 = 1379215) (by norm_num)
theorem B1634161 : Blo 1451545 1634161 := bbase (se 2 (by rfl) ⟨612810, by rfl⟩ : syracuseStep 1634161 = 1225621) (by norm_num)
theorem B8269685 : Blo 1451545 8269685 := bbase (se 5 (by rfl) ⟨387641, by rfl⟩ : syracuseStep 8269685 = 775283) (by norm_num)
theorem B2756501 : Blo 1451545 2756501 := bbase (se 6 (by rfl) ⟨64605, by rfl⟩ : syracuseStep 2756501 = 129211) (by norm_num)
theorem B1634197 : Blo 1451545 1634197 := bbase (se 6 (by rfl) ⟨38301, by rfl⟩ : syracuseStep 1634197 = 76603) (by norm_num)
theorem B4902821 : Blo 1451545 4902821 := bbase (se 4 (by rfl) ⟨459639, by rfl⟩ : syracuseStep 4902821 = 919279) (by norm_num)
theorem B1634233 : Blo 1451545 1634233 := bbase (se 2 (by rfl) ⟨612837, by rfl⟩ : syracuseStep 1634233 = 1225675) (by norm_num)
theorem B39727061 : Blo 1451545 39727061 := bbase (se 7 (by rfl) ⟨465551, by rfl⟩ : syracuseStep 39727061 = 931103) (by norm_num)
theorem B1634269 : Blo 1451545 1634269 := bbase (se 3 (by rfl) ⟨306425, by rfl⟩ : syracuseStep 1634269 = 612851) (by norm_num)
theorem B1634305 : Blo 1451545 1634305 := bbase (se 2 (by rfl) ⟨612864, by rfl⟩ : syracuseStep 1634305 = 1225729) (by norm_num)
theorem B1839125 : Blo 1451545 1839125 := bbase (se 6 (by rfl) ⟨43104, by rfl⟩ : syracuseStep 1839125 = 86209) (by norm_num)
theorem B1634341 : Blo 1451545 1634341 := bbase (se 4 (by rfl) ⟨153219, by rfl⟩ : syracuseStep 1634341 = 306439) (by norm_num)
theorem B1634377 : Blo 1451545 1634377 := bbase (se 2 (by rfl) ⟨612891, by rfl⟩ : syracuseStep 1634377 = 1225783) (by norm_num)
theorem B1839181 : Blo 1451545 1839181 := bbase (se 3 (by rfl) ⟨344846, by rfl⟩ : syracuseStep 1839181 = 689693) (by norm_num)
theorem B1634413 : Blo 1451545 1634413 := bbase (se 3 (by rfl) ⟨306452, by rfl⟩ : syracuseStep 1634413 = 612905) (by norm_num)
theorem B1634449 : Blo 1451545 1634449 := bbase (se 2 (by rfl) ⟨612918, by rfl⟩ : syracuseStep 1634449 = 1225837) (by norm_num)
theorem B3674261 : Blo 1451545 3674261 := bbase (se 6 (by rfl) ⟨86115, by rfl⟩ : syracuseStep 3674261 = 172231) (by norm_num)
theorem B1839277 : Blo 1451545 1839277 := bbase (se 3 (by rfl) ⟨344864, by rfl⟩ : syracuseStep 1839277 = 689729) (by norm_num)
theorem B1634485 : Blo 1451545 1634485 := bbase (se 5 (by rfl) ⟨76616, by rfl⟩ : syracuseStep 1634485 = 153233) (by norm_num)
theorem B1863869 : Blo 1451545 1863869 := bbase (se 3 (by rfl) ⟨349475, by rfl⟩ : syracuseStep 1863869 = 698951) (by norm_num)
theorem B2068669 : Blo 1451545 2068669 := bbase (se 3 (by rfl) ⟨387875, by rfl⟩ : syracuseStep 2068669 = 775751) (by norm_num)
theorem B11030741 : Blo 1451545 11030741 := bbase (se 7 (by rfl) ⟨129266, by rfl⟩ : syracuseStep 11030741 = 258533) (by norm_num)
theorem B1634521 : Blo 1451545 1634521 := bbase (se 2 (by rfl) ⟨612945, by rfl⟩ : syracuseStep 1634521 = 1225891) (by norm_num)
theorem B1634557 : Blo 1451545 1634557 := bbase (se 3 (by rfl) ⟨306479, by rfl⟩ : syracuseStep 1634557 = 612959) (by norm_num)
theorem B1634593 : Blo 1451545 1634593 := bbase (se 2 (by rfl) ⟨612972, by rfl⟩ : syracuseStep 1634593 = 1225945) (by norm_num)
theorem B12407093 : Blo 1451545 12407093 := bbase (se 5 (by rfl) ⟨581582, by rfl⟩ : syracuseStep 12407093 = 1163165) (by norm_num)
theorem B1634629 : Blo 1451545 1634629 := bbase (se 4 (by rfl) ⟨153246, by rfl⟩ : syracuseStep 1634629 = 306493) (by norm_num)
theorem B4903253 : Blo 1451545 4903253 := bbase (se 10 (by rfl) ⟨7182, by rfl⟩ : syracuseStep 4903253 = 14365) (by norm_num)
theorem B1839449 : Blo 1451545 1839449 := bbase (se 2 (by rfl) ⟨689793, by rfl⟩ : syracuseStep 1839449 = 1379587) (by norm_num)
theorem B1634665 : Blo 1451545 1634665 := bbase (se 2 (by rfl) ⟨612999, by rfl⟩ : syracuseStep 1634665 = 1225999) (by norm_num)
theorem B7352693 : Blo 1451545 7352693 := bbase (se 5 (by rfl) ⟨344657, by rfl⟩ : syracuseStep 7352693 = 689315) (by norm_num)
theorem B1634701 : Blo 1451545 1634701 := bbase (se 3 (by rfl) ⟨306506, by rfl⟩ : syracuseStep 1634701 = 613013) (by norm_num)
theorem B1839505 : Blo 1451545 1839505 := bbase (se 2 (by rfl) ⟨689814, by rfl⟩ : syracuseStep 1839505 = 1379629) (by norm_num)
theorem B2208149 : Blo 1451545 2208149 := bbase (se 6 (by rfl) ⟨51753, by rfl⟩ : syracuseStep 2208149 = 103507) (by norm_num)
theorem B13250965 : Blo 1451545 13250965 := bbase (se 6 (by rfl) ⟨310569, by rfl⟩ : syracuseStep 13250965 = 621139) (by norm_num)
theorem B1634737 : Blo 1451545 1634737 := bbase (se 2 (by rfl) ⟨613026, by rfl⟩ : syracuseStep 1634737 = 1226053) (by norm_num)
theorem B1634773 : Blo 1451545 1634773 := bbase (se 7 (by rfl) ⟨19157, by rfl⟩ : syracuseStep 1634773 = 38315) (by norm_num)
theorem B3674605 : Blo 1451545 3674605 := bbase (se 3 (by rfl) ⟨688988, by rfl⟩ : syracuseStep 3674605 = 1377977) (by norm_num)
theorem B1839601 : Blo 1451545 1839601 := bbase (se 2 (by rfl) ⟨689850, by rfl⟩ : syracuseStep 1839601 = 1379701) (by norm_num)
theorem B1634809 : Blo 1451545 1634809 := bbase (se 2 (by rfl) ⟨613053, by rfl⟩ : syracuseStep 1634809 = 1226107) (by norm_num)
theorem B2069005 : Blo 1451545 2069005 := bbase (se 3 (by rfl) ⟨387938, by rfl⟩ : syracuseStep 2069005 = 775877) (by norm_num)
theorem B1634845 : Blo 1451545 1634845 := bbase (se 3 (by rfl) ⟨306533, by rfl⟩ : syracuseStep 1634845 = 613067) (by norm_num)
theorem B1634881 : Blo 1451545 1634881 := bbase (se 2 (by rfl) ⟨613080, by rfl⟩ : syracuseStep 1634881 = 1226161) (by norm_num)
theorem B3101269 : Blo 1451545 3101269 := bbase (se 8 (by rfl) ⟨18171, by rfl⟩ : syracuseStep 3101269 = 36343) (by norm_num)
theorem B3674717 : Blo 1451545 3674717 := bbase (se 3 (by rfl) ⟨689009, by rfl⟩ : syracuseStep 3674717 = 1378019) (by norm_num)
theorem B1634917 : Blo 1451545 1634917 := bbase (se 4 (by rfl) ⟨153273, by rfl⟩ : syracuseStep 1634917 = 306547) (by norm_num)
theorem B11022965 : Blo 1451545 11022965 := bbase (se 5 (by rfl) ⟨516701, by rfl⟩ : syracuseStep 11022965 = 1033403) (by norm_num)
theorem B2757253 : Blo 1451545 2757253 := bbase (se 4 (by rfl) ⟨258492, by rfl⟩ : syracuseStep 2757253 = 516985) (by norm_num)
theorem B1634953 : Blo 1451545 1634953 := bbase (se 2 (by rfl) ⟨613107, by rfl⟩ : syracuseStep 1634953 = 1226215) (by norm_num)
theorem B6976165 : Blo 1451545 6976165 := bbase (se 4 (by rfl) ⟨654015, by rfl⟩ : syracuseStep 6976165 = 1308031) (by norm_num)
theorem B1634989 : Blo 1451545 1634989 := bbase (se 3 (by rfl) ⟨306560, by rfl⟩ : syracuseStep 1634989 = 613121) (by norm_num)
theorem B1635025 : Blo 1451545 1635025 := bbase (se 2 (by rfl) ⟨613134, by rfl⟩ : syracuseStep 1635025 = 1226269) (by norm_num)
theorem B2069221 : Blo 1451545 2069221 := bbase (se 4 (by rfl) ⟨193989, by rfl⟩ : syracuseStep 2069221 = 387979) (by norm_num)
theorem B1635061 : Blo 1451545 1635061 := bbase (se 5 (by rfl) ⟨76643, by rfl⟩ : syracuseStep 1635061 = 153287) (by norm_num)
theorem B4903685 : Blo 1451545 4903685 := bbase (se 4 (by rfl) ⟨459720, by rfl⟩ : syracuseStep 4903685 = 919441) (by norm_num)
theorem B2519813 : Blo 1451545 2519813 := bbase (se 4 (by rfl) ⟨236232, by rfl⟩ : syracuseStep 2519813 = 472465) (by norm_num)
theorem B2757397 : Blo 1451545 2757397 := bbase (se 6 (by rfl) ⟨64626, by rfl⟩ : syracuseStep 2757397 = 129253) (by norm_num)
theorem B1635097 : Blo 1451545 1635097 := bbase (se 2 (by rfl) ⟨613161, by rfl⟩ : syracuseStep 1635097 = 1226323) (by norm_num)
theorem B3674909 : Blo 1451545 3674909 := bbase (se 3 (by rfl) ⟨689045, by rfl⟩ : syracuseStep 3674909 = 1378091) (by norm_num)
theorem B2519837 : Blo 1451545 2519837 := bbase (se 3 (by rfl) ⟨472469, by rfl⟩ : syracuseStep 2519837 = 944939) (by norm_num)
theorem B1635133 : Blo 1451545 1635133 := bbase (se 3 (by rfl) ⟨306587, by rfl⟩ : syracuseStep 1635133 = 613175) (by norm_num)
theorem B3683141 : Blo 1451545 3683141 := bbase (se 4 (by rfl) ⟨345294, by rfl⟩ : syracuseStep 3683141 = 690589) (by norm_num)
theorem B6714181 : Blo 1451545 6714181 := bbase (se 4 (by rfl) ⟨629454, by rfl⟩ : syracuseStep 6714181 = 1258909) (by norm_num)
theorem B8835925 : Blo 1451545 8835925 := bbase (se 9 (by rfl) ⟨25886, by rfl⟩ : syracuseStep 8835925 = 51773) (by norm_num)
theorem B5518165 : Blo 1451545 5518165 := bbase (se 9 (by rfl) ⟨16166, by rfl⟩ : syracuseStep 5518165 = 32333) (by norm_num)
theorem B1635169 : Blo 1451545 1635169 := bbase (se 2 (by rfl) ⟨613188, by rfl⟩ : syracuseStep 1635169 = 1226377) (by norm_num)
theorem B4133749 : Blo 1451545 4133749 := bbase (se 5 (by rfl) ⟨193769, by rfl⟩ : syracuseStep 4133749 = 387539) (by norm_num)
theorem B1635205 : Blo 1451545 1635205 := bbase (se 4 (by rfl) ⟨153300, by rfl⟩ : syracuseStep 1635205 = 306601) (by norm_num)
theorem B1962901 : Blo 1451545 1962901 := bbase (se 6 (by rfl) ⟨46005, by rfl⟩ : syracuseStep 1962901 = 92011) (by norm_num)
theorem B2757557 : Blo 1451545 2757557 := bbase (se 5 (by rfl) ⟨129260, by rfl⟩ : syracuseStep 2757557 = 258521) (by norm_num)
theorem B3101645 : Blo 1451545 3101645 := bbase (se 3 (by rfl) ⟨581558, by rfl⟩ : syracuseStep 3101645 = 1163117) (by norm_num)
theorem B4133909 : Blo 1451545 4133909 := bbase (se 6 (by rfl) ⟨96888, by rfl⟩ : syracuseStep 4133909 = 193777) (by norm_num)
theorem B8270869 : Blo 1451545 8270869 := bbase (se 6 (by rfl) ⟨193848, by rfl⟩ : syracuseStep 8270869 = 387697) (by norm_num)
theorem B2757701 : Blo 1451545 2757701 := bbase (se 4 (by rfl) ⟨258534, by rfl⟩ : syracuseStep 2757701 = 517069) (by norm_num)
theorem B2069597 : Blo 1451545 2069597 := bbase (se 3 (by rfl) ⟨388049, by rfl⟩ : syracuseStep 2069597 = 776099) (by norm_num)
theorem B3675253 : Blo 1451545 3675253 := bbase (se 5 (by rfl) ⟨172277, by rfl⟩ : syracuseStep 3675253 = 344555) (by norm_num)
theorem B5231749 : Blo 1451545 5231749 := bbase (se 4 (by rfl) ⟨490476, by rfl⟩ : syracuseStep 5231749 = 980953) (by norm_num)
theorem B5518469 : Blo 1451545 5518469 := bbase (se 4 (by rfl) ⟨517356, by rfl⟩ : syracuseStep 5518469 = 1034713) (by norm_num)
theorem B2389141 : Blo 1451545 2389141 := bbase (se 6 (by rfl) ⟨55995, by rfl⟩ : syracuseStep 2389141 = 111991) (by norm_num)
theorem B4904117 : Blo 1451545 4904117 := bbase (se 5 (by rfl) ⟨229880, by rfl⟩ : syracuseStep 4904117 = 459761) (by norm_num)
theorem B3675365 : Blo 1451545 3675365 := bbase (se 4 (by rfl) ⟨344565, by rfl⟩ : syracuseStep 3675365 = 689131) (by norm_num)
theorem B4134149 : Blo 1451545 4134149 := bbase (se 4 (by rfl) ⟨387576, by rfl⟩ : syracuseStep 4134149 = 775153) (by norm_num)
theorem B2757989 : Blo 1451545 2757989 := bbase (se 4 (by rfl) ⟨258561, by rfl⟩ : syracuseStep 2757989 = 517123) (by norm_num)
theorem B3675557 : Blo 1451545 3675557 := bbase (se 4 (by rfl) ⟨344583, by rfl⟩ : syracuseStep 3675557 = 689167) (by norm_num)
theorem B2209189 : Blo 1451545 2209189 := bbase (se 4 (by rfl) ⟨207111, by rfl⟩ : syracuseStep 2209189 = 414223) (by norm_num)
theorem B4134341 : Blo 1451545 4134341 := bbase (se 4 (by rfl) ⟨387594, by rfl⟩ : syracuseStep 4134341 = 775189) (by norm_num)
theorem B12269045 : Blo 1451545 12269045 := bbase (se 5 (by rfl) ⟨575111, by rfl⟩ : syracuseStep 12269045 = 1150223) (by norm_num)
theorem B3266045 : Blo 1451545 3266045 := bbase (se 3 (by rfl) ⟨612383, by rfl⟩ : syracuseStep 3266045 = 1224767) (by norm_num)
theorem B2758141 : Blo 1451545 2758141 := bbase (se 3 (by rfl) ⟨517151, by rfl⟩ : syracuseStep 2758141 = 1034303) (by norm_num)
theorem B1472005 : Blo 1451545 1472005 := bbase (se 4 (by rfl) ⟨138000, by rfl⟩ : syracuseStep 1472005 = 276001) (by norm_num)
theorem B9942581 : Blo 1451545 9942581 := bbase (se 5 (by rfl) ⟨466058, by rfl⟩ : syracuseStep 9942581 = 932117) (by norm_num)
theorem B3266117 : Blo 1451545 3266117 := bbase (se 4 (by rfl) ⟨306198, by rfl⟩ : syracuseStep 3266117 = 612397) (by norm_num)
theorem B4904549 : Blo 1451545 4904549 := bbase (se 4 (by rfl) ⟨459801, by rfl⟩ : syracuseStep 4904549 = 919603) (by norm_num)
theorem B7353989 : Blo 1451545 7353989 := bbase (se 4 (by rfl) ⟨689436, by rfl⟩ : syracuseStep 7353989 = 1378873) (by norm_num)
theorem B3266189 : Blo 1451545 3266189 := bbase (se 3 (by rfl) ⟨612410, by rfl⟩ : syracuseStep 3266189 = 1224821) (by norm_num)
theorem B3266261 : Blo 1451545 3266261 := bbase (se 7 (by rfl) ⟨38276, by rfl⟩ : syracuseStep 3266261 = 76553) (by norm_num)
theorem B2209493 : Blo 1451545 2209493 := bbase (se 7 (by rfl) ⟨25892, by rfl⟩ : syracuseStep 2209493 = 51785) (by norm_num)
theorem B3675901 : Blo 1451545 3675901 := bbase (se 3 (by rfl) ⟨689231, by rfl⟩ : syracuseStep 3675901 = 1378463) (by norm_num)
theorem B1472261 : Blo 1451545 1472261 := bbase (se 4 (by rfl) ⟨138024, by rfl⟩ : syracuseStep 1472261 = 276049) (by norm_num)
theorem B3266333 : Blo 1451545 3266333 := bbase (se 3 (by rfl) ⟨612437, by rfl⟩ : syracuseStep 3266333 = 1224875) (by norm_num)
theorem B2209565 : Blo 1451545 2209565 := bbase (se 3 (by rfl) ⟨414293, by rfl⟩ : syracuseStep 2209565 = 828587) (by norm_num)
theorem B2758445 : Blo 1451545 2758445 := bbase (se 3 (by rfl) ⟨517208, by rfl⟩ : syracuseStep 2758445 = 1034417) (by norm_num)
theorem B3143477 : Blo 1451545 3143477 := bbase (se 5 (by rfl) ⟨147350, by rfl⟩ : syracuseStep 3143477 = 294701) (by norm_num)
theorem B3266405 : Blo 1451545 3266405 := bbase (se 4 (by rfl) ⟨306225, by rfl⟩ : syracuseStep 3266405 = 612451) (by norm_num)
theorem B4650853 : Blo 1451545 4650853 := bbase (se 4 (by rfl) ⟨436017, by rfl⟩ : syracuseStep 4650853 = 872035) (by norm_num)
theorem B3676013 : Blo 1451545 3676013 := bbase (se 3 (by rfl) ⟨689252, by rfl⟩ : syracuseStep 3676013 = 1378505) (by norm_num)
theorem B3266477 : Blo 1451545 3266477 := bbase (se 3 (by rfl) ⟨612464, by rfl⟩ : syracuseStep 3266477 = 1224929) (by norm_num)
theorem B3266549 : Blo 1451545 3266549 := bbase (se 5 (by rfl) ⟨153119, by rfl⟩ : syracuseStep 3266549 = 306239) (by norm_num)
theorem B4904981 : Blo 1451545 4904981 := bbase (se 6 (by rfl) ⟨114960, by rfl⟩ : syracuseStep 4904981 = 229921) (by norm_num)
theorem B2095141 : Blo 1451545 2095141 := bbase (se 4 (by rfl) ⟨196419, by rfl⟩ : syracuseStep 2095141 = 392839) (by norm_num)
theorem B3676205 : Blo 1451545 3676205 := bbase (se 3 (by rfl) ⟨689288, by rfl⟩ : syracuseStep 3676205 = 1378577) (by norm_num)
theorem B3487805 : Blo 1451545 3487805 := bbase (se 3 (by rfl) ⟨653963, by rfl⟩ : syracuseStep 3487805 = 1307927) (by norm_num)
theorem B3266621 : Blo 1451545 3266621 := bbase (se 3 (by rfl) ⟨612491, by rfl⟩ : syracuseStep 3266621 = 1224983) (by norm_num)
theorem B1964101 : Blo 1451545 1964101 := bbase (se 4 (by rfl) ⟨184134, by rfl⟩ : syracuseStep 1964101 = 368269) (by norm_num)
theorem B5232757 : Blo 1451545 5232757 := bbase (se 5 (by rfl) ⟨245285, by rfl⟩ : syracuseStep 5232757 = 490571) (by norm_num)
theorem B3266693 : Blo 1451545 3266693 := bbase (se 4 (by rfl) ⟨306252, by rfl⟩ : syracuseStep 3266693 = 612505) (by norm_num)
theorem B3266765 : Blo 1451545 3266765 := bbase (se 3 (by rfl) ⟨612518, by rfl⟩ : syracuseStep 3266765 = 1225037) (by norm_num)
theorem B3266837 : Blo 1451545 3266837 := bbase (se 6 (by rfl) ⟨76566, by rfl⟩ : syracuseStep 3266837 = 153133) (by norm_num)
theorem B2177333 : Blo 1451545 2177333 := bbase (se 5 (by rfl) ⟨102062, by rfl⟩ : syracuseStep 2177333 = 204125) (by norm_num)
theorem B2177357 : Blo 1451545 2177357 := bbase (se 3 (by rfl) ⟨408254, by rfl⟩ : syracuseStep 2177357 = 816509) (by norm_num)
theorem B3266909 : Blo 1451545 3266909 := bbase (se 3 (by rfl) ⟨612545, by rfl⟩ : syracuseStep 3266909 = 1225091) (by norm_num)
theorem B2177381 : Blo 1451545 2177381 := bbase (se 4 (by rfl) ⟨204129, by rfl⟩ : syracuseStep 2177381 = 408259) (by norm_num)
theorem B2177405 : Blo 1451545 2177405 := bbase (se 3 (by rfl) ⟨408263, by rfl⟩ : syracuseStep 2177405 = 816527) (by norm_num)
theorem B3676549 : Blo 1451545 3676549 := bbase (se 4 (by rfl) ⟨344676, by rfl⟩ : syracuseStep 3676549 = 689353) (by norm_num)
theorem B2177429 : Blo 1451545 2177429 := bbase (se 6 (by rfl) ⟨51033, by rfl⟩ : syracuseStep 2177429 = 102067) (by norm_num)
theorem B3266981 : Blo 1451545 3266981 := bbase (se 4 (by rfl) ⟨306279, by rfl⟩ : syracuseStep 3266981 = 612559) (by norm_num)
theorem B4135333 : Blo 1451545 4135333 := bbase (se 4 (by rfl) ⟨387687, by rfl⟩ : syracuseStep 4135333 = 775375) (by norm_num)
theorem B2177453 : Blo 1451545 2177453 := bbase (se 3 (by rfl) ⟨408272, by rfl⟩ : syracuseStep 2177453 = 816545) (by norm_num)
theorem B2177477 : Blo 1451545 2177477 := bbase (se 4 (by rfl) ⟨204138, by rfl⟩ : syracuseStep 2177477 = 408277) (by norm_num)
theorem B4905413 : Blo 1451545 4905413 := bbase (se 4 (by rfl) ⟨459882, by rfl⟩ : syracuseStep 4905413 = 919765) (by norm_num)
theorem B9312725 : Blo 1451545 9312725 := bbase (se 7 (by rfl) ⟨109133, by rfl⟩ : syracuseStep 9312725 = 218267) (by norm_num)
theorem B2177501 : Blo 1451545 2177501 := bbase (se 3 (by rfl) ⟨408281, by rfl⟩ : syracuseStep 2177501 = 816563) (by norm_num)
theorem B3267053 : Blo 1451545 3267053 := bbase (se 3 (by rfl) ⟨612572, by rfl⟩ : syracuseStep 3267053 = 1225145) (by norm_num)
theorem B2177525 : Blo 1451545 2177525 := bbase (se 5 (by rfl) ⟨102071, by rfl⟩ : syracuseStep 2177525 = 204143) (by norm_num)
theorem B3676661 : Blo 1451545 3676661 := bbase (se 5 (by rfl) ⟨172343, by rfl⟩ : syracuseStep 3676661 = 344687) (by norm_num)
theorem B2177549 : Blo 1451545 2177549 := bbase (se 3 (by rfl) ⟨408290, by rfl⟩ : syracuseStep 2177549 = 816581) (by norm_num)
theorem B2759197 : Blo 1451545 2759197 := bbase (se 3 (by rfl) ⟨517349, by rfl⟩ : syracuseStep 2759197 = 1034699) (by norm_num)
theorem B2177573 : Blo 1451545 2177573 := bbase (se 4 (by rfl) ⟨204147, by rfl⟩ : syracuseStep 2177573 = 408295) (by norm_num)
theorem B3267125 : Blo 1451545 3267125 := bbase (se 5 (by rfl) ⟨153146, by rfl⟩ : syracuseStep 3267125 = 306293) (by norm_num)
theorem B3103285 : Blo 1451545 3103285 := bbase (se 5 (by rfl) ⟨145466, by rfl⟩ : syracuseStep 3103285 = 290933) (by norm_num)
theorem B2177597 : Blo 1451545 2177597 := bbase (se 3 (by rfl) ⟨408299, by rfl⟩ : syracuseStep 2177597 = 816599) (by norm_num)
theorem B2177621 : Blo 1451545 2177621 := bbase (se 8 (by rfl) ⟨12759, by rfl⟩ : syracuseStep 2177621 = 25519) (by norm_num)
theorem B2177645 : Blo 1451545 2177645 := bbase (se 3 (by rfl) ⟨408308, by rfl⟩ : syracuseStep 2177645 = 816617) (by norm_num)
theorem B3267197 : Blo 1451545 3267197 := bbase (se 3 (by rfl) ⟨612599, by rfl⟩ : syracuseStep 3267197 = 1225199) (by norm_num)
theorem B2177669 : Blo 1451545 2177669 := bbase (se 4 (by rfl) ⟨204156, by rfl⟩ : syracuseStep 2177669 = 408313) (by norm_num)
theorem B2177693 : Blo 1451545 2177693 := bbase (se 3 (by rfl) ⟨408317, by rfl⟩ : syracuseStep 2177693 = 816635) (by norm_num)
theorem B2759341 : Blo 1451545 2759341 := bbase (se 3 (by rfl) ⟨517376, by rfl⟩ : syracuseStep 2759341 = 1034753) (by norm_num)
theorem B2177717 : Blo 1451545 2177717 := bbase (se 5 (by rfl) ⟨102080, by rfl⟩ : syracuseStep 2177717 = 204161) (by norm_num)
theorem B3676853 : Blo 1451545 3676853 := bbase (se 5 (by rfl) ⟨172352, by rfl⟩ : syracuseStep 3676853 = 344705) (by norm_num)
theorem B3267269 : Blo 1451545 3267269 := bbase (se 4 (by rfl) ⟨306306, by rfl⟩ : syracuseStep 3267269 = 612613) (by norm_num)
theorem B2177741 : Blo 1451545 2177741 := bbase (se 3 (by rfl) ⟨408326, by rfl⟩ : syracuseStep 2177741 = 816653) (by norm_num)
theorem B2177765 : Blo 1451545 2177765 := bbase (se 4 (by rfl) ⟨204165, by rfl⟩ : syracuseStep 2177765 = 408331) (by norm_num)
theorem B2177789 : Blo 1451545 2177789 := bbase (se 3 (by rfl) ⟨408335, by rfl⟩ : syracuseStep 2177789 = 816671) (by norm_num)
theorem B3267341 : Blo 1451545 3267341 := bbase (se 3 (by rfl) ⟨612626, by rfl⟩ : syracuseStep 3267341 = 1225253) (by norm_num)
theorem B2177813 : Blo 1451545 2177813 := bbase (se 6 (by rfl) ⟨51042, by rfl⟩ : syracuseStep 2177813 = 102085) (by norm_num)
theorem B3144485 : Blo 1451545 3144485 := bbase (se 4 (by rfl) ⟨294795, by rfl⟩ : syracuseStep 3144485 = 589591) (by norm_num)
theorem B2177837 : Blo 1451545 2177837 := bbase (se 3 (by rfl) ⟨408344, by rfl⟩ : syracuseStep 2177837 = 816689) (by norm_num)
theorem B2177861 : Blo 1451545 2177861 := bbase (se 4 (by rfl) ⟨204174, by rfl⟩ : syracuseStep 2177861 = 408349) (by norm_num)
theorem B3267413 : Blo 1451545 3267413 := bbase (se 9 (by rfl) ⟨9572, by rfl⟩ : syracuseStep 3267413 = 19145) (by norm_num)
theorem B2177885 : Blo 1451545 2177885 := bbase (se 3 (by rfl) ⟨408353, by rfl⟩ : syracuseStep 2177885 = 816707) (by norm_num)
theorem B2177909 : Blo 1451545 2177909 := bbase (se 5 (by rfl) ⟨102089, by rfl⟩ : syracuseStep 2177909 = 204179) (by norm_num)
theorem B2177933 : Blo 1451545 2177933 := bbase (se 3 (by rfl) ⟨408362, by rfl⟩ : syracuseStep 2177933 = 816725) (by norm_num)
theorem B7355285 : Blo 1451545 7355285 := bbase (se 6 (by rfl) ⟨172389, by rfl⟩ : syracuseStep 7355285 = 344779) (by norm_num)
theorem B3267485 : Blo 1451545 3267485 := bbase (se 3 (by rfl) ⟨612653, by rfl⟩ : syracuseStep 3267485 = 1225307) (by norm_num)
theorem B2177957 : Blo 1451545 2177957 := bbase (se 4 (by rfl) ⟨204183, by rfl⟩ : syracuseStep 2177957 = 408367) (by norm_num)
theorem B2177981 : Blo 1451545 2177981 := bbase (se 3 (by rfl) ⟨408371, by rfl⟩ : syracuseStep 2177981 = 816743) (by norm_num)
theorem B2178005 : Blo 1451545 2178005 := bbase (se 7 (by rfl) ⟨25523, by rfl⟩ : syracuseStep 2178005 = 51047) (by norm_num)
theorem B8272853 : Blo 1451545 8272853 := bbase (se 7 (by rfl) ⟨96947, by rfl⟩ : syracuseStep 8272853 = 193895) (by norm_num)
theorem B5594069 : Blo 1451545 5594069 := bbase (se 7 (by rfl) ⟨65555, by rfl⟩ : syracuseStep 5594069 = 131111) (by norm_num)
theorem B3267557 : Blo 1451545 3267557 := bbase (se 4 (by rfl) ⟨306333, by rfl⟩ : syracuseStep 3267557 = 612667) (by norm_num)
theorem B2178029 : Blo 1451545 2178029 := bbase (se 3 (by rfl) ⟨408380, by rfl⟩ : syracuseStep 2178029 = 816761) (by norm_num)
theorem B2178053 : Blo 1451545 2178053 := bbase (se 4 (by rfl) ⟨204192, by rfl⟩ : syracuseStep 2178053 = 408385) (by norm_num)
theorem B3677197 : Blo 1451545 3677197 := bbase (se 3 (by rfl) ⟨689474, by rfl⟩ : syracuseStep 3677197 = 1378949) (by norm_num)
theorem B2178077 : Blo 1451545 2178077 := bbase (se 3 (by rfl) ⟨408389, by rfl⟩ : syracuseStep 2178077 = 816779) (by norm_num)
theorem B3267629 : Blo 1451545 3267629 := bbase (se 3 (by rfl) ⟨612680, by rfl⟩ : syracuseStep 3267629 = 1225361) (by norm_num)
theorem B2178101 : Blo 1451545 2178101 := bbase (se 5 (by rfl) ⟨102098, by rfl⟩ : syracuseStep 2178101 = 204197) (by norm_num)
theorem B2325581 : Blo 1451545 2325581 := bbase (se 3 (by rfl) ⟨436046, by rfl⟩ : syracuseStep 2325581 = 872093) (by norm_num)
theorem B2178125 : Blo 1451545 2178125 := bbase (se 3 (by rfl) ⟨408398, by rfl⟩ : syracuseStep 2178125 = 816797) (by norm_num)
theorem B1989725 : Blo 1451545 1989725 := bbase (se 3 (by rfl) ⟨373073, by rfl⟩ : syracuseStep 1989725 = 746147) (by norm_num)
theorem B2178149 : Blo 1451545 2178149 := bbase (se 4 (by rfl) ⟨204201, by rfl⟩ : syracuseStep 2178149 = 408403) (by norm_num)
theorem B2325613 : Blo 1451545 2325613 := bbase (se 3 (by rfl) ⟨436052, by rfl⟩ : syracuseStep 2325613 = 872105) (by norm_num)
theorem B3267701 : Blo 1451545 3267701 := bbase (se 5 (by rfl) ⟨153173, by rfl⟩ : syracuseStep 3267701 = 306347) (by norm_num)
theorem B2178173 : Blo 1451545 2178173 := bbase (se 3 (by rfl) ⟨408407, by rfl⟩ : syracuseStep 2178173 = 816815) (by norm_num)
theorem B3677309 : Blo 1451545 3677309 := bbase (se 3 (by rfl) ⟨689495, by rfl⟩ : syracuseStep 3677309 = 1378991) (by norm_num)
theorem B2178197 : Blo 1451545 2178197 := bbase (se 6 (by rfl) ⟨51051, by rfl⟩ : syracuseStep 2178197 = 102103) (by norm_num)
theorem B2178221 : Blo 1451545 2178221 := bbase (se 3 (by rfl) ⟨408416, by rfl⟩ : syracuseStep 2178221 = 816833) (by norm_num)
theorem B3267773 : Blo 1451545 3267773 := bbase (se 3 (by rfl) ⟨612707, by rfl⟩ : syracuseStep 3267773 = 1225415) (by norm_num)
theorem B2178245 : Blo 1451545 2178245 := bbase (se 4 (by rfl) ⟨204210, by rfl⟩ : syracuseStep 2178245 = 408421) (by norm_num)
theorem B14351573 : Blo 1451545 14351573 := bbase (se 7 (by rfl) ⟨168182, by rfl⟩ : syracuseStep 14351573 = 336365) (by norm_num)
theorem B2178269 : Blo 1451545 2178269 := bbase (se 3 (by rfl) ⟨408425, by rfl⟩ : syracuseStep 2178269 = 816851) (by norm_num)
theorem B2178293 : Blo 1451545 2178293 := bbase (se 5 (by rfl) ⟨102107, by rfl⟩ : syracuseStep 2178293 = 204215) (by norm_num)
theorem B6208757 : Blo 1451545 6208757 := bbase (se 5 (by rfl) ⟨291035, by rfl⟩ : syracuseStep 6208757 = 582071) (by norm_num)
theorem B3267845 : Blo 1451545 3267845 := bbase (se 4 (by rfl) ⟨306360, by rfl⟩ : syracuseStep 3267845 = 612721) (by norm_num)
theorem B2178317 : Blo 1451545 2178317 := bbase (se 3 (by rfl) ⟨408434, by rfl⟩ : syracuseStep 2178317 = 816869) (by norm_num)
theorem B2178341 : Blo 1451545 2178341 := bbase (se 4 (by rfl) ⟨204219, by rfl⟩ : syracuseStep 2178341 = 408439) (by norm_num)
theorem B2178365 : Blo 1451545 2178365 := bbase (se 3 (by rfl) ⟨408443, by rfl⟩ : syracuseStep 2178365 = 816887) (by norm_num)
theorem B3677501 : Blo 1451545 3677501 := bbase (se 3 (by rfl) ⟨689531, by rfl⟩ : syracuseStep 3677501 = 1379063) (by norm_num)
theorem B3267917 : Blo 1451545 3267917 := bbase (se 3 (by rfl) ⟨612734, by rfl⟩ : syracuseStep 3267917 = 1225469) (by norm_num)
theorem B3145037 : Blo 1451545 3145037 := bbase (se 3 (by rfl) ⟨589694, by rfl⟩ : syracuseStep 3145037 = 1179389) (by norm_num)
theorem B2178389 : Blo 1451545 2178389 := bbase (se 11 (by rfl) ⟨1595, by rfl⟩ : syracuseStep 2178389 = 3191) (by norm_num)
theorem B2178413 : Blo 1451545 2178413 := bbase (se 3 (by rfl) ⟨408452, by rfl⟩ : syracuseStep 2178413 = 816905) (by norm_num)
theorem B2178437 : Blo 1451545 2178437 := bbase (se 4 (by rfl) ⟨204228, by rfl⟩ : syracuseStep 2178437 = 408457) (by norm_num)
theorem B3267989 : Blo 1451545 3267989 := bbase (se 6 (by rfl) ⟨76593, by rfl⟩ : syracuseStep 3267989 = 153187) (by norm_num)
theorem B2178461 : Blo 1451545 2178461 := bbase (se 3 (by rfl) ⟨408461, by rfl⟩ : syracuseStep 2178461 = 816923) (by norm_num)
theorem B1744301 : Blo 1451545 1744301 := bbase (se 3 (by rfl) ⟨327056, by rfl⟩ : syracuseStep 1744301 = 654113) (by norm_num)
theorem B3104173 : Blo 1451545 3104173 := bbase (se 3 (by rfl) ⟨582032, by rfl⟩ : syracuseStep 3104173 = 1164065) (by norm_num)
theorem B2178485 : Blo 1451545 2178485 := bbase (se 5 (by rfl) ⟨102116, by rfl⟩ : syracuseStep 2178485 = 204233) (by norm_num)
theorem B2178509 : Blo 1451545 2178509 := bbase (se 3 (by rfl) ⟨408470, by rfl⟩ : syracuseStep 2178509 = 816941) (by norm_num)
theorem B3268061 : Blo 1451545 3268061 := bbase (se 3 (by rfl) ⟨612761, by rfl⟩ : syracuseStep 3268061 = 1225523) (by norm_num)
theorem B2178533 : Blo 1451545 2178533 := bbase (se 4 (by rfl) ⟨204237, by rfl⟩ : syracuseStep 2178533 = 408475) (by norm_num)
theorem B4136437 : Blo 1451545 4136437 := bbase (se 5 (by rfl) ⟨193895, by rfl⟩ : syracuseStep 4136437 = 387791) (by norm_num)
theorem B2178557 : Blo 1451545 2178557 := bbase (se 3 (by rfl) ⟨408479, by rfl⟩ : syracuseStep 2178557 = 816959) (by norm_num)
theorem B2178581 : Blo 1451545 2178581 := bbase (se 6 (by rfl) ⟨51060, by rfl⟩ : syracuseStep 2178581 = 102121) (by norm_num)
theorem B3268133 : Blo 1451545 3268133 := bbase (se 4 (by rfl) ⟨306387, by rfl⟩ : syracuseStep 3268133 = 612775) (by norm_num)
theorem B2178605 : Blo 1451545 2178605 := bbase (se 3 (by rfl) ⟨408488, by rfl⟩ : syracuseStep 2178605 = 816977) (by norm_num)
theorem B2178629 : Blo 1451545 2178629 := bbase (se 4 (by rfl) ⟨204246, by rfl⟩ : syracuseStep 2178629 = 408493) (by norm_num)
theorem B2178653 : Blo 1451545 2178653 := bbase (se 3 (by rfl) ⟨408497, by rfl⟩ : syracuseStep 2178653 = 816995) (by norm_num)
theorem B5512805 : Blo 1451545 5512805 := bbase (se 4 (by rfl) ⟨516825, by rfl⟩ : syracuseStep 5512805 = 1033651) (by norm_num)
theorem B3268205 : Blo 1451545 3268205 := bbase (se 3 (by rfl) ⟨612788, by rfl⟩ : syracuseStep 3268205 = 1225577) (by norm_num)
theorem B4415093 : Blo 1451545 4415093 := bbase (se 5 (by rfl) ⟨206957, by rfl⟩ : syracuseStep 4415093 = 413915) (by norm_num)
theorem B2178677 : Blo 1451545 2178677 := bbase (se 5 (by rfl) ⟨102125, by rfl⟩ : syracuseStep 2178677 = 204251) (by norm_num)
theorem B6200965 : Blo 1451545 6200965 := bbase (se 4 (by rfl) ⟨581340, by rfl⟩ : syracuseStep 6200965 = 1162681) (by norm_num)
theorem B2178701 : Blo 1451545 2178701 := bbase (se 3 (by rfl) ⟨408506, by rfl⟩ : syracuseStep 2178701 = 817013) (by norm_num)
theorem B9936533 : Blo 1451545 9936533 := bbase (se 6 (by rfl) ⟨232887, by rfl⟩ : syracuseStep 9936533 = 465775) (by norm_num)
theorem B3677845 : Blo 1451545 3677845 := bbase (se 6 (by rfl) ⟨86199, by rfl⟩ : syracuseStep 3677845 = 172399) (by norm_num)
theorem B2178725 : Blo 1451545 2178725 := bbase (se 4 (by rfl) ⟨204255, by rfl⟩ : syracuseStep 2178725 = 408511) (by norm_num)
theorem B3268277 : Blo 1451545 3268277 := bbase (se 5 (by rfl) ⟨153200, by rfl⟩ : syracuseStep 3268277 = 306401) (by norm_num)
theorem B2178749 : Blo 1451545 2178749 := bbase (se 3 (by rfl) ⟨408515, by rfl⟩ : syracuseStep 2178749 = 817031) (by norm_num)
theorem B2178773 : Blo 1451545 2178773 := bbase (se 7 (by rfl) ⟨25532, by rfl⟩ : syracuseStep 2178773 = 51065) (by norm_num)
theorem B2178797 : Blo 1451545 2178797 := bbase (se 3 (by rfl) ⟨408524, by rfl⟩ : syracuseStep 2178797 = 817049) (by norm_num)
theorem B3268349 : Blo 1451545 3268349 := bbase (se 3 (by rfl) ⟨612815, by rfl⟩ : syracuseStep 3268349 = 1225631) (by norm_num)
theorem B2391805 : Blo 1451545 2391805 := bbase (se 3 (by rfl) ⟨448463, by rfl⟩ : syracuseStep 2391805 = 896927) (by norm_num)
theorem B2178821 : Blo 1451545 2178821 := bbase (se 4 (by rfl) ⟨204264, by rfl⟩ : syracuseStep 2178821 = 408529) (by norm_num)
theorem B3677957 : Blo 1451545 3677957 := bbase (se 4 (by rfl) ⟨344808, by rfl⟩ : syracuseStep 3677957 = 689617) (by norm_num)
theorem B2178845 : Blo 1451545 2178845 := bbase (se 3 (by rfl) ⟨408533, by rfl⟩ : syracuseStep 2178845 = 817067) (by norm_num)
theorem B3489581 : Blo 1451545 3489581 := bbase (se 3 (by rfl) ⟨654296, by rfl⟩ : syracuseStep 3489581 = 1308593) (by norm_num)
theorem B2178869 : Blo 1451545 2178869 := bbase (se 5 (by rfl) ⟨102134, by rfl⟩ : syracuseStep 2178869 = 204269) (by norm_num)
theorem B3268421 : Blo 1451545 3268421 := bbase (se 4 (by rfl) ⟨306414, by rfl⟩ : syracuseStep 3268421 = 612829) (by norm_num)
theorem B2178893 : Blo 1451545 2178893 := bbase (se 3 (by rfl) ⟨408542, by rfl⟩ : syracuseStep 2178893 = 817085) (by norm_num)
theorem B3358549 : Blo 1451545 3358549 := bbase (se 9 (by rfl) ⟨9839, by rfl⟩ : syracuseStep 3358549 = 19679) (by norm_num)
theorem B2178917 : Blo 1451545 2178917 := bbase (se 4 (by rfl) ⟨204273, by rfl⟩ : syracuseStep 2178917 = 408547) (by norm_num)
theorem B12582773 : Blo 1451545 12582773 := bbase (se 5 (by rfl) ⟨589817, by rfl⟩ : syracuseStep 12582773 = 1179635) (by norm_num)
theorem B2178941 : Blo 1451545 2178941 := bbase (se 3 (by rfl) ⟨408551, by rfl⟩ : syracuseStep 2178941 = 817103) (by norm_num)
theorem B5513093 : Blo 1451545 5513093 := bbase (se 4 (by rfl) ⟨516852, by rfl⟩ : syracuseStep 5513093 = 1033705) (by norm_num)
theorem B3268493 : Blo 1451545 3268493 := bbase (se 3 (by rfl) ⟨612842, by rfl⟩ : syracuseStep 3268493 = 1225685) (by norm_num)
theorem B2178965 : Blo 1451545 2178965 := bbase (se 6 (by rfl) ⟨51069, by rfl⟩ : syracuseStep 2178965 = 102139) (by norm_num)
theorem B2178989 : Blo 1451545 2178989 := bbase (se 3 (by rfl) ⟨408560, by rfl⟩ : syracuseStep 2178989 = 817121) (by norm_num)
theorem B2179013 : Blo 1451545 2179013 := bbase (se 4 (by rfl) ⟨204282, by rfl⟩ : syracuseStep 2179013 = 408565) (by norm_num)
theorem B3678149 : Blo 1451545 3678149 := bbase (se 4 (by rfl) ⟨344826, by rfl⟩ : syracuseStep 3678149 = 689653) (by norm_num)
theorem B1679305 : Blo 1451545 1679305 := bbase (se 2 (by rfl) ⟨629739, by rfl⟩ : syracuseStep 1679305 = 1259479) (by norm_num)
theorem B3268565 : Blo 1451545 3268565 := bbase (se 7 (by rfl) ⟨38303, by rfl⟩ : syracuseStep 3268565 = 76607) (by norm_num)
theorem B2179037 : Blo 1451545 2179037 := bbase (se 3 (by rfl) ⟨408569, by rfl⟩ : syracuseStep 2179037 = 817139) (by norm_num)
theorem B12574709 : Blo 1451545 12574709 := bbase (se 5 (by rfl) ⟨589439, by rfl⟩ : syracuseStep 12574709 = 1178879) (by norm_num)
theorem B2179061 : Blo 1451545 2179061 := bbase (se 5 (by rfl) ⟨102143, by rfl⟩ : syracuseStep 2179061 = 204287) (by norm_num)
theorem B2179073 : Blo 1451545 2179073 := bstep (se 2 (by rfl) ⟨817152, by rfl⟩ : syracuseStep 2179073 = 1634305) B1634305
theorem B2179091 : Blo 1451545 2179091 := bstep (se 1 (by rfl) ⟨1634318, by rfl⟩ : syracuseStep 2179091 = 3268637) B3268637
theorem B2793521 : Blo 1451545 2793521 := bstep (se 2 (by rfl) ⟨1047570, by rfl⟩ : syracuseStep 2793521 = 2095141) B2095141
theorem B5890097 : Blo 1451545 5890097 := bstep (se 2 (by rfl) ⟨2208786, by rfl⟩ : syracuseStep 5890097 = 4417573) B4417573
theorem B2179121 : Blo 1451545 2179121 := bstep (se 2 (by rfl) ⟨817170, by rfl⟩ : syracuseStep 2179121 = 1634341) B1634341
theorem B15704117 : Blo 1451545 15704117 := bstep (se 5 (by rfl) ⟨736130, by rfl⟩ : syracuseStep 15704117 = 1472261) B1472261
theorem B2179139 : Blo 1451545 2179139 := bstep (se 1 (by rfl) ⟨1634354, by rfl⟩ : syracuseStep 2179139 = 3268709) B3268709
theorem B2179169 : Blo 1451545 2179169 := bstep (se 2 (by rfl) ⟨817188, by rfl⟩ : syracuseStep 2179169 = 1634377) B1634377
theorem B2449507 : Blo 1451545 2449507 := bstep (se 1 (by rfl) ⟨1837130, by rfl⟩ : syracuseStep 2449507 = 3674261) B3674261
theorem B2179187 : Blo 1451545 2179187 := bstep (se 1 (by rfl) ⟨1634390, by rfl⟩ : syracuseStep 2179187 = 3268781) B3268781
theorem B2326657 : Blo 1451545 2326657 := bstep (se 2 (by rfl) ⟨872496, by rfl⟩ : syracuseStep 2326657 = 1744993) B1744993
theorem B2179217 : Blo 1451545 2179217 := bstep (se 2 (by rfl) ⟨817206, by rfl⟩ : syracuseStep 2179217 = 1634413) B1634413
theorem B2179235 : Blo 1451545 2179235 := bstep (se 1 (by rfl) ⟨1634426, by rfl⟩ : syracuseStep 2179235 = 3268853) B3268853
theorem B2179265 : Blo 1451545 2179265 := bstep (se 2 (by rfl) ⟨817224, by rfl⟩ : syracuseStep 2179265 = 1634449) B1634449
theorem B3268817 : Blo 1451545 3268817 := bstep (se 2 (by rfl) ⟨1225806, by rfl⟩ : syracuseStep 3268817 = 2451613) B2451613
theorem B2179283 : Blo 1451545 2179283 := bstep (se 1 (by rfl) ⟨1634462, by rfl⟩ : syracuseStep 2179283 = 3268925) B3268925
theorem B3268835 : Blo 1451545 3268835 := bstep (se 1 (by rfl) ⟨2451626, by rfl⟩ : syracuseStep 3268835 = 4903253) B4903253
theorem B25166051 : Blo 1451545 25166051 := bstep (se 1 (by rfl) ⟨18874538, by rfl⟩ : syracuseStep 25166051 = 37749077) B37749077
theorem B2449649 : Blo 1451545 2449649 := bstep (se 2 (by rfl) ⟨918618, by rfl⟩ : syracuseStep 2449649 = 1837237) B1837237
theorem B2179313 : Blo 1451545 2179313 := bstep (se 2 (by rfl) ⟨817242, by rfl⟩ : syracuseStep 2179313 = 1634485) B1634485
theorem B2179331 : Blo 1451545 2179331 := bstep (se 1 (by rfl) ⟨1634498, by rfl⟩ : syracuseStep 2179331 = 3268997) B3268997
theorem B2179361 : Blo 1451545 2179361 := bstep (se 2 (by rfl) ⟨817260, by rfl⟩ : syracuseStep 2179361 = 1634521) B1634521
theorem B2179379 : Blo 1451545 2179379 := bstep (se 1 (by rfl) ⟨1634534, by rfl⟩ : syracuseStep 2179379 = 3269069) B3269069
theorem B4899149 : Blo 1451545 4899149 := bstep (se 3 (by rfl) ⟨918590, by rfl⟩ : syracuseStep 4899149 = 1837181) B1837181
theorem B2179409 : Blo 1451545 2179409 := bstep (se 2 (by rfl) ⟨817278, by rfl⟩ : syracuseStep 2179409 = 1634557) B1634557
theorem B2179427 : Blo 1451545 2179427 := bstep (se 1 (by rfl) ⟨1634570, by rfl⟩ : syracuseStep 2179427 = 3269141) B3269141
theorem B2449777 : Blo 1451545 2449777 := bstep (se 2 (by rfl) ⟨918666, by rfl⟩ : syracuseStep 2449777 = 1837333) B1837333
theorem B2179457 : Blo 1451545 2179457 := bstep (se 2 (by rfl) ⟨817296, by rfl⟩ : syracuseStep 2179457 = 1634593) B1634593
theorem B4899203 : Blo 1451545 4899203 := bstep (se 1 (by rfl) ⟨3674402, by rfl⟩ : syracuseStep 4899203 = 7348805) B7348805
theorem B2449811 : Blo 1451545 2449811 := bstep (se 1 (by rfl) ⟨1837358, by rfl⟩ : syracuseStep 2449811 = 3674717) B3674717
theorem B2179475 : Blo 1451545 2179475 := bstep (se 1 (by rfl) ⟨1634606, by rfl⟩ : syracuseStep 2179475 = 3269213) B3269213
theorem B7348643 : Blo 1451545 7348643 := bstep (se 1 (by rfl) ⟨5511482, by rfl⟩ : syracuseStep 7348643 = 11022965) B11022965
theorem B2179505 : Blo 1451545 2179505 := bstep (se 2 (by rfl) ⟨817314, by rfl⟩ : syracuseStep 2179505 = 1634629) B1634629
theorem B2179523 : Blo 1451545 2179523 := bstep (se 1 (by rfl) ⟨1634642, by rfl⟩ : syracuseStep 2179523 = 3269285) B3269285
theorem B5972429 : Blo 1451545 5972429 := bstep (se 3 (by rfl) ⟨1119830, by rfl⟩ : syracuseStep 5972429 = 2239661) B2239661
theorem B2179553 : Blo 1451545 2179553 := bstep (se 2 (by rfl) ⟨817332, by rfl⟩ : syracuseStep 2179553 = 1634665) B1634665
theorem B3269105 : Blo 1451545 3269105 := bstep (se 2 (by rfl) ⟨1225914, by rfl⟩ : syracuseStep 3269105 = 2451829) B2451829
theorem B2097649 : Blo 1451545 2097649 := bstep (se 2 (by rfl) ⟨786618, by rfl⟩ : syracuseStep 2097649 = 1573237) B1573237
theorem B2179571 : Blo 1451545 2179571 := bstep (se 1 (by rfl) ⟨1634678, by rfl⟩ : syracuseStep 2179571 = 3269357) B3269357
theorem B3269123 : Blo 1451545 3269123 := bstep (se 1 (by rfl) ⟨2451842, by rfl⟩ : syracuseStep 3269123 = 4903685) B4903685
theorem B8831501 : Blo 1451545 8831501 := bstep (se 3 (by rfl) ⟨1655906, by rfl⟩ : syracuseStep 8831501 = 3311813) B3311813
theorem B2179601 : Blo 1451545 2179601 := bstep (se 2 (by rfl) ⟨817350, by rfl⟩ : syracuseStep 2179601 = 1634701) B1634701
theorem B2449939 : Blo 1451545 2449939 := bstep (se 1 (by rfl) ⟨1837454, by rfl⟩ : syracuseStep 2449939 = 3674909) B3674909
theorem B1679891 : Blo 1451545 1679891 := bstep (se 1 (by rfl) ⟨1259918, by rfl⟩ : syracuseStep 1679891 = 2519837) B2519837
theorem B2179619 : Blo 1451545 2179619 := bstep (se 1 (by rfl) ⟨1634714, by rfl⟩ : syracuseStep 2179619 = 3269429) B3269429
theorem B5513777 : Blo 1451545 5513777 := bstep (se 2 (by rfl) ⟨2067666, by rfl⟩ : syracuseStep 5513777 = 4135333) B4135333
theorem B2179649 : Blo 1451545 2179649 := bstep (se 2 (by rfl) ⟨817368, by rfl⟩ : syracuseStep 2179649 = 1634737) B1634737
theorem B2179667 : Blo 1451545 2179667 := bstep (se 1 (by rfl) ⟨1634750, by rfl⟩ : syracuseStep 2179667 = 3269501) B3269501
theorem B2179697 : Blo 1451545 2179697 := bstep (se 2 (by rfl) ⟨817386, by rfl⟩ : syracuseStep 2179697 = 1634773) B1634773
theorem B2179715 : Blo 1451545 2179715 := bstep (se 1 (by rfl) ⟨1634786, by rfl⟩ : syracuseStep 2179715 = 3269573) B3269573
theorem B4899473 : Blo 1451545 4899473 := bstep (se 2 (by rfl) ⟨1837302, by rfl⟩ : syracuseStep 4899473 = 3674605) B3674605
theorem B2450081 : Blo 1451545 2450081 := bstep (se 2 (by rfl) ⟨918780, by rfl⟩ : syracuseStep 2450081 = 1837561) B1837561
theorem B2179745 : Blo 1451545 2179745 := bstep (se 2 (by rfl) ⟨817404, by rfl⟩ : syracuseStep 2179745 = 1634809) B1634809
theorem B2179763 : Blo 1451545 2179763 := bstep (se 1 (by rfl) ⟨1634822, by rfl⟩ : syracuseStep 2179763 = 3269645) B3269645
theorem B23560901 : Blo 1451545 23560901 := bstep (se 4 (by rfl) ⟨2208834, by rfl⟩ : syracuseStep 23560901 = 4417669) B4417669
theorem B2179793 : Blo 1451545 2179793 := bstep (se 2 (by rfl) ⟨817422, by rfl⟩ : syracuseStep 2179793 = 1634845) B1634845
theorem B3678929 : Blo 1451545 3678929 := bstep (se 2 (by rfl) ⟨1379598, by rfl⟩ : syracuseStep 3678929 = 2759197) B2759197
theorem B2179811 : Blo 1451545 2179811 := bstep (se 1 (by rfl) ⟨1634858, by rfl⟩ : syracuseStep 2179811 = 3269717) B3269717
theorem B4137713 : Blo 1451545 4137713 := bstep (se 2 (by rfl) ⟨1551642, by rfl⟩ : syracuseStep 4137713 = 3103285) B3103285
theorem B2179841 : Blo 1451545 2179841 := bstep (se 2 (by rfl) ⟨817440, by rfl⟩ : syracuseStep 2179841 = 1634881) B1634881
theorem B3678979 : Blo 1451545 3678979 := bstep (se 1 (by rfl) ⟨2759234, by rfl⟩ : syracuseStep 3678979 = 5518469) B5518469
theorem B3269393 : Blo 1451545 3269393 := bstep (se 2 (by rfl) ⟨1226022, by rfl⟩ : syracuseStep 3269393 = 2452045) B2452045
theorem B2179859 : Blo 1451545 2179859 := bstep (se 1 (by rfl) ⟨1634894, by rfl⟩ : syracuseStep 2179859 = 3269789) B3269789
theorem B2450209 : Blo 1451545 2450209 := bstep (se 2 (by rfl) ⟨918828, by rfl⟩ : syracuseStep 2450209 = 1837657) B1837657
theorem B3269411 : Blo 1451545 3269411 := bstep (se 1 (by rfl) ⟨2452058, by rfl⟩ : syracuseStep 3269411 = 4904117) B4904117
theorem B2179889 : Blo 1451545 2179889 := bstep (se 2 (by rfl) ⟨817458, by rfl⟩ : syracuseStep 2179889 = 1634917) B1634917
theorem B33547061 : Blo 1451545 33547061 := bstep (se 5 (by rfl) ⟨1572518, by rfl⟩ : syracuseStep 33547061 = 3145037) B3145037
theorem B2450243 : Blo 1451545 2450243 := bstep (se 1 (by rfl) ⟨1837682, by rfl⟩ : syracuseStep 2450243 = 3675365) B3675365
theorem B2179907 : Blo 1451545 2179907 := bstep (se 1 (by rfl) ⟨1634930, by rfl⟩ : syracuseStep 2179907 = 3269861) B3269861
theorem B2179937 : Blo 1451545 2179937 := bstep (se 2 (by rfl) ⟨817476, by rfl⟩ : syracuseStep 2179937 = 1634953) B1634953
theorem B5309297 : Blo 1451545 5309297 := bstep (se 2 (by rfl) ⟨1990986, by rfl⟩ : syracuseStep 5309297 = 3981973) B3981973
theorem B2179955 : Blo 1451545 2179955 := bstep (se 1 (by rfl) ⟨1634966, by rfl⟩ : syracuseStep 2179955 = 3269933) B3269933
theorem B2179985 : Blo 1451545 2179985 := bstep (se 2 (by rfl) ⟨817494, by rfl⟩ : syracuseStep 2179985 = 1634989) B1634989
theorem B3679121 : Blo 1451545 3679121 := bstep (se 2 (by rfl) ⟨1379670, by rfl⟩ : syracuseStep 3679121 = 2759341) B2759341
theorem B2180003 : Blo 1451545 2180003 := bstep (se 1 (by rfl) ⟨1635002, by rfl⟩ : syracuseStep 2180003 = 3270005) B3270005
theorem B2180033 : Blo 1451545 2180033 := bstep (se 2 (by rfl) ⟨817512, by rfl⟩ : syracuseStep 2180033 = 1635025) B1635025
theorem B2450371 : Blo 1451545 2450371 := bstep (se 1 (by rfl) ⟨1837778, by rfl⟩ : syracuseStep 2450371 = 3675557) B3675557
theorem B2180051 : Blo 1451545 2180051 := bstep (se 1 (by rfl) ⟨1635038, by rfl⟩ : syracuseStep 2180051 = 3270077) B3270077
theorem B7955441 : Blo 1451545 7955441 := bstep (se 2 (by rfl) ⟨2983290, by rfl⟩ : syracuseStep 7955441 = 5966581) B5966581
theorem B2180081 : Blo 1451545 2180081 := bstep (se 2 (by rfl) ⟨817530, by rfl⟩ : syracuseStep 2180081 = 1635061) B1635061
theorem B2180099 : Blo 1451545 2180099 := bstep (se 1 (by rfl) ⟨1635074, by rfl⟩ : syracuseStep 2180099 = 3270149) B3270149
theorem B2180129 : Blo 1451545 2180129 := bstep (se 2 (by rfl) ⟨817548, by rfl⟩ : syracuseStep 2180129 = 1635097) B1635097
theorem B6628387 : Blo 1451545 6628387 := bstep (se 1 (by rfl) ⟨4971290, by rfl⟩ : syracuseStep 6628387 = 9942581) B9942581
theorem B3269681 : Blo 1451545 3269681 := bstep (se 2 (by rfl) ⟨1226130, by rfl⟩ : syracuseStep 3269681 = 2452261) B2452261
theorem B2180147 : Blo 1451545 2180147 := bstep (se 1 (by rfl) ⟨1635110, by rfl⟩ : syracuseStep 2180147 = 3270221) B3270221
theorem B3269699 : Blo 1451545 3269699 := bstep (se 1 (by rfl) ⟨2452274, by rfl⟩ : syracuseStep 3269699 = 4904549) B4904549
theorem B2450513 : Blo 1451545 2450513 := bstep (se 2 (by rfl) ⟨918942, by rfl⟩ : syracuseStep 2450513 = 1837885) B1837885
theorem B2180177 : Blo 1451545 2180177 := bstep (se 2 (by rfl) ⟨817566, by rfl⟩ : syracuseStep 2180177 = 1635133) B1635133
theorem B2180195 : Blo 1451545 2180195 := bstep (se 1 (by rfl) ⟨1635146, by rfl⟩ : syracuseStep 2180195 = 3270293) B3270293
theorem B11781233 : Blo 1451545 11781233 := bstep (se 2 (by rfl) ⟨4417962, by rfl⟩ : syracuseStep 11781233 = 8835925) B8835925
theorem B7357553 : Blo 1451545 7357553 := bstep (se 2 (by rfl) ⟨2759082, by rfl⟩ : syracuseStep 7357553 = 5518165) B5518165
theorem B2180225 : Blo 1451545 2180225 := bstep (se 2 (by rfl) ⟨817584, by rfl⟩ : syracuseStep 2180225 = 1635169) B1635169
theorem B2180243 : Blo 1451545 2180243 := bstep (se 1 (by rfl) ⟨1635182, by rfl⟩ : syracuseStep 2180243 = 3270365) B3270365
theorem B4900013 : Blo 1451545 4900013 := bstep (se 3 (by rfl) ⟨918752, by rfl⟩ : syracuseStep 4900013 = 1837505) B1837505
theorem B2180273 : Blo 1451545 2180273 := bstep (se 2 (by rfl) ⟨817602, by rfl⟩ : syracuseStep 2180273 = 1635205) B1635205
theorem B2180291 : Blo 1451545 2180291 := bstep (se 1 (by rfl) ⟨1635218, by rfl⟩ : syracuseStep 2180291 = 3270437) B3270437
theorem B7349453 : Blo 1451545 7349453 := bstep (se 3 (by rfl) ⟨1378022, by rfl⟩ : syracuseStep 7349453 = 2756045) B2756045
theorem B2450641 : Blo 1451545 2450641 := bstep (se 2 (by rfl) ⟨918990, by rfl⟩ : syracuseStep 2450641 = 1837981) B1837981
theorem B4900067 : Blo 1451545 4900067 := bstep (se 1 (by rfl) ⟨3675050, by rfl⟩ : syracuseStep 4900067 = 7350101) B7350101
theorem B2450675 : Blo 1451545 2450675 := bstep (se 1 (by rfl) ⟨1838006, by rfl⟩ : syracuseStep 2450675 = 3676013) B3676013
theorem B8267021 : Blo 1451545 8267021 := bstep (se 3 (by rfl) ⟨1550066, by rfl⟩ : syracuseStep 8267021 = 3100133) B3100133
theorem B3269969 : Blo 1451545 3269969 := bstep (se 2 (by rfl) ⟨1226238, by rfl⟩ : syracuseStep 3269969 = 2452477) B2452477
theorem B3269987 : Blo 1451545 3269987 := bstep (se 1 (by rfl) ⟨2452490, by rfl⟩ : syracuseStep 3269987 = 4904981) B4904981
theorem B11027825 : Blo 1451545 11027825 := bstep (se 2 (by rfl) ⟨4135434, by rfl⟩ : syracuseStep 11027825 = 8270869) B8270869
theorem B2450803 : Blo 1451545 2450803 := bstep (se 1 (by rfl) ⟨1838102, by rfl⟩ : syracuseStep 2450803 = 3676205) B3676205
theorem B4900337 : Blo 1451545 4900337 := bstep (se 2 (by rfl) ⟨1837626, by rfl⟩ : syracuseStep 4900337 = 3675253) B3675253
theorem B2450945 : Blo 1451545 2450945 := bstep (se 2 (by rfl) ⟨919104, by rfl⟩ : syracuseStep 2450945 = 1838209) B1838209
theorem B15926797 : Blo 1451545 15926797 := bstep (se 3 (by rfl) ⟨2986274, by rfl⟩ : syracuseStep 15926797 = 5972549) B5972549
theorem B1451555 : Blo 1451545 1451555 := bstep (se 1 (by rfl) ⟨1088666, by rfl⟩ : syracuseStep 1451555 = 2177333) B2177333
theorem B1451571 : Blo 1451545 1451571 := bstep (se 1 (by rfl) ⟨1088678, by rfl⟩ : syracuseStep 1451571 = 2177357) B2177357
theorem B1451587 : Blo 1451545 1451587 := bstep (se 1 (by rfl) ⟨1088690, by rfl⟩ : syracuseStep 1451587 = 2177381) B2177381
theorem B1451603 : Blo 1451545 1451603 := bstep (se 1 (by rfl) ⟨1088702, by rfl⟩ : syracuseStep 1451603 = 2177405) B2177405
theorem B1451619 : Blo 1451545 1451619 := bstep (se 1 (by rfl) ⟨1088714, by rfl⟩ : syracuseStep 1451619 = 2177429) B2177429
theorem B3270257 : Blo 1451545 3270257 := bstep (se 2 (by rfl) ⟨1226346, by rfl⟩ : syracuseStep 3270257 = 2452693) B2452693
theorem B1451635 : Blo 1451545 1451635 := bstep (se 1 (by rfl) ⟨1088726, by rfl⟩ : syracuseStep 1451635 = 2177453) B2177453
theorem B2451073 : Blo 1451545 2451073 := bstep (se 2 (by rfl) ⟨919152, by rfl⟩ : syracuseStep 2451073 = 1838305) B1838305
theorem B1451651 : Blo 1451545 1451651 := bstep (se 1 (by rfl) ⟨1088738, by rfl⟩ : syracuseStep 1451651 = 2177477) B2177477
theorem B3270275 : Blo 1451545 3270275 := bstep (se 1 (by rfl) ⟨2452706, by rfl⟩ : syracuseStep 3270275 = 4905413) B4905413
theorem B9307781 : Blo 1451545 9307781 := bstep (se 4 (by rfl) ⟨872604, by rfl⟩ : syracuseStep 9307781 = 1745209) B1745209
theorem B1451667 : Blo 1451545 1451667 := bstep (se 1 (by rfl) ⟨1088750, by rfl⟩ : syracuseStep 1451667 = 2177501) B2177501
theorem B1451683 : Blo 1451545 1451683 := bstep (se 1 (by rfl) ⟨1088762, by rfl⟩ : syracuseStep 1451683 = 2177525) B2177525
theorem B2451107 : Blo 1451545 2451107 := bstep (se 1 (by rfl) ⟨1838330, by rfl⟩ : syracuseStep 2451107 = 3676661) B3676661
theorem B1451699 : Blo 1451545 1451699 := bstep (se 1 (by rfl) ⟨1088774, by rfl⟩ : syracuseStep 1451699 = 2177549) B2177549
theorem B1451715 : Blo 1451545 1451715 := bstep (se 1 (by rfl) ⟨1088786, by rfl⟩ : syracuseStep 1451715 = 2177573) B2177573
theorem B2328259 : Blo 1451545 2328259 := bstep (se 1 (by rfl) ⟨1746194, by rfl⟩ : syracuseStep 2328259 = 3492389) B3492389
theorem B1451731 : Blo 1451545 1451731 := bstep (se 1 (by rfl) ⟨1088798, by rfl⟩ : syracuseStep 1451731 = 2177597) B2177597
theorem B1451747 : Blo 1451545 1451747 := bstep (se 1 (by rfl) ⟨1088810, by rfl⟩ : syracuseStep 1451747 = 2177621) B2177621
theorem B1451763 : Blo 1451545 1451763 := bstep (se 1 (by rfl) ⟨1088822, by rfl⟩ : syracuseStep 1451763 = 2177645) B2177645
theorem B1451779 : Blo 1451545 1451779 := bstep (se 1 (by rfl) ⟨1088834, by rfl⟩ : syracuseStep 1451779 = 2177669) B2177669
theorem B1451795 : Blo 1451545 1451795 := bstep (se 1 (by rfl) ⟨1088846, by rfl⟩ : syracuseStep 1451795 = 2177693) B2177693
theorem B1451811 : Blo 1451545 1451811 := bstep (se 1 (by rfl) ⟨1088858, by rfl⟩ : syracuseStep 1451811 = 2177717) B2177717
theorem B2451235 : Blo 1451545 2451235 := bstep (se 1 (by rfl) ⟨1838426, by rfl⟩ : syracuseStep 2451235 = 3676853) B3676853
theorem B1451827 : Blo 1451545 1451827 := bstep (se 1 (by rfl) ⟨1088870, by rfl⟩ : syracuseStep 1451827 = 2177741) B2177741
theorem B1451843 : Blo 1451545 1451843 := bstep (se 1 (by rfl) ⟨1088882, by rfl⟩ : syracuseStep 1451843 = 2177765) B2177765
theorem B1451859 : Blo 1451545 1451859 := bstep (se 1 (by rfl) ⟨1088894, by rfl⟩ : syracuseStep 1451859 = 2177789) B2177789
theorem B1451875 : Blo 1451545 1451875 := bstep (se 1 (by rfl) ⟨1088906, by rfl⟩ : syracuseStep 1451875 = 2177813) B2177813
theorem B1451891 : Blo 1451545 1451891 := bstep (se 1 (by rfl) ⟨1088918, by rfl⟩ : syracuseStep 1451891 = 2177837) B2177837
theorem B1451907 : Blo 1451545 1451907 := bstep (se 1 (by rfl) ⟨1088930, by rfl⟩ : syracuseStep 1451907 = 2177861) B2177861
theorem B4654979 : Blo 1451545 4654979 := bstep (se 1 (by rfl) ⟨3491234, by rfl⟩ : syracuseStep 4654979 = 6982469) B6982469
theorem B1451923 : Blo 1451545 1451923 := bstep (se 1 (by rfl) ⟨1088942, by rfl⟩ : syracuseStep 1451923 = 2177885) B2177885
theorem B1451939 : Blo 1451545 1451939 := bstep (se 1 (by rfl) ⟨1088954, by rfl⟩ : syracuseStep 1451939 = 2177909) B2177909
theorem B2451377 : Blo 1451545 2451377 := bstep (se 2 (by rfl) ⟨919266, by rfl⟩ : syracuseStep 2451377 = 1838533) B1838533
theorem B1451955 : Blo 1451545 1451955 := bstep (se 1 (by rfl) ⟨1088966, by rfl⟩ : syracuseStep 1451955 = 2177933) B2177933
theorem B1451971 : Blo 1451545 1451971 := bstep (se 1 (by rfl) ⟨1088978, by rfl⟩ : syracuseStep 1451971 = 2177957) B2177957
theorem B1451987 : Blo 1451545 1451987 := bstep (se 1 (by rfl) ⟨1088990, by rfl⟩ : syracuseStep 1451987 = 2177981) B2177981
theorem B1452003 : Blo 1451545 1452003 := bstep (se 1 (by rfl) ⟨1089002, by rfl⟩ : syracuseStep 1452003 = 2178005) B2178005
theorem B5515235 : Blo 1451545 5515235 := bstep (se 1 (by rfl) ⟨4136426, by rfl⟩ : syracuseStep 5515235 = 8272853) B8272853
theorem B5515249 : Blo 1451545 5515249 := bstep (se 2 (by rfl) ⟨2068218, by rfl⟩ : syracuseStep 5515249 = 4136437) B4136437
theorem B1452019 : Blo 1451545 1452019 := bstep (se 1 (by rfl) ⟨1089014, by rfl⟩ : syracuseStep 1452019 = 2178029) B2178029
theorem B1452035 : Blo 1451545 1452035 := bstep (se 1 (by rfl) ⟨1089026, by rfl⟩ : syracuseStep 1452035 = 2178053) B2178053
theorem B4900877 : Blo 1451545 4900877 := bstep (se 3 (by rfl) ⟨918914, by rfl⟩ : syracuseStep 4900877 = 1837829) B1837829
theorem B6719501 : Blo 1451545 6719501 := bstep (se 3 (by rfl) ⟨1259906, by rfl⟩ : syracuseStep 6719501 = 2519813) B2519813
theorem B1452051 : Blo 1451545 1452051 := bstep (se 1 (by rfl) ⟨1089038, by rfl⟩ : syracuseStep 1452051 = 2178077) B2178077
theorem B1452067 : Blo 1451545 1452067 := bstep (se 1 (by rfl) ⟨1089050, by rfl⟩ : syracuseStep 1452067 = 2178101) B2178101
theorem B2451505 : Blo 1451545 2451505 := bstep (se 2 (by rfl) ⟨919314, by rfl⟩ : syracuseStep 2451505 = 1838629) B1838629
theorem B1550387 : Blo 1451545 1550387 := bstep (se 1 (by rfl) ⟨1162790, by rfl⟩ : syracuseStep 1550387 = 2325581) B2325581
theorem B1452083 : Blo 1451545 1452083 := bstep (se 1 (by rfl) ⟨1089062, by rfl⟩ : syracuseStep 1452083 = 2178125) B2178125
theorem B1452099 : Blo 1451545 1452099 := bstep (se 1 (by rfl) ⟨1089074, by rfl⟩ : syracuseStep 1452099 = 2178149) B2178149
theorem B4900931 : Blo 1451545 4900931 := bstep (se 1 (by rfl) ⟨3675698, by rfl⟩ : syracuseStep 4900931 = 7351397) B7351397
theorem B1452115 : Blo 1451545 1452115 := bstep (se 1 (by rfl) ⟨1089086, by rfl⟩ : syracuseStep 1452115 = 2178173) B2178173
theorem B2451539 : Blo 1451545 2451539 := bstep (se 1 (by rfl) ⟨1838654, by rfl⟩ : syracuseStep 2451539 = 3677309) B3677309
theorem B1452131 : Blo 1451545 1452131 := bstep (se 1 (by rfl) ⟨1089098, by rfl⟩ : syracuseStep 1452131 = 2178197) B2178197
theorem B1837171 : Blo 1451545 1837171 := bstep (se 1 (by rfl) ⟨1377878, by rfl⟩ : syracuseStep 1837171 = 2755757) B2755757
theorem B1452147 : Blo 1451545 1452147 := bstep (se 1 (by rfl) ⟨1089110, by rfl⟩ : syracuseStep 1452147 = 2178221) B2178221
theorem B1452163 : Blo 1451545 1452163 := bstep (se 1 (by rfl) ⟨1089122, by rfl⟩ : syracuseStep 1452163 = 2178245) B2178245
theorem B1452179 : Blo 1451545 1452179 := bstep (se 1 (by rfl) ⟨1089134, by rfl⟩ : syracuseStep 1452179 = 2178269) B2178269
theorem B1452195 : Blo 1451545 1452195 := bstep (se 1 (by rfl) ⟨1089146, by rfl⟩ : syracuseStep 1452195 = 2178293) B2178293
theorem B4139171 : Blo 1451545 4139171 := bstep (se 1 (by rfl) ⟨3104378, by rfl⟩ : syracuseStep 4139171 = 6208757) B6208757
theorem B8267953 : Blo 1451545 8267953 := bstep (se 2 (by rfl) ⟨3100482, by rfl⟩ : syracuseStep 8267953 = 6200965) B6200965
theorem B1452211 : Blo 1451545 1452211 := bstep (se 1 (by rfl) ⟨1089158, by rfl⟩ : syracuseStep 1452211 = 2178317) B2178317
theorem B1452227 : Blo 1451545 1452227 := bstep (se 1 (by rfl) ⟨1089170, by rfl⟩ : syracuseStep 1452227 = 2178341) B2178341
theorem B1452243 : Blo 1451545 1452243 := bstep (se 1 (by rfl) ⟨1089182, by rfl⟩ : syracuseStep 1452243 = 2178365) B2178365
theorem B2451667 : Blo 1451545 2451667 := bstep (se 1 (by rfl) ⟨1838750, by rfl⟩ : syracuseStep 2451667 = 3677501) B3677501
theorem B1452259 : Blo 1451545 1452259 := bstep (se 1 (by rfl) ⟨1089194, by rfl⟩ : syracuseStep 1452259 = 2178389) B2178389
theorem B1452275 : Blo 1451545 1452275 := bstep (se 1 (by rfl) ⟨1089206, by rfl⟩ : syracuseStep 1452275 = 2178413) B2178413
theorem B2984195 : Blo 1451545 2984195 := bstep (se 1 (by rfl) ⟨2238146, by rfl⟩ : syracuseStep 2984195 = 4476293) B4476293
theorem B1452291 : Blo 1451545 1452291 := bstep (se 1 (by rfl) ⟨1089218, by rfl⟩ : syracuseStep 1452291 = 2178437) B2178437
theorem B1452307 : Blo 1451545 1452307 := bstep (se 1 (by rfl) ⟨1089230, by rfl⟩ : syracuseStep 1452307 = 2178461) B2178461
theorem B1452323 : Blo 1451545 1452323 := bstep (se 1 (by rfl) ⟨1089242, by rfl⟩ : syracuseStep 1452323 = 2178485) B2178485
theorem B1452339 : Blo 1451545 1452339 := bstep (se 1 (by rfl) ⟨1089254, by rfl⟩ : syracuseStep 1452339 = 2178509) B2178509
theorem B1452355 : Blo 1451545 1452355 := bstep (se 1 (by rfl) ⟨1089266, by rfl⟩ : syracuseStep 1452355 = 2178533) B2178533
theorem B4901201 : Blo 1451545 4901201 := bstep (se 2 (by rfl) ⟨1837950, by rfl⟩ : syracuseStep 4901201 = 3675901) B3675901
theorem B3189073 : Blo 1451545 3189073 := bstep (se 2 (by rfl) ⟨1195902, by rfl⟩ : syracuseStep 3189073 = 2391805) B2391805
theorem B1452371 : Blo 1451545 1452371 := bstep (se 1 (by rfl) ⟨1089278, by rfl⟩ : syracuseStep 1452371 = 2178557) B2178557
theorem B2451809 : Blo 1451545 2451809 := bstep (se 2 (by rfl) ⟨919428, by rfl⟩ : syracuseStep 2451809 = 1838857) B1838857
theorem B1452387 : Blo 1451545 1452387 := bstep (se 1 (by rfl) ⟨1089290, by rfl⟩ : syracuseStep 1452387 = 2178581) B2178581
theorem B1452403 : Blo 1451545 1452403 := bstep (se 1 (by rfl) ⟨1089302, by rfl⟩ : syracuseStep 1452403 = 2178605) B2178605
theorem B1452419 : Blo 1451545 1452419 := bstep (se 1 (by rfl) ⟨1089314, by rfl⟩ : syracuseStep 1452419 = 2178629) B2178629
theorem B1452435 : Blo 1451545 1452435 := bstep (se 1 (by rfl) ⟨1089326, by rfl⟩ : syracuseStep 1452435 = 2178653) B2178653
theorem B2943395 : Blo 1451545 2943395 := bstep (se 1 (by rfl) ⟨2207546, by rfl⟩ : syracuseStep 2943395 = 4415093) B4415093
theorem B1452451 : Blo 1451545 1452451 := bstep (se 1 (by rfl) ⟨1089338, by rfl⟩ : syracuseStep 1452451 = 2178677) B2178677
theorem B1452467 : Blo 1451545 1452467 := bstep (se 1 (by rfl) ⟨1089350, by rfl⟩ : syracuseStep 1452467 = 2178701) B2178701
theorem B1452483 : Blo 1451545 1452483 := bstep (se 1 (by rfl) ⟨1089362, by rfl⟩ : syracuseStep 1452483 = 2178725) B2178725
theorem B4655569 : Blo 1451545 4655569 := bstep (se 2 (by rfl) ⟨1745838, by rfl⟩ : syracuseStep 4655569 = 3491677) B3491677
theorem B1452499 : Blo 1451545 1452499 := bstep (se 1 (by rfl) ⟨1089374, by rfl⟩ : syracuseStep 1452499 = 2178749) B2178749
theorem B2451937 : Blo 1451545 2451937 := bstep (se 2 (by rfl) ⟨919476, by rfl⟩ : syracuseStep 2451937 = 1838953) B1838953
theorem B1452515 : Blo 1451545 1452515 := bstep (se 1 (by rfl) ⟨1089386, by rfl⟩ : syracuseStep 1452515 = 2178773) B2178773
theorem B1452531 : Blo 1451545 1452531 := bstep (se 1 (by rfl) ⟨1089398, by rfl⟩ : syracuseStep 1452531 = 2178797) B2178797
theorem B1452547 : Blo 1451545 1452547 := bstep (se 1 (by rfl) ⟨1089410, by rfl⟩ : syracuseStep 1452547 = 2178821) B2178821
theorem B2451971 : Blo 1451545 2451971 := bstep (se 1 (by rfl) ⟨1838978, by rfl⟩ : syracuseStep 2451971 = 3677957) B3677957
theorem B10471949 : Blo 1451545 10471949 := bstep (se 3 (by rfl) ⟨1963490, by rfl⟩ : syracuseStep 10471949 = 3926981) B3926981
theorem B1452563 : Blo 1451545 1452563 := bstep (se 1 (by rfl) ⟨1089422, by rfl⟩ : syracuseStep 1452563 = 2178845) B2178845
theorem B1452579 : Blo 1451545 1452579 := bstep (se 1 (by rfl) ⟨1089434, by rfl⟩ : syracuseStep 1452579 = 2178869) B2178869
theorem B1452595 : Blo 1451545 1452595 := bstep (se 1 (by rfl) ⟨1089446, by rfl⟩ : syracuseStep 1452595 = 2178893) B2178893
theorem B1452611 : Blo 1451545 1452611 := bstep (se 1 (by rfl) ⟨1089458, by rfl⟩ : syracuseStep 1452611 = 2178917) B2178917
theorem B1452627 : Blo 1451545 1452627 := bstep (se 1 (by rfl) ⟨1089470, by rfl⟩ : syracuseStep 1452627 = 2178941) B2178941
theorem B2239073 : Blo 1451545 2239073 := bstep (se 2 (by rfl) ⟨839652, by rfl⟩ : syracuseStep 2239073 = 1679305) B1679305
theorem B1837667 : Blo 1451545 1837667 := bstep (se 1 (by rfl) ⟨1378250, by rfl⟩ : syracuseStep 1837667 = 2756501) B2756501
theorem B1452643 : Blo 1451545 1452643 := bstep (se 1 (by rfl) ⟨1089482, by rfl⟩ : syracuseStep 1452643 = 2178965) B2178965
theorem B1452659 : Blo 1451545 1452659 := bstep (se 1 (by rfl) ⟨1089494, by rfl⟩ : syracuseStep 1452659 = 2178989) B2178989
theorem B1452675 : Blo 1451545 1452675 := bstep (se 1 (by rfl) ⟨1089506, by rfl⟩ : syracuseStep 1452675 = 2179013) B2179013
theorem B2452099 : Blo 1451545 2452099 := bstep (se 1 (by rfl) ⟨1839074, by rfl⟩ : syracuseStep 2452099 = 3678149) B3678149
theorem B1452691 : Blo 1451545 1452691 := bstep (se 1 (by rfl) ⟨1089518, by rfl⟩ : syracuseStep 1452691 = 2179037) B2179037
theorem B8383139 : Blo 1451545 8383139 := bstep (se 1 (by rfl) ⟨6287354, by rfl⟩ : syracuseStep 8383139 = 12574709) B12574709
theorem B1452707 : Blo 1451545 1452707 := bstep (se 1 (by rfl) ⟨1089530, by rfl⟩ : syracuseStep 1452707 = 2179061) B2179061
theorem B1452723 : Blo 1451545 1452723 := bstep (se 1 (by rfl) ⟨1089542, by rfl⟩ : syracuseStep 1452723 = 2179085) B2179085
theorem B1452739 : Blo 1451545 1452739 := bstep (se 1 (by rfl) ⟨1089554, by rfl⟩ : syracuseStep 1452739 = 2179109) B2179109
theorem B6204109 : Blo 1451545 6204109 := bstep (se 3 (by rfl) ⟨1163270, by rfl⟩ : syracuseStep 6204109 = 2326541) B2326541
theorem B1452755 : Blo 1451545 1452755 := bstep (se 1 (by rfl) ⟨1089566, by rfl⟩ : syracuseStep 1452755 = 2179133) B2179133
theorem B1452771 : Blo 1451545 1452771 := bstep (se 1 (by rfl) ⟨1089578, by rfl⟩ : syracuseStep 1452771 = 2179157) B2179157
theorem B1452787 : Blo 1451545 1452787 := bstep (se 1 (by rfl) ⟨1089590, by rfl⟩ : syracuseStep 1452787 = 2179181) B2179181
theorem B1633027 : Blo 1451545 1633027 := bstep (se 1 (by rfl) ⟨1224770, by rfl⟩ : syracuseStep 1633027 = 2449541) B2449541
theorem B1452803 : Blo 1451545 1452803 := bstep (se 1 (by rfl) ⟨1089602, by rfl⟩ : syracuseStep 1452803 = 2179205) B2179205
theorem B2452241 : Blo 1451545 2452241 := bstep (se 2 (by rfl) ⟨919590, by rfl⟩ : syracuseStep 2452241 = 1839181) B1839181
theorem B1452819 : Blo 1451545 1452819 := bstep (se 1 (by rfl) ⟨1089614, by rfl⟩ : syracuseStep 1452819 = 2179229) B2179229
theorem B1452835 : Blo 1451545 1452835 := bstep (se 1 (by rfl) ⟨1089626, by rfl⟩ : syracuseStep 1452835 = 2179253) B2179253
theorem B1452851 : Blo 1451545 1452851 := bstep (se 1 (by rfl) ⟨1089638, by rfl⟩ : syracuseStep 1452851 = 2179277) B2179277
theorem B1452867 : Blo 1451545 1452867 := bstep (se 1 (by rfl) ⟨1089650, by rfl⟩ : syracuseStep 1452867 = 2179301) B2179301
theorem B1452883 : Blo 1451545 1452883 := bstep (se 1 (by rfl) ⟨1089662, by rfl⟩ : syracuseStep 1452883 = 2179325) B2179325
theorem B1452899 : Blo 1451545 1452899 := bstep (se 1 (by rfl) ⟨1089674, by rfl⟩ : syracuseStep 1452899 = 2179349) B2179349
theorem B4901741 : Blo 1451545 4901741 := bstep (se 3 (by rfl) ⟨919076, by rfl⟩ : syracuseStep 4901741 = 1838153) B1838153
theorem B1452915 : Blo 1451545 1452915 := bstep (se 1 (by rfl) ⟨1089686, by rfl⟩ : syracuseStep 1452915 = 2179373) B2179373
theorem B1452931 : Blo 1451545 1452931 := bstep (se 1 (by rfl) ⟨1089698, by rfl⟩ : syracuseStep 1452931 = 2179397) B2179397
theorem B2452369 : Blo 1451545 2452369 := bstep (se 2 (by rfl) ⟨919638, by rfl⟩ : syracuseStep 2452369 = 1839277) B1839277
theorem B1633171 : Blo 1451545 1633171 := bstep (se 1 (by rfl) ⟨1224878, by rfl⟩ : syracuseStep 1633171 = 2449757) B2449757
theorem B1452947 : Blo 1451545 1452947 := bstep (se 1 (by rfl) ⟨1089710, by rfl⟩ : syracuseStep 1452947 = 2179421) B2179421
theorem B4901795 : Blo 1451545 4901795 := bstep (se 1 (by rfl) ⟨3676346, by rfl⟩ : syracuseStep 4901795 = 7352693) B7352693
theorem B3926947 : Blo 1451545 3926947 := bstep (se 1 (by rfl) ⟨2945210, by rfl⟩ : syracuseStep 3926947 = 5890421) B5890421
theorem B1452963 : Blo 1451545 1452963 := bstep (se 1 (by rfl) ⟨1089722, by rfl⟩ : syracuseStep 1452963 = 2179445) B2179445
theorem B1452979 : Blo 1451545 1452979 := bstep (se 1 (by rfl) ⟨1089734, by rfl⟩ : syracuseStep 1452979 = 2179469) B2179469
theorem B2452403 : Blo 1451545 2452403 := bstep (se 1 (by rfl) ⟨1839302, by rfl⟩ : syracuseStep 2452403 = 3678605) B3678605
theorem B1452995 : Blo 1451545 1452995 := bstep (se 1 (by rfl) ⟨1089746, by rfl⟩ : syracuseStep 1452995 = 2179493) B2179493
theorem B1453011 : Blo 1451545 1453011 := bstep (se 1 (by rfl) ⟨1089758, by rfl⟩ : syracuseStep 1453011 = 2179517) B2179517
theorem B1453027 : Blo 1451545 1453027 := bstep (se 1 (by rfl) ⟨1089770, by rfl⟩ : syracuseStep 1453027 = 2179541) B2179541
theorem B1453043 : Blo 1451545 1453043 := bstep (se 1 (by rfl) ⟨1089782, by rfl⟩ : syracuseStep 1453043 = 2179565) B2179565
theorem B1453059 : Blo 1451545 1453059 := bstep (se 1 (by rfl) ⟨1089794, by rfl⟩ : syracuseStep 1453059 = 2179589) B2179589
theorem B1453075 : Blo 1451545 1453075 := bstep (se 1 (by rfl) ⟨1089806, by rfl⟩ : syracuseStep 1453075 = 2179613) B2179613
theorem B1633315 : Blo 1451545 1633315 := bstep (se 1 (by rfl) ⟨1224986, by rfl⟩ : syracuseStep 1633315 = 2449973) B2449973
theorem B6204451 : Blo 1451545 6204451 := bstep (se 1 (by rfl) ⟨4653338, by rfl⟩ : syracuseStep 6204451 = 9306677) B9306677
theorem B1453091 : Blo 1451545 1453091 := bstep (se 1 (by rfl) ⟨1089818, by rfl⟩ : syracuseStep 1453091 = 2179637) B2179637
theorem B1453107 : Blo 1451545 1453107 := bstep (se 1 (by rfl) ⟨1089830, by rfl⟩ : syracuseStep 1453107 = 2179661) B2179661
theorem B2452531 : Blo 1451545 2452531 := bstep (se 1 (by rfl) ⟨1839398, by rfl⟩ : syracuseStep 2452531 = 3678797) B3678797
theorem B1453123 : Blo 1451545 1453123 := bstep (se 1 (by rfl) ⟨1089842, by rfl⟩ : syracuseStep 1453123 = 2179685) B2179685
theorem B1453139 : Blo 1451545 1453139 := bstep (se 1 (by rfl) ⟨1089854, by rfl⟩ : syracuseStep 1453139 = 2179709) B2179709
theorem B1453155 : Blo 1451545 1453155 := bstep (se 1 (by rfl) ⟨1089866, by rfl⟩ : syracuseStep 1453155 = 2179733) B2179733
theorem B1453171 : Blo 1451545 1453171 := bstep (se 1 (by rfl) ⟨1089878, by rfl⟩ : syracuseStep 1453171 = 2179757) B2179757
theorem B1453187 : Blo 1451545 1453187 := bstep (se 1 (by rfl) ⟨1089890, by rfl⟩ : syracuseStep 1453187 = 2179781) B2179781
theorem B1453203 : Blo 1451545 1453203 := bstep (se 1 (by rfl) ⟨1089902, by rfl⟩ : syracuseStep 1453203 = 2179805) B2179805
theorem B1551523 : Blo 1451545 1551523 := bstep (se 1 (by rfl) ⟨1163642, by rfl⟩ : syracuseStep 1551523 = 2327285) B2327285
theorem B1453219 : Blo 1451545 1453219 := bstep (se 1 (by rfl) ⟨1089914, by rfl⟩ : syracuseStep 1453219 = 2179829) B2179829
theorem B4902065 : Blo 1451545 4902065 := bstep (se 2 (by rfl) ⟨1838274, by rfl⟩ : syracuseStep 4902065 = 3676549) B3676549
theorem B1633459 : Blo 1451545 1633459 := bstep (se 1 (by rfl) ⟨1225094, by rfl⟩ : syracuseStep 1633459 = 2450189) B2450189
theorem B1453235 : Blo 1451545 1453235 := bstep (se 1 (by rfl) ⟨1089926, by rfl⟩ : syracuseStep 1453235 = 2179853) B2179853
theorem B2452673 : Blo 1451545 2452673 := bstep (se 2 (by rfl) ⟨919752, by rfl⟩ : syracuseStep 2452673 = 1839505) B1839505
theorem B1453251 : Blo 1451545 1453251 := bstep (se 1 (by rfl) ⟨1089938, by rfl⟩ : syracuseStep 1453251 = 2179877) B2179877
theorem B1453267 : Blo 1451545 1453267 := bstep (se 1 (by rfl) ⟨1089950, by rfl⟩ : syracuseStep 1453267 = 2179901) B2179901
theorem B1453283 : Blo 1451545 1453283 := bstep (se 1 (by rfl) ⟨1089962, by rfl⟩ : syracuseStep 1453283 = 2179925) B2179925
theorem B1453299 : Blo 1451545 1453299 := bstep (se 1 (by rfl) ⟨1089974, by rfl⟩ : syracuseStep 1453299 = 2179949) B2179949
theorem B1453315 : Blo 1451545 1453315 := bstep (se 1 (by rfl) ⟨1089986, by rfl⟩ : syracuseStep 1453315 = 2179973) B2179973
theorem B1453331 : Blo 1451545 1453331 := bstep (se 1 (by rfl) ⟨1089998, by rfl⟩ : syracuseStep 1453331 = 2179997) B2179997
theorem B1838371 : Blo 1451545 1838371 := bstep (se 1 (by rfl) ⟨1378778, by rfl⟩ : syracuseStep 1838371 = 2757557) B2757557
theorem B1453347 : Blo 1451545 1453347 := bstep (se 1 (by rfl) ⟨1090010, by rfl⟩ : syracuseStep 1453347 = 2180021) B2180021
theorem B2067763 : Blo 1451545 2067763 := bstep (se 1 (by rfl) ⟨1550822, by rfl⟩ : syracuseStep 2067763 = 3101645) B3101645
theorem B1453363 : Blo 1451545 1453363 := bstep (se 1 (by rfl) ⟨1090022, by rfl⟩ : syracuseStep 1453363 = 2180045) B2180045
theorem B2452801 : Blo 1451545 2452801 := bstep (se 2 (by rfl) ⟨919800, by rfl⟩ : syracuseStep 2452801 = 1839601) B1839601
theorem B1633603 : Blo 1451545 1633603 := bstep (se 1 (by rfl) ⟨1225202, by rfl⟩ : syracuseStep 1633603 = 2450405) B2450405
theorem B1453379 : Blo 1451545 1453379 := bstep (se 1 (by rfl) ⟨1090034, by rfl⟩ : syracuseStep 1453379 = 2180069) B2180069
theorem B10071373 : Blo 1451545 10071373 := bstep (se 3 (by rfl) ⟨1888382, by rfl⟩ : syracuseStep 10071373 = 3776765) B3776765
theorem B1453395 : Blo 1451545 1453395 := bstep (se 1 (by rfl) ⟨1090046, by rfl⟩ : syracuseStep 1453395 = 2180093) B2180093
theorem B2755939 : Blo 1451545 2755939 := bstep (se 1 (by rfl) ⟨2066954, by rfl⟩ : syracuseStep 2755939 = 4133909) B4133909
theorem B1453411 : Blo 1451545 1453411 := bstep (se 1 (by rfl) ⟨1090058, by rfl⟩ : syracuseStep 1453411 = 2180117) B2180117
theorem B1453427 : Blo 1451545 1453427 := bstep (se 1 (by rfl) ⟨1090070, by rfl⟩ : syracuseStep 1453427 = 2180141) B2180141
theorem B1838467 : Blo 1451545 1838467 := bstep (se 1 (by rfl) ⟨1378850, by rfl⟩ : syracuseStep 1838467 = 2757701) B2757701
theorem B1453443 : Blo 1451545 1453443 := bstep (se 1 (by rfl) ⟨1090082, by rfl⟩ : syracuseStep 1453443 = 2180165) B2180165
theorem B1453459 : Blo 1451545 1453459 := bstep (se 1 (by rfl) ⟨1090094, by rfl⟩ : syracuseStep 1453459 = 2180189) B2180189
theorem B5516707 : Blo 1451545 5516707 := bstep (se 1 (by rfl) ⟨4137530, by rfl⟩ : syracuseStep 5516707 = 8275061) B8275061
theorem B1453475 : Blo 1451545 1453475 := bstep (se 1 (by rfl) ⟨1090106, by rfl⟩ : syracuseStep 1453475 = 2180213) B2180213
theorem B1453491 : Blo 1451545 1453491 := bstep (se 1 (by rfl) ⟨1090118, by rfl⟩ : syracuseStep 1453491 = 2180237) B2180237
theorem B1453507 : Blo 1451545 1453507 := bstep (se 1 (by rfl) ⟨1090130, by rfl⟩ : syracuseStep 1453507 = 2180261) B2180261
theorem B12742085 : Blo 1451545 12742085 := bstep (se 4 (by rfl) ⟨1194570, by rfl⟩ : syracuseStep 12742085 = 2389141) B2389141
theorem B1633747 : Blo 1451545 1633747 := bstep (se 1 (by rfl) ⟨1225310, by rfl⟩ : syracuseStep 1633747 = 2450621) B2450621
theorem B1453523 : Blo 1451545 1453523 := bstep (se 1 (by rfl) ⟨1090142, by rfl⟩ : syracuseStep 1453523 = 2180285) B2180285
theorem B1453539 : Blo 1451545 1453539 := bstep (se 1 (by rfl) ⟨1090154, by rfl⟩ : syracuseStep 1453539 = 2180309) B2180309
theorem B2756099 : Blo 1451545 2756099 := bstep (se 1 (by rfl) ⟨2067074, by rfl⟩ : syracuseStep 2756099 = 4134149) B4134149
theorem B9301553 : Blo 1451545 9301553 := bstep (se 2 (by rfl) ⟨3488082, by rfl⟩ : syracuseStep 9301553 = 6976165) B6976165
theorem B2452835 : Blo 1451545 2452835 := bstep (se 1 (by rfl) ⟨1839626, by rfl⟩ : syracuseStep 2452835 = 3679253) B3679253
theorem B8269411 : Blo 1451545 8269411 := bstep (se 1 (by rfl) ⟨6202058, by rfl⟩ : syracuseStep 8269411 = 12404117) B12404117
theorem B1633891 : Blo 1451545 1633891 := bstep (se 1 (by rfl) ⟨1225418, by rfl⟩ : syracuseStep 1633891 = 2450837) B2450837
theorem B8179363 : Blo 1451545 8179363 := bstep (se 1 (by rfl) ⟨6134522, by rfl⟩ : syracuseStep 8179363 = 12269045) B12269045
theorem B4902605 : Blo 1451545 4902605 := bstep (se 3 (by rfl) ⟨919238, by rfl⟩ : syracuseStep 4902605 = 1838477) B1838477
theorem B15920867 : Blo 1451545 15920867 := bstep (se 1 (by rfl) ⟨11940650, by rfl⟩ : syracuseStep 15920867 = 23881301) B23881301
theorem B1634035 : Blo 1451545 1634035 := bstep (se 1 (by rfl) ⟨1225526, by rfl⟩ : syracuseStep 1634035 = 2451053) B2451053
theorem B4902659 : Blo 1451545 4902659 := bstep (se 1 (by rfl) ⟨3676994, by rfl⟩ : syracuseStep 4902659 = 7353989) B7353989
theorem B2617201 : Blo 1451545 2617201 := bstep (se 2 (by rfl) ⟨981450, by rfl⟩ : syracuseStep 2617201 = 1962901) B1962901
theorem B1838963 : Blo 1451545 1838963 := bstep (se 1 (by rfl) ⟨1379222, by rfl⟩ : syracuseStep 1838963 = 2758445) B2758445
theorem B1634179 : Blo 1451545 1634179 := bstep (se 1 (by rfl) ⟨1225634, by rfl⟩ : syracuseStep 1634179 = 2451269) B2451269
theorem B4902929 : Blo 1451545 4902929 := bstep (se 2 (by rfl) ⟨1838598, by rfl⟩ : syracuseStep 4902929 = 3677197) B3677197
theorem B1634323 : Blo 1451545 1634323 := bstep (se 1 (by rfl) ⟨1225742, by rfl⟩ : syracuseStep 1634323 = 2451485) B2451485
theorem B7352369 : Blo 1451545 7352369 := bstep (se 2 (by rfl) ⟨2757138, by rfl⟩ : syracuseStep 7352369 = 5514277) B5514277
theorem B9941069 : Blo 1451545 9941069 := bstep (se 3 (by rfl) ⟨1863950, by rfl⟩ : syracuseStep 9941069 = 3727901) B3727901
theorem B3584099 : Blo 1451545 3584099 := bstep (se 1 (by rfl) ⟨2688074, by rfl⟩ : syracuseStep 3584099 = 5376149) B5376149
theorem B8269937 : Blo 1451545 8269937 := bstep (se 2 (by rfl) ⟨3101226, by rfl⟩ : syracuseStep 8269937 = 6202453) B6202453
theorem B3100817 : Blo 1451545 3100817 := bstep (se 2 (by rfl) ⟨1162806, by rfl⟩ : syracuseStep 3100817 = 2325613) B2325613
theorem B1634467 : Blo 1451545 1634467 := bstep (se 1 (by rfl) ⟨1225850, by rfl⟩ : syracuseStep 1634467 = 2451701) B2451701
theorem B6975665 : Blo 1451545 6975665 := bstep (se 2 (by rfl) ⟨2615874, by rfl⟩ : syracuseStep 6975665 = 5231749) B5231749
theorem B16543925 : Blo 1451545 16543925 := bstep (se 5 (by rfl) ⟨775496, by rfl⟩ : syracuseStep 16543925 = 1550993) B1550993
theorem B1634611 : Blo 1451545 1634611 := bstep (se 1 (by rfl) ⟨1225958, by rfl⟩ : syracuseStep 1634611 = 2451917) B2451917
theorem B2617699 : Blo 1451545 2617699 := bstep (se 1 (by rfl) ⟨1963274, by rfl⟩ : syracuseStep 2617699 = 3926549) B3926549
theorem B2068897 : Blo 1451545 2068897 := bstep (se 2 (by rfl) ⟨775836, by rfl⟩ : syracuseStep 2068897 = 1551673) B1551673
theorem B1634755 : Blo 1451545 1634755 := bstep (se 1 (by rfl) ⟨1226066, by rfl⟩ : syracuseStep 1634755 = 2452133) B2452133
theorem B17912261 : Blo 1451545 17912261 := bstep (se 4 (by rfl) ⟨1679274, by rfl⟩ : syracuseStep 17912261 = 3358549) B3358549
theorem B14913989 : Blo 1451545 14913989 := bstep (se 4 (by rfl) ⟨1398186, by rfl⟩ : syracuseStep 14913989 = 2796373) B2796373
theorem B35336675 : Blo 1451545 35336675 := bstep (se 1 (by rfl) ⟨26502506, by rfl⟩ : syracuseStep 35336675 = 53005013) B53005013
theorem B3928547 : Blo 1451545 3928547 := bstep (se 1 (by rfl) ⟨2946410, by rfl⟩ : syracuseStep 3928547 = 5892821) B5892821
theorem B2068993 : Blo 1451545 2068993 := bstep (se 2 (by rfl) ⟨775872, by rfl⟩ : syracuseStep 2068993 = 1551745) B1551745
theorem B4903469 : Blo 1451545 4903469 := bstep (se 3 (by rfl) ⟨919400, by rfl⟩ : syracuseStep 4903469 = 1838801) B1838801
theorem B2757169 : Blo 1451545 2757169 := bstep (se 2 (by rfl) ⟨1033938, by rfl⟩ : syracuseStep 2757169 = 2067877) B2067877
theorem B2945585 : Blo 1451545 2945585 := bstep (se 2 (by rfl) ⟨1104594, by rfl⟩ : syracuseStep 2945585 = 2209189) B2209189
theorem B1634899 : Blo 1451545 1634899 := bstep (se 1 (by rfl) ⟨1226174, by rfl⟩ : syracuseStep 1634899 = 2452349) B2452349
theorem B4903523 : Blo 1451545 4903523 := bstep (se 1 (by rfl) ⟨3677642, by rfl⟩ : syracuseStep 4903523 = 7355285) B7355285
theorem B4133521 : Blo 1451545 4133521 := bstep (se 2 (by rfl) ⟨1550070, by rfl⟩ : syracuseStep 4133521 = 3100141) B3100141
theorem B1962673 : Blo 1451545 1962673 := bstep (se 2 (by rfl) ⟨736002, by rfl⟩ : syracuseStep 1962673 = 1472005) B1472005
theorem B1635043 : Blo 1451545 1635043 := bstep (se 1 (by rfl) ⟨1226282, by rfl⟩ : syracuseStep 1635043 = 2452565) B2452565
theorem B1962739 : Blo 1451545 1962739 := bstep (se 1 (by rfl) ⟨1472054, by rfl⟩ : syracuseStep 1962739 = 2944109) B2944109
theorem B3674929 : Blo 1451545 3674929 := bstep (se 2 (by rfl) ⟨1378098, by rfl⟩ : syracuseStep 3674929 = 2756197) B2756197
theorem B1962803 : Blo 1451545 1962803 := bstep (se 1 (by rfl) ⟨1472102, by rfl⟩ : syracuseStep 1962803 = 2944205) B2944205
theorem B3314513 : Blo 1451545 3314513 := bstep (se 2 (by rfl) ⟨1242942, by rfl⟩ : syracuseStep 3314513 = 2485885) B2485885
theorem B18617201 : Blo 1451545 18617201 := bstep (se 2 (by rfl) ⟨6981450, by rfl⟩ : syracuseStep 18617201 = 13962901) B13962901
theorem B4903793 : Blo 1451545 4903793 := bstep (se 2 (by rfl) ⟨1838922, by rfl⟩ : syracuseStep 4903793 = 3677845) B3677845
theorem B1635187 : Blo 1451545 1635187 := bstep (se 1 (by rfl) ⟨1226390, by rfl⟩ : syracuseStep 1635187 = 2452781) B2452781
theorem B3404675 : Blo 1451545 3404675 := bstep (se 1 (by rfl) ⟨2553506, by rfl⟩ : syracuseStep 3404675 = 5107013) B5107013
theorem B2618339 : Blo 1451545 2618339 := bstep (se 1 (by rfl) ⟨1963754, by rfl⟩ : syracuseStep 2618339 = 3927509) B3927509
theorem B2069489 : Blo 1451545 2069489 := bstep (se 2 (by rfl) ⟨776058, by rfl⟩ : syracuseStep 2069489 = 1552117) B1552117
theorem B3675203 : Blo 1451545 3675203 := bstep (se 1 (by rfl) ⟨2756402, by rfl⟩ : syracuseStep 3675203 = 5512805) B5512805
theorem B6624355 : Blo 1451545 6624355 := bstep (se 1 (by rfl) ⟨4968266, by rfl⟩ : syracuseStep 6624355 = 9936533) B9936533
theorem B3675395 : Blo 1451545 3675395 := bstep (se 1 (by rfl) ⟨2756546, by rfl⟩ : syracuseStep 3675395 = 5513093) B5513093
theorem B4904333 : Blo 1451545 4904333 := bstep (se 3 (by rfl) ⟨919562, by rfl⟩ : syracuseStep 4904333 = 1839125) B1839125
theorem B2618801 : Blo 1451545 2618801 := bstep (se 2 (by rfl) ⟨982050, by rfl⟩ : syracuseStep 2618801 = 1964101) B1964101
theorem B4904387 : Blo 1451545 4904387 := bstep (se 1 (by rfl) ⟨3678290, by rfl⟩ : syracuseStep 4904387 = 7356581) B7356581
theorem B7353827 : Blo 1451545 7353827 := bstep (se 1 (by rfl) ⟨5515370, by rfl⟩ : syracuseStep 7353827 = 11030741) B11030741
theorem B6977009 : Blo 1451545 6977009 := bstep (se 2 (by rfl) ⟨2616378, by rfl⟩ : syracuseStep 6977009 = 5232757) B5232757
theorem B8271395 : Blo 1451545 8271395 := bstep (se 1 (by rfl) ⟨6203546, by rfl⟩ : syracuseStep 8271395 = 12407093) B12407093
theorem B5518925 : Blo 1451545 5518925 := bstep (se 3 (by rfl) ⟨1034798, by rfl⟩ : syracuseStep 5518925 = 2069597) B2069597
theorem B2758225 : Blo 1451545 2758225 := bstep (se 2 (by rfl) ⟨1034334, by rfl⟩ : syracuseStep 2758225 = 2068669) B2068669
theorem B1472099 : Blo 1451545 1472099 := bstep (se 1 (by rfl) ⟨1104074, by rfl⟩ : syracuseStep 1472099 = 2208149) B2208149
theorem B20936333 : Blo 1451545 20936333 := bstep (se 3 (by rfl) ⟨3925562, by rfl⟩ : syracuseStep 20936333 = 7851125) B7851125
theorem B3266225 : Blo 1451545 3266225 := bstep (se 2 (by rfl) ⟨1224834, by rfl⟩ : syracuseStep 3266225 = 2449669) B2449669
theorem B3266243 : Blo 1451545 3266243 := bstep (se 1 (by rfl) ⟨2449682, by rfl⟩ : syracuseStep 3266243 = 4899365) B4899365
theorem B4904657 : Blo 1451545 4904657 := bstep (se 2 (by rfl) ⟨1839246, by rfl⟩ : syracuseStep 4904657 = 3678493) B3678493
theorem B3102499 : Blo 1451545 3102499 := bstep (se 1 (by rfl) ⟨2326874, by rfl⟩ : syracuseStep 3102499 = 4653749) B4653749
theorem B4970317 : Blo 1451545 4970317 := bstep (se 3 (by rfl) ⟨931934, by rfl⟩ : syracuseStep 4970317 = 1863869) B1863869
theorem B6371185 : Blo 1451545 6371185 := bstep (se 2 (by rfl) ⟨2389194, by rfl⟩ : syracuseStep 6371185 = 4778389) B4778389
theorem B17667953 : Blo 1451545 17667953 := bstep (se 2 (by rfl) ⟨6625482, by rfl⟩ : syracuseStep 17667953 = 13250965) B13250965
theorem B2455427 : Blo 1451545 2455427 := bstep (se 1 (by rfl) ⟨1841570, by rfl⟩ : syracuseStep 2455427 = 3683141) B3683141
theorem B4134797 : Blo 1451545 4134797 := bstep (se 3 (by rfl) ⟨775274, by rfl⟩ : syracuseStep 4134797 = 1550549) B1550549
theorem B3266513 : Blo 1451545 3266513 := bstep (se 2 (by rfl) ⟨1224942, by rfl⟩ : syracuseStep 3266513 = 2449885) B2449885
theorem B3266531 : Blo 1451545 3266531 := bstep (se 1 (by rfl) ⟨2449898, by rfl⟩ : syracuseStep 3266531 = 4899797) B4899797
theorem B2758627 : Blo 1451545 2758627 := bstep (se 1 (by rfl) ⟨2068970, by rfl⟩ : syracuseStep 2758627 = 4137941) B4137941
theorem B2758673 : Blo 1451545 2758673 := bstep (se 2 (by rfl) ⟨1034502, by rfl⟩ : syracuseStep 2758673 = 2069005) B2069005
theorem B4134979 : Blo 1451545 4134979 := bstep (se 1 (by rfl) ⟨3101234, by rfl⟩ : syracuseStep 4134979 = 6202469) B6202469
theorem B4135025 : Blo 1451545 4135025 := bstep (se 2 (by rfl) ⟨1550634, by rfl⟩ : syracuseStep 4135025 = 3101269) B3101269
theorem B3676337 : Blo 1451545 3676337 := bstep (se 2 (by rfl) ⟨1378626, by rfl⟩ : syracuseStep 3676337 = 2757253) B2757253
theorem B3676387 : Blo 1451545 3676387 := bstep (se 1 (by rfl) ⟨2757290, by rfl⟩ : syracuseStep 3676387 = 5514581) B5514581
theorem B4905197 : Blo 1451545 4905197 := bstep (se 3 (by rfl) ⟨919724, by rfl⟩ : syracuseStep 4905197 = 1839449) B1839449
theorem B3266801 : Blo 1451545 3266801 := bstep (se 2 (by rfl) ⟨1225050, by rfl⟩ : syracuseStep 3266801 = 2450101) B2450101
theorem B3102961 : Blo 1451545 3102961 := bstep (se 2 (by rfl) ⟨1163610, by rfl⟩ : syracuseStep 3102961 = 2327221) B2327221
theorem B3266819 : Blo 1451545 3266819 := bstep (se 1 (by rfl) ⟨2450114, by rfl⟩ : syracuseStep 3266819 = 4900229) B4900229
theorem B7354637 : Blo 1451545 7354637 := bstep (se 3 (by rfl) ⟨1378994, by rfl⟩ : syracuseStep 7354637 = 2757989) B2757989
theorem B4905251 : Blo 1451545 4905251 := bstep (se 1 (by rfl) ⟨3678938, by rfl⟩ : syracuseStep 4905251 = 7357877) B7357877
theorem B2758961 : Blo 1451545 2758961 := bstep (se 2 (by rfl) ⟨1034610, by rfl⟩ : syracuseStep 2758961 = 2069221) B2069221
theorem B21223733 : Blo 1451545 21223733 := bstep (se 5 (by rfl) ⟨994862, by rfl⟩ : syracuseStep 21223733 = 1989725) B1989725
theorem B2177345 : Blo 1451545 2177345 := bstep (se 2 (by rfl) ⟨816504, by rfl⟩ : syracuseStep 2177345 = 1633009) B1633009
theorem B2177363 : Blo 1451545 2177363 := bstep (se 1 (by rfl) ⟨1633022, by rfl⟩ : syracuseStep 2177363 = 3266045) B3266045
theorem B2177393 : Blo 1451545 2177393 := bstep (se 2 (by rfl) ⟨816522, by rfl⟩ : syracuseStep 2177393 = 1633045) B1633045
theorem B3676529 : Blo 1451545 3676529 := bstep (se 2 (by rfl) ⟨1378698, by rfl⟩ : syracuseStep 3676529 = 2757397) B2757397
theorem B2177411 : Blo 1451545 2177411 := bstep (se 1 (by rfl) ⟨1633058, by rfl⟩ : syracuseStep 2177411 = 3266117) B3266117
theorem B6977933 : Blo 1451545 6977933 := bstep (se 3 (by rfl) ⟨1308362, by rfl⟩ : syracuseStep 6977933 = 2616725) B2616725
theorem B2177441 : Blo 1451545 2177441 := bstep (se 2 (by rfl) ⟨816540, by rfl⟩ : syracuseStep 2177441 = 1633081) B1633081
theorem B8952241 : Blo 1451545 8952241 := bstep (se 2 (by rfl) ⟨3357090, by rfl⟩ : syracuseStep 8952241 = 6714181) B6714181
theorem B2177459 : Blo 1451545 2177459 := bstep (se 1 (by rfl) ⟨1633094, by rfl⟩ : syracuseStep 2177459 = 3266189) B3266189
theorem B4651469 : Blo 1451545 4651469 := bstep (se 3 (by rfl) ⟨872150, by rfl⟩ : syracuseStep 4651469 = 1744301) B1744301
theorem B2177489 : Blo 1451545 2177489 := bstep (se 2 (by rfl) ⟨816558, by rfl⟩ : syracuseStep 2177489 = 1633117) B1633117
theorem B2177507 : Blo 1451545 2177507 := bstep (se 1 (by rfl) ⟨1633130, by rfl⟩ : syracuseStep 2177507 = 3266261) B3266261
theorem B1472995 : Blo 1451545 1472995 := bstep (se 1 (by rfl) ⟨1104746, by rfl⟩ : syracuseStep 1472995 = 2209493) B2209493
theorem B5511665 : Blo 1451545 5511665 := bstep (se 2 (by rfl) ⟨2066874, by rfl⟩ : syracuseStep 5511665 = 4133749) B4133749
theorem B2177537 : Blo 1451545 2177537 := bstep (se 2 (by rfl) ⟨816576, by rfl⟩ : syracuseStep 2177537 = 1633153) B1633153
theorem B11024909 : Blo 1451545 11024909 := bstep (se 3 (by rfl) ⟨2067170, by rfl⟩ : syracuseStep 11024909 = 4134341) B4134341
theorem B3267089 : Blo 1451545 3267089 := bstep (se 2 (by rfl) ⟨1225158, by rfl⟩ : syracuseStep 3267089 = 2450317) B2450317
theorem B2177555 : Blo 1451545 2177555 := bstep (se 1 (by rfl) ⟨1633166, by rfl⟩ : syracuseStep 2177555 = 3266333) B3266333
theorem B1473043 : Blo 1451545 1473043 := bstep (se 1 (by rfl) ⟨1104782, by rfl⟩ : syracuseStep 1473043 = 2209565) B2209565
theorem B2095651 : Blo 1451545 2095651 := bstep (se 1 (by rfl) ⟨1571738, by rfl⟩ : syracuseStep 2095651 = 3143477) B3143477
theorem B3267107 : Blo 1451545 3267107 := bstep (se 1 (by rfl) ⟨2450330, by rfl⟩ : syracuseStep 3267107 = 4900661) B4900661
theorem B2177585 : Blo 1451545 2177585 := bstep (se 2 (by rfl) ⟨816594, by rfl⟩ : syracuseStep 2177585 = 1633189) B1633189
theorem B4905521 : Blo 1451545 4905521 := bstep (se 2 (by rfl) ⟨1839570, by rfl⟩ : syracuseStep 4905521 = 3679141) B3679141
theorem B2177603 : Blo 1451545 2177603 := bstep (se 1 (by rfl) ⟨1633202, by rfl⟩ : syracuseStep 2177603 = 3266405) B3266405
theorem B14899781 : Blo 1451545 14899781 := bstep (se 4 (by rfl) ⟨1396854, by rfl⟩ : syracuseStep 14899781 = 2793709) B2793709
theorem B6978125 : Blo 1451545 6978125 := bstep (se 3 (by rfl) ⟨1308398, by rfl⟩ : syracuseStep 6978125 = 2616797) B2616797
theorem B2177633 : Blo 1451545 2177633 := bstep (se 2 (by rfl) ⟨816612, by rfl⟩ : syracuseStep 2177633 = 1633225) B1633225
theorem B2177651 : Blo 1451545 2177651 := bstep (se 1 (by rfl) ⟨1633238, by rfl⟩ : syracuseStep 2177651 = 3266477) B3266477
theorem B2177681 : Blo 1451545 2177681 := bstep (se 2 (by rfl) ⟨816630, by rfl⟩ : syracuseStep 2177681 = 1633261) B1633261
theorem B2177699 : Blo 1451545 2177699 := bstep (se 1 (by rfl) ⟨1633274, by rfl⟩ : syracuseStep 2177699 = 3266549) B3266549
theorem B2177729 : Blo 1451545 2177729 := bstep (se 2 (by rfl) ⟨816648, by rfl⟩ : syracuseStep 2177729 = 1633297) B1633297
theorem B2325203 : Blo 1451545 2325203 := bstep (se 1 (by rfl) ⟨1743902, by rfl⟩ : syracuseStep 2325203 = 3487805) B3487805
theorem B2177747 : Blo 1451545 2177747 := bstep (se 1 (by rfl) ⟨1633310, by rfl⟩ : syracuseStep 2177747 = 3266621) B3266621
theorem B2177777 : Blo 1451545 2177777 := bstep (se 2 (by rfl) ⟨816666, by rfl⟩ : syracuseStep 2177777 = 1633333) B1633333
theorem B2177795 : Blo 1451545 2177795 := bstep (se 1 (by rfl) ⟨1633346, by rfl⟩ : syracuseStep 2177795 = 3266693) B3266693
theorem B2177825 : Blo 1451545 2177825 := bstep (se 2 (by rfl) ⟨816684, by rfl⟩ : syracuseStep 2177825 = 1633369) B1633369
theorem B3267377 : Blo 1451545 3267377 := bstep (se 2 (by rfl) ⟨1225266, by rfl⟩ : syracuseStep 3267377 = 2450533) B2450533
theorem B2177843 : Blo 1451545 2177843 := bstep (se 1 (by rfl) ⟨1633382, by rfl⟩ : syracuseStep 2177843 = 3266765) B3266765
theorem B3267395 : Blo 1451545 3267395 := bstep (se 1 (by rfl) ⟨2450546, by rfl⟩ : syracuseStep 3267395 = 4901093) B4901093
theorem B2177873 : Blo 1451545 2177873 := bstep (se 2 (by rfl) ⟨816702, by rfl⟩ : syracuseStep 2177873 = 1633405) B1633405
theorem B2177891 : Blo 1451545 2177891 := bstep (se 1 (by rfl) ⟨1633418, by rfl⟩ : syracuseStep 2177891 = 3266837) B3266837
theorem B2177921 : Blo 1451545 2177921 := bstep (se 2 (by rfl) ⟨816720, by rfl⟩ : syracuseStep 2177921 = 1633441) B1633441
theorem B2177939 : Blo 1451545 2177939 := bstep (se 1 (by rfl) ⟨1633454, by rfl⟩ : syracuseStep 2177939 = 3266909) B3266909
theorem B2177969 : Blo 1451545 2177969 := bstep (se 2 (by rfl) ⟨816738, by rfl⟩ : syracuseStep 2177969 = 1633477) B1633477
theorem B2177987 : Blo 1451545 2177987 := bstep (se 1 (by rfl) ⟨1633490, by rfl⟩ : syracuseStep 2177987 = 3266981) B3266981
theorem B2178017 : Blo 1451545 2178017 := bstep (se 2 (by rfl) ⟨816756, by rfl⟩ : syracuseStep 2178017 = 1633513) B1633513
theorem B6208483 : Blo 1451545 6208483 := bstep (se 1 (by rfl) ⟨4656362, by rfl⟩ : syracuseStep 6208483 = 9312725) B9312725
theorem B2178035 : Blo 1451545 2178035 := bstep (se 1 (by rfl) ⟨1633526, by rfl⟩ : syracuseStep 2178035 = 3267053) B3267053
theorem B2178065 : Blo 1451545 2178065 := bstep (se 2 (by rfl) ⟨816774, by rfl⟩ : syracuseStep 2178065 = 1633549) B1633549
theorem B2178083 : Blo 1451545 2178083 := bstep (se 1 (by rfl) ⟨1633562, by rfl⟩ : syracuseStep 2178083 = 3267125) B3267125
theorem B2178113 : Blo 1451545 2178113 := bstep (se 2 (by rfl) ⟨816792, by rfl⟩ : syracuseStep 2178113 = 1633585) B1633585
theorem B3267665 : Blo 1451545 3267665 := bstep (se 2 (by rfl) ⟨1225374, by rfl⟩ : syracuseStep 3267665 = 2450749) B2450749
theorem B2178131 : Blo 1451545 2178131 := bstep (se 1 (by rfl) ⟨1633598, by rfl⟩ : syracuseStep 2178131 = 3267197) B3267197
theorem B3267683 : Blo 1451545 3267683 := bstep (se 1 (by rfl) ⟨2450762, by rfl⟩ : syracuseStep 3267683 = 4901525) B4901525
theorem B2178161 : Blo 1451545 2178161 := bstep (se 2 (by rfl) ⟨816810, by rfl⟩ : syracuseStep 2178161 = 1633621) B1633621
theorem B2178179 : Blo 1451545 2178179 := bstep (se 1 (by rfl) ⟨1633634, by rfl⟩ : syracuseStep 2178179 = 3267269) B3267269
theorem B5512333 : Blo 1451545 5512333 := bstep (se 3 (by rfl) ⟨1033562, by rfl⟩ : syracuseStep 5512333 = 2067125) B2067125
theorem B2178209 : Blo 1451545 2178209 := bstep (se 2 (by rfl) ⟨816828, by rfl⟩ : syracuseStep 2178209 = 1633657) B1633657
theorem B5889187 : Blo 1451545 5889187 := bstep (se 1 (by rfl) ⟨4416890, by rfl⟩ : syracuseStep 5889187 = 8833781) B8833781
theorem B2178227 : Blo 1451545 2178227 := bstep (se 1 (by rfl) ⟨1633670, by rfl⟩ : syracuseStep 2178227 = 3267341) B3267341
theorem B2096323 : Blo 1451545 2096323 := bstep (se 1 (by rfl) ⟨1572242, by rfl⟩ : syracuseStep 2096323 = 3144485) B3144485
theorem B2178257 : Blo 1451545 2178257 := bstep (se 2 (by rfl) ⟨816846, by rfl⟩ : syracuseStep 2178257 = 1633693) B1633693
theorem B2178275 : Blo 1451545 2178275 := bstep (se 1 (by rfl) ⟨1633706, by rfl⟩ : syracuseStep 2178275 = 3267413) B3267413
theorem B2178305 : Blo 1451545 2178305 := bstep (se 2 (by rfl) ⟨816864, by rfl⟩ : syracuseStep 2178305 = 1633729) B1633729
theorem B3104003 : Blo 1451545 3104003 := bstep (se 1 (by rfl) ⟨2328002, by rfl⟩ : syracuseStep 3104003 = 4656005) B4656005
theorem B2178323 : Blo 1451545 2178323 := bstep (se 1 (by rfl) ⟨1633742, by rfl⟩ : syracuseStep 2178323 = 3267485) B3267485
theorem B2178353 : Blo 1451545 2178353 := bstep (se 2 (by rfl) ⟨816882, by rfl⟩ : syracuseStep 2178353 = 1633765) B1633765
theorem B2178371 : Blo 1451545 2178371 := bstep (se 1 (by rfl) ⟨1633778, by rfl⟩ : syracuseStep 2178371 = 3267557) B3267557
theorem B3677521 : Blo 1451545 3677521 := bstep (se 2 (by rfl) ⟨1379070, by rfl⟩ : syracuseStep 3677521 = 2758141) B2758141
theorem B2178401 : Blo 1451545 2178401 := bstep (se 2 (by rfl) ⟨816900, by rfl⟩ : syracuseStep 2178401 = 1633801) B1633801
theorem B3267953 : Blo 1451545 3267953 := bstep (se 2 (by rfl) ⟨1225482, by rfl⟩ : syracuseStep 3267953 = 2450965) B2450965
theorem B2178419 : Blo 1451545 2178419 := bstep (se 1 (by rfl) ⟨1633814, by rfl⟩ : syracuseStep 2178419 = 3267629) B3267629
theorem B3267971 : Blo 1451545 3267971 := bstep (se 1 (by rfl) ⟨2450978, by rfl⟩ : syracuseStep 3267971 = 4901957) B4901957
theorem B8273285 : Blo 1451545 8273285 := bstep (se 4 (by rfl) ⟨775620, by rfl⟩ : syracuseStep 8273285 = 1551241) B1551241
theorem B2178449 : Blo 1451545 2178449 := bstep (se 2 (by rfl) ⟨816918, by rfl⟩ : syracuseStep 2178449 = 1633837) B1633837
theorem B1744291 : Blo 1451545 1744291 := bstep (se 1 (by rfl) ⟨1308218, by rfl⟩ : syracuseStep 1744291 = 2616437) B2616437
theorem B2178467 : Blo 1451545 2178467 := bstep (se 1 (by rfl) ⟨1633850, by rfl⟩ : syracuseStep 2178467 = 3267701) B3267701
theorem B7855537 : Blo 1451545 7855537 := bstep (se 2 (by rfl) ⟨2945826, by rfl⟩ : syracuseStep 7855537 = 5891653) B5891653
theorem B2178497 : Blo 1451545 2178497 := bstep (se 2 (by rfl) ⟨816936, by rfl⟩ : syracuseStep 2178497 = 1633873) B1633873
theorem B9305549 : Blo 1451545 9305549 := bstep (se 3 (by rfl) ⟨1744790, by rfl⟩ : syracuseStep 9305549 = 3489581) B3489581
theorem B2178515 : Blo 1451545 2178515 := bstep (se 1 (by rfl) ⟨1633886, by rfl⟩ : syracuseStep 2178515 = 3267773) B3267773
theorem B9567715 : Blo 1451545 9567715 := bstep (se 1 (by rfl) ⟨7175786, by rfl⟩ : syracuseStep 9567715 = 14351573) B14351573
theorem B2178545 : Blo 1451545 2178545 := bstep (se 2 (by rfl) ⟨816954, by rfl⟩ : syracuseStep 2178545 = 1633909) B1633909
theorem B2178563 : Blo 1451545 2178563 := bstep (se 1 (by rfl) ⟨1633922, by rfl⟩ : syracuseStep 2178563 = 3267845) B3267845
theorem B2178593 : Blo 1451545 2178593 := bstep (se 2 (by rfl) ⟨816972, by rfl⟩ : syracuseStep 2178593 = 1633945) B1633945
theorem B4136483 : Blo 1451545 4136483 := bstep (se 1 (by rfl) ⟨3102362, by rfl⟩ : syracuseStep 4136483 = 6204725) B6204725
theorem B2178611 : Blo 1451545 2178611 := bstep (se 1 (by rfl) ⟨1633958, by rfl⟩ : syracuseStep 2178611 = 3267917) B3267917
theorem B4972099 : Blo 1451545 4972099 := bstep (se 1 (by rfl) ⟨3729074, by rfl⟩ : syracuseStep 4972099 = 7458149) B7458149
theorem B16555589 : Blo 1451545 16555589 := bstep (se 4 (by rfl) ⟨1552086, by rfl⟩ : syracuseStep 16555589 = 3104173) B3104173
theorem B2178641 : Blo 1451545 2178641 := bstep (se 2 (by rfl) ⟨816990, by rfl⟩ : syracuseStep 2178641 = 1633981) B1633981
theorem B2178659 : Blo 1451545 2178659 := bstep (se 1 (by rfl) ⟨1633994, by rfl⟩ : syracuseStep 2178659 = 3267989) B3267989
theorem B3677795 : Blo 1451545 3677795 := bstep (se 1 (by rfl) ⟨2758346, by rfl⟩ : syracuseStep 3677795 = 5516693) B5516693
theorem B14900849 : Blo 1451545 14900849 := bstep (se 2 (by rfl) ⟨5587818, by rfl⟩ : syracuseStep 14900849 = 11175637) B11175637
theorem B2178689 : Blo 1451545 2178689 := bstep (se 2 (by rfl) ⟨817008, by rfl⟩ : syracuseStep 2178689 = 1634017) B1634017
theorem B3268241 : Blo 1451545 3268241 := bstep (se 2 (by rfl) ⟨1225590, by rfl⟩ : syracuseStep 3268241 = 2451181) B2451181
theorem B2178707 : Blo 1451545 2178707 := bstep (se 1 (by rfl) ⟨1634030, by rfl⟩ : syracuseStep 2178707 = 3268061) B3268061
theorem B3268259 : Blo 1451545 3268259 := bstep (se 1 (by rfl) ⟨2451194, by rfl⟩ : syracuseStep 3268259 = 4902389) B4902389
theorem B2178737 : Blo 1451545 2178737 := bstep (se 2 (by rfl) ⟨817026, by rfl⟩ : syracuseStep 2178737 = 1634053) B1634053
theorem B2178755 : Blo 1451545 2178755 := bstep (se 1 (by rfl) ⟨1634066, by rfl⟩ : syracuseStep 2178755 = 3268133) B3268133
theorem B2178785 : Blo 1451545 2178785 := bstep (se 2 (by rfl) ⟨817044, by rfl⟩ : syracuseStep 2178785 = 1634089) B1634089
theorem B2178803 : Blo 1451545 2178803 := bstep (se 1 (by rfl) ⟨1634102, by rfl⟩ : syracuseStep 2178803 = 3268205) B3268205
theorem B2178833 : Blo 1451545 2178833 := bstep (se 2 (by rfl) ⟨817062, by rfl⟩ : syracuseStep 2178833 = 1634125) B1634125
theorem B2178851 : Blo 1451545 2178851 := bstep (se 1 (by rfl) ⟨1634138, by rfl⟩ : syracuseStep 2178851 = 3268277) B3268277
theorem B3677987 : Blo 1451545 3677987 := bstep (se 1 (by rfl) ⟨2758490, by rfl⟩ : syracuseStep 3677987 = 5516981) B5516981
theorem B6201137 : Blo 1451545 6201137 := bstep (se 2 (by rfl) ⟨2325426, by rfl⟩ : syracuseStep 6201137 = 4650853) B4650853
theorem B2178881 : Blo 1451545 2178881 := bstep (se 2 (by rfl) ⟨817080, by rfl⟩ : syracuseStep 2178881 = 1634161) B1634161
theorem B2178899 : Blo 1451545 2178899 := bstep (se 1 (by rfl) ⟨1634174, by rfl⟩ : syracuseStep 2178899 = 3268349) B3268349
theorem B2178929 : Blo 1451545 2178929 := bstep (se 2 (by rfl) ⟨817098, by rfl⟩ : syracuseStep 2178929 = 1634197) B1634197
theorem B2178947 : Blo 1451545 2178947 := bstep (se 1 (by rfl) ⟨1634210, by rfl⟩ : syracuseStep 2178947 = 3268421) B3268421
theorem B14917517 : Blo 1451545 14917517 := bstep (se 3 (by rfl) ⟨2797034, by rfl⟩ : syracuseStep 14917517 = 5594069) B5594069
theorem B2178977 : Blo 1451545 2178977 := bstep (se 2 (by rfl) ⟨817116, by rfl⟩ : syracuseStep 2178977 = 1634233) B1634233
theorem B5513123 : Blo 1451545 5513123 := bstep (se 1 (by rfl) ⟨4134842, by rfl⟩ : syracuseStep 5513123 = 8269685) B8269685
theorem B8388515 : Blo 1451545 8388515 := bstep (se 1 (by rfl) ⟨6291386, by rfl⟩ : syracuseStep 8388515 = 12582773) B12582773
theorem B3268529 : Blo 1451545 3268529 := bstep (se 2 (by rfl) ⟨1225698, by rfl⟩ : syracuseStep 3268529 = 2451397) B2451397
theorem B2178995 : Blo 1451545 2178995 := bstep (se 1 (by rfl) ⟨1634246, by rfl⟩ : syracuseStep 2178995 = 3268493) B3268493
theorem B3268547 : Blo 1451545 3268547 := bstep (se 1 (by rfl) ⟨2451410, by rfl⟩ : syracuseStep 3268547 = 4902821) B4902821
theorem B2179025 : Blo 1451545 2179025 := bstep (se 2 (by rfl) ⟨817134, by rfl⟩ : syracuseStep 2179025 = 1634269) B1634269
theorem B26484707 : Blo 1451545 26484707 := bstep (se 1 (by rfl) ⟨19863530, by rfl⟩ : syracuseStep 26484707 = 39727061) B39727061
theorem B2179043 : Blo 1451545 2179043 := bstep (se 1 (by rfl) ⟨1634282, by rfl⟩ : syracuseStep 2179043 = 3268565) B3268565
theorem B11034629 : Blo 1451545 11034629 := bstep (se 4 (by rfl) ⟨1034496, by rfl⟩ : syracuseStep 11034629 = 2068993) B2068993
theorem B3268619 : Blo 1451545 3268619 := bstep (se 1 (by rfl) ⟨2451464, by rfl⟩ : syracuseStep 3268619 = 4902929) B4902929
theorem B2179097 : Blo 1451545 2179097 := bstep (se 2 (by rfl) ⟨817161, by rfl⟩ : syracuseStep 2179097 = 1634323) B1634323
theorem B10469411 : Blo 1451545 10469411 := bstep (se 1 (by rfl) ⟨7852058, by rfl⟩ : syracuseStep 10469411 = 15704117) B15704117
theorem B3268673 : Blo 1451545 3268673 := bstep (se 2 (by rfl) ⟨1225752, by rfl⟩ : syracuseStep 3268673 = 2451505) B2451505
theorem B5513291 : Blo 1451545 5513291 := bstep (se 1 (by rfl) ⟨4134968, by rfl⟩ : syracuseStep 5513291 = 8269937) B8269937
theorem B5513305 : Blo 1451545 5513305 := bstep (se 2 (by rfl) ⟨2067489, by rfl⟩ : syracuseStep 5513305 = 4134979) B4134979
theorem B2179211 : Blo 1451545 2179211 := bstep (se 1 (by rfl) ⟨1634408, by rfl⟩ : syracuseStep 2179211 = 3268817) B3268817
theorem B2179223 : Blo 1451545 2179223 := bstep (se 1 (by rfl) ⟨1634417, by rfl⟩ : syracuseStep 2179223 = 3268835) B3268835
theorem B16777367 : Blo 1451545 16777367 := bstep (se 1 (by rfl) ⟨12583025, by rfl⟩ : syracuseStep 16777367 = 25166051) B25166051
theorem B2449561 : Blo 1451545 2449561 := bstep (se 2 (by rfl) ⟨918585, by rfl⟩ : syracuseStep 2449561 = 1837171) B1837171
theorem B26509517 : Blo 1451545 26509517 := bstep (se 3 (by rfl) ⟨4970534, by rfl⟩ : syracuseStep 26509517 = 9941069) B9941069
theorem B2179289 : Blo 1451545 2179289 := bstep (se 2 (by rfl) ⟨817233, by rfl⟩ : syracuseStep 2179289 = 1634467) B1634467
theorem B4899095 : Blo 1451545 4899095 := bstep (se 1 (by rfl) ⟨3674321, by rfl⟩ : syracuseStep 4899095 = 7348643) B7348643
theorem B3268889 : Blo 1451545 3268889 := bstep (se 2 (by rfl) ⟨1225833, by rfl⟩ : syracuseStep 3268889 = 2451667) B2451667
theorem B3981619 : Blo 1451545 3981619 := bstep (se 1 (by rfl) ⟨2986214, by rfl⟩ : syracuseStep 3981619 = 5972429) B5972429
theorem B4137281 : Blo 1451545 4137281 := bstep (se 2 (by rfl) ⟨1551480, by rfl⟩ : syracuseStep 4137281 = 3102961) B3102961
theorem B2179403 : Blo 1451545 2179403 := bstep (se 1 (by rfl) ⟨1634552, by rfl⟩ : syracuseStep 2179403 = 3269105) B3269105
theorem B2179415 : Blo 1451545 2179415 := bstep (se 1 (by rfl) ⟨1634561, by rfl⟩ : syracuseStep 2179415 = 3269123) B3269123
theorem B3268979 : Blo 1451545 3268979 := bstep (se 1 (by rfl) ⟨2451734, by rfl⟩ : syracuseStep 3268979 = 4903469) B4903469
theorem B3269015 : Blo 1451545 3269015 := bstep (se 1 (by rfl) ⟨2451761, by rfl⟩ : syracuseStep 3269015 = 4903523) B4903523
theorem B2179481 : Blo 1451545 2179481 := bstep (se 2 (by rfl) ⟨817305, by rfl⟩ : syracuseStep 2179481 = 1634611) B1634611
theorem B4252097 : Blo 1451545 4252097 := bstep (se 2 (by rfl) ⟨1594536, by rfl⟩ : syracuseStep 4252097 = 3189073) B3189073
theorem B3490265 : Blo 1451545 3490265 := bstep (se 2 (by rfl) ⟨1308849, by rfl⟩ : syracuseStep 3490265 = 2617699) B2617699
theorem B2179595 : Blo 1451545 2179595 := bstep (se 1 (by rfl) ⟨1634696, by rfl⟩ : syracuseStep 2179595 = 3269393) B3269393
theorem B2179607 : Blo 1451545 2179607 := bstep (se 1 (by rfl) ⟨1634705, by rfl⟩ : syracuseStep 2179607 = 3269411) B3269411
theorem B22364707 : Blo 1451545 22364707 := bstep (se 1 (by rfl) ⟨16773530, by rfl⟩ : syracuseStep 22364707 = 33547061) B33547061
theorem B226386485 : Blo 1451545 226386485 := bstep (se 5 (by rfl) ⟨10611866, by rfl⟩ : syracuseStep 226386485 = 21223733) B21223733
theorem B11936321 : Blo 1451545 11936321 := bstep (se 2 (by rfl) ⟨4476120, by rfl⟩ : syracuseStep 11936321 = 8952241) B8952241
theorem B12411467 : Blo 1451545 12411467 := bstep (se 1 (by rfl) ⟨9308600, by rfl⟩ : syracuseStep 12411467 = 18617201) B18617201
theorem B3269195 : Blo 1451545 3269195 := bstep (se 1 (by rfl) ⟨2451896, by rfl⟩ : syracuseStep 3269195 = 4903793) B4903793
theorem B3539531 : Blo 1451545 3539531 := bstep (se 1 (by rfl) ⟨2654648, by rfl⟩ : syracuseStep 3539531 = 5309297) B5309297
theorem B2269783 : Blo 1451545 2269783 := bstep (se 1 (by rfl) ⟨1702337, by rfl⟩ : syracuseStep 2269783 = 3404675) B3404675
theorem B2179673 : Blo 1451545 2179673 := bstep (se 2 (by rfl) ⟨817377, by rfl⟩ : syracuseStep 2179673 = 1634755) B1634755
theorem B3269249 : Blo 1451545 3269249 := bstep (se 2 (by rfl) ⟨1225968, by rfl⟩ : syracuseStep 3269249 = 2451937) B2451937
theorem B2179787 : Blo 1451545 2179787 := bstep (se 1 (by rfl) ⟨1634840, by rfl⟩ : syracuseStep 2179787 = 3269681) B3269681
theorem B2450135 : Blo 1451545 2450135 := bstep (se 1 (by rfl) ⟨1837601, by rfl⟩ : syracuseStep 2450135 = 3675203) B3675203
theorem B2179799 : Blo 1451545 2179799 := bstep (se 1 (by rfl) ⟨1634849, by rfl⟩ : syracuseStep 2179799 = 3269699) B3269699
theorem B2794201 : Blo 1451545 2794201 := bstep (se 2 (by rfl) ⟨1047825, by rfl⟩ : syracuseStep 2794201 = 2095651) B2095651
theorem B2179865 : Blo 1451545 2179865 := bstep (se 2 (by rfl) ⟨817449, by rfl⟩ : syracuseStep 2179865 = 1634899) B1634899
theorem B7357229 : Blo 1451545 7357229 := bstep (se 3 (by rfl) ⟨1379480, by rfl⟩ : syracuseStep 7357229 = 2758961) B2758961
theorem B4899635 : Blo 1451545 4899635 := bstep (se 1 (by rfl) ⟨3674726, by rfl⟩ : syracuseStep 4899635 = 7349453) B7349453
theorem B2450263 : Blo 1451545 2450263 := bstep (se 1 (by rfl) ⟨1837697, by rfl⟩ : syracuseStep 2450263 = 3675395) B3675395
theorem B3269465 : Blo 1451545 3269465 := bstep (se 2 (by rfl) ⟨1226049, by rfl⟩ : syracuseStep 3269465 = 2452099) B2452099
theorem B43623269 : Blo 1451545 43623269 := bstep (se 4 (by rfl) ⟨4089681, by rfl⟩ : syracuseStep 43623269 = 8179363) B8179363
theorem B2179979 : Blo 1451545 2179979 := bstep (se 1 (by rfl) ⟨1634984, by rfl⟩ : syracuseStep 2179979 = 3269969) B3269969
theorem B2179991 : Blo 1451545 2179991 := bstep (se 1 (by rfl) ⟨1634993, by rfl⟩ : syracuseStep 2179991 = 3269987) B3269987
theorem B3269555 : Blo 1451545 3269555 := bstep (se 1 (by rfl) ⟨2452166, by rfl⟩ : syracuseStep 3269555 = 4904333) B4904333
theorem B1745867 : Blo 1451545 1745867 := bstep (se 1 (by rfl) ⟨1309400, by rfl⟩ : syracuseStep 1745867 = 2618801) B2618801
theorem B3269591 : Blo 1451545 3269591 := bstep (se 1 (by rfl) ⟨2452193, by rfl⟩ : syracuseStep 3269591 = 4904387) B4904387
theorem B2180057 : Blo 1451545 2180057 := bstep (se 2 (by rfl) ⟨817521, by rfl⟩ : syracuseStep 2180057 = 1635043) B1635043
theorem B41870357 : Blo 1451545 41870357 := bstep (se 6 (by rfl) ⟨981336, by rfl⟩ : syracuseStep 41870357 = 1962673) B1962673
theorem B5514263 : Blo 1451545 5514263 := bstep (se 1 (by rfl) ⟨4135697, by rfl⟩ : syracuseStep 5514263 = 8271395) B8271395
theorem B3679283 : Blo 1451545 3679283 := bstep (se 1 (by rfl) ⟨2759462, by rfl⟩ : syracuseStep 3679283 = 5518925) B5518925
theorem B4899905 : Blo 1451545 4899905 := bstep (se 2 (by rfl) ⟨1837464, by rfl⟩ : syracuseStep 4899905 = 3674929) B3674929
theorem B2180171 : Blo 1451545 2180171 := bstep (se 1 (by rfl) ⟨1635128, by rfl⟩ : syracuseStep 2180171 = 3270257) B3270257
theorem B2180183 : Blo 1451545 2180183 := bstep (se 1 (by rfl) ⟨1635137, by rfl⟩ : syracuseStep 2180183 = 3270275) B3270275
theorem B3269771 : Blo 1451545 3269771 := bstep (se 1 (by rfl) ⟨2452328, by rfl⟩ : syracuseStep 3269771 = 4904657) B4904657
theorem B2180249 : Blo 1451545 2180249 := bstep (se 2 (by rfl) ⟨817593, by rfl⟩ : syracuseStep 2180249 = 1635187) B1635187
theorem B3269825 : Blo 1451545 3269825 := bstep (se 2 (by rfl) ⟨1226184, by rfl⟩ : syracuseStep 3269825 = 2452369) B2452369
theorem B5235929 : Blo 1451545 5235929 := bstep (se 2 (by rfl) ⟨1963473, by rfl⟩ : syracuseStep 5235929 = 3926947) B3926947
theorem B3270041 : Blo 1451545 3270041 := bstep (se 2 (by rfl) ⟨1226265, by rfl⟩ : syracuseStep 3270041 = 2452531) B2452531
theorem B2450891 : Blo 1451545 2450891 := bstep (se 1 (by rfl) ⟨1838168, by rfl⟩ : syracuseStep 2450891 = 3676337) B3676337
theorem B8832473 : Blo 1451545 8832473 := bstep (se 2 (by rfl) ⟨3312177, by rfl⟩ : syracuseStep 8832473 = 6624355) B6624355
theorem B3270131 : Blo 1451545 3270131 := bstep (se 1 (by rfl) ⟨2452598, by rfl⟩ : syracuseStep 3270131 = 4905197) B4905197
theorem B7349777 : Blo 1451545 7349777 := bstep (se 2 (by rfl) ⟨2756166, by rfl⟩ : syracuseStep 7349777 = 5512333) B5512333
theorem B3270167 : Blo 1451545 3270167 := bstep (se 1 (by rfl) ⟨2452625, by rfl⟩ : syracuseStep 3270167 = 4905251) B4905251
theorem B1451563 : Blo 1451545 1451563 := bstep (se 1 (by rfl) ⟨1088672, by rfl⟩ : syracuseStep 1451563 = 2177345) B2177345
theorem B1451575 : Blo 1451545 1451575 := bstep (se 1 (by rfl) ⟨1088681, by rfl⟩ : syracuseStep 1451575 = 2177363) B2177363
theorem B1451595 : Blo 1451545 1451595 := bstep (se 1 (by rfl) ⟨1088696, by rfl⟩ : syracuseStep 1451595 = 2177393) B2177393
theorem B2451019 : Blo 1451545 2451019 := bstep (se 1 (by rfl) ⟨1838264, by rfl⟩ : syracuseStep 2451019 = 3676529) B3676529
theorem B1451607 : Blo 1451545 1451607 := bstep (se 1 (by rfl) ⟨1088705, by rfl⟩ : syracuseStep 1451607 = 2177411) B2177411
theorem B4900445 : Blo 1451545 4900445 := bstep (se 3 (by rfl) ⟨918833, by rfl⟩ : syracuseStep 4900445 = 1837667) B1837667
theorem B3925597 : Blo 1451545 3925597 := bstep (se 3 (by rfl) ⟨736049, by rfl⟩ : syracuseStep 3925597 = 1472099) B1472099
theorem B1451627 : Blo 1451545 1451627 := bstep (se 1 (by rfl) ⟨1088720, by rfl⟩ : syracuseStep 1451627 = 2177441) B2177441
theorem B1451639 : Blo 1451545 1451639 := bstep (se 1 (by rfl) ⟨1088729, by rfl⟩ : syracuseStep 1451639 = 2177459) B2177459
theorem B1451659 : Blo 1451545 1451659 := bstep (se 1 (by rfl) ⟨1088744, by rfl⟩ : syracuseStep 1451659 = 2177489) B2177489
theorem B1451671 : Blo 1451545 1451671 := bstep (se 1 (by rfl) ⟨1088753, by rfl⟩ : syracuseStep 1451671 = 2177507) B2177507
theorem B1451691 : Blo 1451545 1451691 := bstep (se 1 (by rfl) ⟨1088768, by rfl⟩ : syracuseStep 1451691 = 2177537) B2177537
theorem B7349939 : Blo 1451545 7349939 := bstep (se 1 (by rfl) ⟨5512454, by rfl⟩ : syracuseStep 7349939 = 11024909) B11024909
theorem B6981299 : Blo 1451545 6981299 := bstep (se 1 (by rfl) ⟨5235974, by rfl⟩ : syracuseStep 6981299 = 10471949) B10471949
theorem B1451703 : Blo 1451545 1451703 := bstep (se 1 (by rfl) ⟨1088777, by rfl⟩ : syracuseStep 1451703 = 2177555) B2177555
theorem B1451723 : Blo 1451545 1451723 := bstep (se 1 (by rfl) ⟨1088792, by rfl⟩ : syracuseStep 1451723 = 2177585) B2177585
theorem B3270347 : Blo 1451545 3270347 := bstep (se 1 (by rfl) ⟨2452760, by rfl⟩ : syracuseStep 3270347 = 4905521) B4905521
theorem B1451735 : Blo 1451545 1451735 := bstep (se 1 (by rfl) ⟨1088801, by rfl⟩ : syracuseStep 1451735 = 2177603) B2177603
theorem B2451161 : Blo 1451545 2451161 := bstep (se 2 (by rfl) ⟨919185, by rfl⟩ : syracuseStep 2451161 = 1838371) B1838371
theorem B1451755 : Blo 1451545 1451755 := bstep (se 1 (by rfl) ⟨1088816, by rfl⟩ : syracuseStep 1451755 = 2177633) B2177633
theorem B1492715 : Blo 1451545 1492715 := bstep (se 1 (by rfl) ⟨1119536, by rfl⟩ : syracuseStep 1492715 = 2239073) B2239073
theorem B1451767 : Blo 1451545 1451767 := bstep (se 1 (by rfl) ⟨1088825, by rfl⟩ : syracuseStep 1451767 = 2177651) B2177651
theorem B3270401 : Blo 1451545 3270401 := bstep (se 2 (by rfl) ⟨1226400, by rfl⟩ : syracuseStep 3270401 = 2452801) B2452801
theorem B1451787 : Blo 1451545 1451787 := bstep (se 1 (by rfl) ⟨1088840, by rfl⟩ : syracuseStep 1451787 = 2177681) B2177681
theorem B13428497 : Blo 1451545 13428497 := bstep (se 2 (by rfl) ⟨5035686, by rfl⟩ : syracuseStep 13428497 = 10071373) B10071373
theorem B1451799 : Blo 1451545 1451799 := bstep (se 1 (by rfl) ⟨1088849, by rfl⟩ : syracuseStep 1451799 = 2177699) B2177699
theorem B5588759 : Blo 1451545 5588759 := bstep (se 1 (by rfl) ⟨4191569, by rfl⟩ : syracuseStep 5588759 = 8383139) B8383139
theorem B1451819 : Blo 1451545 1451819 := bstep (se 1 (by rfl) ⟨1088864, by rfl⟩ : syracuseStep 1451819 = 2177729) B2177729
theorem B1550135 : Blo 1451545 1550135 := bstep (se 1 (by rfl) ⟨1162601, by rfl⟩ : syracuseStep 1550135 = 2325203) B2325203
theorem B1451831 : Blo 1451545 1451831 := bstep (se 1 (by rfl) ⟨1088873, by rfl⟩ : syracuseStep 1451831 = 2177747) B2177747
theorem B1451851 : Blo 1451545 1451851 := bstep (se 1 (by rfl) ⟨1088888, by rfl⟩ : syracuseStep 1451851 = 2177777) B2177777
theorem B1451863 : Blo 1451545 1451863 := bstep (se 1 (by rfl) ⟨1088897, by rfl⟩ : syracuseStep 1451863 = 2177795) B2177795
theorem B2451289 : Blo 1451545 2451289 := bstep (se 2 (by rfl) ⟨919233, by rfl⟩ : syracuseStep 2451289 = 1838467) B1838467
theorem B1451883 : Blo 1451545 1451883 := bstep (se 1 (by rfl) ⟨1088912, by rfl⟩ : syracuseStep 1451883 = 2177825) B2177825
theorem B1451895 : Blo 1451545 1451895 := bstep (se 1 (by rfl) ⟨1088921, by rfl⟩ : syracuseStep 1451895 = 2177843) B2177843
theorem B1451915 : Blo 1451545 1451915 := bstep (se 1 (by rfl) ⟨1088936, by rfl⟩ : syracuseStep 1451915 = 2177873) B2177873
theorem B1451927 : Blo 1451545 1451927 := bstep (se 1 (by rfl) ⟨1088945, by rfl⟩ : syracuseStep 1451927 = 2177891) B2177891
theorem B1451947 : Blo 1451545 1451947 := bstep (se 1 (by rfl) ⟨1088960, by rfl⟩ : syracuseStep 1451947 = 2177921) B2177921
theorem B1451959 : Blo 1451545 1451959 := bstep (se 1 (by rfl) ⟨1088969, by rfl⟩ : syracuseStep 1451959 = 2177939) B2177939
theorem B1451979 : Blo 1451545 1451979 := bstep (se 1 (by rfl) ⟨1088984, by rfl⟩ : syracuseStep 1451979 = 2177969) B2177969
theorem B1451991 : Blo 1451545 1451991 := bstep (se 1 (by rfl) ⟨1088993, by rfl⟩ : syracuseStep 1451991 = 2177987) B2177987
theorem B12756953 : Blo 1451545 12756953 := bstep (se 2 (by rfl) ⟨4783857, by rfl⟩ : syracuseStep 12756953 = 9567715) B9567715
theorem B1452011 : Blo 1451545 1452011 := bstep (se 1 (by rfl) ⟨1089008, by rfl⟩ : syracuseStep 1452011 = 2178017) B2178017
theorem B1452023 : Blo 1451545 1452023 := bstep (se 1 (by rfl) ⟨1089017, by rfl⟩ : syracuseStep 1452023 = 2178035) B2178035
theorem B1452043 : Blo 1451545 1452043 := bstep (se 1 (by rfl) ⟨1089032, by rfl⟩ : syracuseStep 1452043 = 2178065) B2178065
theorem B21235729 : Blo 1451545 21235729 := bstep (se 2 (by rfl) ⟨7963398, by rfl⟩ : syracuseStep 21235729 = 15926797) B15926797
theorem B1452055 : Blo 1451545 1452055 := bstep (se 1 (by rfl) ⟨1089041, by rfl⟩ : syracuseStep 1452055 = 2178083) B2178083
theorem B1452075 : Blo 1451545 1452075 := bstep (se 1 (by rfl) ⟨1089056, by rfl⟩ : syracuseStep 1452075 = 2178113) B2178113
theorem B1452087 : Blo 1451545 1452087 := bstep (se 1 (by rfl) ⟨1089065, by rfl⟩ : syracuseStep 1452087 = 2178131) B2178131
theorem B1452107 : Blo 1451545 1452107 := bstep (se 1 (by rfl) ⟨1089080, by rfl⟩ : syracuseStep 1452107 = 2178161) B2178161
theorem B1452119 : Blo 1451545 1452119 := bstep (se 1 (by rfl) ⟨1089089, by rfl⟩ : syracuseStep 1452119 = 2178179) B2178179
theorem B6629465 : Blo 1451545 6629465 := bstep (se 2 (by rfl) ⟨2486049, by rfl⟩ : syracuseStep 6629465 = 4972099) B4972099
theorem B1452139 : Blo 1451545 1452139 := bstep (se 1 (by rfl) ⟨1089104, by rfl⟩ : syracuseStep 1452139 = 2178209) B2178209
theorem B1452151 : Blo 1451545 1452151 := bstep (se 1 (by rfl) ⟨1089113, by rfl⟩ : syracuseStep 1452151 = 2178227) B2178227
theorem B1452171 : Blo 1451545 1452171 := bstep (se 1 (by rfl) ⟨1089128, by rfl⟩ : syracuseStep 1452171 = 2178257) B2178257
theorem B1452183 : Blo 1451545 1452183 := bstep (se 1 (by rfl) ⟨1089137, by rfl⟩ : syracuseStep 1452183 = 2178275) B2178275
theorem B1452203 : Blo 1451545 1452203 := bstep (se 1 (by rfl) ⟨1089152, by rfl⟩ : syracuseStep 1452203 = 2178305) B2178305
theorem B1452215 : Blo 1451545 1452215 := bstep (se 1 (by rfl) ⟨1089161, by rfl⟩ : syracuseStep 1452215 = 2178323) B2178323
theorem B1452235 : Blo 1451545 1452235 := bstep (se 1 (by rfl) ⟨1089176, by rfl⟩ : syracuseStep 1452235 = 2178353) B2178353
theorem B1452247 : Blo 1451545 1452247 := bstep (se 1 (by rfl) ⟨1089185, by rfl⟩ : syracuseStep 1452247 = 2178371) B2178371
theorem B1452267 : Blo 1451545 1452267 := bstep (se 1 (by rfl) ⟨1089200, by rfl⟩ : syracuseStep 1452267 = 2178401) B2178401
theorem B1452279 : Blo 1451545 1452279 := bstep (se 1 (by rfl) ⟨1089209, by rfl⟩ : syracuseStep 1452279 = 2178419) B2178419
theorem B5515523 : Blo 1451545 5515523 := bstep (se 1 (by rfl) ⟨4136642, by rfl⟩ : syracuseStep 5515523 = 8273285) B8273285
theorem B1452299 : Blo 1451545 1452299 := bstep (se 1 (by rfl) ⟨1089224, by rfl⟩ : syracuseStep 1452299 = 2178449) B2178449
theorem B1452311 : Blo 1451545 1452311 := bstep (se 1 (by rfl) ⟨1089233, by rfl⟩ : syracuseStep 1452311 = 2178467) B2178467
theorem B1452331 : Blo 1451545 1452331 := bstep (se 1 (by rfl) ⟨1089248, by rfl⟩ : syracuseStep 1452331 = 2178497) B2178497
theorem B6203699 : Blo 1451545 6203699 := bstep (se 1 (by rfl) ⟨4652774, by rfl⟩ : syracuseStep 6203699 = 9305549) B9305549
theorem B1452343 : Blo 1451545 1452343 := bstep (se 1 (by rfl) ⟨1089257, by rfl⟩ : syracuseStep 1452343 = 2178515) B2178515
theorem B1452363 : Blo 1451545 1452363 := bstep (se 1 (by rfl) ⟨1089272, by rfl⟩ : syracuseStep 1452363 = 2178545) B2178545
theorem B1837399 : Blo 1451545 1837399 := bstep (se 1 (by rfl) ⟨1378049, by rfl⟩ : syracuseStep 1837399 = 2756099) B2756099
theorem B1452375 : Blo 1451545 1452375 := bstep (se 1 (by rfl) ⟨1089281, by rfl⟩ : syracuseStep 1452375 = 2178563) B2178563
theorem B1452395 : Blo 1451545 1452395 := bstep (se 1 (by rfl) ⟨1089296, by rfl⟩ : syracuseStep 1452395 = 2178593) B2178593
theorem B1452407 : Blo 1451545 1452407 := bstep (se 1 (by rfl) ⟨1089305, by rfl⟩ : syracuseStep 1452407 = 2178611) B2178611
theorem B11037059 : Blo 1451545 11037059 := bstep (se 1 (by rfl) ⟨8277794, by rfl⟩ : syracuseStep 11037059 = 16555589) B16555589
theorem B1452427 : Blo 1451545 1452427 := bstep (se 1 (by rfl) ⟨1089320, by rfl⟩ : syracuseStep 1452427 = 2178641) B2178641
theorem B1452439 : Blo 1451545 1452439 := bstep (se 1 (by rfl) ⟨1089329, by rfl⟩ : syracuseStep 1452439 = 2178659) B2178659
theorem B2451863 : Blo 1451545 2451863 := bstep (se 1 (by rfl) ⟨1838897, by rfl⟩ : syracuseStep 2451863 = 3677795) B3677795
theorem B1452459 : Blo 1451545 1452459 := bstep (se 1 (by rfl) ⟨1089344, by rfl⟩ : syracuseStep 1452459 = 2178689) B2178689
theorem B1452471 : Blo 1451545 1452471 := bstep (se 1 (by rfl) ⟨1089353, by rfl⟩ : syracuseStep 1452471 = 2178707) B2178707
theorem B1452491 : Blo 1451545 1452491 := bstep (se 1 (by rfl) ⟨1089368, by rfl⟩ : syracuseStep 1452491 = 2178737) B2178737
theorem B1452503 : Blo 1451545 1452503 := bstep (se 1 (by rfl) ⟨1089377, by rfl⟩ : syracuseStep 1452503 = 2178755) B2178755
theorem B1452523 : Blo 1451545 1452523 := bstep (se 1 (by rfl) ⟨1089392, by rfl⟩ : syracuseStep 1452523 = 2178785) B2178785
theorem B1452535 : Blo 1451545 1452535 := bstep (se 1 (by rfl) ⟨1089401, by rfl⟩ : syracuseStep 1452535 = 2178803) B2178803
theorem B1452555 : Blo 1451545 1452555 := bstep (se 1 (by rfl) ⟨1089416, by rfl⟩ : syracuseStep 1452555 = 2178833) B2178833
theorem B1452567 : Blo 1451545 1452567 := bstep (se 1 (by rfl) ⟨1089425, by rfl⟩ : syracuseStep 1452567 = 2178851) B2178851
theorem B2451991 : Blo 1451545 2451991 := bstep (se 1 (by rfl) ⟨1838993, by rfl⟩ : syracuseStep 2451991 = 3677987) B3677987
theorem B1452587 : Blo 1451545 1452587 := bstep (se 1 (by rfl) ⟨1089440, by rfl⟩ : syracuseStep 1452587 = 2178881) B2178881
theorem B1452599 : Blo 1451545 1452599 := bstep (se 1 (by rfl) ⟨1089449, by rfl⟩ : syracuseStep 1452599 = 2178899) B2178899
theorem B1452619 : Blo 1451545 1452619 := bstep (se 1 (by rfl) ⟨1089464, by rfl⟩ : syracuseStep 1452619 = 2178929) B2178929
theorem B1452631 : Blo 1451545 1452631 := bstep (se 1 (by rfl) ⟨1089473, by rfl⟩ : syracuseStep 1452631 = 2178947) B2178947
theorem B6982237 : Blo 1451545 6982237 := bstep (se 3 (by rfl) ⟨1309169, by rfl⟩ : syracuseStep 6982237 = 2618339) B2618339
theorem B1452651 : Blo 1451545 1452651 := bstep (se 1 (by rfl) ⟨1089488, by rfl⟩ : syracuseStep 1452651 = 2178977) B2178977
theorem B1452663 : Blo 1451545 1452663 := bstep (se 1 (by rfl) ⟨1089497, by rfl⟩ : syracuseStep 1452663 = 2178995) B2178995
theorem B1452683 : Blo 1451545 1452683 := bstep (se 1 (by rfl) ⟨1089512, by rfl⟩ : syracuseStep 1452683 = 2179025) B2179025
theorem B17656471 : Blo 1451545 17656471 := bstep (se 1 (by rfl) ⟨13242353, by rfl⟩ : syracuseStep 17656471 = 26484707) B26484707
theorem B1452695 : Blo 1451545 1452695 := bstep (se 1 (by rfl) ⟨1089521, by rfl⟩ : syracuseStep 1452695 = 2179043) B2179043
theorem B1452715 : Blo 1451545 1452715 := bstep (se 1 (by rfl) ⟨1089536, by rfl⟩ : syracuseStep 1452715 = 2179073) B2179073
theorem B1452727 : Blo 1451545 1452727 := bstep (se 1 (by rfl) ⟨1089545, by rfl⟩ : syracuseStep 1452727 = 2179091) B2179091
theorem B1862347 : Blo 1451545 1862347 := bstep (se 1 (by rfl) ⟨1396760, by rfl⟩ : syracuseStep 1862347 = 2793521) B2793521
theorem B4901579 : Blo 1451545 4901579 := bstep (se 1 (by rfl) ⟨3676184, by rfl⟩ : syracuseStep 4901579 = 7352369) B7352369
theorem B3926731 : Blo 1451545 3926731 := bstep (se 1 (by rfl) ⟨2945048, by rfl⟩ : syracuseStep 3926731 = 5890097) B5890097
theorem B1452747 : Blo 1451545 1452747 := bstep (se 1 (by rfl) ⟨1089560, by rfl⟩ : syracuseStep 1452747 = 2179121) B2179121
theorem B1452759 : Blo 1451545 1452759 := bstep (se 1 (by rfl) ⟨1089569, by rfl⟩ : syracuseStep 1452759 = 2179139) B2179139
theorem B1452779 : Blo 1451545 1452779 := bstep (se 1 (by rfl) ⟨1089584, by rfl⟩ : syracuseStep 1452779 = 2179169) B2179169
theorem B1452791 : Blo 1451545 1452791 := bstep (se 1 (by rfl) ⟨1089593, by rfl⟩ : syracuseStep 1452791 = 2179187) B2179187
theorem B2067211 : Blo 1451545 2067211 := bstep (se 1 (by rfl) ⟨1550408, by rfl⟩ : syracuseStep 2067211 = 3100817) B3100817
theorem B1452811 : Blo 1451545 1452811 := bstep (se 1 (by rfl) ⟨1089608, by rfl⟩ : syracuseStep 1452811 = 2179217) B2179217
theorem B1452823 : Blo 1451545 1452823 := bstep (se 1 (by rfl) ⟨1089617, by rfl⟩ : syracuseStep 1452823 = 2179235) B2179235
theorem B11029283 : Blo 1451545 11029283 := bstep (se 1 (by rfl) ⟨8271962, by rfl⟩ : syracuseStep 11029283 = 16543925) B16543925
theorem B1452843 : Blo 1451545 1452843 := bstep (se 1 (by rfl) ⟨1089632, by rfl⟩ : syracuseStep 1452843 = 2179265) B2179265
theorem B1452855 : Blo 1451545 1452855 := bstep (se 1 (by rfl) ⟨1089641, by rfl⟩ : syracuseStep 1452855 = 2179283) B2179283
theorem B1633099 : Blo 1451545 1633099 := bstep (se 1 (by rfl) ⟨1224824, by rfl⟩ : syracuseStep 1633099 = 2449649) B2449649
theorem B1452875 : Blo 1451545 1452875 := bstep (se 1 (by rfl) ⟨1089656, by rfl⟩ : syracuseStep 1452875 = 2179313) B2179313
theorem B1452887 : Blo 1451545 1452887 := bstep (se 1 (by rfl) ⟨1089665, by rfl⟩ : syracuseStep 1452887 = 2179331) B2179331
theorem B1452907 : Blo 1451545 1452907 := bstep (se 1 (by rfl) ⟨1089680, by rfl⟩ : syracuseStep 1452907 = 2179361) B2179361
theorem B1452919 : Blo 1451545 1452919 := bstep (se 1 (by rfl) ⟨1089689, by rfl⟩ : syracuseStep 1452919 = 2179379) B2179379
theorem B1452939 : Blo 1451545 1452939 := bstep (se 1 (by rfl) ⟨1089704, by rfl⟩ : syracuseStep 1452939 = 2179409) B2179409
theorem B1452951 : Blo 1451545 1452951 := bstep (se 1 (by rfl) ⟨1089713, by rfl⟩ : syracuseStep 1452951 = 2179427) B2179427
theorem B1452971 : Blo 1451545 1452971 := bstep (se 1 (by rfl) ⟨1089728, by rfl⟩ : syracuseStep 1452971 = 2179457) B2179457
theorem B1633207 : Blo 1451545 1633207 := bstep (se 1 (by rfl) ⟨1224905, by rfl⟩ : syracuseStep 1633207 = 2449811) B2449811
theorem B1452983 : Blo 1451545 1452983 := bstep (se 1 (by rfl) ⟨1089737, by rfl⟩ : syracuseStep 1452983 = 2179475) B2179475
theorem B1453003 : Blo 1451545 1453003 := bstep (se 1 (by rfl) ⟨1089752, by rfl⟩ : syracuseStep 1453003 = 2179505) B2179505
theorem B1453015 : Blo 1451545 1453015 := bstep (se 1 (by rfl) ⟨1089761, by rfl⟩ : syracuseStep 1453015 = 2179523) B2179523
theorem B4901849 : Blo 1451545 4901849 := bstep (se 2 (by rfl) ⟨1838193, by rfl⟩ : syracuseStep 4901849 = 3676387) B3676387
theorem B1453035 : Blo 1451545 1453035 := bstep (se 1 (by rfl) ⟨1089776, by rfl⟩ : syracuseStep 1453035 = 2179553) B2179553
theorem B1453047 : Blo 1451545 1453047 := bstep (se 1 (by rfl) ⟨1089785, by rfl⟩ : syracuseStep 1453047 = 2179571) B2179571
theorem B1453067 : Blo 1451545 1453067 := bstep (se 1 (by rfl) ⟨1089800, by rfl⟩ : syracuseStep 1453067 = 2179601) B2179601
theorem B1453079 : Blo 1451545 1453079 := bstep (se 1 (by rfl) ⟨1089809, by rfl⟩ : syracuseStep 1453079 = 2179619) B2179619
theorem B1453099 : Blo 1451545 1453099 := bstep (se 1 (by rfl) ⟨1089824, by rfl⟩ : syracuseStep 1453099 = 2179649) B2179649
theorem B1453111 : Blo 1451545 1453111 := bstep (se 1 (by rfl) ⟨1089833, by rfl⟩ : syracuseStep 1453111 = 2179667) B2179667
theorem B1453131 : Blo 1451545 1453131 := bstep (se 1 (by rfl) ⟨1089848, by rfl⟩ : syracuseStep 1453131 = 2179697) B2179697
theorem B1453143 : Blo 1451545 1453143 := bstep (se 1 (by rfl) ⟨1089857, by rfl⟩ : syracuseStep 1453143 = 2179715) B2179715
theorem B1633387 : Blo 1451545 1633387 := bstep (se 1 (by rfl) ⟨1225040, by rfl⟩ : syracuseStep 1633387 = 2450081) B2450081
theorem B1453163 : Blo 1451545 1453163 := bstep (se 1 (by rfl) ⟨1089872, by rfl⟩ : syracuseStep 1453163 = 2179745) B2179745
theorem B1453175 : Blo 1451545 1453175 := bstep (se 1 (by rfl) ⟨1089881, by rfl⟩ : syracuseStep 1453175 = 2179763) B2179763
theorem B15707267 : Blo 1451545 15707267 := bstep (se 1 (by rfl) ⟨11780450, by rfl⟩ : syracuseStep 15707267 = 23560901) B23560901
theorem B1453195 : Blo 1451545 1453195 := bstep (se 1 (by rfl) ⟨1089896, by rfl⟩ : syracuseStep 1453195 = 2179793) B2179793
theorem B2452619 : Blo 1451545 2452619 := bstep (se 1 (by rfl) ⟨1839464, by rfl⟩ : syracuseStep 2452619 = 3678929) B3678929
theorem B1453207 : Blo 1451545 1453207 := bstep (se 1 (by rfl) ⟨1089905, by rfl⟩ : syracuseStep 1453207 = 2179811) B2179811
theorem B1453227 : Blo 1451545 1453227 := bstep (se 1 (by rfl) ⟨1089920, by rfl⟩ : syracuseStep 1453227 = 2179841) B2179841
theorem B1453239 : Blo 1451545 1453239 := bstep (se 1 (by rfl) ⟨1089929, by rfl⟩ : syracuseStep 1453239 = 2179859) B2179859
theorem B1453259 : Blo 1451545 1453259 := bstep (se 1 (by rfl) ⟨1089944, by rfl⟩ : syracuseStep 1453259 = 2179889) B2179889
theorem B1633495 : Blo 1451545 1633495 := bstep (se 1 (by rfl) ⟨1225121, by rfl⟩ : syracuseStep 1633495 = 2450243) B2450243
theorem B1453271 : Blo 1451545 1453271 := bstep (se 1 (by rfl) ⟨1089953, by rfl⟩ : syracuseStep 1453271 = 2179907) B2179907
theorem B1453291 : Blo 1451545 1453291 := bstep (se 1 (by rfl) ⟨1089968, by rfl⟩ : syracuseStep 1453291 = 2179937) B2179937
theorem B1453303 : Blo 1451545 1453303 := bstep (se 1 (by rfl) ⟨1089977, by rfl⟩ : syracuseStep 1453303 = 2179955) B2179955
theorem B1453323 : Blo 1451545 1453323 := bstep (se 1 (by rfl) ⟨1089992, by rfl⟩ : syracuseStep 1453323 = 2179985) B2179985
theorem B2452747 : Blo 1451545 2452747 := bstep (se 1 (by rfl) ⟨1839560, by rfl⟩ : syracuseStep 2452747 = 3679121) B3679121
theorem B1453335 : Blo 1451545 1453335 := bstep (se 1 (by rfl) ⟨1090001, by rfl⟩ : syracuseStep 1453335 = 2180003) B2180003
theorem B1453355 : Blo 1451545 1453355 := bstep (se 1 (by rfl) ⟨1090016, by rfl⟩ : syracuseStep 1453355 = 2180033) B2180033
theorem B1453367 : Blo 1451545 1453367 := bstep (se 1 (by rfl) ⟨1090025, by rfl⟩ : syracuseStep 1453367 = 2180051) B2180051
theorem B2796865 : Blo 1451545 2796865 := bstep (se 2 (by rfl) ⟨1048824, by rfl⟩ : syracuseStep 2796865 = 2097649) B2097649
theorem B5303627 : Blo 1451545 5303627 := bstep (se 1 (by rfl) ⟨3977720, by rfl⟩ : syracuseStep 5303627 = 7955441) B7955441
theorem B1453387 : Blo 1451545 1453387 := bstep (se 1 (by rfl) ⟨1090040, by rfl⟩ : syracuseStep 1453387 = 2180081) B2180081
theorem B1453399 : Blo 1451545 1453399 := bstep (se 1 (by rfl) ⟨1090049, by rfl⟩ : syracuseStep 1453399 = 2180099) B2180099
theorem B7957853 : Blo 1451545 7957853 := bstep (se 3 (by rfl) ⟨1492097, by rfl⟩ : syracuseStep 7957853 = 2984195) B2984195
theorem B1453419 : Blo 1451545 1453419 := bstep (se 1 (by rfl) ⟨1090064, by rfl⟩ : syracuseStep 1453419 = 2180129) B2180129
theorem B1453431 : Blo 1451545 1453431 := bstep (se 1 (by rfl) ⟨1090073, by rfl⟩ : syracuseStep 1453431 = 2180147) B2180147
theorem B1633675 : Blo 1451545 1633675 := bstep (se 1 (by rfl) ⟨1225256, by rfl⟩ : syracuseStep 1633675 = 2450513) B2450513
theorem B1453451 : Blo 1451545 1453451 := bstep (se 1 (by rfl) ⟨1090088, by rfl⟩ : syracuseStep 1453451 = 2180177) B2180177
theorem B1453463 : Blo 1451545 1453463 := bstep (se 1 (by rfl) ⟨1090097, by rfl⟩ : syracuseStep 1453463 = 2180195) B2180195
theorem B1453483 : Blo 1451545 1453483 := bstep (se 1 (by rfl) ⟨1090112, by rfl⟩ : syracuseStep 1453483 = 2180225) B2180225
theorem B1453495 : Blo 1451545 1453495 := bstep (se 1 (by rfl) ⟨1090121, by rfl⟩ : syracuseStep 1453495 = 2180243) B2180243
theorem B1453515 : Blo 1451545 1453515 := bstep (se 1 (by rfl) ⟨1090136, by rfl⟩ : syracuseStep 1453515 = 2180273) B2180273
theorem B1453527 : Blo 1451545 1453527 := bstep (se 1 (by rfl) ⟨1090145, by rfl⟩ : syracuseStep 1453527 = 2180291) B2180291
theorem B1633783 : Blo 1451545 1633783 := bstep (se 1 (by rfl) ⟨1225337, by rfl⟩ : syracuseStep 1633783 = 2450675) B2450675
theorem B7351883 : Blo 1451545 7351883 := bstep (se 1 (by rfl) ⟨5513912, by rfl⟩ : syracuseStep 7351883 = 11027825) B11027825
theorem B4902551 : Blo 1451545 4902551 := bstep (se 1 (by rfl) ⟨3676913, by rfl⟩ : syracuseStep 4902551 = 7353827) B7353827
theorem B2616985 : Blo 1451545 2616985 := bstep (se 2 (by rfl) ⟨981369, by rfl⟩ : syracuseStep 2616985 = 1962739) B1962739
theorem B1633963 : Blo 1451545 1633963 := bstep (se 1 (by rfl) ⟨1225472, by rfl⟩ : syracuseStep 1633963 = 2450945) B2450945
theorem B6205187 : Blo 1451545 6205187 := bstep (se 1 (by rfl) ⟨4653890, by rfl⟩ : syracuseStep 6205187 = 9307781) B9307781
theorem B1634071 : Blo 1451545 1634071 := bstep (se 1 (by rfl) ⟨1225553, by rfl⟩ : syracuseStep 1634071 = 2451107) B2451107
theorem B2756531 : Blo 1451545 2756531 := bstep (se 1 (by rfl) ⟨2067398, by rfl⟩ : syracuseStep 2756531 = 4134797) B4134797
theorem B1634251 : Blo 1451545 1634251 := bstep (se 1 (by rfl) ⟨1225688, by rfl⟩ : syracuseStep 1634251 = 2451377) B2451377
theorem B8277977 : Blo 1451545 8277977 := bstep (se 2 (by rfl) ⟨3104241, by rfl⟩ : syracuseStep 8277977 = 6208483) B6208483
theorem B1839115 : Blo 1451545 1839115 := bstep (se 1 (by rfl) ⟨1379336, by rfl⟩ : syracuseStep 1839115 = 2758673) B2758673
theorem B1634359 : Blo 1451545 1634359 := bstep (se 1 (by rfl) ⟨1225769, by rfl⟩ : syracuseStep 1634359 = 2451539) B2451539
theorem B2756683 : Blo 1451545 2756683 := bstep (se 1 (by rfl) ⟨2067512, by rfl⟩ : syracuseStep 2756683 = 4135025) B4135025
theorem B4903091 : Blo 1451545 4903091 := bstep (se 1 (by rfl) ⟨3677318, by rfl⟩ : syracuseStep 4903091 = 7354637) B7354637
theorem B7852249 : Blo 1451545 7852249 := bstep (se 2 (by rfl) ⟨2944593, by rfl⟩ : syracuseStep 7852249 = 5889187) B5889187
theorem B2068697 : Blo 1451545 2068697 := bstep (se 2 (by rfl) ⟨775761, by rfl⟩ : syracuseStep 2068697 = 1551523) B1551523
theorem B1634539 : Blo 1451545 1634539 := bstep (se 1 (by rfl) ⟨1225904, by rfl⟩ : syracuseStep 1634539 = 2451809) B2451809
theorem B1962263 : Blo 1451545 1962263 := bstep (se 1 (by rfl) ⟨1471697, by rfl⟩ : syracuseStep 1962263 = 2943395) B2943395
theorem B3100979 : Blo 1451545 3100979 := bstep (se 1 (by rfl) ⟨2325734, by rfl⟩ : syracuseStep 3100979 = 4651469) B4651469
theorem B3674443 : Blo 1451545 3674443 := bstep (se 1 (by rfl) ⟨2755832, by rfl⟩ : syracuseStep 3674443 = 5511665) B5511665
theorem B1634647 : Blo 1451545 1634647 := bstep (se 1 (by rfl) ⟨1225985, by rfl⟩ : syracuseStep 1634647 = 2451971) B2451971
theorem B9933187 : Blo 1451545 9933187 := bstep (se 1 (by rfl) ⟨7449890, by rfl⟩ : syracuseStep 9933187 = 14899781) B14899781
theorem B2757017 : Blo 1451545 2757017 := bstep (se 2 (by rfl) ⟨1033881, by rfl⟩ : syracuseStep 2757017 = 2067763) B2067763
theorem B4903361 : Blo 1451545 4903361 := bstep (se 2 (by rfl) ⟨1838760, by rfl⟩ : syracuseStep 4903361 = 3677521) B3677521
theorem B3674585 : Blo 1451545 3674585 := bstep (se 2 (by rfl) ⟨1377969, by rfl⟩ : syracuseStep 3674585 = 2755939) B2755939
theorem B1634827 : Blo 1451545 1634827 := bstep (se 1 (by rfl) ⟨1226120, by rfl⟩ : syracuseStep 1634827 = 2452241) B2452241
theorem B10474049 : Blo 1451545 10474049 := bstep (se 2 (by rfl) ⟨3927768, by rfl⟩ : syracuseStep 10474049 = 7855537) B7855537
theorem B1634935 : Blo 1451545 1634935 := bstep (se 1 (by rfl) ⟨1226201, by rfl⟩ : syracuseStep 1634935 = 2452403) B2452403
theorem B1635115 : Blo 1451545 1635115 := bstep (se 1 (by rfl) ⟨1226336, by rfl⟩ : syracuseStep 1635115 = 2452673) B2452673
theorem B2069335 : Blo 1451545 2069335 := bstep (se 1 (by rfl) ⟨1552001, by rfl⟩ : syracuseStep 2069335 = 3104003) B3104003
theorem B1635223 : Blo 1451545 1635223 := bstep (se 1 (by rfl) ⟨1226417, by rfl⟩ : syracuseStep 1635223 = 2452835) B2452835
theorem B4903901 : Blo 1451545 4903901 := bstep (se 3 (by rfl) ⟨919481, by rfl⟩ : syracuseStep 4903901 = 1838963) B1838963
theorem B2757655 : Blo 1451545 2757655 := bstep (se 1 (by rfl) ⟨2068241, by rfl⟩ : syracuseStep 2757655 = 4136483) B4136483
theorem B9933899 : Blo 1451545 9933899 := bstep (se 1 (by rfl) ⟨7450424, by rfl⟩ : syracuseStep 9933899 = 14900849) B14900849
theorem B22369373 : Blo 1451545 22369373 := bstep (se 3 (by rfl) ⟨4194257, by rfl⟩ : syracuseStep 22369373 = 8388515) B8388515
theorem B10613911 : Blo 1451545 10613911 := bstep (se 1 (by rfl) ⟨7960433, by rfl⟩ : syracuseStep 10613911 = 15920867) B15920867
theorem B4134091 : Blo 1451545 4134091 := bstep (se 1 (by rfl) ⟨3100568, by rfl⟩ : syracuseStep 4134091 = 6201137) B6201137
theorem B3675415 : Blo 1451545 3675415 := bstep (se 1 (by rfl) ⟨2756561, by rfl⟩ : syracuseStep 3675415 = 5513123) B5513123
theorem B5518637 : Blo 1451545 5518637 := bstep (se 3 (by rfl) ⟨1034744, by rfl⟩ : syracuseStep 5518637 = 2069489) B2069489
theorem B7353665 : Blo 1451545 7353665 := bstep (se 2 (by rfl) ⟨2757624, by rfl⟩ : syracuseStep 7353665 = 5515249) B5515249
theorem B4650443 : Blo 1451545 4650443 := bstep (se 1 (by rfl) ⟨3487832, by rfl⟩ : syracuseStep 4650443 = 6975665) B6975665
theorem B3266009 : Blo 1451545 3266009 := bstep (se 2 (by rfl) ⟨1224753, by rfl⟩ : syracuseStep 3266009 = 2449507) B2449507
theorem B4134365 : Blo 1451545 4134365 := bstep (se 3 (by rfl) ⟨775193, by rfl⟩ : syracuseStep 4134365 = 1550387) B1550387
theorem B3102209 : Blo 1451545 3102209 := bstep (se 2 (by rfl) ⟨1163328, by rfl⟩ : syracuseStep 3102209 = 2326657) B2326657
theorem B3266099 : Blo 1451545 3266099 := bstep (se 1 (by rfl) ⟨2449574, by rfl⟩ : syracuseStep 3266099 = 4899149) B4899149
theorem B11023937 : Blo 1451545 11023937 := bstep (se 2 (by rfl) ⟨4133976, by rfl⟩ : syracuseStep 11023937 = 8267953) B8267953
theorem B3266135 : Blo 1451545 3266135 := bstep (se 1 (by rfl) ⟨2449601, by rfl⟩ : syracuseStep 3266135 = 4899203) B4899203
theorem B9557597 : Blo 1451545 9557597 := bstep (se 3 (by rfl) ⟨1792049, by rfl⟩ : syracuseStep 9557597 = 3584099) B3584099
theorem B11941507 : Blo 1451545 11941507 := bstep (se 1 (by rfl) ⟨8956130, by rfl⟩ : syracuseStep 11941507 = 17912261) B17912261
theorem B9942659 : Blo 1451545 9942659 := bstep (se 1 (by rfl) ⟨7456994, by rfl⟩ : syracuseStep 9942659 = 14913989) B14913989
theorem B5887667 : Blo 1451545 5887667 := bstep (se 1 (by rfl) ⟨4415750, by rfl⟩ : syracuseStep 5887667 = 8831501) B8831501
theorem B3675851 : Blo 1451545 3675851 := bstep (se 1 (by rfl) ⟨2756888, by rfl⟩ : syracuseStep 3675851 = 5513777) B5513777
theorem B3266315 : Blo 1451545 3266315 := bstep (se 1 (by rfl) ⟨2449736, by rfl⟩ : syracuseStep 3266315 = 4899473) B4899473
theorem B3266369 : Blo 1451545 3266369 := bstep (se 2 (by rfl) ⟨1224888, by rfl⟩ : syracuseStep 3266369 = 2449777) B2449777
theorem B2758475 : Blo 1451545 2758475 := bstep (se 1 (by rfl) ⟨2068856, by rfl⟩ : syracuseStep 2758475 = 4137713) B4137713
theorem B2758529 : Blo 1451545 2758529 := bstep (se 2 (by rfl) ⟨1034448, by rfl⟩ : syracuseStep 2758529 = 2068897) B2068897
theorem B2209675 : Blo 1451545 2209675 := bstep (se 1 (by rfl) ⟨1657256, by rfl⟩ : syracuseStep 2209675 = 3314513) B3314513
theorem B6207425 : Blo 1451545 6207425 := bstep (se 2 (by rfl) ⟨2327784, by rfl⟩ : syracuseStep 6207425 = 4655569) B4655569
theorem B1963993 : Blo 1451545 1963993 := bstep (se 2 (by rfl) ⟨736497, by rfl⟩ : syracuseStep 1963993 = 1472995) B1472995
theorem B3266585 : Blo 1451545 3266585 := bstep (se 2 (by rfl) ⟨1224969, by rfl⟩ : syracuseStep 3266585 = 2449939) B2449939
theorem B1964057 : Blo 1451545 1964057 := bstep (se 2 (by rfl) ⟨736521, by rfl⟩ : syracuseStep 1964057 = 1473043) B1473043
theorem B3676225 : Blo 1451545 3676225 := bstep (se 2 (by rfl) ⟨1378584, by rfl⟩ : syracuseStep 3676225 = 2757169) B2757169
theorem B7854155 : Blo 1451545 7854155 := bstep (se 1 (by rfl) ⟨5890616, by rfl⟩ : syracuseStep 7854155 = 11781233) B11781233
theorem B4905035 : Blo 1451545 4905035 := bstep (se 1 (by rfl) ⟨3678776, by rfl⟩ : syracuseStep 4905035 = 7357553) B7357553
theorem B3266675 : Blo 1451545 3266675 := bstep (se 1 (by rfl) ⟨2450006, by rfl⟩ : syracuseStep 3266675 = 4900013) B4900013
theorem B3266711 : Blo 1451545 3266711 := bstep (se 1 (by rfl) ⟨2450033, by rfl⟩ : syracuseStep 3266711 = 4900067) B4900067
theorem B5511347 : Blo 1451545 5511347 := bstep (se 1 (by rfl) ⟨4133510, by rfl⟩ : syracuseStep 5511347 = 8267021) B8267021
theorem B5511361 : Blo 1451545 5511361 := bstep (se 2 (by rfl) ⟨2066760, by rfl⟩ : syracuseStep 5511361 = 4133521) B4133521
theorem B8272145 : Blo 1451545 8272145 := bstep (se 2 (by rfl) ⟨3102054, by rfl⟩ : syracuseStep 8272145 = 6204109) B6204109
theorem B4651339 : Blo 1451545 4651339 := bstep (se 1 (by rfl) ⟨3488504, by rfl⟩ : syracuseStep 4651339 = 6977009) B6977009
theorem B3266891 : Blo 1451545 3266891 := bstep (se 1 (by rfl) ⟨2450168, by rfl⟩ : syracuseStep 3266891 = 4900337) B4900337
theorem B2177369 : Blo 1451545 2177369 := bstep (se 2 (by rfl) ⟨816513, by rfl⟩ : syracuseStep 2177369 = 1633027) B1633027
theorem B4905305 : Blo 1451545 4905305 := bstep (se 2 (by rfl) ⟨1839489, by rfl⟩ : syracuseStep 4905305 = 3678979) B3678979
theorem B11180389 : Blo 1451545 11180389 := bstep (se 4 (by rfl) ⟨1048161, by rfl⟩ : syracuseStep 11180389 = 2096323) B2096323
theorem B3266945 : Blo 1451545 3266945 := bstep (se 2 (by rfl) ⟨1225104, by rfl⟩ : syracuseStep 3266945 = 2450209) B2450209
theorem B13957555 : Blo 1451545 13957555 := bstep (se 1 (by rfl) ⟨10468166, by rfl⟩ : syracuseStep 13957555 = 20936333) B20936333
theorem B2177483 : Blo 1451545 2177483 := bstep (se 1 (by rfl) ⟨1633112, by rfl⟩ : syracuseStep 2177483 = 3266225) B3266225
theorem B2177495 : Blo 1451545 2177495 := bstep (se 1 (by rfl) ⟨1633121, by rfl⟩ : syracuseStep 2177495 = 3266243) B3266243
theorem B2177561 : Blo 1451545 2177561 := bstep (se 2 (by rfl) ⟨816585, by rfl⟩ : syracuseStep 2177561 = 1633171) B1633171
theorem B11778635 : Blo 1451545 11778635 := bstep (se 1 (by rfl) ⟨8833976, by rfl⟩ : syracuseStep 11778635 = 17667953) B17667953
theorem B1636951 : Blo 1451545 1636951 := bstep (se 1 (by rfl) ⟨1227713, by rfl⟩ : syracuseStep 1636951 = 2455427) B2455427
theorem B3103319 : Blo 1451545 3103319 := bstep (se 1 (by rfl) ⟨2327489, by rfl⟩ : syracuseStep 3103319 = 4654979) B4654979
theorem B3267161 : Blo 1451545 3267161 := bstep (se 2 (by rfl) ⟨1225185, by rfl⟩ : syracuseStep 3267161 = 2450371) B2450371
theorem B94231133 : Blo 1451545 94231133 := bstep (se 3 (by rfl) ⟨17668337, by rfl⟩ : syracuseStep 94231133 = 35336675) B35336675
theorem B10476125 : Blo 1451545 10476125 := bstep (se 3 (by rfl) ⟨1964273, by rfl⟩ : syracuseStep 10476125 = 3928547) B3928547
theorem B2177675 : Blo 1451545 2177675 := bstep (se 1 (by rfl) ⟨1633256, by rfl⟩ : syracuseStep 2177675 = 3266513) B3266513
theorem B2177687 : Blo 1451545 2177687 := bstep (se 1 (by rfl) ⟨1633265, by rfl⟩ : syracuseStep 2177687 = 3266531) B3266531
theorem B3676823 : Blo 1451545 3676823 := bstep (se 1 (by rfl) ⟨2757617, by rfl⟩ : syracuseStep 3676823 = 5515235) B5515235
theorem B3267251 : Blo 1451545 3267251 := bstep (se 1 (by rfl) ⟨2450438, by rfl⟩ : syracuseStep 3267251 = 4900877) B4900877
theorem B4479667 : Blo 1451545 4479667 := bstep (se 1 (by rfl) ⟨3359750, by rfl⟩ : syracuseStep 4479667 = 6719501) B6719501
theorem B3267287 : Blo 1451545 3267287 := bstep (se 1 (by rfl) ⟨2450465, by rfl⟩ : syracuseStep 3267287 = 4900931) B4900931
theorem B2177753 : Blo 1451545 2177753 := bstep (se 2 (by rfl) ⟨816657, by rfl⟩ : syracuseStep 2177753 = 1633315) B1633315
theorem B8272601 : Blo 1451545 8272601 := bstep (se 2 (by rfl) ⟨3102225, by rfl⟩ : syracuseStep 8272601 = 6204451) B6204451
theorem B8837849 : Blo 1451545 8837849 := bstep (se 2 (by rfl) ⟨3314193, by rfl⟩ : syracuseStep 8837849 = 6628387) B6628387
theorem B4479709 : Blo 1451545 4479709 := bstep (se 3 (by rfl) ⟨839945, by rfl⟩ : syracuseStep 4479709 = 1679891) B1679891
theorem B2759447 : Blo 1451545 2759447 := bstep (se 1 (by rfl) ⟨2069585, by rfl⟩ : syracuseStep 2759447 = 4139171) B4139171
theorem B7854893 : Blo 1451545 7854893 := bstep (se 3 (by rfl) ⟨1472792, by rfl⟩ : syracuseStep 7854893 = 2945585) B2945585
theorem B2177867 : Blo 1451545 2177867 := bstep (se 1 (by rfl) ⟨1633400, by rfl⟩ : syracuseStep 2177867 = 3266801) B3266801
theorem B2177879 : Blo 1451545 2177879 := bstep (se 1 (by rfl) ⟨1633409, by rfl⟩ : syracuseStep 2177879 = 3266819) B3266819
theorem B3267467 : Blo 1451545 3267467 := bstep (se 1 (by rfl) ⟨2450600, by rfl⟩ : syracuseStep 3267467 = 4901201) B4901201
theorem B2177945 : Blo 1451545 2177945 := bstep (se 2 (by rfl) ⟨816729, by rfl⟩ : syracuseStep 2177945 = 1633459) B1633459
theorem B4651955 : Blo 1451545 4651955 := bstep (se 1 (by rfl) ⟨3488966, by rfl⟩ : syracuseStep 4651955 = 6977933) B6977933
theorem B3267521 : Blo 1451545 3267521 := bstep (se 2 (by rfl) ⟨1225320, by rfl⟩ : syracuseStep 3267521 = 2450641) B2450641
theorem B2178059 : Blo 1451545 2178059 := bstep (se 1 (by rfl) ⟨1633544, by rfl⟩ : syracuseStep 2178059 = 3267089) B3267089
theorem B2178071 : Blo 1451545 2178071 := bstep (se 1 (by rfl) ⟨1633553, by rfl⟩ : syracuseStep 2178071 = 3267107) B3267107
theorem B4652083 : Blo 1451545 4652083 := bstep (se 1 (by rfl) ⟨3489062, by rfl⟩ : syracuseStep 4652083 = 6978125) B6978125
theorem B2178137 : Blo 1451545 2178137 := bstep (se 2 (by rfl) ⟨816801, by rfl⟩ : syracuseStep 2178137 = 1633603) B1633603
theorem B3267737 : Blo 1451545 3267737 := bstep (se 2 (by rfl) ⟨1225401, by rfl⟩ : syracuseStep 3267737 = 2450803) B2450803
theorem B2178251 : Blo 1451545 2178251 := bstep (se 1 (by rfl) ⟨1633688, by rfl⟩ : syracuseStep 2178251 = 3267377) B3267377
theorem B2178263 : Blo 1451545 2178263 := bstep (se 1 (by rfl) ⟨1633697, by rfl⟩ : syracuseStep 2178263 = 3267395) B3267395
theorem B2325721 : Blo 1451545 2325721 := bstep (se 2 (by rfl) ⟨872145, by rfl⟩ : syracuseStep 2325721 = 1744291) B1744291
theorem B7355609 : Blo 1451545 7355609 := bstep (se 2 (by rfl) ⟨2758353, by rfl⟩ : syracuseStep 7355609 = 5516707) B5516707
theorem B3267827 : Blo 1451545 3267827 := bstep (se 1 (by rfl) ⟨2450870, by rfl⟩ : syracuseStep 3267827 = 4901741) B4901741
theorem B13958405 : Blo 1451545 13958405 := bstep (se 4 (by rfl) ⟨1308600, by rfl⟩ : syracuseStep 13958405 = 2617201) B2617201
theorem B3267863 : Blo 1451545 3267863 := bstep (se 1 (by rfl) ⟨2450897, by rfl⟩ : syracuseStep 3267863 = 4901795) B4901795
theorem B2178329 : Blo 1451545 2178329 := bstep (se 2 (by rfl) ⟨816873, by rfl⟩ : syracuseStep 2178329 = 1633747) B1633747
theorem B2178443 : Blo 1451545 2178443 := bstep (se 1 (by rfl) ⟨1633832, by rfl⟩ : syracuseStep 2178443 = 3267665) B3267665
theorem B2178455 : Blo 1451545 2178455 := bstep (se 1 (by rfl) ⟨1633841, by rfl⟩ : syracuseStep 2178455 = 3267683) B3267683
theorem B3677633 : Blo 1451545 3677633 := bstep (se 2 (by rfl) ⟨1379112, by rfl⟩ : syracuseStep 3677633 = 2758225) B2758225
theorem B3268043 : Blo 1451545 3268043 := bstep (se 1 (by rfl) ⟨2451032, by rfl⟩ : syracuseStep 3268043 = 4902065) B4902065
theorem B11025881 : Blo 1451545 11025881 := bstep (se 2 (by rfl) ⟨4134705, by rfl⟩ : syracuseStep 11025881 = 8269411) B8269411
theorem B2178521 : Blo 1451545 2178521 := bstep (se 2 (by rfl) ⟨816945, by rfl⟩ : syracuseStep 2178521 = 1633891) B1633891
theorem B5234141 : Blo 1451545 5234141 := bstep (se 3 (by rfl) ⟨981401, by rfl⟩ : syracuseStep 5234141 = 1962803) B1962803
theorem B3268097 : Blo 1451545 3268097 := bstep (se 2 (by rfl) ⟨1225536, by rfl⟩ : syracuseStep 3268097 = 2451073) B2451073
theorem B2178635 : Blo 1451545 2178635 := bstep (se 1 (by rfl) ⟨1633976, by rfl⟩ : syracuseStep 2178635 = 3267953) B3267953
theorem B2178647 : Blo 1451545 2178647 := bstep (se 1 (by rfl) ⟨1633985, by rfl⟩ : syracuseStep 2178647 = 3267971) B3267971
theorem B3104345 : Blo 1451545 3104345 := bstep (se 2 (by rfl) ⟨1164129, by rfl⟩ : syracuseStep 3104345 = 2328259) B2328259
theorem B8494723 : Blo 1451545 8494723 := bstep (se 1 (by rfl) ⟨6371042, by rfl⟩ : syracuseStep 8494723 = 12742085) B12742085
theorem B2178713 : Blo 1451545 2178713 := bstep (se 2 (by rfl) ⟨817017, by rfl⟩ : syracuseStep 2178713 = 1634035) B1634035
theorem B6201035 : Blo 1451545 6201035 := bstep (se 1 (by rfl) ⟨4650776, by rfl⟩ : syracuseStep 6201035 = 9301553) B9301553
theorem B3268313 : Blo 1451545 3268313 := bstep (se 2 (by rfl) ⟨1225617, by rfl⟩ : syracuseStep 3268313 = 2451235) B2451235
theorem B4136665 : Blo 1451545 4136665 := bstep (se 2 (by rfl) ⟨1551249, by rfl⟩ : syracuseStep 4136665 = 3102499) B3102499
theorem B2178827 : Blo 1451545 2178827 := bstep (se 1 (by rfl) ⟨1634120, by rfl⟩ : syracuseStep 2178827 = 3268241) B3268241
theorem B6627089 : Blo 1451545 6627089 := bstep (se 2 (by rfl) ⟨2485158, by rfl⟩ : syracuseStep 6627089 = 4970317) B4970317
theorem B2178839 : Blo 1451545 2178839 := bstep (se 1 (by rfl) ⟨1634129, by rfl⟩ : syracuseStep 2178839 = 3268259) B3268259
theorem B3268403 : Blo 1451545 3268403 := bstep (se 1 (by rfl) ⟨2451302, by rfl⟩ : syracuseStep 3268403 = 4902605) B4902605
theorem B8494913 : Blo 1451545 8494913 := bstep (se 2 (by rfl) ⟨3185592, by rfl⟩ : syracuseStep 8494913 = 6371185) B6371185
theorem B3268439 : Blo 1451545 3268439 := bstep (se 1 (by rfl) ⟨2451329, by rfl⟩ : syracuseStep 3268439 = 4902659) B4902659
theorem B2178905 : Blo 1451545 2178905 := bstep (se 2 (by rfl) ⟨817089, by rfl⟩ : syracuseStep 2178905 = 1634179) B1634179
theorem B9945011 : Blo 1451545 9945011 := bstep (se 1 (by rfl) ⟨7458758, by rfl⟩ : syracuseStep 9945011 = 14917517) B14917517
theorem B2179019 : Blo 1451545 2179019 := bstep (se 1 (by rfl) ⟨1634264, by rfl⟩ : syracuseStep 2179019 = 3268529) B3268529
theorem B2179031 : Blo 1451545 2179031 := bstep (se 1 (by rfl) ⟨1634273, by rfl⟩ : syracuseStep 2179031 = 3268547) B3268547
theorem B3678169 : Blo 1451545 3678169 := bstep (se 2 (by rfl) ⟨1379313, by rfl⟩ : syracuseStep 3678169 = 2758627) B2758627
theorem B7356419 : Blo 1451545 7356419 := bstep (se 1 (by rfl) ⟨5517314, by rfl⟩ : syracuseStep 7356419 = 11034629) B11034629
theorem B2179079 : Blo 1451545 2179079 := bstep (se 1 (by rfl) ⟨1634309, by rfl⟩ : syracuseStep 2179079 = 3268619) B3268619
theorem B6979607 : Blo 1451545 6979607 := bstep (se 1 (by rfl) ⟨5234705, by rfl⟩ : syracuseStep 6979607 = 10469411) B10469411
theorem B2179115 : Blo 1451545 2179115 := bstep (se 1 (by rfl) ⟨1634336, by rfl⟩ : syracuseStep 2179115 = 3268673) B3268673
theorem B2179145 : Blo 1451545 2179145 := bstep (se 2 (by rfl) ⟨817179, by rfl⟩ : syracuseStep 2179145 = 1634359) B1634359
theorem B3268727 : Blo 1451545 3268727 := bstep (se 1 (by rfl) ⟨2451545, by rfl⟩ : syracuseStep 3268727 = 4903091) B4903091
theorem B2179259 : Blo 1451545 2179259 := bstep (se 1 (by rfl) ⟨1634444, by rfl⟩ : syracuseStep 2179259 = 3268889) B3268889
theorem B2179319 : Blo 1451545 2179319 := bstep (se 1 (by rfl) ⟨1634489, by rfl⟩ : syracuseStep 2179319 = 3268979) B3268979
theorem B7348481 : Blo 1451545 7348481 := bstep (se 2 (by rfl) ⟨2755680, by rfl⟩ : syracuseStep 7348481 = 5511361) B5511361
theorem B2179343 : Blo 1451545 2179343 := bstep (se 1 (by rfl) ⟨1634507, by rfl⟩ : syracuseStep 2179343 = 3269015) B3269015
theorem B10469665 : Blo 1451545 10469665 := bstep (se 2 (by rfl) ⟨3926124, by rfl⟩ : syracuseStep 10469665 = 7852249) B7852249
theorem B3268907 : Blo 1451545 3268907 := bstep (se 1 (by rfl) ⟨2451680, by rfl⟩ : syracuseStep 3268907 = 4903361) B4903361
theorem B2834731 : Blo 1451545 2834731 := bstep (se 1 (by rfl) ⟨2126048, by rfl⟩ : syracuseStep 2834731 = 4252097) B4252097
theorem B2179385 : Blo 1451545 2179385 := bstep (se 2 (by rfl) ⟨817269, by rfl⟩ : syracuseStep 2179385 = 1634539) B1634539
theorem B2449723 : Blo 1451545 2449723 := bstep (se 1 (by rfl) ⟨1837292, by rfl⟩ : syracuseStep 2449723 = 3674585) B3674585
theorem B2326843 : Blo 1451545 2326843 := bstep (se 1 (by rfl) ⟨1745132, by rfl⟩ : syracuseStep 2326843 = 3490265) B3490265
theorem B8274311 : Blo 1451545 8274311 := bstep (se 1 (by rfl) ⟨6205733, by rfl⟩ : syracuseStep 8274311 = 12411467) B12411467
theorem B2179463 : Blo 1451545 2179463 := bstep (se 1 (by rfl) ⟨1634597, by rfl⟩ : syracuseStep 2179463 = 3269195) B3269195
theorem B2359687 : Blo 1451545 2359687 := bstep (se 1 (by rfl) ⟨1769765, by rfl⟩ : syracuseStep 2359687 = 3539531) B3539531
theorem B2179499 : Blo 1451545 2179499 := bstep (se 1 (by rfl) ⟨1634624, by rfl⟩ : syracuseStep 2179499 = 3269249) B3269249
theorem B4899257 : Blo 1451545 4899257 := bstep (se 2 (by rfl) ⟨1837221, by rfl⟩ : syracuseStep 4899257 = 3674443) B3674443
theorem B6201785 : Blo 1451545 6201785 := bstep (se 2 (by rfl) ⟨2325669, by rfl⟩ : syracuseStep 6201785 = 4651339) B4651339
theorem B2449865 : Blo 1451545 2449865 := bstep (se 2 (by rfl) ⟨918699, by rfl⟩ : syracuseStep 2449865 = 1837399) B1837399
theorem B2179529 : Blo 1451545 2179529 := bstep (se 2 (by rfl) ⟨817323, by rfl⟩ : syracuseStep 2179529 = 1634647) B1634647
theorem B2179643 : Blo 1451545 2179643 := bstep (se 1 (by rfl) ⟨1634732, by rfl⟩ : syracuseStep 2179643 = 3269465) B3269465
theorem B29082179 : Blo 1451545 29082179 := bstep (se 1 (by rfl) ⟨21811634, by rfl⟩ : syracuseStep 29082179 = 43623269) B43623269
theorem B2179703 : Blo 1451545 2179703 := bstep (se 1 (by rfl) ⟨1634777, by rfl⟩ : syracuseStep 2179703 = 3269555) B3269555
theorem B2179727 : Blo 1451545 2179727 := bstep (se 1 (by rfl) ⟨1634795, by rfl⟩ : syracuseStep 2179727 = 3269591) B3269591
theorem B3269267 : Blo 1451545 3269267 := bstep (se 1 (by rfl) ⟨2451950, by rfl⟩ : syracuseStep 3269267 = 4903901) B4903901
theorem B2179769 : Blo 1451545 2179769 := bstep (se 2 (by rfl) ⟨817413, by rfl⟩ : syracuseStep 2179769 = 1634827) B1634827
theorem B3269321 : Blo 1451545 3269321 := bstep (se 2 (by rfl) ⟨1225995, by rfl⟩ : syracuseStep 3269321 = 2451991) B2451991
theorem B29819609 : Blo 1451545 29819609 := bstep (se 2 (by rfl) ⟨11182353, by rfl⟩ : syracuseStep 29819609 = 22364707) B22364707
theorem B2179847 : Blo 1451545 2179847 := bstep (se 1 (by rfl) ⟨1634885, by rfl⟩ : syracuseStep 2179847 = 3269771) B3269771
theorem B2179883 : Blo 1451545 2179883 := bstep (se 1 (by rfl) ⟨1634912, by rfl⟩ : syracuseStep 2179883 = 3269825) B3269825
theorem B3490619 : Blo 1451545 3490619 := bstep (se 1 (by rfl) ⟨2617964, by rfl⟩ : syracuseStep 3490619 = 5235929) B5235929
theorem B2179913 : Blo 1451545 2179913 := bstep (se 2 (by rfl) ⟨817467, by rfl⟩ : syracuseStep 2179913 = 1634935) B1634935
theorem B3679091 : Blo 1451545 3679091 := bstep (se 1 (by rfl) ⟨2759318, by rfl⟩ : syracuseStep 3679091 = 5518637) B5518637
theorem B2483129 : Blo 1451545 2483129 := bstep (se 2 (by rfl) ⟨931173, by rfl⟩ : syracuseStep 2483129 = 1862347) B1862347
theorem B5235641 : Blo 1451545 5235641 := bstep (se 2 (by rfl) ⟨1963365, by rfl⟩ : syracuseStep 5235641 = 3926731) B3926731
theorem B2180027 : Blo 1451545 2180027 := bstep (se 1 (by rfl) ⟨1635020, by rfl⟩ : syracuseStep 2180027 = 3270041) B3270041
theorem B5972945 : Blo 1451545 5972945 := bstep (se 2 (by rfl) ⟨2239854, by rfl⟩ : syracuseStep 5972945 = 4479709) B4479709
theorem B2180087 : Blo 1451545 2180087 := bstep (se 1 (by rfl) ⟨1635065, by rfl⟩ : syracuseStep 2180087 = 3270131) B3270131
theorem B4899851 : Blo 1451545 4899851 := bstep (se 1 (by rfl) ⟨3674888, by rfl⟩ : syracuseStep 4899851 = 7349777) B7349777
theorem B2180111 : Blo 1451545 2180111 := bstep (se 1 (by rfl) ⟨1635083, by rfl⟩ : syracuseStep 2180111 = 3270167) B3270167
theorem B7349291 : Blo 1451545 7349291 := bstep (se 1 (by rfl) ⟨5511968, by rfl⟩ : syracuseStep 7349291 = 11023937) B11023937
theorem B2180153 : Blo 1451545 2180153 := bstep (se 2 (by rfl) ⟨817557, by rfl⟩ : syracuseStep 2180153 = 1635115) B1635115
theorem B6628439 : Blo 1451545 6628439 := bstep (se 1 (by rfl) ⟨4971329, by rfl⟩ : syracuseStep 6628439 = 9942659) B9942659
theorem B4899959 : Blo 1451545 4899959 := bstep (se 1 (by rfl) ⟨3674969, by rfl⟩ : syracuseStep 4899959 = 7349939) B7349939
theorem B3925111 : Blo 1451545 3925111 := bstep (se 1 (by rfl) ⟨2943833, by rfl⟩ : syracuseStep 3925111 = 5887667) B5887667
theorem B4654199 : Blo 1451545 4654199 := bstep (se 1 (by rfl) ⟨3490649, by rfl⟩ : syracuseStep 4654199 = 6981299) B6981299
theorem B2450567 : Blo 1451545 2450567 := bstep (se 1 (by rfl) ⟨1837925, by rfl⟩ : syracuseStep 2450567 = 3675851) B3675851
theorem B2180231 : Blo 1451545 2180231 := bstep (se 1 (by rfl) ⟨1635173, by rfl⟩ : syracuseStep 2180231 = 3270347) B3270347
theorem B2180267 : Blo 1451545 2180267 := bstep (se 1 (by rfl) ⟨1635200, by rfl⟩ : syracuseStep 2180267 = 3270401) B3270401
theorem B2180297 : Blo 1451545 2180297 := bstep (se 2 (by rfl) ⟨817611, by rfl⟩ : syracuseStep 2180297 = 1635223) B1635223
theorem B4138283 : Blo 1451545 4138283 := bstep (se 1 (by rfl) ⟨3103712, by rfl⟩ : syracuseStep 4138283 = 6207425) B6207425
theorem B8504635 : Blo 1451545 8504635 := bstep (se 1 (by rfl) ⟨6378476, by rfl⟩ : syracuseStep 8504635 = 12756953) B12756953
theorem B5236103 : Blo 1451545 5236103 := bstep (se 1 (by rfl) ⟨3927077, by rfl⟩ : syracuseStep 5236103 = 7854155) B7854155
theorem B3270023 : Blo 1451545 3270023 := bstep (se 1 (by rfl) ⟨2452517, by rfl⟩ : syracuseStep 3270023 = 4905035) B4905035
theorem B6202777 : Blo 1451545 6202777 := bstep (se 2 (by rfl) ⟨2326041, by rfl⟩ : syracuseStep 6202777 = 4652083) B4652083
theorem B5514763 : Blo 1451545 5514763 := bstep (se 1 (by rfl) ⟨4136072, by rfl⟩ : syracuseStep 5514763 = 8272145) B8272145
theorem B31409693 : Blo 1451545 31409693 := bstep (se 3 (by rfl) ⟨5889317, by rfl⟩ : syracuseStep 31409693 = 11778635) B11778635
theorem B1451579 : Blo 1451545 1451579 := bstep (se 1 (by rfl) ⟨1088684, by rfl⟩ : syracuseStep 1451579 = 2177369) B2177369
theorem B8275517 : Blo 1451545 8275517 := bstep (se 3 (by rfl) ⟨1551659, by rfl⟩ : syracuseStep 8275517 = 3103319) B3103319
theorem B3270203 : Blo 1451545 3270203 := bstep (se 1 (by rfl) ⟨2452652, by rfl⟩ : syracuseStep 3270203 = 4905305) B4905305
theorem B7358039 : Blo 1451545 7358039 := bstep (se 1 (by rfl) ⟨5518529, by rfl⟩ : syracuseStep 7358039 = 11037059) B11037059
theorem B21235301 : Blo 1451545 21235301 := bstep (se 4 (by rfl) ⟨1990809, by rfl⟩ : syracuseStep 21235301 = 3981619) B3981619
theorem B1451655 : Blo 1451545 1451655 := bstep (se 1 (by rfl) ⟨1088741, by rfl⟩ : syracuseStep 1451655 = 2177483) B2177483
theorem B1451663 : Blo 1451545 1451663 := bstep (se 1 (by rfl) ⟨1088747, by rfl⟩ : syracuseStep 1451663 = 2177495) B2177495
theorem B3270329 : Blo 1451545 3270329 := bstep (se 2 (by rfl) ⟨1226373, by rfl⟩ : syracuseStep 3270329 = 2452747) B2452747
theorem B1451707 : Blo 1451545 1451707 := bstep (se 1 (by rfl) ⟨1088780, by rfl⟩ : syracuseStep 1451707 = 2177561) B2177561
theorem B4900553 : Blo 1451545 4900553 := bstep (se 2 (by rfl) ⟨1837707, by rfl⟩ : syracuseStep 4900553 = 3675415) B3675415
theorem B1451783 : Blo 1451545 1451783 := bstep (se 1 (by rfl) ⟨1088837, by rfl⟩ : syracuseStep 1451783 = 2177675) B2177675
theorem B1451791 : Blo 1451545 1451791 := bstep (se 1 (by rfl) ⟨1088843, by rfl⟩ : syracuseStep 1451791 = 2177687) B2177687
theorem B2451215 : Blo 1451545 2451215 := bstep (se 1 (by rfl) ⟨1838411, by rfl⟩ : syracuseStep 2451215 = 3676823) B3676823
theorem B1451835 : Blo 1451545 1451835 := bstep (se 1 (by rfl) ⟨1088876, by rfl⟩ : syracuseStep 1451835 = 2177753) B2177753
theorem B5515067 : Blo 1451545 5515067 := bstep (se 1 (by rfl) ⟨4136300, by rfl⟩ : syracuseStep 5515067 = 8272601) B8272601
theorem B5891899 : Blo 1451545 5891899 := bstep (se 1 (by rfl) ⟨4418924, by rfl⟩ : syracuseStep 5891899 = 8837849) B8837849
theorem B5236595 : Blo 1451545 5236595 := bstep (se 1 (by rfl) ⟨3927446, by rfl⟩ : syracuseStep 5236595 = 7854893) B7854893
theorem B1451911 : Blo 1451545 1451911 := bstep (se 1 (by rfl) ⟨1088933, by rfl⟩ : syracuseStep 1451911 = 2177867) B2177867
theorem B1451919 : Blo 1451545 1451919 := bstep (se 1 (by rfl) ⟨1088939, by rfl⟩ : syracuseStep 1451919 = 2177879) B2177879
theorem B1451963 : Blo 1451545 1451963 := bstep (se 1 (by rfl) ⟨1088972, by rfl⟩ : syracuseStep 1451963 = 2177945) B2177945
theorem B1452039 : Blo 1451545 1452039 := bstep (se 1 (by rfl) ⟨1089029, by rfl⟩ : syracuseStep 1452039 = 2178059) B2178059
theorem B1452047 : Blo 1451545 1452047 := bstep (se 1 (by rfl) ⟨1089035, by rfl⟩ : syracuseStep 1452047 = 2178071) B2178071
theorem B1452091 : Blo 1451545 1452091 := bstep (se 1 (by rfl) ⟨1089068, by rfl⟩ : syracuseStep 1452091 = 2178137) B2178137
theorem B14903357 : Blo 1451545 14903357 := bstep (se 3 (by rfl) ⟨2794379, by rfl⟩ : syracuseStep 14903357 = 5588759) B5588759
theorem B7358525 : Blo 1451545 7358525 := bstep (se 3 (by rfl) ⟨1379723, by rfl⟩ : syracuseStep 7358525 = 2759447) B2759447
theorem B10471511 : Blo 1451545 10471511 := bstep (se 1 (by rfl) ⟨7853633, by rfl⟩ : syracuseStep 10471511 = 15707267) B15707267
theorem B1452167 : Blo 1451545 1452167 := bstep (se 1 (by rfl) ⟨1089125, by rfl⟩ : syracuseStep 1452167 = 2178251) B2178251
theorem B1452175 : Blo 1451545 1452175 := bstep (se 1 (by rfl) ⟨1089131, by rfl⟩ : syracuseStep 1452175 = 2178263) B2178263
theorem B22653101 : Blo 1451545 22653101 := bstep (se 3 (by rfl) ⟨4247456, by rfl⟩ : syracuseStep 22653101 = 8494913) B8494913
theorem B1452219 : Blo 1451545 1452219 := bstep (se 1 (by rfl) ⟨1089164, by rfl⟩ : syracuseStep 1452219 = 2178329) B2178329
theorem B1452295 : Blo 1451545 1452295 := bstep (se 1 (by rfl) ⟨1089221, by rfl⟩ : syracuseStep 1452295 = 2178443) B2178443
theorem B1452303 : Blo 1451545 1452303 := bstep (se 1 (by rfl) ⟨1089227, by rfl⟩ : syracuseStep 1452303 = 2178455) B2178455
theorem B5515553 : Blo 1451545 5515553 := bstep (se 2 (by rfl) ⟨2068332, by rfl⟩ : syracuseStep 5515553 = 4136665) B4136665
theorem B2451755 : Blo 1451545 2451755 := bstep (se 1 (by rfl) ⟨1838816, by rfl⟩ : syracuseStep 2451755 = 3677633) B3677633
theorem B7350587 : Blo 1451545 7350587 := bstep (se 1 (by rfl) ⟨5512940, by rfl⟩ : syracuseStep 7350587 = 11025881) B11025881
theorem B1452347 : Blo 1451545 1452347 := bstep (se 1 (by rfl) ⟨1089260, by rfl⟩ : syracuseStep 1452347 = 2178521) B2178521
theorem B4901255 : Blo 1451545 4901255 := bstep (se 1 (by rfl) ⟨3675941, by rfl⟩ : syracuseStep 4901255 = 7351883) B7351883
theorem B1452423 : Blo 1451545 1452423 := bstep (se 1 (by rfl) ⟨1089317, by rfl⟩ : syracuseStep 1452423 = 2178635) B2178635
theorem B1452431 : Blo 1451545 1452431 := bstep (se 1 (by rfl) ⟨1089323, by rfl⟩ : syracuseStep 1452431 = 2178647) B2178647
theorem B1452475 : Blo 1451545 1452475 := bstep (se 1 (by rfl) ⟨1089356, by rfl⟩ : syracuseStep 1452475 = 2178713) B2178713
theorem B7350749 : Blo 1451545 7350749 := bstep (se 3 (by rfl) ⟨1378265, by rfl⟩ : syracuseStep 7350749 = 2756531) B2756531
theorem B1452551 : Blo 1451545 1452551 := bstep (se 1 (by rfl) ⟨1089413, by rfl⟩ : syracuseStep 1452551 = 2178827) B2178827
theorem B4418059 : Blo 1451545 4418059 := bstep (se 1 (by rfl) ⟨3313544, by rfl⟩ : syracuseStep 4418059 = 6627089) B6627089
theorem B1452559 : Blo 1451545 1452559 := bstep (se 1 (by rfl) ⟨1089419, by rfl⟩ : syracuseStep 1452559 = 2178839) B2178839
theorem B4655645 : Blo 1451545 4655645 := bstep (se 3 (by rfl) ⟨872933, by rfl⟩ : syracuseStep 4655645 = 1745867) B1745867
theorem B1452603 : Blo 1451545 1452603 := bstep (se 1 (by rfl) ⟨1089452, by rfl⟩ : syracuseStep 1452603 = 2178905) B2178905
theorem B6630007 : Blo 1451545 6630007 := bstep (se 1 (by rfl) ⟨4972505, by rfl⟩ : syracuseStep 6630007 = 9945011) B9945011
theorem B1452679 : Blo 1451545 1452679 := bstep (se 1 (by rfl) ⟨1089509, by rfl⟩ : syracuseStep 1452679 = 2179019) B2179019
theorem B1452687 : Blo 1451545 1452687 := bstep (se 1 (by rfl) ⟨1089515, by rfl⟩ : syracuseStep 1452687 = 2179031) B2179031
theorem B2452153 : Blo 1451545 2452153 := bstep (se 2 (by rfl) ⟨919557, by rfl⟩ : syracuseStep 2452153 = 1839115) B1839115
theorem B1452731 : Blo 1451545 1452731 := bstep (se 1 (by rfl) ⟨1089548, by rfl⟩ : syracuseStep 1452731 = 2179097) B2179097
theorem B28314305 : Blo 1451545 28314305 := bstep (se 2 (by rfl) ⟨10617864, by rfl⟩ : syracuseStep 28314305 = 21235729) B21235729
theorem B4901633 : Blo 1451545 4901633 := bstep (se 2 (by rfl) ⟨1838112, by rfl⟩ : syracuseStep 4901633 = 3676225) B3676225
theorem B1452807 : Blo 1451545 1452807 := bstep (se 1 (by rfl) ⟨1089605, by rfl⟩ : syracuseStep 1452807 = 2179211) B2179211
theorem B1452815 : Blo 1451545 1452815 := bstep (se 1 (by rfl) ⟨1089611, by rfl⟩ : syracuseStep 1452815 = 2179223) B2179223
theorem B11184911 : Blo 1451545 11184911 := bstep (se 1 (by rfl) ⟨8388683, by rfl⟩ : syracuseStep 11184911 = 16777367) B16777367
theorem B7351073 : Blo 1451545 7351073 := bstep (se 2 (by rfl) ⟨2756652, by rfl⟩ : syracuseStep 7351073 = 5513305) B5513305
theorem B17673011 : Blo 1451545 17673011 := bstep (se 1 (by rfl) ⟨13254758, by rfl⟩ : syracuseStep 17673011 = 26509517) B26509517
theorem B1452859 : Blo 1451545 1452859 := bstep (se 1 (by rfl) ⟨1089644, by rfl⟩ : syracuseStep 1452859 = 2179289) B2179289
theorem B2067319 : Blo 1451545 2067319 := bstep (se 1 (by rfl) ⟨1550489, by rfl⟩ : syracuseStep 2067319 = 3100979) B3100979
theorem B1452935 : Blo 1451545 1452935 := bstep (se 1 (by rfl) ⟨1089701, by rfl⟩ : syracuseStep 1452935 = 2179403) B2179403
theorem B1452943 : Blo 1451545 1452943 := bstep (se 1 (by rfl) ⟨1089707, by rfl⟩ : syracuseStep 1452943 = 2179415) B2179415
theorem B20949941 : Blo 1451545 20949941 := bstep (se 5 (by rfl) ⟨982028, by rfl⟩ : syracuseStep 20949941 = 1964057) B1964057
theorem B1452987 : Blo 1451545 1452987 := bstep (se 1 (by rfl) ⟨1089740, by rfl⟩ : syracuseStep 1452987 = 2179481) B2179481
theorem B1453063 : Blo 1451545 1453063 := bstep (se 1 (by rfl) ⟨1089797, by rfl⟩ : syracuseStep 1453063 = 2179595) B2179595
theorem B1453071 : Blo 1451545 1453071 := bstep (se 1 (by rfl) ⟨1089803, by rfl⟩ : syracuseStep 1453071 = 2179607) B2179607
theorem B150924323 : Blo 1451545 150924323 := bstep (se 1 (by rfl) ⟨113193242, by rfl⟩ : syracuseStep 150924323 = 226386485) B226386485
theorem B7957547 : Blo 1451545 7957547 := bstep (se 1 (by rfl) ⟨5968160, by rfl⟩ : syracuseStep 7957547 = 11936321) B11936321
theorem B6982699 : Blo 1451545 6982699 := bstep (se 1 (by rfl) ⟨5237024, by rfl⟩ : syracuseStep 6982699 = 10474049) B10474049
theorem B1453115 : Blo 1451545 1453115 := bstep (se 1 (by rfl) ⟨1089836, by rfl⟩ : syracuseStep 1453115 = 2179673) B2179673
theorem B1453191 : Blo 1451545 1453191 := bstep (se 1 (by rfl) ⟨1089893, by rfl⟩ : syracuseStep 1453191 = 2179787) B2179787
theorem B1633423 : Blo 1451545 1633423 := bstep (se 1 (by rfl) ⟨1225067, by rfl⟩ : syracuseStep 1633423 = 2450135) B2450135
theorem B1453199 : Blo 1451545 1453199 := bstep (se 1 (by rfl) ⟨1089899, by rfl⟩ : syracuseStep 1453199 = 2179799) B2179799
theorem B1453243 : Blo 1451545 1453243 := bstep (se 1 (by rfl) ⟨1089932, by rfl⟩ : syracuseStep 1453243 = 2179865) B2179865
theorem B5516525 : Blo 1451545 5516525 := bstep (se 3 (by rfl) ⟨1034348, by rfl⟩ : syracuseStep 5516525 = 2068697) B2068697
theorem B1453319 : Blo 1451545 1453319 := bstep (se 1 (by rfl) ⟨1089989, by rfl⟩ : syracuseStep 1453319 = 2179979) B2179979
theorem B1453327 : Blo 1451545 1453327 := bstep (se 1 (by rfl) ⟨1089995, by rfl⟩ : syracuseStep 1453327 = 2179991) B2179991
theorem B1453371 : Blo 1451545 1453371 := bstep (se 1 (by rfl) ⟨1090028, by rfl⟩ : syracuseStep 1453371 = 2180057) B2180057
theorem B27913571 : Blo 1451545 27913571 := bstep (se 1 (by rfl) ⟨20935178, by rfl⟩ : syracuseStep 27913571 = 41870357) B41870357
theorem B45305189 : Blo 1451545 45305189 := bstep (se 4 (by rfl) ⟨4247361, by rfl⟩ : syracuseStep 45305189 = 8494723) B8494723
theorem B63688037 : Blo 1451545 63688037 := bstep (se 4 (by rfl) ⟨5970753, by rfl⟩ : syracuseStep 63688037 = 11941507) B11941507
theorem B2452855 : Blo 1451545 2452855 := bstep (se 1 (by rfl) ⟨1839641, by rfl⟩ : syracuseStep 2452855 = 3679283) B3679283
theorem B1453447 : Blo 1451545 1453447 := bstep (se 1 (by rfl) ⟨1090085, by rfl⟩ : syracuseStep 1453447 = 2180171) B2180171
theorem B1453455 : Blo 1451545 1453455 := bstep (se 1 (by rfl) ⟨1090091, by rfl⟩ : syracuseStep 1453455 = 2180183) B2180183
theorem B14912915 : Blo 1451545 14912915 := bstep (se 1 (by rfl) ⟨11184686, by rfl⟩ : syracuseStep 14912915 = 22369373) B22369373
theorem B1453499 : Blo 1451545 1453499 := bstep (se 1 (by rfl) ⟨1090124, by rfl⟩ : syracuseStep 1453499 = 2180249) B2180249
theorem B2182601 : Blo 1451545 2182601 := bstep (se 2 (by rfl) ⟨818475, by rfl⟩ : syracuseStep 2182601 = 1636951) B1636951
theorem B3026377 : Blo 1451545 3026377 := bstep (se 2 (by rfl) ⟨1134891, by rfl⟩ : syracuseStep 3026377 = 2269783) B2269783
theorem B9309649 : Blo 1451545 9309649 := bstep (se 2 (by rfl) ⟨3491118, by rfl⟩ : syracuseStep 9309649 = 6982237) B6982237
theorem B4902443 : Blo 1451545 4902443 := bstep (se 1 (by rfl) ⟨3676832, by rfl⟩ : syracuseStep 4902443 = 7353665) B7353665
theorem B3100295 : Blo 1451545 3100295 := bstep (se 1 (by rfl) ⟨2325221, by rfl⟩ : syracuseStep 3100295 = 4650443) B4650443
theorem B1633927 : Blo 1451545 1633927 := bstep (se 1 (by rfl) ⟨1225445, by rfl⟩ : syracuseStep 1633927 = 2450891) B2450891
theorem B2756243 : Blo 1451545 2756243 := bstep (se 1 (by rfl) ⟨2067182, by rfl⟩ : syracuseStep 2756243 = 4134365) B4134365
theorem B2068139 : Blo 1451545 2068139 := bstep (se 1 (by rfl) ⟨1551104, by rfl⟩ : syracuseStep 2068139 = 3102209) B3102209
theorem B2756281 : Blo 1451545 2756281 := bstep (se 2 (by rfl) ⟨1033605, by rfl⟩ : syracuseStep 2756281 = 2067211) B2067211
theorem B7352045 : Blo 1451545 7352045 := bstep (se 3 (by rfl) ⟨1378508, by rfl⟩ : syracuseStep 7352045 = 2757017) B2757017
theorem B1634107 : Blo 1451545 1634107 := bstep (se 1 (by rfl) ⟨1225580, by rfl⟩ : syracuseStep 1634107 = 2451161) B2451161
theorem B1839019 : Blo 1451545 1839019 := bstep (se 1 (by rfl) ⟨1379264, by rfl⟩ : syracuseStep 1839019 = 2758529) B2758529
theorem B59666453 : Blo 1451545 59666453 := bstep (se 6 (by rfl) ⟨1398432, by rfl⟩ : syracuseStep 59666453 = 2796865) B2796865
theorem B4419643 : Blo 1451545 4419643 := bstep (se 1 (by rfl) ⟨3314732, by rfl⟩ : syracuseStep 4419643 = 6629465) B6629465
theorem B3674231 : Blo 1451545 3674231 := bstep (se 1 (by rfl) ⟨2755673, by rfl⟩ : syracuseStep 3674231 = 5511347) B5511347
theorem B14151881 : Blo 1451545 14151881 := bstep (se 2 (by rfl) ⟨5306955, by rfl⟩ : syracuseStep 14151881 = 10613911) B10613911
theorem B1634575 : Blo 1451545 1634575 := bstep (se 1 (by rfl) ⟨1225931, by rfl⟩ : syracuseStep 1634575 = 2451863) B2451863
theorem B3100961 : Blo 1451545 3100961 := bstep (se 2 (by rfl) ⟨1162860, by rfl⟩ : syracuseStep 3100961 = 2325721) B2325721
theorem B62820755 : Blo 1451545 62820755 := bstep (se 1 (by rfl) ⟨47115566, by rfl⟩ : syracuseStep 62820755 = 94231133) B94231133
theorem B6984083 : Blo 1451545 6984083 := bstep (se 1 (by rfl) ⟨5238062, by rfl⟩ : syracuseStep 6984083 = 10476125) B10476125
theorem B59609621 : Blo 1451545 59609621 := bstep (se 6 (by rfl) ⟨1397100, by rfl⟩ : syracuseStep 59609621 = 2794201) B2794201
theorem B7352855 : Blo 1451545 7352855 := bstep (se 1 (by rfl) ⟨5514641, by rfl⟩ : syracuseStep 7352855 = 11029283) B11029283
theorem B3101303 : Blo 1451545 3101303 := bstep (se 1 (by rfl) ⟨2325977, by rfl⟩ : syracuseStep 3101303 = 4651955) B4651955
theorem B1635079 : Blo 1451545 1635079 := bstep (se 1 (by rfl) ⟨1226309, by rfl⟩ : syracuseStep 1635079 = 2452619) B2452619
theorem B4903739 : Blo 1451545 4903739 := bstep (se 1 (by rfl) ⟨3677804, by rfl⟩ : syracuseStep 4903739 = 7355609) B7355609
theorem B4133693 : Blo 1451545 4133693 := bstep (se 3 (by rfl) ⟨775067, by rfl⟩ : syracuseStep 4133693 = 1550135) B1550135
theorem B3535751 : Blo 1451545 3535751 := bstep (se 1 (by rfl) ⟨2651813, by rfl⟩ : syracuseStep 3535751 = 5303627) B5303627
theorem B5305235 : Blo 1451545 5305235 := bstep (se 1 (by rfl) ⟨3978926, by rfl⟩ : syracuseStep 5305235 = 7957853) B7957853
theorem B2069563 : Blo 1451545 2069563 := bstep (se 1 (by rfl) ⟨1552172, by rfl⟩ : syracuseStep 2069563 = 3104345) B3104345
theorem B4134023 : Blo 1451545 4134023 := bstep (se 1 (by rfl) ⟨3100517, by rfl⟩ : syracuseStep 4134023 = 6201035) B6201035
theorem B2946233 : Blo 1451545 2946233 := bstep (se 2 (by rfl) ⟨1104837, by rfl⟩ : syracuseStep 2946233 = 2209675) B2209675
theorem B4904225 : Blo 1451545 4904225 := bstep (se 2 (by rfl) ⟨1839084, by rfl⟩ : syracuseStep 4904225 = 3678169) B3678169
theorem B2618657 : Blo 1451545 2618657 := bstep (se 2 (by rfl) ⟨981996, by rfl⟩ : syracuseStep 2618657 = 1963993) B1963993
theorem B5518651 : Blo 1451545 5518651 := bstep (se 1 (by rfl) ⟨4138988, by rfl⟩ : syracuseStep 5518651 = 8277977) B8277977
theorem B3675527 : Blo 1451545 3675527 := bstep (se 1 (by rfl) ⟨2756645, by rfl⟩ : syracuseStep 3675527 = 5513291) B5513291
theorem B3675577 : Blo 1451545 3675577 := bstep (se 2 (by rfl) ⟨1378341, by rfl⟩ : syracuseStep 3675577 = 2756683) B2756683
theorem B3266063 : Blo 1451545 3266063 := bstep (se 1 (by rfl) ⟨2449547, by rfl⟩ : syracuseStep 3266063 = 4899095) B4899095
theorem B26490397 : Blo 1451545 26490397 := bstep (se 3 (by rfl) ⟨4966949, by rfl⟩ : syracuseStep 26490397 = 9933899) B9933899
theorem B3266081 : Blo 1451545 3266081 := bstep (se 2 (by rfl) ⟨1224780, by rfl⟩ : syracuseStep 3266081 = 2449561) B2449561
theorem B2758187 : Blo 1451545 2758187 := bstep (se 1 (by rfl) ⟨2068640, by rfl⟩ : syracuseStep 2758187 = 4137281) B4137281
theorem B14907185 : Blo 1451545 14907185 := bstep (se 2 (by rfl) ⟨5590194, by rfl⟩ : syracuseStep 14907185 = 11180389) B11180389
theorem B13244249 : Blo 1451545 13244249 := bstep (se 2 (by rfl) ⟨4966593, by rfl⟩ : syracuseStep 13244249 = 9933187) B9933187
theorem B4904819 : Blo 1451545 4904819 := bstep (se 1 (by rfl) ⟨3678614, by rfl⟩ : syracuseStep 4904819 = 7357229) B7357229
theorem B3266423 : Blo 1451545 3266423 := bstep (se 1 (by rfl) ⟨2449817, by rfl⟩ : syracuseStep 3266423 = 4899635) B4899635
theorem B18610073 : Blo 1451545 18610073 := bstep (se 2 (by rfl) ⟨6978777, by rfl⟩ : syracuseStep 18610073 = 13957555) B13957555
theorem B3676175 : Blo 1451545 3676175 := bstep (se 1 (by rfl) ⟨2757131, by rfl⟩ : syracuseStep 3676175 = 5514263) B5514263
theorem B3266603 : Blo 1451545 3266603 := bstep (se 1 (by rfl) ⟨2449952, by rfl⟩ : syracuseStep 3266603 = 4899905) B4899905
theorem B5232701 : Blo 1451545 5232701 := bstep (se 3 (by rfl) ⟨981131, by rfl⟩ : syracuseStep 5232701 = 1962263) B1962263
theorem B23541961 : Blo 1451545 23541961 := bstep (se 2 (by rfl) ⟨8828235, by rfl⟩ : syracuseStep 23541961 = 17656471) B17656471
theorem B2177339 : Blo 1451545 2177339 := bstep (se 1 (by rfl) ⟨1633004, by rfl⟩ : syracuseStep 2177339 = 3266009) B3266009
theorem B5888315 : Blo 1451545 5888315 := bstep (se 1 (by rfl) ⟨4416236, by rfl⟩ : syracuseStep 5888315 = 8832473) B8832473
theorem B2177399 : Blo 1451545 2177399 := bstep (se 1 (by rfl) ⟨1633049, by rfl⟩ : syracuseStep 2177399 = 3266099) B3266099
theorem B2177423 : Blo 1451545 2177423 := bstep (se 1 (by rfl) ⟨1633067, by rfl⟩ : syracuseStep 2177423 = 3266135) B3266135
theorem B6371731 : Blo 1451545 6371731 := bstep (se 1 (by rfl) ⟨4778798, by rfl⟩ : syracuseStep 6371731 = 9557597) B9557597
theorem B3266963 : Blo 1451545 3266963 := bstep (se 1 (by rfl) ⟨2450222, by rfl⟩ : syracuseStep 3266963 = 4900445) B4900445
theorem B95566229 : Blo 1451545 95566229 := bstep (se 6 (by rfl) ⟨2239833, by rfl⟩ : syracuseStep 95566229 = 4479667) B4479667
theorem B2177465 : Blo 1451545 2177465 := bstep (se 2 (by rfl) ⟨816549, by rfl⟩ : syracuseStep 2177465 = 1633099) B1633099
theorem B3267017 : Blo 1451545 3267017 := bstep (se 2 (by rfl) ⟨1225131, by rfl⟩ : syracuseStep 3267017 = 2450263) B2450263
theorem B2759113 : Blo 1451545 2759113 := bstep (se 2 (by rfl) ⟨1034667, by rfl⟩ : syracuseStep 2759113 = 2069335) B2069335
theorem B2177543 : Blo 1451545 2177543 := bstep (se 1 (by rfl) ⟨1633157, by rfl⟩ : syracuseStep 2177543 = 3266315) B3266315
theorem B8952331 : Blo 1451545 8952331 := bstep (se 1 (by rfl) ⟨6714248, by rfl⟩ : syracuseStep 8952331 = 13428497) B13428497
theorem B2177579 : Blo 1451545 2177579 := bstep (se 1 (by rfl) ⟨1633184, by rfl⟩ : syracuseStep 2177579 = 3266369) B3266369
theorem B2177609 : Blo 1451545 2177609 := bstep (se 2 (by rfl) ⟨816603, by rfl⟩ : syracuseStep 2177609 = 1633207) B1633207
theorem B2177723 : Blo 1451545 2177723 := bstep (se 1 (by rfl) ⟨1633292, by rfl⟩ : syracuseStep 2177723 = 3266585) B3266585
theorem B3676873 : Blo 1451545 3676873 := bstep (se 2 (by rfl) ⟨1378827, by rfl⟩ : syracuseStep 3676873 = 2757655) B2757655
theorem B2177783 : Blo 1451545 2177783 := bstep (se 1 (by rfl) ⟨1633337, by rfl⟩ : syracuseStep 2177783 = 3266675) B3266675
theorem B2177807 : Blo 1451545 2177807 := bstep (se 1 (by rfl) ⟨1633355, by rfl⟩ : syracuseStep 2177807 = 3266711) B3266711
theorem B2177849 : Blo 1451545 2177849 := bstep (se 2 (by rfl) ⟨816693, by rfl⟩ : syracuseStep 2177849 = 1633387) B1633387
theorem B3677015 : Blo 1451545 3677015 := bstep (se 1 (by rfl) ⟨2757761, by rfl⟩ : syracuseStep 3677015 = 5515523) B5515523
theorem B4135799 : Blo 1451545 4135799 := bstep (se 1 (by rfl) ⟨3101849, by rfl⟩ : syracuseStep 4135799 = 6203699) B6203699
theorem B2177927 : Blo 1451545 2177927 := bstep (se 1 (by rfl) ⟨1633445, by rfl⟩ : syracuseStep 2177927 = 3266891) B3266891
theorem B2177963 : Blo 1451545 2177963 := bstep (se 1 (by rfl) ⟨1633472, by rfl⟩ : syracuseStep 2177963 = 3266945) B3266945
theorem B5512121 : Blo 1451545 5512121 := bstep (se 2 (by rfl) ⟨2067045, by rfl⟩ : syracuseStep 5512121 = 4134091) B4134091
theorem B2177993 : Blo 1451545 2177993 := bstep (se 2 (by rfl) ⟨816747, by rfl⟩ : syracuseStep 2177993 = 1633495) B1633495
theorem B2178107 : Blo 1451545 2178107 := bstep (se 1 (by rfl) ⟨1633580, by rfl⟩ : syracuseStep 2178107 = 3267161) B3267161
theorem B2178167 : Blo 1451545 2178167 := bstep (se 1 (by rfl) ⟨1633625, by rfl⟩ : syracuseStep 2178167 = 3267251) B3267251
theorem B3267719 : Blo 1451545 3267719 := bstep (se 1 (by rfl) ⟨2450789, by rfl⟩ : syracuseStep 3267719 = 4901579) B4901579
theorem B2178191 : Blo 1451545 2178191 := bstep (se 1 (by rfl) ⟨1633643, by rfl⟩ : syracuseStep 2178191 = 3267287) B3267287
theorem B2178233 : Blo 1451545 2178233 := bstep (se 2 (by rfl) ⟨816837, by rfl⟩ : syracuseStep 2178233 = 1633675) B1633675
theorem B2178311 : Blo 1451545 2178311 := bstep (se 1 (by rfl) ⟨1633733, by rfl⟩ : syracuseStep 2178311 = 3267467) B3267467
theorem B3980573 : Blo 1451545 3980573 := bstep (se 3 (by rfl) ⟨746357, by rfl⟩ : syracuseStep 3980573 = 1492715) B1492715
theorem B2178347 : Blo 1451545 2178347 := bstep (se 1 (by rfl) ⟨1633760, by rfl⟩ : syracuseStep 2178347 = 3267521) B3267521
theorem B3267899 : Blo 1451545 3267899 := bstep (se 1 (by rfl) ⟨2450924, by rfl⟩ : syracuseStep 3267899 = 4901849) B4901849
theorem B2178377 : Blo 1451545 2178377 := bstep (se 2 (by rfl) ⟨816891, by rfl⟩ : syracuseStep 2178377 = 1633783) B1633783
theorem B3268025 : Blo 1451545 3268025 := bstep (se 2 (by rfl) ⟨1225509, by rfl⟩ : syracuseStep 3268025 = 2451019) B2451019
theorem B2178491 : Blo 1451545 2178491 := bstep (se 1 (by rfl) ⟨1633868, by rfl⟩ : syracuseStep 2178491 = 3267737) B3267737
theorem B5234129 : Blo 1451545 5234129 := bstep (se 2 (by rfl) ⟨1962798, by rfl⟩ : syracuseStep 5234129 = 3925597) B3925597
theorem B2178551 : Blo 1451545 2178551 := bstep (se 1 (by rfl) ⟨1633913, by rfl⟩ : syracuseStep 2178551 = 3267827) B3267827
theorem B9305603 : Blo 1451545 9305603 := bstep (se 1 (by rfl) ⟨6979202, by rfl⟩ : syracuseStep 9305603 = 13958405) B13958405
theorem B2178575 : Blo 1451545 2178575 := bstep (se 1 (by rfl) ⟨1633931, by rfl⟩ : syracuseStep 2178575 = 3267863) B3267863
theorem B7355933 : Blo 1451545 7355933 := bstep (se 3 (by rfl) ⟨1379237, by rfl⟩ : syracuseStep 7355933 = 2758475) B2758475
theorem B3489313 : Blo 1451545 3489313 := bstep (se 2 (by rfl) ⟨1308492, by rfl⟩ : syracuseStep 3489313 = 2616985) B2616985
theorem B2178617 : Blo 1451545 2178617 := bstep (se 2 (by rfl) ⟨816981, by rfl⟩ : syracuseStep 2178617 = 1633963) B1633963
theorem B2178695 : Blo 1451545 2178695 := bstep (se 1 (by rfl) ⟨1634021, by rfl⟩ : syracuseStep 2178695 = 3268043) B3268043
theorem B3489427 : Blo 1451545 3489427 := bstep (se 1 (by rfl) ⟨2617070, by rfl⟩ : syracuseStep 3489427 = 5234141) B5234141
theorem B2178731 : Blo 1451545 2178731 := bstep (se 1 (by rfl) ⟨1634048, by rfl⟩ : syracuseStep 2178731 = 3268097) B3268097
theorem B2178761 : Blo 1451545 2178761 := bstep (se 2 (by rfl) ⟨817035, by rfl⟩ : syracuseStep 2178761 = 1634071) B1634071
theorem B3268367 : Blo 1451545 3268367 := bstep (se 1 (by rfl) ⟨2451275, by rfl⟩ : syracuseStep 3268367 = 4902551) B4902551
theorem B3268385 : Blo 1451545 3268385 := bstep (se 2 (by rfl) ⟨1225644, by rfl⟩ : syracuseStep 3268385 = 2451289) B2451289
theorem B2178875 : Blo 1451545 2178875 := bstep (se 1 (by rfl) ⟨1634156, by rfl⟩ : syracuseStep 2178875 = 3268313) B3268313
theorem B4136791 : Blo 1451545 4136791 := bstep (se 1 (by rfl) ⟨3102593, by rfl⟩ : syracuseStep 4136791 = 6205187) B6205187
theorem B2178935 : Blo 1451545 2178935 := bstep (se 1 (by rfl) ⟨1634201, by rfl⟩ : syracuseStep 2178935 = 3268403) B3268403
theorem B2178959 : Blo 1451545 2178959 := bstep (se 1 (by rfl) ⟨1634219, by rfl⟩ : syracuseStep 2178959 = 3268439) B3268439
theorem B2179001 : Blo 1451545 2179001 := bstep (se 2 (by rfl) ⟨817125, by rfl⟩ : syracuseStep 2179001 = 1634251) B1634251
theorem B4653071 : Blo 1451545 4653071 := bstep (se 1 (by rfl) ⟨3489803, by rfl⟩ : syracuseStep 4653071 = 6979607) B6979607
theorem B2449487 : Blo 1451545 2449487 := bstep (se 1 (by rfl) ⟨1837115, by rfl⟩ : syracuseStep 2449487 = 3674231) B3674231
theorem B2179151 : Blo 1451545 2179151 := bstep (se 1 (by rfl) ⟨1634363, by rfl⟩ : syracuseStep 2179151 = 3268727) B3268727
theorem B4898987 : Blo 1451545 4898987 := bstep (se 1 (by rfl) ⟨3674240, by rfl⟩ : syracuseStep 4898987 = 7348481) B7348481
theorem B2179271 : Blo 1451545 2179271 := bstep (se 1 (by rfl) ⟨1634453, by rfl⟩ : syracuseStep 2179271 = 3268907) B3268907
theorem B39739747 : Blo 1451545 39739747 := bstep (se 1 (by rfl) ⟨29804810, by rfl⟩ : syracuseStep 39739747 = 59609621) B59609621
theorem B2179433 : Blo 1451545 2179433 := bstep (se 2 (by rfl) ⟨817287, by rfl⟩ : syracuseStep 2179433 = 1634575) B1634575
theorem B13959553 : Blo 1451545 13959553 := bstep (se 2 (by rfl) ⟨5234832, by rfl⟩ : syracuseStep 13959553 = 10469665) B10469665
theorem B2179511 : Blo 1451545 2179511 := bstep (se 1 (by rfl) ⟨1634633, by rfl⟩ : syracuseStep 2179511 = 3269267) B3269267
theorem B2179547 : Blo 1451545 2179547 := bstep (se 1 (by rfl) ⟨1634660, by rfl⟩ : syracuseStep 2179547 = 3269321) B3269321
theorem B7856621 : Blo 1451545 7856621 := bstep (se 3 (by rfl) ⟨1473116, by rfl⟩ : syracuseStep 7856621 = 2946233) B2946233
theorem B3146249 : Blo 1451545 3146249 := bstep (se 2 (by rfl) ⟨1179843, by rfl⟩ : syracuseStep 3146249 = 2359687) B2359687
theorem B8495641 : Blo 1451545 8495641 := bstep (se 2 (by rfl) ⟨3185865, by rfl⟩ : syracuseStep 8495641 = 6371731) B6371731
theorem B3269159 : Blo 1451545 3269159 := bstep (se 1 (by rfl) ⟨2451869, by rfl⟩ : syracuseStep 3269159 = 4903739) B4903739
theorem B3678817 : Blo 1451545 3678817 := bstep (se 2 (by rfl) ⟨1379556, by rfl⟩ : syracuseStep 3678817 = 2759113) B2759113
theorem B1655419 : Blo 1451545 1655419 := bstep (se 1 (by rfl) ⟨1241564, by rfl⟩ : syracuseStep 1655419 = 2483129) B2483129
theorem B3490427 : Blo 1451545 3490427 := bstep (se 1 (by rfl) ⟨2617820, by rfl⟩ : syracuseStep 3490427 = 5235641) B5235641
theorem B11936441 : Blo 1451545 11936441 := bstep (se 2 (by rfl) ⟨4476165, by rfl⟩ : syracuseStep 11936441 = 8952331) B8952331
theorem B5890745 : Blo 1451545 5890745 := bstep (se 2 (by rfl) ⟨2209029, by rfl⟩ : syracuseStep 5890745 = 4418059) B4418059
theorem B4899527 : Blo 1451545 4899527 := bstep (se 1 (by rfl) ⟨3674645, by rfl⟩ : syracuseStep 4899527 = 7349291) B7349291
theorem B8840009 : Blo 1451545 8840009 := bstep (se 2 (by rfl) ⟨3315003, by rfl⟩ : syracuseStep 8840009 = 6630007) B6630007
theorem B3269483 : Blo 1451545 3269483 := bstep (se 1 (by rfl) ⟨2452112, by rfl⟩ : syracuseStep 3269483 = 4904225) B4904225
theorem B1745771 : Blo 1451545 1745771 := bstep (se 1 (by rfl) ⟨1309328, by rfl⟩ : syracuseStep 1745771 = 2618657) B2618657
theorem B3269537 : Blo 1451545 3269537 := bstep (se 2 (by rfl) ⟨1226076, by rfl⟩ : syracuseStep 3269537 = 2452153) B2452153
theorem B2450351 : Blo 1451545 2450351 := bstep (se 1 (by rfl) ⟨1837763, by rfl⟩ : syracuseStep 2450351 = 3675527) B3675527
theorem B3490735 : Blo 1451545 3490735 := bstep (se 1 (by rfl) ⟨2618051, by rfl⟩ : syracuseStep 3490735 = 5236103) B5236103
theorem B2180015 : Blo 1451545 2180015 := bstep (se 1 (by rfl) ⟨1635011, by rfl⟩ : syracuseStep 2180015 = 3270023) B3270023
theorem B2180105 : Blo 1451545 2180105 := bstep (se 2 (by rfl) ⟨817539, by rfl⟩ : syracuseStep 2180105 = 1635079) B1635079
theorem B20939795 : Blo 1451545 20939795 := bstep (se 1 (by rfl) ⟨15704846, by rfl⟩ : syracuseStep 20939795 = 31409693) B31409693
theorem B2180135 : Blo 1451545 2180135 := bstep (se 1 (by rfl) ⟨1635101, by rfl⟩ : syracuseStep 2180135 = 3270203) B3270203
theorem B14156867 : Blo 1451545 14156867 := bstep (se 1 (by rfl) ⟨10617650, by rfl⟩ : syracuseStep 14156867 = 21235301) B21235301
theorem B2180219 : Blo 1451545 2180219 := bstep (se 1 (by rfl) ⟨1635164, by rfl⟩ : syracuseStep 2180219 = 3270329) B3270329
theorem B9938123 : Blo 1451545 9938123 := bstep (se 1 (by rfl) ⟨7453592, by rfl⟩ : syracuseStep 9938123 = 14907185) B14907185
theorem B3491063 : Blo 1451545 3491063 := bstep (se 1 (by rfl) ⟨2618297, by rfl⟩ : syracuseStep 3491063 = 5236595) B5236595
theorem B3269879 : Blo 1451545 3269879 := bstep (se 1 (by rfl) ⟨2452409, by rfl⟩ : syracuseStep 3269879 = 4904819) B4904819
theorem B2450783 : Blo 1451545 2450783 := bstep (se 1 (by rfl) ⟨1838087, by rfl⟩ : syracuseStep 2450783 = 3676175) B3676175
theorem B6981007 : Blo 1451545 6981007 := bstep (se 1 (by rfl) ⟨5235755, by rfl⟩ : syracuseStep 6981007 = 10471511) B10471511
theorem B1451559 : Blo 1451545 1451559 := bstep (se 1 (by rfl) ⟨1088669, by rfl⟩ : syracuseStep 1451559 = 2177339) B2177339
theorem B4900391 : Blo 1451545 4900391 := bstep (se 1 (by rfl) ⟨3675293, by rfl⟩ : syracuseStep 4900391 = 7350587) B7350587
theorem B3925543 : Blo 1451545 3925543 := bstep (se 1 (by rfl) ⟨2944157, by rfl⟩ : syracuseStep 3925543 = 5888315) B5888315
theorem B1451599 : Blo 1451545 1451599 := bstep (se 1 (by rfl) ⟨1088699, by rfl⟩ : syracuseStep 1451599 = 2177399) B2177399
theorem B1451615 : Blo 1451545 1451615 := bstep (se 1 (by rfl) ⟨1088711, by rfl⟩ : syracuseStep 1451615 = 2177423) B2177423
theorem B63710819 : Blo 1451545 63710819 := bstep (se 1 (by rfl) ⟨47783114, by rfl⟩ : syracuseStep 63710819 = 95566229) B95566229
theorem B1451643 : Blo 1451545 1451643 := bstep (se 1 (by rfl) ⟨1088732, by rfl⟩ : syracuseStep 1451643 = 2177465) B2177465
theorem B4900499 : Blo 1451545 4900499 := bstep (se 1 (by rfl) ⟨3675374, by rfl⟩ : syracuseStep 4900499 = 7350749) B7350749
theorem B1451695 : Blo 1451545 1451695 := bstep (se 1 (by rfl) ⟨1088771, by rfl⟩ : syracuseStep 1451695 = 2177543) B2177543
theorem B8267453 : Blo 1451545 8267453 := bstep (se 3 (by rfl) ⟨1550147, by rfl⟩ : syracuseStep 8267453 = 3100295) B3100295
theorem B1451719 : Blo 1451545 1451719 := bstep (se 1 (by rfl) ⟨1088789, by rfl⟩ : syracuseStep 1451719 = 2177579) B2177579
theorem B1451739 : Blo 1451545 1451739 := bstep (se 1 (by rfl) ⟨1088804, by rfl⟩ : syracuseStep 1451739 = 2177609) B2177609
theorem B11339513 : Blo 1451545 11339513 := bstep (se 2 (by rfl) ⟨4252317, by rfl⟩ : syracuseStep 11339513 = 8504635) B8504635
theorem B7358201 : Blo 1451545 7358201 := bstep (se 2 (by rfl) ⟨2759325, by rfl⟩ : syracuseStep 7358201 = 5518651) B5518651
theorem B5515037 : Blo 1451545 5515037 := bstep (se 3 (by rfl) ⟨1034069, by rfl⟩ : syracuseStep 5515037 = 2068139) B2068139
theorem B1451815 : Blo 1451545 1451815 := bstep (se 1 (by rfl) ⟨1088861, by rfl⟩ : syracuseStep 1451815 = 2177723) B2177723
theorem B18876203 : Blo 1451545 18876203 := bstep (se 1 (by rfl) ⟨14157152, by rfl⟩ : syracuseStep 18876203 = 28314305) B28314305
theorem B3270473 : Blo 1451545 3270473 := bstep (se 2 (by rfl) ⟨1226427, by rfl⟩ : syracuseStep 3270473 = 2452855) B2452855
theorem B1451855 : Blo 1451545 1451855 := bstep (se 1 (by rfl) ⟨1088891, by rfl⟩ : syracuseStep 1451855 = 2177783) B2177783
theorem B1451871 : Blo 1451545 1451871 := bstep (se 1 (by rfl) ⟨1088903, by rfl⟩ : syracuseStep 1451871 = 2177807) B2177807
theorem B7456607 : Blo 1451545 7456607 := bstep (se 1 (by rfl) ⟨5592455, by rfl⟩ : syracuseStep 7456607 = 11184911) B11184911
theorem B4900715 : Blo 1451545 4900715 := bstep (se 1 (by rfl) ⟨3675536, by rfl⟩ : syracuseStep 4900715 = 7351073) B7351073
theorem B11782007 : Blo 1451545 11782007 := bstep (se 1 (by rfl) ⟨8836505, by rfl⟩ : syracuseStep 11782007 = 17673011) B17673011
theorem B1451899 : Blo 1451545 1451899 := bstep (se 1 (by rfl) ⟨1088924, by rfl⟩ : syracuseStep 1451899 = 2177849) B2177849
theorem B2451343 : Blo 1451545 2451343 := bstep (se 1 (by rfl) ⟨1838507, by rfl⟩ : syracuseStep 2451343 = 3677015) B3677015
theorem B4900769 : Blo 1451545 4900769 := bstep (se 2 (by rfl) ⟨1837788, by rfl⟩ : syracuseStep 4900769 = 3675577) B3675577
theorem B1451951 : Blo 1451545 1451951 := bstep (se 1 (by rfl) ⟨1088963, by rfl⟩ : syracuseStep 1451951 = 2177927) B2177927
theorem B12412865 : Blo 1451545 12412865 := bstep (se 2 (by rfl) ⟨4654824, by rfl⟩ : syracuseStep 12412865 = 9309649) B9309649
theorem B1451975 : Blo 1451545 1451975 := bstep (se 1 (by rfl) ⟨1088981, by rfl⟩ : syracuseStep 1451975 = 2177963) B2177963
theorem B1451995 : Blo 1451545 1451995 := bstep (se 1 (by rfl) ⟨1088996, by rfl⟩ : syracuseStep 1451995 = 2177993) B2177993
theorem B100616215 : Blo 1451545 100616215 := bstep (se 1 (by rfl) ⟨75462161, by rfl⟩ : syracuseStep 100616215 = 150924323) B150924323
theorem B1452071 : Blo 1451545 1452071 := bstep (se 1 (by rfl) ⟨1089053, by rfl⟩ : syracuseStep 1452071 = 2178107) B2178107
theorem B1452111 : Blo 1451545 1452111 := bstep (se 1 (by rfl) ⟨1089083, by rfl⟩ : syracuseStep 1452111 = 2178167) B2178167
theorem B1452127 : Blo 1451545 1452127 := bstep (se 1 (by rfl) ⟨1089095, by rfl⟩ : syracuseStep 1452127 = 2178191) B2178191
theorem B1452155 : Blo 1451545 1452155 := bstep (se 1 (by rfl) ⟨1089116, by rfl⟩ : syracuseStep 1452155 = 2178233) B2178233
theorem B9308317 : Blo 1451545 9308317 := bstep (se 3 (by rfl) ⟨1745309, by rfl⟩ : syracuseStep 9308317 = 3490619) B3490619
theorem B1452207 : Blo 1451545 1452207 := bstep (se 1 (by rfl) ⟨1089155, by rfl⟩ : syracuseStep 1452207 = 2178311) B2178311
theorem B1452231 : Blo 1451545 1452231 := bstep (se 1 (by rfl) ⟨1089173, by rfl⟩ : syracuseStep 1452231 = 2178347) B2178347
theorem B1452251 : Blo 1451545 1452251 := bstep (se 1 (by rfl) ⟨1089188, by rfl⟩ : syracuseStep 1452251 = 2178377) B2178377
theorem B1452327 : Blo 1451545 1452327 := bstep (se 1 (by rfl) ⟨1089245, by rfl⟩ : syracuseStep 1452327 = 2178491) B2178491
theorem B11028797 : Blo 1451545 11028797 := bstep (se 3 (by rfl) ⟨2067899, by rfl⟩ : syracuseStep 11028797 = 4135799) B4135799
theorem B1452367 : Blo 1451545 1452367 := bstep (se 1 (by rfl) ⟨1089275, by rfl⟩ : syracuseStep 1452367 = 2178551) B2178551
theorem B6203735 : Blo 1451545 6203735 := bstep (se 1 (by rfl) ⟨4652801, by rfl⟩ : syracuseStep 6203735 = 9305603) B9305603
theorem B1452383 : Blo 1451545 1452383 := bstep (se 1 (by rfl) ⟨1089287, by rfl⟩ : syracuseStep 1452383 = 2178575) B2178575
theorem B1452411 : Blo 1451545 1452411 := bstep (se 1 (by rfl) ⟨1089308, by rfl⟩ : syracuseStep 1452411 = 2178617) B2178617
theorem B1452463 : Blo 1451545 1452463 := bstep (se 1 (by rfl) ⟨1089347, by rfl⟩ : syracuseStep 1452463 = 2178695) B2178695
theorem B1837495 : Blo 1451545 1837495 := bstep (se 1 (by rfl) ⟨1378121, by rfl⟩ : syracuseStep 1837495 = 2756243) B2756243
theorem B1452487 : Blo 1451545 1452487 := bstep (se 1 (by rfl) ⟨1089365, by rfl⟩ : syracuseStep 1452487 = 2178731) B2178731
theorem B5515721 : Blo 1451545 5515721 := bstep (se 2 (by rfl) ⟨2068395, by rfl⟩ : syracuseStep 5515721 = 4136791) B4136791
theorem B1452507 : Blo 1451545 1452507 := bstep (se 1 (by rfl) ⟨1089380, by rfl⟩ : syracuseStep 1452507 = 2178761) B2178761
theorem B4901363 : Blo 1451545 4901363 := bstep (se 1 (by rfl) ⟨3676022, by rfl⟩ : syracuseStep 4901363 = 7352045) B7352045
theorem B1452583 : Blo 1451545 1452583 := bstep (se 1 (by rfl) ⟨1089437, by rfl⟩ : syracuseStep 1452583 = 2178875) B2178875
theorem B15927853 : Blo 1451545 15927853 := bstep (se 3 (by rfl) ⟨2986472, by rfl⟩ : syracuseStep 15927853 = 5972945) B5972945
theorem B2452025 : Blo 1451545 2452025 := bstep (se 2 (by rfl) ⟨919509, by rfl⟩ : syracuseStep 2452025 = 1839019) B1839019
theorem B1452623 : Blo 1451545 1452623 := bstep (se 1 (by rfl) ⟨1089467, by rfl⟩ : syracuseStep 1452623 = 2178935) B2178935
theorem B1452639 : Blo 1451545 1452639 := bstep (se 1 (by rfl) ⟨1089479, by rfl⟩ : syracuseStep 1452639 = 2178959) B2178959
theorem B1452667 : Blo 1451545 1452667 := bstep (se 1 (by rfl) ⟨1089500, by rfl⟩ : syracuseStep 1452667 = 2179001) B2179001
theorem B1452719 : Blo 1451545 1452719 := bstep (se 1 (by rfl) ⟨1089539, by rfl⟩ : syracuseStep 1452719 = 2179079) B2179079
theorem B1452743 : Blo 1451545 1452743 := bstep (se 1 (by rfl) ⟨1089557, by rfl⟩ : syracuseStep 1452743 = 2179115) B2179115
theorem B1452763 : Blo 1451545 1452763 := bstep (se 1 (by rfl) ⟨1089572, by rfl⟩ : syracuseStep 1452763 = 2179145) B2179145
theorem B5892857 : Blo 1451545 5892857 := bstep (se 2 (by rfl) ⟨2209821, by rfl⟩ : syracuseStep 5892857 = 4419643) B4419643
theorem B1452839 : Blo 1451545 1452839 := bstep (se 1 (by rfl) ⟨1089629, by rfl⟩ : syracuseStep 1452839 = 2179259) B2179259
theorem B39742285 : Blo 1451545 39742285 := bstep (se 3 (by rfl) ⟨7451678, by rfl⟩ : syracuseStep 39742285 = 14903357) B14903357
theorem B1452879 : Blo 1451545 1452879 := bstep (se 1 (by rfl) ⟨1089659, by rfl⟩ : syracuseStep 1452879 = 2179319) B2179319
theorem B1452895 : Blo 1451545 1452895 := bstep (se 1 (by rfl) ⟨1089671, by rfl⟩ : syracuseStep 1452895 = 2179343) B2179343
theorem B1452923 : Blo 1451545 1452923 := bstep (se 1 (by rfl) ⟨1089692, by rfl⟩ : syracuseStep 1452923 = 2179385) B2179385
theorem B5516207 : Blo 1451545 5516207 := bstep (se 1 (by rfl) ⟨4137155, by rfl⟩ : syracuseStep 5516207 = 8274311) B8274311
theorem B1452975 : Blo 1451545 1452975 := bstep (se 1 (by rfl) ⟨1089731, by rfl⟩ : syracuseStep 1452975 = 2179463) B2179463
theorem B41880503 : Blo 1451545 41880503 := bstep (se 1 (by rfl) ⟨31410377, by rfl⟩ : syracuseStep 41880503 = 62820755) B62820755
theorem B4656055 : Blo 1451545 4656055 := bstep (se 1 (by rfl) ⟨3492041, by rfl⟩ : syracuseStep 4656055 = 6984083) B6984083
theorem B1452999 : Blo 1451545 1452999 := bstep (se 1 (by rfl) ⟨1089749, by rfl⟩ : syracuseStep 1452999 = 2179499) B2179499
theorem B1633243 : Blo 1451545 1633243 := bstep (se 1 (by rfl) ⟨1224932, by rfl⟩ : syracuseStep 1633243 = 2449865) B2449865
theorem B1453019 : Blo 1451545 1453019 := bstep (se 1 (by rfl) ⟨1089764, by rfl⟩ : syracuseStep 1453019 = 2179529) B2179529
theorem B4901903 : Blo 1451545 4901903 := bstep (se 1 (by rfl) ⟨3676427, by rfl⟩ : syracuseStep 4901903 = 7352855) B7352855
theorem B1453095 : Blo 1451545 1453095 := bstep (se 1 (by rfl) ⟨1089821, by rfl⟩ : syracuseStep 1453095 = 2179643) B2179643
theorem B3779641 : Blo 1451545 3779641 := bstep (se 2 (by rfl) ⟨1417365, by rfl⟩ : syracuseStep 3779641 = 2834731) B2834731
theorem B2067535 : Blo 1451545 2067535 := bstep (se 1 (by rfl) ⟨1550651, by rfl⟩ : syracuseStep 2067535 = 3101303) B3101303
theorem B1453135 : Blo 1451545 1453135 := bstep (se 1 (by rfl) ⟨1089851, by rfl⟩ : syracuseStep 1453135 = 2179703) B2179703
theorem B1453151 : Blo 1451545 1453151 := bstep (se 1 (by rfl) ⟨1089863, by rfl⟩ : syracuseStep 1453151 = 2179727) B2179727
theorem B1453179 : Blo 1451545 1453179 := bstep (se 1 (by rfl) ⟨1089884, by rfl⟩ : syracuseStep 1453179 = 2179769) B2179769
theorem B1453231 : Blo 1451545 1453231 := bstep (se 1 (by rfl) ⟨1089923, by rfl⟩ : syracuseStep 1453231 = 2179847) B2179847
theorem B1453255 : Blo 1451545 1453255 := bstep (se 1 (by rfl) ⟨1089941, by rfl⟩ : syracuseStep 1453255 = 2179883) B2179883
theorem B2755795 : Blo 1451545 2755795 := bstep (se 1 (by rfl) ⟨2066846, by rfl⟩ : syracuseStep 2755795 = 4133693) B4133693
theorem B1453275 : Blo 1451545 1453275 := bstep (se 1 (by rfl) ⟨1089956, by rfl⟩ : syracuseStep 1453275 = 2179913) B2179913
theorem B2452727 : Blo 1451545 2452727 := bstep (se 1 (by rfl) ⟨1839545, by rfl⟩ : syracuseStep 2452727 = 3679091) B3679091
theorem B1453351 : Blo 1451545 1453351 := bstep (se 1 (by rfl) ⟨1090013, by rfl⟩ : syracuseStep 1453351 = 2180027) B2180027
theorem B1453391 : Blo 1451545 1453391 := bstep (se 1 (by rfl) ⟨1090043, by rfl⟩ : syracuseStep 1453391 = 2180087) B2180087
theorem B1453407 : Blo 1451545 1453407 := bstep (se 1 (by rfl) ⟨1090055, by rfl⟩ : syracuseStep 1453407 = 2180111) B2180111
theorem B1453435 : Blo 1451545 1453435 := bstep (se 1 (by rfl) ⟨1090076, by rfl⟩ : syracuseStep 1453435 = 2180153) B2180153
theorem B4418959 : Blo 1451545 4418959 := bstep (se 1 (by rfl) ⟨3314219, by rfl⟩ : syracuseStep 4418959 = 6628439) B6628439
theorem B8269229 : Blo 1451545 8269229 := bstep (se 3 (by rfl) ⟨1550480, by rfl⟩ : syracuseStep 8269229 = 3100961) B3100961
theorem B2756015 : Blo 1451545 2756015 := bstep (se 1 (by rfl) ⟨2067011, by rfl⟩ : syracuseStep 2756015 = 4134023) B4134023
theorem B1633711 : Blo 1451545 1633711 := bstep (se 1 (by rfl) ⟨1225283, by rfl⟩ : syracuseStep 1633711 = 2450567) B2450567
theorem B1453487 : Blo 1451545 1453487 := bstep (se 1 (by rfl) ⟨1090115, by rfl⟩ : syracuseStep 1453487 = 2180231) B2180231
theorem B1453511 : Blo 1451545 1453511 := bstep (se 1 (by rfl) ⟨1090133, by rfl⟩ : syracuseStep 1453511 = 2180267) B2180267
theorem B1453531 : Blo 1451545 1453531 := bstep (se 1 (by rfl) ⟨1090148, by rfl⟩ : syracuseStep 1453531 = 2180297) B2180297
theorem B4902497 : Blo 1451545 4902497 := bstep (se 2 (by rfl) ⟨1838436, by rfl⟩ : syracuseStep 4902497 = 3676873) B3676873
theorem B1838791 : Blo 1451545 1838791 := bstep (se 1 (by rfl) ⟨1379093, by rfl⟩ : syracuseStep 1838791 = 2758187) B2758187
theorem B5517011 : Blo 1451545 5517011 := bstep (se 1 (by rfl) ⟨4137758, by rfl⟩ : syracuseStep 5517011 = 8275517) B8275517
theorem B39767773 : Blo 1451545 39767773 := bstep (se 3 (by rfl) ⟨7456457, by rfl⟩ : syracuseStep 39767773 = 14912915) B14912915
theorem B2756425 : Blo 1451545 2756425 := bstep (se 2 (by rfl) ⟨1033659, by rfl⟩ : syracuseStep 2756425 = 2067319) B2067319
theorem B1634143 : Blo 1451545 1634143 := bstep (se 1 (by rfl) ⟨1225607, by rfl⟩ : syracuseStep 1634143 = 2451215) B2451215
theorem B12406715 : Blo 1451545 12406715 := bstep (se 1 (by rfl) ⟨9305036, by rfl⟩ : syracuseStep 12406715 = 18610073) B18610073
theorem B9310265 : Blo 1451545 9310265 := bstep (se 2 (by rfl) ⟨3491349, by rfl⟩ : syracuseStep 9310265 = 6982699) B6982699
theorem B15102067 : Blo 1451545 15102067 := bstep (se 1 (by rfl) ⟨11326550, by rfl⟩ : syracuseStep 15102067 = 22653101) B22653101
theorem B1634503 : Blo 1451545 1634503 := bstep (se 1 (by rfl) ⟨1225877, by rfl⟩ : syracuseStep 1634503 = 2451755) B2451755
theorem B8270369 : Blo 1451545 8270369 := bstep (se 2 (by rfl) ⟨3101388, by rfl⟩ : syracuseStep 8270369 = 6202777) B6202777
theorem B4035169 : Blo 1451545 4035169 := bstep (se 2 (by rfl) ⟨1513188, by rfl⟩ : syracuseStep 4035169 = 3026377) B3026377
theorem B3674747 : Blo 1451545 3674747 := bstep (se 1 (by rfl) ⟨2756060, by rfl⟩ : syracuseStep 3674747 = 5512121) B5512121
theorem B7353017 : Blo 1451545 7353017 := bstep (se 2 (by rfl) ⟨2757381, by rfl⟩ : syracuseStep 7353017 = 5514763) B5514763
theorem B5305031 : Blo 1451545 5305031 := bstep (se 1 (by rfl) ⟨3978773, by rfl⟩ : syracuseStep 5305031 = 7957547) B7957547
theorem B35320529 : Blo 1451545 35320529 := bstep (se 2 (by rfl) ⟨13245198, by rfl⟩ : syracuseStep 35320529 = 26490397) B26490397
theorem B18609047 : Blo 1451545 18609047 := bstep (se 1 (by rfl) ⟨13956785, by rfl⟩ : syracuseStep 18609047 = 27913571) B27913571
theorem B3675041 : Blo 1451545 3675041 := bstep (se 2 (by rfl) ⟨1378140, by rfl⟩ : syracuseStep 3675041 = 2756281) B2756281
theorem B1455067 : Blo 1451545 1455067 := bstep (se 1 (by rfl) ⟨1091300, by rfl⟩ : syracuseStep 1455067 = 2182601) B2182601
theorem B4903955 : Blo 1451545 4903955 := bstep (se 1 (by rfl) ⟨3677966, by rfl⟩ : syracuseStep 4903955 = 7355933) B7355933
theorem B4904279 : Blo 1451545 4904279 := bstep (se 1 (by rfl) ⟨3678209, by rfl⟩ : syracuseStep 4904279 = 7356419) B7356419
theorem B39777635 : Blo 1451545 39777635 := bstep (se 1 (by rfl) ⟨29833226, by rfl⟩ : syracuseStep 39777635 = 59666453) B59666453
theorem B31389281 : Blo 1451545 31389281 := bstep (se 2 (by rfl) ⟨11770980, by rfl⟩ : syracuseStep 31389281 = 23541961) B23541961
theorem B3266171 : Blo 1451545 3266171 := bstep (se 1 (by rfl) ⟨2449628, by rfl⟩ : syracuseStep 3266171 = 4899257) B4899257
theorem B19388119 : Blo 1451545 19388119 := bstep (se 1 (by rfl) ⟨14541089, by rfl⟩ : syracuseStep 19388119 = 29082179) B29082179
theorem B3266297 : Blo 1451545 3266297 := bstep (se 2 (by rfl) ⟨1224861, by rfl⟩ : syracuseStep 3266297 = 2449723) B2449723
theorem B3102457 : Blo 1451545 3102457 := bstep (se 2 (by rfl) ⟨1163421, by rfl⟩ : syracuseStep 3102457 = 2326843) B2326843
theorem B19879739 : Blo 1451545 19879739 := bstep (se 1 (by rfl) ⟨14909804, by rfl⟩ : syracuseStep 19879739 = 29819609) B29819609
theorem B37738349 : Blo 1451545 37738349 := bstep (se 3 (by rfl) ⟨7075940, by rfl⟩ : syracuseStep 37738349 = 14151881) B14151881
theorem B3266567 : Blo 1451545 3266567 := bstep (se 1 (by rfl) ⟨2449925, by rfl⟩ : syracuseStep 3266567 = 4899851) B4899851
theorem B3266639 : Blo 1451545 3266639 := bstep (se 1 (by rfl) ⟨2449979, by rfl⟩ : syracuseStep 3266639 = 4899959) B4899959
theorem B3102799 : Blo 1451545 3102799 := bstep (se 1 (by rfl) ⟨2327099, by rfl⟩ : syracuseStep 3102799 = 4654199) B4654199
theorem B2758855 : Blo 1451545 2758855 := bstep (se 1 (by rfl) ⟨2069141, by rfl⟩ : syracuseStep 2758855 = 4138283) B4138283
theorem B169834765 : Blo 1451545 169834765 := bstep (se 3 (by rfl) ⟨31844018, by rfl⟩ : syracuseStep 169834765 = 63688037) B63688037
theorem B2177375 : Blo 1451545 2177375 := bstep (se 1 (by rfl) ⟨1633031, by rfl⟩ : syracuseStep 2177375 = 3266063) B3266063
theorem B2177387 : Blo 1451545 2177387 := bstep (se 1 (by rfl) ⟨1633040, by rfl⟩ : syracuseStep 2177387 = 3266081) B3266081
theorem B4905359 : Blo 1451545 4905359 := bstep (se 1 (by rfl) ⟨3679019, by rfl⟩ : syracuseStep 4905359 = 7358039) B7358039
theorem B3267035 : Blo 1451545 3267035 := bstep (se 1 (by rfl) ⟨2450276, by rfl⟩ : syracuseStep 3267035 = 4900553) B4900553
theorem B16538093 : Blo 1451545 16538093 := bstep (se 3 (by rfl) ⟨3100892, by rfl⟩ : syracuseStep 16538093 = 6201785) B6201785
theorem B3676711 : Blo 1451545 3676711 := bstep (se 1 (by rfl) ⟨2757533, by rfl⟩ : syracuseStep 3676711 = 5515067) B5515067
theorem B8829499 : Blo 1451545 8829499 := bstep (se 1 (by rfl) ⟨6622124, by rfl⟩ : syracuseStep 8829499 = 13244249) B13244249
theorem B2177615 : Blo 1451545 2177615 := bstep (se 1 (by rfl) ⟨1633211, by rfl⟩ : syracuseStep 2177615 = 3266423) B3266423
theorem B2177735 : Blo 1451545 2177735 := bstep (se 1 (by rfl) ⟨1633301, by rfl⟩ : syracuseStep 2177735 = 3266603) B3266603
theorem B3488467 : Blo 1451545 3488467 := bstep (se 1 (by rfl) ⟨2616350, by rfl⟩ : syracuseStep 3488467 = 5232701) B5232701
theorem B4905683 : Blo 1451545 4905683 := bstep (se 1 (by rfl) ⟨3679262, by rfl⟩ : syracuseStep 4905683 = 7358525) B7358525
theorem B2759417 : Blo 1451545 2759417 := bstep (se 2 (by rfl) ⟨1034781, by rfl⟩ : syracuseStep 2759417 = 2069563) B2069563
theorem B5233481 : Blo 1451545 5233481 := bstep (se 2 (by rfl) ⟨1962555, by rfl⟩ : syracuseStep 5233481 = 3925111) B3925111
theorem B2177897 : Blo 1451545 2177897 := bstep (se 2 (by rfl) ⟨816711, by rfl⟩ : syracuseStep 2177897 = 1633423) B1633423
theorem B3677035 : Blo 1451545 3677035 := bstep (se 1 (by rfl) ⟨2757776, by rfl⟩ : syracuseStep 3677035 = 5515553) B5515553
theorem B3267503 : Blo 1451545 3267503 := bstep (se 1 (by rfl) ⟨2450627, by rfl⟩ : syracuseStep 3267503 = 4901255) B4901255
theorem B2177975 : Blo 1451545 2177975 := bstep (se 1 (by rfl) ⟨1633481, by rfl⟩ : syracuseStep 2177975 = 3266963) B3266963
theorem B2178011 : Blo 1451545 2178011 := bstep (se 1 (by rfl) ⟨1633508, by rfl⟩ : syracuseStep 2178011 = 3267017) B3267017
theorem B3103763 : Blo 1451545 3103763 := bstep (se 1 (by rfl) ⟨2327822, by rfl⟩ : syracuseStep 3103763 = 4655645) B4655645
theorem B3267755 : Blo 1451545 3267755 := bstep (se 1 (by rfl) ⟨2450816, by rfl⟩ : syracuseStep 3267755 = 4901633) B4901633
theorem B13966627 : Blo 1451545 13966627 := bstep (se 1 (by rfl) ⟨10474970, by rfl⟩ : syracuseStep 13966627 = 20949941) B20949941
theorem B4652417 : Blo 1451545 4652417 := bstep (se 2 (by rfl) ⟨1744656, by rfl⟩ : syracuseStep 4652417 = 3489313) B3489313
theorem B2178479 : Blo 1451545 2178479 := bstep (se 1 (by rfl) ⟨1633859, by rfl⟩ : syracuseStep 2178479 = 3267719) B3267719
theorem B3677683 : Blo 1451545 3677683 := bstep (se 1 (by rfl) ⟨2758262, by rfl⟩ : syracuseStep 3677683 = 5516525) B5516525
theorem B2178569 : Blo 1451545 2178569 := bstep (se 2 (by rfl) ⟨816963, by rfl⟩ : syracuseStep 2178569 = 1633927) B1633927
theorem B2653715 : Blo 1451545 2653715 := bstep (se 1 (by rfl) ⟨1990286, by rfl⟩ : syracuseStep 2653715 = 3980573) B3980573
theorem B4652569 : Blo 1451545 4652569 := bstep (se 2 (by rfl) ⟨1744713, by rfl⟩ : syracuseStep 4652569 = 3489427) B3489427
theorem B2178599 : Blo 1451545 2178599 := bstep (se 1 (by rfl) ⟨1633949, by rfl⟩ : syracuseStep 2178599 = 3267899) B3267899
theorem B30203459 : Blo 1451545 30203459 := bstep (se 1 (by rfl) ⟨22652594, by rfl⟩ : syracuseStep 30203459 = 45305189) B45305189
theorem B2178683 : Blo 1451545 2178683 := bstep (se 1 (by rfl) ⟨1634012, by rfl⟩ : syracuseStep 2178683 = 3268025) B3268025
theorem B3489419 : Blo 1451545 3489419 := bstep (se 1 (by rfl) ⟨2617064, by rfl⟩ : syracuseStep 3489419 = 5234129) B5234129
theorem B9428669 : Blo 1451545 9428669 := bstep (se 3 (by rfl) ⟨1767875, by rfl⟩ : syracuseStep 9428669 = 3535751) B3535751
theorem B3268295 : Blo 1451545 3268295 := bstep (se 1 (by rfl) ⟨2451221, by rfl⟩ : syracuseStep 3268295 = 4902443) B4902443
theorem B14147293 : Blo 1451545 14147293 := bstep (se 3 (by rfl) ⟨2652617, by rfl⟩ : syracuseStep 14147293 = 5305235) B5305235
theorem B2178809 : Blo 1451545 2178809 := bstep (se 2 (by rfl) ⟨817053, by rfl⟩ : syracuseStep 2178809 = 1634107) B1634107
theorem B7855865 : Blo 1451545 7855865 := bstep (se 2 (by rfl) ⟨2945949, by rfl⟩ : syracuseStep 7855865 = 5891899) B5891899
theorem B2178911 : Blo 1451545 2178911 := bstep (se 1 (by rfl) ⟨1634183, by rfl⟩ : syracuseStep 2178911 = 3268367) B3268367
theorem B2178923 : Blo 1451545 2178923 := bstep (se 1 (by rfl) ⟨1634192, by rfl⟩ : syracuseStep 2178923 = 3268385) B3268385
theorem B4137065 : Blo 1451545 4137065 := bstep (se 2 (by rfl) ⟨1551399, by rfl⟩ : syracuseStep 4137065 = 3102799) B3102799
theorem B24813701 : Blo 1451545 24813701 := bstep (se 4 (by rfl) ⟨2326284, by rfl⟩ : syracuseStep 24813701 = 4652569) B4652569
theorem B20136089 : Blo 1451545 20136089 := bstep (se 2 (by rfl) ⟨7551033, by rfl⟩ : syracuseStep 20136089 = 15102067) B15102067
theorem B12411089 : Blo 1451545 12411089 := bstep (se 2 (by rfl) ⟨4654158, by rfl⟩ : syracuseStep 12411089 = 9308317) B9308317
theorem B2179337 : Blo 1451545 2179337 := bstep (se 2 (by rfl) ⟨817251, by rfl⟩ : syracuseStep 2179337 = 1634503) B1634503
theorem B3678473 : Blo 1451545 3678473 := bstep (se 2 (by rfl) ⟨1379427, by rfl⟩ : syracuseStep 3678473 = 2758855) B2758855
theorem B2097499 : Blo 1451545 2097499 := bstep (se 1 (by rfl) ⟨1573124, by rfl⟩ : syracuseStep 2097499 = 3146249) B3146249
theorem B5513579 : Blo 1451545 5513579 := bstep (se 1 (by rfl) ⟨4135184, by rfl⟩ : syracuseStep 5513579 = 8270369) B8270369
theorem B2179439 : Blo 1451545 2179439 := bstep (se 1 (by rfl) ⟨1634579, by rfl⟩ : syracuseStep 2179439 = 3269159) B3269159
theorem B11026853 : Blo 1451545 11026853 := bstep (se 4 (by rfl) ⟨1033767, by rfl⟩ : syracuseStep 11026853 = 2067535) B2067535
theorem B2449831 : Blo 1451545 2449831 := bstep (se 1 (by rfl) ⟨1837373, by rfl⟩ : syracuseStep 2449831 = 3674747) B3674747
theorem B2326951 : Blo 1451545 2326951 := bstep (se 1 (by rfl) ⟨1745213, by rfl⟩ : syracuseStep 2326951 = 3490427) B3490427
theorem B52986329 : Blo 1451545 52986329 := bstep (se 2 (by rfl) ⟨19869873, by rfl⟩ : syracuseStep 52986329 = 39739747) B39739747
theorem B18612737 : Blo 1451545 18612737 := bstep (se 2 (by rfl) ⟨6979776, by rfl⟩ : syracuseStep 18612737 = 13959553) B13959553
theorem B2179655 : Blo 1451545 2179655 := bstep (se 1 (by rfl) ⟨1634741, by rfl⟩ : syracuseStep 2179655 = 3269483) B3269483
theorem B2449993 : Blo 1451545 2449993 := bstep (se 2 (by rfl) ⟨918747, by rfl⟩ : syracuseStep 2449993 = 1837495) B1837495
theorem B2450027 : Blo 1451545 2450027 := bstep (se 1 (by rfl) ⟨1837520, by rfl⟩ : syracuseStep 2450027 = 3675041) B3675041
theorem B2179691 : Blo 1451545 2179691 := bstep (se 1 (by rfl) ⟨1634768, by rfl⟩ : syracuseStep 2179691 = 3269537) B3269537
theorem B13959863 : Blo 1451545 13959863 := bstep (se 1 (by rfl) ⟨10469897, by rfl⟩ : syracuseStep 13959863 = 20939795) B20939795
theorem B3269303 : Blo 1451545 3269303 := bstep (se 1 (by rfl) ⟨2451977, by rfl⟩ : syracuseStep 3269303 = 4903955) B4903955
theorem B11772665 : Blo 1451545 11772665 := bstep (se 2 (by rfl) ⟨4414749, by rfl⟩ : syracuseStep 11772665 = 8829499) B8829499
theorem B2327375 : Blo 1451545 2327375 := bstep (se 1 (by rfl) ⟨1745531, by rfl⟩ : syracuseStep 2327375 = 3491063) B3491063
theorem B2179919 : Blo 1451545 2179919 := bstep (se 1 (by rfl) ⟨1634939, by rfl⟩ : syracuseStep 2179919 = 3269879) B3269879
theorem B3269519 : Blo 1451545 3269519 := bstep (se 1 (by rfl) ⟨2452139, by rfl⟩ : syracuseStep 3269519 = 4904279) B4904279
theorem B26518423 : Blo 1451545 26518423 := bstep (se 1 (by rfl) ⟨19888817, by rfl⟩ : syracuseStep 26518423 = 39777635) B39777635
theorem B12584135 : Blo 1451545 12584135 := bstep (se 1 (by rfl) ⟨9438101, by rfl⟩ : syracuseStep 12584135 = 18876203) B18876203
theorem B2180315 : Blo 1451545 2180315 := bstep (se 1 (by rfl) ⟨1635236, by rfl⟩ : syracuseStep 2180315 = 3270473) B3270473
theorem B4654313 : Blo 1451545 4654313 := bstep (se 2 (by rfl) ⟨1745367, by rfl⟩ : syracuseStep 4654313 = 3490735) B3490735
theorem B25158899 : Blo 1451545 25158899 := bstep (se 1 (by rfl) ⟨18869174, by rfl⟩ : syracuseStep 25158899 = 37738349) B37738349
theorem B8275243 : Blo 1451545 8275243 := bstep (se 1 (by rfl) ⟨6206432, by rfl⟩ : syracuseStep 8275243 = 12412865) B12412865
theorem B1451583 : Blo 1451545 1451583 := bstep (se 1 (by rfl) ⟨1088687, by rfl⟩ : syracuseStep 1451583 = 2177375) B2177375
theorem B1451591 : Blo 1451545 1451591 := bstep (se 1 (by rfl) ⟨1088693, by rfl⟩ : syracuseStep 1451591 = 2177387) B2177387
theorem B3270239 : Blo 1451545 3270239 := bstep (se 1 (by rfl) ⟨2452679, by rfl⟩ : syracuseStep 3270239 = 4905359) B4905359
theorem B18622169 : Blo 1451545 18622169 := bstep (se 2 (by rfl) ⟨6983313, by rfl⟩ : syracuseStep 18622169 = 13966627) B13966627
theorem B1451743 : Blo 1451545 1451743 := bstep (se 1 (by rfl) ⟨1088807, by rfl⟩ : syracuseStep 1451743 = 2177615) B2177615
theorem B1451823 : Blo 1451545 1451823 := bstep (se 1 (by rfl) ⟨1088867, by rfl⟩ : syracuseStep 1451823 = 2177735) B2177735
theorem B3270455 : Blo 1451545 3270455 := bstep (se 1 (by rfl) ⟨2452841, by rfl⟩ : syracuseStep 3270455 = 4905683) B4905683
theorem B9308009 : Blo 1451545 9308009 := bstep (se 2 (by rfl) ⟨3490503, by rfl⟩ : syracuseStep 9308009 = 6981007) B6981007
theorem B5891945 : Blo 1451545 5891945 := bstep (se 2 (by rfl) ⟨2209479, by rfl⟩ : syracuseStep 5891945 = 4418959) B4418959
theorem B1451931 : Blo 1451545 1451931 := bstep (se 1 (by rfl) ⟨1088948, by rfl⟩ : syracuseStep 1451931 = 2177897) B2177897
theorem B1451983 : Blo 1451545 1451983 := bstep (se 1 (by rfl) ⟨1088987, by rfl⟩ : syracuseStep 1451983 = 2177975) B2177975
theorem B27920335 : Blo 1451545 27920335 := bstep (se 1 (by rfl) ⟨20940251, by rfl⟩ : syracuseStep 27920335 = 41880503) B41880503
theorem B1452007 : Blo 1451545 1452007 := bstep (se 1 (by rfl) ⟨1089005, by rfl⟩ : syracuseStep 1452007 = 2178011) B2178011
theorem B2451721 : Blo 1451545 2451721 := bstep (se 2 (by rfl) ⟨919395, by rfl⟩ : syracuseStep 2451721 = 1838791) B1838791
theorem B4655389 : Blo 1451545 4655389 := bstep (se 3 (by rfl) ⟨872885, by rfl⟩ : syracuseStep 4655389 = 1745771) B1745771
theorem B1837343 : Blo 1451545 1837343 := bstep (se 1 (by rfl) ⟨1378007, by rfl⟩ : syracuseStep 1837343 = 2756015) B2756015
theorem B1452319 : Blo 1451545 1452319 := bstep (se 1 (by rfl) ⟨1089239, by rfl⟩ : syracuseStep 1452319 = 2178479) B2178479
theorem B1452379 : Blo 1451545 1452379 := bstep (se 1 (by rfl) ⟨1089284, by rfl⟩ : syracuseStep 1452379 = 2178569) B2178569
theorem B1452399 : Blo 1451545 1452399 := bstep (se 1 (by rfl) ⟨1089299, by rfl⟩ : syracuseStep 1452399 = 2178599) B2178599
theorem B1452455 : Blo 1451545 1452455 := bstep (se 1 (by rfl) ⟨1089341, by rfl⟩ : syracuseStep 1452455 = 2178683) B2178683
theorem B6285779 : Blo 1451545 6285779 := bstep (se 1 (by rfl) ⟨4714334, by rfl⟩ : syracuseStep 6285779 = 9428669) B9428669
theorem B1452539 : Blo 1451545 1452539 := bstep (se 1 (by rfl) ⟨1089404, by rfl⟩ : syracuseStep 1452539 = 2178809) B2178809
theorem B5237243 : Blo 1451545 5237243 := bstep (se 1 (by rfl) ⟨3927932, by rfl⟩ : syracuseStep 5237243 = 7855865) B7855865
theorem B1452607 : Blo 1451545 1452607 := bstep (se 1 (by rfl) ⟨1089455, by rfl⟩ : syracuseStep 1452607 = 2178911) B2178911
theorem B1452615 : Blo 1451545 1452615 := bstep (se 1 (by rfl) ⟨1089461, by rfl⟩ : syracuseStep 1452615 = 2178923) B2178923
theorem B134154953 : Blo 1451545 134154953 := bstep (se 2 (by rfl) ⟨50308107, by rfl⟩ : syracuseStep 134154953 = 100616215) B100616215
theorem B8276701 : Blo 1451545 8276701 := bstep (se 3 (by rfl) ⟨1551881, by rfl⟩ : syracuseStep 8276701 = 3103763) B3103763
theorem B1632991 : Blo 1451545 1632991 := bstep (se 1 (by rfl) ⟨1224743, by rfl⟩ : syracuseStep 1632991 = 2449487) B2449487
theorem B1452767 : Blo 1451545 1452767 := bstep (se 1 (by rfl) ⟨1089575, by rfl⟩ : syracuseStep 1452767 = 2179151) B2179151
theorem B1452847 : Blo 1451545 1452847 := bstep (se 1 (by rfl) ⟨1089635, by rfl⟩ : syracuseStep 1452847 = 2179271) B2179271
theorem B37751645 : Blo 1451545 37751645 := bstep (se 3 (by rfl) ⟨7078433, by rfl⟩ : syracuseStep 37751645 = 14156867) B14156867
theorem B1452955 : Blo 1451545 1452955 := bstep (se 1 (by rfl) ⟨1089716, by rfl⟩ : syracuseStep 1452955 = 2179433) B2179433
theorem B1453007 : Blo 1451545 1453007 := bstep (se 1 (by rfl) ⟨1089755, by rfl⟩ : syracuseStep 1453007 = 2179511) B2179511
theorem B1453031 : Blo 1451545 1453031 := bstep (se 1 (by rfl) ⟨1089773, by rfl⟩ : syracuseStep 1453031 = 2179547) B2179547
theorem B5237747 : Blo 1451545 5237747 := bstep (se 1 (by rfl) ⟨3928310, by rfl⟩ : syracuseStep 5237747 = 7856621) B7856621
theorem B226446353 : Blo 1451545 226446353 := bstep (se 2 (by rfl) ⟨84917382, by rfl⟩ : syracuseStep 226446353 = 169834765) B169834765
theorem B4902011 : Blo 1451545 4902011 := bstep (se 1 (by rfl) ⟨3676508, by rfl⟩ : syracuseStep 4902011 = 7353017) B7353017
theorem B23547019 : Blo 1451545 23547019 := bstep (se 1 (by rfl) ⟨17660264, by rfl⟩ : syracuseStep 23547019 = 35320529) B35320529
theorem B5893339 : Blo 1451545 5893339 := bstep (se 1 (by rfl) ⟨4420004, by rfl⟩ : syracuseStep 5893339 = 8840009) B8840009
theorem B12406031 : Blo 1451545 12406031 := bstep (se 1 (by rfl) ⟨9304523, by rfl⟩ : syracuseStep 12406031 = 18609047) B18609047
theorem B1633567 : Blo 1451545 1633567 := bstep (se 1 (by rfl) ⟨1225175, by rfl⟩ : syracuseStep 1633567 = 2450351) B2450351
theorem B1453343 : Blo 1451545 1453343 := bstep (se 1 (by rfl) ⟨1090007, by rfl⟩ : syracuseStep 1453343 = 2180015) B2180015
theorem B1453403 : Blo 1451545 1453403 := bstep (se 1 (by rfl) ⟨1090052, by rfl⟩ : syracuseStep 1453403 = 2180105) B2180105
theorem B1453423 : Blo 1451545 1453423 := bstep (se 1 (by rfl) ⟨1090067, by rfl⟩ : syracuseStep 1453423 = 2180135) B2180135
theorem B4902281 : Blo 1451545 4902281 := bstep (se 2 (by rfl) ⟨1838355, by rfl⟩ : syracuseStep 4902281 = 3676711) B3676711
theorem B21237137 : Blo 1451545 21237137 := bstep (se 2 (by rfl) ⟨7963926, by rfl⟩ : syracuseStep 21237137 = 15927853) B15927853
theorem B1453479 : Blo 1451545 1453479 := bstep (se 1 (by rfl) ⟨1090109, by rfl⟩ : syracuseStep 1453479 = 2180219) B2180219
theorem B2207225 : Blo 1451545 2207225 := bstep (se 2 (by rfl) ⟨827709, by rfl⟩ : syracuseStep 2207225 = 1655419) B1655419
theorem B1633855 : Blo 1451545 1633855 := bstep (se 1 (by rfl) ⟨1225391, by rfl⟩ : syracuseStep 1633855 = 2450783) B2450783
theorem B20926187 : Blo 1451545 20926187 := bstep (se 1 (by rfl) ⟨15694640, by rfl⟩ : syracuseStep 20926187 = 31389281) B31389281
theorem B52989713 : Blo 1451545 52989713 := bstep (se 2 (by rfl) ⟨19871142, by rfl⟩ : syracuseStep 52989713 = 39742285) B39742285
theorem B4902713 : Blo 1451545 4902713 := bstep (se 2 (by rfl) ⟨1838517, by rfl⟩ : syracuseStep 4902713 = 3677035) B3677035
theorem B7352531 : Blo 1451545 7352531 := bstep (se 1 (by rfl) ⟨5514398, by rfl⟩ : syracuseStep 7352531 = 11028797) B11028797
theorem B3674393 : Blo 1451545 3674393 := bstep (se 2 (by rfl) ⟨1377897, by rfl⟩ : syracuseStep 3674393 = 2755795) B2755795
theorem B1634683 : Blo 1451545 1634683 := bstep (se 1 (by rfl) ⟨1226012, by rfl⟩ : syracuseStep 1634683 = 2452025) B2452025
theorem B31830509 : Blo 1451545 31830509 := bstep (se 3 (by rfl) ⟨5968220, by rfl⟩ : syracuseStep 31830509 = 11936441) B11936441
theorem B15708653 : Blo 1451545 15708653 := bstep (se 3 (by rfl) ⟨2945372, by rfl⟩ : syracuseStep 15708653 = 5890745) B5890745
theorem B3928571 : Blo 1451545 3928571 := bstep (se 1 (by rfl) ⟨2946428, by rfl⟩ : syracuseStep 3928571 = 5892857) B5892857
theorem B1839611 : Blo 1451545 1839611 := bstep (se 1 (by rfl) ⟨1379708, by rfl⟩ : syracuseStep 1839611 = 2759417) B2759417
theorem B4903577 : Blo 1451545 4903577 := bstep (se 2 (by rfl) ⟨1838841, by rfl⟩ : syracuseStep 4903577 = 3677683) B3677683
theorem B1635151 : Blo 1451545 1635151 := bstep (se 1 (by rfl) ⟨1226363, by rfl⟩ : syracuseStep 1635151 = 2452727) B2452727
theorem B3101611 : Blo 1451545 3101611 := bstep (se 1 (by rfl) ⟨2326208, by rfl⟩ : syracuseStep 3101611 = 4652417) B4652417
theorem B25850825 : Blo 1451545 25850825 := bstep (se 2 (by rfl) ⟨9694059, by rfl⟩ : syracuseStep 25850825 = 19388119) B19388119
theorem B18863057 : Blo 1451545 18863057 := bstep (se 2 (by rfl) ⟨7073646, by rfl⟩ : syracuseStep 18863057 = 14147293) B14147293
theorem B53023697 : Blo 1451545 53023697 := bstep (se 2 (by rfl) ⟨19883886, by rfl⟩ : syracuseStep 53023697 = 39767773) B39767773
theorem B3675233 : Blo 1451545 3675233 := bstep (se 2 (by rfl) ⟨1378212, by rfl⟩ : syracuseStep 3675233 = 2756425) B2756425
theorem B8271143 : Blo 1451545 8271143 := bstep (se 1 (by rfl) ⟨6203357, by rfl⟩ : syracuseStep 8271143 = 12406715) B12406715
theorem B3102047 : Blo 1451545 3102047 := bstep (se 1 (by rfl) ⟨2326535, by rfl⟩ : syracuseStep 3102047 = 4653071) B4653071
theorem B6206843 : Blo 1451545 6206843 := bstep (se 1 (by rfl) ⟨4655132, by rfl⟩ : syracuseStep 6206843 = 9310265) B9310265
theorem B3265991 : Blo 1451545 3265991 := bstep (se 1 (by rfl) ⟨2449493, by rfl⟩ : syracuseStep 3265991 = 4898987) B4898987
theorem B20158085 : Blo 1451545 20158085 := bstep (se 4 (by rfl) ⟨1889820, by rfl⟩ : syracuseStep 20158085 = 3779641) B3779641
theorem B3266351 : Blo 1451545 3266351 := bstep (se 1 (by rfl) ⟨2449763, by rfl⟩ : syracuseStep 3266351 = 4899527) B4899527
theorem B3536687 : Blo 1451545 3536687 := bstep (se 1 (by rfl) ⟨2652515, by rfl⟩ : syracuseStep 3536687 = 5305031) B5305031
theorem B11327521 : Blo 1451545 11327521 := bstep (se 2 (by rfl) ⟨4247820, by rfl⟩ : syracuseStep 11327521 = 8495641) B8495641
theorem B5380225 : Blo 1451545 5380225 := bstep (se 2 (by rfl) ⟨2017584, by rfl⟩ : syracuseStep 5380225 = 4035169) B4035169
theorem B4905089 : Blo 1451545 4905089 := bstep (se 2 (by rfl) ⟨1839408, by rfl⟩ : syracuseStep 4905089 = 3678817) B3678817
theorem B6625415 : Blo 1451545 6625415 := bstep (se 1 (by rfl) ⟨4969061, by rfl⟩ : syracuseStep 6625415 = 9938123) B9938123
theorem B4651289 : Blo 1451545 4651289 := bstep (se 2 (by rfl) ⟨1744233, by rfl⟩ : syracuseStep 4651289 = 3488467) B3488467
theorem B3266927 : Blo 1451545 3266927 := bstep (se 1 (by rfl) ⟨2450195, by rfl⟩ : syracuseStep 3266927 = 4900391) B4900391
theorem B42473879 : Blo 1451545 42473879 := bstep (se 1 (by rfl) ⟨31855409, by rfl⟩ : syracuseStep 42473879 = 63710819) B63710819
theorem B2177447 : Blo 1451545 2177447 := bstep (se 1 (by rfl) ⟨1633085, by rfl⟩ : syracuseStep 2177447 = 3266171) B3266171
theorem B3266999 : Blo 1451545 3266999 := bstep (se 1 (by rfl) ⟨2450249, by rfl⟩ : syracuseStep 3266999 = 4900499) B4900499
theorem B5511635 : Blo 1451545 5511635 := bstep (se 1 (by rfl) ⟨4133726, by rfl⟩ : syracuseStep 5511635 = 8267453) B8267453
theorem B2177531 : Blo 1451545 2177531 := bstep (se 1 (by rfl) ⟨1633148, by rfl⟩ : syracuseStep 2177531 = 3266297) B3266297
theorem B7559675 : Blo 1451545 7559675 := bstep (se 1 (by rfl) ⟨5669756, by rfl⟩ : syracuseStep 7559675 = 11339513) B11339513
theorem B4905467 : Blo 1451545 4905467 := bstep (se 1 (by rfl) ⟨3679100, by rfl⟩ : syracuseStep 4905467 = 7358201) B7358201
theorem B3676691 : Blo 1451545 3676691 := bstep (se 1 (by rfl) ⟨2757518, by rfl⟩ : syracuseStep 3676691 = 5515037) B5515037
theorem B13253159 : Blo 1451545 13253159 := bstep (se 1 (by rfl) ⟨9939869, by rfl⟩ : syracuseStep 13253159 = 19879739) B19879739
theorem B4971071 : Blo 1451545 4971071 := bstep (se 1 (by rfl) ⟨3728303, by rfl⟩ : syracuseStep 4971071 = 7456607) B7456607
theorem B3267143 : Blo 1451545 3267143 := bstep (se 1 (by rfl) ⟨2450357, by rfl⟩ : syracuseStep 3267143 = 4900715) B4900715
theorem B6208073 : Blo 1451545 6208073 := bstep (se 2 (by rfl) ⟨2328027, by rfl⟩ : syracuseStep 6208073 = 4656055) B4656055
theorem B7854671 : Blo 1451545 7854671 := bstep (se 1 (by rfl) ⟨5891003, by rfl⟩ : syracuseStep 7854671 = 11782007) B11782007
theorem B3267179 : Blo 1451545 3267179 := bstep (se 1 (by rfl) ⟨2450384, by rfl⟩ : syracuseStep 3267179 = 4900769) B4900769
theorem B2177657 : Blo 1451545 2177657 := bstep (se 2 (by rfl) ⟨816621, by rfl⟩ : syracuseStep 2177657 = 1633243) B1633243
theorem B1940089 : Blo 1451545 1940089 := bstep (se 2 (by rfl) ⟨727533, by rfl⟩ : syracuseStep 1940089 = 1455067) B1455067
theorem B2177711 : Blo 1451545 2177711 := bstep (se 1 (by rfl) ⟨1633283, by rfl⟩ : syracuseStep 2177711 = 3266567) B3266567
theorem B2177759 : Blo 1451545 2177759 := bstep (se 1 (by rfl) ⟨1633319, by rfl⟩ : syracuseStep 2177759 = 3266639) B3266639
theorem B4135823 : Blo 1451545 4135823 := bstep (se 1 (by rfl) ⟨3101867, by rfl⟩ : syracuseStep 4135823 = 6203735) B6203735
theorem B3677147 : Blo 1451545 3677147 := bstep (se 1 (by rfl) ⟨2757860, by rfl⟩ : syracuseStep 3677147 = 5515721) B5515721
theorem B2178023 : Blo 1451545 2178023 := bstep (se 1 (by rfl) ⟨1633517, by rfl⟩ : syracuseStep 2178023 = 3267035) B3267035
theorem B11025395 : Blo 1451545 11025395 := bstep (se 1 (by rfl) ⟨8269046, by rfl⟩ : syracuseStep 11025395 = 16538093) B16538093
theorem B3267575 : Blo 1451545 3267575 := bstep (se 1 (by rfl) ⟨2450681, by rfl⟩ : syracuseStep 3267575 = 4901363) B4901363
theorem B9305117 : Blo 1451545 9305117 := bstep (se 3 (by rfl) ⟨1744709, by rfl⟩ : syracuseStep 9305117 = 3489419) B3489419
theorem B3488987 : Blo 1451545 3488987 := bstep (se 1 (by rfl) ⟨2616740, by rfl⟩ : syracuseStep 3488987 = 5233481) B5233481
theorem B2178281 : Blo 1451545 2178281 := bstep (se 2 (by rfl) ⟨816855, by rfl⟩ : syracuseStep 2178281 = 1633711) B1633711
theorem B2178335 : Blo 1451545 2178335 := bstep (se 1 (by rfl) ⟨1633751, by rfl⟩ : syracuseStep 2178335 = 3267503) B3267503
theorem B3677471 : Blo 1451545 3677471 := bstep (se 1 (by rfl) ⟨2758103, by rfl⟩ : syracuseStep 3677471 = 5516207) B5516207
theorem B3267935 : Blo 1451545 3267935 := bstep (se 1 (by rfl) ⟨2450951, by rfl⟩ : syracuseStep 3267935 = 4901903) B4901903
theorem B5234057 : Blo 1451545 5234057 := bstep (se 2 (by rfl) ⟨1962771, by rfl⟩ : syracuseStep 5234057 = 3925543) B3925543
theorem B2178503 : Blo 1451545 2178503 := bstep (se 1 (by rfl) ⟨1633877, by rfl⟩ : syracuseStep 2178503 = 3267755) B3267755
theorem B5512819 : Blo 1451545 5512819 := bstep (se 1 (by rfl) ⟨4134614, by rfl⟩ : syracuseStep 5512819 = 8269229) B8269229
theorem B4136609 : Blo 1451545 4136609 := bstep (se 2 (by rfl) ⟨1551228, by rfl⟩ : syracuseStep 4136609 = 3102457) B3102457
theorem B1769143 : Blo 1451545 1769143 := bstep (se 1 (by rfl) ⟨1326857, by rfl⟩ : syracuseStep 1769143 = 2653715) B2653715
theorem B20135639 : Blo 1451545 20135639 := bstep (se 1 (by rfl) ⟨15101729, by rfl⟩ : syracuseStep 20135639 = 30203459) B30203459
theorem B3268331 : Blo 1451545 3268331 := bstep (se 1 (by rfl) ⟨2451248, by rfl⟩ : syracuseStep 3268331 = 4902497) B4902497
theorem B2178857 : Blo 1451545 2178857 := bstep (se 2 (by rfl) ⟨817071, by rfl⟩ : syracuseStep 2178857 = 1634143) B1634143
theorem B2178863 : Blo 1451545 2178863 := bstep (se 1 (by rfl) ⟨1634147, by rfl⟩ : syracuseStep 2178863 = 3268295) B3268295
theorem B3678007 : Blo 1451545 3678007 := bstep (se 1 (by rfl) ⟨2758505, by rfl⟩ : syracuseStep 3678007 = 5517011) B5517011
theorem B3268457 : Blo 1451545 3268457 := bstep (se 2 (by rfl) ⟨1225671, by rfl⟩ : syracuseStep 3268457 = 2451343) B2451343
theorem B8274059 : Blo 1451545 8274059 := bstep (se 1 (by rfl) ⟨6205544, by rfl⟩ : syracuseStep 8274059 = 12411089) B12411089
theorem B2449595 : Blo 1451545 2449595 := bstep (se 1 (by rfl) ⟨1837196, by rfl⟩ : syracuseStep 2449595 = 3674393) B3674393
theorem B35324219 : Blo 1451545 35324219 := bstep (se 1 (by rfl) ⟨26493164, by rfl⟩ : syracuseStep 35324219 = 52986329) B52986329
theorem B3268961 : Blo 1451545 3268961 := bstep (se 2 (by rfl) ⟨1225860, by rfl⟩ : syracuseStep 3268961 = 2451721) B2451721
theorem B3269051 : Blo 1451545 3269051 := bstep (se 1 (by rfl) ⟨2451788, by rfl⟩ : syracuseStep 3269051 = 4903577) B4903577
theorem B9306575 : Blo 1451545 9306575 := bstep (se 1 (by rfl) ⟨6979931, by rfl⟩ : syracuseStep 9306575 = 13959863) B13959863
theorem B2179535 : Blo 1451545 2179535 := bstep (se 1 (by rfl) ⟨1634651, by rfl⟩ : syracuseStep 2179535 = 3269303) B3269303
theorem B2179577 : Blo 1451545 2179577 := bstep (se 2 (by rfl) ⟨817341, by rfl⟩ : syracuseStep 2179577 = 1634683) B1634683
theorem B7848443 : Blo 1451545 7848443 := bstep (se 1 (by rfl) ⟨5886332, by rfl⟩ : syracuseStep 7848443 = 11772665) B11772665
theorem B2179679 : Blo 1451545 2179679 := bstep (se 1 (by rfl) ⟨1634759, by rfl⟩ : syracuseStep 2179679 = 3269519) B3269519
theorem B12575371 : Blo 1451545 12575371 := bstep (se 1 (by rfl) ⟨9431528, by rfl⟩ : syracuseStep 12575371 = 18863057) B18863057
theorem B35349131 : Blo 1451545 35349131 := bstep (se 1 (by rfl) ⟨26511848, by rfl⟩ : syracuseStep 35349131 = 53023697) B53023697
theorem B2450155 : Blo 1451545 2450155 := bstep (se 1 (by rfl) ⟨1837616, by rfl⟩ : syracuseStep 2450155 = 3675233) B3675233
theorem B4899581 : Blo 1451545 4899581 := bstep (se 3 (by rfl) ⟨918671, by rfl⟩ : syracuseStep 4899581 = 1837343) B1837343
theorem B8389423 : Blo 1451545 8389423 := bstep (se 1 (by rfl) ⟨6292067, by rfl⟩ : syracuseStep 8389423 = 12584135) B12584135
theorem B5514095 : Blo 1451545 5514095 := bstep (se 1 (by rfl) ⟨4135571, by rfl⟩ : syracuseStep 5514095 = 8271143) B8271143
theorem B4137895 : Blo 1451545 4137895 := bstep (se 1 (by rfl) ⟨3103421, by rfl⟩ : syracuseStep 4137895 = 6206843) B6206843
theorem B11035601 : Blo 1451545 11035601 := bstep (se 2 (by rfl) ⟨4138350, by rfl⟩ : syracuseStep 11035601 = 8276701) B8276701
theorem B2180159 : Blo 1451545 2180159 := bstep (se 1 (by rfl) ⟨1635119, by rfl⟩ : syracuseStep 2180159 = 3270239) B3270239
theorem B2180201 : Blo 1451545 2180201 := bstep (se 2 (by rfl) ⟨817575, by rfl⟩ : syracuseStep 2180201 = 1635151) B1635151
theorem B35357897 : Blo 1451545 35357897 := bstep (se 2 (by rfl) ⟨13259211, by rfl⟩ : syracuseStep 35357897 = 26518423) B26518423
theorem B2180303 : Blo 1451545 2180303 := bstep (se 1 (by rfl) ⟨1635227, by rfl⟩ : syracuseStep 2180303 = 3270455) B3270455
theorem B3270059 : Blo 1451545 3270059 := bstep (se 1 (by rfl) ⟨2452544, by rfl⟩ : syracuseStep 3270059 = 4905089) B4905089
theorem B4416943 : Blo 1451545 4416943 := bstep (se 1 (by rfl) ⟨3312707, by rfl⟩ : syracuseStep 4416943 = 6625415) B6625415
theorem B1451631 : Blo 1451545 1451631 := bstep (se 1 (by rfl) ⟨1088723, by rfl⟩ : syracuseStep 1451631 = 2177447) B2177447
theorem B7857785 : Blo 1451545 7857785 := bstep (se 2 (by rfl) ⟨2946669, by rfl⟩ : syracuseStep 7857785 = 5893339) B5893339
theorem B1451687 : Blo 1451545 1451687 := bstep (se 1 (by rfl) ⟨1088765, by rfl⟩ : syracuseStep 1451687 = 2177531) B2177531
theorem B3491495 : Blo 1451545 3491495 := bstep (se 1 (by rfl) ⟨2618621, by rfl⟩ : syracuseStep 3491495 = 5237243) B5237243
theorem B5039783 : Blo 1451545 5039783 := bstep (se 1 (by rfl) ⟨3779837, by rfl⟩ : syracuseStep 5039783 = 7559675) B7559675
theorem B3270311 : Blo 1451545 3270311 := bstep (se 1 (by rfl) ⟨2452733, by rfl⟩ : syracuseStep 3270311 = 4905467) B4905467
theorem B2451127 : Blo 1451545 2451127 := bstep (se 1 (by rfl) ⟨1838345, by rfl⟩ : syracuseStep 2451127 = 3676691) B3676691
theorem B4138715 : Blo 1451545 4138715 := bstep (se 1 (by rfl) ⟨3104036, by rfl⟩ : syracuseStep 4138715 = 6208073) B6208073
theorem B1451771 : Blo 1451545 1451771 := bstep (se 1 (by rfl) ⟨1088828, by rfl⟩ : syracuseStep 1451771 = 2177657) B2177657
theorem B1451807 : Blo 1451545 1451807 := bstep (se 1 (by rfl) ⟨1088855, by rfl⟩ : syracuseStep 1451807 = 2177711) B2177711
theorem B1451839 : Blo 1451545 1451839 := bstep (se 1 (by rfl) ⟨1088879, by rfl⟩ : syracuseStep 1451839 = 2177759) B2177759
theorem B25167763 : Blo 1451545 25167763 := bstep (se 1 (by rfl) ⟨18875822, by rfl⟩ : syracuseStep 25167763 = 37751645) B37751645
theorem B2451431 : Blo 1451545 2451431 := bstep (se 1 (by rfl) ⟨1838573, by rfl⟩ : syracuseStep 2451431 = 3677147) B3677147
theorem B1452015 : Blo 1451545 1452015 := bstep (se 1 (by rfl) ⟨1089011, by rfl⟩ : syracuseStep 1452015 = 2178023) B2178023
theorem B7350263 : Blo 1451545 7350263 := bstep (se 1 (by rfl) ⟨5512697, by rfl⟩ : syracuseStep 7350263 = 11025395) B11025395
theorem B3491831 : Blo 1451545 3491831 := bstep (se 1 (by rfl) ⟨2618873, by rfl⟩ : syracuseStep 3491831 = 5237747) B5237747
theorem B150964235 : Blo 1451545 150964235 := bstep (se 1 (by rfl) ⟨113223176, by rfl⟩ : syracuseStep 150964235 = 226446353) B226446353
theorem B6203411 : Blo 1451545 6203411 := bstep (se 1 (by rfl) ⟨4652558, by rfl⟩ : syracuseStep 6203411 = 9305117) B9305117
theorem B7350425 : Blo 1451545 7350425 := bstep (se 2 (by rfl) ⟨2756409, by rfl⟩ : syracuseStep 7350425 = 5512819) B5512819
theorem B1452187 : Blo 1451545 1452187 := bstep (se 1 (by rfl) ⟨1089140, by rfl⟩ : syracuseStep 1452187 = 2178281) B2178281
theorem B1452223 : Blo 1451545 1452223 := bstep (se 1 (by rfl) ⟨1089167, by rfl⟩ : syracuseStep 1452223 = 2178335) B2178335
theorem B2451647 : Blo 1451545 2451647 := bstep (se 1 (by rfl) ⟨1838735, by rfl⟩ : syracuseStep 2451647 = 3677471) B3677471
theorem B14158091 : Blo 1451545 14158091 := bstep (se 1 (by rfl) ⟨10618568, by rfl⟩ : syracuseStep 14158091 = 21237137) B21237137
theorem B1452335 : Blo 1451545 1452335 := bstep (se 1 (by rfl) ⟨1089251, by rfl⟩ : syracuseStep 1452335 = 2178503) B2178503
theorem B35326475 : Blo 1451545 35326475 := bstep (se 1 (by rfl) ⟨26494856, by rfl⟩ : syracuseStep 35326475 = 52989713) B52989713
theorem B41388565 : Blo 1451545 41388565 := bstep (se 6 (by rfl) ⟨970044, by rfl⟩ : syracuseStep 41388565 = 1940089) B1940089
theorem B1452571 : Blo 1451545 1452571 := bstep (se 1 (by rfl) ⟨1089428, by rfl⟩ : syracuseStep 1452571 = 2178857) B2178857
theorem B1452575 : Blo 1451545 1452575 := bstep (se 1 (by rfl) ⟨1089431, by rfl⟩ : syracuseStep 1452575 = 2178863) B2178863
theorem B37227113 : Blo 1451545 37227113 := bstep (se 2 (by rfl) ⟨13960167, by rfl⟩ : syracuseStep 37227113 = 27920335) B27920335
theorem B16542467 : Blo 1451545 16542467 := bstep (se 1 (by rfl) ⟨12406850, by rfl⟩ : syracuseStep 16542467 = 24813701) B24813701
theorem B4901687 : Blo 1451545 4901687 := bstep (se 1 (by rfl) ⟨3676265, by rfl⟩ : syracuseStep 4901687 = 7352531) B7352531
theorem B1452891 : Blo 1451545 1452891 := bstep (se 1 (by rfl) ⟨1089668, by rfl⟩ : syracuseStep 1452891 = 2179337) B2179337
theorem B2452315 : Blo 1451545 2452315 := bstep (se 1 (by rfl) ⟨1839236, by rfl⟩ : syracuseStep 2452315 = 3678473) B3678473
theorem B1452959 : Blo 1451545 1452959 := bstep (se 1 (by rfl) ⟨1089719, by rfl⟩ : syracuseStep 1452959 = 2179439) B2179439
theorem B7351235 : Blo 1451545 7351235 := bstep (se 1 (by rfl) ⟨5513426, by rfl⟩ : syracuseStep 7351235 = 11026853) B11026853
theorem B10472435 : Blo 1451545 10472435 := bstep (se 1 (by rfl) ⟨7854326, by rfl⟩ : syracuseStep 10472435 = 15708653) B15708653
theorem B1453103 : Blo 1451545 1453103 := bstep (se 1 (by rfl) ⟨1089827, by rfl⟩ : syracuseStep 1453103 = 2179655) B2179655
theorem B1633351 : Blo 1451545 1633351 := bstep (se 1 (by rfl) ⟨1225013, by rfl⟩ : syracuseStep 1633351 = 2450027) B2450027
theorem B1453127 : Blo 1451545 1453127 := bstep (se 1 (by rfl) ⟨1089845, by rfl⟩ : syracuseStep 1453127 = 2179691) B2179691
theorem B2796665 : Blo 1451545 2796665 := bstep (se 2 (by rfl) ⟨1048749, by rfl⟩ : syracuseStep 2796665 = 2097499) B2097499
theorem B1551583 : Blo 1451545 1551583 := bstep (se 1 (by rfl) ⟨1163687, by rfl⟩ : syracuseStep 1551583 = 2327375) B2327375
theorem B1453279 : Blo 1451545 1453279 := bstep (se 1 (by rfl) ⟨1089959, by rfl⟩ : syracuseStep 1453279 = 2179919) B2179919
theorem B1453543 : Blo 1451545 1453543 := bstep (se 1 (by rfl) ⟨1090157, by rfl⟩ : syracuseStep 1453543 = 2180315) B2180315
theorem B16772599 : Blo 1451545 16772599 := bstep (se 1 (by rfl) ⟨12579449, by rfl⟩ : syracuseStep 16772599 = 25158899) B25158899
theorem B2068031 : Blo 1451545 2068031 := bstep (se 1 (by rfl) ⟨1551023, by rfl⟩ : syracuseStep 2068031 = 3102047) B3102047
theorem B13438723 : Blo 1451545 13438723 := bstep (se 1 (by rfl) ⟨10079042, by rfl⟩ : syracuseStep 13438723 = 20158085) B20158085
theorem B12414779 : Blo 1451545 12414779 := bstep (se 1 (by rfl) ⟨9311084, by rfl⟩ : syracuseStep 12414779 = 18622169) B18622169
theorem B6205339 : Blo 1451545 6205339 := bstep (se 1 (by rfl) ⟨4654004, by rfl⟩ : syracuseStep 6205339 = 9308009) B9308009
theorem B84881357 : Blo 1451545 84881357 := bstep (se 3 (by rfl) ⟨15915254, by rfl⟩ : syracuseStep 84881357 = 31830509) B31830509
theorem B31396025 : Blo 1451545 31396025 := bstep (se 2 (by rfl) ⟨11773509, by rfl⟩ : syracuseStep 31396025 = 23547019) B23547019
theorem B3100859 : Blo 1451545 3100859 := bstep (se 1 (by rfl) ⟨2325644, by rfl⟩ : syracuseStep 3100859 = 4651289) B4651289
theorem B28315919 : Blo 1451545 28315919 := bstep (se 1 (by rfl) ⟨21236939, by rfl⟩ : syracuseStep 28315919 = 42473879) B42473879
theorem B3674423 : Blo 1451545 3674423 := bstep (se 1 (by rfl) ⟨2755817, by rfl⟩ : syracuseStep 3674423 = 5511635) B5511635
theorem B4190519 : Blo 1451545 4190519 := bstep (se 1 (by rfl) ⟨3142889, by rfl⟩ : syracuseStep 4190519 = 6285779) B6285779
theorem B8835439 : Blo 1451545 8835439 := bstep (se 1 (by rfl) ⟨6626579, by rfl⟩ : syracuseStep 8835439 = 13253159) B13253159
theorem B3314047 : Blo 1451545 3314047 := bstep (se 1 (by rfl) ⟨2485535, by rfl⟩ : syracuseStep 3314047 = 4971071) B4971071
theorem B89436635 : Blo 1451545 89436635 := bstep (se 1 (by rfl) ⟨67077476, by rfl⟩ : syracuseStep 89436635 = 134154953) B134154953
theorem B53695037 : Blo 1451545 53695037 := bstep (se 3 (by rfl) ⟨10067819, by rfl⟩ : syracuseStep 53695037 = 20135639) B20135639
theorem B2757215 : Blo 1451545 2757215 := bstep (se 1 (by rfl) ⟨2067911, by rfl⟩ : syracuseStep 2757215 = 4135823) B4135823
theorem B8270687 : Blo 1451545 8270687 := bstep (se 1 (by rfl) ⟨6203015, by rfl⟩ : syracuseStep 8270687 = 12406031) B12406031
theorem B1471483 : Blo 1451545 1471483 := bstep (se 1 (by rfl) ⟨1103612, by rfl⟩ : syracuseStep 1471483 = 2207225) B2207225
theorem B4904009 : Blo 1451545 4904009 := bstep (se 2 (by rfl) ⟨1839003, by rfl⟩ : syracuseStep 4904009 = 3678007) B3678007
theorem B2757739 : Blo 1451545 2757739 := bstep (se 1 (by rfl) ⟨2068304, by rfl⟩ : syracuseStep 2757739 = 4136609) B4136609
theorem B15103361 : Blo 1451545 15103361 := bstep (se 2 (by rfl) ⟨5663760, by rfl⟩ : syracuseStep 15103361 = 11327521) B11327521
theorem B2758043 : Blo 1451545 2758043 := bstep (se 1 (by rfl) ⟨2068532, by rfl⟩ : syracuseStep 2758043 = 4137065) B4137065
theorem B13424059 : Blo 1451545 13424059 := bstep (se 1 (by rfl) ⟨10068044, by rfl⟩ : syracuseStep 13424059 = 20136089) B20136089
theorem B3675719 : Blo 1451545 3675719 := bstep (se 1 (by rfl) ⟨2756789, by rfl⟩ : syracuseStep 3675719 = 5513579) B5513579
theorem B2619047 : Blo 1451545 2619047 := bstep (se 1 (by rfl) ⟨1964285, by rfl⟩ : syracuseStep 2619047 = 3928571) B3928571
theorem B12408491 : Blo 1451545 12408491 := bstep (se 1 (by rfl) ⟨9306368, by rfl⟩ : syracuseStep 12408491 = 18612737) B18612737
theorem B6207185 : Blo 1451545 6207185 := bstep (se 2 (by rfl) ⟨2327694, by rfl⟩ : syracuseStep 6207185 = 4655389) B4655389
theorem B3266441 : Blo 1451545 3266441 := bstep (se 2 (by rfl) ⟨1224915, by rfl⟩ : syracuseStep 3266441 = 2449831) B2449831
theorem B17233883 : Blo 1451545 17233883 := bstep (se 1 (by rfl) ⟨12925412, by rfl⟩ : syracuseStep 17233883 = 25850825) B25850825
theorem B28694533 : Blo 1451545 28694533 := bstep (se 4 (by rfl) ⟨2690112, by rfl⟩ : syracuseStep 28694533 = 5380225) B5380225
theorem B3266657 : Blo 1451545 3266657 := bstep (se 2 (by rfl) ⟨1224996, by rfl⟩ : syracuseStep 3266657 = 2449993) B2449993
theorem B3102875 : Blo 1451545 3102875 := bstep (se 1 (by rfl) ⟨2327156, by rfl⟩ : syracuseStep 3102875 = 4654313) B4654313
theorem B2177321 : Blo 1451545 2177321 := bstep (se 2 (by rfl) ⟨816495, by rfl⟩ : syracuseStep 2177321 = 1632991) B1632991
theorem B2177327 : Blo 1451545 2177327 := bstep (se 1 (by rfl) ⟨1632995, by rfl⟩ : syracuseStep 2177327 = 3265991) B3265991
theorem B2177567 : Blo 1451545 2177567 := bstep (se 1 (by rfl) ⟨1633175, by rfl⟩ : syracuseStep 2177567 = 3266351) B3266351
theorem B2357791 : Blo 1451545 2357791 := bstep (se 1 (by rfl) ⟨1768343, by rfl⟩ : syracuseStep 2357791 = 3536687) B3536687
theorem B4135481 : Blo 1451545 4135481 := bstep (se 2 (by rfl) ⟨1550805, by rfl⟩ : syracuseStep 4135481 = 3101611) B3101611
theorem B4905629 : Blo 1451545 4905629 := bstep (se 3 (by rfl) ⟨919805, by rfl⟩ : syracuseStep 4905629 = 1839611) B1839611
theorem B20945789 : Blo 1451545 20945789 := bstep (se 3 (by rfl) ⟨3927335, by rfl⟩ : syracuseStep 20945789 = 7854671) B7854671
theorem B2177951 : Blo 1451545 2177951 := bstep (se 1 (by rfl) ⟨1633463, by rfl⟩ : syracuseStep 2177951 = 3266927) B3266927
theorem B2177999 : Blo 1451545 2177999 := bstep (se 1 (by rfl) ⟨1633499, by rfl⟩ : syracuseStep 2177999 = 3266999) B3266999
theorem B2178089 : Blo 1451545 2178089 := bstep (se 2 (by rfl) ⟨816783, by rfl⟩ : syracuseStep 2178089 = 1633567) B1633567
theorem B2178095 : Blo 1451545 2178095 := bstep (se 1 (by rfl) ⟨1633571, by rfl⟩ : syracuseStep 2178095 = 3267143) B3267143
theorem B11033657 : Blo 1451545 11033657 := bstep (se 2 (by rfl) ⟨4137621, by rfl⟩ : syracuseStep 11033657 = 8275243) B8275243
theorem B2178119 : Blo 1451545 2178119 := bstep (se 1 (by rfl) ⟨1633589, by rfl⟩ : syracuseStep 2178119 = 3267179) B3267179
theorem B2178383 : Blo 1451545 2178383 := bstep (se 1 (by rfl) ⟨1633787, by rfl⟩ : syracuseStep 2178383 = 3267575) B3267575
theorem B3268007 : Blo 1451545 3268007 := bstep (se 1 (by rfl) ⟨2451005, by rfl⟩ : syracuseStep 3268007 = 4902011) B4902011
theorem B2178473 : Blo 1451545 2178473 := bstep (se 2 (by rfl) ⟨816927, by rfl⟩ : syracuseStep 2178473 = 1633855) B1633855
theorem B2325991 : Blo 1451545 2325991 := bstep (se 1 (by rfl) ⟨1744493, by rfl⟩ : syracuseStep 2325991 = 3488987) B3488987
theorem B12410405 : Blo 1451545 12410405 := bstep (se 4 (by rfl) ⟨1163475, by rfl⟩ : syracuseStep 12410405 = 2326951) B2326951
theorem B2178623 : Blo 1451545 2178623 := bstep (se 1 (by rfl) ⟨1633967, by rfl⟩ : syracuseStep 2178623 = 3267935) B3267935
theorem B2358857 : Blo 1451545 2358857 := bstep (se 2 (by rfl) ⟨884571, by rfl⟩ : syracuseStep 2358857 = 1769143) B1769143
theorem B3489371 : Blo 1451545 3489371 := bstep (se 1 (by rfl) ⟨2617028, by rfl⟩ : syracuseStep 3489371 = 5234057) B5234057
theorem B3268187 : Blo 1451545 3268187 := bstep (se 1 (by rfl) ⟨2451140, by rfl⟩ : syracuseStep 3268187 = 4902281) B4902281
theorem B15711853 : Blo 1451545 15711853 := bstep (se 3 (by rfl) ⟨2945972, by rfl⟩ : syracuseStep 15711853 = 5891945) B5891945
theorem B13950791 : Blo 1451545 13950791 := bstep (se 1 (by rfl) ⟨10463093, by rfl⟩ : syracuseStep 13950791 = 20926187) B20926187
theorem B2178887 : Blo 1451545 2178887 := bstep (se 1 (by rfl) ⟨1634165, by rfl⟩ : syracuseStep 2178887 = 3268331) B3268331
theorem B3268475 : Blo 1451545 3268475 := bstep (se 1 (by rfl) ⟨2451356, by rfl⟩ : syracuseStep 3268475 = 4902713) B4902713
theorem B2178971 : Blo 1451545 2178971 := bstep (se 1 (by rfl) ⟨1634228, by rfl⟩ : syracuseStep 2178971 = 3268457) B3268457
theorem B20930683 : Blo 1451545 20930683 := bstep (se 1 (by rfl) ⟨15698012, by rfl⟩ : syracuseStep 20930683 = 31396025) B31396025
theorem B12574885 : Blo 1451545 12574885 := bstep (se 4 (by rfl) ⟨1178895, by rfl⟩ : syracuseStep 12574885 = 2357791) B2357791
theorem B2449615 : Blo 1451545 2449615 := bstep (se 1 (by rfl) ⟨1837211, by rfl⟩ : syracuseStep 2449615 = 3674423) B3674423
theorem B2793679 : Blo 1451545 2793679 := bstep (se 1 (by rfl) ⟨2095259, by rfl⟩ : syracuseStep 2793679 = 4190519) B4190519
theorem B2179307 : Blo 1451545 2179307 := bstep (se 1 (by rfl) ⟨1634480, by rfl⟩ : syracuseStep 2179307 = 3268961) B3268961
theorem B2179367 : Blo 1451545 2179367 := bstep (se 1 (by rfl) ⟨1634525, by rfl⟩ : syracuseStep 2179367 = 3269051) B3269051
theorem B11780585 : Blo 1451545 11780585 := bstep (se 2 (by rfl) ⟨4417719, by rfl⟩ : syracuseStep 11780585 = 8835439) B8835439
theorem B5513791 : Blo 1451545 5513791 := bstep (se 1 (by rfl) ⟨4135343, by rfl⟩ : syracuseStep 5513791 = 8270687) B8270687
theorem B7357067 : Blo 1451545 7357067 := bstep (se 1 (by rfl) ⟨5517800, by rfl⟩ : syracuseStep 7357067 = 11035601) B11035601
theorem B3269339 : Blo 1451545 3269339 := bstep (se 1 (by rfl) ⟨2452004, by rfl⟩ : syracuseStep 3269339 = 4904009) B4904009
theorem B10068907 : Blo 1451545 10068907 := bstep (se 1 (by rfl) ⟨7551680, by rfl⟩ : syracuseStep 10068907 = 15103361) B15103361
theorem B2180039 : Blo 1451545 2180039 := bstep (se 1 (by rfl) ⟨1635029, by rfl⟩ : syracuseStep 2180039 = 3270059) B3270059
theorem B2450479 : Blo 1451545 2450479 := bstep (se 1 (by rfl) ⟨1837859, by rfl⟩ : syracuseStep 2450479 = 3675719) B3675719
theorem B2327663 : Blo 1451545 2327663 := bstep (se 1 (by rfl) ⟨1745747, by rfl⟩ : syracuseStep 2327663 = 3491495) B3491495
theorem B3359855 : Blo 1451545 3359855 := bstep (se 1 (by rfl) ⟨2519891, by rfl⟩ : syracuseStep 3359855 = 5039783) B5039783
theorem B1746031 : Blo 1451545 1746031 := bstep (se 1 (by rfl) ⟨1309523, by rfl⟩ : syracuseStep 1746031 = 2619047) B2619047
theorem B2180207 : Blo 1451545 2180207 := bstep (se 1 (by rfl) ⟨1635155, by rfl⟩ : syracuseStep 2180207 = 3270311) B3270311
theorem B3269753 : Blo 1451545 3269753 := bstep (se 2 (by rfl) ⟨1226157, by rfl⟩ : syracuseStep 3269753 = 2452315) B2452315
theorem B4138123 : Blo 1451545 4138123 := bstep (se 1 (by rfl) ⟨3103592, by rfl⟩ : syracuseStep 4138123 = 6207185) B6207185
theorem B4900175 : Blo 1451545 4900175 := bstep (se 1 (by rfl) ⟨3675131, by rfl⟩ : syracuseStep 4900175 = 7350263) B7350263
theorem B2327887 : Blo 1451545 2327887 := bstep (se 1 (by rfl) ⟨1745915, by rfl⟩ : syracuseStep 2327887 = 3491831) B3491831
theorem B4900283 : Blo 1451545 4900283 := bstep (se 1 (by rfl) ⟨3675212, by rfl⟩ : syracuseStep 4900283 = 7350425) B7350425
theorem B5514749 : Blo 1451545 5514749 := bstep (se 3 (by rfl) ⟨1034015, by rfl⟩ : syracuseStep 5514749 = 2068031) B2068031
theorem B9438727 : Blo 1451545 9438727 := bstep (se 1 (by rfl) ⟨7079045, by rfl⟩ : syracuseStep 9438727 = 14158091) B14158091
theorem B1451547 : Blo 1451545 1451547 := bstep (se 1 (by rfl) ⟨1088660, by rfl⟩ : syracuseStep 1451547 = 2177321) B2177321
theorem B1451551 : Blo 1451545 1451551 := bstep (se 1 (by rfl) ⟨1088663, by rfl⟩ : syracuseStep 1451551 = 2177327) B2177327
theorem B1451711 : Blo 1451545 1451711 := bstep (se 1 (by rfl) ⟨1088783, by rfl⟩ : syracuseStep 1451711 = 2177567) B2177567
theorem B3270419 : Blo 1451545 3270419 := bstep (se 1 (by rfl) ⟨2452814, by rfl⟩ : syracuseStep 3270419 = 4905629) B4905629
theorem B11028311 : Blo 1451545 11028311 := bstep (se 1 (by rfl) ⟨8271233, by rfl⟩ : syracuseStep 11028311 = 16542467) B16542467
theorem B11036573 : Blo 1451545 11036573 := bstep (se 3 (by rfl) ⟨2069357, by rfl⟩ : syracuseStep 11036573 = 4138715) B4138715
theorem B1451967 : Blo 1451545 1451967 := bstep (se 1 (by rfl) ⟨1088975, by rfl⟩ : syracuseStep 1451967 = 2177951) B2177951
theorem B4900823 : Blo 1451545 4900823 := bstep (se 1 (by rfl) ⟨3675617, by rfl⟩ : syracuseStep 4900823 = 7351235) B7351235
theorem B1451999 : Blo 1451545 1451999 := bstep (se 1 (by rfl) ⟨1088999, by rfl⟩ : syracuseStep 1451999 = 2177999) B2177999
theorem B6981623 : Blo 1451545 6981623 := bstep (se 1 (by rfl) ⟨5236217, by rfl⟩ : syracuseStep 6981623 = 10472435) B10472435
theorem B1452059 : Blo 1451545 1452059 := bstep (se 1 (by rfl) ⟨1089044, by rfl⟩ : syracuseStep 1452059 = 2178089) B2178089
theorem B1452063 : Blo 1451545 1452063 := bstep (se 1 (by rfl) ⟨1089047, by rfl⟩ : syracuseStep 1452063 = 2178095) B2178095
theorem B1452079 : Blo 1451545 1452079 := bstep (se 1 (by rfl) ⟨1089059, by rfl⟩ : syracuseStep 1452079 = 2178119) B2178119
theorem B20949137 : Blo 1451545 20949137 := bstep (se 2 (by rfl) ⟨7855926, by rfl⟩ : syracuseStep 20949137 = 15711853) B15711853
theorem B1452255 : Blo 1451545 1452255 := bstep (se 1 (by rfl) ⟨1089191, by rfl⟩ : syracuseStep 1452255 = 2178383) B2178383
theorem B1452315 : Blo 1451545 1452315 := bstep (se 1 (by rfl) ⟨1089236, by rfl⟩ : syracuseStep 1452315 = 2178473) B2178473
theorem B17918297 : Blo 1451545 17918297 := bstep (se 2 (by rfl) ⟨6719361, by rfl⟩ : syracuseStep 17918297 = 13438723) B13438723
theorem B1452415 : Blo 1451545 1452415 := bstep (se 1 (by rfl) ⟨1089311, by rfl⟩ : syracuseStep 1452415 = 2178623) B2178623
theorem B33557017 : Blo 1451545 33557017 := bstep (se 2 (by rfl) ⟨12583881, by rfl⟩ : syracuseStep 33557017 = 25167763) B25167763
theorem B8276519 : Blo 1451545 8276519 := bstep (se 1 (by rfl) ⟨6207389, by rfl⟩ : syracuseStep 8276519 = 12414779) B12414779
theorem B9300527 : Blo 1451545 9300527 := bstep (se 1 (by rfl) ⟨6975395, by rfl⟩ : syracuseStep 9300527 = 13950791) B13950791
theorem B1452591 : Blo 1451545 1452591 := bstep (se 1 (by rfl) ⟨1089443, by rfl⟩ : syracuseStep 1452591 = 2178887) B2178887
theorem B1452647 : Blo 1451545 1452647 := bstep (se 1 (by rfl) ⟨1089485, by rfl⟩ : syracuseStep 1452647 = 2178971) B2178971
theorem B38259377 : Blo 1451545 38259377 := bstep (se 2 (by rfl) ⟨14347266, by rfl⟩ : syracuseStep 38259377 = 28694533) B28694533
theorem B5516039 : Blo 1451545 5516039 := bstep (se 1 (by rfl) ⟨4137029, by rfl⟩ : syracuseStep 5516039 = 8274059) B8274059
theorem B1633063 : Blo 1451545 1633063 := bstep (se 1 (by rfl) ⟨1224797, by rfl⟩ : syracuseStep 1633063 = 2449595) B2449595
theorem B2067239 : Blo 1451545 2067239 := bstep (se 1 (by rfl) ⟨1550429, by rfl⟩ : syracuseStep 2067239 = 3100859) B3100859
theorem B18877279 : Blo 1451545 18877279 := bstep (se 1 (by rfl) ⟨14157959, by rfl⟩ : syracuseStep 18877279 = 28315919) B28315919
theorem B6204383 : Blo 1451545 6204383 := bstep (se 1 (by rfl) ⟨4653287, by rfl⟩ : syracuseStep 6204383 = 9306575) B9306575
theorem B1453023 : Blo 1451545 1453023 := bstep (se 1 (by rfl) ⟨1089767, by rfl⟩ : syracuseStep 1453023 = 2179535) B2179535
theorem B59624423 : Blo 1451545 59624423 := bstep (se 1 (by rfl) ⟨44718317, by rfl⟩ : syracuseStep 59624423 = 89436635) B89436635
theorem B7457773 : Blo 1451545 7457773 := bstep (se 3 (by rfl) ⟨1398332, by rfl⟩ : syracuseStep 7457773 = 2796665) B2796665
theorem B1453051 : Blo 1451545 1453051 := bstep (se 1 (by rfl) ⟨1089788, by rfl⟩ : syracuseStep 1453051 = 2179577) B2179577
theorem B1838143 : Blo 1451545 1838143 := bstep (se 1 (by rfl) ⟨1378607, by rfl⟩ : syracuseStep 1838143 = 2757215) B2757215
theorem B1453119 : Blo 1451545 1453119 := bstep (se 1 (by rfl) ⟨1089839, by rfl⟩ : syracuseStep 1453119 = 2179679) B2179679
theorem B4418729 : Blo 1451545 4418729 := bstep (se 2 (by rfl) ⟨1657023, by rfl⟩ : syracuseStep 4418729 = 3314047) B3314047
theorem B55184753 : Blo 1451545 55184753 := bstep (se 2 (by rfl) ⟨20694282, by rfl⟩ : syracuseStep 55184753 = 41388565) B41388565
theorem B1453439 : Blo 1451545 1453439 := bstep (se 1 (by rfl) ⟨1090079, by rfl⟩ : syracuseStep 1453439 = 2180159) B2180159
theorem B1453467 : Blo 1451545 1453467 := bstep (se 1 (by rfl) ⟨1090100, by rfl⟩ : syracuseStep 1453467 = 2180201) B2180201
theorem B23571931 : Blo 1451545 23571931 := bstep (se 1 (by rfl) ⟨17678948, by rfl⟩ : syracuseStep 23571931 = 35357897) B35357897
theorem B1453535 : Blo 1451545 1453535 := bstep (se 1 (by rfl) ⟨1090151, by rfl⟩ : syracuseStep 1453535 = 2180303) B2180303
theorem B1838695 : Blo 1451545 1838695 := bstep (se 1 (by rfl) ⟨1379021, by rfl⟩ : syracuseStep 1838695 = 2758043) B2758043
theorem B11185897 : Blo 1451545 11185897 := bstep (se 2 (by rfl) ⟨4194711, by rfl⟩ : syracuseStep 11185897 = 8389423) B8389423
theorem B5238523 : Blo 1451545 5238523 := bstep (se 1 (by rfl) ⟨3928892, by rfl⟩ : syracuseStep 5238523 = 7857785) B7857785
theorem B5517193 : Blo 1451545 5517193 := bstep (se 2 (by rfl) ⟨2068947, by rfl⟩ : syracuseStep 5517193 = 4137895) B4137895
theorem B11489255 : Blo 1451545 11489255 := bstep (se 1 (by rfl) ⟨8616941, by rfl⟩ : syracuseStep 11489255 = 17233883) B17233883
theorem B1634287 : Blo 1451545 1634287 := bstep (se 1 (by rfl) ⟨1225715, by rfl⟩ : syracuseStep 1634287 = 2451431) B2451431
theorem B1961977 : Blo 1451545 1961977 := bstep (se 2 (by rfl) ⟨735741, by rfl⟩ : syracuseStep 1961977 = 1471483) B1471483
theorem B100642823 : Blo 1451545 100642823 := bstep (se 1 (by rfl) ⟨75482117, by rfl⟩ : syracuseStep 100642823 = 150964235) B150964235
theorem B2068583 : Blo 1451545 2068583 := bstep (se 1 (by rfl) ⟨1551437, by rfl⟩ : syracuseStep 2068583 = 3102875) B3102875
theorem B1634431 : Blo 1451545 1634431 := bstep (se 1 (by rfl) ⟨1225823, by rfl⟩ : syracuseStep 1634431 = 2451647) B2451647
theorem B2068777 : Blo 1451545 2068777 := bstep (se 2 (by rfl) ⟨775791, by rfl⟩ : syracuseStep 2068777 = 1551583) B1551583
theorem B2756987 : Blo 1451545 2756987 := bstep (se 1 (by rfl) ⟨2067740, by rfl⟩ : syracuseStep 2756987 = 4135481) B4135481
theorem B24818075 : Blo 1451545 24818075 := bstep (se 1 (by rfl) ⟨18613556, by rfl⟩ : syracuseStep 24818075 = 37227113) B37227113
theorem B13963859 : Blo 1451545 13963859 := bstep (se 1 (by rfl) ⟨10472894, by rfl⟩ : syracuseStep 13963859 = 20945789) B20945789
theorem B3101321 : Blo 1451545 3101321 := bstep (se 2 (by rfl) ⟨1162995, by rfl⟩ : syracuseStep 3101321 = 2325991) B2325991
theorem B56587571 : Blo 1451545 56587571 := bstep (se 1 (by rfl) ⟨42440678, by rfl⟩ : syracuseStep 56587571 = 84881357) B84881357
theorem B5232295 : Blo 1451545 5232295 := bstep (se 1 (by rfl) ⟨3924221, by rfl⟩ : syracuseStep 5232295 = 7848443) B7848443
theorem B35796691 : Blo 1451545 35796691 := bstep (se 1 (by rfl) ⟨26847518, by rfl⟩ : syracuseStep 35796691 = 53695037) B53695037
theorem B23566087 : Blo 1451545 23566087 := bstep (se 1 (by rfl) ⟨17674565, by rfl⟩ : syracuseStep 23566087 = 35349131) B35349131
theorem B3266387 : Blo 1451545 3266387 := bstep (se 1 (by rfl) ⟨2449790, by rfl⟩ : syracuseStep 3266387 = 4899581) B4899581
theorem B3676063 : Blo 1451545 3676063 := bstep (se 1 (by rfl) ⟨2757047, by rfl⟩ : syracuseStep 3676063 = 5514095) B5514095
theorem B94197917 : Blo 1451545 94197917 := bstep (se 3 (by rfl) ⟨17662109, by rfl⟩ : syracuseStep 94197917 = 35324219) B35324219
theorem B16767161 : Blo 1451545 16767161 := bstep (se 2 (by rfl) ⟨6287685, by rfl⟩ : syracuseStep 16767161 = 12575371) B12575371
theorem B3266873 : Blo 1451545 3266873 := bstep (se 2 (by rfl) ⟨1225077, by rfl⟩ : syracuseStep 3266873 = 2450155) B2450155
theorem B8272327 : Blo 1451545 8272327 := bstep (se 1 (by rfl) ⟨6204245, by rfl⟩ : syracuseStep 8272327 = 12408491) B12408491
theorem B2177627 : Blo 1451545 2177627 := bstep (se 1 (by rfl) ⟨1633220, by rfl⟩ : syracuseStep 2177627 = 3266441) B3266441
theorem B4135607 : Blo 1451545 4135607 := bstep (se 1 (by rfl) ⟨3101705, by rfl⟩ : syracuseStep 4135607 = 6203411) B6203411
theorem B2177771 : Blo 1451545 2177771 := bstep (se 1 (by rfl) ⟨1633328, by rfl⟩ : syracuseStep 2177771 = 3266657) B3266657
theorem B2177801 : Blo 1451545 2177801 := bstep (se 2 (by rfl) ⟨816675, by rfl⟩ : syracuseStep 2177801 = 1633351) B1633351
theorem B3676985 : Blo 1451545 3676985 := bstep (se 2 (by rfl) ⟨1378869, by rfl⟩ : syracuseStep 3676985 = 2757739) B2757739
theorem B23550983 : Blo 1451545 23550983 := bstep (se 1 (by rfl) ⟨17663237, by rfl⟩ : syracuseStep 23550983 = 35326475) B35326475
theorem B3267791 : Blo 1451545 3267791 := bstep (se 1 (by rfl) ⟨2450843, by rfl⟩ : syracuseStep 3267791 = 4901687) B4901687
theorem B5889257 : Blo 1451545 5889257 := bstep (se 2 (by rfl) ⟨2208471, by rfl⟩ : syracuseStep 5889257 = 4416943) B4416943
theorem B17898745 : Blo 1451545 17898745 := bstep (se 2 (by rfl) ⟨6712029, by rfl⟩ : syracuseStep 17898745 = 13424059) B13424059
theorem B22363465 : Blo 1451545 22363465 := bstep (se 2 (by rfl) ⟨8386299, by rfl⟩ : syracuseStep 22363465 = 16772599) B16772599
theorem B7355771 : Blo 1451545 7355771 := bstep (se 1 (by rfl) ⟨5516828, by rfl⟩ : syracuseStep 7355771 = 11033657) B11033657
theorem B3268169 : Blo 1451545 3268169 := bstep (se 2 (by rfl) ⟨1225563, by rfl⟩ : syracuseStep 3268169 = 2451127) B2451127
theorem B2178671 : Blo 1451545 2178671 := bstep (se 1 (by rfl) ⟨1634003, by rfl⟩ : syracuseStep 2178671 = 3268007) B3268007
theorem B8273603 : Blo 1451545 8273603 := bstep (se 1 (by rfl) ⟨6205202, by rfl⟩ : syracuseStep 8273603 = 12410405) B12410405
theorem B1572571 : Blo 1451545 1572571 := bstep (se 1 (by rfl) ⟨1179428, by rfl⟩ : syracuseStep 1572571 = 2358857) B2358857
theorem B2326247 : Blo 1451545 2326247 := bstep (se 1 (by rfl) ⟨1744685, by rfl⟩ : syracuseStep 2326247 = 3489371) B3489371
theorem B2178791 : Blo 1451545 2178791 := bstep (se 1 (by rfl) ⟨1634093, by rfl⟩ : syracuseStep 2178791 = 3268187) B3268187
theorem B8273785 : Blo 1451545 8273785 := bstep (se 2 (by rfl) ⟨3102669, by rfl⟩ : syracuseStep 8273785 = 6205339) B6205339
theorem B2178983 : Blo 1451545 2178983 := bstep (se 1 (by rfl) ⟨1634237, by rfl⟩ : syracuseStep 2178983 = 3268475) B3268475
theorem B2179241 : Blo 1451545 2179241 := bstep (se 2 (by rfl) ⟨817215, by rfl⟩ : syracuseStep 2179241 = 1634431) B1634431
theorem B2179559 : Blo 1451545 2179559 := bstep (se 1 (by rfl) ⟨1634669, by rfl⟩ : syracuseStep 2179559 = 3269339) B3269339
theorem B2179835 : Blo 1451545 2179835 := bstep (se 1 (by rfl) ⟨1634876, by rfl⟩ : syracuseStep 2179835 = 3269753) B3269753
theorem B37725047 : Blo 1451545 37725047 := bstep (se 1 (by rfl) ⟨28293785, by rfl⟩ : syracuseStep 37725047 = 56587571) B56587571
theorem B2180279 : Blo 1451545 2180279 := bstep (se 1 (by rfl) ⟨1635209, by rfl⟩ : syracuseStep 2180279 = 3270419) B3270419
theorem B7357715 : Blo 1451545 7357715 := bstep (se 1 (by rfl) ⟨5518286, by rfl⟩ : syracuseStep 7357715 = 11036573) B11036573
theorem B4654415 : Blo 1451545 4654415 := bstep (se 1 (by rfl) ⟨3490811, by rfl⟩ : syracuseStep 4654415 = 6981623) B6981623
theorem B2450857 : Blo 1451545 2450857 := bstep (se 2 (by rfl) ⟨919071, by rfl⟩ : syracuseStep 2450857 = 1838143) B1838143
theorem B2328041 : Blo 1451545 2328041 := bstep (se 2 (by rfl) ⟨873015, by rfl⟩ : syracuseStep 2328041 = 1746031) B1746031
theorem B11945531 : Blo 1451545 11945531 := bstep (se 1 (by rfl) ⟨8959148, by rfl⟩ : syracuseStep 11945531 = 17918297) B17918297
theorem B23864993 : Blo 1451545 23864993 := bstep (se 2 (by rfl) ⟨8949372, by rfl⟩ : syracuseStep 23864993 = 17898745) B17898745
theorem B1451751 : Blo 1451545 1451751 := bstep (se 1 (by rfl) ⟨1088813, by rfl⟩ : syracuseStep 1451751 = 2177627) B2177627
theorem B1451847 : Blo 1451545 1451847 := bstep (se 1 (by rfl) ⟨1088885, by rfl⟩ : syracuseStep 1451847 = 2177771) B2177771
theorem B1451867 : Blo 1451545 1451867 := bstep (se 1 (by rfl) ⟨1088900, by rfl⟩ : syracuseStep 1451867 = 2177801) B2177801
theorem B2451323 : Blo 1451545 2451323 := bstep (se 1 (by rfl) ⟨1838492, by rfl⟩ : syracuseStep 2451323 = 3676985) B3676985
theorem B39749615 : Blo 1451545 39749615 := bstep (se 1 (by rfl) ⟨29812211, by rfl⟩ : syracuseStep 39749615 = 59624423) B59624423
theorem B12584969 : Blo 1451545 12584969 := bstep (se 2 (by rfl) ⟨4719363, by rfl⟩ : syracuseStep 12584969 = 9438727) B9438727
theorem B2451593 : Blo 1451545 2451593 := bstep (se 2 (by rfl) ⟨919347, by rfl⟩ : syracuseStep 2451593 = 1838695) B1838695
theorem B3926171 : Blo 1451545 3926171 := bstep (se 1 (by rfl) ⟨2944628, by rfl⟩ : syracuseStep 3926171 = 5889257) B5889257
theorem B47728921 : Blo 1451545 47728921 := bstep (se 2 (by rfl) ⟨17898345, by rfl⟩ : syracuseStep 47728921 = 35796691) B35796691
theorem B1452447 : Blo 1451545 1452447 := bstep (se 1 (by rfl) ⟨1089335, by rfl⟩ : syracuseStep 1452447 = 2178671) B2178671
theorem B5515735 : Blo 1451545 5515735 := bstep (se 1 (by rfl) ⟨4136801, by rfl⟩ : syracuseStep 5515735 = 8273603) B8273603
theorem B1550831 : Blo 1451545 1550831 := bstep (se 1 (by rfl) ⟨1163123, by rfl⟩ : syracuseStep 1550831 = 2326247) B2326247
theorem B1452527 : Blo 1451545 1452527 := bstep (se 1 (by rfl) ⟨1089395, by rfl⟩ : syracuseStep 1452527 = 2178791) B2178791
theorem B4901417 : Blo 1451545 4901417 := bstep (se 2 (by rfl) ⟨1838031, by rfl⟩ : syracuseStep 4901417 = 3676063) B3676063
theorem B1452655 : Blo 1451545 1452655 := bstep (se 1 (by rfl) ⟨1089491, by rfl⟩ : syracuseStep 1452655 = 2178983) B2178983
theorem B2615969 : Blo 1451545 2615969 := bstep (se 2 (by rfl) ⟨980988, by rfl⟩ : syracuseStep 2615969 = 1961977) B1961977
theorem B67095215 : Blo 1451545 67095215 := bstep (se 1 (by rfl) ⟨50321411, by rfl⟩ : syracuseStep 67095215 = 100642823) B100642823
theorem B1452871 : Blo 1451545 1452871 := bstep (se 1 (by rfl) ⟨1089653, by rfl⟩ : syracuseStep 1452871 = 2179307) B2179307
theorem B1452911 : Blo 1451545 1452911 := bstep (se 1 (by rfl) ⟨1089683, by rfl⟩ : syracuseStep 1452911 = 2179367) B2179367
theorem B1837991 : Blo 1451545 1837991 := bstep (se 1 (by rfl) ⟨1378493, by rfl⟩ : syracuseStep 1837991 = 2756987) B2756987
theorem B5516221 : Blo 1451545 5516221 := bstep (se 3 (by rfl) ⟨1034291, by rfl⟩ : syracuseStep 5516221 = 2068583) B2068583
theorem B9309239 : Blo 1451545 9309239 := bstep (se 1 (by rfl) ⟨6981929, by rfl⟩ : syracuseStep 9309239 = 13963859) B13963859
theorem B2067547 : Blo 1451545 2067547 := bstep (se 1 (by rfl) ⟨1550660, by rfl⟩ : syracuseStep 2067547 = 3101321) B3101321
theorem B11029769 : Blo 1451545 11029769 := bstep (se 2 (by rfl) ⟨4136163, by rfl⟩ : syracuseStep 11029769 = 8272327) B8272327
theorem B1453359 : Blo 1451545 1453359 := bstep (se 1 (by rfl) ⟨1090019, by rfl⟩ : syracuseStep 1453359 = 2180039) B2180039
theorem B2239903 : Blo 1451545 2239903 := bstep (se 1 (by rfl) ⟨1679927, by rfl⟩ : syracuseStep 2239903 = 3359855) B3359855
theorem B1453471 : Blo 1451545 1453471 := bstep (se 1 (by rfl) ⟨1090103, by rfl⟩ : syracuseStep 1453471 = 2180207) B2180207
theorem B7351721 : Blo 1451545 7351721 := bstep (se 2 (by rfl) ⟨2756895, by rfl⟩ : syracuseStep 7351721 = 5513791) B5513791
theorem B27905573 : Blo 1451545 27905573 := bstep (se 4 (by rfl) ⟨2616147, by rfl⟩ : syracuseStep 27905573 = 5232295) B5232295
theorem B25169705 : Blo 1451545 25169705 := bstep (se 2 (by rfl) ⟨9438639, by rfl⟩ : syracuseStep 25169705 = 18877279) B18877279
theorem B7352207 : Blo 1451545 7352207 := bstep (se 1 (by rfl) ⟨5514155, by rfl⟩ : syracuseStep 7352207 = 11028311) B11028311
theorem B27938789 : Blo 1451545 27938789 := bstep (se 4 (by rfl) ⟨2619261, by rfl⟩ : syracuseStep 27938789 = 5238523) B5238523
theorem B11178107 : Blo 1451545 11178107 := bstep (se 1 (by rfl) ⟨8383580, by rfl⟩ : syracuseStep 11178107 = 16767161) B16767161
theorem B5517497 : Blo 1451545 5517497 := bstep (se 2 (by rfl) ⟨2069061, by rfl⟩ : syracuseStep 5517497 = 4138123) B4138123
theorem B5517679 : Blo 1451545 5517679 := bstep (se 1 (by rfl) ⟨4138259, by rfl⟩ : syracuseStep 5517679 = 8276519) B8276519
theorem B25506251 : Blo 1451545 25506251 := bstep (se 1 (by rfl) ⟨19129688, by rfl⟩ : syracuseStep 25506251 = 38259377) B38259377
theorem B2757071 : Blo 1451545 2757071 := bstep (se 1 (by rfl) ⟨2067803, by rfl⟩ : syracuseStep 2757071 = 4135607) B4135607
theorem B31429241 : Blo 1451545 31429241 := bstep (se 2 (by rfl) ⟨11785965, by rfl⟩ : syracuseStep 31429241 = 23571931) B23571931
theorem B15700655 : Blo 1451545 15700655 := bstep (se 1 (by rfl) ⟨11775491, by rfl⟩ : syracuseStep 15700655 = 23550983) B23550983
theorem B2945819 : Blo 1451545 2945819 := bstep (se 1 (by rfl) ⟨2209364, by rfl⟩ : syracuseStep 2945819 = 4418729) B4418729
theorem B4903847 : Blo 1451545 4903847 := bstep (se 1 (by rfl) ⟨3677885, by rfl⟩ : syracuseStep 4903847 = 7355771) B7355771
theorem B14914529 : Blo 1451545 14914529 := bstep (se 2 (by rfl) ⟨5592948, by rfl⟩ : syracuseStep 14914529 = 11185897) B11185897
theorem B31421449 : Blo 1451545 31421449 := bstep (se 2 (by rfl) ⟨11783043, by rfl⟩ : syracuseStep 31421449 = 23566087) B23566087
theorem B11031713 : Blo 1451545 11031713 := bstep (se 2 (by rfl) ⟨4136892, by rfl⟩ : syracuseStep 11031713 = 8273785) B8273785
theorem B27907577 : Blo 1451545 27907577 := bstep (se 2 (by rfl) ⟨10465341, by rfl⟩ : syracuseStep 27907577 = 20930683) B20930683
theorem B16766513 : Blo 1451545 16766513 := bstep (se 2 (by rfl) ⟨6287442, by rfl⟩ : syracuseStep 16766513 = 12574885) B12574885
theorem B16545383 : Blo 1451545 16545383 := bstep (se 1 (by rfl) ⟨12409037, by rfl⟩ : syracuseStep 16545383 = 24818075) B24818075
theorem B3266153 : Blo 1451545 3266153 := bstep (se 2 (by rfl) ⟨1224807, by rfl⟩ : syracuseStep 3266153 = 2449615) B2449615
theorem B6207101 : Blo 1451545 6207101 := bstep (se 3 (by rfl) ⟨1163831, by rfl⟩ : syracuseStep 6207101 = 2327663) B2327663
theorem B7853723 : Blo 1451545 7853723 := bstep (se 1 (by rfl) ⟨5890292, by rfl⟩ : syracuseStep 7853723 = 11780585) B11780585
theorem B2758369 : Blo 1451545 2758369 := bstep (se 2 (by rfl) ⟨1034388, by rfl⟩ : syracuseStep 2758369 = 2068777) B2068777
theorem B4904711 : Blo 1451545 4904711 := bstep (se 1 (by rfl) ⟨3678533, by rfl⟩ : syracuseStep 4904711 = 7357067) B7357067
theorem B44742689 : Blo 1451545 44742689 := bstep (se 2 (by rfl) ⟨16778508, by rfl⟩ : syracuseStep 44742689 = 33557017) B33557017
theorem B3266783 : Blo 1451545 3266783 := bstep (se 1 (by rfl) ⟨2450087, by rfl⟩ : syracuseStep 3266783 = 4900175) B4900175
theorem B3266855 : Blo 1451545 3266855 := bstep (se 1 (by rfl) ⟨2450141, by rfl⟩ : syracuseStep 3266855 = 4900283) B4900283
theorem B3676499 : Blo 1451545 3676499 := bstep (se 1 (by rfl) ⟨2757374, by rfl⟩ : syracuseStep 3676499 = 5514749) B5514749
theorem B2177417 : Blo 1451545 2177417 := bstep (se 2 (by rfl) ⟨816531, by rfl⟩ : syracuseStep 2177417 = 1633063) B1633063
theorem B14899621 : Blo 1451545 14899621 := bstep (se 4 (by rfl) ⟨1396839, by rfl⟩ : syracuseStep 14899621 = 2793679) B2793679
theorem B2177591 : Blo 1451545 2177591 := bstep (se 1 (by rfl) ⟨1633193, by rfl⟩ : syracuseStep 2177591 = 3266387) B3266387
theorem B13425209 : Blo 1451545 13425209 := bstep (se 2 (by rfl) ⟨5034453, by rfl⟩ : syracuseStep 13425209 = 10068907) B10068907
theorem B3267215 : Blo 1451545 3267215 := bstep (se 1 (by rfl) ⟨2450411, by rfl⟩ : syracuseStep 3267215 = 4900823) B4900823
theorem B9943697 : Blo 1451545 9943697 := bstep (se 2 (by rfl) ⟨3728886, by rfl⟩ : syracuseStep 9943697 = 7457773) B7457773
theorem B3267305 : Blo 1451545 3267305 := bstep (se 2 (by rfl) ⟨1225239, by rfl⟩ : syracuseStep 3267305 = 2450479) B2450479
theorem B13966091 : Blo 1451545 13966091 := bstep (se 1 (by rfl) ⟨10474568, by rfl⟩ : syracuseStep 13966091 = 20949137) B20949137
theorem B62798611 : Blo 1451545 62798611 := bstep (se 1 (by rfl) ⟨47098958, by rfl⟩ : syracuseStep 62798611 = 94197917) B94197917
theorem B2177915 : Blo 1451545 2177915 := bstep (se 1 (by rfl) ⟨1633436, by rfl⟩ : syracuseStep 2177915 = 3266873) B3266873
theorem B6200351 : Blo 1451545 6200351 := bstep (se 1 (by rfl) ⟨4650263, by rfl⟩ : syracuseStep 6200351 = 9300527) B9300527
theorem B29817953 : Blo 1451545 29817953 := bstep (se 2 (by rfl) ⟨11181732, by rfl⟩ : syracuseStep 29817953 = 22363465) B22363465
theorem B3103849 : Blo 1451545 3103849 := bstep (se 2 (by rfl) ⟨1163943, by rfl⟩ : syracuseStep 3103849 = 2327887) B2327887
theorem B3677359 : Blo 1451545 3677359 := bstep (se 1 (by rfl) ⟨2758019, by rfl⟩ : syracuseStep 3677359 = 5516039) B5516039
theorem B4136255 : Blo 1451545 4136255 := bstep (se 1 (by rfl) ⟨3102191, by rfl⟩ : syracuseStep 4136255 = 6204383) B6204383
theorem B5512637 : Blo 1451545 5512637 := bstep (se 3 (by rfl) ⟨1033619, by rfl⟩ : syracuseStep 5512637 = 2067239) B2067239
theorem B2178527 : Blo 1451545 2178527 := bstep (se 1 (by rfl) ⟨1633895, by rfl⟩ : syracuseStep 2178527 = 3267791) B3267791
theorem B36789835 : Blo 1451545 36789835 := bstep (se 1 (by rfl) ⟨27592376, by rfl⟩ : syracuseStep 36789835 = 55184753) B55184753
theorem B2096761 : Blo 1451545 2096761 := bstep (se 2 (by rfl) ⟨786285, by rfl⟩ : syracuseStep 2096761 = 1572571) B1572571
theorem B2178779 : Blo 1451545 2178779 := bstep (se 1 (by rfl) ⟨1634084, by rfl⟩ : syracuseStep 2178779 = 3268169) B3268169
theorem B7356257 : Blo 1451545 7356257 := bstep (se 2 (by rfl) ⟨2758596, by rfl⟩ : syracuseStep 7356257 = 5517193) B5517193
theorem B2179049 : Blo 1451545 2179049 := bstep (se 2 (by rfl) ⟨817143, by rfl⟩ : syracuseStep 2179049 = 1634287) B1634287
theorem B7659503 : Blo 1451545 7659503 := bstep (se 1 (by rfl) ⟨5744627, by rfl⟩ : syracuseStep 7659503 = 11489255) B11489255
theorem B3678331 : Blo 1451545 3678331 := bstep (se 1 (by rfl) ⟨2758748, by rfl⟩ : syracuseStep 3678331 = 5517497) B5517497
theorem B7356905 : Blo 1451545 7356905 := bstep (se 2 (by rfl) ⟨2758839, by rfl⟩ : syracuseStep 7356905 = 5517679) B5517679
theorem B19866161 : Blo 1451545 19866161 := bstep (se 2 (by rfl) ⟨7449810, by rfl⟩ : syracuseStep 19866161 = 14899621) B14899621
theorem B25150031 : Blo 1451545 25150031 := bstep (se 1 (by rfl) ⟨18862523, by rfl⟩ : syracuseStep 25150031 = 37725047) B37725047
theorem B3269231 : Blo 1451545 3269231 := bstep (se 1 (by rfl) ⟨2451923, by rfl⟩ : syracuseStep 3269231 = 4903847) B4903847
theorem B18605051 : Blo 1451545 18605051 := bstep (se 1 (by rfl) ⟨13953788, by rfl⟩ : syracuseStep 18605051 = 27907577) B27907577
theorem B83731481 : Blo 1451545 83731481 := bstep (se 2 (by rfl) ⟨31399305, by rfl⟩ : syracuseStep 83731481 = 62798611) B62798611
theorem B7963687 : Blo 1451545 7963687 := bstep (se 1 (by rfl) ⟨5972765, by rfl⟩ : syracuseStep 7963687 = 11945531) B11945531
theorem B4138067 : Blo 1451545 4138067 := bstep (se 1 (by rfl) ⟨3103550, by rfl⟩ : syracuseStep 4138067 = 6207101) B6207101
theorem B5235815 : Blo 1451545 5235815 := bstep (se 1 (by rfl) ⟨3926861, by rfl⟩ : syracuseStep 5235815 = 7853723) B7853723
theorem B15909995 : Blo 1451545 15909995 := bstep (se 1 (by rfl) ⟨11932496, by rfl⟩ : syracuseStep 15909995 = 23864993) B23864993
theorem B3269807 : Blo 1451545 3269807 := bstep (se 1 (by rfl) ⟨2452355, by rfl⟩ : syracuseStep 3269807 = 4904711) B4904711
theorem B8389979 : Blo 1451545 8389979 := bstep (se 1 (by rfl) ⟨6292484, by rfl⟩ : syracuseStep 8389979 = 12584969) B12584969
theorem B41895265 : Blo 1451545 41895265 := bstep (se 2 (by rfl) ⟨15710724, by rfl⟩ : syracuseStep 41895265 = 31421449) B31421449
theorem B29828459 : Blo 1451545 29828459 := bstep (se 1 (by rfl) ⟨22371344, by rfl⟩ : syracuseStep 29828459 = 44742689) B44742689
theorem B4138465 : Blo 1451545 4138465 := bstep (se 2 (by rfl) ⟨1551924, by rfl⟩ : syracuseStep 4138465 = 3103849) B3103849
theorem B2450999 : Blo 1451545 2450999 := bstep (se 1 (by rfl) ⟨1838249, by rfl⟩ : syracuseStep 2450999 = 3676499) B3676499
theorem B1451611 : Blo 1451545 1451611 := bstep (se 1 (by rfl) ⟨1088708, by rfl⟩ : syracuseStep 1451611 = 2177417) B2177417
theorem B1451727 : Blo 1451545 1451727 := bstep (se 1 (by rfl) ⟨1088795, by rfl⟩ : syracuseStep 1451727 = 2177591) B2177591
theorem B6629131 : Blo 1451545 6629131 := bstep (se 1 (by rfl) ⟨4971848, by rfl⟩ : syracuseStep 6629131 = 9943697) B9943697
theorem B44730143 : Blo 1451545 44730143 := bstep (se 1 (by rfl) ⟨33547607, by rfl⟩ : syracuseStep 44730143 = 67095215) B67095215
theorem B1451943 : Blo 1451545 1451943 := bstep (se 1 (by rfl) ⟨1088957, by rfl⟩ : syracuseStep 1451943 = 2177915) B2177915
theorem B2795681 : Blo 1451545 2795681 := bstep (se 2 (by rfl) ⟨1048380, by rfl⟩ : syracuseStep 2795681 = 2096761) B2096761
theorem B4901147 : Blo 1451545 4901147 := bstep (se 1 (by rfl) ⟨3675860, by rfl⟩ : syracuseStep 4901147 = 7351721) B7351721
theorem B1452351 : Blo 1451545 1452351 := bstep (se 1 (by rfl) ⟨1089263, by rfl⟩ : syracuseStep 1452351 = 2178527) B2178527
theorem B4901309 : Blo 1451545 4901309 := bstep (se 3 (by rfl) ⟨918995, by rfl⟩ : syracuseStep 4901309 = 1837991) B1837991
theorem B1452519 : Blo 1451545 1452519 := bstep (se 1 (by rfl) ⟨1089389, by rfl⟩ : syracuseStep 1452519 = 2178779) B2178779
theorem B16779803 : Blo 1451545 16779803 := bstep (se 1 (by rfl) ⟨12584852, by rfl⟩ : syracuseStep 16779803 = 25169705) B25169705
theorem B4901471 : Blo 1451545 4901471 := bstep (se 1 (by rfl) ⟨3676103, by rfl⟩ : syracuseStep 4901471 = 7352207) B7352207
theorem B1452699 : Blo 1451545 1452699 := bstep (se 1 (by rfl) ⟨1089524, by rfl⟩ : syracuseStep 1452699 = 2179049) B2179049
theorem B5106335 : Blo 1451545 5106335 := bstep (se 1 (by rfl) ⟨3829751, by rfl⟩ : syracuseStep 5106335 = 7659503) B7659503
theorem B1452827 : Blo 1451545 1452827 := bstep (se 1 (by rfl) ⟨1089620, by rfl⟩ : syracuseStep 1452827 = 2179241) B2179241
theorem B1838047 : Blo 1451545 1838047 := bstep (se 1 (by rfl) ⟨1378535, by rfl⟩ : syracuseStep 1838047 = 2757071) B2757071
theorem B1453039 : Blo 1451545 1453039 := bstep (se 1 (by rfl) ⟨1089779, by rfl⟩ : syracuseStep 1453039 = 2179559) B2179559
theorem B63638561 : Blo 1451545 63638561 := bstep (se 2 (by rfl) ⟨23864460, by rfl⟩ : syracuseStep 63638561 = 47728921) B47728921
theorem B1453223 : Blo 1451545 1453223 := bstep (se 1 (by rfl) ⟨1089917, by rfl⟩ : syracuseStep 1453223 = 2179835) B2179835
theorem B1453519 : Blo 1451545 1453519 := bstep (se 1 (by rfl) ⟨1090139, by rfl⟩ : syracuseStep 1453519 = 2180279) B2180279
theorem B11177675 : Blo 1451545 11177675 := bstep (se 1 (by rfl) ⟨8383256, by rfl⟩ : syracuseStep 11177675 = 16766513) B16766513
theorem B11030255 : Blo 1451545 11030255 := bstep (se 1 (by rfl) ⟨8272691, by rfl⟩ : syracuseStep 11030255 = 16545383) B16545383
theorem B1634215 : Blo 1451545 1634215 := bstep (se 1 (by rfl) ⟨1225661, by rfl⟩ : syracuseStep 1634215 = 2451323) B2451323
theorem B1634395 : Blo 1451545 1634395 := bstep (se 1 (by rfl) ⟨1225796, by rfl⟩ : syracuseStep 1634395 = 2451593) B2451593
theorem B2617447 : Blo 1451545 2617447 := bstep (se 1 (by rfl) ⟨1963085, by rfl⟩ : syracuseStep 2617447 = 3926171) B3926171
theorem B2756729 : Blo 1451545 2756729 := bstep (se 2 (by rfl) ⟨1033773, by rfl⟩ : syracuseStep 2756729 = 2067547) B2067547
theorem B4903145 : Blo 1451545 4903145 := bstep (se 2 (by rfl) ⟨1838679, by rfl⟩ : syracuseStep 4903145 = 3677359) B3677359
theorem B8950139 : Blo 1451545 8950139 := bstep (se 1 (by rfl) ⟨6712604, by rfl⟩ : syracuseStep 8950139 = 13425209) B13425209
theorem B9310727 : Blo 1451545 9310727 := bstep (se 1 (by rfl) ⟨6983045, by rfl⟩ : syracuseStep 9310727 = 13966091) B13966091
theorem B2986537 : Blo 1451545 2986537 := bstep (se 2 (by rfl) ⟨1119951, by rfl⟩ : syracuseStep 2986537 = 2239903) B2239903
theorem B4133567 : Blo 1451545 4133567 := bstep (se 1 (by rfl) ⟨3100175, by rfl⟩ : syracuseStep 4133567 = 6200351) B6200351
theorem B6206159 : Blo 1451545 6206159 := bstep (se 1 (by rfl) ⟨4654619, by rfl⟩ : syracuseStep 6206159 = 9309239) B9309239
theorem B19878635 : Blo 1451545 19878635 := bstep (se 1 (by rfl) ⟨14908976, by rfl⟩ : syracuseStep 19878635 = 29817953) B29817953
theorem B7353179 : Blo 1451545 7353179 := bstep (se 1 (by rfl) ⟨5514884, by rfl⟩ : syracuseStep 7353179 = 11029769) B11029769
theorem B2757503 : Blo 1451545 2757503 := bstep (se 1 (by rfl) ⟨2068127, by rfl⟩ : syracuseStep 2757503 = 4136255) B4136255
theorem B3675091 : Blo 1451545 3675091 := bstep (se 1 (by rfl) ⟨2756318, by rfl⟩ : syracuseStep 3675091 = 5512637) B5512637
theorem B4904171 : Blo 1451545 4904171 := bstep (se 1 (by rfl) ⟨3678128, by rfl⟩ : syracuseStep 4904171 = 7356257) B7356257
theorem B18625859 : Blo 1451545 18625859 := bstep (se 1 (by rfl) ⟨13969394, by rfl⟩ : syracuseStep 18625859 = 27938789) B27938789
theorem B7452071 : Blo 1451545 7452071 := bstep (se 1 (by rfl) ⟨5589053, by rfl⟩ : syracuseStep 7452071 = 11178107) B11178107
theorem B17004167 : Blo 1451545 17004167 := bstep (se 1 (by rfl) ⟨12753125, by rfl⟩ : syracuseStep 17004167 = 25506251) B25506251
theorem B20952827 : Blo 1451545 20952827 := bstep (se 1 (by rfl) ⟨15714620, by rfl⟩ : syracuseStep 20952827 = 31429241) B31429241
theorem B10467103 : Blo 1451545 10467103 := bstep (se 1 (by rfl) ⟨7850327, by rfl⟩ : syracuseStep 10467103 = 15700655) B15700655
theorem B7354313 : Blo 1451545 7354313 := bstep (se 2 (by rfl) ⟨2757867, by rfl⟩ : syracuseStep 7354313 = 5515735) B5515735
theorem B9943019 : Blo 1451545 9943019 := bstep (se 1 (by rfl) ⟨7457264, by rfl⟩ : syracuseStep 9943019 = 14914529) B14914529
theorem B7354475 : Blo 1451545 7354475 := bstep (se 1 (by rfl) ⟨5515856, by rfl⟩ : syracuseStep 7354475 = 11031713) B11031713
theorem B4905143 : Blo 1451545 4905143 := bstep (se 1 (by rfl) ⟨3678857, by rfl⟩ : syracuseStep 4905143 = 7357715) B7357715
theorem B3102943 : Blo 1451545 3102943 := bstep (se 1 (by rfl) ⟨2327207, by rfl⟩ : syracuseStep 3102943 = 4654415) B4654415
theorem B2177435 : Blo 1451545 2177435 := bstep (se 1 (by rfl) ⟨1633076, by rfl⟩ : syracuseStep 2177435 = 3266153) B3266153
theorem B7354961 : Blo 1451545 7354961 := bstep (se 2 (by rfl) ⟨2758110, by rfl⟩ : syracuseStep 7354961 = 5516221) B5516221
theorem B6208109 : Blo 1451545 6208109 := bstep (se 3 (by rfl) ⟨1164020, by rfl⟩ : syracuseStep 6208109 = 2328041) B2328041
theorem B4135549 : Blo 1451545 4135549 := bstep (se 3 (by rfl) ⟨775415, by rfl⟩ : syracuseStep 4135549 = 1550831) B1550831
theorem B26499743 : Blo 1451545 26499743 := bstep (se 1 (by rfl) ⟨19874807, by rfl⟩ : syracuseStep 26499743 = 39749615) B39749615
theorem B2177855 : Blo 1451545 2177855 := bstep (se 1 (by rfl) ⟨1633391, by rfl⟩ : syracuseStep 2177855 = 3266783) B3266783
theorem B2177903 : Blo 1451545 2177903 := bstep (se 1 (by rfl) ⟨1633427, by rfl⟩ : syracuseStep 2177903 = 3266855) B3266855
theorem B3267611 : Blo 1451545 3267611 := bstep (se 1 (by rfl) ⟨2450708, by rfl⟩ : syracuseStep 3267611 = 4901417) B4901417
theorem B2178143 : Blo 1451545 2178143 := bstep (se 1 (by rfl) ⟨1633607, by rfl⟩ : syracuseStep 2178143 = 3267215) B3267215
theorem B1743979 : Blo 1451545 1743979 := bstep (se 1 (by rfl) ⟨1307984, by rfl⟩ : syracuseStep 1743979 = 2615969) B2615969
theorem B2178203 : Blo 1451545 2178203 := bstep (se 1 (by rfl) ⟨1633652, by rfl⟩ : syracuseStep 2178203 = 3267305) B3267305
theorem B3267809 : Blo 1451545 3267809 := bstep (se 2 (by rfl) ⟨1225428, by rfl⟩ : syracuseStep 3267809 = 2450857) B2450857
theorem B7855517 : Blo 1451545 7855517 := bstep (se 3 (by rfl) ⟨1472909, by rfl⟩ : syracuseStep 7855517 = 2945819) B2945819
theorem B49053113 : Blo 1451545 49053113 := bstep (se 2 (by rfl) ⟨18394917, by rfl⟩ : syracuseStep 49053113 = 36789835) B36789835
theorem B3677825 : Blo 1451545 3677825 := bstep (se 2 (by rfl) ⟨1379184, by rfl⟩ : syracuseStep 3677825 = 2758369) B2758369
theorem B18603715 : Blo 1451545 18603715 := bstep (se 1 (by rfl) ⟨13952786, by rfl⟩ : syracuseStep 18603715 = 27905573) B27905573
theorem B2179193 : Blo 1451545 2179193 := bstep (se 2 (by rfl) ⟨817197, by rfl⟩ : syracuseStep 2179193 = 1634395) B1634395
theorem B3489929 : Blo 1451545 3489929 := bstep (se 2 (by rfl) ⟨1308723, by rfl⟩ : syracuseStep 3489929 = 2617447) B2617447
theorem B3268763 : Blo 1451545 3268763 := bstep (se 1 (by rfl) ⟨2451572, by rfl⟩ : syracuseStep 3268763 = 4903145) B4903145
theorem B4137257 : Blo 1451545 4137257 := bstep (se 2 (by rfl) ⟨1551471, by rfl⟩ : syracuseStep 4137257 = 3102943) B3102943
theorem B2179487 : Blo 1451545 2179487 := bstep (se 1 (by rfl) ⟨1634615, by rfl⟩ : syracuseStep 2179487 = 3269231) B3269231
theorem B7455149 : Blo 1451545 7455149 := bstep (se 3 (by rfl) ⟨1397840, by rfl⟩ : syracuseStep 7455149 = 2795681) B2795681
theorem B12403367 : Blo 1451545 12403367 := bstep (se 1 (by rfl) ⟨9302525, by rfl⟩ : syracuseStep 12403367 = 18605051) B18605051
theorem B55820987 : Blo 1451545 55820987 := bstep (se 1 (by rfl) ⟨41865740, by rfl⟩ : syracuseStep 55820987 = 83731481) B83731481
theorem B3982049 : Blo 1451545 3982049 := bstep (se 2 (by rfl) ⟨1493268, by rfl⟩ : syracuseStep 3982049 = 2986537) B2986537
theorem B3490543 : Blo 1451545 3490543 := bstep (se 1 (by rfl) ⟨2617907, by rfl⟩ : syracuseStep 3490543 = 5235815) B5235815
theorem B2179871 : Blo 1451545 2179871 := bstep (se 1 (by rfl) ⟨1634903, by rfl⟩ : syracuseStep 2179871 = 3269807) B3269807
theorem B3269447 : Blo 1451545 3269447 := bstep (se 1 (by rfl) ⟨2452085, by rfl⟩ : syracuseStep 3269447 = 4904171) B4904171
theorem B5514065 : Blo 1451545 5514065 := bstep (se 2 (by rfl) ⟨2067774, by rfl⟩ : syracuseStep 5514065 = 4135549) B4135549
theorem B13968551 : Blo 1451545 13968551 := bstep (se 1 (by rfl) ⟨10476413, by rfl⟩ : syracuseStep 13968551 = 20952827) B20952827
theorem B29820095 : Blo 1451545 29820095 := bstep (se 1 (by rfl) ⟨22365071, by rfl⟩ : syracuseStep 29820095 = 44730143) B44730143
theorem B4900121 : Blo 1451545 4900121 := bstep (se 2 (by rfl) ⟨1837545, by rfl⟩ : syracuseStep 4900121 = 3675091) B3675091
theorem B2450729 : Blo 1451545 2450729 := bstep (se 2 (by rfl) ⟨919023, by rfl⟩ : syracuseStep 2450729 = 1838047) B1838047
theorem B6628679 : Blo 1451545 6628679 := bstep (se 1 (by rfl) ⟨4971509, by rfl⟩ : syracuseStep 6628679 = 9943019) B9943019
theorem B44746141 : Blo 1451545 44746141 := bstep (se 3 (by rfl) ⟨8389901, by rfl⟩ : syracuseStep 44746141 = 16779803) B16779803
theorem B3270095 : Blo 1451545 3270095 := bstep (se 1 (by rfl) ⟨2452571, by rfl⟩ : syracuseStep 3270095 = 4905143) B4905143
theorem B1451623 : Blo 1451545 1451623 := bstep (se 1 (by rfl) ⟨1088717, by rfl⟩ : syracuseStep 1451623 = 2177435) B2177435
theorem B4138739 : Blo 1451545 4138739 := bstep (se 1 (by rfl) ⟨3104054, by rfl⟩ : syracuseStep 4138739 = 6208109) B6208109
theorem B13616893 : Blo 1451545 13616893 := bstep (se 3 (by rfl) ⟨2553167, by rfl⟩ : syracuseStep 13616893 = 5106335) B5106335
theorem B16549757 : Blo 1451545 16549757 := bstep (se 3 (by rfl) ⟨3103079, by rfl⟩ : syracuseStep 16549757 = 6206159) B6206159
theorem B1451903 : Blo 1451545 1451903 := bstep (se 1 (by rfl) ⟨1088927, by rfl⟩ : syracuseStep 1451903 = 2177855) B2177855
theorem B1451935 : Blo 1451545 1451935 := bstep (se 1 (by rfl) ⟨1088951, by rfl⟩ : syracuseStep 1451935 = 2177903) B2177903
theorem B1452095 : Blo 1451545 1452095 := bstep (se 1 (by rfl) ⟨1089071, by rfl⟩ : syracuseStep 1452095 = 2178143) B2178143
theorem B1452135 : Blo 1451545 1452135 := bstep (se 1 (by rfl) ⟨1089101, by rfl⟩ : syracuseStep 1452135 = 2178203) B2178203
theorem B5237011 : Blo 1451545 5237011 := bstep (se 1 (by rfl) ⟨3927758, by rfl⟩ : syracuseStep 5237011 = 7855517) B7855517
theorem B2451883 : Blo 1451545 2451883 := bstep (se 1 (by rfl) ⟨1838912, by rfl⟩ : syracuseStep 2451883 = 3677825) B3677825
theorem B1837819 : Blo 1451545 1837819 := bstep (se 1 (by rfl) ⟨1378364, by rfl⟩ : syracuseStep 1837819 = 2756729) B2756729
theorem B5966759 : Blo 1451545 5966759 := bstep (se 1 (by rfl) ⟨4475069, by rfl⟩ : syracuseStep 5966759 = 8950139) B8950139
theorem B2755711 : Blo 1451545 2755711 := bstep (se 1 (by rfl) ⟨2066783, by rfl⟩ : syracuseStep 2755711 = 4133567) B4133567
theorem B4902119 : Blo 1451545 4902119 := bstep (se 1 (by rfl) ⟨3676589, by rfl⟩ : syracuseStep 4902119 = 7353179) B7353179
theorem B4968047 : Blo 1451545 4968047 := bstep (se 1 (by rfl) ⟨3726035, by rfl⟩ : syracuseStep 4968047 = 7452071) B7452071
theorem B1633999 : Blo 1451545 1633999 := bstep (se 1 (by rfl) ⟨1225499, by rfl⟩ : syracuseStep 1633999 = 2450999) B2450999
theorem B4902875 : Blo 1451545 4902875 := bstep (se 1 (by rfl) ⟨3677156, by rfl⟩ : syracuseStep 4902875 = 7354313) B7354313
theorem B4902983 : Blo 1451545 4902983 := bstep (se 1 (by rfl) ⟨3677237, by rfl⟩ : syracuseStep 4902983 = 7354475) B7354475
theorem B4903307 : Blo 1451545 4903307 := bstep (se 1 (by rfl) ⟨3677480, by rfl⟩ : syracuseStep 4903307 = 7354961) B7354961
theorem B17666495 : Blo 1451545 17666495 := bstep (se 1 (by rfl) ⟨13249871, by rfl⟩ : syracuseStep 17666495 = 26499743) B26499743
theorem B5517953 : Blo 1451545 5517953 := bstep (se 2 (by rfl) ⟨2069232, by rfl⟩ : syracuseStep 5517953 = 4138465) B4138465
theorem B7353341 : Blo 1451545 7353341 := bstep (se 3 (by rfl) ⟨1378751, by rfl⟩ : syracuseStep 7353341 = 2757503) B2757503
theorem B13956137 : Blo 1451545 13956137 := bstep (se 2 (by rfl) ⟨5233551, by rfl⟩ : syracuseStep 13956137 = 10467103) B10467103
theorem B7451783 : Blo 1451545 7451783 := bstep (se 1 (by rfl) ⟨5588837, by rfl⟩ : syracuseStep 7451783 = 11177675) B11177675
theorem B7353503 : Blo 1451545 7353503 := bstep (se 1 (by rfl) ⟨5515127, by rfl⟩ : syracuseStep 7353503 = 11030255) B11030255
theorem B169702829 : Blo 1451545 169702829 := bstep (se 3 (by rfl) ⟨31819280, by rfl⟩ : syracuseStep 169702829 = 63638561) B63638561
theorem B4904441 : Blo 1451545 4904441 := bstep (se 2 (by rfl) ⟨1839165, by rfl⟩ : syracuseStep 4904441 = 3678331) B3678331
theorem B42472997 : Blo 1451545 42472997 := bstep (se 4 (by rfl) ⟨3981843, by rfl⟩ : syracuseStep 42472997 = 7963687) B7963687
theorem B4904603 : Blo 1451545 4904603 := bstep (se 1 (by rfl) ⟨3678452, by rfl⟩ : syracuseStep 4904603 = 7356905) B7356905
theorem B6207151 : Blo 1451545 6207151 := bstep (se 1 (by rfl) ⟨4655363, by rfl⟩ : syracuseStep 6207151 = 9310727) B9310727
theorem B13244107 : Blo 1451545 13244107 := bstep (se 1 (by rfl) ⟨9933080, by rfl⟩ : syracuseStep 13244107 = 19866161) B19866161
theorem B16766687 : Blo 1451545 16766687 := bstep (se 1 (by rfl) ⟨12575015, by rfl⟩ : syracuseStep 16766687 = 25150031) B25150031
theorem B13252423 : Blo 1451545 13252423 := bstep (se 1 (by rfl) ⟨9939317, by rfl⟩ : syracuseStep 13252423 = 19878635) B19878635
theorem B2758711 : Blo 1451545 2758711 := bstep (se 1 (by rfl) ⟨2069033, by rfl⟩ : syracuseStep 2758711 = 4138067) B4138067
theorem B10606663 : Blo 1451545 10606663 := bstep (se 1 (by rfl) ⟨7954997, by rfl⟩ : syracuseStep 10606663 = 15909995) B15909995
theorem B12417239 : Blo 1451545 12417239 := bstep (se 1 (by rfl) ⟨9312929, by rfl⟩ : syracuseStep 12417239 = 18625859) B18625859
theorem B5593319 : Blo 1451545 5593319 := bstep (se 1 (by rfl) ⟨4194989, by rfl⟩ : syracuseStep 5593319 = 8389979) B8389979
theorem B79542557 : Blo 1451545 79542557 := bstep (se 3 (by rfl) ⟨14914229, by rfl⟩ : syracuseStep 79542557 = 29828459) B29828459
theorem B11336111 : Blo 1451545 11336111 := bstep (se 1 (by rfl) ⟨8502083, by rfl⟩ : syracuseStep 11336111 = 17004167) B17004167
theorem B2325305 : Blo 1451545 2325305 := bstep (se 2 (by rfl) ⟨871989, by rfl⟩ : syracuseStep 2325305 = 1743979) B1743979
theorem B3267431 : Blo 1451545 3267431 := bstep (se 1 (by rfl) ⟨2450573, by rfl⟩ : syracuseStep 3267431 = 4901147) B4901147
theorem B3267539 : Blo 1451545 3267539 := bstep (se 1 (by rfl) ⟨2450654, by rfl⟩ : syracuseStep 3267539 = 4901309) B4901309
theorem B3267647 : Blo 1451545 3267647 := bstep (se 1 (by rfl) ⟨2450735, by rfl⟩ : syracuseStep 3267647 = 4901471) B4901471
theorem B55860353 : Blo 1451545 55860353 := bstep (se 2 (by rfl) ⟨20947632, by rfl⟩ : syracuseStep 55860353 = 41895265) B41895265
theorem B2178407 : Blo 1451545 2178407 := bstep (se 1 (by rfl) ⟨1633805, by rfl⟩ : syracuseStep 2178407 = 3267611) B3267611
theorem B2178539 : Blo 1451545 2178539 := bstep (se 1 (by rfl) ⟨1633904, by rfl⟩ : syracuseStep 2178539 = 3267809) B3267809
theorem B24804953 : Blo 1451545 24804953 := bstep (se 2 (by rfl) ⟨9301857, by rfl⟩ : syracuseStep 24804953 = 18603715) B18603715
theorem B32702075 : Blo 1451545 32702075 := bstep (se 1 (by rfl) ⟨24526556, by rfl⟩ : syracuseStep 32702075 = 49053113) B49053113
theorem B8838841 : Blo 1451545 8838841 := bstep (se 2 (by rfl) ⟨3314565, by rfl⟩ : syracuseStep 8838841 = 6629131) B6629131
theorem B2178953 : Blo 1451545 2178953 := bstep (se 2 (by rfl) ⟨817107, by rfl⟩ : syracuseStep 2178953 = 1634215) B1634215
theorem B3268655 : Blo 1451545 3268655 := bstep (se 1 (by rfl) ⟨2451491, by rfl⟩ : syracuseStep 3268655 = 4902983) B4902983
theorem B3678281 : Blo 1451545 3678281 := bstep (se 2 (by rfl) ⟨1379355, by rfl⟩ : syracuseStep 3678281 = 2758711) B2758711
theorem B2326619 : Blo 1451545 2326619 := bstep (se 1 (by rfl) ⟨1744964, by rfl⟩ : syracuseStep 2326619 = 3489929) B3489929
theorem B2179175 : Blo 1451545 2179175 := bstep (se 1 (by rfl) ⟨1634381, by rfl⟩ : syracuseStep 2179175 = 3268763) B3268763
theorem B3268871 : Blo 1451545 3268871 := bstep (se 1 (by rfl) ⟨2451653, by rfl⟩ : syracuseStep 3268871 = 4903307) B4903307
theorem B3678635 : Blo 1451545 3678635 := bstep (se 1 (by rfl) ⟨2758976, by rfl⟩ : syracuseStep 3678635 = 5517953) B5517953
theorem B2654699 : Blo 1451545 2654699 := bstep (se 1 (by rfl) ⟨1991024, by rfl⟩ : syracuseStep 2654699 = 3982049) B3982049
theorem B2179631 : Blo 1451545 2179631 := bstep (se 1 (by rfl) ⟨1634723, by rfl⟩ : syracuseStep 2179631 = 3269447) B3269447
theorem B3269177 : Blo 1451545 3269177 := bstep (se 2 (by rfl) ⟨1225941, by rfl⟩ : syracuseStep 3269177 = 2451883) B2451883
theorem B2180063 : Blo 1451545 2180063 := bstep (se 1 (by rfl) ⟨1635047, by rfl⟩ : syracuseStep 2180063 = 3270095) B3270095
theorem B4654057 : Blo 1451545 4654057 := bstep (se 2 (by rfl) ⟨1745271, by rfl⟩ : syracuseStep 4654057 = 3490543) B3490543
theorem B2450425 : Blo 1451545 2450425 := bstep (se 2 (by rfl) ⟨918909, by rfl⟩ : syracuseStep 2450425 = 1837819) B1837819
theorem B3269627 : Blo 1451545 3269627 := bstep (se 1 (by rfl) ⟨2452220, by rfl⟩ : syracuseStep 3269627 = 4904441) B4904441
theorem B3269735 : Blo 1451545 3269735 := bstep (se 1 (by rfl) ⟨2452301, by rfl⟩ : syracuseStep 3269735 = 4904603) B4904603
theorem B72623429 : Blo 1451545 72623429 := bstep (se 4 (by rfl) ⟨6808446, by rfl⟩ : syracuseStep 72623429 = 13616893) B13616893
theorem B3728879 : Blo 1451545 3728879 := bstep (se 1 (by rfl) ⟨2796659, by rfl⟩ : syracuseStep 3728879 = 5593319) B5593319
theorem B53028371 : Blo 1451545 53028371 := bstep (se 1 (by rfl) ⟨39771278, by rfl⟩ : syracuseStep 53028371 = 79542557) B79542557
theorem B8276201 : Blo 1451545 8276201 := bstep (se 2 (by rfl) ⟨3103575, by rfl⟩ : syracuseStep 8276201 = 6207151) B6207151
theorem B1452271 : Blo 1451545 1452271 := bstep (se 1 (by rfl) ⟨1089203, by rfl⟩ : syracuseStep 1452271 = 2178407) B2178407
theorem B1452359 : Blo 1451545 1452359 := bstep (se 1 (by rfl) ⟨1089269, by rfl⟩ : syracuseStep 1452359 = 2178539) B2178539
theorem B3312031 : Blo 1451545 3312031 := bstep (se 1 (by rfl) ⟨2484023, by rfl⟩ : syracuseStep 3312031 = 4968047) B4968047
theorem B21801383 : Blo 1451545 21801383 := bstep (se 1 (by rfl) ⟨16351037, by rfl⟩ : syracuseStep 21801383 = 32702075) B32702075
theorem B1452635 : Blo 1451545 1452635 := bstep (se 1 (by rfl) ⟨1089476, by rfl⟩ : syracuseStep 1452635 = 2178953) B2178953
theorem B1452795 : Blo 1451545 1452795 := bstep (se 1 (by rfl) ⟨1089596, by rfl⟩ : syracuseStep 1452795 = 2179193) B2179193
theorem B14142217 : Blo 1451545 14142217 := bstep (se 2 (by rfl) ⟨5303331, by rfl⟩ : syracuseStep 14142217 = 10606663) B10606663
theorem B1452991 : Blo 1451545 1452991 := bstep (se 1 (by rfl) ⟨1089743, by rfl⟩ : syracuseStep 1452991 = 2179487) B2179487
theorem B6982681 : Blo 1451545 6982681 := bstep (se 2 (by rfl) ⟨2618505, by rfl⟩ : syracuseStep 6982681 = 5237011) B5237011
theorem B8268911 : Blo 1451545 8268911 := bstep (se 1 (by rfl) ⟨6201683, by rfl⟩ : syracuseStep 8268911 = 12403367) B12403367
theorem B1453247 : Blo 1451545 1453247 := bstep (se 1 (by rfl) ⟨1089935, by rfl⟩ : syracuseStep 1453247 = 2179871) B2179871
theorem B4902227 : Blo 1451545 4902227 := bstep (se 1 (by rfl) ⟨3676670, by rfl⟩ : syracuseStep 4902227 = 7353341) B7353341
theorem B4967855 : Blo 1451545 4967855 := bstep (se 1 (by rfl) ⟨3725891, by rfl⟩ : syracuseStep 4967855 = 7451783) B7451783
theorem B4902335 : Blo 1451545 4902335 := bstep (se 1 (by rfl) ⟨3676751, by rfl⟩ : syracuseStep 4902335 = 7353503) B7353503
theorem B1633819 : Blo 1451545 1633819 := bstep (se 1 (by rfl) ⟨1225364, by rfl⟩ : syracuseStep 1633819 = 2450729) B2450729
theorem B4419119 : Blo 1451545 4419119 := bstep (se 1 (by rfl) ⟨3314339, by rfl⟩ : syracuseStep 4419119 = 6628679) B6628679
theorem B113135219 : Blo 1451545 113135219 := bstep (se 1 (by rfl) ⟨84851414, by rfl⟩ : syracuseStep 113135219 = 169702829) B169702829
theorem B28315331 : Blo 1451545 28315331 := bstep (se 1 (by rfl) ⟨21236498, by rfl⟩ : syracuseStep 28315331 = 42472997) B42472997
theorem B8278159 : Blo 1451545 8278159 := bstep (se 1 (by rfl) ⟨6208619, by rfl⟩ : syracuseStep 8278159 = 12417239) B12417239
theorem B3674281 : Blo 1451545 3674281 := bstep (se 2 (by rfl) ⟨1377855, by rfl⟩ : syracuseStep 3674281 = 2755711) B2755711
theorem B7557407 : Blo 1451545 7557407 := bstep (se 1 (by rfl) ⟨5668055, by rfl⟩ : syracuseStep 7557407 = 11336111) B11336111
theorem B3977839 : Blo 1451545 3977839 := bstep (se 1 (by rfl) ⟨2983379, by rfl⟩ : syracuseStep 3977839 = 5966759) B5966759
theorem B11785121 : Blo 1451545 11785121 := bstep (se 2 (by rfl) ⟨4419420, by rfl⟩ : syracuseStep 11785121 = 8838841) B8838841
theorem B17658809 : Blo 1451545 17658809 := bstep (se 2 (by rfl) ⟨6622053, by rfl⟩ : syracuseStep 17658809 = 13244107) B13244107
theorem B16536635 : Blo 1451545 16536635 := bstep (se 1 (by rfl) ⟨12402476, by rfl⟩ : syracuseStep 16536635 = 24804953) B24804953
theorem B4970099 : Blo 1451545 4970099 := bstep (se 1 (by rfl) ⟨3727574, by rfl⟩ : syracuseStep 4970099 = 7455149) B7455149
theorem B11777663 : Blo 1451545 11777663 := bstep (se 1 (by rfl) ⟨8833247, by rfl⟩ : syracuseStep 11777663 = 17666495) B17666495
theorem B37213991 : Blo 1451545 37213991 := bstep (se 1 (by rfl) ⟨27910493, by rfl⟩ : syracuseStep 37213991 = 55820987) B55820987
theorem B3676043 : Blo 1451545 3676043 := bstep (se 1 (by rfl) ⟨2757032, by rfl⟩ : syracuseStep 3676043 = 5514065) B5514065
theorem B9304091 : Blo 1451545 9304091 := bstep (se 1 (by rfl) ⟨6978068, by rfl⟩ : syracuseStep 9304091 = 13956137) B13956137
theorem B11032685 : Blo 1451545 11032685 := bstep (se 3 (by rfl) ⟨2068628, by rfl⟩ : syracuseStep 11032685 = 4137257) B4137257
theorem B9312367 : Blo 1451545 9312367 := bstep (se 1 (by rfl) ⟨6984275, by rfl⟩ : syracuseStep 9312367 = 13968551) B13968551
theorem B19880063 : Blo 1451545 19880063 := bstep (se 1 (by rfl) ⟨14910047, by rfl⟩ : syracuseStep 19880063 = 29820095) B29820095
theorem B3266747 : Blo 1451545 3266747 := bstep (se 1 (by rfl) ⟨2450060, by rfl⟩ : syracuseStep 3266747 = 4900121) B4900121
theorem B2759159 : Blo 1451545 2759159 := bstep (se 1 (by rfl) ⟨2069369, by rfl⟩ : syracuseStep 2759159 = 4138739) B4138739
theorem B11033171 : Blo 1451545 11033171 := bstep (se 1 (by rfl) ⟨8274878, by rfl⟩ : syracuseStep 11033171 = 16549757) B16549757
theorem B59661521 : Blo 1451545 59661521 := bstep (se 2 (by rfl) ⟨22373070, by rfl⟩ : syracuseStep 59661521 = 44746141) B44746141
theorem B2178287 : Blo 1451545 2178287 := bstep (se 1 (by rfl) ⟨1633715, by rfl⟩ : syracuseStep 2178287 = 3267431) B3267431
theorem B44711165 : Blo 1451545 44711165 := bstep (se 3 (by rfl) ⟨8383343, by rfl⟩ : syracuseStep 44711165 = 16766687) B16766687
theorem B2178359 : Blo 1451545 2178359 := bstep (se 1 (by rfl) ⟨1633769, by rfl⟩ : syracuseStep 2178359 = 3267539) B3267539
theorem B2178431 : Blo 1451545 2178431 := bstep (se 1 (by rfl) ⟨1633823, by rfl⟩ : syracuseStep 2178431 = 3267647) B3267647
theorem B37240235 : Blo 1451545 37240235 := bstep (se 1 (by rfl) ⟨27930176, by rfl⟩ : syracuseStep 37240235 = 55860353) B55860353
theorem B6200813 : Blo 1451545 6200813 := bstep (se 3 (by rfl) ⟨1162652, by rfl⟩ : syracuseStep 6200813 = 2325305) B2325305
theorem B3268079 : Blo 1451545 3268079 := bstep (se 1 (by rfl) ⟨2451059, by rfl⟩ : syracuseStep 3268079 = 4902119) B4902119
theorem B2178665 : Blo 1451545 2178665 := bstep (se 2 (by rfl) ⟨816999, by rfl⟩ : syracuseStep 2178665 = 1633999) B1633999
theorem B17669897 : Blo 1451545 17669897 := bstep (se 2 (by rfl) ⟨6626211, by rfl⟩ : syracuseStep 17669897 = 13252423) B13252423
theorem B3268583 : Blo 1451545 3268583 := bstep (se 1 (by rfl) ⟨2451437, by rfl⟩ : syracuseStep 3268583 = 4902875) B4902875
theorem B2179103 : Blo 1451545 2179103 := bstep (se 1 (by rfl) ⟨1634327, by rfl⟩ : syracuseStep 2179103 = 3268655) B3268655
theorem B2179247 : Blo 1451545 2179247 := bstep (se 1 (by rfl) ⟨1634435, by rfl⟩ : syracuseStep 2179247 = 3268871) B3268871
theorem B5038271 : Blo 1451545 5038271 := bstep (se 1 (by rfl) ⟨3778703, by rfl⟩ : syracuseStep 5038271 = 7557407) B7557407
theorem B4899041 : Blo 1451545 4899041 := bstep (se 2 (by rfl) ⟨1837140, by rfl⟩ : syracuseStep 4899041 = 3674281) B3674281
theorem B2179451 : Blo 1451545 2179451 := bstep (se 1 (by rfl) ⟨1634588, by rfl⟩ : syracuseStep 2179451 = 3269177) B3269177
theorem B4416041 : Blo 1451545 4416041 := bstep (se 2 (by rfl) ⟨1656015, by rfl⟩ : syracuseStep 4416041 = 3312031) B3312031
theorem B7856747 : Blo 1451545 7856747 := bstep (se 1 (by rfl) ⟨5892560, by rfl⟩ : syracuseStep 7856747 = 11785121) B11785121
theorem B11772539 : Blo 1451545 11772539 := bstep (se 1 (by rfl) ⟨8829404, by rfl⟩ : syracuseStep 11772539 = 17658809) B17658809
theorem B2179751 : Blo 1451545 2179751 := bstep (se 1 (by rfl) ⟨1634813, by rfl⟩ : syracuseStep 2179751 = 3269627) B3269627
theorem B2179823 : Blo 1451545 2179823 := bstep (se 1 (by rfl) ⟨1634867, by rfl⟩ : syracuseStep 2179823 = 3269735) B3269735
theorem B48415619 : Blo 1451545 48415619 := bstep (se 1 (by rfl) ⟨36311714, by rfl⟩ : syracuseStep 48415619 = 72623429) B72623429
theorem B2450695 : Blo 1451545 2450695 := bstep (se 1 (by rfl) ⟨1838021, by rfl⟩ : syracuseStep 2450695 = 3676043) B3676043
theorem B6202727 : Blo 1451545 6202727 := bstep (se 1 (by rfl) ⟨4652045, by rfl⟩ : syracuseStep 6202727 = 9304091) B9304091
theorem B14534255 : Blo 1451545 14534255 := bstep (se 1 (by rfl) ⟨10900691, by rfl⟩ : syracuseStep 14534255 = 21801383) B21801383
theorem B39774347 : Blo 1451545 39774347 := bstep (se 1 (by rfl) ⟨29830760, by rfl⟩ : syracuseStep 39774347 = 59661521) B59661521
theorem B1452191 : Blo 1451545 1452191 := bstep (se 1 (by rfl) ⟨1089143, by rfl⟩ : syracuseStep 1452191 = 2178287) B2178287
theorem B1452239 : Blo 1451545 1452239 := bstep (se 1 (by rfl) ⟨1089179, by rfl⟩ : syracuseStep 1452239 = 2178359) B2178359
theorem B1452287 : Blo 1451545 1452287 := bstep (se 1 (by rfl) ⟨1089215, by rfl⟩ : syracuseStep 1452287 = 2178431) B2178431
theorem B3311903 : Blo 1451545 3311903 := bstep (se 1 (by rfl) ⟨2483927, by rfl⟩ : syracuseStep 3311903 = 4967855) B4967855
theorem B1452443 : Blo 1451545 1452443 := bstep (se 1 (by rfl) ⟨1089332, by rfl⟩ : syracuseStep 1452443 = 2178665) B2178665
theorem B18876887 : Blo 1451545 18876887 := bstep (se 1 (by rfl) ⟨14157665, by rfl⟩ : syracuseStep 18876887 = 28315331) B28315331
theorem B2452187 : Blo 1451545 2452187 := bstep (se 1 (by rfl) ⟨1839140, by rfl⟩ : syracuseStep 2452187 = 3678281) B3678281
theorem B1551079 : Blo 1451545 1551079 := bstep (se 1 (by rfl) ⟨1163309, by rfl⟩ : syracuseStep 1551079 = 2326619) B2326619
theorem B1452783 : Blo 1451545 1452783 := bstep (se 1 (by rfl) ⟨1089587, by rfl⟩ : syracuseStep 1452783 = 2179175) B2179175
theorem B11037545 : Blo 1451545 11037545 := bstep (se 2 (by rfl) ⟨4139079, by rfl⟩ : syracuseStep 11037545 = 8278159) B8278159
theorem B2452423 : Blo 1451545 2452423 := bstep (se 1 (by rfl) ⟨1839317, by rfl⟩ : syracuseStep 2452423 = 3678635) B3678635
theorem B1453087 : Blo 1451545 1453087 := bstep (se 1 (by rfl) ⟨1089815, by rfl⟩ : syracuseStep 1453087 = 2179631) B2179631
theorem B1453375 : Blo 1451545 1453375 := bstep (se 1 (by rfl) ⟨1090031, by rfl⟩ : syracuseStep 1453375 = 2180063) B2180063
theorem B2485919 : Blo 1451545 2485919 := bstep (se 1 (by rfl) ⟨1864439, by rfl⟩ : syracuseStep 2485919 = 3728879) B3728879
theorem B35352247 : Blo 1451545 35352247 := bstep (se 1 (by rfl) ⟨26514185, by rfl⟩ : syracuseStep 35352247 = 53028371) B53028371
theorem B3313399 : Blo 1451545 3313399 := bstep (se 1 (by rfl) ⟨2485049, by rfl⟩ : syracuseStep 3313399 = 4970099) B4970099
theorem B7851775 : Blo 1451545 7851775 := bstep (se 1 (by rfl) ⟨5888831, by rfl⟩ : syracuseStep 7851775 = 11777663) B11777663
theorem B24809327 : Blo 1451545 24809327 := bstep (se 1 (by rfl) ⟨18606995, by rfl⟩ : syracuseStep 24809327 = 37213991) B37213991
theorem B6205409 : Blo 1451545 6205409 := bstep (se 2 (by rfl) ⟨2327028, by rfl⟩ : syracuseStep 6205409 = 4654057) B4654057
theorem B9310241 : Blo 1451545 9310241 := bstep (se 2 (by rfl) ⟨3491340, by rfl⟩ : syracuseStep 9310241 = 6982681) B6982681
theorem B5517467 : Blo 1451545 5517467 := bstep (se 1 (by rfl) ⟨4138100, by rfl⟩ : syracuseStep 5517467 = 8276201) B8276201
theorem B1839439 : Blo 1451545 1839439 := bstep (se 1 (by rfl) ⟨1379579, by rfl⟩ : syracuseStep 1839439 = 2759159) B2759159
theorem B29807443 : Blo 1451545 29807443 := bstep (se 1 (by rfl) ⟨22355582, by rfl⟩ : syracuseStep 29807443 = 44711165) B44711165
theorem B24826823 : Blo 1451545 24826823 := bstep (se 1 (by rfl) ⟨18620117, by rfl⟩ : syracuseStep 24826823 = 37240235) B37240235
theorem B4133875 : Blo 1451545 4133875 := bstep (se 1 (by rfl) ⟨3100406, by rfl⟩ : syracuseStep 4133875 = 6200813) B6200813
theorem B2946079 : Blo 1451545 2946079 := bstep (se 1 (by rfl) ⟨2209559, by rfl⟩ : syracuseStep 2946079 = 4419119) B4419119
theorem B28316789 : Blo 1451545 28316789 := bstep (se 5 (by rfl) ⟨1327349, by rfl⟩ : syracuseStep 28316789 = 2654699) B2654699
theorem B12416489 : Blo 1451545 12416489 := bstep (se 2 (by rfl) ⟨4656183, by rfl⟩ : syracuseStep 12416489 = 9312367) B9312367
theorem B21215141 : Blo 1451545 21215141 := bstep (se 4 (by rfl) ⟨1988919, by rfl⟩ : syracuseStep 21215141 = 3977839) B3977839
theorem B11024423 : Blo 1451545 11024423 := bstep (se 1 (by rfl) ⟨8268317, by rfl⟩ : syracuseStep 11024423 = 16536635) B16536635
theorem B18856289 : Blo 1451545 18856289 := bstep (se 2 (by rfl) ⟨7071108, by rfl⟩ : syracuseStep 18856289 = 14142217) B14142217
theorem B3267233 : Blo 1451545 3267233 := bstep (se 2 (by rfl) ⟨1225212, by rfl⟩ : syracuseStep 3267233 = 2450425) B2450425
theorem B7355123 : Blo 1451545 7355123 := bstep (se 1 (by rfl) ⟨5516342, by rfl⟩ : syracuseStep 7355123 = 11032685) B11032685
theorem B13253375 : Blo 1451545 13253375 := bstep (se 1 (by rfl) ⟨9940031, by rfl⟩ : syracuseStep 13253375 = 19880063) B19880063
theorem B2177831 : Blo 1451545 2177831 := bstep (se 1 (by rfl) ⟨1633373, by rfl⟩ : syracuseStep 2177831 = 3266747) B3266747
theorem B7355447 : Blo 1451545 7355447 := bstep (se 1 (by rfl) ⟨5516585, by rfl⟩ : syracuseStep 7355447 = 11033171) B11033171
theorem B2178425 : Blo 1451545 2178425 := bstep (se 2 (by rfl) ⟨816909, by rfl⟩ : syracuseStep 2178425 = 1633819) B1633819
theorem B5512607 : Blo 1451545 5512607 := bstep (se 1 (by rfl) ⟨4134455, by rfl⟩ : syracuseStep 5512607 = 8268911) B8268911
theorem B3268151 : Blo 1451545 3268151 := bstep (se 1 (by rfl) ⟨2451113, by rfl⟩ : syracuseStep 3268151 = 4902227) B4902227
theorem B3268223 : Blo 1451545 3268223 := bstep (se 1 (by rfl) ⟨2451167, by rfl⟩ : syracuseStep 3268223 = 4902335) B4902335
theorem B2178719 : Blo 1451545 2178719 := bstep (se 1 (by rfl) ⟨1634039, by rfl⟩ : syracuseStep 2178719 = 3268079) B3268079
theorem B75423479 : Blo 1451545 75423479 := bstep (se 1 (by rfl) ⟨56567609, by rfl⟩ : syracuseStep 75423479 = 113135219) B113135219
theorem B11779931 : Blo 1451545 11779931 := bstep (se 1 (by rfl) ⟨8834948, by rfl⟩ : syracuseStep 11779931 = 17669897) B17669897
theorem B2179055 : Blo 1451545 2179055 := bstep (se 1 (by rfl) ⟨1634291, by rfl⟩ : syracuseStep 2179055 = 3268583) B3268583
theorem B3678311 : Blo 1451545 3678311 := bstep (se 1 (by rfl) ⟨2758733, by rfl⟩ : syracuseStep 3678311 = 5517467) B5517467
theorem B3358847 : Blo 1451545 3358847 := bstep (se 1 (by rfl) ⟨2519135, by rfl⟩ : syracuseStep 3358847 = 5038271) B5038271
theorem B7848359 : Blo 1451545 7848359 := bstep (se 1 (by rfl) ⟨5886269, by rfl⟩ : syracuseStep 7848359 = 11772539) B11772539
theorem B32277079 : Blo 1451545 32277079 := bstep (se 1 (by rfl) ⟨24207809, by rfl⟩ : syracuseStep 32277079 = 48415619) B48415619
theorem B3269897 : Blo 1451545 3269897 := bstep (se 2 (by rfl) ⟨1226211, by rfl⟩ : syracuseStep 3269897 = 2452423) B2452423
theorem B7349615 : Blo 1451545 7349615 := bstep (se 1 (by rfl) ⟨5512211, by rfl⟩ : syracuseStep 7349615 = 11024423) B11024423
theorem B12584591 : Blo 1451545 12584591 := bstep (se 1 (by rfl) ⟨9438443, by rfl⟩ : syracuseStep 12584591 = 18876887) B18876887
theorem B1451887 : Blo 1451545 1451887 := bstep (se 1 (by rfl) ⟨1088915, by rfl⟩ : syracuseStep 1451887 = 2177831) B2177831
theorem B7358363 : Blo 1451545 7358363 := bstep (se 1 (by rfl) ⟨5518772, by rfl⟩ : syracuseStep 7358363 = 11037545) B11037545
theorem B1452283 : Blo 1451545 1452283 := bstep (se 1 (by rfl) ⟨1089212, by rfl⟩ : syracuseStep 1452283 = 2178425) B2178425
theorem B4417865 : Blo 1451545 4417865 := bstep (se 2 (by rfl) ⟨1656699, by rfl⟩ : syracuseStep 4417865 = 3313399) B3313399
theorem B1452479 : Blo 1451545 1452479 := bstep (se 1 (by rfl) ⟨1089359, by rfl⟩ : syracuseStep 1452479 = 2178719) B2178719
theorem B1657279 : Blo 1451545 1657279 := bstep (se 1 (by rfl) ⟨1242959, by rfl⟩ : syracuseStep 1657279 = 2485919) B2485919
theorem B1452703 : Blo 1451545 1452703 := bstep (se 1 (by rfl) ⟨1089527, by rfl⟩ : syracuseStep 1452703 = 2179055) B2179055
theorem B1452735 : Blo 1451545 1452735 := bstep (se 1 (by rfl) ⟨1089551, by rfl⟩ : syracuseStep 1452735 = 2179103) B2179103
theorem B1452831 : Blo 1451545 1452831 := bstep (se 1 (by rfl) ⟨1089623, by rfl⟩ : syracuseStep 1452831 = 2179247) B2179247
theorem B1452967 : Blo 1451545 1452967 := bstep (se 1 (by rfl) ⟨1089725, by rfl⟩ : syracuseStep 1452967 = 2179451) B2179451
theorem B2944027 : Blo 1451545 2944027 := bstep (se 1 (by rfl) ⟨2208020, by rfl⟩ : syracuseStep 2944027 = 4416041) B4416041
theorem B5237831 : Blo 1451545 5237831 := bstep (se 1 (by rfl) ⟨3928373, by rfl⟩ : syracuseStep 5237831 = 7856747) B7856747
theorem B2452585 : Blo 1451545 2452585 := bstep (se 2 (by rfl) ⟨919719, by rfl⟩ : syracuseStep 2452585 = 1839439) B1839439
theorem B1453167 : Blo 1451545 1453167 := bstep (se 1 (by rfl) ⟨1089875, by rfl⟩ : syracuseStep 1453167 = 2179751) B2179751
theorem B1453215 : Blo 1451545 1453215 := bstep (se 1 (by rfl) ⟨1089911, by rfl⟩ : syracuseStep 1453215 = 2179823) B2179823
theorem B16551215 : Blo 1451545 16551215 := bstep (se 1 (by rfl) ⟨12413411, by rfl⟩ : syracuseStep 16551215 = 24826823) B24826823
theorem B18877859 : Blo 1451545 18877859 := bstep (se 1 (by rfl) ⟨14158394, by rfl⟩ : syracuseStep 18877859 = 28316789) B28316789
theorem B2068105 : Blo 1451545 2068105 := bstep (se 2 (by rfl) ⟨775539, by rfl⟩ : syracuseStep 2068105 = 1551079) B1551079
theorem B8277659 : Blo 1451545 8277659 := bstep (se 1 (by rfl) ⟨6208244, by rfl⟩ : syracuseStep 8277659 = 12416489) B12416489
theorem B39743257 : Blo 1451545 39743257 := bstep (se 2 (by rfl) ⟨14903721, by rfl⟩ : syracuseStep 39743257 = 29807443) B29807443
theorem B14143427 : Blo 1451545 14143427 := bstep (se 1 (by rfl) ⟨10607570, by rfl⟩ : syracuseStep 14143427 = 21215141) B21215141
theorem B3928105 : Blo 1451545 3928105 := bstep (se 2 (by rfl) ⟨1473039, by rfl⟩ : syracuseStep 3928105 = 2946079) B2946079
theorem B2207935 : Blo 1451545 2207935 := bstep (se 1 (by rfl) ⟨1655951, by rfl⟩ : syracuseStep 2207935 = 3311903) B3311903
theorem B12570859 : Blo 1451545 12570859 := bstep (se 1 (by rfl) ⟨9428144, by rfl⟩ : syracuseStep 12570859 = 18856289) B18856289
theorem B1634791 : Blo 1451545 1634791 := bstep (se 1 (by rfl) ⟨1226093, by rfl⟩ : syracuseStep 1634791 = 2452187) B2452187
theorem B4903415 : Blo 1451545 4903415 := bstep (se 1 (by rfl) ⟨3677561, by rfl⟩ : syracuseStep 4903415 = 7355123) B7355123
theorem B8835583 : Blo 1451545 8835583 := bstep (se 1 (by rfl) ⟨6626687, by rfl⟩ : syracuseStep 8835583 = 13253375) B13253375
theorem B4903631 : Blo 1451545 4903631 := bstep (se 1 (by rfl) ⟨3677723, by rfl⟩ : syracuseStep 4903631 = 7355447) B7355447
theorem B3675071 : Blo 1451545 3675071 := bstep (se 1 (by rfl) ⟨2756303, by rfl⟩ : syracuseStep 3675071 = 5512607) B5512607
theorem B7853287 : Blo 1451545 7853287 := bstep (se 1 (by rfl) ⟨5889965, by rfl⟩ : syracuseStep 7853287 = 11779931) B11779931
theorem B6206827 : Blo 1451545 6206827 := bstep (se 1 (by rfl) ⟨4655120, by rfl⟩ : syracuseStep 6206827 = 9310241) B9310241
theorem B3266027 : Blo 1451545 3266027 := bstep (se 1 (by rfl) ⟨2449520, by rfl⟩ : syracuseStep 3266027 = 4899041) B4899041
theorem B4135151 : Blo 1451545 4135151 := bstep (se 1 (by rfl) ⟨3101363, by rfl⟩ : syracuseStep 4135151 = 6202727) B6202727
theorem B9689503 : Blo 1451545 9689503 := bstep (se 1 (by rfl) ⟨7267127, by rfl⟩ : syracuseStep 9689503 = 14534255) B14534255
theorem B5511833 : Blo 1451545 5511833 := bstep (se 2 (by rfl) ⟨2066937, by rfl⟩ : syracuseStep 5511833 = 4133875) B4133875
theorem B26516231 : Blo 1451545 26516231 := bstep (se 1 (by rfl) ⟨19887173, by rfl⟩ : syracuseStep 26516231 = 39774347) B39774347
theorem B3267593 : Blo 1451545 3267593 := bstep (se 2 (by rfl) ⟨1225347, by rfl⟩ : syracuseStep 3267593 = 2450695) B2450695
theorem B2178155 : Blo 1451545 2178155 := bstep (se 1 (by rfl) ⟨1633616, by rfl⟩ : syracuseStep 2178155 = 3267233) B3267233
theorem B201129277 : Blo 1451545 201129277 := bstep (se 3 (by rfl) ⟨37711739, by rfl⟩ : syracuseStep 201129277 = 75423479) B75423479
theorem B47136329 : Blo 1451545 47136329 := bstep (se 2 (by rfl) ⟨17676123, by rfl⟩ : syracuseStep 47136329 = 35352247) B35352247
theorem B10469033 : Blo 1451545 10469033 := bstep (se 2 (by rfl) ⟨3925887, by rfl⟩ : syracuseStep 10469033 = 7851775) B7851775
theorem B2178767 : Blo 1451545 2178767 := bstep (se 1 (by rfl) ⟨1634075, by rfl⟩ : syracuseStep 2178767 = 3268151) B3268151
theorem B2178815 : Blo 1451545 2178815 := bstep (se 1 (by rfl) ⟨1634111, by rfl⟩ : syracuseStep 2178815 = 3268223) B3268223
theorem B16539551 : Blo 1451545 16539551 := bstep (se 1 (by rfl) ⟨12404663, by rfl⟩ : syracuseStep 16539551 = 24809327) B24809327
theorem B4136939 : Blo 1451545 4136939 := bstep (se 1 (by rfl) ⟨3102704, by rfl⟩ : syracuseStep 4136939 = 6205409) B6205409
theorem B13967549 : Blo 1451545 13967549 := bstep (se 3 (by rfl) ⟨2618915, by rfl⟩ : syracuseStep 13967549 = 5237831) B5237831
theorem B3268943 : Blo 1451545 3268943 := bstep (se 1 (by rfl) ⟨2451707, by rfl⟩ : syracuseStep 3268943 = 4903415) B4903415
theorem B3269087 : Blo 1451545 3269087 := bstep (se 1 (by rfl) ⟨2451815, by rfl⟩ : syracuseStep 3269087 = 4903631) B4903631
theorem B12919337 : Blo 1451545 12919337 := bstep (se 2 (by rfl) ⟨4844751, by rfl⟩ : syracuseStep 12919337 = 9689503) B9689503
theorem B2450047 : Blo 1451545 2450047 := bstep (se 1 (by rfl) ⟨1837535, by rfl⟩ : syracuseStep 2450047 = 3675071) B3675071
theorem B2179721 : Blo 1451545 2179721 := bstep (se 2 (by rfl) ⟨817395, by rfl⟩ : syracuseStep 2179721 = 1634791) B1634791
theorem B11780777 : Blo 1451545 11780777 := bstep (se 2 (by rfl) ⟨4417791, by rfl⟩ : syracuseStep 11780777 = 8835583) B8835583
theorem B2179931 : Blo 1451545 2179931 := bstep (se 1 (by rfl) ⟨1634948, by rfl⟩ : syracuseStep 2179931 = 3269897) B3269897
theorem B4899743 : Blo 1451545 4899743 := bstep (se 1 (by rfl) ⟨3674807, by rfl⟩ : syracuseStep 4899743 = 7349615) B7349615
theorem B8389727 : Blo 1451545 8389727 := bstep (se 1 (by rfl) ⟨6292295, by rfl⟩ : syracuseStep 8389727 = 12584591) B12584591
theorem B67044581 : Blo 1451545 67044581 := bstep (se 4 (by rfl) ⟨6285429, by rfl⟩ : syracuseStep 67044581 = 12570859) B12570859
theorem B3925369 : Blo 1451545 3925369 := bstep (se 2 (by rfl) ⟨1472013, by rfl⟩ : syracuseStep 3925369 = 2944027) B2944027
theorem B3270113 : Blo 1451545 3270113 := bstep (se 2 (by rfl) ⟨1226292, by rfl⟩ : syracuseStep 3270113 = 2452585) B2452585
theorem B10471049 : Blo 1451545 10471049 := bstep (se 2 (by rfl) ⟨3926643, by rfl⟩ : syracuseStep 10471049 = 7853287) B7853287
theorem B8275769 : Blo 1451545 8275769 := bstep (se 2 (by rfl) ⟨3103413, by rfl⟩ : syracuseStep 8275769 = 6206827) B6206827
theorem B1452103 : Blo 1451545 1452103 := bstep (se 1 (by rfl) ⟨1089077, by rfl⟩ : syracuseStep 1452103 = 2178155) B2178155
theorem B12585239 : Blo 1451545 12585239 := bstep (se 1 (by rfl) ⟨9438929, by rfl⟩ : syracuseStep 12585239 = 18877859) B18877859
theorem B1452511 : Blo 1451545 1452511 := bstep (se 1 (by rfl) ⟨1089383, by rfl⟩ : syracuseStep 1452511 = 2178767) B2178767
theorem B1452543 : Blo 1451545 1452543 := bstep (se 1 (by rfl) ⟨1089407, by rfl⟩ : syracuseStep 1452543 = 2178815) B2178815
theorem B5237473 : Blo 1451545 5237473 := bstep (se 2 (by rfl) ⟨1964052, by rfl⟩ : syracuseStep 5237473 = 3928105) B3928105
theorem B2452207 : Blo 1451545 2452207 := bstep (se 1 (by rfl) ⟨1839155, by rfl⟩ : syracuseStep 2452207 = 3678311) B3678311
theorem B2239231 : Blo 1451545 2239231 := bstep (se 1 (by rfl) ⟨1679423, by rfl⟩ : syracuseStep 2239231 = 3358847) B3358847
theorem B2943913 : Blo 1451545 2943913 := bstep (se 2 (by rfl) ⟨1103967, by rfl⟩ : syracuseStep 2943913 = 2207935) B2207935
theorem B43036105 : Blo 1451545 43036105 := bstep (se 2 (by rfl) ⟨16138539, by rfl⟩ : syracuseStep 43036105 = 32277079) B32277079
theorem B2756767 : Blo 1451545 2756767 := bstep (se 1 (by rfl) ⟨2067575, by rfl⟩ : syracuseStep 2756767 = 4135151) B4135151
theorem B2945243 : Blo 1451545 2945243 := bstep (se 1 (by rfl) ⟨2208932, by rfl⟩ : syracuseStep 2945243 = 4417865) B4417865
theorem B3674555 : Blo 1451545 3674555 := bstep (se 1 (by rfl) ⟨2755916, by rfl⟩ : syracuseStep 3674555 = 5511833) B5511833
theorem B2757473 : Blo 1451545 2757473 := bstep (se 2 (by rfl) ⟨1034052, by rfl⟩ : syracuseStep 2757473 = 2068105) B2068105
theorem B52991009 : Blo 1451545 52991009 := bstep (se 2 (by rfl) ⟨19871628, by rfl⟩ : syracuseStep 52991009 = 39743257) B39743257
theorem B5518439 : Blo 1451545 5518439 := bstep (se 1 (by rfl) ⟨4138829, by rfl⟩ : syracuseStep 5518439 = 8277659) B8277659
theorem B2757959 : Blo 1451545 2757959 := bstep (se 1 (by rfl) ⟨2068469, by rfl⟩ : syracuseStep 2757959 = 4136939) B4136939
theorem B5232239 : Blo 1451545 5232239 := bstep (se 1 (by rfl) ⟨3924179, by rfl⟩ : syracuseStep 5232239 = 7848359) B7848359
theorem B2177351 : Blo 1451545 2177351 := bstep (se 1 (by rfl) ⟨1633013, by rfl⟩ : syracuseStep 2177351 = 3266027) B3266027
theorem B4905575 : Blo 1451545 4905575 := bstep (se 1 (by rfl) ⟨3679181, by rfl⟩ : syracuseStep 4905575 = 7358363) B7358363
theorem B268172369 : Blo 1451545 268172369 := bstep (se 2 (by rfl) ⟨100564638, by rfl⟩ : syracuseStep 268172369 = 201129277) B201129277
theorem B17677487 : Blo 1451545 17677487 := bstep (se 1 (by rfl) ⟨13258115, by rfl⟩ : syracuseStep 17677487 = 26516231) B26516231
theorem B2178395 : Blo 1451545 2178395 := bstep (se 1 (by rfl) ⟨1633796, by rfl⟩ : syracuseStep 2178395 = 3267593) B3267593
theorem B11034143 : Blo 1451545 11034143 := bstep (se 1 (by rfl) ⟨8275607, by rfl⟩ : syracuseStep 11034143 = 16551215) B16551215
theorem B8838821 : Blo 1451545 8838821 := bstep (se 4 (by rfl) ⟨828639, by rfl⟩ : syracuseStep 8838821 = 1657279) B1657279
theorem B31424219 : Blo 1451545 31424219 := bstep (se 1 (by rfl) ⟨23568164, by rfl⟩ : syracuseStep 31424219 = 47136329) B47136329
theorem B6979355 : Blo 1451545 6979355 := bstep (se 1 (by rfl) ⟨5234516, by rfl⟩ : syracuseStep 6979355 = 10469033) B10469033
theorem B11026367 : Blo 1451545 11026367 := bstep (se 1 (by rfl) ⟨8269775, by rfl⟩ : syracuseStep 11026367 = 16539551) B16539551
theorem B9428951 : Blo 1451545 9428951 := bstep (se 1 (by rfl) ⟨7071713, by rfl⟩ : syracuseStep 9428951 = 14143427) B14143427
theorem B2179295 : Blo 1451545 2179295 := bstep (se 1 (by rfl) ⟨1634471, by rfl⟩ : syracuseStep 2179295 = 3268943) B3268943
theorem B2449703 : Blo 1451545 2449703 := bstep (se 1 (by rfl) ⟨1837277, by rfl⟩ : syracuseStep 2449703 = 3674555) B3674555
theorem B2179391 : Blo 1451545 2179391 := bstep (se 1 (by rfl) ⟨1634543, by rfl⟩ : syracuseStep 2179391 = 3269087) B3269087
theorem B3678959 : Blo 1451545 3678959 := bstep (se 1 (by rfl) ⟨2759219, by rfl⟩ : syracuseStep 3678959 = 5518439) B5518439
theorem B44696387 : Blo 1451545 44696387 := bstep (se 1 (by rfl) ⟨33522290, by rfl⟩ : syracuseStep 44696387 = 67044581) B67044581
theorem B3269609 : Blo 1451545 3269609 := bstep (se 2 (by rfl) ⟨1226103, by rfl⟩ : syracuseStep 3269609 = 2452207) B2452207
theorem B2180075 : Blo 1451545 2180075 := bstep (se 1 (by rfl) ⟨1635056, by rfl⟩ : syracuseStep 2180075 = 3270113) B3270113
theorem B6980699 : Blo 1451545 6980699 := bstep (se 1 (by rfl) ⟨5235524, by rfl⟩ : syracuseStep 6980699 = 10471049) B10471049
theorem B3925217 : Blo 1451545 3925217 := bstep (se 2 (by rfl) ⟨1471956, by rfl⟩ : syracuseStep 3925217 = 2943913) B2943913
theorem B8390159 : Blo 1451545 8390159 := bstep (se 1 (by rfl) ⟨6292619, by rfl⟩ : syracuseStep 8390159 = 12585239) B12585239
theorem B1451567 : Blo 1451545 1451567 := bstep (se 1 (by rfl) ⟨1088675, by rfl⟩ : syracuseStep 1451567 = 2177351) B2177351
theorem B3270383 : Blo 1451545 3270383 := bstep (se 1 (by rfl) ⟨2452787, by rfl⟩ : syracuseStep 3270383 = 4905575) B4905575
theorem B23570189 : Blo 1451545 23570189 := bstep (se 3 (by rfl) ⟨4419410, by rfl⟩ : syracuseStep 23570189 = 8838821) B8838821
theorem B1452263 : Blo 1451545 1452263 := bstep (se 1 (by rfl) ⟨1089197, by rfl⟩ : syracuseStep 1452263 = 2178395) B2178395
theorem B20949479 : Blo 1451545 20949479 := bstep (se 1 (by rfl) ⟨15712109, by rfl⟩ : syracuseStep 20949479 = 31424219) B31424219
theorem B7350911 : Blo 1451545 7350911 := bstep (se 1 (by rfl) ⟨5513183, by rfl⟩ : syracuseStep 7350911 = 11026367) B11026367
theorem B6285967 : Blo 1451545 6285967 := bstep (se 1 (by rfl) ⟨4714475, by rfl⟩ : syracuseStep 6285967 = 9428951) B9428951
theorem B8612891 : Blo 1451545 8612891 := bstep (se 1 (by rfl) ⟨6459668, by rfl⟩ : syracuseStep 8612891 = 12919337) B12919337
theorem B1453147 : Blo 1451545 1453147 := bstep (se 1 (by rfl) ⟨1089860, by rfl⟩ : syracuseStep 1453147 = 2179721) B2179721
theorem B47139965 : Blo 1451545 47139965 := bstep (se 3 (by rfl) ⟨8838743, by rfl⟩ : syracuseStep 47139965 = 17677487) B17677487
theorem B1453287 : Blo 1451545 1453287 := bstep (se 1 (by rfl) ⟨1089965, by rfl⟩ : syracuseStep 1453287 = 2179931) B2179931
theorem B1838315 : Blo 1451545 1838315 := bstep (se 1 (by rfl) ⟨1378736, by rfl⟩ : syracuseStep 1838315 = 2757473) B2757473
theorem B35327339 : Blo 1451545 35327339 := bstep (se 1 (by rfl) ⟨26495504, by rfl⟩ : syracuseStep 35327339 = 52991009) B52991009
theorem B1838639 : Blo 1451545 1838639 := bstep (se 1 (by rfl) ⟨1378979, by rfl⟩ : syracuseStep 1838639 = 2757959) B2757959
theorem B6983297 : Blo 1451545 6983297 := bstep (se 2 (by rfl) ⟨2618736, by rfl⟩ : syracuseStep 6983297 = 5237473) B5237473
theorem B2985641 : Blo 1451545 2985641 := bstep (se 2 (by rfl) ⟨1119615, by rfl⟩ : syracuseStep 2985641 = 2239231) B2239231
theorem B5517179 : Blo 1451545 5517179 := bstep (se 1 (by rfl) ⟨4137884, by rfl⟩ : syracuseStep 5517179 = 8275769) B8275769
theorem B57381473 : Blo 1451545 57381473 := bstep (se 2 (by rfl) ⟨21518052, by rfl⟩ : syracuseStep 57381473 = 43036105) B43036105
theorem B9311699 : Blo 1451545 9311699 := bstep (se 1 (by rfl) ⟨6983774, by rfl⟩ : syracuseStep 9311699 = 13967549) B13967549
theorem B1963495 : Blo 1451545 1963495 := bstep (se 1 (by rfl) ⟨1472621, by rfl⟩ : syracuseStep 1963495 = 2945243) B2945243
theorem B3675689 : Blo 1451545 3675689 := bstep (se 2 (by rfl) ⟨1378383, by rfl⟩ : syracuseStep 3675689 = 2756767) B2756767
theorem B7853851 : Blo 1451545 7853851 := bstep (se 1 (by rfl) ⟨5890388, by rfl⟩ : syracuseStep 7853851 = 11780777) B11780777
theorem B3266495 : Blo 1451545 3266495 := bstep (se 1 (by rfl) ⟨2449871, by rfl⟩ : syracuseStep 3266495 = 4899743) B4899743
theorem B5593151 : Blo 1451545 5593151 := bstep (se 1 (by rfl) ⟨4194863, by rfl⟩ : syracuseStep 5593151 = 8389727) B8389727
theorem B3266729 : Blo 1451545 3266729 := bstep (se 2 (by rfl) ⟨1225023, by rfl⟩ : syracuseStep 3266729 = 2450047) B2450047
theorem B3488159 : Blo 1451545 3488159 := bstep (se 1 (by rfl) ⟨2616119, by rfl⟩ : syracuseStep 3488159 = 5232239) B5232239
theorem B5233825 : Blo 1451545 5233825 := bstep (se 2 (by rfl) ⟨1962684, by rfl⟩ : syracuseStep 5233825 = 3925369) B3925369
theorem B178781579 : Blo 1451545 178781579 := bstep (se 1 (by rfl) ⟨134086184, by rfl⟩ : syracuseStep 178781579 = 268172369) B268172369
theorem B7356095 : Blo 1451545 7356095 := bstep (se 1 (by rfl) ⟨5517071, by rfl⟩ : syracuseStep 7356095 = 11034143) B11034143
theorem B4652903 : Blo 1451545 4652903 := bstep (se 1 (by rfl) ⟨3489677, by rfl⟩ : syracuseStep 4652903 = 6979355) B6979355
theorem B2179739 : Blo 1451545 2179739 := bstep (se 1 (by rfl) ⟨1634804, by rfl⟩ : syracuseStep 2179739 = 3269609) B3269609
theorem B2450459 : Blo 1451545 2450459 := bstep (se 1 (by rfl) ⟨1837844, by rfl⟩ : syracuseStep 2450459 = 3675689) B3675689
theorem B2180255 : Blo 1451545 2180255 := bstep (se 1 (by rfl) ⟨1635191, by rfl⟩ : syracuseStep 2180255 = 3270383) B3270383
theorem B15713459 : Blo 1451545 15713459 := bstep (se 1 (by rfl) ⟨11785094, by rfl⟩ : syracuseStep 15713459 = 23570189) B23570189
theorem B24831197 : Blo 1451545 24831197 := bstep (se 3 (by rfl) ⟨4655849, by rfl⟩ : syracuseStep 24831197 = 9311699) B9311699
theorem B3728767 : Blo 1451545 3728767 := bstep (se 1 (by rfl) ⟨2796575, by rfl⟩ : syracuseStep 3728767 = 5593151) B5593151
theorem B4900607 : Blo 1451545 4900607 := bstep (se 1 (by rfl) ⟨3675455, by rfl⟩ : syracuseStep 4900607 = 7350911) B7350911
theorem B31426643 : Blo 1451545 31426643 := bstep (se 1 (by rfl) ⟨23569982, by rfl⟩ : syracuseStep 31426643 = 47139965) B47139965
theorem B119187719 : Blo 1451545 119187719 := bstep (se 1 (by rfl) ⟨89390789, by rfl⟩ : syracuseStep 119187719 = 178781579) B178781579
theorem B10471801 : Blo 1451545 10471801 := bstep (se 2 (by rfl) ⟨3926925, by rfl⟩ : syracuseStep 10471801 = 7853851) B7853851
theorem B4655531 : Blo 1451545 4655531 := bstep (se 1 (by rfl) ⟨3491648, by rfl⟩ : syracuseStep 4655531 = 6983297) B6983297
theorem B1452863 : Blo 1451545 1452863 := bstep (se 1 (by rfl) ⟨1089647, by rfl⟩ : syracuseStep 1452863 = 2179295) B2179295
theorem B1633135 : Blo 1451545 1633135 := bstep (se 1 (by rfl) ⟨1224851, by rfl⟩ : syracuseStep 1633135 = 2449703) B2449703
theorem B1452927 : Blo 1451545 1452927 := bstep (se 1 (by rfl) ⟨1089695, by rfl⟩ : syracuseStep 1452927 = 2179391) B2179391
theorem B18615197 : Blo 1451545 18615197 := bstep (se 3 (by rfl) ⟨3490349, by rfl⟩ : syracuseStep 18615197 = 6980699) B6980699
theorem B2452639 : Blo 1451545 2452639 := bstep (se 1 (by rfl) ⟨1839479, by rfl⟩ : syracuseStep 2452639 = 3678959) B3678959
theorem B29797591 : Blo 1451545 29797591 := bstep (se 1 (by rfl) ⟨22348193, by rfl⟩ : syracuseStep 29797591 = 44696387) B44696387
theorem B4902173 : Blo 1451545 4902173 := bstep (se 3 (by rfl) ⟨919157, by rfl⟩ : syracuseStep 4902173 = 1838315) B1838315
theorem B1453383 : Blo 1451545 1453383 := bstep (se 1 (by rfl) ⟨1090037, by rfl⟩ : syracuseStep 1453383 = 2180075) B2180075
theorem B4903037 : Blo 1451545 4903037 := bstep (se 3 (by rfl) ⟨919319, by rfl⟩ : syracuseStep 4903037 = 1838639) B1838639
theorem B2617993 : Blo 1451545 2617993 := bstep (se 2 (by rfl) ⟨981747, by rfl⟩ : syracuseStep 2617993 = 1963495) B1963495
theorem B12407741 : Blo 1451545 12407741 := bstep (se 3 (by rfl) ⟨2326451, by rfl⟩ : syracuseStep 12407741 = 4652903) B4652903
theorem B4904063 : Blo 1451545 4904063 := bstep (se 1 (by rfl) ⟨3678047, by rfl⟩ : syracuseStep 4904063 = 7356095) B7356095
theorem B134100629 : Blo 1451545 134100629 := bstep (se 6 (by rfl) ⟨3142983, by rfl⟩ : syracuseStep 134100629 = 6285967) B6285967
theorem B10467245 : Blo 1451545 10467245 := bstep (se 3 (by rfl) ⟨1962608, by rfl⟩ : syracuseStep 10467245 = 3925217) B3925217
theorem B5593439 : Blo 1451545 5593439 := bstep (se 1 (by rfl) ⟨4195079, by rfl⟩ : syracuseStep 5593439 = 8390159) B8390159
theorem B2177663 : Blo 1451545 2177663 := bstep (se 1 (by rfl) ⟨1633247, by rfl⟩ : syracuseStep 2177663 = 3266495) B3266495
theorem B2177819 : Blo 1451545 2177819 := bstep (se 1 (by rfl) ⟨1633364, by rfl⟩ : syracuseStep 2177819 = 3266729) B3266729
theorem B6978433 : Blo 1451545 6978433 := bstep (se 2 (by rfl) ⟨2616912, by rfl⟩ : syracuseStep 6978433 = 5233825) B5233825
theorem B153017261 : Blo 1451545 153017261 := bstep (se 3 (by rfl) ⟨28690736, by rfl⟩ : syracuseStep 153017261 = 57381473) B57381473
theorem B2325439 : Blo 1451545 2325439 := bstep (se 1 (by rfl) ⟨1744079, by rfl⟩ : syracuseStep 2325439 = 3488159) B3488159
theorem B13966319 : Blo 1451545 13966319 := bstep (se 1 (by rfl) ⟨10474739, by rfl⟩ : syracuseStep 13966319 = 20949479) B20949479
theorem B5741927 : Blo 1451545 5741927 := bstep (se 1 (by rfl) ⟨4306445, by rfl⟩ : syracuseStep 5741927 = 8612891) B8612891
theorem B23551559 : Blo 1451545 23551559 := bstep (se 1 (by rfl) ⟨17663669, by rfl⟩ : syracuseStep 23551559 = 35327339) B35327339
theorem B1990427 : Blo 1451545 1990427 := bstep (se 1 (by rfl) ⟨1492820, by rfl⟩ : syracuseStep 1990427 = 2985641) B2985641
theorem B3678119 : Blo 1451545 3678119 := bstep (se 1 (by rfl) ⟨2758589, by rfl⟩ : syracuseStep 3678119 = 5517179) B5517179
theorem B3268691 : Blo 1451545 3268691 := bstep (se 1 (by rfl) ⟨2451518, by rfl⟩ : syracuseStep 3268691 = 4903037) B4903037
theorem B3269375 : Blo 1451545 3269375 := bstep (se 1 (by rfl) ⟨2452031, by rfl⟩ : syracuseStep 3269375 = 4904063) B4904063
theorem B3490657 : Blo 1451545 3490657 := bstep (se 2 (by rfl) ⟨1308996, by rfl⟩ : syracuseStep 3490657 = 2617993) B2617993
theorem B89400419 : Blo 1451545 89400419 := bstep (se 1 (by rfl) ⟨67050314, by rfl⟩ : syracuseStep 89400419 = 134100629) B134100629
theorem B3270185 : Blo 1451545 3270185 := bstep (se 2 (by rfl) ⟨1226319, by rfl⟩ : syracuseStep 3270185 = 2452639) B2452639
theorem B3728959 : Blo 1451545 3728959 := bstep (se 1 (by rfl) ⟨2796719, by rfl⟩ : syracuseStep 3728959 = 5593439) B5593439
theorem B1451775 : Blo 1451545 1451775 := bstep (se 1 (by rfl) ⟨1088831, by rfl⟩ : syracuseStep 1451775 = 2177663) B2177663
theorem B1451879 : Blo 1451545 1451879 := bstep (se 1 (by rfl) ⟨1088909, by rfl⟩ : syracuseStep 1451879 = 2177819) B2177819
theorem B3827951 : Blo 1451545 3827951 := bstep (se 1 (by rfl) ⟨2870963, by rfl⟩ : syracuseStep 3827951 = 5741927) B5741927
theorem B2452079 : Blo 1451545 2452079 := bstep (se 1 (by rfl) ⟨1839059, by rfl⟩ : syracuseStep 2452079 = 3678119) B3678119
theorem B1453159 : Blo 1451545 1453159 := bstep (se 1 (by rfl) ⟨1089869, by rfl⟩ : syracuseStep 1453159 = 2179739) B2179739
theorem B13962401 : Blo 1451545 13962401 := bstep (se 2 (by rfl) ⟨5235900, by rfl⟩ : syracuseStep 13962401 = 10471801) B10471801
theorem B1633639 : Blo 1451545 1633639 := bstep (se 1 (by rfl) ⟨1225229, by rfl⟩ : syracuseStep 1633639 = 2450459) B2450459
theorem B1453503 : Blo 1451545 1453503 := bstep (se 1 (by rfl) ⟨1090127, by rfl⟩ : syracuseStep 1453503 = 2180255) B2180255
theorem B20951095 : Blo 1451545 20951095 := bstep (se 1 (by rfl) ⟨15713321, by rfl⟩ : syracuseStep 20951095 = 31426643) B31426643
theorem B79458479 : Blo 1451545 79458479 := bstep (se 1 (by rfl) ⟨59593859, by rfl⟩ : syracuseStep 79458479 = 119187719) B119187719
theorem B102011507 : Blo 1451545 102011507 := bstep (se 1 (by rfl) ⟨76508630, by rfl⟩ : syracuseStep 102011507 = 153017261) B153017261
theorem B9310879 : Blo 1451545 9310879 := bstep (se 1 (by rfl) ⟨6983159, by rfl⟩ : syracuseStep 9310879 = 13966319) B13966319
theorem B15701039 : Blo 1451545 15701039 := bstep (se 1 (by rfl) ⟨11775779, by rfl⟩ : syracuseStep 15701039 = 23551559) B23551559
theorem B8271827 : Blo 1451545 8271827 := bstep (se 1 (by rfl) ⟨6203870, by rfl⟩ : syracuseStep 8271827 = 12407741) B12407741
theorem B10475639 : Blo 1451545 10475639 := bstep (se 1 (by rfl) ⟨7856729, by rfl⟩ : syracuseStep 10475639 = 15713459) B15713459
theorem B16554131 : Blo 1451545 16554131 := bstep (se 1 (by rfl) ⟨12415598, by rfl⟩ : syracuseStep 16554131 = 24831197) B24831197
theorem B2177513 : Blo 1451545 2177513 := bstep (se 2 (by rfl) ⟨816567, by rfl⟩ : syracuseStep 2177513 = 1633135) B1633135
theorem B3267071 : Blo 1451545 3267071 := bstep (se 1 (by rfl) ⟨2450303, by rfl⟩ : syracuseStep 3267071 = 4900607) B4900607
theorem B9304577 : Blo 1451545 9304577 := bstep (se 2 (by rfl) ⟨3489216, by rfl⟩ : syracuseStep 9304577 = 6978433) B6978433
theorem B6978163 : Blo 1451545 6978163 := bstep (se 1 (by rfl) ⟨5233622, by rfl⟩ : syracuseStep 6978163 = 10467245) B10467245
theorem B3103687 : Blo 1451545 3103687 := bstep (se 1 (by rfl) ⟨2327765, by rfl⟩ : syracuseStep 3103687 = 4655531) B4655531
theorem B39730121 : Blo 1451545 39730121 := bstep (se 2 (by rfl) ⟨14898795, by rfl⟩ : syracuseStep 39730121 = 29797591) B29797591
theorem B4971689 : Blo 1451545 4971689 := bstep (se 2 (by rfl) ⟨1864383, by rfl⟩ : syracuseStep 4971689 = 3728767) B3728767
theorem B12410131 : Blo 1451545 12410131 := bstep (se 1 (by rfl) ⟨9307598, by rfl⟩ : syracuseStep 12410131 = 18615197) B18615197
theorem B5307805 : Blo 1451545 5307805 := bstep (se 3 (by rfl) ⟨995213, by rfl⟩ : syracuseStep 5307805 = 1990427) B1990427
theorem B3268115 : Blo 1451545 3268115 := bstep (se 1 (by rfl) ⟨2451086, by rfl⟩ : syracuseStep 3268115 = 4902173) B4902173
theorem B12402341 : Blo 1451545 12402341 := bstep (se 4 (by rfl) ⟨1162719, by rfl⟩ : syracuseStep 12402341 = 2325439) B2325439
theorem B2179127 : Blo 1451545 2179127 := bstep (se 1 (by rfl) ⟨1634345, by rfl⟩ : syracuseStep 2179127 = 3268691) B3268691
theorem B27934793 : Blo 1451545 27934793 := bstep (se 2 (by rfl) ⟨10475547, by rfl⟩ : syracuseStep 27934793 = 20951095) B20951095
theorem B2179583 : Blo 1451545 2179583 := bstep (se 1 (by rfl) ⟨1634687, by rfl⟩ : syracuseStep 2179583 = 3269375) B3269375
theorem B2180123 : Blo 1451545 2180123 := bstep (se 1 (by rfl) ⟨1635092, by rfl⟩ : syracuseStep 2180123 = 3270185) B3270185
theorem B4138249 : Blo 1451545 4138249 := bstep (se 2 (by rfl) ⟨1551843, by rfl⟩ : syracuseStep 4138249 = 3103687) B3103687
theorem B5514551 : Blo 1451545 5514551 := bstep (se 1 (by rfl) ⟨4135913, by rfl⟩ : syracuseStep 5514551 = 8271827) B8271827
theorem B11036087 : Blo 1451545 11036087 := bstep (se 1 (by rfl) ⟨8277065, by rfl⟩ : syracuseStep 11036087 = 16554131) B16554131
theorem B1451675 : Blo 1451545 1451675 := bstep (se 1 (by rfl) ⟨1088756, by rfl⟩ : syracuseStep 1451675 = 2177513) B2177513
theorem B6203051 : Blo 1451545 6203051 := bstep (se 1 (by rfl) ⟨4652288, by rfl⟩ : syracuseStep 6203051 = 9304577) B9304577
theorem B26486747 : Blo 1451545 26486747 := bstep (se 1 (by rfl) ⟨19865060, by rfl⟩ : syracuseStep 26486747 = 39730121) B39730121
theorem B9308267 : Blo 1451545 9308267 := bstep (se 1 (by rfl) ⟨6981200, by rfl⟩ : syracuseStep 9308267 = 13962401) B13962401
theorem B8268227 : Blo 1451545 8268227 := bstep (se 1 (by rfl) ⟨6201170, by rfl⟩ : syracuseStep 8268227 = 12402341) B12402341
theorem B52972319 : Blo 1451545 52972319 := bstep (se 1 (by rfl) ⟨39729239, by rfl⟩ : syracuseStep 52972319 = 79458479) B79458479
theorem B59600279 : Blo 1451545 59600279 := bstep (se 1 (by rfl) ⟨44700209, by rfl⟩ : syracuseStep 59600279 = 89400419) B89400419
theorem B12414505 : Blo 1451545 12414505 := bstep (se 2 (by rfl) ⟨4655439, by rfl⟩ : syracuseStep 12414505 = 9310879) B9310879
theorem B6983759 : Blo 1451545 6983759 := bstep (se 1 (by rfl) ⟨5237819, by rfl⟩ : syracuseStep 6983759 = 10475639) B10475639
theorem B2551967 : Blo 1451545 2551967 := bstep (se 1 (by rfl) ⟨1913975, by rfl⟩ : syracuseStep 2551967 = 3827951) B3827951
theorem B1634719 : Blo 1451545 1634719 := bstep (se 1 (by rfl) ⟨1226039, by rfl⟩ : syracuseStep 1634719 = 2452079) B2452079
theorem B18616837 : Blo 1451545 18616837 := bstep (se 4 (by rfl) ⟨1745328, by rfl⟩ : syracuseStep 18616837 = 3490657) B3490657
theorem B3314459 : Blo 1451545 3314459 := bstep (se 1 (by rfl) ⟨2485844, by rfl⟩ : syracuseStep 3314459 = 4971689) B4971689
theorem B19887781 : Blo 1451545 19887781 := bstep (se 4 (by rfl) ⟨1864479, by rfl⟩ : syracuseStep 19887781 = 3728959) B3728959
theorem B68007671 : Blo 1451545 68007671 := bstep (se 1 (by rfl) ⟨51005753, by rfl⟩ : syracuseStep 68007671 = 102011507) B102011507
theorem B10467359 : Blo 1451545 10467359 := bstep (se 1 (by rfl) ⟨7850519, by rfl⟩ : syracuseStep 10467359 = 15701039) B15701039
theorem B9304217 : Blo 1451545 9304217 := bstep (se 2 (by rfl) ⟨3489081, by rfl⟩ : syracuseStep 9304217 = 6978163) B6978163
theorem B2178047 : Blo 1451545 2178047 := bstep (se 1 (by rfl) ⟨1633535, by rfl⟩ : syracuseStep 2178047 = 3267071) B3267071
theorem B16546841 : Blo 1451545 16546841 := bstep (se 2 (by rfl) ⟨6205065, by rfl⟩ : syracuseStep 16546841 = 12410131) B12410131
theorem B2178185 : Blo 1451545 2178185 := bstep (se 2 (by rfl) ⟨816819, by rfl⟩ : syracuseStep 2178185 = 1633639) B1633639
theorem B7077073 : Blo 1451545 7077073 := bstep (se 2 (by rfl) ⟨2653902, by rfl⟩ : syracuseStep 7077073 = 5307805) B5307805
theorem B2178743 : Blo 1451545 2178743 := bstep (se 1 (by rfl) ⟨1634057, by rfl⟩ : syracuseStep 2178743 = 3268115) B3268115
theorem B2179625 : Blo 1451545 2179625 := bstep (se 2 (by rfl) ⟨817359, by rfl⟩ : syracuseStep 2179625 = 1634719) B1634719
theorem B24822449 : Blo 1451545 24822449 := bstep (se 2 (by rfl) ⟨9308418, by rfl⟩ : syracuseStep 24822449 = 18616837) B18616837
theorem B7357391 : Blo 1451545 7357391 := bstep (se 1 (by rfl) ⟨5518043, by rfl⟩ : syracuseStep 7357391 = 11036087) B11036087
theorem B6202811 : Blo 1451545 6202811 := bstep (se 1 (by rfl) ⟨4652108, by rfl⟩ : syracuseStep 6202811 = 9304217) B9304217
theorem B1452031 : Blo 1451545 1452031 := bstep (se 1 (by rfl) ⟨1089023, by rfl⟩ : syracuseStep 1452031 = 2178047) B2178047
theorem B1452123 : Blo 1451545 1452123 := bstep (se 1 (by rfl) ⟨1089092, by rfl⟩ : syracuseStep 1452123 = 2178185) B2178185
theorem B39733519 : Blo 1451545 39733519 := bstep (se 1 (by rfl) ⟨29800139, by rfl⟩ : syracuseStep 39733519 = 59600279) B59600279
theorem B1452495 : Blo 1451545 1452495 := bstep (se 1 (by rfl) ⟨1089371, by rfl⟩ : syracuseStep 1452495 = 2178743) B2178743
theorem B1452751 : Blo 1451545 1452751 := bstep (se 1 (by rfl) ⟨1089563, by rfl⟩ : syracuseStep 1452751 = 2179127) B2179127
theorem B18623195 : Blo 1451545 18623195 := bstep (se 1 (by rfl) ⟨13967396, by rfl⟩ : syracuseStep 18623195 = 27934793) B27934793
theorem B4655839 : Blo 1451545 4655839 := bstep (se 1 (by rfl) ⟨3491879, by rfl⟩ : syracuseStep 4655839 = 6983759) B6983759
theorem B1453055 : Blo 1451545 1453055 := bstep (se 1 (by rfl) ⟨1089791, by rfl⟩ : syracuseStep 1453055 = 2179583) B2179583
theorem B1453415 : Blo 1451545 1453415 := bstep (se 1 (by rfl) ⟨1090061, by rfl⟩ : syracuseStep 1453415 = 2180123) B2180123
theorem B45338447 : Blo 1451545 45338447 := bstep (se 1 (by rfl) ⟨34003835, by rfl⟩ : syracuseStep 45338447 = 68007671) B68007671
theorem B17657831 : Blo 1451545 17657831 := bstep (se 1 (by rfl) ⟨13243373, by rfl⟩ : syracuseStep 17657831 = 26486747) B26486747
theorem B6205511 : Blo 1451545 6205511 := bstep (se 1 (by rfl) ⟨4654133, by rfl⟩ : syracuseStep 6205511 = 9308267) B9308267
theorem B5517665 : Blo 1451545 5517665 := bstep (se 2 (by rfl) ⟨2069124, by rfl⟩ : syracuseStep 5517665 = 4138249) B4138249
theorem B11031227 : Blo 1451545 11031227 := bstep (se 1 (by rfl) ⟨8273420, by rfl⟩ : syracuseStep 11031227 = 16546841) B16546841
theorem B16552673 : Blo 1451545 16552673 := bstep (se 2 (by rfl) ⟨6207252, by rfl⟩ : syracuseStep 16552673 = 12414505) B12414505
theorem B1701311 : Blo 1451545 1701311 := bstep (se 1 (by rfl) ⟨1275983, by rfl⟩ : syracuseStep 1701311 = 2551967) B2551967
theorem B3676367 : Blo 1451545 3676367 := bstep (se 1 (by rfl) ⟨2757275, by rfl⟩ : syracuseStep 3676367 = 5514551) B5514551
theorem B4135367 : Blo 1451545 4135367 := bstep (se 1 (by rfl) ⟨3101525, by rfl⟩ : syracuseStep 4135367 = 6203051) B6203051
theorem B6978239 : Blo 1451545 6978239 := bstep (se 1 (by rfl) ⟨5233679, by rfl⟩ : syracuseStep 6978239 = 10467359) B10467359
theorem B9436097 : Blo 1451545 9436097 := bstep (se 2 (by rfl) ⟨3538536, by rfl⟩ : syracuseStep 9436097 = 7077073) B7077073
theorem B5512151 : Blo 1451545 5512151 := bstep (se 1 (by rfl) ⟨4134113, by rfl⟩ : syracuseStep 5512151 = 8268227) B8268227
theorem B35314879 : Blo 1451545 35314879 := bstep (se 1 (by rfl) ⟨26486159, by rfl⟩ : syracuseStep 35314879 = 52972319) B52972319
theorem B8838557 : Blo 1451545 8838557 := bstep (se 3 (by rfl) ⟨1657229, by rfl⟩ : syracuseStep 8838557 = 3314459) B3314459
theorem B26517041 : Blo 1451545 26517041 := bstep (se 2 (by rfl) ⟨9943890, by rfl⟩ : syracuseStep 26517041 = 19887781) B19887781
theorem B4137007 : Blo 1451545 4137007 := bstep (se 1 (by rfl) ⟨3102755, by rfl⟩ : syracuseStep 4137007 = 6205511) B6205511
theorem B3678443 : Blo 1451545 3678443 := bstep (se 1 (by rfl) ⟨2758832, by rfl⟩ : syracuseStep 3678443 = 5517665) B5517665
theorem B52978025 : Blo 1451545 52978025 := bstep (se 2 (by rfl) ⟨19866759, by rfl⟩ : syracuseStep 52978025 = 39733519) B39733519
theorem B16548299 : Blo 1451545 16548299 := bstep (se 1 (by rfl) ⟨12411224, by rfl⟩ : syracuseStep 16548299 = 24822449) B24822449
theorem B11035115 : Blo 1451545 11035115 := bstep (se 1 (by rfl) ⟨8276336, by rfl⟩ : syracuseStep 11035115 = 16552673) B16552673
theorem B2450911 : Blo 1451545 2450911 := bstep (se 1 (by rfl) ⟨1838183, by rfl⟩ : syracuseStep 2450911 = 3676367) B3676367
theorem B5892371 : Blo 1451545 5892371 := bstep (se 1 (by rfl) ⟨4419278, by rfl⟩ : syracuseStep 5892371 = 8838557) B8838557
theorem B1453083 : Blo 1451545 1453083 := bstep (se 1 (by rfl) ⟨1089812, by rfl⟩ : syracuseStep 1453083 = 2179625) B2179625
theorem B2756911 : Blo 1451545 2756911 := bstep (se 1 (by rfl) ⟨2067683, by rfl⟩ : syracuseStep 2756911 = 4135367) B4135367
theorem B12415463 : Blo 1451545 12415463 := bstep (se 1 (by rfl) ⟨9311597, by rfl⟩ : syracuseStep 12415463 = 18623195) B18623195
theorem B3674767 : Blo 1451545 3674767 := bstep (se 1 (by rfl) ⟨2756075, by rfl⟩ : syracuseStep 3674767 = 5512151) B5512151
theorem B30225631 : Blo 1451545 30225631 := bstep (se 1 (by rfl) ⟨22669223, by rfl⟩ : syracuseStep 30225631 = 45338447) B45338447
theorem B7354151 : Blo 1451545 7354151 := bstep (se 1 (by rfl) ⟨5515613, by rfl⟩ : syracuseStep 7354151 = 11031227) B11031227
theorem B4904927 : Blo 1451545 4904927 := bstep (se 1 (by rfl) ⟨3678695, by rfl⟩ : syracuseStep 4904927 = 7357391) B7357391
theorem B4135207 : Blo 1451545 4135207 := bstep (se 1 (by rfl) ⟨3101405, by rfl⟩ : syracuseStep 4135207 = 6202811) B6202811
theorem B6207785 : Blo 1451545 6207785 := bstep (se 2 (by rfl) ⟨2327919, by rfl⟩ : syracuseStep 6207785 = 4655839) B4655839
theorem B4536829 : Blo 1451545 4536829 := bstep (se 3 (by rfl) ⟨850655, by rfl⟩ : syracuseStep 4536829 = 1701311) B1701311
theorem B47086505 : Blo 1451545 47086505 := bstep (se 2 (by rfl) ⟨17657439, by rfl⟩ : syracuseStep 47086505 = 35314879) B35314879
theorem B4652159 : Blo 1451545 4652159 := bstep (se 1 (by rfl) ⟨3489119, by rfl⟩ : syracuseStep 4652159 = 6978239) B6978239
theorem B6290731 : Blo 1451545 6290731 := bstep (se 1 (by rfl) ⟨4718048, by rfl⟩ : syracuseStep 6290731 = 9436097) B9436097
theorem B17678027 : Blo 1451545 17678027 := bstep (se 1 (by rfl) ⟨13258520, by rfl⟩ : syracuseStep 17678027 = 26517041) B26517041
theorem B11771887 : Blo 1451545 11771887 := bstep (se 1 (by rfl) ⟨8828915, by rfl⟩ : syracuseStep 11771887 = 17657831) B17657831
theorem B7356743 : Blo 1451545 7356743 := bstep (se 1 (by rfl) ⟨5517557, by rfl⟩ : syracuseStep 7356743 = 11035115) B11035115
theorem B5513609 : Blo 1451545 5513609 := bstep (se 2 (by rfl) ⟨2067603, by rfl⟩ : syracuseStep 5513609 = 4135207) B4135207
theorem B4899689 : Blo 1451545 4899689 := bstep (se 2 (by rfl) ⟨1837383, by rfl⟩ : syracuseStep 4899689 = 3674767) B3674767
theorem B3269951 : Blo 1451545 3269951 := bstep (se 1 (by rfl) ⟨2452463, by rfl⟩ : syracuseStep 3269951 = 4904927) B4904927
theorem B4138523 : Blo 1451545 4138523 := bstep (se 1 (by rfl) ⟨3103892, by rfl⟩ : syracuseStep 4138523 = 6207785) B6207785
theorem B5516009 : Blo 1451545 5516009 := bstep (se 2 (by rfl) ⟨2068503, by rfl⟩ : syracuseStep 5516009 = 4137007) B4137007
theorem B2452295 : Blo 1451545 2452295 := bstep (se 1 (by rfl) ⟨1839221, by rfl⟩ : syracuseStep 2452295 = 3678443) B3678443
theorem B35318683 : Blo 1451545 35318683 := bstep (se 1 (by rfl) ⟨26489012, by rfl⟩ : syracuseStep 35318683 = 52978025) B52978025
theorem B8276975 : Blo 1451545 8276975 := bstep (se 1 (by rfl) ⟨6207731, by rfl⟩ : syracuseStep 8276975 = 12415463) B12415463
theorem B12405757 : Blo 1451545 12405757 := bstep (se 3 (by rfl) ⟨2326079, by rfl⟩ : syracuseStep 12405757 = 4652159) B4652159
theorem B4902767 : Blo 1451545 4902767 := bstep (se 1 (by rfl) ⟨3677075, by rfl⟩ : syracuseStep 4902767 = 7354151) B7354151
theorem B3928247 : Blo 1451545 3928247 := bstep (se 1 (by rfl) ⟨2946185, by rfl⟩ : syracuseStep 3928247 = 5892371) B5892371
theorem B40300841 : Blo 1451545 40300841 := bstep (se 2 (by rfl) ⟨15112815, by rfl⟩ : syracuseStep 40300841 = 30225631) B30225631
theorem B11785351 : Blo 1451545 11785351 := bstep (se 1 (by rfl) ⟨8839013, by rfl⟩ : syracuseStep 11785351 = 17678027) B17678027
theorem B24196421 : Blo 1451545 24196421 := bstep (se 4 (by rfl) ⟨2268414, by rfl⟩ : syracuseStep 24196421 = 4536829) B4536829
theorem B11032199 : Blo 1451545 11032199 := bstep (se 1 (by rfl) ⟨8274149, by rfl⟩ : syracuseStep 11032199 = 16548299) B16548299
theorem B3675881 : Blo 1451545 3675881 := bstep (se 2 (by rfl) ⟨1378455, by rfl⟩ : syracuseStep 3675881 = 2756911) B2756911
theorem B8387641 : Blo 1451545 8387641 := bstep (se 2 (by rfl) ⟨3145365, by rfl⟩ : syracuseStep 8387641 = 6290731) B6290731
theorem B31391003 : Blo 1451545 31391003 := bstep (se 1 (by rfl) ⟨23543252, by rfl⟩ : syracuseStep 31391003 = 47086505) B47086505
theorem B3267881 : Blo 1451545 3267881 := bstep (se 2 (by rfl) ⟨1225455, by rfl⟩ : syracuseStep 3267881 = 2450911) B2450911
theorem B15695849 : Blo 1451545 15695849 := bstep (se 2 (by rfl) ⟨5885943, by rfl⟩ : syracuseStep 15695849 = 11771887) B11771887
theorem B2179967 : Blo 1451545 2179967 := bstep (se 1 (by rfl) ⟨1634975, by rfl⟩ : syracuseStep 2179967 = 3269951) B3269951
theorem B16130947 : Blo 1451545 16130947 := bstep (se 1 (by rfl) ⟨12098210, by rfl⟩ : syracuseStep 16130947 = 24196421) B24196421
theorem B2450587 : Blo 1451545 2450587 := bstep (se 1 (by rfl) ⟨1837940, by rfl⟩ : syracuseStep 2450587 = 3675881) B3675881
theorem B16541009 : Blo 1451545 16541009 := bstep (se 2 (by rfl) ⟨6202878, by rfl⟩ : syracuseStep 16541009 = 12405757) B12405757
theorem B11183521 : Blo 1451545 11183521 := bstep (se 2 (by rfl) ⟨4193820, by rfl⟩ : syracuseStep 11183521 = 8387641) B8387641
theorem B15713801 : Blo 1451545 15713801 := bstep (se 2 (by rfl) ⟨5892675, by rfl⟩ : syracuseStep 15713801 = 11785351) B11785351
theorem B10463899 : Blo 1451545 10463899 := bstep (se 1 (by rfl) ⟨7847924, by rfl⟩ : syracuseStep 10463899 = 15695849) B15695849
theorem B47091577 : Blo 1451545 47091577 := bstep (se 2 (by rfl) ⟨17659341, by rfl⟩ : syracuseStep 47091577 = 35318683) B35318683
theorem B1634863 : Blo 1451545 1634863 := bstep (se 1 (by rfl) ⟨1226147, by rfl⟩ : syracuseStep 1634863 = 2452295) B2452295
theorem B5517983 : Blo 1451545 5517983 := bstep (se 1 (by rfl) ⟨4138487, by rfl⟩ : syracuseStep 5517983 = 8276975) B8276975
theorem B20927335 : Blo 1451545 20927335 := bstep (se 1 (by rfl) ⟨15695501, by rfl⟩ : syracuseStep 20927335 = 31391003) B31391003
theorem B2618831 : Blo 1451545 2618831 := bstep (se 1 (by rfl) ⟨1964123, by rfl⟩ : syracuseStep 2618831 = 3928247) B3928247
theorem B26867227 : Blo 1451545 26867227 := bstep (se 1 (by rfl) ⟨20150420, by rfl⟩ : syracuseStep 26867227 = 40300841) B40300841
theorem B4904495 : Blo 1451545 4904495 := bstep (se 1 (by rfl) ⟨3678371, by rfl⟩ : syracuseStep 4904495 = 7356743) B7356743
theorem B3675739 : Blo 1451545 3675739 := bstep (se 1 (by rfl) ⟨2756804, by rfl⟩ : syracuseStep 3675739 = 5513609) B5513609
theorem B3266459 : Blo 1451545 3266459 := bstep (se 1 (by rfl) ⟨2449844, by rfl⟩ : syracuseStep 3266459 = 4899689) B4899689
theorem B2759015 : Blo 1451545 2759015 := bstep (se 1 (by rfl) ⟨2069261, by rfl⟩ : syracuseStep 2759015 = 4138523) B4138523
theorem B7354799 : Blo 1451545 7354799 := bstep (se 1 (by rfl) ⟨5516099, by rfl⟩ : syracuseStep 7354799 = 11032199) B11032199
theorem B3677339 : Blo 1451545 3677339 := bstep (se 1 (by rfl) ⟨2758004, by rfl⟩ : syracuseStep 3677339 = 5516009) B5516009
theorem B2178587 : Blo 1451545 2178587 := bstep (se 1 (by rfl) ⟨1633940, by rfl⟩ : syracuseStep 2178587 = 3267881) B3267881
theorem B3268511 : Blo 1451545 3268511 := bstep (se 1 (by rfl) ⟨2451383, by rfl⟩ : syracuseStep 3268511 = 4902767) B4902767
theorem B3678655 : Blo 1451545 3678655 := bstep (se 1 (by rfl) ⟨2758991, by rfl⟩ : syracuseStep 3678655 = 5517983) B5517983
theorem B2179817 : Blo 1451545 2179817 := bstep (se 2 (by rfl) ⟨817431, by rfl⟩ : syracuseStep 2179817 = 1634863) B1634863
theorem B13951865 : Blo 1451545 13951865 := bstep (se 2 (by rfl) ⟨5231949, by rfl⟩ : syracuseStep 13951865 = 10463899) B10463899
theorem B11027339 : Blo 1451545 11027339 := bstep (se 1 (by rfl) ⟨8270504, by rfl⟩ : syracuseStep 11027339 = 16541009) B16541009
theorem B1745887 : Blo 1451545 1745887 := bstep (se 1 (by rfl) ⟨1309415, by rfl⟩ : syracuseStep 1745887 = 2618831) B2618831
theorem B3269663 : Blo 1451545 3269663 := bstep (se 1 (by rfl) ⟨2452247, by rfl⟩ : syracuseStep 3269663 = 4904495) B4904495
theorem B27903113 : Blo 1451545 27903113 := bstep (se 2 (by rfl) ⟨10463667, by rfl⟩ : syracuseStep 27903113 = 20927335) B20927335
theorem B14911361 : Blo 1451545 14911361 := bstep (se 2 (by rfl) ⟨5591760, by rfl⟩ : syracuseStep 14911361 = 11183521) B11183521
theorem B2451559 : Blo 1451545 2451559 := bstep (se 1 (by rfl) ⟨1838669, by rfl⟩ : syracuseStep 2451559 = 3677339) B3677339
theorem B4900985 : Blo 1451545 4900985 := bstep (se 2 (by rfl) ⟨1837869, by rfl⟩ : syracuseStep 4900985 = 3675739) B3675739
theorem B1452391 : Blo 1451545 1452391 := bstep (se 1 (by rfl) ⟨1089293, by rfl⟩ : syracuseStep 1452391 = 2178587) B2178587
theorem B1453311 : Blo 1451545 1453311 := bstep (se 1 (by rfl) ⟨1089983, by rfl⟩ : syracuseStep 1453311 = 2179967) B2179967
theorem B21507929 : Blo 1451545 21507929 := bstep (se 2 (by rfl) ⟨8065473, by rfl⟩ : syracuseStep 21507929 = 16130947) B16130947
theorem B1839343 : Blo 1451545 1839343 := bstep (se 1 (by rfl) ⟨1379507, by rfl⟩ : syracuseStep 1839343 = 2759015) B2759015
theorem B4903199 : Blo 1451545 4903199 := bstep (se 1 (by rfl) ⟨3677399, by rfl⟩ : syracuseStep 4903199 = 7354799) B7354799
theorem B62788769 : Blo 1451545 62788769 := bstep (se 2 (by rfl) ⟨23545788, by rfl⟩ : syracuseStep 62788769 = 47091577) B47091577
theorem B10475867 : Blo 1451545 10475867 := bstep (se 1 (by rfl) ⟨7856900, by rfl⟩ : syracuseStep 10475867 = 15713801) B15713801
theorem B2177639 : Blo 1451545 2177639 := bstep (se 1 (by rfl) ⟨1633229, by rfl⟩ : syracuseStep 2177639 = 3266459) B3266459
theorem B3267449 : Blo 1451545 3267449 := bstep (se 2 (by rfl) ⟨1225293, by rfl⟩ : syracuseStep 3267449 = 2450587) B2450587
theorem B35822969 : Blo 1451545 35822969 := bstep (se 2 (by rfl) ⟨13433613, by rfl⟩ : syracuseStep 35822969 = 26867227) B26867227
theorem B2179007 : Blo 1451545 2179007 := bstep (se 1 (by rfl) ⟨1634255, by rfl⟩ : syracuseStep 2179007 = 3268511) B3268511
theorem B3268745 : Blo 1451545 3268745 := bstep (se 2 (by rfl) ⟨1225779, by rfl⟩ : syracuseStep 3268745 = 2451559) B2451559
theorem B3268799 : Blo 1451545 3268799 := bstep (se 1 (by rfl) ⟨2451599, by rfl⟩ : syracuseStep 3268799 = 4903199) B4903199
theorem B2179775 : Blo 1451545 2179775 := bstep (se 1 (by rfl) ⟨1634831, by rfl⟩ : syracuseStep 2179775 = 3269663) B3269663
theorem B2327849 : Blo 1451545 2327849 := bstep (se 2 (by rfl) ⟨872943, by rfl⟩ : syracuseStep 2327849 = 1745887) B1745887
theorem B1451759 : Blo 1451545 1451759 := bstep (se 1 (by rfl) ⟨1088819, by rfl⟩ : syracuseStep 1451759 = 2177639) B2177639
theorem B23881979 : Blo 1451545 23881979 := bstep (se 1 (by rfl) ⟨17911484, by rfl⟩ : syracuseStep 23881979 = 35822969) B35822969
theorem B14338619 : Blo 1451545 14338619 := bstep (se 1 (by rfl) ⟨10753964, by rfl⟩ : syracuseStep 14338619 = 21507929) B21507929
theorem B1452671 : Blo 1451545 1452671 := bstep (se 1 (by rfl) ⟨1089503, by rfl⟩ : syracuseStep 1452671 = 2179007) B2179007
theorem B2452457 : Blo 1451545 2452457 := bstep (se 2 (by rfl) ⟨919671, by rfl⟩ : syracuseStep 2452457 = 1839343) B1839343
theorem B1453211 : Blo 1451545 1453211 := bstep (se 1 (by rfl) ⟨1089908, by rfl⟩ : syracuseStep 1453211 = 2179817) B2179817
theorem B9301243 : Blo 1451545 9301243 := bstep (se 1 (by rfl) ⟨6975932, by rfl⟩ : syracuseStep 9301243 = 13951865) B13951865
theorem B7351559 : Blo 1451545 7351559 := bstep (se 1 (by rfl) ⟨5513669, by rfl⟩ : syracuseStep 7351559 = 11027339) B11027339
theorem B9940907 : Blo 1451545 9940907 := bstep (se 1 (by rfl) ⟨7455680, by rfl⟩ : syracuseStep 9940907 = 14911361) B14911361
theorem B6983911 : Blo 1451545 6983911 := bstep (se 1 (by rfl) ⟨5237933, by rfl⟩ : syracuseStep 6983911 = 10475867) B10475867
theorem B4904873 : Blo 1451545 4904873 := bstep (se 2 (by rfl) ⟨1839327, by rfl⟩ : syracuseStep 4904873 = 3678655) B3678655
theorem B18602075 : Blo 1451545 18602075 := bstep (se 1 (by rfl) ⟨13951556, by rfl⟩ : syracuseStep 18602075 = 27903113) B27903113
theorem B41859179 : Blo 1451545 41859179 := bstep (se 1 (by rfl) ⟨31394384, by rfl⟩ : syracuseStep 41859179 = 62788769) B62788769
theorem B3267323 : Blo 1451545 3267323 := bstep (se 1 (by rfl) ⟨2450492, by rfl⟩ : syracuseStep 3267323 = 4900985) B4900985
theorem B2178299 : Blo 1451545 2178299 := bstep (se 1 (by rfl) ⟨1633724, by rfl⟩ : syracuseStep 2178299 = 3267449) B3267449
theorem B2179163 : Blo 1451545 2179163 := bstep (se 1 (by rfl) ⟨1634372, by rfl⟩ : syracuseStep 2179163 = 3268745) B3268745
theorem B2179199 : Blo 1451545 2179199 := bstep (se 1 (by rfl) ⟨1634399, by rfl⟩ : syracuseStep 2179199 = 3268799) B3268799
theorem B3269915 : Blo 1451545 3269915 := bstep (se 1 (by rfl) ⟨2452436, by rfl⟩ : syracuseStep 3269915 = 4904873) B4904873
theorem B1452199 : Blo 1451545 1452199 := bstep (se 1 (by rfl) ⟨1089149, by rfl⟩ : syracuseStep 1452199 = 2178299) B2178299
theorem B4901039 : Blo 1451545 4901039 := bstep (se 1 (by rfl) ⟨3675779, by rfl⟩ : syracuseStep 4901039 = 7351559) B7351559
theorem B1453183 : Blo 1451545 1453183 := bstep (se 1 (by rfl) ⟨1089887, by rfl⟩ : syracuseStep 1453183 = 2179775) B2179775
theorem B1551899 : Blo 1451545 1551899 := bstep (se 1 (by rfl) ⟨1163924, by rfl⟩ : syracuseStep 1551899 = 2327849) B2327849
theorem B27906119 : Blo 1451545 27906119 := bstep (se 1 (by rfl) ⟨20929589, by rfl⟩ : syracuseStep 27906119 = 41859179) B41859179
theorem B15921319 : Blo 1451545 15921319 := bstep (se 1 (by rfl) ⟨11940989, by rfl⟩ : syracuseStep 15921319 = 23881979) B23881979
theorem B1634971 : Blo 1451545 1634971 := bstep (se 1 (by rfl) ⟨1226228, by rfl⟩ : syracuseStep 1634971 = 2452457) B2452457
theorem B9311881 : Blo 1451545 9311881 := bstep (se 2 (by rfl) ⟨3491955, by rfl⟩ : syracuseStep 9311881 = 6983911) B6983911
theorem B12401383 : Blo 1451545 12401383 := bstep (se 1 (by rfl) ⟨9301037, by rfl⟩ : syracuseStep 12401383 = 18602075) B18602075
theorem B12401657 : Blo 1451545 12401657 := bstep (se 2 (by rfl) ⟨4650621, by rfl⟩ : syracuseStep 12401657 = 9301243) B9301243
theorem B9559079 : Blo 1451545 9559079 := bstep (se 1 (by rfl) ⟨7169309, by rfl⟩ : syracuseStep 9559079 = 14338619) B14338619
theorem B2178215 : Blo 1451545 2178215 := bstep (se 1 (by rfl) ⟨1633661, by rfl⟩ : syracuseStep 2178215 = 3267323) B3267323
theorem B6627271 : Blo 1451545 6627271 := bstep (se 1 (by rfl) ⟨4970453, by rfl⟩ : syracuseStep 6627271 = 9940907) B9940907
theorem B18604079 : Blo 1451545 18604079 := bstep (se 1 (by rfl) ⟨13953059, by rfl⟩ : syracuseStep 18604079 = 27906119) B27906119
theorem B2179943 : Blo 1451545 2179943 := bstep (se 1 (by rfl) ⟨1634957, by rfl⟩ : syracuseStep 2179943 = 3269915) B3269915
theorem B2179961 : Blo 1451545 2179961 := bstep (se 2 (by rfl) ⟨817485, by rfl⟩ : syracuseStep 2179961 = 1634971) B1634971
theorem B4138397 : Blo 1451545 4138397 := bstep (se 3 (by rfl) ⟨775949, by rfl⟩ : syracuseStep 4138397 = 1551899) B1551899
theorem B8267771 : Blo 1451545 8267771 := bstep (se 1 (by rfl) ⟨6200828, by rfl⟩ : syracuseStep 8267771 = 12401657) B12401657
theorem B1452143 : Blo 1451545 1452143 := bstep (se 1 (by rfl) ⟨1089107, by rfl⟩ : syracuseStep 1452143 = 2178215) B2178215
theorem B1452775 : Blo 1451545 1452775 := bstep (se 1 (by rfl) ⟨1089581, by rfl⟩ : syracuseStep 1452775 = 2179163) B2179163
theorem B1452799 : Blo 1451545 1452799 := bstep (se 1 (by rfl) ⟨1089599, by rfl⟩ : syracuseStep 1452799 = 2179199) B2179199
theorem B21228425 : Blo 1451545 21228425 := bstep (se 2 (by rfl) ⟨7960659, by rfl⟩ : syracuseStep 21228425 = 15921319) B15921319
theorem B16535177 : Blo 1451545 16535177 := bstep (se 2 (by rfl) ⟨6200691, by rfl⟩ : syracuseStep 16535177 = 12401383) B12401383
theorem B12415841 : Blo 1451545 12415841 := bstep (se 2 (by rfl) ⟨4655940, by rfl⟩ : syracuseStep 12415841 = 9311881) B9311881
theorem B8836361 : Blo 1451545 8836361 := bstep (se 2 (by rfl) ⟨3313635, by rfl⟩ : syracuseStep 8836361 = 6627271) B6627271
theorem B3267359 : Blo 1451545 3267359 := bstep (se 1 (by rfl) ⟨2450519, by rfl⟩ : syracuseStep 3267359 = 4901039) B4901039
theorem B6372719 : Blo 1451545 6372719 := bstep (se 1 (by rfl) ⟨4779539, by rfl⟩ : syracuseStep 6372719 = 9559079) B9559079
theorem B12402719 : Blo 1451545 12402719 := bstep (se 1 (by rfl) ⟨9302039, by rfl⟩ : syracuseStep 12402719 = 18604079) B18604079
theorem B5890907 : Blo 1451545 5890907 := bstep (se 1 (by rfl) ⟨4418180, by rfl⟩ : syracuseStep 5890907 = 8836361) B8836361
theorem B8277227 : Blo 1451545 8277227 := bstep (se 1 (by rfl) ⟨6207920, by rfl⟩ : syracuseStep 8277227 = 12415841) B12415841
theorem B1453295 : Blo 1451545 1453295 := bstep (se 1 (by rfl) ⟨1089971, by rfl⟩ : syracuseStep 1453295 = 2179943) B2179943
theorem B1453307 : Blo 1451545 1453307 := bstep (se 1 (by rfl) ⟨1089980, by rfl⟩ : syracuseStep 1453307 = 2179961) B2179961
theorem B14152283 : Blo 1451545 14152283 := bstep (se 1 (by rfl) ⟨10614212, by rfl⟩ : syracuseStep 14152283 = 21228425) B21228425
theorem B4248479 : Blo 1451545 4248479 := bstep (se 1 (by rfl) ⟨3186359, by rfl⟩ : syracuseStep 4248479 = 6372719) B6372719
theorem B11023451 : Blo 1451545 11023451 := bstep (se 1 (by rfl) ⟨8267588, by rfl⟩ : syracuseStep 11023451 = 16535177) B16535177
theorem B2758931 : Blo 1451545 2758931 := bstep (se 1 (by rfl) ⟨2069198, by rfl⟩ : syracuseStep 2758931 = 4138397) B4138397
theorem B5511847 : Blo 1451545 5511847 := bstep (se 1 (by rfl) ⟨4133885, by rfl⟩ : syracuseStep 5511847 = 8267771) B8267771
theorem B2178239 : Blo 1451545 2178239 := bstep (se 1 (by rfl) ⟨1633679, by rfl⟩ : syracuseStep 2178239 = 3267359) B3267359
theorem B7348967 : Blo 1451545 7348967 := bstep (se 1 (by rfl) ⟨5511725, by rfl⟩ : syracuseStep 7348967 = 11023451) B11023451
theorem B7349129 : Blo 1451545 7349129 := bstep (se 2 (by rfl) ⟨2755923, by rfl⟩ : syracuseStep 7349129 = 5511847) B5511847
theorem B1452159 : Blo 1451545 1452159 := bstep (se 1 (by rfl) ⟨1089119, by rfl⟩ : syracuseStep 1452159 = 2178239) B2178239
theorem B8268479 : Blo 1451545 8268479 := bstep (se 1 (by rfl) ⟨6201359, by rfl⟩ : syracuseStep 8268479 = 12402719) B12402719
theorem B1839287 : Blo 1451545 1839287 := bstep (se 1 (by rfl) ⟨1379465, by rfl⟩ : syracuseStep 1839287 = 2758931) B2758931
theorem B5518151 : Blo 1451545 5518151 := bstep (se 1 (by rfl) ⟨4138613, by rfl⟩ : syracuseStep 5518151 = 8277227) B8277227
theorem B15709085 : Blo 1451545 15709085 := bstep (se 3 (by rfl) ⟨2945453, by rfl⟩ : syracuseStep 15709085 = 5890907) B5890907
theorem B9434855 : Blo 1451545 9434855 := bstep (se 1 (by rfl) ⟨7076141, by rfl⟩ : syracuseStep 9434855 = 14152283) B14152283
theorem B2832319 : Blo 1451545 2832319 := bstep (se 1 (by rfl) ⟨2124239, by rfl⟩ : syracuseStep 2832319 = 4248479) B4248479
theorem B4899311 : Blo 1451545 4899311 := bstep (se 1 (by rfl) ⟨3674483, by rfl⟩ : syracuseStep 4899311 = 7348967) B7348967
theorem B3678767 : Blo 1451545 3678767 := bstep (se 1 (by rfl) ⟨2759075, by rfl⟩ : syracuseStep 3678767 = 5518151) B5518151
theorem B4899419 : Blo 1451545 4899419 := bstep (se 1 (by rfl) ⟨3674564, by rfl⟩ : syracuseStep 4899419 = 7349129) B7349129
theorem B10472723 : Blo 1451545 10472723 := bstep (se 1 (by rfl) ⟨7854542, by rfl⟩ : syracuseStep 10472723 = 15709085) B15709085
theorem B4904765 : Blo 1451545 4904765 := bstep (se 3 (by rfl) ⟨919643, by rfl⟩ : syracuseStep 4904765 = 1839287) B1839287
theorem B6289903 : Blo 1451545 6289903 := bstep (se 1 (by rfl) ⟨4717427, by rfl⟩ : syracuseStep 6289903 = 9434855) B9434855
theorem B5512319 : Blo 1451545 5512319 := bstep (se 1 (by rfl) ⟨4134239, by rfl⟩ : syracuseStep 5512319 = 8268479) B8268479
theorem B3776425 : Blo 1451545 3776425 := bstep (se 2 (by rfl) ⟨1416159, by rfl⟩ : syracuseStep 3776425 = 2832319) B2832319
theorem B3269843 : Blo 1451545 3269843 := bstep (se 1 (by rfl) ⟨2452382, by rfl⟩ : syracuseStep 3269843 = 4904765) B4904765
theorem B6981815 : Blo 1451545 6981815 := bstep (se 1 (by rfl) ⟨5236361, by rfl⟩ : syracuseStep 6981815 = 10472723) B10472723
theorem B2452511 : Blo 1451545 2452511 := bstep (se 1 (by rfl) ⟨1839383, by rfl⟩ : syracuseStep 2452511 = 3678767) B3678767
theorem B3674879 : Blo 1451545 3674879 := bstep (se 1 (by rfl) ⟨2756159, by rfl⟩ : syracuseStep 3674879 = 5512319) B5512319
theorem B20140933 : Blo 1451545 20140933 := bstep (se 4 (by rfl) ⟨1888212, by rfl⟩ : syracuseStep 20140933 = 3776425) B3776425
theorem B3266207 : Blo 1451545 3266207 := bstep (se 1 (by rfl) ⟨2449655, by rfl⟩ : syracuseStep 3266207 = 4899311) B4899311
theorem B3266279 : Blo 1451545 3266279 := bstep (se 1 (by rfl) ⟨2449709, by rfl⟩ : syracuseStep 3266279 = 4899419) B4899419
theorem B8386537 : Blo 1451545 8386537 := bstep (se 2 (by rfl) ⟨3144951, by rfl⟩ : syracuseStep 8386537 = 6289903) B6289903
theorem B2449919 : Blo 1451545 2449919 := bstep (se 1 (by rfl) ⟨1837439, by rfl⟩ : syracuseStep 2449919 = 3674879) B3674879
theorem B2179895 : Blo 1451545 2179895 := bstep (se 1 (by rfl) ⟨1634921, by rfl⟩ : syracuseStep 2179895 = 3269843) B3269843
theorem B26854577 : Blo 1451545 26854577 := bstep (se 2 (by rfl) ⟨10070466, by rfl⟩ : syracuseStep 26854577 = 20140933) B20140933
theorem B1635007 : Blo 1451545 1635007 := bstep (se 1 (by rfl) ⟨1226255, by rfl⟩ : syracuseStep 1635007 = 2452511) B2452511
theorem B18618173 : Blo 1451545 18618173 := bstep (se 3 (by rfl) ⟨3490907, by rfl⟩ : syracuseStep 18618173 = 6981815) B6981815
theorem B2177471 : Blo 1451545 2177471 := bstep (se 1 (by rfl) ⟨1633103, by rfl⟩ : syracuseStep 2177471 = 3266207) B3266207
theorem B2177519 : Blo 1451545 2177519 := bstep (se 1 (by rfl) ⟨1633139, by rfl⟩ : syracuseStep 2177519 = 3266279) B3266279
theorem B11182049 : Blo 1451545 11182049 := bstep (se 2 (by rfl) ⟨4193268, by rfl⟩ : syracuseStep 11182049 = 8386537) B8386537
theorem B2180009 : Blo 1451545 2180009 := bstep (se 2 (by rfl) ⟨817503, by rfl⟩ : syracuseStep 2180009 = 1635007) B1635007
theorem B12412115 : Blo 1451545 12412115 := bstep (se 1 (by rfl) ⟨9309086, by rfl⟩ : syracuseStep 12412115 = 18618173) B18618173
theorem B1451647 : Blo 1451545 1451647 := bstep (se 1 (by rfl) ⟨1088735, by rfl⟩ : syracuseStep 1451647 = 2177471) B2177471
theorem B1451679 : Blo 1451545 1451679 := bstep (se 1 (by rfl) ⟨1088759, by rfl⟩ : syracuseStep 1451679 = 2177519) B2177519
theorem B1633279 : Blo 1451545 1633279 := bstep (se 1 (by rfl) ⟨1224959, by rfl⟩ : syracuseStep 1633279 = 2449919) B2449919
theorem B1453263 : Blo 1451545 1453263 := bstep (se 1 (by rfl) ⟨1089947, by rfl⟩ : syracuseStep 1453263 = 2179895) B2179895
theorem B17903051 : Blo 1451545 17903051 := bstep (se 1 (by rfl) ⟨13427288, by rfl⟩ : syracuseStep 17903051 = 26854577) B26854577
theorem B7454699 : Blo 1451545 7454699 := bstep (se 1 (by rfl) ⟨5591024, by rfl⟩ : syracuseStep 7454699 = 11182049) B11182049
theorem B8274743 : Blo 1451545 8274743 := bstep (se 1 (by rfl) ⟨6206057, by rfl⟩ : syracuseStep 8274743 = 12412115) B12412115
theorem B1453339 : Blo 1451545 1453339 := bstep (se 1 (by rfl) ⟨1090004, by rfl⟩ : syracuseStep 1453339 = 2180009) B2180009
theorem B4969799 : Blo 1451545 4969799 := bstep (se 1 (by rfl) ⟨3727349, by rfl⟩ : syracuseStep 4969799 = 7454699) B7454699
theorem B2177705 : Blo 1451545 2177705 := bstep (se 2 (by rfl) ⟨816639, by rfl⟩ : syracuseStep 2177705 = 1633279) B1633279
theorem B11935367 : Blo 1451545 11935367 := bstep (se 1 (by rfl) ⟨8951525, by rfl⟩ : syracuseStep 11935367 = 17903051) B17903051
theorem B1451803 : Blo 1451545 1451803 := bstep (se 1 (by rfl) ⟨1088852, by rfl⟩ : syracuseStep 1451803 = 2177705) B2177705
theorem B7956911 : Blo 1451545 7956911 := bstep (se 1 (by rfl) ⟨5967683, by rfl⟩ : syracuseStep 7956911 = 11935367) B11935367
theorem B5516495 : Blo 1451545 5516495 := bstep (se 1 (by rfl) ⟨4137371, by rfl⟩ : syracuseStep 5516495 = 8274743) B8274743
theorem B3313199 : Blo 1451545 3313199 := bstep (se 1 (by rfl) ⟨2484899, by rfl⟩ : syracuseStep 3313199 = 4969799) B4969799
theorem B21218429 : Blo 1451545 21218429 := bstep (se 3 (by rfl) ⟨3978455, by rfl⟩ : syracuseStep 21218429 = 7956911) B7956911
theorem B2208799 : Blo 1451545 2208799 := bstep (se 1 (by rfl) ⟨1656599, by rfl⟩ : syracuseStep 2208799 = 3313199) B3313199
theorem B3677663 : Blo 1451545 3677663 := bstep (se 1 (by rfl) ⟨2758247, by rfl⟩ : syracuseStep 3677663 = 5516495) B5516495
theorem B11780261 : Blo 1451545 11780261 := bstep (se 4 (by rfl) ⟨1104399, by rfl⟩ : syracuseStep 11780261 = 2208799) B2208799
theorem B2451775 : Blo 1451545 2451775 := bstep (se 1 (by rfl) ⟨1838831, by rfl⟩ : syracuseStep 2451775 = 3677663) B3677663
theorem B14145619 : Blo 1451545 14145619 := bstep (se 1 (by rfl) ⟨10609214, by rfl⟩ : syracuseStep 14145619 = 21218429) B21218429
theorem B3269033 : Blo 1451545 3269033 := bstep (se 2 (by rfl) ⟨1225887, by rfl⟩ : syracuseStep 3269033 = 2451775) B2451775
theorem B18860825 : Blo 1451545 18860825 := bstep (se 2 (by rfl) ⟨7072809, by rfl⟩ : syracuseStep 18860825 = 14145619) B14145619
theorem B7853507 : Blo 1451545 7853507 := bstep (se 1 (by rfl) ⟨5890130, by rfl⟩ : syracuseStep 7853507 = 11780261) B11780261
theorem B2179355 : Blo 1451545 2179355 := bstep (se 1 (by rfl) ⟨1634516, by rfl⟩ : syracuseStep 2179355 = 3269033) B3269033
theorem B5235671 : Blo 1451545 5235671 := bstep (se 1 (by rfl) ⟨3926753, by rfl⟩ : syracuseStep 5235671 = 7853507) B7853507
theorem B12573883 : Blo 1451545 12573883 := bstep (se 1 (by rfl) ⟨9430412, by rfl⟩ : syracuseStep 12573883 = 18860825) B18860825
theorem B3490447 : Blo 1451545 3490447 := bstep (se 1 (by rfl) ⟨2617835, by rfl⟩ : syracuseStep 3490447 = 5235671) B5235671
theorem B1452903 : Blo 1451545 1452903 := bstep (se 1 (by rfl) ⟨1089677, by rfl⟩ : syracuseStep 1452903 = 2179355) B2179355
theorem B16765177 : Blo 1451545 16765177 := bstep (se 2 (by rfl) ⟨6286941, by rfl⟩ : syracuseStep 16765177 = 12573883) B12573883
theorem B4653929 : Blo 1451545 4653929 := bstep (se 2 (by rfl) ⟨1745223, by rfl⟩ : syracuseStep 4653929 = 3490447) B3490447
theorem B22353569 : Blo 1451545 22353569 := bstep (se 2 (by rfl) ⟨8382588, by rfl⟩ : syracuseStep 22353569 = 16765177) B16765177
theorem B14902379 : Blo 1451545 14902379 := bstep (se 1 (by rfl) ⟨11176784, by rfl⟩ : syracuseStep 14902379 = 22353569) B22353569
theorem B3102619 : Blo 1451545 3102619 := bstep (se 1 (by rfl) ⟨2326964, by rfl⟩ : syracuseStep 3102619 = 4653929) B4653929
theorem B9934919 : Blo 1451545 9934919 := bstep (se 1 (by rfl) ⟨7451189, by rfl⟩ : syracuseStep 9934919 = 14902379) B14902379
theorem B4136825 : Blo 1451545 4136825 := bstep (se 2 (by rfl) ⟨1551309, by rfl⟩ : syracuseStep 4136825 = 3102619) B3102619
theorem B6623279 : Blo 1451545 6623279 := bstep (se 1 (by rfl) ⟨4967459, by rfl⟩ : syracuseStep 6623279 = 9934919) B9934919
theorem B2757883 : Blo 1451545 2757883 := bstep (se 1 (by rfl) ⟨2068412, by rfl⟩ : syracuseStep 2757883 = 4136825) B4136825
theorem B4415519 : Blo 1451545 4415519 := bstep (se 1 (by rfl) ⟨3311639, by rfl⟩ : syracuseStep 4415519 = 6623279) B6623279
theorem B3677177 : Blo 1451545 3677177 := bstep (se 2 (by rfl) ⟨1378941, by rfl⟩ : syracuseStep 3677177 = 2757883) B2757883
theorem B2451451 : Blo 1451545 2451451 := bstep (se 1 (by rfl) ⟨1838588, by rfl⟩ : syracuseStep 2451451 = 3677177) B3677177
theorem B11774717 : Blo 1451545 11774717 := bstep (se 3 (by rfl) ⟨2207759, by rfl⟩ : syracuseStep 11774717 = 4415519) B4415519
theorem B7849811 : Blo 1451545 7849811 := bstep (se 1 (by rfl) ⟨5887358, by rfl⟩ : syracuseStep 7849811 = 11774717) B11774717
theorem B3268601 : Blo 1451545 3268601 := bstep (se 2 (by rfl) ⟨1225725, by rfl⟩ : syracuseStep 3268601 = 2451451) B2451451
theorem B5233207 : Blo 1451545 5233207 := bstep (se 1 (by rfl) ⟨3924905, by rfl⟩ : syracuseStep 5233207 = 7849811) B7849811
theorem B2179067 : Blo 1451545 2179067 := bstep (se 1 (by rfl) ⟨1634300, by rfl⟩ : syracuseStep 2179067 = 3268601) B3268601
theorem B1452711 : Blo 1451545 1452711 := bstep (se 1 (by rfl) ⟨1089533, by rfl⟩ : syracuseStep 1452711 = 2179067) B2179067
theorem B6977609 : Blo 1451545 6977609 := bstep (se 2 (by rfl) ⟨2616603, by rfl⟩ : syracuseStep 6977609 = 5233207) B5233207
theorem B4651739 : Blo 1451545 4651739 := bstep (se 1 (by rfl) ⟨3488804, by rfl⟩ : syracuseStep 4651739 = 6977609) B6977609
theorem B3101159 : Blo 1451545 3101159 := bstep (se 1 (by rfl) ⟨2325869, by rfl⟩ : syracuseStep 3101159 = 4651739) B4651739
theorem B2067439 : Blo 1451545 2067439 := bstep (se 1 (by rfl) ⟨1550579, by rfl⟩ : syracuseStep 2067439 = 3101159) B3101159
theorem B2756585 : Blo 1451545 2756585 := bstep (se 2 (by rfl) ⟨1033719, by rfl⟩ : syracuseStep 2756585 = 2067439) B2067439
theorem B1837723 : Blo 1451545 1837723 := bstep (se 1 (by rfl) ⟨1378292, by rfl⟩ : syracuseStep 1837723 = 2756585) B2756585
theorem B2450297 : Blo 1451545 2450297 := bstep (se 2 (by rfl) ⟨918861, by rfl⟩ : syracuseStep 2450297 = 1837723) B1837723
theorem B1633531 : Blo 1451545 1633531 := bstep (se 1 (by rfl) ⟨1225148, by rfl⟩ : syracuseStep 1633531 = 2450297) B2450297
theorem B2178041 : Blo 1451545 2178041 := bstep (se 2 (by rfl) ⟨816765, by rfl⟩ : syracuseStep 2178041 = 1633531) B1633531
theorem B1452027 : Blo 1451545 1452027 := bstep (se 1 (by rfl) ⟨1089020, by rfl⟩ : syracuseStep 1452027 = 2178041) B2178041

theorem C0 (j : ℕ) (h1 : 362886 ≤ j) (h2 : j ≤ 363385) : Blo 1451545 (4 * j + 3) := by
  interval_cases j
  · exact B1451547
  · exact B1451551
  · exact B1451555
  · exact B1451559
  · exact B1451563
  · exact B1451567
  · exact B1451571
  · exact B1451575
  · exact B1451579
  · exact B1451583
  · exact B1451587
  · exact B1451591
  · exact B1451595
  · exact B1451599
  · exact B1451603
  · exact B1451607
  · exact B1451611
  · exact B1451615
  · exact B1451619
  · exact B1451623
  · exact B1451627
  · exact B1451631
  · exact B1451635
  · exact B1451639
  · exact B1451643
  · exact B1451647
  · exact B1451651
  · exact B1451655
  · exact B1451659
  · exact B1451663
  · exact B1451667
  · exact B1451671
  · exact B1451675
  · exact B1451679
  · exact B1451683
  · exact B1451687
  · exact B1451691
  · exact B1451695
  · exact B1451699
  · exact B1451703
  · exact B1451707
  · exact B1451711
  · exact B1451715
  · exact B1451719
  · exact B1451723
  · exact B1451727
  · exact B1451731
  · exact B1451735
  · exact B1451739
  · exact B1451743
  · exact B1451747
  · exact B1451751
  · exact B1451755
  · exact B1451759
  · exact B1451763
  · exact B1451767
  · exact B1451771
  · exact B1451775
  · exact B1451779
  · exact B1451783
  · exact B1451787
  · exact B1451791
  · exact B1451795
  · exact B1451799
  · exact B1451803
  · exact B1451807
  · exact B1451811
  · exact B1451815
  · exact B1451819
  · exact B1451823
  · exact B1451827
  · exact B1451831
  · exact B1451835
  · exact B1451839
  · exact B1451843
  · exact B1451847
  · exact B1451851
  · exact B1451855
  · exact B1451859
  · exact B1451863
  · exact B1451867
  · exact B1451871
  · exact B1451875
  · exact B1451879
  · exact B1451883
  · exact B1451887
  · exact B1451891
  · exact B1451895
  · exact B1451899
  · exact B1451903
  · exact B1451907
  · exact B1451911
  · exact B1451915
  · exact B1451919
  · exact B1451923
  · exact B1451927
  · exact B1451931
  · exact B1451935
  · exact B1451939
  · exact B1451943
  · exact B1451947
  · exact B1451951
  · exact B1451955
  · exact B1451959
  · exact B1451963
  · exact B1451967
  · exact B1451971
  · exact B1451975
  · exact B1451979
  · exact B1451983
  · exact B1451987
  · exact B1451991
  · exact B1451995
  · exact B1451999
  · exact B1452003
  · exact B1452007
  · exact B1452011
  · exact B1452015
  · exact B1452019
  · exact B1452023
  · exact B1452027
  · exact B1452031
  · exact B1452035
  · exact B1452039
  · exact B1452043
  · exact B1452047
  · exact B1452051
  · exact B1452055
  · exact B1452059
  · exact B1452063
  · exact B1452067
  · exact B1452071
  · exact B1452075
  · exact B1452079
  · exact B1452083
  · exact B1452087
  · exact B1452091
  · exact B1452095
  · exact B1452099
  · exact B1452103
  · exact B1452107
  · exact B1452111
  · exact B1452115
  · exact B1452119
  · exact B1452123
  · exact B1452127
  · exact B1452131
  · exact B1452135
  · exact B1452139
  · exact B1452143
  · exact B1452147
  · exact B1452151
  · exact B1452155
  · exact B1452159
  · exact B1452163
  · exact B1452167
  · exact B1452171
  · exact B1452175
  · exact B1452179
  · exact B1452183
  · exact B1452187
  · exact B1452191
  · exact B1452195
  · exact B1452199
  · exact B1452203
  · exact B1452207
  · exact B1452211
  · exact B1452215
  · exact B1452219
  · exact B1452223
  · exact B1452227
  · exact B1452231
  · exact B1452235
  · exact B1452239
  · exact B1452243
  · exact B1452247
  · exact B1452251
  · exact B1452255
  · exact B1452259
  · exact B1452263
  · exact B1452267
  · exact B1452271
  · exact B1452275
  · exact B1452279
  · exact B1452283
  · exact B1452287
  · exact B1452291
  · exact B1452295
  · exact B1452299
  · exact B1452303
  · exact B1452307
  · exact B1452311
  · exact B1452315
  · exact B1452319
  · exact B1452323
  · exact B1452327
  · exact B1452331
  · exact B1452335
  · exact B1452339
  · exact B1452343
  · exact B1452347
  · exact B1452351
  · exact B1452355
  · exact B1452359
  · exact B1452363
  · exact B1452367
  · exact B1452371
  · exact B1452375
  · exact B1452379
  · exact B1452383
  · exact B1452387
  · exact B1452391
  · exact B1452395
  · exact B1452399
  · exact B1452403
  · exact B1452407
  · exact B1452411
  · exact B1452415
  · exact B1452419
  · exact B1452423
  · exact B1452427
  · exact B1452431
  · exact B1452435
  · exact B1452439
  · exact B1452443
  · exact B1452447
  · exact B1452451
  · exact B1452455
  · exact B1452459
  · exact B1452463
  · exact B1452467
  · exact B1452471
  · exact B1452475
  · exact B1452479
  · exact B1452483
  · exact B1452487
  · exact B1452491
  · exact B1452495
  · exact B1452499
  · exact B1452503
  · exact B1452507
  · exact B1452511
  · exact B1452515
  · exact B1452519
  · exact B1452523
  · exact B1452527
  · exact B1452531
  · exact B1452535
  · exact B1452539
  · exact B1452543
  · exact B1452547
  · exact B1452551
  · exact B1452555
  · exact B1452559
  · exact B1452563
  · exact B1452567
  · exact B1452571
  · exact B1452575
  · exact B1452579
  · exact B1452583
  · exact B1452587
  · exact B1452591
  · exact B1452595
  · exact B1452599
  · exact B1452603
  · exact B1452607
  · exact B1452611
  · exact B1452615
  · exact B1452619
  · exact B1452623
  · exact B1452627
  · exact B1452631
  · exact B1452635
  · exact B1452639
  · exact B1452643
  · exact B1452647
  · exact B1452651
  · exact B1452655
  · exact B1452659
  · exact B1452663
  · exact B1452667
  · exact B1452671
  · exact B1452675
  · exact B1452679
  · exact B1452683
  · exact B1452687
  · exact B1452691
  · exact B1452695
  · exact B1452699
  · exact B1452703
  · exact B1452707
  · exact B1452711
  · exact B1452715
  · exact B1452719
  · exact B1452723
  · exact B1452727
  · exact B1452731
  · exact B1452735
  · exact B1452739
  · exact B1452743
  · exact B1452747
  · exact B1452751
  · exact B1452755
  · exact B1452759
  · exact B1452763
  · exact B1452767
  · exact B1452771
  · exact B1452775
  · exact B1452779
  · exact B1452783
  · exact B1452787
  · exact B1452791
  · exact B1452795
  · exact B1452799
  · exact B1452803
  · exact B1452807
  · exact B1452811
  · exact B1452815
  · exact B1452819
  · exact B1452823
  · exact B1452827
  · exact B1452831
  · exact B1452835
  · exact B1452839
  · exact B1452843
  · exact B1452847
  · exact B1452851
  · exact B1452855
  · exact B1452859
  · exact B1452863
  · exact B1452867
  · exact B1452871
  · exact B1452875
  · exact B1452879
  · exact B1452883
  · exact B1452887
  · exact B1452891
  · exact B1452895
  · exact B1452899
  · exact B1452903
  · exact B1452907
  · exact B1452911
  · exact B1452915
  · exact B1452919
  · exact B1452923
  · exact B1452927
  · exact B1452931
  · exact B1452935
  · exact B1452939
  · exact B1452943
  · exact B1452947
  · exact B1452951
  · exact B1452955
  · exact B1452959
  · exact B1452963
  · exact B1452967
  · exact B1452971
  · exact B1452975
  · exact B1452979
  · exact B1452983
  · exact B1452987
  · exact B1452991
  · exact B1452995
  · exact B1452999
  · exact B1453003
  · exact B1453007
  · exact B1453011
  · exact B1453015
  · exact B1453019
  · exact B1453023
  · exact B1453027
  · exact B1453031
  · exact B1453035
  · exact B1453039
  · exact B1453043
  · exact B1453047
  · exact B1453051
  · exact B1453055
  · exact B1453059
  · exact B1453063
  · exact B1453067
  · exact B1453071
  · exact B1453075
  · exact B1453079
  · exact B1453083
  · exact B1453087
  · exact B1453091
  · exact B1453095
  · exact B1453099
  · exact B1453103
  · exact B1453107
  · exact B1453111
  · exact B1453115
  · exact B1453119
  · exact B1453123
  · exact B1453127
  · exact B1453131
  · exact B1453135
  · exact B1453139
  · exact B1453143
  · exact B1453147
  · exact B1453151
  · exact B1453155
  · exact B1453159
  · exact B1453163
  · exact B1453167
  · exact B1453171
  · exact B1453175
  · exact B1453179
  · exact B1453183
  · exact B1453187
  · exact B1453191
  · exact B1453195
  · exact B1453199
  · exact B1453203
  · exact B1453207
  · exact B1453211
  · exact B1453215
  · exact B1453219
  · exact B1453223
  · exact B1453227
  · exact B1453231
  · exact B1453235
  · exact B1453239
  · exact B1453243
  · exact B1453247
  · exact B1453251
  · exact B1453255
  · exact B1453259
  · exact B1453263
  · exact B1453267
  · exact B1453271
  · exact B1453275
  · exact B1453279
  · exact B1453283
  · exact B1453287
  · exact B1453291
  · exact B1453295
  · exact B1453299
  · exact B1453303
  · exact B1453307
  · exact B1453311
  · exact B1453315
  · exact B1453319
  · exact B1453323
  · exact B1453327
  · exact B1453331
  · exact B1453335
  · exact B1453339
  · exact B1453343
  · exact B1453347
  · exact B1453351
  · exact B1453355
  · exact B1453359
  · exact B1453363
  · exact B1453367
  · exact B1453371
  · exact B1453375
  · exact B1453379
  · exact B1453383
  · exact B1453387
  · exact B1453391
  · exact B1453395
  · exact B1453399
  · exact B1453403
  · exact B1453407
  · exact B1453411
  · exact B1453415
  · exact B1453419
  · exact B1453423
  · exact B1453427
  · exact B1453431
  · exact B1453435
  · exact B1453439
  · exact B1453443
  · exact B1453447
  · exact B1453451
  · exact B1453455
  · exact B1453459
  · exact B1453463
  · exact B1453467
  · exact B1453471
  · exact B1453475
  · exact B1453479
  · exact B1453483
  · exact B1453487
  · exact B1453491
  · exact B1453495
  · exact B1453499
  · exact B1453503
  · exact B1453507
  · exact B1453511
  · exact B1453515
  · exact B1453519
  · exact B1453523
  · exact B1453527
  · exact B1453531
  · exact B1453535
  · exact B1453539
  · exact B1453543

theorem solution (m : ℕ) (hlo : 1451545 ≤ m) (hhi : m ≤ 1453545) (hodd : Odd m) :
    ∃ t : ℕ, syracuseStep^[t] m < m := by
  obtain ⟨w, hw⟩ := hodd
  have h4 : m % 4 = 1 ∨ m % 4 = 3 := by omega
  rcases h4 with h4 | h4
  · refine ⟨1, ?_⟩
    rw [Function.iterate_one]
    exact step_lt_of_one_mod_four m (by omega) h4
  · obtain ⟨j, rfl⟩ : ∃ j, m = 4 * j + 3 := ⟨m / 4, by omega⟩
    have hj1 : 362886 ≤ j := by omega
    have hj2 : j ≤ 363385 := by omega
    have hb : Blo 1451545 (4 * j + 3) := by
      exact C0 j (by omega) (by omega)
    obtain ⟨t, ht⟩ := hb
    exact ⟨t, by omega⟩
